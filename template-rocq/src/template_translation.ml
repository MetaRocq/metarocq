(* The translation of template-polymorphic inductives into universe-polymorphic
   ones, which SafeCheck needs because PCUIC has no template polymorphism
   (issue #16).  [Quoter.quote_term_rec ~translate_template:true] creates one
   translation [t] for its run and gives it to the quoter, which calls the
   functions below at each template-specific step.  A quotation without a
   translation calls none of them.  Nothing here depends on the quoted
   representation.

   This code is trusted: it changes declarations and adds universe constraints
   before the checker runs. *)

open Declarations

let template_inverse_substitution template =
  let _, bound_levels =
    UVars.Instance.to_array
      (UVars.UContext.instance
         (UVars.AbstractContext.repr template.template_context))
  in
  let _, default_levels =
    UVars.Instance.to_array template.template_defaults
  in
  let level_substitution =
    CArray.fold_left2
      (fun substitution default bound ->
         Univ.Level.Map.add default bound substitution)
      Univ.Level.Map.empty default_levels bound_levels
  in
  ((Sorts.QVar.Map.empty, level_substitution),
   UVars.Instance.of_array ([||], bound_levels))

let named_template_context template =
  let { UVars.quals = _; UVars.univs } =
    UVars.AbstractContext.names template.template_context
  in
  let univs =
    Array.mapi
      (fun index _ ->
         Names.Name (Names.Id.of_string ("template" ^ string_of_int index)))
      univs
  in
  UVars.AbstractContext.make { UVars.quals = [||]; UVars.univs }
    (UVars.UContext.constraints
       (UVars.AbstractContext.repr template.template_context))

(* Per-declaration scope for algebraic template universes whose components
   mention bound universe variables of the enclosing polymorphic declaration.
   Such a universe cannot be replaced by a fresh *global* level (the global
   context forbids variable levels); instead we add a fresh *bound* level
   [Var (ls_n_orig + k)] to the declaration's own abstract universe context,
   lower-bounded by the components.  [ls_definitions.(k)] is the universe that
   level stands for.  Every use site of the declaration then supplies, for
   that extra level, the component expression instantiated at the use's own
   universe instance (see [extend_instance_for]). *)
type local_scope = {
  ls_n_orig : int;
  mutable ls_memo : Univ.Level.t Univ.Universe.Map.t;
  mutable ls_definitions : Univ.Universe.t array;
  mutable ls_constraints : Univ.UnivConstraints.t;
}

let new_local_scope n_orig = {
  ls_n_orig = n_orig;
  ls_memo = Univ.Universe.Map.empty;
  ls_definitions = [||];
  ls_constraints = Univ.UnivConstraints.empty;
}

(* What the quoted value of one kernel subterm was computed from, besides the
   subterm itself.  [Quoter.quote_term_remember] uses it to decide whether its
   cache may return that value at another occurrence of the same physical
   subterm; the argument is in the comment there.
   - The flags say that the subterm, or one of its subterms, read that part
     of the context.  [qd_env] and [qd_scope] keep what was read.  Retyping
     requires the same environment object because it can inspect every
     global table as well as the local context; graph reads require the same
     universe graph.  A cached record without those flags keeps neither
     environment nor scope. *)
type quote_dependencies = {
  mutable qd_env : Environ.env;
  mutable qd_scope : local_scope option;
  (* [template_instance] retyped an argument in [qd_env], whose identity is
     part of the cache key. *)
  mutable qd_retypes : bool;
  (* [read_local_scope] read the declaration-local universe scope. *)
  mutable qd_reads_scope : bool;
  (* [read_universe_graph] read the universe graph of [qd_env]. *)
  mutable qd_graph : bool;
  (* The subterm refers to a declaration that was still being quoted, whose
     extra universe levels ([extended_constants], [extended_inductives]) were
     not known yet.  Quoting it again later can give another value, so it is
     never cached. *)
  mutable qd_unstable : bool;
}

let new_quote_dependencies env =
  { qd_env = env; qd_scope = None; qd_retypes = false;
    qd_reads_scope = false; qd_graph = false; qd_unstable = false }

(* The declaration being quoted: its name for diagnostics, its local universe
   scope, the dependency record of the subterm being quoted, and the
   declarations still in progress.  They are one record so that one
   exception-safe swap ([with_state]) restores the whole declaration
   boundary. *)
type declaration_state = {
  ds_name : string;
  ds_scope : local_scope option;
  ds_dependencies : quote_dependencies;
  ds_in_progress : Names.KNset.t;
}

(* The state of one translating quotation. *)
type t = {
  (* One global level strictly above every level of the quoted program
     ([program_universes] adds [l < top] for each), used by
     [template_instance ~canonical]. *)
  top : Univ.Level.t;
  mutable universe_levels : Univ.Level.t Univ.Universe.Map.t;
  mutable fresh_definitions : Univ.Universe.t Univ.Level.Map.t;
  mutable fresh_constraints : Univ.UnivConstraints.t;
  mutable next_fresh_level : int;
  (* Levels the translated program uses that the quoted kernel terms need not
     mention: each fresh level and the levels of the universe it stands for,
     and the levels of every sort and instance the quoter met or emitted. *)
  mutable program_levels : Univ.Level.Set.t;
  (* The template default levels of the quoted template inductives. *)
  mutable default_levels : Univ.Level.Set.t;
  mutable state : declaration_state;
  (* Declarations whose abstract universe context we extended with extra
     bound levels, together with the component expressions (over the
     declaration's original bound variables) that those levels stand for, in
     index order. *)
  mutable extended_constants : Univ.Universe.t list Names.KerName.Map.t;
  mutable extended_inductives : Univ.Universe.t list Names.KerName.Map.t;
}

(* The first level [MetaRocq.Template.algebraic.i] with [i >= index] that
   [graph] does not declare, and the index after it. *)
let fresh_global_level graph index =
  let dirpath =
    Names.DirPath.make [Names.Id.of_string "MetaRocq";
                        Names.Id.of_string "Template"]
  in
  let rec fresh index =
    let level =
      Univ.Level.make (Univ.UGlobal.make dirpath "algebraic" index)
    in
    match UGraph.check_declared_universes graph
            (Univ.Level.Set.singleton level) with
    | Ok () -> fresh (index + 1)
    | Error _ -> level, index + 1
  in
  fresh index

let fresh_template_level graph translation =
  let level, next = fresh_global_level graph translation.next_fresh_level in
  translation.next_fresh_level <- next;
  level

(* The translation for one quotation in [env].  [top] is its first fresh
   level. *)
let create env =
  let top, next_fresh_level = fresh_global_level (Environ.universes env) 0 in
  { top;
    universe_levels = Univ.Universe.Map.empty;
    fresh_definitions = Univ.Level.Map.empty;
    fresh_constraints = Univ.UnivConstraints.empty;
    next_fresh_level;
    program_levels = Univ.Level.Set.empty;
    default_levels = Univ.Level.Set.empty;
    state =
      { ds_name = "<toplevel>";
        ds_scope = None;
        ds_dependencies = new_quote_dependencies Environ.empty_env;
        ds_in_progress = Names.KNset.empty };
    extended_constants = Names.KerName.Map.empty;
    extended_inductives = Names.KerName.Map.empty }

let with_state translation state f =
  let saved = translation.state in
  translation.state <- state;
  match f () with
  | result ->
    translation.state <- saved;
    result
  | exception e ->
    let e = Exninfo.capture e in
    translation.state <- saved;
    Exninfo.iraise e

(* Run [f] as the quotation of declaration [kn], with the local universe
   scope [scope], from a fresh dependency root: what the declaration reads is
   not a dependency of the subterm whose quotation reached it.  While [f]
   runs, [kn] is in progress, so a subterm referring to it is not cached (see
   [quote_dependencies.qd_unstable]). *)
let with_declaration translation kn ~name ~scope f =
  with_state translation
    { ds_name = name;
      ds_scope = scope;
      ds_dependencies = new_quote_dependencies Environ.empty_env;
      ds_in_progress = Names.KNset.add kn translation.state.ds_in_progress }
    f

let with_constant translation kn cb f =
  let scope =
    match cb.const_universes with
    | Polymorphic auctx ->
      Some (new_local_scope (snd (UVars.AbstractContext.size auctx)))
    | Monomorphic -> None
  in
  with_declaration translation kn
    ~name:(Pp.string_of_ppcmds (Names.KerName.print kn)) ~scope f

let with_inductive translation mind mib f =
  let universe_count =
    match mib.mind_template, mib.mind_universes with
    | Some template, _ ->
      snd (UVars.AbstractContext.size template.template_context)
    | None, Polymorphic auctx -> snd (UVars.AbstractContext.size auctx)
    | None, Monomorphic -> 0
  in
  Option.iter
    (fun template ->
       translation.default_levels <-
         Univ.Level.Set.union
           (snd (UVars.Instance.levels template.template_defaults))
           translation.default_levels)
    mib.mind_template;
  let scope =
    if Int.equal universe_count 0 then None
    else Some (new_local_scope universe_count)
  in
  with_declaration translation (Names.MutInd.canonical mind)
    ~name:(Pp.string_of_ppcmds (Names.MutInd.print mind)) ~scope f

let current_dependencies translation =
  translation.state.ds_dependencies

let read_local_scope translation =
  let state = translation.state in
  let dependencies = state.ds_dependencies in
  dependencies.qd_reads_scope <- true;
  dependencies.qd_scope <- state.ds_scope;
  state.ds_scope

let read_universe_graph translation env =
  (current_dependencies translation).qd_graph <- true;
  Environ.universes env

let retype_template_argument translation env sigma arg =
  (current_dependencies translation).qd_retypes <- true;
  EConstr.to_constr sigma
    (Retyping.get_type_of env sigma (EConstr.of_constr arg))

let note_declaration_reference translation kn =
  let state = translation.state in
  if Names.KNset.mem kn state.ds_in_progress then
    state.ds_dependencies.qd_unstable <- true

let note_instance_levels translation instance =
  translation.program_levels <-
    Univ.Level.Set.union (snd (UVars.Instance.levels instance))
      translation.program_levels

let note_sort_levels translation = function
  | Sorts.Type universe | Sorts.QSort (_, universe) ->
    translation.program_levels <-
      Univ.Universe.levels ~init:translation.program_levels universe
  | _ -> ()

(* The cache is used only under an evar map with no evars, no conversion
   problems, no local universes and no flexible universe variables, as made
   by [Evd.from_env].  Under such a map [EConstr.to_constr] and [Retyping]
   find no evar to expand, and the universe substitution they apply is the
   identity, so every usable evar map gives the same quotation.  The SafeCheck
   command quotes its elaborated input under the evar map that holds the
   input's universes, so the subterms of that top term are quoted without the
   cache; constant bodies are quoted under [Evd.from_env] and use it. *)
let quote_cache_usable sigma =
  Evd.is_empty sigma && UState.is_empty (Evd.ustate sigma)

(* Whether a value cached with dependencies [deps] is the value quoting the
   same subterm would compute now, in [env].  Retyping reads global constants,
   inductives and reduction data, for which [Environ] exposes no stable
   identity separate from [env], so a retyped value is specific to the exact
   environment object that produced it.  The check records no read: on a
   hit, [add_quote_dependencies] charges the reads of [deps] to the parent. *)
let quote_dependencies_hold translation deps env =
  (not deps.qd_retypes || deps.qd_env == env)
  && (not deps.qd_reads_scope
      || Option.equal (==) translation.state.ds_scope deps.qd_scope)
  && (not deps.qd_graph
      || Environ.universes env == Environ.universes deps.qd_env)

(* Charge the reads of a subterm to [parent]. *)
let add_quote_dependencies parent child =
  if child.qd_retypes then parent.qd_retypes <- true;
  if child.qd_reads_scope then begin
    parent.qd_reads_scope <- true;
    parent.qd_scope <- child.qd_scope
  end;
  if child.qd_graph then parent.qd_graph <- true;
  if child.qd_unstable then parent.qd_unstable <- true

(* Drop what a finished record does not need before the cache keeps it. *)
let release_quote_dependencies deps =
  if not (deps.qd_retypes || deps.qd_graph) then
    deps.qd_env <- Environ.empty_env;
  if not deps.qd_reads_scope then deps.qd_scope <- None

let universe_has_var_component universe =
  List.exists
    (fun (level, _) -> not (Option.is_empty (Univ.Level.var_index level)))
    (Univ.Universe.repr universe)

(* Expand each component of [universe] through [definition_of], repeatedly. *)
let expand_universe definition_of universe =
  let rec expand_component shift level =
    match definition_of level with
    | Some definition ->
      List.concat_map
        (fun (component, component_shift) ->
           expand_component (shift + component_shift) component)
        (Univ.Universe.repr definition)
    | None -> [level, shift]
  in
  Univ.Universe.unrepr
    (List.concat_map
       (fun (level, shift) -> expand_component shift level)
       (Univ.Universe.repr universe))

let normalize_local_universe scope universe =
  expand_universe
    (fun level ->
       match Univ.Level.var_index level with
       | Some index
         when index >= scope.ls_n_orig
           && index < scope.ls_n_orig + Array.length scope.ls_definitions ->
         Some scope.ls_definitions.(index - scope.ls_n_orig)
       | _ -> None)
    universe

(* [component <= level] for each component, [<] for a unit offset. *)
let add_lower_bound_constraints level components constraints =
  List.fold_left
    (fun constraints (component, shift) ->
       let kind =
         match shift with
         | 0 -> Univ.UnivConstraint.Le
         | 1 -> Univ.UnivConstraint.Lt
         | _ ->
           CErrors.user_err
             Pp.(str "Quoting template universe offsets above one is not supported.")
       in
       Univ.UnivConstraints.add (component, kind, level) constraints)
    constraints components

let local_fresh_var scope universe =
  let universe = normalize_local_universe scope universe in
  match Univ.Universe.Map.find_opt universe scope.ls_memo with
  | Some level -> level
  | None ->
    let level =
      Univ.Level.var (scope.ls_n_orig + Array.length scope.ls_definitions)
    in
    let constraints =
      add_lower_bound_constraints level (Univ.Universe.repr universe)
        scope.ls_constraints
    in
    scope.ls_memo <- Univ.Universe.Map.add universe level scope.ls_memo;
    scope.ls_definitions <- Array.append scope.ls_definitions [| universe |];
    scope.ls_constraints <- constraints;
    level

let extend_abstract_context auctx scope upper_bounds =
  let repr = UVars.AbstractContext.repr auctx in
  let { UVars.quals; UVars.univs } =
    UVars.AbstractContext.names auctx
  in
  let extra =
    Array.init (Array.length scope.ls_definitions)
      (fun k ->
         Names.Name
           (Names.Id.of_string ("template_alg" ^ string_of_int k)))
  in
  let new_pcon =
    Univ.UnivConstraints.fold
      (fun cstr pcon -> PConstraints.add_univ cstr pcon)
      (Univ.UnivConstraints.union scope.ls_constraints upper_bounds)
      (UVars.UContext.constraints repr)
  in
  UVars.AbstractContext.make
    { UVars.quals; UVars.univs = Array.append univs extra } new_pcon

(* [auctx] with [Var k <= top] for each of its bound levels.  Every instance
   the quoted program gives a polymorphic declaration is made of levels at
   most [top]: [top] itself (canonical template instances), global levels
   below it (constrained in [program_universes]), and bound levels of other
   polymorphic declarations (constrained here).  So the extra constraints
   reject no use site, and inside the declaration they let PCUIC derive
   [Type@{Var k} <= Type@{top}] where a canonical instance needs it. *)
let constrain_below_top top auctx =
  let repr = UVars.AbstractContext.repr auctx in
  let _, levels = UVars.Instance.to_array (UVars.UContext.instance repr) in
  let pcon =
    Array.fold_left
      (fun pcon level ->
         PConstraints.add_univ (level, Univ.UnivConstraint.Le, top) pcon)
      (UVars.UContext.constraints repr) levels
  in
  UVars.AbstractContext.make (UVars.AbstractContext.names auctx) pcon

(* Every universe level is at least [Set], so [max(Set, u1, ..., un)] equals
   [max(u1, ..., un)] when a non-[Set] component is present.  Removing that
   redundant component before minting representatives prevents list's
   intrinsic [max(Set, u)] result sort from introducing a spurious second
   universe parameter.

   Only the component [(Set, 0)] is redundant.  [Set+n] for [n > 0] is not:
   [max(Set+1, u)] and [u] differ whenever [u] may be [Set], and dropping
   the offset would turn the obligation of a cast from [Type@{max(Set+1,u)}]
   to [Type@{u}] into a reflexive one.  A positive offset is kept, and the
   algebraic universe then gets a representative with its lower bounds. *)
let simplify_template_universe universe =
  let redundant_set (level, shift) =
    Univ.Level.equal level Univ.Level.set && Int.equal shift 0
  in
  match
    List.filter (fun component -> not (redundant_set component))
      (Univ.Universe.repr universe)
  with
  | [] -> universe
  | kept -> Univ.Universe.unrepr kept

let normalize_global_universe translation universe =
  expand_universe
    (fun level -> Univ.Level.Map.find_opt level translation.fresh_definitions)
    universe

let fresh_template_upper_bounds leq graph univs definitions constraints =
  let definition_of level =
    match Univ.Level.Map.find_opt level definitions with
    | Some definition -> definition
    | None -> Univ.Universe.make level
  in
  let candidates =
    Univ.Level.Map.fold
      (fun level _ candidates -> Univ.Level.Set.add level candidates)
      definitions
      (Univ.Level.Set.inter univs (UGraph.domain graph))
  in
  let provably_leq u v =
    let levels =
      Univ.Level.Set.union
        (Univ.Universe.levels ~init:Univ.Level.Set.empty u)
        (Univ.Universe.levels ~init:Univ.Level.Set.empty v)
    in
    match UGraph.check_declared_universes graph levels with
    | Ok () -> leq graph u v
    | Error _ -> false
  in
  Tm_util.time Pp.(str "Computing fresh template upper bounds")
    (Univ.Level.Map.fold
       (fun fresh definition constraints ->
          Univ.Level.Set.fold
            (fun level constraints ->
               if Univ.Level.equal fresh level
                  || not (provably_leq definition (definition_of level))
               then constraints
               else
                 Univ.UnivConstraints.add
                   (fresh, Univ.UnivConstraint.Le, level) constraints)
            candidates constraints)
       definitions)
    constraints

(* Upper bounds for the levels that [scope] added to the abstract context
   [auctx] of the declaration being quoted, as [program_universes] adds them
   for fresh global levels: [a <= l] for each added level [a] and each level
   [l] of the declaration, bound or added, with [D_a <= D_l] in the graph of
   [env] extended with [auctx] and with type-in-type disabled.  [D_x] is the
   universe that an added level [x] stands for, and [l] itself for any other
   level.  A global level [l] of the program so far is tried too, when a
   constraint of [auctx] bounds a bound level by a global one: without such a
   constraint, no [D_a] with a bound component is below a global level.

   Under the valuation [v(a) = v(D_a)], which satisfies the lower bounds of
   [a], each upper bound holds wherever the declaration's own constraints
   hold, so the extended context is a conservative extension.  A use site
   supplies for [a] the level of [D_a] at its own instance, and that level
   gets its upper bounds by the same rule, so it is below [l] at that
   instance when the kernel's constraints on the instance prove it.  Without
   these bounds PCUIC cannot derive what the kernel checks on [D_a] itself,
   such as [max(i, j) <= k] from [i <= k] and [j <= k]. *)
let local_upper_bounds translation env auctx scope =
  let repr = UVars.AbstractContext.repr auctx in
  let is_var level = not (Option.is_empty (Univ.Level.var_index level)) in
  match Environ.push_context ~strict:false repr env with
  | exception UGraph.UniverseInconsistency _ -> Univ.UnivConstraints.empty
  | env ->
    let graph = UGraph.set_type_in_type false (Environ.universes env) in
    let _, bound = UVars.Instance.to_array (UVars.UContext.instance repr) in
    let bounded_by_global =
      Univ.UnivConstraints.exists
        (fun (u, _, v) ->
           is_var u && not (is_var v) && not (Univ.Level.is_set v))
        (UVars.UContext.univ_constraints repr)
    in
    let globals =
      if bounded_by_global then
        Univ.Level.Set.filter (fun l -> not (is_var l))
          translation.program_levels
      else Univ.Level.Set.empty
    in
    let candidates =
      Array.fold_left (fun levels l -> Univ.Level.Set.add l levels)
        globals bound
    in
    let definitions =
      CArray.fold_left_i
        (fun k definitions definition ->
           Univ.Level.Map.add (Univ.Level.var (scope.ls_n_orig + k))
             definition definitions)
        Univ.Level.Map.empty scope.ls_definitions
    in
    fresh_template_upper_bounds UGraph.check_leq graph candidates definitions
      Univ.UnivConstraints.empty

(* The abstract context of the declaration being quoted: [auctx] with the
   levels its scope added and their bounds, whose definitions go to
   [record], constrained below [top] when [below_top]. *)
let finish_abstract_context translation env ~below_top ~record auctx =
  let constrain auctx =
    if below_top then constrain_below_top translation.top auctx else auctx
  in
  match read_local_scope translation with
  | Some scope when Array.length scope.ls_definitions > 0 ->
    record (Array.to_list scope.ls_definitions);
    constrain
      (extend_abstract_context auctx scope
         (local_upper_bounds translation env auctx scope))
  | _ -> constrain auctx

let finish_constant_context translation env kn auctx =
  finish_abstract_context translation env ~below_top:true auctx
    ~record:(fun exprs ->
        translation.extended_constants <-
          Names.KerName.Map.add kn exprs translation.extended_constants)

(* The universe context and the variance of the inductive [kn] being quoted,
   after its bodies are quoted: [Some] context for a template or polymorphic
   inductive, [None] for a monomorphic one.

   A template inductive becomes polymorphic over its template context.  Its
   context is not constrained below [top].  Template universes are irrelevant
   for conversion in the kernel (kernel/indTyping.ml treats them as
   irrelevant), so every template level gets Irrelevant variance, and two
   occurrences with different template instances stay convertible in PCUIC
   (e.g. list@{BinList.21} A vs list@{List.21} A).

   In both cases the context gets the levels the declaration's scope added,
   and the variance gets one entry per level of the finished context.  An
   added level gets Irrelevant variance.  At every use site the quoter
   supplies for an added level the representative of its definition [D_a] at
   that use's own instance ([extend_instance_for]), so an added level is
   determined by the original levels of the instance.  Comparing two instances
   under this variance compares their original levels with the declaration's
   own variance, as the kernel compares them, and puts no condition on the
   added levels: no relation between original levels follows that the kernel
   does not have.  Whether the constructors respect the declared variance is
   checked by PCUIC itself ([cstr_respects_variance] and
   [ind_respects_variance] in common/theories/EnvironmentTyping.v), so a
   variance the bodies do not respect causes a rejection, not an
   acceptance. *)
let finish_inductive translation env kn mib =
  let finish ~template auctx variance =
    let auctx =
      finish_abstract_context translation env ~below_top:(not template) auctx
        ~record:(fun exprs ->
            translation.extended_inductives <-
              Names.KerName.Map.add kn exprs translation.extended_inductives)
    in
    let size = snd (UVars.AbstractContext.size auctx) in
    let variance =
      Option.map
        (fun variance ->
           Array.append variance
             (Array.make (size - Array.length variance)
                UVars.Variance.Irrelevant))
        variance
    in
    Some auctx, variance
  in
  match mib.mind_template, mib.mind_universes with
  | Some template, _ ->
    finish ~template:true (named_template_context template) (Some [||])
  | None, Polymorphic auctx -> finish ~template:false auctx mib.mind_variance
  | None, Monomorphic -> None, mib.mind_variance

let template_universe_level translation env universe =
  let universe =
    simplify_template_universe
      (normalize_global_universe translation
         (simplify_template_universe universe))
  in
  let components = Univ.Universe.repr universe in
  (* Every level of the program other than [top] is at most [top], so a
     maximum with a [top] component and no [top+n] component is [top].  This
     keeps [top] out of the fresh levels. *)
  let is_top level = Univ.Level.equal level translation.top in
  if List.exists
       (fun (level, shift) -> Int.equal shift 0 && is_top level) components
  && not
       (List.exists (fun (level, shift) -> shift > 0 && is_top level)
          components)
  then translation.top
  else
  match Univ.Universe.level universe with
  | Some level -> level
  | None ->
    if universe_has_var_component universe then begin
      (* Polymorphic scope: components include bound universe variables. *)
      match read_local_scope translation with
      | Some scope -> local_fresh_var scope universe
      | None ->
        CErrors.user_err
          Pp.(str "Quoting algebraic template universe "
              ++ Univ.Universe.pr Univ.Level.raw_pr universe
              ++ str " with bound-variable components, in declaration "
              ++ str translation.state.ds_name
              ++ str ", outside any polymorphic declaration, is not supported.")
    end else begin
      let graph =
        UGraph.set_type_in_type false (read_universe_graph translation env)
      in
      (* Prefer reusing an already-declared level when the universe graph
         proves the algebraic expression equal to one of its components. *)
      let graph_equal_level =
        match
          UGraph.check_declared_universes graph
            (Univ.Universe.levels ~init:Univ.Level.Set.empty universe)
        with
        | Error _ -> None
        | Ok () ->
          List.find_map
            (fun (level, shift) ->
               if Int.equal shift 0
                  && UGraph.check_eq graph universe (Univ.Universe.make level)
               then Some level
               else None)
            components
      in
      match graph_equal_level with
      | Some level -> level
      | None ->
        (* Global scope: introduce one fresh global level [l] with the
           lower-bound constraints [component <= l] (or [< l] for a unit
           shift).  Setting [v(l)] to the largest [v(component_i) + shift_i]
           satisfies these, so adding [l] is a conservative extension of the
           universe graph. *)
        match Univ.Universe.Map.find_opt universe translation.universe_levels with
        | Some level -> level
        | None ->
          let level = fresh_template_level graph translation in
          let constraints =
            add_lower_bound_constraints level components
              translation.fresh_constraints
          in
          translation.universe_levels <-
            Univ.Universe.Map.add universe level translation.universe_levels;
          translation.fresh_definitions <-
            Univ.Level.Map.add level universe translation.fresh_definitions;
          translation.program_levels <-
            Univ.Universe.levels
              ~init:(Univ.Level.Set.add level translation.program_levels)
              universe;
          translation.fresh_constraints <- constraints;
          level
    end

(* At a use site [c@{pu}] of a declaration [kn] whose abstract universe
   context we extended ([table] is [extended_constants] or
   [extended_inductives]), append one level per recorded component
   expression, instantiated at the use's own instance. *)
let extend_instance_for translation env table kn pu =
  note_declaration_reference translation kn;
  match Names.KerName.Map.find_opt kn table with
  | None -> pu
  | Some exprs ->
    List.fold_left
      (fun instance e ->
         let level =
           template_universe_level translation env
             (UVars.subst_instance_universe instance e)
         in
         let quals, levels = UVars.Instance.to_array instance in
         UVars.Instance.of_array (quals, Array.append levels [| level |]))
      pu exprs

let extend_constant_instance translation env kn pu =
  extend_instance_for translation env translation.extended_constants kn pu

let extend_inductive_instance translation env (mind, _) pu =
  extend_instance_for translation env translation.extended_inductives
    (Names.MutInd.canonical mind) pu

(* [~canonical] is for an occurrence where PCUIC compares the instance
   exactly: a [Case] ([`Case]), or an [Ind]/[Construct] applied to fewer
   arguments than its full arity ([`Partial]; [global_variance_gen],
   PCUICEquality.v:46-74).  The kernel stores no instance there, and the
   instance inferred from the arguments' types is fixed at quotation: after
   PCUIC substitutes into the arguments, one kernel term can carry two
   instances (a [match .. in prod _ _] reached two ways; [eq@{Set} Z] against
   [eq@{RelationClasses.21} Z] in [Z.eq_equiv]).  So a level bound by a given
   argument becomes the program's top level, which is above every argument
   type and does not depend on it.
   - [`Case]: every bound level.  The instance only types the predicate's
     binder and the parameters, which are below [top].
   - [`Partial]: the levels that are not in the inductive's conclusion sort.
     A level in the conclusion reaches the occurrence's type, where [top]
     could exceed what the context allows, so it keeps the inferred level. *)
let template_instance translation ?canonical ~mib env sigma args
    default_instance =
  match mib.mind_template with
  | None -> default_instance
  | Some template ->
    let _, bound_levels =
      UVars.Instance.to_array
        (UVars.UContext.instance
           (UVars.AbstractContext.repr template.template_context))
    in
    let concl_levels = Sorts.levels template.template_concl in
    (* A template constraint bounds its level from above by a global level
       (kernel/inductive.ml, [instantiate_template_constraints]), which [top]
       would violate.  Such levels keep the inferred instance. *)
    let constrained_levels =
      Univ.UnivConstraints.fold
        (fun (u, _, _) levels -> Univ.Level.Set.add u levels)
        (UVars.UContext.univ_constraints
           (UVars.AbstractContext.repr template.template_context))
        Univ.Level.Set.empty
    in
    let keeps_inference kind bound =
      Univ.Level.Set.mem bound constrained_levels
      || (kind = `Partial && Univ.Level.Set.mem bound concl_levels)
    in
    (* The canonical substitution maps each level bound by a given argument
       to [top] and each level bound by a missing argument to its default,
       as the kernel does.  It reads no argument. *)
    let canonical_level =
      match canonical with
      | Some kind ->
        let _, _, (_, substitution) =
          Inductive.instantiate_template_universes mib
            (List.map
               (fun _ ~default:_ ->
                  Inductive.TemplateUniv (Univ.Universe.make translation.top))
               (Array.to_list args))
        in
        (fun bound ->
           match Univ.Level.var_index bound with
           | _ when keeps_inference kind bound -> None
           | None -> assert false
           | Some index ->
             Some
               (template_universe_level translation env
                  (Int.Map.get index substitution)))
      | None -> (fun _ -> None)
    in
    let canonical_levels = Array.map canonical_level bound_levels in
    let needs_inference =
      Array.exists Option.is_empty canonical_levels
    in
    (* Mirror the kernel's [make_param_univs] (kernel/typeops.ml:417-431):
       the template universe bound by a parameter is the conclusion sort of
       the argument's type viewed as an arity, so a parameter such as
       [P : A -> Type@{u}] (e.g. [sigT]) binds [u]. *)
    let argument_universe arg ~default:_ =
      let type_of_argument =
        try retype_template_argument translation env sigma arg
        with Retyping.RetypeError _ ->
          CErrors.user_err
            Pp.(str "Could not retype a template-inductive parameter.")
      in
      match snd (Reduction.dest_arity env type_of_argument) with
      | Sorts.Prop -> Inductive.TemplateProp
      | Sorts.Set -> Inductive.TemplateUniv Univ.Universe.type0
      | Sorts.Type universe -> Inductive.TemplateUniv universe
      | Sorts.QSort (quality, universe) ->
        Inductive.TemplateAboveProp (quality, universe)
      | Sorts.SProp | exception Reduction.NotArity ->
        CErrors.user_err
          Pp.(str "Could not infer a template-inductive universe from its parameter.")
    in
    (* Retype the arguments only when some level is inferred from them. *)
    let universe_substitution =
      if needs_inference then
        let _, _, (_, substitution) =
          Inductive.instantiate_template_universes mib
            (List.map argument_universe (Array.to_list args))
        in
        substitution
      else Int.Map.empty
    in
    let levels =
      CArray.map2_i
        (fun _ bound canonical_level ->
           match canonical_level with
           | Some level -> level
           | None ->
             match Univ.Level.var_index bound with
             | None -> assert false
             | Some index ->
               template_universe_level translation env
                 (Int.Map.get index universe_substitution))
        bound_levels canonical_levels
    in
    UVars.Instance.of_array ([||], levels)

(* The levels and the extra constraints of the universe context of a
   translated program whose quoted terms use [univs].

   A fresh level [a] stands for the algebraic universe [D_a] it was minted
   for, and has only the lower bounds [c <= a] of its components.  Add its
   upper bounds: [a <= l] for each kept level or fresh level [l] with
   [D_a <= D_l] in the source graph, checked with type-in-type disabled
   ([D_l = l] for a kept level).  Under the valuation [v(a) = v(D_a)] each of
   them holds, so the extension stays conservative.  Without them PCUIC cannot
   derive what the kernel checks on [D_a] itself, such as a record field of
   sort [max(u, v)] below the record's sort [max(u, v, w)] (a record whose
   field sort is a strict sub-maximum).

   [top] is a new level with only incoming edges, so adding it keeps the graph
   acyclic: a conservative extension. *)
let program_universes translation env univs =
  let univs =
    Univ.Level.Set.filter
      (fun l -> Option.is_empty (Univ.Level.var_index l))
      (Univ.Level.Set.union univs translation.program_levels)
  in
  let constraints =
    Univ.Level.Set.fold
      (fun level constraints ->
         Univ.UnivConstraints.add
           (Univ.Level.set, Univ.UnivConstraint.Le, level) constraints)
      translation.default_levels translation.fresh_constraints
  in
  let constraints =
    fresh_template_upper_bounds UGraph.check_leq
      (UGraph.set_type_in_type false (Environ.universes env))
      univs translation.fresh_definitions constraints
  in
  let constraints =
    Univ.Level.Set.fold
      (fun level constraints ->
         Univ.UnivConstraints.add
           (level, Univ.UnivConstraint.Lt, translation.top) constraints)
      (Univ.Level.Set.remove translation.top
         (Univ.Level.Set.add Univ.Level.set univs))
      constraints
  in
  Univ.Level.Set.add translation.top univs, constraints
