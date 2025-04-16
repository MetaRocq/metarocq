open Univ
open UVars
open Entries
open Names
open Redops
open Genredexpr
open Pp (* this adds the ++ to the current scope *)

open Tm_util
open Denoter
open Constr_quoter
open Constr_denoter
open Template_monad


let reduce_all env evm trm =
  EConstr.to_constr evm (Reductionops.nf_all env evm (EConstr.of_constr trm))

let unquote_reduction_strategy env evm trm (* of type reductionStrategy *) : Redexpr.red_expr =
  let (trm, args) = app_full trm [] in
  (* from g_tactic.ml4 *)
  let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
  if constr_equall trm tcbv then Cbv default_flags
  else if constr_equall trm tcbn then Cbn default_flags
  else if constr_equall trm thnf then Hnf
  else if constr_equall trm tall then Cbv all_flags
  else if constr_equall trm tlazy then Lazy all_flags
  else if constr_equall trm tunfold then
    match args with
    | name (* to unfold *) :: _ ->
       let name = reduce_all env evm name in
       let name = unquote_kn name in
       Unfold [Locus.AllOccurrences, Tacred.evaluable_of_global_reference env (GlobRef.ConstRef (Constant.make1 name))]
    | _ -> bad_term_verb trm "unquote_reduction_strategy"
  else not_supported_verb trm "unquote_reduction_strategy"

let unquote_hint_locality env evm trm (* of type Hints.hint_locality *) : Hints.hint_locality =
  let (trm, args) = app_full trm [] in
  if constr_equall trm thints_local then Hints.Local
  else if constr_equall trm thints_export then Hints.Export
  else if constr_equall trm thints_global then Hints.SuperGlobal
  else not_supported_verb trm "unquote_hint_locality"

let denote_mind_entry_finite trm =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if constr_equall h cFinite then Declarations.Finite
    else if  constr_equall h cCoFinite then Declarations.CoFinite
    else if  constr_equall h cBiFinite then Declarations.BiFinite
    else not_supported_verb trm "denote_mind_entry_finite"
  | _ -> bad_term_verb trm "denote_mind_entry_finite"


let unquote_map_option f trm =
  let (h,args) = app_full trm [] in
  if constr_equall h cSome then
    match args with
      _ :: x :: [] -> Some (f x)
    | _ -> bad_term trm
  else if constr_equall h cNone then
    match args with
      _ :: [] -> None
    | _ -> bad_term trm
  else
    not_supported_verb trm "unquote_map_option"

let unquote_option = unquote_map_option (fun x -> x)

let rec unquote_pos trm : int =
  let (h,args) = app_full trm [] in
  match args with
    [x] ->
    if constr_equall h cposI then
      (2 * unquote_pos x + 1)
    else if constr_equall h cposO then
      (2 * unquote_pos x)
    else not_supported_verb trm "unquote_pos"
  | [] ->
    if constr_equall h cposzero then 1
    else not_supported_verb trm "unquote_pos"
  | _ -> bad_term_verb trm "unquote_pos"

let unquote_Z trm : int =
  let (h,args) = app_full trm [] in
  match args with
    [x] ->
     if constr_equall h cZpos then unquote_pos x
     else if constr_equall h cZneg then - unquote_pos x
     else not_supported_verb trm "unquote_pos"
  | [] ->
    if constr_equall h cZ0 then 0
    else not_supported_verb trm "unquote_pos"
  | _ -> bad_term_verb trm "unquote_pos"

let unquote_constraint_type trm (* of type constraint_type *) : constraint_type =
  let (h,args) = app_full trm [] in
  match args with
    [x] ->
    if constr_equall h tunivLe then
      let n = unquote_Z x in
      if n = 0 then Univ.Le
      else Univ.Lt
    else not_supported_verb trm "unquote_constraint_type"
  | [] ->
    if constr_equall h tunivEq then Univ.Eq
    else not_supported_verb trm "unquote_constraint_type"
  | _ -> bad_term_verb trm "unquote_constraint_type"


let unquote_univ_constraint evm c (* of type univ_constraint *) : _ * univ_constraint =
  let c, l2 = unquote_pair c in
  let l1, c = unquote_pair c in
  let evm, l1 = unquote_level evm l1 in
  let evm, l2 = unquote_level evm l2 in
  let c = unquote_constraint_type c in
  evm, (l1, c, l2)


(* set given by MSets.MSetWeakList.Make *)
let _unquote_set trm =
  let (h, args) = app_full trm [] in
  (* h supposed to be Mkt, the constructor of the record *)
  match args with
  | list :: ok :: [] -> unquote_list list
  | _ -> not_supported_verb trm "unquote_set"


let unquote_constraints env evm c (* of type constraints *) : _ * Constraints.t =
  let c = reduce_all env evm (constr_mkApp (tConstraintSet_elements, [| c |])) in
  let c = unquote_list c in
  List.fold_left (fun (evm, set) c -> let evm, c = unquote_univ_constraint evm c in evm, Constraints.add c set)
                 (evm, Constraints.empty) c

(* let denote_ucontext evm trm (* of type UContext.t *) : _ * UContext.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_universe_instance evm i in
  let evm, c = unquote_constraints evm c in
  evm, Univ.UContext.make (i, c) *)

let unquote_levelset env evm c (* of type Level.Set.t *) : _ * Level.Set.t =
  let c = reduce_all env evm (constr_mkApp (tLevelSet_elements, [| c |])) in
  let c = unquote_list c in
  List.fold_left (fun (evm, set) c -> let evm, c = unquote_level evm c in evm, Level.Set.add c set)
                 (evm, Level.Set.empty) c
let denote_ucontextset env evm trm (* of type ContextSet.t *) : _ * ContextSet.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_levelset env evm i in
  let evm, c = unquote_constraints env evm c in
  evm, (i, c)

let denote_names evm trm : _ * Name.t array =
  let l = unquote_list trm in
  evm, CArray.map_of_list unquote_name l

let denote_ucontext env evm trm (* of type UContext.t *) : _ * UVars.UContext.t =
  let l, c = unquote_pair trm in
  let evm, names = denote_names evm l in
  let l, c = unquote_pair c in
  let l = unquote_list l in
  let evm, vars = map_evm unquote_level evm l in
  let evm, c = unquote_constraints env evm c in
  let inst = Instance.of_array ([||], Array.of_list vars) in
  evm, (UVars.UContext.make { UVars.quals = [||]; UVars.univs = names} (inst, c))

let denote_aucontext env evm trm (* of type AbstractContext.t *) : _ * UVars.AbstractContext.t =
  let i, c = unquote_pair trm in
  let l = unquote_list i in
  let vars = List.mapi (fun i l -> Level.var i) l in
  let vars = Instance.of_array ([||], Array.of_list vars) in
  let evm, c = unquote_constraints env evm c in
  evm, snd (abstract_universes (UContext.make { UVars.quals = [||]; UVars.univs = CArray.map_of_list unquote_name l} (vars, c)))

let denote_variance trm (* of type Variance *) : Variance.t =
  if constr_equall trm cIrrelevant then Variance.Irrelevant
  else if constr_equall trm cCovariant then Variance.Covariant
  else if constr_equall trm cInvariant then Variance.Invariant
  else not_supported_verb trm "denote_variance"


let denote_variance evm trm (* of type Variance.t list *) : _ * Variance.t array =
  let variances = List.map denote_variance (unquote_list trm) in
  evm, Array.of_list variances

let _denote_variances evm trm : _ * Variance.t array option =
  match unquote_option trm with
  | None -> evm, None
  | Some t -> let evm, v = denote_variance evm t in
      evm, Some v

(* todo : stick to Rocq implem *)
type universe_context_type =
  | Monomorphic_uctx of ContextSet.t
  | Polymorphic_uctx of AbstractContext.t

let _to_entry_inductive_universes = function
  | Monomorphic_uctx ctx -> UState.Monomorphic_entry ctx
  | Polymorphic_uctx ctx -> UState.Polymorphic_entry (AbstractContext.repr ctx)

let _denote_universes_decl env evm trm (* of type universes_decl *) : _ * universe_context_type =
  let (h, args) = app_full trm [] in
  match args with
  | ctx :: [] -> if constr_equall h cMonomorphic_ctx then
                   let evm, ctx = denote_ucontextset env evm ctx in
                   evm, Monomorphic_uctx ctx
                 else if constr_equall h cPolymorphic_ctx then
                   let evm, ctx = denote_aucontext env evm ctx in
                   evm, Polymorphic_uctx ctx
                 else
                   not_supported_verb trm "denote_universes_decl"
  | _ -> bad_term_verb trm "denote_universes_decl"

let denote_universes_entry env evm trm (* of type universes_entry *) : _ * UState.universes_entry =
  let (h, args) = app_full trm [] in
  match args with
  | ctx :: [] -> if constr_equall h cMonomorphic_entry then
                   let evm, ctx = denote_ucontextset env evm ctx in
                   evm, UState.Monomorphic_entry ctx
                 else if constr_equall h cPolymorphic_entry then
                   let evm, ctx = denote_ucontext env evm ctx in
                   evm, UState.Polymorphic_entry ctx
                 else
                   not_supported_verb trm "denote_universes_entry"
  | _ -> bad_term_verb trm "denote_universes_entry"


let unquote_one_inductive_entry env evm trm (* of type one_inductive_entry *) : _ * Entries.one_inductive_entry =
  let (h,args) = app_full trm [] in
  if constr_equall h tBuild_one_inductive_entry then
    match args with
    | id::ar::cnames::ctms::[] ->
       let id = unquote_ident id in
       let evm, ar = denote_term env evm ar in
       let cnames = List.map unquote_ident (unquote_list cnames) in
       let evm, ctms = map_evm (denote_term env) evm (unquote_list ctms) in
       evm, { mind_entry_typename = id ;
              mind_entry_arity = ar;
              mind_entry_consnames = cnames;
              mind_entry_lc = ctms }
    | _ -> bad_term_verb trm "unquote_one_inductive_entry"
  else
    not_supported_verb trm "unquote_one_inductive_entry"

let map_option f o =
  match o with
  | Some x -> Some (f x)
  | None -> None

let denote_decl env evm d =
  let (h, args) = app_full d [] in
  if constr_equall h tmkdecl then
    match args with
    | _ty :: name :: body :: typ :: [] ->
      let name = unquote_aname name in
      let evm, ty = denote_term env evm typ in
      let evm, decl = (match unquote_option body with
      | None -> evm, Context.Rel.Declaration.LocalAssum (name, ty)
      | Some body -> let evm, body = denote_term env evm body in
        evm, Context.Rel.Declaration.LocalDef (name, body, ty))
      in Environ.push_rel decl env, evm, decl
    | _ -> bad_term_verb d "denote_decl"
  else bad_term_verb d "denote_decl"

let denote_context env evm ctx =
  fold_env_evm_right denote_decl env evm (unquote_list ctx)

let unquote_mutual_inductive_entry env evm trm (* of type mutual_inductive_entry *) : _ * _ * Entries.mutual_inductive_entry =
  let (h,args) = app_full trm [] in
  if constr_equall h tBuild_mutual_inductive_entry then
    match args with
    | record::finite::params::inds::univs::template::variance::priv::[] ->
       let record = map_option (map_option (fun x -> [|x|])) (unquote_map_option (unquote_map_option unquote_ident) record) in
       let finite = denote_mind_entry_finite finite in
       let envpars, evm, params = denote_context env evm params in
       let evm, inds = map_evm (unquote_one_inductive_entry env) evm (unquote_list inds) in
       let evm, univs = denote_universes_entry env evm univs in
       let template = unquote_bool template in
       let variance = unquote_map_option
           (fun v -> CArray.map_of_list (unquote_map_option unquote_variance) (unquote_list v))
           variance
       in
       let priv = unquote_map_option unquote_bool priv in
       let ctx, univs = match univs with
         | UState.Monomorphic_entry ctx ->
           if template then
             let mk_anon_names u =
               let qs, us = UVars.Instance.to_array u in
               { UVars.quals = Array.make (Array.length qs) Anonymous; UVars.univs = Array.make (Array.length us) Anonymous}
             in
             let uctx = UVars.UContext.of_context_set mk_anon_names Sorts.QVar.Set.empty ctx in
             let default_univs = UVars.UContext.instance uctx in
             Univ.ContextSet.empty, Entries.Template_ind_entry { uctx; default_univs }
          else ctx, Entries.Monomorphic_ind_entry
       | UState.Polymorphic_entry uctx -> Univ.ContextSet.empty, Entries.Polymorphic_ind_entry uctx
       in
       evm, ctx, { mind_entry_record = record;
              mind_entry_finite = finite;
              mind_entry_params = params;
              mind_entry_inds = inds;
              mind_entry_universes = univs;
              mind_entry_variance = variance;
              mind_entry_private = priv }
    | _ -> bad_term_verb trm "unquote_mutual_inductive_entry"
  else
    not_supported_verb trm "unquote_mutual_inductive_entry"

let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (infer_univs : bool) (mind: Constr.t) : Evd.evar_map =
  let mind = reduce_all env evm mind in
  let evm' = Evd.from_env env in
  let evm', ctx, mind = unquote_mutual_inductive_entry env evm' mind in
  let () = Global.push_context_set ctx in
  let evm, mind =
    if infer_univs then
      let ctx, mind = Tm_util.RetypeMindEntry.infer_mentry_univs env evm' mind in
      debug (fun () -> Pp.(str "Declaring universe context " ++ Univ.ContextSet.pr UnivNames.pr_level_with_global_universes ctx));
      Global.push_context_set ctx;
      Evd.merge_context_set Evd.UnivRigid evm ctx, mind
    else evm, mind
  in
  let names = (UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders) in
  let primitive_expected =
    match mind.mind_entry_record with
    | Some (Some _) -> true
    | _ -> false
  in
  let ind_kn = DeclareInd.declare_mutual_inductive_with_eliminations mind names [] in
  if primitive_expected
  then begin
    let open Record.Internal in
    let dflt_pf = { pf_coercion = false; pf_instance = false; pf_priority = None; pf_locality = OptDefault; pf_canonical = false; pf_reversible = false} in
    let decl_projs i oie =
      let ind = (ind_kn, i) in
      let inhabitant_id = List.hd oie.mind_entry_consnames in
      let fields, _ = Term.decompose_prod_decls (List.hd oie.mind_entry_lc) in
      let fieldimpls = List.map (fun _ -> []) fields in
      let pfs = List.map (fun _ -> dflt_pf) fields in
      let projections = Record.Internal.declare_projections ind ~kind:Decls.Definition ~inhabitant_id pfs fieldimpls in
      let struc = Structures.Structure.make (Global.env()) ind projections in
      Record.Internal.declare_structure_entry struc
    in
    List.iteri decl_projs mind.mind_entry_inds
  end;
  evm

let not_in_tactic s =
  CErrors.user_err  (str ("You can not use " ^ s ^ " in a tactic."))

let rec run_template_program_rec ~poly ?(intactic=false) (k : Constr.t Plugin_core.cont) ~st env ((evm, pgm) : Evd.evar_map * Constr.t) : Plugin_core.coq_state =
  let (kind, universes) = next_action env evm pgm in
  match kind with
    TmReturn h ->
    let (evm, _) = Typing.type_of env evm (EConstr.of_constr h) in
    k ~st env evm h
  | TmBind (a,f) ->
    run_template_program_rec ~poly ~intactic:intactic
      (fun ~st env evm ar ->
         run_template_program_rec ~poly ~intactic:intactic k env ~st (evm, Constr.mkApp (f, [|ar|]))) env ~st (evm, a)
 | TmVariable (name, typ) ->
    if intactic then not_in_tactic "tmVariable"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let kind = Decls.IsAssumption Decls.Definitional in
      (* FIXME: better handling of evm *)
      let empty_mono_univ_entry = UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders in
      Declare.declare_variable ~typing_flags:None ~name ~kind (SectionLocalAssum { typ; impl=Glob_term.Explicit; univs=empty_mono_univ_entry });
      let env = Global.env () in
      k ~st env evm (Lazy.force unit_tt)
  | TmDefinition (opaque,name,s,typ,body) ->
    if intactic
    then not_in_tactic "tmDefinition"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let opaque = unquote_bool (reduce_all env evm opaque) in
      let evm, typ = (match unquote_option s with Some s -> let red = unquote_reduction_strategy env evm s in Plugin_core.reduce env evm red typ | None -> evm, typ) in
      let cinfo = Declare.CInfo.make ~name () ~typ:(Some (EConstr.of_constr typ)) in
      let info = Declare.Info.make ~poly ~kind:(Decls.IsDefinition Decls.Definition) () in
      let n = Declare.declare_definition ~cinfo ~info ~opaque ~body:(EConstr.of_constr body) evm in
      let env = Global.env () in
      (* Careful, universes in evm were modified for the declaration of def *)
      let evm = Evd.from_env env in
      let evm, c = Evd.fresh_global (Global.env ()) evm n in
      k ~st env evm (EConstr.to_constr evm c)
  | TmDefinitionTerm (opaque, name, typ, body) ->
    if intactic
    then not_in_tactic "tmDefinition"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let opaque = unquote_bool (reduce_all env evm opaque) in
      let evm,body = denote_term env evm (reduce_all env evm body) in
      let evm,typ =
        match unquote_option typ with
        | None -> (evm, None)
        | Some t ->
          let (evm, t) = denote_term env evm (reduce_all env evm t) in
          (evm, Some t)
      in
      Plugin_core.run ~st
        (Plugin_core.tmDefinition name ~poly ~opaque typ body) env evm
        (fun ~st env evm res -> k ~st env evm (quote_kn res))
  | TmLemmaTerm (name, typ) ->
    let ident = unquote_ident (reduce_all env evm name) in
    let evm,typ = denote_term env evm (reduce_all env evm typ) in
    Plugin_core.run ~st
      (Plugin_core.tmLemma ident ~poly typ) env evm
      (fun ~st env evm kn -> k ~st env  evm (quote_kn kn))

  | TmAxiom (name,s,typ) ->
    if intactic
    then not_in_tactic "tmAxiom"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let evm, typ = (match unquote_option s with Some s -> let red = unquote_reduction_strategy env evm s in Plugin_core.reduce env evm red typ | None -> evm, typ) in
      let univs = Evd.univ_entry ~poly evm in
      let entry = Declare.parameter_entry ~univs typ in
      let param = Declare.ParameterEntry entry in
      let n = Declare.declare_constant ~name ~kind:Decls.(IsDefinition Definition) param in
      let env = Global.env () in
      k ~st env evm (Constr.mkConstU (n, UVars.Instance.empty))
  | TmAxiomTerm (name,typ) ->
    if intactic
    then not_in_tactic "tmAxiom"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let evm,typ = denote_term env evm (reduce_all env evm typ) in
      Plugin_core.run ~st (Plugin_core.tmAxiom name ~poly typ) env evm
        (fun ~st a b c -> k ~st a b (quote_kn c))

  | TmLemma (name,typ) ->
    let name = reduce_all env evm name in
    let kind = Decls.(IsDefinition Definition) in
    let hole = CAst.make (Constrexpr.CHole (None)) in
    let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls ~program_mode:true env evm hole (EConstr.of_constr typ) in
    let ident = unquote_ident name in
    RetrieveObl.check_evars env evm;
    let obls, _, c, cty = RetrieveObl.retrieve_obligations env ident evm 0 c (EConstr.of_constr typ) in
    (* let evm = Evd.minimize_universes evm in *)
    let uctx = Evd.ustate evm in
    let obl_hook = Declare.Hook.make_g (fun { Declare.Hook.S.dref = gr } pm ->
        let env = Global.env () in
        let evm = Evd.from_env env in
        let evm, t = Evd.fresh_global env evm gr in
        k ~st:pm env evm (EConstr.to_constr evm t)) in  (* todo better *)
    let cinfo = Declare.CInfo.make ~name:ident ~typ:cty () in
    let info = Declare.Info.make ~poly ~kind () in
    let pm, _ = Declare.Obls.add_definition ~pm:st ~cinfo ~info ~body:c ~uctx ~obl_hook ~opaque:false obls in
    pm

  | TmQuote trm ->
    (* user should do the reduction (using tmEval) if they want *)
    let qt = quote_term env evm trm
    in k ~st env evm qt
  | TmQuoteRecTransp  (bypass, trm) ->
    let bypass = unquote_bool (reduce_all env evm bypass) in
    let qt = quote_term_rec ~bypass ~with_universes:true env evm trm in
    k ~st env evm qt
  | TmQuoteInd (name, strict) ->
    let kn = unquote_kn (reduce_all env evm name) in
    let kn = MutInd.make1 kn in
    let mib = Environ.lookup_mind kn env in
    let t = quote_mind_decl env evm kn mib in
    let _, args = Constr.destApp t in
    (match args with
    | [|decl|] -> k ~st env evm decl
    | _ -> bad_term_verb t "anomaly in quoting of inductive types")
  | TmQuoteConst (name, bypass, strict) ->
    let name = unquote_kn (reduce_all env evm name) in
    let bypass = unquote_bool (reduce_all env evm bypass) in
    let cd = Environ.lookup_constant (Constant.make1 name) env in
    let cb = quote_constant_body bypass env evm cd in
    k ~st env evm cb
  | TmQuoteUnivs ->
    let univs = Environ.universes env in
    k ~st env evm (quote_ugraph univs)
  | TmQuoteModule id ->
    let id = unquote_string (reduce_all env evm id) in
    Plugin_core.run ~st (Plugin_core.tmQuoteModule (Libnames.qualid_of_string id)) env evm
      (fun ~st env evm l ->
         let l = List.map quote_global_reference l in
         let l = to_coq_listl tglobal_reference l in
         k ~st env evm l)
  | TmQuoteModFunctor id ->
    let id = unquote_string (reduce_all env evm id) in
    Plugin_core.run ~st (Plugin_core.tmQuoteModFunctor (Libnames.qualid_of_string id)) env evm
      (fun ~st env evm l ->
         let l = List.map quote_global_reference l in
         let l = to_coq_listl tglobal_reference l in
         k ~st env evm l)
  | TmQuoteModType id ->
    let id = unquote_string (reduce_all env evm id) in
    Plugin_core.run ~st (Plugin_core.tmQuoteModType (Libnames.qualid_of_string id)) env evm
      (fun ~st env evm l ->
         let l = List.map quote_global_reference l in
         let l = to_coq_listl tglobal_reference l in
         k ~st env evm l)
  | TmPrint trm ->
    Feedback.msg_info (Printer.pr_constr_env env evm trm);
    k ~st env evm (Lazy.force unit_tt)
  | TmMsg msg ->
     let msg = unquote_string (reduce_all env evm msg) in
     Plugin_core.run ~st (Plugin_core.tmMsg msg) env evm
      (fun ~st env evm _ -> k ~st env evm (Lazy.force unit_tt))
  | TmFail trm ->
    let err = unquote_string (reduce_all env evm trm) in
    CErrors.user_err (str err)
  | TmLocate id ->
    let id = unquote_string (reduce_all env evm id) in
    Plugin_core.run ~st (Plugin_core.tmLocateString id) env evm
      (fun ~st env evm l ->
         let l = List.map quote_global_reference l in
         let l = to_coq_listl tglobal_reference l in
         k ~st env evm l)
  | TmLocateModule id ->
    let id = unquote_string (reduce_all env evm id) in
    Plugin_core.run ~st (Plugin_core.tmLocateModuleString id) env evm
      (fun ~st env evm l ->
         let l = List.map quote_modpath l in
         let l = to_coq_listl tmodpath l in
         k ~st env evm l)
  | TmLocateModType id ->
    let id = unquote_string (reduce_all env evm id) in
    Plugin_core.run ~st (Plugin_core.tmLocateModTypeString id) env evm
      (fun ~st env evm l ->
         let l = List.map quote_modpath l in
         let l = to_coq_listl tmodpath l in
         k ~st env evm l)
  | TmCurrentModPath ->
    let mp = Lib.current_mp () in
    let s = quote_modpath mp in
    k ~st env evm s
  | TmEval (s, trm) ->
    let red = unquote_reduction_strategy env evm (reduce_all env evm s) in
    let (evm, trm) = Plugin_core.reduce env evm red trm
    in k ~st env evm trm
  | TmEvalTerm (s,trm) ->
    let red = unquote_reduction_strategy env evm (reduce_all env evm s) in
    let evm,trm = denote_term env evm (reduce_all env evm trm) in
    Plugin_core.run ~st (Plugin_core.tmEval red trm) env evm
      (fun ~st env evm trm -> k ~st env evm (quote_term env evm trm))
  | TmMkInductive (b, mind) ->
    if intactic
    then not_in_tactic "tmMkInductive"
    else
      let infer_univs = unquote_bool (reduce_all env evm b) in
      let evm = declare_inductive env evm infer_univs mind in
      let env = Global.env () in
      k ~st env evm (Lazy.force unit_tt)
  | TmUnquote t ->
    begin
       try
         (*debug Pp.(fun () -> str"Unquoting:" ++ Printer.pr_constr_env env evm t);*)
         let evm, t' = denote_term env evm (reduce_all env evm t) in
         (* Typecheck. *)
         let evm, typ = Typing.type_of env evm (EConstr.of_constr t') in
         let evm, typ = Evarsolve.refresh_universes (Some false) env evm typ in
         (* Solve evars. *)
         let evm = Typeclasses.resolve_typeclasses env evm in
         let t' = Evarutil.nf_evars_universes evm t' in
         (* Package the unquoted term with its type. *)
         let make_typed_term typ term evm =
           match Lazy.force texistT_typed_term with
           | GlobRef.ConstructRef ctor ->
              let (evm,c) = Evd.fresh_global (Global.env ()) evm (Lazy.force texistT_typed_term) in
              let term = Constr.mkApp
               (EConstr.to_constr evm c, [|EConstr.to_constr ~abort_on_undefined_evars:false evm typ; t'|]) in
             let evm, _ = Typing.type_of env evm (EConstr.of_constr term) in
               (env, evm, term)
           | _ -> CErrors.anomaly (str "texistT_typed_term does not refer to a constructor")
         in
         let env, evm, term = make_typed_term typ t' evm in
         k ~st env evm term
        with Reduction.NotArity -> CErrors.user_err (str "unquoting ill-typed term")
      end
  | TmUnquoteTyped (typ, t) ->
       let evm, t' = denote_term env evm (reduce_all env evm t) in
       (* Typecheck. *)
       let evm = Typing.check env evm (EConstr.of_constr t') (EConstr.of_constr typ) in
       (* Solve evars. *)
       let evm = Typeclasses.resolve_typeclasses env evm in 
       let t' = Evarutil.nf_evars_universes evm t' in
       k ~st env evm t'
  | TmFreshName name ->
    let name = reduce_all env evm name in
    let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
    k ~st env evm (quote_ident name')
  | TmExistingInstance (locality, gr) ->
    let locality = reduce_all env evm locality in
    let locality = unquote_hint_locality env evm locality in
    let gr = reduce_all env evm gr in
    let gr = unquote_global_reference gr in
    Plugin_core.run ~st (Plugin_core.tmExistingInstance locality gr) env evm
      (fun ~st env evm () -> k ~st env evm (Lazy.force unit_tt))
  | TmInferInstance (s, typ) ->
    begin
      let evm, typ =
        match unquote_option s with
          Some s ->
          let red = unquote_reduction_strategy env evm s in
          Plugin_core.reduce env evm red typ
        | None -> evm, typ in
      try
        let (evm,t) = Class_tactics.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        let (evm, cSome_instance) = Evd.fresh_global env evm (Lazy.force cSome_instance) in
        k ~st env evm (Constr.mkApp (EConstr.to_constr evm cSome_instance, [| typ; EConstr.to_constr evm t|]))
      with
        Not_found ->
        let (evm, cNone_instance) = Evd.fresh_global env evm (Lazy.force cNone_instance) in
        k ~st env evm (Constr.mkApp (EConstr.to_constr evm cNone_instance, [|typ|]))
    end
  | TmInferInstanceTerm typ ->
    let evm,typ = denote_term env evm (reduce_all env evm typ) in
    Plugin_core.run ~st (Plugin_core.tmInferInstance typ) env evm
      (fun ~st env evm -> function
           None -> k ~st env evm (constr_mkAppl (cNone, [| tTerm|]))
         | Some trm ->
           let qtrm = quote_term env evm trm in
           k ~st env evm (constr_mkApp (cSome, [| Lazy.force tTerm; qtrm |])))
  | TmPrintTerm trm ->
    let evm,trm = denote_term env evm (reduce_all env evm trm) in
    Plugin_core.run ~st  (Plugin_core.tmPrint trm) env evm
      (fun ~st env evm _ -> k ~st env evm (Lazy.force unit_tt))
