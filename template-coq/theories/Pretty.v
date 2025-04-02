(** This module defines pretty-printers for template-coq terms,
    declarations and environments. It relies the PPrint pretty-printing 
    library : to print a document to a string, use [pp_string] or [pp_bytestring]. *)

From Coq Require Import PrimString Uint63.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Utils Require Import utils.
From PPrint Require Export All.

Local Open Scope pstring.

(** * Pretty-printing configuration. *)

Module PrettyFlags.

(** The pretty-printing functions can show a variable amount of information,
    depending on the printing flags. *)
Record t := mk
  { (** Should we print universes ? *)
    universes : bool 
  ; (** Should we print case return clauses ? *)
    case_returns : bool
  ; (** Should we print evar instances (delayed substitutions) ? *)
    evar_instances : bool 
  ; (** Should we print all parentheses ? *) 
    parentheses : bool 
  ; (** Should we print full kernel names ? *)
    full_names : bool 
  ; (** Should we print the bodies of definition and inductives ?
        (only relevant when printing declarations) *)
    full_defs : bool }.

(** Default flags : don't print any low-level details. *)
Definition default : t := mk false false false false false false.
  
(** Print all low-level details. *)
Definition all : t := mk true true true true true true.
  
End PrettyFlags.

(** * Utils *)

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 100, right associativity, only parsing).

(** Some notations to avoid confusing string types. *)
Notation pstring := PrimString.string.
Notation bstring := bytestring.string.

(** Convert a bytestring to a primitive string. *)
Definition pstring_of_sbtring (bstr : bstring) : pstring :=
  let fix loop pstr bstr :=
    match bstr with 
    | String.EmptyString => pstr
    | String.String byte bstr => 
      let char := PrimString.make 1 $ Uint63.of_nat (Byte.to_nat byte) in
      loop (PrimString.cat pstr char) bstr
    end
  in
  loop "" bstr.

(** Convert a primitive string to a byte string. *)
Definition bstring_of_pstring (pstr : pstring) : bstring :=
  let chars := List.map char63_to_string (PrimStringAxioms.to_list pstr) in 
  List.fold_left (fun s s' => s ^ s') chars ""%bs.

(** [bstr s] builds an atomic document containing the bytestring [s]. *)
Definition bstr {A} (s : bstring) : doc A :=
  str $ pstring_of_sbtring s.

(** [pp_bytestring] is analogous to [pp_string] except it outputs a bytestring
    instead of a primitive string. *)
Definition pp_bytestring {A} width (d : doc A) : bstring :=
  bstring_of_pstring $ pp_string width d.
  
Definition string_of_constructor (ind : inductive) (ctor_idx : nat) : bstring :=
  (string_of_inductive ind ++ "," ++ string_of_nat ctor_idx)%bs.
  
(** [context_names ctx] returns the names of the declarations in context [ctx]. *)
Definition context_names (ctx : context) : list ident :=
  List.map (fun d => string_of_name d.(decl_name).(binder_name)) ctx.

(** [filter_mask xs bs] filters out all the elements of [xs] for which the corresponding
    boolean in [bs] is [false]. *)
Fixpoint filter_mask {A} (xs : list A) (bs : list bool) : list A :=
  match xs, bs with 
  | x :: xs, true :: bs => x :: filter_mask xs bs 
  | _ :: xs, false :: bs => filter_mask xs bs 
  | _, _ => []
  end.  

(** * Pretty-printing. *)

(** While pretty-printing terms we store the names of the binders traversed so far
    in a _name context_ [id_0; id_1; ...; id_n], which is simply a list of [ident]. 
    The identifier [id_i] is the name associated to the de Bruijn index [i]. *)

Section Printing.
Context (flags : PrettyFlags.t).

Section Env.
Context (env : global_env_ext).

(** [paren_if min_prec prec d] adds parentheses around document [d] if [min_prec > prec].
    It takes into account the flag to force parentheses. *)
Definition paren_if {A} (min_prec prec : nat) (d : doc A) : doc A :=
  if PrettyFlags.parentheses flags || Nat.ltb prec min_prec then paren d else d.
  
Definition print_name (n : name) : doc unit :=
  match n with 
  | nAnon => str "_"
  | nNamed n => bstr n
  end. 

(** Print a kernel name. This is not so simple : 
    - the flags might require us to print the full name.
    - we treat single-letter labels specially, e.g. [MetaCoq.Common.Universes.Instance.t]
      is printed as [Instance.t] instead of just [t]. *)
Definition print_kername (kname : kername) : doc unit :=
  (* Helper function get the identifiers in a module path. *)
  let fix modpath_ids path acc :=
    match path with 
    | MPfile dirpath => List.rev dirpath ++ acc
    | MPbound dirpath id _ => 
      (* Not sure this is completely correct ? *)
      List.rev (id :: dirpath)
    | MPdot path id => modpath_ids path (id :: acc)
    end
  in
  let (modpath, label) := kname in
  let path := modpath_ids modpath [] in 
  if PrettyFlags.full_names flags then 
    (* If the flag is set, print the full module path. *)
    separate_map (str ".") bstr $ path ++ [label]
  else if String.length label <=? 2 then 
    (* If the label is very short, print the last part of the modpath + the label. *)
    match List.last (List.map Some path) None with 
    | Some prefix => bstr prefix ^^ str "." ^^ bstr label
    | None => bstr label 
    end
  else 
    (* Otherwise print only the identifier *)
    bstr label.

Definition print_cast_kind (kind : cast_kind) : doc unit :=
  match kind with 
  | Cast => str ":"
  | VmCast => str "<:"
  | NativeCast => str "<<:"
  end.

Definition print_level (l : Level.t) : doc unit :=
  match l with 
  | Level.lzero => str "Set"
  | Level.level s => bstr s
  | Level.lvar n => 
    (* For level variables, we try to get the name of the level in the local universe context. *)
    match snd env with 
    | Monomorphic_ctx => str "lvar" ^^ nat10 n
    | Polymorphic_ctx (univ_names, _) => 
      match List.nth_error univ_names n with 
      | Some uname => print_name uname 
      | None => str "lvar" ^^ nat10 n
      end
    end
  end.

Definition print_level_expr (le : LevelExprSet.elt) : doc unit :=
  match le with 
  | (l, 0) => print_level l
  | (l, n) => print_level l ^^ str "+" ^^ nat10 n
  end.
  
Definition print_sort (s : sort) :=
  match s with
  | sProp => str "Prop"
  | sSProp => str "SProp"
  | sType l =>
    if PrettyFlags.universes flags
    then
      let lvls := flow_map (str "," ^^ break 0) print_level_expr $ LevelExprSet.elements l in 
      bracket "Type@{" lvls "}"
    else str "Type"
  end.

Definition print_univ_instance (uinst : Instance.t) : doc unit :=
  if PrettyFlags.universes flags && negb (uinst == []) then 
    let lvls := flow_map (break 0) print_level uinst in 
    bracket "@{" lvls "}"
  else 
    empty.

(** Prints the names bound by a universe declaration, but _not_ the constraints. *)
Definition print_univ_decl (decl : universes_decl) : doc unit :=
  match decl with 
  | Monomorphic_ctx => empty 
  | Polymorphic_ctx (unames, _) =>
      bracket "@{" (flow_map (str "," ^^ break 0) print_name unames) "}"  
  end.
  
(** Helper function to print a single definition in a fixpoint block. *)
Definition print_def {A} (on_ty : A -> doc unit) (on_body : A -> doc unit) (def : def A) :=
  let n_doc := 
    separate space 
      [ print_name (binder_name $ def.(dname)) 
      ; str "{ struct" ^+^ nat10 def.(rarg) ^+^ str "}" 
      ; str ":" ] 
  in
  let ty_doc := on_ty def.(dtype) ^+^ str ":=" in
  let body_doc := on_body def.(dbody) in 
  (* We don't [align] here on purpose. *)
  group $ group (n_doc ^//^ ty_doc) ^//^ body_doc.

(** Helper function to print a term of the form [tFix mfix n] or [tCoFix mfix n].
    The parameter [is_fix] controls whether to print a fixpoint or a co-fixpoint. *)
Definition print_fixpoint (on_term : list ident -> term -> doc unit) (ctx : list ident) 
  (defs : mfixpoint term) (n : nat) (is_fix : bool) : doc unit  :=
  let prefix := if is_fix then str "let fix" else str "let cofix" in
  let sep := break 0 ^^ str "with" ^^ space in
  let on_def := 
    print_def (on_term ctx) (on_term $ ctx ,,, context_names (fix_context defs))
  in
  let func_name := 
    option_default 
      (fun def => print_name def.(dname).(binder_name)) 
      (List.nth_error defs n) (nat10 n) 
  in
  if Nat.ltb 1 (List.length defs)
  then align $ group $ prefix ^+^ separate_map sep on_def defs ^/^ str "for" ^+^ func_name
  else align $ group $ prefix ^+^ separate_map sep on_def defs.

(** Helper function to print a case single branch (without the leading "|"). *)
Definition print_branch (on_term : list ident -> term -> doc unit) (ctx : list ident) 
  (branch : branch term) (ctor : constructor_body) : doc unit :=
  let var_names := List.map (fun b => string_of_name b.(binder_name)) branch.(bcontext) in
  let branch_ctx := ctx ,,, var_names in
  let binder := flow_map (break 2) bstr (ctor.(cstr_name) :: rev var_names) in
  group $ align $ binder ^+^ str "⇒" ^//^ on_term branch_ctx branch.(bbody).

(** Helper function to print a the header of case : [match x as y in I _ _ i i' return z]. *)
Definition print_case_header (on_term : list ident -> term -> doc unit) (ctx : list ident)  
  (ind_kname : kername) (scrutinee : term) (pred : predicate term) : doc unit :=
  let pred_ctx := List.map (fun b => string_of_name b.(binder_name)) pred.(pcontext) in
  (* [match_clause] is [match xxx]. *)
  let match_clause := str "match" ^+^ on_term ctx scrutinee in
  (* [as_clause] is [as xxx]. *)
  let as_clause := str "as" ^+^ bstr (List.hd "x"%bs pred_ctx) in
  (* [in_clause] is [in I _ _ ... index1 index2 ...]. *)
  let ind_name := print_kername ind_kname in
  let ind_params := map (fun _ => str "_") pred.(pparams) in
  let ind_indices := rev_map bstr $ List.tl pred_ctx in
  let in_clause := str "in" ^+^ align $ flow (break 2) $ ind_name :: ind_params ++ ind_indices in
  (* [ret_clause] is [return xxx]. *)
  let ret_clause := str "return" ^+^ on_term (ctx ,,, pred_ctx) pred.(preturn) in
  (* Compute which clauses are needed.
     In the future we could skip the as/in clause if possible. *)
  let clauses := [match_clause ; as_clause ; in_clause ; ret_clause] in
  let b := PrettyFlags.case_returns flags in 
  let bs := [true ; b ; b ; b] in
  (* Assemble all the clauses. *)
  align $ group $ separate (break 0) $ filter_mask clauses bs. 

(** Get the precedence of a term. Higher precedences bind tighter : 
    for instance application has the highest precedence.  *)
Definition term_prec (t : term) : nat :=
  match t with  
  | tCast _ _ _ => 5
  | tCase _ _ _ _ => 10
  | tLambda _ _ _ => 10
  | tLetIn _ _ _ body => 10
  | tProd _ _ body => 10
  | tFix _ _ => 10
  | tCoFix _ _ => 10
  | tProj _ _ => 100
  | tApp _ _ => 100
  | _ => 0
  end.

(** [print_term_prec min_prec ctx t] pretty-prints the term [t].
    - [ctx] contains the names of bound variables (tRels) in [t]. 
      Innermost variables are stored at the head of the list (as in a [context]). 
    - [min_prec] is the minimum precedence required to print [t] without parentheses.
      If [term_prec t >= min_prec] than [t] is printed without parentheses,
      otherwise parentheses are added as needed. Initially [min_prec] is set to [0]. 
    
    Consider using the higher-level function [print_term] defined below. *)
Fixpoint print_term_prec (min_prec : nat) (ctx : list ident) (t : term) : doc unit :=
  let prec := term_prec t in
  match t with
  | tRel n =>
    match List.nth_error ctx n with
    | Some id => bstr id
    | None => str "#unbound_rel(" ^^ nat10 n ^^ str ")"
    end
  | tVar n => bstr n
  | tEvar ev args => 
    if PrettyFlags.evar_instances flags then 
      let args_doc := flow_map (str ";" ^^ break 0) (print_term_prec 0 ctx) args in
      str "#evar(" ^^ nat10 ev ^^ bracket "[" args_doc "]" ^^ str ")"
    else 
      str "#evar(" ^^ nat10 ev ^^ str ")"
  | tSort s => print_sort s
  | tCast c kind t =>
    let contents := 
      print_term_prec (S prec) ctx c ^+^ 
      print_cast_kind kind ^//^ 
      print_term_prec (S prec) ctx t
    in
    paren_if min_prec prec $ align $ group contents
  | tProd n ty body =>
    let n := string_of_name n.(binder_name) in
    let contents :=
      (* Decide whether this is a dependent or non-dependent product. *)
      if noccur_between 0 1 body
      then [print_term_prec (S prec) ctx ty ^+^ str "->" ; print_term_prec prec (n :: ctx) body]
      else [str "∀" ^+^ bstr n ^+^ str ":" ; 
            print_term_prec 0 ctx ty ^^ str "," ; 
            print_term_prec prec (ctx ,, n) body]
    in 
    paren_if min_prec prec $ align $ flow (break 2) contents
  | tLambda n ty body =>
    let n := string_of_name n.(binder_name) in
    let contents :=
      [str "fun" ^+^ bstr n ^+^ str ":" ; 
       print_term_prec 0 ctx ty ^+^ str "⇒" ; 
       print_term_prec prec (ctx ,, n) body]
    in 
    paren_if min_prec prec $ align $ flow (break 2) contents
  | tLetIn n def ty body =>
    let n := string_of_name n.(binder_name) in
    let n_doc := str "let" ^+^ bstr n ^+^ str ":" in
    let ty_doc := print_term_prec 0 ctx ty ^+^ str ":=" in
    let def_doc := print_term_prec 0 ctx def in
    let body_doc := print_term_prec prec (ctx ,, n) body in
    (* Getting the formatting correct is a bit tricky. *)
    let line := group $ group (n_doc ^//^ ty_doc) ^//^ def_doc ^/^ str "in" in 
    paren_if min_prec prec $ align $ group $ line ^/^ body_doc
  | tApp f args =>
    let contents := print_term_prec prec ctx f :: List.map (print_term_prec (S prec) ctx) args in 
    paren_if min_prec prec $ align $ flow (break 2) contents 
  | tConst kname uinst => print_kername kname ^^ print_univ_instance uinst
  | tInd ind uinst =>
    let name := 
      match lookup_inductive env ind with
      | Some (_, body) => print_kername (ind.(inductive_mind).1, body.(ind_name))
      | None => bracket "#unbound_ind(" (bstr $ string_of_inductive ind) ")"
      end
    in 
    name ^^ print_univ_instance uinst
  | tConstruct ind idx uinst =>
    let name :=
      match lookup_constructor env ind idx with
      | Some (_, body) => bstr body.(cstr_name)
      | None =>
        str "#unbound_ctor(" ^^ (bstr $ string_of_constructor ind idx) ^^ str ")"
      end
    in
    name ^^ print_univ_instance uinst
  | tCase ci pred x branches =>
    match lookup_inductive env ci.(ci_ind) with
    | Some (mbody, body) =>
        (* Print each branch separately. *)
        let branch_docs := map2 (print_branch (print_term_prec 0) ctx) branches body.(ind_ctors) in
        (* Part 1 is [match x with]. *)
        let ind_kname := (ci.(ci_ind).(inductive_mind).1, body.(ind_name)) in
        let part1 := 
          group $ print_case_header (print_term_prec 0) ctx ind_kname x pred ^/^ str "with"
        in
        (* Part 2 is [C1 => ... | C2 => ... | C3 => ... end]*)
        let part2 := 
          group $ concat 
            [ break 0 ^^ ifflat empty (str "|" ^^ space)
            ; separate (break 0 ^^ str "|" ^^ space) branch_docs
            ; break 0 ^^ str "end" ]
        in
        paren_if min_prec prec $ align $ part1 ^^ part2
    | None => str "#case_error"
    end
  | tFix mfix n => paren_if min_prec prec $ print_fixpoint (print_term_prec 0) ctx mfix n true 
  | tCoFix mfix n => paren_if min_prec prec $ print_fixpoint (print_term_prec 0) ctx mfix n false
  | tProj p t =>
    match lookup_projection env p with
    | Some (_, _, _, pbody) => 
      (* Projections never need parentheses. *)
      group $ align $ concat 
        [ print_term_prec (S prec) ctx t
        ; ifflat empty (hardline ^^ blank 2) 
        ; str ".(" ^^ bstr pbody.(proj_name) ^^ str ")" ]
    | None =>
      let contents := 
        [ bstr (string_of_inductive p.(proj_ind)) 
        ; nat10 p.(proj_npars)
        ; nat10 p.(proj_arg) 
        ; print_term_prec 0 ctx t ]
      in
      bracket "#unbound_proj(" (flow (str "," ^^ break 0) contents) ")"
    end 
  | tInt i => str "#int(" ^^ bstr (string_of_prim_int i) ^^ str ")"
  | tFloat f => str "#float(" ^^ bstr (string_of_float f) ^^ str ")"
  | tString s => str "#string(" ^^ str s ^^ str ")"
  | tArray u arr def ty => 
    let arr_doc := bracket "[" (flow_map (space ^^ str ";" ^^ break 0) (print_term_prec 0 ctx) arr) "]" in 
    let contents := [print_level u ; arr_doc ; print_term_prec 0 ctx def ; print_term_prec 0 ctx ty] in
    bracket "#array(" (flow (str "," ^^ break 0) contents) ")"
  end.

(** [print_term ctx t] pretty-prints the term [t] in context [ctx]. *)
Definition print_term ctx t : doc unit := print_term_prec 0 ctx t.

(** [print_context_decl ctx decl] pretty-prints the context declaration [decl] in context [ctx]. *)
Definition print_context_decl (ctx : list ident) (decl : context_decl) : doc unit :=
  let contents := 
    match decl.(decl_body) with
    | None => 
      [ print_name decl.(decl_name).(binder_name) 
      ; str ":" ^+^ print_term ctx decl.(decl_type)]
    | Some body => 
        [ print_name decl.(decl_name).(binder_name) 
        ; str ":" ^+^ print_term ctx decl.(decl_type)
        ; str ":=" ^+^ print_term ctx body ]
    end
  in 
  group $ paren $ flow (break 2) contents.

(** [print_context ctx decls] prints the declarations in [decls], 
    assuming they live in context [ctx]. 
    It returns the documents in the same order they were given in [decls]. *)
Definition print_context (ctx : list ident) (decls : context) : list (doc unit) := 
  (* We process the declarations from outermost to innermost,
     while extending the named context as we go. *)
  let fix loop (ctx : list ident) (acc : list (doc unit)) (decls : list context_decl) :=
    match decls with 
    | [] => acc
    | d :: decls =>
      (* Print the first declaration. *)
      let d_name := string_of_name d.(decl_name).(binder_name) in
      let d_doc := print_context_decl ctx d in
      (* Recurse in an extended named context. *)
      loop (ctx ,, d_name) (d_doc :: acc) decls
    end
  in 
  loop ctx [] (rev decls).

Definition print_recursivity_kind kind : doc unit :=
  match kind with
  | Finite => str "Inductive"
  | CoFinite => str "CoInductive"
  | BiFinite => str "Record"
  end.

(** Helper function to print a single constructor.
    - [ctx] should contain the names of the other inductives in the block as well
      as the inductive parameters. 
    - [params] is the list of parameters (ordered from first to last) represented as 
      local variables (tRel). *)
Definition print_one_cstr (ctx : list ident) (ind : inductive) (params : list term) (ctor : constructor_body) : doc unit :=
  (* TODO : handle universes for [tInd]. *)
  let n_args := List.length ctor.(cstr_args) in
  let ctor_ty := 
    it_mkProd_or_LetIn ctor.(cstr_args) $ 
    mkApps (tInd ind []) $ 
    (List.map (lift0 n_args) params) ++ ctor.(cstr_indices) 
  in
  align $ group $ bstr ctor.(cstr_name) ^+^ str ":" ^//^ print_term ctx ctor_ty.

(** Helper function to print a single inductive.
    - [header] is the keyword which should be printed before the inductive name 
      (usually it is [Inductive] or [with]).
    - [ctx] should contain the names of the other inductives in the block. *)
Definition print_one_ind (header : doc unit) (ctx : list ident) 
  (mbody : mutual_inductive_body) (body : one_inductive_body) (ind : inductive) : doc unit :=
  (* Print the parameters and arity. *)
  let param_docs := print_context ctx mbody.(ind_params) in
  let params := rev $ mapi (fun i _ => tRel i) mbody.(ind_params) in
  let ctx_params := ctx ,,, context_names mbody.(ind_params) in
  let arity := it_mkProd_or_LetIn body.(ind_indices) (tSort body.(ind_sort)) in
  (* part1 is [ind_name@{univs} params : arity :=]*)
  let part1 := flow (break 2) $ 
    header ::
    (print_kername (ind.(inductive_mind).1, body.(ind_name)) ^^ print_univ_decl env.2) ::
    rev param_docs ++
    [ str ":"
    ; print_term ctx_params arity
    ; str ":=" ]
  in 
  (* part2 is [C1 : ... | C2 : ... | C2 : ...] *)
  let part2 := 
    ifflat empty (str "|" ^^ space) ^^
    separate_map (break 0 ^^ str "|" ^^ space) (print_one_cstr ctx_params ind params) body.(ind_ctors)
  in
  align $ flow (break 0) [part1 ; if PrettyFlags.full_defs flags then part2 else str "..."].

End Env.

(** Print a mutual inductive block. *)
Definition print_mutual_inductive (env : global_env) (ind_kname : kername) (mbody : mutual_inductive_body) : doc unit :=
  let ext_env := (env, mbody.(ind_universes)) in
  let ind_ctx := 
    map 
      (fun body => pp_bytestring 0 $ print_kername (ind_kname.1, body.(ind_name)))
      mbody.(ind_bodies)
  in
  let contents := 
    mapi 
      (fun i body => 
        let header := if i == 0 then print_recursivity_kind mbody.(ind_finite) else str "with" in
        print_one_ind ext_env header ind_ctx mbody body (mkInd ind_kname i))
      mbody.(ind_bodies) 
  in
  align $ group $ separate (break 0) contents.
  
(** Print a constant. *)
Definition print_constant (env : global_env) (kname : kername) (cst : constant_body) : doc unit :=
  let ext_env := (env, cst.(cst_universes)) in
  let ctx := [] in
  let header := 
    match cst.(cst_body) with 
    | Some _ => str "Definition" 
    | None => str "Axiom" 
    end
  in
  let decl := 
    flow (break 2)
      [ header ; (print_kername kname ^^ print_univ_decl cst.(cst_universes))
      ; str ":" ; print_term ext_env ctx cst.(cst_type) ]
  in
  let body :=
    if PrettyFlags.full_defs flags then  
      match cst.(cst_body) with 
      | Some body => print_term ext_env ctx body
      | None => empty
      end
    else str "..."
  in
  align $ group $ decl ^+^ str ":=" ^//^ body.
  
(** Print all the declarations in a global environment. *)
Definition print_env (env : global_env) : doc unit :=
  let fix loop decls acc :=
    match decls with 
    | [] => separate (hardline ^^ if PrettyFlags.full_defs flags then hardline else empty) acc
    | (kname, decl) :: decls =>
      let doc := 
        match decl with 
        | ConstantDecl cst => print_constant env kname cst 
        | InductiveDecl mbody => print_mutual_inductive env kname mbody
        end
      in 
      loop decls (doc :: acc)
    end 
  in 
  loop env.(declarations) [].

End Printing.

