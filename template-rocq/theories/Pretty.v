(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Primitive Environment Universes.
From MetaRocq.Template Require Import Ast AstUtils LiftSubst.

(** * Pretty printing *)

Section print_term.
  Context (Σ : global_env_ext).

  Fixpoint decompose_lam (t : term) (n : nat) : (list aname) * (list term) * term :=
    match n with
    | 0 => ([], [], t)
    | S n =>
      match t with
      | tLambda na A B => let (nAs, B) := decompose_lam B n in
                          let (ns, As) := nAs in
                          (na :: ns, A :: As, B)
      | _ => ([], [], t)
      end
    end.

  Definition is_fresh (Γ : list ident) (id : ident) :=
    List.forallb (fun id' => negb (eqb id id')) Γ.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl {| ind_bodies := l; ind_universes := uctx |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  Fixpoint name_from_term (t : term) :=
    match t with
    | tRel _ | tVar _ | tEvar _ _ => "H"
    | tSort s => "X"
    | tProd na b t => "f"
    | tLambda na b t => "f"
    | tLetIn na b _ t' => name_from_term t'
    | tApp f _ => name_from_term f
    | tConst c u => "x"
    | tInd (mkInd i k) u =>
      match lookup_ind_decl i k with
      | Some body => String.substring 0 1 (body.(ind_name))
      | None => "X"
      end
    (* | tInt _ => "i" *)
    | _ => "U"
    end.

  Definition fresh_id_from Γ n id :=
    let fix aux i :=
      match i with
      | 0 => id
      | S i' =>
        let id' := id ^ string_of_nat (n - i) in
        if is_fresh Γ id' then id'
        else aux i'
      end
    in aux n.

  Definition fresh_name (Γ : list ident) (na : name) (t : option term) : ident :=
    let id := match na with
              | nNamed id => id
              | nAnon =>
                match t with
                | Some t => name_from_term t
                | None => "_"
                end
              end
    in
    if is_fresh Γ id then id
    else fresh_id_from Γ 10 id.

  Definition fix_context (m : mfixpoint term) : context :=
    List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

  Definition rename_decl (na : aname) (decl : context_decl) : context_decl :=
    {| decl_name := na;
       decl_type := decl_type decl;
       decl_body := decl_body decl |}.

  Definition build_return_context
             (ind : inductive)
             (oib : one_inductive_body)
             (pred : predicate term) : option context :=
    (* Decompose the type. It will contain parameters too, but at the end, which is ok. *)
    let '(Γ, _) := decompose_prod_assum [] (ind_type oib) in
    (* We have to skip the first name since that's the name of the inductive binder. *)
    let index_names := tl (pcontext pred) in
    match hd_error (pcontext pred) with
    | Some ind_binder_name =>
      Some (
          map (fun '(na, decl) => rename_decl na decl)
          (combine (tl (pcontext pred)) Γ)
          ,,
          vass ind_binder_name (mkApps (tInd ind (puinst pred)) (pparams pred)))
    | None => None
    end.

  Definition fresh_names (Γ : list ident) (Γ' : context) : list ident :=
    let fix aux Γids Γ :=
        match Γ with
        | [] => Γids
        | decl :: Γ => aux (fresh_name Γids (binder_name (decl_name decl))
                                       (Some (decl_type decl)) :: Γids)
                           Γ
        end in
    aux Γ (MRList.rev Γ').

End print_term.

Module PrintTermTree.
  Import bytestring.Tree.
  Infix "^" := append.

  Section env.
  Context (Σ : global_env_ext).
  Context (with_universes : bool).

  Definition print_def {A} (f : A -> t) (g : A -> t) (def : def A) :=
    string_of_name (binder_name (dname def)) ^ " { struct " ^ string_of_nat (rarg def) ^ " }" ^
                 " : " ^ f (dtype def) ^ " := " ^ nl ^ g (dbody def).

  Definition print_defs (print_term : list ident -> bool -> term -> t)
             Γ
             (defs : mfixpoint term) :=
    let ctx' := fix_context defs in
    print_list (print_def (print_term Γ true) (print_term (fresh_names Σ Γ ctx') true))
               (nl ^ " with ") defs.
  Definition print_sort (s : sort) :=
    match s with
    | sProp => "Prop"
    | sSProp => "SProp"
    | sType l =>
      if with_universes then
        ("Type(" ++
           MRString.string_of_list string_of_level_expr (LevelExprSet.elements l) ++
          ")")%bs
       else "Type"
    end.

  (* TODO: SPROP: we ignore relevance on printing, maybe add print config? *)
  Fixpoint print_term (Γ : list ident) (top : bool) (t : term) {struct t} : Tree.t :=
  match t with
  | tRel n =>
    match nth_error Γ n with
    | Some id => id
    | None => "UnboundRel(" ^ string_of_nat n ^ ")"
    end
  | tVar n => "Var(" ^ n ^ ")"
  | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "[]" (* TODO *)  ^ ")"
  | tSort s => print_sort s
  | tCast c k t => parens top (print_term Γ true c ^ ":"  ^ print_term Γ true t)
  | tProd na dom codom =>
    let na' := (fresh_name Σ Γ na.(binder_name) (Some dom)) in
    if (noccur_between 0 1 codom) then
      parens top
      (print_term Γ false dom ^ " → " ^ print_term (na' :: Γ) true codom)
    else parens top
           ("∀ " ^ na' ^ " : " ^
                     print_term Γ false dom ^ ", " ^ print_term (na' :: Γ) true codom)
  | tLambda na dom body =>
    let na' := (fresh_name Σ Γ na.(binder_name) (Some dom)) in
    parens top ("fun " ^ na' ^ " : " ^ print_term Γ true dom
                                ^ " ⇒ " ^ print_term (na' :: Γ) true body)
  | tLetIn na def dom body =>
    let na' := (fresh_name Σ Γ na.(binder_name) (Some dom)) in
    parens top ("let " ^ na' ^ " : " ^ print_term Γ true dom ^
                      " := " ^ print_term Γ true def ^ " in " ^ nl ^
                      print_term (na' :: Γ) true body)
  | tApp f l =>
    parens top (print_term Γ false f ^ " " ^ print_list (print_term Γ false) " " l)
  | tConst c u => string_of_kername c ^ print_universe_instance u
  | tInd (mkInd i k) u =>
    match lookup_ind_decl Σ i k with
    | Some oib => oib.(ind_name) ^ print_universe_instance u
    | None =>
      "UnboundInd(" ^ string_of_inductive (mkInd i k) ^ "," ^ string_of_universe_instance u ^ ")"
    end
  | tConstruct (mkInd i k as ind) l u =>
    match lookup_ind_decl Σ i k with
    | Some oib =>
      match nth_error oib.(ind_ctors) l with
      | Some cb => cb.(cstr_name) ^ print_universe_instance u
      | None =>
        "UnboundConstruct(" ^ string_of_inductive ind ^ "," ^ string_of_nat l ^ ","
                            ^ string_of_universe_instance u ^ ")"
      end
    | None =>
      "UnboundConstruct(" ^ string_of_inductive ind ^ "," ^ string_of_nat l ^ ","
                          ^ string_of_universe_instance u ^ ")"
    end
  | tCase {| ci_ind := mkInd mind i as ind; ci_npar := pars |} p t brs =>
    match lookup_ind_decl Σ mind i with
    | Some oib =>
      match build_return_context ind oib p with
      | None =>
        "Case(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_term t ^ ","
                ^ string_of_predicate string_of_term p ^ "," ^
                string_of_list (pretty_string_of_branch string_of_term) brs ^ ")"

      | Some Γret =>
        let Γret := fresh_names Σ Γ Γret in
        let ret_binders := firstn #|pcontext p| Γret in
        let (as_name, indices) := (hd "_" ret_binders, MRList.rev (tail ret_binders)) in
        let in_args := (repeat "_" #|pparams p| ++ indices)%list in
        let in_str := oib.(ind_name) ^ concat "" (map (fun a : bytestring.string => " " ^ a) in_args) in

        let fix print_branch Γ names prbr {struct names} :=
            match names with
            | [] => "⇒ " ^ prbr Γ
            | na :: l =>
              let na' := (fresh_name Σ Γ na.(binder_name) None) in
                na' ^ "  " ^ print_branch (na' :: Γ) l prbr
            end
        in

        let brs := map (fun br => print_branch Γ (List.rev br.(bcontext)) (fun Γ => print_term Γ true br.(bbody))) brs in
        let brs := combine brs oib.(ind_ctors) in

        parens top ("match " ^ print_term Γ true t ^
                    " as " ^ as_name ^
                    " in " ^ in_str ^
                    " return " ^ print_term Γret true (preturn p) ^
                    " with " ^ nl ^
                    print_list (fun '(b, cb) => cb.(cstr_name) ^ " " ^ b)
                    (nl ^ " | ") brs ^ nl ^ "end" ^ nl)
      end
    | None =>
      "Case(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_term t ^ ","
              ^ string_of_predicate string_of_term p ^ "," ^
              string_of_list (pretty_string_of_branch string_of_term) brs ^ ")"
    end
  | tProj p c =>
    match lookup_projection Σ p with
    | Some (mdecl, idecl, cdecl, pdecl) => print_term Γ false c ^ ".(" ^ pdecl.(proj_name) ^ ")"
    | None =>
      "UnboundProj(" ^ string_of_inductive p.(proj_ind) ^ "," ^ string_of_nat p.(proj_npars) ^ "," ^ string_of_nat p.(proj_arg) ^ ","
                     ^ print_term Γ true c ^ ")"
    end


  | tFix l n =>
    parens top ("let fix " ^ print_defs print_term Γ l ^ nl ^
                          " in " ^ List.nth_default (string_of_nat n) (map (string_of_name ∘ binder_name ∘ dname) l) n)
  | tCoFix l n =>
    parens top ("let cofix " ^ print_defs print_term Γ l ^ nl ^
                              " in " ^ List.nth_default (string_of_nat n) (map (string_of_name ∘ binder_name ∘ dname) l) n)
  | tInt i => "Int(" ^ string_of_prim_int i ^ ")"
  | tFloat f => "Float(" ^ string_of_float f ^ ")"
  | tString s => "Float(" ^ string_of_pstring s ^ ")"
  | tArray u arr def ty => "Array(" ^ string_of_universe u ^ "," ^
    string_of_list string_of_term arr ^ "," ^ string_of_term def ^ "," ^ string_of_term ty ^ ")"
  end.

  Definition pr_context_decl Γ (c : context_decl) : ident * t :=
    match c with
    | {| decl_name := na; decl_type := ty; decl_body := None |} =>
      let na' := (fresh_name Σ Γ na.(binder_name) (Some ty)) in
      (na', ("(" ^ na' ^ " : " ^ print_term Γ true ty ^ ")"))
    | {| decl_name := na; decl_type := ty; decl_body := Some b |} =>
      let na' := (fresh_name Σ Γ na.(binder_name) (Some ty)) in
      (na', ("(" ^ na' ^ " : " ^ print_term Γ true ty ^ " := " ^
        print_term Γ true b ^ ")"))
    end.

  Fixpoint print_context Γ Δ : list ident * t :=
    match Δ with
    | [] => (Γ, "" : t)
    | d :: decls =>
      let '(Γ, s) := print_context Γ decls in
      let '(na, s') := pr_context_decl Γ d in
      match decls with
      | [] => (na :: Γ, s ^ s')
      | _ => (na :: Γ, s ^ " " ^ s')
      end
    end.

  Definition print_one_cstr Γ (mib : mutual_inductive_body) (c : constructor_body) : t :=
    let '(Γargs, s) := print_context Γ c.(cstr_args) in
    c.(cstr_name) ^ " : " ^ s ^ "_" ^ print_list (print_term Γargs true) " " c.(cstr_indices).

  Definition print_one_ind (short : bool) Γ (mib : mutual_inductive_body) (oib : one_inductive_body) : t :=
    let '(Γpars, spars) := print_context Γ mib.(ind_params) in
    let '(Γinds, sinds) := print_context Γpars oib.(ind_indices) in
    oib.(ind_name) ^ spars ^ sinds ^ print_term Γinds true (tSort oib.(ind_sort)) ^ ":=" ^ nl ^
    if short then "..."
    else print_list (print_one_cstr Γpars mib) nl oib.(ind_ctors).

  Definition print_one_cstr_entry Γ (mie : mutual_inductive_entry) (c : ident × term) : t :=
    c.1 ^ " : " ^ print_term Γ true c.2.

  Definition print_one_ind_entry (short : bool) Γ (mie : mutual_inductive_entry) (oie : one_inductive_entry) : t :=
    let '(Γpars, spars) := print_context Γ mie.(mind_entry_params) in
    oie.(mind_entry_typename) ^ spars ^ print_term Γpars true oie.(mind_entry_arity) ^ ":=" ^ nl ^
    if short then "..."
    else print_list (print_one_cstr_entry Γpars mie) nl (combine oie.(mind_entry_consnames) oie.(mind_entry_lc)).
  End env.

  Definition universes_decl_of_universes_entry e :=
    match e with
    | Monomorphic_entry ctx => Monomorphic_ctx
    | Polymorphic_entry uctx => Polymorphic_ctx (fst uctx, snd (snd uctx))
    end.

  Definition print_recursivity_kind k :=
    match k with
    | Finite => "Inductive"
    | CoFinite => "CoInductive"
    | BiFinite => "Variant"
    end.

  Definition print_mib Σ with_universes (short : bool) (mib : mutual_inductive_body) : t :=
    let Σ' := (Σ, mib.(ind_universes)) in
    let names := fresh_names Σ' [] (arities_context mib.(ind_bodies)) in
      (print_recursivity_kind mib.(ind_finite) ^ " " ^
      print_list (print_one_ind Σ' with_universes short names mib) (nl ^ "with ") mib.(ind_bodies) ^ "." ^ nl).

  Definition mie_arities_context mie :=
    rev_map (fun ind => vass (mkBindAnn (nNamed ind.(mind_entry_typename)) Relevant)
      (it_mkProd_or_LetIn mie.(mind_entry_params) ind.(mind_entry_arity)))
      mie.(mind_entry_inds).

  Definition print_mie Σ with_universes (short : bool) (mie : mutual_inductive_entry) : t :=
    let Σ' := (Σ, universes_decl_of_universes_entry mie.(mind_entry_universes)) in
    let names := fresh_names Σ' [] (mie_arities_context mie) in
      (print_recursivity_kind mie.(mind_entry_finite) ^ " " ^
      print_list (print_one_ind_entry Σ' with_universes short names mie) (nl ^ "with ") mie.(mind_entry_inds) ^ "." ^ nl).

  Fixpoint print_env_aux with_universes (short : bool) (prefix : nat) (Σ : global_env) (acc : t) : t :=
    match prefix with
    | 0 => match Σ.(declarations) with [] => acc | _ => ("..." ^ nl ^ acc) end
    | S n =>
      let univs := Σ.(Env.universes) in
      let retro := Σ.(Env.retroknowledge) in
      match Σ.(declarations) with
      | [] => acc
      | (kn, InductiveDecl mib) :: Σ =>
        let Σ := {| Env.universes := univs; declarations := Σ; retroknowledge := retro |} in
        print_env_aux with_universes short n Σ (print_mib Σ with_universes short mib ^ acc)
      | (kn, ConstantDecl cb) :: Σ =>
        let Σ' := ({| Env.universes := univs; declarations := Σ; retroknowledge := retro |}, cb.(cst_universes)) in
        print_env_aux with_universes short n Σ'.1
          ((match cb.(cst_body) with
            | Some _ => "Definition "
            | None => "Axiom "
          end) ^ string_of_kername kn ^ " : " ^ print_term Σ' with_universes nil true cb.(cst_type) ^
          match cb.(cst_body) with
          | Some b =>
            if short then ("..." ^ nl)
            else (" := " ^ nl ^ print_term Σ' with_universes nil true b ^ "." ^ nl)
          | None => "."
          end ^ acc)
      end
    end.

  Definition print_env with_universes (short : bool) (prefix : nat) Σ :=
    print_env_aux with_universes short prefix Σ (Tree.string "").

  Definition print_program with_universes (short : bool) (prefix : nat) (p : program) : t :=
    print_env with_universes short prefix (fst p) ^ nl ^ print_term (empty_ext (fst p)) with_universes nil true (snd p).

End PrintTermTree.

Definition print_mie Σ with_universes short := Tree.to_string ∘ PrintTermTree.print_mie Σ with_universes short.
Definition print_mib Σ with_universes short := Tree.to_string ∘ PrintTermTree.print_mib Σ with_universes short.

Definition print_term Σ Γ top := Tree.to_string ∘ PrintTermTree.print_term Σ true Γ top.

Definition print_env (short : bool) (prefix : nat) Σ :=
  Tree.to_string (PrintTermTree.print_env true short prefix Σ).

Definition print_program (short : bool) (prefix : nat) (p : program) : string :=
  Tree.to_string (PrintTermTree.print_program true short prefix p).
