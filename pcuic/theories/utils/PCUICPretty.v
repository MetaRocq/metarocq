(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.

(** * Pretty printing *)

Section lookups.
  Context (Σ : global_env).

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl {| ind_bodies := l; ind_universes := uctx |}) =>
      match nth_error l i with
      | Some body => Some (l, uctx, body)
      | None => None
      end
    | _ => None
    end.
End lookups.

Section fresh.
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
    negb (List.existsb (eqb id) Γ).

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
      match lookup_ind_decl Σ i k with
      | Some (_, body) => String.substring 0 1 (body.(ind_name))
      | None => "X"
      end
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
    else fresh_id_from Γ #|Γ| id.

  Definition rename_decl (na : aname) (decl : context_decl) : context_decl :=
    {| decl_name := na;
        decl_type := decl_type decl;
        decl_body := decl_body decl |}.

  (* Definition build_return_context
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
    end. *)

  Definition fresh_names (Γ : list ident) (Γ' : context) : list ident :=
    let fix aux Γids Γ :=
        match Γ with
        | [] => Γids
        | decl :: Γ => aux (fresh_name Γids (binder_name (decl_name decl))
                                        (Some (decl_type decl)) :: Γids)
                            Γ
        end in
    aux Γ (MRList.rev Γ').
End fresh.

Module PrintTermTree.
  Section env.
    Context (Σ : global_env_ext).
    Import bytestring.Tree.
    Infix "^" := append.

    Definition print_prim (soft : term -> Tree.t) (p : prim_val) : Tree.t :=
      match p.π2 return Tree.t with
      | primIntModel f => "(int: " ^ show f ^ ")"
      | primFloatModel f => "(float: " ^ show f ^ ")"
      | primStringModel s => "(string: " ^ show s ^ ")"
      | primArrayModel a => "(array:" ^ string_of_list soft a.(array_value) ^ ")"
      end.

    Section Aux.
      Context (print_term : list ident -> bool -> bool -> term -> t).

      Definition print_def {A} (f : A -> t) (g : A -> t) (def : def A) :=
        string_of_name (binder_name (dname def)) ^ " { struct " ^ show (rarg def) ^ " }" ^
                    " : " ^ f (dtype def) ^ " := " ^ nl ^ g (dbody def).

      Definition print_defs Γ (defs : mfixpoint term) :=
        let ctx' := fix_context defs in
        print_list (print_def (print_term Γ true false) (print_term (fresh_names Σ Γ ctx') true false))
              (nl ^ " with ") defs.

      Definition pr_context_decl Γ (c : context_decl) : ident * t :=
        match c with
        | {| decl_name := na; decl_type := ty; decl_body := None |} =>
          let na' := (fresh_name Σ Γ na.(binder_name) (Some ty)) in
          (na', ("(" ^ na' ^ " : " ^ print_term Γ true false ty ^ ")")%bs)
        | {| decl_name := na; decl_type := ty; decl_body := Some b |} =>
          let na' := (fresh_name Σ Γ na.(binder_name) (Some ty)) in
          (na', ("(" ^ na' ^ " : " ^ print_term Γ true false ty ^ " := " ^
            print_term Γ true false b ^ ")")%bs)
        end.

      Fixpoint print_context_gen Γ Δ :=
        match Δ with
        | [] => (Γ, "" : t)
        | d :: decls =>
          let '(Γ, s) := print_context_gen Γ decls in
          let '(na, s') := pr_context_decl Γ d in
          match decls with
          | [] => (na :: Γ, s ^ s')
          | _ => (na :: Γ, s ^ " " ^ s')
          end
        end.

      Fixpoint print_context_names Γ Δ :=
        match Δ with
        | [] => (Γ, "" : t)
        | d :: decls =>
          let '(Γ, s) := print_context_names Γ decls in
          let na := (fresh_name Σ Γ d.(decl_name).(binder_name) (Some d.(decl_type))) in
          match decls with
          | [] => (na :: Γ, (s ^ na))
          | _ => (na :: Γ, (s ^ " " ^ na))
          end
        end.

    End Aux.

    Context (all : bool).

    Fixpoint print_term (Γ : list ident) (top : bool)(inapp : bool) (t : term) {struct t} : Tree.t :=
    match t with
    | tRel n =>
      match nth_error Γ n with
      | Some id => id
      | None => "UnboundRel(" ^ string_of_nat n ^ ")"
      end
    | tVar n => "Var(" ^ n ^ ")"
    | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "[]" (* TODO *)  ^ ")"
    | tSort s => string_of_sort s
    | tProd na dom codom =>
      let na' := fresh_name Σ Γ na.(binder_name) (Some dom) in
      parens top
            ("∀ " ^ na' ^ " : " ^
                      print_term Γ true false dom ^ ", " ^ print_term (na':: Γ) true false codom)
    | tLambda na dom body =>
      let na' := fresh_name Σ Γ na.(binder_name) (Some dom) in
        parens top ("fun " ^ na' ^ " : " ^ print_term Γ true false dom
                  ^ " => " ^ print_term (na':: Γ) true false body)
    | tLetIn na def dom body =>
      let na' := fresh_name Σ Γ na.(binder_name) (Some dom) in
      parens top ("let" ^ na' ^ " : " ^ print_term Γ true false dom ^
                        " := " ^ print_term Γ true false def ^ " in " ^ nl ^
                        print_term (na' :: Γ) true false body)
    | tApp f l =>
      parens (top || inapp) (print_term Γ false true f ^ " " ^ print_term Γ false false l)
    | tConst c u => string_of_kername c ^ print_universe_instance u
    | tInd (mkInd i k) u =>
      match lookup_ind_decl Σ i k with
      | Some (_, oib) => oib.(ind_name) ^ print_universe_instance u
      | None =>
        "UnboundInd(" ^ string_of_inductive (mkInd i k) ^ "," ^ string_of_universe_instance u ^ ")"
      end
    | tConstruct (mkInd i k as ind) l u =>
      match lookup_ind_decl Σ i k with
      | Some (_, oib) =>
        match nth_error oib.(ind_ctors) l with
        | Some cdecl => cdecl.(cstr_name) ^ print_universe_instance u
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
      | Some (_, oib) =>
        let Γret := p.(pcontext) in
        let Γret := fresh_names Σ Γ Γret in
        let ret_binders := firstn #|pcontext p| Γret in
        let (as_name, indices) := (hd "_" ret_binders, MRList.rev (tail ret_binders)) in
        let in_args := (repeat "_" #|pparams p| ++ indices)%list in
        let in_str := oib.(ind_name) ^ concat "" (map (fun a : String.t => " " ^ a) in_args) in

        let brs := map (fun br =>
            let (Γctx, pctx) :=
              if all then print_context_gen print_term Γ br.(bcontext)
              else print_context_names Γ br.(bcontext)
            in
            pctx ^ " ⇒ " ^ print_term Γctx true false br.(bbody)) brs in
        let brs := combine brs oib.(ind_ctors) in

        parens top ("match " ^ print_term Γ true false t ^
                    " as " ^ as_name ^
                    " in " ^ in_str ^
                    " return " ^ print_term Γret true false (preturn p) ^
                    " with " ^ nl ^
                    print_list (fun '(b, cdecl) => cdecl.(cstr_name) ^ " " ^ b)
                    (nl ^ " | ") brs ^ nl ^ "end" ^ nl)
    | None =>
      "Case(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_term t ^ ","
              ^ string_of_predicate string_of_term p ^ "," ^
              string_of_list (pretty_string_of_branch string_of_term) brs ^ ")"
      end
    | tProj p c =>
      match lookup_projection Σ p with
      | Some (mdecl, idecl, cdecl, pdecl) =>
        print_term Γ false false c ^ ".(" ^ pdecl.(proj_name) ^ ")"
      | None =>
        "UnboundProj(" ^ string_of_inductive p.(proj_ind) ^ "," ^ string_of_nat p.(proj_npars) ^ "," ^ string_of_nat p.(proj_arg) ^ ","
                      ^ print_term Γ true false c ^ ")"
      end


    | tFix l n =>
      parens top ("let fix " ^ print_defs print_term Γ l ^ nl ^
                            " in " ^ List.nth_default (string_of_nat n) (map (string_of_aname ∘ dname) l) n)
    | tCoFix l n =>
      parens top ("let cofix " ^ print_defs print_term Γ l ^ nl ^
                                " in " ^ List.nth_default (string_of_nat n) (map (string_of_aname ∘ dname) l) n)
    | tPrim i => parens top (print_prim (print_term Γ true false) i)
    end.
  End env.

  Import bytestring.Tree.
  Infix "^" := append.

  Section env.
    Context (Σ : global_env_ext).
    Abbreviation print_context := (print_context_gen Σ (print_term Σ true)).
    Abbreviation pr_term Γ top := (print_term Σ true Γ top false).

    Definition print_one_cstr Γ (mib : mutual_inductive_body) (c : constructor_body) : t :=
      let '(Γargs, s) := print_context Γ c.(cstr_args) in
      c.(cstr_name) ^ " : " ^ s ^ "_" ^ print_list (pr_term Γargs true) " " c.(cstr_indices).

    Definition print_one_ind (short : bool) Γ (mib : mutual_inductive_body) (oib : one_inductive_body) : t :=
      let '(Γpars, spars) := print_context Γ mib.(ind_params) in
      let '(Γinds, sinds) := print_context Γpars oib.(ind_indices) in
      oib.(ind_name) ^ spars ^ " : " ^ sinds ^ " " ^ pr_term Γinds true (tSort oib.(ind_sort)) ^ ":=" ^ nl ^
      if short then "..."
      else print_list (print_one_cstr Γpars mib) nl oib.(ind_ctors).
  End env.

  Definition print_recursivity_kind k :=
    match k with
    | Finite => "Inductive"
    | CoFinite => "CoInductive"
    | BiFinite => "Variant"
    end.

  Fixpoint print_env_aux (short : bool) (prefix : nat) (Σ : global_env) (acc : t) : t :=
    match prefix with
    | 0 => match Σ.(declarations) with [] => acc | _ => ("..." ^ nl ^ acc) end
    | S n =>
      match Σ.(declarations) with
      | [] => acc
      | (kn, InductiveDecl mib) :: decls =>
        let Σ' := (set_declarations Σ decls, mib.(ind_universes)) in
        let names := fresh_names Σ' [] (arities_context mib.(ind_bodies)) in
        print_env_aux short n Σ'.1
          (print_recursivity_kind mib.(ind_finite) ^ " " ^
          print_list (print_one_ind Σ' short names mib) (nl ^ "with ") mib.(ind_bodies) ^ "." ^
          nl ^ acc)
      | (kn, ConstantDecl cb) :: decls =>
        let Σ' := (set_declarations Σ decls, cb.(cst_universes)) in
        print_env_aux short n Σ'.1
          ((match cb.(cst_body) with
            | Some _ => "Definition "
            | None => "Axiom "
          end) ^ string_of_kername kn ^ " : " ^ print_term Σ' true nil true false cb.(cst_type) ^
          match cb.(cst_body) with
          | Some b =>
            if short then ("..." ^ nl)
            else (" := " ^ nl ^ print_term Σ' true nil true false b ^ "." ^ nl)
          | None => "."
          end ^ acc)
      end
    end.

  Definition print_env (short : bool) (prefix : nat) Σ :=
    print_env_aux short prefix Σ (Tree.string "").

  Definition print_program (short : bool) (prefix : nat) (p : program) : t :=
    print_env short prefix (fst p) ^ nl ^ print_term (empty_ext (fst p)) true nil true false (snd p).

End PrintTermTree.

Definition print_term Σ all Γ top inapp t :=
  Tree.to_string (PrintTermTree.print_term Σ all Γ top inapp t).

Definition print_context Σ Γ Δ : string :=
  Tree.to_string (PrintTermTree.print_context_gen Σ (PrintTermTree.print_term Σ true) Γ Δ).2.

Definition print_env (short : bool) (prefix : nat) Σ :=
  Tree.to_string (PrintTermTree.print_env short prefix Σ).

#[export] Instance show_env : Show global_env :=
  fun Σ => print_env false (List.length Σ.(declarations)) Σ.

Definition print_program (short : bool) (prefix : nat) (p : program) : string :=
  Tree.to_string (PrintTermTree.print_program short prefix p).

#[export] Instance show_program : Show program :=
  fun p => print_program false (List.length p.1.(declarations)) p.
