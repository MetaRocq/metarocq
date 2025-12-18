(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv.

(** * Pretty printing *)

Section freshnames.
  Context (Σ : global_context).

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl {| ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  Fixpoint decompose_lam (t : term) (n : nat) : (list name) * term :=
    match n with
    | 0 => ([], t)
    | S n =>
      match t with
      | tLambda na B => let (ns, B) := decompose_lam B n in
                        (na :: ns, B)
      | _ => ([], t)
      end
    end.

  Definition is_fresh (Γ : context) (id : ident) :=
    List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' => negb (eqb id id')
         | nAnon => true
         end) Γ.

  Fixpoint name_from_term (t : term) :=
    match t with
    | tRel _ | tVar _ | tEvar _ _ => "H"
    | tLambda na t => "f"
    | tLetIn na b t' => name_from_term t'
    | tApp f _ => name_from_term f
    | tConst c => "x"
    | _ => "U"
    end.

  Definition fresh_id_from Γ n id :=
    let fix aux i :=
      match i with
      | 0 => id
      | S i' =>
        let id' := id ^ (string_of_nat (n - i)) in
        if is_fresh Γ id' then id'
        else aux i'
      end
    in aux n.

  Definition fresh_name (Γ : context) (na : name) (t : term) :=
    let id := match na with
              | nNamed id => id
              | nAnon => name_from_term t
              end
    in
    if is_fresh Γ id then nNamed id
    else nNamed (fresh_id_from Γ 10 id).
End freshnames.

Module PrintTermTree.
  Import Tree.
  Infix "^" := append.

  Section print_term.
    Context (Σ : global_context).

    Definition print_def {A : Set} (f : A -> t) (def : def A) :=
      string_of_name (dname def) ^ " { struct " ^ string_of_nat (rarg def) ^ " }"
                    ^ " := " ^ nl ^ f (dbody def).

    Definition print_defs (print_term : context -> bool -> bool -> term -> t) Γ (defs : mfixpoint term) :=
      let ctx' := MRList.rev_map (fun d => {| decl_name := dname d; decl_body := None |}) defs in
      print_list (print_def (print_term (ctx' ++ Γ)%list true false)) (nl ^ " with ") defs.

    Definition print_prim (soft : EAst.term -> Tree.t) (p : @prim_val EAst.term) : Tree.t :=
      match p.π2 return Tree.t with
      | primIntModel f => "(int: " ^ show f ^ ")"
      | primFloatModel f => "(float: " ^ show f ^ ")"
      | primStringModel f => "(string: " ^ show f ^ ")"
      | primArrayModel a => "(array:" ^ soft a.(array_default) ^ " , " ^ string_of_list soft a.(array_value) ^ ")"
      end.

    Fixpoint print_term (Γ : context) (top : bool) (inapp : bool) (t : term) {struct t} : Tree.t :=
    match t with
    | tBox => "∎"
    | tRel n =>
      match nth_error Γ n with
      | Some {| decl_name := na |} =>
        match na with
        | nAnon => "Anonymous (" ^ string_of_nat n ^ ")"
        | nNamed id => id
        end
      | None => "UnboundRel(" ^ string_of_nat n ^ ")"
      end
    | tVar n => "Var(" ^ n ^ ")"
    | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "[]" (* TODO *)  ^ ")"
    | tLambda na body =>
      let na' := fresh_name Γ na t in
      parens top ("fun " ^ string_of_name na'
                                  ^ " => " ^ print_term (vass na' :: Γ) true false body)
    | tLetIn na def body =>
      let na' := fresh_name Γ na t in
      parens top ("let " ^ string_of_name na' ^
                        " := " ^ print_term Γ true false def ^ " in " ^ nl ^
                        print_term (vdef na' def :: Γ) true false body)
    | tApp f l =>
      parens (top || inapp) (print_term Γ false true f ^ " " ^ print_term Γ false false l)
    | tConst c => string_of_kername c
    | tConstruct (mkInd i k as ind) l args =>
      match lookup_ind_decl Σ i k with
      | Some oib =>
        match nth_error oib.(ind_ctors) l with
        | Some cstr =>
          match args with
          | [] => cstr.(cstr_name)
          | args => parens (top || inapp) (cstr.(cstr_name) ^ "[" ^ print_list (print_term Γ false false) " " args ^ "]")
          end
        | None =>
          "UnboundConstruct(" ^ string_of_inductive ind ^ "," ^ string_of_nat l ^ ")"
        end
      | None =>
        "UnboundConstruct(" ^ string_of_inductive ind ^ "," ^ string_of_nat l ^ ")"
      end
    | tCase (mkInd mind i as ind, pars) t brs =>
      match lookup_ind_decl Σ mind i with
      | Some oib =>
        let fix print_args Γ nas br {struct nas} :=
          match nas with
          | [] => "=>" ^ " " ^ br Γ
          | na :: nas =>
            string_of_name na ^ "  " ^ print_args (vass na :: Γ) nas br
          end
        in
        let brs := map (fun '(nas, br) => print_args Γ (List.rev nas) (fun Γ => print_term Γ true false br)) brs in
        let brs := combine brs oib.(ind_ctors) in
        parens top ("match " ^ print_term Γ true false t ^
                    " with " ^ nl ^
                    print_list (fun '(b, cstr) => (cstr.(cstr_name) : String.t) ^ " " ^ b)
                    (nl ^ " | ") brs ^ nl ^ "end" ^ nl)
      | None =>
        "Case(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_term t ^ ","
                ^ string_of_list (fun b => string_of_term (snd b)) brs ^ ")"
      end
    | tProj p c =>
      match lookup_projection Σ p with
      | Some (mdecl, idecl, cdecl, pdecl) =>
        print_term Γ false false c ^ ".(" ^ pdecl.(proj_name) ^ ")"
      | None =>
        "UnboundProj(" ^ string_of_inductive p.(proj_ind) ^ "," ^ string_of_nat p.(proj_npars)
          ^ "," ^ string_of_nat p.(proj_arg) ^ ","
          ^ print_term Γ true false c ^ ")"
      end


    | tFix l n =>
      parens top ("let fix " ^ print_defs print_term Γ l ^ nl ^
                            " in " ^ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
    | tCoFix l n =>
      parens top ("let cofix " ^ print_defs print_term Γ l ^ nl ^
                                " in " ^ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
    | tPrim p => parens top (print_prim (print_term Γ false false) p)
    | tLazy t => parens top ("lazy " ^ print_term Γ false false t)
    | tForce t => parens top ("force " ^ print_term Γ false false t)
    end.
  End print_term.

  Definition pr Σ (t : term) := print_term Σ [] true false t.

  Definition print_constant_body Σ kn decl :=
    match decl.(cst_body) with
    | Some b => "Definition " ^ string_of_kername kn ^ " := " ^ pr Σ b
    | None => "Axiom " ^ string_of_kername kn
    end.

  Definition pr_allowed_elim (elims : Universes.allowed_eliminations) :=
    match elims with
    | Universes.IntoSProp => "into sprop"
    | Universes.IntoPropSProp => "into prop or sprop"
    | Universes.IntoSetPropSProp => "into set, prop or sprop"
    | Universes.IntoAny => "into any sort"
    end.

  Definition print_one_inductive_body npars body : Tree.t :=
    let params := string_of_nat npars ^ " parameters" in
    let prop := if body.(ind_propositional) then "propositional" else "computational" in
    let kelim := pr_allowed_elim body.(ind_kelim) in
    let ctors := print_list (fun cstr => "| " ^ (cstr.(cstr_name) : ident) ^ " " ^
      string_of_nat cstr.(cstr_nargs) ^ " arguments") nl body.(ind_ctors) in
    let projs :=
    match body.(ind_projs) return Tree.t with
    | [] => ""
    | _ => nl ^ "projections: " ^ print_list (fun x => x.(proj_name)) ", " body.(ind_projs)
    end
    in
    body.(ind_name) ^ "(" ^ params ^ "," ^ prop ^ ", elimination " ^ kelim ^ ") := " ^ nl ^ ctors ^ projs.

  Definition print_recursivity_kind k :=
    match k with
    | Finite => "Inductive"
    | CoFinite => "CoInductive"
    | BiFinite => "Variant"
    end.

  Definition print_inductive_body decl :=
    print_recursivity_kind decl.(ind_finite) ^ " " ^
    print_list (print_one_inductive_body decl.(ind_npars)) (nl ^ " with ") decl.(ind_bodies).

  Definition print_decl Σ '(kn, d) :=
    match d with
    | ConstantDecl body => print_constant_body Σ kn body
    | InductiveDecl mind => print_inductive_body mind
    end.

  Definition print_global_context (g : global_context) :=
    print_list (print_decl g) nl (List.rev g).
  Notation print_env := print_global_context.

  Definition print_program (p : program) : t :=
    "Environment: " ^ nl ^
    print_env p.1 ^ nl ^
    "Program: " ^ pr p.1 p.2.

End PrintTermTree.

Definition pr Σ := Tree.to_string ∘ PrintTermTree.pr Σ.

Definition print_global_context := Tree.to_string ∘ PrintTermTree.print_global_context.

Definition print_program := Tree.to_string ∘ PrintTermTree.print_program.
