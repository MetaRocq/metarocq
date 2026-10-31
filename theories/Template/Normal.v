(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import Ast Typing.


Section Normal.
  Context (Σ : global_env).

  Inductive normal (Γ : context) : term -> Prop :=
  | nf_ne t : neutral Γ t -> normal Γ t
  | nf_sort s : normal Γ (tSort s)
  | nf_prod na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                     normal Γ (tProd na A B)
  | nf_lam na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                    normal Γ (tLambda na A B)
  | nf_cstrapp i n u v : All (normal Γ) v -> normal Γ (mkApps (tConstruct i n u) v)
  | nf_indapp i u v : All (normal Γ) v -> normal Γ (mkApps (tInd i u) v)
  | nf_fix mfix idx : All (normal Γ ∘ dbody) mfix ->
                      normal Γ (tFix mfix idx)
  | nf_cofix mfix idx : All (normal Γ ∘ dbody) mfix ->
                        normal Γ (tCoFix mfix idx)

  with neutral (Γ : context) : term -> Prop :=
       | ne_rel i :
           option_map decl_body (nth_error Γ i) = Some None ->
           neutral Γ (tRel i)
       | ne_var v : neutral Γ (tVar v)
       | ne_evar n l : neutral Γ (tEvar n l)
       | ne_const c u decl :
           lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
           neutral Γ (tConst c u)
       | ne_app f v : neutral Γ f -> Forall (normal Γ) v -> neutral Γ (tApp f v)
       | ne_case i p c brs : neutral Γ c ->
            (* FIXME context of the branch can contain let-ins *)
            Forall (normal Γ ∘ bbody) brs ->
            neutral Γ (tCase i p c brs)
       | ne_proj p c : neutral Γ c -> neutral Γ (tProj p c).

  Inductive whnf (Γ : context) : term -> Prop :=
  | whnf_ne t : whne Γ t -> whnf Γ t
  | whnf_sort s : whnf Γ (tSort s)
  | whnf_prod na A B : whnf Γ (tProd na A B)
  | whnf_lam na A B : whnf Γ (tLambda na A B)
  | whnf_cstrapp i n u v : whnf Γ (mkApps (tConstruct i n u) v)
  | whnf_indapp i u v : whnf Γ (mkApps (tInd i u) v)
  | whnf_fix mfix idx : whnf Γ (tFix mfix idx)
  | whnf_cofix mfix idx : whnf Γ (tCoFix mfix idx)

  with whne (Γ : context) : term -> Prop :=
  | whne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      whne Γ (tRel i)
  | whne_var v : whne Γ (tVar v)
  | whne_evar n l : whne Γ (tEvar n l)
  | whne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
      whne Γ (tConst c u)
  | whne_app f v : whne Γ f -> whne Γ (tApp f v)
  | whne_case i p c brs : whne Γ c -> whne Γ (tCase i p c brs)
  | whne_proj p c : whne Γ c -> whne Γ (tProj p c).
End Normal.
