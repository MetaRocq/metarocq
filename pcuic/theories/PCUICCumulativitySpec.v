(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Reflect.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICEquality
     PCUICLiftSubst PCUICUnivSubst PCUICCases PCUICOnFreeVars.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

Definition cumul_predicate (cumul : context -> term -> term -> Type) cumul_universe Γ p p' :=
  All2 (cumul Γ) p.(pparams) p'.(pparams) ×
  cmp_universe_instance cumul_universe p.(puinst) p'.(puinst) ×
  eq_context_upto_names p.(pcontext) p'.(pcontext) ×
  cumul (Γ ,,, inst_case_predicate_context p) p.(preturn) p'.(preturn).

Definition cumul_predicate_dep {cumul cumul_universe Γ p p'}
  (H : cumul_predicate cumul cumul_universe Γ p p')
  (cumul' : forall Γ p p', cumul Γ p p' -> Type)
  cumul_universe'
  :=
  let '(Hparams, (Huinst, (Heq, Hcumul))) := H in
  All2_dep (cumul' Γ) Hparams ×
  cmp_universe_instance_dep cumul_universe cumul_universe' Huinst ×
  cumul' _ _ _ Hcumul.

Lemma cumul_predicate_undep {cumul cumul_universe Γ p p' H cumul' cumul_universe'} :
  @cumul_predicate cumul' cumul_universe' Γ p p' <~>
  @cumul_predicate_dep cumul cumul_universe Γ p p' H (fun Γ p p' _ => cumul' Γ p p') (fun x y _ => on_rel cumul_universe' Universe.of_level x y).
Proof.
  cbv [cumul_predicate cumul_predicate_dep cmp_universe_instance cmp_universe_instance_dep] in *.
  split; intro; repeat destruct ?; subst; rdest; try assumption.
  all: repeat first [ assumption | toAll ].
Qed.

Definition cumul_branch (cumul_term : context -> term -> term -> Type) Γ p br br' :=
  eq_context_upto_names br.(bcontext) br'.(bcontext) ×
  cumul_term (Γ ,,, inst_case_branch_context p br) br.(bbody) br'.(bbody).

Definition cumul_branches cumul_term Γ p brs brs' := All2 (cumul_branch cumul_term Γ p) brs brs'.

Definition cumul_mfixpoint (cumul_term : context -> term -> term -> Type) Γ mfix mfix' :=
  All2 (fun d d' =>
    cumul_term Γ d.(dtype) d'.(dtype) ×
    cumul_term (Γ ,,, fix_context mfix) d.(dbody) d'.(dbody) ×
    d.(rarg) = d'.(rarg) ×
    eq_binder_annot d.(dname) d'.(dname)
  ) mfix mfix'.

Reserved Notation " Σ ;;; Γ ⊢ t ≤s[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤s[ pb ]  u").

Definition cumul_Ind_univ {cf} (Σ : global_env_ext) pb i napp :=
  cmp_global_instance Σ (compare_universe Σ) pb (IndRef i) napp.

Definition cumul_Construct_univ {cf} (Σ : global_env_ext) pb  i k napp :=
  cmp_global_instance Σ (compare_universe Σ) pb (ConstructRef i k) napp.

(** * Definition of cumulativity and conversion relations *)
Local Unset Elimination Schemes.
Inductive cumulSpec0 {cf : checker_flags} (Σ : global_env_ext) Γ (pb : conv_pb) : term -> term -> Type :=

(* transitivity *)

| cumul_Trans : forall t u v,
    is_closed_context Γ -> is_open_term Γ u ->
    Σ ;;; Γ ⊢ t ≤s[pb] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] v ->
    Σ ;;; Γ ⊢ t ≤s[pb] v

(* symmetry *)

| cumul_Sym : forall t u,
    Σ ;;; Γ ⊢ t ≤s[Conv] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] t

(* reflexivity *)

| cumul_Refl : forall t,
    Σ ;;; Γ ⊢ t ≤s[pb] t

(* Cumulativity rules *)

| cumul_Ind : forall i u u' args args',
    cumul_Ind_univ Σ pb i #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤s[pb] mkApps (tInd i u') args'

| cumul_Construct : forall i k u u' args args',
    cumul_Construct_univ Σ pb i k #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tConstruct i k u) args ≤s[pb] mkApps (tConstruct i k u') args'

| cumul_Sort : forall s s',
    compare_sort Σ pb s s' ->
    Σ ;;; Γ ⊢ tSort s ≤s[pb] tSort s'

| cumul_Const : forall c u u',
    cmp_universe_instance (compare_universe Σ Conv) u u' ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] tConst c u'

(* congruence rules *)

| cumul_Evar : forall e args args',
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ tEvar e args ≤s[pb] tEvar e args'

| cumul_App : forall t t' u u',
    Σ ;;; Γ ⊢ t ≤s[pb] t' ->
    Σ ;;; Γ ⊢ u ≤s[Conv] u' ->
    Σ ;;; Γ ⊢ tApp t u ≤s[pb] tApp t' u'

| cumul_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vass na ty ⊢ t ≤s[Conv] t' ->
    Σ ;;; Γ ⊢ tLambda na ty t ≤s[pb] tLambda na' ty' t'

| cumul_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ a ≤s[Conv] a' ->
    Σ ;;; Γ ,, vass na a ⊢ b ≤s[pb] b' ->
    Σ ;;; Γ ⊢ tProd na a b ≤s[pb] tProd na' a' b'

| cumul_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ t ≤s[Conv] t' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vdef na t ty ⊢ u ≤s[Conv] u' ->
    Σ ;;; Γ ⊢ tLetIn na t ty u ≤s[pb] tLetIn na' t' ty' u'

| cumul_Case indn : forall p p' c c' brs brs',
    cumul_predicate (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) (compare_universe Σ Conv) Γ p p' ->
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    cumul_branches (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) Γ p brs brs' ->
    Σ ;;; Γ ⊢ tCase indn p c brs ≤s[pb] tCase indn p' c' brs'

| cumul_Proj : forall p c c',
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    Σ ;;; Γ ⊢ tProj p c ≤s[pb] tProj p c'

| cumul_Fix : forall mfix mfix' idx,
    cumul_mfixpoint (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx ≤s[pb] tFix mfix' idx

| cumul_CoFix : forall mfix mfix' idx,
    cumul_mfixpoint (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tCoFix mfix idx ≤s[pb] tCoFix mfix' idx

| cumul_Prim p p' :
  onPrims (fun x y => Σ ;;; Γ ⊢ x ≤s[Conv] y) (compare_universe Σ Conv) p p' ->
  Σ ;;; Γ ⊢ tPrim p ≤s[pb] tPrim p'

(** Reductions *)

(** Beta red *)
| cumul_beta : forall na t b a,
    Σ ;;; Γ ⊢ tApp (tLambda na t b) a ≤s[pb] b {0 := a}

(** Let *)
| cumul_zeta : forall na b t b',
    Σ ;;; Γ ⊢ tLetIn na b t b' ≤s[pb] b' {0 := b}

| cumul_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ ⊢ tRel i ≤s[pb] lift0 (S i) body

(** iota red *)
| cumul_iota : forall ci c u args p brs br,
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs  ≤s[pb] iota_red ci.(ci_npar) p args br

(** Fix unfolding, with guard *)
| cumul_fix : forall mfix idx args narg fn,
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ ⊢ mkApps (tFix mfix idx) args ≤s[pb] mkApps fn args

(** CoFix-case unfolding *)
| cumul_cofix_case : forall ip p mfix idx args narg fn brs,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs ≤s[pb] tCase ip p (mkApps fn args) brs

(** CoFix-proj unfolding *)
| cumul_cofix_proj : forall p mfix idx args narg fn,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ≤s[pb] tProj p (mkApps fn args)

(** Constant unfolding *)
| cumul_delta : forall c decl body (isdecl : declared_constant Σ c decl) u,
    decl.(cst_body) = Some body ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] body@[u]

(** Proj *)
| cumul_proj : forall p args u arg,
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ≤s[pb] arg

where " Σ ;;; Γ ⊢ t ≤s[ pb ] u " := (@cumulSpec0 _ Σ Γ pb t u) : type_scope.

Definition convSpec `{checker_flags} (Σ : global_env_ext) Γ := cumulSpec0 Σ Γ Conv.
Definition cumulSpec `{checker_flags} (Σ : global_env_ext) Γ := cumulSpec0 Σ Γ Cumul.

(* ** Syntactic cumulativity up-to universes *)

Notation " Σ ;;; Γ |- t <=s u " := (@cumulSpec _ Σ Γ t u) (at level 50, Γ, t, u at next level).
Notation " Σ ;;; Γ |- t =s u " := (@convSpec _ Σ Γ t u) (at level 50, Γ, t, u at next level).

Include PCUICConversion.

Module PCUICConversionParSpec <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.
  Definition cumul_gen := @cumulSpec0.
End PCUICConversionParSpec.


Notation " Σ ⊢ Γ ≤s[ pb ] Δ " := (@cumul_pb_context _ pb Σ Γ Δ) (at level 50, Γ, Δ at next level) : type_scope.
Notation " Σ ⊢ Γ ≤s Δ " := (@cumul_pb_context _ Cumul Σ Γ Δ) (at level 50, Γ, Δ at next level) : type_scope.
Notation " Σ ⊢ Γ =s Δ " := (@cumul_pb_context _ Conv Σ Γ Δ) (at level 50, Γ, Δ at next level) : type_scope.

#[global]
Instance cumul_spec_refl {cf:checker_flags} Σ Γ pb : Reflexive (cumulSpec0 Σ Γ pb).
Proof. intro; constructor 3. Qed.

#[global]
Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (convSpec Σ Γ) := _.

#[global]
Instance cumul_pb_decls_refl {cf:checker_flags} pb Σ Γ Γ' : Reflexive (cumul_pb_decls cumulSpec0 pb Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; reflexivity.
Qed.

#[global]
Instance conv_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (conv_decls cumulSpec0 Σ Γ Γ') := _.
#[global]
Instance cumul_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (cumul_decls cumulSpec0 Σ Γ Γ') := _.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Notation conv_context := (conv_context cumulSpec0 Σ).
  Notation cumul_context := (cumul_context cumulSpec0 Σ).

  Global Instance cumul_pb_ctx_refl pb : Reflexive (cumul_pb_context cumulSpec0 pb Σ).
  Proof using Type.
    intro Γ; induction Γ; try econstructor; auto.
    reflexivity.
  Qed.

  Global Instance conv_ctx_refl : Reflexive (conv_context) := _.
  Global Instance cumul_ctx_refl : Reflexive (cumul_context) := _.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

End ContextConversion.

Lemma cumulSpec0_rect :
  forall cf (Σ : global_env_ext)
         (P : forall cf Σ Γ pb u v, @cumulSpec0 cf Σ Γ pb u v -> Type),

    (* beta *)
    (forall (Γ : context) (pb : conv_pb) (na : aname) (t b a : term),
        P cf Σ Γ pb (tApp (tLambda na t b) a) (b {0 := a}) (cumul_beta _ _ _ _ _ _ _)) ->

    (* let *)
    (forall (Γ : context) (pb : conv_pb) (na : aname) (b t b' : term),
        P cf Σ Γ pb (tLetIn na b t b') (b' {0 := b}) (cumul_zeta _ _ _ _ _ _ _)) ->

    (forall (Γ : context) (pb : conv_pb) (i : nat) (body : term)
            (pf : option_map decl_body (nth_error Γ i) = Some (Some body)),
        P cf Σ Γ pb (tRel i) ((lift0 (S i)) body) (cumul_rel _ _ _ _ _ pf)) ->

    (* iota *)
    (forall (Γ : context) (pb : conv_pb) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
            (p : predicate term) (brs : list (branch term)) br
            (Hbrs : nth_error brs c = Some br)
            (Hnargs : #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat),
        P cf Σ Γ pb (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
          (iota_red ci.(ci_npar) p args br)
          (cumul_iota _ _ _ _ _ _ _ _ _ _ Hbrs Hnargs)) ->

    (* fix unfolding *)
    (forall (Γ : context) (pb : conv_pb) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term)
            (Hufix : unfold_fix mfix idx = Some (narg, fn))
            (Hisctor : is_constructor narg args = true),
        P cf Σ Γ pb (mkApps (tFix mfix idx) args) (mkApps fn args)
          (cumul_fix _ _ _ _ _ _ _ _ Hufix Hisctor)) ->

    (* cofix unfolding *)
    (forall (Γ : context) (pb : conv_pb) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
            (args : list term) (narg : nat) (fn : term) (brs : list (branch term))
            (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
        P cf Σ Γ pb (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)
          (cumul_cofix_case _ _ _ _ _ _ _ _ _ _ _ Hucofix)) ->

    (forall (Γ : context) (pb : conv_pb) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
            (narg : nat) (fn : term)
            (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
        P cf Σ Γ pb (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))
          (cumul_cofix_proj _ _ _ _ _ _ _ _ _ Hucofix)) ->

    (* constant unfolding *)
    (forall (Γ : context) (pb : conv_pb) c (decl : constant_body) (body : term)
            (Hdecl_decl : declared_constant Σ c decl)
            (u : Instance.t)
            (Hdecl_body : cst_body decl = Some body),
        P cf Σ Γ pb (tConst c u) (subst_instance u body)
          (cumul_delta _ _ _ _ _ _ Hdecl_decl _ Hdecl_body)) ->

    (* Proj *)
    (forall (Γ : context) (pb : conv_pb)p (args : list term) (u : Instance.t)
            (arg : term)
            (Hargs : nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg),
        P cf Σ Γ pb (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg
          (cumul_proj _ _ _ _ _ _ _ Hargs)) ->

    (* transitivity *)
    (forall (Γ : context) (pb : conv_pb) (t u v : term)
            (Hclosed_ctx : is_closed_context Γ) (Hopen_term : is_open_term Γ u)
            (Htu : cumulSpec0 Σ Γ pb t u) (_ : P cf Σ Γ pb t u Htu)
            (Huv : cumulSpec0 Σ Γ pb u v) (_ : P cf Σ Γ pb u v Huv),
        P cf Σ Γ pb t v
          (cumul_Trans _ _ _ _ _ _ Hclosed_ctx Hopen_term Htu Huv)) ->

    (* symmetry *)
    (forall (Γ : context) (pb : conv_pb) (t u : term)
            (Hut : cumulSpec0 Σ Γ Conv u t) (_ : P cf Σ Γ Conv u t Hut),
        P cf Σ Γ pb t u
          (cumul_Sym _ _ _ _ _ Hut)) ->

    (* reflexivity *)
    (forall (Γ : context) (pb : conv_pb) (t : term),
        P cf Σ Γ pb t t
          (cumul_Refl _ _ _ _)) ->

    (* congruence rules *)

    (forall (Γ : context) (pb : conv_pb) (ev : nat) (l l' : list term)
            (H : All2 (cumulSpec0 Σ Γ Conv) l l') (_ : All2_dep (P cf Σ Γ Conv) H),
        P cf Σ Γ pb (tEvar ev l) (tEvar ev l')
          (cumul_Evar _ _ _ _ _ _ H)) ->

    (forall (Γ : context) (pb : conv_pb) (t t' u u' : term)
            (Htt' : cumulSpec0 Σ Γ pb t t') (_ : P cf Σ Γ pb t t' Htt')
            (Huu' : cumulSpec0 Σ Γ Conv u u') (_ : P cf Σ Γ Conv u u' Huu'),
        P cf Σ Γ pb (tApp t u) (tApp t' u')
          (cumul_App _ _ _ _ _ _ _ Htt' Huu')) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : aname) (ty ty' t t' : term)
            (Hna : eq_binder_annot na na')
            (Hty : cumulSpec0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
            (Ht : cumulSpec0 Σ (Γ ,, vass na ty) Conv t t') ( _ : P cf Σ (Γ ,, vass na ty) Conv t t' Ht),
        P cf Σ Γ pb (tLambda na ty t) (tLambda na' ty' t')
          (cumul_Lambda _ _ _ _ _ _ _ _ _ Hna Hty Ht)) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : binder_annot name) (a a' b b' : term)
            (Hna : eq_binder_annot na na')
            (Ha : cumulSpec0 Σ Γ Conv a a') (_ : P cf Σ Γ Conv a a' Ha)
            (Hb : cumulSpec0 Σ (Γ,, vass na a) pb b b') (_ : P cf Σ (Γ,, vass na a) pb b b' Hb),
        P cf Σ Γ pb (tProd na a b) (tProd na' a' b')
          (cumul_Prod _ _ _ _ _ _ _ _ _ Hna Ha Hb)) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : binder_annot name) (t t' ty ty' u u' : term)
            (Hna : eq_binder_annot na na')
            (Ht : cumulSpec0 Σ Γ Conv t t') (_ : P cf Σ Γ Conv t t' Ht)
            (Hty : cumulSpec0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
            (Hu : cumulSpec0 Σ (Γ,, vdef na t ty) Conv u u') (_ : P cf Σ (Γ,, vdef na t ty) Conv u u' Hu),
        P cf Σ Γ pb (tLetIn na t ty u) (tLetIn na' t' ty' u')
          (cumul_LetIn _ _ _ _ _ _ _ _ _ _ _ Hna Ht Hty Hu)) ->

    (forall (Γ : context) (pb : conv_pb) (indn : case_info) (p p' : predicate term)
            (c c' : term) (brs brs' : list (branch term))
            (Hp : cumul_predicate (fun Γ => cumulSpec0 Σ Γ Conv) (compare_universe Σ Conv) Γ p p')
            (_ : cumul_predicate_dep Hp (fun Γ => P cf Σ Γ Conv) (fun l l' _ => on_rel (fun _ _ => True) Universe.of_level l l'))
            (Hc : cumulSpec0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc)
            (Hbody : cumul_branches (fun Γ => cumulSpec0 Σ Γ Conv) Γ p brs brs')
            (_ : All2_dep
                   (fun br br' Hc => P cf Σ (Γ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br') (snd Hc)) Hbody),
        P cf Σ Γ pb (tCase indn p c brs) (tCase indn p' c' brs')
          (cumul_Case _ _ _ _ _ _ _ _ _ _ Hp Hc Hbody)) ->

    (forall (Γ : context) (pb : conv_pb)
            (p : projection) (c c' : term)
            (Hc : cumulSpec0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc),
        P cf Σ Γ pb (tProj p c) (tProj p c')
          (cumul_Proj _ _ _ _ _ _ Hc)) ->

    (forall (Γ : context) (pb : conv_pb)
            (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
            (H : All2
                   (fun x y : def term =>
                      (cumulSpec0 Σ Γ Conv (dtype x) (dtype y))
                      * ((cumulSpec0 Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y))
                           × (rarg x = rarg y)
                           × eq_binder_annot (dname x) (dname y)))
                   mfix mfix')
            (_ : All2_dep
                   (fun x y H
                    => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                   H),
        P cf Σ Γ pb (tFix mfix idx) (tFix mfix' idx)
          (cumul_Fix _ _ _ _ _ _ H)) ->

    (forall (Γ : context) (pb : conv_pb)
            (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
            (H : All2
                   (fun x y : def term =>
                      (cumulSpec0 Σ Γ Conv (dtype x) (dtype y))
                        × ((cumulSpec0 Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y))
                             × (rarg x = rarg y)
                             × (eq_binder_annot (dname x) (dname y))))
                   mfix mfix')
            (_ : All2_dep
                   (fun x y H
                    => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                   H),
        P cf Σ Γ pb (tCoFix mfix idx) (tCoFix mfix' idx)
          (cumul_CoFix _ _ _ _ _ _ H)) ->

    (forall Γ pb p p' (e : onPrims (cumulSpec0 Σ Γ Conv) (eq_universe Σ) p p'),
      onPrims_dep (cumulSpec0 Σ Γ Conv) (eq_universe Σ) (P cf Σ Γ Conv) (fun _ _ _ => True) p p' e ->
      P cf Σ Γ pb (tPrim p) (tPrim p') (cumul_Prim _ _ _ _ _ e)) ->

    (* cumulativity rules *)

    (forall (Γ : context) (pb : conv_pb) (i : inductive) (u u' : list Level.t)
            (args args' : list term)
            (Hu : cumul_Ind_univ Σ pb i #|args| u u')
            (Hargs : All2 (cumulSpec0 Σ Γ Conv) args args')
            (_ : All2_dep (P cf Σ Γ Conv) Hargs),
        P cf Σ Γ pb (mkApps (tInd i u) args) (mkApps (tInd i u') args')
          (cumul_Ind _ _ _ _ _ _ _ _ Hu Hargs)) ->

    (forall (Γ : context) (pb : conv_pb) (i : inductive) (k : nat)
            (u u' : list Level.t) (args args' : list term)
            (Hu : cumul_Construct_univ Σ pb i k #|args| u u')
            (Hargs : All2 (cumulSpec0 Σ Γ Conv) args args')
            (_ : All2_dep (P cf Σ Γ Conv) Hargs),
        P cf Σ Γ pb (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args')
          (cumul_Construct _ _ _ _ _ _ _ _ _ Hu Hargs)) ->

    (forall (Γ : context) (pb : conv_pb) (s s' : sort)
            (Hs : compare_sort Σ pb s s'),
        P cf Σ Γ pb (tSort s) (tSort s')
          (cumul_Sort _ _ _ _ _ Hs)) ->

    (forall (Γ : context) (pb : conv_pb) (c : kername) (u u' : list Level.t)
            (Hu : cmp_universe_instance (compare_universe Σ Conv) u u'),
        P cf Σ Γ pb (tConst c u) (tConst c u')
          (cumul_Const _ _ _ _ _ _ Hu)) ->

    forall (Γ : context) (pb : conv_pb) (t t0 : term) (Ht : @cumulSpec0 cf Σ Γ pb t t0), P cf Σ Γ pb t t0 Ht.
Proof.
  intros. rename Ht into Xlast.
  revert Γ pb t t0 Xlast.
  fix aux 5. intros Γ pb t u Xlast.
  move aux at top.
  destruct Xlast.
  - eapply X8; eauto.
  - eapply X9; eauto.
  - eapply X10; eauto.
  - eapply X21; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct a; constructor; auto.
  - eapply X22; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct a; constructor; auto.
  - eapply X23; eauto.
  - eapply X24; eauto.
  - eapply X11; eauto.
    revert args args' a.
    fix aux' 3; destruct a; constructor; auto.
  - eapply X12; eauto.
  - eapply X13; eauto.
  - eapply X14; eauto.
  - eapply X15; eauto.
  - eapply X16 ; eauto.
    + unfold cumul_predicate in *. destruct c0 as [c0 [cuniv [ccontext creturn]]].
      repeat split ; eauto.
      * revert c0. generalize (pparams p), (pparams p').
        fix aux' 3; destruct c0; constructor; auto.
      * apply Forall2_dep_from_nth_error; intros; exact I.
    + revert brs brs' c1.
      fix aux' 3; destruct c1; constructor; intuition auto.
  - eapply X17 ; eauto.
  - eapply X18 ; eauto.
    revert c. unfold cumul_mfixpoint.
    set (mfixAbs_context := fix_context mfix).
    clearbody mfixAbs_context.
    revert mfix mfix'.
    fix aux' 3; destruct c; constructor.
    + intuition auto.
    + auto.
  - eapply X19 ; eauto.
    revert c. unfold cumul_mfixpoint.
    set (mfixAbs_context := fix_context mfix).
    clearbody mfixAbs_context.
    revert mfix mfix'.
    fix aux' 3; destruct c; constructor.
    + intuition auto.
    + auto.
  - eapply X20; eauto.
    clear -o aux.
    induction o; constructor; auto.
    clear -a0 aux. revert a0.
    induction a0; constructor; auto.
  - eapply X; eauto.
  - eapply X0; eauto.
  - eapply X1; eauto.
  - eapply X2; eauto.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.
  - eapply X7; eauto.
Defined.

Notation cumulSpec0_ind_all := cumulSpec0_rect (only parsing).

Definition cumulSpec0_rec
  : forall cf (Σ : global_env_ext)
           (P : forall cf Σ Γ pb u v, @cumulSpec0 cf Σ Γ pb u v -> Set),
    _
  := cumulSpec0_rect.

Definition cumulSpec0_ind
  : forall cf (Σ : global_env_ext)
           (P : forall cf Σ Γ pb u v, @cumulSpec0 cf Σ Γ pb u v -> Prop),
    _
  := cumulSpec0_rec.

Lemma convSpec0_ind_all :
  forall cf (Σ : global_env_ext)
         (P : forall cf Σ Γ pb u v, @cumulSpec0 cf Σ Γ pb u v -> Type),

        (* beta *)
       (forall (Γ : context) (na : aname) (t b a : term),
        P cf Σ Γ Conv (tApp (tLambda na t b) a) (b {0 := a}) (cumul_beta _ _ _ _ _ _ _)) ->

        (* let *)
       (forall (Γ : context) (na : aname) (b t b' : term), P cf Σ Γ Conv (tLetIn na b t b') (b' {0 := b}) (cumul_zeta _ _ _ _ _ _ _)) ->

       (forall (Γ : context) (i : nat) (body : term)
               (pf : option_map decl_body (nth_error Γ i) = Some (Some body)),
           P cf Σ Γ Conv (tRel i) ((lift0 (S i)) body) (cumul_rel _ _ _ _ _ pf)) ->

        (* iota *)
       (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br
          (Hbrs : nth_error brs c = Some br)
          (Hnargs : #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat),
           P cf Σ Γ Conv (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
             (iota_red ci.(ci_npar) p args br)
             (cumul_iota _ _ _ _ _ _ _ _ _ _ Hbrs Hnargs)) ->

        (* fix unfolding *)
       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term)
               (Hufix : unfold_fix mfix idx = Some (narg, fn))
               (Hisctor : is_constructor narg args = true),
           P cf Σ Γ Conv (mkApps (tFix mfix idx) args) (mkApps fn args)
             (cumul_fix _ _ _ _ _ _ _ _ Hufix Hisctor)) ->

      (* cofix unfolding *)
       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
               (args : list term) (narg : nat) (fn : term) (brs : list (branch term))
               (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
           P cf Σ Γ Conv (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)
             (cumul_cofix_case _ _ _ _ _ _ _ _ _ _ _ Hucofix)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
               (narg : nat) (fn : term)
               (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
           P cf Σ Γ Conv (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))
             (cumul_cofix_proj _ _ _ _ _ _ _ _ _ Hucofix)) ->

        (* constant unfolding *)
       (forall (Γ : context) c (decl : constant_body) (body : term)
               (Hdecl_decl : declared_constant Σ c decl)
               (u : Instance.t)
               (Hdecl_body : cst_body decl = Some body),
           P cf Σ Γ Conv (tConst c u) (subst_instance u body)
             (cumul_delta _ _ _ _ _ _ Hdecl_decl _ Hdecl_body)) ->

        (* Proj *)
       (forall (Γ : context)p (args : list term) (u : Instance.t)
               (arg : term)
               (Hargs : nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg),
           P cf Σ Γ Conv (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg
             (cumul_proj _ _ _ _ _ _ _ Hargs)) ->

        (* transitivity *)
       (forall (Γ : context) (t u v : term)
               (Hclosed_ctx : is_closed_context Γ) (Hopen_term : is_open_term Γ u)
               (Htu : cumulSpec0 Σ Γ Conv t u) (_ : P cf Σ Γ Conv t u Htu)
               (Huv : cumulSpec0 Σ Γ Conv u v) (_ : P cf Σ Γ Conv u v Huv),
           P cf Σ Γ Conv t v
             (cumul_Trans _ _ _ _ _ _ Hclosed_ctx Hopen_term Htu Huv)) ->

        (* symmetry *)
       (forall (Γ : context) (t u : term)
               (Hut : cumulSpec0 Σ Γ Conv u t) (_ : P cf Σ Γ Conv u t Hut),
           P cf Σ Γ Conv t u
             (cumul_Sym _ _ _ _ _ Hut)) ->

        (* reflexivity *)
        (forall (Γ : context) (t : term),
            P cf Σ Γ Conv t t
              (cumul_Refl _ _ _ _)) ->

        (* congruence rules *)

        (forall (Γ : context) (ev : nat) (l l' : list term)
                (H : All2 (cumulSpec0 Σ Γ Conv) l l') (_ : All2_dep (P cf Σ Γ Conv) H),
            P cf Σ Γ Conv (tEvar ev l) (tEvar ev l')
              (cumul_Evar _ _ _ _ _ _ H)) ->

        (forall (Γ : context) (t t' u u' : term)
                (Htt' : cumulSpec0 Σ Γ Conv t t') (_ : P cf Σ Γ Conv t t' Htt')
                (Huu' : cumulSpec0 Σ Γ Conv u u') (_ : P cf Σ Γ Conv u u' Huu'),
            P cf Σ Γ Conv (tApp t u) (tApp t' u')
              (cumul_App _ _ _ _ _ _ _ Htt' Huu')) ->

        (forall (Γ : context) (na na' : aname) (ty ty' t t' : term)
                (Hna : eq_binder_annot na na')
                (Hty : cumulSpec0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
                (Ht : cumulSpec0 Σ (Γ ,, vass na ty) Conv t t') ( _ : P cf Σ (Γ ,, vass na ty) Conv t t' Ht),
            P cf Σ Γ Conv (tLambda na ty t) (tLambda na' ty' t')
              (cumul_Lambda _ _ _ _ _ _ _ _ _ Hna Hty Ht)) ->

        (forall (Γ : context) (na na' : binder_annot name) (a a' b b' : term)
                (Hna : eq_binder_annot na na')
                (Ha : cumulSpec0 Σ Γ Conv a a') (_ : P cf Σ Γ Conv a a' Ha)
                (Hb : cumulSpec0 Σ (Γ,, vass na a) Conv b b') (_ : P cf Σ (Γ,, vass na a) Conv b b' Hb),
            P cf Σ Γ Conv (tProd na a b) (tProd na' a' b')
              (cumul_Prod _ _ _ _ _ _ _ _ _ Hna Ha Hb)) ->

     (forall (Γ : context) (na na' : binder_annot name) (t t' ty ty' u u' : term)
             (Hna : eq_binder_annot na na')
             (Ht : cumulSpec0 Σ Γ Conv t t') (_ : P cf Σ Γ Conv t t' Ht)
             (Hty : cumulSpec0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
             (Hu : cumulSpec0 Σ (Γ,, vdef na t ty) Conv u u') (_ : P cf Σ (Γ,, vdef na t ty) Conv u u' Hu),
         P cf Σ Γ Conv (tLetIn na t ty u) (tLetIn na' t' ty' u')
           (cumul_LetIn _ _ _ _ _ _ _ _ _ _ _ Hna Ht Hty Hu)) ->

      (forall (Γ : context) (indn : case_info) (p p' : predicate term)
              (c c' : term) (brs brs' : list (branch term))
              (Hp : cumul_predicate (fun Γ => cumulSpec0 Σ Γ Conv) (compare_universe Σ Conv) Γ p p')
              (_ : cumul_predicate_dep Hp (fun Γ => P cf Σ Γ Conv) (fun l l' _ => on_rel (fun _ _ => True) Universe.of_level l l'))
              (Hc : cumulSpec0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc)
              (Hbody : cumul_branches (fun Γ => cumulSpec0 Σ Γ Conv) Γ p brs brs')
              (_ : All2_dep
                     (fun br br' Hc => P cf Σ (Γ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br') (snd Hc)) Hbody),
          P cf Σ Γ Conv (tCase indn p c brs) (tCase indn p' c' brs')
            (cumul_Case _ _ _ _ _ _ _ _ _ _ Hp Hc Hbody)) ->

       (forall (Γ : context)
               (p : projection) (c c' : term)
               (Hc : cumulSpec0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc),
           P cf Σ Γ Conv (tProj p c) (tProj p c')
             (cumul_Proj _ _ _ _ _ _ Hc)) ->

       (forall (Γ : context)
               (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
               (H : cumul_mfixpoint (fun Γ => cumulSpec0 Σ Γ Conv) Γ mfix mfix')
               (_ : All2_dep
                      (fun x y H
                       => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                      H),
           P cf Σ Γ Conv (tFix mfix idx) (tFix mfix' idx)
             (cumul_Fix _ _ _ _ _ _ H)) ->

       (forall (Γ : context)
               (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
               (H : cumul_mfixpoint (fun Γ => cumulSpec0 Σ Γ Conv) Γ mfix mfix')
               (_ : All2_dep
                      (fun x y H
                       => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                      H),
           P cf Σ Γ Conv (tCoFix mfix idx) (tCoFix mfix' idx)
             (cumul_CoFix _ _ _ _ _ _ H)) ->

      (forall Γ p p' (e : onPrims (cumulSpec0 Σ Γ Conv) (eq_universe Σ) p p'),
        onPrims_dep (cumulSpec0 Σ Γ Conv) (eq_universe Σ) (P cf Σ Γ Conv) (fun _ _ _ => True) p p' e ->
        P cf Σ Γ Conv (tPrim p) (tPrim p') (cumul_Prim _ _ _ _ _ e)) ->

      (* cumulativity rules *)

      (forall (Γ : context) (i : inductive) (u u' : list Level.t)
              (args args' : list term)
              (Hu : cumul_Ind_univ Σ Conv i #|args| u u')
              (Hargs : All2 (cumulSpec0 Σ Γ Conv) args args')
              (_ : All2_dep (P cf Σ Γ Conv) Hargs),
          P cf Σ Γ Conv (mkApps (tInd i u) args) (mkApps (tInd i u') args')
            (cumul_Ind _ _ _ _ _ _ _ _ Hu Hargs)) ->

    (forall (Γ : context) (i : inductive) (k : nat)
            (u u' : list Level.t) (args args' : list term)
            (Hu : cumul_Construct_univ Σ Conv i k #|args| u u')
            (Hargs : All2 (cumulSpec0 Σ Γ Conv) args args')
            (_ : All2_dep (P cf Σ Γ Conv) Hargs),
        P cf Σ Γ Conv (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args')
          (cumul_Construct _ _ _ _ _ _ _ _ _ Hu Hargs)) ->

      (forall (Γ : context) (s s' : sort)
              (Hs : compare_sort Σ Conv s s'),
          P cf Σ Γ Conv (tSort s) (tSort s')
            (cumul_Sort _ _ _ _ _ Hs)) ->

      (forall (Γ : context) (c : kername) (u u' : list Level.t)
              (Hu : cmp_universe_instance (compare_universe Σ Conv) u u'),
          P cf Σ Γ Conv (tConst c u) (tConst c u')
            (cumul_Const _ _ _ _ _ _ Hu)) ->

       forall (Γ : context) (t t0 : term) (Ht : cumulSpec0 Σ Γ Conv t t0), P cf Σ Γ Conv t t0 Ht.
Proof.
  intros.
  remember Conv as pb eqn:Hpb in Ht |- *.
  induction Ht; eauto; subst.
  all: exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end; eauto).
  6:{ destruct X25; constructor; auto. eapply All2_dep_impl; tea; intuition auto. }
  all: cbv [cumul_predicate_dep] in *.
  all: repeat destruct ?; subst.
  all: destruct_head'_prod.
  all: repeat split; eauto.
  all: eapply All2_dep_impl; tea; cbv beta; intuition auto.
Defined.
