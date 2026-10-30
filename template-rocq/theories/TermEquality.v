(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CMorphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Reflect Environment EnvironmentTyping.
From MetaRocq.Template Require Import Ast AstUtils Induction.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Definition cmp_universe_instance (cmp_univ : Universe.t -> Universe.t -> Prop) : Instance.t -> Instance.t -> Prop :=
  Forall2 cmp_univ.

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly
  match the instances, so as to keep syntactic equality an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition cmp_universe_variance (cmp_univ : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => cmp_univ pb u u'
  | Variance.Invariant => cmp_univ Conv u u'
  end.

Definition cmp_universe_instance_variance cmp_univ pb v u u' :=
  Forall3 (cmp_universe_variance cmp_univ pb) v u u'.

Definition global_variance_gen lookup gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then
          match mdecl.(ind_variance) with
          | Some var => Variance var
          | None => AllEqual
          end
        else AllEqual
      | None => AllEqual
      end
    | None => AllEqual
    end
  | ConstructRef ind k =>
    match lookup_constructor_gen lookup ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then
        (** Fully applied constructors are always compared at the same supertype,
          which implies that no universe ws_cumul_pb needs to be checked here.
          We will still check that the instances have the same length. *)
        AllIrrelevant
      else AllEqual
    | _ => AllEqual
    end
  | _ => AllEqual
  end.

Notation global_variance Σ := (global_variance_gen (lookup_env Σ)).

Definition cmp_opt_variance cmp_univ pb v :=
  match v with
  | AllEqual => cmp_universe_instance (cmp_univ Conv)
  | AllIrrelevant => fun l l' => #|l| = #|l'|
  | Variance v => fun u u' => cmp_universe_instance (cmp_univ Conv) u u' \/ cmp_universe_instance_variance cmp_univ pb v u u'
  end.

Lemma cmp_instance_opt_variance cmp_univ pb v :
  RelationClasses.subrelation (cmp_opt_variance cmp_univ pb AllEqual) (cmp_opt_variance cmp_univ pb v).
Proof.
  intros u u' H.
  destruct v as [| |v] => //=.
  1: now apply Forall2_length in H.
  now left.
Qed.

Lemma cmp_universe_universe_variance (cmp_univ : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  cmp_univ Conv u u' -> cmp_universe_variance cmp_univ pb v u u'.
Proof.
  destruct v => //=.
  intros H H1; apply H, H1.
Qed.

Lemma cmp_instance_variance cmp_univ pb v u u' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  #|v| = #|u| ->
  cmp_universe_instance (cmp_univ Conv) u u' -> cmp_universe_instance_variance cmp_univ pb v u u'.
Proof.
  intros Hsub Hlen Hu.
  apply Forall2_triv in Hlen.
  eapply Forall2_Forall2_Forall3 in Hu; tea.
  apply Forall3_impl with (1 := Hu) => v1 u1 u1' [] _ H1.
  now apply cmp_universe_universe_variance.
Qed.

Lemma cmp_opt_variance_var_dec cmp_univ pb v ui ui' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  cmp_universe_instance (cmp_univ Conv) ui ui' \/ cmp_universe_instance_variance cmp_univ pb v ui ui' ->
  { cmp_universe_instance (cmp_univ Conv) ui ui' } + { cmp_universe_instance_variance cmp_univ pb v ui ui' }.
Proof.
  intros subr H.
  elim:(eq_dec #|v| #|ui|).
  - right.
    destruct H as [|]; tas.
    now eapply cmp_instance_variance.
  - left.
    destruct H as [|]; tas.
    eapply @Forall3_Forall2_left with (Q := fun _ _ => True) in H => //.
    apply Forall2_length in H.
    now exfalso.
Qed.

Definition cmp_global_instance_gen Σ cmp_universe pb gr napp :=
  cmp_opt_variance cmp_universe pb (global_variance_gen Σ gr napp).

Notation cmp_global_instance Σ := (cmp_global_instance_gen (lookup_env Σ)).

Lemma cmp_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (cmp_universe_instance R) (cmp_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl; tea; unfold on_rel; auto.
Qed.

Lemma cmp_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', cmp_universe_instance R u u' -> cmp_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl; tea; unfold on_rel; auto.
Qed.

Lemma cmp_universe_instance_variance_impl R R' pb pb' v :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  RelationClasses.subrelation (cmp_universe_instance_variance R pb v) (cmp_universe_instance_variance R' pb' v).
Proof.
  intros HConv Hpb x y xy.
  eapply Forall3_impl; tea. clear v x y xy.
  intros v u u'.
  destruct v => //=.
  all: unfold on_rel; now auto.
Qed.


Inductive eq_decl_upto_names : context_decl -> context_decl -> Type :=
  | compare_vass {na na' T} :
    eq_binder_annot na na' -> eq_decl_upto_names (vass na T) (vass na' T)
  | compare_vdef {na na' b T} :
    eq_binder_annot na na' -> eq_decl_upto_names (vdef na b T) (vdef na' b T).

Derive Signature NoConfusion for eq_decl_upto_names.
Notation eq_context_upto_names := (All2 eq_decl_upto_names).

Lemma alpha_eq_context_assumptions {Γ Δ} :
  eq_context_upto_names Γ Δ ->
  context_assumptions Γ = context_assumptions Δ.
Proof.
  induction 1 in |- *; cbn; auto.
  destruct r; subst; cbn; auto.
Qed.

Lemma alpha_eq_extended_subst {Γ Δ k} :
  eq_context_upto_names Γ Δ ->
  extended_subst Γ k = extended_subst Δ k.
Proof.
  induction 1 in k |- *; cbn; auto.
  destruct r; subst; cbn; f_equal; auto.
  rewrite IHX. now rewrite (alpha_eq_context_assumptions X).
Qed.

Lemma expand_lets_eq {Γ Δ t} :
  eq_context_upto_names Γ Δ ->
  expand_lets Γ t = expand_lets Δ t.
Proof.
  intros. rewrite /expand_lets /expand_lets_k.
  now rewrite (All2_length X) (alpha_eq_context_assumptions X) (alpha_eq_extended_subst X).
Qed.

Lemma alpha_eq_subst_context {Γ Δ s k} :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (subst_context s k Γ) (subst_context s k Δ).
Proof.
  intros.
  rewrite /subst_context.
  induction X.
  - cbn; auto.
  - rewrite !fold_context_k_snoc0. constructor; auto.
    rewrite -(All2_length X).
    destruct r; subst; constructor; cbn; auto.
Qed.

(** ** Syntactic equality up-to universes
  We don't look at printing annotations *)

(** Equality is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)

Inductive eq_term_upto_univ_napp Σ
  (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop)
  (cmp_sort : conv_pb -> sort -> sort -> Prop)
  (pb : conv_pb) (napp : nat) : term -> term -> Type :=
| eq_Rel n  :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tRel n) (tRel n)

| eq_Evar e args args' :
    All2 (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0) args args' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tVar id) (tVar id)

| eq_Sort s s' :
    cmp_sort pb s s' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tSort s) (tSort s')

| eq_App t t' u u' :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb (#|u| + napp) t t' ->
    All2 (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0) u u' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tApp t u) (tApp t' u')

| eq_Const c u u' :
    cmp_universe_instance (cmp_universe Conv) u u' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tConst c u) (tConst c u')

| eq_Ind i u u' :
    cmp_global_instance Σ cmp_universe pb (IndRef i) napp u u' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    cmp_global_instance Σ cmp_universe pb (ConstructRef i k) napp u u' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 ty ty' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 t t' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 a a' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb 0 b b' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 t t' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 ty ty' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 u u' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case ind p p' c c' brs brs' :
    All2 (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0) p.(pparams) p'.(pparams) ->
    cmp_universe_instance (cmp_universe Conv) p.(puinst) p'.(puinst) ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 p.(preturn) p'.(preturn) ->
    All2 eq_binder_annot p.(pcontext) p'.(pcontext) ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 c c' ->
    All2 (fun x y =>
      All2 (eq_binder_annot) (bcontext x) (bcontext y) *
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 (bbody x) (bbody y)
    ) brs brs' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tCase ind p c brs) (tCase ind p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 c c' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tCoFix mfix idx) (tCoFix mfix' idx)

| eq_Cast t1 c t2 t1' c' t2' :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 t1 t1' ->
  eq_cast_kind c c' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 t2 t2' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tCast t1 c t2) (tCast t1' c' t2')

| eq_Int i : eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tInt i) (tInt i)
| eq_Float f : eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tFloat f) (tFloat f)
| eq_String s : eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tString s) (tString s)
| eq_Array u u' arr arr' def def' ty ty' :
  cmp_universe_instance (cmp_universe Conv) [u] [u'] ->
  All2 (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0) arr arr' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 def def' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv 0 ty ty' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tArray u arr def ty) (tArray u' arr' def' ty').

Notation eq_term_upto_univ Σ cmp_universe cmp_sort pb := (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb 0).

(* ** Syntactic conversion/cumulativity up-to universes *)

Definition compare_term `{checker_flags} Σ φ (pb : conv_pb) :=
  eq_term_upto_univ Σ (compare_universe φ) (compare_sort φ) pb.

Notation eq_term Σ φ := (compare_term Σ φ Conv).
Notation leq_term Σ φ := (compare_term Σ φ Cumul).

Lemma cmp_universe_instance_refl cmp_universe :
  RelationClasses.Reflexive cmp_universe ->
  forall u, cmp_universe_instance cmp_universe u u.
Proof.
  intros refl_univ u.
  apply Forall2_same; reflexivity.
Qed.

Lemma cmp_global_instance_refl Σ cmp_universe pb gr napp :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  forall u, cmp_global_instance Σ cmp_universe pb gr napp u u.
Proof.
  intros rRE rRle.
  unfold cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //= u.
  - now apply cmp_universe_instance_refl.
  - left. now apply cmp_universe_instance_refl.
Qed.

#[global] Instance eq_binder_annot_equiv {A} : RelationClasses.Equivalence (@eq_binder_annot A A).
Proof.
  split.
  - red. reflexivity.
  - red; now symmetry.
  - intros x y z; unfold eq_binder_annot.
    congruence.
Qed.

Definition eq_binder_annot_refl {A} x : @eq_binder_annot A A x x.
Proof. reflexivity. Qed.
#[global] Hint Resolve eq_binder_annot_refl : core.

#[global] Instance eq_binder_annots_refl {A} : CRelationClasses.Equivalence (All2 (@eq_binder_annot A A)).
Proof.
  split.
  intros x. apply All2_reflexivity; tc.
  * intros l. reflexivity.
  * intros l l' H. eapply All2_symmetry => //.
  * intros l l' H. eapply All2_transitivity => //.
    intros ? ? ? ? ?. now etransitivity.
Qed.

Lemma eq_term_upto_univ_refl Σ cmp_universe cmp_sort pb :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  forall napp t, eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t.
Proof.
  intros refl_univ refl_univ' refl_sort refl_sort' napp t.
  induction t in napp, pb, refl_univ', refl_sort' |- * using term_forall_list_rect; simpl;
    try constructor; try apply Forall_Forall2; try apply All_All2 ; try easy;
      try now (try apply Forall_All ; apply Forall_True).
  - eapply All_All2. 1: eassumption.
    intros. simpl in X0. easy.
  - destruct c; constructor.
  - eapply All_All2. 1: eassumption.
    intros. easy.
  - now apply cmp_global_instance_refl.
  - now apply cmp_global_instance_refl.
  - destruct X as [Ppars Preturn]. eapply All_All2. 1:eassumption.
    intros; easy.
  - destruct X as [Ppars Preturn]. now apply Preturn.
  - red in X0. eapply All_All2_refl. solve_all. reflexivity.
  - eapply All_All2. 1: eassumption.
    intros x [? ?]. repeat split ; auto.
  - eapply All_All2. 1: eassumption.
    intros x [? ?]. repeat split ; auto.
  - eapply All_All2; tea. cbn. eauto.
Qed.

Lemma eq_term_refl `{checker_flags} Σ φ t : eq_term Σ φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - apply eq_universe_refl.
  - apply eq_universe_refl.
  - apply eq_sort_refl.
  - apply eq_sort_refl.
Qed.


Lemma leq_term_refl `{checker_flags} Σ φ t : leq_term Σ φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - apply eq_universe_refl.
  - apply leq_universe_refl.
  - intro; apply eq_sort_refl.
  - intro; apply leq_sort_refl.
Qed.
(*
Lemma eq_term_leq_term `{checker_flags} Σ φ napp t u :
  eq_term_upto_univ_napp Σ napp φ t u -> leq_term Σ φ t u.
Proof.
  induction t in u |- * using term_forall_list_rect; simpl; inversion 1;
    subst; constructor; try (now unfold eq_term, leq_term in * );
  try eapply Forall2_impl' ; try eapply All2_impl' ; try easy.
  now apply eq_sort_leq_sort.
  all: try (apply Forall_True, eq_sort_leq_sort).
  apply IHt.
Qed. *)

#[global] Instance cmp_global_instance_impl_same_napp Σ cmp_universe cmp_universe' pb pb' gr napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  subrelation (cmp_global_instance Σ cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp).
Proof.
  intros sub_conv sub_pb u u'.
  unfold cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen as [| |v] => //.
  1: now apply cmp_universe_instance_impl.

  intros [H | H]; [left | right].
  1: eapply cmp_universe_instance_impl; tea.

  eapply Forall3_impl; tea. clear v u u' H.
  intros v u u'.
  destruct v => //=.
  all: unfold on_rel; now auto.
Qed.

Lemma global_variance_napp_mon Σ gr {napp napp'} :
  napp <= napp' ->
  match global_variance Σ gr napp with
  | Variance v => global_variance Σ gr napp' = Variance v
  | AllEqual => True
  | AllIrrelevant => global_variance Σ gr napp' = AllIrrelevant
  end.
Proof.
  intros hnapp.
  rewrite /global_variance_gen.
  destruct gr => //=.
  - destruct lookup_inductive_gen as [[mdecl idec]|] => //=.
    destruct destArity as [[ctx s]|] => //=.
    elim: Nat.leb_spec => // cass.
    destruct ind_variance => //=.
    elim: Nat.leb_spec => //. lia.
  - destruct lookup_constructor_gen as [[[mdecl idecl] cdecl]|] => //=.
    elim: Nat.leb_spec => // cass.
    elim: Nat.leb_spec => //. lia.
Qed.

#[global]
Instance cmp_global_instance_impl Σ cmp_universe cmp_universe' pb pb' gr napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  napp <= napp' ->
  subrelation (cmp_global_instance Σ cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp').
Proof.
  intros sub_conv sub_pb lenapp u u'.
  unfold cmp_global_instance_gen.
  move: (global_variance_napp_mon Σ gr lenapp).
  destruct global_variance_gen as [| |v] => //.
  all: [> intros _ | intros ->; cbn ..]; auto.
  1: intro H; apply: cmp_instance_opt_variance; move: H => /=.
  - now apply cmp_universe_instance_impl.
  - intros [H | H]; [left | right].
    1: eapply cmp_universe_instance_impl; tea.
    eapply cmp_universe_instance_variance_impl; eassumption.
Qed.

#[global] Instance eq_term_upto_univ_impl Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp) (eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' pb' napp').
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb hnapp t t'.
  induction t in napp, napp', hnapp, pb, pb', univ_sub_pb, sort_sub_pb, t' |- * using term_forall_list_rect;
    try (inversion 1; subst; constructor;
         eauto using cmp_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply IHt. 4:eauto. all:auto with arith. eauto.
    solve_all.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:auto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:eauto.
  - destruct X as [IHpars IHret].
    inversion 1; subst; constructor; eauto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    eapply cmp_universe_instance_impl; eauto.
    eapply All2_impl'; eauto.
    cbn.
    eapply All_impl; eauto.
    intros x ? y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor; eauto.
    1: eapply cmp_universe_instance_impl; eauto.
    eapply All2_impl'; tea. eapply All_impl; eauto.
Qed.

Lemma eq_term_upto_univ_morphism0 Σ cmp_universe cmp_universe' cmp_sort cmp_sort' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  forall t u napp, eq_term_upto_univ_napp Σ cmp_universe cmp_sort Conv napp t u -> eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' Conv napp t u.
Proof.
  intros univ_sub sort_sub t u napp.
  apply eq_term_upto_univ_impl.
  5: auto with arith. all: auto.
Qed.

Lemma eq_term_upto_univ_morphism Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  forall t u napp, eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t u -> eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' pb' napp t u.
Proof.
  intros univ_sub univ_sub_pb sort_sub sort_sub_pb t u napp.
  apply eq_term_upto_univ_impl.
  5: auto with arith. all: auto.
Qed.

Lemma eq_term_leq_term `{checker_flags} Σ φ t u :
  eq_term Σ φ t u -> leq_term Σ φ t u.
Proof.
  eapply eq_term_upto_univ_morphism.
  - reflexivity.
  - apply eq_leq_universe.
  - reflexivity.
  - apply eq_leq_sort.
Qed.

Lemma eq_term_upto_univ_App `{checker_flags} Σ cmp_universe cmp_sort pb napp f f' :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_App `{checker_flags} Σ φ f f' :
  eq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps `{checker_flags} Σ cmp_universe cmp_sort pb napp f l f' l' :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb (#|l| + napp) f f' ->
  All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) l l' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - pose proof (eq_term_upto_univ_App _ _ _ _ _ _ _ e).
    case_eq (isApp f).
    + intro X; rewrite X in H0.
      destruct f; try discriminate.
      destruct f'; try discriminate.
      cbn. inversion_clear e. constructor.
      rewrite length_app /= -Nat.add_assoc //.
      apply All2_app. assumption.
      now constructor.
    + intro X; rewrite X in H0.
      eapply negbT in X. symmetry in H0; eapply negbT in H0.
      rewrite - !mkApps_tApp //.
      constructor. simpl. now simpl in e.
      now constructor.
Qed.

Lemma leq_term_mkApps `{checker_flags} Σ φ f l f' l' :
  leq_term Σ φ f f' ->
  All2 (eq_term Σ φ) l l' ->
  leq_term Σ φ (mkApps f l) (mkApps f' l').
Proof.
  intros.
  eapply eq_term_upto_univ_mkApps. 2: assumption.
  eapply eq_term_upto_univ_impl. 6:eauto. 5:auto with arith.
  all:typeclasses eauto.
Qed.

Lemma leq_term_App `{checker_flags} Σ φ f f' :
  leq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.
