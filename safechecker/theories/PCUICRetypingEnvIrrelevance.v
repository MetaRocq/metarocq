
(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool Utf8.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

From Stdlib Require Import Bool String List Program.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICTyping PCUICValidity PCUICSN
    PCUICWellScopedCumulativity PCUICSafeLemmata PCUICInversion.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICSafeReduce PCUICWfEnv PCUICSafeRetyping.

(** We might need to weaken calls to the retyping function w.r.t. the global environment: i.e.
    if we infer some type for a term in an environment Σ, then any other environment having at least
    the same declarations as Σ should give us the same result. For example erasure can be called on
    all the declarations in a well-formed global environment without having to take successive prefixes of it.

    This does not follow from correctness of retyping alone. We rather prove that the result of retyping (and hence also reduction) are invariant
    in this sense. As retyping relies on reduction of types also show that safe reduction is invariant under extension.
    This cannot be shown using only the correctness and completeness lemmas of reduction either as
    in different enviroments we might find different declarations and hence produce different
    reduced terms. Morally we could hope that a parametericity style lemma could prove this:
    for two environments that are obsevationally equal on the declared constants/inductives
    appearing in a well-typed terms, the output of reduction/inference is equal.
    However parametricity would not directly allow us to restrict to observational
    equivalence only on declared constants, so we have to perform this relational proof meticulously.
    As the functions involved use dependent types everywhere, we restrict our observations to the
    computational results returned by each function and do not compare proofs (in potentially different types/fibers). *)

Implicit Types (cf : checker_flags).

Definition Hlookup {cf} (X_type : abstract_env_impl) (X : X_type.π2.π1) (X_type' : abstract_env_impl)
  (X' : X_type'.π2.π1) :=
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
  forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' ->
  (forall kn decl decl',
    lookup_env Σ kn = Some decl ->
    lookup_env Σ' kn = Some decl' ->
    abstract_env_lookup X kn = abstract_env_lookup X' kn) /\
    (forall tag,
    abstract_primitive_constant X tag = abstract_primitive_constant X' tag).

Definition reduce_stack_eq {cf} {fl} {nor:normalizing_flags} {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ t π wi : reduce_stack fl X_type X Γ t π wi = ` (reduce_stack_full fl X_type X Γ t π wi).
Proof.
  unfold reduce_stack. destruct reduce_stack_full => //.
Qed.

Definition same_principal_type {cf}
  {X_type : abstract_env_impl} {X : X_type.π2.π1}
  {X_type' : abstract_env_impl} {X' : X_type'.π2.π1}
  {Γ : context} {t} (p : PCUICSafeRetyping.principal_type X_type X Γ t) (p' : PCUICSafeRetyping.principal_type X_type' X' Γ t) :=
  p.π1 = p'.π1.


Lemma welltyped_mkApps_inv {cf} {Σ : global_env_ext} Γ f args :  ∥ wf Σ ∥ ->
  welltyped Σ Γ (mkApps f args) -> welltyped Σ Γ f /\ Forall (welltyped Σ Γ) args.
Proof.
  intros wf (A & HA). sq. eapply inversion_mkApps in HA as (? & ? & ?).
  split. eexists; eauto.
  induction t0 in f |- *; econstructor; eauto; econstructor; eauto.
Qed.

Section infer_irrel.
  Context {cf} {nor : normalizing_flags} {X_type : abstract_env_impl} {X : X_type.π2.π1}
    {X_type' : abstract_env_impl} {X' : X_type'.π2.π1}.
  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}
    {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}.
  Context (hl : Hlookup X_type X X_type' X').

  Definition same_prod (Γ : context) {T}
     (pf : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥)
    (pf' : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥) :=
    let '(na; A; B; _) := pf in
    let '(na'; A'; B'; _) := pf' in
    (na, A, B) = (na', A', B').

  Lemma same_prod_last (Γ : context) {T}
    (pf : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥)
    (pf' : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥)
    : same_prod Γ pf pf' -> pf.π2.π2.π1 = pf'.π2.π2.π1.
  Proof using Type.
    destruct pf as [na [A [B prf]]].
    destruct pf' as [na' [A' []]].
    cbn. congruence.
  Qed.

  Lemma same_reduce_stack {Γ t π} {fl} (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ (PCUICPosition.zip (t, π)))
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ (PCUICPosition.zip (t, π))) :
    reduce_stack fl X_type X Γ t π wi = reduce_stack fl X_type' X' Γ t π wi'.
  Proof using hl.
    rewrite !reduce_stack_eq.
    revert X_type' X' wi' hl normalization_in'.
    apply_funelim (reduce_stack_full fl X_type X Γ t π wi).
    intros.
    rewrite reduce_stack_full_unfold_eq.
    set (rec := (fun t' π' => _)).
    simp _reduce_stack.
    unfold reduce_stack_full_unfold. simp _reduce_stack.
    set (rec' := (fun t' π' => _)).
    assert (ih : forall (t' : term) (π' : PCUICPosition.stack)
      (hr : forall Σ : global_env_ext,
            abstract_env_ext_rel X Σ -> R Σ Γ (t', π') (t0, π0))
      (hr' : forall Σ : global_env_ext,
      abstract_env_ext_rel X' Σ -> R Σ Γ (t', π') (t0, π0)),
      ` (rec t' π' hr) = ` (rec' t' π' hr')).
    { intros. unshelve eapply H. exact hl. } clear H.
    clearbody rec rec'.
    Ltac reccall ih rec rec' :=
      match goal with
      [ |- context [rec ?t ?π ?hr] ] =>
        match goal with
        [ |- context [rec' ?t' ?π' ?hr'] ] =>
          let H := fresh in
          assert (H := ih t π hr hr');
          set (call := rec t π hr) in *;
          set (call' := rec' t π' hr') in *;
          clearbody call call';
          destruct call, call'; cbn in H |- *; subst; auto
          end
      end.
    destruct red_viewc.
    - cbn. simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.zeta fl); simp _reduce_stack. 2:reflexivity.
      destruct PCUICSafeReduce.inspect => //.
      destruct x as [[? [?|] ?]|] => //.
      simp _reduce_stack. simpl.
      reccall ih rec rec'.
      cbn. bang.
    - simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.zeta fl); simp _reduce_stack. 2:reflexivity.
      simpl.
      reccall ih rec rec'.
    - cbn.
      destruct (PCUICNormal.RedFlags.delta fl); simp _reduce_stack. 2:reflexivity.
      assert (abstract_env_lookup X c = abstract_env_lookup X' c).
      { clear -hl h wi'.
        epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
        epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
        specialize (h _ wfΣ).
        epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
        epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
        specialize (wi' _ wfΣ').
        eapply welltyped_zipc_zipp in h. 2:pcuic. cbn in h.
        unfold PCUICPosition.zipp in *.
        destruct (PCUICPosition.decompose_stack π0) eqn:decomp; eauto.
        assert (∥ wf Σ ∥). sq. apply hwfΣ.
        eapply (welltyped_mkApps_inv (Σ := Σ) _ _ _ H) in h as [].
        eapply welltyped_zipc_zipp in wi'. 2:pcuic. cbn in wi'.
        unfold PCUICPosition.zipp in *.
        destruct (PCUICPosition.decompose_stack π0) eqn:decomp'; eauto.
        assert (∥ wf Σ' ∥). sq. apply hwfΣ'.
        eapply (welltyped_mkApps_inv (Σ := Σ') _ _ _ H2) in wi' as [].
        destruct H0, H3.
        eapply inversion_Const in X0 as [decl [_ [Hdecl _]]]; eauto.
        eapply inversion_Const in X1 as [decl' [_ [Hdecl' _]]]; eauto.
        sq. eapply hl; eauto;
        unshelve eapply declared_constant_to_gen in Hdecl, Hdecl'; eauto.
        }
      destruct PCUICSafeReduce.inspect => //.
      destruct PCUICSafeReduce.inspect => //.
      destruct x as [[]|] => //; simp _reduce_stack. 2-3:bang.
      destruct x0 as [[]|] => //; simp _reduce_stack. 2-3:bang.
      assert (c0 = c1).
      { congruence. } subst c1.
      destruct c0 as [? [|] ? ?]; simp _reduce_stack.
      simpl. reccall ih rec rec'. now cbn.
    - simp _reduce_stack.
      simpl.
      reccall ih rec rec'.
    - simp _reduce_stack.
      destruct PCUICSafeReduce.inspect => //. destruct x.
      simp _reduce_stack. simpl.
      reccall ih rec rec'. now cbn.
    - simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.fix_ fl); simp _reduce_stack. 2:reflexivity.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x; simp _reduce_stack. 2:reflexivity.
      destruct p. simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x; simp _reduce_stack. 2:reflexivity.
      destruct p as [[? ?] ?]. simp _reduce_stack.
      Ltac reccall' ih rec rec' :=
        match goal with
        [ |- context [rec ?t ?π ?hr] ] =>
          match goal with
          [ |- context [rec' ?t' ?π' ?hr'] ] =>
            let H := fresh in
            assert (H := ih t π hr hr');
            set (call := rec t π hr) in *;
            set (call' := rec' t π' hr') in *
            end
        end.
      reccall' ih rec rec'.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      subst x. subst x0.
      match goal with
        [ |- context [@exist ?A ?P call ?e] ] =>
          match goal with
          [ |- context [@exist ?A' ?P' call' ?e'] ] =>
            set (ex := @exist A P call e);
            set (ex' := @exist A' P' call' e');
            clearbody ex ex'
          end
      end.
      destruct ex as [[? ?] eq].
      destruct ex' as [[? ?] eq'].
      assert (x = x0). { subst call call'. move: eq eq'.
        reccall ih rec rec'. congruence. }
      subst x0. destruct x.
      simp _reduce_stack.
      destruct (construct_viewc); simp _reduce_stack.
      * destruct PCUICSafeReduce.inspect; simp _reduce_stack.
        destruct x as []; simp _reduce_stack.
        simpl. subst call call'.
        reccall ih rec rec'.
      * destruct PCUICSafeReduce.inspect; simp _reduce_stack.
        destruct x as []; simp _reduce_stack. reflexivity.
    - simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.iota fl); simp _reduce_stack. 2:reflexivity.
      reccall' ih rec rec'.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      subst x. subst x0.
      match goal with
        [ |- context [@exist ?A ?P call ?e] ] =>
          match goal with
          [ |- context [@exist ?A' ?P' call' ?e'] ] =>
            set (ex := @exist A P call e);
            set (ex' := @exist A' P' call' e');
            clearbody ex ex'
          end
      end.
      destruct ex as [[? ?] eq].
      destruct ex' as [[? ?] eq'].
      assert (x = x0). { subst call call'. move: eq eq'.
        reccall ih rec rec'. congruence. }
      subst x0. destruct x.
      simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack.
      destruct cc_viewc; simp _reduce_stack. 3:reflexivity.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack.
      simpl. subst call call'.
      reccall ih rec rec'. bang.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack. 2:bang.
      destruct p0; simp _reduce_stack. simpl.
      subst call call'; reccall ih rec rec'.
    - destruct p as [[] ?]. simp _reduce_stack. simpl.
      destruct (PCUICNormal.RedFlags.iota fl); simp _reduce_stack. 2:reflexivity.
      reccall' ih rec rec'.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      subst x. subst x0.
      match goal with
        [ |- context [@exist ?A ?P call ?e] ] =>
          match goal with
          [ |- context [@exist ?A' ?P' call' ?e'] ] =>
            set (ex := @exist A P call e);
            set (ex' := @exist A' P' call' e');
            clearbody ex ex'
          end
      end.
      destruct ex as [[? ?] eq].
      destruct ex' as [[? ?] eq'].
      assert (x = x0). { subst call call'. move: eq eq'.
        reccall ih rec rec'. congruence. }
      subst x0. destruct x.
      simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack.
      destruct cc0_viewc; simp _reduce_stack. 3:reflexivity.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack.
      simpl. subst call call'.
      reccall ih rec rec'. bang.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack. 2:bang.
      destruct p; simp _reduce_stack. simpl.
      subst call call'; reccall ih rec rec'.
    - simpl. reflexivity.
  Qed.

  Lemma same_hnf {Γ t} (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) :
    hnf Γ t wi = hnf Γ t wi'.
  Proof using hl.
    unfold hnf. unfold reduce_term.
    f_equal. apply same_reduce_stack.
  Qed.

  Definition same_typing_result_comp {A B} (P : A -> B -> Prop) (c : typing_result_comp A) (c' : typing_result_comp B) : Prop :=
    match c, c' with
    | Checked_comp a, Checked_comp a' => P a a'
    | TypeError_comp e ne, TypeError_comp e' na' => True
    | _, _ => False
    end.

  Definition same_prod_comp {Γ T}
     (pf : typing_result_comp (∑ (na' : aname) (A' B' : term),
       forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥))
    (pf' : typing_result_comp (∑ (na' : aname) (A' B' : term),
       forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥)) :=
    same_typing_result_comp (same_prod Γ) pf pf'.

  Lemma reduce_to_prod_irrel {Γ t}
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) :
    same_prod_comp (reduce_to_prod Γ t wi) (reduce_to_prod Γ t wi').
  Proof using hl.
    unfold reduce_to_prod.
    destruct view_prodc; simp reduce_to_prod.
    red. cbn. auto.
    epose proof (same_hnf wi wi').
    unfold reduce_to_prod_clause_1_clause_2. cbn.
    set (e := eq_refl). set (e' := eq_refl).
    set (v := view_prodc (hnf Γ t wi)). clearbody v.
    set (v' := view_prodc (hnf Γ t wi')). clearbody v'.
    clearbody e e'.
    unfold reduce_to_prod_clause_1_clause_2_clause_1.
    destruct v. destruct v'. cbn. now noconf H. cbn.
    noconf H. now cbn in n0.
    destruct v'. cbn. subst t0. now cbn in n0.
    subst t1. cbn. auto.
  Qed.

  Lemma infer_as_prod_irrel {Γ t}
    (wf : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ wf_local Σ Γ ∥)
    (wf' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ wf_local Σ Γ ∥)
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t)
    hp hp' : same_prod Γ (infer_as_prod X_type X Γ t wf wi hp) (infer_as_prod X_type' X' Γ t wf' wi' hp').
  Proof using hl.
    unfold same_prod.
    unfold infer_as_prod.
    destruct reduce_to_prod as [[na [A [B hr]]]|] eqn:h. 2:bang.
    destruct (reduce_to_prod _ _ wi') as [[na' [A' [B' hr']]]|] eqn:h'. 2:bang.
    pose proof (reduce_to_prod_irrel wi wi').
    rewrite h h' in H. now cbn in H.
  Qed.

  Definition same_sort_comp {cf} {nor : normalizing_flags}
    {X_type : abstract_env_impl} {X : X_type.π2.π1}
    {X_type' : abstract_env_impl} {X' : X_type'.π2.π1}
    {Γ : context} {t t'}
    (pf : typing_result_comp
      (∑ u, forall Σ0 : global_env_ext, abstract_env_ext_rel X Σ0 -> ∥ Σ0 ;;; Γ ⊢ t ⇝ tSort u ∥))
    (pf' : typing_result_comp
      (∑ u, forall Σ0 : global_env_ext, abstract_env_ext_rel X' Σ0 -> ∥ Σ0 ;;; Γ ⊢ t' ⇝ tSort u ∥)) :=
    same_typing_result_comp (fun x y => x.π1 = y.π1) pf pf'.

  Lemma reduce_to_sort_irrel {Γ t t'} (e : t = t')
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t') :
    same_sort_comp (reduce_to_sort Γ t wi) (reduce_to_sort Γ t' wi').
  Proof using hl.
    destruct e.
    unfold reduce_to_sort.
    destruct (view_sortc); simp reduce_to_sort.
    now cbn.
    unfold reduce_to_sort_clause_1_clause_2; cbn.
    epose proof (same_hnf wi wi').
    do 2 match goal with
    |- context [@eq_refl ?A ?t] => let e := fresh "e" in set(e := @eq_refl A t)
    end.
    set (v := view_sortc (hnf Γ t wi)). clearbody v.
    set (v' := view_sortc (hnf Γ t wi')). clearbody v'.
    clearbody e e0.
    unfold reduce_to_sort_clause_1_clause_2_clause_1.
    destruct v. destruct v'. cbn. now noconf H. cbn.
    noconf H. now cbn in n0.
    destruct v'. cbn. subst t0. now cbn in n0.
    subst t1. cbn. auto.
  Qed.

  Lemma infer_as_sort_irrel {Γ t}
    (wf : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ wf_local Σ Γ ∥)
    (wf' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ wf_local Σ Γ ∥)
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> well_sorted Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> well_sorted Σ Γ t)
    hp hp' : hp.π1 = hp'.π1 -> (infer_as_sort X_type X wf wi hp).π1 = (infer_as_sort X_type' X' wf' wi' hp').π1.
  Proof using hl.
    unfold infer_as_sort.
    unfold PCUICSafeRetyping.principal_type_type.
    set (obl := fun Σ wfΣ => PCUICSafeRetyping.infer_as_sort_obligation_1 _ _ _ _ _ _ _ Σ wfΣ).
    set (obl' := fun Σ wfΣ => PCUICSafeRetyping.infer_as_sort_obligation_1 _ _ _ _ _ _ _ Σ wfΣ).
    clearbody obl obl'.
    destruct reduce_to_sort as [[s hr]|] eqn:h. 2:bang.
    destruct (reduce_to_sort _ hp'.π1 _) as [[s' hr']|] eqn:h'. 2:bang.
    cbn. destruct hp, hp'; cbn; intros <-.
    cbn -[reduce_to_sort] in *.
    epose proof (reduce_to_sort_irrel eq_refl obl obl').
    rewrite h h' in H. now cbn in H.
  Qed.

  Definition same_ind_comp {Γ t t'}
    (pf : typing_result_comp
    (∑ (i : inductive) (u : Instance.t) (l : list term),
         forall Σ : global_env_ext,
         abstract_env_ext_rel X Σ ->
         ∥ Σ ;;; Γ ⊢ t ⇝  mkApps (tInd i u) l ∥))
    (pf' : typing_result_comp
    (∑ (i : inductive) (u : Instance.t) (l : list term),
    forall Σ : global_env_ext,
    abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ t' ⇝ mkApps (tInd i u) l ∥)) :=
 same_typing_result_comp (fun x y => (x.π1, x.π2.π1, x.π2.π2.π1) = (y.π1, y.π2.π1, y.π2.π2.π1)) pf pf'.


  Lemma elim_inspect {A} (x : A) (P : { y : A | y = x } -> Type) :
    (forall y (e : y = x), P (exist y e)) -> P (PCUICSafeReduce.inspect x).
  Proof using Type.
    intros hp. unfold PCUICSafeReduce.inspect. apply hp.
  Qed.

 Lemma reduce_to_ind_irrel {Γ t t'} (e : t = t')
  (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
  (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t') :
  same_ind_comp (reduce_to_ind Γ t wi) (reduce_to_ind Γ t' wi').
  Proof using hl.
    subst t'.
    simp reduce_to_ind.
    eapply elim_inspect => [[f args] eq].
    simp reduce_to_ind.
    destruct view_indc => //.
    simp reduce_to_ind.
    epose proof (same_reduce_stack (fl := PCUICNormal.RedFlags.default) (π := []) wi wi').
    eapply elim_inspect => [[f' π'] eq']. simp reduce_to_ind.
    eapply elim_inspect => [[f'' π''] eq'']. simp reduce_to_ind.
    rewrite -eq' -eq'' in H. noconf H.
    destruct view_indc => //. simp reduce_to_ind.
    eapply elim_inspect => [[app st] eqst]. simp reduce_to_ind => //.
  Qed.

  Definition same_typing_result {A B} (P : A -> B -> Prop) (c : typing_result A) (c' : typing_result B) : Prop :=
    match c, c' with
    | Checked a, Checked a' => P a a'
    | TypeError e, TypeError e' => True
    | _, _ => False
    end.

  Lemma same_lookup_ind_decl ind :
    abstract_env_lookup X (inductive_mind ind) = abstract_env_lookup X' (inductive_mind ind) ->
    same_typing_result (fun x y => (x.π1, x.π2.π1) = (y.π1, y.π2.π1)) (lookup_ind_decl X_type X ind) (lookup_ind_decl X_type' X' ind).
  Proof using Type.
    intros eq.
    funelim (lookup_ind_decl X_type X ind); simp lookup_ind_decl;
    eapply elim_inspect; intros opt e'.
    - rewrite -e -e' in eq. destruct opt; noconf eq => //.
    - rewrite -e in eq. destruct opt => //. exfalso; congruence.
    - destruct opt as [[]|]. cbn. congruence.
      rewrite -look -e' in eq. noconf eq.
      simp lookup_ind_decl.
      eapply elim_inspect; intros opt e''.
      destruct opt => //. simp lookup_ind_decl. cbn. congruence.
      cbn. congruence. cbn. congruence.
    - destruct opt as [[]|] => //. simp lookup_ind_decl.
      eapply elim_inspect; intros opt e''.
      destruct opt => //. simp lookup_ind_decl. cbn. congruence.
  Qed.

End infer_irrel.

Lemma infer_irrel {cf} {nor : normalizing_flags} {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}
  {X_type' : abstract_env_impl} {X' : X_type'.π2.π1} {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
  (hl : Hlookup X_type X X_type' X')
  {Γ t}
  (wf : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ wf_local Σ Γ ∥)
  (wf' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ wf_local Σ Γ ∥)
  (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> wellinferred Σ Γ t)
  (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> wellinferred Σ Γ t) :
  (infer X_type X Γ wf t wi).π1 = (infer X_type' X' Γ wf' t wi').π1.
Proof.
  revert X_type' X' hl wf' wi' normalization_in'. apply_funelim (infer X_type X Γ wf t wi).
  all:intros.
  all:try bang.
  - now cbn.
  - simpl.
    cbn. f_equal. f_equal; unfold PCUICSafeRetyping.principal_sort_sort.
    set (obl := fun a b => _).
    set (obl' := fun a b => _).
    set (obl'' := fun a b => _).
    set (obl''' := fun a b => _).
    cbn. eapply infer_as_sort_irrel => //. now eapply H.
    eapply infer_as_sort_irrel => //. now eapply H0.
  - cbn. f_equal.
    unfold PCUICSafeRetyping.principal_type_type. apply H; eauto.
  - cbn. f_equal. apply H; eauto.
  - cbn. f_equal.
    unfold PCUICSafeRetyping.principal_type_type.
    set (obl1 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_14 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl2 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_13 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (t' := (infer _ _ _ _ _ _)) in *.
    set (obl3 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_14 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl4 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_13 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (t'' := (infer X_type' _ _ _ _ _)) in *.
    clearbody obl3 obl4.
    assert (t'.π1 = t''.π1).
    { unfold t', t''. apply H; eauto. }
    clearbody t''. clearbody obl1 obl2. clearbody t'.
    destruct t', t''. cbn in H0. subst x0. cbn.
    eapply same_prod_last; eauto.
    now eapply infer_as_prod_irrel.
  - simp infer. rewrite Heq /= //.
  - assert (abstract_env_lookup X cst = abstract_env_lookup X' cst).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      specialize (wt _ wfΣ).
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      specialize (wi' _ wfΣ').
      depelim wt. inv X0.
      depelim wi'. inv X0.
      destruct hwfΣ, hwfΣ'. eapply hl; eauto;
      unshelve eapply declared_constant_to_gen in isdecl, isdecl0; eauto.
    }
    move: e Heq.
    cbn -[infer].
    rewrite H. simp infer.
    now intros e -> => /=.
  - destruct decl as [decl [body hd]].
    cbn -[infer].
    simp infer.
    assert (abstract_env_lookup X (inductive_mind ind) = abstract_env_lookup X' (inductive_mind ind)).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      destruct (wi' _ wfΣ'). inv X0.
      pose proof (hd _ wfΣ).
      destruct isdecl, H0. destruct hwfΣ, hwfΣ'.
      eapply hl; eauto;
      unshelve eapply declared_minductive_to_gen in H1, H0; eauto.
      }
    destruct (PCUICSafeReduce.inspect (lookup_ind_decl _ X' ind)).
    generalize (same_lookup_ind_decl ind H). rewrite -{1}e0 -{1}e.
    destruct x => //. cbn. cbn.
    destruct a as [decl' [body' ?]]; cbn.
    congruence.
  - cbn -[infer].
    simp infer.
    assert (abstract_env_lookup X (inductive_mind ind) = abstract_env_lookup X' (inductive_mind ind)).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      destruct (wi' _ wfΣ'). inv X0.
      pose proof (wt _ wfΣ).
      destruct isdecl, H0. inv X0.
      destruct H1. destruct isdecl as [[] ?].
      destruct hwfΣ, hwfΣ'.
      eapply hl; eauto;
      unshelve eapply declared_minductive_to_gen in H1, H4; eauto.
      }
    destruct (PCUICSafeReduce.inspect (lookup_ind_decl _ X' ind)).
    generalize (same_lookup_ind_decl _ H). rewrite -{1}e1 -{1}e.
    destruct x => //.
    destruct a as [decl' [body' ?]] => //.
    simp infer.
    eapply elim_inspect; intros o eq. cbn in eq.
    destruct o => //. simp infer. cbn. destruct decl as [decl [body ?]]; cbn.
    intros [=]. subst decl' body'. cbn in e0.
    congruence.
    cbn. bang.
  - cbn -[infer].
    simp infer.
    set (t' := (infer X_type _ _ _ _ _)) in *.
    specialize (Hind X_type' X' hl).
    set (obl4 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_25 X_type _ _ _ _ _ _ _ _ _ Σ wfΣ)) in *.
    set (obl3 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_25 X_type' _ _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl1 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_24 X_type _ _ _ _ _ _ _ Σ wfΣ)) in *; cbn in obl1.
    set (obl2 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_24 X_type' _ _ _ _ _ _ _ Σ wfΣ)) in *; cbn in obl2.
    specialize (Hind wf' obl2 ltac:(assumption)).
    set (t'' := (infer X_type' _ _ _ _ _)) in *.
    cbn in obl3. unfold PCUICSafeRetyping.principal_type_type in obl3 |- *.
    eapply elim_inspect => y eq.
    epose proof (reduce_to_ind_irrel hl Hind obl4 obl3).
    rewrite -e -eq in H.
    destruct y => //. destruct a as [ind' [u' [l' ?]]] => //. cbn.
    destruct indargs as [ind [u [l ?]]]; cbn. now cbn in H; noconf H.
  - cbn -[infer].
    simp infer.
    set (t' := (infer X_type _ _ _ _ _)) in *.
    specialize (Hind X_type' X' hl ltac:(assumption)).
    unfold PCUICSafeRetyping.principal_type_type in *.
    eapply elim_inspect => y eq.
    assert (abstract_env_lookup X (inductive_mind p.(proj_ind)) = abstract_env_lookup X' (inductive_mind p.(proj_ind))).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      destruct (wi' _ wfΣ'). inv X0.
      pose proof (wt _ wfΣ).
      inv H1. inv X0. destruct H1 as [[[]]]. destruct H as [[[]]].
      destruct hwfΣ, hwfΣ'.
      eapply hl; eauto;
      unshelve eapply declared_minductive_to_gen in H1, H; eauto.
      }
    generalize (same_lookup_ind_decl _ H). rewrite -{1}eq -{1}e.
    destruct y => //.
    destruct a as [decl [body ?]], d as [decl' [body' ?]].
    simp infer.
    intros h. cbn in h. noconf h.
    eapply elim_inspect => nth eq'.
    cbn in eq', e0. destruct nth as [[]|] => //.
    simp infer.
    set (obl4 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_29 X_type _ _ _ _ _ _ _ Σ wfΣ)) in *.
    set (obl3 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_29 X_type' _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl1 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_28 X_type _ _ _ _ _ Σ wfΣ)) in *; cbn in obl1.
    set (obl2 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_28 X_type' _ _ _ _ _ Σ wfΣ)) in *; cbn in obl2.
    specialize (Hind obl2 ltac:(assumption)).
    set (t'' := (infer X_type' _ _ _ _ _)) in *.
    cbn in obl3. unfold PCUICSafeRetyping.principal_type_type in obl3 |- *.
    eapply elim_inspect => rind eqrind.
    epose proof (reduce_to_ind_irrel hl Hind obl4 obl3).
    rewrite -e1 -eqrind in H0.
    destruct rind => //. destruct a as [ind' [u' [l' ?]]] => //. cbn.
    destruct indargs as [ind'' [u [l ?]]]; cbn. cbn in H0; noconf H0.
    clear -e0 eq'. destruct pdecl. rewrite -e0 in eq'. noconf eq'. now cbn.
    exfalso.
    clear -e0 eq'. congruence.
  - cbn -[infer]. simp infer; rewrite Heq /= //.
  - cbn -[infer]. simp infer; rewrite Heq /= //.
  - cbn -[infer]. simp infer.
    eapply elim_inspect => y eq.
    assert (forall tag, abstract_primitive_constant X tag = abstract_primitive_constant X' tag).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      apply (hl _ wfΣ _ wfΣ'). }
    clear Heq. rewrite H in eqp. rewrite -eq in eqp.
    destruct y;  simp infer; cbn; congruence.
Qed.

Lemma sort_of_type_irrel
  {cf} {nor : normalizing_flags} {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}
  {X_type' : abstract_env_impl} {X' : X_type'.π2.π1} {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
  (hl : Hlookup X_type X X_type' X')
  {Γ : context} {t}
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ isType Σ Γ t ∥)
  (wt' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ isType Σ Γ t ∥) :
  (sort_of_type X_type X Γ t wt).π1 = (sort_of_type X_type' X' Γ t wt').π1.
Proof.
  simp sort_of_type.
  set (obl := sort_of_type_obligation_1 _ _ _ _ _).
  set (obl2 := sort_of_type_obligation_1 _ _ _ _ _ ).
  set(ty := (type_of_typing _ _ _ _ obl)) in *.
  set(ty' := (type_of_typing _ _ _ _ obl2)) in *.
  set (obl' := sort_of_type_obligation_2 _ _ _ _ _ _).
  set (obl2' := sort_of_type_obligation_2 _ _ _ _ _ _).
  assert (ty.π1 = ty'.π1).
  { subst ty ty'. unfold type_of_typing.
    eapply infer_irrel => //. }
  clearbody ty. clearbody ty'.
  destruct ty, ty'. cbn in H. subst x0.
  pose proof (reduce_to_sort_irrel hl eq_refl obl' obl2').
  destruct (PCUICSafeReduce.inspect) eqn:hi.
  cbn -[sort_of_type_clause_1_clause_1].
  destruct (PCUICSafeReduce.inspect (reduce_to_sort _ x obl2')) eqn:hi';
  rewrite -e -e0 in H.
  destruct x0, x1 => //. cbn in H.
  destruct a, a0. cbn in H; noconf H.
  now cbn.
  cbn. bang.
Qed.
