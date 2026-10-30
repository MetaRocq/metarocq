(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnOne
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakeningConv PCUICWeakeningTyp PCUICReduction PCUICConversion
     PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICConversion PCUICWfUniverses.

From MetaRocq.SafeChecker Require Import PCUICWfEnv.


From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Local Set Keyed Unification.
Set Equations Transparent.

Lemma Acc_no_loop X (R : X -> X -> Prop) t : Acc R t -> R t t -> False.
Proof.
  induction 1. intros. eapply H0; eauto.
Qed.

(* Show that taking head normal forms and then the subterm relation is well-founded *)

Inductive term_direct_subterm : term -> term -> Type :=
| term_direct_subterm_4_1 : forall (na : aname) (A B : term),
  term_direct_subterm B (tProd na A B)
| term_direct_subterm_4_2 : forall (na : aname) (A B : term),
  term_direct_subterm A (tProd na A B)
| term_direct_subterm_5_1 : forall (na : aname) (A t : term),
  term_direct_subterm t (tLambda na A t)
| term_direct_subterm_5_2 : forall (na : aname) (A t : term),
  term_direct_subterm A (tLambda na A t)
| term_direct_subterm_6_1 : forall (na : aname) (b B t : term),
  term_direct_subterm t (tLetIn na b B t)
| term_direct_subterm_6_2 : forall (na : aname) (b B t : term),
  term_direct_subterm B (tLetIn na b B t)
| term_direct_subterm_6_3 : forall (na : aname) (b B t : term),
  term_direct_subterm b (tLetIn na b B t)
| term_direct_subterm_7_1 : forall u v : term,
  term_direct_subterm v (tApp u v)
| term_direct_subterm_7_2 : forall u v : term,
  term_direct_subterm u (tApp u v)
| term_direct_subterm_11_1 : forall (ci : case_info)
     (p : predicate term) (c : term) (brs : list (branch term)),
   term_direct_subterm c (tCase ci p c brs)
| term_direct_subterm_11_2 : forall (ci : case_info)
  (p : predicate term) (c : term) (brs : list (branch term)),
  term_direct_subterm p.(preturn) (tCase ci p c brs)
| term_direct_subterm_12_1 : forall (p : projection) (c : term),
  term_direct_subterm c (tProj p c).
Derive Signature for term_direct_subterm.

Definition term_direct_subterm_context (t u : term) (p : term_direct_subterm t u) : context :=
  match p with
  | term_direct_subterm_4_1 na A B => [vass na A]
  | term_direct_subterm_5_1 na A t => [vass na A]
  | term_direct_subterm_6_1 na b B t => [vdef na b B]
  | term_direct_subterm_11_2 ci p c brs => inst_case_predicate_context p
  | _ => []
  end.

Require Equations.Type.WellFounded.
Definition term_subterm := Relation.trans_clos term_direct_subterm.

Fixpoint term_subterm_context {t u : term} (p : term_subterm t u) : context :=
  match p with
  | Relation.t_step y xy => term_direct_subterm_context _ _ xy
  | Relation.t_trans y z rxy ryz =>
    term_subterm_context rxy ++ term_subterm_context ryz
  end.

Definition term_subterm_wf : Equations.Type.WellFounded.well_founded term_subterm.
Proof.
  eapply WellFounded.wf_trans_clos.
  red. fix IH 1. intro x; constructor.
  destruct x; intros y sub; depelim sub; apply IH.
Defined.

(** At least one step of reduction *)
Definition redp Σ Γ t u := Relation.trans_clos (red1 Σ Γ) t u.

#[global]
Instance redp_trans Σ Γ : CRelationClasses.Transitive (redp Σ Γ).
Proof. econstructor 2; eauto. Qed.

#[global]
Instance redp_red Σ Γ : CRelationClasses.subrelation (redp Σ Γ) (red Σ Γ).
Proof.
  intros x y.
  induction 1; solve [econstructor; eauto].
Qed.

#[global]
Instance cored_transitive Σ Γ : RelationClasses.Transitive (cored Σ Γ).
Proof.
  intros x y z.
  induction 1 in z |- *. econstructor 2; eauto.
  intros uz. specialize (IHcored _ uz).
  econstructor 2. eapply IHcored. assumption.
Qed.

Lemma cored_redp Σ Γ t u : cored Σ Γ u t <-> ∥ redp Σ Γ t u ∥.
Proof.
  split.
  * induction 1; sq; try solve [econstructor; eauto].
    transitivity v; auto. now constructor.
  * intros []. induction X.
    + now constructor.
    + now transitivity y.
Qed.

(** Well-founded relation allowing to define functions using weak-head reduction
on (welltyped) terms and going under binders. *)
Section fix_sigma.
  Context {cf : checker_flags} {no : normalizing_flags}.
  Context {Σ : global_env_ext} {normalization:NormalizationIn Σ} {HΣ : ∥wf_ext Σ∥}.

  Lemma term_subterm_red1 {Γ s s' t} {ts : term_subterm s t} :
    red1 Σ (Γ ,,, term_subterm_context ts) s s' ->
    exists t', ∥ red1 Σ Γ t t' × ∑ ts' : term_subterm s' t', term_subterm_context ts' = term_subterm_context ts ∥.
  Proof using Type.
    induction ts in Γ, s' |- *.
    - induction r; simpl.
    all:intros red; eexists; split;
    try solve [split; [solve [eauto using red1]|unshelve eexists;[repeat constructor|simpl; eauto]]].
    split.
    eapply letin_red_body; eauto. unshelve eexists. repeat constructor. reflexivity.
    split.
    eapply letin_red_ty; eauto. unshelve eexists. repeat constructor. reflexivity.
    split. eapply letin_red_def; eauto. unshelve eexists. repeat constructor. reflexivity.
    split. eapply case_red_return; eauto. unshelve eexists. repeat constructor.
    eapply (term_direct_subterm_11_2 ci (set_preturn p s')). simpl. reflexivity.
    - simpl. intros.
    rw app_context_assoc in X.
    specialize (IHts1 _ _ X) as [t' [[yt' [ts Hts]]]].
    specialize (IHts2 _ _ yt') as [t'' [[zt' [ts'' Hts'']]]].
    exists t''. split; split; auto.
    unshelve eexists. econstructor 2; eauto. simpl.
    now rw Hts Hts''.
  Qed.

  Lemma term_subterm_redp {Γ s s' t} {ts : term_subterm s t} :
    redp Σ (Γ ,,, term_subterm_context ts : context) s s' ->
    exists t', ∥ redp Σ Γ t t' × ∑ ts' : term_subterm s' t', term_subterm_context ts' = term_subterm_context ts ∥.
  Proof using Type.
    intros r.
    generalize_eqs r. intros ->. revert t ts.
    induction r.
    - intros t ts ->.
      destruct (term_subterm_red1 r) as [t' [[red1 [ts' Hts']]]].
      exists t'; split; auto. split; auto. now constructor. exists ts'; auto.
    - intros t ts ->. specialize (IHr1 t ts eq_refl) as [t' [[yt' [ts' Hts]]]].
      specialize (IHr2 t' ts').
      forward IHr2. now rw Hts.
      destruct IHr2 as [t'' [[zt' [ts'' Hts'']]]].
      exists t''. split; split; auto.
      now transitivity t'.
      exists ts''.
      now rw Hts'' Hts.
  Qed.

  Definition hnf_subterm_rel : Relation_Definitions.relation (∑ Γ t, welltyped Σ Γ t) :=
    fun '(Γ2; t2; H) '(Γ1; t1; H2) =>
    ∥∑ t', red (fst Σ) Γ1 t1 t' × ∑ ts : term_subterm t2 t', Γ2 = (Γ1 ,,, term_subterm_context ts) ∥.

  Ltac sq' := try (destruct HΣ; clear HΣ);
    repeat match goal with
    | H : ∥ _ ∥ |- _ => destruct H; try clear H
    end; try eapply sq.

  Definition wf_hnf_subterm_rel : WellFounded hnf_subterm_rel.
  Proof.
    intros (Γ & s & H). sq'.
    induction (normalization_in Γ s H) as [s _ IH].
    induction (term_subterm_wf s) as [s _ IH_sub] in Γ, H, IH |- *.
    econstructor.
    intros (Γ' & t2 & ?) [(t' & r & ts & eqctx)].
    eapply Relation_Properties.clos_rt_rtn1 in r. inversion r.
    + subst. eapply IH_sub; auto.
      intros.
      inversion H0.
      * subst.
        destruct (term_subterm_red1 X0) as [t'' [[redt' [tst' Htst']]]].
        eapply IH. econstructor. eauto. red.
        sq. exists t''. split; eauto. exists tst'. now rw Htst'.
        Unshelve.
        eapply red_welltyped; sq. 3:eapply red1_red; tea. all:eauto.
      * subst. eapply cored_redp in H2 as [].
        pose proof (term_subterm_redp X1) as [t'' [[redt' [tst' Htst']]]].
        rw -Htst' in X0.
        destruct (term_subterm_red1 X0) as [t''' [[redt'' [tst'' Htst'']]]].
        eapply IH.
        eapply cored_redp. sq. transitivity t''; eauto.
        constructor; eauto.
        split.
        exists t'''. split; auto. exists tst''.
        now rw Htst'' Htst'.
        Unshelve.
        eapply red_welltyped in H; eauto. all:sq; eauto.
        eapply redp_red in redt'.
        now transitivity t''.
      + subst. eapply IH.
      * eapply red_neq_cored.
        eapply Relation_Properties.clos_rtn1_rt. exact r.
        intros ?. subst.
        eapply Relation_Properties.clos_rtn1_rt in X1.
        eapply cored_red_trans in X0; [| exact X1 ].
        eapply Acc_no_loop in X0. eauto.
        eapply @normalization; eauto.
      * split. exists t'. split; eauto.
    Unshelve.
    - eapply red_welltyped; sq.
      3:eapply Relation_Properties.clos_rtn1_rt in r; eassumption. all:eauto.
  Defined.

  Global Instance wf_hnf_subterm : WellFounded hnf_subterm_rel.
  Proof.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_hnf_subterm_rel.
  Defined.
  Opaque wf_hnf_subterm.
  Opaque Acc_intro_generator.
  Opaque Wf.Acc_intro_generator.
  Ltac sq := try (destruct HΣ as [wfΣ]; clear HΣ);
    repeat match goal with
    | H : ∥ _ ∥ |- _ => destruct H
    end; try eapply sq.

End fix_sigma.

Section fix_sigma.
  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  (* Reducing at least one step or taking a subterm is well-founded *)
  Definition redp_subterm_rel : Relation_Definitions.relation (∑ Γ t, forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t) :=
    fun '(Γ2; t2; H) '(Γ1; t1; H2) => forall Σ (wfΣ : abstract_env_ext_rel X Σ),
    ∥ (redp Σ Γ1 t1 t2 * (Γ1 = Γ2)) + ∑ ts : term_subterm t2 t1, Γ2 = (Γ1 ,,, term_subterm_context ts) ∥.

  Definition wf_redp_subterm_rel : WellFounded redp_subterm_rel.
  Proof.
    intros (Γ & s & H). pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose (wf_extΣ := abstract_env_ext_wf _ wfΣ). sq.
    induction (normalization_in Σ wf_extΣ wfΣ Γ s (H _ wfΣ)) as [s _ IH].
    induction (term_subterm_wf s) as [s _ IH_sub] in Γ, H, IH |- *.
    econstructor.
    intros (Γ' & t2 & ?). intro R. specialize (R _ wfΣ).
    destruct R as [[[r eq]|[ts eqctx]]].
    + subst. eapply Relation_Properties.trans_clos_tn1 in r.
      eapply IH. clear -r.
      induction r; try solve [econstructor; auto].
      now eapply cored_trans with y.
    + subst.
      apply IH_sub. eauto.
      intros. eapply cored_redp in H0 as [].
      destruct (term_subterm_redp X0) as [t'' [[redt' [tst' Htst']]]].
      eapply IH. eapply cored_redp. sq. eassumption. red. intros.
      sq. right. exists tst'. now rw Htst'.
    Unshelve. intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
              eapply redp_red in redt'; eapply red_welltyped; sq; eauto.
    Unshelve. eauto.
  Defined.

  Global Instance wf_redp_subterm : WellFounded redp_subterm_rel.
  Proof.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_redp_subterm_rel.
  Defined.
  Opaque wf_redp_subterm.
  Opaque Acc_intro_generator.
  Opaque Wf.Acc_intro_generator.

End fix_sigma.
