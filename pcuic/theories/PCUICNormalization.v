(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICWcbvEval PCUICClassification PCUICProgress PCUICSN.

From Equations Require Import Equations.

From MetaRocq.PCUIC Require Import PCUICSN.

Lemma wh_normalization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {t} : wf Σ -> axiom_free Σ ->
{A & Σ ;;; [] |- t : A}  -> { v & whnf RedFlags.default Σ [] v * red Σ [] t v}.
Proof.
intros Hwf Hax [A HA].
assert (welltyped Σ [] t) as Hwt. { econstructor; eauto. }
eapply PCUICSN.normalization_in in Hwt as HSN; eauto. clear Hwt.
induction HSN as [t H IH].
edestruct progress_env_prop as [_ [_ [[t' Ht'] | Hval]]]; eauto.
- eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closed. eauto. }
  edestruct IH as [v Hv]. econstructor. eauto.
  eapply subject_reduction; eauto.
  exists v. sq. destruct Hv. split; eauto. eapply red_step; eauto.
- exists t. sq. split; eauto. eapply value_whnf; eauto.
  eapply @subject_closed with (Γ := []); eauto.
Defined.

Lemma SN_to_WN {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {A t} : wf Σ -> axiom_free Σ ->
  Acc (cored Σ []) t -> Σ ;;; [] |- t : A -> { v & eval Σ t v}.
  intros Hwf Hax HSN HA.
  induction HSN as [t H IH].
  edestruct progress_env_prop as [_ [_ [[t' Ht'] | Hval]]]; eauto.
  - eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closed. eauto. }
    edestruct IH as [v Hv]. econstructor. eauto.
    eapply subject_reduction; eauto.
    exists v. sq. eapply wcbv_red1_eval; eauto.
    now eapply subject_closed in HA.
  - exists t. sq. eapply value_final; eauto.
Qed.

Lemma wcbv_normalization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {A t} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : A -> { v & eval Σ t v}.
Proof.
  intros Hwf Hax HA.
  assert (welltyped Σ [] t) as Hwt. { econstructor; eauto. }
  eapply PCUICSN.normalization_in in Hwt as HSN; eauto. clear Hwt.
  eapply SN_to_WN; eauto.
Qed.

From MetaRocq.PCUIC Require Import PCUICFirstorder.

Lemma firstorder_value_irred {cf:checker_flags} Σ t t' :
  firstorder_value Σ [] t ->
  PCUICReduction.red1 Σ [] t t' -> False.
Proof.
  intros H.
  revert t'. pattern t. revert t H.
  eapply firstorder_value_inds.
  intros i n ui u args pandi Hty Hargs IH Hprop t' Hred.
  eapply red1_mkApps_tConstruct_inv in Hred as (x & -> & Hone).
  solve_all.
  clear - IH Hone. induction IH as [ | ? ? []] in x, Hone |- *.
  - invs Hone.
  - invs Hone; eauto.
Qed.

Definition ws_empty f : ws_context f.
Proof.
  unshelve econstructor.
  exact nil.
  reflexivity.
Defined.

Lemma irred_equal Σ Γ t t' :
  Σ ;;; Γ ⊢ t ⇝ t' ->
  (forall v', PCUICReduction.red1 Σ Γ t v' -> False) ->
  t = t'.
Proof.
  intros Hred Hirred. destruct Hred.
  clear clrel_ctx clrel_src.
  induction clrel_rel.
  - edestruct Hirred; eauto.
  - reflexivity.
  - assert (x = y) as <- by eauto. eauto.
Qed.

Lemma ws_wcbv_standardization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {T} {t v : ws_term (fun _ => false)} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : T ->
  closed_red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  {v' & eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
Proof.
  intros Hwf Hax Hty Hred Hirred.
  destruct (@wcbv_normalization _ no Σ normalization T t) as (v' & Hv'); eauto.
  assert (Σ;;; [] |- t ⇝* v') as Hred' by now eapply wcbveval_red.
  eapply closed_red_confluence in Hred as Hred_. destruct Hred_ as (v'' & H1 & H2).
  2:{ econstructor; eauto. eapply subject_is_open_term. eauto. }
  destruct v as [v Hv].
  assert (v = v'') as <- by (eapply irred_equal; eauto).
  exists v'; split; eauto.
Qed.

Lemma ws_wcbv_standardization_fst {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {i u args mind} {t v : ws_term (fun _ => false)} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  closed_red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  eval Σ t v.
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  destruct (ws_wcbv_standardization Hwf Hax Hty Hred Hirred) as [v' [H H']].
  assert (firstorder_value Σ [] v'). {
    eapply firstorder_value_spec; eauto.
    eapply subject_reduction_eval; eauto.
    eapply eval_to_value. eauto.
  }
  enough (v' = v) as -> by eauto.
  eapply irred_equal. eauto.
  intros. eapply firstorder_value_irred; eauto.
  Unshelve.
Qed.

Lemma wcbv_standardization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {T t v : term} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : T ->
  Σ ;;; [] |- t ⇝ v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  {v' & eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
Proof.
  intros Hwf Hax Hty Hred Hirred.
  unshelve eapply @ws_wcbv_standardization with (T := T) (t := (exist t _)) (v := (exist v _)).
  all: sq; eauto; cbn.
  1-2: shelve.
  econstructor; eauto.
  eapply subject_is_open_term. eauto.
  Unshelve.
  all: rw -closed_on_free_vars_none.
  - now eapply subject_closed in Hty.
  - eapply @subject_closed with (Γ := []); eauto.
    eapply subject_reduction; eauto.
Qed.

Lemma wcbv_standardization_fst {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {i u args mind} {t v : term} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  eval Σ t v.
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  unshelve eapply @ws_wcbv_standardization_fst with (t := (exist t _)) (v := (exist v _)).
  all: sq; eauto; cbn.
  1-2: shelve.
  econstructor; eauto.
  eapply subject_is_open_term. eauto.
  Unshelve.
  all: rw -closed_on_free_vars_none.
  - now eapply subject_closed in Hty.
  - eapply @subject_closed with (Γ := []); eauto.
    eapply subject_reduction; eauto.
Qed.
