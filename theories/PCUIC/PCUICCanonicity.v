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
  PCUICWcbvEval PCUICClassification PCUICSN PCUICNormalization PCUICViews.

Lemma pcuic_canonicity {cf:checker_flags} {nor : normalizing_flags} Σ {normalization_in: NormalizationIn Σ} t i u args :
     axiom_free Σ -> wf Σ ->
     Σ ;;; [] |- t : mkApps (tInd i u) args ->
     { t':term & (Σ ;;; [] |- t' : mkApps (tInd i u) args) * (Σ ;;; [] |- t =s t') * construct_cofix_discr (head t')}.
Proof.
  intros axΣ wfΣ typ_ind. pose proof (_ ; typ_ind) as wt.
  eapply wh_normalization in wt ; eauto.
  destruct wt as [t' [Hnormal Ht']].
  pose proof (Ht'_ := Ht').
  pose proof (typ_ind' := typ_ind).
  eapply subject_reduction in typ_ind; eauto.
  eapply whnf_classification with (args := args) in typ_ind as ctor; auto.
  exists t'; repeat split; eauto.
  eapply cumulAlgo_cumulSpec.
  eapply red_ws_cumul_pb. split; eauto.
  now eapply subject_is_open_term.
Qed.
