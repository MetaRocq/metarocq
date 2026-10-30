From Stdlib Require Import ssreflect Wellfounded.Inclusion.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICSN PCUICTyping PCUICSafeLemmata PCUICWeakeningEnvTyp.
Import PCUICEnvironment.

(* It would be nice to prove this, but I'm not sure how -Jason Gross *)
Class normalizationInAdjustUniversesIn {cf} {no} (Σ : global_env_ext) :=
  normalization_in_adjust_universes
    : forall kn cb,
      lookup_env Σ.1 kn = Some (ConstantDecl cb) ->
      PCUICTyping.wf_ext Σ ->
      PCUICTyping.wf_ext (Σ.1, cst_universes cb) ->
      @NormalizationIn cf no Σ -> @NormalizationIn cf no (Σ.1, cst_universes cb).

Lemma weakening_env_normalization_in {cf} {no}
  Σ Σ' ϕ (Hext : extends Σ Σ')
  (HΣ : PCUICTyping.wf Σ)
  (HΣ' : PCUICTyping.wf Σ')
  : @PCUICSN.NormalizationIn cf no (Σ', ϕ) -> @PCUICSN.NormalizationIn cf no (Σ, ϕ).
Proof.
  cbv [PCUICSN.NormalizationIn].
  intros normalization_in Γ t1 [T Hwt]; specialize (normalization_in Γ t1); move: normalization_in.
  cbn in *.
  move => normalization_in.
  eapply Acc_incl; [ | eapply normalization_in; econstructor; instantiate (1:=T); revert Hwt ].
  { repeat match goal with H : wf_ext _ |- _ => apply wf_ext_wf in H end.
    hnf; eapply weakening_env_cored; eassumption. }
  intro Hty.
  destruct (weakening_env _ _ _ _ _ Hty) as (_&_&H').
  cbn in *.
  repeat match goal with H : wf_ext _ |- _ => apply wf_ext_wf in H end.
  eapply H'; eauto.
Qed.
