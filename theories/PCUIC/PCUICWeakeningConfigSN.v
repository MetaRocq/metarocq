From Stdlib Require Import ssreflect Wellfounded.Inclusion.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICSN PCUICTyping PCUICSafeLemmata PCUICWeakeningConfigTyp.
Import PCUICEnvironment.

Lemma weakening_config_normalization_in {cf1 cf2} {no1 no2}
  Σ
  (Hcf : config.impl cf2 cf1)
  : @PCUICSN.NormalizationIn cf1 no1 Σ -> @PCUICSN.NormalizationIn cf2 no2 Σ.
Proof.
  cbv [PCUICSN.NormalizationIn].
  intros normalization_in Γ t1 [T Hwt]; specialize (normalization_in Γ t1).
  eapply Acc_incl; [ | eapply normalization_in; econstructor; instantiate (1:=T); revert Hwt ].
  { hnf; trivial. }
  eapply (@weakening_config cf2 cf1); assumption.
Qed.
