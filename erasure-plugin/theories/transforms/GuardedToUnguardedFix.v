(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
Set Warnings "-notation-overridden".
Set Warnings "+notation-overridden".
From MetaRocq.Erasure Require ERemoveParams.
From MetaRocq.TemplatePCUIC Require Import PCUICTransform.

Import EProgram Transform.
Import EEnvMap EGlobalEnv.
From MetaRocq.Erasure.Typed Require Import ExtractionCorrectness.
From MetaRocq.Erasure Require Import EWellformed.


#[local] Obligation Tactic := idtac.

(** This transformation is the identity on terms but changes the evaluation relation to one
    where fixpoints are not guarded. It requires eta-expanded fixpoints and evaluation
    to use the guarded fixpoint rule as a precondition. *)

Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).

Program Definition guarded_to_unguarded_fix {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram_env fl) (eval_eprogram_env (EWcbvEval.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints";
    transform p pre := p;
    pre p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    post p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    obseq p hp p' v v' := v' = v |}.
Next Obligation. cbn. eauto. Qed.
Next Obligation.
  cbn.
  move=> fl wcon efl wguard [Σ t] v [wfp [etae etat]]. cbn in *.
  intros [ev]. exists v. split => //.
  red. sq. cbn in *.
  unshelve eapply EEtaExpandedFix.eval_opt_to_target => //. auto. 2:apply wfp.
  now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

#[global]
Instance guarded_to_unguarded_fix_extends {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  TransformExt.t (guarded_to_unguarded_fix (wcon:=wcon) wguard) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ?. now rewrite /transform /=.
Qed.

#[global]
Instance guarded_to_unguarded_fix_extends' {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  TransformExt.t (guarded_to_unguarded_fix (wcon:=wcon) wguard) extends_eprogram_env extends_eprogram_env.
Proof.
  red. intros p p' pr pr' [? ?]. now rewrite /transform /=.
Qed.
