(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Environment Transform config BasicAst uGraph.
From MetaRocq.Template Require Pretty Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICWeakeningEnvSN.
Set Warnings "+notation-overridden".
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureCorrectness Extract EOptimizePropDiscr
  ERemoveParams EProgram EConstructorsAsBlocks ECoInductiveToInductive.
From MetaRocq.Erasure Require Import ErasureFunction ErasureFunctionProperties.
From MetaRocq.TemplatePCUIC Require Import PCUICTransform.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform ERemoveParams.
Import EEnvMap EGlobalEnv EWellformed.
From MetaRocq.ErasurePlugin Require Import ETransform.
Import Extract.
From MetaRocq.Erasure.Typed Require Import Erasure ExAst Optimize ExtractionCorrectness OptimizeCorrectness.
From MetaRocq.Erasure Require Import EWellformed.
From MetaRocq.PCUIC Require Import PCUICTyping.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
Set Equations Transparent.
Import EOptimizePropDiscr OptimizePropDiscr EWcbvEval.
Import EOptimizePropDiscr.
Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).

#[local] Obligation Tactic := idtac.

Program Definition remove_params_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl : EEnvFlags) (has_app : has_tApp) (cstrs : cstr_as_blocks = false) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (using a view)";
    transform p pre := ERemoveParams.strip_program p;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = (ERemoveParams.strip p.1 v) |}.
Next Obligation.
  move=> fl wcon efl has_app cstrs [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  split. now eapply ERemoveParams.strip_program_wf.
  now eapply ERemoveParams.strip_program_expanded.
Qed.

Next Obligation.
  red. move=> ? wcon efl hasapp cstrs [Σ t] /= v [[wfe wft] etap] [ev].
  unshelve eapply ERemoveParams.strip_eval in ev; cbn -[strip] in *; eauto.
  eexists; split => /= //.
  - now sq.
  - now move/andP: etap.
  - now eapply wellformed_closed_env.
  - now move/andP: etap.
Qed.

#[global]
Instance remove_params_extends {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl : EEnvFlags) (has_app : has_tApp) (cstrs : cstr_as_blocks = false) :
  TransformExt.t (remove_params_optimization (fl := fl) (wcon:=wcon) efl has_app cstrs) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /= /strip_program.
  red. cbn -[strip_env strip]. eapply strip_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance remove_params_extends' {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl : EEnvFlags) (has_app : has_tApp) (cstrs : cstr_as_blocks = false) :
  TransformExt.t (remove_params_optimization (wcon:=wcon) efl has_app cstrs) extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /strip_program. rewrite eq.
  red. cbn -[strip_env strip]. split. eapply strip_extends_env => //. apply pr. apply pr'.
  cbn -[strip_env strip]. eapply strip_extends => //. apply pr'. rewrite -eq. apply pr.
Qed.

Program Definition remove_params_fast_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl : EEnvFlags) (has_app : has_tApp) (cstrs : cstr_as_blocks = false) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (using accumulators)";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = (ERemoveParams.strip p.1 v) |}.
Next Obligation.
  move=> fl wcon efl has_app cstrs [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  split.
  now eapply (ERemoveParams.strip_program_wf has_app cstrs (Σ, t)).
  now eapply (ERemoveParams.strip_program_expanded has_app (Σ, t)).
Qed.

Next Obligation.
  red. move=> ? wcon efl has_app cstrs [Σ t] /= v [[wfe wft] etap] [ev].
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //.
  now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now move/andP: etap.
Qed.

#[global]
Instance remove_params_fast_extends {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl : EEnvFlags) (has_app : has_tApp) (cstrs : cstr_as_blocks = false) :
  TransformExt.t (remove_params_fast_optimization (wcon:=wcon) efl has_app cstrs) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  rewrite -!ERemoveParams.Fast.strip_env_fast.
  eapply strip_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance remove_params_fast_extends' {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl : EEnvFlags) (has_app : has_tApp) (cstrs : cstr_as_blocks = false) :
  TransformExt.t (remove_params_fast_optimization (wcon:=wcon) efl has_app cstrs) extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. rewrite eq.
  rewrite -!ERemoveParams.Fast.strip_env_fast -!ERemoveParams.Fast.strip_fast.
  split => /=. eapply strip_extends_env => //. apply pr. apply pr'.
  eapply strip_extends => //. apply pr'. rewrite -eq. apply pr.
Qed.
