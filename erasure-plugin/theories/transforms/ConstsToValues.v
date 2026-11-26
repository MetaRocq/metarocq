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
Import EOptimizePropDiscr EWcbvEval.
From MetaRocq.Erasure Require Import EInlineProjections.
From MetaRocq.Erasure Require Import EConstructorsAsBlocks.
From MetaRocq.Erasure Require ECoInductiveToInductive.
From MetaRocq.Erasure Require EPushForce.
From MetaRocq.Erasure Require Import EReorderCstrs.
From MetaRocq.Erasure Require Import EUnboxing.

#[local] Obligation Tactic := idtac.

From MetaRocq.Erasure Require Import EConstantsToValues.

Program Definition consts_to_values_transformation (efl : EEnvFlags) (wfl : WcbvFlags) (hApp : has_tApp) (hBox : has_tBox || ~~with_prop_case) (hLazy : has_tLazy_Force) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "Constants to values";
    transform p _ := consts_to_values_program p ;
    pre p := wf_eprogram efl p ;
    post (p : eprogram) := wf_eprogram efl p /\ ∥ lazy_glob p.1∥ ;
    obseq p hp (p' : eprogram) v v' := v' = consts_to_values v |}.

Next Obligation.
  repeat intro.
  split.
  + now apply wf_consts_to_values.
  + constructor.
    now apply consts_to_values_env_lazy.
Qed.

Next Obligation.
  repeat intro.
  pose proof consts_to_values_pres.
  now eexists.
Qed.

#[global]
Instance consts_to_values_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) hApp hBox hLazy,
  TransformExt.t (consts_to_values_transformation efl wfl hApp hBox hLazy)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  intros efl wfl hApp hBox hLazy p p' h1 h2.
  apply consts_to_values_extends.
Qed.


#[global]
Instance consts_to_values_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) hApp hBox hLazy,
  TransformExt.t (consts_to_values_transformation efl wfl hApp hBox hLazy)
    extends_eprogram extends_eprogram.
Proof.
  intros efl wfl hApp hBox hLazy p p' h1 h2.
  unfold TransformExt.t, transform, consts_to_values_transformation, consts_to_values_program, extends_eprogram.
  intros [ctx ->]. split => //. now apply consts_to_values_extends.
Qed.
