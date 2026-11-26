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

#[local] Obligation Tactic := idtac.

From MetaRocq.Erasure Require Import EUnboxing.

Program Definition unbox_transformation (efl : EEnvFlags) (wfl : WcbvFlags) {has_app : has_tApp} {has_cofix : ~~ has_tCoFix} {has_prop_case : has_tBox || ~~with_prop_case} {has_letin : has_tLetIn} {has_cstrparams : ~~ has_cstr_params} {has_cstr_block: with_constructor_as_block} :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram_env wfl) (eval_eprogram wfl) :=
  {| name := "unbox singleton constructors ";
    transform p _ := EUnboxing.unbox_program p ;
    pre p := wf_eprogram_env efl p ;
    post p := wf_eprogram efl p ;
    obseq p hp p' v v' := v' = unbox p.1 v |}.

Next Obligation.
  red. intros.
  apply wf_unboxing; assumption.
Qed.
Next Obligation.
  red. intros.
  exists (unbox p.1 v); split.
  - eapply unbox_pres; try assumption.
  - reflexivity.
Qed.

#[global]
Instance trust_unbox_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags)
   {happ : has_tApp} {hcofix : ~~ has_tCoFix} {hprop_case : has_tBox || ~~with_prop_case} {hletin : has_tLetIn} {hcstrparams : ~~ has_cstr_params} {hcstrblocks: with_constructor_as_block},
  TransformExt.t (@unbox_transformation efl wfl happ hcofix hprop_case hletin hcstrparams hcstrblocks)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros * h_extends.
  simpl in *.
  unfold wf_eprogram_env in *.
  now eapply unbox_extends.
Qed.

#[global]
Instance trust_unbox_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags)
  {happ : has_tApp} {hcofix : ~~ has_tCoFix} {hprop_case : has_tBox || ~~with_prop_case} {hletin : has_tLetIn} {hcstrparams : ~~ has_cstr_params} {hcstrblocks: with_constructor_as_block},
  TransformExt.t (@unbox_transformation efl wfl happ hcofix hprop_case hletin hcstrparams hcstrblocks)
    extends_eprogram_env extends_eprogram.
Proof.
  red; simpl; unfold extends_eprogram, extends_eprogram_env, wf_eprogram_env.
  do 8 intro.
  intros [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *; subst; split.
  - now eapply unbox_extends.
  - symmetry. unfold unbox_program; simpl.
    now eapply unbox_extends_eq.
Qed.
