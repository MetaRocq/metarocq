(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require EEtaExpandedFix.
From MetaRocq.Erasure Require Import EProgram EEnvMap EGlobalEnv EWellformed
  EWcbvEval EReorderCstrs.
Import Transform.

#[local] Obligation Tactic := idtac.

Definition eval_eprogram_mapping (wfl : WcbvFlags)
  (p : inductives_mapping * eprogram) t :=
  eval_eprogram wfl p.2 t.

Definition eval_eprogram_env_mapping (wfl : WcbvFlags)
  (p : inductives_mapping * eprogram_env) t :=
  eval_eprogram_env wfl p.2 t.

Definition to_program (e : eprogram_env) : eprogram :=
  (e.1, e.2).

Program Definition reorder_cstrs_transformation {efl : EEnvFlags}
  {wca : cstr_as_blocks = false} {has_app : has_tApp}
  (wfl : WcbvFlags) {wcon : with_constructor_as_block = false} :
  Transform.t _ _ _ EAst.term _ _
    (eval_eprogram_env_mapping wfl) (eval_eprogram wfl) :=
  {| name := "reorder inductive constructors ";
    transform p _ := EReorderCstrs.reorder_program p.1 (to_program p.2) ;
    pre p := [/\ wf_eprogram_env efl p.2,
      EEtaExpandedFix.expanded_eprogram_env p.2 &
      wf_inductives_mapping p.2.1 p.1] ;
    post p := wf_eprogram efl p /\ EEtaExpandedFix.expanded_eprogram p;
    obseq p hp p' v v' := v' = EReorderCstrs.reorder p.1 v |}.

Next Obligation.
  move=> efl wca hasapp wfl wcb [m p] [wfp exp wfm]. split => //.
  now unshelve eapply reorder_program_wf. cbn.
  now eapply reorder_program_expanded_fix.
Qed.
Next Obligation.
  red. intros efl wca hasapp wfl wcb [m p] v [wfp wfm] evp.
  destruct evp as [ev].
  unshelve eapply EReorderCstrs.optimize_correct in ev; trea.
  2,3:apply wfp.
  exists (reorder m v). split => //.
Qed.

#[global]
Instance reorder_cstrs_transformation_ext {efl : EEnvFlags}
  (wca : cstr_as_blocks = false) (has_app : has_tApp) (wfl : WcbvFlags)
  {wcon : with_constructor_as_block = false} :
  TransformExt.t
    (reorder_cstrs_transformation (wca := wca) (has_app := has_app) wfl
      (wcon:=wcon))
    (fun p p' => p.1 = p'.1 /\ extends p.2.1 p'.2.1)
    (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' [eq ext].
  red; cbn. rewrite -eq.
  eapply EReorderCstrs.optimize_extends_env; eauto.
  move: pr'; cbn. now intros []. apply pr. apply pr'.
Qed.

#[global]
Instance reorder_cstrs_transformation_ext' {efl : EEnvFlags}
  (wca : cstr_as_blocks = false) (has_app : has_tApp) (wfl : WcbvFlags)
  {wcon : with_constructor_as_block = false} :
  TransformExt.t
    (reorder_cstrs_transformation (wca := wca) (has_app := has_app) wfl
      (wcon:=wcon))
    (fun p p' => p.1 = p'.1 /\ extends_eprogram_env p.2 p'.2)
    extends_eprogram.
Proof.
  red. intros p p' pr pr' [eq [ext eq']]. cbn.
  red. cbn. rewrite -eq -eq'. split => //.
  eapply EReorderCstrs.optimize_extends_env; eauto.
  move: pr'; cbn. now intros []. apply pr. apply pr'.
Qed.
