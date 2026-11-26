(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EProgram EGlobalEnv EWellformed EWcbvEval
  EConstantsToValues.
Import Transform.

#[local] Obligation Tactic := idtac.

Program Definition consts_to_values_transformation (efl : EEnvFlags)
  (wfl : WcbvFlags) (hApp : has_tApp) (hBox : has_tBox || ~~with_prop_case)
  (hLazy : has_tLazy_Force) :
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
  unfold TransformExt.t, transform, consts_to_values_transformation,
    consts_to_values_program, extends_eprogram.
  intros [ctx ->]. split => //. now apply consts_to_values_extends.
Qed.
