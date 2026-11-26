(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EProgram EGlobalEnv EWellformed EWcbvEval
  EFirstorder EConstantsToValues.
Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.

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

(** First-order values contain no constant: they are left unchanged. *)
Lemma consts_to_values_firstorder_evalue_block Σ v :
  firstorder_evalue_block Σ v -> consts_to_values v = v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros i n args _ _ IH. cbn. f_equal.
  rewrite -{2}(map_id args). now apply map_ext_Forall.
Qed.

Lemma firstorder_evalue_block_consts_to_values_env Σ v :
  firstorder_evalue_block Σ v ->
  firstorder_evalue_block (consts_to_values_env Σ) v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros i n args hl hargs IH. constructor => //.
  now rewrite lookup_constructor_pars_args_consts_to_values.
Qed.

Lemma fo_evalue_block_consts_to_values_env Σ v :
  fo_evalue_block (Σ, v) -> fo_evalue_block (consts_to_values_env Σ, v).
Proof.
  intros [fo hco].
  split; [now apply firstorder_evalue_block_consts_to_values_env|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. apply is_coind_consts_to_values.
Qed.

Section ConstsToValuesETransform.
Local Obligation Tactic := idtac.

(** First-order values are unchanged: the readback is the identity. *)
Program Definition consts_to_values_etransform (efl : EEnvFlags)
  (wfl : WcbvFlags) (hApp : has_tApp) (hBox : has_tBox || ~~with_prop_case)
  (hLazy : has_tLazy_Force) :
  ETransform.t extends_env extends_env fo_evalue_block fo_evalue_block
    (fun _ => True) (fun _ => True) :=
  {| ETransform.tr := consts_to_values_transformation efl wfl hApp hBox hLazy;
     ETransform.compile_fo p pr fo := consts_to_values_program p;
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply consts_to_values_transformation_ext.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy [] [] pr pr' _ eq. cbn in eq |- *.
  now rewrite eq.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy [Σ t] pr [fo hco].
  rewrite /consts_to_values_program /=.
  rewrite (consts_to_values_firstorder_evalue_block Σ t) //.
  now apply fo_evalue_block_consts_to_values_env.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy [Σ t] pr v v' [fo hco] obs.
  cbn in fo, obs |- *. subst v'.
  rewrite (consts_to_values_firstorder_evalue_block Σ v) //.
  now apply fo_evalue_block_consts_to_values_env.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy [Σ t] pr p' v v' [fo _] obs.
  cbn in fo, obs. subst v'.
  now rewrite (consts_to_values_firstorder_evalue_block Σ v).
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy [Σ t] pr [fo _].
  cbn. f_equal. now apply (consts_to_values_firstorder_evalue_block Σ).
Qed.
Next Obligation.
  intros. reflexivity.
Qed.
Next Obligation.
  now intros efl wfl hApp hBox hLazy [] [] pr pr'; cbn; intros <-.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy Σ t u pr _.
  unshelve eexists.
  { destruct pr as [? ?]; split; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  unshelve eexists.
  { destruct pr as [? ?]; split; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  cbn. reflexivity.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy [Σ t] pr; cbn.
  apply isFunction_hom => //.
  intros. apply consts_to_values_mkApps.
Qed.
Next Obligation.
  intros efl wfl hApp hBox hLazy [Σ t] pr p' v v' obs hf.
  cbn in obs. subst v'. move: hf.
  apply isFunctionS_hom => //.
  intros. apply consts_to_values_mkApps.
Qed.
End ConstsToValuesETransform.
