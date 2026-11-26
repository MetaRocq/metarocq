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

#[local] Obligation Tactic := idtac.

From MetaRocq.Erasure Require EPushForce.

(** Pushing forces inside terms, cancelling them against thunks. Values are
    observed up to [EPushForce.frel], which only differs from equality under
    a force: first-order values are observed unchanged
    ([EPushForce.frel_firstorder_evalue_block]). *)
Program Definition push_force_transformation (efl : EEnvFlags)
  (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "pushing forces inside terms";
    transform p _ := EPushForce.force_opt_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram efl p ;
    obseq p hp p' v v' := ∥ EPushForce.frel v v' ∥ /\
      ∥ value (wfl := wfl) p'.1 v' ∥ |}.

Next Obligation.
  move=> efl wfl p wf. now apply EPushForce.force_opt_program_wf.
Qed.
Next Obligation.
  red. move=> efl wfl [Σ t] /= v wf [ev].
  destruct (EPushForce.force_opt_correct Σ t v ev) as [v' [ev' hv]].
  exists v'. split; [now constructor|]. split; [now constructor|].
  constructor. now eapply eval_to_value.
Qed.

#[global]
Instance push_force_transformation_ext (efl : EEnvFlags) (wfl : WcbvFlags) :
  TransformExt.t (push_force_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  now apply EPushForce.force_opt_env_extends.
Qed.

#[global]
Instance push_force_transformation_ext' (efl : EEnvFlags) (wfl : WcbvFlags) :
  TransformExt.t (push_force_transformation efl wfl)
    extends_eprogram extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. split.
  - now apply EPushForce.force_opt_env_extends.
  - cbn. now rewrite eq.
Qed.

Lemma frel_isFunctionS t t' :
  EPushForce.frel t t' -> isFunctionS t -> isFunctionS t'.
Proof.
  have napp := EAstUtils.decompose_app_notApp _ _ _
    (EAstUtils.decompose_app_head_spine t).
  rewrite -(EAstUtils.mkApps_head_spine t). move: napp.
  generalize (EAstUtils.head t) (EAstUtils.spine t) => hd l napp h.
  apply EPushForce.frel_mkApps_inv in h as [hd' [l' [-> hhd hl]]].
  have hlen := All2_length hl.
  rewrite /isFunctionS /cofix_unsaturated /isFunction /EAstUtils.isFixApp
    !EAstUtils.head_mkApps !isLambda_mkApps_eq.
  rewrite EAstUtils.decompose_app_mkApps //.
  destruct hd => //=; depelim hhd => //=; rewrite ?hlen //.
  all: rewrite EAstUtils.decompose_app_mkApps //= ?orb_true_r //.
  intros h. move: h.
  destruct (nth_error mfix idx) eqn:hn => //.
  eapply All2_nth_error_Some in a as [d' [-> [_ hr _]]]; tea.
  now rewrite hr.
Qed.

Lemma force_opt_mkApps f l :
  EPushForce.force_opt (EAst.mkApps f l) =
  EAst.mkApps (EPushForce.force_opt f) (List.map EPushForce.force_opt l).
Proof.
  induction l using rev_ind; simpl; auto.
  now rewrite EAstUtils.mkApps_app /= IHl map_app /= EAstUtils.mkApps_app.
Qed.

Lemma force_opt_firstorder_evalue_block Σ v :
  firstorder_evalue_block Σ v -> EPushForce.force_opt v = v.
Proof.
  intros fo. eapply EPushForce.frel_firstorder_evalue_block; tea.
  apply EPushForce.frel_force_opt.
Qed.

Lemma firstorder_evalue_block_force_opt_env Σ v :
  firstorder_evalue_block Σ v ->
  firstorder_evalue_block (EPushForce.force_opt_env Σ) v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros i n args hl hargs IH. constructor => //.
  move: hl. rewrite /EGlobalEnv.lookup_constructor_pars_args.
  now rewrite EPushForce.lookup_constructor_force_opt.
Qed.

Lemma fo_evalue_block_force_opt_env Σ v :
  fo_evalue_block (Σ, v) -> fo_evalue_block (EPushForce.force_opt_env Σ, v).
Proof.
  intros [fo hco]. split; [now apply firstorder_evalue_block_force_opt_env|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. apply EPushForce.is_coind_force_opt.
Qed.

Section PushForceETransform.
Local Obligation Tactic := idtac.

(** First-order values contain no force: the readback is the identity. *)
Program Definition push_force_etransform (efl : EEnvFlags) (wfl : WcbvFlags) :
  ETransform.t extends_env extends_env fo_evalue_block fo_evalue_block
    (fun _ => True) (fun _ => True) :=
  {| ETransform.tr := push_force_transformation efl wfl;
     ETransform.compile_fo p pr fo := EPushForce.force_opt_program p;
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply push_force_transformation_ext.
Qed.
Next Obligation.
  intros efl wfl p p' pr pr' ext eq.
  now apply (push_force_transformation_ext' efl wfl p p' pr pr').
Qed.
Next Obligation.
  intros efl wfl [Σ t] pr fo.
  rewrite /EPushForce.force_opt_program /=.
  rewrite (force_opt_firstorder_evalue_block Σ t) //. apply fo.
  now apply fo_evalue_block_force_opt_env.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl [Σ t] pr v v' [fo hco] [[obs] _].
  cbn in fo, obs |- *.
  apply (EPushForce.frel_firstorder_evalue_block Σ) in obs => //.
  subst v'. now apply fo_evalue_block_force_opt_env.
Qed.
Next Obligation.
  intros efl wfl [Σ t] pr p' v v' [fo _] [[obs] _].
  apply (EPushForce.frel_firstorder_evalue_block Σ) in obs => //.
  now subst v'.
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  intros efl wfl [Σ t] pr [fo _].
  cbn. f_equal. now apply (force_opt_firstorder_evalue_block Σ).
Qed.
Next Obligation.
  intros. reflexivity.
Qed.
Next Obligation.
  now intros efl wfl [] [] pr pr'; cbn; intros <-.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl Σ t u pr _.
  unshelve eexists.
  { destruct pr as [? ?]; split; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  unshelve eexists.
  { destruct pr as [? ?]; split; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  cbn. reflexivity.
Qed.
Next Obligation.
  intros efl wfl [Σ t] pr; cbn.
  have napp := EAstUtils.decompose_app_notApp _ _ _
    (EAstUtils.decompose_app_head_spine t).
  rewrite -(EAstUtils.mkApps_head_spine t). move: napp.
  generalize (EAstUtils.head t) (EAstUtils.spine t) => f l napp.
  rewrite force_opt_mkApps.
  rewrite /isFunction /EAstUtils.isFixApp !EAstUtils.head_mkApps.
  rewrite !isLambda_mkApps_eq.
  destruct f => //=; rewrite ?length_map //.
Qed.
Next Obligation.
  intros efl wfl [Σ t] pr p' v v' [[obs] _] hf.
  now eapply frel_isFunctionS.
Qed.
End PushForceETransform.
