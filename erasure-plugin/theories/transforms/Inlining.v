(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require EAstUtils ELiftSubst ECoInductiveToInductive.
From MetaRocq.Erasure Require Import Extract EProgram EEnvMap EGlobalEnv
  EWellformed EWcbvEval EFirstorder.
Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.Erasure Require Import EInlining.

#[local] Obligation Tactic := idtac.

Program Definition inline_transformation (efl : EEnvFlags) (wfl : WcbvFlags)
  inlining (hApp : has_tApp) (hBox : has_tBox || ~~ with_prop_case) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_inlined_program wfl) :=
  {| name := "inlining ";
    transform p _ := inline_program inlining p ;
    pre p := wf_eprogram efl p;
    post (p : inlined_program) := wf_eprogram efl p;
    obseq p hp (p' : inlined_program) v v' := v' = inline p' v |}.

Next Obligation.
  intros. now apply inlining_wf.
Qed.
Next Obligation.
  repeat intro.
  now eapply inlining_pres.
Qed.


#[global]
Instance inline_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inlining hApp hBox,
  TransformExt.t (inline_transformation efl wfl inlining hApp hBox)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1.1 p'.1.1).
Proof.
  intros ? ? inlining ? ?.
  unfold TransformExt.t, transform, inline_transformation, inline_program.
  intros [ctx e] [ctx' e'] [? ?] [? ?] h_extends.
  EInlining.simple.
  now eapply extends_inline_env.
Qed.



#[global]
Instance inline_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inlining hApp hBox,
  TransformExt.t (inline_transformation efl wfl inlining hApp hBox)
    extends_eprogram extends_inlined_eprogram.
Proof.
  intros ? ? inlining ? ?.
  unfold TransformExt.t, transform, inline_transformation, inline_program,
    extends_inlined_eprogram.
  intros [ctx e] [ctx' e'] [? ?] [? ?] [h_extends []].
  pose proof extends_inline_env efl.
  pose proof inline_extends efl inlining.
  now simple.
Qed.



Program Definition forget_inlining_info_transformation (efl : EEnvFlags)
  (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
      (eval_inlined_program wfl) (eval_eprogram wfl) :=
    {| name := "forgetting about inlining info";
      transform p _ := (p.1.1, p.2) ;
      pre (p : inlined_program) := wf_eprogram efl p ;
      post (p : eprogram) := wf_eprogram efl p ;
      obseq p hp p' v v' := v' = v |}.

  Next Obligation.
    intros efl wfl [[Σ inls] t] p.
    exact p.
  Qed.
  Next Obligation.
    intros efl wfl [[Σ inls] t] v [wf_Σ wf_t] [h_eval] p'.
    now exists v.
  Qed.

#[global]
Instance forget_inlining_info_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (forget_inlining_info_transformation efl wfl)
    (fun p p' => extends p.1.1 p'.1.1) (fun p p' => extends p.1 p'.1).
Proof.
  intros.
  red. now intros [[] ?] [[] ?]; cbn.
Qed.

#[global]
Instance forget_inlining_info_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (forget_inlining_info_transformation efl wfl)
    extends_inlined_eprogram extends_eprogram.
Proof.
  intros ? ? [[] ?] [[] ?]; cbn.
   now rewrite /extends_inlined_eprogram /extends_eprogram /=.
Qed.

Lemma inline_firstorder_block inls Σ v :
  firstorder_evalue_block Σ v -> inline inls v = v.
Proof.
  revert v. apply: firstorder_evalue_block_elim; intros i n args hl hargs IH.
  simp inline. f_equal. ELiftSubst.solve_all.
Qed.

Lemma firstorder_block_inline_env {efl : EEnvFlags} inls Σ v :
  firstorder_evalue_block Σ v ->
  firstorder_evalue_block (inline_env inls Σ).1 v.
Proof.
  revert v. apply: firstorder_evalue_block_elim; intros i n args hl hargs IH.
  constructor => //.
  move: hl. rewrite /EGlobalEnv.lookup_constructor_pars_args.
  simple. now intros.
Qed.

Definition extends_inl
  (p p' :
    Transform.program (E.global_context × constants_inlining) EAst.term) :=
  extends p.1.1 p'.1.1.
Definition fo_evalue_block_inl
  (p : Transform.program (E.global_context × constants_inlining) EAst.term) :=
  firstorder_evalue_block p.1.1 p.2 /\
  ∥ EFirstorder.firstorder_ind_value p.1.1 p.2 ∥.

Section InlineETransform.
Local Obligation Tactic := idtac.

(** First-order values contain no constants: the readback is the
    identity. *)
Program Definition inline_etransform (efl : EEnvFlags) (wfl : WcbvFlags)
  inlining (hApp : has_tApp) (hBox : has_tBox || ~~ with_prop_case) :
  ETransform.t extends_env extends_inl fo_evalue_block fo_evalue_block_inl
    (fun _ => True) (fun _ => True) :=
  {| ETransform.tr := inline_transformation efl wfl inlining hApp hBox;
     ETransform.compile_fo p pr fo := inline_program inlining p;
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply inline_transformation_ext.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox p p' pr pr' ext eq.
  now apply (inline_transformation_ext' efl wfl inlining hApp hBox p p' pr pr').
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox [Σ t] pr [fo hco].
  rewrite /fo_evalue_block_inl /inline_program /=.
  destruct_inline_env; cbn [fst snd] in *.
  rewrite (inline_firstorder_block _ Σ t fo).
  split; [now apply firstorder_block_inline_env|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. now rewrite inline_is_coind.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox [Σ t] pr v v' [fo hco] obs.
  unfold obseq, inline_transformation in obs. subst v'.
  rewrite /fo_evalue_block_inl.
  rewrite (inline_firstorder_block _ Σ v fo).
  cbn. rewrite /inline_program /=. destruct_inline_env; cbn [fst snd] in *.
  split; [now apply firstorder_block_inline_env|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. now rewrite inline_is_coind.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox [Σ t] pr p' v v' [fo _] obs.
  unfold obseq, inline_transformation in obs. subst v'.
  f_equal. now apply (inline_firstorder_block _ Σ).
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox [Σ t] pr [fo _].
  rewrite /inline_program /=. destruct_inline_env; cbn [fst snd] in *.
  f_equal. now apply (inline_firstorder_block _ Σ).
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox p p' pr pr' eq.
  destruct p, p'; simpl in *; subst.
  now unfold inline_program; repeat destruct_inline_env.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox Σ t u pr _.
  unshelve eexists.
  now unfold pre, inline_transformation, wf_eprogram in *; simple.
  unshelve eexists.
  now unfold pre, inline_transformation, wf_eprogram in *; simple.
  simpl.
  now unfold inline_program; repeat destruct_inline_env.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox p pr H.
  unfold isFunction, inline_transformation, transform, inline_program in *.
  repeat destruct_inline_env.
  simple.
  unfold is_true in *.
  rewrite ->!orb_true_iff in *.
  destruct H as [[H | H] | H].
  + repeat left. now apply isLambda_inline.
  + left; right. now apply inline_isFixApp_imp.
  + repeat right. now apply inline_isCoFixHead_imp.
Qed.
Next Obligation.
  intros efl wfl inlining hApp hBox p pr p' v v' obs.
  unfold obseq, inline_transformation in obs. subst v'.
  apply isFunctionS_hom => //.
  intros. apply inline_mkApps.
Qed.
End InlineETransform.

Section ForgetInliningETransform.
Local Obligation Tactic := idtac.

Program Definition forget_inlining_info_etransform (efl : EEnvFlags)
  (wfl : WcbvFlags) :
  ETransform.t extends_inl extends_env fo_evalue_block_inl fo_evalue_block
    (fun _ => True) (fun _ => True) :=
  {| ETransform.tr := forget_inlining_info_transformation efl wfl;
     ETransform.compile_fo p pr fo := (p.1.1, p.2);
     ETransform.readback := Some |}.
Next Obligation.
  intros efl wfl [[] ?] [[] ?] pr pr' ext. exact ext.
Qed.
Next Obligation.
  now intros efl wfl [[] ?] [[] ?] pr pr' ext eq.
Qed.
Next Obligation.
  now intros efl wfl [[] ?] pr fo.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl p pr v v' fo obs. change (v' = v) in obs. subst v'.
  exact fo.
Qed.
Next Obligation.
  intros efl wfl p pr p' v v' fo obs. change (v' = v) in obs. subst v'.
  reflexivity.
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl [[] ?] [[] ?] pr pr' eq. cbn in *. now subst.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl wfl Σ t u pr _.
  unshelve eexists.
  { destruct Σ as [Σ inl]. destruct pr as [wfΣ wft]. split => //.
    cbn in wft |- *. now move/andP: wft => [] /andP []. }
  unshelve eexists.
  { destruct Σ as [Σ inl]. destruct pr as [wfΣ wft]. split => //.
    cbn in wft |- *. now move/andP: wft => [] /andP []. }
  reflexivity.
Qed.
Next Obligation.
  now intros efl wfl [[] ?] pr h.
Qed.
Next Obligation.
  intros efl wfl p pr p' v v' obs h. change (v' = v) in obs. now subst v'.
Qed.
End ForgetInliningETransform.
