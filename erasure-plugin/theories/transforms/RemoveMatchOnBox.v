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

Import EOptimizePropDiscr EWcbvEval.

Program Definition remove_match_on_box_trans {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _  EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram (disable_prop_cases fl)) :=
  {| name := "optimize_prop_discr";
    transform p _ := remove_match_on_box_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram efl p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = EOptimizePropDiscr.remove_match_on_box p.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply remove_match_on_box_program_wf.
  - now eapply remove_match_on_box_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EOptimizePropDiscr.remove_match_on_box_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
  Unshelve. eauto.
Qed.

#[global]
Instance remove_match_on_box_extends  {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (remove_match_on_box_trans (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
  Proof.
  red. intros p p' pr pr' ext. rewrite /transform /= /remove_match_on_box_program.
  eapply remove_match_on_box_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance remove_match_on_box_extends'  {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (remove_match_on_box_trans (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /remove_match_on_box_program. split.
  eapply remove_match_on_box_extends_env => //. apply pr. apply pr'.
  rewrite -eq.
  eapply wellformed_remove_match_on_box_extends; eauto. apply pr. apply pr'.
Qed.

Lemma remove_match_on_box_firstorder {efl : EEnvFlags} (Σ : GlobalContextMap.t)
  v :
  wf_glob Σ -> has_cstr_params = false ->
  firstorder_evalue Σ v ->
  firstorder_evalue (EOptimizePropDiscr.remove_match_on_box_env Σ) v /\
  EOptimizePropDiscr.remove_match_on_box Σ v = v.
Proof.
  intros wf nopars. revert v.
  apply: firstorder_evalue_elim; intros i n args npars nargs hl hargs IH hlen.
  have hnp := EConstructorsAsBlocks.lookup_constructor_pars_args_nopars _ _ _
    _ _ wf nopars hl.
  subst npars. rewrite skipn_0 in hargs IH.
  split.
  - econstructor; tea.
    + move: hl. rewrite /EGlobalEnv.lookup_constructor_pars_args
        -EOptimizePropDiscr.lookup_constructor_remove_match_on_box //.
    + rewrite skipn_0. ELiftSubst.solve_all.
  - rewrite EOptimizePropDiscr.remove_match_on_box_mkApps /=. f_equal.
    ELiftSubst.solve_all.
Qed.

Section RemoveMatchOnBoxETransform.
Local Obligation Tactic := idtac.

(** First-order values are unchanged: the readback is the identity. *)
Program Definition remove_match_on_box_etransform {fl : WcbvFlags}
  {wcon : with_constructor_as_block = false} {efl : EEnvFlags}
  {hastrel : has_tRel} {hastbox : has_tBox}
  (nopars : has_cstr_params = false) :
  ETransform.t extends_map extends_env
    fo_evalue_map fo_evalue is_eta_app_map is_eta_app :=
  {| ETransform.tr := remove_match_on_box_trans (wcon := wcon)
       (hastrel := hastrel) (hastbox := hastbox);
     ETransform.compile_fo p pr fo :=
       (EOptimizePropDiscr.remove_match_on_box_env p.1, p.2);
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply remove_match_on_box_extends.
Qed.
Next Obligation.
  intros. now apply (remove_match_on_box_extends' p p' pr pr').
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars [Σ t] [[wf _] _] [fo hco].
  split; [now apply remove_match_on_box_firstorder|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. cbn. now rewrite -EOptimizePropDiscr.is_coind_remove_match_on_box.
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars [Σ t] pr [fo _].
  pose proof pr as [[wf _] _].
  cbn. unfold EOptimizePropDiscr.remove_match_on_box_program; cbn. f_equal.
  now apply remove_match_on_box_firstorder.
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars [Σ t] pr v v' [fo hco] ->.
  pose proof pr as [[wf _] _].
  cbn in *. unfold fo_evalue; cbn.
  destruct (remove_match_on_box_firstorder Σ v wf nopars fo) as [h1 h2].
  rewrite h2. split => //.
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. cbn. now rewrite -EOptimizePropDiscr.is_coind_remove_match_on_box.
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars [Σ t] pr p' v v' [fo _] ->.
  pose proof pr as [[wf _] _].
  f_equal. cbn in *. now apply remove_match_on_box_firstorder.
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros. reflexivity.
Qed.
Next Obligation.
  now intros fl wcon efl hastrel hastbox nopars [] [] pr pr'; cbn; intros <-.
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars ctx t p => /=.
  rewrite /is_eta_app /is_eta_app_map /=.
  move=> isapp.
  eapply EEtaExpanded.expanded_isEtaExp.
  eapply EOptimizePropDiscr.remove_match_on_box_expanded_irrel. apply p.
  eapply EOptimizePropDiscr.remove_match_on_box_expanded.
  now eapply EEtaExpanded.isEtaExp_expanded.
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars ctx t u pr => /=.
  rewrite /is_eta_app_map /is_eta_app /= => isapp.
  eexists.
  { destruct pr as [[] pr']; move/andP: pr' => [] etactx; split => //.
    split => //. cbn in H0. now move/andP: H0 => [] /andP [].
    apply/andP. split => //. }
  eexists.
  { destruct pr as [[] pr']; move/andP: pr' => [] etactx; split => //.
    split => //. cbn in H0. now move/andP: H0 => [] /andP [].
    apply/andP. split => //. now apply EEtaExpanded.isEtaExp_tApp_arg in b. }
  now rewrite /EOptimizePropDiscr.remove_match_on_box_program /=.
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars [Σ t] pr; cbn.
  clear -t. revert t.
  apply: EInduction.MkAppsInd.rec => //= t u.
  rewrite /isFunction /EAstUtils.isFixApp EAstUtils.head_mkApps
    EOptimizePropDiscr.remove_match_on_box_mkApps !EAstUtils.head_mkApps;
    rtoProp; intuition auto.
  destruct u using rev_case => //.
  rewrite ?map_app !EAstUtils.mkApps_app /= in H2 *.
  rewrite -!orb_assoc in H1.
  forward H1. apply/or3P. move/orP in H2; intuition auto. now constructor 2.
  now constructor 3.
  apply/orP. move/or3P: H1 => []; intuition auto. destruct t => //.
Qed.
Next Obligation.
  intros fl wcon efl hastrel hastbox nopars [Σ t] pr p' v v' ->.
  apply isFunctionS_hom => //.
  intros. apply EOptimizePropDiscr.remove_match_on_box_mkApps.
Qed.
End RemoveMatchOnBoxETransform.
