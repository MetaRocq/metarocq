(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require EAstUtils EInduction ELiftSubst EEtaExpanded
  EConstructorsAsBlocks.
From MetaRocq.Erasure Require Import EProgram EEnvMap EGlobalEnv EWellformed
  EWcbvEval EFirstorder.
Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.Erasure Require Import EInlineProjections.

#[local] Obligation Tactic := idtac.

Program Definition inline_projections_optimization {fl : WcbvFlags}
  {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags}
  (cstrs : cstr_as_blocks = false)
  (no_pars : has_cstr_params = false)
  {has_app : has_tApp}
  {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env fl)
    (eval_eprogram fl) :=
  {| name := "primitive projection inlining";
    transform p _ := EInlineProjections.optimize_program p ;
    pre p := wf_eprogram_env efl p /\
      EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (disable_projections_env_flag efl) p /\
      EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = EInlineProjections.optimize p.1 v |}.

Next Obligation.
  move=> fl wcon efl cstrs no_pars hasapp hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon efl cstrs no_pars hasapp hastrel hastbox [Σ t] /= v
    [wfe wft] [ev].
  eapply EInlineProjections.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  cbn. eapply wfe. Unshelve. auto.
Qed.

#[global]
Instance inline_projections_optimization_extends {fl : WcbvFlags}
  {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags}
  (cstrs : cstr_as_blocks = false)
  (no_pars : has_cstr_params = false)
  {has_app : has_tApp}
  {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t
    (inline_projections_optimization (wcon:=wcon) cstrs no_pars
      (has_app := has_app) (hastrel := hastrel) (hastbox := hastbox))
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /= /optimize_program /=.
  eapply optimize_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance inline_projections_optimization_extends' {fl : WcbvFlags}
  {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags}
  (cstrs : cstr_as_blocks = false)
  (no_pars : has_cstr_params = false)
  {has_app : has_tApp}
  {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t
    (inline_projections_optimization (wcon:=wcon) cstrs no_pars
      (has_app := has_app) (hastrel := hastrel) (hastbox := hastbox))
    extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /optimize_program /=.
  split.
  eapply optimize_extends_env => //. apply pr. apply pr'.
  rewrite -eq.
  eapply wellformed_optimize_extends; eauto. apply pr. apply pr'.
Qed.

Lemma inline_projections_firstorder {efl : EEnvFlags} (Σ : GlobalContextMap.t)
  v :
  wf_glob Σ -> has_cstr_params = false ->
  firstorder_evalue Σ v ->
  firstorder_evalue (EInlineProjections.optimize_env Σ) v /\
  EInlineProjections.optimize Σ v = v.
Proof.
  intros wf nopars. revert v.
  apply: firstorder_evalue_elim; intros i n args npars nargs hl hargs IH hlen.
  have hnp := EConstructorsAsBlocks.lookup_constructor_pars_args_nopars _ _ _
    _ _ wf nopars hl.
  subst npars. rewrite skipn_0 in hargs IH.
  split.
  - econstructor; tea.
    + move: hl. rewrite /EGlobalEnv.lookup_constructor_pars_args
        EInlineProjections.lookup_constructor_optimize //.
    + rewrite skipn_0. ELiftSubst.solve_all.
  - rewrite EInlineProjections.optimize_mkApps /=. f_equal.
    ELiftSubst.solve_all.
Qed.

Section InlineProjectionsETransform.
Local Obligation Tactic := idtac.

(** First-order values have no projections: the readback is the identity. *)
Program Definition inline_projections_etransform {fl : WcbvFlags}
  {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags}
  (cstrs : cstr_as_blocks = false) (no_pars : has_cstr_params = false)
  {has_app : has_tApp} {hastrel : has_tRel} {hastbox : has_tBox} :
  ETransform.t extends_map extends_env
    fo_evalue_map fo_evalue is_eta_app_map is_eta_app :=
  {| ETransform.tr := inline_projections_optimization (wcon := wcon) cstrs
       no_pars (has_app := has_app) (hastrel := hastrel) (hastbox := hastbox);
     ETransform.compile_fo p pr fo :=
       (EInlineProjections.optimize_env p.1, p.2);
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply inline_projections_optimization_extends.
Qed.
Next Obligation.
  intros. now apply (inline_projections_optimization_extends' cstrs no_pars
    p p' pr pr').
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox [Σ t] [[wf _] _]
    [fo hco].
  split; [now apply inline_projections_firstorder|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. cbn. now rewrite -EInlineProjections.is_coind_optimize.
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox [Σ t] pr [fo _].
  pose proof pr as [[wf _] _].
  cbn. unfold EInlineProjections.optimize_program; cbn. f_equal.
  now apply inline_projections_firstorder.
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox [Σ t] pr v v'
    [fo hco] obs.
  change (v' = EInlineProjections.optimize Σ v) in obs. subst v'.
  pose proof pr as [[wf _] _].
  cbn in *. unfold fo_evalue; cbn.
  destruct (inline_projections_firstorder Σ v wf no_pars fo) as [h1 h2].
  rewrite h2. split => //.
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. cbn. now rewrite -EInlineProjections.is_coind_optimize.
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox [Σ t] pr p' v v'
    [fo _] obs.
  change (v' = EInlineProjections.optimize Σ v) in obs. subst v'.
  pose proof pr as [[wf _] _].
  f_equal. cbn in *. now apply inline_projections_firstorder.
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
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox [ctx t] [ctx' t']
    pr pr' eq; move: pr'; cbn in *.
  now subst ctx'.
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox env p pr => /= eta.
  unfold is_eta_app_map, is_eta_app; cbn.
  eapply EEtaExpanded.expanded_isEtaExp.
  eapply EInlineProjections.optimize_expanded_irrel. apply pr.
  eapply EInlineProjections.optimize_expanded.
  now eapply EEtaExpanded.isEtaExp_expanded.
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox ctx pr u pru => /=.
  unfold is_eta_app_map. cbn => etapr.
  destruct pru as [[] ?].
  eexists. split => //. split => //. cbn in *.
  now move/andP: H0 => [] /andP [].
  move/andP: H1 => [] etactx etaapp.
  apply/andP => //.
  eexists. split => //. split => //. cbn in *.
  now move/andP: H0 => [] /andP []. move/andP: H1 => [] etactx etaapp.
  apply/andP => //. split => //.
  now apply EEtaExpanded.isEtaExp_tApp_arg in etaapp.
  reflexivity.
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox [Σ t] pr; cbn.
  clear pr. move: t.
  apply: EInduction.MkAppsInd.rec => //= t u.
  rewrite /isFunction /EAstUtils.isFixApp EAstUtils.head_mkApps
    EInlineProjections.optimize_mkApps !EAstUtils.head_mkApps;
    rtoProp; intuition auto.
  destruct u using rev_case => //.
  rewrite ?map_app !EAstUtils.mkApps_app /= in H2 *.
  rewrite -!orb_assoc in H1.
  forward H1. apply/or3P. move/orP in H2; intuition auto. now constructor 2.
  now constructor 3.
  apply/orP. move/or3P: H1 => []; intuition auto. destruct t => //.
Qed.
Next Obligation.
  intros fl wcon efl cstrs no_pars has_app hastrel hastbox [Σ t] pr p' v v'
    obs.
  change (v' = EInlineProjections.optimize Σ v) in obs. subst v'.
  apply isFunctionS_hom => //.
  intros. apply EInlineProjections.optimize_mkApps.
Qed.
End InlineProjectionsETransform.
