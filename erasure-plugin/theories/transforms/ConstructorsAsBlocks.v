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

#[local] Obligation Tactic := idtac.

From MetaRocq.Erasure Require Import EConstructorsAsBlocks.


Program Definition constructors_as_blocks_transformation {efl : EEnvFlags}
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env target_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming to constuctors as blocks";
    transform p _ := EConstructorsAsBlocks.transform_blocks_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_cstr_as_blocks efl) p ;
    obseq p hp p' v v' := v' = EConstructorsAsBlocks.transform_blocks p.1 v |}.

Next Obligation.
  move=> efl hasapp hasrel hasbox haspars hascstrs [Σ t] [] [wftp wft] /andP [etap etat].
  cbn in *. split.
  - eapply transform_wf_global; eauto.
  - eapply transform_wellformed; eauto.
Qed.
Next Obligation.
  red. move=> efl hasapp hasrel hasbox haspars hascstrs [Σ t] /= v [[wfe1 wfe2] wft] [ev].
  eexists. split; [ | eauto].
  unfold EEtaExpanded.expanded_eprogram_env_cstrs in *.
  revert wft. move => /andP // [e1 e2].
  econstructor.
  cbn -[transform_blocks].
  eapply transform_blocks_eval; cbn; eauto.
Qed.

#[global]
Instance constructors_as_blocks_extends (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  TransformExt.t (constructors_as_blocks_transformation (has_app := has_app) (has_rel := has_rel) (has_box := has_box) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks))
  (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  eapply transform_blocks_env_extends => //. apply pr. apply pr'.
Qed.

#[global]
Instance constructors_as_blocks_extends' (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  TransformExt.t (constructors_as_blocks_transformation (has_app := has_app) (has_rel := has_rel) (has_box := has_box) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks))
  extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. split.
  eapply transform_blocks_env_extends => //. apply pr. apply pr'.
  unfold transform_blocks_program => /=.
  rewrite -eq.
  eapply transform_blocks_extends; eauto. apply pr. apply pr'.
Qed.

Lemma transform_blocks_firstorder {efl : EEnvFlags} (Σ : GlobalContextMap.t)
  v :
  wf_glob Σ -> has_cstr_params = false ->
  firstorder_evalue Σ v ->
  transform_blocks Σ v = compile_evalue_box v [].
Proof.
  intros wf nopars. move: v.
  apply: firstorder_evalue_elim; intros.
  rewrite transform_blocks_decompose.
  rewrite EAstUtils.decompose_app_mkApps // /=.
  rewrite compile_evalue_box_mkApps // ?app_nil_r.
  rewrite H.
  eapply lookup_constructor_pars_args_nopars in H => //. subst npars.
  rewrite chop_all. len. cbn. f_equal. rewrite skipn_0 in H1 H0.
  ELiftSubst.solve_all.
Qed.

(** Reads back constructor blocks as applications of constructors. *)
Fixpoint blocks_readback (t : EAst.term) : option EAst.term :=
  match t with
  | EAst.tConstruct i n args =>
    let fix aux l :=
      match l with
      | [] => Some []
      | a :: l =>
        match blocks_readback a, aux l with
        | Some a, Some l => Some (a :: l)
        | _, _ => None
        end
      end in
    option_map (EAst.mkApps (EAst.tConstruct i n [])) (aux args)
  | _ => None
  end.

Lemma blocks_readback_compile {efl : EEnvFlags} (Σ : GlobalContextMap.t) v :
  wf_glob Σ -> has_cstr_params = false ->
  firstorder_evalue Σ v ->
  blocks_readback (compile_evalue_box v []) = Some v.
Proof.
  intros wf nopars. move: v.
  apply: firstorder_evalue_elim; intros i n args npars nargs hl hargs IH hlen.
  rewrite compile_evalue_box_mkApps app_nil_r /=.
  eapply lookup_constructor_pars_args_nopars in hl => //. subst npars.
  rewrite skipn_0 in IH. clear -IH.
  match goal with
  | |- option_map _ (?aux _) = _ =>
    enough (h : aux (map (flip compile_evalue_box []) args) = Some args)
      by now rewrite h
  end.
  induction IH; cbn => //.
  now rewrite /flip H IHIH.
Qed.

(** [blocks_readback] is injective. *)
Lemma blocks_readback_inj v1 v2 x :
  blocks_readback v1 = Some x -> blocks_readback v2 = Some x -> v1 = v2.
Proof.
  induction v1 using EInduction.term_forall_list_ind in v2, x |- *;
    cbn => //.
  destruct v2 => //=.
  match goal with
  | |- option_map _ (?aux _) = _ -> _ => set (au := aux)
  end.
  destruct (au args) as [l1|] eqn:e1 => //=.
  destruct (au args0) as [l2|] eqn:e2 => //=.
  intros [= <-] [= h].
  eapply EAstUtils.mkApps_eq_inj in h as [[= <- <-] <-] => //.
  f_equal. clear -X e1 e2. subst au.
  induction X in args0, l2, e1, e2 |- *; destruct args0 => //=;
    cbn in e1, e2.
  all: repeat (match goal with
    | h : context [match ?x with Some _ => _ | None => _ end] |- _ =>
      destruct x eqn:? end); try congruence.
  noconf e1. noconf e2. f_equal; [now eapply p|]. eapply IHX; tea.
  reflexivity.
Qed.

Section BlocksETransform.
Local Obligation Tactic := idtac.

(** First-order values become trees of blocks, read back by
    [blocks_readback]. *)
Program Definition constructors_as_blocks_etransform {efl : EEnvFlags}
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox}
  {has_pars : has_cstr_params = false}
  {has_cstrblocks : cstr_as_blocks = false} :
  ETransform.t extends_map extends_env
    fo_evalue_map fo_evalue_block is_eta_app_map (fun _ => True) :=
  {| ETransform.tr := @constructors_as_blocks_transformation efl has_app
       has_rel has_box has_pars has_cstrblocks;
     ETransform.compile_fo p pr fo :=
       (transform_blocks_env p.1, compile_evalue_box p.2 []);
     ETransform.readback := blocks_readback |}.
Next Obligation.
  intros. now apply constructors_as_blocks_extends.
Qed.
Next Obligation.
  intros. now apply (constructors_as_blocks_extends' efl p p' pr pr').
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks [Σ v] pr
    [fo hco].
  cbn. split.
  - eapply firstorder_evalue_block_transform.
    eapply compile_evalue_box_firstorder; tea. apply pr.
  - eapply firstorder_ind_value_is_coind; tea.
    intros kn. apply is_coind_transform_blocks.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks [Σ v] pr
    [fo _].
  pose proof pr as [[wf _] _].
  cbn [transform constructors_as_blocks_transformation].
  unfold transform_blocks_program; cbn [fst snd]; f_equal.
  now apply transform_blocks_firstorder.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks [Σ t] pr v v'
    [fo hco] obs.
  change (v' = transform_blocks Σ v) in obs. subst v'.
  pose proof pr as [[wf _] _].
  rewrite /fo_evalue_block /=.
  rewrite (transform_blocks_firstorder Σ v wf has_pars fo).
  split.
  - eapply firstorder_evalue_block_transform.
    now eapply compile_evalue_box_firstorder.
  - eapply firstorder_ind_value_is_coind; tea.
    intros kn. apply is_coind_transform_blocks.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks [Σ t] pr p' v v'
    [fo _] obs.
  change (v' = transform_blocks Σ v) in obs. subst v'.
  pose proof pr as [[wf _] _].
  rewrite (transform_blocks_firstorder Σ v wf has_pars fo).
  now apply (blocks_readback_compile Σ).
Qed.
Next Obligation.
  intros. now eapply blocks_readback_inj.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks [Σ v] pr [fo _].
  pose proof pr as [[wf _] _].
  cbn. now apply (blocks_readback_compile Σ).
Qed.
Next Obligation.
  intros. reflexivity.
Qed.
Next Obligation.
  now intros efl has_app has_rel has_box has_pars has_cstrblocks [] [] pr pr';
    cbn; intros <-.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  rewrite /is_eta_app_map.
  move=> efl has_app has_rel has_box has_pars has_cstrblocks ctx t u /= [] wf
    /andP[] exp exp' eta.
  eexists.
  { destruct wf. split => //. split => //. cbn in H0.
    now move/andP: H0 => [] /andP[].
    apply/andP. split => //. }
  eexists.
  { destruct wf. split => //. split => //. cbn in H0.
    now move/andP: H0 => [] /andP[].
    apply/andP. split => //. now apply EEtaExpanded.isEtaExp_tApp_arg in exp'. }
  simpl. unfold transform_blocks_program; cbn [fst snd]. f_equal.
  rewrite (transform_blocks_mkApps_eta_fn _ _ [u]) //.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks [Σ t] pr;
    cbn [fst snd transform constructors_as_blocks_transformation].
  destruct pr as [_ h]. move/andP: h => [] _ /=.
  clear -t.
  destruct (EAstUtils.decompose_app t) as [f l] eqn:da.
  pose proof (EAstUtils.decompose_app_notApp _ _ _ da).
  eapply EAstUtils.decompose_app_inv in da. subst t.
  rewrite /isFunction /EAstUtils.isFixApp !EAstUtils.head_mkApps.
  rewrite isLambda_mkApps_eq //=.
  rewrite EEtaExpanded.isEtaExp_mkApps_napp //=.
  destruct EEtaExpanded.construct_viewc => //.
  move/andP => [etat etal].
  rewrite !(transform_blocks_mkApps_eta_fn _ _ l) // !EAstUtils.head_mkApps /=.
  rewrite isLambda_mkApps_eq.
  destruct t0 => //=. rewrite !orb_false_r. move/Nat.eqb_eq.
  destruct l => //=. all:now rewrite !orb_false_r !orb_true_r.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks [Σ t] pr p' v v'
    obs.
  change (v' = transform_blocks Σ v) in obs. subst v'.
  apply isFunctionS_hom.
  - intros hd args napp h.
    rewrite EConstructorsAsBlocks.transform_blocks_mkApps //. now destruct hd.
  - intros. now simp transform_blocks.
  - intros. now simp transform_blocks.
  - intros. now simp transform_blocks.
Qed.
End BlocksETransform.
