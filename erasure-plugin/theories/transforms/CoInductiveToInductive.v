(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EAstUtils ECoInductiveToInductive.
From MetaRocq.Erasure Require Import EProgram EEnvMap EGlobalEnv EWellformed
  EWcbvEval EFirstorder.
Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.Erasure Require Import EConstructorsAsBlocks.

#[local] Obligation Tactic := idtac.

(** The flags after the translation of cofixpoints: no [tCoFix] left. *)
Definition efl_coind_to_ind (efl : EEnvFlags) :=
  switch_off_cofix efl.

(** Coinductive values are observed up to the relation
    [ECoInductiveToInductive.crel]: a cofixpoint or an evaluated coinductive
    constructor is related to the thunk computed by the translation.
    First-order values of inductive types are related to themselves only
    ([ECoInductiveToInductive.crel_firstorder_ind_value]). *)
Program Definition coinductive_to_inductive_transformation (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_pars : has_cstr_params = false}
  {has_cstrblocks : cstr_as_blocks = true}
  {has_lazy : has_tLazy_Force} {has_fix : has_tFix} :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram_env block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming co-inductive to lazy inductive types";
    transform p _ := trans_program p ;
    pre p := wf_eprogram_env efl p ;
    post p := wf_eprogram (efl_coind_to_ind efl) p ;
    obseq p hp p' v v' :=
      ∥ crel (wfl := block_wcbv_flags)
        (GlobalContextMap.global_decls p.1) p'.1 v v' ∥ /\
      ∥ value (wfl := block_wcbv_flags) p'.1 v' ∥ /\
      wellformed (efl := efl_coind_to_ind efl) p'.1 0 v' |}.

Next Obligation.
  move=> efl hasapp hasrel haspars hascstrs haslazy hasfix [Σ t] [wftp wft].
  cbn in *. eapply trans_program_wf; eauto.
  split => //.
Qed.
Next Obligation.
  red. move=> efl hasapp hasrel haspars hascstrs haslazy hasfix [Σ t] /= v
    [wfe1 wfe2] [ev].
  destruct (trans_correct (wfl := block_wcbv_flags)
    Σ eq_refl hascstrs eq_refl eq_refl hasapp wfe1 t v wfe2 ev)
    as [v' [ev' hv]].
  exists v'. split; [now constructor|].
  split; [now constructor|]. split; [constructor; now eapply eval_to_value|].
  have wf' := trans_program_wf (efl := efl)
    (haslf := haslazy) (hasfix := hasfix) (Σ, t) (conj wfe1 wfe2).
  destruct wf' as [wfg wft].
  eapply (eval_wellformed (efl := efl_coind_to_ind efl)); tea.
Qed.

#[global]
Instance coinductive_to_inductive_transformation_ext (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_pars : has_cstr_params = false}
  {has_cstrblocks : cstr_as_blocks = true}
  {has_lazy : has_tLazy_Force} {has_fix : has_tFix} :
  TransformExt.t (coinductive_to_inductive_transformation efl
    (has_app := has_app) (has_rel := has_rel)
    (has_pars := has_pars) (has_cstrblocks := has_cstrblocks)
    (has_lazy := has_lazy) (has_fix := has_fix))
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  eapply trans_env_extends => //.
  apply pr. apply pr'.
Qed.

#[global]
Instance coinductive_to_inductive_transformation_ext' (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox}
  {has_pars : has_cstr_params = false}
  {has_cstrblocks : cstr_as_blocks = true}
  {has_lazy : has_tLazy_Force} {has_fix : has_tFix} :
  TransformExt.t (coinductive_to_inductive_transformation efl
    (has_app := has_app) (has_rel := has_rel)
    (has_pars := has_pars) (has_cstrblocks := has_cstrblocks)
    (has_lazy := has_lazy) (has_fix := has_fix))
    extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. split.
  - eapply trans_env_extends => //.
    apply pr. apply pr'.
  - unfold trans_program => /=. rewrite -eq.
    eapply wellformed_trans_extends; eauto.
    apply pr. apply pr'.
Qed.

Lemma trans_firstorder_ind_value (Σ : GlobalContextMap.t) v :
  firstorder_ind_value Σ v ->
  trans Σ v = v.
Proof.
  revert v. apply: firstorder_ind_value_rect.
  intros ind c args hco hargs IH. cbn.
  rewrite GlobalContextMap.is_coind_spec hco. f_equal.
  clear -IH. induction IH; cbn; f_equal; auto.
Qed.

Lemma firstorder_evalue_block_trans_env {efl : EEnvFlags}
  (Σ : GlobalContextMap.t) v :
  wf_glob Σ ->
  firstorder_evalue_block Σ v ->
  firstorder_evalue_block (trans_env Σ) v.
Proof.
  intros wf. revert v. apply: firstorder_evalue_block_elim.
  intros i n args hl hargs IH. constructor => //.
  move: hl. rewrite /lookup_constructor_pars_args.
  rewrite lookup_constructor_trans //.
  destruct lookup_constructor as [[[] ?]|] => //.
Qed.

Lemma firstorder_ind_value_impl Σ Σ' v :
  (forall kn, is_coind Σ kn = false -> is_coind Σ' kn = false) ->
  ∥ firstorder_ind_value Σ v ∥ ->
  ∥ firstorder_ind_value Σ' v ∥.
Proof.
  intros hco [h]. sq. revert v h.
  apply: firstorder_ind_value_rect.
  intros ind c args hc hargs IH. constructor => //. now apply hco.
Qed.

Lemma value_app_isFunction {wfl : WcbvFlags} Σ f a :
  with_constructor_as_block = true ->
  value Σ (EAst.tApp f a) -> isFunction (EAst.tApp f a).
Proof.
  intros hblock.
  rewrite -(mkApps_head_spine (EAst.tApp f a)).
  have napp := decompose_app_notApp _ _ _
    (decompose_app_head_spine (EAst.tApp f a)).
  have hsp : spine (EAst.tApp f a) <> [].
  { rewrite spine_tApp. now destruct spine. }
  move: napp hsp.
  generalize (head (EAst.tApp f a)) (spine (EAst.tApp f a)) => hd l napp hl.
  intros hv. eapply value_mkApps_inv in hv as [[[] |[]]|[_ vh _]] => //.
  depelim vh => //.
  all: try congruence.
  all: rewrite /isFunction /isFixApp head_mkApps /=; now rewrite ?orb_true_r.
Qed.

(** Without cofixpoints, a term is never an unsaturated cofixpoint. *)
Lemma wellformed_cofix_unsaturated {efl : EEnvFlags} Σ k t :
  has_tApp -> has_tCoFix = false -> wellformed Σ k t -> cofix_unsaturated t.
Proof.
  intros hasapp nocofix.
  rewrite /cofix_unsaturated.
  destruct (decompose_app t) as [f l] eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  eapply decompose_app_inv in da. subst t.
  rewrite wellformed_mkApps //. move/andP => [wff _].
  destruct f => //. cbn in wff. now rewrite nocofix in wff.
Qed.

Lemma crel_value_isFunction Σ Σ' w x :
  crel (wfl := block_wcbv_flags) Σ Σ' w x ->
  value (wfl := block_wcbv_flags) Σ' x ->
  isFunctionS w -> isFunction x.
Proof.
  intros h hv. depelim h => //.
  - intros _. now apply (value_app_isFunction (wfl := block_wcbv_flags) Σ').
  - destruct c as [mfix mfix0 idx d0 args args' -> -> hall hnth hne hle
      _ _ _ _ hargs].
    rewrite /isFunctionS /cofix_unsaturated decompose_app_mkApps //=.
    move/andP => [_].
    destruct (nth_error mfix idx) as [d|] eqn:hnth' => //.
    move/Nat.ltb_lt => hlt.
    eapply All2_nth_error in hall; tea. destruct hall as [hna hr hlam hb].
    rewrite /cofix_app_target.
    have hl := All2_length hargs.
    have := isLambdas_beta_apps (EAst.rarg d0) _ args'
      (isLambdas_substl _ (fix_subst (List.map wrap_def mfix0)) _ hlam)
      ltac:(lia).
    rewrite -hl.
    destruct (EAst.rarg d0 - #|args|) eqn:hd; [lia|].
    cbn. destruct beta_apps => //=.
Qed.

Lemma isFunction_trans Σ t :
  isFunction t -> isFunction (trans Σ t).
Proof.
  have napp := decompose_app_notApp _ _ _ (decompose_app_head_spine t).
  rewrite -(mkApps_head_spine t). move: napp.
  generalize (head t) (spine t) => f l napp.
  rewrite trans_mkApps.
  rewrite /isFunction /isFixApp !head_mkApps.
  rewrite !isLambda_mkApps_eq.
  destruct f => //=; rewrite ?length_map //.
  all:match goal with |- context [if ?b then _ else _] => destruct b end => //.
Qed.

Section CoindETransform.
Local Obligation Tactic := idtac.

(** First-order values of inductive types are related to themselves only:
    the readback is the identity. *)
Program Definition coinductive_to_inductive_etransform (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox}
  {has_pars : has_cstr_params = false}
  {has_cstrblocks : cstr_as_blocks = true}
  {has_lazy : has_tLazy_Force} {has_fix : has_tFix} :
  ETransform.t extends_map extends_env (on_map fo_evalue_block)
    fo_evalue_block (on_map (fun _ => True)) (fun _ => True) :=
  {| ETransform.tr := coinductive_to_inductive_transformation efl
       (has_app := has_app) (has_rel := has_rel) (has_pars := has_pars)
       (has_cstrblocks := has_cstrblocks) (has_lazy := has_lazy)
       (has_fix := has_fix);
     ETransform.compile_fo p pr fo := trans_program p;
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply coinductive_to_inductive_transformation_ext.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    p p' pr pr' ext eq.
  now apply (coinductive_to_inductive_transformation_ext' efl
    (has_box := has_box) p p' pr pr').
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    [Σ t] [wf _] [fo [hco]].
  cbn in fo, hco. rewrite /fo_evalue_block /=.
  rewrite trans_firstorder_ind_value //.
  split; [now apply firstorder_evalue_block_trans_env|].
  eapply firstorder_ind_value_impl; [|exact (sq hco)].
  intros kn _. now apply is_coind_trans_env.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    [Σ t] pr v v' [fo [hco]] [[obs] _].
  cbn in fo, hco, obs |- *.
  pose proof pr as [wf _].
  apply crel_firstorder_ind_value in obs => //.
  subst v'.
  rewrite /fo_evalue_block /=.
  split; [now apply firstorder_evalue_block_trans_env|].
  eapply firstorder_ind_value_impl; [|exact (sq hco)].
  intros kn _. now apply is_coind_trans_env.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    [Σ t] pr p' v v' [fo [hco]] [[obs] _].
  cbn in fo, hco, obs |- *.
  apply crel_firstorder_ind_value in obs => //.
  now subst v'.
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    [Σ t] pr [fo [hco]].
  cbn. f_equal. now apply trans_firstorder_ind_value.
Qed.
Next Obligation.
  intros. reflexivity.
Qed.
Next Obligation.
  now intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy
    has_fix [] [] pr pr'; cbn; intros <-.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    Σ t u pr _.
  unshelve eexists.
  { destruct pr as [? ?]; split; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  unshelve eexists.
  { destruct pr as [? ?]; split; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  cbn. reflexivity.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    [Σ t] pr; cbn. now apply isFunction_trans.
Qed.
Next Obligation.
  intros efl has_app has_rel has_box has_pars has_cstrblocks has_lazy has_fix
    [Σ t] pr p' v v' [[obs] [[hv] hwf]] hf.
  rewrite /isFunctionS. apply/andP. split.
  - eapply crel_value_isFunction; tea.
  - eapply (wellformed_cofix_unsaturated (efl := efl_coind_to_ind efl)); tea.
    reflexivity.
Qed.
End CoindETransform.
