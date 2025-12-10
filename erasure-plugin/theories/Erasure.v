(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Template Require Import EtaExpand TemplateProgram.
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaRocq.Erasure Require Import EProgram EInlining EBeta.
From MetaRocq.ErasurePlugin Require Import ETransform.

Import PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Common.Transform.Transform.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

Import EWcbvEval.

Local Obligation Tactic := program_simpl.

Record unsafe_passes :=
  { cofix_to_lazy : bool;
    inlining : bool;
    unboxing : bool;
    betared : bool }.

Record erasure_configuration := {
  enable_unsafe : unsafe_passes;
  enable_typed_erasure : bool;
  dearging_config : dearging_config;
  inlined_constants : KernameSet.t
  }.

Definition default_dearging_config :=
  {| overridden_masks := fun _ => None;
      do_trim_const_masks := true;
      do_trim_ctor_masks := false |}.


Definition make_unsafe_passes b :=
  {| cofix_to_lazy := b;
     inlining := b;
     unboxing := b;
     betared := b |}.

Definition no_unsafe_passes := make_unsafe_passes false.
Definition all_unsafe_passes := make_unsafe_passes true.

(* This runs the cofix -> fix/lazy translation as well as inlining and
  beta-redex simplification,  which are not verified. It does not do unboxing. *)

Definition default_unsafe_passes :=
  {| cofix_to_lazy := true;
      inlining := true;
      unboxing := false;
      betared := true |}.

Definition default_erasure_config :=
  {| enable_unsafe := default_unsafe_passes;
     dearging_config := default_dearging_config;
     enable_typed_erasure := true;
     inlined_constants := KernameSet.empty |}.

(* This runs only the verified phases without the typed erasure and "fast" remove params *)
Definition safe_erasure_config :=
  {| enable_unsafe := no_unsafe_passes;
     enable_typed_erasure := false;
     dearging_config := default_dearging_config;
     inlined_constants := KernameSet.empty |}.

Axiom assume_welltyped_template_program_expansion :
  forall p (wtp : ∥ wt_template_program_env p ∥),
  let p' := EtaExpand.eta_expand_program p in
  ∥ wt_template_program p' ∥ /\ EtaExpand.expanded_program p'.

Axiom assume_preservation_template_program_env_expansion :
  forall p (wtp : ∥ wt_template_program_env p ∥) v,
  eval_template_program_env p v ->
  ∥ eval_template_program (EtaExpand.eta_expand_program p) (EtaExpand.eta_expand p.1 [] v) ∥.

(** We kludge the normalization assumptions by parameterizing over a continuation of "what will be done to the program later" as well as what properties we'll need of it *)

Program Definition eta_expand K : Transform.t _ _ Ast.term Ast.term _ _
  eval_template_program_env eval_template_program :=
  {| name := "eta expand cstrs and fixpoints";
     pre := fun p => ∥ wt_template_program_env p ∥ /\ K (eta_expand_global_env p.1) ;
     transform p _ := EtaExpand.eta_expand_program p ;
     post := fun p => ∥ wt_template_program p ∥ /\ EtaExpand.expanded_program p /\ K p.1;
     obseq p hp p' v v' := v' = EtaExpand.eta_expand p.1 [] v |}.
Next Obligation.
  let p := match goal with H : program _ _ |- _ => H end in
  destruct p. split; [|split]; auto; now apply assume_welltyped_template_program_expansion.
Qed.
Next Obligation.
  red. intros p v [wt] ev.
  apply assume_preservation_template_program_env_expansion in ev as [ev']; eauto.
Qed.

Definition final_wcbv_flags := {|
  with_prop_case := false;
  with_guarded_fix := false;
  with_constructor_as_block := true |}.

Program Definition optional_unsafe_transforms econf :=
  let passes := econf.(enable_unsafe) in
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  ETransform.optional_self_transform passes.(cofix_to_lazy)
    ((* Rebuild the efficient lookup table *)
    rebuild_wf_env_transform (efl := efl) false false ▷
    (* Coinductives & cofixpoints are translated to inductive types and thunked fixpoints *)
    coinductive_to_inductive_transformation efl
      (has_app := eq_refl) (has_box := eq_refl) (has_rel := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl)) ▷
  ETransform.optional_self_transform passes.(unboxing)
    (rebuild_wf_env_transform (efl := efl) false false ▷
      unbox_transformation efl final_wcbv_flags) ▷
  ETransform.optional_self_transform passes.(inlining)
      (inline_transformation efl final_wcbv_flags econf.(inlined_constants) ▷
       forget_inlining_info_transformation efl final_wcbv_flags) ▷
  (* Heuristically do it twice for more beta-normal terms *)
  ETransform.optional_self_transform passes.(betared)
    (betared_transformation efl final_wcbv_flags ▷
     betared_transformation efl final_wcbv_flags).

Next Obligation.
  destruct (enable_unsafe econf) as [[] [] [] []]; cbn in * => //; intuition auto.
Qed.
Next Obligation.
  destruct (enable_unsafe econf) as [[] [] [] []]; cbn in * => //; intuition auto.
Qed.
Next Obligation.
  destruct (enable_unsafe econf) as [[] [] [] []]; cbn in * => //; intuition auto.
Qed.

Program Definition verified_lambdabox_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags)
  : Transform.t _ _ _ EAst.term _ _
   (* Standard evaluation, with cases on prop, guarded fixpoints, applied constructors *)
   (eval_eprogram_env default_wcbv_flags)
   (* Target evaluation, with no more cases on prop, unguarded fixpoints, constructors as block *)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  (* Simulation of the guarded fixpoint rules with a single unguarded one:
    the only "stuck" fixpoints remaining are unapplied.
    This translation is a noop on terms and environments.  *)
  guarded_to_unguarded_fix (fl := default_wcbv_flags) (wcon := eq_refl) eq_refl ▷
  (* Remove all constructor parameters *)
  remove_params_optimization (wcon := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
  (* Remove all cases / projections on propositional content *)
  remove_match_on_box_trans (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
  (* Inline projections to cases *)
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) true false ▷
  (* First-order constructor representation *)
  constructors_as_blocks_transformation
    (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags))
    (has_app := eq_refl) (has_pars := eq_refl) (has_rel := eq_refl) (has_box := eq_refl) (has_cstrblocks := eq_refl).

(* At the end of erasure we get a well-formed program (well-scoped globally and localy), without
   parameters in inductive declarations. The constructor applications are also transformed to a first-order
   "block"  application, of the right length, and the evaluation relation does not need to consider guarded
   fixpoints or case analyses on propositional content. All fixpoint bodies start with a lambda as well.
   Finally, projections are inlined to cases, so no `tProj` remains. *)

Import EGlobalEnv EWellformed.

Next Obligation.
  destruct H. split => //. sq.
  now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs.
Qed.

Program Definition verified_lambdabox_pipeline_mapping {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags)
  : Transform.t _ _ _ EAst.term _ _
   (* Standard evaluation, with cases on prop, guarded fixpoints, applied constructors *)
   (eval_eprogram_env_mapping default_wcbv_flags)
   (* Target evaluation, with no more cases on prop, unguarded fixpoints, constructors as block *)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  (* Reorder constructors according to the mapping *)
  reorder_cstrs_transformation (wca := eq_refl) (has_app := eq_refl) default_wcbv_flags (wcon := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := efl) true true ▷
  (* Extract as usual *)
  verified_lambdabox_pipeline.

(* At the end of erasure we get a well-formed program (well-scoped globally and localy), without
   parameters in inductive declarations. The constructor applications are also transformed to a first-order
   "block"  application, of the right length, and the evaluation relation does not need to consider guarded
   fixpoints or case analyses on propositional content. All fixpoint bodies start with a lambda as well.
   Finally, projections are inlined to cases, so no `tProj` remains. *)

Import EGlobalEnv EWellformed.

Definition eval_pcuic_program_mapping (p : inductives_mapping * pcuic_program) t :=
  PCUICTransform.eval_pcuic_program p.2 t.

Import EReorderCstrs (wf_tags_list).

Definition wf_pcuic_inductive_mapping (Σ : PCUICAst.PCUICEnvironment.global_env) (m : inductive_mapping) : bool :=
  let '(ind, (_, cstrs)) := m in
  match PCUICAst.PCUICLookup.lookup_inductive Σ ind with
  | Some (mib, oib) => wf_tags_list cstrs #|oib.(PCUICAst.PCUICEnvironment.ind_ctors)|
  | None => true
  end.

Definition wf_pcuic_inductives_mapping Σ m := forallb (wf_pcuic_inductive_mapping Σ) m.

Import ErasureFunction ErasureFunctionProperties.

Import PCUICAst.PCUICEnvironment Extract EReorderCstrs EDeps EGlobalEnv.

Lemma lookup_env_filter Σ f kn :
  fresh_global kn Σ ->
  lookup_env (filter f Σ) kn = None.
Proof.
  induction 1; cbn => //.
  destruct f. cbn. case: eqb_spec. intros ->. contradiction.
  eauto. eauto.
Qed.

Lemma lookup_env_filter_deps {efl : EEnvFlags} {Σ f i p} :
  wf_glob Σ ->
  lookup_env Σ i = Some p ->
  lookup_env (filter f Σ) i = Some p \/
  lookup_env (filter f Σ) i = None.
Proof.
  move=> wfΣ.
  induction Σ in wfΣ |- *; cbn => //.
  case: eqb_spec.
  - intros -> [= <-]. destruct f. left. cbn. now rewrite eqb_refl.
    right. depelim wfΣ. cbn. now apply lookup_env_filter.
  - intros diff hl.
    destruct f. cbn. case: eqb_spec.
    intros ->. contradiction. intros _. depelim wfΣ.
    now specialize (IHΣ wfΣ hl).
    depelim wfΣ.
    now specialize (IHΣ wfΣ hl).
Qed.

Lemma lookup_env_filter_deps_None {efl : EEnvFlags} {Σ f i} :
  wf_glob Σ ->
  lookup_env Σ i = None ->
  lookup_env (filter f Σ) i = None.
Proof.
  move=> wfΣ.
  induction Σ in wfΣ |- *; cbn => //.
  case: eqb_spec.
  - intros -> [= <-].
  - intros diff hl.
    destruct f. cbn. case: eqb_spec.
    intros ->. contradiction. intros _. depelim wfΣ.
    now specialize (IHΣ wfΣ hl).
    depelim wfΣ.
    now specialize (IHΣ wfΣ hl).
Qed.

Lemma lookup_inductive_filter_deps_Some {efl : EEnvFlags} {Σ f i p} :
  wf_glob Σ ->
  lookup_inductive Σ i = Some p ->
  lookup_inductive (filter f Σ) i = Some p \/
  lookup_inductive (filter f Σ) i = None.
Proof.
  move => wfΣ.
  rewrite /lookup_inductive /lookup_minductive.
  destruct lookup_env eqn:hle => //=.
  eapply lookup_env_filter_deps in hle as [-> | ->] => //; destruct g => //=. now left.
  now right.
Qed.

Lemma lookup_inductive_filter_deps_None {efl : EEnvFlags} {Σ f i} :
  wf_glob Σ ->
  lookup_inductive Σ i = None ->
  lookup_inductive (filter f Σ) i = None.
Proof.
  move => wfΣ.
  rewrite /lookup_inductive /lookup_minductive.
  destruct lookup_env eqn:hle => //=; try destruct g => //=.
  eapply (lookup_env_filter_deps) in hle as [-> | ->] => //; destruct g => //=.
  eapply (lookup_env_filter_deps) in hle as [-> | ->] => //; destruct g => //=.
  eapply (lookup_env_filter_deps_None) in hle as -> => //; destruct g => //=.
Qed.

Lemma erases_global_lookup_env_constant Σ Σ' kn :
  erases_global Σ Σ' ->
  forall d, PCUICAst.PCUICEnvironment.lookup_env Σ kn = Some (ConstantDecl d) ->
  exists d', lookup_env Σ' kn = Some (EAst.ConstantDecl d').
Proof.
  destruct Σ as [? ? ?]. rewrite /erases_global //=.
  induction 1; cbn => //.
  - intros d. case: eqb_spec.
    + intros ->. intros [=]; subst. now eexists.
    + intros diff. cbn in *. eauto.
  - intros d. case: eqb_spec.
    + intros ->. intros [=]; subst.
    + intros diff. cbn in *. eauto.
Qed.

Lemma erases_global_lookup_env_inductive Σ Σ' kn :
  erases_global Σ Σ' ->
  forall d, PCUICAst.PCUICEnvironment.lookup_env Σ kn = Some (InductiveDecl d) ->
  exists d', lookup_env Σ' kn = Some (EAst.InductiveDecl d') /\ erases_mutual_inductive_body d d'.
Proof.
  destruct Σ as [? ? ?]. rewrite /erases_global //=.
  induction 1; cbn => //.
  - intros d. case: eqb_spec.
    + intros ->. intros [=]; subst.
    + intros diff. cbn in *. eauto.
  - intros d. case: eqb_spec.
    + intros ->. intros [=]; subst. now eexists.
    + intros diff. cbn in *. eauto.
Qed.

Lemma erases_global_lookup_env_none Σ Σ' kn :
  erases_global Σ Σ' ->
  PCUICAst.PCUICEnvironment.lookup_env Σ kn = None ->
  lookup_env Σ' kn = None.
Proof.
  destruct Σ as [? ? ?]. rewrite /erases_global //=.
  induction 1; cbn => //.
  - case: eqb_spec.
    + intros ->. intros [=]; subst.
    + intros diff. cbn in *. eauto.
  - case: eqb_spec.
    + intros ->. intros [=]; subst.
    + intros diff. cbn in *. eauto.
Qed.

Lemma erases_wf_inductives_mapping {Σ : global_env_ext} {Σ' deps m} :
  PCUICTyping.wf_ext Σ ->
  erases_global Σ Σ' ->
  wf_pcuic_inductives_mapping Σ m ->
  EReorderCstrs.wf_inductives_mapping (filter_deps deps Σ') m.
Proof.
  move=> wfΣ  er.
  have wfΣ' := ErasureCorrectness.erases_global_wf_glob _ (fst wfΣ) er.
  rewrite /wf_pcuic_inductives_mapping /wf_inductives_mapping.
  solve_all. move: H.
  rewrite /wf_pcuic_inductive_mapping /wf_inductive_mapping.
  destruct x as [ind [na tags]].
  have eral := EDeps.erases_global_all_deps _ _ (PCUICElimination.wf_ext_wf _ wfΣ) er.
  have trind := ErasureProperties.trans_lookup_inductive eral ind.
  destruct PCUICAst.PCUICLookup.lookup_inductive as [[mib oib]|] eqn:li.
  specialize (trind _ _ eq_refl).
  - intros wftags.
    destruct trind as [mib' [oib' [hli' hctors]]].
    rewrite (filter_deps_filter (efl := all_env_flags)) //.
    set (f := fun x => _).
    eapply (lookup_inductive_filter_deps_Some (efl := all_env_flags) (f:=f)) in hli' as [H|H] => //; rewrite H //.
    congruence.
  - intros _. clear trind.
    destruct (lookup_inductive (filter_deps deps Σ') ind) eqn:li' => //.
    apply False_rect. move: li'.
    rewrite (filter_deps_filter (efl:=all_env_flags)) //.
    generalize (fun x : KernameSet.elt × EAst.global_decl => flip KernameSet.mem (global_deps Σ' deps) x.1).
    intros f li'.
    have nli : lookup_inductive Σ' ind = None.
    { clear -wfΣ wfΣ' er li.
      move: li. rewrite /PCUICAst.PCUICLookup.lookup_inductive /lookup_inductive.
      rewrite /PCUICAst.PCUICLookup.lookup_inductive_gen /lookup_minductive.
      rewrite /PCUICAst.PCUICLookup.lookup_minductive_gen /lookup_minductive.
      destruct PCUICAst.PCUICEnvironment.lookup_env eqn:hle => //=. destruct g => //.
      eapply erases_global_lookup_env_constant in hle as [? ->]; tea => //.
      eapply erases_global_lookup_env_inductive in hle as [? [-> ?]]; tea => //=.
      depelim H.
      destruct nth_error eqn:hnth => // _.
      destruct (nth_error (EAst.ind_bodies _) _) eqn:hnth' => //=.
      eapply nth_error_Some_length in hnth'. eapply nth_error_None in hnth. eapply Forall2_length in H. lia.
      intros _.
      eapply erases_global_lookup_env_none in hle as ->; tea => //. }
    now rewrite (lookup_inductive_filter_deps_None wfΣ' nli) in li'.
Qed.


Program Definition erase_transform_mapping {guard : abstract_guard_impl} : Transform.t _ _ _ _ PCUICAst.term EAst.term
  eval_pcuic_program_mapping (eval_eprogram_env_mapping EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p := wf_pcuic_inductives_mapping p.2.1 p.1 /\ pre erase_transform p.2 ;
    transform p hp := let nhs := proj2 hp in
      (p.1, transform erase_transform p.2 nhs) ;
   post p := EReorderCstrs.wf_inductives_mapping p.2.1.(EEnvMap.GlobalContextMap.global_decls) p.1 /\ post erase_transform p.2;
   obseq p hp p' := obseq erase_transform p.2 (proj2 hp) p'.2 |}.

Local Obligation Tactic := idtac.
Next Obligation.
  cbn -[erase_transform]. intros.
  split. 2:eapply (correctness erase_transform).
  destruct input as [m prog]; cbn [fst snd] in *.
  destruct p.
  unfold erase_transform; cbn [transform].
  unfold erase_program, erase_pcuic_program;
  set (egf := erase_global_fast _ _ _ _ _);
  set (ef := ErasureFunction.erase _ _ _ _ _);
  cbn -[egf ef]; unfold erase_global_fast in egf; rewrite /egf; clear egf ef;
  set (deps := EAstUtils.term_global_deps _); clearbody deps;
  match goal with
  |- context [erase_global_deps_fast ?deps ?X_type ?X ?decls (normalization_in:=?normalization_in) ?hprefix ] =>
    have heq := @erase_global_deps_fast_erase_global_deps deps X_type X decls normalization_in hprefix
  end; cbn in heq; specialize (heq (fun Σ eq => f_equal declarations eq));
  destruct heq as [nin' eq]; rewrite eq; clear eq.
  rewrite erase_global_deps_erase_global.
  cbn -[ErasureFunction.erase_global].
  match goal with
  |- context [@erase_global ?X_type ?X ?decls ?SN ?eq] =>
  have erg := @erases_global_erase_global X_type X _ _ SN eq
  end.
  cbn in erg. specialize (erg _ eq_refl).
  cbn in p. destruct p as [[wt] ?].
  set (eg := erase_global _ _ _) in erg |- *. clearbody eg.
  have := erases_wf_inductives_mapping (Σ' := eg) (fst wt) erg i.
  intros h. eauto.
Qed.

Next Obligation.
  intros g p v pr ev. cbn.
  now apply (preservation erase_transform).
Qed.

Program Definition pcuic_expand_lets_transform_mapping {cf : checker_flags} K : Transform.t _ _ _ _ PCUICAst.term PCUICAst.term
  eval_pcuic_program_mapping eval_pcuic_program_mapping :=
 {| name := "let expansion in constructors";
    pre p := wf_pcuic_inductives_mapping p.2.1 p.1 /\ pre (pcuic_expand_lets_transform K) p.2 ;
    transform p hp := let nhs := proj2 hp in
      (p.1, transform (pcuic_expand_lets_transform K) p.2 nhs) ;
   post p := wf_pcuic_inductives_mapping p.2.1 p.1 /\ post (pcuic_expand_lets_transform K) p.2;
   obseq p hp p' := obseq (pcuic_expand_lets_transform K) p.2 (proj2 hp) p'.2 |}.
Next Obligation.
  cbn. intros cf K input []. split => //.
  - move: H; rewrite /wf_pcuic_inductives_mapping.
    solve_all. move: H; rewrite /wf_pcuic_inductive_mapping.
    destruct x as [ind [na tags]].
    rewrite /PCUICAst.PCUICLookup.lookup_inductive /PCUICAst.PCUICLookup.lookup_inductive_gen /PCUICAst.PCUICLookup.lookup_minductive_gen.
    rewrite PCUICExpandLetsCorrectness.trans_lookup. destruct PCUICAst.PCUICEnvironment.lookup_env => //. destruct g => //=.
    rewrite nth_error_mapi. destruct nth_error => //=. now len.
  - unshelve eapply (correctness (pcuic_expand_lets_transform K)). apply H0.
Qed.
Next Obligation.
  intros cf K p v pr ev. now eapply (preservation (pcuic_expand_lets_transform K)).
Qed.

Program Definition verified_erasure_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t _ _ _ EAst.term _ _
  PCUICTransform.eval_pcuic_program
  (EProgram.eval_eprogram final_wcbv_flags) :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
  pcuic_expand_lets_transform (K _ T1) ▷
  (* Erasure of proofs terms in Prop and types *)
  erase_transform ▷
  verified_lambdabox_pipeline.
Next Obligation.
  intros guard efl K T1 p.
  cbn. intuition eauto. now eapply H2. now eapply H2.
Qed.
Next Obligation.
  intros guard efl K T1 p. cbn. intuition auto.
Qed.

Program Definition verified_erasure_pipeline_mapping {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t _ _ _ EAst.term _ _
  eval_pcuic_program_mapping
  (EProgram.eval_eprogram final_wcbv_flags) :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
  pcuic_expand_lets_transform_mapping (K _ T1) ▷
  (* Erasure of proofs terms in Prop and types *)
  erase_transform_mapping ▷
  verified_lambdabox_pipeline_mapping.
Next Obligation.
  intros guard efl K T1 p.
  cbn. intuition eauto. now eapply H3. now eapply H3.
Qed.
Next Obligation.
  intros guard efl K T1 p. cbn. intuition auto.
  split; eauto.
Qed.

Import EGlobalEnv EWellformed.

Definition transform_compose
  {env env' env'' term term' term'' value value' value'' : Type}
  {eval eval' eval''}
  (o : t env env' term term' value value' eval eval')
  (o' : t env' env'' term' term'' value' value'' eval' eval'')
  (pre : forall p, post o p -> pre o' p) :
  forall x p1, exists p3,
    transform (compose o o' pre) x p1 = transform o' (transform o x p1) p3.
Proof.
  cbn. intros.
  unfold run, time.
  eexists;reflexivity.
Qed.

Instance verified_lambdabox_pipeline_extends {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
  TransformExt.t verified_lambdabox_pipeline
    (fun p p' =>
      extends (EEnvMap.GlobalContextMap.global_decls p.1) (EEnvMap.GlobalContextMap.global_decls p'.1)) (fun p p' => extends p.1 p'.1).
Proof.
  unfold verified_lambdabox_pipeline. tc.
Qed.

Instance verified_lambdabox_pipeline_mapping_extends {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
  TransformExt.t verified_lambdabox_pipeline_mapping
    (fun p p' =>
      p.1 = p'.1 /\
      extends (EEnvMap.GlobalContextMap.global_decls p.2.1) (EEnvMap.GlobalContextMap.global_decls p'.2.1)) (fun p p' => extends p.1 p'.1).
Proof.
  unfold verified_lambdabox_pipeline_mapping. tc.
Qed.

Lemma verified_lambdabox_pipeline_extends' {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
  TransformExt.t verified_lambdabox_pipeline extends_eprogram_env extends_eprogram.
Proof.
  unfold verified_lambdabox_pipeline. tc.
Qed.

Lemma verified_lambdabox_pipeline_mapping_extends' {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
  TransformExt.t verified_lambdabox_pipeline_mapping (fun p p' => p.1 = p'.1 /\ extends_eprogram_env p.2 p'.2) extends_eprogram.
Proof.
  unfold verified_lambdabox_pipeline_mapping. tc.
Qed.

Definition eval_template_program_mapping (p : inductives_mapping * template_program) t :=
  TemplateProgram.eval_template_program p.2 t.

Definition eval_template_program_env_mapping (p : inductives_mapping * template_program_env) t :=
  TemplateProgram.eval_template_program_env p.2 t.

Definition wf_template_inductive_mapping (Σ : Env.global_env) (m : inductive_mapping) : bool :=
  let '(ind, (_, cstrs)) := m in
  match Template.Ast.lookup_inductive Σ ind with
  | Some (mib, oib) => wf_tags_list cstrs #|oib.(Env.ind_ctors)|
  | None => true
  end.

Definition wf_template_inductives_mapping Σ m := forallb (wf_template_inductive_mapping Σ) m.

Program Definition build_template_program_env_mapping {cf : checker_flags} K :
  Transform.t _ _ _ _ _ _ eval_template_program_mapping eval_template_program_env_mapping :=
 {| name := name (build_template_program_env K);
    pre p := wf_template_inductives_mapping p.2.1 p.1 /\ pre (build_template_program_env K) p.2 ;
    transform p hp := let nhs := proj2 hp in
      (p.1, transform (build_template_program_env K) p.2 nhs) ;
   post p := wf_template_inductives_mapping p.2.1 p.1 /\ post (build_template_program_env K) p.2;
   obseq p hp p' := obseq (build_template_program_env K) p.2 (proj2 hp) p'.2 |}.
Next Obligation.
  cbn; intros  cf K input [? []]. intuition auto.
Qed.
Next Obligation.
  cbn; intros  cf K ? ? [? []] ev. cbn.
  now unshelve eapply (preservation (build_template_program_env K)).
Qed.

Lemma lookup_lookup_global_env_None (Σ : GlobalEnvMap.t) kn :
  Env.lookup_env Σ kn = None ->
  Env.lookup_global (eta_global_declarations Σ (Env.declarations Σ)) kn = None.
Proof.
  intros hl.
  induction Σ => // /=. induction env => //=. cbn in hl.
  rewrite /eta_global_declarations. cbn in *. rewrite lookup_global_map_on_snd hl //.
Qed.

Lemma eta_lookup_inductive_ctors (Σ : GlobalEnvMap.t) ind :
  option_map (fun '(mib, oib) => #|Env.ind_ctors oib|) (Ast.lookup_inductive Σ ind) = option_map (fun '(mib, oib) => #|Env.ind_ctors oib|) (Ast.lookup_inductive (eta_expand_global_env Σ) ind).
Proof.
  rewrite /Ast.lookup_inductive /eta_expand_global_env /lookup_inductive_gen /lookup_minductive_gen.
  destruct Env.lookup_env eqn:le => //.
  cbn. eapply eta_lookup_global in le. rewrite le /=.
  destruct g => //=. rewrite nth_error_map. destruct nth_error => //=. len.
  cbn. now eapply lookup_lookup_global_env_None in le as ->.
Qed.

Program Definition eta_expand_mapping K :
  Transform.t _ _ _ _ _ _ eval_template_program_env_mapping eval_template_program_mapping :=
 {| name := name (eta_expand K);
    pre p := wf_template_inductives_mapping p.2.1 p.1 /\ pre (eta_expand K) p.2 ;
    transform p hp := let nhs := proj2 hp in
      (p.1, transform (eta_expand K) p.2 nhs) ;
   post p := wf_template_inductives_mapping p.2.1 p.1 /\ post (eta_expand K) p.2;
   obseq p hp p' := obseq (eta_expand K) p.2 (proj2 hp) p'.2 |}.
Next Obligation.
  cbn; intros K input [? ?]. split. 2:now unshelve eapply (correctness (eta_expand K)).
  move: H. rewrite /wf_template_inductives_mapping.
  solve_all. move: H.
  rewrite /wf_template_inductive_mapping.
  destruct x as [ind [na tags]].
  have eqe := eta_lookup_inductive_ctors input.2.1 ind.
  do 2 destruct Ast.lookup_inductive as [[? ?]|]; cbn in *; congruence.
Qed.
Next Obligation.
  cbn; intros K ? ? [? []] ev. cbn.
  now unshelve eapply (preservation (eta_expand K)).
Qed.

Program Definition template_to_pcuic_mapping K :
  Transform.t _ _ _ _ _ _ eval_template_program_mapping eval_pcuic_program_mapping :=
 {| name := name (template_to_pcuic_transform K);
    pre p := wf_template_inductives_mapping p.2.1 p.1 /\ pre (template_to_pcuic_transform K) p.2 ;
    transform p hp := let nhs := proj2 hp in
      (p.1, transform (template_to_pcuic_transform K) p.2 nhs) ;
   post p := wf_pcuic_inductives_mapping p.2.1 p.1 /\ post (template_to_pcuic_transform K) p.2;
   obseq p hp p' := obseq (template_to_pcuic_transform K) p.2 (proj2 hp) p'.2 |}.
Next Obligation.
  cbn; intros K input [wfm pre].
  pose proof (correctness (template_to_pcuic_transform K) _ pre) as post.
  split. 2:now unshelve eapply (correctness (template_to_pcuic_transform K)).
  move: wfm. rewrite /wf_template_inductives_mapping.
  solve_all. move: H.
  rewrite /wf_template_inductive_mapping /wf_pcuic_inductive_mapping.
  unfold Ast.lookup_inductive, PCUICAst.PCUICLookup.lookup_inductive, Ast.lookup_inductive_gen,
    PCUICAst.PCUICLookup.lookup_inductive_gen,
    PCUICAst.PCUICLookup.lookup_minductive_gen,
    Ast.lookup_minductive_gen, lookup_minductive_gen.
  cbn. destruct post as [[[wtr _]] _]. cbn in wtr.
  destruct x as [ind [na tags]].
  destruct pre as [[wta] _].
  have trl := TemplateToPCUICCorrectness.trans_lookup input.2.1 (inductive_mind ind) wta.1 wtr.1.
  destruct Env.lookup_env; cbn in *; rewrite trl //.
  destruct g => //=. rewrite nth_error_map. destruct nth_error => //=. len.
Qed.
Next Obligation.
  cbn; intros K ? ? [? []] ev. cbn.
  now unshelve eapply (preservation (template_to_pcuic_transform K)).
Qed.

Program Definition pre_erasure_pipeline (efl := EWellformed.all_env_flags) :
 Transform.t _ _
  _ _ _ _
  eval_template_program
  PCUICTransform.eval_pcuic_program :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  let T2 (p:global_env_ext_map) := T1 (build_global_env_map (PCUICExpandLets.trans_global_env p.1), p.2) in
  let T3 (p:Env.global_env) := T2 (TemplateToPCUIC.trans_global_env p, Monomorphic_ctx) in
  let T4 (p:GlobalEnvMap.t) := T3 (eta_expand_global_env p) in
  (* Build an efficient lookup map for the following eta-expansion phase *)
  build_template_program_env (K _ T4) ▷
  (* Eta-expand constructors and fixpoint *)
  eta_expand (K _ T3) ▷
  (* Casts are removed, application is binary, case annotations are inferred from the global environment *)
  template_to_pcuic_transform (K _ T2).
Next Obligation.
  intros efl K T1 T2 T3 T4 p. cbn. intuition eauto.
Qed.
Next Obligation.
  intros efl K T1 T2 T3 T4 p. cbn. intuition eauto.
Qed.

Program Definition pre_erasure_pipeline_mapping (efl := EWellformed.all_env_flags) :
 Transform.t _ _
  _ _ _ _
  eval_template_program_mapping
  eval_pcuic_program_mapping :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  let T2 (p:global_env_ext_map) := T1 (build_global_env_map (PCUICExpandLets.trans_global_env p.1), p.2) in
  let T3 (p:Env.global_env) := T2 (TemplateToPCUIC.trans_global_env p, Monomorphic_ctx) in
  let T4 (p:GlobalEnvMap.t) := T3 (eta_expand_global_env p) in
  (* Build an efficient lookup map for the following eta-expansion phase *)
  build_template_program_env_mapping (K _ T4) ▷
  (* Eta-expand constructors and fixpoint *)
  eta_expand_mapping (K _ T3) ▷
  (* Casts are removed, application is binary, case annotations are inferred from the global environment *)
  template_to_pcuic_mapping (K _ T2).
Next Obligation.
  intros efl K T1 T2 T3 T4 p. cbn. intuition eauto.
Qed.
Next Obligation.
  intros efl K T1 T2 T3 T4 p. cbn. intuition eauto.
Qed.

Program Definition erasure_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) : Transform.t _ _ _ _ _ _
  eval_template_program
  (EProgram.eval_eprogram final_wcbv_flags) :=
  pre_erasure_pipeline ▷
  verified_erasure_pipeline.

Next Obligation.
  intros guard efl p; cbn. intuition auto.
Qed.

Program Definition erasure_pipeline_mapping {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) : Transform.t _ _ _ _ _ _
  eval_template_program_mapping
  (EProgram.eval_eprogram final_wcbv_flags) :=
  pre_erasure_pipeline_mapping ▷
  verified_erasure_pipeline_mapping.

Next Obligation.
  intros guard efl p; cbn. intuition auto.
Qed.

Local Obligation Tactic := program_simpl.

Program Definition verified_lambdabox_typed_pipeline (efl := EWellformed.all_env_flags)
  (wfl := {| with_prop_case := false; with_guarded_fix := true; with_constructor_as_block := false |}) econf :
  Transform.t _ _ _ EAst.term _ _
    (eval_eprogram_env_mapping wfl)
    (EProgram.eval_eprogram final_wcbv_flags) :=
  (* Reorder constructors according to the mapping *)
  reorder_cstrs_transformation (wca := eq_refl) (has_app := eq_refl) wfl (wcon := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := efl) true true ▷
   (* Simulation of the guarded fixpoint rules with a single unguarded one:
     the only "stuck" fixpoints remaining are unapplied.
     This translation is a noop on terms and environments.  *)
  guarded_to_unguarded_fix (fl := {| with_prop_case := false; with_guarded_fix := true; with_constructor_as_block := false |}) (wcon := eq_refl) eq_refl ▷
   (* Remove all constructor parameters *)
   remove_params_optimization (wcon := eq_refl) ▷
   (* Rebuild the efficient lookup table *)
   rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
   (* Inline projections to cases *)
   inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   (* Rebuild the efficient lookup table *)
   rebuild_wf_env_transform (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) true false ▷
   (* First-order constructor representation *)
   constructors_as_blocks_transformation
     (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags))
     (has_app := eq_refl) (has_pars := eq_refl) (has_rel := eq_refl) (has_box := eq_refl) (has_cstrblocks := eq_refl) ▷
   optional_unsafe_transforms econf.

 (* At the end of erasure we get a well-formed program (well-scoped globally and localy), without
    parameters in inductive declarations. The constructor applications are also transformed to a first-order
    "block"  application, of the right length, and the evaluation relation does not need to consider guarded
    fixpoints or case analyses on propositional content. All fixpoint bodies start with a lambda as well.
    Finally, projections are inlined to cases, so no `tProj` remains. *)

Import EGlobalEnv EWellformed.

Next Obligation.
  destruct H. split => //. sq.
  now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs.
Qed.

Next Obligation.
  unfold optional_unsafe_transforms. cbn.
  destruct enable_unsafe as [[] ? ? ?]=> //.
Qed.

Local Obligation Tactic := intros; eauto.

Definition eval_typed_eprogram_mapping (wfl : WcbvFlags) (p : inductives_mapping × (ExAst.global_env × EAst.term)) t :=
  eval_typed_eprogram wfl p.2 t.

Lemma wf_inductive_mapping_trans {Σ Σ' m} :
  (forall kn decl, ExAst.lookup_inductive Σ' kn = Some decl ->
    exists decl', PCUICAst.lookup_inductive Σ kn = Some decl' /\ #|ind_ctors decl'.2| = #|ExAst.ind_ctors decl|) ->
  wf_pcuic_inductive_mapping Σ m ->
  wf_inductive_mapping (ExAst.trans_env Σ') m.
Proof.
  intros hkn.
  rewrite /wf_pcuic_inductive_mapping /wf_inductive_mapping.
  destruct m as [ind [na tags]].
  destruct lookup_inductive as [decl|]eqn:hl => //.
  have [pdecl [hl' htr]] : exists p, ExAst.lookup_inductive Σ' ind = Some p /\ ExAst.trans_oib p = decl.2.
  { move: hl; rewrite /lookup_inductive /ExAst.lookup_inductive.
    rewrite /lookup_minductive /= /ExAst.lookup_minductive.
    rewrite OptimizeCorrectness.lookup_env_trans_env.
    destruct ExAst.lookup_env => //=. destruct g => //=.
    rewrite nth_error_map //=. destruct nth_error => //=. intros [= <-].
    now eexists. }
  eapply hkn in hl' as [decl' [hl''hct]].
  rewrite hl''hct. destruct decl'; cbn in *. destruct decl. cbn in *. subst o0.
  rewrite H. rewrite /ExAst.trans_oib /=.
  rewrite /ExAst.trans_ctors. now rewrite length_map.
Qed.

From Equations Require Import Equations.

Lemma nth_error_map_In {A B} (l : list A) (f : forall x, In x l -> B) n o :
  nth_error (map_In l f) n = Some o ->
  exists a (ha : In a l), nth_error l n = Some a /\ o = f a ha.
Proof.
  funelim (map_In l f); cbn.
  - rewrite nth_error_nil => //.
  - destruct n; cbn.
    * intros [= <-]; now eexists.
    * intros h. have [a [hin []]]:= H _ _ h.
      intros -> ->. exists a. exists (or_intror hin). split => //.
Qed.

Lemma map_In_length {A B} (l : list A) (f : forall x, In x l -> B) :
  #|map_In l f| = #|l|.
Proof. funelim (map_In l f); cbn; auto; lia. Qed.

Lemma lookup_inductive_erase_global_decls_deps {X_type X} {decls : global_env} {prop incl ignore} {kn} {decl} :
  ExAst.lookup_inductive (@Erasure.erase_global_decls_deps_recursive X_type X (declarations decls) (universes decls) (retroknowledge decls) prop incl ignore) kn = Some decl ->
  exists decl', PCUICAst.lookup_inductive decls kn = Some decl' /\ #|ind_ctors decl'.2| = #|ExAst.ind_ctors decl|.
Proof.
  rewrite /ExAst.lookup_inductive /ExAst.lookup_minductive.
  destruct decls as [univs' decls retro].
  cbn. unfold ExAst.lookup_env.
  induction decls as [|[kn' []]] in X, prop, incl |- *. cbn => //.
  - cbn [Erasure.erase_global_decls_deps_recursive] => //.
    destruct KernameSet.mem; cbn [ExAst.lookup_env Erasure.erase_global_decl];
    try destruct Erasure.erase_constant_decl => //=;
    unfold PCUICAst.lookup_inductive;
    unfold PCUICAst.PCUICEnvironment.lookup_env; cbn;
    unfold PCUICAst.lookup_inductive_gen, PCUICAst.lookup_minductive_gen.
    * unfold ExAst.lookup_env. cbn.
      case: eqb_spec.
      + intros <-. now cbn.
      + intros diff. cbn in IHdecls. eapply IHdecls.
    * case: eqb_spec.
      + intros <-. now cbn.
      + intros diff. eapply IHdecls.
    * case: eqb_spec.
      + intros heq.
        pose proof (PCUICWfEnv.abstract_env_exists X) as [[Σ abs]].
        pose proof (PCUICWfEnv.abstract_env_wf _ abs) as [].
        pose proof (prop _ abs). subst Σ. cbn in X0.
        eapply wf_fresh_globals in X0. cbn in  X0.
        depelim X0. clear abs.
        match goal with
        |- context [@Erasure.erase_global_decls_deps_recursive ?X_type ?X ?decls ?univs ?retro ?prop ?incl ?ignore ] =>
        set (iprop := prop); set (iincl := incl)
        (* have hcor := @ErasureCorrectness.erase_global_decls_deps_recursive_correct X_type X decls univs retro prop incl ignore (fun _ => eq_refl) *)
        end.
        intros h; specialize (IHdecls _ iprop iincl h).
        destruct IHdecls as [decl'' []].
        subst kn'. move: H0.
        rewrite /PCUICAst.lookup_inductive /PCUICAst.lookup_inductive_gen.
        rewrite /PCUICAst.lookup_minductive /PCUICAst.lookup_minductive_gen. cbn.
        destruct lookup_global eqn:hl => //=.
        eapply PCUICAst.fresh_global_iff_lookup_global_None in H. rewrite H in hl. congruence.
      + intros diff. eapply IHdecls.
  - cbn [Erasure.erase_global_decls_deps_recursive] => //.
    destruct KernameSet.mem; cbn [ExAst.lookup_env Erasure.erase_global_decl];
    unfold PCUICAst.lookup_inductive;
    unfold PCUICAst.PCUICEnvironment.lookup_env; cbn;
    unfold PCUICAst.lookup_inductive_gen, PCUICAst.lookup_minductive_gen.
    * unfold ExAst.lookup_env. cbn.
      case: eqb_spec.
      + intros <-. cbn.
        destruct nth_error eqn:hmi => //. intros [= <-].
        eapply nth_error_map_In in hmi as [oib [hin [hnth ->]]].
        exists (m, oib); rewrite hnth. split => //=.
        now rewrite /Erasure.erase_ind_body map_In_length.
      + intros diff. eapply IHdecls.
    * case: eqb_spec.
      + intros heq.
        pose proof (PCUICWfEnv.abstract_env_exists X) as [[Σ abs]].
        pose proof (PCUICWfEnv.abstract_env_wf _ abs) as [].
        pose proof (prop _ abs). subst Σ. cbn in X0.
        eapply wf_fresh_globals in X0. cbn in  X0.
        depelim X0. clear abs.
        match goal with
        |- context [@Erasure.erase_global_decls_deps_recursive ?X_type ?X ?decls ?univs ?retro ?prop ?incl ?ignore ] =>
        set (iprop := prop); set (iincl := incl)
        (* have hcor := @ErasureCorrectness.erase_global_decls_deps_recursive_correct X_type X decls univs retro prop incl ignore (fun _ => eq_refl) *)
        end.
        intros h; specialize (IHdecls _ iprop iincl h).
        destruct IHdecls as [decl'' []].
        subst kn'. move: H0.
        rewrite /PCUICAst.lookup_inductive /PCUICAst.lookup_inductive_gen.
        rewrite /PCUICAst.lookup_minductive /PCUICAst.lookup_minductive_gen. cbn.
        destruct lookup_global eqn:hl => //=.
        eapply PCUICAst.fresh_global_iff_lookup_global_None in H. rewrite H in hl. congruence.
      + intros diff. eapply IHdecls.
Qed.

Local Obligation Tactic := program_simpl.

Program Definition typed_erase_transform_mapping :
  Transform.t _ _ _ _ _ _ eval_pcuic_program_mapping (eval_typed_eprogram_mapping default_wcbv_flags) :=
 {| name := name typed_erase_transform;
    pre p := wf_pcuic_inductives_mapping p.2.1 p.1 /\ pre typed_erase_transform p.2 ;
    transform p hp := let nhs := proj2 hp in
      (p.1, transform typed_erase_transform p.2 nhs) ;
   post p := wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ post typed_erase_transform p.2;
   obseq p hp p' := obseq typed_erase_transform p.2 (proj2 hp) p'.2 |}.

Next Obligation.
Proof.
  destruct s. cbn -[ExAst.trans_env typed_erase_transform]. split => //.
  2:{ eapply (correctness typed_erase_transform). }
  move: i; rewrite /wf_pcuic_inductives_mapping /wf_inductives_mapping.
  solve_all.
  destruct w as [wf wt].
  eapply wf_inductive_mapping_trans; tea.
  intros kn d.
  eapply lookup_inductive_erase_global_decls_deps.
Qed.
Next Obligation.
  cbn. intros p v pr. eapply (preservation typed_erase_transform).
Qed.

Lemma lookup_inductive_map_on_snd_remove_decl Σ Σ' kn :
  lookup_inductive (map (on_snd (EOptimizePropDiscr.remove_match_on_box_decl Σ')) Σ) kn = lookup_inductive Σ kn.
Proof.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite EGenericGlobalMap.lookup_env_map_snd. destruct lookup_env => //=.
  destruct g => //.
Qed.

Program Definition remove_match_on_box_typed_transform_mapping {fl} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_mapping fl) (eval_typed_eprogram_mapping (disable_prop_cases fl)) :=
  let tr := (remove_match_on_box_typed_transform (fl:=fl) (wcon := wcon) (hastrel := hastrel) (hastbox := hastbox)) in
 {| name := name tr;
    pre p := wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ pre tr p.2 ;
    transform p hp := let nhs := proj2 hp in (p.1, transform tr p.2 nhs) ;
    post p := wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ post tr p.2;
     obseq p hp p' := obseq tr p.2 (proj2 hp) p'.2 |}.

Next Obligation.
Proof.
  split. 2:{ cbn. now unshelve eapply (correctness remove_match_on_box_typed_transform). }
  cbn.
  move: i; rewrite /wf_inductives_mapping; solve_all.
  move: H; rewrite /wf_inductive_mapping.
  rewrite /remove_match_on_box_typed_env.
  rewrite -map_trans_env.
  destruct x as [ind [na tags]]. now rewrite lookup_inductive_map_on_snd_remove_decl.
Qed.
Next Obligation.
  intros p v pr ev.
  now unshelve eapply (preservation remove_match_on_box_typed_transform).
Qed.

Definition eval_typed_eprogram_masks_mapping (fl : WcbvFlags) (p : inductives_mapping × ((option Optimize.dearg_set × ExAst.global_env) × EAst.term)) t :=
  eval_typed_eprogram_masks fl p.2 t.

Program Definition dearging_checks_transform_mapping {efl : EEnvFlags} (cf : ETransform.dearging_config) {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_mapping opt_wcbv_flags) (eval_typed_eprogram_masks_mapping opt_wcbv_flags) :=
  let tr := (dearging_checks_transform (efl:=efl) cf (hastrel := hastrel) (hastbox := hastbox)) in
 {| name := name tr;
    pre p := wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ pre tr p.2 ;
    transform p hp := let nhs := proj2 hp in (p.1, transform tr p.2 nhs) ;
    post p := wf_inductives_mapping (ExAst.trans_env p.2.1.2) p.1 /\ post tr p.2;
    obseq p hp p' := obseq tr p.2 (proj2 hp) p'.2 |}.
Next Obligation.
Proof.
  split => //.
Qed.
Next Obligation.
Proof.
  intros p v pr ev. now unshelve eapply (preservation (dearging_checks_transform cf)).
Qed.

Program Definition dearging_transform_mapping (cf : ETransform.dearging_config) :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_masks_mapping opt_wcbv_flags) (eval_eprogram_mapping opt_wcbv_flags)  :=
  let tr := (dearging_transform cf) in
 {| name := name tr;
    pre p := wf_inductives_mapping (ExAst.trans_env p.2.1.2) p.1 /\ pre tr p.2 ;
    transform p hp := let nhs := proj2 hp in (p.1, transform tr p.2 nhs) ;
    post p := wf_inductives_mapping p.2.1 p.1 /\ post tr p.2;
    obseq p hp p' := obseq tr p.2 (proj2 hp) p'.2 |}.
Next Obligation.
Proof.
  split => //.
  2:{ now unshelve eapply (correctness (dearging_transform cf)). }
  move: H; rewrite /wf_inductives_mapping; solve_all.
  move: H; rewrite /wf_inductive_mapping. destruct x as [ind [na tags]].
  rewrite /dearg. destruct input.2.1.1 => //.
  rewrite /OptimizeCorrectness.dearg_env.
  rewrite /lookup_inductive /lookup_minductive /=.
  rewrite !OptimizeCorrectness.lookup_env_trans_env.
  rewrite OptimizeCorrectness.lookup_env_debox_env_types option_map_two /=.
  rewrite OptimizeCorrectness.lookup_env_dearg_env option_map_two /=.
  destruct ExAst.lookup_env => //=; destruct g => //=.
  rewrite !nth_error_map option_map_two /=.
  rewrite /Optimize.dearg_mib /=. destruct Optimize.get_mib_masks => //=.
  rewrite !nth_error_mapi.
  1-2:destruct nth_error eqn:hnth => //=; len.
  intros _. destruct o => //=. destruct p => //.
Qed.
Next Obligation.
Proof.
  intros p v pr ev. now unshelve eapply (preservation (dearging_transform cf)).
Qed.

Program Definition rebuild_wf_env_transform_mapping {fl : WcbvFlags} {efl : EEnvFlags} (with_exp with_fix : bool) :
  Transform.t _ _ _ _ _ _ (eval_eprogram_mapping fl) (eval_eprogram_env_mapping fl) :=
  let tr := @rebuild_wf_env_transform fl efl with_exp with_fix in
 {| name := name tr;
    pre p := wf_inductives_mapping p.2.1 p.1 /\ pre tr p.2 ;
    transform p hp := let nhs := proj2 hp in (p.1, transform tr p.2 nhs) ;
    post p := wf_inductives_mapping p.2.1.(EEnvMap.GlobalContextMap.global_decls) p.1 /\ post tr p.2;
    obseq p hp p' := obseq tr p.2 (proj2 hp) p'.2 |}.
Next Obligation.
Proof.
  intros p v pr ev. now unshelve eapply (preservation (rebuild_wf_env_transform _ _)).
Qed.

Program Definition verified_typed_erasure_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags)
  econf :
  Transform.t _ _ _ _ _ _
   eval_pcuic_program_mapping
   (EProgram.eval_eprogram final_wcbv_flags) :=
   (* a bunch of nonsense for normalization preconditions *)
   let K ty (T : ty -> _) p
     := let p := T p in
        (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
          (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
   let T1 (p:global_env_ext_map) := p in
   (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
   pcuic_expand_lets_transform_mapping (K _ T1) ▷
   (* Erasure of proofs terms in Prop and types *)
   typed_erase_transform_mapping ▷
   (* Remove match on box early for dearging *)
   remove_match_on_box_typed_transform_mapping (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   (* Check if the preconditions for dearging are valid, otherwise dearging will be the identity *)
   dearging_checks_transform_mapping econf.(dearging_config) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   dearging_transform_mapping econf.(dearging_config) ▷
   rebuild_wf_env_transform_mapping true true ▷
   verified_lambdabox_typed_pipeline econf.

  Next Obligation.
    unfold pre_remove_match_on_box_typed. split; intuition eauto.
  Qed.
  Next Obligation.
    split; intuition auto.
  Qed.

Program Definition typed_erasure_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags) econf :
  Transform.t _ _ _ _ _ _
   eval_template_program_mapping
   (EProgram.eval_eprogram final_wcbv_flags) :=
   pre_erasure_pipeline_mapping ▷
   verified_typed_erasure_pipeline econf.

(* At the end of erasure we get a well-formed program (well-scoped globally and localy), without
   parameters in inductive declarations. The constructor applications are also transformed to a first-order
   "block"  application, of the right length, and the evaluation relation does not need to consider guarded
   fixpoints or case analyses on propositional content. All fixpoint bodies start with a lambda as well.
   Finally, projections are inlined to cases, so no `tProj` remains. *)

Import EGlobalEnv EWellformed.

Local Open Scope string_scope.

Axiom fake_guard_impl_properties :
forall (fix_cofix: PCUICTyping.FixCoFix)
       (Σ: PCUICAst.PCUICEnvironment.global_env_ext)
       (Γ: PCUICAst.PCUICEnvironment.context)
       (mfix: BasicAst.mfixpoint PCUICAst.term),
PCUICTyping.guard fix_cofix Σ Γ mfix <-> fake_guard_impl fix_cofix Σ Γ mfix.


Global Program Instance fake_guard_impl : abstract_guard_impl :=
{| guard_impl := fake_guard_impl |}.
Next Obligation. apply fake_guard_impl_properties. Qed.

(** Ideally we'd have a MetaRocq template program that generates a proof of Strong Normalization for the particular program we're erasing.  For now we just axiomatize SN. *)
Axiom fake_normalization : PCUICSN.Normalization.
Global Existing Instance fake_normalization.

(** This uses the retyping-based erasure and assumes that the global environment and term
  are welltyped (for speed). As such this should only be used for testing, or when we know that
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a
  Rocq definition). *)

Axiom assume_that_we_only_erase_on_wellformed_inductive_mappings : forall {cf : checker_flags},
  forall (p : Ast.Env.program) (m : inductives_mapping), wf_template_inductives_mapping p.1 m.

Axiom assume_that_we_only_erase_on_welltyped_programs : forall {cf : checker_flags},
  forall (p : Ast.Env.program), squash (TemplateProgram.wt_template_program p).

(* This also optionally runs the cofix to fix translation *)
Program Definition run_erase_program {guard : abstract_guard_impl} econf :=
  if econf.(enable_typed_erasure) then run (typed_erasure_pipeline econf)
  else run (erasure_pipeline_mapping ▷ (optional_unsafe_transforms econf)).
Next Obligation.
Proof.
  unfold optional_unsafe_transforms; cbn.
  destruct enable_unsafe as [[] ? ? ?]=> //.
Qed.

Program Definition erase_and_print_template_program econf (m : inductives_mapping) (p : Ast.Env.program) : string :=
  let p' := run_erase_program econf (m, p) _ in
  time "Pretty printing" EPretty.print_program p'.
Next Obligation.
  split.
  now eapply assume_that_we_only_erase_on_wellformed_inductive_mappings.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

Definition typed_erasure_config :=
  {| enable_unsafe := no_unsafe_passes;
      dearging_config := default_dearging_config;
      enable_typed_erasure := true;
      inlined_constants := KernameSet.empty |}.

(* TODO: Parameterize by a configuration for dearging, allowing to, e.g., override masks. *)
Program Definition typed_erase_and_print_template_program (p : Ast.Env.program)
  : string :=
  erase_and_print_template_program typed_erasure_config [] p.
