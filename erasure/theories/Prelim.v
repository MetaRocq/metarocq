(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Erasure Require Import EAstUtils Extract EArities EWcbvEval.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
     PCUICSubstitution PCUICLiftSubst PCUICClosedTyp
     PCUICReduction PCUICWcbvEval PCUICSR PCUICInversion PCUICGeneration
     PCUICContextConversion PCUICArities PCUICWellScopedCumulativity PCUICConversion
     PCUICWeakeningEnvTyp PCUICClassification.
From MetaRocq.SafeChecker Require Import PCUICErrors.
From Stdlib Require Import Program ssreflect.

Local Existing Instance extraction_checker_flags.

Ltac inv H := inversion H; subst; clear H.

Lemma typing_spine_inv args arg a Σ x2 x3 :
  nth_error args (arg) = Some a ->
  typing_spine Σ [] x2 args x3 ->
  {T & Σ;;; [] |- a : T}.
Proof.
  intros. revert arg H.
  dependent induction X; intros arg H17.
  - rewrite nth_error_nil in H17. congruence.
  - destruct (arg)%nat eqn:EAst.
    + cbn in H17. invs H17. eauto.
    + cbn in H17. eauto.
Qed.

Definition well_typed Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma typing_spine_wt args Σ x2 x3 :  wf Σ.1 ->
  typing_spine Σ [] x2 args x3 ->
  All (well_typed Σ []) args.
Proof.
  intros wfΣ sp.
  dependent induction sp; constructor; auto.
  now exists A.
Qed.

Lemma typing_spine_eval:
  forall (Σ : global_env_ext) (args args' : list PCUICAst.term)
  (X : All2 (PCUICWcbvEval.eval Σ) args args') (bla : wf Σ)
    (T x x0 : PCUICAst.term) (t0 : typing_spine Σ [] x args x0)
    (c : Σ;;; [] ⊢ x0 ≤ T) (x1 : PCUICAst.term)
    (c0 : Σ;;; [] ⊢ x1 ≤ x), isType Σ [] x1 -> isType Σ [] T -> typing_spine Σ [] x1 args' T.
Proof.
  intros. eapply typing_spine_red; eauto.
  eapply typing_spine_wt in t0; auto.
  eapply All2_All_mix_left in X; eauto. simpl in X.
  eapply All2_impl. eassumption. simpl. intros t u [ct et]. eapply wcbveval_red; eauto.
  eapply (projT2 ct).
Qed.

Lemma cumul_Sort_Prod_discr {Σ Γ T s na A B} :
  wf_ext Σ ->
  Σ ;;; Γ ⊢ T ≤ tSort s ->
  Σ ;;; Γ ⊢ T ≤ tProd na A B -> False.
Proof.
  intros wfΣ hs hs'.
  eapply ws_cumul_pb_Sort_r_inv in hs as [s' []].
  eapply ws_cumul_pb_Prod_r_inv in hs' as [dom' [codom' [T' []]]].
  destruct (closed_red_confluence c c1) as [nf []].
  eapply invert_red_sort in c2; subst.
  eapply invert_red_prod in c3 as [? [? []]]. discriminate.
Qed.

(** ** on mkApps *)

Lemma emkApps_snoc a l b :
  EAst.mkApps a (l ++ [b]) = EAst.tApp (EAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkAppBox_repeat n a :
  mkAppBox a n = EAst.mkApps a (repeat EAst.tBox n).
Proof.
  revert a; induction n; cbn; firstorder congruence.
Qed.

Lemma decompose_app_rec_inv2 {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  isApp f = false.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply IHt1.
Qed.

Lemma fst_decompose_app_rec t l : fst (EAstUtils.decompose_app_rec t l) = fst (EAstUtils.decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

(** ** Prelim on fixpoints *)

Lemma fix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (fix_subst mfix) n = Some (tFix mfix (#|mfix| - n - 1)).
Proof.
  unfold fix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma efix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (EGlobalEnv.fix_subst mfix) n = Some (EAst.tFix mfix (#|mfix| - n - 1)).
Proof.
  unfold EGlobalEnv.fix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma subslet_fix_subst `{cf : checker_flags} Σ mfix1 T n :
  wf Σ.1 ->
  Σ ;;; [] |- tFix mfix1 n : T ->
  subslet Σ [] (fix_subst mfix1) (fix_context mfix1).
Proof.
  intro hΣ.
  unfold fix_subst, fix_context.
  assert (exists L, mfix1 = mfix1 ++ L) by (exists []; now simpl_list). revert H.
  generalize mfix1 at 2 5 6.  intros.
  induction mfix0 using rev_ind.
  - econstructor.
  - rewrite mapi_app. cbn in *. rewrite rev_app_distr. cbn in *.
    rewrite length_app. cbn. rewrite Nat.add_comm /=; econstructor.
    + eapply IHmfix0. destruct H as [L]. exists (x :: L). subst. now rewrite <- app_assoc.
    + rewrite <- plus_n_O.
      rewrite PCUICLiftSubst.simpl_subst_k. clear. induction l; cbn; try congruence.
      eapply inversion_Fix in X as (? & ? & ? & ? & ? & ? & ?) ; auto.
      econstructor; eauto. destruct H. subst.
      rewrite <- app_assoc, nth_error_app_ge; try lia.
      now rewrite Nat.sub_diag.
Qed.

Lemma cofix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (cofix_subst mfix) n = Some (tCoFix mfix (#|mfix| - n - 1)).
Proof.
  unfold cofix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm; lia_f_equal.
Qed.

Lemma ecofix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (EGlobalEnv.cofix_subst mfix) n = Some (EAst.tCoFix mfix (#|mfix| - n - 1)).
Proof.
  unfold EGlobalEnv.cofix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma subslet_cofix_subst `{cf : checker_flags} Σ mfix1 T n :
  wf Σ.1 ->
  Σ ;;; [] |- tCoFix mfix1 n : T ->
  subslet Σ [] (cofix_subst mfix1) (fix_context mfix1).
Proof.
  intro hΣ.
  unfold cofix_subst, fix_context.
  assert (exists L, mfix1 = mfix1 ++ L)%list by (exists []; now simpl_list). revert H.
  generalize mfix1 at 2 5 6.  intros.
  induction mfix0 using rev_ind.
  - econstructor.
  - rewrite mapi_app. cbn in *. rewrite rev_app_distr. cbn in *.
    rewrite length_app /= Nat.add_comm /=. econstructor.
    + eapply IHmfix0. destruct H as [L]. exists (x :: L). subst. now rewrite <- app_assoc.
    + rewrite <- plus_n_O.
      rewrite PCUICLiftSubst.simpl_subst_k. clear. induction l; cbn; try congruence.
      eapply inversion_CoFix in X as (? & ? & ? & ? & ? & ? & ?) ; auto.
      econstructor; eauto. destruct H. subst.
      rewrite <- app_assoc. rewrite nth_error_app_ge. lia.
      now rewrite Nat.sub_diag.
Qed.

Lemma unfold_cofix_type Σ mfix idx args narg fn ty :
  wf Σ.1 ->
  Σ ;;; [] |- mkApps (tCoFix mfix idx) args : ty ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  Σ ;;; [] |- mkApps fn args : ty.
Proof.
  intros wfΣ ht.
  pose proof (typing_wf_local ht).
  eapply PCUICValidity.inversion_mkApps in ht as (? & ? & ?); eauto.
  eapply inversion_CoFix in t; auto.
  destruct_sigma t.
  rewrite /unfold_cofix e => [=] harg hfn.
  subst fn.
  eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
  eapply PCUICSpine.type_mkApps; eauto.
  pose proof a0 as a0'.
  eapply nth_error_all in a0'; eauto. apply unlift_TermTyp in a0'.
  eapply (substitution (Δ := [])) in a0'; eauto.
  2:{ eapply subslet_cofix_subst; pcuic. constructor; eauto. }
  rewrite PCUICLiftSubst.simpl_subst_k in a0'. now autorewrite with len.
  eapply a0'. now eapply nth_error_all, isTypeRel_isType in a; tea.
Qed.

(** Assumption contexts: constructor arguments/case branches contexts contain only assumptions, no local definitions *)

Lemma is_assumption_context_spec Γ :
  is_true (is_assumption_context Γ) <-> PCUICLiftSubst.assumption_context Γ.
Proof.
 induction Γ; cbn.
 - split; econstructor.
 - split; intros H.
   + destruct a; cbn in *. destruct decl_body; inversion H. now econstructor.
   + invs H. cbn. now eapply IHΓ.
Qed.

Lemma assumption_context_map2_binders nas Γ :
  assumption_context Γ ->
  assumption_context (map2 set_binder_name nas Γ).
Proof.
  induction 1 in nas |- *; cbn. destruct nas; cbn; auto; constructor.
  destruct nas; cbn; auto; constructor. auto.
Qed.

Lemma declared_constructor_assumption_context (wfl := default_wcbv_flags) {Σ c mdecl idecl cdecl} {wfΣ : wf_ext Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  assumption_context (cstr_args cdecl).
Proof.
  intros.
  destruct (on_declared_constructor H) as [? [cu [_ onc]]].
  destruct onc.
  now eapply is_assumption_context_spec.
Qed.

Lemma assumption_context_cstr_branch_context (wfl := default_wcbv_flags) {Σ} {wfΣ : wf_ext Σ} {c mdecl idecl cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  assumption_context (cstr_branch_context c.1 mdecl cdecl).
Proof.
  intros decl.
  eapply declared_constructor_assumption_context in decl.
  rewrite /cstr_branch_context. pcuic.
Qed.

Lemma expand_lets_erasure (wfl := default_wcbv_flags) {Σ mdecl idecl cdecl c brs p} {wfΣ : wf_ext Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  wf_branches idecl brs ->
  All2i (fun i cdecl br =>
  PCUICEquality.eq_context_upto_names (bcontext br)
      (cstr_branch_context c.1 mdecl cdecl)) 0 idecl.(ind_ctors) brs ->
  All (fun br =>
    expand_lets (inst_case_branch_context p br) (bbody br) = bbody br) brs.
Proof.
  intros decl wfbrs.
  red in wfbrs.
  eapply Forall2_All2 in wfbrs.
  intros ai.
  eapply All2i_nth_hyp in ai.
  eapply All2i_All2_mix_left in ai; tea. clear wfbrs.
  solve_all.
  red in a. red in a.
  erewrite <- PCUICCasesContexts.inst_case_branch_context_eq; tea.
  rewrite PCUICSigmaCalculus.expand_lets_assumption_context //.
  eapply assumption_context_map2_binders.
  rewrite /pre_case_branch_context_gen /inst_case_context.
  eapply PCUICInductiveInversion.assumption_context_subst_context.
  eapply PCUICInductiveInversion.assumption_context_subst_instance.
  destruct c. cbn.
  eapply (assumption_context_cstr_branch_context (c:=(i0, i))). split. apply decl. tea.
Qed.

Lemma assumption_context_compare_decls Γ Δ :
  PCUICEquality.eq_context_upto_names Γ Δ ->
  assumption_context Γ ->
  assumption_context Δ.
Proof.
  induction 1; auto.
  intros H; depelim H.
  depelim r; econstructor; auto.
Qed.

Lemma smash_assumption_context Γ Δ : assumption_context Γ ->
  smash_context Δ Γ = Γ ,,, Δ.
Proof.
  intros ass; induction ass in Δ |- *; cbn; auto.
  - now rewrite app_context_nil_l.
  - rewrite PCUICSigmaCalculus.smash_context_acc /app_context.
    rewrite IHass /=.
    rewrite -(app_tip_assoc Δ _ Γ). f_equal.
    rewrite -/(expand_lets_k_ctx Γ 0 _).
    rewrite [expand_lets_k_ctx _ _ _]PCUICSigmaCalculus.expand_lets_ctx_assumption_context //.
Qed.

Import PCUICGlobalEnv PCUICSpine.
Lemma subslet_cstr_branch_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ pars parsubst parsubst' s' inst' ind n mdecl idecl cdecl u p br napp} :
  declared_constructor Σ (ind, n) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  PCUICEquality.cmp_ind_universes Σ ind napp u (puinst p) ->
  spine_subst Σ Γ pars parsubst (ind_params mdecl)@[u] ->
  spine_subst Σ Γ (pparams p) parsubst' (ind_params mdecl)@[puinst p] ->
  assumption_context cdecl.(cstr_args) ->
  ws_cumul_pb_terms Σ Γ pars (pparams p) ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  PCUICSpine.spine_subst Σ Γ s' inst'
    (subst_context parsubst 0 (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)@[u])) ->
  subslet Σ Γ (List.rev s') (case_branch_context ind mdecl p (forget_types (bcontext br)) cdecl).
Proof.
  intros declc cu cu' hr sppars sppars' assargs eqp wfp wfbr spargs.
  rewrite /case_branch_context /case_branch_context_gen.
  eapply PCUICSpine.subslet_eq_context_alpha.
  symmetry. eapply PCUICCasesContexts.eq_binder_annots_eq.
  eapply PCUICInductiveInversion.wf_pre_case_branch_context_gen; tea.
  rewrite /pre_case_branch_context_gen /inst_case_context.
  rewrite /cstr_branch_context.
  rewrite PCUICInductiveInversion.subst_instance_expand_lets_ctx PCUICUnivSubstitutionConv.subst_instance_subst_context.
  rewrite PCUICInductives.instantiate_inds //. exact declc.
  epose proof (PCUICInductiveInversion.constructor_cumulative_indices declc cu cu' hr _ _ _ _ _ sppars sppars' eqp) as [eqctx _].
  cbn in eqctx.
  epose proof (spine_subst_smash spargs).
  eapply spine_subst_cumul in X. eapply X.
  pcuic. pcuic. apply X.
  { eapply substitution_wf_local. eapply (spine_subst_smash sppars').
    eapply PCUICInductives.wf_local_expand_lets.
    rewrite -app_context_assoc.
    eapply PCUICWeakeningTyp.weaken_wf_local => //. eapply sppars.
    eapply (PCUICSR.on_constructor_wf_args declc) => //. }
  rewrite /=.
  rewrite -(spine_subst_inst_subst sppars').
  assert (smash_context [] (cstr_args cdecl)@[puinst p] = (cstr_args cdecl)@[puinst p]).
  { rewrite smash_assumption_context //. pcuic. }
  rewrite -H.
  rewrite -PCUICClosed.smash_context_subst /= subst_context_nil.
  rewrite -PCUICClosed.smash_context_subst /= subst_context_nil. apply eqctx.
Qed.


(** ** Prelim on typing *)

Inductive red_decls Σ Γ Γ' : forall (x y : context_decl), Type :=
| conv_vass na na' T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
  eq_binder_annot na na' ->
  red_decls Σ Γ Γ' (vass na T) (vass na' T')

| conv_vdef_type na na' b T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
  eq_binder_annot na na' ->
  red_decls Σ Γ Γ' (vdef na b T) (vdef na' b T')

| conv_vdef_body na na' b b' T : isType Σ Γ' T ->
  eq_binder_annot na na' ->
  Σ ;;; Γ' |- b' : T -> red Σ Γ b b' ->
  red_decls Σ Γ Γ' (vdef na b T) (vdef na' b' T).

Abbreviation red_context Σ := (All2_fold (red_decls Σ)).

Lemma conv_context_app (Σ : global_env_ext) (Γ1 Γ2 Γ1' : context) :
  wf Σ ->
  wf_local Σ (Γ1 ,,, Γ2) ->
  conv_context cumulSpec0 Σ Γ1 Γ1' -> conv_context cumulSpec0 Σ (Γ1 ,,, Γ2) (Γ1' ,,, Γ2).
Proof.
  intros. induction Γ2.
  - cbn; eauto.
  - destruct a. destruct decl_body.
    + cbn. econstructor. inv X0. apply IHΓ2. eauto.
      depelim X0; econstructor; reflexivity.
    + cbn. econstructor. inv X0. apply IHΓ2. eauto. now econstructor.
Qed.
