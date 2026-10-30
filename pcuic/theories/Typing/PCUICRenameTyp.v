(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICCumulativity
  PCUICTyping PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars PCUICOnFreeVarsConv PCUICGuardCondition PCUICTyping
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICRenameConv.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".
Set Default Proof Using "Type*".

Section Renaming.

Context `{cf : checker_flags}.

Lemma renaming_vass :
  forall P Σ Γ Δ na A f,
    wf_local Σ (Δ ,, vass na (rename f A)) ->
    renaming P Σ Γ Δ f ->
    renaming (shiftnP 1 P) Σ (Γ ,, vass na A) (Δ ,, vass na (rename f A)) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na A f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vass; assumption.
Qed.

Lemma renaming_vdef :
  forall P Σ Γ Δ na b B f,
    wf_local Σ (Δ ,, vdef na (rename f b) (rename f B)) ->
    renaming P Σ Γ Δ f ->
    renaming (shiftnP 1 P) Σ (Γ ,, vdef na b B) (Δ ,, vdef na (rename f b) (rename f B)) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na b B f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vdef; assumption.
Qed.

Lemma rename_ind_predicate_context {Σ : global_env_ext} {wfΣ : wf Σ} {f ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  rename_context (shiftn (context_assumptions (ind_params mdecl)) f) (ind_predicate_context ind mdecl idecl) =
  ind_predicate_context ind mdecl idecl.
Proof.
  intros isdecl.
  generalize (declared_inductive_closed_pars_indices isdecl).
  rw closedn_ctx_app => /andP [] clpars /= clinds.
  rw /ind_predicate_context.
  rw /expand_lets_ctx /expand_lets_k_ctx.
  rw !rename_context_snoc /= /map_decl /= /snoc. f_equal.
  - f_equal. len.
    rw rename_mkApps /=. f_equal.
    rw shiftn_add.
    relativize (#|_| + _).
    1:now erewrite -> rename_to_extended_list.
    now len.
  - rw rename_context_subst.
    rw rename_closed_extended_subst //. f_equal.
    rw shiftn_add Nat.add_comm. len.
    rw rename_context_lift. f_equal.
    rw rename_closedn_ctx //.
Qed.

Lemma rename_case_predicate_context {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  rename_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (rename_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rw rename_context_set_binder_name.
  - len.
    now rw -(wf_predicate_length_pcontext wfp).
  - f_equal. rw /pre_case_predicate_context_gen.
    rw rename_inst_case_context.
    rw (wf_predicate_length_pars wfp) (declared_minductive_ind_npars decli).
    now rw (rename_ind_predicate_context decli).
Qed.

Lemma rename_case_branch_type {Σ : global_env_ext} {wfΣ : wf Σ} f (ci : case_info) mdecl idecl p br i cdecl :
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  let p' := rename_predicate f p in
  let ptm' := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p') (preturn p') in
  case_branch_type ci mdecl idecl
     (rename_predicate f p)
     (map_branch_shift rename shiftn f br)
     ptm' i (rename_constructor_body mdecl f cdecl) =
  map_pair (rename_context f) (rename (shiftn #|bcontext br| f))
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rw /case_branch_type /case_branch_type_gen /map_pair /=.
  rw rename_case_branch_context_gen //.
  { eapply (declared_inductive_closed_params decli). }
  { len; now apply wf_branch_length. }
  { rw -(declared_minductive_ind_npars decli).
    apply (wf_predicate_length_pars wfp). }
  f_equal.
  rw rename_mkApps map_app map_map_compose.
  rw (wf_branch_length wfb).
  f_equal.
  * rw /ptm' /ptm !lift_it_mkLambda_or_LetIn !rename_it_mkLambda_or_LetIn.
    rw !lift_rename. f_equal.
    ++ rw /p'. len.
      epose proof (rename_context_lift f #|cstr_args cdecl| 0).
        rw Nat.add_0_r in H.
        rw H. len.
        rw shiftn0 //. f_equal.
        rw rename_case_predicate_context //.
    ++ rw /p'. rw Nat.add_0_r. simpl. len.
      rw map2_length //. 1:{ len. now rw (wf_predicate_length_pcontext wfp). }
      rw - !lift_rename; len. rw case_predicate_context_length // shiftn_add.
      now rw -rename_shiftnk Nat.add_comm.
  * rw /= rename_mkApps /=. f_equal.
    ++ rw !map_map_compose /id. apply map_ext => t.
      rw /expand_lets /expand_lets_k.
      rw -rename_subst_instance. len.
      rw -shiftn_add -shiftn_add.
      rw rename_subst map_rev. f_equal.
      rw List.length_rev rename_subst.
      rw (wf_predicate_length_pars wfp).
      rw (declared_minductive_ind_npars decli).
      rw -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
      rw rename_closed_extended_subst.
      { rw closedn_subst_instance_context.
        apply (declared_inductive_closed_params decli). }
      f_equal. len. rw !shiftn_add.
      rw (Nat.add_comm _ (context_assumptions _)) rename_shiftnk.
      f_equal. rw Nat.add_comm rename_subst.
      rw rename_inds. f_equal.
      rw shiftn_add. now len.
    ++ unfold id. f_equal. f_equal.
       rw map_app map_map_compose.
       rw map_map_compose.
       setoid_rewrite rename_shiftn. len. f_equal.
       rw rename_to_extended_list.
       now rw /to_extended_list /to_extended_list_k reln_fold.
Qed.

Lemma cumulSpec_renameP pb P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
    wf Σ.1 ->
    urenaming sP Γ Δ f ->
    is_closed_context Γ ->
    is_open_term Γ A ->
    is_open_term Γ B ->
    is_closed_context Δ ->
    Σ ;;; Γ ⊢ A ≤s[pb] B ->
    Σ ;;; Δ ⊢ rename f A ≤s[pb] rename f B.
Proof.
  intros sP wfΣ Hren HfreeA HfreeB HΓ HΔ e.
  revert pb Γ A B e sP Δ f wfΣ Hren HfreeA HfreeB HΓ HΔ e.
  induction 1; intros; cbn.
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  all: repeat match goal with
         | [ H : All2_dep _ _ |- _ ] => apply All2_undep in H
         end.
  - rw rename_subst10. solve [econstructor].
  - rw rename_subst10. solve [econstructor].
  - rename Hren into hf. unfold urenaming in hf.
    destruct (nth_error Γ i) eqn:hnth; noconf pf.
    assert (hav : sP i).
    { unfold sP, shiftnP in *. cbn in *. rw orb_false_r in HfreeB. intuition auto with *. }
    clear HfreeB.
    specialize hf with (1 := hav) (2 := hnth).
    destruct hf as [decl' [e' [eqann [hr hbo]]]].
    rw H /= in hbo.
    rw lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    let H0 := match goal with H : rename _ _ = rename _ _ |- _ => H end in
    sigma in H0; sigma; rw H0.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rw -rename_inst.
        now rw -(lift0_rename (S (f i)) _). }
     eapply cumul_rel. now rw e' /= hdecl.
   - rw rename_mkApps. simpl.
     rw rename_iota_red //.
    * rw length_skipn; lia.
    * change (bcontext br) with (bcontext (rename_branch f br)).
     move/and5P: HfreeB => [_ _ _ _ hbrs].
     eapply nth_error_forallb in hbrs; tea. simpl in hbrs.
     move/andP: hbrs => [] clbctx clbod.
     rw closedn_ctx_on_free_vars.
     now rw test_context_k_closed_on_free_vars_ctx in clbctx.
   * eapply cumul_iota.
     + rw nth_error_map Hbrs /= //.
     + simpl. now len.
   - rw 2!rename_mkApps. simpl.
     eapply cumul_fix.
     + eapply rename_unfold_fix. eassumption.
     + rw -is_constructor_rename. assumption.
   - rw 2!rename_mkApps. simpl.
     eapply cumul_cofix_case.
     eapply rename_unfold_cofix. eassumption.
   - rw 2!rename_mkApps. simpl.
     eapply cumul_cofix_proj.
     eapply rename_unfold_cofix. eassumption.
   - rw rename_subst_instance.
     eapply cumul_delta.
     + eassumption.
     + rw rename_closed. 2: assumption.
       eapply declared_constant_closed_body. all: eauto.
   - rw rename_mkApps. simpl.
     eapply cumul_proj. rw nth_error_map. rw Hargs. reflexivity.
   - eapply cumul_Trans; try apply X0; try apply X2; eauto. eapply urename_is_open_term; eauto.
   - eapply cumul_Sym; intuition; eauto.
   - eapply cumul_Refl; intuition; eauto.
   - eapply cumul_Evar. cbn in *.
     apply forallb_All in HfreeB, HΓ.
     repeat toAll. eapply All2_impl. 1:tea. cbn; intros.
     eapply X0.1.2; intuition.
   - cbn in *. rtoProp.
     eapply cumul_App; try apply X0; try apply X2; eauto.
   - cbn in HfreeB, HΓ; rtoProp.
     eapply cumul_Lambda; try apply IHe1; try apply IHe2; eauto;
     try rw shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rw shiftnP_S; eauto. apply urenaming_vass; eauto.
     * rw on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rw on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.
   - cbn in HfreeB, HΓ. rtoProp.
     eapply cumul_Prod; try apply IHe1; try apply IHe2; eauto;
     try rw shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rw shiftnP_S; eauto. apply urenaming_vass; eauto.
     * rw on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rw on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.
   - cbn in HfreeB, HΓ; rtoProp.
     eapply cumul_LetIn; try apply IHe1; try apply IHe2; eauto; try apply IHe3;
     try rw shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rw shiftnP_S; eauto. apply urenaming_vdef; eauto.
     * rw on_free_vars_ctx_snoc_def; eauto.
     * rw on_free_vars_ctx_snoc_def; eauto.
       all: eapply urename_is_open_term; eauto.
   - cbn in HfreeB, HΓ.
     rename Hp into Hpold, HΓ into H'; rename HfreeB into H.
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hp H]; destruct H' as [Hp' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hreturn H]; destruct H' as [Hreturn' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hcontext H]; destruct H' as [Hcontext' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hc Hbrs]; destruct H' as [Hc' Hbrs'].
     eapply cumul_Case.
     * unfold cumul_predicate in *; destruct_head'_prod.
       repeat split; eauto.
       + eapply All2_map. apply forallb_All in Hp, Hp'. repeat toAll.
         eapply All2_impl. 1: tea. cbn; intros. destruct X as [[X [X''' X']] X'']. apply X'; eauto.
       + unfold preturn. cbn. unshelve erewrite (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
         exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
         ++ rw app_context_length.
            eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
            unshelve erewrite <- (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
            rewrite <- inst_case_predicate_context_length.
            rw test_context_k_closed_on_free_vars_ctx in Hcontext.
            rw inst_case_predicate_context_rename; eauto.
            apply urenaming_context; eauto.
         ++ rw test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context.
            apply on_free_vars_ctx_inst_case_context; eauto.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rw length_app.
            rewrite <- shiftnP_add.
            rw inst_case_predicate_context_length.
            eassumption.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rw length_app.
            rewrite <- shiftnP_add.
            rw inst_case_predicate_context_length.
            unshelve erewrite (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
         ++ rw test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
            +++ eapply All_forallb. apply All_map. apply forallb_All in Hp; eapply All_impl. 1: tea.
                cbn; intros. eapply urename_is_open_term; eauto.
            +++ unfold pparams. cbn. rw length_map. exact Hcontext.
     * eauto.
     * unfold cumul_branches, cumul_branch in *.
       let X2 := match goal with H : All2 _ brs brs' |- _ => H end in
       rename X2 into Hbrsbrs'.
       apply forallb_All in Hbrs, Hbrs'. apply (All2_All_mix_left Hbrs) in Hbrsbrs'. clear Hbrs.
       apply (All2_All_mix_right Hbrs') in Hbrsbrs'. clear Hbrs'.
       apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros; destruct_head'_prod.
       unshelve erewrite (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
       split; eauto.
       repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
       + rw app_context_length.
       eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
       unshelve erewrite <- (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
       rewrite <- (inst_case_branch_context_length p).
       rewrite -> test_context_k_closed_on_free_vars_ctx in *.
       rw inst_case_branch_context_rename; eauto.
       apply urenaming_context; eauto.
       + rewrite -> test_context_k_closed_on_free_vars_ctx in *.
         unfold inst_case_predicate_context.
         apply on_free_vars_ctx_inst_case_context; eauto.
         repeat toAll; eauto.
      + unfold inst_case_predicate_context.
         unfold is_open_term. rw length_app.
        rewrite <- shiftnP_add.
        rw inst_case_branch_context_length.
        eassumption.
      + unfold inst_case_predicate_context.
        unfold is_open_term. rw length_app.
        rewrite <- shiftnP_add.
        rw inst_case_branch_context_length.
       unshelve erewrite (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
      + rw test_context_k_closed_on_free_vars_ctx in Hcontext.
        unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
       ++ eapply All_forallb. apply All_map. repeat toAll. eapply All_impl. 1: tea.
           cbn; intros. eapply urename_is_open_term; eauto.
       ++ unfold pparams. rewrite -> test_context_k_closed_on_free_vars_ctx in *.
        cbn. rw length_map. eassumption.
  - cbn in *. eapply cumul_Proj; try apply X0; eauto.
  - rw (All2_length X).
    eapply cumul_Fix. cbn in *.
    apply forallb_All in HfreeB, HΓ.
    apply (All2_All_mix_left HfreeB) in X. clear HfreeB.
    apply (All2_All_mix_right HΓ) in X. clear HΓ.
    apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
    destruct_head'_prod.
    repeat split; eauto.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: cbv [test_def] in *; cbn in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      all: tea.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: unfold test_def in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      + rw app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
      rewrite <- (All2_length X).
      rw rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto.
      + rw on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        destruct_head'_prod; eauto.
      + unfold is_open_term. rw length_app.
        rewrite <- shiftnP_add.
        rw fix_context_length. eauto.
      + unfold is_open_term. rw length_app.
        rewrite <- shiftnP_add.
        rw fix_context_length.
        rw (All2_length X). eauto.
      + rw on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        repeat toAll.
        eapply All2_All_left. 1: tea. cbn ; intros.
        destruct_head'_prod.
        unfold test_def in *.
        repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
        apply andb_and. cbn. split.
        ++ eapply urename_is_open_term; eauto.
        ++ rw length_map. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rw fix_context_length; eauto.
  - rw (All2_length X).
    eapply cumul_CoFix. cbn in *.
    apply forallb_All in HfreeB, HΓ.
    apply (All2_All_mix_left HfreeB) in X. clear HfreeB.
    apply (All2_All_mix_right HΓ) in X. clear HΓ.
    apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
    destruct_head'_prod.
    repeat split; eauto.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: unfold test_def in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      all: tea.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: unfold test_def in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      + rw app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
      rewrite <- (All2_length X).
      rw rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto.
      + rw on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        destruct_head'_prod; eauto.
      + unfold is_open_term. rw length_app.
        rewrite <- shiftnP_add.
        rw fix_context_length. eauto.
      + unfold is_open_term. rw length_app.
        rewrite <- shiftnP_add.
        rw fix_context_length.
        rw (All2_length X). eauto.
      + rw on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        apply All_map. repeat toAll.
        eapply All2_All_left. 1: tea. cbn ; intros.
        unfold test_def in *.
        destruct_head'_prod.
        repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
        apply andb_and. cbn. split.
        ++ eapply urename_is_open_term; eauto.
        ++ rw length_map. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rw fix_context_length; eauto.
  - eapply cumul_Prim. depelim X; cbn; cbn in HfreeB, HΓ; rtoProp; constructor; cbn; eauto. solve_all.
  - repeat rw rename_mkApps. eapply cumul_Ind.
    * repeat rw length_map; eauto.
    * inv_on_free_vars.
      eapply forallb_All in b, b0.
      apply (All2_All_mix_left b0) in X. clear b0.
      apply (All2_All_mix_right b) in X. clear b.
      apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      destruct_head'_prod.
      eauto.
  - repeat rw rename_mkApps. eapply cumul_Construct.
    * repeat rw length_map; eauto.
    * inv_on_free_vars. repeat toAll.
      eapply All2_impl. 1: tea. cbn; intros.
      destruct_head'_prod; eauto.
  - eapply cumul_Sort; eauto.
  - eapply cumul_Const; eauto.
Defined.

Lemma convSpec_renameP P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
    wf Σ.1 ->
    urenaming sP Γ Δ f ->
    is_closed_context Γ ->
    is_open_term Γ A ->
    is_open_term Γ B ->
    is_closed_context Δ ->
    Σ ;;; Γ |- A =s B ->
    Σ ;;; Δ |- rename f A =s rename f B.
Proof.
  apply cumulSpec_renameP.
Qed.

(* Lemma cumul_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    cumul_decls Σ Γ Γ' d d' ->
    cumul_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply convSpec_renameP || eapply cumulSpec_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed.

Lemma conv_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    conv_decls Σ Γ Γ' d d' ->
    conv_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply convSpec_renameP || eapply cumulSpec_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed. *)

Lemma on_free_vars_ctx_onctx_k P ctx :
  reflectT (onctx_k (fun k => on_free_vars (shiftnP k P)) 0 ctx)
    (on_free_vars_ctx P ctx).
Proof.
  rw -test_context_k_on_free_vars_ctx.
  apply (onctx_k_P reflectT_pred2).
Qed.

Lemma Alli_helper Q Γ :
  Alli (fun (i : nat) (d : context_decl) => ondecl (Q (#|Γ| - i + 0)) d) 1 Γ ->
  onctx_k Q 0 Γ.
Proof.
  move/(Alli_shiftn_inv 0 _ 1) => H.
  eapply Alli_impl; tea => n x /=.
  now replace (#|Γ| - S n + 0) with (Nat.pred #|Γ| - n + 0) by lia.
Qed.

Lemma ondecl_on_free_vars_decl P d :
  ondecl (on_free_vars P) d ->
  on_free_vars_decl P d.
Proof.
  rw /on_free_vars_decl.
  now case: (ondeclP reflectT_pred).
Qed.

(* Lemma conv_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  conv_context Σ (Γ ,,, L) (Γ ,,, R) ->
  conv_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply conv_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea =>
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply conv_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH').
    now eapply ondecl_on_free_vars_decl.
  + rewrite on_ctx_free_vars_extend // onΓ.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed. *)


(* Lemma cumul_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  cumul_context Σ (Γ ,,, L) (Γ ,,, R) ->
  cumul_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply cumul_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea =>
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply cumul_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH').
    now eapply ondecl_on_free_vars_decl.
  + rewrite on_ctx_free_vars_extend // onΓ.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed. *)

Lemma subst1_inst :
  forall t n u,
    t{ n := u } = t.[⇑^n (u ⋅ ids)].
Proof.
  intros t n u.
  unfold subst1. rw subst_inst.
  eapply inst_ext. intro i.
  unfold Upn, subst_compose, subst_consn.
  destruct (Nat.ltb_spec0 i n).
  - rewrite -> nth_error_idsn_Some by assumption. reflexivity.
  - rewrite -> nth_error_idsn_None by lia.
    rw idsn_length.
    destruct (Nat.eqb_spec (i - n) 0).
    + rw e. simpl. reflexivity.
    + replace (i - n) with (S (i - n - 1)) by lia. simpl.
      destruct (i - n - 1) eqn: e.
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.
(* Hint Rewrite @subst1_inst : sigma. *)

Lemma rename_predicate_preturn f p :
  rename (shiftn #|p.(pcontext)| f) (preturn p) =
  preturn (rename_predicate f p).
Proof. reflexivity. Qed.

Lemma wf_local_app_renaming P Σ Γ Δ :
  All_local_rel (fun (Γ : context) j =>
    forall P Δ (f : nat -> nat),
    renaming (shiftnP #|Γ| P) Σ Γ Δ f ->
    lift_typing0 (fun t T => Σ ;;; Δ |- rename f t : rename f T) j)
    Γ Δ ->
  forall Δ' f,
  renaming (shiftnP #|Γ| P) Σ Γ Δ' f ->
  wf_local Σ (Δ' ,,, rename_context f Δ).
Proof.
  intros. destruct X0.
  induction X using All_local_rel_ind1.
  1: now apply a.
  rw rename_context_snoc /=. apply All_local_env_snoc; auto.
  eapply lift_typing_map with (j := j_decl _) => //.
  eapply X.
  split; auto.
  eapply urenaming_ext.
  { now rw length_app -shiftnP_add. }
  { reflexivity. } now eapply urenaming_context.
Qed.

Lemma rename_decompose_prod_assum f Γ t :
    decompose_prod_assum (rename_context f Γ) (rename (shiftn #|Γ| f) t)
    = let '(Γ, t) := decompose_prod_assum Γ t in (rename_context f Γ, rename (shiftn #|Γ| f) t).
Proof.
  induction t in Γ |- *. all: try reflexivity.
  - specialize (IHt2 (Γ ,, vass na t1)).
    rw rename_context_snoc /= in IHt2.
    simpl. now rw shiftn_add IHt2.
  - specialize (IHt3 (Γ ,, vdef na t1 t2)).
    rw rename_context_snoc /= in IHt3.
    simpl. now rw shiftn_add IHt3.
Qed.

Lemma rename_app_context f Γ Δ :
  rename_context f (Γ ,,, Δ) =
  rename_context f Γ ,,, rename_context (shiftn #|Γ| f) Δ.
Proof.
  rw /rename_context fold_context_k_app /app_context. f_equal.
  apply fold_context_k_ext. intros i x. now rw shiftn_add.
Qed.

Lemma rename_smash_context f Γ Δ :
  rename_context f (smash_context Γ Δ) =
  smash_context (rename_context (shiftn #|Δ| f) Γ) (rename_context f Δ).
Proof.
  induction Δ as [|[na [b|] ty] Δ] in Γ |- *; simpl; auto;
    rw ?shiftn0 // ?rename_context_snoc IHΔ /=; len.
  - f_equal. now rw rename_context_subst /= shiftn_add.
  - f_equal. rw rename_app_context /map_decl /= /app_context.
    f_equal.
    * now rw shiftn_add.
    * rw /rename_context fold_context_k_tip /map_decl /=. do 2 f_equal.
      now rw shiftn0.
Qed.

Lemma nth_error_rename_context f Γ n :
  nth_error (rename_context f Γ) n =
  option_map (map_decl (rename (shiftn (#|Γ| - S n) f))) (nth_error Γ n).
Proof.
  induction Γ in n |- *; intros.
  - simpl. unfold rename_context, fold_context_k; simpl; rw nth_error_nil. easy.
  - simpl. destruct n; rw rename_context_snoc.
    + simpl. lia_f_equal.
    + simpl. rw IHΓ; simpl in *.
      assert (e : #|Γ| - S n = S #|Γ| - S (S n)). { lia. }
      rw e. reflexivity.
Qed.

Lemma rename_check_one_fix f (mfix : mfixpoint term) d x :
  check_one_fix d = Some x ->
  check_one_fix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rw shiftn0. intros ->.
  destruct decompose_prod_assum.
  rw -(rename_smash_context f []).
  destruct nth_error eqn:hnth => //.
  pose proof (nth_error_Some_length hnth). len in H.
  simpl in H.
  destruct (nth_error (List.rev (rename_context _ _)) _) eqn:hnth'.
  2:{ eapply nth_error_None in hnth'. len in hnth'. }
  rw nth_error_rev_inv in hnth; len; auto.
  len in hnth. simpl in hnth.
  rw nth_error_rev_inv in hnth'; len; auto.
  len in hnth'. simpl in hnth'.
  rw nth_error_rename_context /= hnth /= in hnth'. noconf hnth'.
  simpl.
  destruct decompose_app eqn:da. len.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rw da.
  rw rename_mkApps. simpl. rw decompose_app_mkApps //.
Qed.

Lemma rename_check_one_cofix f (mfix : mfixpoint term) d x :
  check_one_cofix d = Some x ->
  check_one_cofix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rw shiftn0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_app eqn:da.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rw da /=.
  rw rename_mkApps. simpl. rw decompose_app_mkApps //.
Qed.

Lemma rename_wf_fixpoint Σ f mfix :
  wf_fixpoint Σ mfix ->
  wf_fixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  unfold wf_fixpoint, wf_fixpoint_gen.
  rw forallb_map.
  move/andP => [] hmfix ho.
  apply/andP; split.
  { eapply forallb_impl; tea. intros. cbn in H0.
    now eapply isLambda_rename. }
  move: ho.
  rw map_map_compose.
  destruct (map_option_out (map check_one_fix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_fix f mfix). }
  now rw hmap.
Qed.

Lemma rename_wf_cofixpoint Σ f mfix :
  wf_cofixpoint Σ mfix ->
  wf_cofixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  rw map_map_compose.
  destruct (map_option_out (map check_one_cofix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_cofix f mfix). }
  now rw hmap.
Qed.

Lemma rename_subst_telescope f s Γ :
  rename_telescope f (subst_telescope s 0 Γ) =
  subst_telescope (map (rename f) s) 0
    (rename_telescope (shiftn #|s| f) Γ).
Proof.
  rw /rename_telescope /subst_telescope.
  rw !mapi_compose. apply mapi_ext => k' d.
  rw !compose_map_decl; apply map_decl_ext => t'.
  now rw Nat.add_0_r rename_subst.
Qed.

Instance rename_telescope_ext : Proper (`≐1` ==> `≐1`) rename_telescope.
Proof.
  intros f g Hfg Γ.
  rw /rename_telescope. apply mapi_ext => n x.
  now rw Hfg.
Qed.

Lemma rename_telescope_shiftn0 f Γ : rename_telescope (shiftn 0 f) Γ = rename_telescope f Γ.
Proof. now sigma. Qed.

Lemma rename_telescope_cons f d Γ :
  rename_telescope f (d :: Γ) = rename_decl f d :: rename_telescope (shiftn 1 f) Γ.
Proof.
  rw /rename_telescope mapi_cons /rename_decl.
  f_equal; sigma => //.
  apply mapi_ext => i x. now rw shiftn_add Nat.add_1_r.
Qed.

Hint Rewrite <- Upn_ren : sigma.

Lemma rename_prim_type f p pty : rename f (prim_type p pty) = prim_type (map_prim (rename f) p) pty.
Proof.
  destruct p as [? []]; cbn; simp prim_type => //.
Qed.

(** For an unconditional renaming defined on all variables in the source context *)
Lemma typing_rename_prop :
  let Pj := (fun Σ Γ j =>
    forall P Δ f,
    renaming (shiftnP #|Γ| P) Σ Γ Δ f ->
    lift_typing (fun Σ Γ t T => Σ ;;; Δ |- rename f t : rename f T) Σ Γ j)
  in
  env_prop
  (fun Σ Γ t A =>
    forall P Δ f,
    renaming (shiftnP #|Γ| P) Σ Γ Δ f ->
    Σ ;;; Δ |- rename f t : rename f A)
  Pj
  (fun Σ Γ => All_local_env (Pj Σ) Γ).
Proof.
  apply typing_ind_env.

  - intros Σ wfΣ Γ j H P Δ f Hr.
    apply lift_typing_impl with (1 := H) => t T [_ IH].
    now eapply IH.

  - intros Σ wfΣ Γ _ _ HΓ. assumption.

  - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ P Δ f hf.
    simpl in *.
    eapply hf in isdecl as h => //.
    2:{ rw /shiftnP. eapply nth_error_Some_length in isdecl. now nat_compare_specs. }
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rw lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto. apply hf.

  - intros Σ wfΣ Γ wfΓ l X H0 P Δ f [hΔ hf].
    simpl. constructor. all: auto.

  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB P Δ f hf.
    assert (lift_typing0 (typing Σ Δ) (j_vass_s na (rename f A) s1)).
    + eapply ihA; eauto.
    + rw /=. econstructor; tas.
      eapply ihB; eauto.
      simpl.
      eapply renaming_extP. { now rw -(shiftnP_add 1). }
      eapply renaming_vass. 2: eauto.
      constructor.
      * destruct hf as [hΔ hf]. assumption.
      * eapply lift_sorting_forget_univ, X0.
  - intros Σ wfΣ Γ wfΓ na A t B X hA ihA ht iht P Δ f hf.
    assert (lift_typing0 (typing Σ Δ) (j_vass na (rename f A))).
    + eapply ihA; eauto.
    + simpl. econstructor; tas.
      eapply iht; eauto; simpl.
      eapply renaming_extP. { now rw -(shiftnP_add 1). }
      eapply renaming_vass. 2: eauto.
      constructor; tas.
      destruct hf as [hΔ hf]. assumption.
  - intros Σ wfΣ Γ wfΓ na b B t A X hbB ihbB ht iht P Δ f hf.
    assert (lift_typing0 (typing Σ Δ) (j_vdef na (rename f b) (rename f B))).
    + eapply ihbB; tea.
    + simpl. econstructor; tas.
      eapply iht; tea.
      eapply renaming_extP. { now rw -(shiftnP_add 1). }
      eapply renaming_vdef. 2: eauto.
      constructor; tas.
      destruct hf as [hΔ hf]. assumption.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu P Δ f hf.
    simpl. eapply meta_conv.
    + eapply type_App.
      * simpl in ihty. eapply ihty; tea.
      * simpl in iht. eapply iht. eassumption.
      * eapply ihu. eassumption.
    + autorewrite with sigma. rw !subst1_inst. sigma.
      eapply inst_ext => i.
      unfold subst_cons, ren, shiftn, subst_compose. simpl.
      destruct i.
      * simpl. reflexivity.
      * simpl. replace (i - 0) with i by lia.
        reflexivity.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst P Δ f hf.
    simpl. eapply meta_conv.
    + constructor. all: eauto. apply hf.
    + rw rename_subst_instance. f_equal.
      rw rename_closed. 2: auto.
      eapply declared_constant_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst P Δ σ hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rw rename_subst_instance. f_equal.
      rw rename_closed. 2: auto.
      eapply declared_inductive_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst P Δ f hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rw rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar eqpctx predctx wfp cup wfpctx Hpret IHpret IHpredctx isallowed Her.
    intros IHctxi Hc IHc iscof ptm wfbrs Hbrs P Δ f Hf.
    simpl.
    rw rename_mkApps.
    rw map_app. simpl.
    rw /ptm. rw rename_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite rename_predicate_preturn.
      rw rename_case_predicate_context //.
      eapply type_Case; eauto; tea; rw - ?rename_case_predicate_context.
      7,10: constructor; eauto; tea; rw - ?rename_case_predicate_context.
      all:tea.
      + simpl. eapply IHpret.
        split.
        ++ apply All_local_env_app_inv in IHpredctx as [].
          eapply wf_local_app_renaming; eauto.
        ++ rw /predctx length_app.
           eapply urenaming_ext.
           { now rw -shiftnP_add. }
           { reflexivity. }
          relativize #|pcontext p|; [eapply urenaming_context|].
          { apply Hf. }
          now rw case_predicate_context_length.
      + simpl. unfold id.
        specialize (IHc _ _ _ Hf).
        now rw rename_mkApps map_app in IHc.
      + now eapply rename_wf_predicate.
      + simpl. eauto.
        apply All_local_env_app_inv in IHpredctx as [].
        eapply wf_local_app_renaming; eauto.
      + revert IHctxi.
        rw /= /id -map_app.
        rw -{2}[subst_instance _ _](rename_closedn_ctx f 0).
        { pose proof (declared_inductive_closed_pars_indices isdecl).
          now rw closedn_subst_instance_context. }
        rw rename_context_telescope.
        rw rename_telescope_shiftn0.
        clear -P Δ f Hf.
        induction 1.
        { constructor; auto. }
        { destruct t0; simpl. rw rename_telescope_cons.
          constructor; cbn; eauto.
          now rw rename_subst_telescope /= in IHIHctxi. }
        { simpl. rw rename_telescope_cons.
          constructor; cbn; eauto.
          now rw rename_subst_telescope /= in IHIHctxi. }
      + now eapply rename_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        intros (Hnth & wfbr & eqbctx & IHbctx & (Hbod & IHbod) & Hbty & IHbty).
        rw -(rename_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        split; auto.
        { simpl. rw -rename_cstr_branch_context //.
          1:eapply (declared_inductive_closed_params isdecl).
          rw rename_closedn_ctx //.
          eapply closed_cstr_branch_context. split; tea. }
        cbn -[case_branch_type].
        rw case_branch_type_fst.
        rw -rename_case_branch_context_gen //.
        2-3:len.
        1:exact (declared_inductive_closed_params isdecl).
        1:rw (wf_branch_length wfbr) //.
        1:rw (wf_predicate_length_pars wfp).
        1:now rw (declared_minductive_ind_npars isdecl).
        set (brctx' := rename_context f _).
        assert (wf_local Σ (Δ ,,, brctx')).
        { apply All_local_env_app_inv in IHbctx as [].
          eapply wf_local_app_renaming; tea. }
        split => //.
        rw rename_case_predicate_context // rename_case_branch_type //.
        split.
        { eapply IHbod => //.
          split => //.
          * eapply urenaming_ext.
          { now rw app_context_length -shiftnP_add. }
          { reflexivity. }
          relativize #|bcontext br|; [eapply urenaming_context|].
          1:apply Hf. rw case_branch_context_length //. }
        { eapply IHbty. split=> //.
          rw /brctx' case_branch_type_fst.
          rw (wf_branch_length wfbr).
          eapply urenaming_ext.
          { now rw app_context_length -shiftnP_add. }
          { reflexivity. }
          rw -(wf_branch_length wfbr).
          rw -/(rename_context f _).
          relativize #|bcontext br|; [eapply urenaming_context, Hf|len].
          now rw case_branch_context_length. }
    * rw /predctx case_predicate_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e
           P Δ f hf.
    simpl. eapply meta_conv.
    + econstructor.
      * eassumption.
      * eapply meta_conv.
        -- eapply ihc; tea.
        -- rw rename_mkApps. simpl. reflexivity.
      * rw length_map. assumption.
    + rw rename_subst0. simpl. rw map_rev. f_equal.
      rw rename_subst_instance. f_equal.
      rw rename_closedn. 2: reflexivity.
      eapply declared_projection_closed_type in isdecl.
      rw List.length_rev. rw e. assumption.

  - intros Σ wfΣ Γ wfΓ mfix n decl types H1 hdecl X hmfixt ihmfixt hmfixb ihmfixb wffix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; tea.
    simpl. eapply meta_conv.
    + eapply type_Fix.
      * apply hf.
      * destruct hf; eapply fix_guard_rename; eauto.
      * rw nth_error_map. rw hdecl. simpl. reflexivity.
      * apply All_map, (All_impl ihmfixt).
        intros x t. eapply t. eauto.
      * apply All_map, (All_impl ihmfixb).
        unfold on_def_body. rw fix_context_length length_map {2}/map_def /=.
        intros x t.
        relativize (lift0 _ _).
        1: eapply t; eauto.
        2: len; now sigma.
        rw rename_fix_context.
        split; auto.
        subst types. rw -(fix_context_length mfix).
        eapply urenaming_ext.
        { now rw app_context_length -shiftnP_add. }
        { reflexivity. }
        apply urenaming_context; auto. apply hf.
      * now eapply rename_wf_fixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types guard hdecl X hmfixt ihmfixt hmfixb ihmfixb wfcofix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; eauto.
    simpl. eapply meta_conv.
    + eapply type_CoFix; auto.
      * apply hf.
      * destruct hf; eapply cofix_guard_rename; eauto.
      * rw nth_error_map. rw hdecl. simpl. reflexivity.
      * apply All_map, (All_impl ihmfixt).
        intros x t. eapply t. eauto.
      * apply All_map, (All_impl ihmfixb).
        unfold on_def_body. rw fix_context_length length_map {2}/map_def /=.
        intros x t.
        relativize (lift0 _ _).
        1: eapply t; eauto.
        2: len; now sigma.
        rw rename_fix_context.
        split; auto.
        subst types. rw -(fix_context_length mfix).
        eapply urenaming_ext.
        { now rw app_context_length -shiftnP_add. }
        { reflexivity. }
        apply urenaming_context; auto. apply hf.
      * now eapply rename_wf_cofixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ p pty cdecl _ hp hdecl pinv ptyp IH P Δ f hf.
    cbn. rw rename_prim_type /=. econstructor; tea.
    * apply hf.
    * rw prim_val_tag_map //.
    * rw prim_val_tag_map //.
    * depelim IH; eauto; cbn; constructor; cbn; eauto. solve_all.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht htB ihB cum P Δ f hf.
    eapply type_Cumul.
    + eapply iht; tea.
    + eapply ihB; tea.
    + eapply cumulSpec_renameP.  all: try eassumption.
      * apply hf.
      * apply wf_local_closed_context; eauto.
      * pose proof (type_closed ht).
        now eapply closedn_on_free_vars in H.
      * pose proof (subject_closed htB).
        now eapply closedn_on_free_vars in H.
      * pose proof (closed_ctx_on_free_vars P _ (closed_wf_local _ (typing_wf_local ht))).
        destruct hf as [HΔ _]. apply wf_local_closed_context; eauto.
Qed.

Lemma typing_rename_P {P Σ Γ Δ f t A} {wfΣ : wf Σ.1} :
  renaming (shiftnP #|Γ| P) Σ Γ Δ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros hf h.
  revert Σ wfΣ Γ t A h P Δ f hf.
  apply typing_rename_prop.
Qed.

Lemma typing_rename {Σ Γ Δ f t A} :
  wf Σ.1 -> wf_local Σ Δ ->
  renaming_closed Γ Δ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros ? ? hf h. eapply (typing_rename_P (P:=fun _ => false)) ; eauto; split; eauto.
Qed.

End Renaming.
