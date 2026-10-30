(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import RelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICTyping PCUICPosition PCUICUnivSubst
     PCUICNamelessDef PCUICGuardCondition PCUICNamelessConv PCUICConversion
     PCUICWellScopedCumulativity PCUICOnFreeVars PCUICOnFreeVarsConv PCUICConfluence PCUICClosedTyp PCUICClosed
     PCUICSigmaCalculus (* for context manipulations *).
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.

Implicit Types cf : checker_flags.

(** Typing does not rely on name annotations of binders.

  We prove this by constructing a type-preserving translation to
  terms where all binders are anonymous. An alternative would be to
  be parametrically polymorphic everywhere on the binder name type.
  This would allow to add implicit information too. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".


(* Seems unused *)

(*
Lemma nlg_wf_local {cf : checker_flags} :
  forall Σ Γ (hΓ : wf_local Σ Γ),
    All_local_env_over
      typing
      (fun Σ Γ (_ : wf_local Σ Γ) (t T : term) (_ : Σ ;;; Γ |- t : T) =>
         nlg Σ ;;; nlctx Γ |- nl t : nl T)
      Σ Γ hΓ ->
    wf_local (nlg Σ) (nlctx Γ).
Proof.
  intros Σ Γ hΓ h.
  induction h.
  - constructor.
  - simpl. unfold map_decl_anon. cbn. constructor. 1: assumption.
    apply infer_typing_sort_impl with id tu; intros Hty.
    exact Hs.
  - simpl. unfold map_decl_anon. cbn. constructor.
    + assumption.
    + apply infer_typing_sort_impl with id tu; intros Hty. exact Hs.
    + assumption.
Qed.

Lemma nl_check_one_fix d : check_one_fix d = check_one_fix (map_def_anon nl nl d).
Proof.
  destruct d; simpl.
  rewrite (nl_decompose_prod_assum [] dtype).
  destruct decompose_prod_assum.
  rewrite -(nlctx_smash_context []) -map_rev nth_error_map.
  destruct nth_error => //. cbn.
  rewrite [decompose_app_rec _ _]nl_decompose_app.
  destruct decompose_app => //.
  destruct t0 => //.
Qed.

Lemma nl_wf_fixpoint Σ mfix :
  wf_fixpoint Σ.1 mfix = wf_fixpoint (nlg Σ) (map (map_def_anon nl nl) mfix).
Proof.
  unfold wf_fixpoint, wf_fixpoint_gen.
  f_equal.
  { rewrite forallb_map. eapply forallb_ext => x. cbn. destruct (dbody x) => //. }
  replace (map check_one_fix mfix) with (map check_one_fix (map (map_def_anon nl nl) mfix)) => //.
  * destruct map_option_out => //. destruct l => //.
    f_equal. rewrite /check_recursivity_kind.
    epose proof (nl_lookup_env Σ.1).
    destruct Σ; cbn in *. rewrite H.
    destruct lookup_env => //. cbn.
    destruct g0 => //.
  * rewrite map_map_compose.
    now setoid_rewrite <-nl_check_one_fix.
Qed.

Lemma nl_check_one_cofix d : check_one_cofix d = check_one_cofix (map_def_anon nl nl d).
Proof.
  destruct d; simpl.
  rewrite (nl_decompose_prod_assum [] dtype).
  destruct decompose_prod_assum.
  rewrite nl_decompose_app.
  destruct decompose_app => //.
  destruct t0 => //.
Qed.

Lemma nl_wf_cofixpoint Σ mfix :
  wf_cofixpoint Σ.1 mfix = wf_cofixpoint (nlg Σ) (map (map_def_anon nl nl) mfix).
Proof.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  replace (map check_one_cofix mfix) with (map check_one_cofix (map (map_def_anon nl nl) mfix)) => //.
  * destruct map_option_out => //. destruct l => //.
    f_equal. rewrite /check_recursivity_kind.
    epose proof (nl_lookup_env Σ.1).
    destruct Σ; cbn in *. rewrite H.
    destruct lookup_env => //. cbn.
    destruct g0 => //.
  * rewrite map_map_compose.
    now setoid_rewrite <- nl_check_one_cofix.
Qed.

Lemma wf_sort_nl Σ u : wf_sort Σ u -> wf_sort (nlg Σ) u.
Proof.
  destruct u; simpl; auto.
  intros.
  now rewrite nl_global_ext_levels.
Qed.

Lemma nl_wf {cf:checker_flags} (Σ : global_env_ext) :
  wf Σ -> wf (nlg Σ).

Lemma nl_cumulSpec {cf:checker_flags} :
  forall (Σ:global_env_ext) Γ A B, wf Σ ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  Σ ;;; Γ |- A <=s B ->
  nlg Σ ;;; nlctx Γ |- nl A <=s nl B.
Proof.
  intros. eapply (cumulAlgo_cumulSpec (nlg Σ) (pb:=Cumul)).
  eapply into_ws_cumul_pb.
  - eapply nl_cumul. eapply (ws_cumul_pb_forget (pb:=Cumul)).
  unshelve eapply (cumulSpec_cumulAlgo _ _ (exist _ _ ) (exist _ _) (exist _ _)); eauto; cbn.
  - eapply closed_ctx_on_free_vars. apply closed_nlctx.
    rewrite is_closed_ctx_closed; eauto.
  - eapply closedn_on_free_vars. apply closed_nl. rewrite nlctx_length.
    rewrite on_free_vars_closedn; eauto.
  - eapply closedn_on_free_vars. apply closed_nl. rewrite nlctx_length.
    rewrite on_free_vars_closedn; eauto.
  Unshelve. eapply nl_wf; eauto.
Defined.

Lemma typing_nlg {cf : checker_flags} :
  env_prop (fun Σ Γ t T => nlg Σ ;;; nlctx Γ |- nl t : nl T)
    (fun Σ Γ => wf_local (nlg Σ) (nlctx Γ)).
Proof.
  clear.
  apply typing_ind_env; intros; cbn in *;
    rewrite ?nl_lift ?nl_subst ?nl_subst_instance;
    try (econstructor; eauto using nlg_wf_local; fail).
  - induction X; simpl; constructor; auto.
    * now exists (tu.π1).
    * now exists (tu.π1).

  - replace (nl (decl_type decl)) with (decl_type (map_decl_anon nl decl));
      [|destruct decl; reflexivity].
    constructor. 1: eauto using nlg_wf_local.
    unfold nlctx. rewrite nth_error_map. now rewrite H.
  - constructor; eauto using nlg_wf_local.
    now apply wf_sort_nl.
  - replace (nl (cst_type decl)) with (cst_type (map_constant_body nl decl));
      [|destruct decl; reflexivity].
    constructor; eauto using nlg_wf_local.
    + unfold declared_constant in *. now erewrite lookup_env_nlg; tea.
    + red. rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
  - replace (nl (ind_type idecl)) with (ind_type (nl_one_inductive_body idecl));
      [|destruct idecl; reflexivity].
    destruct isdecl as [H1 H2].
    econstructor; eauto using nlg_wf_local. 1: split.
    + eapply lookup_env_nlg in H1. eapply H1.
    + replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
          (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
      rewrite nth_error_map H2. reflexivity.
    + unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
  - cbn.
    rewrite nl_inds.
    eapply type_Construct with (idecl0:=nl_one_inductive_body idecl)
                               (mdecl0:=nl_mutual_inductive_body mdecl)
                               (cdecl0:=nl_constructor_body cdecl);
    eauto using nlg_wf_local.
    + destruct isdecl as [[H1 H2] H3]. repeat split.
      * eapply lookup_env_nlg in H1. eapply H1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map H2. reflexivity.
      * rewrite nth_error_map H3. reflexivity.
    + unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
  - rewrite nl_mkApps map_app nl_it_mkLambda_or_LetIn /predctx nl_case_predicate_context.
    eapply type_Case with  (mdecl0:=nl_mutual_inductive_body mdecl)
                           (idecl0:=nl_one_inductive_body idecl)
                           (p0:=nl_predicate nl p); tea; rewrite - ?nl_case_predicate_context.
    + destruct isdecl as [HH1 HH2]. split.
      * eapply lookup_env_nlg in HH1. eapply HH1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map HH2. reflexivity.
    + simpl. clear -X1. move: X1.
      rewrite /ind_predicate_context.
      intros a; depelim a. rewrite H. simpl.
      constructor; auto.
      * depelim c; constructor; simpl; auto. subst T.
        rewrite nl_mkApps /=. f_equal.
        now rewrite nl_to_extended_list nlctx_app_context nlctx_smash_context nl_expand_lets_ctx.
      * rewrite -nl_expand_lets_ctx. eapply All2_map, (All2_impl a).
        intros ?? []; constructor; subst; auto.
    + destruct H0 as [wfpars wfpctx].
      split; simpl; rewrite ?length_map //.
      clear -wfpctx. depelim wfpctx.
      rewrite nl_forget_types H0 /=.
      simpl. constructor => //.
      eapply Forall2_map; solve_all.
    + simpl. tas.
      unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
    + rewrite -nlctx_app_context. exact X4.
    + now rewrite -nlctx_app_context.
    + now apply nl_is_allowed_elimination.
    + revert X6. simpl.
      rewrite -map_app -nlctx_app_context.
      rewrite -nlctx_subst_instance.
      rewrite -[List.rev (nlctx _)]map_rev.
      clear. induction 1; simpl; constructor; eauto.
      * now rewrite -(nl_subst_telescope [i] 0 Δ).
      * now rewrite -(nl_subst_telescope [b] 0 Δ).
    + now rewrite nl_mkApps map_app in X8.
    + now eapply nl_wf_branches.
    + eapply All2i_map, (All2i_impl X9).
      intros i cdecl br.
      set (cbt := case_branch_type _ _ _ _ _ _ _ _) in *.
      intros (convctx & wfctx & bbodyty & IHbody & bty & IHbty).
      simpl preturn. rewrite -nl_it_mkLambda_or_LetIn.
      cbn -[case_branch_type].
      rewrite nl_case_branch_type.
      rewrite -/cbt. unfold map_pair. cbn.
      repeat split.
      * cbn. rewrite -nl_cstr_branch_context.
        eapply All2_map, (All2_impl convctx).
        intros ??[]; constructor; subst; auto.
      * now rewrite -[_ ++ _]nlctx_app_context.
      * now rewrite - ![_ ++ _]nlctx_app_context.
      * rewrite - ![_ ++ _]nlctx_app_context. eauto.
  - destruct pdecl as [pdecl1 pdecl2]; simpl.
    rewrite map_rev.
    eapply type_Proj with (mdecl0:=nl_mutual_inductive_body mdecl)
                          (idecl0:=nl_one_inductive_body idecl)
                          (cdecl0:=nl_constructor_body cdecl)
                          (pdecl:=(pdecl1, nl pdecl2)).
    + destruct isdecl as [[[H1 H2] H3] [H4 H5]]. repeat split.
      * eapply lookup_env_nlg in H1. eapply H1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map H2. reflexivity.
      * rewrite nth_error_map H3. reflexivity.
      * rewrite nth_error_map H4. reflexivity.
      * assumption.
    + now rewrite nl_mkApps in X2.
    + now rewrite length_map.
  - replace (nl (dtype decl)) with (dtype (map_def_anon nl nl decl));
      [|destruct decl; reflexivity].
    assert (XX: nlctx Γ ,,, fix_context (map (map_def_anon nl nl) mfix)
                = nlctx (Γ ,,, fix_context mfix))
      by now rewrite <- nl_fix_context, <- nlctx_app_context.
    constructor.
    + now eapply fix_guard_nl.
    + now rewrite nth_error_map H0.
    + rewrite nlctx_app_context in X. now eapply All_local_env_app_inv in X.
    + clear -X0.
      apply All_map. eapply All_impl; tea.
      simpl. intros x [s Hs]. now exists s.
    + apply All_map. eapply All_impl; tea.
      simpl. intros [] [s Hs].
      simpl in *; intuition auto.
      * rewrite fix_context_length length_map.
        rewrite fix_context_length in Hs.
        now rewrite -> XX, <- nl_lift.
    + now rewrite <-nl_wf_fixpoint.
  - replace (nl (dtype decl)) with (dtype (map_def_anon nl nl decl));
      [|destruct decl; reflexivity].
    assert (XX: nlctx Γ ,,, fix_context (map (map_def_anon nl nl) mfix)
                = nlctx (Γ ,,, fix_context mfix))
      by now rewrite <- nl_fix_context, <- nlctx_app_context.
    constructor; auto.
    + now apply cofix_guard_nl.
    + now rewrite nth_error_map H0.
    + now rewrite nlctx_app_context in X; apply All_local_env_app_inv in X.
    + clear -X0.
      apply All_map. eapply All_impl; tea.
      simpl. intros x [s Hs]. now exists s.
    + apply All_map. eapply All_impl; tea.
      simpl. intros [] [s Hs].
      simpl in *; intuition auto.
      * rewrite fix_context_length length_map.
        rewrite fix_context_length in Hs.
        now rewrite -> XX, <- nl_lift.
    + now rewrite <-nl_wf_cofixpoint.
  - econstructor; tea.
    apply nl_cumulSpec; eauto.
    + eapply wf_local_closed_context; eauto.
    + eapply closedn_on_free_vars. eapply type_closed; eauto.
    + eapply closedn_on_free_vars. eapply subject_closed; eauto.
Qed.


*)
