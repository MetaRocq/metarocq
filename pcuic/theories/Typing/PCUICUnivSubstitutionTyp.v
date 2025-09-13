(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICOnFreeVars
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICCases PCUICCumulativity PCUICTyping PCUICReduction PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICClosed PCUICPosition PCUICGuardCondition PCUICUnivSubstitutionConv.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(** * Universe Substitution lemmas for typing derivations. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".

Local Ltac aa := rdest; eauto with univ_subst.

Section SubstIdentity.
  Context `{cf:checker_flags}.

Lemma compare_sort_subst_instance pb {Σ : global_env_ext} univs u :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  RelationClasses.subrelation (compare_sort Σ pb)
    (fun x y : sort =>
    compare_sort (global_ext_constraints (Σ.1, univs)) pb (subst_instance_sort u x)
      (subst_instance_sort u y)).
Proof using Type.
  intros v.
  destruct pb; cbn.
  - now apply eq_sort_subst_instance.
  - now apply leq_sort_subst_instance.
Qed.

Lemma cumulSpec_subst_instance (Σ : global_env_ext) Γ u A B pb univs :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ ⊢ A ≤s[pb] B ->
  (Σ.1,univs) ;;; subst_instance u Γ ⊢ subst_instance u A ≤s[pb] subst_instance u B.
Proof.
  intros e H. unfold cumulSpec.
  induction H; intros; cbn; try solve [econstructor; intuition eauto].
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_lift. eapply cumul_rel.
    unfold subst_instance.
    cbv [option_map subst_instance_context map_context map_decl] in *.
    rewrite nth_error_map; cbv [option_map].
    repeat destruct ?; inversion pf; clear pf; try congruence.
    match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
    subst; cbn.
    reflexivity.
  - rewrite subst_instance_mkApps. cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcotext (map_branch (subst_instance u) br)).
    eapply cumul_iota; eauto with pcuic.
    * rewrite nth_error_map Hbrs //.
    * simpl. now len.
  - rewrite !subst_instance_mkApps. cbn.
    eapply cumul_fix.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
        rewrite nth_error_map E. cbn.
        destruct d. cbn in *. cbn in *; try congruence.
        f_equal. f_equal.
        now rewrite subst_instance_subst fix_subst_instance_subst.
      * congruence.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; try congruence.
      rewrite nth_error_map E; cbn.
      now rewrite isConstruct_app_subst_instance.
  - rewrite !subst_instance_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E; try congruence.
    match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
    eapply cumul_cofix_case.  fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map E. cbn.
    rewrite subst_instance_subst.
    now rewrite cofix_subst_instance_subst.
  - unfold unfold_cofix in *.
    destruct nth_error eqn:E; try congruence.
    match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
    rewrite !subst_instance_mkApps.
    eapply cumul_cofix_proj. fold subst_instance.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
     1: rewrite subst_instance_subst cofix_subst_instance_subst.
    all: now inversion E.
  - rewrite subst_instance_two. solve [econstructor; eauto].
  - rewrite !subst_instance_mkApps.
    eapply cumul_proj. now rewrite nth_error_map Hargs.
  - eapply cumul_Trans; intuition eauto.
    * rewrite on_free_vars_ctx_subst_instance; eauto.
    * rewrite on_free_vars_subst_instance. unfold is_open_term.
      replace #|Γ@[u]| with #|Γ|; eauto. rewrite length_map; eauto.
  - eapply cumul_Evar. eapply All2_map.
    repeat toAll.
    eapply All2_impl.  1: tea. cbn; intros. eapply X0.2; eauto.
  - eapply cumul_Case; try solve [intuition eauto; eauto].
    * cbv [cumul_predicate] in *; destruct_head'_prod. repeat split; eauto; cbn.
      + apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros. destruct_head'_prod; eauto.
      + apply precompose_subst_instance. eapply cmp_universe_instance_impl.
        1:now apply eq_universe_subst_instance.
        eauto.
      + rewrite -> subst_instance_app, inst_case_predicate_context_subst_instance in *.
        eauto.
    * unfold cumul_branches, cumul_branch in *.
      eapply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      repeat split; intuition eauto.
      rewrite -> subst_instance_app, inst_case_branch_context_subst_instance in *; eauto.
  - eapply cumul_Fix. apply All2_map. repeat toAll. eapply All2_impl. 1: tea.
    cbn; intros; intuition eauto.
    rewrite -> subst_instance_app, fix_context_subst_instance in *; eauto.
  - eapply cumul_CoFix. apply All2_map. repeat toAll. eapply All2_impl. 1: tea.
    cbn; intros; intuition eauto.
    rewrite -> subst_instance_app, fix_context_subst_instance in *; eauto.
  - eapply cumul_Prim. depelim e0; depelim X; cbn in H; cbn; noconf H; cbn in H; constructor; cbn -[Universe.make]; eauto.
    + rewrite -!subst_instance_universe_make.
      eapply eq_universe_subst_instance; tea.
    + solve_all.
 - repeat rewrite subst_instance_mkApps. eapply cumul_Ind.
    * apply precompose_subst_instance_global.
      rewrite length_map. eapply cmp_global_instance_impl_same_napp; try eapply H; eauto.
      { now apply eq_universe_subst_instance. }
      { now apply compare_universe_subst_instance. }
    * eapply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      eapply X0.2; eauto.
 - repeat rewrite subst_instance_mkApps. eapply cumul_Construct.
    * apply precompose_subst_instance_global. cbn.
      rewrite length_map. eapply cmp_global_instance_impl_same_napp; try eapply H; eauto.
      { now apply eq_universe_subst_instance. }
      { now apply compare_universe_subst_instance. }
    * eapply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      eapply X0.2; eauto.
  - eapply cumul_Sort. now apply compare_sort_subst_instance.
  - eapply cumul_Const. apply precompose_subst_instance.
    eapply cmp_universe_instance_impl; eauto.
    now apply compare_universe_subst_instance.
Defined.

Lemma convSpec_subst_instance (Σ : global_env_ext) Γ u A B univs :
valid_constraints (global_ext_constraints (Σ.1, univs))
                  (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A =s B ->
  (Σ.1,univs) ;;; subst_instance u Γ |- subst_instance u A =s subst_instance u B.
Proof using Type.
  apply cumulSpec_subst_instance.
Qed.

Lemma conv_decls_subst_instance (Σ : global_env_ext) {Γ Γ'} u univs d d' :
  valid_constraints (global_ext_constraints (Σ.1, univs))
    (subst_instance_cstrs u Σ) ->
  conv_decls cumulSpec0 Σ Γ Γ' d d' ->
  conv_decls cumulSpec0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ')
    (subst_instance u d) (subst_instance u d').
Proof using Type.
  intros valid Hd; depelim Hd; constructor; tas;
    eapply convSpec_subst_instance; tea.
Qed.

Lemma cumul_decls_subst_instance (Σ : global_env_ext) {Γ Γ'} u univs d d' :
  valid_constraints (global_ext_constraints (Σ.1, univs))
    (subst_instance_cstrs u Σ) ->
  cumul_decls cumulSpec0 Σ Γ Γ' d d' ->
  cumul_decls cumulSpec0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ')
    (subst_instance u d) (subst_instance u d').
Proof using Type.
  intros valid Hd; depelim Hd; constructor; tas;
    (eapply convSpec_subst_instance || eapply cumulSpec_subst_instance); tea.
Qed.

Lemma conv_ctx_subst_instance (Σ : global_env_ext) {Γ Γ'} u univs :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  conv_context cumulSpec0 Σ Γ Γ' ->
  conv_context cumulSpec0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ').
Proof using Type.
  intros valid.
  intros; eapply All2_fold_map, All2_fold_impl; tea => ? ? d d'.
  now eapply conv_decls_subst_instance.
Qed.

Lemma subst_instance_ws_cumul_ctx_pb_rel (Σ : global_env_ext) {Γ Γ'} u univs :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  cumul_context cumulSpec0 Σ Γ Γ' ->
  cumul_context cumulSpec0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ').
Proof using Type.
  intros valid.
  intros; eapply All2_fold_map, All2_fold_impl; tea => ? ? d d'.
  now eapply cumul_decls_subst_instance.
Qed.

Lemma subst_instance_prim_type p prim_ty u : (prim_type p prim_ty)@[u] = prim_type (mapu_prim (subst_instance_level u) (subst_instance u) p) prim_ty.
Proof.
  destruct p as [? []]; simp prim_type => //=.
Qed.

Lemma subst_instance_prim_val_tag (p : PCUICPrimitive.prim_val term) u :
  prim_val_tag (mapu_prim (subst_instance_level u) (subst_instance u) p) =
  prim_val_tag p.
Proof.
  destruct p as [? []] => //=.
Qed.

Hint Resolve subst_instance_cstrs_two
     satisfies_equal_sets satisfies_subsets : univ_subst.
Hint Resolve monomorphic_global_constraint monomorphic_global_constraint_ext : univ_subst.
Hint Unfold UCS.For_all : univ_subst.
Hint Resolve consistent_ext_trans : univ_subst.
Hint Resolve consistent_instance_valid_constraints : univ_subst.
Hint Rewrite subst_instance_extended_subst : substu.
Hint Rewrite expand_lets_subst_instance : substu.
Hint Rewrite subst_instance_subst_context subst_instance_lift_context
  subst_instance_lift subst_instance_mkApps
  subst_instance_subst
  subst_instance_it_mkProd_or_LetIn
  subst_instance_it_mkLambda_or_LetIn
  subst_instance_inds
  : substu.
Ltac substu := autorewrite with substu.
Hint Rewrite subst_instance_expand_lets_ctx : substu.
Hint Resolve subst_instance_wf_predicate
  subst_instance_wf_branch subst_instance_wf_branches : pcuic.
Hint Resolve All_local_env_over_subst_instance : univ_subst.
Hint Resolve declared_inductive_wf_ext_wk declared_inductive_wf_global_ext : pcuic.


Lemma typing_subst_instance :
  env_prop (fun Σ Γ t T => forall u univs,
                wf_ext_wk Σ ->
                consistent_instance_ext (Σ.1, univs) Σ.2 u ->
                (Σ.1,univs) ;;; subst_instance u Γ
                |- subst_instance u t : subst_instance u T)
          (fun Σ Γ j => forall u univs,
            wf_ext_wk Σ ->
            consistent_instance_ext (Σ.1, univs) Σ.2 u ->
            lift_typing (fun Σ Γ t T =>
            (Σ.1,univs) ;;; Γ@[u] |- t@[u] : T@[u]) Σ Γ j)
          (fun Σ Γ => forall u univs,
          wf_ext_wk Σ ->
          consistent_instance_ext (Σ.1, univs) Σ.2 u ->
          wf_local(Σ.1,univs) (subst_instance u Γ)).
Proof using Type.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; cbn  -[Universe.make] in *.
  - intros X ????.
    apply lift_typing_impl with (1 := X) => t T [_ IH].
    now eapply IH.
  - rewrite /subst_instance /=.
    intros _; clear wfΓ.
    induction 1 using All_local_env_ind1. 1: constructor.
    intros. simpl.
    apply All_local_env_snoc. 1: now apply IHX.
    eapply lift_typing_mapu with (u := None) => //; auto using relevance_subst_opt.

  - intros n decl eq X u univs wfΣ' H. rewrite subst_instance_lift.
    rewrite map_decl_type. econstructor; aa.
    unfold subst_instance, map_context.
    now rewrite nth_error_map eq.
  - intros l X Hl u univs wfΣ' H.
    rewrite subst_instance_univ_super.
    + econstructor.
      * aa.
      * now apply wf_sort_subst_instance.
  - intros n t0 b s1 s2 X X0 X1 X2 X3 u univs wfΣ' H.
    rewrite product_subst_instance; aa. econstructor.
    + eapply lift_typing_mapu with (tm := None) (u := Some _) => //;
      auto using relevance_subst_opt.
    + eapply X3; eauto.
  - intros n t0 b bty X X0 X1 X2 X3 u univs wfΣ' H.
    econstructor.
    + eapply lift_typing_mapu with (tm := None) (u := None) => //;
      auto using relevance_subst_opt.
    + eapply X3; aa.
  - intros n b b_ty b' b'_ty X X0 X1 X2 X3 u univs wfΣ' H.
    econstructor; eauto.
    + eapply lift_typing_mapu with (tm := Some _) (u := None) => //;
      auto using relevance_subst_opt.
    + eapply X3; aa.
  - intros t0 na A B s u X X0 X1 X2 X3 X4 X5 u0 univs wfΣ' H.
    rewrite subst_instance_subst. cbn. econstructor.
    + eapply X1; eauto.
    + eapply X3; eauto.
    + eapply X5; eauto.
  - intros. rewrite subst_instance_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_trans; eauto.
  - intros. rewrite subst_instance_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_trans; eauto.
  - intros. eapply meta_conv. 1: econstructor; aa.
    clear.
    unfold type_of_constructor; cbn.
    rewrite subst_instance_subst. f_equal.
    + unfold inds. induction #|ind_bodies mdecl|. 1: reflexivity.
      cbn. now rewrite IHn.
    + symmetry; apply subst_instance_two.

  - intros ci p c brs args u mdecl idecl isdecl hΣ hΓ indnp eqpctx wfp cup
      wfpctx pty Hpty Hcpc kelim hrel
      IHctxi Hc IHc notCoFinite wfbrs hbrs i univs wfext cu.
    rewrite subst_instance_mkApps subst_instance_it_mkLambda_or_LetIn map_app.
    cbn.
    change (subst_instance i (preturn p)) with (preturn (subst_instance i p)).
    change (subst_instance i (pcontext p)) with (pcontext (subst_instance i p)).
    change (map_predicate _ _ _ _ _) with (subst_instance i p).
    rewrite subst_instance_case_predicate_context.
    eapply type_Case with (p:=subst_instance i p)
                          (ps:=subst_instance_sort i u); eauto with pcuic.
    3,4: constructor; eauto with pcuic.
    + rewrite -subst_instance_case_predicate_context - !subst_instance_app_ctx.
      eapply Hpty; eauto.
    + eapply IHc in cu => //.
      now rewrite subst_instance_mkApps map_app in cu.
    + simpl. eapply consistent_ext_trans; tea.
    + now rewrite -subst_instance_case_predicate_context -subst_instance_app_ctx.
    + cbn in *.
      eapply is_allowed_elimination_subst_instance; aa.
    + now apply relevance_subst.
    + move: IHctxi. simpl.
      rewrite -subst_instance_app.
      rewrite -subst_instance_two_context.
      rewrite -[List.rev (subst_instance i _)]map_rev.
      clear -wfext cu. induction 1; try destruct t0; cbn; constructor; simpl; eauto.
      all:now rewrite -(subst_instance_subst_telescope i [_]).
    + rewrite -{1}(map_id (ind_ctors idecl)).
      eapply All2i_map. eapply All2i_impl; eauto.
      cbn -[case_branch_type case_branch_context subst_instance].
      intros k cdecl br (hctx & hcbctx & (hbod & ihbod) & hbty & ihbty).
      rewrite case_branch_type_fst.
      rewrite - !subst_instance_case_branch_context - !subst_instance_app_ctx.
      rewrite -subst_instance_case_predicate_context subst_instance_case_branch_type.
      repeat split; [auto..| |].
      * specialize (ihbod i univs wfext cu).
        cbn. eapply ihbod.
      * specialize (ihbty i univs wfext cu).
        cbn. eapply ihbty.
  - intros p c u mdecl idecl cdecl pdecl isdecl args X X0 X1 X2 H u0 univs wfΣ' H0.
    rewrite subst_instance_subst. cbn.
    rewrite !subst_instance_two.
    rewrite {4}/subst_instance /subst_instance_list /=.
    rewrite map_rev.
    econstructor; eauto. 2:now rewrite length_map.
    eapply X2 in H0; tas. rewrite subst_instance_mkApps in H0.
    eassumption.

  - intros mfix n decl H H0 H1 X IHX X0 IHX0 wffix u univs wfΣ'.
    rewrite (map_dtype _ (subst_instance u)). econstructor.
    + specialize (H1 u univs wfΣ' H2).
      rewrite subst_instance_app in H1.
      now eapply All_local_env_app_inv in H1 as [].
    + now eapply fix_guard_subst_instance.
    + rewrite nth_error_map H0. reflexivity.
    + apply All_map, (All_impl IHX); simpl. intros d X1.
      eapply lift_typing_mapu with (tm := None) (u := None); cbn; eauto using relevance_subst_opt.
    + eapply All_map, (All_impl IHX0); simpl. intros d X1.
      unfold map_def at 2, on_def_body. cbn.
      rewrite -fix_context_subst_instance /app_context -(subst_instance_app u (fix_context mfix) Γ) -/(app_context Γ _).
      rewrite -subst_instance_lift length_map.
      eapply lift_typing_mapu with (tm := Some _) (u := None); cbn; eauto using relevance_subst_opt.
    + red; rewrite <- wffix.
      unfold wf_fixpoint, wf_fixpoint_gen.
      f_equal.
      { rewrite forallb_map. solve_all. cbn.
        destruct (dbody x) => //. }
      rewrite map_map_compose.
      now rewrite subst_instance_check_one_fix.

  - intros mfix n decl H H0 H1 X IHX X0 IHX0 wffix u univs wfΣ'.
    rewrite (map_dtype _ (subst_instance u)). econstructor.
    + specialize (H1 u univs wfΣ' H2).
      rewrite subst_instance_app in H1.
      now eapply All_local_env_app_inv in H1 as [].
    + now eapply cofix_guard_subst_instance.
    + rewrite nth_error_map H0. reflexivity.
    + apply All_map, (All_impl IHX); simpl. intros d X1.
      eapply lift_typing_mapu with (tm := None) (u := None); cbn; eauto using relevance_subst_opt.
    + eapply All_map, (All_impl IHX0); simpl. intros d X1.
      unfold map_def at 2, on_def_body. cbn.
      rewrite -fix_context_subst_instance /app_context -(subst_instance_app u (fix_context mfix) Γ) -/(app_context Γ _).
      rewrite -subst_instance_lift length_map.
      eapply lift_typing_mapu with (tm := Some _) (u := None); cbn; eauto using relevance_subst_opt.
    + red; rewrite <- wffix.
      unfold wf_cofixpoint, wf_cofixpoint_gen.
      rewrite map_map_compose.
      now rewrite subst_instance_check_one_cofix.

  - intros.
    rewrite subst_instance_prim_type.
    econstructor.
    + eauto.
    + now rewrite subst_instance_prim_val_tag.
    + exact H0.
    + now rewrite subst_instance_prim_val_tag.
    + destruct p as [? []]; depelim X1; constructor; eauto.
      * rewrite -subst_instance_universe_make. eapply wf_universe_subst_instance => //.
      * cbn -[Universe.make'] in hty.
        specialize (hty u univs).
        rewrite /subst_instance subst_instance_universe_make in hty. now eapply hty.
      * cbn. solve_all.

  - intros t0 A B X X0 X1 X2 X3 X4 cum u univs wfΣ' H.
    econstructor.
    + eapply X2; aa.
    + eapply X4; aa.
    + eapply cumulSpec_subst_instance; aa.
Qed.

Lemma typing_subst_instance' Σ φ Γ t T u univs :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof using Type.
  intros X X0 X1.
  eapply (typing_subst_instance (Σ, univs)); tas. apply X.
Qed.

Lemma typing_subst_instance_wf_local Σ φ Γ u univs :
  wf_ext_wk (Σ, univs) ->
  wf_local (Σ, univs) Γ ->
  consistent_instance_ext (Σ, φ) univs u ->
  wf_local (Σ, φ) (subst_instance u Γ).
Proof using Type.
  intros X X0 X1.
  eapply (env_prop_wf_local typing_subst_instance (Σ, univs)); tas. 1: apply X.
Qed.

Lemma typing_subst_instance'' Σ φ Γ t T u univs :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof using Type.
  intros X X0 X1.
  eapply (typing_subst_instance (Σ, univs)); tas. 1: apply X.
Qed.

Lemma typing_subst_instance_ctx (Σ : global_env_ext) Γ t T ctx u :
  wf Σ.1 ->
  on_udecl_prop Σ (Polymorphic_ctx ctx) ->
  (Σ.1, Polymorphic_ctx ctx) ;;; Γ |- t : T ->
  consistent_instance_ext Σ (Polymorphic_ctx ctx) u ->
  Σ ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1.
  eapply typing_subst_instance''; tea.
  split; tas.
Qed.

Lemma typing_subst_instance_decl Σ Γ t T c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |- t : T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  Σ ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  eapply typing_subst_instance''; tea.
  split; tas.
  eapply weaken_lookup_on_global_env'; tea.
Qed.




Lemma wf_local_instantiate_poly {Σ ctx Γ u} :
  wf_ext (Σ.1, Polymorphic_ctx ctx) ->
  consistent_instance_ext Σ (Polymorphic_ctx ctx) u ->
  wf_local (Σ.1, Polymorphic_ctx ctx) Γ ->
  wf_local Σ (subst_instance u Γ).
Proof using Type.
  intros wfΣ Huniv wf.
  epose proof (type_Sort _ _ sProp wf) as ty. forward ty.
  - now simpl.
  - eapply typing_subst_instance_ctx in ty;
    cbn; eauto using typing_wf_local.
    * apply wfΣ.
    * destruct wfΣ. now eapply on_udecl_on_udecl_prop.
Qed.

Lemma wf_local_instantiate {Σ} {decl : global_decl} {Γ u c} :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_local (Σ.1, universes_decl_of_decl decl) Γ ->
  wf_local Σ (subst_instance u Γ).
Proof using Type.
  intros wfΣ Hdecl Huniv wf.
  epose proof (type_Sort _ _ sProp wf) as ty. forward ty.
  - now simpl.
  - eapply typing_subst_instance_decl in ty;
    cbn; eauto using typing_wf_local.
Qed.

Lemma lift_typing_subst_instance_decl Σ Γ j c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  lift_typing typing (Σ.1, universes_decl_of_decl decl) Γ j ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  lift_typing typing Σ (subst_instance u Γ) {| j_term := option_map (subst_instance u) (j_term j); j_typ := subst_instance u (j_typ j);
                                               j_univ := option_map (subst_instance u) (j_univ j); j_rel := j_rel j |}.
Proof.
  intros wfΣ look Hj cu.
  eapply lift_typing_fu_impl with (1 := Hj) => //; auto using relevance_subst_opt.
  intros ?? Hs; now eapply typing_subst_instance_decl.
Qed.

Lemma isType_subst_instance_decl Σ Γ T c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  isType (Σ.1, universes_decl_of_decl decl) Γ T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  isType Σ (subst_instance u Γ) (subst_instance u T).
Proof using Type.
  apply lift_typing_subst_instance_decl.
Qed.

Lemma isTypeRel_subst_instance_decl Σ Γ T r c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  isTypeRel (Σ.1, universes_decl_of_decl decl) Γ T r ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  isTypeRel Σ (subst_instance u Γ) (subst_instance u T) r.
Proof using Type.
  apply lift_typing_subst_instance_decl.
Qed.

Lemma isArity_subst_instance u T :
  isArity T ->
  isArity (subst_instance u T).
Proof using Type.
  induction T; cbn; intros; tauto.
Qed.

Lemma wf_local_subst_instance Σ Γ ext u :
  wf_global_ext Σ.1 ext ->
  consistent_instance_ext Σ ext u ->
  wf_local (Σ.1, ext) Γ ->
  wf_local Σ (subst_instance u Γ).
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1. simpl in *.
  induction X1; cbn; constructor; auto.
  all: eapply lift_typing_fu_impl with (1 := t0) => //= ?? Hs; auto using relevance_subst_opt.
  all: eapply typing_subst_instance'' in Hs; eauto; apply X.
Qed.

Lemma wf_local_subst_instance_decl Σ Γ c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  wf_local (Σ.1, universes_decl_of_decl decl) Γ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_local Σ (subst_instance u Γ).
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  induction X1; cbn; constructor; auto.
  all: eapply lift_typing_fu_impl with (1 := t0) => // ?? Hs; auto using relevance_subst_opt.
  all: eapply typing_subst_instance_decl in Hs; eauto; apply X.
Qed.

  Lemma isTypeRel_subst_instance_id Σ Γ T r :
    wf_ext_wk Σ ->
    let u := abstract_instance Σ.2 in
    isTypeRel Σ Γ T r -> subst_instance u T = T.
  Proof using Type.
    intros wf_ext u isT.
    destruct isT as (_ & s & Hs & _).
    eapply typed_subst_abstract_instance in Hs; auto.
  Qed.

  Lemma isType_subst_instance_id Σ Γ T :
    wf_ext_wk Σ ->
    let u := abstract_instance Σ.2 in
    isType Σ Γ T -> subst_instance u T = T.
  Proof using Type.
    intros wf_ext u isT.
    destruct isT as (_ & s & Hs & _).
    eapply typed_subst_abstract_instance in Hs; auto.
  Qed.

  Lemma subst_instance_ind_sort_id Σ mdecl ind idecl :
    wf Σ ->
    declared_inductive Σ ind mdecl idecl ->
    let u := abstract_instance (ind_universes mdecl) in
    subst_instance_sort u (ind_sort idecl) = ind_sort idecl.
  Proof using Type.
    intros wfΣ decli u.
    pose proof (on_declared_inductive decli) as [onmind oib].
    pose proof (onArity oib) as ona.
    rewrite (oib.(ind_arity_eq)) in ona.
    apply isTypeRel_subst_instance_id in ona.
    2:split; simpl; auto.
    - rewrite !subst_instance_it_mkProd_or_LetIn in ona.
      eapply (f_equal (destArity [])) in ona.
      rewrite !destArity_it_mkProd_or_LetIn in ona. simpl in ona. noconf ona.
      simpl in H; noconf H. apply H0.
    - destruct decli as [declm _].
      eapply declared_inductive_wf_global_ext in declm; auto.
      destruct declm. apply o.
  Qed.

  Lemma subst_instance_ind_type_id Σ mdecl ind idecl :
    wf Σ ->
    declared_inductive Σ ind mdecl idecl ->
    let u := abstract_instance (ind_universes mdecl) in
    subst_instance u (ind_type idecl) = ind_type idecl.
  Proof using Type.
    intros wfΣ decli u.
    pose proof (on_declared_inductive decli) as [_ oib].
    pose proof (onArity oib) as ona.
    rewrite (oib.(ind_arity_eq)) in ona |- *.
    apply isTypeRel_subst_instance_id in ona; eauto.
    destruct decli as [declm _].
    eapply declared_inductive_wf_global_ext in declm; auto.
  Qed.

End SubstIdentity.
