(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Erasure Require Import ELiftSubst EGlobalEnv EWcbvEval Extract Prelim
     ESubstitution EArities EDeps ErasureProperties.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICGlobalEnv PCUICAst
  PCUICAstUtils PCUICConversion PCUICSigmaCalculus
  PCUICClosed PCUICClosedTyp
  PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICLiftSubst
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICClassification
  PCUICUnivSubst PCUICViews
  PCUICCumulativity PCUICSafeLemmata
  PCUICArities PCUICInductiveInversion
  PCUICContextConversion PCUICContextConversionTyp
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICValidity
  PCUICContexts PCUICEquality PCUICSpine
  PCUICInductives.
From MetaRocq.PCUIC Require Import PCUICTactics.

From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect.

Local Set Keyed Unification.

Local Existing Instance config.extraction_checker_flags.

(** * Correctness of erasure  *)

Notation "Σ |-p s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.
Notation "Σ ⊢ s ⇓ t" := (EWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

(** ** The correctness proof  *)

#[export] Hint Constructors PCUICWcbvEval.eval erases : core.

Import ssrbool.

Lemma erases_lazy Σ Γ t t' : Σ ;;; Γ |- t ⇝ℇ t' -> EAstUtils.isLazyApp t' -> False.
Proof.
  rewrite /EAstUtils.isLazyApp /EAstUtils.head /EAstUtils.decompose_app.
  generalize (@nil EAst.term) as l; intros l.
  induction 1 in l |- *; cbn => //=.
  eapply IHerases1.
Qed.

Lemma erases_correct (wfl := default_wcbv_flags) Σ t t' v Σ' :
  wf_ext Σ ->
  welltyped Σ [] t ->
  Σ;;; [] |- t ⇝ℇ t' ->
  erases_deps Σ Σ' t' ->
  Σ |-p t ⇓ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ ∥ Σ' ⊢ t' ⇓ v' ∥.
Proof.
  intros wfΣ [T Hty] He Hed H.
  revert T Hty t' He Hed.
  induction H; intros T Hty t' He Hed.
  - assert (Hty' := Hty).
    assert (eval Σ (PCUICAst.tApp f a) res) by eauto.
    eapply inversion_App in Hty as (? & ? & ? & ? & ? & ?).
    invs He.

    + depelim Hed.
      eapply IHeval1 in H4 as (vf' & Hvf' & [He_vf']); eauto.
      eapply IHeval2 in H6 as (vu' & Hvu' & [He_vu']); eauto.
      pose proof (subject_reduction_eval t0 H).
      eapply inversion_Lambda in X0 as (? & h1 & ? & e0).
      apply isTypeRel_isType in h1.
      assert (Σ ;;; [] |- a' : t). {
          eapply subject_reduction_eval; eauto.
          eapply PCUICConversion.ws_cumul_pb_Prod_Prod_inv in e0 as [? e1 e2].
          eapply type_Cumul_alt; tea.
          symmetry in e1.
          eapply ws_cumul_pb_forget in e1.
          now eapply conv_cumul. }
      assert (eqs := type_closed_subst b wfΣ X0).
      invs Hvf'.
      * assert (Σ;;; [] |- PCUICAst.subst1 a' 0 b ⇝ℇ ELiftSubst.subst1 vu' 0 t').
        eapply (erases_subst Σ [] [vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty. eassumption.
        rewrite eqs in H2.
        eapply IHeval3 in H2 as (v' & Hv' & [He_v']).
        -- exists v'. split; eauto.
           constructor.
           econstructor; eauto.
           rewrite ECSubst.closed_subst; auto.
           eapply erases_closed in Hvu'; auto; fvs.
        -- rewrite <-eqs. eapply substitution0; eauto.
        -- eapply erases_deps_subst1; [now eauto|].
           eapply erases_deps_eval in He_vf'; [|now eauto].
           depelim He_vf'.
           assumption.
      * exists EAst.tBox. split.
        eapply Is_type_lambda in X1; eauto. destruct X1. econstructor.
        eapply (is_type_subst Σ [] [vass na _] [] _ [a']) in X1 ; auto.
        cbn in X1.
        eapply Is_type_eval; try assumption.
        eauto. eapply H1. rewrite <-eqs. eassumption.
        all: eauto. econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty.
        eauto. constructor. econstructor. eauto. eauto.
      * auto.
    + exists EAst.tBox. split. 2:constructor; econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
    + auto.
  - assert (Hty' := Hty).
    assert (Σ |-p tLetIn na b0 t b1 ⇓ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & h1 & ? & ?); auto.
    assert (wf_rel : lift_typing0 (typing Σ []) (j_vdef na b0' t)).
    { apply lift_sorting_it_impl_gen with h1 => // HT. eapply subject_reduction_eval; eauto. }
    apply unlift_TermTyp in h1 as h1'.
    invs He.
    + depelim Hed.
      eapply IHeval1 in H6 as (vt1' & Hvt2' & [He_vt1']); eauto.
      assert (Hc : conv_context cumulAlgo_gen Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor. reflexivity.
        eapply PCUICCumulativity.red_conv.
        eapply wcbveval_red; eauto.
        reflexivity.
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x). {
        cbn in *. eapply context_conversion. 3:eauto. all:cbn; eauto.
        econstructor. constructor. assumption.
      }
      assert (Σ;;; [] |- subst1 b0' 0 b1 ⇝ℇ ELiftSubst.subst1 vt1' 0 t2'). {
        eapply (erases_subst Σ [] [vdef na b0' t] [] b1 [b0'] t2'); eauto.
        enough (subslet Σ [] [subst [] 0 b0'] [vdef na b0' t]).
        now rewrite PCUICLiftSubst.subst_empty in X1.
        econstructor. econstructor.
        rewrite !PCUICLiftSubst.subst_empty.
        eapply subject_reduction_eval; eauto.
        eapply erases_context_conversion. 3:eassumption.
        all: cbn; eauto.
        econstructor. constructor. assumption.
      }
      pose proof (subject_reduction_eval h1' H).
      assert (eqs := type_closed_subst b1 _ X1).
      rewrite eqs in H1.
      eapply IHeval2 in H1 as (vres & Hvres & [Hty_vres]); [| |now eauto].
      2:{ rewrite <-eqs. eapply substitution_let; eauto. }
      exists vres. split. eauto. constructor; econstructor; eauto.
      enough (ECSubst.csubst vt1' 0 t2' = ELiftSubst.subst10 vt1' t2') as ->; auto.
      eapply ECSubst.closed_subst. eapply erases_closed in Hvt2'; auto.
      eapply eval_closed. eauto. 2:eauto. now eapply subject_closed in h1'.
    + exists EAst.tBox. split. 2:constructor; econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.

  - assert (Σ |-p tConst c u ⇓ res) by eauto.
    eapply inversion_Const in Hty as (? & ? & ? & ? & ?); [|easy].
    invs He.
    + depelim Hed.
      assert (isdecl' := isdecl). destruct wfΣ as [wfΣ ?].
      unshelve eapply declared_constant_to_gen in H0, d; eauto.
      eapply declared_constant_inj in H0; [|now eauto]; subst.
      unfold erases_constant_body in *. rewrite -> e in *.
      destruct ?; try tauto. cbn in *.
      eapply declared_constant_inj in d; [|now eauto]; subst.
      edestruct IHeval as (? & ? & [?]).
      * cbn in *.
        assert (isdecl'' := isdecl').
        apply declared_constant_from_gen in isdecl', isdecl''.
        eapply declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        2:exact weaken_env_prop_typing.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. eapply unlift_TermTyp in isdecl'.
        unfold declared_constant in isdecl''.
        now eapply @typing_subst_instance_decl with (Σ := Σ) (Γ := []); eauto.
      * assert (isdecl'' := isdecl').
        apply declared_constant_from_gen in isdecl', isdecl''.
        eapply declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. eapply unlift_TermTyp in isdecl'.
        2:exact weaken_env_prop_typing.
        now eapply erases_subst_instance_decl with (Σ := Σ) (Γ := []); eauto.
      * now eauto.
      * exists x0. split; eauto. constructor; econstructor; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. eauto. constructor. econstructor. eauto.

  - assert (Hty' := Hty).
  assert (Σ |-p tCase ci p discr brs ⇓ res) by eauto.
  (* assert (Σ |-p tCase ci p discr brs ⇓ res) by eauto.
 *)
  eapply inversion_Case in Hty' as (mdecl' & idecl' & di & indices & [] & c0); auto.

  rename ci into ind.
  pose proof d as d'. pose proof (wfΣ' := wfΣ.1).
  eapply declared_constructor_inductive in d'.
  unshelve eapply declared_inductive_to_gen in di; eauto.
  edestruct (declared_inductive_inj d' di); subst. clear d'.
  assert (Σ ;;; [] |- mkApps (tConstruct ind c u) args :   mkApps (tInd ind (puinst p)) (pparams p ++ indices)).
  eapply subject_reduction_eval; eauto.
  assert (Hcstr := X0).
  eapply Construct_Ind_ind_eq in X0; tea. 2:{ eapply declared_constructor_from_gen; tea. }
  destruct X0 as (((([_ Ru] & cu) & cpu) & ?) & (parsubst & argsubst & parsubst' & argsubst' & [])).
  invs He.
  + depelim Hed. rename H5 into Hlen.
    rename H1 into decli. rename H2 into decli'.
    rename H3 into em. rename Hed into er.
    rename H6 into H5. rename H7 into H6. rename H8 into H7.
    edestruct (IHeval1 _ scrut_ty) as (v' & Hv' & [He_v']); eauto.
    pose proof e0 as Hnth.
    assert (lenppars : ind_npars mdecl = #|pparams p|).
    { now rewrite (wf_predicate_length_pars wf_pred). }
    unshelve eapply declared_inductive_to_gen in decli; eauto.
    destruct (declared_inductive_inj d.p1 decli); subst mdecl0 idecl0.
    eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
    * subst.
      eapply Is_type_app in X1; auto. destruct X1.
      2:{ rewrite -mkApps_app; tea. }
      rewrite -mkApps_app in X1.

      eapply tConstruct_no_Type in X1; auto.

      eapply H6 in X1 as []; eauto.
      2: eapply declared_inductive_from_gen; eauto.
      2: split; auto; exists []; now destruct Σ.
      destruct (ind_ctors idecl) eqn:hctors.
      { cbn in *. depelim brs_ty. depelim X0. rewrite nth_error_nil // in Hnth. }
      depelim brs_ty. cbn in H1.
      destruct l; cbn in *; try lia.
      depelim brs_ty. depelim X0. depelim X0.
      destruct p1.
      destruct c; cbn in *. noconf Hnth. 2:{ rewrite nth_error_nil // in Hnth. }
      destruct p0 as (? & ? & ? & ?).
      assert (c1 = cdecl).
      { destruct d.
        rewrite hctors /= in H10. now noconf H10. }
      depelim H5.
      subst c1.
      destruct y0 as [n br']; cbn in *.
      rename y into br.
      edestruct IHeval2 as (? & ? & [?]).
      eapply subject_reduction. eauto. exact Hty.
      etransitivity.
      eapply PCUICReduction.red_case_c. eapply wcbveval_red; eauto.
      econstructor. econstructor.
      eauto.
      all:unfold iota_red in *. all:cbn in *.
      { rewrite e2 e1. now f_equal. }
      {
        assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
          unshelve edestruct @on_declared_constructor as (? & ? & ? & []).
          8: eapply declared_constructor_from_gen; exact d. all: eauto.
          pattern br.
          eapply All_nth_error.
          pose proof (d_ := declared_constructor_from_gen d).
          eapply (expand_lets_erasure (p:=p) d_ wf_brs); eauto.
          rewrite hctors; constructor.
          solve_all. constructor.
          instantiate (1 := 0); cbn; eassumption.
        }
        invs H9.
        eapply erases_subst0; eauto.
        rewrite [case_branch_context_gen _ _ _ _ _ _]PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        1:{ unfold app_context. cbn. rewrite app_nil_r.
            eapply (subslet_cstr_branch_context (u:=u)); tea.
            - eapply declared_constructor_from_gen. eauto.
            - rewrite lenppars firstn_app_left // in s0. exact s0.
            - eapply declared_constructor_from_gen in d.
              eapply (declared_constructor_assumption_context d).
            - destruct s3 as [Hs [_ []]].
              rewrite {2}lenppars [firstn _ (pparams p ++ _)]firstn_app_left // in a1.
            - red in wf_brs. rewrite hctors in wf_brs. now depelim wf_brs.
            - rewrite -eq_npars. exact s1. }
        eapply All2_rev.
        rewrite -eq_npars.
        eapply All_All2_flex; tea.
        2:{ instantiate (1 := repeat EAst.tBox #|skipn (ind_npars mdecl) (x ++ x0)|).
            now rewrite repeat_length. }
        intros ? ? ? % repeat_spec. subst.
        constructor.
        now eapply isErasable_Proof. }
      2:{
      exists x2. split; eauto. constructor. eapply eval_iota_sing => //.
      pose proof (EWcbvEval.eval_to_value _ _ He_v').
      let X0 := match goal with H : EWcbvEval.value _ (EAst.mkApps _ _) |- _ => H end in
      eapply value_app_inv in X0. subst. eassumption.
      depelim H2.
      eapply isErasable_Propositional in X0; eauto.
      rewrite -eq_npars.
      erewrite isPropositional_propositional; eauto. now rewrite X0.
      apply declared_inductive_from_gen; eauto.
      invs e. cbn in *.
      rewrite length_map.
      rewrite length_skipn H13 e3 in H11.
      rewrite (@assumption_context_assumptions (bcontext br)) // ?rev_repeat in H11 => //.
      { eapply assumption_context_compare_decls. symmetry in a. exact a.
        rewrite /cstr_branch_context. eapply assumption_context_expand_lets_ctx.
        eapply assumption_context_subst_context.
        eapply declared_constructor_from_gen in d.
        apply (declared_constructor_assumption_context d). }
      rewrite ECSubst.substl_subst //.
      { eapply forallb_repeat. econstructor. }
      replace (ind_npars mdecl + #|bcontext br| - ind_npars mdecl)
      with #|bcontext br| in H11 by lia. eauto.
      }
      depelim H4.
      cbn in H1.
      eapply erases_deps_subst. 2: eauto.
      eapply All_rev. eapply Forall_All.
      eapply All_Forall, All_repeat. econstructor.
    * subst. unfold iota_red in *.
      destruct (All2_nth_error_Some _ _ X0 Hnth) as (? & ? & ? & ?).
      destruct (All2i_nth_error_r _ _ _ _ _ _ brs_ty Hnth) as (? & ? & ? & ? & ? & ?).
      cbn in *. subst.
      assert (declared_constructor Σ (ind, c) mdecl idecl x2).
      { apply declared_constructor_from_gen; split; tea. }
      unshelve eapply declared_constructor_to_gen in H1; eauto.
      destruct (declared_constructor_inj d H1) as [_ [_ <-]]. clear H1.
      edestruct IHeval2 as (? & ? & [?]).
      eapply subject_reduction. eauto. exact Hty.
      etransitivity.
      eapply PCUICReduction.red_case_c. eapply wcbveval_red. eauto.
      eauto. eauto.

      etransitivity. constructor. constructor.
      eauto.
      { rewrite e1 /cstr_arity e3. congruence. }
      unfold iota_red. reflexivity.

      {
        assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
        unshelve edestruct @on_declared_constructor as (? & ? & ? & []).
          8: eapply declared_constructor_from_gen; exact d. all: eauto.
          pattern br.
          eapply All_nth_error. 2: eauto.
          pose proof (d_ := declared_constructor_from_gen d).
          eapply (expand_lets_erasure d_ wf_brs). solve_all.
        }
        eapply erases_subst0; eauto.
        all: try rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        rewrite app_context_nil_l.
        erewrite <-PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        1:{ eapply (subslet_cstr_branch_context (u:=u)); tea.
            - eapply declared_constructor_from_gen; eauto.
            - rewrite lenppars firstn_app_left // in s0. exact s0.
            - apply declared_constructor_from_gen in d.
              eapply (declared_constructor_assumption_context d).
            - destruct s3 as [Hs [_ []]].
              rewrite {2}lenppars [firstn _ (pparams p ++ _)]firstn_app_left // in a1.
            - red in wf_brs. eapply Forall2_All2 in wf_brs.
              eapply All2_nth_error in wf_brs; tea.
            - rewrite -eq_npars. exact s1. }
      eapply All2_rev. eapply All2_skipn.
      eapply Forall2_All2 in H3. eapply All2_impl. exact H3. intros. eauto.
       }

      eapply nth_error_forall in H5; [|now eauto].
      eapply erases_deps_subst; eauto.
      eapply All_rev.
      eapply erases_deps_eval in He_v'; [|now eauto].
      eapply erases_deps_mkApps_inv in He_v' as (? & ?).
      now eapply All_skipn, Forall_All.

      invs H2.
      -- exists x2. split; eauto.
         constructor. econstructor. eauto. eauto. 2:eauto.
         4:{ unfold EGlobalEnv.iota_red.
          rewrite ECSubst.substl_subst //.
          rewrite forallb_rev forallb_skipn //.
          assert (forallb (closedn 0) args).
          { move/eval_closed: H; tea.
            move/(_ (subject_closed scrut_ty)).
            now rewrite closedn_mkApps /=. }
          solve_all. eapply (erases_closed _ []); tea. }
         rewrite -eq_npars.
         erewrite isPropositional_propositional_cstr; eauto.
         move/negbTE: H13 => ->. reflexivity.
         eapply declared_constructor_from_gen; eauto.
         rewrite  -(Forall2_length H3) /= e2 //.
         rewrite length_skipn -(Forall2_length H3) -e6 /= length_map.
         rewrite (All2_length a).
         replace #|cstr_branch_context ind mdecl cdecl|
          with (context_assumptions (cstr_branch_context ind mdecl cdecl)).
         2:{ eapply assumption_context_assumptions.
             apply declared_constructor_from_gen in d.
             eapply (assumption_context_cstr_branch_context d). }
         rewrite e2 /cstr_arity e1 cstr_branch_context_assumptions; lia.
      -- eapply Is_type_app in X1 as []; auto.
         2:{ eapply subject_reduction_eval. 2:eassumption. eauto. }
         assert (ispind : inductive_isprop_and_pars Σ' ind = Some (true, ind_npars mdecl)).
         { erewrite isPropositional_propositional; eauto. f_equal. f_equal.
           eapply isErasable_Propositional; eauto.
          apply declared_inductive_from_gen; eauto. }

         eapply tConstruct_no_Type in X1; auto.
         eapply H6 in X1 as []; eauto.
         2: apply declared_inductive_from_gen; eauto.
         2:reflexivity.

         destruct (ind_ctors idecl) eqn:hctors. cbn in *. destruct c; invs e7.
         destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in *; invs e7.

         (* destruct btys as [ | ? []]; cbn in *; try discriminate. *)
         destruct brs'; invs e4.
         destruct brs; invs Hnth.
         destruct H9.
         depelim brs_ty. depelim brs_ty.
         depelim X0. depelim X0.
         destruct p0 as (? & ? & ? & ?).
         edestruct IHeval2 as (? & ? & [?]).
         eapply subject_reduction. eauto. exact Hty.
         etransitivity.
         eapply PCUICReduction.red_case_c. eapply wcbveval_red. eauto.
         eauto. eauto.
         etransitivity. constructor. constructor. cbn. reflexivity.
         { rewrite e1 /cstr_arity e2 e3 //. }
         eauto.

         {
          assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
            unshelve edestruct @on_declared_constructor as (? & ? & ? & []).
            8: apply declared_constructor_from_gen; exact d. all: eauto.
            pattern br.
            eapply All_nth_error.
            eapply expand_lets_erasure; eauto.
            eapply declared_constructor_from_gen; eauto.
            2: instantiate (1 := 0); cbn; eassumption.
            rewrite hctors. constructor; auto. constructor. }
          destruct p1.
          eapply erases_subst0; eauto.
          - rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
          - rewrite app_context_nil_l.
            eapply subslet_cstr_branch_context. tea.
            eapply declared_constructor_from_gen; eauto.
            exact cu. all:eauto.
            now rewrite lenppars firstn_app_left // in s0.
            eapply declared_constructor_from_gen in d.
            eapply (declared_constructor_assumption_context d).
            destruct s3 as [? [? [eqp _]]].
            rewrite lenppars (firstn_app_left) // in eqp.
            match goal with
            | [ H : ?f (firstn ?n ?ls) ?p |- ?f (firstn ?n' ?ls) ?p ]
              => replace n' with n; first [ exact H | congruence ]
            end.
            move: wf_brs. now rewrite /wf_branches hctors => h; depelim h.
            rewrite -eq_npars. exact s1.
          - eapply All2_rev. cbn.
            rewrite -eq_npars.
            eapply All_All2_flex.
            exact X1.
            intros ? ? -> % repeat_spec.
            intros. econstructor. eapply isErasable_Proof. eauto.
            rewrite repeat_length. reflexivity.
        }

         depelim H5.
         eapply erases_deps_subst; eauto.
         eapply All_rev, All_repeat.
         econstructor.

         exists x. split; eauto.
         constructor.
         destruct x1 as [n br'].
         eapply eval_iota_sing => //.
         pose proof (EWcbvEval.eval_to_value _ _ He_v') as X0.
         apply value_app_inv in X0; subst x0.
         apply He_v'.
         now rewrite -eq_npars.

         cbn in *.

         rewrite ECSubst.substl_subst.
         { eapply forallb_repeat. econstructor. }

         rewrite rev_repeat in H10.

         enough (#|skipn (ind_npars mdecl) args| = #|n|) as <- by eauto.
         edestruct invert_Case_Construct as (? & ? & ? & ?).
         { econstructor. eauto. }
         { eapply subject_reduction. eauto. exact Hty.
           eapply PCUICReduction.red_case_c. eapply wcbveval_red; eauto. }

        rewrite eq_npars. rewrite List.length_skipn e1 /cstr_arity -e2 e3.
        replace (ci_npar ind + context_assumptions (bcontext br) - ci_npar ind)
    with (context_assumptions (bcontext br)) by lia.
        subst n. rewrite length_map.
        rewrite assumption_context_assumptions //.
        eapply assumption_context_compare_decls. symmetry; tea.
        eapply declared_constructor_from_gen in d.
        eapply (assumption_context_cstr_branch_context d).
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval; eauto. constructor. econstructor; eauto.


  - pose (Hty' := Hty).
    pose proof (proj2 (proj2 d)) as eqpars.
    rename e1 into hnth. rename e0 into eargs.
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ? & ?); [|easy].
    pose proof (wfΣ' := wfΣ.1).
    unshelve eapply declared_projection_to_gen in d0; eauto.
    assert (Hpars : p.(proj_npars) = ind_npars x0).
    { destruct (declared_constructor_inj d0.p1 d.p1). now subst. }
    invs He.

    + depelim Hed.
      rename H1 into decli. rename H2 into decli'. rename H4 into er. rename H3 into em. rename H5 into H3.
      eapply IHeval1 in H6 as (vc' & Hvc' & [Hty_vc']); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists EAst.tBox.
        unshelve eapply declared_projection_to_gen in decli; eauto.
        destruct (declared_inductive_inj decli.p1 d.p1) as [<- <-].
        assert (isprop : inductive_isprop_and_pars Σ' p.(proj_ind) = Some (true, ind_npars mdecl)).
        { erewrite isPropositional_propositional; eauto. f_equal. f_equal.
          eapply isErasable_Propositional; eauto.
          eapply declared_inductive_from_gen; exact d. all:eauto. apply decli'. }
        split.
        eapply Is_type_app in X as []; eauto. 2:{ rewrite -mkApps_app. eapply subject_reduction_eval; eauto. }
        rewrite -mkApps_app in X.

        eapply tConstruct_no_Type in X; eauto. eapply H3 in X as [? []]; eauto.
        2:{ eapply declared_inductive_from_gen; exact d. }
        2: split; auto; now exists []; destruct Σ.
        destruct d0 as (? & ? & ?).

        econstructor.
        eapply Is_type_eval; eauto.
        eapply nth_error_all.
        erewrite nth_error_skipn. eassumption.
        eapply All_impl.
        subst. rewrite -eqpars.
        eassumption.
        eapply isErasable_Proof. constructor. eauto.

        eapply eval_proj_prop => //.
        pose proof (EWcbvEval.eval_to_value _ _ Hty_vc') as X0.
        eapply value_app_inv in X0. subst. eassumption.
        now rewrite -eqpars.
      * rename H3 into Hinf.
        assert (lenx5 := Forall2_length H4).
        eapply Forall2_nth_error_Some in H4 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct p.(proj_ind) 0 u) args : mkApps (tInd p.(proj_ind) x) x3).
        eapply subject_reduction_eval; eauto.
        eapply inversion_mkApps in X as (? & ? & ?); eauto.
        eapply Prelim.typing_spine_inv in t1 as []; eauto.
        eapply IHeval2 in H3 as (? & ? & [?]); eauto.
        unshelve eapply declared_projection_to_gen in decli; eauto.
        destruct (declared_projection_inj decli d0) as [? [? []]].
        subst x0 x1 cdecl0 x2.
        destruct (declared_projection_inj d d0) as [? [? []]]; subst mdecl0 idecl0 pdecl0 cdecl.
        invs H2.
        -- exists x9. split; eauto. constructor.
            eapply EWcbvEval.eval_proj; eauto. rewrite -eqpars.
            erewrite isPropositional_propositional_cstr; eauto.
            move/negbTE: H9 => ->. reflexivity.
            eapply declared_constructor_from_gen. apply d0. cbn. eapply decli'. cbn. rewrite -lenx5 //.
            move: eargs. unfold PCUICWcbvEval.cstr_arity; cbn.
            now rewrite -eqpars.
        -- exists EAst.tBox.
          assert (isprop : inductive_isprop_and_pars Σ' p.(proj_ind) = Some (true, ind_npars mdecl)).
          { erewrite isPropositional_propositional; eauto. do 2 f_equal.
            eapply (isErasable_Propositional (args:=[])); eauto.
            eapply declared_inductive_from_gen. apply d. apply decli'. }
          split.
          eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval; [|eauto]; eauto. }

          eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
          2: apply declared_inductive_from_gen; now eapply d. 2:reflexivity. 2:eauto.
          econstructor.
          eapply Is_type_eval; eauto.
          eapply nth_error_all.
          erewrite nth_error_skipn. eassumption. rewrite -eqpars.
          eapply All_impl.
          eassumption.
          eapply isErasable_Proof.
          constructor. eapply eval_proj_prop => //.
          pose proof (EWcbvEval.eval_to_value _ _ Hty_vc') as X0.
          eapply value_app_inv in X0. subst. eassumption.
          now rewrite -eqpars.
        -- eapply erases_deps_eval in Hty_vc'; [|now eauto].
            eapply erases_deps_mkApps_inv in Hty_vc' as (? & ?).
            now eapply nth_error_forall in H1; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. all:eauto. constructor. econstructor. eauto.
  - assert (Hty' := Hty).
    assert (Hunf := H).
    assert (Hcon := H0).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & e0); eauto.
    assert (Ht := t).
    eapply subject_reduction in t. 2:auto. 2:eapply wcbveval_red; eauto.
    assert (HT := t).
    apply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
    assert (Ht1 := t1).
    apply inversion_Fix in t1 as Hfix; auto.
    rename e0 into hcum.
    rename e1 into e.
    destruct Hfix as (? & ? & ? & ? & ? & ? & e1).
    unfold cunfold_fix in e. rewrite e0 in e.
    apply some_inj in e. apply pair_equal_spec in e as [H3 e_fn]. subst.
    depelim He; first last.

    + exists EAst.tBox. split; [|now constructor; constructor].
      econstructor.
      eapply Is_type_eval. 3:eapply X. eauto.
      eapply eval_fix; eauto.
      rewrite /cunfold_fix e0 //. now rewrite H3.
    + depelim Hed.
      eapply IHeval1 in He1 as (er_stuck_v & er_stuck & [ev_stuck]); eauto.
      eapply IHeval2 in He2 as (er_argv & er_arg & [ev_arg]); eauto.
      eapply erases_mkApps_inv in er_stuck; eauto.
      destruct er_stuck as [(? & ? & ? & -> & ? & ? & ? & ->)|
                            (? & ? & -> & ? & ?)].
      { exists E.tBox.
        eapply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
        cbn in *.
        split; [|constructor; eauto].
        2:{ eapply (eval_box_apps _ _ [_]); eauto. }
        destruct H2.
        eapply (Is_type_app _ _ _ (x5 ++ [av])) in X as []; eauto; first last.
        - rewrite -mkApps_app app_assoc mkApps_snoc.
          eapply PCUICValidity.type_App'; eauto.
          eapply subject_reduction; eauto.
          eapply wcbveval_red; eauto.
        - eapply erases_box.
          eapply Is_type_eval; auto. 2:eauto.
          rewrite mkApps_app /=.
          eapply eval_fix.
          rewrite -mkApps_app. eapply value_final.
          eapply eval_to_value; eauto.
          eapply value_final, eval_to_value; eauto.
          rewrite /cunfold_fix e0 //. auto.
          now rewrite H3. auto. }

      invs H2.
      * assert (Hmfix' := X).
        eapply All2_nth_error_Some in X as (? & ? & ?); eauto.
        pose proof (closed_fix_substl_subst_eq (subject_closed t1) e0) as cls.
        destruct x3. cbn in *. subst.

        enough (Σ;;; [] ,,, subst_context (fix_subst mfix) 0 []
                |- subst (fix_subst mfix) 0 dbody
                ⇝ℇ ELiftSubst.subst (EGlobalEnv.fix_subst mfix') 0 (Extract.E.dbody x4)).
        destruct a2.

        rename e3 into eargsv.
        -- rename x5 into L.
           eapply (erases_mkApps _ _ _ _ (argsv ++ [av])) in H2; first last.
           { eapply Forall2_app.
             - exact H4.
             - eauto. }
           rewrite mkApps_app in H2.
           rewrite EAstUtils.mkApps_app in H2.
           cbn in *. simpl in H2.
          rewrite cls in H2.
          eapply IHeval3 in H2 as (? & ? & [?]); cbn; eauto; cycle 1.
           { eapply subject_reduction. eauto. exact Hty.
             etransitivity.
             eapply PCUICReduction.red_app. eapply wcbveval_red; eauto.
             eapply wcbveval_red; eauto.
             rewrite <- !mkApps_snoc.
             eapply PCUICReduction.red1_red.
             eapply PCUICReduction.red_fix.
             rewrite closed_unfold_fix_cunfold_eq.
             now eapply subject_closed in t1.
             rewrite /cunfold_fix e0 /= //.
             pose proof (eval_to_value _ _ _ H) as vfix.
             eapply PCUICWcbvEval.stuck_fix_value_args in vfix; eauto.
             2:{ rewrite /cunfold_fix e0 //. }
             simpl in vfix.
             subst. unfold is_constructor.
             rewrite nth_error_snoc. lia.
             assert(Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : subst [av] 0 x1).
             { rewrite mkApps_app. eapply PCUICValidity.type_App'; eauto.
               eapply subject_reduction_eval; eauto. }
             epose proof (fix_app_is_constructor (args:=argsv ++ [av]) X).
             rewrite /unfold_fix e0 in X0.
             specialize (X0 eq_refl). simpl in X0.
             rewrite nth_error_snoc in X0. auto. apply X0.
             eapply value_axiom_free, eval_to_value; eauto.
             eapply value_whnf; eauto.
             eapply eval_closed; eauto. now eapply subject_closed in t0.
             eapply eval_to_value; eauto. }

           { constructor.
             - eapply erases_deps_eval in ev_stuck; [|now eauto].
               eapply erases_deps_mkApps_inv in ev_stuck as (? & ?).
               apply erases_deps_mkApps; [|now eauto].
               depelim H3.
               eapply nth_error_forall in H3 as H'; eauto.
               apply erases_deps_subst; [|now eauto].
               now apply Forall_All, Forall_erases_deps_fix_subst; eauto.
             - now eapply erases_deps_eval in ev_arg; eauto. }

           exists x3. split. eauto.
           constructor. eapply EWcbvEval.eval_fix.
           ++ eauto.
           ++ eauto.
           ++ eauto.
           ++ rewrite <- EWcbvEval.closed_unfold_fix_cunfold_eq.
              { unfold EGlobalEnv.unfold_fix. rewrite e.
                eapply All2_nth_error in Hmfix' as []; tea. cbn in *.
                rewrite -eargsv -(Forall2_length H4); trea. }
              eapply eval_closed in H; eauto.
              clear -H Hmfix'. rename H into e3.
              pose proof (All2_length Hmfix').
              rewrite closedn_mkApps in e3.
              apply andb_true_iff in e3 as (e3 & _).
              change (?a = true) with (is_true a) in e3.
              simpl in e3 |- *. solve_all.
              rewrite app_context_nil_l in b.
              destruct b as [eqb eqrar isl isl' e].
              eapply erases_closed in e. simpl in e.
              rewrite <- H.
              unfold EAst.test_def.
              simpl in e.
              rewrite fix_context_length in e.
              now rewrite Nat.add_0_r.
              unfold test_def in a. apply andb_and in a as [_ Hbod].
              rewrite fix_context_length.
              now rewrite Nat.add_0_r in Hbod.
              eauto with pcuic.
              now eapply subject_closed in Ht.
          ++ auto.

        -- cbn. destruct a2 as [eqb eqrar isl isl' e5].
           eapply (erases_subst Σ [] (fix_context mfix) [] dbody (fix_subst mfix)) in e5; cbn; eauto.
           ++ eapply subslet_fix_subst. now eapply wf_ext_wf. all: eassumption.
           ++ eapply nth_error_all in a1; eauto. cbn in a1.
              eapply a1.
           ++ eapply All2_from_nth_error.
              erewrite fix_subst_length, EGlobalEnv.fix_subst_length, All2_length; eauto.
              intros.
              rewrite fix_subst_nth in H3. now rewrite fix_subst_length in H2.
              rewrite efix_subst_nth in H5. rewrite fix_subst_length in H2.
              erewrite <- All2_length; eauto.
              invs H5; invs H3.
              erewrite All2_length; eauto.
      * eapply (Is_type_app _ _ _ (argsv ++ [av])) in X as []; tas.
        -- exists EAst.tBox.
           split.
           ++ econstructor.
              eapply Is_type_eval. 3:eauto. all:eauto.
              rewrite mkApps_app.
              eapply eval_fix; eauto.
              1-2:eapply value_final, eval_to_value; eauto.
              rewrite /cunfold_fix e0 //. congruence.
           ++ constructor. eapply EWcbvEval.eval_box; [|now eauto].
              apply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
              eauto.
        -- eauto.
        -- rewrite mkApps_snoc.
           eapply PCUICValidity.type_App'; eauto.
           eapply subject_reduction; eauto.
           eapply wcbveval_red; eauto.

  - apply inversion_App in Hty as Hty'; [|eauto].
    destruct Hty' as (? & ? & ? & ? & ? & ?).

    eapply subject_reduction in t as typ_stuck_fix; [|eauto|]; first last.
    { eapply wcbveval_red; eauto. }

    eapply erases_App in He as [(-> & [])|(? & ? & -> & ? & ?)].
    + exists E.tBox.
      split; [|now constructor; eauto using @EWcbvEval.eval].
      constructor.
      eapply Is_type_red.
      * eauto.
      * eapply PCUICReduction.red_app.
        -- eapply wcbveval_red; revgoals; eauto.
        -- eapply wcbveval_red; revgoals; eauto.
      * eauto.
    + depelim Hed.
      eapply subject_reduction in t0 as typ_arg; [|eauto|]; first last.
      { eapply wcbveval_red; revgoals; eauto. }

      eapply IHeval1 in H1 as (? & ? & [?]); [|now eauto|now eauto].
      eapply IHeval2 in H2 as (? & ? & [?]); [|now eauto|now eauto].
      eapply erases_mkApps_inv in H1.
      destruct H1 as [(? & ? & ? & -> & [] & ? & ? & ->)|(? & ? & -> & ? & ?)].
      * apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
        depelim H5.
        rewrite -> !app_nil_r in *.
        cbn in *.
        exists E.tBox.
        split; [|now constructor; eauto using @EWcbvEval.eval].
        eapply (Is_type_app _ _ _ [av]) in X as [].
        -- constructor.
           apply X.
        -- eauto.
        -- eauto.
        -- cbn.
           eapply PCUICValidity.type_App'; eauto.
      * depelim H1.
        -- exists (E.tApp (E.mkApps (E.tFix mfix' idx) x7) x5).
           split; [eauto using erases_tApp, erases_mkApps|].
           unfold cunfold_fix in *.
           destruct (nth_error _ _) eqn:nth; [|congruence].
           eapply All2_nth_error_Some in X as (?&?&[? ? ? ? ?]); [|eauto].
           constructor. eapply EWcbvEval.eval_fix_value.
           ++ eauto.
           ++ eauto.
           ++ eauto.
           ++ unfold EGlobalEnv.cunfold_fix. now rewrite e.
           ++ eapply Forall2_length in H5. noconf e1. lia.

        -- exists E.tBox.
           apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
           split; [|now constructor; eauto using @EWcbvEval.eval].
           eapply Is_type_app in X as [].
           ++ constructor.
              rewrite <- mkApps_snoc.
              exact X.
           ++ eauto.
           ++ eauto.
           ++ rewrite mkApps_snoc.
              eapply PCUICValidity.type_App'; eauto.

  - assert (Hty' := Hty).
    eapply inversion_Case in Hty' as [mdecl [idecl [decli [args' [[] ht0]]]]]; auto.
    assert (t0' := scrut_ty).
    pose proof H as Heval.
    eapply subject_reduction_eval in t0' as t1. 2: eauto.
    eapply PCUICValidity.inversion_mkApps in t1 as (? & ? & ?); eauto.
    pose proof (subject_closed t) as clfix.
    assert (htcof : Σ ;;; [] |- tCase ip p (mkApps (tCoFix mfix idx) args) brs : T).
    { eapply subject_reduction; eauto. eapply PCUICReduction.red_case_c.
      eapply wcbveval_red in H; eauto. }
    assert (hredcasecof :
      PCUICReduction.red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
        (tCase ip p (mkApps fn args) brs)).
    { constructor; eapply PCUICReduction.red_cofix_case.
        move: e. rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    assert (htcasefn : Σ ;;; [] |- tCase ip p (mkApps fn args) brs : T).
    { eapply subject_reduction; eauto. }
    assert (hredcasediscrcof :
      PCUICReduction.red Σ [] (tCase ip p discr brs) res).
    { etransitivity. eapply PCUICReduction.red_case_c; tea.
      eapply wcbveval_red in H. tea. eauto.
      etransitivity; tea. eapply wcbveval_red; tea. }
    assert (htunfcof : Σ ;;; [] |- tCase ip p (mkApps fn args) brs : T).
    { eapply subject_reduction; eauto. }
    specialize (IHeval1 _ t0').
    specialize (IHeval2 _ htunfcof).
    eapply inversion_CoFix in t; destruct_sigma t; auto.
    pose proof (wfΣ' := wfΣ.1).
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    2:{ now eapply nth_error_all, isTypeRel_isType in a; tea. }
    invs He.
    * edestruct IHeval1 as (? & ? & ?); eauto. now depelim Hed.
      depelim Hed. rename H5 into Hlen.
      rename H6 into H5. rename H7 into H6. rename H8 into H7.
      rename H9 into H8. rename H10 into H9.
      unshelve eapply declared_inductive_to_gen in H1, decli; eauto.
      destruct (declared_inductive_inj H1 decli). subst mdecl0 idecl0.
      rename H0 into decli'. rename H1 into decli''. rename H2 into er. rename H3 into H0.
      eapply erases_mkApps_inv in H8; eauto.
      destruct H8 as [He|He]; destruct_sigma He.
      -- destruct He as (? & ? & ? & ? & ? & ? & ? & ?). subst.
        destruct H9.
        edestruct IHeval2 as (? & ? & [?]).
        { destruct H2 as [i1]. constructor; eauto.
          rewrite mkApps_app.
          eapply erases_mkApps. instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply tCoFix_no_Type in i1; auto.
          pose proof i1 as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          eapply unfold_cofix_type; eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e0.
          intros e; eapply e. eauto. }
        { destruct (declared_inductive_inj decli'' decli); subst.
          econstructor; eauto.
          eapply declared_inductive_from_gen; eauto.  }
        destruct H2.
        eapply tCoFix_no_Type in X0; auto.
        move: (eval_to_mkApps_tBox_inv _ _ H1). intros ->. depelim H8.
        rewrite -> app_nil_r in *.
        exists x0; split; [|constructor]; auto.
        eapply eval_case_eval_inv_discr; tea.
      -- destruct H9.
        destruct He as [f' [L' [-> [hcof hl']]]].
        have clfix' : ELiftSubst.closed f'.
        { now eapply erases_closed in hcof; tea. }
        depelim hcof.
        { eapply All2_nth_error_Some in X0 as X'; tea.
          destruct X' as [t' [nth' [bn [rar eb]]]].
          specialize (IHeval2 (E.tCase (ip, ci_npar ip)
            (E.mkApps (ELiftSubst.subst0 (EGlobalEnv.cofix_subst mfix') (E.dbody t')) L') brs')).
          forward IHeval2.
          econstructor; eauto.
          eapply erases_mkApps.
          move: e0 e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth.
          intros Heq. apply some_inj in Heq.
          apply pair_equal_spec in Heq as [Hnarg Hfn].
          subst fn narg.
          eapply All_nth_error in a0 as a'; tea. apply unlift_TermTyp in a'.
          eapply erases_subst0. eauto. 2:eauto. pcuic. all:tea.
          { rewrite app_context_nil_l. eapply subslet_cofix_subst; eauto.
            econstructor; eauto. }
          {eapply All2_from_nth_error.
            erewrite cofix_subst_length, EGlobalEnv.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H3. now rewrite cofix_subst_length in H2.
            rewrite ecofix_subst_nth in H8. rewrite cofix_subst_length in H2.
            erewrite <- All2_length; eauto.
            invs H3; invs H8.
            erewrite All2_length; eauto. }
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            apply declared_inductive_from_gen; eauto.
            eapply erases_deps_eval in Hed. 2:tea.
            apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
            depelim edcofix.
            apply erases_deps_mkApps; [|now eauto].
            apply erases_deps_subst.
            - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
            - now eapply nth_error_forall in H2; eauto. }
          exists v'. split => //. split.
          eapply EWcbvEval.eval_cofix_case; tea.
          rewrite /EGlobalEnv.cunfold_cofix nth' //. f_equal.
          f_equal.
          rewrite -(EWcbvEval.closed_cofix_substl_subst_eq (idx:=idx)) //. }
        { eapply eval_to_mkApps_tBox_inv in H1 as H'; subst L'; cbn in *. depelim hl'.
          edestruct IHeval1 as (? & ? & [?]); tea.
          pose proof (EWcbvEval.eval_deterministic H1 H3). subst x0.
          eapply erases_deps_eval in Hed; tea.
          specialize (IHeval2 (E.tCase (ip, ci_npar ip) E.tBox brs')).
          forward IHeval2.
          econstructor; eauto. cbn.
          move: e0 e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth.
          intros Heq. apply some_inj in Heq.
          apply pair_equal_spec in Heq as [Hnarg Hfn].
          subst fn narg.
          constructor.
          eapply isErasable_unfold_cofix; tea.
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            apply declared_inductive_from_gen; eauto. }
          exists v'. split => //. split.
          eapply eval_case_eval_inv_discr; tea. }

    * depelim Hed.
      exists E.tBox. split; repeat constructor; auto.
      assert (PCUICReduction.red Σ [] (tCase ip p discr brs) res).
      eapply wcbveval_red in Heval; tea.
      solve [eapply isErasable_red; tea].

  - assert (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & ? & [] & ? & ? & ? & e0 & e1); auto.
    pose proof (t0' := t).
    pose proof (subject_closed t) as cldiscr.
    assert(clcof : PCUICAst.closedn 0 (mkApps (tCoFix mfix idx) args)).
    { eapply eval_closed; tea; eauto. }
    move: clcof; rewrite closedn_mkApps => /andP[] clcofix clargs.
    eapply subject_reduction_eval in t as t0''; tea.
    eapply inversion_mkApps in t0'' as (? & ? & ?).
    eapply type_tCoFix_inv in t0 as t1'; eauto.
    destruct_sigma t1'; auto.
    eapply inversion_CoFix in t0; destruct_sigma t0.
    destruct p0 as [[hnth wfcof] hdef].
    eapply PCUICSpine.typing_spine_strengthen in t1; eauto.
    2:{ now eapply validity. }
    assert(Hty' := Hty).
    eapply subject_reduction in Hty'. 2:auto.
    2:{ etransitivity. eapply PCUICReduction.red_proj_c.
        eapply wcbveval_red; tea.
        constructor. eapply PCUICReduction.red_cofix_proj. eauto.
        rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    specialize (IHeval2 _ Hty').
    specialize (IHeval1 _ t).
    pose proof (wfΣ' := wfΣ.1).
    invs He.
    * depelim Hed.
      unshelve eapply declared_projection_to_gen in d, H1; eauto.
      destruct (declared_projection_inj d H1) as [? [? []]]. subst x0 x1 x2 pdecl.
      rename H1 into decli. rename H2 into decli'.
      rename H3 into erm. rename H4 into erb.
      destruct (IHeval1 _ H6 Hed) as [dv' [? []]].
      eapply erases_mkApps_inv in H1 as []; eauto.
      { destruct H1 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
        destruct H3.
        eapply eval_to_mkApps_tBox_inv in H2 as H'. subst. depelim H7.
        edestruct IHeval2 as (? & ? & [?]).
        { constructor; eauto.
          instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply tCoFix_no_Type in X; auto.
          pose proof X as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
          intros Heq. apply some_inj in Heq.
          apply pair_equal_spec in Heq as [<- <-].
          eapply unfold_cofix_type; eauto.
          2:{ unfold unfold_cofix; erewrite e2. reflexivity. }
          now rewrite app_nil_r. }
        { eapply erases_deps_eval in Hed. 2:tea.
          apply erases_deps_mkApps_inv in Hed as (_ & edargs).
          econstructor; eauto.
          apply declared_projection_from_gen; eauto.
          constructor. }
        exists x1; split; [|constructor]; auto.
        eapply eval_proj_eval_inv_discr; tea. }
      { destruct H1 as [f' [L' [-> [hcof hl']]]].
        have clfix' : ELiftSubst.closed f'.
        { now eapply erases_closed in hcof; tea. }
        depelim hcof.
        { eapply All2_nth_error_Some in X as X'; tea.
          destruct X' as [t' [nth' [bn [rar eb]]]].
          specialize (IHeval2 (E.tProj p
            (E.mkApps (ELiftSubst.subst0 (EGlobalEnv.cofix_subst mfix') (E.dbody t')) L'))).
          forward IHeval2.
          econstructor; eauto.
          eapply erases_mkApps.
          move: hnth e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth'; rewrite hnth'.
          intros Heq. apply some_inj in Heq.
          apply pair_equal_spec in Heq as [Hnarg Hfn].
          subst fn narg. rewrite hnth' in e2. noconf e2.
          eapply All_nth_error in a0 as a'; tea. eapply unlift_TermTyp in a'.
          eapply erases_subst0. eauto. 2:eauto. pcuic. all:tea.
          { rewrite app_context_nil_l. eapply subslet_cofix_subst; eauto.
            econstructor; eauto. }
          {eapply All2_from_nth_error.
            erewrite cofix_subst_length, EGlobalEnv.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H3. now rewrite cofix_subst_length in H1.
            rewrite ecofix_subst_nth in H4. rewrite cofix_subst_length in H1.
            erewrite <- All2_length; eauto.
            invs H3; invs H4.
            erewrite All2_length; eauto. }
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            eapply declared_projection_from_gen; eauto.
            eapply erases_deps_eval in Hed. 2:tea.
            apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
            depelim edcofix.
            apply erases_deps_mkApps; [|now eauto].
            apply erases_deps_subst.
            - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
            - now eapply nth_error_forall in H1; eauto. }
          exists v'. split => //. split.
          eapply EWcbvEval.eval_cofix_proj; tea.
          rewrite /EGlobalEnv.cunfold_cofix nth' //. f_equal.
          f_equal.
          rewrite -(EWcbvEval.closed_cofix_substl_subst_eq (idx:=idx)) //. }
        { eapply eval_to_mkApps_tBox_inv in H2 as H'; subst L'; cbn in *. depelim hl'.
          edestruct IHeval1 as (? & ? & [?]); tea.
          pose proof (EWcbvEval.eval_deterministic H3 H2). subst x0.
          eapply erases_deps_eval in Hed; tea.
          specialize (IHeval2 (E.tProj p E.tBox)).
          forward IHeval2.
          econstructor; eauto. cbn.
          move: hnth e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth.
          intros Heq. apply some_inj in Heq.
          apply pair_equal_spec in Heq as [Hnarg Hfn].
          subst fn narg.
          constructor.
          eapply isErasable_unfold_cofix; tea.
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            eapply declared_projection_from_gen; eauto. }
          exists v'. split => //. split.
          eapply eval_proj_eval_inv_discr; tea. }
      }

    * depelim Hed.
      exists E.tBox. split; repeat constructor; auto.
      assert (PCUICReduction.red Σ [] (tProj p discr) res).
      eapply wcbveval_red in H0; tea.
      etransitivity; tea.
      etransitivity. eapply PCUICReduction.red_proj_c.
      eapply wcbveval_red; tea.
      constructor. eapply PCUICReduction.red_cofix_proj.
      move: e. rewrite closed_unfold_cofix_cunfold_eq //. intros e; exact e.
      now eapply isErasable_red.

    * eauto.

  - pose (Hty' := Hty).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    invs He.
    + depelim Hed.
      assert (t' := t). eapply IHeval1 in t as (? & ? & [?]); eauto.
      eapply IHeval2 in t0 as (? & ? & [?]); eauto.
      destruct (EAstUtils.isBox x2) eqn:E.
      * destruct x2; invs E. exists EAst.tBox. split. 2: now constructor; econstructor; eauto.
        pose proof (Is_type_app Σ [] (mkApps (tConstruct ind c u) args) [a']).
        inversion H1.
        edestruct H7; eauto. cbn. eapply subject_reduction. eauto.
        exact Hty. eapply PCUICReduction.red_app.
        eapply wcbveval_red; eauto.
        eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; eauto.
        eapply wcbveval_red; eauto. constructor. rewrite mkApps_app //.
      * exists (E.tApp x2 x3).
        rewrite mkApps_app.
        split; [econstructor; eauto|].
        eapply erases_mkApps_inv in H1; eauto.
        destruct H1 as [].
        { destruct H1 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
          eapply eval_to_mkApps_tBox_inv in H2 as H'. subst. depelim H9.
          now cbn in E. }
        destruct H1 as [f'' [L' [eq []]]].
        subst x2.
        depelim H1.
        2:{ eapply eval_to_mkApps_tBox_inv in H2 as H'. subst. now cbn in E. }
        eapply erases_deps_eval in Hed1; tea.
        eapply erases_deps_mkApps_inv in Hed1 as [].
        depelim H8.
        constructor. eapply EWcbvEval.eval_construct; tea. eauto.
        eapply (EGlobalEnv.declared_constructor_lookup H9).
        rewrite -(Forall2_length H7).
        rewrite /EAst.cstr_arity.
        pose proof (wfΣ' := wfΣ.1).
        unshelve eapply declared_constructor_to_gen in H8; eauto.
        destruct (declared_constructor_inj H8 d) as [? []]. subst mdecl0 idecl0 cdecl0.
        destruct H8, H9, H11 as [Hc _].
        eapply Forall2_nth_error_Some in Hc as [? []]; tea.
        rewrite H14 in H11. noconf H11.
        destruct cdecl' as [cname cargs]; cbn. cbn in *.
        destruct H15 as [<- _].
        destruct H10 as [_ <-].
        move: l. rewrite /cstr_arity.
        clear -d wfΣ.
        eapply declared_constructor_from_gen in d.
        destruct (on_declared_constructor d) as [_ [? []]].
        eapply cstr_args_length in o. lia.
    + exists E.tBox. split => //. 2:repeat constructor.
      econstructor.
      eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
      eapply Is_type_red. 3:eauto. eauto.
      rewrite mkApps_app.
      eapply PCUICReduction.red_app.
      eapply subject_closed in Hf; auto.
      eapply wcbveval_red; eauto.
      eapply subject_closed in Ha; auto.
      eapply wcbveval_red; eauto.

  - pose (Hty' := Hty).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    invs He.
    + depelim Hed.
      assert (t' := t). eapply IHeval1 in t as (? & ? & [?]); eauto.
      eapply IHeval2 in t0 as (? & ? & [?]); eauto.
      destruct (EAstUtils.isBox x2) eqn:E.
      * destruct x2; invs E. exists EAst.tBox. split. 2: now constructor; econstructor; eauto.
        pose proof (Is_type_app Σ [] f' [a']).
        inversion H1.
        edestruct H7; eauto. cbn. eapply subject_reduction. eauto.
        exact Hty. eapply PCUICReduction.red_app.
        eapply wcbveval_red; eauto.
        eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; eauto.
        eapply wcbveval_red; eauto.
      * exists (E.tApp x2 x3).
        split; [econstructor; eauto|].
        constructor; eapply EWcbvEval.eval_app_cong; eauto.
        eapply ssrbool.negbT.
        repeat eapply orb_false_intro.
        -- destruct x2; try reflexivity.
          invs H1. invs i.
        -- destruct x2 eqn:Ex; try reflexivity.
          ++ cbn. invs H1. cbn in *.
            eapply ssrbool.negbTE, is_FixApp_erases.
            econstructor; eauto.
            rewrite orb_false_r !negb_or in i.
            now move/andP: i => [] /andP [].
          ++ cbn in *.
            invs H1. invs i.
        -- eauto.
        -- rewrite !negb_or in i.
           rtoProp; intuition auto.
           eapply is_ConstructApp_erases in H9; tea.
           now move/negbTE: H9.
        -- rewrite !negb_or in i. rtoProp; intuition auto.
           eapply is_PrimApp_erases in H8; tea.
           now move/negbTE: H8.
        -- rewrite !negb_or in i.
           rtoProp; intuition auto.
           apply/negbTE. apply PCUICNormal.negb_is_true => isl.
           eapply erases_lazy in H1; tea.
    + exists EAst.tBox. split. 2: now constructor; econstructor.
      econstructor.
      eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
      eapply Is_type_red. 3:eauto. eauto.
      eapply PCUICReduction.red_app.
      eapply subject_closed in Hf; auto.
      eapply wcbveval_red; eauto.
      eapply subject_closed in Ha; auto.
      eapply wcbveval_red; eauto.

  - depelim X; (depelim He; try depelim H; [|now eapply nisErasable_tPrim in X]).
    + exists (EAst.tPrim (EPrimitive.prim_int i)); split => //; repeat constructor.
      depelim X. constructor.
    + exists (EAst.tPrim (EPrimitive.prim_float f)); split => //; repeat constructor.
      depelim X. constructor.
    + exists (EAst.tPrim (EPrimitive.prim_string s)); split => //; repeat constructor.
      depelim X. constructor.
    + depelim X. subst a0 a'; cbn in *.
      depelim Hed; cbn in *.
      eapply inversion_Prim in Hty as [prim_ty [cdecl []]]; cbn in *; eauto.
      depelim p0; cbn in *. eapply e in hdef as [d' [er [e'v]]]; tea.
      eapply All2_undep in a.
      eapply (All2_apply ty) in a.
      assert (exists ev, ∥ All3 (fun x y z => erases Σ [] x z /\ ∥ Σ' ⊢ y ⇓ z ∥) v' ev0 ev ∥).
      { clear -a a2 H hvalue.
        solve_all.
        induction a in ev0, a2 |- *; depelim a2.
        + exists []; repeat constructor.
        + destruct (IHa _ a2) as [x0 [hx0]]. destruct p as [[] ?].
          specialize (r t _ e e0) as [v' []].
          exists (v' :: x0). sq. repeat constructor; intuition eauto. }
      destruct H0 as [evr [Hevr]].
      exists (EAst.tPrim (EPrimitive.prim_array {| EPrimitive.array_default := d'; EPrimitive.array_value := evr |})); split => //; eauto.
      repeat constructor; eauto.
      * clear -Hevr; induction Hevr; constructor; intuition eauto.
      * clear -Hevr e'v; induction Hevr. repeat constructor; eauto.
        destruct r; sq. constructor; intuition eauto. constructor; eauto. depelim IHHevr. depelim e. constructor; eauto. now cbn in i.

  - destruct t; try easy.
    + invs He. eexists. split; eauto. now constructor; econstructor.
    + invs He. eexists. split; eauto. now constructor; econstructor.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split. 2:{ constructor. eapply EWcbvEval.eval_atom. cbn [EWcbvEval.atom].
        depelim Hed. eapply EGlobalEnv.declared_constructor_lookup in H0. now rewrite H0. }
        econstructor; eauto.
      * eexists. split. 2: now constructor; econstructor.
        eauto.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
        Unshelve. all: repeat econstructor.
Qed.

(* Print Assumptions erases_correct. *)

Lemma erases_global_closed_env {Σ : global_env} Σ' : wf Σ -> erases_global Σ Σ' -> closed_env Σ'.
Proof.
  destruct Σ as [univs Σ]; cbn in *.
  intros [onu wf] er; cbn in *.
  move: wf. red in er; cbn in er.
  induction er; intros wf.
  - constructor.
  - cbn. destruct cb' as [[]].
    cbn in *. depelim wf. destruct o.
    rewrite [forallb _ _](IHer wf) andb_true_r.
    red in H. destruct cb as [ty []]; cbn in *. apply unlift_TermTyp in on_global_decl_d.
    unshelve eapply PCUICClosedTyp.subject_closed in on_global_decl_d. cbn. split; auto.
    eapply erases_closed in H; tea. elim H.
    cbn. apply IHer. now depelim wf.
  - depelim wf.
    cbn. apply IHer, wf.
Qed.

Lemma erases_global_decls_fresh univs retro {Σ : global_declarations} kn Σ' : fresh_global kn Σ ->
  erases_global_decls univs retro Σ Σ' -> EGlobalEnv.fresh_global kn Σ'.
Proof.
  induction 2; constructor; eauto; now depelim H.
Qed.

Import EWellformed.

Lemma erases_mutual_inductive_body_wf (efl := all_env_flags) {Σ univs retro Σ' kn mib mib'} :
  erases_mutual_inductive_body mib mib' ->
  let udecl := PCUICLookup.universes_decl_of_decl (InductiveDecl mib) in
  on_global_decl cumulSpec0 (PCUICEnvTyping.lift_typing typing)
    ({| universes := univs; declarations := Σ; retroknowledge := retro |}, udecl) kn
       (InductiveDecl mib) ->
  wf_global_decl Σ' (E.InductiveDecl mib').
Proof.
  intros [] udecl [].
  cbn. unfold wf_minductive => /=. cbn. clear -H onInductives.
  repeat toAll.
  revert H. subst udecl.
  generalize (E.ind_bodies mib').
  induction onInductives; intros l a; depelim a; constructor; eauto.
  destruct e. unfold wf_inductive, wf_projections.
  destruct H0 as [Hprojs _].
  depelim Hprojs. rewrite H1 => //.
  rewrite H2.
  pose proof (onProjections p) as X.
  rewrite H1 in X.
  destruct (ind_ctors hd) as [|ctor []] eqn:hctors ; edestruct X => //.
  clear X.
  depelim H. rewrite H1.
  depelim H0. cbn.
  destruct H. rewrite -H.
  rewrite H3 in on_projs_all. cbn in on_projs_all.
  eapply Forall2_length in Hprojs. rewrite Hprojs in on_projs_all.
  rewrite on_projs_all.
  pose proof (onConstructors p).
  rewrite hctors in X. red in X.
  depelim X. destruct o. rewrite cstr_args_length.
  apply eqb_refl.
Qed.

Lemma erases_global_wf_glob {Σ : global_env} Σ' : wf Σ -> erases_global Σ Σ' -> @wf_glob all_env_flags Σ'.
Proof.
  destruct Σ as [univs Σ]; cbn in *.
  intros [onu wf] er; cbn in *.
  move: wf. red in er; cbn in er.
  induction er; intros wf.
  - constructor.
  - cbn. depelim wf. destruct o.
    constructor; eauto.
    2:eapply erases_global_decls_fresh; tea.
    cbn. red in H.
    do 2 red in on_global_decl_d.
    destruct (cst_body cb).
    eapply unlift_TermTyp in on_global_decl_d.
    destruct (E.cst_body cb') => //. cbn.
    set (Σ'' := ({| universes := _ |}, _)) in *.
    assert (PCUICTyping.wf_ext Σ'').
    { split => //. }
    epose proof (erases_wellformed (Σ:=Σ'') (Γ := []) (a:=t)).
    forward H0. now eexists.
    specialize (H0 H Σ'). eapply H0.
    eapply erases_global_all_deps; tea. split => //.
    destruct (E.cst_body cb') => //.
  - depelim wf. destruct o.
    constructor; eauto.
    now eapply erases_mutual_inductive_body_wf.
    now eapply erases_global_decls_fresh; tea.
Qed.


Import PCUICAst.

Lemma declared_constructor_arity {cf : checker_flags} {Σ c mdecl idecl cdecl} {wf : wf Σ} :
  PCUICAst.declared_constructor Σ c mdecl idecl cdecl ->
  context_assumptions (cstr_args cdecl) = cstr_arity cdecl.
Proof.
  intros hd.
  destruct (PCUICWeakeningEnvTyp.on_declared_constructor hd) as [[onmind onind] [cu []]].
  now eapply cstr_args_length in o.
Qed.

From MetaRocq.PCUIC Require Import PCUICEtaExpand.
From MetaRocq.Erasure Require Import EDeps EEtaExpandedFix.
Local Hint Constructors expanded : core.

Lemma expanded_erases (cf := config.extraction_checker_flags) {Σ : global_env_ext} Σ' Γ Γ' t v :
  wf Σ ->
  Σ ;;; Γ |- t ⇝ℇ v ->
  PCUICEtaExpand.expanded Σ.1 Γ' t ->
  erases_deps Σ Σ' v ->
  EEtaExpandedFix.expanded Σ' Γ' v.
Proof.
  intros wfΣ he exp etaΣ.
  revert Γ v etaΣ he.
  induction exp using PCUICEtaExpand.expanded_ind; cbn.
  all:try solve [intros Γ0 v etaΣ hv; depelim hv; try depelim etaΣ; constructor; solve_all].
  - move=> Γ0 etaΣ v /erases_mkApps_inv; intros [(?&?&?&?&?&?&?&?)|(?&?&?&?&?)]; subst.
    * constructor => //.
      eapply EDeps.erases_deps_mkApps_inv in v as [].
      repeat All_Forall.toAll. eapply All_app in H1 as [].
      solve_all.
    * eapply EDeps.erases_deps_mkApps_inv in v as [].
      depelim H4; simp_eta => //.
      + eapply expanded_tRel_app; tea. now rewrite -(Forall2_length H5).
        eapply Forall_All in H2. eapply Forall2_All2 in H5. solve_all.
      + constructor => //. solve_all.
  - intros Γ0 v etaΣ.
    move=> /erases_mkApps_inv; intros [(?&?&?&?&?&?&?&?)|(?&?&?&?&?)]; subst.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      constructor => //.
      eapply Forall_All in H1. eapply Forall2_All2 in H5.
      eapply All_app in H1 as []. solve_all.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      specialize (IHexp _ _ H2 H3).
      constructor => //.
      clear -H H3. destruct H3; cbn in *; congruence.
      solve_all.
  - intros Γ0 v etaΣ hv; depelim hv; try constructor.
    depelim etaΣ.
    eauto.
    depelim etaΣ.
    solve_all. rewrite -b2. len. eapply H8 => //.
    exact a0.
  - intros Γ0 v etaΣ.
    move=> /erases_mkApps_inv; intros [(?&?&?&?&_&?&?&?)|(?&?&?&?&?)]; subst.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      constructor => //.
      eapply Forall_All in H2. eapply Forall2_All2 in H8.
      eapply All_app in H2 as []. solve_all.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      depelim H7; simp_eta => //.
      + eapply All2_nth_error_Some in H4; tea. destruct H4 as [? [? []]]; tea.
        assert (rev_map (fun d1 : def term => S (rarg d1)) mfix = rev_map (fun d1 => S (EAst.rarg d1)) mfix').
        { rewrite !rev_map_spec. f_equal. clear -X. induction X; cbn; auto. destruct r as [eqb eqrar isl isl' e].
          rewrite eqrar IHX //. }
        depelim H6.
        eapply EEtaExpandedFix.expanded_tFix; tea.
        ++ cbn. rewrite -H6. solve_all. apply b0.
          eapply b1 => //. eapply b0.
        ++ solve_all.
        ++ intros hx0. subst x0. depelim H8 => //.
        ++ now rewrite -(Forall2_length H8) -e1.
      + constructor => //; solve_all.
  - intros Γ0 v etaΣ hv. depelim hv. depelim etaΣ.
    constructor => //. rewrite -(All2_length X). solve_all. constructor.
  - intros Γ0 v etaΣ.
    move=> /erases_mkApps_inv; intros [(?&?&?&?&_&?&?&?)|(?&?&?&?&?)]; subst.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      constructor => //.
      eapply Forall_All in H2. eapply Forall2_All2 in H5.
      eapply All_app in H2 as []. solve_all.
    * depelim H4; simp_eta => //.
      + eapply erases_deps_mkApps_inv in etaΣ as [].
        depelim H4.
        destruct cdecl'.
        eapply EEtaExpandedFix.expanded_tConstruct_app; tea.
        ++ cbn. rewrite -(Forall2_length H5).
          pose proof (H_ := H).
          unshelve eapply declared_constructor_to_gen in H, H4; eauto.
          destruct (PCUICGlobalEnv.declared_constructor_inj H H4) as [? []]. subst idecl0 mind cdecl0.
          rewrite (declared_constructor_arity H_) in H0.
          destruct H7. rewrite -H10.
          destruct H8 as [? _].
          eapply Forall2_nth_error_left in H8. 2:apply H.
          destruct H8 as [[i' n'] [hnth heq]].
          cbn in hnth.
          rewrite (proj2 H6) in hnth. noconf hnth.
          destruct heq. cbn in *. congruence.
        ++ solve_all.
        + constructor => //.
          eapply erases_deps_mkApps_inv in etaΣ as [].
          solve_all.
  - intros Γ0 v etaΣ er.
    depelim er; eauto. depelim H1.
    depelim H0. 1-3:depelim X; repeat constructor.
    depelim X0. eapply expanded_tPrim. constructor; split => //; cbn.
    eapply H0; tea. now depelim etaΣ; cbn in *.
    eapply Forall_All. depelim etaΣ. cbn in *.
    solve_all.
Qed.
