(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICTyping PCUICWeakeningConv PCUICWeakeningTyp PCUICCases
     PCUICCumulativity PCUICReduction
     PCUICParallelReduction PCUICEquality PCUICUnivSubstitutionConv
     PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextReduction PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICGuardCondition PCUICConversion PCUICContextConversion PCUICClosedTyp.

From Stdlib Require Import CRelationClasses ssreflect ssrbool.
From Equations Require Import Equations.

Arguments red_ctx : clear implicits.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Local Ltac intuition_solver ::= auto with *.

Lemma lift0_open {cf:checker_flags} {Γ : closed_context} {Γ'' : open_context Γ}
  {M : open_term Γ} {n} :
  n = #|Γ''| -> is_open_term (Γ ,,, Γ'') (lift0 n M).
Proof.
  intro e. rw on_free_vars_lift0; eauto. rw length_app. rewrite <- shiftnP_add.
  subst. rw addnP_shiftnP; intuition.
Defined.

Lemma weakening_cumulSpec0 {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : closed_context} {Γ'' : open_context Γ}
  {M N : open_term Γ} n :
  n = #|Γ''| ->
  Σ ;;; Γ |- M <=s N ->
  Σ ;;; Γ ,,, Γ'' |- lift0 n M <=s lift0 n N.
Proof.
  intros e H.
  eapply (@cumulAlgo_cumulSpec _ _ Cumul).
  eapply into_ws_cumul_pb; try  apply lift0_open; eauto.
  - cbn. eapply weakening_cumul0; eauto. apply cumulSpec_cumulAlgo in H; eauto. exact (ws_cumul_pb_forget H).
  - cbn. rw on_free_vars_ctx_app; solve_all; intuition.
Defined.

Lemma split_closed_context {Γ : context} (n : nat) :
  is_closed_context Γ ->
  n <= #|Γ| ->
  ∑ (Δ : closed_context) (Δ' : open_context Δ),
    [× Δ = skipn n Γ :> context, Δ' = firstn n Γ :> context,
       Γ = Δ ,,, Δ' & n = #|Δ'|].
Proof.
  rw -{1}(firstn_skipn n Γ).
  rw on_free_vars_ctx_app => /andP[] sk fi.
  exists (exist (skipn n Γ) sk).
  exists (exist (firstn n Γ) fi). split; auto.
  cbn. now rw firstn_skipn. cbn.
  rw List.length_firstn. lia.
Qed.

Lemma nth_error_closed_context {Γ n d} :
  is_closed_context Γ ->
  nth_error Γ n = Some d ->
  ws_decl (skipn (S n) Γ) d.
Proof.
  rw -on_free_vars_ctx_on_ctx_free_vars -[shiftnP _ _]addnP0 => hΔ' hnth.
  eapply nth_error_on_free_vars_ctx in hΔ'; tea.
  2:{ rw /shiftnP /= orb_false_r. apply Nat.ltb_lt. now apply nth_error_Some_length in hnth. }
  rw List.length_skipn.
  eapply on_free_vars_decl_impl; tea.
  intros i.
  rw /= /addnP /shiftnP /= !orb_false_r => /Nat.ltb_lt hl.
  apply Nat.ltb_lt. lia.
Qed.

Lemma on_free_vars_decl_lift (p : nat -> bool) n k t :
  on_free_vars_decl (strengthenP k n p) (lift_decl n k t) = on_free_vars_decl p t.
Proof.
  rw /on_free_vars_decl /test_decl /=.
  f_equal. destruct (decl_body t) => /= //.
  all:now rw on_free_vars_lift.
Qed.

Lemma on_free_vars_decl_lift_impl (p : nat -> bool) n k d :
  on_free_vars_decl (shiftnP k p) d ->
  on_free_vars_decl (shiftnP (n + k) p) (lift_decl n k d).
Proof.
  rw /on_free_vars_decl /test_decl /= => /andP[].
  destruct (decl_body d) => /= //.
  move/(on_free_vars_lift_impl _ n) ->.
  move/(on_free_vars_lift_impl _ n) -> => //.
  move=> _.
  move/(on_free_vars_lift_impl _ n) -> => //.
Qed.

Lemma nth_error_Some_add {A} (l : list A) (n : nat) (x : A) :
  (nth_error l n = Some x) <~>
  (n < #|l| × nth_error l n = Some x).
Proof.
  split. intros hnth; split => //.
  now eapply nth_error_Some_length in hnth.
  now intros [].
Qed.

Lemma nth_error_closed_context_lift {Γ n d} :
  is_closed_context Γ ->
  nth_error Γ n = Some d ->
  ws_decl Γ (lift_decl (S n) 0 d).
Proof.
  move=> cl /nth_error_Some_add[] hn /(nth_error_closed_context cl).
  rw -(on_free_vars_decl_lift _ (S n) 0 d).
  apply: on_free_vars_decl_impl => i.
  rw /strengthenP /= /shiftnP !orb_false_r List.length_skipn.
  repeat PCUICSigmaCalculus.nat_compare_specs => //.
Qed.

Lemma wt_cum_ws_cumul_pb {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {t A B : term} {s} :
  Σ ;;; Γ |- t : A ->
  Σ ;;; Γ |- B : tSort s ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ ⊢ A ≤ B.
Proof.
  move=> a; move: a (typing_wf_local a).
  move/PCUICClosedTyp.type_closed/(@closedn_on_free_vars xpred0) => clA.
  move/wf_local_closed_context => clΓ.
  move/PCUICClosedTyp.subject_closed/(@closedn_on_free_vars xpred0) => clB cum.
  now apply into_ws_cumul_pb.
Qed.

Lemma wt_cum_ws_cumul_ctx_pb {cf:checker_flags} {Σ:global_env_ext} {wfΣ : wf Σ} {Γ Δ : context} pb :
  wf_local Σ Γ ->
  wf_local Σ Δ ->
  cumul_pb_context cumulAlgo_gen pb Σ Γ Δ ->
  Σ ⊢ Γ ≤[pb] Δ.
Proof.
  move/wf_local_closed_context => wfΓ.
  move/wf_local_closed_context => wfΔ.
  now eapply into_ws_cumul_ctx_pb.
Qed.

Lemma All2_conv_over_refl {cf:checker_flags} {Σ : global_env_ext} {Γ Γ' Δ} :
  All2_fold (All_over (conv_decls cumulAlgo_gen Σ) Γ Γ') Δ Δ.
Proof.
  eapply All2_fold_refl. intros ? ?; reflexivity.
Qed.

Lemma All2_cumul_over_refl {cf:checker_flags} {Σ : global_env_ext} {Γ Γ' Δ} :
  All2_fold (All_over (cumul_decls cumulAlgo_gen Σ) Γ Γ') Δ Δ.
Proof.
  eapply All2_fold_refl. intros ? ?; reflexivity.
Qed.

Lemma eq_context_cumul_Spec {cf:checker_flags} Σ pb Γ Δ :
  compare_context Σ pb Γ Δ -> PCUICCumulativitySpec.cumul_pb_context cumulSpec0 pb Σ Γ Δ.
Proof.
  intros e.
  eapply All2_fold_impl. 1: tea. cbn; intros.
  destruct X.
  - econstructor 1; eauto. eapply eq_term_upto_univ_cumulSpec; eauto.
  - econstructor 2; eauto.
    all: eapply eq_term_upto_univ_cumulSpec; eauto.
Defined.

Lemma eq_context_cumul_Spec_rel {cf:checker_flags} Σ Ξ0 Γ Δ :
  compare_context Σ Cumul Γ Δ -> cumul_ctx_rel cumulSpec0 Σ Ξ0 Γ Δ.
Proof.
  intros e.
  eapply All2_fold_impl. 1: tea. cbn; intros.
  destruct X.
  - econstructor 1; eauto. eapply eq_term_upto_univ_cumulSpec; eauto.
  - econstructor 2; eauto.
    all: eapply eq_term_upto_univ_cumulSpec; eauto.
Defined.

Lemma cumul_context_Algo_Spec {cf:checker_flags} Σ pb Γ' Γ :
  Σ ⊢ Γ' ≤[pb] Γ -> PCUICCumulativitySpec.cumul_pb_context cumulSpec0 pb Σ Γ' Γ.
Proof.
  intros e.
  eapply All2_fold_impl. 1: tea. cbn; intros.
  destruct X.
  - econstructor 1; eauto. eapply cumulAlgo_cumulSpec; eauto.
  - econstructor 2; eauto.
    all: eapply cumulAlgo_cumulSpec; eauto.
Defined.

Lemma context_cumulativity_prop {cf:checker_flags} :
  env_prop
    (fun Σ Γ t T =>
       forall Γ', cumul_context cumulAlgo_gen Σ Γ' Γ -> wf_local Σ Γ' -> Σ ;;; Γ' |- t : T)
    (fun Σ Γ j =>
       forall Γ', cumul_context cumulAlgo_gen Σ Γ' Γ -> wf_local Σ Γ' -> lift_typing0 (fun t T => Σ ;;; Γ' |- t : T) j)
    (fun Σ Γ =>
    All_local_env (fun Γ j =>
       forall Γ' : context, cumul_context cumulAlgo_gen Σ Γ' Γ -> wf_local Σ Γ' ->
       (lift_typing0 (fun t T => Σ;;; Γ' |- t : T) j)) Γ).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps;
    try solve [econstructor; eauto].

  - apply lift_typing_impl with (1 := X) => ?? [_ IH].
    now apply IH.

  - assumption.

  - pose proof heq_nth_error.
    eapply (All2_fold_nth_r X0) in H as [d' [Hnth [Hrel Hconv]]].
    eapply All_local_env_nth_error in X; tea.
    red in X. specialize (X _ Hrel).
    forward X by now eapply All_local_env_skipn.
    destruct X as (_ & s & Hty & _).
    eapply type_Cumul with _ s.
    * econstructor. auto. eauto.
    * rw -(firstn_skipn (S n) Γ').
      change (tSort s) with (lift0 (S n) (tSort s)).
      eapply weakening_length. auto.
      rw firstn_length_le. eapply nth_error_Some_length in Hnth. lia. auto.
      now rw /app_context firstn_skipn.
      assumption.
    * destruct (split_closed_context (S n) (wf_local_closed_context X1)) as [Δ [Δ' [eqΔ eqΔ' -> hn]]].
      eapply nth_error_Some_length in Hnth. lia.
      rw -eqΔ in Hty, Hrel.
      eapply PCUICClosedTyp.subject_closed in Hty.
      eapply (@closedn_on_free_vars xpred0) in Hty.
      assert (is_open_term Δ (decl_type d') × cumulAlgo Σ Δ (decl_type d') (decl_type decl)) as [H H']. {
        eapply nth_error_closed_context in Hnth. 2: eauto with fvs.
        rw -eqΔ in Hnth.
        depelim Hconv; simpl in *.
        all: rw -eqΔ in eqt.
        all: now move/andP: Hnth => [].
      }
      eapply (weakening_cumulSpec0 (Γ := Δ) (Γ'' := Δ') (M := exist (decl_type d') H) (N := exist (decl_type decl) Hty)); cbn. lia.
      unshelve eapply (@cumulAlgo_cumulSpec _ _ Cumul). apply into_ws_cumul_pb; eauto.
      now intuition.
  - constructor; pcuic.
    eapply forall_Γ'0; constructor; pcuic. eapply lift_sorting_forget_univ. now eapply forall_Γ'.
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
  - econstructor; eauto. 2,3: constructor; eauto.
    * eapply IHp0. rw /predctx.
      eapply All2_fold_app => //.
      eapply All2_fold_refl. intros ? ?; reflexivity.
      eapply context_cumulativity_wf_app; tea.
    * eapply context_cumulativity_wf_app; tea.
    * revert X5.
      clear -Γ' X9 X10. induction 1; constructor; eauto. now destruct t0.
    * eapply All2i_impl; tea => i cdecl br. cbv beta.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _). cbn.
      move=> [] hbctx [] ihbctxty [] [] hbody IHbody [] hbty IHbty.
      intuition eauto; solve_all.
      eapply context_cumulativity_wf_app; tea.
      eapply IHbody. eapply All2_fold_app => //. apply All2_cumul_over_refl.
      eauto using context_cumulativity_app, context_cumulativity_wf_app.
      eapply IHbty.
      eapply All2_fold_app => //. apply All2_cumul_over_refl.
      eapply context_cumulativity_wf_app; tea.
  - econstructor.
    all:pcuic.
    * eapply fix_guard_context_cumulativity; eauto.
      eapply cumul_context_Algo_Spec; eauto. eapply into_ws_cumul_ctx_pb; eauto.
      + apply wf_local_closed_context; eauto.
      + apply wf_local_closed_context; eauto.
    * eapply (All_impl X1).
      intros d Ht. now apply Ht.
    * eapply (All_impl X3).
      intros d Hb. apply Hb.
      1: now apply cumul_context_app_same.
      eapply (All_mfix_wf); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
  - econstructor.
    all:pcuic.
    * eapply cofix_guard_context_cumulativity; eauto.
      eapply cumul_context_Algo_Spec; eauto. eapply into_ws_cumul_ctx_pb; eauto.
      + apply wf_local_closed_context; eauto.
      + apply wf_local_closed_context; eauto.
      * eapply (All_impl X1).
      intros d Ht. now apply Ht.
    * eapply (All_impl X3).
      intros d Hb. apply Hb.
      1: now apply cumul_context_app_same.
      eapply (All_mfix_wf); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
  - econstructor; tea.
    depelim X1; constructor; eauto. solve_all.
  - econstructor; eauto. pose proof (wf_local_closed_context wfΓ).
    pose proof (type_closed (forall_Γ' _ X5 X6)). eapply (@closedn_on_free_vars xpred0) in H0.
    pose proof (subject_closed (forall_Γ'0 _ X5 X6)). eapply (@closedn_on_free_vars xpred0) in H1.
    pose proof (type_closed typet). eapply (@closedn_on_free_vars xpred0) in H2.
    pose proof (subject_closed typeB). eapply (@closedn_on_free_vars xpred0) in H3.
    unshelve eapply (@cumulAlgo_cumulSpec  _ _ Cumul); eauto.
    apply into_ws_cumul_pb; eauto.
    * unshelve eapply (cumulSpec_cumulAlgo _ _ (exist Γ _) (exist A _) (exist B _)) in X4; eauto.
      apply ws_cumul_pb_forget in X4. eapply wt_cum_ws_cumul_pb in X4; tea.
      apply (wt_cum_ws_cumul_ctx_pb Cumul) in X5; tea.
      eapply (ws_cumul_pb_ws_cumul_ctx X5) in X4.
      now eapply ws_cumul_pb_forget in X4.
    * eapply wf_local_closed_context; eauto.
Qed.

Lemma closed_context_cumul_cumul {cf} {Σ} {wfΣ : wf Σ} {Γ Γ'} :
  Σ ⊢ Γ ≤ Γ' -> cumul_context cumulAlgo_gen Σ Γ Γ'.
Proof.
  now move/ws_cumul_ctx_pb_forget.
Qed.
#[global] Hint Resolve closed_context_cumul_cumul : pcuic.

Lemma closed_context_conv_conv {cf} {Σ} {wfΣ : wf Σ} {Γ Γ'} :
  Σ ⊢ Γ = Γ' -> conv_context cumulAlgo_gen Σ Γ Γ'.
Proof.
  now move/ws_cumul_ctx_pb_forget.
Qed.
#[global] Hint Resolve closed_context_conv_conv : pcuic.

Lemma closed_context_cumulativity {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {pb t T Γ'} :
  Σ ;;; Γ |- t : T ->
  wf_local Σ Γ' ->
  Σ ⊢ Γ' ≤[pb] Γ ->
  Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  pose proof (ws_cumul_ctx_pb_forget e).
  eapply context_cumulativity_prop; eauto.
  destruct pb; tas.
  eapply conv_cumul_context in e; tea.
  eapply (ws_cumul_ctx_pb_forget e).
Qed.

Lemma context_cumulativity {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |- t : T ->
  wf_local Σ Γ' ->
  cumul_context cumulAlgo_gen Σ Γ' Γ ->
  Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  eapply context_cumulativity_prop; eauto.
Qed.

#[global] Hint Resolve wf_local_closed_context : fvs.

Lemma wf_conv_context_closed {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} {Γ Γ'} :
  conv_context cumulAlgo_gen Σ Γ Γ' ->
  wf_local Σ Γ ->
  wf_local Σ Γ' ->
  Σ ⊢ Γ = Γ'.
Proof.
  move=> a wf wf'.
  eapply into_ws_cumul_ctx_pb; eauto with fvs.
Qed.

Lemma wf_cumul_context_closed {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} {Γ Γ'} :
  cumul_context cumulAlgo_gen Σ Γ Γ' ->
  wf_local Σ Γ ->
  wf_local Σ Γ' ->
  Σ ⊢ Γ ≤ Γ'.
Proof.
  move=> a wf wf'.
  eapply into_ws_cumul_ctx_pb; eauto with fvs.
Qed.

Lemma context_conversion {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |- t : T ->
  wf_local Σ Γ' ->
  conv_context cumulAlgo_gen Σ Γ Γ' ->
  Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  eapply wf_conv_context_closed in e; eauto with fvs pcuic.
  symmetry in e.
  now eapply closed_context_cumulativity in e.
Qed.

(* For ease of application, avoiding to add a call to symmetry *)
Lemma closed_context_conversion {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |- t : T ->
  wf_local Σ Γ' ->
  Σ ⊢ Γ = Γ' ->
  Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  symmetry in e.
  now eapply closed_context_cumulativity in e.
Qed.
