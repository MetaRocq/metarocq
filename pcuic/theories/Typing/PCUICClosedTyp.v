(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICClosed
     PCUICOnFreeVars PCUICTyping PCUICReduction PCUICGlobalEnv PCUICWeakeningEnvConv PCUICClosedConv
     PCUICWeakeningEnv PCUICWeakeningEnvTyp.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Lemma declared_projection_closed_ind {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ}{mdecl idecl cdecl p pdecl} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  on_global_env cumulSpec0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ ->
  closedn (S (ind_npars mdecl)) pdecl.(proj_type).
Proof.
  intros isdecl X0.
  pose proof (declared_projection_inv weaken_env_prop_closed wfΣ X0 isdecl) as onp.
  set (declared_inductive_inv _ wfΣ X0 _) as oib in *.
  clearbody oib. unfold declared_projection in isdecl.
  have onpars := onParams (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1.p1).
  have parslen := onNpars (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1.p1).
  simpl in onp.
  destruct (ind_ctors idecl) as [|? []] eqn:Heq; try contradiction.
  destruct onp as [_ onp].
  red in onp.
  destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
  destruct onp as [onna onp]. rewrite {}onp.
  pose proof (onConstructors oib) as onc.
  red in onc. rewrite Heq in onc. inv onc. clear X1.
  eapply on_cargs in X.
  simpl.
  replace (S (ind_npars mdecl)) with (0 + (1 + ind_npars mdecl)) by lia.
  eapply closedn_subst.
  { clear. unfold inds. generalize (ind_bodies mdecl).
    induction l; simpl; auto. }
  rewrite inds_length.
  eapply closedn_subst0.
  { clear. unfold projs. induction p.(proj_arg); simpl; auto. }
  rewrite projs_length /=.
  eapply (@closed_upwards (ind_npars mdecl + #|ind_bodies mdecl| + p.(proj_arg) + 1)).
  2:lia.
  eapply closedn_lift.
  clear -parslen isdecl Heq' onpars X.
  rename X into args.
  apply sorts_local_ctx_Pclosed in args.
  red in onpars.
  eapply All_local_env_Pclosed in onpars.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|ind_params mdecl| + i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  2:{ intros n x. rewrite app_context_length.
      intros H; eapply closed_decl_upwards; eauto. lia. }
  eapply (Alli_shiftn (P:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  rewrite Nat.add_0_r in args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in onpars.
  2:{ intros n x d. eapply closed_decl_upwards; eauto; lia. }
  epose proof (Alli_app_inv onpars). rewrite List.length_rev /= in X.
  specialize (X args). rewrite -List.rev_app_distr in X.
  clear onpars args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|arities_context (ind_bodies mdecl)| + i) d)) in X.
  2:intros; eapply closed_decl_upwards; eauto; lia.
  eapply closed_smash_context_unfold in X.
  eapply Alli_rev_nth_error in X; eauto.
  rewrite smash_context_length in X. simpl in X.
  eapply nth_error_Some_length in Heq'. rewrite smash_context_length in Heq'.
  simpl in Heq'. unfold closed_decl in X.
  move/andP: X => [] _ cl.
  eapply closed_upwards. eauto. rewrite arities_context_length.
  rewrite context_assumptions_app parslen.
  rewrite context_assumptions_app in Heq'. lia.
Qed.


Lemma declared_decl_closed_ind {cf : checker_flags} {Σ : global_env} {wfΣ : wf Σ} {cst decl} :
  lookup_env Σ cst = Some decl ->
  on_global_env cumulSpec0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ ->
  on_global_decl cumulSpec0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t))
                 (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env; eauto. do 2 red; eauto.
Qed.

Lemma declared_minductive_closed_ind {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ}{mdecl mind} :
  on_global_env cumulSpec0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ ->
  declared_minductive Σ mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  intros HΣ decl. pose proof (decl_ := decl).
  unshelve eapply declared_minductive_to_gen in decl; tea.
  pose proof (declared_decl_closed_ind decl) as decl'.
  specialize (decl' HΣ).
  red in decl'.
  unfold closed_inductive_decl.
  apply andb_and. split. apply onParams in decl'.
  now apply closedn_All_local_env in decl'; auto.
  apply onInductives in decl'.
  eapply All_forallb.

  assert (Alli (fun i =>  declared_inductive Σ {| inductive_mind := mind; inductive_ind := i |} mdecl)
    0 (ind_bodies mdecl)).
  { eapply forall_nth_error_Alli. intros.
    split; auto.  }
  eapply Alli_mix in decl'; eauto. clear X.
  clear decl.
  eapply Alli_All; eauto.
  intros n x [decli oib].
  rewrite /closed_inductive_body.
  apply andb_and; split. apply andb_and. split.
  - rewrite andb_and. split.
    * apply onArity in oib.
      now move/andP: oib => [] /=.
    * pose proof (onArity oib) as X. unfold on_type_rel in X.
      rewrite oib.(ind_arity_eq) in X.
      cbn in X.
      rewrite !closedn_it_mkProd_or_LetIn /= !andb_true_r in X.
      now move/andP: X.
  - pose proof (onConstructors oib).
    red in X. eapply All_forallb. eapply All2_All_left; eauto.
    intros cdecl cs X0;
    move: (on_ctype X0) => /=. unfold on_type_rel. cbn.
    simpl. unfold closed_constructor_body.
    intros Hty.
    rewrite arities_context_length in Hty.
    rewrite Hty.
    rewrite X0.(cstr_eq) closedn_it_mkProd_or_LetIn in Hty.
    move/andP: Hty => [] _.
    rewrite closedn_it_mkProd_or_LetIn.
    move/andP=> [] ->. rewrite closedn_mkApps /=.
    move/andP=> [] _. rewrite forallb_app.
    now move/andP=> [] _ ->.

  - eapply All_forallb.
    pose proof (onProjections oib).
    destruct (eq_dec (ind_projs x) []) as [->|eq]; try constructor.
    destruct (ind_projs x) in X, eq; try congruence. clear eq.
    destruct (ind_ctors x) as [|cdecl []] eqn:hcdecl; try contradiction.
    apply on_projs in X.
    assert (Alli (fun i pdecl => declared_projection Σ
      (mkProjection {| inductive_mind := mind; inductive_ind := n |} mdecl.(ind_npars) i) mdecl x cdecl pdecl)
      0 (ind_projs x)).
    { eapply forall_nth_error_Alli.
      intros. split; auto. split; auto. cbn. now rewrite hcdecl. }
    eapply (Alli_All X0). intros.
    now eapply declared_projection_closed_ind in H.
Qed.



Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T)
           (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t))
           (fun Σ Γ => closed_ctx Γ).
Proof.
  assert (X := weaken_env_prop_closed).
  apply typing_ind_env; intros * wfΣ Γ wfΓ *; intros; unfold lift_wfb_term in *; cbn in *;
  rewrite -> ?andb_and in *; try solve [intuition auto].

  - destruct X0 as (Htm & s & (_ & Hty) & _).
    rewrite /= andb_true_r in Hty. split; tas.
    destruct j_term => //=.
    move:Htm => [] _ /andP [] //.

  - now apply closedn_All_local_closed in X0.

  - pose proof (nth_error_Some_length H).
    elim (Nat.ltb_spec n #|Γ|); intuition auto. all: try lia. clear H1.

    induction Γ in n, H, H0, H2 |- *. rewrite nth_error_nil in H. discriminate.
    destruct n.
    simpl in H. noconf H. simpl.
    rewrite -Nat.add_1_r. apply closedn_lift.
    rewrite closedn_ctx_cons in H0. move/andP: H0 => [_ ca].
    destruct a as [na [b|] ty]. simpl in ca.
    rewrite /test_decl /= in ca.
    now move/andP: ca => [_ cty].
    now rewrite /test_decl /= in ca.
    simpl.
    rewrite -Nat.add_1_r.
    rewrite -(simpl_lift _ (S n) 0 1 0); try lia.
    apply closedn_lift. apply IHΓ; auto.
    rewrite closedn_ctx_cons in H0.
    now move/andP: H0 => [H0 _]. simpl in H2; lia.

  - intuition auto.
    generalize (closedn_subst [u] #|Γ| 0 B). rewrite Nat.add_0_r.
    move=> Hs. apply: Hs => /=. simpl. rewrite H1 => //.
    rewrite Nat.add_1_r. auto.

  - unshelve eapply declared_constant_to_gen in H0; tea.
    rewrite closedn_subst_instance.
    eapply lookup_on_global_env in X0; eauto.
    destruct X0 as (Σ' & hext & [onu HΣ'] & [IHtm IHty]%andb_and).
    simpl in *.
    eauto using closed_upwards with arith.

  - rewrite closedn_subst_instance.
    eapply declared_inductive_inv in X0; eauto with extends.
    apply onArity in X0.
    rewrite /on_type_rel /lift_wfb_term /= in X0.
    intuition eauto using closed_upwards with arith.

  - destruct isdecl as [Hidecl Hcdecl].
    apply closedn_subst0.
    + unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
      simpl. now rewrite IHn.
    + rewrite inds_length.
      rewrite closedn_subst_instance.
      eapply declared_inductive_inv in X0; eauto with extends.
      pose proof X0.(onConstructors) as XX.
      eapply All2_nth_error_Some in Hcdecl; eauto.
      destruct Hcdecl as [? [? ?]]. cbn in *.
      destruct o as [? ? HT _].
      rewrite /on_type_rel /lift_wfb_term /= in HT.
      rewrite arities_context_length in HT.
      eauto using closed_upwards with arith.

  - destruct H3 as [clret _].
    destruct H7 as [clc clty].
    rewrite closedn_mkApps in clty. simpl in clty.
    rewrite forallb_app in clty. move/andP: clty => [clpar clinds].
    rewrite app_context_length in clret.
    red in H9. eapply Forall2_All2 in H9.
    eapply All2i_All2_mix_left in X5; eauto.
    eapply declared_minductive_closed_ind in X0; tea. 2:exact isdecl.
    pose proof (closed_ind_closed_cstrs X0 isdecl).
    eapply All2i_All_mix_left in X5; tea. clear X6.
    intuition auto.
    + unfold test_predicate_k. simpl. rtoProp; intuition eauto.
      rewrite (closedn_ctx_alpha X1).
      eapply closed_ind_predicate_context in X0; tea.
      rewrite (wf_predicate_length_pars H1).
      now rewrite (declared_minductive_ind_npars isdecl).
      rewrite (All2_length X1).
      rewrite /predctx in clret.
      rewrite case_predicate_context_length_indices // in clret.
      { now rewrite ind_predicate_context_length. }
    + clear H9. solve_all. unfold test_branch_k. clear H7. solve_all.
      * rewrite (closedn_ctx_alpha a1).
        eapply closed_cstr_branch_context_gen in X0; tea.
        rewrite (wf_predicate_length_pars H1).
        now rewrite (declared_minductive_ind_npars isdecl).
      * rewrite (All2_length a1).
        len in H9.
        (*unfold case_branch_context_gen in H8. simpl in H9.
        rewrite case_branch_type_fst in H8. *)
        rewrite case_branch_context_length_args in H9 => //.
        now rewrite cstr_branch_context_length.
    + rewrite closedn_mkApps; auto.
      rewrite closedn_it_mkLambda_or_LetIn //.
      rewrite closedn_ctx_app in H4.
      now move/andP: H4 => [].
      now rewrite Nat.add_comm.
      rewrite forallb_app. simpl. now rewrite clc clinds.

  - intuition auto.
    apply closedn_subst0.
    + simpl. rewrite closedn_mkApps in H3.
      rewrite forallb_rev H2. apply H3.
    + rewrite closedn_subst_instance.
      eapply declared_projection_closed_ind in X0; eauto.
      simpl; rewrite List.length_rev H1.
      eapply closed_upwards; eauto. lia.

  - clear H.
    split. solve_all.
    rewrite /on_def_type /on_def_body ?andb_and in a0, b |- *. cbn in *.
    simpl in *. unfold test_def.
    rewrite -> app_context_length in *.
    subst types.
    rewrite fix_context_length in b. intuition auto.
    eapply nth_error_all in X1 as (_ & X1)%andb_and; eauto.

  - split. solve_all.
    rewrite /on_def_type /on_def_body ?andb_and in a0, b |- *. cbn in *.
    simpl in *. unfold test_def.
    rewrite -> app_context_length in *.
    subst types.
    rewrite fix_context_length in b. intuition auto.
    eapply nth_error_all in X1 as (_ & X1)%andb_and; eauto.

  - destruct p as [[] pv]; cbn in X0 |- *; simp prim_type => //.
    depelim pv. simp prim_type. cbn. depelim X1.
    move/andP: hdef => [] -> ->; rewrite !andb_true_r. split => //.
    solve_all.
Qed.

Lemma declared_minductive_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl mind} :
  declared_minductive Σ mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  eapply declared_minductive_closed_ind; tea.
  now apply (env_prop_sigma typecheck_closed).
Qed.

Lemma declared_inductive_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl mind idecl} :
  declared_inductive Σ mind mdecl idecl ->
  closed_inductive_body mdecl idecl.
Proof.
  intros [decli hnth].
  eapply declared_minductive_closed in decli; tea.
  move/andP: decli => [clpars cli].
  solve_all. eapply nth_error_all in cli; eauto.
  now simpl in cli.
Qed.

Lemma declared_projection_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ}{mdecl idecl p cdecl pdecl} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  closedn (S (ind_npars mdecl)) pdecl.(proj_type).
Proof.
  intros; eapply declared_projection_closed_ind; eauto.
  eapply (env_prop_sigma typecheck_closed); eauto.
Qed.

Lemma declared_inductive_closed_pars_indices {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl mind idecl} :
  declared_inductive Σ mind mdecl idecl ->
  closed_ctx (ind_params mdecl ,,, ind_indices idecl).
Proof.
  intros decli.
  pose proof (declared_minductive_closed (proj1 decli)).
  move/andP: H => [] clpars _. move: decli.
  move/declared_inductive_closed.
  move/andP => [] /andP [] clind clbodies.
  move/andP: clind => [] _ indpars _.
  now rewrite closedn_ctx_app clpars indpars.
Qed.

Lemma declared_constructor_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl idecl c cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closed_constructor_body mdecl cdecl.
Proof.
  intros declc.
  generalize (declared_minductive_closed declc).
  rewrite /closed_inductive_decl.
  rewrite /closed_inductive_body.
  move/andP=> [_ clbs].
  destruct declc.
  destruct H.
  solve_all.
  eapply nth_error_all in clbs; eauto.
  simpl in clbs.
  move/andP: clbs => [] /andP [] _ clc _.
  solve_all.
  eapply nth_error_all in clc; eauto. now simpl in clc.
Qed.


Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma subject_closed {cf} {Σ} {wfΣ : wf Σ.1} {Γ t T} :
  Σ ;;; Γ |- t : T ->
  closedn #|Γ| t.
Proof.
  now move/(env_prop_typing typecheck_closed) => /andP [ct _].
Qed.

Lemma type_closed {cf} {Σ} {wfΣ : wf Σ.1} {Γ t T} :
  Σ ;;; Γ |- t : T ->
  closedn #|Γ| T.
Proof.
  now move/typecheck_closed => [_ [_ /andP [_ ct]]].
Qed.

#[global] Hint Extern 4 (closedn #|?Γ| ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |- A : _ |- _ ] => exact (subject_closed H)
  end : fvs.

#[global] Hint Extern 4 (closedn #|?Γ| ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |- _ : A |- _ ] => exact (type_closed H)
  end : fvs.

#[global] Hint Extern 10 => progress unfold PCUICTypingDef.typing in * : fvs.

Lemma lift_typing_closed {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ j} :
  lift_typing typing Σ Γ j ->
  lift_wf_term (closedn #|Γ|) j.
Proof.
  intro Hj. apply lift_typing_subject with (1 := Hj) => t T.
  apply subject_closed.
Qed.

Lemma isTypeRel_closed {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T r} : isTypeRel Σ Γ T r -> closedn #|Γ| T.
Proof. move/lift_typing_closed => [] //. Qed.

Lemma isType_closed {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T} : isType Σ Γ T -> closedn #|Γ| T.
Proof. move/lift_typing_closed => [] //. Qed.

#[global] Hint Extern 4 (closedn #|?Γ| ?A = true) =>
  match goal with
  | [ H : isType _ Γ A |- _ ] => exact (isType_closed H)
  | [ H : isTypeRel _ Γ A _ |- _ ] => exact (isTypeRel_closed H)
  end : fvs.

Lemma is_open_term_closed (Γ : context) t :
  closedn #|Γ| t = is_open_term Γ t.
Proof.
  rewrite closedP_on_free_vars.
  eapply on_free_vars_ext.
  now rewrite closedP_shiftnP.
Qed.

Lemma is_closed_ctx_closed (Γ : context) :
  closed_ctx Γ = is_closed_context Γ.
Proof.
  rewrite closedn_ctx_on_free_vars //.
Qed.

#[global]
Hint Rewrite is_open_term_closed is_closed_ctx_closed : fvs.
#[global] Hint Extern 4 => progress autorewrite with fvs : fvs.

Lemma subject_is_open_term {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ t T} :
  Σ ;;; Γ |- t : T ->
  is_open_term Γ t.
Proof.
  move/subject_closed.
  now rewrite is_open_term_closed.
Qed.

Lemma type_is_open_term {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ t T} :
  Σ ;;; Γ |- t : T ->
  is_open_term Γ T.
Proof.
  move/type_closed. now rewrite is_open_term_closed.
Qed.

Lemma lift_typing_is_open_term {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ j} :
  lift_typing typing Σ Γ j ->
  lift_wf_term (is_open_term Γ) j.
Proof.
  move/lift_typing_closed => Hj.
  apply lift_wf_term_impl with (1 := Hj) => t.
  rewrite is_open_term_closed //.
Qed.

Lemma isTypeRel_is_open_term {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T r} :
  isTypeRel Σ Γ T r ->
  is_open_term Γ T.
Proof.
  move/isType_closed. now rewrite is_open_term_closed.
Qed.

Lemma isType_is_open_term {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T} :
  isType Σ Γ T ->
  is_open_term Γ T.
Proof.
  move/isType_closed. now rewrite is_open_term_closed.
Qed.

Lemma closed_wf_local `{checker_flags} {Σ Γ} :
  wf Σ.1 ->
  wf_local Σ Γ ->
  closed_ctx Γ.
Proof.
  intros wfΣ wfΓ.
  apply (env_prop_wf_local typecheck_closed Σ wfΣ _ wfΓ).
Qed.

#[global] Hint Extern 4 (is_open_term ?Γ ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |- A : _ |- _ ] => exact (subject_is_open_term H)
  end : fvs.

#[global] Hint Extern 4 (is_open_term ?Γ ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |- _ : A |- _ ] => exact (type_is_open_term H)
  end : fvs.

#[global] Hint Extern 4 (is_open_term ?Γ ?A = true) =>
  match goal with
  | [ H : isType _ Γ A |- _ ] => exact (isType_is_open_term H)
  end : fvs.

#[global] Hint Extern 4 (is_open_term ?Γ ?A = true) =>
  match goal with
  | [ H : isTypeRel _ Γ A _ |- _ ] => exact (isTypeRel_is_open_term H)
  end : fvs.

Lemma closed_ctx_on_ctx_free_vars Γ : closed_ctx Γ = on_ctx_free_vars (closedP #|Γ| xpredT) Γ.
Proof.
  rewrite closedn_ctx_on_free_vars.
  now rewrite -on_free_vars_ctx_on_ctx_free_vars shiftnP_closedP shiftnP_xpredT Nat.add_0_r.
Qed.

Lemma wf_local_closed_context `{checker_flags} {Σ Γ} {wfΣ : wf Σ} : wf_local Σ Γ -> on_free_vars_ctx xpred0 Γ.
Proof.
  move/PCUICClosedTyp.closed_wf_local.
  now rewrite closed_ctx_on_ctx_free_vars on_free_vars_ctx_on_ctx_free_vars_closedP.
Qed.

Lemma typing_closed_context {cf} {Σ} {wfΣ : wf Σ} {Γ T U} :
  Σ ;;; Γ |- T : U ->
  is_closed_context Γ.
Proof.
  now move/typing_wf_local/wf_local_closed_context.
Qed.

#[global] Hint Extern 4 (is_closed_context ?Γ = true) =>
  match goal with
  | [ H : _ ;;; Γ |- _ : _ |- _ ] => exact (typing_closed_context H)
  end : fvs.

Lemma ctx_inst_closed {cf:checker_flags} (Σ : global_env_ext) Γ i Δ :
  wf Σ.1 -> ctx_inst (typing Σ) Γ i Δ -> All (closedn #|Γ|) i.
Proof.
  intros wfΣ; induction 1; auto; constructor; auto; fvs.
Qed.

#[global] Hint Resolve ctx_inst_closed : fvs.

Lemma declared_decl_closed `{checker_flags} {Σ : global_env} {cst decl} :
  wf Σ ->
  lookup_env Σ cst = Some decl ->
  on_global_decl cumulSpec0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  apply declared_decl_closed_ind; eauto.
  now eapply (env_prop_sigma typecheck_closed).
Qed.



Lemma declared_constant_closed_type {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {cst decl} :
  declared_constant Σ cst decl ->
  closed decl.(cst_type).
Proof.
  apply (env_prop_sigma typecheck_closed) in wfΣ.
  intros h. unshelve eapply declared_constant_to_gen in h; tea.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as (Σ' & ext & wfΣ' & [Htm Hty]%andb_and).
  easy.
Qed.


Lemma declared_constant_closed_body {cf : checker_flags} :
  forall (Σ : global_env) cst decl body,
    wf Σ ->
    declared_constant Σ cst decl ->
    decl.(cst_body) = Some body ->
    closed body.
Proof.
  intros Σ cst decl body hΣ h e.
  apply (env_prop_sigma typecheck_closed) in hΣ.
  unshelve eapply declared_constant_to_gen in h; tea.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as (Σ' & ext & wfΣ' & [Htm _]%andb_and).
  simpl in Htm.
  rewrite e in Htm.
  easy.
Qed.


Lemma declared_inductive_closed_type {cf:checker_flags} :
  forall Σ mdecl ind idecl,
    wf Σ ->
    declared_inductive Σ ind mdecl idecl ->
    closed idecl.(ind_type).
Proof.
  intros Σ mdecl ind idecl hΣ h.
  apply (env_prop_sigma typecheck_closed) in hΣ.
  unfold declared_inductive in h.
  destruct h as [h1 h2].
  unshelve eapply declared_minductive_to_gen in h1; tea.
  eapply lookup_on_global_env in h1. 2: eauto.
  destruct h1 as (Σ' & ext & wfΣ' & decl').
  red in decl'. destruct decl' as [h ? ? ?].
  eapply Alli_nth_error in h. 2: eassumption.
  simpl in h. now destruct h as [? [? h]%andb_and ? ? ?].
Qed.


Lemma declared_inductive_closed_params {cf:checker_flags} {Σ mdecl ind idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ind mdecl idecl ->
  closed_ctx mdecl.(ind_params).
Proof.
  intros h.
  pose proof (on_declared_inductive h) as [onmind _].
  eapply onParams in onmind. unfold on_context in onmind.
  eapply closed_wf_local. 2:tea. eauto.
Qed.


Lemma declared_inductive_closed_params_inst {cf:checker_flags} {Σ mdecl ind idecl} {wfΣ : wf Σ} {u} :
  declared_inductive Σ ind mdecl idecl ->
  closed_ctx (subst_instance u mdecl.(ind_params)).
Proof.
  intros h.
  rewrite closedn_subst_instance_context.
  now apply (declared_inductive_closed_params h).
Qed.

Lemma declared_inductive_closed_constructors {cf:checker_flags} {Σ ind mdecl idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ind mdecl idecl ->
  All (closed_constructor_body mdecl) idecl.(ind_ctors).
Proof.
  intros [hmdecl hidecl].
  eapply (declared_minductive_closed (Σ:=empty_ext Σ)) in hmdecl; auto.
  unfold closed_inductive_decl in hmdecl.
  move/andP: hmdecl => [clpars clbodies].
  eapply forallb_nth_error in clbodies; eauto.
  erewrite hidecl in clbodies. simpl in clbodies.
  unfold closed_inductive_body in clbodies.
  move/andP: clbodies => [/andP [_ cl] _].
  now eapply forallb_All in cl.
Qed.


Lemma declared_minductive_closed_arities {cf:checker_flags}
  {Σ ind mdecl} {wfΣ : wf Σ} :
  declared_minductive Σ ind mdecl ->
  closed_ctx (arities_context (ind_bodies mdecl)).
Proof.
  intros h.
  eapply declared_minductive_closed in h.
  move/andP: h => [] _ clbs.
  induction (ind_bodies mdecl) => //.
  rewrite /arities_context /= rev_map_spec /=.
  move: clbs; simpl. move=> /andP[] cla clbs.
  rewrite closedn_ctx_app /=. apply/andP; split; auto.
  rewrite /test_decl /=. now move/andP: cla => [] /andP[] /andP[].
  eapply closedn_ctx_upwards. rewrite -rev_map_spec. eapply IHl => //. lia.
Qed.




Lemma declared_constructor_closed_gen_type {cf:checker_flags}
  {Σ mdecl idecl c cdecl} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closedn #|arities_context (ind_bodies mdecl)| cdecl.(cstr_type).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  eapply All_nth_error in h. 2: eassumption.
  move/andP: h => [/andP [hargs hindices]] hty. now len.
Qed.

Lemma declared_constructor_closed_type {cf:checker_flags}
  {Σ mdecl idecl c cdecl u} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closed (type_of_constructor mdecl cdecl c u).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  unfold type_of_constructor. simpl.
  eapply All_nth_error in h. 2: eassumption.
  move/andP: h => [/andP [hargs hindices]] hty.
  eapply closedn_subst0.
  - eapply declared_minductive_closed_inds.
    now destruct hidecl.
  - simpl. rewrite inds_length.
    rewrite closedn_subst_instance. assumption.
Qed.

Lemma declared_constructor_closed_args {cf:checker_flags}
  {Σ mdecl idecl c cdecl} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closedn_ctx (#|ind_bodies mdecl| + #|ind_params mdecl|) cdecl.(cstr_args).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  eapply All_nth_error in h. 2: eassumption.
  move/andP: h => [/andP [hargs hindices]] hty.
  apply hargs.
Qed.

Lemma declared_constructor_closed_indices {cf:checker_flags}
  {Σ mdecl idecl c cdecl} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  forallb (closedn (#|ind_bodies mdecl| + #|ind_params mdecl| + #|cstr_args cdecl|)) cdecl.(cstr_indices).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  eapply All_nth_error in h. 2: eassumption.
  now move/andP: h => [/andP [hargs hindices]] hty.
Qed.

Lemma closed_cstr_branch_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind i mdecl idecl cdecl} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (cstr_branch_context ind mdecl cdecl).
Proof.
  intros decli.
  eapply closed_cstr_branch_context_gen; tea.
  eapply declared_minductive_closed. eapply decli.
  eapply declared_constructor_closed; tea.
Qed.

Lemma closed_cstr_branch_context_npars {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind i mdecl idecl cdecl} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  closedn_ctx (ind_npars mdecl) (cstr_branch_context ind mdecl cdecl).
Proof.
  intros declc.
  rewrite (declared_minductive_ind_npars declc).
  now apply (closed_cstr_branch_context declc).
Qed.

Lemma declared_projection_closed_type {cf:checker_flags}
  {Σ mdecl idecl p cdecl pdecl} {wfΣ : wf Σ} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  closedn (S (ind_npars mdecl)) pdecl.(proj_type).
Proof.
  intros decl.
  now eapply declared_projection_closed in decl.
Qed.


#[global] Hint Unfold inst_case_branch_context : len.

(** This shows preservation by reduction of closed/noccur_between predicates
  necessary to prove exchange and strengthening lemmas. *)
Lemma red1_on_free_vars {cf:checker_flags} {P : nat -> bool} {Σ Γ u v} {wfΣ : wf Σ} :
  red1 Σ Γ u v ->
  on_free_vars P u ->
  on_ctx_free_vars P Γ ->
  on_free_vars P v.
Proof.
  intros h hav hctx.
  induction h using red1_ind_all in P, hav, hctx |- *.
  all: try solve [
    simpl ; constructor ; eapply IHh ;
    try (simpl in hav; rtoProp);
    try eapply urenaming_vass ;
    try eapply urenaming_vdef ;
    assumption
  ].
  all:simpl in hav |- *; try toAll.
  all:try move/and3P: hav => [h1 h2 h3].
  all:try (move/andP: hav => [] /andP [] h1 h2 h3).
  all:try move/andP: hav => [h1 h2].
  all:try move/andP: h3 => [] h3 h4.
  all:try move/andP: h4 => [] h4 h5.
  all:try rewrite ?h1 // ?h2 // ?h3 // ?h4 // ?IHh /= // ?andb_true_r.
  all:try eapply on_free_vars_subst1; eauto.
  - destruct (nth_error Γ i) eqn:hnth => //.
    simpl in H. noconf H.
    epose proof (nth_error_on_free_vars_ctx P 0 Γ i c).
    forward H0. { now rewrite addnP0. }
    specialize (H0 hav hnth). simpl in H0.
    rewrite /test_decl H in H0.
    rewrite on_free_vars_lift0 //.
    now move/andP: H0 => [] /=.
  - rewrite /iota_red.
    rename h5 into hbrs.
    move: h4. rewrite on_free_vars_mkApps => /andP [] /= _ hargs.
    apply on_free_vars_subst.
    { rewrite forallb_rev forallb_skipn //. }
    len.
    rewrite length_skipn; try lia; rewrite H0.
    replace (ci_npar ci + context_assumptions (bcontext br) - ci_npar ci)
    with (context_assumptions (bcontext br)) by lia.
    rewrite /expand_lets /expand_lets_k /=.
    eapply forallb_nth_error in hbrs.
    erewrite H in hbrs; simpl in hbrs.
    move/andP: hbrs => [] hbr hbody.
    eapply on_free_vars_subst.
    * relativize (context_assumptions _).
      + unshelve eapply foron_free_vars_extended_subst. eauto.
        eapply on_free_vars_ctx_inst_case_context; tea => //.
      + unfold inst_case_branch_context. now len.
    * rewrite extended_subst_length.
      rewrite shiftnP_add.
      eapply on_free_vars_lift_impl in hbody. unfold inst_case_branch_context. len.
      now rewrite Nat.add_comm.
  - rewrite !on_free_vars_mkApps in hav |- *.
    rtoProp.
    eapply on_free_vars_unfold_fix in H; eauto.
  - move: h4; rewrite !on_free_vars_mkApps.
    move=> /andP [] hcofix ->.
    eapply on_free_vars_unfold_cofix in hcofix; eauto.
  - move: hav; rewrite !on_free_vars_mkApps => /andP [] hcofix ->.
    eapply on_free_vars_unfold_cofix in H as ->; eauto.
  - eapply closed_on_free_vars. rewrite closedn_subst_instance.
    eapply declared_constant_closed_body; eauto.
  - move: hav; rewrite on_free_vars_mkApps /=.
    now move/(nth_error_forallb H).
  - rewrite (on_ctx_free_vars_concat _ _ [_]) // /= hctx
      on_ctx_free_vars_tip /= addnP_shiftnP /on_free_vars_decl
      /test_decl /= // hctx h2.
  - rewrite (on_ctx_free_vars_concat _ _ [_]) // hctx
      on_ctx_free_vars_tip /= addnP_shiftnP /on_free_vars_decl /test_decl /= h2 /=
      /foroptb /= h1 // h2.
  - solve_all.
    + eapply OnOne2_impl_All_r; eauto. solve_all.
    + now rewrite -(OnOne2_length X).
    + now rewrite -(OnOne2_length X).
  - relativize #|pcontext p|; unfold inst_case_predicate_context.
    * erewrite on_ctx_free_vars_extend; rewrite // hctx.
      erewrite on_free_vars_ctx_inst_case_context => //.
    * now len.
  - toAll.
    clear -h1 hctx X h5.
    eapply OnOne2_All_mix_left in X; tea.
    toAll. eapply OnOne2_impl_All_r in X; tea; solve_all; rewrite -?b0 //.
    eapply b1 => //.
    relativize #|bcontext x|; unfold inst_case_branch_context.
    * erewrite on_ctx_free_vars_extend; rewrite // hctx.
      erewrite on_free_vars_ctx_inst_case_context => //. solve_all.
    * now len.
  - rewrite (on_ctx_free_vars_concat _ _ [_]) // /= hctx
      on_ctx_free_vars_tip /= addnP_shiftnP /on_free_vars_decl /test_decl /= h1 /= //.
  - toAll. eapply OnOne2_impl_All_r; eauto; solve_all.
  - toAll. unfold test_def.
    rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all.
    destruct x, y; noconf b; simpl in *. rtoProp; solve_all.
  - toAll. unfold test_def in *. rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all;
     destruct x, y; noconf b; simpl in *; rtoProp; solve_all.
    apply b0 => //.
    rewrite -(fix_context_length mfix0).
    erewrite on_ctx_free_vars_extend; rewrite // hctx.
    now apply on_free_vars_fix_context.
  - toAll. unfold test_def.
    rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all.
    destruct x, y; noconf b; simpl in *. rtoProp; solve_all.
  - toAll. unfold test_def in *. rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all;
    destruct x, y; noconf b; simpl in *; rtoProp; solve_all.
    apply b0 => //.
    rewrite -(fix_context_length mfix0).
    rewrite on_ctx_free_vars_extend // hctx.
    now apply on_free_vars_fix_context.
  - cbn. toAll. solve_all.
    eapply OnOne2_impl_All_r; eauto; solve_all.
Qed.

Lemma red_on_free_vars {cf} {P : nat -> bool} {Σ Γ u v} {wfΣ : wf Σ} :
  red Σ Γ u v ->
  on_free_vars P u ->
  on_ctx_free_vars P Γ ->
  on_free_vars P v.
Proof.
  induction 1; eauto using red1_on_free_vars.
Qed.


Lemma term_closedn_list_ind :
  forall (P : nat -> term -> Type),
    (forall k (n : nat), n < k -> P k (tRel n)) ->
    (forall k (i : ident), P k (tVar i)) ->
    (forall k (n : nat) (l : list term), All (P k) l -> P k (tEvar n l)) ->
    (forall k s, P k (tSort s)) ->
    (forall k (n : aname) (t : term), P k t -> forall t0 : term, P (S k) t0 -> P k (tProd n t t0)) ->
    (forall k (n : aname) (t : term), P k t -> forall t0 : term, P (S k)  t0 -> P k (tLambda n t t0)) ->
    (forall k (n : aname) (t : term),
        P k t -> forall t0 : term, P k t0 -> forall t1 : term, P (S k) t1 -> P k (tLetIn n t t0 t1)) ->
    (forall k (t u : term), P k t -> P k u -> P k (tApp t u)) ->
    (forall k s (u : Instance.t), P  k (tConst s u)) ->
    (forall k (i : inductive) (u : Instance.t), P k (tInd i u)) ->
    (forall k (i : inductive) (n : nat) (u : Instance.t), P k (tConstruct i n u)) ->
    (forall k (ci : case_info) (p : predicate term),
        tCasePredProp_k P k p ->
        forall t0 : term, P k t0 -> forall l : list (branch term),
        tCaseBrsProp_k P p k l -> P k (tCase ci p t0 l)) ->
    (forall k (s : projection) (t : term), P k t -> P k (tProj s t)) ->
    (forall k (m : mfixpoint term) (n : nat), tFixProp (P k) (P (#|fix_context m| + k)) m -> P k (tFix m n)) ->
    (forall k (m : mfixpoint term) (n : nat), tFixProp (P k) (P (#|fix_context m| + k)) m -> P k (tCoFix m n)) ->
    (forall k p, tPrimProp (P k) p -> P k (tPrim p)) ->
    forall k (t : term), closedn k t -> P k t.
Proof.
  intros until t. revert k t.
  fix auxt 2.
  move auxt at top.
  intros k t.
  destruct t; intros clt;  match goal with
                 H : _ |- _ => apply H
              end; auto; simpl in clt;
            try move/andP: clt => [cl1 cl2];
            try move/andP: cl1 => [cl1 cl1'];
            try solve[apply auxt; auto];
              simpl in *.

  - now apply Nat.ltb_lt in clt.
  - revert l clt.
    fix auxl' 1.
    destruct l; constructor; [|apply auxl'].
    apply auxt. simpl in clt. now move/andP: clt  => [clt cll].
    now move/andP: clt => [clt cll].

  - red. move/andP: cl1 => /= [] /andP [] clpars clctx clret.
    repeat split.
    * revert clpars. generalize (pparams p).
      fix auxl' 1.
      destruct l; [constructor|]; cbn.
      move=> /= /andP []. simpl. move=> /= clt cll.
      constructor; [|apply auxl'].
      apply auxt => //. now rewrite cll /=.
    * revert clctx.
      unfold onctx_k.
      generalize (pcontext p).
      fix auxl' 1.
      destruct l; [constructor|]. simpl.
      move=>  /andP []. simpl. move=> /= clctx /andP [] clt cll.
      destruct c as [na [b|] ty]; simpl in *;
      constructor; simpl.
      split; apply auxt; rewrite Nat.sub_0_r //. simpl.
      eapply Alli_shift, Alli_impl; eauto. simpl.
      intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
      rewrite Nat.sub_0_r //. split; auto. exact tt.
      eapply Alli_shift, Alli_impl; eauto. simpl.
      intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
    * apply auxt => //.
  - unfold tCaseBrsProp_k.
    revert brs cl2. clear cl1 cl1'.
    rewrite /test_branch_k.
    fix auxl' 1.
    destruct brs; constructor; [|apply auxl'].
    simpl in cl2. move/andP: cl2  => [/andP [clctx clt] cll].
    split.
    move: clctx.
    generalize (bcontext b).
    fix auxl'' 1.
    destruct l; [constructor|]. simpl.
    move=>  /andP []. simpl. move=> /= clctx /andP [] clt' cll'.
    destruct c as [na [bod|] ty]; simpl in *;
    constructor; simpl.
    split; apply auxt; rewrite Nat.sub_0_r //.
    eapply Alli_shift, Alli_impl; eauto. eapply auxl'' => //. simpl.
    intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
    repeat split. rewrite Nat.sub_0_r. apply auxt => //.
    eapply Alli_shift, Alli_impl; eauto. eapply auxl'' => //. simpl.
    intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
    eapply auxt => //.
    simpl in cl2. now move/andP: cl2 => [].

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1.
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1.
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.

  - destruct prim as [? []]; cbn in clt |- *; rtoProp; intuition eauto.
    move: H. clear -auxt. generalize (array_value a).
    fix auxl 1. destruct l; intro.
    * constructor.
    * cbn in H; move/andP: H => []; eauto.
Defined.

Lemma term_noccur_between_list_ind :
  forall (P : nat -> nat -> term -> Type),
    (forall k n (i : nat), i < k \/ k + n <= i -> P k n (tRel i)) ->
    (forall k n (i : ident), P k n (tVar i)) ->
    (forall k n (id : nat) (l : list term), All (P k n) l -> P k n (tEvar id l)) ->
    (forall k n s, P k n (tSort s)) ->
    (forall k n (na : aname) (t : term), P k n t -> forall t0 : term, P (S k) n t0 -> P k n (tProd na t t0)) ->
    (forall k n (na : aname) (t : term), P k n t -> forall t0 : term, P (S k) n t0 -> P k n (tLambda na t t0)) ->
    (forall k n (na : aname) (t : term),
        P k n t -> forall t0 : term, P k n t0 -> forall t1 : term, P (S k) n t1 -> P k n (tLetIn na t t0 t1)) ->
    (forall k n (t u : term), P k n t -> P k n u -> P k n (tApp t u)) ->
    (forall k n s (u : Instance.t), P k n (tConst s u)) ->
    (forall k n (i : inductive) (u : Instance.t), P k n (tInd i u)) ->
    (forall k n (i : inductive) (c : nat) (u : Instance.t), P k n (tConstruct i c u)) ->
    (forall k n (ci : case_info) (p : predicate term),
        tCasePredProp_k (fun k' => P k' n) k p -> forall t0 : term, P k n t0 ->
        forall l : list (branch term),
        tCaseBrsProp_k (fun k' => P k' n) p k l -> P k n (tCase ci p t0 l)) ->
    (forall k n (s : projection) (t : term), P k n t -> P k n (tProj s t)) ->
    (forall k n (m : mfixpoint term) (i : nat), tFixProp (P k n) (P (#|fix_context m| + k) n) m -> P k n (tFix m i)) ->
    (forall k n (m : mfixpoint term) (i : nat), tFixProp (P k n) (P (#|fix_context m| + k) n) m -> P k n (tCoFix m i)) ->
    (forall k n p, tPrimProp (P k n) p -> P k n (tPrim p)) ->
    forall k n (t : term), noccur_between k n t -> P k n t.
Proof.
  intros until t. revert k n t.
  fix auxt 3.
  move auxt at top.
  intros k n t.
  destruct t; intros clt;  match goal with
                 H : _ |- _ => apply H
              end; auto; simpl in clt;
            try move/andP: clt => [cl1 cl2];
            try move/andP: cl1 => [cl1 cl1'];
            try solve[apply auxt; auto];
              simpl in *.

  - move/orP: clt => [cl|cl].
    now apply Nat.ltb_lt in cl; eauto.
    now apply Nat.leb_le in cl; eauto.

  - revert l clt.
    fix auxl' 1.
    destruct l; constructor; [|apply auxl'].
    apply auxt. simpl in clt. now move/andP: clt  => [clt cll].
    now move/andP: clt => [clt cll].

  - move/andP: cl1 => /= []/andP[] clpars clctx clret.
    split.
    * revert clpars. generalize (pparams p).
      fix auxl' 1.
      case => [|t' ts] /= //; cbn => /andP[] Ht' Hts; constructor; [apply auxt|apply auxl'] => //.
    * split; [|now apply auxt].
      move: clctx.
      clear -auxt.
      unfold onctx_k, ondecl.
      generalize (pcontext p).
      fix auxl' 1; destruct l; [constructor|]; simpl; rewrite ?Nat.sub_0_r.
      move/andP => [] tl /andP [tdef tty]. constructor.
      + rewrite Nat.sub_0_r. simpl. split; [|apply auxt]; tas.
        destruct (decl_body c); simpl in *; auto.
      + eapply Alli_shift, Alli_impl; eauto. simpl.
        intros n' x.
        now replace (Nat.pred #|l| - n' + #|pparams p|) with (#|l| - S n' + #|pparams p|).

  - revert brs cl2. clear cl1 cl1'.
    unfold test_branch_k, tCaseBrsProp_k.
    fix auxl' 1.
    destruct brs; constructor; [|apply auxl'].
    simpl in cl2. move/andP: cl2  => [/andP [clctx clb] cll].
    split.
    * unfold onctx_k, ondecl.
      revert clctx.
      generalize (bcontext b).
      fix auxl'' 1; destruct l; [constructor|]; simpl; rewrite ?Nat.sub_0_r.
      move/andP => [] tl /andP [tdef tty]. constructor.
      + rewrite Nat.sub_0_r. simpl. split; [|apply auxt]; tas.
        destruct (decl_body c); simpl in *; auto.
      + eapply Alli_shift, Alli_impl; eauto. simpl.
        intros n' x.
        now replace (Nat.pred #|l| - n' + #|pparams p|) with (#|l| - S n' + #|pparams p|).
    * eapply auxt => //.
    * now simpl in cl2; move/andP: cl2 => [].

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1.
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1.
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.


  - destruct prim as [? []]; cbn in clt |- *; rtoProp; intuition eauto.
    move: H. clear -auxt. generalize (array_value a).
    fix auxl 1. destruct l; intro.
    * constructor.
    * cbn in H; move/andP: H => []; eauto.
Defined.
