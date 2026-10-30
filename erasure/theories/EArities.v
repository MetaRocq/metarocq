(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICReduction
  PCUICClosed PCUICTyping PCUICWcbvEval PCUICLiftSubst PCUICInversion PCUICArities
  PCUICSR PCUICGeneration PCUICSubstitution PCUICElimination
  PCUICWeakeningEnv PCUICWeakeningEnvTyp
  PCUICWellScopedCumulativity
  PCUICContextConversion PCUICConversion PCUICClassification
  PCUICSpine PCUICInductives PCUICInductiveInversion PCUICConfluence
  PCUICArities PCUICPrincipality PCUICFirstorder.

From MetaRocq.Erasure Require Import Extract.

Notation "Σ ⊢p s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

From Stdlib Require Import Program.
From Equations Require Import Equations.

Local Existing Instance extraction_checker_flags.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(* TODO move *)
#[global] Existing Instance extends_refl.

Lemma isErasable_Proof Σ Γ t :
  Is_proof Σ Γ t -> isErasable Σ Γ t.
Proof.
  intros. destruct X as (? & ? & ? & ? & ?). exists x. split. eauto. right.
  eauto.
Qed.

Lemma isType_isErasable Σ Γ T : isType Σ Γ T -> isErasable Σ Γ T.
Proof.
  intros (_ & s & Hs & _).
  exists (tSort s). intuition auto.
Qed.

Lemma isType_red:
  forall (Σ : global_env_ext) (Γ : context) (T : term), wf Σ -> wf_local Σ Γ ->
    isType Σ Γ T -> forall T' : term, red Σ Γ T T' -> isType Σ Γ T'.
Proof.
  intros.
  apply lift_sorting_it_impl_gen with X1 => // HT.
  eapply subject_reduction ; eauto.
Qed.

Lemma it_mkProd_isArity:
  forall (l : list context_decl) A,
    isArity A ->
    isArity (it_mkProd_or_LetIn l A).
Proof.
  induction l; cbn; intros; eauto.
  eapply IHl. destruct a, decl_body; cbn; eauto.
Qed.

Lemma isArity_ind_type (Σ : global_env_ext) mind ind idecl :
  wf Σ ->
  declared_inductive (fst Σ) ind mind idecl ->
  isArity (ind_type idecl).
Proof.
  intros.
  eapply (declared_inductive_inv weaken_env_prop_typing) in H; eauto.
  - inv H. rewrite ind_arity_eq.
    change PCUICEnvironment.it_mkProd_or_LetIn with it_mkProd_or_LetIn.
    rewrite <- it_mkProd_or_LetIn_app.
    clear.
    eapply it_mkProd_isArity. econstructor.
Qed.

Lemma isWfArity_prod_inv (Σ : global_env_ext) (Γ : context) (x : aname) (x0 x1 : term) :
    wf Σ ->
    isWfArity Σ Γ (tProd x x0 x1) -> (isType Σ Γ x0 × isWfArity Σ (Γ,, vass x x0) x1).
Proof.
  intros wfΣ (? & ? & ? & ?). cbn in e.
  eapply isType_tProd in i as [dom codom]; auto.
  apply isTypeRel_isType in dom.
  split; auto.
  split; auto.
  clear dom codom.
  eapply destArity_app_Some in e as (? & ? & ?); subst.
  eexists. eexists; eauto.
Qed.

Lemma inds_nth_error ind u l n t :
  nth_error (inds ind u l) n = Some t -> exists n, t = tInd {| inductive_mind := ind ; inductive_ind := n |} u.
Proof.
  unfold inds in *. generalize (#|l|). clear. revert t.
  induction n; intros.
  - destruct n. cbn in H. congruence. cbn in H. inv H.
    eauto.
  - destruct n0. cbn in H. congruence. cbn in H.
    eapply IHn. eauto.
Qed.

Lemma it_mkProd_arity :
  forall (l : list context_decl) (A : term), isArity (it_mkProd_or_LetIn l A) -> isArity A.
Proof.
  induction l; cbn; intros.
  - eauto.
  - eapply IHl in H. destruct a, decl_body; cbn in *; eauto.
Qed.

Lemma isArity_mkApps t L : isArity (mkApps t L) -> isArity t /\ L = [].
Proof.
  revert t; induction L; cbn; intros.
  - eauto.
  - eapply IHL in H. cbn in H. intuition.
Qed.

Lemma typing_spine_red (Σ : global_env_ext) Γ (args args' : list PCUICAst.term)
  (X : All2 (red Σ Γ) args args') (wfΣ : wf Σ)
  (T x x0 : PCUICAst.term)
  (t0 : typing_spine Σ Γ x args x0)
  (c : Σ;;; Γ ⊢ x0 ≤ T) x1
  (c0 : Σ;;; Γ ⊢ x1 ≤ x) :
  isType Σ Γ x1 ->
  isType Σ Γ T ->
  typing_spine Σ Γ x1 args' T.
Proof.
  intros ? ?. revert args' X.
  dependent induction t0; intros.
  - inv X. econstructor; eauto. transitivity ty => //.
    now transitivity ty'.
  - inv X. econstructor; tea.
    + transitivity ty => //.
    + eapply subject_reduction; eauto.
    + eapply IHt0; eauto.
      eapply red_ws_cumul_pb_inv.
      unfold subst1.
      eapply isType_tProd in i0 as [dom codom].
      eapply (closed_red_red_subst (Δ := [vass na A]) (Γ' := [])); auto.
      simpl. eapply isType_wf_local in codom. fvs.
      constructor; auto. eapply into_closed_red; auto. fvs. fvs.
      repeat constructor. eapply isType_is_open_term in codom; fvs.
      eapply isType_apply in i0; tea.
      eapply subject_reduction; tea.
Qed.

Lemma it_mkProd_red_Arity {Σ : global_env_ext} {Γ c0 i u l} {wfΣ : wf Σ} :
  ~ Is_conv_to_Arity Σ Γ (it_mkProd_or_LetIn c0 (mkApps (tInd i u) l)).
Proof.
  intros (? & [] & ?). eapply red_it_mkProd_or_LetIn_mkApps_Ind in X as (? & ? & ?). subst.
  eapply it_mkProd_arity in H. eapply isArity_mkApps in H as [? ?]. cbn in *. congruence.
Qed.

Lemma invert_it_Ind_eq_prod:
  forall (u : Instance.t) (i : inductive) (x : aname) (x0 x1 : term) (x2 : context) (x3 : list term),
    tProd x x0 x1 = it_mkProd_or_LetIn x2 (mkApps (tInd i u) x3) -> exists (L' : context) (l' : list term), x1 = it_mkProd_or_LetIn L' (mkApps (tInd i u) l').
Proof.
  intros u i x x0 x1 x2 x3 H0.
  revert x0 x3 x1 x H0. induction x2 using rev_ind; intros.
  - cbn. assert (decompose_app (tProd x x0 x1) = decompose_app (mkApps (tInd i u) x3)) by now rewrite H0.
    rewrite decompose_app_mkApps in H; cbn; eauto. cbn in H. inv H.
  - rewrite it_mkProd_or_LetIn_app in H0. cbn in *.
    destruct x, decl_body; cbn in H0; try now inv H0.
Qed.

(* if a constructor is a type or proof, it is a proof *)

Lemma declared_constructor_type_not_arity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ind n mdecl idecl cdecl u} :
  declared_constructor Σ (ind, n) mdecl idecl cdecl ->
  ~ Is_conv_to_Arity Σ Γ (type_of_constructor mdecl cdecl (ind, n) u).
Proof.
  intros decl; sq.
  unfold type_of_constructor.
  destruct (on_declared_constructor decl) as [XX [s [XX1 Ht]]].
  rewrite (cstr_eq Ht). clear -wfΣ decl.
  rewrite !PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite /cstr_concl.
  rewrite /cstr_concl_head. len.
  rewrite subst_cstr_concl_head.
  destruct decl as [[] ?]. now eapply nth_error_Some_length in H0.
  rewrite -it_mkProd_or_LetIn_app.
  now eapply it_mkProd_red_Arity.
Qed.

Lemma conv_to_arity_cumul {Σ : global_env_ext} {wfΣ : wf Σ} :
  forall (Γ : context) (C : term) T,
    Is_conv_to_Arity Σ Γ T ->
    Σ;;; Γ ⊢ C ≤ T ->
    Is_conv_to_Arity Σ Γ C.
Proof.
  intros Γ C T [? []] cum. sq.
  eapply invert_cumul_arity_r_gen; tea.
  exists x. split; auto. now sq.
Qed.

Lemma typing_spine_mkApps_Ind_ex {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ ind u args args' T' :
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
  ∑ Δ' args', Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ' (mkApps (tInd ind u) args') ≤ T'.
Proof.
  induction Δ in args, args' |- * using PCUICInduction.ctx_length_rev_ind.
  - simpl. intros sp.
    dependent elimination sp as [spnil i i' e|spcons i i' e e' c].
    * now exists [], args.
    * now eapply invert_cumul_ind_prod in e.
  - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
    * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
      eapply typing_spine_letin_inv in sp; eauto.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
      apply (X (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp).
    * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
      simpl.
      dependent elimination sp as [spnil i i' e|spcons i i' e e' sp].
      { exists (Γ0 ++ [vass na ty]).
        exists args. now rewrite it_mkProd_or_LetIn_app. }
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna dom codom]; pcuic.
      eapply (substitution0_ws_cumul_pb (t:=hd0)) in codom; eauto.
      eapply typing_spine_strengthen in sp. 3:tea.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
      apply (X (subst_context [hd0] 0 Γ0) ltac:(len; reflexivity) _ _ sp).
      eapply isType_apply in i; tea.
      eapply (type_ws_cumul_pb (pb:=Conv)); tea. 2:now symmetry.
      eapply isTypeRel_isType.
      now eapply isType_tProd in i as [].
Qed.

Lemma typing_spine_Is_conv_to_Arity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ ind u args args' T'} :
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
  ~ Is_conv_to_Arity Σ Γ T'.
Proof.
  move/typing_spine_mkApps_Ind_ex => [Δ' [args'' cum]].
  intros iscv.
  eapply invert_cumul_arity_r_gen in iscv; tea.
  now eapply it_mkProd_red_Arity in iscv.
Qed.

Lemma declared_constructor_typing_spine_not_arity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ind n mdecl idecl cdecl u args' T'} :
  declared_constructor Σ (ind, n) mdecl idecl cdecl ->
  typing_spine Σ Γ (type_of_constructor mdecl cdecl (ind, n) u) args' T' ->
  ~ Is_conv_to_Arity Σ Γ T'.
Proof.
  intros decl; sq.
  unfold type_of_constructor.
  destruct (on_declared_constructor decl) as [XX [s [XX1 Ht]]].
  rewrite (cstr_eq Ht). clear -wfΣ decl.
  rewrite !PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite /cstr_concl.
  rewrite /cstr_concl_head. len.
  rewrite subst_cstr_concl_head.
  destruct decl as [[] ?]. now eapply nth_error_Some_length in H0.
  rewrite -it_mkProd_or_LetIn_app.
  apply typing_spine_Is_conv_to_Arity.
Qed.

Lemma type_mkApps_tConstruct_n_conv_arity (Σ : global_env_ext) Γ ind c u x1 T : wf Σ ->
  Σ ;;; Γ |- mkApps (tConstruct ind c u) x1 : T ->
  ~ Is_conv_to_Arity Σ Γ T.
Proof.
  intros.
  eapply PCUICValidity.inversion_mkApps in X0 as (? & ? & ?); eauto.
  eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?) ; auto.
  eapply typing_spine_strengthen in t0. 3:tea.
  eapply declared_constructor_typing_spine_not_arity in t0; tea.
  eapply PCUICValidity.validity. econstructor; eauto.
Qed.

Lemma nIs_conv_to_Arity_nArity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T} :
  isType Σ Γ T ->
  ~ Is_conv_to_Arity Σ Γ T -> ~ isArity T.
Proof.
  intros isty nisc isa. apply nisc.
  exists T. split => //. sq.
  destruct isty as (_ & s & Hs & _).
  eapply wt_closed_red_refl; tea.
Qed.

Lemma tConstruct_no_Type (Σ : global_env_ext) Γ ind c u x1 : wf Σ ->
  isErasable Σ Γ (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ Γ (mkApps (tConstruct ind c u) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso.
    eapply nIs_conv_to_Arity_nArity; tea.
    eapply PCUICValidity.validity; tea.
    eapply type_mkApps_tConstruct_n_conv_arity in t; auto.
  - exists x, x0. eauto.
Qed.

(* if a cofixpoint is a type or proof, it is a proof *)

Lemma tCoFix_no_Type (Σ : global_env_ext) Γ mfix idx x1 : wf Σ ->
  isErasable Σ Γ (mkApps (tCoFix mfix idx) x1) ->
  Is_proof Σ Γ (mkApps (tCoFix mfix idx) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso.
    eapply PCUICValidity.inversion_mkApps in t as (? & ? & ?); eauto.
    pose proof (typing_spine_isType_codom t0).
    assert(c0 : Σ ;;; Γ ⊢ x ≤ x) by now eapply (isType_ws_cumul_pb_refl).
    revert c0 t0 i. generalize x at 1 3.
    intros x2 c0 t0 i.
    assert (HWF : isType Σ Γ x2).
    { eapply PCUICValidity.validity.
      eapply type_mkApps. 2:eauto. eauto.
    }
    eapply inversion_CoFix in t as (? & ? & ? & ? & ? & ? & ?) ; auto.
    eapply invert_cumul_arity_r in c0; eauto.
    eapply typing_spine_strengthen in t0. 3:eauto.
    eapply wf_cofixpoint_spine in i0; eauto.
    2-3:eapply nth_error_all, isTypeRel_isType in a; eauto; simpl in a; eauto.
    destruct i0 as (Γ' & T & DA & ind & u & indargs & (eqT & ck) & cum).
    destruct (Nat.ltb #|x1| (context_assumptions Γ')).
    eapply invert_cumul_arity_r_gen in c0; eauto.
    destruct c0. destruct H as [[r] isA].
    move: r; rewrite subst_it_mkProd_or_LetIn eqT; autorewrite with len.
    rewrite PCUICSigmaCalculus.expand_lets_mkApps subst_mkApps /=.
    move/red_it_mkProd_or_LetIn_mkApps_Ind => [ctx' [args' eq]].
    subst x4. now eapply it_mkProd_arity, isArity_mkApps in isA.
    move: cum => [] Hx1; rewrite eqT PCUICSigmaCalculus.expand_lets_mkApps subst_mkApps /= => cum.
    eapply invert_cumul_arity_r_gen in c0; eauto.
    now eapply Is_conv_to_Arity_ind in c0.
  - eexists _, _; intuition eauto.
Qed.

Lemma typing_spine_wat (Σ : global_env_ext) (Γ : context) (L : list term)
  (x x0 : term) :
    wf Σ ->
    typing_spine Σ Γ x L x0 ->
    isType Σ Γ x0.
Proof.
  intros wfΣ; induction 1; auto.
Qed.

Section Elim'.

Context `{cf : checker_flags}.
Context {Σ : global_env_ext} {wfΣ : wf_ext Σ}.
Variable Hcf : prop_sub_type = false.

Lemma cumul_prop1 Γ A B u :
  Sort.is_prop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u.
Proof using Hcf wfΣ.
  intros; eapply cumul_prop1; tea.
  now apply ws_cumul_pb_forget in X1.
Qed.

Lemma cumul_prop2 Γ A B u :
  Sort.is_prop u ->
  isType Σ Γ B ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof using Hcf wfΣ.
  intros. eapply cumul_prop2; tea.
  now apply ws_cumul_pb_forget in X0.
Qed.

Lemma cumul_sprop1 Γ A B u :
  Sort.is_sprop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u.
Proof using Hcf wfΣ.
  intros. eapply cumul_sprop1; tea.
  now apply ws_cumul_pb_forget in X1.
Qed.

Lemma cumul_sprop2 Γ A B u :
  Sort.is_sprop u ->
  isType Σ Γ B ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof using Hcf wfΣ.
  intros. eapply cumul_sprop2; tea.
  now apply ws_cumul_pb_forget in X0.
Qed.
End Elim'.

Lemma cumul_propositional (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Sort.is_propositional u ->
  isType Σ Γ B ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros wf.
  intros pu isTy cum Ha.
  destruct u => //.
  eapply cumul_prop2; eauto.
  eapply cumul_sprop2; eauto.
Qed.

Lemma sort_typing_spine:
  forall (Σ : global_env_ext) (Γ : context) (L : list term) (u : sort) (x x0 : term),
    wf_ext Σ ->
    Sort.is_propositional u ->
    typing_spine Σ Γ x L x0 ->
    Σ;;; Γ |- x : tSort u ->
    ∑ u', Σ;;; Γ |- x0 : tSort u' × Sort.is_propositional u'.
Proof.
  intros Σ Γ L u x x0 HΣ ? t1 c0.
  assert (X : wf Σ) by apply HΣ.
  revert u H c0.
  induction t1; intros.
  - destruct u => //. eapply cumul_prop2 in c0; eauto.
    eapply cumul_sprop2 in c0; eauto.
  - eapply cumul_propositional in c0; auto. 2-3: tea.
    eapply inversion_Prod in c0 as (? & ? & ? & ? & e0) ; auto.
    eapply ws_cumul_pb_Sort_inv in e0.
    eapply IHt1.
    2: eapply @substitution0 with (T := tSort _); tea.
    unfold compare_sort, leq_sort in *.
    destruct u, x0, x => //.
Qed.

Lemma arity_type_inv (Σ : global_env_ext) Γ t T1 T2 : wf_ext Σ -> wf_local Σ Γ ->
  Σ ;;; Γ |- t : T1 -> isArity T1 -> Σ ;;; Γ |- t : T2 -> Is_conv_to_Arity Σ Γ T2.
Proof.
  intros wfΣ wfΓ. intros.
  destruct (common_typing _ _ X X0) as (? & e & ? & ?).
  eapply invert_cumul_arity_l_gen; tea.
  eapply invert_cumul_arity_r_gen. 2:exact e.
  exists T1. split; auto. sq.
  eapply PCUICValidity.validity in X as (_ & s & Hs & _).
  eapply wt_closed_red_refl; eauto.
Qed.

Lemma cumul_prop1' (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  isType Σ Γ A ->
  Sort.is_propositional u ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  destruct u => //.
  eapply cumul_prop1 in X2; eauto.
  eapply cumul_sprop1 in X2; eauto.
Qed.

Lemma cumul_prop2' (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  isType Σ Γ A ->
  Sort.is_propositional u ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ B ≤ A ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  destruct u => //.
  eapply cumul_prop2 in X2; eauto.
  eapply cumul_sprop2 in X2; eauto.
Qed.

Lemma leq_term_propositional_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Sort.is_propositional u ->
  leq_sort (global_ext_constraints Σ) u' u.
Proof.
  intros wf leq Hv Hv' isp.
  eapply leq_term_prop_sorted_l; eauto.
Qed.

Lemma leq_term_propopositional_sorted_r {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Sort.is_propositional u' ->
  leq_sort (global_ext_constraints Σ) u u'.
Proof.
  intros wfΣ leq hv hv' isp.
  eapply leq_term_prop_sorted_r; eauto.
Qed.

Lemma Is_type_app (Σ : global_env_ext) Γ t L T :
  wf_ext Σ ->
  wf_local Σ Γ ->
  Σ ;;; Γ |- mkApps t L : T ->
  isErasable Σ Γ t ->
  ∥isErasable Σ Γ (mkApps t L)∥.
Proof.
  intros wfΣ wfΓ ? ?.
  assert (HW : isType Σ Γ T). eapply PCUICValidity.validity; eauto.
  eapply PCUICValidity.inversion_mkApps in X as (? & ? & ?); auto.
  destruct X0 as (? & ? & [ | [u]]).
  - eapply common_typing in t2 as (? & e & e0 & ?). 2:eauto. 2:exact t0.
    eapply invert_cumul_arity_r in e0; eauto.
    destruct e0 as (? & ? & ?). destruct H as [].
    eapply ws_cumul_pb_red_l_inv in e. 2:exact X.
    eapply type_reduction_closed in t2; tea.
    eapply typing_spine_strengthen in t1. 3:tea.
    unshelve epose proof (isArity_typing_spine wfΓ t1).
    2:{ eapply PCUICValidity.validity in t2; tea; pcuic. }
    forward H. eapply arity_type_inv; tea.
    destruct H as [T' [[]]].
    sq. exists T'. split. eapply type_mkApps; tea.
    eapply typing_spine_weaken_concl; tea.
    now eapply red_conv.
    eapply isType_red; tea; pcuic. exact X0.
    now left.
  - destruct p.
    eapply PCUICPrincipality.common_typing in t2 as (? & e & e0 & ?). 2:eauto. 2:exact t0.
    eapply cumul_prop1' in e0; eauto.
    eapply cumul_propositional in e; eauto.
    econstructor. exists T. split. eapply type_mkApps. 2:eassumption. eassumption. right.
    eapply sort_typing_spine in t1; eauto.
    now eapply PCUICValidity.validity in t0.
    now apply PCUICValidity.validity in t2.
Qed.

Lemma leq_sort_propositional_r {cf : checker_flags} (ϕ : UnivConstraintSet.t) (u1 u2 : sort) :
  leq_sort ϕ u1 u2 -> Sort.is_propositional u2 -> Sort.is_propositional u1.
Proof.
  destruct u1, u2 => //.
Qed.

Lemma leq_sort_propositional_l {cf : checker_flags} (ϕ : UnivConstraintSet.t) (u1 u2 : sort) :
  prop_sub_type = false ->
  leq_sort ϕ u1 u2 -> Sort.is_propositional u1 -> Sort.is_propositional u2.
Proof.
  destruct u1, u2 => //= -> //.
Qed.

Lemma is_propositional_sort_prod x2 x3 :
  Sort.is_propositional (Sort.sort_of_product x2 x3) -> Sort.is_propositional x3.
Proof.
  destruct x2, x3 => //.
Qed.

Lemma Is_type_lambda (Σ : global_env_ext) Γ na T1 t :
  wf_ext Σ ->
  wf_local Σ Γ ->
  isErasable Σ Γ (tLambda na T1 t) ->
  ∥isErasable Σ (vass na T1 :: Γ) t∥.
Proof.
  intros ? ? (T & ? & ?).
  eapply inversion_Lambda in t0 as (? & h1 & ? & e); auto.
  destruct s as [ | (u & ? & ?)].
  - eapply invert_cumul_arity_r in e; eauto. destruct e as (? & [] & ?).
    eapply invert_red_prod in X1 as (? & ? & []); eauto; subst. cbn in H.
    econstructor. exists x2. econstructor.
    eapply type_reduction_closed; eauto. econstructor; eauto.
  - sq. eapply cumul_prop1' in e; eauto.
    eapply inversion_Prod in e as (? & ? & ? & ? & e) ; auto.
    eapply ws_cumul_pb_Sort_inv in e.
    eapply leq_sort_propositional_r in e as H0; cbn; eauto.
    eexists. split. eassumption. right. eexists. split. eassumption.
    eapply is_propositional_sort_prod in H0; eauto.
    eapply type_Lambda in h1; eauto.
    now apply PCUICValidity.validity in h1.
Qed.

Lemma Is_type_red (Σ : global_env_ext) Γ t v:
  wf Σ ->
  red Σ Γ t v ->
  isErasable Σ Γ t ->
  isErasable Σ Γ v.
Proof.
  intros ? ? (T & ? & ?).
  exists T. split.
  - eapply subject_reduction; eauto.
  - eauto.
Qed.

Lemma Is_type_eval (Σ : global_env_ext) t v:
  wf Σ ->
  eval Σ t v ->
  isErasable Σ [] t ->
  isErasable Σ [] v.
Proof.
  intros; eapply Is_type_red. eauto.
  red in X1. destruct X1 as [T [HT _]].
  eapply wcbveval_red; eauto. assumption.
Qed.

(* Thanks to the restriction to Prop </= Type, erasability is also closed by expansion
  on well-typed terms. *)

Lemma Is_type_eval_inv (Σ : global_env_ext) t v:
  wf_ext Σ ->
  welltyped Σ [] t ->
  PCUICWcbvEval.eval Σ t v ->
  isErasable Σ [] v ->
  ∥ isErasable Σ [] t ∥.
Proof.
  intros wfΣ [T HT] ev [vt [Ht Hp]].
  eapply wcbveval_red in ev; eauto.
  pose proof (subject_reduction _ _ _ _ _ wfΣ.1 HT ev).
  pose proof (common_typing _ wfΣ Ht X) as [P [Pvt [Pt vP]]].
  destruct Hp.
  eapply arity_type_inv in X. 5:eauto. all:eauto.
  red in X. destruct X as [T' [[red] isA]].
  eapply type_reduction_closed in HT; eauto.
  sq. exists T'; intuition auto.
  sq. exists T. intuition auto. right.
  destruct s as [u [vtu isp]].
  exists u; intuition auto.
  eapply cumul_propositional; eauto. now eapply PCUICValidity.validity in HT.
  eapply cumul_prop1'; eauto. now eapply PCUICValidity.validity in vP.
Qed.

Lemma isType_closed_red_refl {Σ} {wfΣ : wf Σ} {Γ T} :
  isType Σ Γ T -> Σ ;;; Γ ⊢ T ⇝ T.
Proof.
  intros (_ & s & hs & _); eapply wt_closed_red_refl; tea.
Qed.

Lemma nIs_conv_to_Arity_isWfArity_elim {Σ} {wfΣ : wf Σ} {Γ x} :
  ~ Is_conv_to_Arity Σ Γ x ->
  isWfArity Σ Γ x ->
  False.
Proof.
  intros nis [isTy [ctx [s da]]]. apply nis.
  red. exists (it_mkProd_or_LetIn ctx (tSort s)).
  split. sq. apply destArity_spec_Some in da.
  simpl in da. subst x.
  eapply isType_closed_red_refl; pcuic.
  now eapply it_mkProd_isArity.
Qed.

Definition isErasable_Type (Σ : global_env_ext) Γ T :=
  (Is_conv_to_Arity Σ Γ T +
    (∑ u : sort, Σ;;; Γ |- T : tSort u × Sort.is_propositional u))%type.

Lemma isErasable_any_type {Σ} {wfΣ : wf_ext Σ} {Γ t T} :
  isErasable Σ Γ t ->
  Σ ;;; Γ |- t : T ->
  isErasable_Type Σ Γ T.
Proof.
  intros [T' [Ht Ha]].
  intros HT.
  destruct (PCUICPrincipality.common_typing _ wfΣ Ht HT) as [P [le [le' tC]]]. sq.
  destruct Ha.
  left. eapply arity_type_inv. 3:exact Ht. all:eauto using typing_wf_local.
  destruct s as [u [Hu isp]].
  right.
  exists u; split; auto.
  eapply cumul_propositional; eauto. eapply PCUICValidity.validity; eauto.
  eapply cumul_prop1'; eauto. eapply PCUICValidity.validity; eauto.
Qed.

Lemma Is_proof_ty Σ Γ t :
  wf_ext Σ ->
  Is_proof Σ Γ t ->
  forall t' ty,
  Σ ;;; Γ |- t : ty ->
  Σ ;;; Γ |- t' : ty ->
  Is_proof Σ Γ t'.
Proof.
  intros wfΣ [ty [u [Hty isp]]].
  intros t' ty' Hty'.
  epose proof (PCUICPrincipality.common_typing _ wfΣ Hty Hty') as [C [Cty [Cty' Ht'']]].
  intros Ht'.
  exists ty', u; intuition auto.
  eapply PCUICValidity.validity in Hty; eauto.
  eapply PCUICValidity.validity in Hty'; eauto.
  eapply PCUICValidity.validity in Ht''; eauto.
  eapply cumul_prop1' in Cty; eauto.
  eapply cumul_propositional in Cty'; eauto.
Qed.


Import PCUICGlobalEnv PCUICUnivSubst PCUICValidity PCUICCumulProp.

Notation " Σ ;;; Γ |- t ~~ u " := (cumul_prop Σ Γ t u)  (at level 50, Γ, t, u at next level) : type_scope.

Lemma is_propositional_bottom' {Σ Γ T s s'} :
  wf_ext Σ ->
  prop_sub_type = false ->
  Σ ;;; Γ |- T ~~ tSort s ->
  Σ ;;; Γ |- T ~~ tSort s' ->
  PCUICCumulProp.eq_univ_prop s s'.
Proof.
  intros.
  eapply PCUICCumulProp.cumul_prop_sort.
  etransitivity; tea.
  now symmetry.
Qed.

Lemma is_propositional_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  prop_sub_type = false ->
  Σ ;;; Γ ⊢ T ≤ tSort s ->
  Σ ;;; Γ ⊢ T ≤ tSort s' ->
  PCUICCumulProp.eq_univ_prop s s'.
Proof.
  move => wf pst /cumul_pb_cumul_prop h /cumul_pb_cumul_prop h'.
  now eapply is_propositional_bottom'.
Qed.

Lemma is_propositional_lower {Σ s u u'} :
  leq_sort Σ s u ->
  leq_sort Σ s u' ->
  PCUICCumulProp.eq_univ_prop u u'.
Proof.
  destruct s, u, u' => //.
Qed.

Lemma typing_spine_inj {Σ Γ Δ s args args' u u'} :
  wf_ext Σ ->
  prop_sub_type = false ->
  let T := it_mkProd_or_LetIn Δ (tSort s) in
  typing_spine Σ Γ T args (tSort u) ->
  typing_spine Σ Γ T args' (tSort u') ->
  PCUICCumulProp.eq_univ_prop u u'.
Proof.
  intros wf ips T.
  move/typing_spine_it_mkProd_or_LetIn_full_inv => su.
  move/typing_spine_it_mkProd_or_LetIn_full_inv => su'.
  eapply is_propositional_lower; tea.
Qed.

Lemma Is_proof_ind Σ Γ t :
  wf_ext Σ ->
  Is_proof Σ Γ t ->
  forall t' ind u args args',
  Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
  Σ ;;; Γ |- t' : mkApps (tInd ind u) args' ->
  Is_proof Σ Γ t'.
Proof.
  intros wfΣ [ty [u [Hty isp]]].
  intros t' ind u' args args' Hty' Hty''.
  epose proof (PCUICPrincipality.common_typing _ wfΣ Hty Hty') as [C [Cty [Cty' Ht'']]].
  destruct isp.
  assert (Σ ;;; Γ |- C : tSort u).
  eapply cumul_prop1'; tea => //. now eapply validity.
  assert (Σ ;;; Γ |- mkApps (tInd ind u') args : tSort u).
  eapply cumul_prop2'; tea => //. now eapply validity.
  eapply inversion_mkApps in X0 as x1. destruct x1 as [? []].
  eapply inversion_Ind in t1 as [mdecl [idecl [wf [decli ?]]]]; eauto.
  destruct (validity Hty'') as (_ & u'' & tyargs' & _).
  eapply inversion_mkApps in X0 as x1. destruct x1 as [? []].
  eapply invert_type_mkApps_ind in X0 as [sp cum]; eauto.
  eapply invert_type_mkApps_ind in tyargs' as f; tea. destruct f as [sp' cum']; eauto.
  do 2 eexists. split => //. tea. instantiate (1 := u'').
  split => //.
  rewrite (declared_inductive_type decli) in sp, sp'.
  rewrite subst_instance_it_mkProd_or_LetIn /= in sp, sp'.
  eapply typing_spine_inj in sp. 4:exact sp'. all:eauto.
  destruct u, u'' => //.
Qed.


Lemma red_case_isproof {Σ : global_env_ext} {Γ ip p discr discr' brs T} {wfΣ : wf_ext Σ} :
  PCUICReduction.red Σ Γ (tCase ip p discr brs) (tCase ip p discr' brs) ->
  Σ ;;; Γ |- tCase ip p discr brs : T ->
  Is_proof Σ Γ discr -> Is_proof Σ Γ discr'.
Proof.
  intros hr hc.
  eapply subject_reduction in hr; tea; eauto.
  eapply inversion_Case in hc as [mdecl [idecl [isdecl [indices ?]]]]; eauto.
  eapply inversion_Case in hr as [mdecl' [idecl' [isdecl' [indices' ?]]]]; eauto.
  pose proof (wfΣ' := wfΣ.1).
  unshelve eapply declared_inductive_to_gen in isdecl, isdecl'; eauto.
  destruct (declared_inductive_inj isdecl isdecl'). subst mdecl' idecl'.
  intros hp.
  epose proof (Is_proof_ind _ _ _ wfΣ hp).
  destruct p0 as [[] ?]. destruct p1 as [[] ?].
  exact (X _ _ _ _ _ scrut_ty scrut_ty0).
Qed.

Lemma Is_proof_app {Σ Γ t args ty} {wfΣ : wf_ext Σ} :
  Is_proof Σ Γ t ->
  Σ ;;; Γ |- mkApps t args : ty ->
  Is_proof Σ Γ (mkApps t args).
Proof.
  intros [ty' [u [Hty [isp pu]]]] Htargs.
  eapply PCUICValidity.inversion_mkApps in Htargs as [A [Ht sp]].
  pose proof (PCUICValidity.validity Hty).
  pose proof (PCUICValidity.validity Ht).
  epose proof (PCUICPrincipality.common_typing _ wfΣ Hty Ht) as [C [Cty [Cty' Ht'']]].
  eapply PCUICSpine.typing_spine_strengthen in sp. 3:tea.
  edestruct (sort_typing_spine _ _ _ u _ _ _ pu sp) as [u' [Hty' isp']].
  eapply cumul_prop1'. 4:tea. all:eauto.
  eapply validity; eauto.
  exists ty, u'; split; auto.
  eapply PCUICSpine.type_mkApps; tea; eauto.
  now eapply validity.
Qed.

Lemma isErasable_Propositional {Σ : global_env_ext} {Γ ind n u args} :
  wf_ext Σ ->
  isErasable Σ Γ (mkApps (tConstruct ind n u) args) -> isPropositional Σ ind.
Proof.
  intros wfΣ ise.
  eapply tConstruct_no_Type in ise; eauto.
  destruct ise as [T [s [HT [Ts isp]]]].
  unfold isPropositional.
  eapply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
  eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?); auto.
  pose proof (wfΣ' := wfΣ.1).
  unshelve epose proof (d_ := declared_constructor_to_gen d); eauto.
  unfold lookup_inductive. rewrite (declared_inductive_lookup_gen d_.p1).
  destruct (on_declared_constructor d).
  destruct p as [onind oib].
  rewrite oib.(ind_arity_eq).
  rewrite /isPropositionalArity !destArity_it_mkProd_or_LetIn /=.
  eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
  unfold type_of_constructor in t0.
  destruct s0 as [indctors [nthcs onc]].
  rewrite onc.(cstr_eq) in t0.
  rewrite !subst_instance_it_mkProd_or_LetIn !PCUICLiftSubst.subst_it_mkProd_or_LetIn in t0.
  len in t0.
  rewrite subst_cstr_concl_head in t0. destruct d as [decli declc].
  destruct decli as [declm decli]. now eapply nth_error_Some_length.
  rewrite -it_mkProd_or_LetIn_app in t0.
  eapply PCUICElimination.typing_spine_proofs in Ts; eauto.
  destruct Ts as [_ Hs].
  specialize (Hs _ _ d c) as [Hs _].
  specialize (Hs isp). subst s. move: isp.
  now destruct (ind_sort x1).
  eapply validity. econstructor; tea.
Qed.

Lemma nisErasable_Propositional {Σ : global_env_ext} {Γ ind n u} :
  wf_ext Σ ->
  welltyped Σ Γ (tConstruct ind n u) ->
  (isErasable Σ Γ (tConstruct ind n u) -> False) -> ~~ isPropositional Σ ind.
Proof.
  intros wfΣ wt ise.
  destruct wt as [T HT].
  epose proof HT as HT'.
  eapply inversion_Construct in HT' as (? & ? & ? & ? & ? & ? & e); auto.
  pose proof (declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ a d c).
  pose proof d as [decli ?].
  destruct (on_declared_constructor d).
  destruct p as [onind oib].
  unfold isPropositional, lookup_inductive.
  pose proof (wfΣ' := wfΣ.1).
  unshelve epose proof (decli_ := declared_inductive_to_gen decli); eauto.
  rewrite (declared_inductive_lookup_gen decli_).
  rewrite oib.(ind_arity_eq).
  rewrite /isPropositionalArity !destArity_it_mkProd_or_LetIn /=.
  destruct (Sort.is_propositional (ind_sort x0)) eqn:isp; auto.
  exfalso; eapply ise.
  red. eexists; intuition eauto. right.
  unfold type_of_constructor in e, X.
  destruct s as [indctors [nthcs onc]].
  rewrite onc.(cstr_eq) in e, X.
  rewrite !subst_instance_it_mkProd_or_LetIn !PCUICLiftSubst.subst_it_mkProd_or_LetIn in e, X.
  len in e; len in X.
  rewrite subst_cstr_concl_head in e, X.
  destruct decli. eapply nth_error_Some_length in H1; eauto.
  rewrite -it_mkProd_or_LetIn_app in e, X.
  exists (subst_instance_sort u (ind_sort x0)).
  rewrite is_propositional_subst_instance => //.
  split; auto.
  eapply cumul_propositional; eauto.
  rewrite is_propositional_subst_instance => //.
  eapply PCUICValidity.validity; eauto.
  destruct X as (_ & cty & ty & _).
  eapply type_Cumul_alt; eauto.
  eapply isType_Sort. 2:eauto.
  destruct (ind_sort x0) => //.
  eapply PCUICSpine.inversion_it_mkProd_or_LetIn in ty; eauto.
  epose proof (typing_spine_proofs _ _ [] _ _ _ [] _ _ wfΣ ty).
  forward H0 by constructor. eapply has_sort_isType; eauto.
  simpl. now eapply has_sort_isType. eapply ws_cumul_eq_pb, PCUICSR.wt_cumul_pb_refl; eauto.
  destruct H0 as [_ sorts].
  specialize (sorts _ _ decli c) as [sorts sorts'].
  forward sorts' by constructor.
  do 2 constructor.
  rewrite is_propositional_subst_instance in sorts, sorts' |- *.
  specialize (sorts' isp). rewrite -sorts'. reflexivity.
Qed.

Lemma isPropositional_propositional Σ {wfΣ: wf Σ} (Σ' : E.global_context) ind mdecl idecl mdecl' idecl' :
  PCUICAst.declared_inductive Σ ind mdecl idecl ->
  EGlobalEnv.declared_inductive Σ' ind mdecl' idecl' ->
  erases_mutual_inductive_body mdecl mdecl' ->
  erases_one_inductive_body idecl idecl' ->
  EGlobalEnv.inductive_isprop_and_pars Σ' ind = Some (isPropositional Σ ind, mdecl.(ind_npars)).
Proof.
  intros decli decli' [_ indp] [].
  unfold isPropositional, EGlobalEnv.inductive_isprop_and_pars.
  unfold lookup_inductive.
  unshelve epose proof (decli_ := declared_inductive_to_gen decli); eauto.
  rewrite (declared_inductive_lookup_gen decli_).
  rewrite (EGlobalEnv.declared_inductive_lookup decli') /=
    /isPropositionalArity.
  destruct H0 as [_ [_ [_ isP]]]. unfold isPropositionalArity in isP.
  destruct destArity as [[ctx s]|] eqn:da => //.
  rewrite isP; congruence. congruence.
Qed.

Lemma isPropositional_propositional_cstr Σ (Σ' : E.global_context) ind c mdecl idecl cdecl mdecl' idecl' :
  wf Σ ->
  PCUICAst.declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  EGlobalEnv.declared_inductive Σ' ind mdecl' idecl' ->
  erases_mutual_inductive_body mdecl mdecl' ->
  erases_one_inductive_body idecl idecl' ->
  EGlobalEnv.constructor_isprop_pars_decl Σ' ind c =
  Some (isPropositional Σ ind, mdecl.(ind_npars), EAst.mkConstructor cdecl.(cstr_name) (context_assumptions cdecl.(cstr_args))).
Proof.
  intros wfΣ declc decli' em ei.
  pose proof declc as [decli'' _].
  eapply isPropositional_propositional in decli''; tea.
  move: decli''.
  rewrite /EGlobalEnv.inductive_isprop_and_pars.
  unfold EGlobalEnv.constructor_isprop_pars_decl.
  unfold EGlobalEnv.lookup_constructor.
  rewrite (EGlobalEnv.declared_inductive_lookup decli') /=.
  intros [= <- <-].
  destruct ei. clear H0.
  eapply Forall2_nth_error_Some in H as [cdecl' []]; tea. 2:apply declc.
  rewrite H //. f_equal. f_equal.
  destruct cdecl'. cbn in *. destruct H0. subst. f_equal.
  destruct (on_declared_constructor declc) as [[] [? []]].
  now eapply cstr_args_length in o1.
Qed.

Lemma eval_tCase {cf : checker_flags} {Σ : global_env_ext}  ci p discr brs res T :
  wf Σ ->
  Σ ;;; [] |- tCase ci p discr brs : T ->
  eval Σ (tCase ci p discr brs) res ->
  ∑ c u args, PCUICReduction.red Σ [] (tCase ci p discr brs) (tCase ci p ((mkApps (tConstruct ci.(ci_ind) c u) args)) brs).
Proof.
  intros wf wt H. depind H; try now (cbn in *; congruence).
  - eapply inversion_Case in wt as (? & ? & ? & ? & cinv & ?); eauto.
    eexists _, _, _. eapply PCUICReduction.red_case_c. eapply wcbveval_red. 2: eauto. eapply cinv.
  - eapply inversion_Case in wt as wt'; eauto. destruct wt' as (? & ? & ? & ? & cinv & ?).
    assert (Hred1 : PCUICReduction.red Σ [] (tCase ip p discr brs) (tCase ip p (mkApps fn args) brs)). {
      etransitivity. { eapply PCUICReduction.red_case_c. eapply wcbveval_red. 2: eauto. eapply cinv. }
      econstructor. econstructor.
      rewrite closed_unfold_cofix_cunfold_eq. eauto.
      enough (closed (mkApps (tCoFix mfix idx) args)) as Hcl by (rewrite closedn_mkApps in Hcl; solve_all).
      eapply eval_closed. eauto.
      2: eauto. eapply @PCUICClosedTyp.subject_closed with (Γ := []); eauto. eapply cinv. eauto.
    }
    edestruct IHeval2 as (c & u & args0 & IH); eauto using subject_reduction.
    exists c, u, args0. etransitivity; eauto.
Qed.

Lemma Subsingleton_cofix v ci p brs T (Σ : global_env_ext) :
   wf_ext Σ ->
   forall (mdecl : mutual_inductive_body) (idecl : one_inductive_body) mfix idx,
   declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
   forall (args : list term), Subsingleton Σ ci.(ci_ind) ->
   Σ ;;; [] |- tCase ci p (mkApps (tCoFix mfix idx) args) brs : T ->
   Σ ⊢p tCase ci p (mkApps (tCoFix mfix idx) args) brs ⇓ v ->
   Is_proof Σ [] (mkApps (tCoFix mfix idx) args) ->
   #|ind_ctors idecl| <= 1.
Proof.
  intros. destruct Σ as [Σ1 Σ2]. cbn in *.
  eapply eval_tCase in X0 as X2'; eauto. destruct X2' as (? & ? & ? & ?).
  eapply subject_reduction in X0 as X2'; eauto.
  eapply inversion_Case in X2' as (? & ? & ? & ? & [] & ?); eauto.
  eapply inversion_Case in X0 as (? & ? & ? & ? & [] & ?); eauto.
  pose (X' := X.1). unshelve eapply declared_inductive_to_gen in x8, x4, H; eauto.
  destruct (declared_inductive_inj x8 x4); subst.
  destruct (declared_inductive_inj x8 H); subst.
  eapply H0; eauto. apply declared_inductive_from_gen; eauto.
  reflexivity.
  eapply Is_proof_ind; tea.
Qed.

Lemma isErasable_unfold_cofix {Σ : global_env_ext} {Γ mfix idx} {wfΣ : wf Σ} decl :
  isErasable Σ Γ (tCoFix mfix idx) ->
  nth_error mfix idx = Some decl ->
  isErasable Σ Γ (subst0 (cofix_subst mfix) (dbody decl)).
Proof.
  intros [Tty []] hred.
  exists Tty. split => //.
  eapply type_tCoFix_inv in t as t''; eauto.
  destruct t'' as [decl' [[[] h'] h'']].
  rewrite e in hred. noconf hred.
  eapply type_ws_cumul_pb; tea.
  now eapply validity.
Qed.

Lemma isErasable_red {Σ : global_env_ext} {Γ T U} {wfΣ : wf Σ} :
  isErasable Σ Γ T -> PCUICReduction.red Σ Γ T U -> isErasable Σ Γ U.
Proof.
  intros [Tty []] hred.
  exists Tty. split => //. eapply subject_reduction; tea.
Qed.

Lemma not_isErasable Σ Γ f A u :
  wf_ext Σ -> wf_local Σ Γ ->
  ∥Σ;;; Γ |- f : A∥ ->
  (forall B, ∥Σ;;; Γ ⊢ A ⇝ B∥ -> A = B) ->
  (forall B, ∥Σ ;;; Γ |- f : B∥ -> ∥Σ ;;; Γ ⊢ A ≤ B∥) ->
  ~ ∥ isArity A ∥ ->
  ∥ Σ;;; Γ |- A : tSort u ∥ ->
  ~ Sort.is_propositional u ->
  ~ ∥ Extract.isErasable Σ Γ f ∥.
Proof.
  intros wfΣ Hlocal Hf Hnf Hprinc Harity Hfu Hu  [[T [HT []]]]; sq.
  - eapply Harity; sq.
    eapply EArities.arity_type_inv in i as [T' [? ?]]; eauto.
    eapply Hnf in H. subst; eauto.
  - destruct s as [s [? ?]]. eapply Hu.
    specialize (Hprinc _ (sq HT)).
    pose proof (Hs := i). sq.
    eapply PCUICElimination.unique_sorting_equality_propositional in Hprinc; eauto.
    rewrite Hprinc; eauto.
Qed.

(** Inhabitants of primitive types are not erasable: they must live in a relevant universe.

  This currently relies on int and float being in Set, while arrays are universe polymorphic,
  hence always relevant, and the primitive types are axioms, so not convertible to arities. *)

Lemma prim_type_inv p prim_ty :
  ∑ u args, prim_type p prim_ty = mkApps (tConst prim_ty u) args.
Proof.
  destruct p as [? []]; simp prim_type.
  - eexists [], []. reflexivity.
  - eexists [], []; reflexivity.
  - eexists [], []; reflexivity.
  - eexists [_], [_]; reflexivity.
Qed.

Lemma primitive_invariants_axiom t decl : primitive_invariants t decl -> cst_body decl = None.
Proof.
  destruct t; cbn => //.
  1-3:now intros [? []].
  now intros [].
Qed.

Lemma nisErasable_tPrim Σ p :
  wf_ext Σ ->
  isErasable Σ [] (tPrim p) -> False.
Proof.
  intros wfΣ [T [Ht h]].
  eapply inversion_Prim in Ht as [prim_ty [cdecl []]]; eauto.
  pose proof (type_Prim _ _ _ _ _ a e d p0 p1). eapply validity in X.
  destruct h.
  - eapply invert_cumul_arity_r in w; tea.
    destruct w as [ar [[H] r]].
    destruct (prim_type_inv p prim_ty) as [u [args eq]].
    rewrite eq in H.
    eapply invert_red_axiom_app in H as [args' []]; tea.
    2:now eapply primitive_invariants_axiom.
    subst ar. now eapply isArity_mkApps in r as [].
  - destruct s as [s [hs isp]].
    eapply cumul_prop1' in hs; tea; eauto.
    depelim p1; simp prim_type in hs.
    * destruct p0 as [hd hb hu].
      eapply inversion_Const in hs as [decl' [wf [decl'' [cu hs']]]]; eauto.
      unshelve eapply declared_constant_to_gen in d, decl''. 3,6:eapply wfΣ.
      eapply declared_constant_inj in d; tea. subst decl'.
      rewrite hd in hs'. cbn in hs'.
      eapply ws_cumul_pb_Sort_inv in hs'. red in hs'.
      destruct s => //.
    * destruct p0 as [hd hb hu].
      eapply inversion_Const in hs as [decl' [wf [decl'' [cu hs']]]]; eauto.
      unshelve eapply declared_constant_to_gen in d, decl''. 3,6:eapply wfΣ.
      eapply declared_constant_inj in d; tea. subst decl'.
      rewrite hd in hs'. cbn in hs'.
      eapply ws_cumul_pb_Sort_inv in hs'. red in hs'.
      destruct s => //.
    * destruct p0 as [hd hb hu].
      eapply inversion_Const in hs as [decl' [wf [decl'' [cu hs']]]]; eauto.
      unshelve eapply declared_constant_to_gen in d, decl''. 3,6:eapply wfΣ.
      eapply declared_constant_inj in d; tea. subst decl'.
      rewrite hd in hs'. cbn in hs'.
      eapply ws_cumul_pb_Sort_inv in hs'. red in hs'.
      destruct s => //.
    * destruct p0 as [hd hb hu].
      eapply inversion_App in hs as [na [A [B [hp [harg hres]]]]]; eauto.
      eapply inversion_Const in hp as [decl' [wf [decl'' [cu hs']]]]; eauto.
      unshelve eapply declared_constant_to_gen in d, decl''. 3,6:eapply wfΣ.
      eapply declared_constant_inj in d; tea. subst decl'.
      rewrite hd in hs'. cbn in hs'.
      eapply ws_cumul_pb_Prod_Prod_inv in hs' as [].
      eapply substitution_ws_cumul_pb_vass in w1; tea.
      cbn in w1.
      pose proof (ws_cumul_pb_trans _ _ _ w1 hres) as X0.
      eapply ws_cumul_pb_Sort_inv in X0.
      destruct s => //.
Qed.
