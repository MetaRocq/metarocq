(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
Set Equations Transparent.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction PCUICReflect PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp PCUICContextConversionTyp PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion PCUICUnivSubstitutionTyp PCUICCumulativity PCUICSR PCUICSafeLemmata PCUICNormalization
  PCUICValidity PCUICPrincipality PCUICElimination PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICEtaExpand
  PCUICFirstorder.

From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICSafeReduce PCUICSafeRetyping PCUICRetypingEnvIrrelevance.
From MetaRocq.Erasure Require Import EPrimitive EAstUtils ELiftSubst EArities Extract Prelim EDeps ErasureProperties ErasureCorrectness ErasureFunction.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Local Set Keyed Unification.
Set Default Proof Using "Type*".
Import MRMonadNotation.

Implicit Types (cf : checker_flags).

#[local] Existing Instance extraction_normalizing.
#[local] Existing Instance extraction_checker_flags.

Notation alpha_eq := (All2 (PCUICEquality.compare_decls eq eq)).

Definition global_erased_with_deps (Σ : global_env) (Σ' : EAst.global_declarations) kn :=
  (exists cst, declared_constant Σ kn cst /\
   exists cst' : EAst.constant_body,
    EGlobalEnv.declared_constant Σ' kn cst' /\
    erases_constant_body (Σ, cst_universes cst) cst cst' /\
    (forall body : EAst.term,
     EAst.cst_body cst' = Some body -> erases_deps Σ Σ' body)) \/
  (exists mib mib', declared_minductive Σ kn mib /\
    EGlobalEnv.declared_minductive Σ' kn mib' /\
    erases_mutual_inductive_body mib mib').

Definition includes_deps (Σ : global_env) (Σ' : EAst.global_declarations) deps :=
  forall kn,
    KernameSet.In kn deps ->
    global_erased_with_deps Σ Σ' kn.

Lemma includes_deps_union (Σ : global_env) (Σ' : EAst.global_declarations) deps deps' :
  includes_deps Σ Σ' (KernameSet.union deps deps') ->
  includes_deps Σ Σ' deps /\ includes_deps Σ Σ' deps'.
Proof.
  intros.
  split; intros kn knin; eapply H; rewrite KernameSet.union_spec; eauto.
Qed.

Lemma includes_deps_fold {A} (Σ : global_env) (Σ' : EAst.global_declarations) brs deps (f : A -> EAst.term) :
  includes_deps Σ Σ'
  (fold_left
    (fun (acc : KernameSet.t) (x : A) =>
      KernameSet.union (term_global_deps (f x)) acc) brs
      deps) ->
  includes_deps Σ Σ' deps /\
  (forall x, In x brs ->
    includes_deps Σ Σ' (term_global_deps (f x))).
Proof.
  intros incl; split.
  intros kn knin; apply incl.
  rewrite knset_in_fold_left. left; auto.
  intros br brin. intros kn knin. apply incl.
  rewrite knset_in_fold_left. right.
  now exists br.
Qed.

Definition declared_kn Σ kn :=
  ∥ ∑ decl, lookup_env Σ kn = Some decl ∥.

Lemma term_global_deps_spec {cf} {Σ : global_env_ext} {Γ t et T} :
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  Σ;;; Γ |- t ⇝ℇ et ->
  forall x, KernameSet.In x (term_global_deps et) -> declared_kn Σ x.
Proof.
  intros wf wt er.
  induction er in T, wt |- * using erases_forall_list_ind;
    cbn in *; try solve [constructor]; intros kn' hin;
    repeat match goal with
    | [ H : KernameSet.In _ KernameSet.empty |- _ ] =>
      now apply KernameSet.empty_spec in hin
    | [ H : KernameSet.In _ (KernameSet.union _ _) |- _ ] =>
      apply KernameSet.union_spec in hin as [?|?]
    end.
  - apply inversion_Lambda in wt as (? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & h1 & ? & ?); eauto.
    now apply unlift_TermTyp in h1.
  - apply inversion_LetIn in wt as (? & ? & ? & ?); eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    eapply KernameSet.singleton_spec in hin; subst.
    unshelve eapply declared_constant_to_gen in d; eauto.
    red in d. red. sq. rewrite d. intuition eauto.
  - apply inversion_Construct in wt as (? & ? & ? & ? & ? & ? & ?); eauto.
    destruct kn.
    eapply KernameSet.singleton_spec in hin; subst.
    destruct d as [[H' _] _].
    unshelve eapply declared_minductive_to_gen in H'; eauto.
    red in H'. simpl in *.
    red. sq. rewrite H'. intuition eauto.
  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    destruct ci as [kn i']; simpl in *.
    eapply KernameSet.singleton_spec in H1; subst.
    destruct x1 as [d _].
    unshelve eapply declared_minductive_to_gen in d; eauto.
    red in d.
    simpl in *. eexists; intuition eauto.
  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    eapply knset_in_fold_left in H1.
    destruct H1. eapply IHer; eauto.
    destruct H1 as [br [inbr inkn]].
    eapply Forall2_All2 in H0.
    assert (All (fun br => ∑ T, Σ ;;; Γ ,,, inst_case_branch_context p br |- br.(bbody) : T) brs).
    eapply All2i_All_right. eapply brs_ty.
    simpl. intuition auto. eexists ; eauto.
    now rewrite -(PCUICCasesContexts.inst_case_branch_context_eq a).
    eapply All2_All_mix_left in H0; eauto. simpl in H0.
    eapply All2_In_right in H0; eauto.
    destruct H0.
    destruct X1 as [br' [[T' HT] ?]].
    eauto.

  - eapply KernameSet.singleton_spec in H0; subst.
    apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?&?); eauto.
    unshelve eapply declared_projection_to_gen in d; eauto.
    destruct d as [[[d _] _] _].
    red in d. eexists; eauto.

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.

  - apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    eapply knset_in_fold_left in hin as [|].
    now eapply KernameSet.empty_spec in H0.
    destruct H0 as [? [ina indeps]].
    eapply Forall2_All2 in H.
    eapply All2_All_mix_left in H; eauto.
    eapply All2_In_right in H; eauto.
    destruct H as [[def [Hty Hdef]]].
    apply unlift_TermTyp in Hty.
    eapply Hdef; eauto.

  - apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    eapply knset_in_fold_left in hin as [|].
    now eapply KernameSet.empty_spec in H0.
    destruct H0 as [? [ina indeps]].
    eapply Forall2_All2 in H.
    eapply All2_All_mix_left in H; eauto.
    eapply All2_In_right in H; eauto.
    destruct H as [[def [Hty Hdef]]].
    apply unlift_TermTyp in Hty.
    eapply Hdef; eauto.

  - eapply inversion_Prim in wt as [prim_ty [decl []]]; eauto.
    move: hin.
    funelim (prim_global_deps _ _); try knset.
    rewrite knset_in_fold_left. depelim H0; cbn in *.
    depelim X. depelim p1. depelim H. depelim X.
    intuition eauto.
    destruct H as [a [hin inkn]]. cbn in hin.
    eapply All2_All_mix_left in a2; tea.
    eapply All2_In_right in a2 as [[x []]]; tea. eapply d1; tea.
Qed.

Global Remove Hints erases_deps_eval : core.

Lemma erase_global_erases_deps {Σ} {Σ' : EAst.global_declarations} {Γ t et T} :
  wf_ext Σ ->
  Σ;;; Γ |- t : T ->
  Σ;;; Γ |- t ⇝ℇ et ->
  includes_deps Σ Σ' (term_global_deps et) ->
  erases_deps Σ Σ' et.
Proof.
  intros wf wt er.
  induction er in er, t, T, wf, wt |- * using erases_forall_list_ind;
    cbn in *; try solve [constructor]; intros Σer;
    repeat match goal with
    | [ H : includes_deps _ _ (KernameSet.union _ _ ) |- _ ] =>
      apply includes_deps_union in H as [? ?]
    end.
  - now apply inversion_Evar in wt.
  - constructor.
    now apply inversion_Lambda in wt as (? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & h1 & ? & ?); eauto.
    apply unlift_TermTyp in h1.
    constructor; eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
    now constructor; eauto.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    specialize (Σer kn).
    forward Σer. rewrite KernameSet.singleton_spec //.
    pose proof (wf' := wf.1).
    unshelve eapply declared_constant_to_gen in d; eauto.
    destruct Σer as [[c' [declc' (? & ? & ? & ?)]]|].
    unshelve eapply declared_constant_to_gen in declc'; eauto.
    pose proof (declared_constant_inj _ _ d declc'). subst x.
    econstructor; eauto. eapply declared_constant_from_gen; eauto.
    destruct H as [mib [mib' [declm declm']]].
    unshelve eapply declared_minductive_to_gen in declm; eauto.
    red in declm, d. unfold declared_minductive_gen in declm.
    rewrite d in declm. noconf declm.
  - apply inversion_Construct in wt as (? & ? & ? & ? & ? & ?); eauto.
    red in Σer. destruct kn.
    setoid_rewrite KernameSetFact.singleton_iff in Σer.
    pose (wf' := wf.1).
    destruct (Σer _ eq_refl) as [ (? & ? & ? & ? & ? & ?) | (? & ? & ? & ? & ?) ].
    + destruct d as [[]].
      unshelve eapply declared_constant_to_gen in H0; eauto.
      unshelve eapply declared_minductive_to_gen in H4; eauto.
      red in H4, H. cbn in *. unfold PCUICEnvironment.fst_ctx in *. congruence.
    + pose proof H2 as H2'. destruct d. cbn in *.
      destruct H3. cbn in *. red in H3.
      unshelve eapply declared_minductive_to_gen in H0, H3; eauto.
      red in H0, H3. rewrite H0 in H3. invs H3.
      destruct H2.
      red in H1.
      eapply Forall2_nth_error_Some_l in H2 as (? & ? & ?); eauto. pose proof H6 as H6'. destruct H6 as (? & ? & ? & ? & ?); eauto.
      eapply Forall2_nth_error_Some_l in H6 as ([] & ? & ? & ?); subst; eauto.
      econstructor.
      eapply declared_constructor_from_gen; eauto.  repeat eapply conj; eauto.
      repeat eapply conj; cbn; eauto. eauto. eauto.
  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    destruct ci as [[kn i'] ? ?]; simpl in *.
    apply includes_deps_fold in H2 as [? ?].
    pose proof (wf' := wf.1).
    specialize (H1 kn). forward H1.
    now rewrite KernameSet.singleton_spec. red in H1. destruct H1.
    exfalso. destruct H1 as [cst [declc _]].
    { destruct x1 as [d _].
      unshelve eapply declared_minductive_to_gen in d; eauto.
      unshelve eapply declared_constant_to_gen in declc; eauto.
      red in d, declc.
      unfold declared_constant_gen in declc. rewrite d in declc. noconf declc. }
    destruct H1 as [mib [mib' [declm [declm' em]]]].
    pose proof em as em'. destruct em'.
    destruct x1 as [x1 hnth].
    unshelve eapply declared_minductive_to_gen in x1, declm; eauto.
    red in x1, declm. unfold declared_minductive_gen in declm. rewrite x1 in declm. noconf declm.
    eapply Forall2_nth_error_left in H1; eauto. destruct H1 as [? [? ?]].
    eapply erases_deps_tCase; eauto.
    apply declared_inductive_from_gen; auto.
    split; eauto. split; eauto.
    apply All2_length in X. rewrite -X.
    destruct H5. apply Forall2_length in H5. rewrite -H5.
    now apply Forall2_length in wf_brs.
    destruct H1.
    eapply In_Forall in H3.
    eapply All_Forall. eapply Forall_All in H3.
    eapply Forall2_All2 in H0.
    eapply All2_All_mix_right in H0; eauto.
    assert (All (fun br => ∑ T, Σ ;;; Γ ,,, inst_case_branch_context p br |- br.(bbody) : T) brs).
    eapply All2i_All_right. eapply brs_ty.
    simpl. intuition auto. eexists ; eauto.
    now rewrite -(PCUICCasesContexts.inst_case_branch_context_eq a).
    ELiftSubst.solve_all. destruct a0 as [T' HT]. eauto.

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?&?); eauto.
    destruct (proj1 d).
    pose proof (wf' := wf.1).
    specialize (H0 (inductive_mind p.(proj_ind))). forward H0.
    now rewrite KernameSet.singleton_spec. red in H0. destruct H0.
    exfalso. destruct H0 as [cst [declc _]].
    {
      unshelve eapply declared_constant_to_gen in declc; eauto.
      red in declc. destruct d as [[[d _] _] _].
      unshelve eapply declared_minductive_to_gen in d; eauto.
      red in d.
      unfold declared_constant_gen in declc.  rewrite d in declc. noconf declc. }
    destruct H0 as [mib [mib' [declm [declm' em]]]].
    assert (mib = x0).
    { destruct d as [[[]]].
      unshelve eapply declared_minductive_to_gen in declm, H0; eauto.
      red in H0, declm. unfold declared_minductive_gen in declm. rewrite H0 in declm. now noconf declm. }
    subst x0.
    pose proof em as em'. destruct em'.
    eapply Forall2_nth_error_left in H0 as (x' & ? & ?); eauto.
    2:{ apply d. }
    simpl in *.
    destruct (ind_ctors x1) => //. noconf H3.
    set (H1' := H5). destruct H1' as [].
    set (d' := d). destruct d' as [[[]]].
    eapply Forall2_All2 in H3. eapply All2_nth_error_Some in H3 as [? [? []]]; tea.
    destruct H6 as [Hprojs _].
    eapply Forall2_All2 in Hprojs. eapply All2_nth_error_Some in Hprojs as [? []]; tea.
    2:eapply d.
    econstructor; tea. all:eauto.
    split => //. 2:split; eauto.
    split; eauto. split; eauto.
    rewrite -H4. symmetry; apply d.

  - constructor.
    apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    eapply All_Forall. eapply includes_deps_fold in Σer as [_ Σer].
    eapply In_Forall in Σer.
    eapply Forall_All in Σer.
    eapply Forall2_All2 in H.
    ELiftSubst.solve_all. apply unlift_TermTyp in b1; eauto.
  - constructor.
    apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    eapply All_Forall. eapply includes_deps_fold in Σer as [_ Σer].
    eapply In_Forall in Σer.
    eapply Forall_All in Σer.
    eapply Forall2_All2 in H.
    ELiftSubst.solve_all. apply unlift_TermTyp in b1; eauto.
  - eapply inversion_Prim in wt as [prim_ty [decl []]]; eauto.
    depelim H; depelim H0. depelim X; depelim X0; depelim p1; constructor;
    noconf H; cbn; simp prim_global_deps in Σer; simpl in *.
    eapply e0; eauto.
    red in Σer. intros kn; specialize (Σer kn).
    rewrite knset_in_fold_left in Σer. intuition eauto. cbn.
    eapply All_Forall.
    eapply includes_deps_fold in Σer as [? Σer].
    eapply In_Forall in Σer.
    eapply Forall_All in Σer.
    solve_all.
Qed.

Lemma erases_deps_weaken kn d (Σ : global_env) (Σ' : EAst.global_declarations) t :
  wf (add_global_decl Σ (kn, d)) ->
  erases_deps Σ Σ' t ->
  erases_deps (add_global_decl Σ (kn, d)) Σ' t.
Proof.
  intros wfΣ er.
  assert (wfΣ' : wf Σ)
    by now eapply strictly_extends_decls_wf; tea; split => //; eexists [_].
  induction er using erases_deps_forall_ind; try solve [now constructor].
  - inv wfΣ. inv X.
    assert (wf Σ) by (inversion H4;econstructor; eauto).
    pose proof (H_ := H). unshelve eapply declared_constant_to_gen in H; eauto.
    assert (kn <> kn0).
    { intros <-.
      eapply lookup_env_Some_fresh in H. destruct X1. contradiction. }
    eapply erases_deps_tConst with cb cb'; eauto.
    eapply declared_constant_from_gen.
    red. rewrite /declared_constant_gen /lookup_env lookup_env_cons_fresh //.
    red.
    red in H1.
    destruct (cst_body cb) eqn:cbe;
    destruct (E.cst_body cb') eqn:cbe'; auto.
    specialize (H3 _ eq_refl).
    eapply on_declared_constant in H_; auto.
    red in H_. rewrite cbe in H_. apply unlift_TermTyp in H_.
    eapply (erases_weakening_env (Σ := (Σ, cst_universes cb))
       (Σ' := (add_global_decl Σ (kn, d), cst_universes cb))); eauto.
    simpl. econstructor; eauto. econstructor; eauto.
    split => //; eexists [(kn, d)]; intuition eauto.
  - econstructor; eauto. eapply weakening_env_declared_constructor; eauto; tc.
    eapply extends_decls_extends, strictly_extends_decls_extends_decls. econstructor; try reflexivity. eexists [(_, _)]; reflexivity.
  - econstructor; eauto.
    eapply declared_inductive_from_gen.
    rename H3 into Hlen, H4 into H3, H5 into H4.
    inv wfΣ. inv X.
    assert (wf Σ) by (inversion H5;econstructor; eauto).
    unshelve eapply declared_inductive_to_gen in H; eauto.
    red. destruct H. split; eauto.
    red in H. red.
    rewrite -H. simpl. unfold lookup_env; simpl. destruct (eqb_spec (inductive_mind p.1) kn); try congruence.
    eapply lookup_env_Some_fresh in H. destruct X1. subst kn; contradiction.
  - econstructor; eauto.
    inv wfΣ. inv X.
    assert (wf Σ) by (inversion H3;econstructor; eauto).
    eapply declared_projection_from_gen.
    unshelve eapply declared_projection_to_gen in H; eauto.
    red. destruct H. split; eauto.
    destruct H; split; eauto.
    destruct H; split; eauto.
    red in H |- *.
    rewrite -H. simpl. unfold lookup_env; simpl; destruct (eqb_spec (inductive_mind p.(proj_ind)) kn); try congruence.
    eapply lookup_env_Some_fresh in H. subst kn. destruct X1. contradiction.
  - solve_all. depelim H; econstructor; intuition eauto.
    solve_all.
Qed.

Lemma lookup_env_ext {Σ kn kn' d d'} :
  wf (add_global_decl Σ (kn', d')) ->
  lookup_env Σ kn = Some d ->
  kn <> kn'.
Proof.
  intros wf hl.
  eapply lookup_env_Some_fresh in hl.
  inv wf. inv X.
  destruct (eqb_spec kn kn'); subst; destruct X1; congruence.
Qed.

Lemma lookup_env_cons_disc {Σ kn kn' d} :
  kn <> kn' ->
  lookup_env (add_global_decl Σ (kn', d)) kn = lookup_env Σ kn.
Proof.
  intros Hk. simpl; unfold lookup_env; simpl.
  destruct (eqb_spec kn kn'); congruence.
Qed.

Lemma elookup_env_cons_disc {Σ kn kn' d} :
  kn <> kn' ->
  EGlobalEnv.lookup_env ((kn', d) :: Σ) kn = EGlobalEnv.lookup_env Σ kn.
Proof.
  intros Hk. simpl.
  destruct (eqb_spec kn kn'); congruence.
Qed.

Lemma global_erases_with_deps_cons kn kn' d d' Σ Σ' :
  wf (add_global_decl Σ (kn', d)) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps (add_global_decl Σ (kn', d)) ((kn', d') :: Σ') kn.
Proof.
  intros wf [[cst [declc [cst' [declc' [ebody IH]]]]]|].
  red. inv wf. inv X.
  assert (wfΣ : PCUICTyping.wf Σ).
  { eapply strictly_extends_decls_wf; split; tea ; eauto. econstructor; eauto.
    now eexists [_].
  }
  left.
  exists cst. split.
  eapply declared_constant_from_gen.
  unshelve eapply declared_constant_to_gen in declc; eauto.
  red in declc |- *. unfold declared_constant_gen, lookup_env in *.
  rewrite lookup_env_cons_fresh //.
  { eapply lookup_env_Some_fresh in declc. destruct X1.
    intros <-; contradiction. }
  exists cst'.
  pose proof (declc_ := declc).
  unshelve eapply declared_constant_to_gen in declc; eauto.
  unfold EGlobalEnv.declared_constant. rewrite EGlobalEnv.elookup_env_cons_fresh //.
  { eapply lookup_env_Some_fresh in declc. destruct X1.
    intros <-; contradiction. }
  red in ebody. unfold erases_constant_body.
  destruct (cst_body cst) eqn:bod; destruct (E.cst_body cst') eqn:bod' => //.
  intuition auto.
  eapply (erases_weakening_env (Σ  := (_, cst_universes cst)) (Σ' := (add_global_decl Σ (kn', d), cst_universes cst))); eauto.
  constructor; eauto. constructor; eauto.
  split => //. exists [(kn', d)]; intuition eauto.
  eapply on_declared_constant in declc_; auto.
  red in declc_. rewrite bod in declc_. eapply declc_.
  noconf H0.
  eapply erases_deps_cons; eauto.
  constructor; auto.

  right.
  pose proof (wf_ := wf). inv wf. inv X.
  assert (wf Σ) by (inversion H0;econstructor; eauto).
  destruct H as [mib [mib' [? [? ?]]]].
  unshelve eapply declared_minductive_to_gen in H; eauto.
  exists mib, mib'. intuition eauto.
  * eapply declared_minductive_from_gen.
    red. red in H. pose proof (lookup_env_ext wf_ H). unfold declared_minductive_gen.
    now rewrite lookup_env_cons_disc.
  * red. pose proof (lookup_env_ext wf_ H).
    now rewrite elookup_env_cons_disc.
Qed.

Lemma global_erases_with_deps_weaken kn kn' d Σ Σ' :
  wf (add_global_decl Σ (kn', d)) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps (add_global_decl Σ (kn', d)) Σ' kn.
Proof.
  intros wf [[cst [declc [cst' [declc' [ebody IH]]]]]|].
  red. inv wf. inv X. left.
  assert (wfΣ : PCUICTyping.wf Σ).
  { eapply strictly_extends_decls_wf; split; tea ; eauto. econstructor; eauto.
    now eexists [_].
  }
  exists cst. split.
  eapply declared_constant_from_gen.
  unshelve eapply declared_constant_to_gen in declc; eauto.
  red in declc |- *.
  unfold declared_constant_gen, lookup_env in *.
  rewrite lookup_env_cons_fresh //.
  { eapply lookup_env_Some_fresh in declc.
    intros <-. destruct X1. contradiction. }
  exists cst'.
  unfold EGlobalEnv.declared_constant.
  red in ebody. unfold erases_constant_body.
  destruct (cst_body cst) eqn:bod; destruct (E.cst_body cst') eqn:bod' => //.
  intuition auto.
  eapply (erases_weakening_env (Σ  := (Σ, cst_universes cst)) (Σ' := (add_global_decl Σ (kn', d), cst_universes cst))). 5:eauto.
  split; auto. constructor; eauto. constructor; eauto.
  split; auto; exists [(kn', d)]; intuition eauto.
  eapply on_declared_constant in declc; auto.
  red in declc. rewrite bod in declc. eapply declc.
  noconf H0.
  apply erases_deps_weaken; auto.
  constructor; eauto. constructor; eauto.

  right. destruct H as [mib [mib' [Hm [? ?]]]].
  exists mib, mib'; intuition auto. pose proof (wf_ := wf).
  inv wf. inv X.
  assert (wf Σ) by (inversion H;econstructor; eauto).
  eapply declared_minductive_from_gen.

  unshelve eapply declared_minductive_to_gen in Hm; eauto.
  red. unfold declared_minductive_gen, lookup_env in *.
  rewrite lookup_env_cons_fresh //.
  now epose proof (lookup_env_ext wf_ Hm).
Qed.

Lemma erase_global_includes X_type (X:X_type.π1) deps decls {normalization_in} prf deps' :
  (forall d, KernameSet.In d deps' ->
    forall Σ : global_env, abstract_env_rel X Σ -> ∥ ∑ decl, lookup_env Σ d = Some decl ∥) ->
  KernameSet.subset deps' deps ->
  forall Σ : global_env, abstract_env_rel X Σ ->
  let Σ' := erase_global_deps deps X decls (normalization_in:=normalization_in) prf in
  includes_deps Σ (fst Σ') deps'.
Proof.
  intros ? sub Σ wfΣ; cbn. induction decls in X, H, sub, prf, deps, deps', Σ , wfΣ, normalization_in |- *.
  - simpl. intros i hin. exfalso.
    edestruct (H i hin) as [[decl Hdecl]]; eauto.
    rewrite /lookup_env (prf _ wfΣ) in Hdecl. noconf Hdecl.
  - intros i hin.
    destruct (abstract_env_wf _ wfΣ) as [wf].
    destruct a as [kn d].
    eapply KernameSet.subset_spec in sub.
    edestruct (H i hin) as [[decl Hdecl]]; eauto. unfold lookup_env in Hdecl.
    pose proof (eqb_spec i kn).
    rewrite (prf _ wfΣ) in Hdecl. move: Hdecl. cbn -[erase_global_deps].
    elim: H0. intros -> [= <-].
    * destruct d as [|]; [left|right].
      { cbn. set (Xpop := abstract_pop_decls X).
        unfold erase_constant_decl.
        set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _).
        epose proof (abstract_env_exists Xpop) as [[Σpop wfpop]].
        epose proof (abstract_env_ext_exists Xmake) as [[Σmake wfmake]].
        exists c. split; auto.
        eapply declared_constant_from_gen.
        unfold declared_constant_gen, lookup_env; simpl; rewrite (prf _ wfΣ). cbn.
        rewrite eq_kername_refl //.
        pose proof (sub _ hin) as indeps.
        eapply KernameSet.mem_spec in indeps.
        unfold EGlobalEnv.declared_constant.
        edestruct (H _ hin) as [[decl hd]]; eauto.
        eexists; intuition eauto.
        rewrite indeps. cbn.
        rewrite eq_kername_refl. reflexivity.
        cut (strictly_extends_decls Σpop Σ) => [?|].
        eapply (erase_constant_body_correct _ _ _ _ (Σpop , _)); eauto.
        rewrite <- (abstract_make_wf_env_ext_correct Xpop (cst_universes c) _ Σpop Σmake wfpop wfmake); eauto.
        { now eapply strictly_extends_decls_wf. }
        red. simpl. unshelve epose (abstract_pop_decls_correct X decls _ Σ Σpop wfΣ wfpop).
        { intros. now eexists. }
        split => //. intuition eauto.
        exists [(kn, ConstantDecl c)]; intuition eauto. rewrite H0; eauto.
        now destruct a.
        rewrite indeps. unshelve epose proof (abstract_pop_decls_correct X decls _ Σ Σpop wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
        { intros. now eexists. }
        pose (prf' := prf _ wfΣ).
        destruct Σ. cbn in *. rewrite Hpop' Hpop'' prf'. rewrite <- Hpop at 1.
        eapply (erases_deps_cons Σpop).
          rewrite <- Hpop'. apply wf.
          rewrite Hpop. rewrite prf' in wf. destruct wf. now rewrite Hpop'' Hpop' in o0.

        pose proof (erase_constant_body_correct' H0). specialize_Σ wfmake.
        sq. destruct H1 as [bod [bodty [[Hbod Hebod] Heqdeps]]].
        rewrite (abstract_make_wf_env_ext_correct Xpop (cst_universes c) _ Σpop Σmake wfpop wfmake) in Hbod, Hebod.
        eapply (erase_global_erases_deps (Σ := (Σpop, cst_universes c))); simpl; auto.
        { constructor; simpl; auto. depelim wf. rewrite Hpop' Hpop'' in o0.
          cbn in o0, o. rewrite prf' in o0. rewrite  <- Hpop in o0. rewrite Hpop' in o. clear -o o0.
          now depelim o0.
          depelim wf. rewrite Hpop' in o0.
          cbn in o0, o. rewrite prf' in o0.  rewrite <- Hpop in o0. clear -o0. depelim o0.
          now destruct o.
           }
        all: eauto.
        apply IHdecls; eauto.
        { intros. pose proof (abstract_env_wf _ wfpop) as [wf'].
          destruct Σpop. cbn in *. clear prf'.  subst.
          unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wfΣ H2) as [Hpop Hpop'].
          { intros. now eexists. }
          destruct Σ.  cbn in *. subst.
          eapply term_global_deps_spec in Hebod; eauto. }
        {  eapply KernameSet.subset_spec.
          intros x hin'. eapply KernameSet.union_spec. right; auto.
          now rewrite -Heqdeps. } }
        { eexists m, _; intuition eauto.
          eapply declared_minductive_from_gen.
          simpl. rewrite /declared_minductive /declared_minductive_gen /lookup_env prf; eauto.
          simpl. rewrite eq_kername_refl. reflexivity.
          specialize (sub _ hin).
          eapply KernameSet.mem_spec in sub.
          simpl. rewrite sub.
          red. cbn. rewrite eq_kername_refl.
          reflexivity.
          assert (declared_minductive Σ kn m).
          { eapply declared_minductive_from_gen. red. unfold declared_minductive_gen, lookup_env. rewrite prf; eauto. cbn. now rewrite eqb_refl. }
          eapply on_declared_minductive in H0; tea.
          now eapply erases_mutual. }

    * intros ikn Hi.
      destruct d as [|].
      ++ simpl. destruct (KernameSet.mem kn deps) eqn:eqkn.
        unfold erase_constant_decl.
        set (Xpop := abstract_pop_decls X).
        set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _).
        epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
        pose proof (abstract_env_wf _ wfpop) as [wfΣp].
        unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
        { intros. now eexists. }
        pose proof (prf _ wfΣ). destruct Σ. cbn in *. subst.
        eapply global_erases_with_deps_cons; eauto.
        eapply (IHdecls Xpop _ _ _ (KernameSet.singleton i)); auto.
        3:{ eapply KernameSet.singleton_spec => //. }
        intros.
        eapply KernameSet.singleton_spec in H0.
        pose proof (abstract_env_irr _ H1 wfpop). subst.
        sq; exists decl; eauto.
        eapply KernameSet.subset_spec. intros ? ?.
        eapply KernameSet.union_spec. left.
        eapply KernameSet.singleton_spec in H0; subst.
        now eapply sub.

        cbn. set (Xpop := abstract_pop_decls X).
        epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
        pose proof (abstract_env_wf _ wfpop) as [wfΣp].
        unshelve epose proof (abstract_pop_decls_correct X decls _ Σ Σp wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
        { intros. now eexists. }
        pose proof (prf _ wfΣ). destruct Σ. cbn in *. subst.
        eapply global_erases_with_deps_weaken. eauto.
        eapply IHdecls => //.
        3:now eapply KernameSet.singleton_spec.
        intros d ind%KernameSet.singleton_spec.
        intros. pose proof (abstract_env_irr _ H0 wfpop). subst.
        sq; eexists; eauto.
        eapply KernameSet.subset_spec.
        intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst.

      ++ simpl. set (Xpop := abstract_pop_decls X).
      epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
      pose proof (abstract_env_wf _ wfpop) as [wfΣp].
      unshelve epose proof (abstract_pop_decls_correct X decls _ Σ Σp wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
      { intros. now eexists. }
      pose proof (prf _ wfΣ). destruct Σ. cbn in *. subst.
      destruct (KernameSet.mem kn deps) eqn:eqkn.
        { eapply (global_erases_with_deps_cons _ kn (InductiveDecl _) _ Σp); eauto.
          eapply (IHdecls Xpop _ _ _ (KernameSet.singleton i)); auto.
          3:{ eapply KernameSet.singleton_spec => //. }
          intros.
          eapply KernameSet.singleton_spec in H0. subst.
          pose proof (abstract_env_irr _ H1 wfpop). subst.
          sq; eexists; eauto.
          eapply KernameSet.subset_spec. intros ? ?.
          eapply KernameSet.singleton_spec in H0; subst.
          now eapply sub. }

        { eapply (global_erases_with_deps_weaken _ kn (InductiveDecl _) Σp). eauto.
          eapply (IHdecls Xpop _ _ _  (KernameSet.singleton i)) => //.
          3:now eapply KernameSet.singleton_spec.
          intros d ind%KernameSet.singleton_spec.
          intros. pose proof (abstract_env_irr _ H0 wfpop). subst.
          sq; eexists; eauto.
          eapply KernameSet.subset_spec.
          intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst. }
Qed.

Lemma erase_correct (wfl := EWcbvEval.default_wcbv_flags) X_type (X : X_type.π1)
  univs wfext t v Σ' t' deps decls {normalization_in} prf
  (Xext :=  abstract_make_wf_env_ext X univs wfext)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ}
  :
  forall wt : forall Σ, Σ ∼_ext Xext -> welltyped Σ [] t,
  erase X_type Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_deps deps X decls (normalization_in:=normalization_in) prf = Σ' ->
  (forall Σ : global_env, abstract_env_rel X Σ -> Σ |-p t ⇓ v) ->
  forall Σ : global_env_ext, abstract_env_ext_rel Xext Σ ->
  exists v', Σ ;;; [] |- v ⇝ℇ v' /\ ∥ fst Σ' ⊢ t' ⇓ v' ∥.
Proof.
  intros wt.
  intros HΣ' Hsub Ht' ev Σext wfΣex.
  pose proof (erases_erase (X := Xext) wt).
  rewrite HΣ' in H.
  destruct (wt _ wfΣex) as [T wt'].
  pose proof (abstract_env_ext_wf _ wfΣex) as [wfΣ].
  specialize (H _ wfΣex).
  unshelve epose proof (erase_global_erases_deps (Σ' := fst Σ') wfΣ wt' H _); cycle 2.
  rewrite <- Ht'.
  eapply erase_global_includes; eauto.
  intros. eapply term_global_deps_spec in H; eauto.
  now rewrite (abstract_make_wf_env_ext_correct X univs wfext Σ _ H1 wfΣex) in H.

  epose proof (abstract_env_exists X) as [[Σ wfΣX]].
  now rewrite (abstract_make_wf_env_ext_correct X univs wfext Σ _ wfΣX wfΣex).
  epose proof (abstract_env_exists X) as [[Σ wfΣX]].
  eapply erases_correct; tea.
  - eexists; eauto.
  - rewrite (abstract_make_wf_env_ext_correct X univs wfext _ _ wfΣX wfΣex); eauto.
Qed.

Lemma global_env_ind (P : global_env -> Type)
  (Pnil : forall univs retro, P {| universes := univs; declarations := []; retroknowledge := retro |})
  (Pcons : forall (Σ : global_env) d, P Σ -> P (add_global_decl Σ d))
  (Σ : global_env) : P Σ.
Proof.
  destruct Σ as [univs Σ].
  induction Σ; cbn. apply Pnil.
  now apply (Pcons {| universes := univs; declarations := Σ |} a).
Qed.

Lemma on_global_env_ind (P : forall Σ : global_env, wf Σ -> Type)
  (Pnil : forall univs retro (onu : on_global_univs univs), P {| universes := univs; declarations := []; retroknowledge := retro |}
    (onu, globenv_nil _ _ _ _))
  (Pcons : forall (Σ : global_env) kn d (wf : wf Σ)
    (Hfresh : fresh_global kn Σ.(declarations))
    (udecl := PCUICLookup.universes_decl_of_decl d)
    (onud : on_udecl Σ.(universes) udecl)
    (pd : on_global_decl cumulSpec0 (lift_typing typing)
    ({| universes := Σ.(universes); declarations := Σ.(declarations); retroknowledge := Σ.(retroknowledge) |}, udecl) kn d),
    P Σ wf -> P (add_global_decl Σ (kn, d))
    (fst wf, globenv_decl _ _ Σ.(universes) Σ.(retroknowledge) Σ.(declarations) kn d (snd wf)
            {| kn_fresh := Hfresh ; on_udecl_udecl := onud ; on_global_decl_d := pd |}))
  (Σ : global_env) (wfΣ : wf Σ) : P Σ wfΣ.
Proof.
  destruct Σ as [univs Σ]. destruct wfΣ; cbn in *.
  induction o0. apply Pnil. destruct o1.
  apply (Pcons {| universes := univs; declarations := Σ |} kn d (o, o0)).
  exact IHo0.
Qed.

Ltac inv_eta :=
  lazymatch goal with
  | [ H : PCUICEtaExpand.expanded _ _ |- _ ] => depelim H
  end.

Lemma leq_term_propositional_sorted_l {Σ Γ v v' u u'} :
   wf_ext Σ ->
   PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
   Σ;;; Γ |- v : tSort u ->
   Σ;;; Γ |- v' : tSort u' -> Sort.is_propositional u ->
   leq_sort (global_ext_constraints Σ) u' u.
Proof.
  intros wfΣ leq hv hv' isp.
  eapply leq_term_prop_sorted_l; eauto.
Qed.

Lemma map_erase_irrel X_type X {normalization_in1 normalization_in2 : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ t H1 H2 :
  erase_terms X_type X Γ t H1 (normalization_in:=normalization_in1) = erase_terms X_type X Γ t H2 (normalization_in:=normalization_in2).
Proof.
  eapply erase_irrel.
Qed.

Lemma erase_mkApps {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ t args H2 Ht Hargs :
  (forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> wf_local Σ Γ) ->
  (forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ~ ∥ isErasable Σ Γ (mkApps t args) ∥) ->
  erase X_type X Γ (mkApps t args) H2 =
  E.mkApps (erase X_type X Γ t Ht) (erase_terms X_type X Γ args Hargs).
Proof.
  epose proof (abstract_env_ext_exists X) as [[Σ wfΣX]].
  pose proof (abstract_env_ext_wf X wfΣX) as [wf].
  intros Hwflocal Herasable. induction args in t, H2, Ht, Hargs, Herasable |- *.
  - cbn. eapply erase_irrel.
  - cbn [mkApps].
    rewrite IHargs; clear IHargs.
    all: intros; specialize_Σ H; try pose proof (abstract_env_ext_wf _ H) as [wfH].
    1: inversion Hargs; eauto. depelim X0. now sq.
    2: eauto.
    2:{ destruct H2. cbn in X0. eapply inversion_mkApps in X0 as (? & ? & ?).
        econstructor. eauto. }
    etransitivity. simp erase. reflexivity. unfold erase_clause_1.
    unfold inspect. unfold erase_clause_1_clause_2.
    elim: is_erasableP.
    + intros. exfalso.
      eapply Herasable; eauto. specialize_Σ wfΣX. destruct p.
      cbn. destruct H2. eapply Is_type_app; eauto.
    + cbn [erase_terms].
      epose proof (fst (erase_irrel _ _)). cbn.
      intros he. f_equal => //. f_equal.
      eapply erase_irrel. eapply erase_irrel.
      eapply map_erase_irrel.
Qed.

Lemma map_erase_length X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ t H1 : length (erase_terms X_type X Γ t H1) = length t.
Proof.
  induction t; cbn; f_equal; eauto.
Qed.

Local Hint Constructors expanded : expanded.

Local Arguments erase_global_deps _ _ _ _ _ : clear implicits.

(*Lemma lookup_env_erase X_type X deps decls normalization_in prf kn d :
  KernameSet.In kn deps ->
  forall Σ : global_env, abstract_env_rel X Σ -> lookup_env Σ kn = Some (InductiveDecl d) ->
  EGlobalEnv.lookup_env (erase_global_deps X_type deps X decls normalization_in prf) kn = Some (EAst.InductiveDecl (erase_mutual_inductive_body d)).
Proof.
  intros hin Σ wfΣ. pose proof (prf _ wfΣ). unfold lookup_env. rewrite H. clear H.
  rewrite /lookup_env.
  induction decls in X, Σ , wfΣ ,prf, deps, hin, normalization_in |- *.
  - move=> /= //.
  - destruct a as [kn' d'].
    cbn -[erase_global_deps].
    case: (eqb_spec kn kn'); intros e'; subst.
    intros [= ->].
    unfold erase_global_deps.
    eapply KernameSet.mem_spec in hin. rewrite hin /=.
    now rewrite eq_kername_refl.
    intros hl. destruct d'. simpl.
    set (Xpop := abstract_pop_decls X).
    set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _).
    epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
    destruct KernameSet.mem. cbn.
    rewrite (negbTE (proj2 (neqb _ _) e')).
    eapply IHdecls => //; eauto. eapply KernameSet.union_spec. left => //.
    eapply IHdecls => //; eauto.
    simpl.
    set (Xpop := abstract_pop_decls X).
    epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
    destruct KernameSet.mem. cbn.
    rewrite (negbTE (proj2 (neqb _ _) e')).
    eapply IHdecls => //; eauto.
    eapply IHdecls => //; eauto.
Qed.
*)

Lemma lookup_env_erase_decl_None X_type X deps decls normalization_in prf kn :
  forall Σ : global_env, abstract_env_rel X Σ -> lookup_env Σ kn = None ->
  EGlobalEnv.lookup_env (erase_global_deps X_type deps X decls normalization_in prf).1 kn = None.
Proof.
  intros Σ wfΣ.
  pose proof (prf _ wfΣ).
  unfold lookup_env. rewrite H. clear H.
  rewrite /lookup_env.
  induction decls in X, Σ , wfΣ ,prf, deps, normalization_in |- *.
  - move=> /= //.
  - destruct a as [kn' d'].
    cbn -[erase_global_deps].
    case: (eqb_spec kn kn'); intros e'; subst.
    intros [= ->].
    cbn. destruct d'. cbn.
    case_eq (KernameSet.mem kn' deps); move => hin'; cbn.
    + destruct (eqb_spec kn kn') => //.
      set (Xpop := abstract_pop_decls X).
      epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
      now eapply IHdecls.
    + intros. set (Xpop := abstract_pop_decls X).
      epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
      now eapply IHdecls.
    + intros hin.
      case_eq (KernameSet.mem kn' deps); move => hin'; cbn.
      destruct (eqb_spec kn kn') => //.
      set (Xpop := abstract_pop_decls X).
      epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
      now eapply IHdecls.
      intros. set (Xpop := abstract_pop_decls X).
      epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
      now eapply IHdecls.
Qed.

Lemma lookup_env_erase_global_diff X_type X deps decls kn kn' d' normalization_in prf :
  kn <> kn' ->
  exists deps' nin' prf',
    KernameSet.Subset deps deps' /\
    EGlobalEnv.lookup_env (erase_global_deps X_type deps X ((kn', d') :: decls) normalization_in prf).1 kn =
    EGlobalEnv.lookup_env (erase_global_deps X_type deps' (abstract_pop_decls X) decls nin' prf').1 kn /\
    (KernameSet.In kn (erase_global_deps X_type deps X ((kn', d') :: decls) normalization_in prf).2 ->
      KernameSet.In kn (erase_global_deps X_type deps' (abstract_pop_decls X) decls nin' prf').2).
Proof.
  intros hd.
  simpl. destruct d'.
  + destruct KernameSet.mem. cbn.
    destruct (eqb_spec kn kn') => //.
    do 3 eexists. split; [|split;[reflexivity|]]. knset.
    auto.
    do 3 eexists. split; [|split;[reflexivity|]]. knset.
    auto.
  + destruct KernameSet.mem. cbn.
    destruct (eqb_spec kn kn') => //.
    do 3 eexists. split; [|split;[reflexivity|]]. knset. auto.
    do 3 eexists. split; [|split;[reflexivity|]]. knset. auto.
Qed.

Lemma lookup_env_In_map_fst Σ kn decl : lookup_global Σ kn = Some decl -> In kn (map fst Σ).
Proof.
  induction Σ; cbn => //.
  case: eqb_spec.
  + intros -> [= <-]. now left.
  + intros _ hl. eauto.
Qed.

Lemma erase_constant_decl_deps {X_type : abstract_env_impl} (X : X_type.π1) (cb : constant_body) normalization_in oncb :
  forall Σ : global_env, abstract_env_rel X Σ ->
  forall kn, KernameSet.In kn (erase_constant_decl X cb normalization_in oncb).2 -> In kn (map fst (declarations Σ)).
Proof.
  intros Σ wfΣ kn.
  unfold erase_constant_decl.
  set (ec := erase_constant_body _ _ _ _).
  destruct cb. destruct cst_body0.
  2:{ subst ec; cbn. knset. }
  intros hc.
  epose proof (erase_constant_body_correct' (@eq_refl _ (EAst.cst_body ec.1))).
  subst ec.
  set (ec := erase_constant_body _ _ _ _) in *.
  set (X' := abstract_make_wf_env_ext _ _ _) in *.
  pose proof (abstract_env_ext_exists X') as [[Σ' H']].
  pose proof (abstract_env_ext_wf _ H') as [wfΣ'].
  specialize (H _ H') as [[t0 [T []]]].
  rewrite -e in hc.
  destruct p as [hty her].
  epose proof (term_global_deps_spec wfΣ' hty her _ hc).
  epose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ wfΣ H'). cbn in H0. subst Σ'.
  red in H. destruct H as [[decl hl]].
  now eapply lookup_env_In_map_fst in hl.
Qed.

Lemma in_erase_global_deps_acc X_type X deps decls kn normalization_in prf  :
  KernameSet.In kn (erase_global_deps X_type deps X decls normalization_in prf).2 ->
  KernameSet.In kn deps \/ In kn (map fst decls).
Proof.
  induction decls in X, prf, deps, normalization_in |- *.
  cbn; auto. destruct a as [kn' []].
  + cbn. set (ec := erase_constant_decl _ _ _ _).
  set (eg := erase_global_deps _ _ _ _ _ _).
  set (eg' := erase_global_deps _ _ _ _ _ _).
    case_eq (KernameSet.mem kn' deps).
  * cbn; intros. specialize (IHdecls _ _ _ _ H0).
    destruct IHdecls as [Hu|Hm]; auto.
    eapply KernameSet.union_spec in Hu. destruct Hu; auto.
    unfold ec in H1; cbn in H1.
    set (Xpop := abstract_pop_decls X).
    epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
    eapply erase_constant_decl_deps in H1; tea.
    pose proof (abstract_env_exists X) as [[ΣX HX]].
    unshelve epose proof (abstract_pop_decls_correct _ decls _ _ _ HX wfpop).
    intros. rewrite prf => //. now eexists.
    now destruct H2 as [<- _].
  * intros hdeps hin.
    eapply IHdecls in hin. intuition auto.
  + cbn; set (eg := erase_global_deps _ _ _ _ _ _);
    set (eg' := erase_global_deps _ _ _ _ _ _).
    case_eq (KernameSet.mem kn' deps).
  * cbn; intros. specialize (IHdecls _ _ _ _ H0).
    destruct IHdecls as [Hu|Hm]; auto.
  * intros hdeps hin.
    eapply IHdecls in hin. intuition auto.
Qed.

Lemma wf_fresh_globals {cf : checker_flags} (Σ : global_env) : wf Σ -> EnvMap.EnvMap.fresh_globals Σ.(declarations).
Proof.
  destruct Σ as [univs Σ]; cbn.
  move=> [] onu; cbn. induction 1; try destruct o; constructor; auto; constructor; eauto.
Qed.

Lemma lookup_env_erase_decl X_type X deps decls normalization_in prf kn decl :
  forall Σ : global_env, abstract_env_rel X Σ -> lookup_env Σ kn = Some decl ->
  let er := erase_global_deps X_type deps X decls normalization_in prf in
  KernameSet.In kn er.2 ->
    match decl with
    | ConstantDecl cb =>
      exists (X' : X_type.π1) nin pf,
        (EGlobalEnv.lookup_env er.1 kn =
          Some (EAst.ConstantDecl (fst (erase_constant_decl X' cb nin pf)))) /\
          (forall Σ Σ', Σ ∼ X -> Σ' ∼ X' -> ∥ strictly_extends_decls Σ' Σ ∥)
    | InductiveDecl mib =>
      EGlobalEnv.lookup_env er.1 kn =
        Some (EAst.InductiveDecl (erase_mutual_inductive_body mib))
    end.
Proof.
  intros Σ wfΣ. pose proof (prf _ wfΣ).
  unfold lookup_env. rewrite H. clear H.
  rewrite /lookup_env.
  induction decls in X, Σ , wfΣ ,prf, deps, decl, normalization_in |- *.
  - move=> /= //.
  - destruct a as [kn' d'].
    cbn -[erase_global_deps].
    case: (eqb_spec kn kn'); intros e'; subst.
    intros [= ->].
    destruct decl.
    + cbn; set (ec := erase_constant_decl _ _ _ _);
      set (eg := erase_global_deps _ _ _ _ _ _);
      set (eg' := erase_global_deps _ _ _ _ _ _).
      case_eq (KernameSet.mem kn' deps).
      move/KernameSet.mem_spec => hin'; cbn.
    ++ intros hin. cbn; rewrite eqb_refl;
      do 3 eexists. split; [reflexivity|].
      intros ? ? hx hpop.
      unshelve epose proof (abstract_pop_decls_correct _ decls _ _ _ hx hpop). intros. rewrite prf => //. now eexists.
      destruct H as [? []]. unfold strictly_extends_decls. rewrite H. sq; split => //. clear ec eg eg' hin. specialize (prf _ hx). rewrite prf.
      now eexists [_].
    ++ intros kn'deps kn'eg'.
      eapply in_erase_global_deps_acc in kn'eg'.
      destruct kn'eg'. eapply KernameSet.mem_spec in H. congruence.
      exfalso. clear -prf wfΣ H.
      specialize (prf _ wfΣ).
      pose proof (abstract_env_wf _ wfΣ) as []. eapply wf_fresh_globals in X0.
      rewrite prf in X0. depelim X0.
      apply EnvMap.EnvMap.fresh_global_iff_not_In in H0. contradiction.
    + cbn;
      set (eg := erase_global_deps _ _ _ _ _ _);
      set (eg' := erase_global_deps _ _ _ _ _ _).
      case_eq (KernameSet.mem kn' deps).
      move/KernameSet.mem_spec => hin'; cbn.
      ++ intros hin. cbn; rewrite eqb_refl;
        do 3 eexists.
      ++ intros kn'deps kn'eg'.
        eapply in_erase_global_deps_acc in kn'eg'.
        destruct kn'eg'. eapply KernameSet.mem_spec in H. congruence.
        exfalso. clear -prf wfΣ H.
        specialize (prf _ wfΣ).
        pose proof (abstract_env_wf _ wfΣ) as []. eapply wf_fresh_globals in X0.
        rewrite prf in X0. depelim X0.
        apply EnvMap.EnvMap.fresh_global_iff_not_In in H0. contradiction.
    + intros hl hin.
      epose proof (lookup_env_erase_global_diff X_type X deps decls kn kn' d' _ _ e').
      destruct H as [deps' [nin' [prf' [sub [hl' hin']]]]].
      eapply hin' in hin.
      erewrite hl'.
      set (Xpop := abstract_pop_decls X).
      epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
      specialize (IHdecls Xpop deps'). specialize (IHdecls nin' prf' decl _ wfpop hl hin).
      destruct decl; intuition auto.
      destruct IHdecls as [X' [nin [pf []]]]. exists X', nin, pf. split => //.
      intros.
      unshelve epose proof (abstract_pop_decls_correct _ decls _ _ _ H1 wfpop). intros. rewrite prf => //. now eexists.
      specialize (H0 _ _ wfpop H2). destruct H0; sq. move: X0; rewrite /strictly_extends_decls. destruct H3 as [? []].
      rewrite H4 H0 H3. rewrite -(prf' _ wfpop). pose proof (prf _ H1). rewrite -H0 in H5. rewrite H5.
      intros []; split => //. destruct s as [Σ'' eq]. eexists ((kn', d') :: Σ''). now rewrite eq.
Qed.

Lemma fresh_global_app kn Σ Σ' : fresh_global kn (Σ ++ Σ') ->
  fresh_global kn Σ /\ fresh_global kn Σ'.
Proof.
  induction Σ; cbn; intuition auto.
  - constructor.
  - depelim H. constructor => //.
    now eapply Forall_app in H0.
  - depelim H.
    now eapply Forall_app in H0.
Qed.

Lemma lookup_global_app_wf Σ Σ' kn : EnvMap.EnvMap.fresh_globals (Σ ++ Σ') ->
  forall decl, lookup_global Σ' kn = Some decl -> lookup_global (Σ ++ Σ') kn = Some decl.
Proof.
  induction Σ in kn |- *; cbn; auto.
  intros fr; depelim fr.
  intros decl hd; cbn.
  destruct (eqb_spec kn kn0).
  eapply PCUICWeakeningEnv.lookup_global_Some_fresh in hd.
  subst. now eapply fresh_global_app in H as [H H'].
  now eapply IHΣ.
Qed.

Lemma strictly_extends_decls_lookup {Σ Σ'} :
  wf Σ' ->
  strictly_extends_decls Σ Σ' ->
  forall kn d, lookup_env Σ kn = Some d ->
  lookup_env Σ' kn = Some d.
Proof.
  intros.
  destruct X0 as [? []].
  rewrite /lookup_env in H *. rewrite e0.
  erewrite lookup_global_app_wf. reflexivity. 2:eauto.
  eapply wf_fresh_globals in X. now rewrite -e0.
Qed.

Lemma in_deps_in_erase_global_deps X_type X deps decls normalization_in prf kn :
  KernameSet.In kn deps ->
  KernameSet.In kn (erase_global_deps X_type deps X decls normalization_in prf).2.
Proof.
  induction decls in X, deps, normalization_in, prf |- *.
  - intros. now cbn.
  - intros. cbn.
    pose proof (abstract_env_exists X) as [[Σ H']].
    set (Xpop := abstract_pop_decls X).
    epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
    unshelve epose proof (abstract_pop_decls_correct _ decls _ _ _ H' wfpop). intros. rewrite prf => //. now eexists.
    destruct H0 as [Hd [Hu Hr]].
    destruct a. destruct g.
    + set (eg := erase_global_deps _ _ _ _ _ _);
      set (eg' := erase_global_deps _ _ _ _ _ _).
      case_eq (KernameSet.mem k deps).
      * cbn. intros hm.
        destruct (eqb_spec k kn).
        ++ subst k. eapply IHdecls. knset.
        ++ eapply IHdecls.
           knset.
      * intros hnin. eapply IHdecls; tea.
    +  set (eg := erase_global_deps _ _ _ _ _ _);
      set (eg' := erase_global_deps _ _ _ _ _ _).
      case_eq (KernameSet.mem k deps).
      * cbn. intros hm.
        destruct (eqb_spec k kn).
        ++ subst k. eapply KernameSet.mem_spec in hm.
          now eapply IHdecls.
      ++ eapply IHdecls. tea.
    * intros hnin. eapply IHdecls; tea.
Qed.

Fixpoint filter_deps deps decls :=
  match decls with
  | [] => []
  | (kn, decl) :: decls =>
    if KernameSet.mem kn deps then
      match decl with
      | EAst.ConstantDecl cst =>
        (kn, decl) :: filter_deps (KernameSet.union deps (constant_decls_deps cst)) decls
      | _ => (kn, decl) :: filter_deps deps decls
      end
    else filter_deps deps decls
  end.

Lemma erase_global_deps_erase_global (X_type : abstract_env_impl) (X:X_type.π1) deps decls {normalization_in} prf :
  (@erase_global_deps X_type deps X decls normalization_in prf).1 =
  filter_deps deps (@erase_global X_type X decls normalization_in prf).
Proof.
  symmetry.
  generalize normalization_in at 1.
  generalize prf at 1.
  intros prf' normalization_in'.
  induction decls in normalization_in, normalization_in', prf, prf', X, deps |- *.
  - cbn. auto.
  - destruct a as [kn []].
    cbn.
    + destruct (KernameSet.mem kn deps).
      destruct c as [? [] ? ?].
      set (ec := erase_constant_decl _ _ _ _).
      set (ec' := erase_constant_decl _ _ _ _).
      assert (ec = ec') as <-.
      { unfold ec, ec'. eapply erase_constant_decl_irrel. red. cbn.
        intros. pose proof (abstract_env_irr _ H H0). subst. red. split; auto. congruence. }
      cbn; f_equal. set (d := KernameSet.union _ _). eapply IHdecls.
      cbn. f_equal. eapply IHdecls.
      eapply IHdecls.
    + cbn; destruct (KernameSet.mem kn deps).
      cbn. f_equal. eapply IHdecls.
      eapply IHdecls.
Qed.


Lemma filter_deps_filter {efl : EWellformed.EEnvFlags} deps Σ :
  EWellformed.wf_glob Σ ->
  (* (forall kn, KernameSet.In kn deps -> In kn (map fst Σ)) -> *)
  filter_deps deps Σ = filter (flip KernameSet.mem (global_deps Σ deps) ∘ fst) Σ.
Proof.
  induction Σ in deps |- *.
  - now cbn.
  - destruct a as [kn [[[]]|]].
    + cbn. unfold flip.
      destruct (knset_mem_spec kn deps).
      * case: (knset_mem_spec kn _).
        ** intros hin' hwf. f_equal. depelim hwf. now eapply IHΣ.
        ** intros nhin.
          elim: nhin.
          rewrite global_deps_union.
          rewrite KernameSet.union_spec. left.
          now eapply in_global_deps.
      * intros hwf.
        case: (knset_mem_spec kn _); intros hin.
        ** exfalso.
            depelim hwf.
            eapply in_global_deps_fresh in hin => //.
        ** depelim hwf. rewrite -IHΣ => //.
    + intros wf; depelim wf.
      cbn. unfold flip.
      * case: (knset_mem_spec kn _).
        ** intros hin'.
          case: (knset_mem_spec kn _) => hin''.
          ++ f_equal. now eapply IHΣ.
          ++ elim: hin''.
            rewrite !global_deps_union.
            rewrite KernameSet.union_spec. left.
            now eapply in_global_deps.
      ** intros hwf.
        case: (knset_mem_spec kn _); intros hin.
        *** exfalso.
            eapply in_global_deps_fresh in hin => //.
        *** rewrite -IHΣ => //.
    + intros wf; depelim wf.
      cbn. unfold flip.
      * case: (knset_mem_spec kn _).
        ** intros hin'.
          case: (knset_mem_spec kn _) => hin''.
          ++ f_equal. rewrite IHΣ //. eapply filter_ext.
             intros ?. unfold flip. rewrite global_deps_union /=.
             rewrite global_deps_empty.
             now rewrite KernameSetFact.union_b KernameSetFact.empty_b orb_false_r.
          ++ elim: hin''.
            rewrite !global_deps_union.
            rewrite KernameSet.union_spec. left.
            now eapply in_global_deps.
      ** intros hwf.
        case: (knset_mem_spec kn _); intros hin.
        *** exfalso.
            eapply in_global_deps_fresh in hin => //.
        *** rewrite -IHΣ => //.
Qed.

Lemma erase_global_declared_constructor X_type X ind c mind idecl cdecl deps decls normalization_in prf:
   forall Σ : global_env, abstract_env_rel X Σ -> declared_constructor Σ (ind, c) mind idecl cdecl ->
   KernameSet.In ind.(inductive_mind) deps ->
   EGlobalEnv.declared_constructor (erase_global_deps X_type deps X decls normalization_in prf).1 (ind, c)
    (erase_mutual_inductive_body mind) (erase_one_inductive_body idecl)
    (EAst.mkConstructor cdecl.(cstr_name) cdecl.(cstr_arity)).
Proof.
  intros Σ wfΣ [[]] Hin. pose (abstract_env_wf _ wfΣ). sq.
  cbn in *. split. split.
  - unshelve eapply declared_minductive_to_gen in H; eauto.
    red in H |- *. eapply (lookup_env_erase_decl _ _ _ _ _ _ _ (InductiveDecl mind)); eauto.
    eapply in_deps_in_erase_global_deps; tea.

  - cbn. now eapply map_nth_error.
  - cbn. erewrite map_nth_error; eauto.
Qed.

Import EGlobalEnv.
Lemma erase_global_deps_fresh X_type kn deps X decls normalization_in heq :
  let Σ' := erase_global_deps X_type deps X decls normalization_in heq in
  PCUICAst.fresh_global kn decls ->
  fresh_global kn Σ'.1.
Proof.
  cbn.
  revert deps X normalization_in heq.
  induction decls; [cbn; auto|].
  - intros. red. constructor.
  - destruct a as [kn' d]. intros. depelim H.
    cbn in H, H0.
    destruct d as []; simpl; destruct KernameSet.mem.
    + cbn [EGlobalEnv.closed_env forallb]. cbn.
      constructor => //. eapply IHdecls => //.
    + eapply IHdecls => //.
    + constructor; auto.
      eapply IHdecls => //.
    + eapply IHdecls => //.
Qed.

Lemma erase_global_fresh X_type kn X decls normalization_in heq :
  let Σ' := @erase_global X_type X decls normalization_in heq in
  PCUICAst.fresh_global kn decls ->
  fresh_global kn Σ'.
Proof.
  cbn.
  revert X normalization_in heq.
  induction decls; [cbn; auto|].
  - intros. red. constructor.
  - destruct a as [kn' d]. intros. depelim H.
    cbn in H, H0. cbn.
    destruct d as []; simpl.
    + cbn [EGlobalEnv.closed_env forallb]. cbn.
      constructor => //. eapply IHdecls => //.
    + constructor; auto.
      eapply IHdecls => //.
Qed.

From MetaRocq.Erasure Require Import EEtaExpandedFix.

Lemma erase_brs_eq X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ p ts wt :
  erase_brs X_type X Γ p ts wt =
  All_Forall.map_All (fun br wt => (erase_context (bcontext br), erase X_type X _ (bbody br) wt)) ts wt.
Proof.
  funelim (All_Forall.map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma erase_fix_eq X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ ts wt :
  erase_fix X_type X Γ ts wt = All_Forall.map_All (fun d wt =>
    let dbody' := erase X_type X _ (dbody d) (fun Σ abs => proj2 (wt Σ abs)) in
    let dbody' := if isBox dbody' then
        match d.(dbody) with
        | tLambda na _ _ => E.tLambda (binder_name na) E.tBox
        | _ => dbody'
        end else dbody'
    in
    {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |}) ts wt.
Proof.
  funelim (All_Forall.map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //.
  rewrite (fst (erase_irrel _ _) _ _ _ _ (fun (Σ : global_env_ext) (abs : abstract_env_ext_rel X Σ) =>
    (map_All_obligation_1 x xs h Σ abs).p2)).
  destruct erase => //.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma erase_cofix_eq X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ ts wt :
  erase_cofix X_type X Γ ts wt = All_Forall.map_All (fun d wt =>
    let dbody' := erase X_type X _ (dbody d) wt in
    {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |}) ts wt.
Proof.
  funelim (All_Forall.map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //.
  apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma isConstruct_erase X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ t wt :
  ~ (PCUICEtaExpand.isConstruct t || PCUICEtaExpand.isFix t || PCUICEtaExpand.isRel t) ->
  ~ (isConstruct (erase X_type X Γ t wt) || isFix (erase X_type X Γ t wt) || isRel (erase X_type X Γ t wt)).
Proof.
  apply (erase_elim X_type X
    (fun Γ t wt e => ~ (PCUICEtaExpand.isConstruct t || PCUICEtaExpand.isFix t || PCUICEtaExpand.isRel t) -> ~ (isConstruct e || isFix e || isRel e))
    (fun Γ l awt e => True)
    (fun Γ p l awt e => True)
    (fun Γ l awt e => True)
    (fun Γ l awt e => True)); intros => //. bang.
Qed.

Lemma apply_expanded Σ Γ Γ' t t' :
  expanded Σ Γ t -> Γ = Γ' -> t = t' -> expanded Σ Γ' t'.
Proof. intros; now subst. Qed.

Lemma isLambda_inv t : isLambda t -> exists na ty bod, t = tLambda na ty bod.
Proof. destruct t => //; eauto. Qed.

Lemma erases_deps_erase (cf := config.extraction_checker_flags)
  {X_type X} univs
  (wfΣ : forall Σ, (abstract_env_rel X Σ) -> ∥ wf_ext (Σ, univs) ∥) decls {normalization_in} prf
  (X' :=  abstract_make_wf_env_ext X univs wfΣ)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
  Γ t
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) :
  let et := erase X_type X' Γ t wt in
  let deps := EAstUtils.term_global_deps et in
  forall Σ, (abstract_env_rel X Σ) ->
  erases_deps Σ (erase_global_deps X_type deps X decls normalization_in prf).1 et.
Proof.
  intros et deps Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
  pose proof (wt _ wfΣ'). destruct H. pose proof (wfΣ _ wf) as [w].
  rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ') in X0.
  eapply (erase_global_erases_deps w); tea.
  eapply (erases_erase (X := X') (Γ := Γ)).
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply erase_global_includes.
  intros. rewrite (abstract_env_irr _ H0 wf).
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply (erases_erase (X := X') (Γ := Γ)).
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply KernameSet.subset_spec. reflexivity.
  now cbn.
Qed.

Lemma erases_deps_erase_weaken (cf := config.extraction_checker_flags)
  {X_type X} univs
  (wfΣ : forall Σ, (abstract_env_rel X Σ) -> ∥ wf_ext (Σ, univs) ∥) decls {normalization_in} prf
  (X' :=  abstract_make_wf_env_ext X univs wfΣ)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
  Γ t
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t)
  deps :
  let et := erase X_type X'  Γ t wt in
  let tdeps := EAstUtils.term_global_deps et in
  forall Σ, (abstract_env_rel X Σ) ->
  erases_deps Σ (erase_global_deps X_type (KernameSet.union deps tdeps) X decls normalization_in prf).1 et.
Proof.
  intros et tdeps Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
  pose proof (wt _ wfΣ'). destruct H. pose proof (wfΣ _ wf) as [w].
  rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ') in X0.
  eapply (erase_global_erases_deps w); tea.
  eapply (erases_erase (X := X') (Γ := Γ)).
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply erase_global_includes.
  intros. rewrite (abstract_env_irr _ H0 wf).
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply (erases_erase (X := X') (Γ := Γ)).
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply KernameSet.subset_spec. intros x hin.
  eapply KernameSet.union_spec. now right.
  now cbn.
Qed.

Lemma eta_expand_erase {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Σ' {Γ t}
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) Γ' :
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
  PCUICEtaExpand.expanded Σ Γ' t ->
  erases_global Σ Σ' ->
  expanded Σ' Γ' (erase X_type X Γ t wt).
Proof.
  intros Σ wfΣ exp deps.
  pose proof (abstract_env_ext_wf _ wfΣ) as [wf].
  eapply expanded_erases. apply wf.
  eapply erases_erase; eauto. assumption.
  pose proof (wt _ wfΣ). destruct H as [T ht].
  eapply erases_global_erases_deps; tea.
  eapply erases_erase; eauto.
Qed.

Lemma erase_global_closed X_type X deps decls {normalization_in} prf :
  let X' := erase_global_deps X_type deps X decls normalization_in prf in
  EGlobalEnv.closed_env X'.1.
Proof.
  revert X normalization_in prf deps.
  induction decls; [cbn; auto|].
  intros X normalization_in prf deps.
  destruct a as [kn d].
  destruct d as []; simpl; destruct KernameSet.mem;
  unfold erase_constant_decl;
  set (Xpop := abstract_pop_decls X);
    try (set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _);
         assert (normalization_in_Xmake : forall Σ : global_env_ext, wf_ext Σ -> Σ ∼_ext Xmake -> NormalizationIn Σ)
           by (subst Xmake; unshelve eapply (normalization_in 0); revgoals; try reflexivity; cbn; lia)).
  + cbn [EGlobalEnv.closed_env forallb]. cbn.
    rewrite [forallb _ _](IHdecls) // andb_true_r.
    rewrite /test_snd /EGlobalEnv.closed_decl /=.
    destruct c as [ty [] univs]; cbn.
    unfold erase_constant_decl.
    set (obl := ErasureFunction.erase_constant_body_obligation_1 _ _ _ _ _).
    unfold erase_constant_body. cbn. clearbody obl. cbn in obl.
    2:auto.
    pose proof (abstract_env_ext_exists Xmake) as [[Σmake wfmake]].
    pose proof (abstract_env_ext_wf _ wfmake) as [[?]].
    unshelve epose proof (erases_erase (X := Xmake) (obl eq_refl) _ _) as H; eauto.
    eapply erases_closed in H.
    1: edestruct erase_irrel as [-> _]; eassumption.
    cbn. destruct (obl eq_refl _ wfmake). clear H.
    now eapply PCUICClosedTyp.subject_closed in X0.
  + eapply IHdecls => //.
  + cbn [EGlobalEnv.closed_env forallb].
    eapply IHdecls => //.
  + eapply IHdecls => //.
  Unshelve. eauto.
Qed.

Import EWellformed.

Section wffix.
  Import EAst.
  Fixpoint wf_fixpoints (t : term) : bool :=
    match t with
    | tRel i => true
    | tEvar ev args => List.forallb (wf_fixpoints) args
    | tLambda N M => wf_fixpoints M
    | tApp u v => wf_fixpoints u && wf_fixpoints v
    | tLetIn na b b' => wf_fixpoints b && wf_fixpoints b'
    | tCase ind c brs =>
      let brs' := forallb (wf_fixpoints ∘ snd) brs in
      wf_fixpoints c && brs'
    | tProj p c => wf_fixpoints c
    | tFix mfix idx =>
      (idx <? #|mfix|) && List.forallb (fun d => isLambda d.(dbody) && wf_fixpoints d.(dbody)) mfix
    | tCoFix mfix idx =>
      (idx <? #|mfix|) && List.forallb (wf_fixpoints ∘ dbody) mfix
    | tConst kn => true
    | tConstruct ind c _ => true
    | tVar _ => true
    | tBox => true
    | tPrim p => test_prim wf_fixpoints p
    | tLazy t => wf_fixpoints t
    | tForce t => wf_fixpoints t
    end.

End wffix.

Lemma erases_deps_wellformed (cf := config.extraction_checker_flags) (efl := all_env_flags) {Σ} {Σ'} et :
  erases_deps Σ Σ' et ->
  forall n, ELiftSubst.closedn n et ->
  wf_fixpoints et ->
  wellformed Σ' n et.
Proof.
  intros ed.
  induction ed using erases_deps_forall_ind; intros => //;
   try solve [cbn in *; unfold wf_fix in *; rtoProp; intuition eauto; PCUICAstUtils.solve_all].
  - cbn. red in H0. rewrite H0 //.
  - cbn -[lookup_constructor].
    cbn. now destruct H0 as [[-> ->] ->].
  - cbn in *. move/andP: H6 => [] cld clbrs.
    cbn. apply/andP; split. apply/andP; split.
    * rewrite /wf_brs. cbn. destruct H0 as [-> ->]. now apply Nat.eqb_eq.
    * now move/andP: H7.
    * move/andP: H7; PCUICAstUtils.solve_all.
  - cbn -[lookup_projection] in *. apply/andP; split; eauto.
    now rewrite (declared_projection_lookup H0).
  - cbn in H, H0 |- *. rtoProp; intuition eauto. solve_all_k 7.
Qed.

Lemma erases_wf_fixpoints Σ Γ t t' : Σ;;; Γ |- t ⇝ℇ t' ->
  ErasureProperties.wellformed Σ t -> wf_fixpoints t'.
Proof.
  induction 1 using erases_forall_list_ind; cbn; auto; try solve [rtoProp; repeat PCUICAstUtils.solve_all].
  - move/andP => []. rewrite (All2_length X) => -> /=. unfold test_def in *.
    eapply Forall2_All2 in H.
    eapply All2_All2_mix in X; tea. PCUICAstUtils.solve_all.
    destruct b0; eapply erases_isLambda in H1; tea.
  - move/andP => []. rewrite (All2_length X) => -> /=.
    unfold test_def in *. PCUICAstUtils.solve_all.
  - depelim H; depelim H0; depelim X; depelim X0; solve_all. noconf H.
    solve_all_k 7. cbn in H0. constructor; cbn; rtoProp; intuition eauto. solve_all.
Qed.

Lemma erase_wf_fixpoints (efl := all_env_flags) {X_type X} univs wfΣ {Γ t} wt
  (X' :=  abstract_make_wf_env_ext X univs wfΣ) {normalization_in} :
  let t' := erase X_type X' (normalization_in:=normalization_in) Γ t wt in
  wf_fixpoints t'.
Proof.
  cbn. pose proof (abstract_env_ext_exists X') as [[Σ' wf']].
  pose proof (abstract_env_exists X) as [[Σ wf]].
  eapply erases_wf_fixpoints.
  eapply erases_erase; eauto.
  specialize (wt _ wf'). destruct (wfΣ _ wf).
  unshelve eapply welltyped_wellformed in wt; eauto.
  now rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wf').
Qed.

Lemma erases_global_erase_global (efl := all_env_flags) {X_type X} Σ decls {normalization_in} prf :
  Σ ∼ X ->
  erases_global Σ (@erase_global X_type X decls normalization_in prf).
Proof.
  intros h. pose proof (prf _ h). red. rewrite H. clear H.
  induction decls in X, Σ, prf, normalization_in, h |- *.
  - cbn. constructor.
  - cbn.
    set (Xpop := abstract_pop_decls X).
    destruct (abstract_env_exists Xpop) as [[Σpop hpop]].
    unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ h hpop).
    intros; eexists; now eapply prf.
    destruct H as [? []].
    destruct a as [kn []].
    * constructor. cbn.
      unfold erase_constant_decl.
      set (Σd := {| universes := _ |}).
      assert (Σd = Σpop).
      { subst Σd. rewrite -H H0 H1. now destruct Σpop. }
      subst Σd.
      set (ext := abstract_make_wf_env_ext _ _ _).
      pose proof (abstract_env_ext_exists ext) as [[Σ' wf']].
      epose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X) (cst_universes c) _ _ _ hpop wf').
      subst Σ'.
      cbn. pose proof (abstract_env_wf _ hpop) as [].
      eapply (erase_constant_body_correct _ _ _ _ (Σpop, cst_universes c)) => //.
      now rewrite H2. rewrite H2. split => //. now exists [].
      rewrite H0 H1.
      now eapply IHdecls.
    * pose proof (abstract_env_wf _ h) as [wfΣ].
      destruct wfΣ. rewrite (prf _ h) in o0.
      depelim o0. depelim o1.
      constructor.
      eapply erases_mutual. eapply on_global_decl_d.
      rewrite H0 H1.
      now eapply IHdecls.
Qed.

Lemma erase_global_wellformed (efl := all_env_flags) {X_type X} decls {normalization_in} prf univs wfΣ {Γ t} wt
  (X' :=  abstract_make_wf_env_ext X univs wfΣ)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
  (t' := erase X_type X' Γ t wt) :
  wellformed (@erase_global X_type X decls normalization_in prf) #|Γ| t'.
Proof.
  cbn.
  epose proof (@erases_erase X_type X' normalization_in' _ _ wt).
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σ' wf']].
  pose proof (abstract_env_ext_wf _ wf') as [?].
  eapply (erases_wellformed (wt _ wf')) in H; eauto; tea.
  eapply erases_global_all_deps. apply X0.
  epose proof (abstract_make_wf_env_ext_correct _ _ wfΣ _ _ wf wf'). subst Σ'.
  now eapply erases_global_erase_global.
Qed.

Lemma erase_wellformed_deps (efl := all_env_flags) {X_type X} decls {normalization_in} prf univs wfΣ {Γ t} wt
  (X' :=  abstract_make_wf_env_ext X univs wfΣ)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
  (t' := erase X_type X' Γ t wt) :
  wellformed (erase_global_deps X_type (term_global_deps t') X decls normalization_in prf).1 #|Γ| t'.
Proof.
  cbn.
  epose proof (@erases_deps_erase X_type X univs wfΣ decls normalization_in prf _ Γ t wt).
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σ' wf']].
  pose proof (abstract_env_ext_wf _ wf') as [[?]].
  epose proof (erases_deps_wellformed _ H #|Γ|).
  apply H0.
  eapply (erases_closed _ Γ).
  destruct (wt _ wf').
  cbn in X. destruct (wfΣ _ wf).
  eapply PCUICClosedTyp.subject_closed in X0. eassumption.
  eapply erases_erase; eauto.
  eapply erase_wf_fixpoints. Unshelve. eauto.
Qed.

Lemma erase_wellformed_weaken (efl := all_env_flags) {X_type X} decls {normalization_in} prf univs wfΣ {Γ t} wt
(X' :=  abstract_make_wf_env_ext X univs wfΣ)
{normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
deps:
let t' := erase X_type X' Γ t wt in
  wellformed (erase_global_deps X_type (KernameSet.union deps (term_global_deps t')) X decls normalization_in prf).1 #|Γ| t'.
Proof.
  set (t' := erase _ _ _ _ _). cbn.
  epose proof (@erases_deps_erase_weaken _ X univs wfΣ decls _ prf _ Γ t wt deps).
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σ' wf']].
  pose proof (abstract_env_ext_wf _ wf') as [[?]].
  epose proof (erases_deps_wellformed _ H #|Γ|).
  apply H0.
  eapply (erases_closed _ Γ).
  - destruct (wt _ wf').
    destruct (wfΣ _ wf).
    eapply PCUICClosedTyp.subject_closed in X0. eassumption.
  - eapply erases_erase; eauto.
  - eapply erase_wf_fixpoints.
  Unshelve. eauto.
Qed.

Lemma erase_constant_body_correct'' {X_type X} {cb} {decls normalization_in prf} {univs wfΣ}
(X' :=  abstract_make_wf_env_ext X univs wfΣ)
{normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
{onc : forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' -> ∥ on_constant_decl (lift_typing typing) Σ' cb ∥} {body} deps :
  EAst.cst_body (fst (erase_constant_body X_type X' cb onc)) = Some body ->
  forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' ->
  ∥ ∑ t T, (cst_body cb = Some t) * (Σ' ;;; [] |- t : T) * (Σ' ;;; [] |- t ⇝ℇ body) *
      (term_global_deps body = snd (erase_constant_body X_type X'  cb onc)) *
      wellformed (efl:=all_env_flags) (erase_global_deps X_type (KernameSet.union deps (term_global_deps body)) X decls normalization_in prf).1 0 body ∥.
Proof.
  intros ? Σ' wfΣ'. pose proof (abstract_env_exists X) as [[Σ wf]].
  destruct cb as [name [bod|] udecl]; simpl.
  simpl in H. noconf H.
  set (obl :=(ErasureFunction.erase_constant_body_obligation_1 X_type X'
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := udecl |} onc bod eq_refl)). clearbody obl.
  destruct (obl _ wfΣ'). sq.
  have er : (Σ, univs);;; [] |- bod ⇝ℇ erase X_type X' [] bod obl.
  { eapply (erases_erase (X:=X')).
    now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
   }
  exists bod, A; intuition auto.
  now rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply erase_wellformed_weaken.
  now simpl in H.
Qed.

Lemma erase_global_cst_decl_wf_glob X_type X deps decls normalization_in heq :
  forall cb wfΣ hcb,
  let X' :=  abstract_make_wf_env_ext X (cst_universes cb) wfΣ in
  forall normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ,
  let ecb := erase_constant_body X_type X' cb hcb in
  let Σ' := erase_global_deps X_type (KernameSet.union deps ecb.2) X decls normalization_in heq in
  (@wf_global_decl all_env_flags Σ'.1 (EAst.ConstantDecl ecb.1) : Prop).
Proof.
  intros cb wfΣ hcb X' normalization_in' ecb Σ'.
  unfold wf_global_decl. cbn.
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σmake wfmake]].
  destruct (wfΣ _ wf), (hcb _ wfmake). red in X1.
  destruct EAst.cst_body eqn:hb => /= //.
  eapply (erase_constant_body_correct'') in hb; eauto.
  destruct hb as [[t0 [T [[] ?]]]]. rewrite e in i. exact i.
Qed.

Lemma erase_global_ind_decl_wf_glob {X_type X} {deps decls normalization_in kn m} heq :
  (forall Σ : global_env, abstract_env_rel X Σ -> on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes m) kn m) ->
  let m' := erase_mutual_inductive_body m in
  let Σ' := erase_global_deps X_type deps X decls normalization_in heq in
  @wf_global_decl all_env_flags Σ'.1 (EAst.InductiveDecl m').
Proof.
  set (m' := erase_mutual_inductive_body m).
  set (Σ' := erase_global_deps _ _ _ _ _ _). simpl.
  intros oni.
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_wf _ wf) as [wfΣ].
  assert (erases_mutual_inductive_body m (erase_mutual_inductive_body m)).
  { eapply (erases_mutual (mdecl:=kn)); tea. }
  eapply (erases_mutual_inductive_body_wf (univs := Σ.(universes)) (retro := Σ.(retroknowledge)) (Σ := decls) (kn := kn) (Σ' := Σ'.1)) in H; tea.
  rewrite -(heq _ wf). now destruct Σ.
Qed.

Lemma erase_global_deps_wf_glob X_type X deps decls normalization_in heq :
  let Σ' := erase_global_deps X_type deps X decls normalization_in heq in
  @wf_glob all_env_flags Σ'.1.
Proof.
  cbn.
  pose proof (abstract_env_exists X) as [[Σ wf]].
  pose proof (abstract_env_wf _ wf) as [wfΣ].
  revert deps X Σ wf wfΣ normalization_in heq.
  induction decls; [cbn; auto|].
  { intros. constructor. }
  intros. destruct a as [kn []]; simpl; destruct KernameSet.mem; set (Xpop := abstract_pop_decls X);
  try set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _);
  epose proof (abstract_env_exists Xpop) as [[Σpop wfpop]];
  pose proof (abstract_env_wf _ wfpop) as [wfΣpop].
  + constructor. eapply IHdecls => //; eauto. eapply erase_global_cst_decl_wf_glob; auto.
    eapply erase_global_deps_fresh; auto.
    destruct wfΣ. destruct wfΣpop.
    rewrite (heq _ wf) in o0. depelim o0. now destruct o3.
  + cbn. eapply IHdecls; eauto.
  + constructor. eapply IHdecls; eauto.
    destruct wfΣ as [[onu ond]].
    rewrite (heq _ wf) in o. depelim o. destruct o0.
    eapply (erase_global_ind_decl_wf_glob (kn:=kn)); tea.
    intros. rewrite (abstract_env_irr _ H wfpop).
    unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wf wfpop) as [? ?].
    {intros; now eexists. }
    destruct Σpop, Σ; cbn in *. now subst.
    eapply erase_global_deps_fresh.
    destruct wfΣ as [[onu ond]].
    rewrite (heq _ wf) in o. depelim o. now destruct o0.
  + eapply IHdecls; eauto.
Qed.

Lemma erase_constant_body_correct_glob {X_type X} {cb} {decls normalization_in prf} {univs wfΣ}
  (X' :=  abstract_make_wf_env_ext X univs wfΣ)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ}
  {onc : forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' -> ∥ on_constant_decl (lift_typing typing) Σ' cb ∥} {body} :
  EAst.cst_body (fst (erase_constant_body X_type X' cb onc)) = Some body ->
  forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' ->
  ∥ ∑ t T, (Σ' ;;; [] |- t : T) * (Σ' ;;; [] |- t ⇝ℇ body) *
      (term_global_deps body = snd (erase_constant_body X_type X'  cb onc)) *
      wellformed (efl:=all_env_flags) (@erase_global X_type X decls normalization_in prf) 0 body ∥.
Proof.
  intros ? Σ' wfΣ'. pose proof (abstract_env_exists X) as [[Σ wf]].
  destruct cb as [name [bod|] udecl]; simpl.
  simpl in H. noconf H.
  set (obl :=(ErasureFunction.erase_constant_body_obligation_1 X_type X'
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := udecl |} onc bod eq_refl)). clearbody obl.
  destruct (obl _ wfΣ'). sq.
  have er : (Σ, univs);;; [] |- bod ⇝ℇ erase X_type X' [] bod obl.
  { eapply (erases_erase (X:=X')).
    now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
   }
  exists bod, A; intuition auto.
  now rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply (erase_global_wellformed decls _ _ _ (Γ := [])).
  now simpl in H.
Qed.

Lemma erase_global_cst_wf_glob X_type X decls normalization_in heq :
  forall cb wfΣ hcb,
  let X' :=  abstract_make_wf_env_ext X (cst_universes cb) wfΣ in
  forall normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ,
  let ecb := erase_constant_body X_type X' cb hcb in
  let Σ' := @erase_global X_type X decls normalization_in heq in
  (@wf_global_decl all_env_flags Σ' (EAst.ConstantDecl ecb.1) : Prop).
Proof.
  intros cb wfΣ hcb X' normalization_in' ecb Σ'.
  unfold wf_global_decl. cbn.
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σmake wfmake]].
  destruct (wfΣ _ wf), (hcb _ wfmake). red in X1.
  destruct EAst.cst_body eqn:hb => /= //.
  eapply (erase_constant_body_correct_glob) in hb; eauto.
  destruct hb as [[t0 [T [[] ?]]]]. exact i.
Qed.

Lemma erase_global_ind_decl_wf_glob' {X_type X} {decls normalization_in kn m} heq :
  (forall Σ : global_env, abstract_env_rel X Σ -> on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes m) kn m) ->
  let m' := erase_mutual_inductive_body m in
  let Σ' := @erase_global X_type X decls normalization_in heq in
  @wf_global_decl all_env_flags Σ' (EAst.InductiveDecl m').
Proof.
  set (m' := erase_mutual_inductive_body m).
  set (Σ' := erase_global _ _ _). simpl.
  intros oni.
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_wf _ wf) as [wfΣ].
  assert (erases_mutual_inductive_body m (erase_mutual_inductive_body m)).
  { eapply (erases_mutual (mdecl:=kn)); tea. }
  eapply (erases_mutual_inductive_body_wf (univs := Σ.(universes)) (retro := Σ.(retroknowledge)) (Σ := decls) (kn := kn) (Σ' := Σ')) in H; tea.
  rewrite -(heq _ wf). now destruct Σ.
Qed.

Lemma erase_global_wf_glob X_type X decls normalization_in heq :
  let Σ' := @erase_global X_type X decls normalization_in heq in
  @wf_glob all_env_flags Σ'.
Proof.
  cbn.
  pose proof (abstract_env_exists X) as [[Σ wf]].
  pose proof (abstract_env_wf _ wf) as [wfΣ].
  revert X Σ wf wfΣ normalization_in heq.
  induction decls; [cbn; auto|].
  { intros. constructor. }
  intros. destruct a as [kn []]; simpl;  set (Xpop := abstract_pop_decls X);
  try set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _);
  epose proof (abstract_env_exists Xpop) as [[Σpop wfpop]];
  pose proof (abstract_env_wf _ wfpop) as [wfΣpop].
  + constructor. eapply IHdecls => //; eauto.
    eapply erase_global_cst_wf_glob; auto.
    eapply erase_global_fresh; auto.
    destruct wfΣ. destruct wfΣpop.
    rewrite (heq _ wf) in o0. depelim o0. now destruct o3.
  + constructor. eapply IHdecls; eauto.
    destruct wfΣ as [[onu ond]].
    rewrite (heq _ wf) in o. depelim o. destruct o0.
    eapply (erase_global_ind_decl_wf_glob' (kn:=kn)); tea.
    intros. rewrite (abstract_env_irr _ H wfpop).
    unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wf wfpop) as [? ?].
    { intros; now eexists. }
    destruct Σpop, Σ; cbn in *. now subst.
    eapply erase_global_fresh.
    destruct wfΣ as [[onu ond]].
    rewrite (heq _ wf) in o. depelim o. now destruct o0.
Qed.

Lemma extends_cons d Σ Σ' : extends Σ Σ' -> extends (d :: Σ) (d :: Σ').
Proof.
  intros ext kn decl.
  cbn.
  case: (eqb_spec kn d.1).
  - now intros -> [= <-].
  - intros hin. apply ext.
Qed.

Lemma extends_fresh Σ Σ' kn d :
  fresh_global kn Σ' ->
  extends Σ Σ' ->
  extends Σ ((kn, d) :: Σ').
Proof.
  intros fr ext.
  intros kn' decl hl.
  cbn. destruct (eqb_spec kn' kn) => //. subst.
  eapply ext in hl. now eapply lookup_env_Some_fresh in hl.
  now eapply ext.
Qed.

Lemma Forall_filter {A} {P} f l : @Forall A P l -> Forall P (filter f l).
Proof.
  induction 1; try econstructor; auto.
  cbn. case E: (f x) => //. now constructor.
Qed.

Lemma extends_filter_impl {efl : EEnvFlags} (f f' : kername * EAst.global_decl -> bool) Σ :
  (forall x, f x -> f' x) ->
  wf_glob Σ ->
  extends (filter f Σ) (filter f' Σ).
Proof.
  intros hf; induction Σ; cbn; auto.
  - red; auto.
  - intros wf; depelim wf.
    case E: (f _); auto. rewrite (hf _ E).
    now eapply extends_cons.
    case E': (f' _); auto.
    eapply extends_fresh. now eapply Forall_filter.
    auto.
Qed.

Lemma extends_filter {efl : EEnvFlags} (f : kername * EAst.global_decl -> bool) Σ :
  wf_glob Σ ->
  extends (filter f Σ) Σ.
Proof.
  intros wf hf; induction Σ; cbn; auto.
  intros decl. depelim wf. cbn in *.
  case E: (f _); auto; cbn.
  case (eqb_spec hf kn) => //.
  - intros hd. now eapply IHΣ.
  - intros hl; eapply IHΣ in hl => //. rewrite hl.
    case (eqb_spec hf kn) => heq.
    subst. now eapply lookup_env_Some_fresh in hl.
    reflexivity.
Qed.

Lemma erase_global_deps_eval {efl : EWcbvEval.WcbvFlags} (X_type : abstract_env_impl) (X X':X_type.π1) ext wfX wfX' {normalization_in} {normalization_in'} decls nin prf Γ t wt v wv :
  let Xext := abstract_make_wf_env_ext X ext wfX in
  let Xext' := abstract_make_wf_env_ext X' ext wfX' in
  let t' := erase X_type Xext (normalization_in := normalization_in) Γ t wt in
  let v' := erase X_type Xext' (normalization_in := normalization_in') Γ v wv in
  let eg := erase_global_deps X_type (term_global_deps t') X decls nin prf in
  let eg' := erase_global_deps X_type (term_global_deps v') X decls nin prf in
  eg.1 ⊢ t' ⇓ v' -> EGlobalEnv.extends eg'.1 eg.1.
Proof.
  intros.
  move: (erase_global_deps_wf_glob X_type X (term_global_deps t') decls nin prf).
  subst eg eg'.
  rewrite !erase_global_deps_erase_global.
  assert (wfer : wf_glob (efl := all_env_flags) (@erase_global X_type X decls nin prf)).
  { eapply erase_global_wf_glob. }
  rewrite !(filter_deps_filter (efl := all_env_flags)) //.
  cbn.
  intros wf.
  eapply extends_filter_impl; tea. unfold flip in *.
  intros [kn d]; cbn. clear d.
  rewrite /is_true !KernameSet.mem_spec. revert kn.
  eapply EWcbvEval.weakening_eval_env in H. 2:exact wfer.
  now eapply eval_global_deps in H.
  rewrite !erase_global_deps_erase_global (filter_deps_filter (efl := all_env_flags)) //.
  now eapply extends_filter.
Qed.

Lemma lookup_erase_global (cf := config.extraction_checker_flags) {X_type X} {deps deps' decls normalization_in prf} :
  KernameSet.Subset deps deps' ->
  EExtends.global_subset (erase_global_deps X_type deps X decls normalization_in prf).1 (erase_global_deps X_type deps' X decls normalization_in prf).1.
Proof.
  intros sub.
  rewrite !erase_global_deps_erase_global.
  assert (wfer : wf_glob (efl := all_env_flags) (@erase_global X_type X decls normalization_in prf)).
  { eapply erase_global_wf_glob. }
  rewrite !(filter_deps_filter (efl := all_env_flags)) //.
  eapply extends_filter_impl => //. 2:exact wfer.
  unfold flip.
  move=> x /KernameSet.mem_spec hin.
  apply/KernameSet.mem_spec.
  eapply global_deps_subset; tea.
Qed.

Lemma expanded_weakening_global X_type X deps deps' decls normalization_in prf Γ t :
  KernameSet.Subset deps deps' ->
  expanded (erase_global_deps X_type deps X decls normalization_in prf).1 Γ t ->
  expanded (erase_global_deps X_type deps' X decls normalization_in prf).1 Γ t.
Proof.
  intros hs.
  eapply expanded_ind; intros; try solve [econstructor; eauto].
  - eapply expanded_tFix; tea. solve_all.
  - eapply expanded_tConstruct_app; tea.
    destruct H. split; tea.
    destruct d; split => //.
    cbn in *. red in H.
    eapply lookup_erase_global in H; tea.
Qed.

Lemma expanded_erase (cf := config.extraction_checker_flags)
  {X_type X decls normalization_in prf} univs wfΣ t wtp :
  forall Σ : global_env, abstract_env_rel X Σ -> PCUICEtaExpand.expanded Σ [] t ->
  let X' :=  abstract_make_wf_env_ext X univs wfΣ in
  forall normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ,
  let et := (erase X_type X' [] t wtp) in
  let deps := EAstUtils.term_global_deps et in
  expanded (erase_global_deps X_type deps X decls normalization_in prf).1 [] et.
Proof.
  intros Σ wf hexp X' normalization_in'.
  pose proof (abstract_env_wf _ wf) as [wf'].
  pose proof (abstract_env_ext_exists X') as [[? wfmake]].
  eapply (expanded_erases (Σ := (Σ, univs))); tea.
  eapply (erases_erase (X := X')); eauto.
  now erewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ).
  cbn.
  eapply (erases_deps_erase (X := X) univs wfΣ); eauto.
Qed.

Lemma expanded_erase_global (cf := config.extraction_checker_flags)
  deps {X_type X decls normalization_in prf} :
  forall Σ : global_env, abstract_env_rel X Σ ->
    PCUICEtaExpand.expanded_global_env Σ ->
    expanded_global_env (erase_global_deps X_type deps X decls normalization_in prf).1.
Proof.
  intros Σ wf etaΣ. pose proof (prf _ wf).
  destruct Σ as [univ decls'].
  red. revert wf. red in etaΣ. cbn in *. subst.
  revert deps X normalization_in prf.
  induction etaΣ; intros deps. intros. constructor. intros.
  pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop wfpop]].
  unshelve epose proof (abstract_pop_decls_correct X Σ _ _ _ wf wfpop) as [? [? ?]].
  { now eexists. }
  destruct Σpop. cbn in H0, H1, H2. subst.
  destruct decl as [kn []];
  destruct (KernameSet.mem kn deps) eqn:eqkn; simpl; rewrite eqkn.
  constructor; [eapply IHetaΣ; auto|].
  red. cbn. red. cbn in *.
  unfold erase_constant_decl.
  set (deps' := KernameSet.union _ _). hidebody deps'.
  set (wfext :=  abstract_make_wf_env_ext _ _ _). hidebody wfext.
  destruct H.
  destruct c as [cst_na [cst_body|] cst_type cst_rel].
  cbn in *.
  eapply expanded_weakening_global.
  2:{ eapply expanded_erase; tea. }
  set (et := erase _ _ _ _) in *.
  unfold deps'. unfold hidebody. intros x hin.
  eapply KernameSet.union_spec. right => //.
  now cbn.
  eapply IHetaΣ; eauto.
  constructor. eapply IHetaΣ; eauto.
  red. cbn => //.
  eapply IHetaΣ; eauto.
Qed.

(* Sanity checks: the [erase] function maximally erases terms *)
Lemma erasable_tBox_value (wfl := EWcbvEval.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : wf_ext Σ) t T v :
  forall wt : Σ ;;; [] |- t : T,
  Σ |-p t ⇓ v -> erases Σ [] v E.tBox -> ∥ isErasable Σ [] t ∥.
Proof.
  intros.
  depind H.
  eapply Is_type_eval_inv; eauto. eexists; eauto.
Qed.

Lemma erase_eval_to_box (wfl := EWcbvEval.default_wcbv_flags)
  {X_type X} {univs wfext t v Σ' t' deps decls normalization_in prf}
  (Xext :=  abstract_make_wf_env_ext X univs wfext)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ}
  :
  forall wt : forall Σ : global_env_ext, abstract_env_ext_rel Xext Σ -> welltyped Σ [] t,
  erase X_type Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_deps X_type deps X decls normalization_in prf = Σ' ->
  forall Σext : global_env_ext, abstract_env_ext_rel Xext Σext ->
  (forall Σ : global_env, abstract_env_rel X Σ ->
    PCUICWcbvEval.eval Σ t v) ->
    @EWcbvEval.eval EWcbvEval.default_wcbv_flags Σ'.1 t' E.tBox -> ∥ isErasable Σext [] t ∥.
Proof.
  intros wt.
  intros.
  destruct (erase_correct X_type X univs wfext _ _ Σ' _ _ decls prf wt H H0 H1 X0 _ H2) as [ev [eg [eg']]].
  pose proof (EWcbvEval.eval_deterministic H3 eg'). subst.
  pose proof (abstract_env_exists X) as [[? wf]].
  destruct (wfext _ wf). destruct (wt _ H2) as [T wt'].
  pose proof (abstract_env_ext_wf _ H2) as [?].
  eapply erasable_tBox_value; eauto.
  pose proof (abstract_make_wf_env_ext_correct X univs wfext _ _ wf H2). subst.
  apply X0; eauto.
Qed.

Lemma erase_eval_to_box_eager (wfl := EWcbvEval.default_wcbv_flags)
  {X_type X} {univs wfext t v Σ' t' deps decls normalization_in prf}
  (Xext :=  abstract_make_wf_env_ext X univs wfext)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ}
  :
  forall wt : forall Σ : global_env_ext, abstract_env_ext_rel Xext Σ -> welltyped Σ [] t,
  erase X_type Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_deps X_type deps X decls normalization_in prf = Σ' ->
  forall Σext : global_env_ext, abstract_env_ext_rel Xext Σext ->
  (forall Σ : global_env, abstract_env_rel X Σ ->
    PCUICWcbvEval.eval Σ t v) ->
  @EWcbvEval.eval EWcbvEval.default_wcbv_flags Σ'.1 t' E.tBox -> t' = E.tBox.
Proof.
  intros wt.
  intros.
  destruct (erase_eval_to_box wt H H0 H1 _ H2 X0 H3).
  subst t'.
  destruct (inspect_bool (is_erasableb X_type Xext [] t wt)) eqn:heq.
  - simp erase. rewrite heq.
    simp erase => //.
  - exfalso.
    pose proof (abstract_env_exists X) as [[? wf]].
    destruct (@is_erasableP X_type Xext _ [] t wt) => //. apply n.
    intros. sq. now rewrite (abstract_env_ext_irr _ H H2).
Qed.

(*Inductive is_abstraction : EAst.term -> Prop :=
  | is_lam na b : is_abstraction (EAst.tLambda na b)
  | is_fix mfix idx : is_abstraction (EAst.tFix mfix idx). *)


Inductive firstorder_evalue Σ : EAst.term -> Prop :=
  | is_fo i n args npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  Forall (firstorder_evalue Σ) (skipn npars args) ->
  #|args| = npars + nargs ->
  firstorder_evalue Σ (EAst.mkApps (EAst.tConstruct i n []) args).

Lemma list_size_skipn {A} (l : list A) size n :
  list_size size (skipn n l) <= list_size size l.
Proof.
  induction n in l |- *.
  - rewrite skipn_0 //.
  - destruct l. rewrite skipn_nil. now cbn.
    rewrite skipn_S. cbn. specialize (IHn l); lia.
Qed.

Section elim.
  Context (Σ : E.global_context).
  Context (P : EAst.term -> Prop).
  Context (ih : (forall i n args npars nargs,
    EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
    Forall (firstorder_evalue Σ) (skipn npars args) ->
    Forall P (skipn npars args) ->
    #|args| = npars + nargs ->
    P (EAst.mkApps (EAst.tConstruct i n []) args))).

  Equations? firstorder_evalue_elim (t : EAst.term) (fo : firstorder_evalue Σ t) : P t by wf t (MR lt EInduction.size) :=
  { | _, is_fo i n args npars nargs hl hf hargs => _ }.
  Proof.
    eapply ih; tea.
    eapply In_Forall. intros x hin.
    eapply PCUICWfUniverses.Forall_In in hf; tea.
    apply firstorder_evalue_elim => //. red.
    rewrite EInduction.size_mkApps.
    eapply (In_size id EInduction.size) in hin.
    unfold id in *. pose proof (list_size_skipn args EInduction.size npars).
    change (fun x => EInduction.size x) with EInduction.size in hin. clear -hin H.
    eapply Nat.lt_le_trans; tea. cbn. lia.
  Qed.
End elim.


Lemma welltyped_mkApps_inv {cf} {Σ : global_env_ext} Γ f args :  ∥ wf Σ ∥ ->
  welltyped Σ Γ (mkApps f args) -> welltyped Σ Γ f /\ Forall (welltyped Σ Γ) args.
Proof.
  intros wf (A & HA). sq. eapply inversion_mkApps in HA as (? & ? & ?).
  split. eexists; eauto.
  induction t0 in f |- *; econstructor; eauto; econstructor; eauto.
Qed.

From MetaRocq.PCUIC Require Import PCUICProgress.

Lemma firstorder_erases_deterministic X_type (X : X_type.π1)
  univs wfext {v t' i u args}
  (Xext :=  abstract_make_wf_env_ext X univs wfext)
  {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ}
  :
  forall wv : (forall Σ, Σ ∼_ext Xext -> welltyped Σ [] v),
  forall Σ, Σ ∼_ext Xext ->
  Σ ;;; [] |- v : mkApps (tInd i u) args ->
  Σ |-p v ⇓ v ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  erases Σ [] v t' ->
  t' = erase X_type Xext (normalization_in:=normalization_in) [] v wv.
Proof.
  intros wv Σ Hrel Hty Hvalue Hfo Herase.
  destruct (firstorder_lookup_inv Hfo) as [mind Hdecl].
  assert (Hext : ∥ wf_ext Σ∥) by now eapply ErasureFunction.heΣ.
  sq. eapply firstorder_value_spec in Hty as Hfov; eauto.
  clear - Hrel Hext Hfov Herase.
  revert t' wv Herase.
  pattern v.
  revert v Hfov.
  eapply firstorder_value_inds. intros.
  rewrite erase_mkApps.
  - intros Σ0 HΣ0. pose proof (abstract_env_ext_irr _ HΣ0 Hrel). subst.
    eapply PCUICValidity.inversion_mkApps in X0 as (? & XX & Happ).
    clear XX. revert Happ. clear. generalize (mkApps (tInd i u) pandi). induction 1.
    + do 2 econstructor.
    + destruct IHHapp. do 2 econstructor. econstructor; eauto. eauto.
  - intros. eapply erases_mkApps_inv in Herase as [(? & ? & ? & -> & [Herasable] & ? & ? & ->)|(? & ? & -> & ? & ?)]. all:eauto.
    + exfalso. eapply isErasable_Propositional in Herasable; eauto. now rewrite Herasable in H1.
    + inv H2.
      * cbn. unfold erase_clause_1. destruct (inspect_bool (is_erasableb X_type Xext [] (tConstruct i n ui) Hyp0)).
        -- exfalso. sq. destruct (@is_erasableP _ _ _ [] (tConstruct i n ui) Hyp0) => //.
           specialize_Σ Hrel. sq.
           eapply (isErasable_Propositional (args := [])) in s; eauto.
           now rewrite s in H1.
        -- f_equal. eapply Forall2_eq. clear X0 H wv. induction H3.
           ++ cbn. econstructor.
           ++ cbn. econstructor.
               ** inv H0. eapply H5. eauto.
               ** inv H0. eapply IHForall2. eauto.
      * exfalso. eapply (isErasable_Propositional (args := [])) in X1; eauto.
        now rewrite X1 in H1.
  - eauto.
  - intros ? ? H3. assert (Hext_ : ∥ wf_ext Σ0∥) by now eapply ErasureFunction.heΣ.
    sq.
    specialize_Σ H2.
    eapply (isErasable_Propositional) in H3; eauto.
    pose proof (abstract_env_ext_irr _ H2 Hrel). subst.
    now rewrite H3 in H1.
  - intros.  assert (Hext__ : ∥ wf_ext Σ0∥) by now eapply ErasureFunction.heΣ.
    specialize_Σ H2. eapply welltyped_mkApps_inv in wv; eauto. eapply wv.
    now sq.
    Unshelve. all: try exact False.
  - eapply PCUICWcbvEval.eval_to_value; eauto.
Qed.

Lemma firstorder_evalue_extends Σ Σ' t :
  extends Σ Σ' ->
  firstorder_evalue Σ t ->
  firstorder_evalue Σ' t.
Proof.
  intros ext; move: t.
  apply: firstorder_evalue_elim => i n args npars nargs hl hf hargs ih.
  econstructor; tea.
  red in ext.
  move: hl; rewrite /lookup_constructor_pars_args /lookup_constructor /lookup_inductive /lookup_minductive.
  move: (ext (inductive_mind i)).
  now case: lookup_env => // a; move/(_ _ eq_refl) ->.
Qed.

Lemma In_map_All {A B C : Type} {Q : C -> Type} {P : C -> A -> Prop}
  (fn : forall x : A, (forall y : C, Q y -> P y x) -> B) (l : list A) (Hl : forall y : C, Q y -> ∥ All (P y) l ∥) :
  forall x, In x l ->
    exists D : forall y : C, Q y -> P y x,
      In (fn x D) (All_Forall.map_All fn l Hl).
Proof.
  induction l; cbn => //.
  intros x [].
  - subst. eexists; left; reflexivity.
  - destruct (IHl (map_All_obligation_2 a l Hl) _ H).
    eexists; now right.
Qed.

Lemma In_term_global_deps t l :
  In t l ->
  forall kn, KernameSet.In kn (term_global_deps t) -> KernameSet.In kn (terms_global_deps l).
Proof.
  induction l; cbn => //.
  intros [].
  - subst; intros kn hin; rewrite knset_in_fold_left.
    left. eapply KernameSet.union_spec. now left.
  - intros kn hin. specialize (IHl H).
    rewrite knset_in_fold_left. right. now exists t.
Qed.

Lemma erase_correct_strong' (wfl := EWcbvEval.default_wcbv_flags) X_type (X : X_type.π1)
  univs wfext {t v Σ' t' i u args} decls normalization_in prf
  (Xext :=  abstract_make_wf_env_ext X univs wfext)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ}
  :
  forall wt : (forall Σ, Σ ∼_ext Xext -> welltyped Σ [] t),
  forall Σ, abstract_env_ext_rel Xext Σ ->
  axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  erase X_type Xext [] t wt = t' ->
  erase_global_deps X_type (term_global_deps t') X decls normalization_in prf = Σ' ->
  red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  forall wt', let ev := erase X_type Xext [] v wt' in ∥ Σ'.1 ⊢ t' ⇓ ev ∥
  /\ firstorder_evalue Σ'.1 ev.
Proof.
  intros wt Σ Hrel Hax Hty Hfo <- <- Hred Hirred wt'.
  destruct (firstorder_lookup_inv Hfo) as [mind Hdecl].
  destruct (abstract_env_exists X) as [[Σg Hg]].
  pose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ Hg Hrel). subst Σ.
  pose proof (ErasureFunction.heΣ _ _ _ Hrel) as [Hwf]. eapply wcbv_standardization_fst in Hty as Heval; eauto.
  edestruct (erase_correct X_type X univs wfext t v) as [v' [H1 H2]]; eauto.
  { eapply KernameSet.subset_spec; reflexivity. }
  1:{ intros ? H_. sq. enough (Σ = Σg) as -> by eauto.
      pose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ H_ Hrel). now subst. }
  eapply firstorder_erases_deterministic in H1; eauto.
  simpl.
  destruct H2. split; [sq; tea|]. rewrite -> H1 in e. exact e.
  assert (PCUICFirstorder.firstorder_value (Σg, univs) [] v).
  { destruct (wfext Σg Hg). eapply PCUICFirstorder.firstorder_value_spec; tea. apply X0. constructor.
    eapply PCUICClassification.subject_reduction_eval; tea.
    eapply PCUICWcbvEval.eval_to_value; tea. }
  2:{ eapply subject_reduction; eauto. }
  { rewrite H1 in e. eapply erase_global_deps_eval in e.
    eapply firstorder_evalue_extends; tea. clear e.
    clear -Hrel H Hg Hwf. move: v H wt'.
    apply: PCUICFirstorder.firstorder_value_inds.
    intros i n ui u args pandi hty hf ih isp wt'.
    rewrite erase_mkApps //.
    { intros ? h; specialize (wt' _ h). eapply welltyped_mkApps_inv in wt' as [? ?] => //. destruct (abstract_env_ext_wf _ h).
       now sq; eapply Forall_All. pose proof (abstract_env_ext_wf _ h). now sq. }
    2:{ intros Σ hΣ [ise]. pose proof (abstract_env_ext_irr _ Hrel hΣ). subst Σ.
         eapply isErasable_Propositional in ise => //.
         cbn in isp, ise. now rewrite ise in isp. }
    2:{ intros Σ hΣ. pose proof (abstract_env_ext_irr _ Hrel hΣ). subst Σ.
        pose proof (iswelltyped hty).
        now eapply welltyped_mkApps_inv in H. }
    intros. simp erase.
    destruct inspect_bool; simp erase.
    move/is_erasableP: i0. intros hc.
    destruct (hc _ Hrel). eapply (isErasable_Propositional (args:=[])) in X0 => //. cbn in X0, isp => //.
    rewrite X0 in isp => //.
    eapply PCUICInductiveInversion.Construct_Ind_ind_eq' in hty as [mdecl [idecl [cdecl [declc [hcstr _]]]]] => //=.
    destruct hcstr as [_ hcstr].
    set (v := E.mkApps _ _).
    pose proof declc as declc'.
    eapply (erase_global_declared_constructor _ _ _ _ _ _ _ (term_global_deps v) decls normalization_in prf _ Hg) in declc; tea.
    destruct declc as [[hm hi] hc].
    2:{ rewrite /v /= term_global_deps_mkApps. destruct i => /=. eapply KernameSet.union_spec; left. now eapply KernameSet.singleton_spec. }
    2:{ eapply Hwf. }
    econstructor.
    { rewrite /lookup_constructor_pars_args /lookup_constructor /lookup_inductive /lookup_minductive hm /= hi //= hc //. }
    eapply Forall_skipn.
    clear -ih Hwf Hrel isp hcstr declc'.
    { revert v. rewrite erase_terms_eq => v.
      eapply Forall_All in ih.
      assert (All
       (fun t : term =>
        forall wt' : forall Σ : global_env_ext, Σ ∼_ext Xext -> welltyped Σ [] t,
        firstorder_evalue
          (erase_global_deps X_type (term_global_deps v) X decls
             normalization_in prf).1 (erase X_type Xext [] t wt')) args).
      { eapply In_All. intros x hin wt.
        eapply All_In in ih; tea. destruct ih as [ih].
        specialize (ih wt).
        eapply firstorder_evalue_extends; tea.
        subst v. eapply lookup_erase_global.
        rewrite term_global_deps_mkApps.
        intros kn hin'. eapply KernameSet.union_spec; right.
        destruct (In_map_All (erase X_type (abstract_make_wf_env_ext X univs wfext) []) _ Hyp1 _ hin).
        eapply In_term_global_deps; tea.
        erewrite (erase_irrel _ _).1; tea. }
      eapply All_Forall, All_map_All.
      { intros. exact X0. }
      cbn. intros x y rx h. apply h. exact Hrel. }
      rewrite erase_terms_eq map_All_length. cbn.
      clear -wt' Hwf declc' Hrel hcstr. specialize (wt' _ Hrel).
      now rewrite -(declared_constructor_arity declc'). }
  { eapply PCUICWcbvEval.value_final. eapply PCUICWcbvEval.eval_to_value. eauto. }
  all: eauto.
  Unshelve. eauto.
Qed.

Lemma erase_correct_strong (wfl := EWcbvEval.default_wcbv_flags) X_type (X : X_type.π1)
  univs wfext {t v i u args} decls normalization_in prf
  (Xext :=  abstract_make_wf_env_ext X univs wfext)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ}
  : forall wt : (forall Σ, Σ ∼_ext Xext -> welltyped Σ [] t),
  forall Σ, abstract_env_ext_rel Xext Σ ->
  axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  let t' := erase X_type Xext [] t wt in
  let Σ' := erase_global_deps X_type (term_global_deps t') X decls normalization_in prf in
  @firstorder_ind Σ (firstorder_env Σ) i ->
  red Σ [] t v ->
  ¬ { v' & Σ ;;; [] |- v ⇝ v'} ->
  exists wt', let et' := erase X_type Xext [] v wt' in
  ∥ Σ'.1 ⊢ t' ⇓ erase X_type Xext [] v wt' ∥ /\ firstorder_evalue Σ'.1 et'.
Proof.
  intros wt Σ Hrel Hax Hty Hdecl Hfo Hsub Hred Hirred.
  unshelve eexists.
  - abstract (intros Σ_ H_; pose proof (ErasureFunction.heΣ _ _ _ H_); sq;
    pose proof (abstract_env_ext_irr _ H_ Hrel); subst; eapply red_welltyped; eauto; econstructor; eauto).
  - eapply erase_correct_strong'; eauto.
    all:reflexivity.
Qed.

Lemma unique_decls {X_type} {X : X_type.π1} univs wfext
(Xext :=  abstract_make_wf_env_ext X univs wfext) {Σ'} (wfΣ' : Σ' ∼_ext Xext) :
  forall Σ, Σ ∼ X -> declarations Σ = declarations Σ'.
Proof.
  intros Σ wfΣ. pose (abstract_make_wf_env_ext_correct X univs wfext Σ Σ' wfΣ wfΣ').
  rewrite e. reflexivity.
Qed.

Lemma unique_type {X_type : abstract_env_impl} {X : X_type.π2.π1}
  {Σ:global_env_ext}
  (wfΣ : Σ ∼_ext X) {t T}:
  Σ ;;; [] |- t : T -> forall Σ, Σ ∼_ext X -> welltyped Σ [] t.
Proof.
  intros wt Σ' wfΣ'. erewrite (abstract_env_ext_irr X wfΣ' wfΣ).
  now exists T.
Qed.

Definition erase_correct_firstorder (wfl := EWcbvEval.default_wcbv_flags)
  X_type (X : X_type.π1) univs wfext {t v i u args}
  (Xext :=  abstract_make_wf_env_ext X univs wfext)
  {normalization_in : forall X Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} :
  forall Σ (wfΣ : abstract_env_ext_rel Xext Σ)
  (wt : Σ ;;; [] |- t : mkApps (tInd i u) args),
  axiom_free Σ ->
  let t' := erase X_type Xext [] t (unique_type wfΣ wt) in
  let decls := declarations (fst Σ) in
  let Σ' := erase_global_deps X_type (term_global_deps t') X decls
              (fun _ _ _ _ _ _ _ =>  normalization_in _ _) (unique_decls univs wfext wfΣ) in
  @firstorder_ind Σ (firstorder_env Σ) i ->
  red Σ [] t v ->
  ¬ { v' & Σ ;;; [] |- v ⇝ v'} ->
  exists wt', let et' := erase X_type Xext [] v wt' in ∥ Σ'.1 ⊢ t' ⇓ et' ∥ /\
    firstorder_evalue Σ'.1 et'.
Proof.
  intros.
  eapply erase_correct_strong; eauto.
Qed.

(* we use the [match] trick to get typeclass resolution to pick up the right instances without leaving any evidence in the resulting term, and without having to pass them manually everywhere *)
Notation NormalizationIn_erase_global_deps_fast X decls
  := (match extraction_checker_flags, extraction_normalizing return _ with
      | cf, no
        => forall n,
          n < List.length decls ->
          forall kn cb pf,
            List.hd_error (List.skipn n decls) = Some (kn, ConstantDecl cb) ->
            let Xext := abstract_make_wf_env_ext X (cst_universes cb) pf in
            forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ
      end)
       (only parsing).


Section EraseGlobalFast.

  Import PCUICEnvironment.

Definition decls_prefix decls (Σ' : global_env) :=
  ∑ Σ'', declarations Σ' = Σ'' ++ decls.

Lemma on_global_decls_prefix {cf} Pcmp P univs retro decls decls' :
  PCUICAst.on_global_decls Pcmp P univs retro (decls ++ decls') ->
  PCUICAst.on_global_decls Pcmp P univs retro decls'.
Proof using Type.
  induction decls => //.
  intros ha; depelim ha.
  now apply IHdecls.
Qed.

Lemma decls_prefix_wf {decls Σ} :
  decls_prefix decls Σ -> wf Σ -> wf {| universes := Σ.(universes); declarations := decls; retroknowledge := Σ.(retroknowledge) |}.
Proof using Type.
  intros [Σ' hd] wfΣ.
  split. apply wfΣ.
  cbn. destruct wfΣ as [_ ond]. rewrite hd in ond.
  now eapply on_global_decls_prefix in ond.
Qed.

Lemma incl_cs_refl cs : cs ⊂_cs cs.
Proof using Type.
  split; [lsets|ucsets].
Qed.

Lemma weaken_prefix {decls Σ kn decl} :
  decls_prefix decls Σ ->
  wf Σ ->
  lookup_env {| universes := Σ; declarations := decls; retroknowledge := Σ.(retroknowledge) |} kn = Some decl ->
  on_global_decl cumulSpec0 (lift_typing typing) (Σ, universes_decl_of_decl decl) kn decl.
Proof using Type.
  intros prefix wfΣ.
  have wfdecls := decls_prefix_wf prefix wfΣ.
  epose proof (weakening_env_lookup_on_global_env (lift_typing typing) _ Σ kn decl
    weaken_env_prop_typing wfΣ wfdecls).
  forward X. apply extends_strictly_on_decls_extends, strictly_extends_decls_extends_strictly_on_decls. red; split => //.
  now apply (X wfdecls).
Qed.


(* This version of global environment erasure keeps the same global environment throughout the whole
   erasure, while folding over the list of declarations. *)

Local Obligation Tactic := program_simpl.

Program Fixpoint erase_global_deps_fast (deps : KernameSet.t)
  X_type (X:X_type.π1) (decls : global_declarations)
  {normalization_in : NormalizationIn_erase_global_deps_fast X decls}
  (prop : forall Σ : global_env, abstract_env_rel X Σ -> ∥ decls_prefix decls Σ ∥) : E.global_declarations * KernameSet.t :=
  match decls with
  | [] => ([],deps)
  | (kn, ConstantDecl cb) :: decls =>
    if KernameSet.mem kn deps then
      let Xext' :=  abstract_make_wf_env_ext X (cst_universes cb) _ in
      let normalization_in' : @id Prop _ := _ in (* hack to avoid program erroring out on unresolved tc *)
      let cb' := @erase_constant_body X_type Xext' normalization_in' cb _ in
      let deps := KernameSet.union deps (snd cb') in
      let Σ' := erase_global_deps_fast deps X_type X decls _ in
      (((kn, E.ConstantDecl (fst cb')) :: Σ'.1), Σ'.2)
    else
      erase_global_deps_fast deps X_type X decls _

  | (kn, InductiveDecl mib) :: decls =>
    if KernameSet.mem kn deps then
      let mib' := erase_mutual_inductive_body mib in
      let Σ' := erase_global_deps_fast deps X_type X decls _ in
      (((kn, E.InductiveDecl mib') :: Σ'.1), Σ'.2)
    else erase_global_deps_fast deps X_type X decls _
  end.
Next Obligation.
  pose proof (abstract_env_wf _ H) as [?].
  specialize_Σ H. sq. split. cbn. apply X3. cbn.
  eapply decls_prefix_wf in X3; tea.
  destruct X3 as [onu ond]. cbn in ond.
  depelim ond. now destruct o.
Qed.
Next Obligation.
  cbv [id].
  unshelve eapply (normalization_in 0); cbn; try reflexivity; try lia.
Defined.
Next Obligation.
  pose proof (abstract_env_ext_wf _ H) as [?].
  pose proof (abstract_env_exists X) as [[? wf]].
  pose proof (abstract_env_wf _ wf) as [?].
  pose proof (prop' := prop _ wf).
  sq. eapply (weaken_prefix (kn := kn)) in prop'; tea.
  2:{ cbn. rewrite eqb_refl //. }
  epose proof (abstract_make_wf_env_ext_correct X (cst_universes cb) _ _ _ wf H). subst.
  apply prop'.
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, ConstantDecl cb)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, ConstantDecl cb)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, _)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, _)]); rewrite -app_assoc //.
Qed.

Import PCUICAst PCUICEnvironment.

Lemma wf_lookup Σ kn d suffix g :
  wf Σ ->
  declarations Σ = suffix ++ (kn, d) :: g ->
  lookup_env Σ kn = Some d.
Proof using Type.
  unfold lookup_env.
  intros [_ ond] eq. rewrite eq in ond |- *.
  move: ond; clear.
  induction suffix.
  - cbn. rewrite eqb_refl //.
  - cbn. intros ond.
    depelim ond. destruct o as [f ? ? ? ]. cbn. red in f.
    eapply Forall_app in f as []. depelim H0. cbn in H0.
    destruct (eqb_spec kn kn0); [contradiction|].
    now apply IHsuffix.
Qed.

Definition add_suffix suffix Σ := set_declarations Σ (suffix ++ Σ.(declarations)).

Lemma add_suffix_cons d suffix Σ : add_suffix (d :: suffix) Σ = add_global_decl (add_suffix suffix Σ) d.
Proof using Type. reflexivity. Qed.

Lemma global_erased_with_deps_weaken_prefix suffix Σ Σ' kn :
  wf (add_suffix suffix Σ) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps (add_suffix suffix Σ) Σ' kn.
Proof using Type.
  induction suffix.
  - unfold add_suffix; cbn. intros wf hg.
    now rewrite /set_declarations /= -eta_global_env.
  - rewrite add_suffix_cons. intros wf H.
    destruct a as [kn' d]. eapply global_erases_with_deps_weaken => //.
    apply IHsuffix => //.
    destruct wf as [onu ond]. now depelim ond.
Qed.


(* Using weakening it is trivial to show that a term found to be erasable in Σ
  will be found erasable in any well-formed extension. The converse is not so trivial:
  some valid types in the extension are not valid in the restricted global context.
  So, we will rather show that the erasure function is invariant under extension. *)

Lemma isErasable_irrel_global_env {Σ Σ' : global_env_ext} {Γ t} :
  wf Σ ->
  wf Σ' ->
  extends Σ' Σ ->
  Σ.2 = Σ'.2 ->
  isErasable Σ' Γ t -> isErasable Σ Γ t.
Proof using Type.
  unfold isErasable.
  intros wfΣ wfΣ' ext eqext [T [ht isar]].
  destruct Σ as [Σ decl], Σ' as [Σ' decl']. cbn in eqext; subst decl'.
  exists T; split.
  eapply (env_prop_typing weakening_env (Σ', decl)) => //=.
  destruct isar as [|s]; [left|right] => //.
  destruct s as [u [Hu isp]].
  exists u; split => //.
  eapply (env_prop_typing weakening_env (Σ', decl)) => //=.
Qed.

Definition reduce_stack_eq {cf} {fl} {no:normalizing_flags} {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ t π wi : reduce_stack fl X_type X Γ t π wi = ` (reduce_stack_full fl X_type X Γ t π wi).
Proof using Type.
  unfold reduce_stack. destruct reduce_stack_full => //.
Qed.

Definition same_principal_type {cf}
  {X_type : abstract_env_impl} {X : X_type.π2.π1}
  {X_type' : abstract_env_impl} {X' : X_type'.π2.π1}
  {Γ : context} {t} (p : PCUICSafeRetyping.principal_type X_type X Γ t) (p' : PCUICSafeRetyping.principal_type X_type' X' Γ t) :=
  p.π1 = p'.π1.

(*Lemma erase_global_deps_suffix {deps} {Σ Σ' : wf_env} {decls hprefix hprefix'} :
  wf Σ -> wf Σ' ->
  universes Σ = universes Σ' ->
  erase_global_deps_fast deps Σ decls hprefix =
  erase_global_deps_fast deps Σ' decls hprefix'.
Proof using Type.
  intros wfΣ wfΣ' equ.
  induction decls in deps, hprefix, hprefix' |- *; cbn => //.
  destruct a as [kn []].
  set (obl := (erase_global_deps_fast_obligation_1 Σ ((kn, ConstantDecl c) :: decls)
             hprefix kn c decls eq_refl)). clearbody obl.
  destruct obl.
  set (eb := erase_constant_body _ _ _).
  set (eb' := erase_constant_body _ _ _).
  assert (eb = eb') as <-.
  { subst eb eb'.
    set (wfΣx :=  abstract_make_wf_env_ext _ _ _).
    set (wfΣ'x :=  abstract_make_wf_env_ext _ _ _).
    set (obl' := erase_global_deps_fast_obligation_2 _ _ _ _ _ _ _).
    clearbody obl'.
    set (Σd := {| universes := Σ.(universes); declarations := decls |}).
    assert (wfΣd : wf Σd).
    { eapply decls_prefix_wf; tea.
      clear -hprefix. move: hprefix. unfold decls_prefix.
      intros [Σ'' eq]. exists (Σ'' ++ [(kn, ConstantDecl c)]).
      rewrite -app_assoc //. }
    set (wfΣdwfe := build_wf_env_from_env _ (sq wfΣd)).
    assert (wfextΣd : wf_ext (Σd, cst_universes c)).
    { split => //. cbn. apply w. }
    set (wfΣdw :=  abstract_make_wf_env_ext wfΣdwfe (cst_universes c) (sq wfextΣd)).
    assert (ond' : ∥ on_constant_decl (lift_typing typing) (Σd, cst_universes c) c ∥ ).
    { pose proof (decls_prefix_wf hprefix wfΣ).
      destruct X as [onu ond]. depelim ond. sq. apply o0. }
    assert (extd' : extends_decls Σd Σ).
    { clear -hprefix. move: hprefix.
      intros [? ?]. split => //. eexists (x ++ [(kn, ConstantDecl c)]). cbn.
      now rewrite -app_assoc. }
    assert (extd'' : extends_decls Σd Σ').
    { clear -equ hprefix'. move: hprefix'.
      intros [? ?]. split => //. eexists (x ++ [(kn, ConstantDecl c)]). cbn.
      now rewrite -app_assoc. }
    rewrite (erase_constant_suffix (Σ := wfΣx) (Σ' := wfΣdw) (ondecl' := ond') wfΣ extd') //.
    rewrite (erase_constant_body_irrel (Σ := wfΣ'x) (Σ' := wfΣdw) (ondecl' := ond') wfΣ' extd'') //. }
  destruct KernameSet.mem => //. f_equal.
  eapply IHdecls.
  destruct KernameSet.mem => //. f_equal.
  eapply IHdecls.
Qed.*)

Lemma strictly_extends_decls_extends_global_env Σ Σ' :
  wf Σ' ->
  strictly_extends_decls Σ Σ' ->
  extends_global_env Σ Σ'.
Proof.
  intros wfΣ' [uni [Σ'' de] retr]. red.
  cbn. unfold lookup_env. rewrite de /primitive_constant retr.
  split => //. intros kn decl.
  intros hl.
  apply lookup_global_Some_iff_In_NoDup.
  apply EnvMap.EnvMap.fresh_globals_iff_NoDup.
  rewrite -de. now apply wf_fresh_globals.
  apply lookup_global_Some_iff_In_NoDup in hl.
  apply in_app_iff. now right.
  apply EnvMap.EnvMap.fresh_globals_iff_NoDup.
  apply wf_fresh_globals in wfΣ'. rewrite de in wfΣ'.
  clear -wfΣ'. induction Σ''; auto. apply IHΣ''.
  now depelim wfΣ'.
Qed.

Lemma extends_global_env_equiv_env Σ Σ' :
  extends_global_env Σ Σ' -> equiv_env_inter Σ Σ'.
Proof.
  intros ext. split. intros kn decl decl' hl hl'.
  destruct ext. apply H in hl. congruence.
  now destruct ext.
Qed.

Lemma erase_global_deps_fast_spec_gen {deps}
  {X_type X X'} {decls normalization_in normalization_in' hprefix hprefix'} :
  (forall Σ Σ', abstract_env_rel X Σ -> abstract_env_rel X' Σ' -> universes Σ = universes Σ' /\ retroknowledge Σ = retroknowledge Σ') ->
  erase_global_deps_fast deps X_type X decls (normalization_in:=normalization_in) hprefix =
  erase_global_deps X_type deps X' decls normalization_in' hprefix'.
Proof using Type.
  intros equ.
  induction decls in X, X', equ, deps, normalization_in, normalization_in', hprefix, hprefix' |- * => //.
  pose proof (abstract_env_exists X) as [[Σ wfΣ]].
  pose proof (abstract_env_exists X') as [[Σ' wfΣ']].
  pose proof (abstract_env_wf _ wfΣ) as [wf].
  pose proof (abstract_env_exists (abstract_pop_decls X')) as [[? wfpop]].
  unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' wfpop) as [? [? ?]].
  { now eexists. }

  destruct a as [kn []].
  - cbn. unfold erase_constant_decl.
    set (obl := (erase_global_deps_fast_obligation_1 X_type X ((kn, ConstantDecl c) :: decls)
             _ hprefix kn c decls eq_refl)).
    set (eb := erase_constant_body _ _ _ _).
    set (eb' := erase_constant_body _ _ _ _).
    set (eg := erase_global_deps _ _ _ _ _ _).
    set (eg' := erase_global_deps _ _ _ _ _ _).

    assert (eb = eb') as <-.
    { subst eb eb'.
      destruct (hprefix _ wfΣ) as [[Σ'' eq]].
      eapply erase_constant_body_irrel; cbn => //.
      eapply equiv_env_inter_hlookup.
      intros ? ? H2 H3.
      epose proof (abstract_make_wf_env_ext_correct X (cst_universes c) _ _ _ wfΣ H2).
      epose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X') (cst_universes c) _ _ _ wfpop H3).
      subst. eapply equiv_env_inter_sym.
      eapply extends_global_env_equiv_env.
      pose proof (abstract_env_wf _ wfΣ) as [].
      apply strictly_extends_decls_extends_global_env.
      apply X0. red.
      rewrite eq. rewrite <- H0, <- H1. split. cbn. symmetry; apply equ; eauto.
      cbn.
      eexists (Σ'' ++ [(kn, ConstantDecl c)]). cbn. subst. now rewrite -app_assoc. subst.
      symmetry. now apply equ. }
    destruct KernameSet.mem => //; f_equal; try eapply IHdecls.
    f_equal. f_equal. eapply IHdecls.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. } intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
    f_equal. eapply IHdecls.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. } intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. }  intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.

    - cbn.
    destruct KernameSet.mem => //; f_equal; try eapply IHdecls.
    f_equal; f_equal; eapply IHdecls.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. }
    intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
    intros.
    f_equal; eapply IHdecls.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. }
    intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
    intros; unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. }
    intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
Qed.

Lemma erase_global_deps_fast_spec {deps} {X_type X} {decls normalization_in normalization_in' hprefix hprefix'} :
  erase_global_deps_fast deps X_type X decls (normalization_in:=normalization_in) hprefix =
  erase_global_deps X_type deps X decls normalization_in' hprefix'.
Proof using Type.
  eapply erase_global_deps_fast_spec_gen; intros.
  rewrite (abstract_env_irr _ H H0); eauto.
Qed.

Lemma cored_extends (Σ Σ' : global_env_ext) Γ x y :
  wf Σ' ->
  extends Σ Σ' ->
  cored Σ Γ x y -> cored Σ' Γ x y.
Proof.
  intros wf ext.
  induction 1.
  - constructor.
    eapply PCUICWeakeningEnvConv.weakening_env_red1. apply wf. exact ext.
    exact X.
  - econstructor 2; tea.
    eapply PCUICWeakeningEnvConv.weakening_env_red1. apply wf.
    exact ext.
    exact X.
Qed.

Lemma normalization_in_extends (Σ Σ' : global_env) ext :
  wf Σ -> wf Σ' ->
  extends Σ' Σ ->
  NormalizationIn (Σ, ext) -> NormalizationIn (Σ', ext).
Proof.
  intros wfΣ wfΣ' extH nin.
  red in nin. intros Γ t wt.
  assert (welltyped (Σ, ext) Γ t).
  { destruct wt. exists A. eapply (env_prop_typing weakening_env) in X; tea; cbn. }
  specialize (nin _ _ H). clear H.
  induction nin.
  constructor. intros y r.
  eapply H0. eapply cored_extends in r; tea.
  eapply cored_welltyped; tea.
Qed.

Lemma iter_abstract_pop_decls_correct {cf} {abstract_env_impl abstract_env_ext_impl : Type}
  {abstract_env_struct0 : abstract_env_struct abstract_env_impl
                          abstract_env_ext_impl} :
  abstract_env_prop abstract_env_impl abstract_env_ext_impl ->
  forall (X : abstract_env_impl) (decls : list (kername × global_decl)) n,
  (forall Σ : global_env,
  Σ ∼ X -> exists decls', #|decls'| = n /\ declarations Σ = decls' ++ decls) ->
  let X' := iter abstract_pop_decls n X in
  forall Σ Σ' : global_env,
  Σ ∼ X ->
  Σ' ∼ X' ->
  declarations Σ' = decls /\ universes Σ = universes Σ' /\ retroknowledge Σ = retroknowledge Σ'.
Proof.
  intros ap X decls.
  induction n in X, decls |- *. cbn.
  - intros hdecl Σ Σ' HX HX'.
    specialize (hdecl _ HX) as [decls' [hlen hde]].
    destruct decls' => //. cbn in hde.
    now rewrite -hde (abstract_env_irr _ HX HX').
  - intros hdecl X' Σ Σ' HX HX'.
    specialize (hdecl _ HX) as [decls' [hlen hde]].
    destruct decls' => //; cbn in hde.
    specialize (IHn (abstract_pop_decls X) decls).
    pose proof (abstract_pop_decls_correct X (decls' ++ decls)).
    forward H.
    { intros ? h. rewrite -(abstract_env_irr _ HX h). now exists p. }
    forward IHn.
    { intros ? H0. now specialize (H _ _ HX H0). }
    pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop hpop]].
    specialize (IHn _ _ hpop HX').
    destruct IHn. split => //.
    pose proof (abstract_pop_decls_correct X (decls' ++ decls)).
    forward H2.
    { intros ? hx. pose proof (abstract_env_irr _ hx HX). subst Σ0. now exists p. }
    specialize (H2 _ _ HX hpop). destruct H2 as [? []].
    destruct H1.
    split; congruence.
Qed.

Lemma skipn_app_prefix {A} n (l l' : list A) : skipn (#|l| + n) (l ++ l') = skipn n l'.
Proof.
  induction l; cbn; auto.
Qed.

Lemma erase_global_deps_fast_erase_global_deps {deps} {X_type X} {decls normalization_in hprefix hprefix'} :
  exists normalization_in',
  erase_global_deps_fast deps X_type X decls (normalization_in:=normalization_in) hprefix =
  erase_global_deps X_type deps X decls normalization_in' hprefix'.
Proof using Type.
  unshelve eexists.
  intros.
  pose proof (abstract_env_exists X) as [[Σ' H']].
  pose proof (abstract_env_wf _ H') as [].
  specialize (hprefix _ H') as [[Σ'' ?]].
  pose proof (abstract_env_exists (iter abstract_pop_decls (S n) X)) as [[? ?]].
  pose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ a H1). noconf H2.
  epose proof (iter_abstract_pop_decls_correct _ X (skipn (S n) (Σ'' ++ decls)) (S n)).
  forward H2. { intros ? h. rewrite (abstract_env_irr _ h H'). exists (firstn (S n) (Σ'' ++ decls)).
  rewrite firstn_skipn. split => //. rewrite firstn_length_le //. rewrite length_app. lia. }
  specialize (H2 _ _ H' a) as [? []].
  eapply normalization_in_extends. exact X1. exact X0.
  { eapply extends_decls_extends, strictly_extends_decls_extends_decls.
    red. rewrite H2 H3 H4. split => //. exists (firstn (S n) (Σ'' ++ decls)).
    now rewrite firstn_skipn. }
  specialize (normalization_in n H kn cb).
  assert (wf_ext (Σ', cst_universes cb)).
  { split => //. cbn. rewrite H3. apply X0. }
  assert (forall Σ : global_env, Σ ∼ X -> ∥ wf_ext (Σ, cst_universes cb) ∥).
  { intros. pose proof (abstract_env_irr _ H' H5). now subst Σ'. }
  unshelve eapply normalization_in; tea.
  set (foo := abstract_make_wf_env_ext X (cst_universes cb) H5).
  pose proof (abstract_env_ext_exists foo) as [[Σext hext]].
  epose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ H' hext). now subst Σext.
  erewrite erase_global_deps_fast_spec; tea. reflexivity.
Qed.

Definition erase_global_fast X_type deps X decls {normalization_in} (prf:forall Σ : global_env, abstract_env_rel X Σ -> declarations Σ = decls) :=
  erase_global_deps_fast deps X_type X decls (normalization_in:=normalization_in) (fun _ H => sq ([] ; prf _ H)).

Lemma expanded_erase_global_fast (cf := config.extraction_checker_flags) deps
  {X_type X decls normalization_in} {normalization_in':NormalizationIn_erase_global_deps X decls} {prf} :
  forall Σ : global_env, abstract_env_rel X Σ ->
  PCUICEtaExpand.expanded_global_env Σ ->
  expanded_global_env (erase_global_fast X_type deps X decls (normalization_in:=normalization_in) prf).1.
Proof using Type.
  unfold erase_global_fast.
  erewrite erase_global_deps_fast_spec.
  eapply expanded_erase_global.
  Unshelve. all: eauto.
Qed.

Lemma expanded_erase_fast (cf := config.extraction_checker_flags)
  {X_type X decls normalization_in prf} {normalization_in'':NormalizationIn_erase_global_deps X decls} univs wfΣ t wtp :
  forall Σ : global_env, abstract_env_rel X Σ ->
  PCUICEtaExpand.expanded Σ [] t ->
  let X' :=  abstract_make_wf_env_ext X univs wfΣ in
  forall (normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ),
  let et := (erase X_type X' [] t wtp) in
  let deps := EAstUtils.term_global_deps et in
  expanded (erase_global_fast X_type deps X decls (normalization_in:=normalization_in) prf).1 [] et.
Proof using Type.
  intros Σ wf hexp X' normalization_in'. pose proof (abstract_env_wf _ wf) as [?].
  eapply (expanded_erases (Σ := (Σ, univs))); tea.
  eapply (erases_erase (X := X')).
  pose proof (abstract_env_ext_exists X') as [[? wfmake]].
  now rewrite <- (abstract_make_wf_env_ext_correct X univs _ _ _ wf wfmake).
  cbn. unfold erase_global_fast. erewrite erase_global_deps_fast_spec => //.
  eapply (erases_deps_erase (X := X) univs wfΣ); eauto.
  Unshelve. all: eauto.
Qed.

Lemma erase_global_fast_wf_glob X_type deps X decls normalization_in (normalization_in':NormalizationIn_erase_global_deps X decls) prf :
  @wf_glob all_env_flags (erase_global_fast X_type deps X decls (normalization_in:=normalization_in) prf).1.
Proof using Type.
  unfold erase_global_fast; erewrite erase_global_deps_fast_spec.
  eapply erase_global_deps_wf_glob.
  Unshelve. all: eauto.
Qed.

Lemma erase_wellformed_fast (efl := all_env_flags)
  {X_type X decls normalization_in prf} {normalization_in'':NormalizationIn_erase_global_deps X decls} univs wfΣ {Γ t} wt
  (X' :=  abstract_make_wf_env_ext X univs wfΣ)
  {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ} :
  let t' := erase X_type X' Γ t wt in
  wellformed (erase_global_fast X_type (term_global_deps t') X decls (normalization_in:=normalization_in) prf).1 #|Γ| t'.
Proof using Type.
  intros.
  cbn. unfold erase_global_fast. erewrite erase_global_deps_fast_spec.
  eapply erase_wellformed_deps.
  Unshelve. all: eauto.
Qed.

End EraseGlobalFast.

Fixpoint compile_value_erase (t : PCUICAst.term) (acc : list EAst.term) : EAst.term :=
  match t with
  | PCUICAst.tApp f a => compile_value_erase f (compile_value_erase a [] :: acc)
  | PCUICAst.tConstruct i n _ => EAst.mkApps (EAst.tConstruct i n []) acc
  | _ => EAst.tVar "error"
  end.

Lemma compile_value_erase_mkApps i n ui args acc :
  compile_value_erase (mkApps (tConstruct i n ui) args) acc =
  EAst.mkApps (EAst.tConstruct i n []) (map (flip compile_value_erase []) args ++ acc).
Proof.
  revert acc; induction args using rev_ind.
  - cbn. auto.
  - intros acc. rewrite PCUICAstUtils.mkApps_app /=. cbn.
    now rewrite IHargs map_app /= -app_assoc /=.
Qed.


Lemma erases_firstorder Σ Γ t :
  PCUICFirstorder.firstorder_value Σ Γ t ->
  erases Σ Γ t (compile_value_erase t []).
Proof.
  move: t.
  apply: (PCUICFirstorder.firstorder_value_inds Σ Γ).
  intros i n ui u args pandi hty hfo ih isp.
  assert (Forall2 (erases Σ Γ) args (map (flip compile_value_erase []) args)).
  { PCUICAstUtils.solve_all. }
  unshelve epose proof (erases_mkApps Σ Γ (tConstruct i n ui) (EAst.tConstruct i n []) args _ _ H).
  now constructor.
  now rewrite compile_value_erase_mkApps app_nil_r.
Qed.

Lemma erases_firstorder' Σ Γ t :
  wf_ext Σ ->
  PCUICFirstorder.firstorder_value Σ Γ t ->
  forall t', erases Σ Γ t t' -> t' = (compile_value_erase t []).
Proof.
  intros wf. move: t.
  apply: (PCUICFirstorder.firstorder_value_inds Σ Γ).
  intros i n ui u args pandi hty hfo ih isp.
  assert (Forall2 (erases Σ Γ) args (map (flip compile_value_erase []) args)).
  { solve_all. eapply All_All2; tea.
    cbn. intros x [fo hx]. now eapply erases_firstorder. }
  unshelve epose proof (erases_mkApps Σ Γ (tConstruct i n ui) (EAst.tConstruct i n []) args _ _ H).
  constructor => //.
  rewrite compile_value_erase_mkApps app_nil_r.
  intros t' ht'.
  eapply erases_mkApps_inv in ht'.
  destruct ht'.
  { destruct H1 as [? [? [? [? [[] ?]]]]].
    eapply isErasable_Propositional in X => //.
    now rewrite X in isp. }
  destruct H1 as [f' [L' [-> [erc erargs]]]].
  depelim erc. f_equal.
  solve_all. clear -erargs.
  induction erargs => //. rewrite IHerargs. cbn. f_equal.
  destruct r as [[] ?]. eapply e in e0. now unfold flip.
  eapply (isErasable_Propositional (args := [])) in X => //.
  now rewrite X in isp.
Qed.
