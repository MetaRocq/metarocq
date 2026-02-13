(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICWeakeningEnv PCUICEquality PCUICReduction PCUICCumulativity PCUICCumulativitySpec
  (* PCUICContextSubst *) (* PCUICUnivSubst *) (* PCUICCases *) (* PCUICTyping *)
  (* PCUICGuardCondition *) (* PCUICGlobalEnv *).
From Equations Require Import Equations.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma compare_term_subset {cf} pb Σ φ φ' t t'
  : UnivConstraintSet.Subset φ φ'
    -> compare_term Σ φ pb t t' -> compare_term Σ φ' pb t t'.
Proof.
  intro H. apply eq_term_upto_univ_impl; auto.
  1,2: intros ??; now eapply cmp_universe_subset.
  1,2: intros ??; now eapply cmp_sort_subset.
Qed.

Lemma eq_term_subset {cf} Σ φ φ' t t'
  : UnivConstraintSet.Subset φ φ' -> eq_term Σ φ t t' -> eq_term Σ φ' t t'.
Proof. apply compare_term_subset with (pb := Conv). Qed.

Lemma leq_term_subset {cf:checker_flags} Σ ctrs ctrs' t u
  : UnivConstraintSet.Subset ctrs ctrs' -> leq_term Σ ctrs t u -> leq_term Σ ctrs' t u.
Proof. apply compare_term_subset with (pb := Cumul). Qed.

Lemma compare_decl_subset {cf} pb Σ φ φ' d d'
  : UnivConstraintSet.Subset φ φ'
    -> compare_decl Σ φ pb d d' -> compare_decl Σ φ' pb d d'.
Proof.
  intros Hφ []; constructor; eauto using compare_term_subset.
Qed.

Lemma compare_context_subset {cf} pb Σ φ φ' Γ Γ'
  : UnivConstraintSet.Subset φ φ'
    -> compare_context Σ φ pb Γ Γ' ->  compare_context Σ φ' pb Γ Γ'.
Proof.
  intros Hφ. induction 1; constructor; auto; eapply compare_decl_subset; eassumption.
Qed.

Section ExtendsWf.
  Context {cf : checker_flags}.
  Context {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P: global_env_ext -> context -> judgment -> Type}.

  Let wf := on_global_env Pcmp P.

Lemma global_variance_sigma_mon {Σ Σ'} gr napp :
  wf Σ' -> extends Σ Σ' ->
  match global_variance Σ gr napp with
  | Variance v => global_variance Σ' gr napp = Variance v
  | AllEqual => True
  | AllIrrelevant => global_variance Σ' gr napp = AllIrrelevant
  end.
Proof using P Pcmp cf.
  intros wfΣ' ext.
  rewrite /global_variance_gen /lookup_constructor /lookup_constructor_gen
    /lookup_inductive /lookup_inductive_gen /lookup_minductive /lookup_minductive_gen.
  destruct gr as [|ind|[ind i]|] => //=.
  - destruct (lookup_env Σ ind) eqn:look => //.
    eapply extends_lookup in look; eauto. rewrite look //.
    destruct g => //=; destruct nth_error => //=.
    destruct destArity as [[ctx s]|] => //=.
    destruct Nat.leb => //=.
    destruct ind_variance => //=.
  - destruct (lookup_env Σ (inductive_mind i)) eqn:look => //.
    eapply extends_lookup in look; eauto. rewrite look //.
    destruct g => //=; destruct nth_error => //=; destruct nth_error => //=.
    destruct Nat.leb => //=.
Qed.

(** The definition of [cmp_global_instance] is defined so that it is weakenable. *)
Lemma cmp_global_instance_weaken_env Σ Σ' cmp_universe cmp_universe' pb pb' gr napp :
  wf Σ' -> extends Σ Σ' ->
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  subrelation (cmp_global_instance Σ cmp_universe pb gr napp) (cmp_global_instance Σ' cmp_universe' pb' gr napp).
Proof using P Pcmp cf.
  intros wfΣ ext sub_conv sub_pb t t'.
  unfold cmp_global_instance_gen.
  move: (global_variance_sigma_mon gr napp wfΣ ext).
  destruct global_variance_gen as [| |v] => //.
  all: [> intros _ | intros ->; cbn ..]; auto.
  1: intro H; apply: cmp_instance_opt_variance; move: H => /=.
  - now apply cmp_universe_instance_impl.
  - intros [H | H]; [left | right].
    1: eapply cmp_universe_instance_impl; tea.
    eapply cmp_universe_instance_variance_impl; eassumption.
Qed.

#[global]
Instance eq_term_upto_univ_weaken_env Σ Σ' cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp :
  wf Σ' -> extends Σ Σ' ->
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  CRelationClasses.subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp)
    (eq_term_upto_univ_napp Σ' cmp_universe' cmp_sort' pb' napp).
Proof using P Pcmp cf.
  intros wfΣ ext univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb t t'.
  induction t in napp, t', pb, pb', univ_sub_pb, sort_sub_pb, t' |- * using PCUICInduction.term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using cmp_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_weaken_env. 5:eauto. all:eauto.
  - inversion 1; subst; constructor.
    eapply cmp_global_instance_weaken_env. 5:eauto. all:eauto.
  - inversion 1; subst; destruct X as [? [? ?]]; constructor; eauto.
    * destruct X2 as [? [? ?]].
      constructor; intuition auto; solve_all.
      + eauto using cmp_universe_instance_impl'.
    * eapply All2_impl'; tea.
      eapply All_impl; eauto.
      cbn. intros x [? ?] y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - inversion 1; subst; constructor.
    depelim X1; constructor; cbn in X; intuition eauto. solve_all.
Qed.

Lemma weakening_env_red1 Σ Σ' Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  red1 Σ Γ M N ->
  red1 Σ' Γ M N.
Proof using P Pcmp cf.
  induction 3 using red1_ind_all;
    try solve [econstructor; eauto with extends; solve_all].
Qed.

Lemma weakening_env_cumul_gen pb Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulAlgo_gen (Σ, φ)  Γ pb M N ->
  cumulAlgo_gen (Σ', φ) Γ pb M N.
Proof using P Pcmp.
  intros wfΣ ext.
  induction 1; simpl.
  - econstructor. eapply compare_term_subset.
    + eapply global_ext_constraints_app. apply ext.
    + simpl in *. eapply eq_term_upto_univ_weaken_env in c; simpl; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto.
Qed.

Lemma weakening_env_conv Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  convAlgo (Σ, φ) Γ M N ->
  convAlgo (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumul_gen with (pb := Conv). Qed.

Lemma weakening_env_cumul Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulAlgo (Σ, φ) Γ M N ->
  cumulAlgo (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumul_gen with (pb := Cumul). Qed.


Lemma weakening_env_cumulSpec0 Σ Σ' φ Γ pb M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulSpec0 (Σ, φ) Γ pb M N ->
  cumulSpec0 (Σ', φ) Γ pb M N.
Proof.
  intros HΣ' Hextends Ind.
  revert pb Γ M N Ind Σ' HΣ' Hextends.
  induction 1.
  all:intros; try solve [econstructor; eauto with extends; intuition auto].
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  - eapply cumul_Evar. solve_all.
  - eapply cumul_Case.
    * cbv [cumul_predicate] in *; destruct_head'_prod. clear c0. repeat split; tas.
      + solve_all.
      + eapply cmp_universe_instance_impl'; tea. tc.
      + eauto.
    * eauto.
    * unfold cumul_branches, cumul_branch in *. solve_all.
  - eapply cumul_Fix; unfold cumul_mfixpoint in *; solve_all.
  - eapply cumul_CoFix; unfold cumul_mfixpoint in *; solve_all.
  - eapply cumul_Prim; solve_all.
    destruct X; constructor; eauto.
    * eapply subrel_extends_cmp_universe; tea.
    * solve_all.
  - eapply cumul_Ind; eauto. 2:solve_all.
    eapply @cmp_global_instance_weaken_env. 1,2,5:eauto. all: tc.
  - eapply cumul_Construct; eauto. 2:solve_all.
    eapply @cmp_global_instance_weaken_env. 1,2,5:eauto. all: tc.
  - eapply cumul_Sort. eapply subrelations_compare_extends; tea.
  - eapply cumul_Const. eapply cmp_universe_instance_impl'; eauto; tc.
Defined.


Lemma weakening_env_convSpec Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  convSpec (Σ, φ) Γ M N ->
  convSpec (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumulSpec0 with (pb := Conv). Qed.

Lemma weakening_env_cumulSpec Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulSpec (Σ, φ) Γ M N ->
  cumulSpec (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumulSpec0 with (pb := Cumul). Qed.

Lemma weakening_env_conv_decls {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (conv_decls cumulSpec0 (Σ, φ) Γ Γ') (conv_decls cumulSpec0 (Σ', φ) Γ Γ').
Proof using P Pcmp.
  intros wfΣ' ext d d' Hd; depelim Hd; constructor; tas;
    eapply weakening_env_convSpec; tea.
Qed.

Lemma weakening_env_cumul_decls {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (cumul_decls cumulSpec0 (Σ, φ) Γ Γ') (cumul_decls cumulSpec0 (Σ', φ) Γ Γ').
Proof using P Pcmp.
  intros wfΣ' ext d d' Hd; depelim Hd; constructor; tas;
    (eapply weakening_env_convSpec || eapply weakening_env_cumulSpec); tea.
Qed.

Lemma weakening_env_conv_ctx {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  conv_context cumulSpec0 (Σ, φ) Γ Δ ->
  conv_context cumulSpec0 (Σ', φ) Γ Δ.
Proof using P Pcmp.
  intros wfΣ' ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_conv_decls.
Qed.


Lemma weakening_env_cumul_ctx {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  cumul_context cumulSpec0 (Σ, φ) Γ Δ ->
  cumul_context cumulSpec0 (Σ', φ) Γ Δ.
Proof using P Pcmp.
  intros wfΣ' ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_cumul_decls.
Qed.

End ExtendsWf.

#[global] Hint Resolve weakening_env_conv_ctx : extends.
#[global] Hint Resolve weakening_env_cumul_ctx : extends.
