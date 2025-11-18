(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import MRUtils utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICWeakeningConfig PCUICEquality PCUICReduction PCUICCumulativity PCUICCumulativitySpec
  (* PCUICContextSubst *) (* PCUICUnivSubst *) (* PCUICCases *) (* PCUICTyping *)
  (* PCUICGuardCondition *) (* PCUICGlobalEnv *).
From Equations Require Import Equations.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma compare_term_config_impl {cf1 cf2} Σ φ pb t t'
  : config.impl cf1 cf2
    -> @compare_term cf1 Σ φ pb t t' -> @compare_term cf2 Σ φ pb t t'.
Proof.
  intro H. apply eq_term_upto_univ_impl; auto.
  1,2: intros ??; now eapply cmp_universe_config_impl.
  1,2: intros ??; now eapply cmp_sort_config_impl.
Qed.

Lemma eq_term_config_impl {cf1 cf2} Σ φ t t'
  : config.impl cf1 cf2 -> @compare_term cf1 Σ φ Conv t t' -> @compare_term cf2 Σ φ Conv t t'.
Proof. eapply compare_term_config_impl with (pb := Conv). Qed.

Lemma leq_term_config_impl {cf1 cf2} Σ ctrs t u
  : config.impl cf1 cf2 -> @compare_term cf1 Σ ctrs Cumul t u -> @compare_term cf2 Σ ctrs Cumul t u.
Proof. apply compare_term_config_impl with (pb := Cumul). Qed.

Lemma compare_decl_config_impl {cf1 cf2} pb Σ φ d d'
  : config.impl cf1 cf2
    -> @compare_decl cf1 pb Σ φ d d' -> @compare_decl cf2 pb Σ φ d d'.
Proof.
  have hc := (@compare_term_config_impl cf1 cf2).
  intros Hcf []; constructor; eauto.
Qed.

Lemma compare_context_config_impl {cf1 cf2} pb Σ φ Γ Γ'
  : config.impl cf1 cf2
    -> @compare_context cf1 pb Σ φ Γ Γ' -> @compare_context cf2 pb Σ φ Γ Γ'.
Proof.
  intros Hcf. induction 1; constructor; auto; eapply (@compare_decl_config_impl cf1 cf2); eassumption.
Qed.

Lemma weakening_config_cumul_gen {cf1 cf2} pb Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulAlgo_gen cf1 Σ Γ pb M N ->
  @cumulAlgo_gen cf2 Σ Γ pb M N.
Proof.
  intro Hcf; induction 1; simpl; trivial.
  all: now econstructor; try eassumption; eapply (@compare_term_config_impl cf1 cf2); eassumption.
Qed.

Lemma weakening_config_conv {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulAlgo_gen cf1 Σ Γ Conv M N ->
  @cumulAlgo_gen cf2 Σ Γ Conv M N.
Proof. apply weakening_config_cumul_gen with (pb := Conv). Qed.

Lemma weakening_config_cumul {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulAlgo_gen cf1 Σ Γ Cumul M N ->
  @cumulAlgo_gen cf2 Σ Γ Cumul M N.
Proof. apply weakening_config_cumul_gen with (pb := Cumul). Qed.

Lemma weakening_config_cumulSpec0 {cf1 cf2} Σ Γ pb M N :
  config.impl cf1 cf2 ->
  @cumulSpec0 cf1 Σ Γ pb M N ->
  @cumulSpec0 cf2 Σ Γ pb M N.
Proof.
  intros Hcf.
  induction 1.
  all:intros; try solve [econstructor; try eassumption; intuition auto].
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  - eapply cumul_Evar. solve_all.
  - eapply cumul_Case.
    * cbv [cumul_predicate] in *; destruct_head'_prod. repeat split; tas.
      eapply cmp_universe_instance_impl';
        [ hnf; intros * ?; eapply (@cmp_universe_config_impl cf1 cf2) | ];
        eassumption.
    * assumption.
    * unfold cumul_branches, cumul_branch in *. solve_all.
  - eapply cumul_Fix. unfold cumul_mfixpoint in *. solve_all.
  - eapply cumul_CoFix. unfold cumul_mfixpoint in *. solve_all.
  - eapply cumul_Prim; solve_all.
    destruct X; constructor; eauto.
    * now eapply (@cmp_universe_config_impl cf1 cf2).
    * solve_all.
  - eapply cumul_Ind; eauto. 2:solve_all.
    eapply @cmp_global_instance_impl; [ .. | eassumption ].
    3: auto with arith. all: intros ??; now apply (@cmp_universe_config_impl cf1 cf2).
  - eapply cumul_Construct; eauto. 2:solve_all.
    eapply @cmp_global_instance_impl; [ .. | eassumption ].
    3: auto with arith. all: intros ??; now apply (@cmp_universe_config_impl cf1 cf2).
  - eapply cumul_Sort. eapply (@cmp_sort_config_impl cf1 cf2); eassumption.
  - eapply cumul_Const. eapply cmp_universe_instance_impl'; eauto; tc.
    hnf; intros *; eapply (@cmp_universe_config_impl cf1 cf2); eassumption.
Defined.

Lemma weakening_config_convSpec {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @convSpec cf1 Σ Γ M N ->
  @convSpec cf2 Σ Γ M N.
Proof. apply weakening_config_cumulSpec0 with (pb := Conv). Qed.

Lemma weakening_config_cumulSpec {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulSpec cf1 Σ Γ M N ->
  @cumulSpec cf2 Σ Γ M N.
Proof. apply weakening_config_cumulSpec0 with (pb := Cumul). Qed.

Lemma weakening_config_conv_decls {cf1 cf2 Σ Γ Γ'} :
  config.impl cf1 cf2 ->
  CRelationClasses.subrelation (conv_decls (@cumulSpec0 cf1) Σ Γ Γ') (conv_decls (@cumulSpec0 cf2) Σ Γ Γ').
Proof.
  intros Hcf d d' Hd; depelim Hd; constructor; tas;
    eapply (@weakening_config_convSpec cf1 cf2); tea.
Qed.

Lemma weakening_config_cumul_decls {cf1 cf2 Σ Γ Γ'} :
  config.impl cf1 cf2 ->
  CRelationClasses.subrelation (cumul_decls (@cumulSpec0 cf1) Σ Γ Γ') (cumul_decls (@cumulSpec0 cf2) Σ Γ Γ').
Proof.
  intros Hcf d d' Hd; depelim Hd; constructor; tas;
    (eapply (@weakening_config_convSpec cf1 cf2) || eapply (@weakening_config_cumulSpec cf1 cf2)); tea.
Qed.

Lemma weakening_config_conv_ctx {cf1 cf2 Σ Γ Δ} :
  config.impl cf1 cf2 ->
  conv_context (@cumulSpec0 cf1) Σ Γ Δ ->
  conv_context (@cumulSpec0 cf2) Σ Γ Δ.
Proof.
  intros Hcf.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_config_conv_decls.
Qed.


Lemma weakening_config_cumul_ctx {cf1 cf2 Σ Γ Δ} :
  config.impl cf1 cf2 ->
  cumul_context (@cumulSpec0 cf1) Σ Γ Δ ->
  cumul_context (@cumulSpec0 cf2) Σ Γ Δ.
Proof.
  intros Hcf.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_config_cumul_decls.
Qed.

(*
#[global] Hint Resolve weakening_config_conv_ctx : config.
#[global] Hint Resolve weakening_config_cumul_ctx : config.
*)
