From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR PCUICWeakeningEnv.
From TemplateExtraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim ESubstitution EInversion.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Lemma is_type_extends Σ Γ t T :
              Σ;;; Γ |- t : T -> wf_local Σ Γ ->
              forall Σ', wf Σ' -> extends Σ Σ' -> is_type_or_proof Σ Γ t = is_type_or_proof Σ' Γ t.
Proof.
  intros.
  destruct is_type_or_proof eqn:E1.
  - symmetry. eapply is_type_or_proof_spec in E1.
    eapply is_type_or_proof_spec.
    all:eauto.
    eapply weakening_env.
    3:eauto. all:eauto. eapply wf_extends; eauto.
    destruct E1 as [ | [u]]; eauto.
    right; exists u. intuition.
    eapply weakening_env.
    3:eauto. all:eauto. eapply wf_extends; eauto.
  - destruct (is_type_or_proof Σ') eqn:E2; try reflexivity.
    rewrite <- E1. clear E1.
    eapply is_type_or_proof_spec in E2.
    eapply is_type_or_proof_spec.
    all:eauto.
    2:{ eapply weakening_env.
        3:eauto. all:eauto. eapply wf_extends; eauto. }
    destruct E2 as [ | [u]]; eauto.
    right. exists u. intuition.
    admit.
Admitted.
  

Hint Constructors typing.

Ltac helper :=
      match goal with [ |- (if ?a then _ else _) = (if ?b then _ else _) ]
                      => enough (a = b) as ->; [ try reflexivity | ]
      end.

Lemma extract_extends :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ Σ' -> extract Σ Γ t = extract Σ' Γ t).
Proof.
  apply typing_ind_env; intros; rename_all_hyps.
  - cbn. enough (is_type_or_proof Σ Γ (PCUICAst.tRel n) = is_type_or_proof Σ' Γ (PCUICAst.tRel n)) as ->. reflexivity.
    eapply is_type_extends; eauto.
  - cbn. helper.
    eapply is_type_extends; eauto.
  - cbn. helper.
    eapply is_type_extends; eauto.
  - cbn. helper.
    destruct ?; try reflexivity.
    erewrite h_forall_Σ'0; eauto.
    eapply is_type_extends; eauto.
  - cbn. helper.
    2: eapply is_type_extends; eauto.
    destruct ?; try reflexivity.
    erewrite h_forall_Σ'0, h_forall_Σ'1; eauto.
  - cbn. helper.
    2: eapply is_type_extends; eauto.
    destruct ?; try reflexivity.
    erewrite h_forall_Σ', h_forall_Σ'0; eauto.
  - cbn. helper.
    eapply is_type_extends; eauto.
  - cbn. helper.
    eapply is_type_extends; eauto.
  - cbn. helper.
    eapply is_type_extends; eauto.
  - cbn. helper.
    2: eapply is_type_extends; eauto.
    destruct ?; try reflexivity.
    2: { econstructor; eauto.
         eapply All2_impl; eauto.
         intros; cbn in *. eapply X1. }
    erewrite h_forall_Σ'0; eauto.
    destruct ?; destruct brs; try reflexivity.
    + destruct p0. inv X3. cbn in X1.
      destruct X1. erewrite e; eauto.
    + f_equal. eapply map_ext_in.
      intros. f_equal.
      eapply All2_All_left in X3.
      2:{ intros; cbn in *. destruct X1. eapply e; eauto. }
      eapply All_Forall in X3.
      eapply Forall_forall in X3; eauto.
  - cbn. helper.
    destruct ?; try reflexivity.
    erewrite h_forall_Σ'; eauto.
    eapply is_type_extends; eauto.
  - cbn. helper.
    destruct ?; try reflexivity.
    unfold extract_mfix. f_equal.
    eapply map_ext_in.
    intros. f_equal.
    2: { eapply is_type_extends; eauto. admit. }

    eapply All_impl in X0.
    2:{ intros; cbn in *. destruct X1. exact e. }
    eapply All_Forall in X0.
    eapply Forall_forall in X0; eauto.
    subst types.
    admit.
  - cbn. helper.
    destruct ?; try reflexivity.
    f_equal. admit. admit.
  - erewrite h_forall_Σ'; eauto.
Admitted.
