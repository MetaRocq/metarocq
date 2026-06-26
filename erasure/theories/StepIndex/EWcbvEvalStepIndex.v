(* 
(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From MetaRocq.Erasure.StepIndex Require Import Tactics Utils SubstLemmas Values Primitives EvalStepIndex.
From Stdlib Require Import Relations.Relations.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".

Print Rewrite HintDb rw_hints.



Lemma subst_add_Γ {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ e u k :
  exp_rel Σ (λ _ _, True) (λ _ _, True) k ((csubst (term_of_val u) 0 e), Γ) (e, u::Γ).
Proof.
  induction k in e, u, Γ |- * using strong_nat_ind.
  induction e in u, Γ |- * using EInduction.term_forall_list_ind;
    intros v1 n1 n1_lt_k h_eval;
    try (inversion h_eval; my_discr).
  - simple. inversion h_eval; try my_discr.
    repeat econstructor.
  - destruct n; simple.
    + exists u, 0; repeat split.
      * now constructor.
      * admit.
    + inversion h_eval; subst; last my_discr.
      repeat econstructor; try easy.
      admit.      (* apply val_rel_refl. *)
  - simple.
    inversion h_eval; subst; try my_discr.
    exists (vClos n e (u :: Γ)), 0; repeat split.
    + constructor.
    + simple. intros.
      assert (eval Σ (u :: Γ) (csubst (term_of_val v2) 0 e) v0 n1) as heval.
      { admit. }
      unshelve epose proof H j _ (u :: Γ) e v2 v0 n1 _ heval as (v3 & n2 & [?] & ? & ?); try lia.
      now repeat (econstructor; simple).
  - simple. inversion h_eval; subst; last my_discr.
    edestruct IHe1 as (? & ? & [?] & _ & ?); [|eassumption|]; try easy.
    edestruct IHe2 as (? & ? & [?] & _ & ?).
    { admit. }
    { admit. }
    repeat (econstructor; simple);
    try easy.
Admitted.








    Search substl_tRel.
   destruct (s H) as (n & [] & ? & ?).

Lemma eval_SI_csubst {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ e v u n : 
  has_tApp ->
  with_constructor_as_block = cstr_as_blocks ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ (S #|Γ|) e ->
  eval Σ Γ (csubst (term_of_val u) 0 e) v n ->
  ∑ (n' : nat) (v' : value),
  term_of_val v = term_of_val v' ×
  eval Σ (u :: Γ) e v' n'.
Proof.
  intros htApp c_blocks wf_Σ wf_Γ wf_e heval; simple.
  dependent induction heval; simple.
  - destruct e; simple; try discriminate.
    + now repeat econstructor.
    + destruct n; last discriminate.
      destruct u; simple; destruct cstr_as_blocks; now my_discr || (repeat econstructor).
  - admit.
  - destruct e; simple; try discriminate.
    destruct n0; simple.
    { destruct u; simple; destruct cstr_as_blocks; try discriminate.
      admit.
    }
    injection x as <-.
    exists 0; repeat econstructor; simple.
  - admit.
  - admit.
  - destruct e; simple; try discriminate.
    { destruct n; simple; try discriminate.
      (* f1 -> vClos ... and head (term_of_val u) = tConstruct *) admit. }
    injection x as ??; subst.
    edestruct IHheval1 as (n1 & v1' & heq1 & Iheval1); simple; try easy.
    edestruct IHheval2 as (n2 & v2' & heq2 & Iheval2); simple; try reflexivity; try easy.
    assert (isvClos v1').
    { now rewrite isvClos_isLambda -heq1. }
    destruct v1'; simple; try easy.
    injection heq1 as <- heq1.
    eexists. eexists; split.
    shelve.
    econstructor; try easy.
    Search b0.
    (* Maybe do a trick with csubsto : option term -> nat -> term who csubst if isSome, and likewise to add to Γ *)
    (* It looks like what I'm doing might be best done after the logical relation *)
Admitted.

Lemma eval_SI_substl {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ e v n : 
  has_tApp ->
  with_constructor_as_block = cstr_as_blocks ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ #|Γ| e ->
  eval Σ [] (substl (map term_of_val Γ) e) v n ->
  ∑ (n' : nat) (v' : value),
  term_of_val v = term_of_val v' ×
  eval Σ Γ e v' n'.
Proof.
  intros htApp c_blocks wf_Σ wf_Γ wf_e heval; simple.
  induction Γ in e, htApp, c_blocks, wf_Σ, wf_Γ, wf_e, heval |- *; simple.
  { now eexists. }
  unfold substl in *; simple.
  unshelve epose proof IHΓ _ _ _ _ _ _ heval as (n' & v' & heq' & heval'); simple; try easy.
  { apply wellformed_csubst; simple.
    apply wellformed_val_wellformed; now simple. }
  rewrite heq'.
  eapply eval_SI_csubst; simple; easy.
Qed.


Lemma eval_SI_subst {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ e v n :
  has_tApp ->
  with_constructor_as_block = cstr_as_blocks ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ #|Γ| e ->
  eval Σ Γ e v n ->
  (* expr_rel e (substl (map term_of_val Γ) e) *)
  ∑ (n' : nat) (v' : value),
  term_of_val v = term_of_val v' × 
  eval Σ [] (substl (map term_of_val Γ) e) v' n'.
Proof.
  intros htApp c_blocks wf_Σ wf_Γ wf_e heval; simple.
  induction heval; simple; try solve[
    now do 4 try econstructor
  ].
  - admit.
  - destruct (eval_SI_val Σ [] v) as (n' & v' & heqv' & hevalv'); simple.
    { now eapply wf_Γ, nth_error_In. }
    exists n', v'; split; simple.
    erewrite substl_tRel; simple; try easy.
    apply nth_error_In in e.
    now eapply wellformed_closed, wellformed_val_wellformed.
  - simple.
    destruct IHheval1 as (n1 & v1 & heq1 & Iheval1); simple; try easy.
    destruct IHheval2 as (n2 & v2 & heq2 & Iheval2); simple; try easy.
    destruct IHheval3 as (n3 & v3 & heq3 & Iheval3); simple; try easy.
    { intros x [<- | hIn]; simple.
      - now apply eval_SI_wf_val in heval2; simple.
      - now apply eval_SI_wf_val in heval1; simple. }
    { now apply eval_SI_wf_val in heval1; simple. }
    unfold substl in Iheval3; simple.
    rewrite fold_csubst_csubst_commute in Iheval3; simple; try easy.
    { admit. }
    { admit. }
    simple.
    assert (isvClos v1).
    { now rewrite isvClos_isLambda -heq1. }
    destruct v1; simple; try easy.
    injection heq1 as -> heq1.
    rewrite heq1 heq2 in Iheval3.
    rewrite -fold_csubst_csubst_commute in Iheval3; simple; try easy.
    { admit. }
    { admit. }
    change (
        fold_left 
          (λ bod term, csubst term 0 bod) 
          (map term_of_val env) 
          (csubst (term_of_val v2) 0 b0)
    ) with (
      substl (map term_of_val (v2 :: env)) b0
    ) in Iheval3.
    epose proof eval_SI_substl _ _ _ _ _ _ _ _ _ _ Iheval3 as (? & v3' & ? & ?).
    eexists. exists v3'; split; first easy.
    now econstructor; simple.
  - destruct IHheval1 as (n1 & v1' & heq1 & IHeval1); simple; 
      try easy.
    destruct IHheval2 as (n2 & v2' & heq2 & IHeval2); simple; try easy.
    { admit. }
     unfold substl in IHeval2; simple.
     rewrite heq1 fold_csubst_csubst_commute in IHeval2; simple; try easy.
    { admit. }
    { admit. }
    unshelve epose proof eval_SI_csubst _ _ _ _ _ _ _ _ _ _ _ IHeval2 as (? & res' & ? & ?); simple; try easy.
    { admit. }
     eexists. exists res'; split; try easy.
     now econstructor; simple.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma eval_SI_eval {efl : EEnvFlags} {wfl : WcbvFlags} Σ e v :
  (*  with_guarded_fix = false -> *)
  cstr_as_blocks = with_constructor_as_block ->
  has_tApp ->
  wf_glob Σ ->
  (* forallb (wellformed_val Σ) Γ -> *)
  wellformed Σ 0 e ->
  EWcbvEval.eval Σ e v ->
  ∑ (n : nat) (v' : value), (v = term_of_val v') × eval Σ [] e v' n.
  (* See to add substitutions here *)
Proof.
  intros hcblocks htApp wf_Σ wf_e h_eval.
  induction h_eval using EWcbvEval.eval_ind; simple.
  - destruct IHh_eval1 as (? & [] & ? & ?); simple; try solve[destruct cstr_as_blocks; my_discr | easy].
    destruct IHh_eval2 as (? & ? & ? & ?); simple; first easy; subst.
    now repeat econstructor.
  - apply eval_wellformed in h_eval1; simple; try easy.
    apply eval_wellformed in h_eval2; simple; try easy.
    assert (wellformed Σ 0 (csubst a' 0 b)).
    { apply wellformed_csubst; now simple.  }
    apply eval_wellformed in h_eval3; simple; try easy.
    destruct 
      IHh_eval1 as (n1 & v'1 & heq1 & IH1),
      IHh_eval2 as (n2 & v'2 & heq2 & IH2),
      IHh_eval3 as (n3 & v'3 & heq3 & IH3); simple; try easy; subst.
    destruct (term_of_val_lambda _ _ _ (eq_sym heq1)) as (Γ & t & ->).
    pose proof eval_SI_subst.
    exists (n1 + n2 + n3 + 1), v'3; split; first easy.
    econstructor; try easy.
    simple.
    injection heq1 as ->.
    rewrite -fold_csubst_csubst_commute in IH3; simple; try easy.
    { now eapply wellformed_closed. }
    { apply eval_SI_wf_val in IH1, IH2; simple; try easy.
      intros. now eapply wellformed_closed, wellformed_val_wellformed. }
Admitted. *)