(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EProgram EGlobalEnv EWellformed EWcbvEval
  EImplementLazyForce.
Import Transform.

#[local] Obligation Tactic := idtac.

Lemma lazy_to_lambda_pred Σ t :
  lazy_value_pred Σ t ->
  lambda_value_pred (implement_lazy_force_env Σ) (implement_lazy_force t).
Proof.
  intros [body eq]. subst t; simp implement_lazy_force.
  now eexists.
Qed.

Lemma lazy_to_lambda_glob Σ :
  lazy_glob Σ -> lambda_glob (implement_lazy_force_env Σ).
Proof.
  induction 1; cbn.
  - constructor.
  - constructor; tea.
    destruct d as [[[dbody|]]|]; cbn -[implement_lazy_force] in * => //.
    now eapply lazy_to_lambda_pred.
Qed.

Lemma value_pres (efl : EEnvFlags) Σ t :
  wf_glob Σ -> @value block_wcbv_flags Σ t -> 
  @value block_wcbv_flags (implement_lazy_force_env Σ)
    (implement_lazy_force t).
Proof.
  intros wf. revert t.
  eapply value_values_ind.
  - move=> -[] //= ato; simp implement_lazy_force;
      try solve [repeat constructor].
    intros n [] => //.
  - intros p hp hp'. simp implement_lazy_force.
    apply value_atom. constructor 2. depelim hp'; constructor; auto.
    cbn. now apply All_map.
  - intros ind c mdecl idecl cdecl args wcb hl hnargs H IH.
    simp implement_lazy_force. econstructor 2; eauto.
    * now rewrite lookup_constructor_implement_lazy_force; tea.
    * now rewrite length_map.
    * now apply All_map.
  - intros f args hd hargs H IH.
    rewrite implement_lazy_force_mkApps; simp implement_lazy_force.
    depelim hd.
    * now cbn in e.
    * constructor 3. rewrite length_map; simp implement_lazy_force.
      { eapply value_head_cofix; [|exact l].
        move: e; rewrite /cofix_arity nth_error_map.
        destruct nth_error => //=. }
      now eapply map_nil.
      now eapply All_map.
    * now cbn in y.
Qed.

Lemma values_glob_pres (efl : EEnvFlags) Σ :
  wf_glob Σ -> ∥ @values_glob block_wcbv_flags Σ ∥ -> 
  ∥ @values_glob block_wcbv_flags (implement_lazy_force_env Σ) ∥.
Proof.
  intros wf v. induction wf. sq. constructor.
  depelim v. depelim X. specialize (IHwf (sq X)). sq. cbn. constructor => //.
  destruct d as [[[dbody|]]|]; cbn in * |-; try solve [constructor; auto].
  cbn -[implement_lazy_force]. 
  eapply value_pres; tea.
Qed.

Program Definition implement_lazy_force_transformation (efl : EEnvFlags)
  (has_app : has_tApp) (has_lam : has_tLambda) (has_tbox : has_tBox)
  (nocofix : has_tCoFix = false) (nopars : has_cstr_params = false)
  (pres_values : bool) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags)
    (eval_eprogram block_wcbv_flags) :=
  {| name := "implementing lazy and force using lambdas ";
    transform p _ := implement_lazy_force_program p ;
    pre p := wf_eprogram efl p /\ 
      (if pres_values then ∥ lazy_glob p.1 ∥ else True) ;
    post p := wf_eprogram (switch_off_thunk efl) p /\ 
      (if pres_values then ∥ lambda_glob p.1 ∥ else True) ;
    obseq p hp p' v v' := v' = implement_lazy_force v |}.
Next Obligation.
  intros efl hasapp haslam hasbox nocof nopars pvals p [wfp hpres].
  split.
  - split. eapply implement_lazy_force_env_wf_glob; eauto. apply wfp.
    apply transform_wellformed'; eauto. all:apply wfp.
  - destruct pvals => //. sq. now apply lazy_to_lambda_glob.
Qed.
Next Obligation.
  intros efl hasapp haslam hasbox nocof nopars pvals p t [wf hpres] ev.
  destruct p as [g p]. destruct wf, ev; cbn in * |-.
  eexists. split; [| eauto].
  split.
  eapply implement_lazy_force_eval; eauto.
Qed.
