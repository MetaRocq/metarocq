(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EProgram EGlobalEnv EWellformed EWcbvEval
  EFirstorder EImplementLazyForce.
Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.

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

(** First-order values contain no thunk nor force: they are left unchanged. *)
Lemma implement_lazy_force_firstorder_evalue_block Σ v :
  firstorder_evalue_block Σ v -> implement_lazy_force v = v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros i n args _ _ IH. simp implement_lazy_force. rewrite ?map_InP_spec.
  f_equal.
  rewrite -{2}(map_id args). now apply map_ext_Forall.
Qed.

Lemma is_coind_implement_lazy_force Σ kn :
  is_coind (implement_lazy_force_env Σ) kn = is_coind Σ kn.
Proof.
  rewrite /is_coind /lookup_inductive_kind /lookup_minductive
    lookup_env_implement_lazy_force.
  now destruct lookup_env as [[]|].
Qed.

Lemma firstorder_evalue_block_implement_lazy_force_env Σ v :
  firstorder_evalue_block Σ v ->
  firstorder_evalue_block (implement_lazy_force_env Σ) v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros i n args hl hargs IH. constructor => //.
  now rewrite (lookup_constructor_pars_args_implement_lazy_force
    (efl := all_env_flags)).
Qed.

Lemma fo_evalue_block_implement_lazy_force_env Σ v :
  fo_evalue_block (Σ, v) -> fo_evalue_block (implement_lazy_force_env Σ, v).
Proof.
  intros [fo hco].
  split; [now apply firstorder_evalue_block_implement_lazy_force_env|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. apply is_coind_implement_lazy_force.
Qed.

Lemma isFunction_implement_lazy_force t :
  isFunction t -> isFunction (implement_lazy_force t).
Proof.
  apply isFunction_hom; intros; simp implement_lazy_force => //.
  apply implement_lazy_force_mkApps.
Qed.

Lemma isFunctionS_implement_lazy_force t :
  isFunctionS t -> isFunctionS (implement_lazy_force t).
Proof.
  apply isFunctionS_hom; intros; simp implement_lazy_force => //.
  all: try apply implement_lazy_force_mkApps.
  all: now rewrite ?map_InP_spec.
Qed.

Section ImplementLazyForceETransform.
Local Obligation Tactic := idtac.

(** First-order values are unchanged: the readback is the identity. *)
Program Definition implement_lazy_force_etransform (efl : EEnvFlags)
  (has_app : has_tApp) (has_lam : has_tLambda) (has_tbox : has_tBox)
  (nocofix : has_tCoFix = false) (nopars : has_cstr_params = false)
  (pres_values : bool) :
  ETransform.t extends_env extends_env fo_evalue_block fo_evalue_block
    (fun _ => True) (fun _ => True) :=
  {| ETransform.tr := implement_lazy_force_transformation efl has_app has_lam
       has_tbox nocofix nopars pres_values;
     ETransform.compile_fo p pr fo := implement_lazy_force_program p;
     ETransform.readback := Some |}.
Next Obligation.
  intros efl ha hl hb hc hp pv [] [] pr pr' ext.
  pose proof pr as [[wf _] _]; pose proof pr' as [[wf' _] _]. cbn in *.
  now eapply implement_lazy_force_env_extends.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [] [] pr pr' _ eq.
  cbn in eq |- *.
  now rewrite eq.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr [fo hco].
  rewrite /implement_lazy_force_program /=.
  rewrite (implement_lazy_force_firstorder_evalue_block Σ t) //.
  now apply fo_evalue_block_implement_lazy_force_env.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr v v' [fo hco] obs.
  have e : v' = implement_lazy_force v := obs.
  rewrite e (implement_lazy_force_firstorder_evalue_block Σ v) //.
  exact (fo_evalue_block_implement_lazy_force_env Σ v (conj fo hco)).
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr p' v v' [fo _] obs.
  have e : v' = implement_lazy_force v := obs.
  now rewrite e (implement_lazy_force_firstorder_evalue_block Σ v).
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr [fo _].
  exact (f_equal Some (implement_lazy_force_firstorder_evalue_block Σ t fo)).
Qed.
Next Obligation.
  intros. reflexivity.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [] [] pr pr'.
  cbn. now intros <-.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv Σ t u pr _.
  unshelve eexists.
  { destruct pr as [[wfg wf] hv]; split; [split|] => //; cbn in wf.
    now move/andP: wf => [] /andP[]. }
  unshelve eexists.
  { destruct pr as [[wfg wf] hv]; split; [split|] => //; cbn in wf.
    now move/andP: wf => [] /andP[]. }
  change (implement_lazy_force_program (Σ, EAst.tApp t u) =
    (implement_lazy_force_env Σ,
     EAst.tApp (implement_lazy_force t)
       (implement_lazy_force u))).
  rewrite /implement_lazy_force_program. f_equal.
  exact (implement_lazy_force_mkApps t [u]).
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv p pr.
  exact (isFunction_implement_lazy_force p.2).
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr p' v v' obs hf.
  have e : v' = implement_lazy_force v := obs.
  rewrite e. now apply isFunctionS_implement_lazy_force.
Qed.
End ImplementLazyForceETransform.
