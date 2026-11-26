(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EProgram EGlobalEnv EWellformed EWcbvEval
  EFirstorder EImplementBox.
Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.

#[local] Obligation Tactic := idtac.

Definition conditionally (b : bool) (P : Prop) := 
  if b then P else True.

(* Implementing box *)

(* It preserves values in the environment *)
Lemma implement_box_value_pres (efl : EEnvFlags) Σ t :
  wf_glob Σ -> @value block_wcbv_flags Σ t -> 
  @value block_wcbv_flags (implement_box_env Σ) (implement_box t).
Proof.
  intros wf. revert t.
  eapply value_values_ind.
  - move=> -[] //= ato; simp implement_box; try solve [repeat constructor].
    intros n [] => //.
  - intros p hp hp'. simp implement_box.
    apply value_atom. constructor 2. depelim hp'; constructor; auto.
    cbn. now apply All_map.
  - intros ind c mdecl idecl cdecl args wcb hl hnargs H IH.
    simp implement_box. econstructor 2; eauto.
    * now rewrite lookup_constructor_implement_box; tea.
    * now rewrite length_map.
    * now apply All_map.
  - intros f args hd hargs H IH.
    rewrite implement_box_mkApps; simp implement_box.
    depelim hd.
    * now cbn in e.
    * constructor 3. rewrite length_map; simp implement_box.
      { eapply value_head_cofix; [|exact l].
        move: e; rewrite /cofix_arity nth_error_map.
        destruct nth_error => //=. }
      now eapply map_nil.
      now eapply All_map.
    * now cbn in y.
Qed.

Lemma implement_box_values_glob_pres (efl : EEnvFlags) Σ :
  wf_glob Σ -> ∥ @values_glob block_wcbv_flags Σ ∥ -> 
  ∥ @values_glob block_wcbv_flags (implement_box_env Σ) ∥.
Proof.
  intros wf v. induction wf. sq. constructor.
  depelim v. depelim X. specialize (IHwf (sq X)). sq. cbn. constructor => //.
  destruct d as [[[dbody|]]|]; cbn in * |-; try solve [constructor; auto].
  cbn -[implement_box]. 
  eapply implement_box_value_pres; tea.
Qed.

Lemma implement_box_lambda_glob_pres (efl : EEnvFlags) Σ :
  wf_glob Σ -> ∥ lambda_glob Σ ∥ -> 
  ∥ lambda_glob (implement_box_env Σ) ∥.
Proof.
  intros wf v. induction wf. sq. constructor.
  depelim v. depelim X. specialize (IHwf (sq X)). sq. cbn. constructor => //.
  destruct d as [[[dbody|]]|]; cbn in * |-; try solve [constructor; auto].
  cbn -[implement_box]. destruct d1 as [na [b ->]]. simp implement_box.
  now eexists.
Qed.

Program Definition implement_box_transformation (efl : EEnvFlags)
  (has_app : has_tApp) (has_lam : has_tLambda) (has_letin : has_tLetIn)
  (nocofix : has_tCoFix = false)
  (nopars : has_cstr_params = false) pres_values :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags)
    (eval_eprogram block_wcbv_flags) :=
  {| name := "implementing box";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := wf_eprogram efl p /\
      conditionally pres_values (∥ lambda_glob p.1 ∥) ;
    post p := wf_eprogram (switch_off_box efl) p /\
      conditionally pres_values (∥ lambda_glob p.1 ∥);
    obseq p hp p' v v' := v' = implement_box v |}.
Next Obligation.
  intros. destruct p as [p pres]; cbn in *. split.
  * split.
    - eapply implement_box_env_wf_glob; eauto. apply p.
    - eapply transform_wellformed'. all:eauto. all: apply p.
  * destruct pres_values => //=. cbn in pres.
    destruct p as [wf _].
    now eapply implement_box_lambda_glob_pres.
    (* now eapply implement_box_values_glob_pres. *)
Qed.
Next Obligation.
  intros efl hasapp haslam haslet nocof nopars pres_values.
  intros pr v [wf pres] pre.
  destruct pr. destruct wf, pre; cbn in * |-.
  eexists. split; [ | eauto].
  econstructor.
  eapply implement_box_eval; cbn; eauto.
Qed.

(** First-order values contain no box: they are left unchanged. *)
Lemma implement_box_firstorder_evalue_block Σ v :
  firstorder_evalue_block Σ v -> implement_box v = v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros i n args _ _ IH. simp implement_box. rewrite ?map_InP_spec.
  f_equal.
  rewrite -{2}(map_id args). now apply map_ext_Forall.
Qed.

Lemma is_coind_implement_box Σ kn :
  is_coind (implement_box_env Σ) kn = is_coind Σ kn.
Proof.
  rewrite /is_coind /lookup_inductive_kind /lookup_minductive
    lookup_env_implement_box.
  now destruct lookup_env as [[]|].
Qed.

Lemma firstorder_evalue_block_implement_box_env Σ v :
  firstorder_evalue_block Σ v ->
  firstorder_evalue_block (implement_box_env Σ) v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros i n args hl hargs IH. constructor => //.
  now rewrite (lookup_constructor_pars_args_implement_box
    (efl := all_env_flags)).
Qed.

Lemma fo_evalue_block_implement_box_env Σ v :
  fo_evalue_block (Σ, v) -> fo_evalue_block (implement_box_env Σ, v).
Proof.
  intros [fo hco].
  split; [now apply firstorder_evalue_block_implement_box_env|].
  eapply firstorder_ind_value_is_coind; tea.
  intros kn. apply is_coind_implement_box.
Qed.

Lemma isFunction_implement_box t :
  isFunction t -> isFunction (implement_box t).
Proof.
  apply isFunction_hom; intros; simp implement_box => //.
  apply implement_box_mkApps.
Qed.

Lemma isFunctionS_implement_box t :
  isFunctionS t -> isFunctionS (implement_box t).
Proof.
  apply isFunctionS_hom; intros; simp implement_box => //.
  all: try apply implement_box_mkApps.
  all: now rewrite ?map_InP_spec.
Qed.

Section ImplementBoxETransform.
Local Obligation Tactic := idtac.

(** First-order values are unchanged: the readback is the identity. *)
Program Definition implement_box_etransform (efl : EEnvFlags)
  (has_app : has_tApp) (has_lam : has_tLambda) (has_letin : has_tLetIn)
  (nocofix : has_tCoFix = false)
  (nopars : has_cstr_params = false) (pres_values : bool) :
  ETransform.t extends_env extends_env fo_evalue_block fo_evalue_block
    (fun _ => True) (fun _ => True) :=
  {| ETransform.tr := implement_box_transformation efl has_app has_lam
       has_letin nocofix nopars pres_values;
     ETransform.compile_fo p pr fo := implement_box_program p;
     ETransform.readback := Some |}.
Next Obligation.
  intros efl ha hl hb hc hp pv [] [] pr pr' ext.
  pose proof pr as [[wf _] _]; pose proof pr' as [[wf' _] _]. cbn in *.
  now eapply implement_box_env_extends.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [] [] pr pr' _ eq.
  cbn in eq |- *.
  now rewrite eq.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr [fo hco].
  rewrite /implement_box_program /=.
  rewrite (implement_box_firstorder_evalue_block Σ t) //.
  now apply fo_evalue_block_implement_box_env.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr v v' [fo hco] obs.
  have e : v' = implement_box v := obs.
  rewrite e (implement_box_firstorder_evalue_block Σ v) //.
  exact (fo_evalue_block_implement_box_env Σ v (conj fo hco)).
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr p' v v' [fo _] obs.
  have e : v' = implement_box v := obs.
  now rewrite e (implement_box_firstorder_evalue_block Σ v).
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr [fo _].
  exact (f_equal Some (implement_box_firstorder_evalue_block Σ t fo)).
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
  change (implement_box_program (Σ, EAst.tApp t u) =
    (implement_box_env Σ,
     EAst.tApp (implement_box t)
       (implement_box u))).
  rewrite /implement_box_program. f_equal.
  exact (implement_box_mkApps t [u]).
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv p pr.
  exact (isFunction_implement_box p.2).
Qed.
Next Obligation.
  intros efl ha hl hb hc hp pv [Σ t] pr p' v v' obs hf.
  have e : v' = implement_box v := obs.
  rewrite e. now apply isFunctionS_implement_box.
Qed.
End ImplementBoxETransform.
