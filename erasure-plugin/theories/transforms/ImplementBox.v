(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EProgram EGlobalEnv EWellformed EWcbvEval
  EImplementBox.
Import Transform.

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
