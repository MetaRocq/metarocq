(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICClosed
     PCUICOnFreeVars PCUICTyping PCUICReduction PCUICGlobalEnv PCUICWeakeningEnv
     PCUICEquality.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma type_local_ctx_All_local_env {cf} P Σ Γ Δ s :
  All_local_env (lift_typing P Σ) Γ ->
  type_local_ctx (lift_typing P) Σ Γ Δ s ->
  All_local_env (lift_typing P Σ) (Γ ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto.
  now eapply lift_sorting_forget_univ.
Qed.

Lemma sorts_local_ctx_All_local_env {cf} P Σ Γ Δ s :
  All_local_env (lift_typing P Σ) Γ ->
  sorts_local_ctx (lift_typing P) Σ Γ Δ s ->
  All_local_env (lift_typing P Σ) (Γ ,,, Δ).
Proof.
  induction Δ in s |- *; simpl; eauto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition eauto.
  destruct s => //. destruct wfctx; eauto.
  destruct s => //. destruct wfctx. now eapply lift_sorting_forget_univ.
Qed.

Lemma type_local_ctx_Pclosed Σ Γ Δ s :
  type_local_ctx (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ Γ Δ s ->
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ).
Proof.
  induction Δ; simpl; auto; try constructor.
  destruct a as [? [] ?]; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rw List.length_rev. 2:constructor.
    rw app_context_length Nat.add_comm in b.
    apply b.
  - apply Alli_app_inv; auto. constructor. simpl.
    rw List.length_rev. 2:constructor.
    rw app_context_length Nat.add_comm in b.
    apply b.
Qed.

Lemma sorts_local_ctx_Pclosed Σ Γ Δ s :
  sorts_local_ctx (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ Γ Δ s ->
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ).
Proof.
  induction Δ in s |- *; simpl; auto; try constructor.
  destruct a as [? [] ?]; intuition auto.
  - apply Alli_app_inv; eauto. constructor. simpl.
    rw List.length_rev. 2:constructor.
    rw app_context_length Nat.add_comm in b.
    apply b.
  - destruct s as [|u us]; auto. destruct X as [X b].
    apply Alli_app_inv; eauto. constructor. simpl.
    rw List.length_rev. 2:constructor.
    rw app_context_length Nat.add_comm in b.
    apply b.
Qed.

Lemma All_local_env_Pclosed Γ :
  All_local_env (lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Γ ->
  Alli (fun i d => closed_decl i d) 0 (List.rev Γ).
Proof.
  induction Γ; simpl; auto; try constructor.
  intros all; depelim all; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rw List.length_rev. 2:constructor.
    assumption.
  - apply Alli_app_inv; auto. constructor. simpl.
    rw List.length_rev. 2:constructor.
    assumption.
Qed.

Lemma weaken_env_prop_closed {cf} :
  weaken_env_prop cumulSpec0 (lift_typing typing) (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)).
Proof. intros ?. auto. Qed.


Lemma closedn_ctx_alpha {k ctx ctx'} :
  eq_context_upto_names ctx ctx' ->
  closedn_ctx k ctx = closedn_ctx k ctx'.
Proof.
  induction 1 in k |- *; simpl; auto.
  rw IHX. f_equal.
  rw (All2_length X).
  destruct r; cbn; now subst.
Qed.

Lemma closedn_All_local_env (ctx : list context_decl) :
  All_local_env (lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) ctx ->
    closedn_ctx 0 ctx.
Proof.
  induction 1 using All_local_env_ind1; auto.
  rw closedn_ctx_cons IHX //=.
Qed.

Lemma declared_minductive_closed_inds {cf} {Σ ind mdecl u} {wfΣ : wf Σ} :
  declared_minductive Σ (inductive_mind ind) mdecl ->
  forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  intros h.
  unshelve eapply declared_minductive_to_gen in h; tea.
  red in h.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as (Σ' & ext & wfΣ' & decl').
  red in decl'. destruct decl' as [h ? ? ?].
  rw inds_spec. rw forallb_rev.
  unfold mapi.
  generalize 0 at 1. generalize 0. intros n m.
  induction h in n, m |- *.
  - reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_cstr_branch_context_gen {cf : checker_flags} {Σ} {wfΣ : wf Σ} {c mdecl cdecl} :
  closed_inductive_decl mdecl ->
  closed_constructor_body mdecl cdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (cstr_branch_context c mdecl cdecl).
Proof.
  intros cl clc.
  move/andP: cl => [] clpars _.
  move/andP: clc => [] /andP [] clargs clinds cltype.
  rw /cstr_branch_context /=.
  eapply (closedn_ctx_expand_lets 0) => // /=.
  eapply (closedn_ctx_subst 0). len. now rw Nat.add_comm.
  eapply closed_inds.
Qed.

Lemma closedn_All_local_closed:
  forall (cf : checker_flags) (Σ : global_env_ext) (Γ : context) (wfΓ : wf_local Σ Γ),
    All_local_env_over (typing Σ) (fun Γ _ t T _ => closedn #|Γ| t && closedn #|Γ| T) Γ wfΓ ->
    closed_ctx Γ.
Proof.
  intros cf Σ Γ wfΓ al.
  induction al; try constructor;
  rw closedn_ctx_cons IHal /= /test_decl //; cbn.
  now move/andP: Hs => [] /= -> _.
Qed.

