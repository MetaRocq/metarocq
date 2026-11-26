(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
Set Warnings "-notation-overridden".
Set Warnings "+notation-overridden".
From MetaRocq.Erasure Require ERemoveParams.
From MetaRocq.TemplatePCUIC Require Import PCUICTransform.

Import EProgram Transform.
Import EEnvMap EGlobalEnv.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.Erasure.Typed Require Import ExtractionCorrectness.
From MetaRocq.Erasure Require Import EWellformed.
Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).


#[local] Obligation Tactic := idtac.

Definition rebuild_wf_env {efl} (p : eprogram) (hwf : wf_eprogram efl p): eprogram_env :=
  (GlobalContextMap.make p.1 (wf_glob_fresh p.1 (proj1 hwf)), p.2).

Definition preserves_expansion with_fix p :=
  if with_fix then EEtaExpandedFix.expanded_eprogram p
  else EEtaExpanded.expanded_eprogram_cstrs p.

Definition preserves_expansion_env with_fix p :=
  if with_fix then EEtaExpandedFix.expanded_eprogram_env p
  else EEtaExpanded.expanded_eprogram_env_cstrs p.

Program Definition rebuild_wf_env_transform {fl : EWcbvEval.WcbvFlags} {efl} (with_exp with_fix : bool) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram fl) (eval_eprogram_env fl) :=
  {| name := "rebuilding environment lookup table";
     pre p := wf_eprogram efl p /\ (with_exp -> preserves_expansion with_fix p);
     transform p pre := rebuild_wf_env p (proj1 pre);
     post p := wf_eprogram_env efl p /\ (with_exp -> preserves_expansion_env with_fix p);
     obseq p hp p' v v' := v = v' |}.
Next Obligation.
  cbn. unfold preserves_expansion, preserves_expansion_env.
  intros fl efl [] [] input [wf exp]; cbn; split => //.
Qed.
Next Obligation.
  cbn. intros fl efl [] [] input v [] ev p'; exists v; split => //.
Qed.

#[global]
Instance rebuild_wf_env_extends {fl : EWcbvEval.WcbvFlags} {efl : EEnvFlags} with_exp with_fix :
  TransformExt.t (rebuild_wf_env_transform with_exp with_fix) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. red. now rewrite /transform /=.
Qed.

#[global]
Instance rebuild_wf_env_extends' {fl : EWcbvEval.WcbvFlags} {efl : EEnvFlags} with_exp with_fix :
  TransformExt.t (rebuild_wf_env_transform with_exp with_fix) extends_eprogram extends_eprogram_env.
Proof.
  red. intros p p' pr pr' [? ?]. now rewrite /transform /=.
Qed.

Section RebuildETransform.
Local Obligation Tactic := idtac.

(** Rebuilding the lookup table changes neither the declarations nor the
    term: the readback is the identity. Without expansion requirements, for
    any predicates on first-order values and eta-expansion. *)
Program Definition rebuild_wf_env_etransform_noexp {fl : WcbvFlags}
  {efl : EEnvFlags} (with_fix : bool)
  (fo eta : Transform.program E.global_context EAst.term -> Prop) :
  ETransform.t extends_env extends_map fo (on_map fo) eta (on_map eta) :=
  {| ETransform.tr := rebuild_wf_env_transform (fl := fl) (efl := efl)
       false with_fix;
     ETransform.compile_fo p pr fo := rebuild_wf_env p (proj1 pr);
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply rebuild_wf_env_extends.
Qed.
Next Obligation.
  intros. now cbn.
Qed.
Next Obligation.
  now intros fl efl wf fo eta [Σ t] pr h.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros fl efl wf fo eta [Σ t] pr v v' h obs. change (v = v') in obs.
  subst v'. exact h.
Qed.
Next Obligation.
  intros fl efl wf fo eta p pr p' v v' h obs. change (v = v') in obs.
  subst v'. reflexivity.
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros. unfold transform, rebuild_wf_env_transform.
  f_equal. apply proof_irrelevance.
Qed.
Next Obligation.
  move=> fl efl wf fo eta [ctx t] [ctx' t'] pr pr' /= eq. move: pr'.
  rewrite -eq. intros. f_equal. eapply proof_irrelevance.
Qed.
Next Obligation.
  now intros fl efl wf fo eta Σ t pr h.
Qed.
Next Obligation.
  intros fl efl wf fo eta Σ t u pr _.
  unshelve eexists.
  { destruct pr as [[? ?] ?]; split; [split|]; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  unshelve eexists.
  { destruct pr as [[? ?] ?]; split; [split|]; cbn in * => //.
    now move/andP: H0 => [] /andP[]. }
  cbn. reflexivity.
Qed.
Next Obligation.
  intros fl efl wf fo eta p pr h. exact h.
Qed.
Next Obligation.
  intros fl efl wf fo eta p pr p' v v' obs h. change (v = v') in obs.
  subst v'. exact h.
Qed.

(** The same, preserving the expansion of constructor applications. *)
Program Definition rebuild_wf_env_etransform_exp {fl : WcbvFlags}
  {efl : EEnvFlags} :
  ETransform.t extends_env extends_map fo_evalue fo_evalue_map
    is_eta_app is_eta_app_map :=
  {| ETransform.tr := rebuild_wf_env_transform (fl := fl) (efl := efl)
       true false;
     ETransform.compile_fo p pr fo := rebuild_wf_env p (proj1 pr);
     ETransform.readback := Some |}.
Next Obligation.
  intros. now apply rebuild_wf_env_extends.
Qed.
Next Obligation.
  intros. now cbn.
Qed.
Next Obligation.
  now intros fl efl p pr fo.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros fl efl p pr v v' fo obs. change (v = v') in obs. subst v'.
  exact fo.
Qed.
Next Obligation.
  intros fl efl p pr p' v v' fo obs. change (v = v') in obs. subst v'.
  reflexivity.
Qed.
Next Obligation.
  intros. congruence.
Qed.
Next Obligation.
  now intros.
Qed.
Next Obligation.
  intros. unfold transform, rebuild_wf_env_transform.
  f_equal. apply proof_irrelevance.
Qed.
Next Obligation.
  move=> fl efl [ctx t] [ctx' t'] pr pr' /= eq. move: pr'. rewrite -eq.
  intros. f_equal. eapply proof_irrelevance.
Qed.
Next Obligation.
  intros fl efl Σ t pr h. exact h.
Qed.
Next Obligation.
  intros fl efl Σ t u pr etat.
  unshelve eexists.
  { destruct pr as [[? ?] ?]; split; [split|]; cbn in * => //.
    now move/andP: H0 => [] /andP[].
    intros _. specialize (H1 eq_refl). move/andP: H1 => [] ? ?.
    apply /andP. split => //. }
  unshelve eexists.
  { destruct pr as [[? ?] ?]; split; [split|]; cbn in * => //.
    now move/andP: H0 => [] /andP[].
    intros h; specialize (H1 h). move/andP: H1 => [] ?. cbn.
    move/EEtaExpanded.isEtaExp_tApp_arg => etau.
    apply/andP. split => //. }
  cbn. reflexivity.
Qed.
Next Obligation.
  intros fl efl p pr h. exact h.
Qed.
Next Obligation.
  intros fl efl p pr p' v v' obs h. change (v = v') in obs. subst v'.
  exact h.
Qed.
End RebuildETransform.
