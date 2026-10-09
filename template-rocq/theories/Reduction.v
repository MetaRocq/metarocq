(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import Ast AstUtils WfAst Induction LiftSubst
     UnivSubst TermEquality Typing.

From Equations Require Import Equations.
From Stdlib Require Import ssreflect.

Lemma red1_tApp_mkApps_l Σ Γ M1 N1 M2 :
red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (mkApps N1 M2).
Proof. constructor. auto. Qed.

Lemma red1_tApp_mkApp Σ Γ M1 N1 M2 :
  red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 [M2]) (mkApp N1 M2).
Proof.
  intros.
  change (mkApp N1 M2) with (mkApps N1 [M2]).
  apply app_red_l. auto.
Qed.

Lemma red1_mkApp Σ Γ M1 N1 M2 :
  WfAst.wf Σ M1 ->
  red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApp M1 M2) (mkApp N1 M2).
Proof.
  intros wfM1 H.
  destruct (isApp M1) eqn:Heq.
  destruct M1; try discriminate. simpl.
  revert wfM1. inv H. simpl. intros.
  rewrite mkApp_mkApps. constructor.

  intros.
  rewrite mkApp_mkApps.
  econstructor; eauto.
  inv wfM1. simpl.
  clear -H1.
  unfold is_constructor in *.
  destruct (nth_error args narg) eqn:Heq.
  eapply nth_error_app_left in Heq. now rewrite -> Heq. discriminate.

  intros. rewrite mkApp_mkApps. now constructor.

  intros. simpl.
  constructor. now apply OnOne2_app_r.

  rewrite mkApp_tApp; auto.
  now apply red1_tApp_mkApp.
Qed.

Lemma red1_mkApps_l Σ Γ M1 N1 M2 :
  WfAst.wf Σ M1 -> All (WfAst.wf Σ) M2 ->
  red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApps M1 M2) (mkApps N1 M2).
Proof.
  induction M2 in M1, N1 |- *. simpl; auto.
  intros. specialize (IHM2 (mkApp M1 a) (mkApp N1 a)).
  inv X0.
  forward IHM2. apply wf_mkApp; auto.
  forward IHM2. auto.
  rewrite <- !mkApps_mkApp; auto.
  apply IHM2.
  apply red1_mkApp; auto.
Qed.

Lemma red1_mkApps_r Σ Γ M1 M2 N2 :
  WfAst.wf Σ M1 -> All (WfAst.wf Σ) M2 ->
  OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (mkApps M1 M2) (mkApps M1 N2).
Proof.
  intros. induction X1 in M1, X, X0 |- *.
  inv X0.
  destruct (isApp M1) eqn:Heq. destruct M1; try discriminate.
  simpl. constructor. apply OnOne2_app. constructor. auto.
  rewrite mkApps_tApp; try congruence.
  rewrite mkApps_tApp; try congruence.
  constructor. constructor. auto.
  inv X0.
  specialize (IHX1 (mkApp M1 hd)). forward IHX1.
  apply wf_mkApp; auto. forward IHX1; auto.
  now rewrite !mkApps_mkApp in IHX1.
Qed.
