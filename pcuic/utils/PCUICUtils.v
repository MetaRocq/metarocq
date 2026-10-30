(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import RelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(* Dependent lexicographic order *)
Inductive dlexprod {A} {B : A -> Type}
          (leA : A -> A -> Prop) (leB : forall x, B x -> B x -> Prop)
  : sigT B -> sigT B -> Prop :=
| left_lex :
    forall x x' y y',
      leA x x' ->
      dlexprod leA leB (x;y) (x';y')

| right_lex :
    forall x y y',
      leB x y y' ->
      dlexprod leA leB (x;y) (x;y').

Derive Signature for dlexprod.

Definition lexprod := Subterm.lexprod.
Arguments lexprod {_ _} _ _ _ _.

(* Dependent lexicographic order modulo another relation *)
Inductive dlexmod {A} {B : A -> Type}
    (leA : A -> A -> Prop)
    (eA : A -> A -> Prop)
    (coe : forall x x', eA x x' -> B x -> B x')
    (leB : forall x, B x -> B x -> Prop)
  : sigT B -> sigT B -> Prop :=
| left_dlexmod :
    forall x x' y y',
      leA x x' ->
      dlexmod leA eA coe leB (x;y) (x';y')

| right_dlexmod :
    forall x x' y y' (e : eA x x'),
      leB x' (coe _ _ e y) y' ->
      dlexmod leA eA coe leB (x;y) (x';y').
Derive Signature for dlexmod.

Notation "x ⊩ R1 ⨶ R2" :=
  (dlexprod R1 (fun x => R2)) (at level 20, right associativity).
Notation "R1 ⊗ R2" :=
  (lexprod R1 R2) (at level 20, right associativity).

Notation "x ⊨ e \ R1 'by' coe ⨷ R2" :=
  (dlexmod R1 e coe (fun x => R2)) (at level 20, right associativity).

Lemma acc_dlexprod A B leA leB :
    (forall x, well_founded (leB x)) ->
    forall x,
      Acc leA x ->
      forall y,
        Acc (leB x) y ->
        Acc (@dlexprod A B leA leB) (x;y).
Proof.
  intros hw. induction 1 as [x hx ih1].
  intros y. induction 1 as [y hy ih2].
  constructor.
  intros [x' y'] h. simple inversion h.
  - intro hA. inversion H0. inversion H1. subst.
    eapply ih1.
    + assumption.
    + apply hw.
  - intro hB. rewrite <- H0.
    pose proof (projT2_eq H1) as p2.
    set (projT1_eq H1) as p1 in *; cbn in p1.
    destruct p1; cbn in p2; destruct p2.
    eapply ih2. assumption.
Qed.

Lemma dlexprod_Acc A B leA leB :
    (forall x, well_founded (leB x)) ->
    forall x y,
      Acc leA x ->
      Acc (@dlexprod A B leA leB) (x;y).
Proof.
  intros hB x y hA.
  eapply acc_dlexprod ; try assumption.
  apply hB.
Qed.

#[global]
Instance dlexprod_trans A B RA RB :
    Transitive RA ->
    (forall x, Transitive (RB x)) ->
    Transitive (@dlexprod A B RA RB).
Proof.
  intros hA hB [u1 u2] [v1 v2] [w1 w2] h1 h2.
  revert w1 w2 h2. induction h1 ; intros w1 w2 h2.
  - dependent induction h2.
    + left. eapply hA ; eassumption.
    + left. assumption.
  - dependent induction h2.
    + left. assumption.
    + right. eapply hB ; eassumption.
Qed.

Lemma acc_dlexmod A B
      (leA : A -> A -> Prop) (eA : A -> A -> Prop)
      (coe : forall x x', eA x x' -> B x -> B x')
      (leB : forall x : A, B x -> B x -> Prop)
      (sym : forall x y, eA x y -> eA y x)
      (trans : forall x y z, eA x y -> eA y z -> eA x z) :
    (forall x, well_founded (leB x)) ->
    (forall x x' y, eA x x' -> leA y x' -> leA y x) ->
    (forall x, exists e : eA x x, forall y, coe _ _ e y = y) ->
    (forall x x' y e, coe x x' (sym _ _ e) (coe _ _ e y) = y) ->
    (forall x0 x1 x2 e1 e2 y,
      coe _ _ (trans x0 x1 x2 e1 e2) y =
      coe _ _ e2 (coe _ _ e1 y)
    ) ->
    (forall x x' e y y',
      leB _ y (coe x x' e y') ->
      leB _ (coe _ _ (sym _ _ e) y) y'
    ) ->
    forall x,
      Acc leA x ->
      forall y,
        Acc (leB x) y ->
        forall x' (e : eA x x'),
          Acc (@dlexmod A B leA eA coe leB) (x'; coe _ _ e y).
Proof.
  intros hw hA hcoe coesym coetrans lesym.
  induction 1 as [x hx ih1].
  induction 1 as [y hy ih2].
  intros x' e.
  constructor.
  intros [x'' y''] h. dependent destruction h.
  - specialize (hcoe x'') as [e' he'].
    rewrite <- (he' y'').
    eapply ih1.
    + eapply hA. all: eauto.
    + apply hw.
  - simpl in *.
    specialize ih2 with (x' := x'').
    set (e2 := trans _ _ _ e0 (sym _ _ e)).
    set (e1 := sym _ _ e2).
    replace y'' with (coe _ _ e1 (coe _ _ e2 y''))
      by eauto using coesym.
    eapply ih2. subst e2.
    rewrite coetrans.
    eapply lesym.
    assumption.
Qed.

Lemma dlexmod_Acc A B
      (leA : A -> A -> Prop) (eA : A -> A -> Prop)
      (coe : forall x x', eA x x' -> B x -> B x')
      (leB : forall x : A, B x -> B x -> Prop)
      (sym : forall x y, eA x y -> eA y x)
      (trans : forall x y z, eA x y -> eA y z -> eA x z) :
    (forall x, well_founded (leB x)) ->
    (forall x x' y, eA x x' -> leA y x' -> leA y x) ->
    (forall x, exists e : eA x x, forall y, coe _ _ e y = y) ->
    (forall x x' y e, coe x x' (sym _ _ e) (coe _ _ e y) = y) ->
    (forall x0 x1 x2 e1 e2 y,
      coe _ _ (trans x0 x1 x2 e1 e2) y =
      coe _ _ e2 (coe _ _ e1 y)
    ) ->
    (forall x x' e y y',
      leB _ y (coe x x' e y') ->
      leB _ (coe _ _ (sym _ _ e) y) y'
    ) ->
    forall x y,
      Acc leA x ->
      Acc (@dlexmod A B leA eA coe leB) (x ; y).
Proof.
  intros hB ? hcoe ? ? ? x y h.
  specialize (hcoe x) as h'. destruct h' as [e he].
  rewrite <- (he y).
  eapply acc_dlexmod. all: eauto.
  apply hB.
Qed.

Lemma wf_dlexprod A B (leA : A -> A -> Prop) (leB : forall x : A, B x -> B x -> Prop) :
  well_founded leA ->
  (forall x : A, well_founded (leB x)) ->
  well_founded (dlexprod leA leB).
Proof.
  intros wA wB.
  intros [a b]. eapply dlexprod_Acc. all: eauto.
Qed.

#[global]
Instance WF_precompose {T M} (R : M -> M -> Prop) (m : T -> M) :
  WellFounded R -> WellFounded (precompose R m)
  := wf_precompose R m.
