From Stdlib Require Import ssreflect ssrbool List.
From Equations Require Import Equations.
Import ListNotations.

(* Some reflection / EqDec lemmata *)

Inductive reflectProp (P : Prop) : bool -> Prop :=
 | reflectP : P -> reflectProp P true
 | reflectF : ~ P -> reflectProp P false.
Derive Signature for reflectProp.

Lemma elimP {T} {b} : reflectProp T b -> b -> T.
Proof. intros [] => //. Qed.
Coercion elimP : reflectProp >-> Funclass.

Lemma introP {T} {b} : reflectProp T b -> T -> b.
Proof. intros [] => //. Qed.

Hint View for move/ introP|2.
Hint View for apply/ introP|2.

Lemma reflect_reflectProp {P b} : reflect P b -> reflectProp P b.
Proof.
  intros []; constructor; auto.
Qed.

(** If one really wants a computational version. *)
Remark reflectProp_reflect {P b} : reflectProp P b -> reflect P b.
Proof.
  now destruct b; intros H; constructor; depelim H.
Defined.

Lemma reflect_reflectProp_1 {A} {P : A -> Prop} {b} : (forall x, reflect (P x) (b x)) -> (forall x, reflectProp (P x) (b x)).
Proof.
  intros f x. now apply reflect_reflectProp.
Qed.

Lemma reflect_reflectProp_2 {A B} {P : A -> B -> Prop} {b} : (forall x y, reflect (P x y) (b x y)) -> (forall x y, reflectProp (P x y) (b x y)).
Proof.
  intros f x y. now apply reflect_reflectProp.
Qed.

Class ReflectEq A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y : A, reflectProp (x = y) (eqb x y) (* Prevent using reflect in computational content *)
}.
Arguments eqb : simpl never.
Infix "==" := eqb (at level 70).

(* If one needs to eliminate a decidable equality in Type, e.g. when working with PCUIC derivations. *)
Lemma eqb_specT {A} {HR : ReflectEq A} (x y : A) : reflect (x = y) (x == y).
Proof.
  eapply reflectProp_reflect. apply eqb_spec.
Qed.

Lemma eqb_eq {A} `{ReflectEq A} (x y : A) : x == y -> x = y.
Proof.
  elim: eqb_spec; auto.
  discriminate.
Qed.

Lemma eqb_refl {A} {R : ReflectEq A} (x : A) : x == x.
Proof.
  destruct (eqb_spec x x); auto.
Qed.

Lemma neqb {A} {R : ReflectEq A} (x y : A) : ~~ (x == y) <-> x <> y.
Proof.
  destruct (eqb_spec x y); auto; subst; intuition auto.
Qed.

#[global, program] Instance ReflectEq_EqDec {A} (R : ReflectEq A) : EqDec A := {
  eq_dec := fun x y =>
    match eqb x y with
    | true => left _
    | false => right _
    end }.
Next Obligation.
  now apply eqb_eq.
Qed.
Next Obligation.
  rw eqb_refl in Heq_anonymous.
  discriminate.
Qed.

Definition eq_dec_to_bool {A} `{EqDec A} x y :=
  match eq_dec x y with
  | left _ => true
  | right _ => false
  end.

(* Not an instance to avoid loops and making boolean definitions depend on sumbool ones *)
#[global, program]
Definition EqDec_ReflectEq A {E : EqDec A} : ReflectEq A :=
  {| eqb := eq_dec_to_bool |}.
Next Obligation.
Proof.
  unfold eq_dec_to_bool.
  destruct (eq_dec x y).
  all: constructor ; assumption.
Qed.

Ltac nodec :=
  let bot := fresh "bot" in
  try solve [ constructor ; intro bot ; inversion bot ; subst ; tauto ].

Definition eq_option {A} (eqA : A -> A -> bool) (u v : option A) : bool :=
  match u, v with
  | Some u, Some v => eqA u v
  | None, None => true
  | _, _ => false
  end.

#[program, global] Instance reflect_option {A} {HA : ReflectEq A} : ReflectEq (option A) :=
  {| eqb := eq_option eqb |}.
Next Obligation.
Proof.
  destruct x, y.
  all: cbn.
  all: try solve [ constructor ; easy ].
  destruct (eqb_spec a a0) ; nodec.
  constructor. f_equal. assumption.
Qed.

Section eq_list.
  Context {A} (eqA : A -> A -> bool).
  Fixpoint eqb_list (l l' : list A) : bool :=
  match l, l' with
  | a :: l, a' :: l' =>
    if eqA a a' then eqb_list l l'
    else false
  | [], [] => true
  | _, _ => false
  end.
End eq_list.

#[program, global] Instance reflect_list {A} {RA : ReflectEq A} : ReflectEq (list A) :=
  {| eqb := eqb_list eqb |}.
Next Obligation.
Proof.
  induction x in y |- * ; destruct y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - cbn. destruct (eqb_spec a a0) ; nodec.
    destruct (IHx y) ; nodec.
    subst. constructor. reflexivity.
Qed.

#[global] Instance reflect_nat : ReflectEq nat := {
  eqb_spec := reflect_reflectProp_2 PeanoNat.Nat.eqb_spec
}.


Definition eq_bool b1 b2 : bool :=
  if b1 then b2 else negb b2.

Local Obligation Tactic := idtac.

#[global, program] Instance reflect_bool : ReflectEq bool := {
  eqb := eq_bool
}.
Next Obligation.
  intros x y. unfold eq_bool.
  destruct x, y.
  all: constructor.
  all: try reflexivity.
  all: discriminate.
Defined.

Definition eq_sig_true {A f} `{ReflectEq A} (x y : { z : A | f z = true }) : bool :=
  proj1_sig x == proj1_sig y.

#[global, program] Instance reflect_sig_true {A f} `{ReflectEq A} : ReflectEq ({ z : A | f z = true }) := {
  eqb := eq_sig_true
}.
Next Obligation.
  intros A f RA. intros [x hx] [y hy]. unfold eq_sig_true; cbn.
  destruct (eqb_spec x y) ; nodec. subst.
  constructor. pose proof (uip hx hy). subst. reflexivity.
Defined.


Definition eq_prod {A B} (eqA : A -> A -> bool) (eqB : B -> B -> bool) x y :=
  let '(a1, b1) := x in
  let '(a2, b2) := y in
  if eqA a1 a2 then eqB b1 b2
  else false.

#[global, program] Instance reflect_prod : forall {A B}, ReflectEq A -> ReflectEq B -> ReflectEq (A * B) := {
  eqb := eq_prod eqb eqb
}.
Next Obligation.
  intros A B RA RB [x y] [u v].
  unfold eq_prod.
  destruct (eqb_spec x u) ; nodec.
  destruct (eqb_spec y v) ; nodec.
  subst. constructor. reflexivity.
Defined.

Lemma eq_prod_refl :
  forall A B (eqA : A -> A -> bool) (eqB : B -> B -> bool),
    (forall a, eqA a a) ->
    (forall b, eqB b b) ->
    forall p, eq_prod eqA eqB p p.
Proof.
  intros A B eqA eqB eqA_refl eqB_refl [a b].
  simpl. rw eqA_refl. apply eqB_refl.
Qed.

