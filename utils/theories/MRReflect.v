(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Bool.
From MetaRocq.Utils Require Import MRPrelude.
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

(** * Notion of reflection for Type-based properties *)

Inductive reflectT (A : Type) : bool -> Type :=
| ReflectT : A -> reflectT A true
| ReflectF : (A -> False) -> reflectT A false.

Lemma reflectT_reflect (A : Prop) b : reflectT A b -> reflect A b.
Proof.
  destruct 1; now constructor.
Qed.

Lemma reflect_reflectT (A : Prop) b : reflect A b -> reflectT A b.
Proof.
  destruct 1; now constructor.
Qed.

Lemma equiv_reflectT P (b : bool) : (P -> b) -> (b -> P) -> reflectT P b.
Proof.
  intros. destruct b; constructor; auto.
  intros p; specialize (H p). discriminate.
Qed.

Lemma elimT {T} {b} : reflectT T b -> b -> T.
Proof. intros [] => //. Qed.
Coercion elimT : reflectT >-> Funclass.

Lemma introT {T} {b} : reflectT T b -> T -> b.
Proof. intros [] => //. Qed.

Hint View for move/ introT|2.

Lemma reflectT_change_left P Q p :
  CRelationClasses.iffT P Q -> reflectT P p -> reflectT Q p.
Proof.
  intros [] []; constructor; auto.
Qed.

Lemma reflectT_subrelation {A} {R} {r : A -> A -> bool} : (forall x y, reflectT (R x y) (r x y)) -> CRelationClasses.subrelation R r.
Proof.
  intros. intros x y h. destruct (X x y); auto.
Qed.

Lemma reflectT_subrelation' {A} {R} {r : A -> A -> bool} : (forall x y, reflectT (R x y) (r x y)) -> CRelationClasses.subrelation r R.
Proof.
  intros. intros x y h. destruct (X x y); auto. discriminate.
Qed.

Lemma reflectT_pred {A} {p : A -> bool} : forall x, reflectT (p x) (p x).
Proof.
  intros x. now apply equiv_reflectT.
Qed.

Lemma reflectT_pred2 {A B} {p : A -> B -> bool} : forall x y, reflectT (p x y) (p x y).
Proof.
  intros x y. now apply equiv_reflectT.
Qed.

Inductive reflect_opt (PN PS : Prop) : option bool -> Prop :=
  | ReflectNone : PN -> reflect_opt PN PS None
  | ReflectSomeT : PS -> reflect_opt PN PS (Some true)
  | ReflectSomeF : ~ PS -> reflect_opt PN PS (Some false).
Derive Signature for reflect_opt.