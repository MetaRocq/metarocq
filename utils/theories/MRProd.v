From Stdlib Require Import Bool RelationClasses.
From Stdlib Require Import ssreflect.
From Stdlib Require Import CRelationClasses.

Local Coercion is_true : bool >-> Sortclass.

Declare Scope pair_scope.

Notation "p .1" := (fst p) : pair_scope.
Notation "p .2" := (snd p) : pair_scope.
Open Scope pair_scope.

Notation "x × y" := (prod x y ) (at level 80, right associativity).

(* transparent version of [proj1], [proj2] *)
Definition proj1 {A B} (x : A /\ B) : A := let (a, b) := x in a.
Definition proj2 {A B} (x : A /\ B) : B := let (a, b) := x in b.

Notation "p .p1" := (proj1 p) (at level 2, left associativity, format "p .p1").
Notation "p .p2" := (proj2 p) (at level 2, left associativity, format "p .p2").

Definition on_snd {A B C} (f : B -> C) (p : A * B) :=
  (fst p, f (snd p)).

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).

Definition map_pair {A B C D} (f : A -> B) (g : C -> D) (p : A × C) : B × D :=
  (f p.1, g p.2).

Lemma on_snd_on_snd {A B C D} (f : C -> D) (g : B -> C) (d : A * B) :
  on_snd f (on_snd g d) = on_snd (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma snd_on_snd {A B C} (f : B -> C) (p : A * B) : snd (on_snd f p) = f (snd p).
Proof. destruct p; reflexivity. Qed.

Lemma compose_on_snd {A B C D} (f : C -> D) (g : B -> C) :
  (fun (x : A * B) => (on_snd f) (on_snd g x)) = on_snd (fun x => f (g x)).
Proof.
  reflexivity.
Qed.

Lemma on_snd_eq_spec {A B C} (f g : B -> C) (x : A * B) :
  f (snd x) = g (snd x) <->
  on_snd f x = on_snd g x.
Proof.
  destruct x; unfold on_snd; cbn. split; congruence.
Qed.

Definition on_pi2 {A B C} (f : B -> B) (p : A * B * C) : A * B * C :=
  (fst (fst p), f (snd (fst p)), snd p).

(** It would be tempting to import ssrbool here, however
  https://github.com/coq/coq/issues/13486 prevents this. *)
Lemma andb_and b b' : b && b' <-> b /\ b'.
Proof. apply andb_true_iff. Qed.

Lemma andb_andI {b b'} : b && b' -> b /\ b'.
Proof. apply andb_and. Qed.

Definition fst_eq {A B} {x x' : A} {y y' : B}
  : (x, y) = (x', y') -> x = x'.
Proof.
  inversion 1; reflexivity.
Qed.

Definition snd_eq {A B} {x x' : A} {y y' : B}
  : (x, y) = (x', y') -> y = y'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma fst_pair {A B} {t : A} (u : B) : (t, u).1 = t.
Proof. reflexivity. Qed.

Lemma snd_pair {A B} {t : A} (u : B) : (t, u).2 = u.
Proof. reflexivity. Qed.

Definition swap {A B : Type} (x : A * B) : B * A :=
  (snd x, fst x).

Definition and_assum {A B : Type} (f : A) (f' : A -> B) : A × B :=
  (f, f' f).

(** n-ary cartesian products in Type, for shorter and more readable intro-patterns *)

Reserved Notation "[ × P1 & P2 ]" (at level 0).
Reserved Notation "[ × P1 , P2 & P3 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 ']' '/ '  &  P3 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 & P4 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 ']' '/ '  &  P4 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 & P5 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  &  P5 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6  ']' '/ '  &  P7 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 ']' '/ '  &  P8 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 ']' '/ '  &  P9 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/'  P9 ']' '/ '  &  P10 ] ']'").

Variant and3 (P1 P2 P3 : Type) : Type := Times3 of P1 & P2 & P3.
Variant and4 (P1 P2 P3 P4 : Type) : Type := Times4 of P1 & P2 & P3 & P4.
Variant and5 (P1 P2 P3 P4 P5 : Type) : Type := Times5 of P1 & P2 & P3 & P4 & P5.
Variant and6 (P1 P2 P3 P4 P5 P6 : Type) : Type := Times6 of P1 & P2 & P3 & P4 & P5 & P6.
Variant and7 (P1 P2 P3 P4 P5 P6 P7 : Type) : Type := Times7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Variant and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Type) : Type := Times8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Variant and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Type) : Type := Times9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Variant and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Type) : Type := Times10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.

#[global] Hint Constructors and3 and4 and5 and6 and7 and8 and9 : core.

Notation "[ × P1 & P2 ]" := (pair P1 P2) (only parsing) : type_scope.
Notation "[ × P1 , P2 & P3 ]" := (and3 P1 P2 P3) : type_scope.
Notation "[ × P1 , P2 , P3 & P4 ]" := (and4 P1 P2 P3 P4) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 & P5 ]" := (and5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.


#[global] Instance Prod_reflexivity {A} {P Q : A -> A -> Type} :
  CRelationClasses.Reflexive P -> CRelationClasses.Reflexive Q -> CRelationClasses.Reflexive (fun x y => prod (P x y) (Q x y)).
Proof.
  econstructor; reflexivity.
Defined.

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
"'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6  ']' '/ '  &  P7 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" (at level 0, format
"'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 ']' '/ '  &  P8 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" (at level 0, format
"'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 ']' '/ '  &  P9 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" (at level 0, format
"'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/'  P9 ']' '/ '  &  P10 ] ']'").

Variant andP6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop := conj6 of P1 & P2 & P3 & P4 & P5 & P6.
Variant andP7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop := conj7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Variant andP8 (P1 P2 P3 P4 P5 P6 P7 P8 : Prop) : Prop := conj8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Variant andP9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Prop) : Prop := conj9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Variant andP10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Prop) : Prop := conj10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (andP6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (andP7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (andP8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (andP9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (andP10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.

#[global] Hint Constructors andP6 andP7 andP8 andP9 andP10 : core.
