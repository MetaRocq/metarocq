From Stdlib Require Import ssreflect ssrfun ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import UnivConstraintType Universes UnivLoopChecking uGraph.
Declare Scope univ_scope.
Delimit Scope univ_scope with univ.
Bind Scope univ_scope with Universe.t.

Declare Scope cstr_scope.
Delimit Scope cstr_scope with cstr.
Bind Scope cstr_scope with UnivConstraint.t.
Import ConstraintType.

Notation " x ≤ y " := (@pair (Universe.t * UnivConstraintType.ConstraintType.t) Universe.t
  (@pair Universe.t _ x%univ Le) y%univ) (at level 70) : cstr_scope.
Notation " x = y " := (@pair (Universe.t * UnivConstraintType.ConstraintType.t) Universe.t
  (@pair Universe.t _ x%univ Eq) y%univ) (at level 70) : cstr_scope.

Definition of_level (l : Level.t_) : Universe.t := Universe.of_level l.
Coercion of_level : Level.t_ >-> Universe.t.
(* Coercion Universe.of_level : Level.t >-> Universe.t. *)

Coercion Level.level : string >-> Level.t_.

Definition makel (l : Level.t) (n : nat) : Universe.t := Universe.make (l, n).

Notation " l + k " := (Universe.make (Level.level l, k)).

Notation "x ⊔ y" := (Universe.union x y) (at level 60) : univ_scope.


Definition test_model : option universe_model :=
  let la := Level.level "a" in
  let lb := Level.level "b" in
  let lc := Level.level "c" in
  let ls := levels_of_list [la; lb; lc] in
  let cs := constraints_of_list ["a" + 1 ≤ lb; lb ≤ la ⊔ lc]%cstr in
  push_uctx init_model (ls, cs).

Lemma test_model_spec : (if test_model is Some _ then true else false) = true.
Proof.
  reflexivity.
Qed.

Import UnivLoopChecking.LoopCheck.

Definition check_model c :=
  match test_model with
  | Some m => checkb m c
  | None => false
  end.

Check eq_refl : check_model ("a" ≤ "b").
Check eq_refl : check_model ("b" ≤ "c").
Check eq_refl : check_model ("a" + 1 ≤ "c").
Check eq_refl : check_model ("a" + 2 ≤ "c") = false.
Check eq_refl : check_model (("b" + 1) ≤ "a") = false.
Check eq_refl : check_model (("b" + 1) ≤ "a") = false.
Check eq_refl : check_model ("a" ⊔ "b" ≤ "b" + 1).
Check eq_refl : check_model ("a" ⊔ "a" + 1 = "a" + 1).
Check eq_refl : check_model ("a" ⊔ "a" + 1 = "a") = false.
Check eq_refl : check_model ("a" ≤ "a" ⊔ "b" ⊔ "b" + 1).