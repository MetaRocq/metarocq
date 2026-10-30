(* Distributed under the terms of the MIT license. *)
(** Tests of the loop-checking algorithm on small examples, run with Rocq's own evaluation
    (see test/test.v for the extracted version, run on the whole standard library). *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import UnivConstraintType Universes uGraph.
From MetaRocq.Common.LoopChecking Require Import UnivLoopChecking.
Import ConstraintType.

Open Scope bs.

Definition a := Level.level "a".
Definition b := Level.level "b".
Definition c := Level.level "c".
Definition d := Level.level "d".
Definition e := Level.level "e".

Definition levels_abcde : LevelSet.t := LevelSetProp.of_list [a; b; c; d; e].

(** The universe [l + n] *)
Definition univ (l : Level.t) (n : nat) : Universe.t := Universe.make (l, n).
Definition sup := Universe.sup.

Definition cstrs_of_list (l : list UnivConstraint.t) : UnivConstraintSet.t :=
  List.fold_right UnivConstraintSet.add UnivConstraintSet.empty l.

(** A model of the constraints on the given (fresh) levels, if they are consistent *)
Definition model_of (ls : LevelSet.t) (cstrs : UnivConstraintSet.t) : option universe_model :=
  push_uctx init_model (ls, cstrs).

Definition print_model (ls : LevelSet.t) (m : universe_model) : string :=
  print_list (fun l => string_of_level l ++ " -> " ++ string_of_nat (UnivLoopChecking.model_val m l))
    ", " (LevelSet.elements ls).

Definition print_result (ls : LevelSet.t) (r : option universe_model) : string :=
  match r with
  | Some m => print_model ls m
  | None => "inconsistent"
  end.

(** Enforcing a single constraint either extends the model or exhibits a looping universe *)
Definition print_enforce (m : universe_model) (cstr : UnivConstraint.t) : string :=
  match UnivLoopChecking.enforce m cstr with
  | None => "undeclared levels"
  | Some (inl _) => "consistent"
  | Some (inr loop) =>
    "loop on " ++ string_of_universe
      (UnivLoopChecking.from_atoms (UnivLoopChecking.LoopCheck.Impl.CorrectModel.loop_univ loop))
  end.

Definition consistent (r : option universe_model) : bool :=
  match r with Some _ => true | None => false end.

Definition entails (r : option universe_model) (cstr : UnivConstraint.t) : bool :=
  match r with
  | Some m => UnivLoopChecking.check m cstr
  | None => false
  end.

Notation "x ≡ y" := (eq_refl : x = y) (at level 70).

(** * Example from Bezem and Coquand's paper

  Each clause [premises -> l + k] is the constraint [l + k <= max premises]. *)
Definition ex_cstrs := cstrs_of_list [
  (univ b 1, Le, sup (univ a 0) (univ b 0));  (* a, b -> b + 1 *)
  (univ c 3, Le, univ b 0);                   (* b -> c + 3 *)
  (univ d 0, Le, univ c 1);                   (* c + 1 -> d *)
  (univ e 0, Le, sup (univ b 0) (univ d 2))   (* b, d + 2 -> e *)
  ].

(* e -> a. Then a <= e <= max(b, d + 2) <= max(b, c + 3) = b, but b + 1 <= a. *)
Definition ex_loop_cstr : UnivConstraint.t := (univ a 0, Le, univ e 0).
Definition ex_loop_cstrs := UnivConstraintSet.add ex_loop_cstr ex_cstrs.

Definition ex_model := model_of levels_abcde ex_cstrs.

Eval vm_compute in print_result levels_abcde ex_model.
Check (consistent ex_model ≡ true).
Check (consistent (model_of levels_abcde ex_loop_cstrs) ≡ false).

(* Constraints entailed by the example (a >= b + 1 >= c + 4) and one that is not *)
Check (entails ex_model (univ c 4, Le, univ a 0) ≡ true).
Check (entails ex_model (univ b 1, Le, univ a 0) ≡ true).
Check (entails ex_model ex_loop_cstr ≡ false).

(* Enforcing the looping constraint incrementally *)
Eval vm_compute in
  match ex_model with
  | Some m => print_enforce m ex_loop_cstr
  | None => "inconsistent"
  end.

(** * A chain of constraints [l_i + 10 <= l_(i+1) + 1] *)
Fixpoint chain (l : list Level.t) : list UnivConstraint.t :=
  match l with
  | [] | [_] => []
  | hd :: ((hd' :: _) as tl) => (univ hd 10, Le, univ hd' 1) :: chain tl
  end.

Definition levels_to_n n := List.map (fun i => Level.level (string_of_nat i)) (seq 0 n).

Definition chain_levels := levels_to_n 10.
Definition chain_model := model_of (LevelSetProp.of_list chain_levels) (cstrs_of_list (chain chain_levels)).

Eval vm_compute in print_result (LevelSetProp.of_list chain_levels) chain_model.
Check (consistent chain_model ≡ true).

(** * [c + 1 <= c] loops *)
Definition above_cstrs := cstrs_of_list [(univ c 1, Le, univ c 0)].
Check (consistent (model_of (LevelSet.singleton c) above_cstrs) ≡ false).

(** * Extending a model with new constraints *)
Definition initial_cstrs := cstrs_of_list [
  (sup (univ a 0) (univ b 0), Eq, univ c 1);
  (univ c 0, Le, sup (univ a 0) (univ b 0));
  (univ c 0, Le, univ b 0)
  ].

Definition enforced_cstrs := cstrs_of_list [(univ b 10, Le, univ e 0)].

Definition initial_model := model_of levels_abcde initial_cstrs.

Eval vm_compute in print_result levels_abcde initial_model.

Definition extended_model :=
  match initial_model with
  | Some m => UnivLoopChecking.enforce_constraints m enforced_cstrs
  | None => None
  end.

(* e is moved up to b + 10, the initial constraints still hold *)
Eval vm_compute in print_result levels_abcde extended_model.

(* Extending the model is the same as enforcing all the constraints at once *)
Check (consistent extended_model ≡ true).
Check (consistent (model_of levels_abcde (UnivConstraintSet.union initial_cstrs enforced_cstrs)) ≡ true).
Check (entails extended_model (univ b 10, Le, univ e 0) ≡ true).
Check (entails extended_model (univ c 10, Le, univ e 0) ≡ true).
Check (entails initial_model (univ b 10, Le, univ e 0) ≡ false).
