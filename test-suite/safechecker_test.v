From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From MetaRocq Require Import SafeCheckerPlugin.SafeTemplateChecker.

Local Open Scope string_scope.

MetaRocq SafeCheck nat.
(*
Environment is well-formed and Ind(Stdlib.Init.Datatypes.nat,0,[]) has type: Sort([Set])
*)

MetaRocq SafeCheck (3 + 1).

Axiom foo : nat -> nat.
Definition eta_rule : foo = fun x => foo x := eq_refl.

Fail MetaRocq SafeCheck eta_rule.
MetaRocq UnsafeCheck eta_rule.

Definition bool_list := List.map negb (cons true (cons false nil)).
(* was working a bit by accident *)
(* MetaRocq SafeCheck bool_list. *)
MetaRocq RocqCheck bool_list.

(* Time MetaRocq SafeCheck @infer_and_print_template_program. *)
(* Uses template polymorphism:
Error:
Type error: Terms are not <= for cumulativity: Sort([Stdlib.Init.Datatypes.23,Stdlib.Init.Datatypes.24]) Sort([Set]) after reduction: Sort([Stdlib.Init.Datatypes.23,Stdlib.Init.Datatypes.24]) Sort([Set]), while checking MetaRocq.Template.Universes.Universe.Expr.t
*)

(* Unset Universe Minimization ToSet. *)

(* From Stdlib Require Import Decimal. *)
From Stdlib Require Import Decimal.
Definition bignat : nat := Nat.of_num_uint 10000%uint.
MetaRocq SafeCheck bignat.
MetaRocq RocqCheck bignat.

Set Warnings "-notation-overriden".
From MetaRocq.TestSuite Require Import hott_example.

MetaRocq SafeCheck @issect'.

MetaRocq SafeCheck @ap_pp.
MetaRocq RocqCheck ap_pp.

Set MetaRocq Timing.

From MetaRocq.TestSuite Require Import hott_example.

(* FIXME TODO Private polymorphic universes *)
MetaRocq SafeCheck @isequiv_adjointify.
MetaRocq RocqCheck isequiv_adjointify.

MetaRocq SafeCheck @IsEquiv.
MetaRocq RocqCheck IsEquiv.
