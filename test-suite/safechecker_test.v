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

(* Eta for primitive records. They live in Set: their occurrences as
   arguments of the template polymorphic [eq] then need no universe
   constraint. *)
Set Primitive Projections.
Record pprod (A B : Set) := ppair { pfst : A; psnd : B }.
Record psig (A : Set) (P : A -> Prop) := pexist { pr1 : A; pr2 : P pr1 }.
Record wrap := Wrap { unwrap : nat }.
Unset Primitive Projections.
Axiom pp : pprod nat bool.
Axiom ps : psig nat (fun n => n = n).
Axiom w : wrap.
Axiom pp2 : pprod (pprod nat nat) nat.
Axiom f : nat -> pprod nat nat.

(* The constructor on either side. *)
Definition eta_record_left :
  @ppair nat bool (@pfst _ _ pp) (@psnd _ _ pp) = pp := eq_refl.
Definition eta_record_right :
  pp = @ppair nat bool (@pfst _ _ pp) (@psnd _ _ pp) := eq_refl.

Fail MetaRocq SafeCheck eta_record_left.
Fail MetaRocq SafeCheck eta_record_right.
MetaRocq UnsafeCheck eta_record_left.
MetaRocq UnsafeCheck eta_record_right.

(* Parameters, and a field whose type depends on the previous one. *)
Definition eta_record_dep :
  ps = @pexist nat (fun n => n = n) (@pr1 _ _ ps) (@pr2 _ _ ps) := eq_refl.
MetaRocq UnsafeCheck eta_record_dep.

(* A single field, without parameters. *)
Definition eta_record_single : Wrap (unwrap w) = w := eq_refl.
MetaRocq UnsafeCheck eta_record_single.

(* Nested records: eta is used again on the fields. *)
Definition eta_record_nested :
  pp2 = @ppair _ _
    (@ppair _ _ (@pfst _ _ (@pfst _ _ pp2)) (@psnd _ _ (@pfst _ _ pp2)))
    (@psnd _ _ pp2) := eq_refl.
MetaRocq UnsafeCheck eta_record_nested.

(* Eta for functions, then for records, in both directions. *)
Definition eta_record_fun :
  f = (fun x => @ppair _ _ (@pfst _ _ (f x)) (@psnd _ _ (f x))) := eq_refl.
Definition eta_record_fun_rev :
  (fun x => @ppair _ _ (@pfst _ _ (f x)) (@psnd _ _ (f x))) = f := eq_refl.
MetaRocq UnsafeCheck eta_record_fun.
MetaRocq UnsafeCheck eta_record_fun_rev.

(* Under a binder, on a variable. *)
Definition eta_record_binder :
  (fun p : pprod nat bool => @ppair _ _ (@pfst _ _ p) (@psnd _ _ p))
  = (fun p => p) := eq_refl.
MetaRocq UnsafeCheck eta_record_binder.

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

(* A universe level that occurs only in the sort of an inductive must be quoted *)
Universe quote_sort_u.
Inductive quote_sort_K : Type@{quote_sort_u} := quote_sort_ck.
MetaRocq SafeCheck quote_sort_K.

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
