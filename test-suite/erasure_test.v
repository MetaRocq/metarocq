From MetaRocq.ErasurePlugin Require Import Loader.
From MetaRocq.Template Require Import Loader.
Set MetaRocq Timing.
Local Open Scope string_scope.

MetaRocq Erase -help.

MetaRocq Erase nat.
(*
Environment is well-formed and Ind(Stdlib.Init.Datatypes.nat,0,[]) has type: ⧆
*)

MetaRocq Erase I.
MetaRocq Erase true.
(*
Environment is well-formed and Construct(Stdlib.Init.Logic.True,0,0,[]) erases to:
⧆
Environment is well-formed and Construct(Stdlib.Init.Datatypes.bool,0,0,[]) erases to:
Construct(Stdlib.Init.Datatypes.bool,0,0)
*)

MetaRocq Erase (@exist _ (fun x => x = 0) 0 (eq_refl)).

Definition test := (proj1_sig (@exist _ (fun x => x = 0) 0 (eq_refl))).

MetaRocq Erase -typed test.

(** Cofix *)
From Stdlib Require Import StreamMemo.

MetaRocq Quote Recursively Definition memo := memo_make.

MetaRocq Erase -typed -unsafe memo_make.

MetaRocq Erase (3 + 1).

Universe i.
MetaRocq Erase ((fun (X : Set) (x : X) => x) nat).

(** Check that optimization of singleton pattern-matchings work *)
MetaRocq Erase  ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

(* (** Check the treatment of Prop <= Type *) *)
MetaRocq Erase ((fun (X : Set) (x : X) => x) True I).
(* MetaRocq Quote Recursively Definition foo := List.map. *)

From Stdlib Require Import List.
Import ListNotations.
MetaRocq Erase (map negb [true; false]).

Set Warnings "-abstract-large-number".
(* Definition bignat := Eval compute in 10000. *)
Test MetaRocq Timing.

(* MetaRocq Erase bignat. *)

From MetaRocq.TestSuite Require Import vs.
MetaRocq Erase main.
