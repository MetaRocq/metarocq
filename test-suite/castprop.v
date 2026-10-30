From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import Loader.
From Stdlib Require Import String.
Set Template Cast Propositions.

Definition foo (x : nat) (p : True) := p.

MetaRocq Quote Recursively Definition q_foo := foo.

Definition fooapp := foo 0 I.
MetaRocq Quote Recursively Definition q_fooapp := @fooapp.
Definition f (x : nat) (p : True) (y : nat) := y.

Definition fapp (x : nat) := f 0 I x.
MetaRocq Quote Recursively Definition q_fapp := @fapp.

Definition setprop : { x : nat | x = 0 } := exist 0 eq_refl.
MetaRocq Quote Recursively Definition q_setprop := setprop.

Notation proof t :=
  (Ast.tCast t BasicAst.Cast (Ast.tCast _ BasicAst.Cast (Ast.tSort ((Universes.sProp :: nil)%list; _)))).
