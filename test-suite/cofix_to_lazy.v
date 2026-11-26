(** * Cofixpoints as lazy fixpoints

  This file runs the verified erasure pipeline on a few cofixpoints and
  prints the resulting programs. The pipeline translates cofixpoints to
  lazy fixpoints ([ECoInductiveToInductive]) and then pushes the forces
  introduced by the translation inside terms ([EPushForce]). *)

From Stdlib Require Import Streams Bool Nat.
From MetaRocq.Template Require Import TemplateMonad Loader.
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Common Require Import config.
From MetaRocq.Erasure Require Import EProgram EPretty.
From MetaRocq.ErasurePlugin Require Import Erasure.
Import MonadNotation.

Local Open Scope bs_scope.

#[local] Existing Instance config.extraction_checker_flags.

(** The verified pipeline only: no typed erasure, no unverified pass. *)
Program Definition erase_program (p : Ast.Env.program) : eprogram :=
  run_erase_program safe_erasure_config ([], p) _.
Next Obligation.
  split; [reflexivity|].
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

Definition test {A} (a : A) : TemplateMonad unit :=
  aq <- tmQuoteRec a ;;
  p <- tmEval lazy (erase_program aq) ;;
  s <- tmEval lazy (EPretty.print_program p) ;;
  tmMsg s.

(** A nullary cofixpoint: a recursive lazy value. Its body is directly a
    constructor, so the force of the translation cancels. *)
CoFixpoint ones : Stream nat := Cons 1 ones.
MetaRocq Run (test ones).

(** A cofixpoint with one argument *)
CoFixpoint from (n : nat) : Stream nat := Cons n (from (S n)).
MetaRocq Run (test from).

(** The body is a match on a coinductive value: the force is pushed in the
    branch, where it cancels. *)
CoFixpoint smap (f : nat -> nat) (s : Stream nat) : Stream nat :=
  match s with
  | Cons x xs => Cons (f x) (smap f xs)
  end.
MetaRocq Run (test smap).

(** A let-binding in the body: the force is pushed under it. *)
CoFixpoint from' (n : nat) : Stream nat :=
  let m := S n in Cons n (from' m).
MetaRocq Run (test from').

(** A branch returns another coinductive value without a constructor: the
    force of that branch remains. *)
CoFixpoint countdown (n : nat) : Stream nat :=
  match n with
  | 0 => ones
  | S m => Cons n (countdown m)
  end.
MetaRocq Run (test countdown).

(** Mutual cofixpoints *)
CoFixpoint evens (n : nat) : Stream nat := Cons n (odds (S n))
with odds (n : nat) : Stream nat := Cons n (evens (S n)).
MetaRocq Run (test evens).

(** A body which is not syntactically a function: it is eta-expanded up to
    the arity of the cofixpoint. *)
Definition from_alias := from.
CoFixpoint from'' : nat -> Stream nat := from_alias.
MetaRocq Run (test from'').

(** Observing streams: matches on a coinductive type force their
    scrutinee. *)
MetaRocq Run (test (Streams.hd (Streams.tl (Streams.tl ones)))).
MetaRocq Run (test (Str_nth 3 (smap S (from 0)))).

(** A coinductive record with primitive projections *)
Module PrimProj.
  Set Primitive Projections.
  CoInductive stream := { shd : nat; stl : stream }.

  CoFixpoint ones : stream := {| shd := 1; stl := ones |}.
  CoFixpoint from (n : nat) : stream := {| shd := n; stl := from (S n) |}.

  MetaRocq Run (test ones).
  MetaRocq Run (test (shd (stl (from 0)))).
End PrimProj.
