From Stdlib Require Import List Nat.
From MetaRocq.Template Require Import All.

Import MonadNotation ListNotations.

Definition foo : nat. exact 0. Qed.

Local Open Scope bs_scope.
MetaRocq Quote Recursively Definition foo_syn := foo.
MetaRocq Quote Recursively Definition comm_syn := PeanoNat.Nat.add_comm.

Axiom really_opaque : nat.

MetaRocq Quote Recursively Definition really_opaque_syn := really_opaque.

MetaRocq Run (foo_t <- tmQuoteRecTransp foo false ;; (* quote respecting transparency *)
             foo_o <- tmQuoteRec foo ;; (* quote ignoring transparency settings  *)
             tmDefinition "foo_t" foo_t ;;
             tmDefinition "foo_o" foo_o).

Example foo_quoted_correctly :
  (exists c v, lookup_env (fst foo_t) (MPfile ["opaque"; "TestSuite"; "MetaRocq"], "foo") = Some v /\
    v = ConstantDecl c /\ c.(cst_body) = None) /\
    (exists c v, lookup_env (fst foo_o) (MPfile ["opaque"; "TestSuite"; "MetaRocq"], "foo") = Some v /\
    v = ConstantDecl c /\ c.(cst_body) <> None ).
Proof.
  split;eexists;eexists;cbn; now intuition.
Qed.

Time MetaRocq Run (t <- tmQuoteRecTransp PeanoNat.Nat.le_add_r false ;;
                  tmDefinition "add_comm_syn" t). (* quote respecting transparency *)

Time MetaRocq Run (t <- tmQuoteRec PeanoNat.Nat.le_add_r ;;
                  tmDefinition "add_comm_syn'" t). (* quote ignoring transparency settings  *)
