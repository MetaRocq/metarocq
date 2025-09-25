From MetaRocq.Utils Require Import MRClasses.
From MetaRocq.Utils Require Import SemiLattice.
From Stdlib Require Import ZArith Lia Program.

Instance Zmin_comm : Commutative Z.min := Z.min_comm.
Instance Zmax_comm : Commutative Z.max := Z.max_comm.

Instance nat_min_comm : Commutative Nat.min := Nat.min_comm.
Instance nat_max_comm : Commutative Nat.max := Nat.max_comm.

Instance nat_min_assoc : Associative Nat.min := Nat.min_assoc.
Instance nat_max_assoc : Associative Nat.max := Nat.max_assoc.

Instance Zmin_assoc : Associative Z.min := Z.min_assoc.
Instance Zmax_assoc : Associative Z.max := Z.max_assoc.

Instance Zadd_assoc : Associative Z.add := Z.add_assoc.
Instance Zadd_comm : Commutative Z.add := Z.add_comm.

Instance Nadd_assoc : Associative Nat.add := Nat.add_assoc.
Instance Nadd_comm : Commutative Nat.add := Nat.add_comm.

Import CommutativeMonoid.

Instance Zadd_neutral : Neutral Z.add 0%Z.
Proof. red. intros. lia. Qed.

Instance Nadd_neutral : Neutral Nat.add 0%nat.
Proof. red. intros. lia. Qed.

Instance Zadd_comm_monoid : CommutativeMonoid 0%Z Z.add := {}.
Instance Nadd_comm_monoid : CommutativeMonoid 0%nat Nat.add := {}.

Instance Zadd_is_comm_monoid : IsCommMonoid Z :=
  { zero := 0%Z;
    one := 1%Z;
    add := Z.add }.

Instance Nadd_is_comm_monoid : IsCommMonoid nat :=
  { zero := 0%nat;
    one := 1%nat;
    add := Nat.add }.


Section ZSemiLattice.
  Import Semilattice.

  Program Definition Zsemilattice : Semilattice Z Z :=
    {| add := Z.add;
      join := Z.max; |}.
  Solve Obligations with program_simpl; try lia.

  Obligation Tactic := idtac.
  Next Obligation.
  Proof.
    intros x; unfold one, Zadd_is_comm_monoid. lia.
  Qed.

End ZSemiLattice.

#[export] Existing Instance Zsemilattice.

Section NatSemiLattice.
  Import Semilattice.

  Program Definition Natsemilattice : Semilattice nat nat :=
    {| add := Nat.add;
      join := Nat.max; |}.
  Solve Obligations with program_simpl; try lia.

End NatSemiLattice.

#[export] Existing Instance Natsemilattice.
