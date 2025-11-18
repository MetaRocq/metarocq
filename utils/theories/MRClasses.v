From Corelib Require Import Relation_Definitions.

Class Injective {A B} (f : A -> B) (R : relation A) (R' : relation B) := inj : forall x y, R' (f x) (f y) -> R x y.

Class Neutral {A} (f : A -> A -> A) (z : A) := neutral x : f z x = x.

Class Commutative {A} (f : A -> A -> A) := comm : forall x y, f x y = f y x.

Class Associative {A} (f : A -> A -> A) := assoc : forall x y z, f x (f y z) = f (f x y) z.
Class CommutativeMonoid {A} (zero : A) (add : A -> A -> A) :=
  { add_assoc :: Associative add;
    add_comm :: Commutative add;
    add_neutral :: Neutral add zero }.

Module CommutativeMonoid.
Class IsCommMonoid (A : Type) :=
  { zero : A;
    one : A;
    add : A -> A -> A;
    comm_mon :: CommutativeMonoid zero add }.

Declare Scope comm_monoid.
Notation "0" := zero : comm_monoid.
Notation "1" := one : comm_monoid.
Notation "+" := add : comm_monoid.
End CommutativeMonoid.
