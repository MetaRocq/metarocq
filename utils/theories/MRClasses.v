
Class Neutral {A} (f : A -> A -> A) (z : A) := neutral x : f z x = x.

Class Commutative {A} (f : A -> A -> A) := comm : forall x y, f x y = f y x.

Class Associative {A} (f : A -> A -> A) := assoc : forall x y z, f x (f y z) = f (f x y) z.

Class CommutativeMonoid {A} (zero : A) (add : A -> A -> A) :=
  { add_assoc :: Associative add;
    add_comm :: Commutative add;
    add_neutral :: Neutral add zero }.

Class Injective {A B} (f : A -> B) := inj : forall x y, f x = f y -> x = y.
