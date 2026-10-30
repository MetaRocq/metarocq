Ltac zeta1 x :=
  lazymatch x with
  | let a := ?b in ?f => constr:(match b with a => f end)
  end.
