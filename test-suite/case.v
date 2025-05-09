From MetaRocq Require Import Template.Loader.

Definition f := fun (n : nat) =>
  match n with
  | 0 => 0
  | S n => n
  end.


MetaRocq Quote Definition f_quoted :=
  ltac:(let t := eval cbv in f in exact t).

MetaRocq Unquote Definition f_from_syntax :=
  ltac:(let t := eval cbv in f_quoted in exact t).

Check eq_refl : f = f_from_syntax.
