From MetaRocq Require Import Template.Loader.

Local Open Scope string_scope.

Abbreviation test := (let x := 2 in x).

MetaRocq Quote Definition letin_syntax := test.

MetaRocq Unquote Definition letin_from_syntax :=
  ltac:(let r := eval red in letin_syntax in exact r).

Check (eq_refl : letin_from_syntax = test).
