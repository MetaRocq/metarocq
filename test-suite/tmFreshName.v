From Stdlib Require Import List Arith.
From MetaRocq Require Import Template.All.
Import ListNotations MonadNotation.


MetaRocq Run (x <- tmFreshName ("x" ++ "y")%bs ;;
             tmDefinition x 0).

Check (eq_refl : xy = 0).


MetaRocq Run (x <- tmFreshName ("x" ++ "y")%bs ;;
             tmDefinition x 1).

Check (eq_refl : xy0 = 1).
