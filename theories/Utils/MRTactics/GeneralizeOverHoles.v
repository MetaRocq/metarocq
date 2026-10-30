From MetaRocq Require Import Utils.MRTactics.Zeta1.
From Stdlib Require Import ssr.ssreflect.

Ltac generalize_over_holes tac :=
  zeta1 (ltac:(let H := fresh in
               (pose H := ltac:(let v := tac () in refine v));
               exact H)).
