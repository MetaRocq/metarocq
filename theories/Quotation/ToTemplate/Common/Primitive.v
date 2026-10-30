From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaRocq.Common Require Import Primitive.

#[export] Instance quote_prim_tag : ground_quotable prim_tag := ltac:(destruct 1; exact _).
