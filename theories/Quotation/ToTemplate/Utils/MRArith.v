From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaRocq.Utils Require Import MRArith.

#[export] Instance quote_BoolSpecSet {P Q : Prop} {b} {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (BoolSpecSet P Q b) := ltac:(destruct 1; exact _).
