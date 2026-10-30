From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From Stdlib.Bool Require Import Bool IfProp.

#[export] Instance quote_reflect {P : Prop} {qP : quotation_of P} {quoteP : ground_quotable P} {quote_negP : ground_quotable (~P)} {b} : ground_quotable (reflect P b) := ltac:(destruct 1; exact _).
#[export] Instance quote_IfProp {A B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {b} : ground_quotable (IfProp A B b) := ltac:(destruct b; adjust_ground_quotable_by_econstructor_inversion ()).
