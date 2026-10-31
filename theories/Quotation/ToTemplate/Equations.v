From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate Require Import (hints) Stdlib.Init.
From Equations Require Import Init.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

#[export] Instance quote_equations_tag : ground_quotable equations_tag := ltac:(destruct 1; exact _).
#[export] Instance quote_sigma {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : forall a, ground_quotable (B a)} : ground_quotable (@sigma A B) := ltac:(destruct 1; exact _).
