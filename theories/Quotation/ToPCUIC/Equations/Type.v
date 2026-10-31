From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Equations.
From Equations.Type Require Import -(notations) Logic Relation.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

#[export] Instance quote_Empty : ground_quotable Empty := ltac:(destruct 1).

#[export] Hint Unfold
  prod
  : quotation.
#[export] Typeclasses Transparent
  prod
.

#[export] Instance quote_Id {A a b} {qA : quotation_of A} {qa : quotation_of a} : ground_quotable (@Id A a b) := ltac:(destruct 1; exact _).
#[export] Instance quote_sum {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sum A B) := ltac:(destruct 1; exact _).

#[export] Instance quote_trans_clos {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@trans_clos A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_trans_clos_1n {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@trans_clos_1n A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_trans_clos_n1 {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@trans_clos_n1 A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_clos_refl {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@clos_refl A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_clos_refl_trans {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@clos_refl_trans A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_clos_refl_trans_1n {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@clos_refl_trans_1n A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_clos_refl_trans_n1 {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@clos_refl_trans_n1 A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_clos_refl_sym_trans {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@clos_refl_sym_trans A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_clos_refl_sym_trans_1n {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@clos_refl_sym_trans_1n A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_clos_refl_sym_trans_n1 {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@clos_refl_sym_trans_n1 A R x y)
  := ltac:(induction 1; exact _).

#[export] Hint Unfold
  union
  : quotation.
#[export] Typeclasses Transparent
  union
.

#[export] Instance quote_le_AsB {A B leA leB} {qA : quotation_of A} {qB : quotation_of B} {qleA : quotation_of leA} {qleB : quotation_of leB} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteleA : forall x y, ground_quotable (leA x y)} {quoteleB : forall x y, ground_quotable (leB x y)} {x y} : ground_quotable (@le_AsB A B leA leB x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_lexprod {A B leA leB} {qA : quotation_of A} {qB : quotation_of B} {qleA : quotation_of leA} {qleB : quotation_of leB} {quoteA : ground_quotable A} {quoteB : forall a, ground_quotable (B a)} {quoteleA : forall x y, ground_quotable (leA x y)} {quoteleB : forall a x y, ground_quotable (leB a x y)} {x y} : ground_quotable (@lexprod A B leA leB x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_symprod {A B leA leB} {qA : quotation_of A} {qB : quotation_of B} {qleA : quotation_of leA} {qleB : quotation_of leB} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteleA : forall x y, ground_quotable (leA x y)} {quoteleB : forall x y, ground_quotable (leB x y)} {x y} : ground_quotable (@symprod A B leA leB x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_swapprod {A R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@swapprod A R x y)
  := ltac:(induction 1; exact _).

#[export] Instance quote_Ltl {A:Set} {R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x y} : ground_quotable (@Ltl A R x y)
  := ltac:(induction 1; exact _).
#[export] Instance quote_Desc {A:Set} {R} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} {x} : ground_quotable (@Desc A R x)
  := ltac:(induction 1; exact _).

#[export] Hint Unfold
  Pow
  lex_exp
  : quotation.
#[export] Typeclasses Transparent
  Pow
  lex_exp
.
