From Stdlib.Numbers Require Import BinNums DecimalFacts HexadecimalFacts
     Cyclic.Int63.PrimInt63 Cyclic.Int63.Uint63
     Cyclic.Abstract.CyclicAxioms
     Cyclic.Abstract.DoubleType
     Cyclic.Int63.CarryType
.

From Stdlib Require Import ZArith.
From MetaRocq.Quotation.ToPCUIC Require Import Stdlib.Init.

#[export] Instance quote_positive : ground_quotable positive := ltac:(induction 1; exact _).
#[export] Instance quote_N : ground_quotable N := ltac:(induction 1; exact _).
#[export] Instance quote_Z : ground_quotable Z := ltac:(induction 1; exact _).

#[export] Hint Unfold
  Pos.le Pos.lt Pos.ge Pos.gt
  N.le N.lt N.ge N.gt
  Z.le Z.lt Z.ge Z.gt
  : quotation.

(* Work around masking-absolute-name warning *)
Module Export Numbers.
  Module Export DecimalFacts.
    #[export] Instance quote_digits : ground_quotable DecimalFacts.digits := ltac:(destruct 1; exact _).
  End DecimalFacts.
  Module Export HexadecimalFacts.
    #[export] Instance quote_digits : ground_quotable HexadecimalFacts.digits := ltac:(destruct 1; exact _).
  End HexadecimalFacts.
End Numbers.

#[export] Instance quote_int : ground_quotable int := fun i => PCUICAst.tInt i.
#[export] Instance quote_pos_neg_int63 : ground_quotable pos_neg_int63 := ltac:(destruct 1; exact _).
#[export] Instance quote_int_wrapper : ground_quotable int_wrapper := ltac:(destruct 1; exact _).
#[export] Instance quote_zn2z {znz} {qznz : quotation_of znz} {quoteznz : ground_quotable znz} : ground_quotable (zn2z znz) := ltac:(destruct 1; exact _).
#[export] Instance quote_carry {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (carry A) := ltac:(destruct 1; exact _).
