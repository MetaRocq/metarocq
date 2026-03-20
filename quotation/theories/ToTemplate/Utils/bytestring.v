From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaRocq.Utils Require Import bytestring.

Module String.
  #[export] Instance quote_t : ground_quotable String.t := ltac:(induction 1; exact _).
End String.
#[export] Existing Instance String.quote_t.
Abbreviation quote_bs := String.quote_t.
Abbreviation quote_string := String.quote_t.

#[export] Hint Unfold
  bs
  OT_byte.t
  OT_byte.eq
  OT_byte.lt
  StringOT.t
  StringOT.eq
  StringOT.lt
  : quotation.

Module Tree.
  #[export] Instance quote_t : ground_quotable Tree.t := ltac:(induction 1; exact _).
End Tree.
#[export] Existing Instance Tree.quote_t.
