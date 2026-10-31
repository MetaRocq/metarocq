From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaRocq.Utils Require Import MRProd.

Section and.
  Context {P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Type}
          {qP1 : quotation_of P1} {qP2 : quotation_of P2} {qP3 : quotation_of P3} {qP4 : quotation_of P4} {qP5 : quotation_of P5} {qP6 : quotation_of P6} {qP7 : quotation_of P7} {qP8 : quotation_of P8} {qP9 : quotation_of P9} {qP10 : quotation_of P10}
          {quoteP1 : ground_quotable P1} {quoteP2 : ground_quotable P2} {quoteP3 : ground_quotable P3} {quoteP4 : ground_quotable P4} {quoteP5 : ground_quotable P5} {quoteP6 : ground_quotable P6} {quoteP7 : ground_quotable P7} {quoteP8 : ground_quotable P8} {quoteP9 : ground_quotable P9} {quoteP10 : ground_quotable P10}.

  #[export] Instance quote_and3 : ground_quotable (@and3 P1 P2 P3) := ltac:(destruct 1; exact _).
  #[export] Instance quote_and4 : ground_quotable (@and4 P1 P2 P3 P4) := ltac:(destruct 1; exact _).
  #[export] Instance quote_and5 : ground_quotable (@and5 P1 P2 P3 P4 P5) := ltac:(destruct 1; exact _).
  #[export] Instance quote_and6 : ground_quotable (@and6 P1 P2 P3 P4 P5 P6) := ltac:(destruct 1; exact _).
  #[export] Instance quote_and7 : ground_quotable (@and7 P1 P2 P3 P4 P5 P6 P7) := ltac:(destruct 1; exact _).
  #[export] Instance quote_and8 : ground_quotable (@and8 P1 P2 P3 P4 P5 P6 P7 P8) := ltac:(destruct 1; exact _).
  #[export] Instance quote_and9 : ground_quotable (@and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) := ltac:(destruct 1; exact _).
  #[export] Instance quote_and10 : ground_quotable (@and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) := ltac:(destruct 1; exact _).
End and.
#[export] Existing Instances
 quote_and3 quote_and4 quote_and5 quote_and6 quote_and7 quote_and8 quote_and9 quote_and10.
