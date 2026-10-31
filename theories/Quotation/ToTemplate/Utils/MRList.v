From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaRocq.Utils Require Import MRList.

#[export] Instance quote_nth_error_Spec {A l n o} {qA : quotation_of A} {quoteA : ground_quotable A} {qo : quotation_of o} {ql : quotation_of l} : ground_quotable (@nth_error_Spec A l n o) := ltac:(destruct 1; exact _).
