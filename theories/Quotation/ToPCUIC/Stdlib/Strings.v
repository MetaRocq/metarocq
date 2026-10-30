From Stdlib Require Import Strings.String Strings.Ascii.
From MetaRocq.Quotation.ToPCUIC Require Import Stdlib.Init.

#[export] Instance quote_ascii : ground_quotable Ascii.ascii := (ltac:(induction 1; exact _)).
#[export] Instance quote_string : ground_quotable string := (ltac:(induction 1; exact _)).
