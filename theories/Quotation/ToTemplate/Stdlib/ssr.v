From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init.
From Stdlib.ssr Require Import ssrbool ssreflect.

#[export] Instance quote_if_spec {A b vT vF} {not_b:Prop} {b' a} {qA : quotation_of A} {qvT : quotation_of vT} {qvF : quotation_of vF} {qnot_b : quotation_of not_b} {quote_not_b : ground_quotable not_b} : ground_quotable (@if_spec A b vT vF not_b b' a) := ltac:(destruct 1; exact _).
#[export] Instance quote_alt_spec {P:Prop} {b b'} {qP : quotation_of P} {quoteP : ground_quotable P} : ground_quotable (@alt_spec P b b') := ltac:(destruct 1; exact _).
Section and.
  Context {P1 P2 P3 P4 P5 : Prop}
          {qP1 : quotation_of P1} {qP2 : quotation_of P2} {qP3 : quotation_of P3} {qP4 : quotation_of P4} {qP5 : quotation_of P5}
          {quoteP1 : ground_quotable P1} {quoteP2 : ground_quotable P2} {quoteP3 : ground_quotable P3} {quoteP4 : ground_quotable P4} {quoteP5 : ground_quotable P5}.

  #[export] Instance quote_and3 : ground_quotable (and3 P1 P2 P3) := (ltac:(destruct 1; exact _)).
  #[export] Instance quote_and4 : ground_quotable (and4 P1 P2 P3 P4) := (ltac:(destruct 1; exact _)).
  #[export] Instance quote_and5 : ground_quotable (and5 P1 P2 P3 P4 P5) := (ltac:(destruct 1; exact _)).
End and.
#[export] Existing Instances quote_and3 quote_and4 quote_and5.
(* can't do or without decidability *)
(*
Inductive or3 (P1 P2 P3 : Prop) : Prop := Or31 of P1 | Or32 of P2 | Or33 of P3.
Inductive or4 (P1 P2 P3 P4 : Prop) : Prop :=
 *)
#[export] Instance quote_put {vT sT v1 v2 s} {qvT : quotation_of vT} {qsT : quotation_of sT} {qv1 : quotation_of v1} {qv2 : quotation_of v2} {qs : quotation_of s} : ground_quotable (@TheCanonical.put vT sT v1 v2 s) := ltac:(destruct 1; exact _).
#[export] Instance quote_phantom {T p} {qT : quotation_of T} {qp : quotation_of p} : ground_quotable (@phantom T p) := ltac:(destruct 1; exact _).
#[export] Instance quote_phant {p} {qp : quotation_of p} : ground_quotable (@phant p) := ltac:(destruct 1; exact _).
