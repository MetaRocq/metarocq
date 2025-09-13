From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetAVL.Sig.

Module qConstraintSet <: MSetAVL.QuotationOfMake UnivConstraint UnivConstraintSet.
  MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSet").
End qUnivConstraintSet.
