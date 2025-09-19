From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetAVL.Sig.

Module qConstraintSet <: MSetAVL.QuotationOfMake UnivConstraint UnivConstraintSet.
  MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSet").
End qUnivConstraintSet.
