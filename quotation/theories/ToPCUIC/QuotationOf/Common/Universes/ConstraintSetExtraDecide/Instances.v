From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MRMSets.Sig.

Module qConstraintSetExtraDecide <: MSetAVL.QuotationOfDecide UnivConstraintSet.E ConstraintSet ConstraintSetExtraDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSetExtraDecide").
End qConstraintSetExtraDecide.
