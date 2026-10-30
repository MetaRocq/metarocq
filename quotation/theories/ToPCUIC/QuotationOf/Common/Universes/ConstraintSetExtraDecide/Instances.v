From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MRMSets.Sig.

Module qUnivConstraintSetExtraDecide <: MSetAVL.QuotationOfDecide UnivConstraintSet.E UnivConstraintSet UnivConstraintSetExtraDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "UnivConstraintSetExtraDecide").
End qUnivConstraintSetExtraDecide.
