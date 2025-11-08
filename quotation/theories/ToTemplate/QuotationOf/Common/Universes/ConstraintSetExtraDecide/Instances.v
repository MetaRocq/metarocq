From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MRMSets.Sig.

Module qConstraintSetExtraDecide <: MSetAVL.QuotationOfDecide UnivConstraintSet.E UnivConstraintSet UnivConstraintSetExtraDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "UnivConstraintSetExtraDecide").
End qConstraintSetExtraDecide.
