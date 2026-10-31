From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MRMSets.Sig.

Module qLevelSetExtraDecide <: MSetAVL.QuotationOfDecide LevelSet.E LevelSet LevelSetExtraDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetExtraDecide").
End qLevelSetExtraDecide.
