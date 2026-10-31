From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetAVL.Sig.

Module qLevelSet <: MSetAVL.QuotationOfMake Level LevelSet.
  MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSet").
End qLevelSet.
