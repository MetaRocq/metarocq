From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetList.Sig.

Module qLevelExprSet <: MSetList.QuotationOfMakeWithLeibniz LevelExpr LevelExprSet.
  MetaRocq Run (tmMakeQuotationOfModule everything None "LevelExprSet").
End qLevelExprSet.
