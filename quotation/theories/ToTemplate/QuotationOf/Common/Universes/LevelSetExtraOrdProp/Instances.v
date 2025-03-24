From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelSetExtraOrdProp <: QuotationOfExtraOrdProperties LevelSet LevelSetOrdProp LevelSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn LevelSet.E LevelSet LevelSetOrdProp.P LevelSetExtraOrdProp.P.
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetExtraOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "LevelSetExtraOrdProp").
End qLevelSetExtraOrdProp.
