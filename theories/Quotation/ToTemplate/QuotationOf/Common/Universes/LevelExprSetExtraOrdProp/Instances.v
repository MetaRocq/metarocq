From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MRMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelExprSetExtraOrdProp <: QuotationOfExtraOrdProperties LevelExprSet LevelExprSetOrdProp LevelExprSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn LevelExprSet.E LevelExprSet LevelExprSetOrdProp.P LevelExprSetExtraOrdProp.P.
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelExprSetExtraOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "LevelExprSetExtraOrdProp").
End qLevelExprSetExtraOrdProp.
