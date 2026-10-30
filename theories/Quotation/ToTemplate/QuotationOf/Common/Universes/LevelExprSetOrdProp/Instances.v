From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelExprSetOrdProp <: QuotationOfOrdPropertiesT LevelExprSet LevelExprSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFactsT LevelExprSet.E LevelExprSetOrdProp.ME.
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWPropertiesT LevelExprSet LevelExprSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOnT LevelExpr LevelExprSet LevelExprSetOrdProp.P.Dec.
      MetaRocq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOnT LevelExpr LevelExprSet LevelExprSetOrdProp.P.FM.
      MetaRocq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.P.FM").
    End qFM.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "LevelExprSetOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "LevelExprSetOrdProp").
End qLevelExprSetOrdProp.
