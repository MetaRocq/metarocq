From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelSetOrdProp <: QuotationOfOrdProperties LevelSet LevelSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts LevelSet.E LevelSetOrdProp.ME.
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties LevelSet LevelSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn Level LevelSet LevelSetOrdProp.P.Dec.
      MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn Level LevelSet LevelSetOrdProp.P.FM.
      MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.P.FM").
    End qFM.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "LevelSetOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "LevelSetOrdProp").
End qLevelSetOrdProp.
