From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelSetOrdProp <: QuotationOfOrdPropertiesT LevelSet LevelSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFactsT LevelSet.E LevelSetOrdProp.ME.
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWPropertiesT LevelSet LevelSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOnT Level LevelSet LevelSetOrdProp.P.Dec.
      MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOnT Level LevelSet LevelSetOrdProp.P.FM.
      MetaRocq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.P.FM").
    End qFM.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "LevelSetOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "LevelSetOrdProp").
End qLevelSetOrdProp.
