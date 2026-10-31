From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameSetOrdProp <: QuotationOfOrdPropertiesT KernameSet KernameSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFactsT KernameSet.E KernameSetOrdProp.ME.
    MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWPropertiesT KernameSet KernameSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOnT Kername KernameSet KernameSetOrdProp.P.Dec.
      MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOnT Kername KernameSet KernameSetOrdProp.P.FM.
      MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.P.FM").
    End qFM.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "KernameSetOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "KernameSetOrdProp").
End qKernameSetOrdProp.
