From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameSetOrdProp <: QuotationOfOrdProperties KernameSet KernameSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts KernameSet.E KernameSetOrdProp.ME.
    MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties KernameSet KernameSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn Kername KernameSet KernameSetOrdProp.P.Dec.
      MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.FM.
      MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.P.FM").
    End qFM.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "KernameSetOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "KernameSetOrdProp").
End qKernameSetOrdProp.
