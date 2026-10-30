From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MRMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameSetExtraOrdProp <: QuotationOfExtraOrdProperties KernameSet KernameSetOrdProp KernameSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn KernameSet.E KernameSet KernameSetOrdProp.P KernameSetExtraOrdProp.P.
    MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetExtraOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "KernameSetExtraOrdProp").
End qKernameSetExtraOrdProp.
