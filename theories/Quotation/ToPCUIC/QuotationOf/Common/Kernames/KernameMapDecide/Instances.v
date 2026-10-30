From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MRFSets.Sig.

Module qKernameMapDecide <: FMapAVL.QuotationOfDecide KernameMap.E KernameMap KernameMapDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMapDecide").
End qKernameMapDecide.
