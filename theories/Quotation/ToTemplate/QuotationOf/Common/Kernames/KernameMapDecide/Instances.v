From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MRFSets.Sig.

Module qKernameMapDecide <: FMapAVL.QuotationOfDecide KernameMap.E KernameMap KernameMapDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMapDecide").
End qKernameMapDecide.
