From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MRMSets.Sig.

Module qKernameSetExtraDecide <: MSetAVL.QuotationOfDecide KernameSet.E KernameSet KernameSetExtraDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSetExtraDecide").
End qKernameSetExtraDecide.
