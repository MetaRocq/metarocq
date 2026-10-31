From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MRFSets.Sig.

Module qKernameMapExtraFact <: QuotationOfWFactsExtra_fun KernameMap.E KernameMap KernameMapFact.F KernameMapExtraFact.
  MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMapExtraFact").
End qKernameMapExtraFact.
