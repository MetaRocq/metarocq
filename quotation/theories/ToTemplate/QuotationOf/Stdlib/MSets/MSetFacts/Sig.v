From Stdlib.MSets Require Import MSetFacts.
From MetaRocq.Utils Require Import MRMSets.
From MetaRocq.Quotation.ToTemplate Require Import Init.

Module Export MSets.
  Module QuotationOfWFactsOn (E : DecidableType) (M : WSetsOn E) (F : WFactsOnSig E M).
    MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFactsOn.

  Module Type QuotationOfWFactsOnT (E : DecidableType) (M : WSetsOn E) (F : WFactsOnSig E M).
    Include QuotationOfWFactsOn E M F.
  End QuotationOfWFactsOnT.

  Module QuotationOfWFacts (M : WSets) (F : WFactsSig M) := QuotationOfWFactsOn M.E M F.
End MSets.
