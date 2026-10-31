From Stdlib.MSets Require Import MSetInterface MSetDecide.
From MetaRocq.Utils Require Import MRMSets.
From MetaRocq.Quotation.ToTemplate Require Import Init.

Module Export MSets.
  Module QuotationOfWDecideOn (E : DecidableType) (M : WSetsOn E) (F : WDecideOnSig E M).
    MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWDecideOn.

  Module Type QuotationOfWDecideOnT (E : DecidableType) (M : WSetsOn E) (F : WDecideOnSig E M).
    Include QuotationOfWDecideOn E M F.
  End QuotationOfWDecideOnT.

  Module QuotationOfWDecide (M : WSets) (F : WDecideSig M) := QuotationOfWDecideOn M.E M F.
End MSets.
