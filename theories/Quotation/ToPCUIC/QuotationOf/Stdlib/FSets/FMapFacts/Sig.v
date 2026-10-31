From Stdlib.FSets Require Import FMapFacts.
From Stdlib.Structures Require Import Orders.
From MetaRocq.Utils Require Import MRFSets.
From MetaRocq.Quotation.ToPCUIC Require Import Init.

Module Export FSets.
  Module Type QuotationOfWFacts_fun (E : DecidableTypeOrig) (M : WSfun E) (F : WFacts_funSig E M).
    MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFacts_fun.
End FSets.
