From Stdlib.Structures Require Import Orders OrdersAlt.
From Stdlib.FSets Require Import FMapInterface.
From MetaRocq.Utils Require Import MRFSets.
From MetaRocq.Quotation.ToTemplate Require Import Init.

Module Type QuotationOfWFactsExtra_fun (E : DecidableTypeOrig) (W : WSfun E) (WFacts : WFacts_funSig E W) (WFactsExtra : WFactsExtra_funSig E W WFacts).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "WFactsExtra").
End QuotationOfWFactsExtra_fun.

Module FMapAVL.
  Module Type QuotationOfDecide (T : OrderedTypeOrig) (M : FMapAVL.MakeSig T) (Dec : FMapAVL.DecideSig T M).
    MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "Dec").
  End QuotationOfDecide.
End FMapAVL.
