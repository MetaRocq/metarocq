From Stdlib.Structures Require Import Orders.
From Stdlib.MSets Require Import MSetAVL.
From MetaRocq.Utils Require Import MRMSets.
From MetaRocq.Quotation.ToPCUIC Require Import Init.

Module MSetAVL.
  Module Type QuotationOfMake (T : OrderedType) (M : MSetAVL.MakeSig T).
    MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "M").
  End QuotationOfMake.
End MSetAVL.
