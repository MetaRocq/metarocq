From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetAVL.Sig.

Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  MetaRocq Run (tmMakeQuotationOfModule everything None "KernameSet").
End qKernameSet.
