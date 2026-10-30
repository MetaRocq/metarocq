From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.FSets Require Import FMapFacts.Sig.

Module qKernameMapFact.
  Module qF <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.F.
    MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMapFact.F").
  End qF.
End qKernameMapFact.
