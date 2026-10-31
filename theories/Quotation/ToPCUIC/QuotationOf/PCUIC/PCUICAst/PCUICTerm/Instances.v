From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICTerm <: QuotationOfTerm PCUICTerm.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICTerm").
End qPCUICTerm.
