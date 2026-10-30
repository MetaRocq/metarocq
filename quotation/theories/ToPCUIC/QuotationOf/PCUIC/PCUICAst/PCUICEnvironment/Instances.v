From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.
From MetaRocq.PCUIC Require Import PCUICAst.

Module qPCUICEnvironment <: QuotationOfEnvironment PCUICTerm PCUICEnvironment.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICEnvironment").
End qPCUICEnvironment.
