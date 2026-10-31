From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICTermUtils <: QuotationOfTermUtils PCUICTerm PCUICEnvironment PCUICTermUtils.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICTermUtils").
End qPCUICTermUtils.
