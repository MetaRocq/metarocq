From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICLookup <: QuotationOfLookup PCUICTerm PCUICEnvironment PCUICLookup.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICLookup").
End qPCUICLookup.
