From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICEnvTyping <: QuotationOfEnvTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICEnvTyping").
End qPCUICEnvTyping.
