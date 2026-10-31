From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICConversion <: QuotationOfConversion PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICConversion").
End qPCUICConversion.
