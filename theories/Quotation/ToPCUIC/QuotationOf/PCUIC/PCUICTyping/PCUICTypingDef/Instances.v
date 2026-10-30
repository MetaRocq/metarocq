From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICTypingDef <: QuotationOfTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICConversionParSpec PCUICTypingDef.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICTypingDef").
End qPCUICTypingDef.
