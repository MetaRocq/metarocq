From MetaRocq.PCUIC Require Import PCUICAst PCUICCumulativitySpec.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICConversionParSpec <: QuotationOfConversionPar PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversionParSpec.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICConversionParSpec").
End qPCUICConversionParSpec.
