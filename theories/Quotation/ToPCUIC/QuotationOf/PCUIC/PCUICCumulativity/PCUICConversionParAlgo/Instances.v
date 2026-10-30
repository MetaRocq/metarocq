From MetaRocq.PCUIC Require Import PCUICAst PCUICCumulativity.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICConversionParAlgo <: QuotationOfConversionPar PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversionParAlgo.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICConversionParAlgo").
End qPCUICConversionParAlgo.
