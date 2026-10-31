From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.Common Require Import Environment.

Module QuotePCUICEnvironmentHelper <: QuoteEnvironmentHelperSig PCUICTerm PCUICEnvironment := QuoteEnvironmentHelper PCUICTerm PCUICEnvironment.

Module qQuotePCUICEnvironmentHelper <: QuotationOfQuoteEnvironmentHelper PCUICTerm PCUICEnvironment QuotePCUICEnvironmentHelper.
  MetaRocq Run (tmMakeQuotationOfModule everything None "QuotePCUICEnvironmentHelper").
End qQuotePCUICEnvironmentHelper.
