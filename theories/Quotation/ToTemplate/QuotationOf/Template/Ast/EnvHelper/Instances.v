From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.Common Require Import Environment.
From MetaRocq.Template Require Import Ast.

Module QuoteEnvHelper <: QuoteEnvironmentHelperSig TemplateTerm Env := QuoteEnvironmentHelper TemplateTerm Env.

Module qQuoteEnvHelper <: QuotationOfQuoteEnvironmentHelper TemplateTerm Env QuoteEnvHelper.
  MetaRocq Run (tmMakeQuotationOfModule everything None "QuoteEnvHelper").
End qQuoteEnvHelper.
