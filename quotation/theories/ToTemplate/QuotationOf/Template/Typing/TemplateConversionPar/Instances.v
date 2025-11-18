From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.
From MetaRocq.Template Require Import Ast Typing.

Module qTemplateConversionPar <: QuotationOfConversionPar TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversionPar.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateConversionPar").
End qTemplateConversionPar.
