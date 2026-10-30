From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.
From MetaRocq.Template Require Import Ast.

Module qTemplateTermUtils <: QuotationOfTermUtils TemplateTerm Env TemplateTermUtils.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateTermUtils").
End qTemplateTermUtils.
