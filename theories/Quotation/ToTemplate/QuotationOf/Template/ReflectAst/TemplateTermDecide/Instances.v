From MetaRocq.Template Require Import Ast ReflectAst.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qTemplateTermDecide <: QuotationOfTermDecide TemplateTerm TemplateTermDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateTermDecide").
End qTemplateTermDecide.
