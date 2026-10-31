From MetaRocq.Template Require Import Ast.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qTemplateTerm <: QuotationOfTerm TemplateTerm.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateTerm").
End qTemplateTerm.
