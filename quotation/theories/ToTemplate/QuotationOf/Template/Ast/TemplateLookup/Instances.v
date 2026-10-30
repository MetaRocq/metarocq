From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.
From MetaRocq.Template Require Import Ast.

Module qTemplateLookup <: QuotationOfLookup TemplateTerm Env TemplateLookup.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateLookup").
End qTemplateLookup.
