From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.
From MetaRocq.Template Require Import Ast ReflectAst.

Module qEnvDecide <: QuotationOfEnvironmentDecide TemplateTerm Env EnvDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "EnvDecide").
End qEnvDecide.
