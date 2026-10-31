From MetaRocq.PCUIC Require Import PCUICAst Syntax.PCUICReflect.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICEnvironmentDecide <: QuotationOfEnvironmentDecide PCUICTerm PCUICEnvironment PCUICEnvironmentDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICEnvironmentDecide").
End qPCUICEnvironmentDecide.
