From MetaRocq.PCUIC Require Import PCUICAst Syntax.PCUICReflect.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICTermDecide <: QuotationOfTermDecide PCUICTerm PCUICTermDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICTermDecide").
End qPCUICTermDecide.
