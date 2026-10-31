From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICDeclarationTyping <: QuotationOfDeclarationTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICConversionParSpec PCUICTypingDef PCUICLookup PCUICGlobalMaps PCUICDeclarationTyping.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICDeclarationTyping").
End qPCUICDeclarationTyping.
