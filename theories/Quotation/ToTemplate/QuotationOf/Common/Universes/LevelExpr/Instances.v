From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelExpr <: QuotationOfOrderedType LevelExpr.
  MetaRocq Run (tmMakeQuotationOfModuleWorkAroundRocqBug17303 everything (*None*) "LevelExpr").
End qLevelExpr.
