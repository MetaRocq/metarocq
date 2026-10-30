From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevel <: QuotationOfOrderedType Level.
  MetaRocq Run (tmMakeQuotationOfModuleWorkAroundRocqBug17303 everything (*None*) "Level").
End qLevel.
