From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKername <: QuotationOfOrderedType Kername.
  Module qOT <: QuotationOfOrderedTypeOrig Kername.OT.
    MetaRocq Run (tmMakeQuotationOfModule everything None "Kername.OT").
  End qOT.
  MetaRocq Run (tmMakeQuotationOfModuleWorkAroundRocqBug17303 (all_submodules_except [["OT"]]%bs) (*None*) "Kername").
End qKername.
