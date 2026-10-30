From Stdlib.Structures Require Import Equalities Orders OrdersFacts.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib Require Export Structures.Orders.Sig.

Module Type CompareFactsT (O : DecStrOrder).
Include CompareFacts O.
End CompareFactsT.

Module Type CompareBasedOrderFactsT (E : EqLtLe) (C : HasCmp E) (O : CompareBasedOrder E C).
Include CompareBasedOrderFacts E C O.
End CompareBasedOrderFactsT.

Module Type BoolOrderFactsT
  (E : EqLtLe)
  (C : HasCmp E)
  (F : HasBoolOrdFuns E)
  (O : CompareBasedOrder E C)
  (S : BoolOrdSpecs E F).
Include BoolOrderFacts E C F O S.
End BoolOrderFactsT.

Module QuotationOfCompareFacts (O : DecStrOrder) (F : CompareFactsT O).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfCompareFacts.

Module Type OrderedTypeFullFactsSig (O : OrderedTypeFull) := Nop <+ OrderedTypeFullFacts O.

Module QuotationOfOrderedTypeFullFacts (O : OrderedTypeFull) (F : OrderedTypeFullFactsSig O).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfOrderedTypeFullFacts.

Module Type OrderedTypeFactsSig (O : Orders.OrderedType) := Nop <+ OrderedTypeFacts O.

Module QuotationOfOrderedTypeFacts (O : Orders.OrderedType) (F : OrderedTypeFactsSig O).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfOrderedTypeFacts.

Module Type QuotationOfOrderedTypeFactsT (O : Orders.OrderedType) (F : OrderedTypeFactsSig O).
  Include QuotationOfOrderedTypeFacts O F.
End QuotationOfOrderedTypeFactsT.

Module Type OrderedTypeRevSig (O : OrderedTypeFull) <: OrderedTypeFull := Nop <+ OrderedTypeRev O.
Module QuotationOfOrderedTypeRev (O : OrderedTypeFull) (S : OrderedTypeRevSig O) (Import qO : QuotationOfOrderedTypeFull O) <: QuotationOfOrderedTypeFull S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of S.eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_equiv : quotation_of S.eq_equiv := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_dec : quotation_of S.eq_dec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle : quotation_of S.le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lteq : quotation_of S.le_lteq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOrderedTypeRev.

Module Type QuotationOfCompareBasedOrder (E : EqLtLe) (C : HasCmp E) (S : CompareBasedOrder E C).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfCompareBasedOrder.

Module QuotationOfCompareBasedOrderFacts (E : EqLtLe) (C : HasCmp E) (O : CompareBasedOrder E C) (F : CompareBasedOrderFactsT E C O).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfCompareBasedOrderFacts.

Module QuotationOfBoolOrderFacts
  (E : EqLtLe)
  (C : HasCmp E)
  (F : HasBoolOrdFuns E)
  (O : CompareBasedOrder E C)
  (S : BoolOrdSpecs E F)
  (Facts : BoolOrderFactsT E C F O S).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "Facts").
End QuotationOfBoolOrderFacts.
