From Stdlib.Structures Require Import Equalities Orders OrdersTac.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib Require Export Structures.Orders.Sig.

Module Type QuotationOfIsTotalOrder (O : EqLtLe) (S : IsTotalOrder O) :=
 QuotationOfIsEq O S <+ QuotationOfIsStrOrder O S <+ QuotationOfLeIsLtEq O S <+ QuotationOfLtIsTotal O S.

Module Type OrderFactsSig (O : EqLtLe) (P : IsTotalOrder O) := Nop <+ OrderFacts O P.
Module Type QuotationOfOrderFacts (O : EqLtLe) (P : IsTotalOrder O) (S : OrderFactsSig O P).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfOrderFacts.

Module Type MakeOrderTacSig (O : EqLtLe) (P : IsTotalOrder O) := Nop <+ MakeOrderTac O P.

(*
Module QuotationOfMakeOrderTac (O : EqLtLe) (P : IsTotalOrder O) (S : MakeOrderTacSig O P) (Import qO : QuotationOfEqLtLe O) (Import qP : QuotationOfIsTotalOrder O P).
  Include QuotationOfOrderFacts O P S qO qP.
End QuotationOfMakeOrderTac.
*)
Module Type OTF_to_OrderTacSig (OTF : OrderedTypeFull) := Nop <+ OTF_to_OrderTac OTF.
(*
Module QuotationOfOTF_to_OrderTac (OTF : OrderedTypeFull) (S : OTF_to_OrderTacSig OTF) (Import qOTF : QuotationOfOrderedTypeFull OTF).
  Module qTO := QuotationOfOTF_to_TotalOrder OTF S.TO qOTF.
  Export (hints) qTO.
  Include !QuotationOfMakeOrderTac OTF S.TO S qOTF qTO.
End QuotationOfOTF_to_OrderTac.
*)
Module Type OT_to_OrderTacSig (OT : OrderedType) := Nop <+ OT_to_OrderTac OT.
(*
Module QuotationOfOT_to_OrderTac (OT : OrderedType) (S : OT_to_OrderTacSig OT) (Import qOT : QuotationOfOrderedType OT).
  Module qOTF := QuotationOfOT_to_Full OT S.OTF qOT.
  Export (hints) qOTF.
  Include !QuotationOfOTF_to_OrderTac S.OTF S qOTF.
End QuotationOfOT_to_OrderTac.
*)
