From Stdlib.Structures Require Import Equalities OrdersAlt.
From Stdlib.Structures Require OrderedType.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib Require Export Structures.Orders.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module Type QuotationOfOrderedTypeOrig (Import O : OrderedTypeOrig).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "O").
End QuotationOfOrderedTypeOrig.

Module Type QuotationOfOrderedTypeAlt (Import O : OrderedTypeAlt).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "O").
End QuotationOfOrderedTypeAlt.

Module Type Update_OTSig (O : OrderedTypeOrig) <: Orders.OrderedType := Nop <+ Update_OT O.
(*
Module QuotationOfUpdate_OT (O : OrderedTypeOrig) (S : Update_OTSig O) (Import qO : QuotationOfOrderedTypeOrig O) <: QuotationOfOrderedType S.

  Include QuotationOfUpdate_DT O S qO.  (* Provides : qt qeq qeq_equiv qeq_dec *)
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfUpdate_OT.
*)
Module Type Backport_OTSig (O : Orders.OrderedType) <: OrderedTypeOrig := Nop <+ Backport_OT O.
(*
Module QuotationOfBackport_OT (O : Orders.OrderedType) (S : Backport_OTSig O) (Import qO : QuotationOfOrderedType O) <: QuotationOfOrderedTypeOrig S.

  Include QuotationOfBackport_DT O S qO. (* Provides : qt qeq qeq_refl qeq_sym qeq_trans qeq_dec *)
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_not_eq : quotation_of S.lt_not_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_trans : quotation_of S.lt_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
End QuotationOfBackport_OT.
*)
Module Type OT_from_AltSig (O : OrderedTypeAlt) <: Orders.OrderedType := Nop <+ OT_from_Alt O.
(*
Module QuotationOfOT_from_Alt (O : OrderedTypeAlt) (S : OT_from_AltSig O) (Import qO : QuotationOfOrderedTypeAlt O) <: QuotationOfOrderedType S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of S.eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_equiv : quotation_of S.eq_equiv := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_eq : quotation_of S.lt_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_lt : quotation_of S.eq_lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_dec : quotation_of S.eq_dec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOT_from_Alt.
*)
Module Type OT_to_AltSig (O : Orders.OrderedType) <: OrderedTypeAlt := Nop <+ OT_to_Alt O.
(*
Module QuotationOfOT_to_Alt (O : Orders.OrderedType) (S : OT_to_AltSig O) (Import qO : QuotationOfOrderedType O) <: QuotationOfOrderedTypeAlt S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_sym : quotation_of S.compare_sym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_Eq : quotation_of S.compare_Eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_Lt : quotation_of S.compare_Lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_Gt : quotation_of S.compare_Gt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_trans : quotation_of S.compare_trans := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOT_to_Alt.
*)

(** * OrderedType *)
Module Type QuotationOfMiniOrderedType (O : OrderedType.MiniOrderedType).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "O").
End QuotationOfMiniOrderedType.

Module Type MOT_to_OTOrigSig (O : OrderedType.MiniOrderedType) <: OrderedTypeOrig := Nop <+ OrderedType.MOT_to_OT O.

Module QuotationOfMOT_to_OTOrig (O : OrderedType.MiniOrderedType) (O' : MOT_to_OTOrigSig O) (Import qO : QuotationOfMiniOrderedType O) <: QuotationOfOrderedTypeOrig O'.
  Include qO.

  #[export] Instance qeq_dec : quotation_of O'.eq_dec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfMOT_to_OTOrig.

Module Type OrderedTypeOrigFactsSig (O : OrderedTypeOrig) := Nop <+ OrderedType.OrderedTypeFacts O.

Module QuotationOfOrderedTypeOrigFacts (O : OrderedTypeOrig) (F : OrderedTypeOrigFactsSig O).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  (*Module qTO.
   #[export] Instance qt : quotation_of F.TO.t := ltac:(unfold_quotation_of (); exact _).
   #[export] Instance qeq : quotation_of F.TO.eq := ltac:(unfold_quotation_of (); exact _).
   #[export] Instance qlt : quotation_of F.TO.lt := ltac:(unfold_quotation_of (); exact _).
   #[export] Instance qle : quotation_of F.TO.le := ltac:(unfold_quotation_of (); exact _).
  End qTO.
  Export (hints) qTO.
  Module qIsTO.
   #[export] Instance qeq_equiv : quotation_of F.IsTO.eq_equiv := ltac:(unfold_quotation_of (); exact _).
   #[export] Instance qlt_strorder : quotation_of F.IsTO.lt_strorder := ltac:(unfold_quotation_of (); exact _).
   #[export] Instance qlt_compat : quotation_of F.IsTO.lt_compat := ltac:(unfold_quotation_of (); exact _).
   #[export] Instance qlt_total : quotation_of F.IsTO.lt_total := ltac:(unfold_quotation_of (); exact _).
   #[export] Instance qle_lteq : quotation_of F.IsTO.le_lteq := ltac:(unfold_quotation_of (); exact _).
  End qIsTO.
  Export (hints) qIsTO.
  Module qOrderTac := !QuotationOfMakeOrderTac F.TO F.IsTO F.OrderTac qTO qIsTO.
  Export (hints) qOrderTac.*)
End QuotationOfOrderedTypeOrigFacts.

Module Type QuotationOfOrderedTypeOrigFactsT (O : OrderedTypeOrig) (F : OrderedTypeOrigFactsSig O).
Include QuotationOfOrderedTypeOrigFacts O F.
End QuotationOfOrderedTypeOrigFactsT.

Module Type KeyOrderedTypeOrigSig (O : OrderedTypeOrig) := Nop <+ OrderedType.KeyOrderedType O.

Module QuotationOfKeyOrderedTypeOrig (O : OrderedTypeOrig) (K : KeyOrderedTypeOrigSig O).
  Module qMO := Nop <+ QuotationOfOrderedTypeOrigFacts O K.MO.
  Export (hints) qMO.
  MetaRocq Run (tmDeclareQuotationOfModule (all_submodules_except [["MO"]]%bs) (Some export) "K").
End QuotationOfKeyOrderedTypeOrig.

Module Type QuotationOfKeyOrderedTypeOrigT (O : OrderedTypeOrig) (K : KeyOrderedTypeOrigSig O).
  Include QuotationOfKeyOrderedTypeOrig O K.
End QuotationOfKeyOrderedTypeOrigT.
