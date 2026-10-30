From Stdlib.Structures Require Import Orders.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib Require Export Structures.Equalities.Sig.

Module Type QuotationOfHasLt (Import T : Typ) (Import E : HasLt T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "E").
End QuotationOfHasLt.

Module Type QuotationOfHasLe (Import T : Typ) (Import E : HasLe T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "E").
End QuotationOfHasLe.

Module Type QuotationOfEqLt (E : EqLt) := QuotationOfTyp E <+ QuotationOfHasEq E E <+ QuotationOfHasLt E E.
Module Type QuotationOfEqLe (E : EqLe) := QuotationOfTyp E <+ QuotationOfHasEq E E <+ QuotationOfHasLe E E.
Module Type QuotationOfEqLtLe (E : EqLtLe) := QuotationOfTyp E <+ QuotationOfHasEq E E <+ QuotationOfHasLt E E <+ QuotationOfHasLe E E.

Module Type QuotationOfIsStrOrder (Import E : EqLt) (Import S : IsStrOrder E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfIsStrOrder.

Module Type QuotationOfLeIsLtEq (Import E : EqLtLe) (Import S : LeIsLtEq E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfLeIsLtEq.

Module Type QuotationOfStrOrder (E : StrOrder) := QuotationOfEqualityType E <+ QuotationOfHasLt E E <+ QuotationOfIsStrOrder E E.

Module Type QuotationOfHasCmp (Import T : Typ) (S : HasCmp T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfHasCmp.

Module Type QuotationOfCmpSpec (Import E : EqLt) (Import C : HasCmp E) (S : CmpSpec E C).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfCmpSpec.

Module Type QuotationOfHasCompare (E : EqLt) (C : HasCompare E) := QuotationOfHasCmp E C <+ QuotationOfCmpSpec E C C.

Module Type QuotationOfDecStrOrder (E : DecStrOrder) := QuotationOfStrOrder E <+ QuotationOfHasCompare E E.

Module Type QuotationOfOrderedType (E : Orders.OrderedType) <: QuotationOfDecidableType E := QuotationOfDecStrOrder E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfOrderedTypeFull (E : OrderedTypeFull) := QuotationOfOrderedType E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E.

Module Type QuotationOfUsualStrOrder (E : UsualStrOrder) := QuotationOfUsualEqualityType E <+ QuotationOfHasLt E E <+ QuotationOfIsStrOrder E E.
Module Type QuotationOfUsualDecStrOrder (E : UsualDecStrOrder) := QuotationOfUsualStrOrder E <+ QuotationOfHasCompare E E.
Module Type QuotationOfUsualOrderedType (E : UsualOrderedType) <: QuotationOfUsualDecidableType E <: QuotationOfOrderedType E
 := QuotationOfUsualDecStrOrder E <+ QuotationOfHasEqDec E E.
Module Type QuotationOfUsualOrderedTypeFull (E : UsualOrderedTypeFull) := QuotationOfUsualOrderedType E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E.

Module Type QuotationOfLtIsTotal (Import E : EqLt) (S : LtIsTotal E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfLtIsTotal.

Module Type QuotationOfTotalOrder (E : TotalOrder) := QuotationOfStrOrder E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E <+ QuotationOfLtIsTotal E E.
Module Type QuotationOfUsualTotalOrder (E : UsualTotalOrder) <: QuotationOfTotalOrder E
 := QuotationOfUsualStrOrder E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E <+ QuotationOfLtIsTotal E E.

Module Type Compare2EqBoolSig (O : DecStrOrder) <: HasEqBool O := Nop <+ Compare2EqBool O.

(*
Module QuotationOfCompare2EqBool (O : DecStrOrder) (Import E : Compare2EqBoolSig O) (Import qE : QuotationOfDecStrOrder O) <: QuotationOfHasEqBool O E.
  #[export] Instance qeqb : quotation_of E.eqb := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_eq : quotation_of E.eqb_eq := ltac:(unfold_quotation_of (); exact _).
End QuotationOfCompare2EqBool.
*)
Module Type DSO_to_OTSig (O : DecStrOrder) <: Orders.OrderedType := Nop <+ DSO_to_OT O.
(*
Module QuotationOfDSO_to_OT (O : DecStrOrder) (E : DSO_to_OTSig O) (qO : QuotationOfDecStrOrder O) <: QuotationOfOrderedType E :=
  qO <+ QuotationOfCompare2EqBool O E <+ QuotationOfHasEqBool2Dec O E E.
*)
Local Set Warnings Append "-notation-overridden".
Module Type OT_to_FullSig (O : Orders.OrderedType) <: OrderedTypeFull := Nop <+ OT_to_Full O.
Module QuotationOfOT_to_Full (O : Orders.OrderedType) (E : OT_to_FullSig O) (qO : QuotationOfOrderedType O) <: QuotationOfOrderedTypeFull E.
  Include qO.
  #[export] Instance qle : quotation_of E.le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lteq : quotation_of E.le_lteq := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOT_to_Full.

Module Type OTF_LtIsTotalSig (O : OrderedTypeFull) <: LtIsTotal O := Nop <+ OTF_LtIsTotal O.

Module QuotationOfOTF_LtIsTotal (O : OrderedTypeFull) (S : OTF_LtIsTotalSig O) (Import qO : QuotationOfOrderedTypeFull O) <: QuotationOfLtIsTotal O S.
  #[export] Instance qlt_total : quotation_of S.lt_total := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOTF_LtIsTotal.

Module Type OTF_to_TotalOrderSig (O : OrderedTypeFull) <: TotalOrder := Nop <+ OTF_to_TotalOrder O.
Module QuotationOfOTF_to_TotalOrder (O : OrderedTypeFull) (S : OTF_to_TotalOrderSig O) (qO : QuotationOfOrderedTypeFull O) <: QuotationOfTotalOrder S
 := qO <+ QuotationOfOTF_LtIsTotal O S.

Module Type QuotationOfHasLeb (Import T : Typ) (Import S : HasLeb T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfHasLeb.

Module Type QuotationOfHasLtb (Import T : Typ) (Import S : HasLtb T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfHasLtb.

Module Type QuotationOfLebSpec (T : Typ) (X : HasLe T) (Y : HasLeb T) (S : LebSpec T X Y).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfLebSpec.

Module Type QuotationOfLtbSpec (T : Typ) (X : HasLt T) (Y : HasLtb T) (S : LtbSpec T X Y).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfLtbSpec.

Module Type QuotationOfLeBool (E : LeBool) := QuotationOfTyp E <+ QuotationOfHasLeb E E.
Module Type QuotationOfLtBool (E : LtBool) := QuotationOfTyp E <+ QuotationOfHasLtb E E.

Module Type QuotationOfLebIsTotal (Import X : LeBool) (Import S : LebIsTotal X).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfLebIsTotal.

Module Type QuotationOfTotalLeBool (E : TotalLeBool) := QuotationOfLeBool E <+ QuotationOfLebIsTotal E E.

Module Type QuotationOfLebIsTransitive (Import X : LeBool) (S : LebIsTransitive X).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfLebIsTransitive.

Module Type QuotationOfTotalTransitiveLeBool (E : TotalTransitiveLeBool) := QuotationOfTotalLeBool E <+ QuotationOfLebIsTransitive E E.

Module Type QuotationOfHasBoolOrdFuns (T : Typ) (S : HasBoolOrdFuns T) := QuotationOfHasEqb T S <+ QuotationOfHasLtb T S <+ QuotationOfHasLeb T S.

Module Type QuotationOfBoolOrdSpecs (O : EqLtLe) (F : HasBoolOrdFuns O) (S : BoolOrdSpecs O F) :=
 QuotationOfEqbSpec O O F S <+ QuotationOfLtbSpec O O F S <+ QuotationOfLebSpec O O F S.

Module Type QuotationOfOrderFunctions (E : EqLtLe) (S : OrderFunctions E) :=
  QuotationOfHasCompare E S <+ QuotationOfHasBoolOrdFuns E S <+ QuotationOfBoolOrdSpecs E S S.

Module Type OTF_to_TTLBSig (O : OrderedTypeFull) <: TotalTransitiveLeBool := Nop <+ OTF_to_TTLB O.

(*
Module QuotationOfOTF_to_TTLB (Import O : OrderedTypeFull) (Import S : OTF_to_TTLBSig O) (Import qO : QuotationOfOrderedTypeFull O) <: QuotationOfTotalTransitiveLeBool S.
  #[export] Instance qleb : quotation_of S.leb := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_le : quotation_of S.leb_le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_total : quotation_of S.leb_total := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_trans : quotation_of S.leb_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOTF_to_TTLB.
*)
Module Type TTLB_to_OTFSig (O : TotalTransitiveLeBool) <: OrderedTypeFull := Nop <+ TTLB_to_OTF O.
(*
Module QuotationOfTTLB_to_OTF (Import O : TotalTransitiveLeBool) (Import S : TTLB_to_OTFSig O) (Import qO : QuotationOfTotalTransitiveLeBool O) <: QuotationOfOrderedTypeFull S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle : quotation_of S.le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of S.eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb : quotation_of S.eqb := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_eq : quotation_of S.eqb_eq := ltac:(unfold_quotation_of (); exact _).
  Include QuotationOfHasEqBool2Dec S S S.
  #[export] Instance qeq_equiv : quotation_of S.eq_equiv := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lteq : quotation_of S.le_lteq := ltac:(unfold_quotation_of (); exact _).
End QuotationOfTTLB_to_OTF.
*)
