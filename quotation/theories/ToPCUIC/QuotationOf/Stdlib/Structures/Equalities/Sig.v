From Stdlib.Structures Require Import Equalities.
From MetaRocq.Quotation.ToPCUIC Require Import Init.

Module Type HasUsualEq (T : Typ).
Include HasUsualEq T.
End HasUsualEq.

Module Type UsualIsEq (T : UsualEq).
Include UsualIsEq T.
End UsualIsEq.

Module Type UsualIsEqOrig (T : UsualEq).
Include UsualIsEqOrig T.
End UsualIsEqOrig.

Module Type QuotationOfTyp (Import T : Typ).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "T").
End QuotationOfTyp.
Module Type QuotationOfHasEq (T : Typ) (Import E : HasEq T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "E").
End QuotationOfHasEq.
Module Type QuotationOfEq (E : Eq) := QuotationOfTyp E <+ QuotationOfHasEq E E.
Module Type QuotationOfIsEq (E : Eq) (Import IE : IsEq E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "IE").
End QuotationOfIsEq.
Module Type QuotationOfIsEqOrig (E : Eq) (Import IEO : IsEqOrig E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "IEO").
End QuotationOfIsEqOrig.
Module Type QuotationOfHasEqDec (E : Eq) (Import EDec : HasEqDec E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "EDec").
End QuotationOfHasEqDec.
Module Type QuotationOfHasEqb (T : Typ) (Import E : HasEqb T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "E").
End QuotationOfHasEqb.

Module Type QuotationOfEqbSpec (T : Typ) (X : HasEq T) (Y : HasEqb T) (Import ES : EqbSpec T X Y).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "ES").
End QuotationOfEqbSpec.

Module Type QuotationOfHasEqBool (E : Eq) (EB : HasEqBool E) := QuotationOfHasEqb E EB <+ QuotationOfEqbSpec E E EB EB.

Module Type QuotationOfEqualityType (E : EqualityType) := QuotationOfEq E <+ QuotationOfIsEq E E.

Module Type QuotationOfEqualityTypeOrig (E : EqualityTypeOrig) := QuotationOfEq E <+ QuotationOfIsEqOrig E E.

Module Type QuotationOfEqualityTypeBoth (E : EqualityTypeBoth) <: QuotationOfEqualityType E <: QuotationOfEqualityTypeOrig E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfIsEqOrig E E.

Module Type QuotationOfDecidableType (E : DecidableType) <: QuotationOfEqualityType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfDecidableTypeOrig (E : DecidableTypeOrig) <: QuotationOfEqualityTypeOrig E
  := QuotationOfEq E <+ QuotationOfIsEqOrig E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfDecidableTypeBoth (E : DecidableTypeBoth) <: QuotationOfDecidableType E <: QuotationOfDecidableTypeOrig E
  := QuotationOfEqualityTypeBoth E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfBooleanEqualityType (E : BooleanEqualityType) <: QuotationOfEqualityType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfBooleanDecidableType (E : BooleanDecidableType) <: QuotationOfDecidableType E <: QuotationOfBooleanEqualityType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfHasEqDec E E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfDecidableTypeFull (E : DecidableTypeFull) <: QuotationOfDecidableTypeBoth E <: QuotationOfBooleanDecidableType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfIsEqOrig E E <+ QuotationOfHasEqDec E E <+ QuotationOfHasEqBool E E.

Module Type BackportEqSig (E : Eq) (F : IsEq E) := Nop <+ BackportEq E F.

Module QuotationOfBackportEq (E : Eq) (F : IsEq E) (Import E' : BackportEqSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfIsEq E F) <: QuotationOfIsEqOrig E E'.
  #[export] Instance qeq_refl : quotation_of eq_refl := ltac:(cbv [eq_refl]; exact _).
  #[export] Instance qeq_sym : quotation_of eq_sym := ltac:(cbv [eq_sym]; exact _).
  #[export] Instance qeq_trans : quotation_of eq_trans := ltac:(cbv [eq_trans]; exact _).
End QuotationOfBackportEq.

Module Type UpdateEqSig (E : Eq) (F : IsEqOrig E) := Nop <+ UpdateEq E F.

Module QuotationOfUpdateEq (E : Eq) (F : IsEqOrig E) (Import E' : UpdateEqSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfIsEqOrig E F) <: QuotationOfIsEq E E'.
  #[export] Instance qeq_equiv : quotation_of E'.eq_equiv := ltac:(change (quotation_of (Build_Equivalence _ F.eq_refl F.eq_sym F.eq_trans)); exact _).
End QuotationOfUpdateEq.

Module Type Backport_ETSig (E:EqualityType) := Nop <+ Backport_ET E.
Module Type Update_ETSig (E:EqualityTypeOrig) := Nop <+ Update_ET E.
Module Type Backport_DTSig (E:DecidableType) := Nop <+ Backport_DT E.
Module Type Update_DTSig (E:DecidableTypeOrig) := Nop <+ Update_DT E.

Module QuotationOfBackport_ET (E : EqualityType) (E' : Backport_ETSig E) (qE : QuotationOfEqualityType E) <: QuotationOfEqualityTypeBoth E'
  := qE <+ QuotationOfBackportEq E E E'.

Module QuotationOfUpdate_ET (E : EqualityTypeOrig) (E' : Update_ETSig E) (qE : QuotationOfEqualityTypeOrig E) <: QuotationOfEqualityTypeBoth E'
  := qE <+ QuotationOfUpdateEq E E E'.

Module QuotationOfBackport_DT (E : DecidableType) (E' : Backport_DTSig E) (qE : QuotationOfDecidableType E) <: QuotationOfDecidableTypeBoth E'
  := qE <+ QuotationOfBackportEq E E E'.

Module QuotationOfUpdate_DT (E : DecidableTypeOrig) (E' : Update_DTSig E) (qE : QuotationOfDecidableTypeOrig E) <: QuotationOfDecidableTypeBoth E'
  := qE <+ QuotationOfUpdateEq E E E'.

Module Type HasEqDec2BoolSig (E : Eq) (F : HasEqDec E) <: HasEqBool E := Nop <+ HasEqDec2Bool E F.

Module QuotationOfHasEqDec2Bool (E : Eq) (F : HasEqDec E) (Import E' : HasEqDec2BoolSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfHasEqDec E F) <: QuotationOfHasEqBool E E'.
  #[export] Instance qeqb : quotation_of eqb := ltac:(cbv [eqb]; exact _).
  #[export] Instance qeqb_eq : quotation_of eqb_eq := ltac:(unfold_quotation_of (); exact _).
End QuotationOfHasEqDec2Bool.

Module Type HasEqBool2DecSig (E : Eq) (F : HasEqBool E) <: HasEqDec E := Nop <+ HasEqBool2Dec E F.

Module QuotationOfHasEqBool2Dec (E : Eq) (F : HasEqBool E) (Import E' : HasEqBool2DecSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfHasEqBool E F) <: QuotationOfHasEqDec E E'.
  #[export] Instance qeq_dec : quotation_of eq_dec := ltac:(cbv [eq_dec]; exact _).
End QuotationOfHasEqBool2Dec.

Module Type Dec2BoolSig (E : DecidableType) <: BooleanDecidableType := Nop <+ Dec2Bool E.
Module Type Bool2DecSig (E : BooleanEqualityType) <: BooleanDecidableType := Nop <+ Bool2Dec E.

Module QuotationOfDec2Bool (E : DecidableType) (E' : Dec2BoolSig E) (qE : QuotationOfDecidableType E) <: QuotationOfBooleanDecidableType E'
  := qE <+ QuotationOfHasEqDec2Bool E E E'.

Module QuotationOfBool2Dec (E : BooleanEqualityType) (E' : Bool2DecSig E) (qE : QuotationOfBooleanEqualityType E) <: QuotationOfBooleanDecidableType E'
  := qE <+ QuotationOfHasEqBool2Dec E E E'.

Module Type BoolEqualityFactsSig (E : BooleanEqualityType) := Nop <+ BoolEqualityFacts E.

Module Type QuotationOfBoolEqualityFacts (Import E : BooleanEqualityType) (Import F : BoolEqualityFactsSig E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfBoolEqualityFacts.

Module QuotationOfHasUsualEq (Import T : Typ) (Import E : HasUsualEq T) (Import qT : QuotationOfTyp T) <: QuotationOfHasEq T E.
  #[export] Instance qeq : quotation_of E.eq := ltac:(cbv [E.eq]; exact _).
End QuotationOfHasUsualEq.

Module Type QuotationOfUsualEq (E : UsualEq) <: QuotationOfEq E := QuotationOfTyp E <+ QuotationOfHasUsualEq E E.

Module QuotationOfUsualIsEq (E : UsualEq) (Import E' : UsualIsEq E) (Import qE : QuotationOfTyp E) <: QuotationOfIsEq E E'.
  #[export] Instance qeq_equiv : quotation_of eq_equiv := ltac:(cbv [eq_equiv]; exact _).
End QuotationOfUsualIsEq.

Module QuotationOfUsualIsEqOrig (E : UsualEq) (Import E' : UsualIsEqOrig E) (Import qE : QuotationOfTyp E) <: QuotationOfIsEqOrig E E'.
  #[export] Instance qeq_refl : quotation_of eq_refl := ltac:(cbv [eq_refl]; exact _).
  #[export] Instance qeq_sym : quotation_of eq_sym := ltac:(cbv [eq_sym]; exact _).
  #[export] Instance qeq_trans : quotation_of eq_trans := ltac:(cbv [eq_trans]; exact _).
End QuotationOfUsualIsEqOrig.

Module Type QuotationOfUsualEqualityType (E : UsualEqualityType) <: QuotationOfEqualityType E
    := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E.

Module Type QuotationOfUsualDecidableType (E : UsualDecidableType) <: QuotationOfDecidableType E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfUsualDecidableTypeOrig (E : UsualDecidableTypeOrig) <: QuotationOfDecidableTypeOrig E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEqOrig E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfUsualDecidableTypeBoth (E : UsualDecidableTypeBoth) <: QuotationOfDecidableTypeBoth E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E <+ QuotationOfUsualIsEqOrig E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfUsualBoolEq (E : UsualBoolEq) := QuotationOfUsualEq E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfUsualDecidableTypeFull (E : UsualDecidableTypeFull) <: QuotationOfDecidableTypeFull E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E <+ QuotationOfUsualIsEqOrig E E <+ QuotationOfHasEqDec E E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfMiniDecidableType (Import M : MiniDecidableType).
  Include QuotationOfTyp M.
  #[export] Declare Instance qeq_dec : quotation_of eq_dec.
End QuotationOfMiniDecidableType.

Module Type Make_UDTSig (M : MiniDecidableType) <: UsualDecidableTypeBoth := Nop <+ Make_UDT M.
Module Type Make_UDTFSig (M : UsualBoolEq) <: UsualDecidableTypeFull := Nop <+ Make_UDTF M.

Module QuotationOfMake_UDT (M : MiniDecidableType) (M' : Make_UDTSig M) (qM : QuotationOfMiniDecidableType M) <: QuotationOfUsualDecidableTypeBoth M'
  := qM <+ QuotationOfHasUsualEq M' M' <+ QuotationOfUsualIsEq M' M' <+ QuotationOfUsualIsEqOrig M' M'.

Module QuotationOfMake_UDTF (M : UsualBoolEq) (M' : Make_UDTFSig M) (qM : QuotationOfUsualBoolEq M) <: QuotationOfUsualDecidableTypeFull M'
  := qM <+ QuotationOfUsualIsEq M M' <+ QuotationOfUsualIsEqOrig M' M' <+ QuotationOfHasEqBool2Dec M' M' M'.
