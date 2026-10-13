From Stdlib Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaRocq.Utils Require Import MRMSets.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Numbers Stdlib.Init Stdlib.Lists.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetInterface.Sig MSetProperties.Sig MSetAVL.Sig MSetList.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MRMSets.Sig.

#[export] Hint Unfold Int.Z_as_Int.t : quotation.

Module QuoteWSetsOn (E : DecidableType) (Import W : WSetsOn E) (WProperties : WPropertiesOnSig E W) (Import WExtraProperties : WExtraPropertiesOnSig E W WProperties) (qE : QuotationOfDecidableType E) (qW : QuotationOfWSetsOn E W) (qWProperties : QuotationOfWPropertiesOnT E W WProperties) (qWExtraProperties : QuotationOfWExtraPropertiesOn E W WProperties WExtraProperties).
  Import (hints) qE qW qWProperties qWExtraProperties.

  #[export] Hint Unfold Int.Z_as_Int.t : quotation.

  #[export] Instance quote_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (In x y)
    := ground_quotable_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_neg_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~In x y)
    := ground_quotable_neg_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_Equal {x y} {qx : quotation_of x} {qy : quotation_of y}  : ground_quotable (Equal x y)
    := ground_quotable_of_dec (eq_dec x y).
  #[export] Typeclasses Opaque Equal.
  #[export] Instance quote_neg_Equal {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Equal x y)
    := ground_quotable_neg_of_dec (eq_dec x y).
  #[export] Instance quote_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (Subset x y) := ground_quotable_of_iff (@subset_spec x y).
  #[export] Typeclasses Opaque Subset.
  #[export] Instance quote_neg_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Subset x y) := quote_neg_of_iff (@subset_spec x y).
  #[export] Instance quote_Empty {x} {qx : quotation_of x} : ground_quotable (Empty x) := ground_quotable_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Typeclasses Opaque Empty.
  #[export] Instance quote_neg_Empty {x} {qx : quotation_of x} : ground_quotable (~Empty x) := quote_neg_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Instance quote_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (WProperties.Add x s s')
    := ground_quotable_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).
  #[export] Instance quote_neg_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (~WProperties.Add x s s')
    := quote_neg_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).
  #[export] Typeclasses Transparent elt.
  #[export] Hint Unfold For_all_alt : quotation.
  Definition quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (For_all P s)
    := ground_quotable_of_iff For_all_alt_iff.
  #[export] Typeclasses Opaque For_all.
  #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_For_all : ground_quotable (For_all (fun v1 => For_all (P v1) s) s)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2)
    := ground_quotable_of_iff For_all_forall2_iff.

  Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (Exists P s)
    := ground_quotable_of_dec (Exists_dec P_dec).
  #[export] Typeclasses Opaque Exists.

  #[export] Hint Extern 13 (ground_quotable (For_all _ _))
  => simple notypeclasses refine (@quote_For_all _ _ _ _ _ _ _ _) : typeclass_instances.

  #[export] Typeclasses Transparent W.elt.
End QuoteWSetsOn.

Module Type QuoteWSetsOnSig (E : DecidableType) (W : WSetsOn E) (WProperties : WPropertiesOnSig E W) (WExtraProperties : WExtraPropertiesOnSig E W WProperties) (qE : QuotationOfDecidableType E) (qW : QuotationOfWSetsOn E W) (qWProperties : QuotationOfWPropertiesOnT E W WProperties) (qWExtraProperties : QuotationOfWExtraPropertiesOn E W WProperties WExtraProperties) := Nop <+ QuoteWSetsOn E W WProperties WExtraProperties qE qW qWProperties qWExtraProperties.

Module QuoteOrdProperties (Import M : Sets) (Import MOrdProperties : OrdPropertiesSig M) (Import MExtraOrdProperties : ExtraOrdPropertiesSig M MOrdProperties) (qE : QuotationOfOrderedType M.E) (qM : QuotationOfSets M) (qMOrdProperties : QuotationOfOrdPropertiesT M MOrdProperties) (qMExtraOrdProperties : QuotationOfExtraOrdProperties M MOrdProperties MExtraOrdProperties).
  Import (hints) qE qM qMOrdProperties qMExtraOrdProperties.

  #[export] Instance quote_Above {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Above x s)
    := ground_quotable_of_iff (above_spec x s).
  #[export] Typeclasses Opaque Above.
  #[export] Instance quote_Below {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Below x s)
    := ground_quotable_of_iff (below_spec x s).
  #[export] Typeclasses Opaque Below.
End QuoteOrdProperties.

Module QuoteSets (Import M : Sets) (Import MOrdProperties : OrdPropertiesSig M) (Import MExtraOrdProperties : ExtraOrdPropertiesSig M MOrdProperties) (qE : QuotationOfOrderedType M.E) (qM : QuotationOfSets M) (qMOrdProperties : QuotationOfOrdPropertiesT M MOrdProperties) (qMExtraOrdProperties : QuotationOfExtraOrdProperties M MOrdProperties MExtraOrdProperties).
  Include QuoteWSetsOn M.E M MOrdProperties.P MExtraOrdProperties.P qE qM qMOrdProperties.qP qMExtraOrdProperties.qP.
  Include QuoteOrdProperties M MOrdProperties MExtraOrdProperties qE qM qMOrdProperties qMExtraOrdProperties.
End QuoteSets.

Module QuoteMSetAVL (T : OrderedType) (M : MSetAVL.MakeSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import MExtraOrdProperties : ExtraOrdPropertiesSig M MOrdProperties) (Import MDecide : MSetAVL.DecideSig T M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetAVL.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdPropertiesT M MOrdProperties) (qMExtraOrdProperties : QuotationOfExtraOrdProperties M MOrdProperties MExtraOrdProperties) (qMDecide : MSetAVL.QuotationOfDecide T M MDecide).
  Import (hints) qT qM qMOrdProperties qMExtraOrdProperties qMDecide.
  Include QuoteSets M MOrdProperties MExtraOrdProperties qT qM qMOrdProperties qMExtraOrdProperties.

  Module Raw.
    Import MDecide.Raw.
    Section with_t.
      Context {quote_T_t : ground_quotable T.t}.

      #[export] Instance quote_tree : ground_quotable M.Raw.tree := (ltac:(induction 1; exact _)).
      #[export] Instance quote_bst t : ground_quotable (M.Raw.bst t)
        := ground_quotable_of_dec (@bst_dec t).
      #[export] Instance quote_Ok s : ground_quotable (M.Raw.Ok s) := (ltac:(cbv [M.Raw.Ok]; exact _)).
    End with_t.
    #[export] Hint Unfold M.Raw.t : quotation.
    #[export] Existing Instances
      quote_tree
      quote_bst
      quote_Ok
    .
  End Raw.
  Export (hints) Raw.

  #[export] Instance quote_t_ {quote_T_t : ground_quotable T.t} : ground_quotable M.t_ := ltac:(induction 1; exact _).
  #[export] Hint Unfold M.t : quotation.
  #[export] Typeclasses Transparent M.t.
End QuoteMSetAVL.

Module QuoteWSetsOnIsUsual (E : UsualDecidableType) (Import M : WSetsOn E) (MProperties : WPropertiesOnSig E M) (MExtraProperties : WExtraPropertiesOnSig E M MProperties) (qE : QuotationOfUsualDecidableType E) (qM : QuotationOfWSetsOn E M) (qMProperties : QuotationOfWPropertiesOnT E M MProperties) (qMExtraProperties : QuotationOfWExtraPropertiesOn E M MProperties MExtraProperties) (Import QuoteM : QuoteWSetsOnSig E M MProperties MExtraProperties qE qM qMProperties qMExtraProperties).

  Import (hints) qE qM qMProperties qMExtraProperties.

  #[export] Instance quote_For_all_usual {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := quote_For_all.
  Definition quote_Exists_dec_usual {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In_usual {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
End QuoteWSetsOnIsUsual.

Module QuoteUsualWSetsOn (E : UsualDecidableType) (M : WSetsOn E) (MProperties : WPropertiesOnSig E M) (MExtraProperties : WExtraPropertiesOnSig E M MProperties) (qE : QuotationOfUsualDecidableType E) (qM : QuotationOfWSetsOn E M) (qMProperties : QuotationOfWPropertiesOnT E M MProperties) (qMExtraProperties : QuotationOfWExtraPropertiesOn E M MProperties MExtraProperties)
  := QuoteWSetsOn E M MProperties MExtraProperties qE qM qMProperties qMExtraProperties <+ QuoteWSetsOnIsUsual E M MProperties MExtraProperties qE qM qMProperties qMExtraProperties.

Module QuoteUsualSets (M : UsualSets) (MProperties : OrdPropertiesSig M) (MExtraProperties : ExtraOrdPropertiesSig M MProperties) (qE : QuotationOfUsualOrderedType M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdPropertiesT M MProperties) (qMExtraProperties : QuotationOfExtraOrdProperties M MProperties MExtraProperties)
  := QuoteSets M MProperties MExtraProperties qE qM qMProperties qMExtraProperties <+ QuoteWSetsOnIsUsual M.E M MProperties.P MExtraProperties.P qE qM qMProperties.qP qMExtraProperties.qP.

Module QuoteWSetsOnIsLeibniz (E : OrderedTypeWithLeibniz) (Import M : WSetsOn E) (MProperties : WPropertiesOnSig E M) (MExtraProperties : WExtraPropertiesOnSig E M MProperties) (qE : QuotationOfOrderedTypeWithLeibniz E) (qM : QuotationOfWSetsOn E M) (qMProperties : QuotationOfWPropertiesOnT E M MProperties) (qMExtraProperties : QuotationOfWExtraPropertiesOn E M MProperties MExtraProperties) (Import QuoteM : QuoteWSetsOnSig E M MProperties MExtraProperties qE qM qMProperties qMExtraProperties).
  Import (hints) qE qM qMProperties qMExtraProperties.

  #[local] Instance all_P_Proper {P : E.t -> Prop} : Proper (E.eq ==> Basics.impl) P.
  Proof.
    intros ?? H.
    apply E.eq_leibniz in H; subst; exact id.
  Defined.
  #[local] Instance qall_P_Proper : quotation_of (@all_P_Proper) := ltac:(unfold_quotation_of (); exact _).

  #[export] Instance quote_For_all_leibniz {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := quote_For_all.
  Definition quote_Exists_dec_leibniz {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In_leibniz {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
End QuoteWSetsOnIsLeibniz.

Module QuoteSWithLeibniz (M : SWithLeibniz) (MProperties : OrdPropertiesSig M) (MExtraProperties : ExtraOrdPropertiesSig M MProperties) (qE : QuotationOfOrderedTypeWithLeibniz M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdPropertiesT M MProperties) (qMExtraProperties : QuotationOfExtraOrdProperties M MProperties MExtraProperties)
  := QuoteSets M MProperties MExtraProperties qE qM qMProperties qMExtraProperties <+ QuoteWSetsOnIsLeibniz M.E M MProperties.P MExtraProperties.P qE qM qMProperties.qP qMExtraProperties.qP.

Module QuoteMSetIsList (T : OrderedType) (Import M : MSetList.MakeSig T) (Import MProperties : WPropertiesOnSig T M) (MExtraProperties : WExtraPropertiesOnSig T M MProperties) (Import qT : QuotationOfOrderedType T) (Import qM : MSetList.QuotationOfMake T M) (qMProperties : QuotationOfWPropertiesOnT T M MProperties) (qMExtraProperties : QuotationOfWExtraPropertiesOn T M MProperties MExtraProperties) (Import QuoteM : QuoteWSetsOnSig T M MProperties MExtraProperties qT qM qMProperties qMExtraProperties).
  Import (hints) qT qM qMProperties qMExtraProperties.

  Module Raw.
    #[export] Instance quote_Ok {v} : ground_quotable (M.Raw.Ok v) := ltac:(cbv [M.Raw.Ok]; exact _).
    #[export] Hint Unfold M.Raw.t M.Raw.elt : quotation.
  End Raw.
  Export (hints) Raw.
  #[export] Instance quote_t_ {quoteE_t : ground_quotable E.t} : ground_quotable t_ := ltac:(destruct 1; exact _).
  #[export] Hint Unfold M.t M.elt : quotation.
  #[export] Typeclasses Transparent M.t M.elt.
End QuoteMSetIsList.

Module QuoteMSetList (T : OrderedType) (M : MSetList.MakeSig T) (MProperties : OrdPropertiesSig M) (MExtraProperties : ExtraOrdPropertiesSig M MProperties) (qT : QuotationOfOrderedType T) (qM : MSetList.QuotationOfMake T M) (qMProperties : QuotationOfOrdPropertiesT M MProperties) (qMExtraProperties : QuotationOfExtraOrdProperties M MProperties MExtraProperties)
  := QuoteSets M MProperties MExtraProperties qT qM qMProperties qMExtraProperties <+ QuoteMSetIsList T M MProperties.P MExtraProperties.P qT qM qMProperties.qP qMExtraProperties.qP.

Module QuoteMSetListWithLeibniz (T : OrderedTypeWithLeibniz) (M : MSetList.MakeWithLeibnizSig T) (MProperties : OrdPropertiesSig M) (MExtraProperties : ExtraOrdPropertiesSig M MProperties) (qT : QuotationOfOrderedTypeWithLeibniz T) (qM : MSetList.QuotationOfMakeWithLeibniz T M) (qMProperties : QuotationOfOrdPropertiesT M MProperties) (qMExtraProperties : QuotationOfExtraOrdProperties M MProperties MExtraProperties)
  := QuoteMSetList T M MProperties MExtraProperties qT qM qMProperties qMExtraProperties <+ QuoteWSetsOnIsLeibniz M.E M MProperties.P MExtraProperties.P qT qM qMProperties.qP qMExtraProperties.qP.
