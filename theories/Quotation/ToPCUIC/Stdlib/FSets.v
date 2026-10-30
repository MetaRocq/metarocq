From Stdlib Require Import Structures.Equalities Structures.OrdersAlt FMapInterface FMapList FMapAVL FMapFullAVL FMapFacts.
From MetaRocq.Utils Require Import MRUtils MRFSets.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Numbers Stdlib.Init Stdlib.Lists.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import OrdersAlt.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.FSets Require Import FMapInterface.Sig FMapFacts.Sig FMapAVL.Sig FMapList.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MRFSets.Sig.

#[export] Hint Unfold Int.Z_as_Int.t : quotation.

Module QuoteWSfun (E : DecidableTypeOrig) (Import W : WSfun E) (Import WFacts : WFacts_funSig E W) (Import WFactsExtra : WFactsExtra_funSig E W WFacts) (qE : QuotationOfDecidableTypeOrig E) (qW : QuotationOfWSfun E W) (qWFacts : QuotationOfWFacts_fun E W WFacts) (qWFactsExtra : QuotationOfWFactsExtra_fun E W WFacts WFactsExtra).
  Import (hints) qE qW qWFacts qWFactsExtra.
  #[export] Hint Unfold Int.Z_as_Int.t : quotation.

  Section with_quote.
    Context {elt : Type}
            {qelt : quotation_of elt}.

    #[export] Instance quote_MapsTo {x y z} {qx : quotation_of x} {qy : quotation_of y} {qz : quotation_of z} : ground_quotable (@MapsTo elt x y z)
      := ground_quotable_of_iff (iff_sym (@find_mapsto_iff _ _ _ _)).
    #[export] Instance quote_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (@In elt k m)
      := ground_quotable_of_iff (iff_sym (@mem_in_iff _ _ _)).
    #[export] Instance quote_neg_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (~@In elt k m)
      := quote_neg_of_iff (iff_sym (@mem_in_iff _ _ _)).

    #[export] Instance quote_Empty {m} {qm : quotation_of m} : ground_quotable (@Empty elt m)
      := ground_quotable_of_iff (iff_sym (@is_empty_iff _ _)).
    #[export] Instance quote_neg_Empty {m} {qm : quotation_of m} : ground_quotable (~@Empty elt m)
      := quote_neg_of_iff (iff_sym (@is_empty_iff _ _)).

    Import StrongerInstances.
    #[export] Instance quote_Equiv_alt {eq_elt} {m m'} {qeq_elt : quotation_of eq_elt} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} {qm : quotation_of m} {qm' : quotation_of m'} : ground_quotable (@Equiv_alt elt eq_elt m m') := ltac:(cbv [Equiv_alt]; exact _).

    #[export] Instance quote_Equiv {eq_elt m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qeq_elt : quotation_of eq_elt} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} : ground_quotable (@Equiv elt eq_elt m m') := ground_quotable_of_iff Equiv_alt_iff.

    #[export] Instance quote_Equal {m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} : ground_quotable (@Equal elt m m') := ground_quotable_of_iff (iff_sym (@Equal_Equiv elt m m')).

    #[export] Instance quote_Equivb {cmp m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qcmp : quotation_of cmp} : ground_quotable (@Equivb elt cmp m m') := ltac:(cbv [Equivb Cmp]; exact _).
  End with_quote.

  #[export] Existing Instances
    quote_MapsTo
    quote_In
    quote_neg_In
    quote_Empty
    quote_neg_Empty
    quote_Equiv_alt
    quote_Equiv
    quote_Equal
    quote_Equivb
  .
  #[export] Typeclasses Opaque
    In
    Empty
    Equiv_alt
    Equiv
    Equal
    Equivb
  .
End QuoteWSfun.

Module QuoteFMapAVL (T : OrderedTypeOrig) (M : FMapAVL.MakeSig T) (Import WFacts : WFacts_funSig T M) (Import WFactsExtra : WFactsExtra_funSig T M WFacts) (Import MDecide : FMapAVL.DecideSig T M) (qT : QuotationOfOrderedTypeOrig T) (qM : FMapAVL.QuotationOfMake T M) (qWFacts : QuotationOfWFacts_fun T M WFacts) (qWFactsExtra : QuotationOfWFactsExtra_fun T M WFacts WFactsExtra) (qMDecide : FMapAVL.QuotationOfDecide T M MDecide).
  Import (hints) qT qM qWFacts qWFactsExtra qMDecide.
  Include QuoteWSfun T M WFacts WFactsExtra qT qM qWFacts qWFactsExtra.

  Module Raw.
    Section with_t.
      Context {elt : Type}
              {qelt : quotation_of elt}
              {quote_elt : ground_quotable elt} {quote_T_t : ground_quotable T.t}.

      #[local] Hint Unfold M.Raw.key : quotation.
      #[export] Instance quote_tree : ground_quotable (M.Raw.tree elt) := (ltac:(induction 1; exact _)).
      #[export] Instance quote_bst t : ground_quotable (M.Raw.bst t)
        := ground_quotable_of_dec (@Raw.bst_dec elt t).
    End with_t.
    #[export] Hint Unfold M.Raw.key : quotation.
    #[export] Existing Instances
      quote_tree
      quote_bst
    .
  End Raw.
  Export (hints) Raw.

  #[export] Hint Unfold M.t : quotation.
  #[export] Typeclasses Transparent M.t.
  #[export] Instance quote_bst
    {elt : Type}
    {qelt : quotation_of elt}
    {quote_elt : ground_quotable elt} {quote_T_t : ground_quotable T.t}
    : ground_quotable (M.bst elt) := (ltac:(induction 1; exact _)).
End QuoteFMapAVL.
