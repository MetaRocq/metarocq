From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.Stdlib Require Import (hints) Init MSets Numbers.
From MetaRocq.Quotation.ToTemplate.Utils Require Import (hints) MROption bytestring.
From MetaRocq.Quotation.ToTemplate.Common Require Import (hints) BasicAst config.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Universes.Instances.
From MetaRocq.Common Require Import Kernames Universes UniversesDec.

(* Grrr, [valuation]s cause so much trouble, because they're not quotable *)
(*
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.
Class Evaluable (A : Type) := val : valuation -> A -> nat.
 *)

Module QuoteLevelSet := MSets.QuoteMSetAVL Level LevelSet LevelSetOrdProp LevelSetExtraOrdProp LevelSetExtraDecide qLevel qLevelSet qLevelSetOrdProp qLevelSetExtraOrdProp qLevelSetExtraDecide.
Export (hints) QuoteLevelSet.
Module QuoteLevelExprSet := MSets.QuoteMSetListWithLeibniz LevelExpr LevelExprSet LevelExprSetOrdProp LevelExprSetExtraOrdProp qLevelExpr qLevelExprSet qLevelExprSetOrdProp qLevelExprSetExtraOrdProp.
Export (hints) QuoteLevelExprSet.
Module QuoteUnivConstraintSet := MSets.QuoteMSetAVL UnivConstraint UnivConstraintSet UnivConstraintSetOrdProp UnivConstraintSetExtraOrdProp UnivConstraintSetExtraDecide qUnivConstraint qUnivConstraintSet qUnivConstraintSetOrdProp qUnivConstraintSetExtraOrdProp qUnivConstraintSetExtraDecide.
Export (hints) QuoteUnivConstraintSet.

Module QuoteUniverses1.
  Module Import Level.
    #[export] Instance quote_t_ : ground_quotable Level.t_ := ltac:(destruct 1; exact _).
    #[export] Hint Unfold Level.t : quotation.
    #[export] Typeclasses Transparent Level.t.
    #[export] Instance quote_lt_ {x y} : ground_quotable (Level.lt_ x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.
    #[export] Hint Unfold Level.lt : quotation.
  End Level.
  Export (hints) Level.

  Module Import PropLevel.
    #[export] Instance quote_t : ground_quotable PropLevel.t := ltac:(destruct 1; exact _).
    #[export] Instance quote_lt_ {x y} : ground_quotable (PropLevel.lt_ x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.
    #[export] Hint Unfold PropLevel.lt : quotation.
  End PropLevel.
  Export (hints) PropLevel.

  Module Import LevelExpr.
    #[export] Instance quote_t : ground_quotable LevelExpr.t := ltac:(cbv [LevelExpr.t]; exact _).
    #[export] Instance quote_lt_ {x y} : ground_quotable (LevelExpr.lt_ x y)
      := ground_quotable_of_dec (@LevelExprSet.Raw.MX.lt_dec x y).
    #[export] Hint Unfold LevelExpr.lt : quotation.
  End LevelExpr.
  Export (hints) LevelExpr.
End QuoteUniverses1.
Export (hints) QuoteUniverses1.

#[export] Hint Unfold
  LevelInstance.t
  UContext.t
  AUContext.t
  ContextSet.t
  ContextSet.Equal
  ContextSet.Subset
  : quotation.

#[export] Typeclasses Transparent
  LevelInstance.t
  Instance.t
  UContext.t
  AUContext.t
  ContextSet.t
.

Module QuoteUniverses2.
  Module Import Universe.
    #[export] Instance quote_t_ {univ} {quniv : quotation_of univ} {quote_univ : ground_quotable univ} : ground_quotable (Sort.t_ univ) := ltac:(destruct 1; exact _).
    #[export] Hint Unfold sort : quotation.
    #[export] Typeclasses Transparent sort.
    #[local] Hint Constructors or eq : typeclass_instances.
    #[export] Instance quote_on_sort {univ P def s} {quniv : quotation_of univ} {quote_univ : ground_quotable univ} {quoteP : forall l, s = sType l -> ground_quotable (P l : Prop)} {quote_def : s = sProp \/ s = sSProp -> ground_quotable (def : Prop)} : ground_quotable (@Sort.on_sort univ Prop P def s) := ltac:(cbv [Sort.on_sort]; exact _).
  End Universe.
  Export (hints) Universe.

  Module Import ConstraintType.
    #[export] Instance quote_t_ : ground_quotable UnivConstraintType.ConstraintType.t_ := ltac:(destruct 1; exact _).
    #[export] Hint Unfold UnivConstraintType.ConstraintType.t : quotation.
    #[export] Typeclasses Transparent UnivConstraintType.ConstraintType.t.
  End ConstraintType.
  Export (hints) ConstraintType.

  Module Import UnivConstraint.
    #[export] Hint Unfold UnivConstraint.t : quotation.
    #[export] Typeclasses Transparent UnivConstraint.t.
  End UnivConstraint.
  Export (hints) UnivConstraint.

  Module Import Variance.
    #[export] Instance quote_t : ground_quotable Variance.t := ltac:(destruct 1; exact _).
  End Variance.
  Export (hints) Variance.
End QuoteUniverses2.
Export (hints) QuoteUniverses2.

#[export] Instance quote_Universe_NES : ground_quotable Universe.NES.t := ltac:(destruct 1; exact _).
#[export] Instance quote_Universe : ground_quotable Universe.t := ltac:(destruct 1; exact _).

#[export] Instance quote_concrete_sort : ground_quotable concrete_sort := ltac:(destruct 1; exact _).
Import StrongerInstances.

#[export] Instance quote_allowed_eliminations : ground_quotable allowed_eliminations := ltac:(destruct 1; exact _).

#[export] Instance quote_declared_cstr_levels {levels cstr} : ground_quotable (declared_univ_cstr_levels levels cstr) := ltac:(cbv [declared_univ_cstr_levels]; exact _).
#[export] Instance quote_universes_decl : ground_quotable universes_decl := ltac:(destruct 1; exact _).
(* #[export] Instance quote_satisfies0 {v s} {qv : quotation_of v} : ground_quotable (@satisfies0 v s) *)
  (* := ground_quotable_of_iff (iff_sym (@uGraph.gc_of_constraint_spec config.default_checker_flags v s)). *)
#[export] Instance quote_satisfies {v s} {qv : quotation_of v} : ground_quotable (@satisfies v s)
  := ground_quotable_of_dec (@uGraph.satisfies_dec config.default_checker_flags s v).
#[export] Instance quote_consistent {ctrs} : ground_quotable (@consistent ctrs)
  := ground_quotable_of_dec (@consistent_dec ctrs).
(* #[export] Instance quote_consistent_extension_on {cs cstr} : ground_quotable (@consistent_extension_on cs cstr) *)
  (* := ground_quotable_of_dec (@consistent_extension_on_dec cs cstr). *)
#[export] Instance quote_leq_universe {cf ϕ u u'} : ground_quotable (@leq_universe cf ϕ u u')
  := ground_quotable_of_dec (@leq_universe_dec cf ϕ u u').
#[export] Instance quote_leq_sort_ {cf univ leq_universe s s'} {quote_leq_universe : forall u u', ground_quotable (leq_universe u u':Prop)} : ground_quotable (@leq_sort_ cf univ leq_universe s s') := ltac:(cbv [leq_sort_]; exact _).
#[export] Instance quote_leq_csort_ {cf s s'} : ground_quotable (@leq_csort cf s s') := @quote_leq_sort_ cf nat _ s s' _.
#[export] Instance quote_leq_sort {cf ϕ s s'} : ground_quotable (@leq_sort cf ϕ s s') := ltac:(cbv [leq_sort]; exact _).
#[export] Instance quote_eq_universe {cf ϕ u u'} : ground_quotable (@eq_universe cf ϕ u u')
  := ground_quotable_of_dec (@eq_universe_dec cf ϕ u u').
#[export] Instance quote_eq_sort_ {univ eq_universe s s'} {quote_eq_universe : forall u u', ground_quotable (eq_universe u u':Prop)} : ground_quotable (@eq_sort_ univ eq_universe s s') := ltac:(cbv [eq_sort_]; exact _).
#[export] Instance quote_eq_sort {cf ϕ s s'} : ground_quotable (@eq_sort cf ϕ s s') := ltac:(cbv [eq_sort]; exact _).
#[export] Instance quote_compare_universe {cf univ pb u u'} : ground_quotable (@compare_universe cf univ pb u u') := ltac:(destruct pb; cbv [compare_universe]; exact _).
#[export] Instance quote_compare_sort {cf univ pb u u'} : ground_quotable (@compare_sort cf univ pb u u') := ltac:(destruct pb; cbv [compare_sort]; exact _).
#[export] Instance quote_valid_constraints0 {ϕ ctrs} : ground_quotable (@valid_constraints0 ϕ ctrs)
  := ground_quotable_of_dec (@valid_constraints0_dec ϕ ctrs).
#[export] Instance quote_valid_constraints {cf ϕ ctrs} : ground_quotable (@valid_constraints cf ϕ ctrs)
  := ground_quotable_of_dec (@valid_constraints_dec cf ϕ ctrs).
#[export] Instance quote_is_lSet {cf φ s} : ground_quotable (@is_lSet cf φ s) := ltac:(cbv [is_lSet]; exact _).
#[export] Instance quote_is_allowed_elimination {cf ϕ allowed u} : ground_quotable (@is_allowed_elimination cf ϕ allowed u)
  := ground_quotable_of_dec (@is_allowed_elimination_dec cf ϕ allowed u).

#[export] Instance quote_universes_entry : ground_quotable universes_entry := ltac:(destruct 1; exact _).