From MetaRocq.PCUIC Require Import PCUICAst PCUICEquality.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Stdlib.Lists Stdlib.Numbers Stdlib.Floats.
From MetaRocq.Quotation.ToPCUIC.Utils Require Import (hints) utils All_Forall.
From MetaRocq.Quotation.ToPCUIC.Common Require Import (hints) config Reflect Environment Universes BasicAst Kernames.
From MetaRocq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAst utils.PCUICPrimitive (*PCUICAstUtils*) (*Induction*).

#[export] Instance quote_on_rel {T T'} {R} {f: T -> T'} {x y : T} {qR : quotation_of R} {quoteR : forall x y, ground_quotable (R x y:Prop)}: ground_quotable (MRRelations.on_rel R f x y) := ltac:(cbv [MRRelations.on_rel]; exact _).

#[export] Instance quote_cmp_universe_instance {R u u'} {qR : quotation_of R} {quoteR : forall x y, ground_quotable (R x y:Prop)} : ground_quotable (@cmp_universe_instance R u u') := ltac:(cbv [cmp_universe_instance]; exact _).
Section with_R.
  Context {cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop}
          {qRe : quotation_of cmp_universe}
          {quoteRe : forall pb x y, ground_quotable (cmp_universe pb x y)}.

  #[export] Instance quote_cmp_universe_variance {pb v u u'} : ground_quotable (@cmp_universe_variance cmp_universe pb v u u') := ltac:(cbv [cmp_universe_variance]; exact _).

  #[export] Instance quote_cmp_universe_instance_variance {pb v u u'} : ground_quotable (@cmp_universe_instance_variance cmp_universe pb v u u') := ltac:(cbv [cmp_universe_instance_variance]; exact _).

  #[export] Instance quote_cmp_opt_variance {pb v u u'} (subr : RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb)) : ground_quotable (@cmp_opt_variance cmp_universe pb v u u').
  Proof using cmp_universe qRe quoteRe.
    destruct v; cbv [cmp_opt_variance]; try exact _.
    eapply Stdlib.Init.quote_or_dec; try exact _.
    now apply cmp_opt_variance_var_dec.
  Defined.

  #[export] Instance quote_cmp_global_instance {Σ pb gr napp u u'} (subr : RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb)) : ground_quotable (@cmp_global_instance Σ cmp_universe pb gr napp u u') := ltac:(cbv [cmp_global_instance]; exact _).
End with_R.
#[export] Existing Instances
  quote_cmp_universe_variance
  quote_cmp_universe_instance_variance
  quote_cmp_opt_variance
  quote_cmp_global_instance
.

#[export] Instance quote_compare_decls {d d'} : ground_quotable (@eq_decl_upto_names d d')
  := ltac:(destruct 1; exact _).

#[export] Hint Unfold
  eq_predicate eq_branches eq_branch eq_mfixpoint
  : quotation.
#[export] Typeclasses Transparent
  eq_predicate eq_branches eq_branch eq_mfixpoint
.

#[export] Instance quote_eq_term_upto_univ_napp
 {cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop}
 {cmp_sort : conv_pb -> sort -> sort -> Prop}
 {qRe : quotation_of cmp_universe} {qRle : quotation_of cmp_sort}
 {quoteRe : forall pb x y, ground_quotable (cmp_universe pb x y)} {quoteRle : forall pb x y, ground_quotable (cmp_sort pb x y)}
 {Σ pb napp x y}
 {subr : RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb)}
  : ground_quotable (@eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp x y).
Proof.
  unfold ground_quotable; revert Σ cmp_universe cmp_sort pb napp x y qRe qRle quoteRe quoteRle subr.
  fix quote_eq_term_upto_univ_napp 13; intros.
  lazymatch type of quote_eq_term_upto_univ_napp with
  | forall (x1 : ?X1) (x2 : ?X2) (x3 : ?X3) (x4 : ?X4) (x5 : ?X5) (x6 : ?X6) (x7 : ?X7) (x8 : ?X8) (x9 : ?X9) (x10 : ?X10) (x11 : ?X11) (x12 : ?X12) (t : ?X13), quotation_of t
    => change (forall (x1 : X1) (x2 : X2) (x3 : X3) (x4 : X4) (x5 : X5) (x6 : X6) (x7 : X7) (x8 : X8) (x9 : X9) (x10 : X10) (x11 : X11) (x12 : X12), ground_quotable X13) in quote_eq_term_upto_univ_napp
  end.
  destruct t; replace_quotation_of_goal ().
Defined.

#[export] Instance quote_compare_term {cf pb Σ ϕ x y} : ground_quotable (@compare_term cf Σ ϕ pb x y).
Proof. unshelve eapply quote_eq_term_upto_univ_napp. apply compare_universe_subrel. Defined.
