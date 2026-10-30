From Stdlib.MSets Require Import MSetInterface.
From MetaRocq.Quotation.ToPCUIC Require Import Init.

Module Type QuotationOfWSetsOn (E : DecidableType) (Import W : WSetsOn E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "W").
End QuotationOfWSetsOn.
Module Type QuotationOfWSets (W : WSets) := QuotationOfWSetsOn W.E W.
Module Type QuotationOfSetsOn (E : OrderedType) (Import M : SetsOn E).
  Include QuotationOfWSetsOn E M.
  #[export] Declare Instance qcompare : quotation_of M.compare.
  #[export] Declare Instance qmin_elt : quotation_of M.min_elt.
  #[export] Declare Instance qmax_elt : quotation_of M.max_elt.
  #[export] Declare Instance qcompare_spec : quotation_of M.compare_spec.
  #[export] Declare Instance qelements_spec2 : quotation_of M.elements_spec2.
  #[export] Declare Instance qmin_elt_spec1 : quotation_of M.min_elt_spec1.
  #[export] Declare Instance qmin_elt_spec2 : quotation_of M.min_elt_spec2.
  #[export] Declare Instance qmin_elt_spec3 : quotation_of M.min_elt_spec3.
  #[export] Declare Instance qmax_elt_spec1 : quotation_of M.max_elt_spec1.
  #[export] Declare Instance qmax_elt_spec2 : quotation_of M.max_elt_spec2.
  #[export] Declare Instance qmax_elt_spec3 : quotation_of M.max_elt_spec3.
  #[export] Declare Instance qchoose_spec3 : quotation_of M.choose_spec3.
End QuotationOfSetsOn.
Module Type QuotationOfSets (M : Sets) := QuotationOfSetsOn M.E M.
