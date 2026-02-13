From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MRMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qUnivConstraintSetExtraOrdProp <: QuotationOfExtraOrdProperties UnivConstraintSet UnivConstraintSetOrdProp UnivConstraintSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn UnivConstraintSet.E UnivConstraintSet UnivConstraintSetOrdProp.P UnivConstraintSetExtraOrdProp.P.
    MetaRocq Run (tmMakeQuotationOfModule everything None "UnivConstraintSetExtraOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "UnivConstraintSetExtraOrdProp").
End qUnivConstraintSetExtraOrdProp.
