From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qConstraintSetOrdProp <: QuotationOfOrdProperties ConstraintSet ConstraintSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts UnivConstraintSet.E ConstraintSetOrdProp.ME.
    MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties ConstraintSet ConstraintSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn UnivConstraint ConstraintSet ConstraintSetOrdProp.P.Dec.
      MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn UnivConstraint ConstraintSet ConstraintSetOrdProp.P.FM.
      MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.P.FM").
    End qFM.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "ConstraintSetOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "ConstraintSetOrdProp").
End qConstraintSetOrdProp.
