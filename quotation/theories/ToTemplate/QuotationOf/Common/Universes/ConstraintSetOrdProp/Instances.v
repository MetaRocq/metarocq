From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qConstraintSetOrdProp <: QuotationOfOrdProperties UnivConstraintSet UnivConstraintSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts UnivConstraintSet.E UnivConstraintSetOrdProp.ME.
    MetaRocq Run (tmMakeQuotationOfModule everything None "UnivConstraintSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaRocq Run (tmMakeQuotationOfModule everything None "UnivConstraintSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties UnivConstraintSet UnivConstraintSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn UnivConstraint UnivConstraintSet UnivConstraintSetOrdProp.P.Dec.
      MetaRocq Run (tmMakeQuotationOfModule everything None "UnivConstraintSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn UnivConstraint UnivConstraintSet UnivConstraintSetOrdProp.P.FM.
      MetaRocq Run (tmMakeQuotationOfModule everything None "UnivConstraintSetOrdProp.P.FM").
    End qFM.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "UnivConstraintSetOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "UnivConstraintSetOrdProp").
End qConstraintSetOrdProp.
