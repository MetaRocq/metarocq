From Stdlib.MSets Require Import MSetProperties.
From MetaRocq.Utils Require Import MRMSets.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import OrdersFacts.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetFacts.Sig MSetDecide.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module Export MSets.
  Module Type QuotationOfWPropertiesOn (E : DecidableType) (M : WSetsOn E) (F : WPropertiesOnSig E M).
    Module qDec := Nop <+ QuotationOfWDecideOn E M F.Dec.
    Module qFM := Nop <+ QuotationOfWFactsOn E M F.FM.
    Export (hints) qDec qFM.
    MetaRocq Run (tmDeclareQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) (Some export) "F").
  End QuotationOfWPropertiesOn.

  Module Type QuotationOfWProperties (M : WSets) (F : WPropertiesSig M) := QuotationOfWPropertiesOn M.E M F.

  Module Type QuotationOfOrdProperties (M : Sets) (F : OrdPropertiesSig M).
    Module qME := Nop <+ QuotationOfOrderedTypeFacts M.E F.ME.
    Module qML. (* OrderedTypeLists(M.E). *)
      MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F.ML").
    End qML.
    Module qP := Nop <+ QuotationOfWProperties M F.P.
    Export (hints) qME qML qP.
    MetaRocq Run (tmDeclareQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) (Some export) "F").
  End QuotationOfOrdProperties.
End MSets.
