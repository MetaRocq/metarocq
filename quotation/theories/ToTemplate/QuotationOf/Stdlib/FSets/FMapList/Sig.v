From Stdlib.FSets Require Import FMapList.
From Stdlib.Structures Require Import Equalities OrdersAlt.
From MetaRocq.Utils Require Import MRFSets.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module FMapList.
  Module QuotationOfRaw (T : OrderedTypeOrig) (M : FMapList.RawSig T).
    Module qMX := Nop <+ QuotationOfOrderedTypeOrigFacts T M.MX.
    Module qPX := Nop <+ QuotationOfKeyOrderedTypeOrig T M.PX.
    Export (hints) qMX qPX.
    MetaRocq Run (tmDeclareQuotationOfModule (all_submodules_except [["MX"]; ["PX"]]%bs) (Some export) "M").
  End QuotationOfRaw.
  Module Type QuotationOfRawT (T : OrderedTypeOrig) (M : FMapList.RawSig T).
    Include QuotationOfRaw T M.
  End QuotationOfRawT.
End FMapList.
