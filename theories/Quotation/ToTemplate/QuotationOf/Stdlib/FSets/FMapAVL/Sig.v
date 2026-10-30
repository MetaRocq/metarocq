From Stdlib.FSets Require Import FMapAVL.
From Stdlib.Structures Require Import Equalities OrdersAlt.
From MetaRocq.Utils Require Import MRFSets.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import OrdersAlt.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.FSets Require Import FMapList.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module FMapAVL.
  Module Type QuotationOfMake (T : OrderedTypeOrig) (M : FMapAVL.MakeSig T).
    Module qRaw.
      Module qProofs.
        Module qMX := Nop <+ QuotationOfOrderedTypeOrigFacts T M.Raw.Proofs.MX.
        Module qPX := Nop <+ QuotationOfKeyOrderedTypeOrig T M.Raw.Proofs.PX.
        Module qL := Nop <+ FMapList.QuotationOfRaw T M.Raw.Proofs.L.
        Export (hints) qMX qPX qL.
        MetaRocq Run (tmDeclareQuotationOfModule (all_submodules_except [["MX"]; ["PX"]; ["L"]]%bs) (Some export) "M.Raw.Proofs").
      End qProofs.
      Export (hints) qProofs.
      MetaRocq Run (tmDeclareQuotationOfModule (all_submodules_except [["Proofs"]]%bs) (Some export) "M.Raw").
    End qRaw.
    Export (hints) qRaw.
    MetaRocq Run (tmDeclareQuotationOfModule (all_submodules_except [["Raw"]]%bs) (Some export) "M").
  End QuotationOfMake.
End FMapAVL.
