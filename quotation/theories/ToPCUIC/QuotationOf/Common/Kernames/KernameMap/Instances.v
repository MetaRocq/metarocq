From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Stdlib.FSets Require Import FMapAVL.Sig FMapList.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameMap <: FMapAVL.QuotationOfMake Kername.OT KernameMap.
  Module qRaw.
    Module qProofs.
      Module qMX <: QuotationOfOrderedTypeOrigFactsT Kername.OT KernameMap.Raw.Proofs.MX.
        MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.MX").
      End qMX.
      Module qPX <: QuotationOfKeyOrderedTypeOrigT Kername.OT KernameMap.Raw.Proofs.PX.
        Module qMO <: QuotationOfOrderedTypeOrigFactsT Kername.OT KernameMap.Raw.Proofs.PX.MO.
          MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.PX.MO").
        End qMO.
        MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["MO"]]%bs) None "KernameMap.Raw.Proofs.PX").
      End qPX.
      Module qL <: FMapList.QuotationOfRawT Kername.OT KernameMap.Raw.Proofs.L.
        Module qMX <: QuotationOfOrderedTypeOrigFactsT Kername.OT KernameMap.Raw.Proofs.L.MX.
          MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.L.MX").
        End qMX.
        Module qPX <: QuotationOfKeyOrderedTypeOrigT Kername.OT KernameMap.Raw.Proofs.L.PX.
          Module qMO <: QuotationOfOrderedTypeOrigFactsT Kername.OT KernameMap.Raw.Proofs.L.PX.MO.
            MetaRocq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.L.PX.MO").
          End qMO.
          MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["MO"]]%bs) None "KernameMap.Raw.Proofs.L.PX").
        End qPX.
        MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["MX"]; ["PX"]]%bs) None "KernameMap.Raw.Proofs.L").
      End qL.
      MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["MX"]; ["PX"]; ["L"]]%bs) None "KernameMap.Raw.Proofs").
    End qProofs.
    MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Proofs"]]%bs) None "KernameMap.Raw").
  End qRaw.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["Raw"]]%bs) None "KernameMap").
End qKernameMap.
