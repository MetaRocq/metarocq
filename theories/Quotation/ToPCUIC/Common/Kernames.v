From MetaRocq.Common Require Import Kernames.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Stdlib.MSets Stdlib.FSets bytestring.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import Kernames.Instances.

#[local] Hint Unfold ident qualid dirpath kername : quotation.
#[export] Instance quote_ident : ground_quotable ident := _.
#[export] Instance quote_qualid : ground_quotable qualid := _.
#[export] Instance quote_dirpath : ground_quotable dirpath := _.
#[export] Instance quote_modpath : ground_quotable modpath := ltac:(induction 1; exact _).
#[export] Instance quote_kername : ground_quotable kername := _.

Module QuoteKernameSet := MSets.QuoteMSetAVL Kername KernameSet KernameSetOrdProp KernameSetExtraOrdProp KernameSetExtraDecide qKername qKernameSet qKernameSetOrdProp qKernameSetExtraOrdProp qKernameSetExtraDecide.
Export (hints) QuoteKernameSet.
Module QuoteKernameMap := FSets.QuoteFMapAVL Kername.OT KernameMap KernameMapFact.F KernameMapExtraFact KernameMapDecide qKername.qOT qKernameMap qKernameMapFact.qF qKernameMapExtraFact qKernameMapDecide.
Export (hints) QuoteKernameMap.

#[export] Instance quote_inductive : ground_quotable inductive := ltac:(destruct 1; exact _).
#[export] Instance quote_projection : ground_quotable projection := ltac:(destruct 1; exact _).
#[export] Instance quote_global_reference : ground_quotable global_reference := ltac:(destruct 1; exact _).
