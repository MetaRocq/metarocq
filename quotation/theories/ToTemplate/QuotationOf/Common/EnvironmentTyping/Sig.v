From MetaRocq.Common Require Import BasicAst Environment EnvironmentTyping.
From MetaRocq.Quotation.ToTemplate Require Import Init.

Module Type QuotationOfLookup (T : Term) (E : EnvironmentSig T) (L : LookupSig T E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "L").
End QuotationOfLookup.

Module Type QuoteLookupSig (Import T : Term) (Import E : EnvironmentSig T) (Import L : LookupSig T E).
  #[export] Hint Unfold
    consistent_instance_ext
  : quotation.
  #[export] Typeclasses Transparent
    consistent_instance_ext
  .

  #[export] Declare Instance quote_consistent_instance {cf lvs ϕ uctx u} : ground_quotable (@consistent_instance cf lvs ϕ uctx u).
  #[export] Declare Instance quote_wf_sort {Σ s} : ground_quotable (@wf_sort Σ s).
  #[export] Declare Instance quote_declared_constant {Σ id decl} : ground_quotable (@declared_constant Σ id decl).
  #[export] Declare Instance quote_declared_minductive {Σ mind decl} : ground_quotable (@declared_minductive Σ mind decl).
  #[export] Declare Instance quote_declared_inductive {Σ ind mdecl decl} : ground_quotable (@declared_inductive Σ ind mdecl decl).
  #[export] Declare Instance quote_declared_constructor {Σ cstr mdecl idecl cdecl} : ground_quotable (@declared_constructor Σ cstr mdecl idecl cdecl).
  #[export] Declare Instance quote_declared_projection {Σ proj mdecl idecl cdecl pdecl} : ground_quotable (@declared_projection Σ proj mdecl idecl cdecl pdecl).
End QuoteLookupSig.

Module Type QuotationOfEnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "ET").
End QuotationOfEnvTyping.

Module Type QuoteEnvTypingSig (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU).

  #[export] Hint Unfold
    lift_typing0
    All_local_rel
  : quotation.
  #[export] Typeclasses Transparent
    lift_typing0
    All_local_rel
  .

  #[export] Declare Instance quote_All_local_env {typing Γ} {qtyping : quotation_of typing} {quote_typing : forall Γ j, ground_quotable (typing Γ j)} : ground_quotable (@All_local_env typing Γ).
  #[export] Declare Instance quote_lift_sorting {checking sorting j} {qcheck : quotation_of checking} {qsorting : quotation_of sorting} {quote_check : forall tm, j_term j = Some tm -> ground_quotable (checking tm (j_typ j))} {quote_sorting : forall u, ground_quotable (sorting (j_typ j) u)} : ground_quotable (@lift_sorting checking sorting j).

  #[export] Declare Instance quote_All_local_env_over_sorting
   {checking sorting cproperty sproperty Γ H}
   {qchecking : quotation_of checking} {qsorting : quotation_of sorting} {qcproperty : quotation_of cproperty} {qsproperty : quotation_of sproperty}
   {quote_checking : forall Γ t T, ground_quotable (checking Γ t T)} {quote_sorting : forall Γ T u, ground_quotable (sorting Γ T u)} {quote_sproperty : forall Γ all t u tu, ground_quotable (sproperty Γ all t u tu)} {quote_cproperty : forall Γ all t T tu, ground_quotable (cproperty Γ all t T tu)}
    : ground_quotable (@All_local_env_over_sorting checking sorting cproperty sproperty Γ H).

  #[export] Declare Instance quote_All_local_env_over {typing property Γ H}
   {qtyping : quotation_of typing} {qproperty : quotation_of property}
   {quote_typing : forall Γ t T, ground_quotable (typing Γ t T)} {quote_property : forall Γ all b t tb, ground_quotable (property Γ all b t tb)}
    : ground_quotable (@All_local_env_over typing property Γ H).

  #[export] Declare Instance quote_ctx_inst {typing Γ ctx inst}
   {qtyping : quotation_of typing}
   {quote_typing : forall i t, ground_quotable (typing Γ i t)}
    : ground_quotable (@ctx_inst typing Γ ctx inst).
End QuoteEnvTypingSig.

Module Type QuotationOfConversion (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (C : ConversionSig T E TU ET).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "C").
End QuotationOfConversion.

Module Type QuoteConversionSig (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import C : ConversionSig T E TU ET).

  #[export] Declare Instance quote_All_decls_alpha_pb {pb P b b'} {qP : quotation_of P} {quoteP : forall pb t t', ground_quotable (P pb t t')}
    : ground_quotable (@All_decls_alpha_pb pb P b b').

  #[export] Declare Instance quote_cumul_pb_decls {cumul_gen pb Σ Γ Γ' x y}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_decls cumul_gen pb Σ Γ Γ' x y).

  #[export] Declare Instance quote_cumul_pb_context {cumul_gen pb Σ Γ Γ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_context cumul_gen pb Σ Γ Γ').

  #[export] Declare Instance quote_cumul_ctx_rel {cumul_gen Σ Γ Δ Δ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_ctx_rel cumul_gen Σ Γ Δ Δ').
End QuoteConversionSig.

Module Type QuotationOfGlobalMaps (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (C : ConversionSig T E TU ET) (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET C L).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "GM").
End QuotationOfGlobalMaps.

Module Type QuoteGlobalMapsSig (Import T: Term) (Import E: EnvironmentSig T) (Import TU : TermUtils T E) (Import ET: EnvTypingSig T E TU) (Import C: ConversionSig T E TU ET) (Import L: LookupSig T E) (Import GM : GlobalMapsSig T E TU ET C L).

  #[export] Hint Unfold
    mdecl_at_i
    constructor_univs
    on_constructors
    fresh_global
  : quotation.
  #[export] Typeclasses Transparent
    mdecl_at_i
    constructor_univs
    on_constructors
    fresh_global
  .

  #[export] Declare Instance quote_on_context {P} {qP : quotation_of P} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ ctx} : ground_quotable (@on_context P Σ ctx).

  #[export] Declare Instance quote_type_local_ctx {P} {qP : quotation_of P} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ Γ Δ u} : ground_quotable (@type_local_ctx P Σ Γ Δ u).

  #[export] Declare Instance quote_sorts_local_ctx {P} {qP : quotation_of P} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ Γ Δ us} : ground_quotable (@sorts_local_ctx P Σ Γ Δ us).

  #[export] Declare Instance quote_on_type {P} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ Γ T} : ground_quotable (@on_type P Σ Γ T).
  #[export] Declare Instance quote_on_type_rel {P} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ Γ T r} : ground_quotable (@on_type_rel P Σ Γ T r).

  #[export] Declare Instance quote_on_udecl {univs udecl} : ground_quotable (@on_udecl univs udecl).
  #[export] Declare Instance quote_satisfiable_udecl {univs ϕ} : ground_quotable (@satisfiable_udecl univs ϕ).
  (* #[export] Declare Instance quote_valid_on_mono_udecl {univs ϕ} : ground_quotable (@valid_on_mono_udecl univs ϕ). *)

  #[export] Declare Instance quote_positive_cstr_arg {mdecl ctx t} : ground_quotable (@positive_cstr_arg mdecl ctx t).
  #[export] Declare Instance quote_positive_cstr {mdecl i ctx t} : ground_quotable (@positive_cstr mdecl i ctx t).

  #[export] Declare Instance quote_ind_respects_variance {Pcmp} {qPcmp : quotation_of Pcmp} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {Σ mdecl v indices} : ground_quotable (@ind_respects_variance Pcmp Σ mdecl v indices).
  #[export] Declare Instance quote_cstr_respects_variance {Pcmp} {qPcmp : quotation_of Pcmp} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {Σ mdecl v cs} : ground_quotable (@cstr_respects_variance Pcmp Σ mdecl v cs).
  #[export] Declare Instance quote_on_constructor {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ mdecl i idecl ind_indices cdecl cunivs} : ground_quotable (@on_constructor cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs).
  #[export] Declare Instance quote_on_proj {mdecl mind i k p decl} : ground_quotable (@on_proj mdecl mind i k p decl).
  #[export] Declare Instance quote_on_projection {mdecl mind i cdecl k p} : ground_quotable (@on_projection mdecl mind i cdecl k p).
  #[export] Declare Instance quote_on_projections {mdecl mind i idecl ind_indices cdecl} : ground_quotable (@on_projections mdecl mind i idecl ind_indices cdecl).
  #[export] Declare Instance quote_check_ind_sorts {cf P} {qP : quotation_of P} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ params kelim ind_indices cdecls ind_sort} : ground_quotable (@check_ind_sorts cf P Σ params kelim ind_indices cdecls ind_sort).
  #[export] Declare Instance quote_on_ind_body {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ mind mdecl i idecl} : ground_quotable (@on_ind_body cf Pcmp P Σ mind mdecl i idecl).
  #[export] Declare Instance quote_on_variance {cf Σ univs variances} : ground_quotable (@on_variance cf Σ univs variances).
  #[export] Declare Instance quote_on_inductive {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ mind mdecl} : ground_quotable (@on_inductive cf Pcmp P Σ mind mdecl).
  #[export] Declare Instance quote_on_constant_decl {P} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ d} : ground_quotable (@on_constant_decl P Σ d).
  #[export] Declare Instance quote_on_global_decl {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ kn d} : ground_quotable (@on_global_decl cf Pcmp P Σ kn d).
  #[export] Declare Instance quote_on_global_decls_data {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {univs retro Σ kn d} : ground_quotable (@on_global_decls_data cf Pcmp P univs retro Σ kn d).
  #[export] Declare Instance quote_on_global_decls {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {univs retro Σ} : ground_quotable (@on_global_decls cf Pcmp P univs retro Σ).
  #[export] Declare Instance quote_on_global_univs {univs} : ground_quotable (@on_global_univs univs).
  #[export] Declare Instance quote_on_global_env {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {g} : ground_quotable (@on_global_env cf Pcmp P g).
  #[export] Declare Instance quote_on_global_env_ext {cf Pcmp P} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)} {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)} {Σ} : ground_quotable (@on_global_env_ext cf Pcmp P Σ).
End QuoteGlobalMapsSig.

Module Type QuotationOfConversionPar (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (CS : ConversionParSig T E TU ET).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "CS").
End QuotationOfConversionPar.

Module Type QuoteConversionParSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (Import CS : ConversionParSig T E TU ET).
  #[export] Declare Instance quote_cumul_gen {cf Σ Γ pb t t'} : ground_quotable (@cumul_gen cf Σ Γ pb t t').
End QuoteConversionParSig.

Module Type QuotationOfTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
  (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "Ty").
End QuotationOfTyping.

Module Type QuoteTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
       (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET) (Import Ty : Typing T E TU ET CT CS).

  #[export] Declare Instance quote_typing {cf Σ Γ t T} : ground_quotable (@typing cf Σ Γ t T).
End QuoteTyping.

Module Type QuotationOfDeclarationTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
  (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
  (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
  (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L) (DT : DeclarationTypingSig T E TU ET CT CS Ty L GM).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "DT").
End QuotationOfDeclarationTyping.

Module Type QuoteDeclarationTypingSig (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E)
       (Import ET : EnvTypingSig T E TU) (Import CT : ConversionSig T E TU ET)
       (Import CS : ConversionParSig T E TU ET) (Import Ty : Typing T E TU ET CT CS)
       (Import L : LookupSig T E) (Import GM : GlobalMapsSig T E TU ET CT L)
       (Import DT : DeclarationTypingSig T E TU ET CT CS Ty L GM).
  #[export] Declare Instance quote_type_local_decl {cf Σ Γ d} : ground_quotable (@type_local_decl cf Σ Γ d).
  #[export] Declare Instance quote_wf_local_rel {cf Σ Γ Γ'} : ground_quotable (@wf_local_rel cf Σ Γ Γ').
End QuoteDeclarationTypingSig.
