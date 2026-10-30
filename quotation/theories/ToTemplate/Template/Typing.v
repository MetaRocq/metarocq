From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate Require Import (hints) Stdlib.Init Stdlib.Lists Stdlib.Numbers Stdlib.Floats.
From MetaRocq.Quotation.ToTemplate.Utils Require Import (hints) utils All_Forall (* MRProd*).
From MetaRocq.Quotation.ToTemplate.Common Require Import (hints) config BasicAst Universes Kernames Environment EnvironmentTyping Primitive Reflect.
From MetaRocq.Quotation.ToTemplate.Template Require Import (hints) AstUtils
  LiftSubst UnivSubst ReflectAst TermEquality WfAst.
From MetaRocq.Quotation.ToTemplate.Common Require Import Environment EnvironmentTyping.
From MetaRocq.Quotation.ToTemplate.Template Require Import Ast.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Template Require Import Ast.Instances Typing.Instances.
From MetaRocq.Template Require Import Ast Typing.

#[export] Instance quote_instantiate_params_subst_spec {params pars s pty s' pty'} : ground_quotable (@instantiate_params_subst_spec params pars s pty s' pty').
Proof.
  revert params pars s pty s' pty'; induction params as [|a params]; intros; [ | destruct a as [? [] ?], pty ]; destruct pars.
  all: try solve [ intro H; exfalso; inversion H ].
  { intro pf.
    assert (s' = s) by now inversion pf.
    assert (pty' = pty) by now inversion pf.
    subst.
    revert pf.
    adjust_ground_quotable_by_econstructor_inversion (). }
  adjust_ground_quotable_by_econstructor_inversion ().
  adjust_ground_quotable_by_econstructor_inversion ().
  adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_red1 {Σ Γ x y} : ground_quotable (@red1 Σ Γ x y).
Proof.
  revert Γ x y; cbv [ground_quotable].
  fix quote_red1 4; change (forall Γ x y, ground_quotable (@red1 Σ Γ x y)) in quote_red1.
  intros Γ x y.
  destruct 1; replace_quotation_of_goal ().
Defined.
#[export] Instance quote_red {Σ Γ x y} : ground_quotable (@red Σ Γ x y) := ltac:(induction 1; exact _).
#[export] Instance quote_eq_term_nocast {cf Σ ϕ t u} : ground_quotable (@eq_term_nocast cf Σ ϕ t u) := ltac:(cbv [eq_term_nocast]; exact _).
#[export] Instance quote_leq_term_nocast {cf Σ ϕ t u} : ground_quotable (@leq_term_nocast cf Σ ϕ t u) := ltac:(cbv [leq_term_nocast]; exact _).
#[export] Instance quote_cumul_gen {cf Σ Γ pb t u} : ground_quotable (@cumul_gen cf Σ Γ pb t u) := ltac:(induction 1; exact _).
#[export] Instance quote_eq_opt_term {cf Σ ϕ t u} : ground_quotable (@eq_opt_term cf Σ ϕ t u) := ltac:(cbv [eq_opt_term]; exact _).
#[export] Instance quote_eq_decl {cf Σ ϕ d d'} : ground_quotable (@eq_decl cf Σ ϕ d d') := ltac:(cbv [eq_decl]; exact _).
#[export] Instance quote_eq_context {cf Σ ϕ d d'} : ground_quotable (@eq_context cf Σ ϕ d d') := ltac:(cbv [eq_context]; exact _).

Module QuoteTemplateEnvTyping := QuoteEnvTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping qTemplateTerm qEnv qTemplateEnvTyping QuoteTemplateTerm QuoteEnv.
Export (hints) QuoteTemplateEnvTyping.

Module QuoteTemplateConversion := QuoteConversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion qTemplateTerm qEnv qTemplateConversion QuoteTemplateTerm QuoteEnv.
Export (hints) QuoteTemplateConversion.

Module QuoteTemplateGlobalMaps := QuoteGlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup TemplateGlobalMaps qTemplateTerm qEnv qTemplateEnvTyping qTemplateConversion qTemplateLookup qTemplateGlobalMaps QuoteTemplateTerm QuoteEnv QuoteTemplateEnvTyping QuoteTemplateConversion QuoteTemplateLookup.
Export (hints) QuoteTemplateGlobalMaps.

Module QuoteTemplateConversionPar <: QuoteConversionParSig TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversionPar.
  #[export] Instance quote_cumul_gen {cf Σ Γ pb t t'} : ground_quotable (@TemplateConversionPar.cumul_gen cf Σ Γ pb t t') := ltac:(cbv [TemplateConversionPar.cumul_gen]; exact _).
End QuoteTemplateConversionPar.
Export (hints) QuoteTemplateConversionPar.

Section quote_typing.
  Context {cf : config.checker_flags} {Σ : global_env_ext}.

  #[local] Hint Extern 1 => progress cbv zeta : typeclass_instances.

  Fixpoint quote_typing' {Γ t T} (pf : @typing cf Σ Γ t T) {struct pf} : quotation_of pf
  with quote_typing_spine' {Γ t s T} (pf : @typing_spine cf Σ Γ t s T) {struct pf} : quotation_of pf.
  Proof.
    all: change (forall Γ t T, ground_quotable (@typing cf Σ Γ t T)) in quote_typing'.
    all: change (forall Γ t s T, ground_quotable (@typing_spine cf Σ Γ t s T)) in quote_typing_spine'.
    all: destruct pf.
    all: [ > replace_quotation_of_goal () .. ].
  Defined.
End quote_typing.
#[export] Instance quote_typing {cf Σ Γ t T} : ground_quotable (@typing cf Σ Γ t T) := quote_typing'.
#[export] Instance quote_typing_spine {cf Σ Γ t s T} : ground_quotable (@typing_spine cf Σ Γ t s T) := quote_typing_spine'.
Definition quote_wf_local {cf : config.checker_flags} {Σ Γ} : ground_quotable (wf_local Σ Γ) := _.

#[export] Instance quote_has_nparams {npars ty} : ground_quotable (@has_nparams npars ty) := ltac:(cbv [has_nparams]; exact _).

Module QuoteTemplateTyping <: QuoteTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping
                                TemplateConversion TemplateConversionPar TemplateTyping.
  #[export] Instance quote_typing {cf Σ Γ t T} : ground_quotable (@TemplateTyping.typing cf Σ Γ t T) := quote_typing.
End QuoteTemplateTyping.
Export (hints) QuoteTemplateTyping.

Module QuoteTemplateDeclarationTyping
  := QuoteDeclarationTyping
       TemplateTerm
       Env
       TemplateTermUtils
       TemplateEnvTyping
       TemplateConversion
       TemplateConversionPar
       TemplateTyping
       TemplateLookup
       TemplateGlobalMaps
       TemplateDeclarationTyping
       qTemplateTerm
       qEnv
       qTemplateEnvTyping
       qTemplateConversion
       qTemplateTyping
       qTemplateGlobalMaps
       QuoteTemplateTerm
       QuoteEnv
       QuoteTemplateEnvTyping
       QuoteTemplateConversion
       QuoteTemplateTyping
       QuoteTemplateLookup
       QuoteTemplateGlobalMaps.
Export (hints) QuoteTemplateDeclarationTyping.

#[export] Instance quote_wf {cf Σ} : ground_quotable (@wf cf Σ) := ltac:(cbv [wf]; exact _).
#[export] Instance quote_wf_ext {cf Σ} : ground_quotable (@wf_ext cf Σ) := ltac:(cbv [wf_ext]; exact _).
#[export] Instance quote_Forall_typing_spine {cf Σ Γ P T t U tls} {qP : quotation_of P} {quoteP : forall x y, ground_quotable (P x y)} : ground_quotable (@Forall_typing_spine cf Σ Γ P T t U tls) := ltac:(induction 1; exact _).
