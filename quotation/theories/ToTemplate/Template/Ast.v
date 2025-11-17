From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate Require Import (hints) Stdlib.Init Stdlib.Lists Stdlib.Numbers Stdlib.Floats.
From MetaRocq.Quotation.ToTemplate.Common Require Import (hints) Universes BasicAst Kernames.
From MetaRocq.Quotation.ToTemplate.Common Require Import Environment EnvironmentTyping.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig EnvironmentTyping.Sig.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Template Require Import Ast.Instances ReflectAst.Instances.
From MetaRocq.Template Require Import Ast ReflectAst Induction.

#[export] Instance quote_pstring : ground_quotable PrimString.string := fun s => Ast.tString s.

#[export] Instance quote_predicate {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (predicate term) := ltac:(destruct 1; exact _).
#[export] Instance quote_branch {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (branch term) := ltac:(destruct 1; exact _).
#[local] Hint Extern 1 => assumption : typeclass_instances.
#[export] Instance quote_term : ground_quotable term := ltac:(induction 1 using term_forall_list_rect; exact _).

Module QuoteTemplateTerm <: QuoteTerm TemplateTerm.
  #[export] Instance quote_term : ground_quotable TemplateTerm.term := ltac:(cbv [TemplateTerm.term]; exact _).
End QuoteTemplateTerm.
Export (hints) QuoteTemplateTerm.

Module QuoteEnv := QuoteEnvironment TemplateTerm Env QuoteEnvHelper qTemplateTerm qEnv qQuoteEnvHelper QuoteTemplateTerm.
Export (hints) QuoteEnv.

Module QuoteTemplateLookup := QuoteLookup TemplateTerm Env TemplateLookup EnvDecide qEnv qTemplateLookup qEnvDecide QuoteEnv.
Export (hints) QuoteTemplateLookup.

#[export] Instance quote_parameter_entry : ground_quotable parameter_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_definition_entry : ground_quotable definition_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_constant_entry : ground_quotable constant_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_one_inductive_entry : ground_quotable one_inductive_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_mutual_inductive_entry : ground_quotable mutual_inductive_entry := ltac:(destruct 1; exact _).
