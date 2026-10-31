From MetaRocq.Common Require Import Environment.
From MetaRocq.Quotation.ToTemplate Require Import Init.

Module Type QuotationOfTerm (T : Term).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "T").
End QuotationOfTerm.

Module Type QuoteTerm (T : Term).
  #[export] Declare Instance quote_term : ground_quotable T.term.
End QuoteTerm.

Module Type QuotationOfTermDecide (T : Term) (TD : TermDecide T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "TD").
End QuotationOfTermDecide.

Module Type QuotationOfEnvironment (T : Term) (Import E : EnvironmentSig T).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "E").
End QuotationOfEnvironment.

Module Type QuoteEnvironmentSig (T : Term) (Import E : EnvironmentSig T).

  #[export] Hint Unfold
    context
    global_declarations
    global_env_ext
    judgment
  : quotation.
  #[export] Typeclasses Transparent
    context
    global_declarations
    global_env_ext
    judgment
  .

  #[export] Declare Instance quote_constructor_body : ground_quotable constructor_body.
  #[export] Declare Instance quote_projection_body : ground_quotable projection_body.
  #[export] Declare Instance quote_one_inductive_body : ground_quotable one_inductive_body.
  #[export] Declare Instance quote_mutual_inductive_body : ground_quotable mutual_inductive_body.
  #[export] Declare Instance quote_constant_body : ground_quotable constant_body.
  #[export] Declare Instance quote_global_decl : ground_quotable global_decl.

  #[export] Declare Instance quote_global_env : ground_quotable global_env.

  #[export] Declare Instance quote_extends {Σ Σ'} : ground_quotable (@extends Σ Σ').
  #[export] Declare Instance quote_extends_decls {Σ Σ'} : ground_quotable (@extends_decls Σ Σ').
  #[export] Declare Instance quote_primitive_invariants {cdecl ty} : ground_quotable (primitive_invariants cdecl ty).

  #[export] Declare Instance quote_All_decls {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls P t t').
  #[export] Declare Instance quote_All_decls_alpha {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls_alpha P t t').

  (** We need to declare these unfoldable for conversion anyway, so we don't register these instances, but we want them for the external interface *)
  Axiom quote_global_env_ext : ground_quotable global_env_ext.
  Axiom quote_context : ground_quotable context.
End QuoteEnvironmentSig.

Module Type QuotationOfEnvironmentDecide (T : Term) (E : EnvironmentSig T) (ED : EnvironmentDecide T E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "ED").
End QuotationOfEnvironmentDecide.

Module Type QuotationOfTermUtils (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
  MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "TU").
End QuotationOfTermUtils.
