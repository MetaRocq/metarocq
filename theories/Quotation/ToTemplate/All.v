From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.Template Require WfAst TypingWf.
From MetaRocq.Quotation.ToTemplate.Template Require Ast Typing WfAst TypingWf.

(* without typing derivations *)
Module Raw.
  (* These are probably the only quotation functions that users of this development will want to use; other files should be considered internal to the development of quotation *)
  Definition quote_checker_flags : checker_flags -> Ast.term := config.quote_checker_flags.
  Definition quote_global_env_ext : global_env_ext -> Ast.term := Ast.QuoteEnv.quote_global_env_ext.
  Definition quote_context : context -> Ast.term := Ast.QuoteEnv.quote_context.
  Definition quote_term : Ast.term -> Ast.term := Ast.quote_term.
  Definition quote_typing {cf : checker_flags} {Σ Γ t T} : (Σ ;;; Γ |- t : T) -> Ast.term := Typing.quote_typing.
  Definition quote_red {Σ Γ x y} : @red Σ Γ x y -> Ast.term := Typing.quote_red.
  Definition quote_wf_local {cf : checker_flags} {Σ Γ} : wf_local Σ Γ -> Ast.term := Typing.quote_wf_local.
  Definition quote_wf {cf Σ} : @wf cf Σ -> Ast.term := Typing.quote_wf.
  Definition quote_wf_ext {cf Σ} : @wf_ext cf Σ -> Ast.term := Typing.quote_wf_ext.
  Module WfAst.
    Definition quote_wf {Σ t} : @WfAst.wf Σ t -> Ast.term := WfAst.quote_wf.
  End WfAst.
  (* TODO: do we want anything from TypingWf? Is there anything else missing here? *)

  (** N.B. Only works if you [Import Raw.QuoteNotationHints] *)
  Abbreviation quote := Init.quoted_term_of (only parsing).
  Module QuoteNotationHints.
    Export (hints) Quotation.ToTemplate.Init
      Quotation.ToTemplate.Template.Ast
      Quotation.ToTemplate.Template.Typing
      Quotation.ToTemplate.Template.WfAst
      Quotation.ToTemplate.Template.TypingWf
    .
  End QuoteNotationHints.
End Raw.

(* eventually we'll have proofs that the above definitions are well-typed *)
