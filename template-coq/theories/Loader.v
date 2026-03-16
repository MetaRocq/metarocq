(* Distributed under the terms of the MIT license. *)
From MetaCoq.Common Require BasicAst.

From MetaCoq.Template Require TemplateMonad.Core TemplateMonad.Extractable Ast Constants.

Declare ML Module "coq-metacoq-template-coq.plugin".

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).

(* Work around COQBUG(https://github.com/coq/coq/issues/16715) with [match] *)
(* Use [return _] to avoid running the program twice on failure *)
Notation "<# x #>" := (match TemplateMonad.Core.tmQuoteRec x return _ with qx => ltac:(let p y := exact y in run_template_program qx p) end)
  (only parsing).

#[global] Hint Extern 0 (Core.tmTryHelper ?run) => run_template_program run (fun v => refine v) : typeclass_instances.
