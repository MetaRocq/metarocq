(* Distributed under the terms of the MIT license. *)
From MetaRocq.Template Require ExtractableLoader.
From MetaRocq.Template Require Export Loader.
From MetaRocq.TemplatePCUIC.PCUICTemplateMonad Require Core.
From MetaRocq.TemplatePCUIC Require Import TemplateMonadToPCUIC.

Abbreviation eval_pcuic_quotation := eval_pcuic_quotation (only parsing).
#[export] Existing Instance default_eval_pcuic_quotation.

Set Warnings "-notation-overridden".
(* Work around COQBUG(https://github.com/coq/coq/issues/16715) *)
Notation "<% x %>" := (match @monad_trans return _ with monad_trans => ltac:(let monad_trans := constr:(monad_trans _) in let p y := exact y in let p y := run_template_program (monad_trans y) p in quote_term x p) end)
  (only parsing).

(* Work around COQBUG(https://github.com/coq/coq/issues/16715) with [match] *)
(* Use [return _] to avoid running the program twice on failure *)
Notation "<# x #>" := (match @PCUICTemplateMonad.Core.tmQuoteRec return _ with tmQuoteRec => ltac:(let qx := constr:(tmQuoteRec _ _ x) in let p y := exact y in run_template_program qx p) end)
  (only parsing).
