(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import Ast AstUtils Common.
From MetaRocq.Template.TemplateMonad Require Export Core.

Set Warnings "-notation-overridden".
From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.TemplatePCUIC Require Import TemplateMonadToPCUIC TemplateToPCUIC PCUICToTemplate.
Set Warnings "+notation-overridden".

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import MonadNotation.

Abbreviation eval_pcuic_quotation := eval_pcuic_quotation (only parsing).
#[export] Existing Instance default_eval_pcuic_quotation.

Definition tmQuote@{t u} `{eval_pcuic_quotation} {A:Type@{t}} (a : A) : TemplateMonad@{t u} PCUICAst.term :=
  bind@{t u} (tmQuote@{t u} a) monad_trans@{t u}.
Definition tmQuoteRecTransp@{t u} `{eval_pcuic_quotation} {A:Type@{t}} (a : A) (bypass_opacity : bool) : TemplateMonad@{t u} PCUICProgram.pcuic_program :=
  bind@{t u} (tmQuoteRecTransp@{t u} a bypass_opacity) (fun p => tmMaybeEval@{t u} (trans_template_program p)).
Definition tmQuoteInductive@{t u} `{eval_pcuic_quotation} (kn : kername) : TemplateMonad@{t u} mutual_inductive_body := tmQuoteInductive@{t u} kn.
Definition tmQuoteConstant@{t u} `{eval_pcuic_quotation} (kn : kername) (bypass_opacity : bool) : TemplateMonad@{t u} constant_body :=
  bind@{t u} (tmQuoteConstant@{t u} kn bypass_opacity) monad_trans_constant_body@{t u}.
Definition tmMkInductive@{t u} `{eval_pcuic_quotation} (b : bool) (mie : mutual_inductive_entry) : TemplateMonad@{t u} unit
  := bind@{t u} (tmMaybeEval (trans_mutual_inductive_entry mie)) (tmMkInductive@{t u} b).
Definition tmUnquote@{t u} `{eval_pcuic_quotation} (t : PCUICAst.term) : TemplateMonad@{t u} typed_term :=
  bind@{t u} (tmMaybeEval@{t u} (PCUICToTemplate.trans t)) tmUnquote@{t u}.
Definition tmUnquoteTyped@{t u} `{eval_pcuic_quotation} A (t : PCUICAst.term) : TemplateMonad@{t u} A :=
  bind@{t u} (tmMaybeEval@{t u} (PCUICToTemplate.trans t)) (tmUnquoteTyped@{t u} A).

(** We keep the original behaviour of [tmQuoteRec]: it quotes all the dependencies regardless of the opaqueness settings *)
Definition tmQuoteRec `{eval_pcuic_quotation} {A} (a : A) := tmQuoteRecTransp a true.

Definition tmMkDefinition@{t u} `{eval_pcuic_quotation} (id : ident) (tm : PCUICAst.term) : TemplateMonad@{t u} unit :=
  bind@{t u} (tmMaybeEval (PCUICToTemplate.trans tm)) (tmMkDefinition@{t u} id).
