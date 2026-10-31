From MetaRocq.Template Require Import TypingWf.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate Require Import (hints) Stdlib.Init.
From MetaRocq.Quotation.ToTemplate.Utils Require Import (hints) All_Forall.
From MetaRocq.Quotation.ToTemplate.Common Require Import (hints) BasicAst.
From MetaRocq.Quotation.ToTemplate.Template Require Import (hints) Ast WfAst.

#[export] Instance quote_wf_inductive_body {Σ idecl} : ground_quotable (@wf_inductive_body Σ idecl) := ltac:(destruct 1; exact _).
