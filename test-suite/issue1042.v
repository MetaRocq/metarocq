From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import MonadNotation.


(*Exemple with a typing error*)
Definition ident_term (a : term) : term := a.

Definition quote_inductive {X}(inductive:X): TemplateMonad _ :=
  quote <- tmQuote inductive;;
  tmReturn quote.

Inductive tm : Set := .

Definition d1 : TemplateMonad unit.
(* Set Debug "backtrace". *)
Fail MetaRocq Run(
    quote  <- quote_inductive tm;;
    constructor <- ident_term quote;;
    tmPrint constructor)
.
Fail run_template_program (quote  <- quote_inductive tm;;
constructor <- ident_term quote;;
tmPrint constructor) ltac:(fun x => idtac).
 Fail refine (
    quote  <- quote_inductive tm;;
    constructor <- ident_term quote;;
    tmPrint constructor).
