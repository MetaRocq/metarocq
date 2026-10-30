(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICOnFreeVars
  PCUICSigmaCalculus PCUICTyping.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".

Section Renaming.

Context `{cf : checker_flags}.


(* Notion of valid renaming without typing information. *)

(** We might want to relax this to allow "renamings" that change e.g.
  the universes or names, but should generalize the renaming operation at
  the same time *)
(** Remark: renaming allows instantiating an assumption with a well-typed body *)

Definition urenaming (P : nat -> bool) Γ Δ f :=
  forall i decl, P i ->
    nth_error Γ i = Some decl ->
    ∑ decl', (nth_error Δ (f i) = Some decl') ×
    (eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
    ((rename (f ∘ rshiftk (S i)) decl.(decl_type) =
     rename (rshiftk (S (f i))) decl'.(decl_type)) ×
      on_Some_or_None (fun body => Some (rename (f ∘ rshiftk (S i)) body) =
         option_map (rename (rshiftk (S (f i)))) decl'.(decl_body)) decl.(decl_body))).

(* Definition of a good renaming with respect to typing *)
Definition renaming P Σ Γ Δ f :=
  wf_local Σ Δ × urenaming P Γ Δ f.

Definition renaming_closed Γ Δ f := urenaming (closedP #|Γ| xpredT) Γ Δ f.

End Renaming.

