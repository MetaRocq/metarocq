(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICTyping PCUICEquality PCUICOnFreeVars
  PCUICSigmaCalculus PCUICRenameDef.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".
Implicit Types cf : checker_flags.

(** * Type preservation for σ-calculus instantiation *)

Open Scope sigma_scope.

Definition inst_context σ (Γ : context) : context :=
  fold_context_k (fun i => inst (⇑^i σ)) Γ.

#[global] Instance inst_context_ext : Proper (`≐1` ==> Logic.eq ==> Logic.eq) inst_context.
Proof.
  intros f g Hfg x y ->.
  apply fold_context_k_ext => i t.
  now rewrite Hfg.
Qed.

Definition inst_decl σ d := map_decl (inst σ) d.

Definition inst_context_snoc0 s Γ d :
  inst_context s (d :: Γ) =
  inst_context s Γ ,, map_decl (inst (⇑^#|Γ| s)) d.
Proof. unfold inst_context. now rewrite fold_context_k_snoc0. Qed.
#[global] Hint Rewrite inst_context_snoc0 : sigma.

Definition inst_mutual_inductive_body σ m :=
  map_mutual_inductive_body (fun i => inst (⇑^i σ)) m.



(* Untyped substitution for untyped reduction / cumulativity *)
Definition usubst (Γ : context) σ (Δ : context) :=
  forall x decl,
    nth_error Γ x = Some decl ->
    (forall b,
        decl.(decl_body) = Some b ->
        (∑ x' decl', σ x = tRel x' ×
          nth_error Δ x' = Some decl' ×
          (** This is let-preservation *)
          option_map (rename (rshiftk (S x'))) decl'.(decl_body) = Some (b.[↑^(S x) ∘s σ])) +
        (* This allows to expand a let-binding everywhere *)
        (σ x = b.[↑^(S x) ∘s σ])).

(* Untyped substitution for untyped reduction / cumulativity *)
Definition closed_subst (Γ : context) σ (Δ : context) :=
  is_closed_context Δ ×
  (forall x decl, nth_error Γ x = Some decl -> is_open_term Δ (σ x)) ×
  usubst Γ σ Δ.

(* Well-typedness of a substitution *)

Definition well_subst {cf} Σ (Γ : context) σ (Δ : context) :=
  (forall x decl,
    nth_error Γ x = Some decl ->
    Σ ;;; Δ |- σ x : ((lift0 (S x)) (decl_type decl)).[ σ ]) ×
  usubst Γ σ Δ.

Notation "Σ ;;; Δ ⊢ σ : Γ" :=
  (well_subst Σ Γ σ Δ) (at level 50, Δ, σ, Γ at next level).
