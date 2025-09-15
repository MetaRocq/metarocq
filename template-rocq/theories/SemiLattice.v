(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils NonEmptyLevelExprSet.

From MetaRocq.Common Require Universes HornClauses.
From Equations Require Import Equations.
Set Equations Transparent.

End Completeness.

Section Presentation.

  Definition term (V : Type) : Type := list (V * nat).
  Definition relation (V : Type) := term V -> term V -> Prop.

  Record presented (V : Type) := {
    terms : term V -> Prop;
    relations : relation V }.

  Definition valid (V : Type) (C : presented V) (t u : term V) := relations _ C t u.

  Section Terms.
    Context (V : Type) (pres : presented V).
    Definition succV (t : term V) := map (fun '(x, n) => (x, S n)) t.
    Definition maxV (t u : term V) := t ++ u.

    Definition presents : semilattice.
    Proof.
      unshelve refine {| carrier := term V; eq := relations _ pres; succ := succV; join := maxV |}.
      (* - intros x y z. *)
      all:apply (todo "laws").
    Defined.

    Definition interp_exp (vn : V * nat) : presents := let '(v, n) := vn in [(v, n)].
    Definition interp_term (t : term V) : presents :=
      match t with
      | [] => []
      | hd :: tl => List.fold_left (fun n x => maxV n (interp_exp x)) tl (interp_exp hd)
      end.

    Lemma all_terms (x : s) : exists t : term,


