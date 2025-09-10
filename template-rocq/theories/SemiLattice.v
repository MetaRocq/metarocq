(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From Equations Require Import Equations.
Set Equations Transparent.


Section Completeness.
  Reserved Notation "x ≡ y" (at level 90).
  Record semilattice :=
    { carrier :> Type;
      eq : carrier -> carrier -> Prop where "x ≡ y" := (eq x y);
      succ : carrier -> carrier;
      join : carrier -> carrier -> carrier;
      join_assoc x y z : join x (join y z) ≡ join (join x y) z;
      join_comm x y : join x y ≡ join y x;
      join_idem x : join x x ≡ x;
      join_sub x : join x (succ x) ≡ succ x;
      succ_inj : forall x y, succ x ≡ succ y -> x ≡ y;
      succ_join : forall x y, succ (join x y) ≡ join (succ x) (succ y);
    }.

  Notation "x ≡ y" := (eq _ x y).

  Section Derived.
    Context (s : semilattice).
    Definition le (x y : s) := join s x y ≡ y.

    Fixpoint add (x : s) n : s :=
      match n with
      | 0 => x
      | S n => succ _ (add x n)
      end.
  End Derived.

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


