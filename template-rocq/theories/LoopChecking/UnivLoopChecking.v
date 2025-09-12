(* Distributed under the terms of the MIT license. *)
(* This module provides an instantiation of the deciders for universe checking,
  i.e. for constraints on non-empty level expressions (l, k) where k ∈ 𝐍 *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Universes.
From MetaRocq.Common.LoopChecking Require Import Common Interfaces Deciders.
From Equations Require Import Equations.
Set Equations Transparent.

Import Universes.

Module MoreLevel.
  Import Universes.
  Include Level.

  Definition to_string := string_of_level.
End MoreLevel.

Module LevelMap.
  Module OT := FMapOrderedType_from_UsualOrderedType Level.
  Include FMapAVL.Make OT.
End LevelMap.

Module LevelExprZ.
  Definition t := (Level.t * Z)%type.
  Local Open Scope Z_scope.

  Definition succ (l : t) : t := (fst l, Z.succ (snd l)).

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltLevelExpr1 l n n' : (n < n') -> lt_ (l, n) (l, n')
  | ltLevelExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').
  Derive Signature for lt_.
  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X. subst. lia. subst.
      eapply Level.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2; now rewrite H1 H2.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match Level.compare l1 l2 with
      | Eq => Z.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [? ?] [? ?]; cbn; repeat constructor.
    destruct (Level.compare_spec t0 t1); repeat constructor; tas.
    subst.
    destruct (Z.compare_spec z z0); repeat constructor; tas. congruence.
  Qed.

  Global Instance reflect_t : ReflectEq t := reflect_prod _ _ .

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2} := Classes.eq_dec.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End LevelExprZ.

Module LevelExprZSet.
  Include MSetList.MakeWithLeibniz LevelExprZ.

  Definition levels (e : t) :=
    fold (fun le => LevelSet.add (fst le)) e LevelSet.empty.

  Record nonEmptyLevelExprSet
    := { t_set : t ;
         t_ne  : is_empty t_set = false }.
End LevelExprZSet.
Module LevelExprZSetFacts := WFactsOn LevelExprZ LevelExprZSet.
Module LevelExprZSetProp := MSetProperties.OrdProperties LevelExprZSet.

Module LevelSet.
  Include MakeWithLeibniz Level.
End LevelSet.
Module LS <: LevelSets.
  Module Level := MoreLevel .
  Module LevelSet := LevelSet.
  Module LevelExpr := LevelExprZ.
  Module LevelExprSet := LevelExprZSet.
  Module LevelMap := LevelMap.
End LS.

Definition to_levelexprzset (u : LevelExprSet.t) : LS.LevelExprSet.t :=
  LevelExprSet.fold (fun '(l, k) => LS.LevelExprSet.add (l, Z.of_nat k)) u LS.LevelExprSet.empty.

Lemma to_levelexprzset_spec_1 u :
  forall l k, LevelExprSet.In (l, k) u -> LevelExprZSet.In (l, Z.of_nat k) (to_levelexprzset u).
Proof.
  intros l k.
  rewrite /to_levelexprzset.
  apply LevelExprSetProp.fold_rec.
  - move=> s' hs'; now move=> /hs'.
  - move=> x a s' s'' hin hnin hadd ih /hadd [].
    + intros ->. apply LevelExprZSet.add_spec. now left.
    + intros hin'. destruct x. apply LevelExprZSet.add_spec. now right.
Qed.

Lemma to_levelexprzset_spec_2 u :
  forall l k, LevelExprZSet.In (l, k) (to_levelexprzset u) -> LevelExprSet.In (l, Z.to_nat k) u /\ (0 <= k)%Z.
Proof.
  intros l k.
  rewrite /to_levelexprzset.
  apply LevelExprSetProp.fold_rec.
  - now move=> s' hs' /LevelExprZSetFacts.empty_iff.
  - move=> x a s' s'' hin hnin hadd ih.
    destruct x as [l' k'].
    rewrite LS.LevelExprSet.add_spec => -[].
    + intros [= -> eq]. subst k. split. apply hadd. now left. lia.
    + intros hin'. move: (ih hin') => []; split => //. apply hadd; now right.
Qed.

Program Definition to_atoms (u : Universe.t) : LevelExprZSet.nonEmptyLevelExprSet :=
  {| LevelExprZSet.t_set := to_levelexprzset u |}.
Next Obligation.
  destruct u. cbn.
  destruct (LevelExprZSet.is_empty _) eqn:he => //.
  apply LevelExprZSet.is_empty_spec in he.
  assert (LevelExprSet.is_empty t_set).
  apply LevelExprSet.is_empty_spec. intros x hin.
  destruct x. eapply (he (t, Z.of_nat n)).
  now apply to_levelexprzset_spec_1.
  congruence.
Qed.

Definition from_levelexprzset (u : LS.LevelExprSet.t) : LevelExprSet.t :=
  LS.LevelExprSet.fold (fun '(l, k) => LevelExprSet.add (l, Z.to_nat k)) u LevelExprSet.empty.

Lemma from_levelexprzset_spec u :
  forall l k, LevelExprZSet.In (l, k) u -> LevelExprSet.In (l, Z.to_nat k) (from_levelexprzset u).
Proof.
  intros l k.
  rewrite /from_levelexprzset.
  apply LevelExprZSetProp.P.fold_rec.
  - now move=> s' hs' /hs'.
  - move=> x a s' s'' hin hnin hadd ih /hadd [].
    * intros ->. apply LevelExprSet.add_spec. now left.
    * intros hin'. destruct x. apply LevelExprSet.add_spec. now right.
Qed.

Lemma from_levelexprzset_spec_2 u :
  forall l k, LevelExprSet.In (l, k) (from_levelexprzset u) -> exists z, LevelExprZSet.In (l, z) u /\ k = Z.to_nat z.
Proof.
  intros l k.
  rewrite /from_levelexprzset.
  apply LevelExprZSetProp.P.fold_rec.
  - now move=> s' hs' /LevelExprSetFact.empty_iff.
  - move=> x a s' s'' hin hnin hadd ih.
    destruct x as [l' k'].
    rewrite LevelExprSet.add_spec => -[].
    + intros [= -> eq]. subst k. exists k'. split => //. apply hadd. now left.
    + intros hin'. move: (ih hin') => [z [hin'' ->]]. exists z. split => //.
      apply hadd. now right.
Qed.

Program Definition from_atoms (u : LS.LevelExprSet.nonEmptyLevelExprSet) : Universe.t :=
  {| LevelExprSet.t_set := from_levelexprzset (LS.LevelExprSet.t_set u) |}.
Next Obligation.
  destruct u. cbn.
  destruct (LevelExprSet.is_empty _) eqn:he => //.
  apply LevelExprSet.is_empty_spec in he.
  assert (LevelExprZSet.is_empty t_set).
  apply LevelExprZSet.is_empty_spec. intros x hin.
  destruct x. eapply (he (t, Z.to_nat z)).
  now apply from_levelexprzset_spec.
  congruence.
Qed.


Module UnivLoopChecking.
  Module LoopCheck := LoopChecking LS.

  Definition to_constraint (x : UnivConstraint.t) : LoopCheck.constraint :=
    let '(l, d, r) := x in
    let '(l, d, r) := match d with
    | ConstraintType.Eq => (l, LoopCheck.UnivEq, r)
    | ConstraintType.Le k =>
      if (k <? 0)%Z then (l, LoopCheck.UnivLe, Universe.add (Z.to_nat (- k)) r)
      else (Universe.add (Z.to_nat k) l, LoopCheck.UnivLe, r)
    end
    in (to_atoms l, d, to_atoms r).

  Module Clauses := LoopCheck.Impl.I.Model.Model.Clauses.Clauses.

  Definition level_constraint_to_constraint (x : LevelConstraint.t) : LoopCheck.constraint :=
    let '(l, d, r) := x in
    let '(l, d, r) := match d with
    | ConstraintType.Eq => (Universe.make' l, LoopCheck.UnivEq, Universe.make' r)
    | ConstraintType.Le k =>
      if (k <? 0)%Z then (Universe.make' l, LoopCheck.UnivLe, Universe.make (r, Z.to_nat (-k)))
      else (Universe.make (l, Z.to_nat k), LoopCheck.UnivLe, Universe.make' r)
    end
    in (to_atoms l, d, to_atoms r).

  Record univ_model := {
    model : LoopCheck.model;
    constraints : UnivConstraintSet.t;
    repr_constraints : forall c, UnivConstraintSet.In c constraints <->
      Clauses.Subset (LoopCheck.to_clauses (to_constraint c)) (LoopCheck.Impl.Abstract.clauses model) }.

  Module C := LoopCheck.Impl.I.Model.Model.Clauses.
  Import C.

  Lemma exists_to_atoms a u :
    LevelExprSet.Exists (fun lk : LevelExprSet.elt => a = lk) (to_atoms u) ->
    Universes.LevelExprSet.Exists (fun lk => a = (fst lk, Z.of_nat (snd lk))) u.
  Proof.
    rewrite /to_atoms; cbn; move=> [] [l k] [] hin ->.
    move/to_levelexprzset_spec_2: hin => [] hin hpos.
    exists (l, Z.to_nat k). split => //=.
    rewrite Z2Nat.id //.
  Qed.

  Lemma exists_to_atoms_2 a (u : Universe.t) :
    Universes.LevelExprSet.Exists (fun lk => a = lk) u ->
    LevelExprSet.Exists (fun lk : LevelExprSet.elt => a = (lk.1, Z.to_nat lk.2)) (to_atoms u).
  Proof.
    rewrite /to_atoms; cbn; move=> [] [l k] [] hin ->.
    move/to_levelexprzset_spec_1: hin => hin.
    exists (l, Z.of_nat k). split => //=.
    rewrite Nat2Z.id //.
  Qed.

  Equations? init_model : univ_model :=
  init_model := {| model := LoopCheck.init_model;
                   constraints := UnivConstraintSet.empty |}.
  Proof. split; try ucsets.
    move=> hyp; apply UnivConstraintSetFact.empty_iff.
    destruct c as [[l d] r]. destruct d; cbn in hyp.
    destruct Z.ltb. cbn in hyp.
    move: hyp. rewrite /Clauses.Subset.
    rw LoopCheck.clauses_of_le_spec.
    move=> h.
    have h' := fun a e => h _ (exists_to_atoms_2 _ _ e).
    specialize (hyp ()) apply hyp.
    2:{ }
    de
clset.

  (* We ignore errors here, which can happen only if the levels are already declared *)
  Definition declare_levels (m : univ_model) (l : LevelSet.t) :=
    LevelSet.fold (fun l m => match LoopCheck.declare_level l m with None => m | Some m => m end) l m.

  Definition enforce_level_constraints (m : univ_model) (l : ConstraintSet.t) :=
    ConstraintSet.fold (fun c m =>
      match m with
      | inl m =>
        let c := (level_constraint_to_constraint c) in
        match LoopCheck.enforce c m with
        | None => (inr (c, None))
        | Some (inl m) => (inl m)
        | Some (inr u) => (inr (c, Some u))
        end
      | inr err => inr err
      end) l (inl m).

  Import LoopCheck.Impl.I.Model.Model.Clauses.FLS.

  Definition of_constraint (c : LoopCheck.constraint) : UnivConstraint.t :=
    let '(l, d, r) := c in
    let d' := match d with
      | LoopCheck.UnivLe => ConstraintType.Le 0
      | LoopCheck.UnivEq => ConstraintType.Eq
      end
    in
    (from_atoms l, d', from_atoms r).

  Definition enforce (c : UnivConstraint.t) (m : univ_model) :=
    match LoopCheck.enforce (to_constraint c) m with
    |





End UnivLoopChecking.
