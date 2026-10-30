(* Distributed under the terms of the MIT license. *)
(* This module provides an instantiation of the deciders for universe checking,
  i.e. for constraints on non-empty level expressions (l, k) where k ∈ 𝐍, by embedding
  into constraints on expressions where k ∈ 𝐙.
  The checking algorithm on partial models is sound and complete for
  entailment in the Horn Clauses system, which is equivalent to the equational theory
  of the free semilattice (InitialSemilattice) which itself implies validity
  of le/eq constraints over universes in [𝐙+∞] and [𝐙], but is *not* equivalent to
  it (see counterexamples in [Deciders]).
  To get a sound and complete algorithm for [𝐙], we use satisfiability checking of
  the inverse clause.
  For [(𝐍, 0, S, Nat.max)], we impose invariants on constraints and the model so that
  it always includes the distinguished [0] level and each other level is bounded below
  by [0] (1 for global levels). One can shift valuations from [𝐙] to [𝐍], with the guarantee
  that the [0] level is always mapped to [0%nat].
  The same checking algorithm as for [𝐙] provides decidable entailment for
  the [𝐍] theory. *)

From Stdlib Require Import ssreflect ssrfun ssrbool.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils NonEmptyLevelExprSet SemiLattice.
From MetaRocq.Common Require Import UnivConstraintType Universes.
From MetaRocq.Common.LoopChecking Require Import Common Interfaces Deciders.
From Equations Require Import Equations.
Set Equations Transparent.

Import Universes.

Module MoreLevel.
  Import Universes.
  Include Level.
  Definition to_string := string_of_level.

  Definition zero := Level.lzero.
  Definition is_global l :=
    match l with
    | Level.lvar _ | Level.lzero => false
    | Level.level _ => true
    end.

  Lemma is_global_zero : ~~ is_global zero.
  Proof. reflexivity. Qed.
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
    intros x x' H1 y y' H2; now rw H1 H2.
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

  Lemma reflect_eq : ReflectEq t.
  Proof.
    refine {| eqb := equal |}.
    intros x y. have := (equal_spec x y).
    destruct equal => //; constructor.
    now apply eq_leibniz, H.
    intros ->. destruct H. now forward H0 by reflexivity.
  Qed.
End LevelExprZSet.
Module LevelExprZSetFacts := WFactsOn LevelExprZ LevelExprZSet.
Module LevelExprZSetProp := MSetProperties.OrdProperties LevelExprZSet.

Module LS (* <: LevelSets *).
  Module Level := MoreLevel.
  Module LevelSet := LevelSet.
  Module LevelExpr := LevelExprZ.
  Module LevelExprSet := LevelExprZSet.
  Module LevelMap := LevelMap.
  Module NES := NonEmptyLevelExprSet MoreLevel Q LevelSet LevelExprZ LevelExprZSet.
End LS.

Definition to_levelexprzset (u : LevelExprSet.t) : LS.LevelExprSet.t :=
  LevelExprSet.fold (fun '(l, k) => LS.LevelExprSet.add (l, Z.of_nat k)) u LS.LevelExprSet.empty.

Lemma to_levelexprzset_spec_1 u :
  forall l k, LevelExprSet.In (l, k) u -> LevelExprZSet.In (l, Z.of_nat k) (to_levelexprzset u).
Proof.
  intros l k.
  rw /to_levelexprzset.
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
  rw /to_levelexprzset.
  apply LevelExprSetProp.fold_rec.
  - now move=> s' hs' /LevelExprZSetFacts.empty_iff.
  - move=> x a s' s'' hin hnin hadd ih.
    destruct x as [l' k'].
    rw LS.LevelExprSet.add_spec => -[].
    + intros [= -> eq]. subst k. split. apply hadd. now left. lia.
    + intros hin'. move: (ih hin') => []; split => //. apply hadd; now right.
Qed.

Definition from_levelexprzset (u : LS.LevelExprSet.t) : LevelExprSet.t :=
  LS.LevelExprSet.fold (fun '(l, k) => LevelExprSet.add (l, Z.to_nat k)) u LevelExprSet.empty.

Lemma from_levelexprzset_spec u :
  forall l k, LevelExprZSet.In (l, k) u -> LevelExprSet.In (l, Z.to_nat k) (from_levelexprzset u).
Proof.
  intros l k.
  rw /from_levelexprzset.
  apply LevelExprZSetProp.P.fold_rec.
  - now move=> s' hs' /hs'.
  - move=> x a s' s'' hin hnin hadd ih /hadd [].
    * intros ->. apply LevelExprSet.add_spec. now left.
    * intros hin'. destruct x. apply LevelExprSet.add_spec. now right.
Qed.

Lemma from_levelexprzset_spec_2 u :
  forall l k, LevelExprSet.In (l, k) (from_levelexprzset u) ->
  exists z, LevelExprZSet.In (l, z) u /\ k = Z.to_nat z.
Proof.
  intros l k.
  rw /from_levelexprzset.
  apply LevelExprZSetProp.P.fold_rec.
  - now move=> s' hs' /LevelExprSetFact.empty_iff.
  - move=> x a s' s'' hin hnin hadd ih.
    destruct x as [l' k'].
    rw LevelExprSet.add_spec => -[].
    + intros [= -> eq]. subst k. exists k'. split => //. apply hadd. now left.
    + intros hin'. move: (ih hin') => [z [hin'' ->]]. exists z. split => //.
      apply hadd. now right.
Qed.

Module UnivLoopChecking.
  Module LoopCheck := LoopChecking LS.
  Import LoopCheck.Impl.Abstract.
  Import LoopCheck.Impl.I.
  Import Universes (valuation).
  Import LoopCheck.

  Definition to_atom '(l, k) : LevelExpr.t := (l, Z.of_nat k).

  Program Definition to_atoms (u : Universe.t) : NES.t :=
    {| NES.t_set := to_levelexprzset u |}.
  Next Obligation.
    destruct u. cbn.
    destruct (LevelExprZSet.is_empty _) eqn:he => //.
    apply LevelExprZSet.is_empty_spec in he.
    assert (Universes.LevelExprSet.is_empty t_set0).
    apply Universes.LevelExprSet.is_empty_spec. intros x hin.
    destruct x. eapply (he (t0, Z.of_nat n)).
    now apply to_levelexprzset_spec_1.
    congruence.
  Qed.

  Lemma to_atoms_singleton l k  : to_atoms (Universe.singleton (l, k)) = NES.singleton (l, Z.of_nat k).
  Proof.
    apply NES.equal_exprsets.
    rw /to_atoms //=.
  Qed.

  Lemma to_atoms_add le u : to_atoms (Universe.add le u) = NES.add (to_atom le) (to_atoms u).
  Proof. apply NES.equal_exprsets => //=.
    move=> [l k].
    rw LevelExprSet.add_spec.
    split.
    - move/to_levelexprzset_spec_2 => [].
      rw Universes.LevelExprSet.add_spec => -[<-|hin].
      * move=> pos.
        left. cbn. lia_f_equal.
      * move=> pos. right.
        apply to_levelexprzset_spec_1 in hin.
        rw Z2Nat.id // in hin.
    - move=> [eq|hin].
      destruct le; noconf eq.
      * apply to_levelexprzset_spec_1.
        rw Universes.LevelExprSet.add_spec.
        now left.
      * apply to_levelexprzset_spec_2 in hin as [hin pos].
        have [k' eq] : exists z, Z.of_nat z = k. exists (Z.to_nat k).
        rw Z2Nat.id //. subst k.
        apply to_levelexprzset_spec_1.
        rw Nat2Z.id in hin.
        rw Universes.LevelExprSet.add_spec. now right.
  Qed.

  Program Definition from_atoms (u : NES.t) : Universe.t :=
    {| Universe.t_set := from_levelexprzset (NES.t_set u) |}.
  Next Obligation.
    apply Universe.NES.not_Empty_is_empty => he.
    eapply (NES.not_Empty_is_empty u). apply t_ne.
    intros [] hin.
    apply from_levelexprzset_spec in hin. now apply he in hin.
  Qed.

  Definition from_atom (le : LevelExprZ.t) := (le.1, Z.to_nat le.2).

  Lemma from_atoms_singleton l k  : from_atoms (singleton (l, k)) = Universe.singleton (l, Z.to_nat k).
  Proof.
    apply Universe.equal_exprsets.
    rw /from_atoms //=.
  Qed.

  Lemma from_atoms_add le u : from_atoms (NES.add le u) = Universe.add (from_atom le) (from_atoms u).
  Proof. apply Universe.equal_exprsets => //=.
    move=> [l k].
    rw Universes.LevelExprSet.add_spec.
    split.
    - move/from_levelexprzset_spec_2 => [] z.
      rw LevelExprZSet.add_spec => -[[<-|hin] eq]. subst k.
      * left. cbn. lia_f_equal. rw /from_atom. now cbn.
      * right. subst.
        now apply from_levelexprzset_spec in hin.
    - move=> [eq|hin].
      * destruct le; noconf eq.
        apply from_levelexprzset_spec. cbn.
        apply LevelExprZSet.add_spec.
        now left.
      * apply from_levelexprzset_spec_2 in hin as [hin [pos eq]]. subst k.
        apply from_levelexprzset_spec.
        apply LevelExprZSet.add_spec. now right.
  Qed.

Module ZUnivConstraint.
  Definition t : Type := NES.t * ConstraintType.t * NES.t.

  Definition eq : t -> t -> Prop := Logic.eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition make l1 ct l2 : t := (l1, ct, l2).

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t (l2 l2' : NES.t) : LevelExprSet.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 (l1 l1' : NES.t) t t' l2 l2' : LevelExprSet.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Derive Signature for lt_.
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X; subst;
        try (eapply LevelExprSet.lt_strorder; eassumption).
      eapply ConstraintType.lt_strorder; eassumption.
    - intros ? ? ? X Y; invs X; invs Y; constructor; tea.
      etransitivity; eassumption.
      2: etransitivity; eassumption.
      eapply ConstraintType.lt_strorder; eassumption.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare : t -> t -> comparison :=
    fun '(l1, t, l2) '(l1', t', l2') =>
      compare_cont (LevelExprSet.compare l1 l1')
        (compare_cont (ConstraintType.compare t t')
                    (LevelExprSet.compare l2 l2')).

  Lemma universe_eq (x y : Universe.t) : Universe.t_set x = Universe.t_set y -> x = y.
  Proof.
    apply Universe.eq_univ.
  Qed.

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x as [[l1 t] l2], y as [[l1' t'] l2']; cbn.
    destruct (LevelExprSet.compare_spec l1 l1'); cbn; repeat constructor; tas.
    eapply LevelExprSet.eq_leibniz, eq_univ in H. subst l1'.
    destruct (ConstraintType.compare_spec t t'); cbn; repeat constructor; tas.
    invs H.
    destruct (LevelExprSet.compare_spec l2 l2'); cbn; repeat constructor; tas.
    eapply LevelExprSet.eq_leibniz, eq_univ in H. now subst l2'.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. decide equality; apply Classes.eq_dec.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End ZUnivConstraint.

  Module ZUnivConstraintSet := MSetAVL.Make ZUnivConstraint.
  Module ZUnivConstraintSetFact := WFactsOn ZUnivConstraint ZUnivConstraintSet.
  Module ZUnivConstraintSetOrdProp := MSetProperties.OrdProperties ZUnivConstraintSet.
  Module ZUnivConstraintSetProp := ZUnivConstraintSetOrdProp.P.
  Module ZUnivConstraintSetDecide := WDecide ZUnivConstraintSet.
  Ltac zucsets := ZUnivConstraintSetDecide.fsetdec.

  Definition of_z_constraints (x : ZUnivConstraintSet.t) : Clauses.t :=
    ZUnivConstraintSet.fold (fun c cls =>
      Clauses.union (LoopCheck.to_clauses c) cls) x Clauses.empty.

  Lemma of_z_constraints_spec {cstrs} :
    forall cl, Clauses.In cl (of_z_constraints cstrs) <->
      (exists cstr, ZUnivConstraintSet.In cstr cstrs /\
        Clauses.In cl (LoopCheck.to_clauses cstr)).
  Proof.
    rw /of_z_constraints.
    eapply ZUnivConstraintSetProp.fold_rec.
    - intros s' he cl; split. clsets.
      intros [cstr [hin ?]]. firstorder.
    - intros x a s' s'' hin hnin hadd h cl.
      rw Clauses.union_spec h.
      split.
      * intros []. exists x. split => //. apply hadd. now left.
        firstorder.
      * intros [cstr [hin' incl]].
        apply hadd in hin' as [].
        + subst. now left.
        + right. exists cstr. split => //.
  Qed.

  Definition to_constraint (x : UnivConstraint.t) : LoopCheck.constraint :=
    let '(l, d, r) := x in
    (to_atoms l, d, to_atoms r).

  Definition to_clauses (x : UnivConstraintSet.t) : Clauses.t :=
    UnivConstraintSet.fold (fun c cls =>
      Clauses.union (LoopCheck.to_clauses (to_constraint c)) cls) x Clauses.empty.

  Lemma to_clauses_spec {cstrs} :
    forall cl, Clauses.In cl (to_clauses cstrs) <->
      (exists cstr, UnivConstraintSet.In cstr cstrs /\
        Clauses.In cl (LoopCheck.to_clauses (to_constraint cstr))).
  Proof.
    rw /to_clauses.
    eapply UnivConstraintSetProp.fold_rec.
    - intros s' he cl; split. clsets.
      intros [cstr [hin ?]]. firstorder.
    - intros x a s' s'' hin hnin hadd h cl.
      rw Clauses.union_spec h.
      split.
      * intros []. exists x. split => //. apply hadd. now left.
        firstorder.
      * intros [cstr [hin' incl]].
        apply hadd in hin' as [].
        + subst. now left.
        + right. exists cstr. split => //.
  Qed.

  Definition to_z_cstrs cstrs :=
    UnivConstraintSet.fold (fun c acc => ZUnivConstraintSet.add (to_constraint c) acc)
      cstrs ZUnivConstraintSet.empty.

  Lemma to_z_cstrs_spec_1 {cstrs} :
    forall c, UnivConstraintSet.In c cstrs ->
      (exists cstrz, ZUnivConstraintSet.In cstrz (to_z_cstrs cstrs) /\
       cstrz = to_constraint c).
  Proof.
    rw /to_z_cstrs.
    eapply UnivConstraintSetProp.fold_rec.
    - now move=> s' he c /he.
    - intros x a s' s'' hin hnin hadd h cl.
      rws ZUnivConstraintSet.add_spec => /hadd [].
      * intros ->. eexists; split => //. now left.
      * move/h => [cstr [hin' incl]]. subst cstr.
        exists (to_constraint cl). firstorder.
  Qed.

  Lemma to_z_cstrs_spec_2 {cstrs} :
    forall c, ZUnivConstraintSet.In c (to_z_cstrs cstrs) ->
      (exists cstr, UnivConstraintSet.In cstr cstrs /\
       c = to_constraint cstr).
  Proof.
    rw /to_z_cstrs.
    eapply UnivConstraintSetProp.fold_rec.
    - move=> s' he c. zucsets.
    - intros x a s' s'' hin hnin hadd h c.
      rw ZUnivConstraintSet.add_spec => -[].
      * intros ->. eexists; split => //. apply hadd. now left.
      * move/h => [cstr [hin' incl]]. subst c.
        exists cstr. firstorder.
  Qed.

  Lemma to_clauses_of_z_constraints {cstrs} :
    to_clauses cstrs =_clset of_z_constraints (to_z_cstrs cstrs).
  Proof.
    intros l.
    rw to_clauses_spec of_z_constraints_spec.
    split.
    - intros [cstr [hin hin']].
      exists (to_constraint cstr). split.
      apply to_z_cstrs_spec_1 in hin as [cstrz []].
      now subst cstrz.
      assumption.
    - intros [cstr [hin hin']].
      apply to_z_cstrs_spec_2 in hin as [cstr' [hin ->]].
      exists cstr'. split => //.
  Qed.


  Module Clauses := LoopCheck.Impl.I.Model.Model.Clauses.Clauses.

  Definition U0 : Universe.t := Universe.make (Level.lzero, 0%nat).
  Definition U1 : Universe.t := Universe.singleton LevelExpr.type1.

  Definition init_constraint_of_level l :=
    match l with
    | Level.lzero => None
    | Level.level s => Some (U1, ConstraintType.Le, Universe.singleton (l, 0%nat))
    | Level.lvar n => Some (U0, ConstraintType.Le, Universe.singleton (l, 0%nat))
    end.

  Definition declared_init_constraint_of_level l cstrs :=
    match init_constraint_of_level l with
    | None => True
    | Some c => UnivConstraintSet.In c cstrs
    end.
  Record univ_model := {
    model :> LoopCheck.t;
    constraints : UnivConstraintSet.t;
    repr_constraints : forall c, UnivConstraintSet.In c constraints ->
      Clauses.Subset (LoopCheck.to_clauses (to_constraint c)) (LoopCheck.Impl.Abstract.clauses model);
    repr_constraints_inv : forall cl, Clauses.In cl (LoopCheck.Impl.Abstract.clauses model) ->
      exists c, UnivConstraintSet.In c constraints /\ Clauses.In cl (LoopCheck.to_clauses (to_constraint c));
    repr_init : forall l c, LevelSet.In l (LoopCheck.levels model) -> init_constraint_of_level l = Some c -> UnivConstraintSet.In c constraints
      }.

  Definition levels m := (LoopCheck.levels m.(model)).

  Lemma declared_zero (m : univ_model) : LevelSet.In Level.lzero (levels m).
  Proof.
    apply zero_declared_in_levels.
  Qed.

  Module C := LoopCheck.Impl.I.Model.Model.Clauses.
  Import C.

  Lemma exists_to_atoms a u :
    LevelExprSet.Exists (fun lk : LevelExprSet.elt => a = lk) (to_atoms u) ->
    Universes.LevelExprSet.Exists (fun lk => a = (fst lk, Z.of_nat (snd lk))) u.
  Proof.
    rw /to_atoms; cbn; move=> [] [l k] [] hin ->.
    move/to_levelexprzset_spec_2: hin => [] hin hpos.
    exists (l, Z.to_nat k). split => //=.
    rw Z2Nat.id //.
  Qed.

  Lemma in_to_atoms a u :
    LevelExprSet.In (a.1, Z.of_nat a.2) (to_atoms u) <-> Universes.LevelExprSet.In a u.
  Proof.
    destruct a as [l k].
    rw /to_atoms //=.
    split.
    - move/to_levelexprzset_spec_2 => [] hin _.
      now rw Nat2Z.id in hin.
    - now move/to_levelexprzset_spec_1.
  Qed.

  Lemma levels_in_to_atoms l u :
    LevelSet.In l (NES.levels (to_atoms u)) <-> Universes.LevelSet.In l (Universe.levels u).
  Proof.
    rw levels_spec.
    rw /in_to_atoms.
    split.
    - move=> [] k. move/to_levelexprzset_spec_2 => [] hin _.
      apply Universe.levels_spec. now eexists.
    - rw Universe.levels_spec => -[] k hin.
      exists (Z.of_nat k). now rw (in_to_atoms (l, k)).
  Qed.

  Lemma exists_to_atoms_spec f u :
    LevelExprSet.Exists f (to_atoms u) <->
    exists le, Universes.LevelExprSet.In le u /\ f (to_atom le).
  Proof.
    rw /to_atoms //=; split; rw /LevelExprSet.Exists.
    - move=> [] [] l k [] /to_levelexprzset_spec_2 [] hin hpos hf.
      eexists; split; tea. cbn. rw Z2Nat.id //.
    - move=> [] [] l k [] hin hf. exists (l, Z.of_nat k); split => //.
      now apply to_levelexprzset_spec_1.
    Qed.

  Lemma exists_to_atoms_2 a (u : Universe.t) :
    Universes.LevelExprSet.Exists (fun lk => a = lk) u ->
    LevelExprSet.Exists (fun lk : LevelExprSet.elt => a = (lk.1, Z.to_nat lk.2)) (to_atoms u).
  Proof.
    rw /to_atoms; cbn; move=> [] [l k] [] hin ->.
    move/to_levelexprzset_spec_1: hin => hin.
    exists (l, Z.of_nat k). split => //=.
    rw Nat2Z.id //.
  Qed.

  Definition relation_of_constraint (c : ZUnivConstraint.t) :=
    let '(l, d, r) := c in
    match d with
    | ConstraintType.Le => ((l ∪ r)%nes, r)
    | ConstraintType.Eq => (l, r)
    end.

  Definition Zuniv_constraint_levels (c : ZUnivConstraint.t) :=
    let '(l, d, r) := c in
    LevelSet.union (NES.levels l) (NES.levels r).

  Definition relations_of_constraints c :=
    ZUnivConstraintSet.fold (fun c acc => relation_of_constraint c :: acc) c [].

  Lemma relations_of_constraints_spec {r cstrs} : List.In r (relations_of_constraints cstrs) <->
    exists cl, ZUnivConstraintSet.In cl cstrs /\ r = relation_of_constraint cl.
  Proof.
    rw /relations_of_constraints.
    eapply ZUnivConstraintSetProp.fold_rec.
    - move=> s' he; split => //.
      intros [cl []]. now apply he in H.
    - move=> x a s' s'' hni hnin hadd.
      split.
      { cbn. move=> [] h.
        * exists x. split => //. apply hadd. now left.
        * apply H in h as [cl []]; eexists; split; tea. apply hadd. now right. }
      { move=> [] cl [] /hadd[].
        * intros -> ->. now left.
        * intros hin heq. right; apply H. exists cl; split => //. }
  Qed.

  Definition levels_of_z_constraints c :=
    ZUnivConstraintSet.fold (fun c acc => LevelSet.union (Zuniv_constraint_levels c) acc) c LevelSet.empty.

  Import ISL.

  Lemma equiv_L_rels_eq {l r} :
    [l ≡ r] ⊫ℒ relations_of_clauses (clauses_of_le l r) ++ relations_of_clauses (clauses_of_le r l).
  Proof.
    rw /clauses_of_eq. split.
    - apply app_Forall.
      * apply Forall_forall => rel.
        have [he he'] := entails_L_relations_of_clauses_le l r.
        red in he, he'.
        rw Forall_forall in he'. move/he'.
        intros ent. destruct rel.
        eapply entails_L_all_one_trans; tea.
        constructor. apply entails_L_eq_le_1, entails_c; repeat constructor. constructor.
      * apply Forall_forall => rel.
        have [he he'] := entails_L_relations_of_clauses_le r l.
        red in he, he'.
        rw Forall_forall in he'. move/he'.
        intros ent. destruct rel.
        eapply entails_L_all_one_trans; tea.
        constructor. apply entails_L_eq_le_2, entails_c; repeat constructor. constructor.
    - constructor; [|constructor].
      apply entails_L_eq_antisym. split.
      * have [he he'] := entails_L_relations_of_clauses_le l r.
        eapply entails_L_rels_subset. depelim he. tea.
        red. intros r' hin. rw in_app_iff. now left.
      * have [he he'] := entails_L_relations_of_clauses_le r l.
        eapply entails_L_rels_subset. depelim he. tea.
        red. intros r' hin. rw in_app_iff. now right.
  Qed.

  Lemma entails_L_relations_of_clauses_eq l r :
    relations_of_clauses (l ≡ r) ⊫ℒ [l ≡ r].
  Proof.
    split.
    - constructor. apply entails_L_relations_of_clauses_eq. constructor.
    - apply Forall_forall => rel.
      move/relations_of_clauses_spec => [] prems [] concl [] hin ->.
      move: hin; rw /clauses_of_eq Clauses.union_spec => -[] hin.
      * setoid_rewrite equiv_L_rels_eq.
        eapply entails_L_rels_subset; revgoals.
        { intros rel'. rw in_app_iff. left. tea. }
        now eapply entails_L_in_cls.
      * setoid_rewrite equiv_L_rels_eq.
        eapply entails_L_rels_subset; revgoals.
        { intros rel'. rw in_app_iff. right. tea. }
        now eapply entails_L_in_cls.
  Qed.

  Lemma relation_of_constraint_of_clause cstr :
    relations_of_clauses (LoopCheck.to_clauses cstr) ⊫ℒ [relation_of_constraint cstr].
  Proof.
    destruct cstr as [[l []] r]. cbn.
    apply entails_L_relations_of_clauses_le.
    apply entails_L_relations_of_clauses_eq.
  Qed.

  Lemma of_z_constraints_subset {cstrs cstrs'} :
    ZUnivConstraintSet.Subset cstrs cstrs' ->
    of_z_constraints cstrs ⊂_clset of_z_constraints cstrs'.
  Proof.
    move=> hsub cl /of_z_constraints_spec => -[] cstr [] hin incl.
    rw of_z_constraints_spec. exists cstr. split => //. now apply hsub.
  Qed.

  Lemma of_z_constraints_add x s :
    of_z_constraints (ZUnivConstraintSet.add x s) =_clset Clauses.union (LoopCheck.to_clauses x) (of_z_constraints s).
  Proof.
    move=> cl; split.
    - move/of_z_constraints_spec => -[] cstr [] hin incl.
      rw Clauses.union_spec. rw ZUnivConstraintSet.add_spec in hin.
      move: hin => [<-|]. now left.
      move=> ins. right. rw of_z_constraints_spec. exists cstr; split => //; now right.
    - rw Clauses.union_spec => -[]; destruct x as [[l []] r].
      * move/LoopCheck.to_clauses_spec => [] k [hin] ->.
        rw of_z_constraints_spec. eexists; split => //.
        rw ZUnivConstraintSet.add_spec; left; trea.
        cbn. now eapply in_clause_of_le.
      * intros hcl; rw of_z_constraints_spec //. eexists; split.
        rw ZUnivConstraintSet.add_spec; left; trea. exact hcl.
      * rw of_z_constraints_spec => -[] cstr [] hin heq.
        rw of_z_constraints_spec. exists cstr. split => //.
        rw ZUnivConstraintSet.add_spec; now right.
      * rw of_z_constraints_spec => -[] cstr [] hin heq.
        rw of_z_constraints_spec. exists cstr. split => //.
        rw ZUnivConstraintSet.add_spec; now right.
  Qed.

  Lemma relations_of_clauses_constraints_add {x s} :
    (relation_of_constraint x :: relations_of_clauses (of_z_constraints s)) ⊫ℒ
      (relations_of_clauses (of_z_constraints (ZUnivConstraintSet.add x s))).
  Proof.
    rw of_z_constraints_add relations_of_clauses_union.
    eapply (entails_L_all_union (x := [_])).
    2:{ reflexivity. }
    now rw relation_of_constraint_of_clause.
  Qed.

  Lemma rels_of_z_constraints_spec {cstrs} :
    relations_of_clauses (of_z_constraints cstrs) ⊫ℒ relations_of_constraints cstrs.
  Proof.
    rw /relations_of_constraints.
    have he := ZUnivConstraintSetProp.fold_rec
      (P := fun s f => relations_of_clauses (of_z_constraints s) ⊫ℒ f). apply: he.
    - split. constructor. red. apply Forall_forall => [] l r.
      eapply relations_of_clauses_spec in r as [prems [concl [hin heq]]]. subst l.
      eapply of_z_constraints_spec in hin as [cstr [hin ]]. now apply H in hin.
    - move=> x a s' s'' hin hnin hadd hr.
      rw entails_equiv_cons.
      split; [|split] => //.
      * have hins'' : ZUnivConstraintSet.In x s''.
        { apply hadd; now left. }
        rw -relation_of_constraint_of_clause.
        apply entails_L_clauses_subset_all.
        move=> cl incl. apply of_z_constraints_spec. now exists x.
      * have ha := @entails_L_clauses_subset_all (of_z_constraints s') (of_z_constraints s'').
        transitivity (relations_of_clauses (of_z_constraints s')) => //.
        apply ha. apply of_z_constraints_subset => ? hin'. apply hadd. now right.
        apply hr.
      * destruct hr.
        transitivity (relation_of_constraint x :: relations_of_clauses (of_z_constraints s')).
        apply entails_L_clauses_cons. now apply entails_L_c; constructor.
        now eapply (entails_L_all_weaken (w:=[_])).
        clear -hadd; intros.
        rw relations_of_clauses_constraints_add.
        eapply entails_L_clauses_subset_all.
        eapply of_z_constraints_subset.
        apply ZUnivConstraintSetProp.Add_Equal in hadd. now rw hadd.
  Qed.

  Lemma equiv_constraints_clauses m :
    relations_of_constraints (to_z_cstrs (constraints m)) ⊫ℒ
    Clauses.relations_of_clauses (LoopCheck.clauses (UnivLoopChecking.model m)).
  Proof.
    have repr := repr_constraints.
    have repr_inv := repr_constraints_inv.
    rw -rels_of_z_constraints_spec.
    rw -to_clauses_of_z_constraints.
    rw (@relations_of_clauses_eq (to_clauses (constraints m))
      (LoopCheck.clauses m)) //.
    2:{ reflexivity. }
    intros cl. rw UnivLoopChecking.to_clauses_spec.
    split.
    - move=> [] cstrs [] /repr incl intocl.
      apply incl, intocl.
    - now move/repr_inv.
  Qed.
  (** Equivalence of interpretations between constraints and relations derived from them *)

  Import Semilattice.
  (** Lifting interpretation to constraints (on Z). *)

  Section interp.
    Import Semilattice.
    Context {S : Type} {SL : Semilattice S Z}.
    Context (v : Level.t -> S).

    Definition interp_z_cstr c :=
      let '(l, d, r) := c in
      match d with
      | ConstraintType.Le => interp_nes v l ≤ interp_nes v r
      | ConstraintType.Eq => interp_nes v l ≡ interp_nes v r
      end%Z.

    Definition interp_univ_cstr c := interp_z_cstr (to_constraint c).
    Definition interp_univ_cstrs c := UnivConstraintSet.For_all interp_univ_cstr c.

  End interp.

  Lemma interp_univ_cstrs_relations {S} {SL : Semilattice S Z} (v : Level.t -> S) cstrs :
    interp_univ_cstrs v cstrs <->
    interp_rels v (relations_of_constraints (to_z_cstrs cstrs)).
  Proof.
    rw /interp_univ_cstrs.
    split.
    - intros hf. red in hf. red.
      apply Forall_forall. move=> [l r] /relations_of_constraints_spec [[[l' d] r'] [hin heq]].
      cbn in heq; noconf heq. destruct d; noconf heq.
      * eapply to_z_cstrs_spec_2 in hin as [cstr [hin heq]].
        destruct cstr as [[] ?]; noconf heq. specialize (hf _ hin). cbn in hf.
        rw /interp_rel interp_nes_union; cbn in *. exact hf.
      * eapply to_z_cstrs_spec_2 in hin as [cstr [hin heq]].
        destruct cstr as [[] ?]; noconf heq. specialize (hf _ hin). cbn in hf.
        exact hf.
    - intros hi uc hin. red in hi. rw Forall_forall in hi.
      move: (hi (relation_of_constraint (to_constraint uc))) => /fwd.
      rw relations_of_constraints_spec; exists (to_constraint uc); split => //.
      now apply to_z_cstrs_spec_1 in hin as [cstrz [hin ->]].
      destruct uc as [[l []] r] => //=.
      rw interp_nes_union //=.
  Qed.

  Lemma interp_cstr_clauses_sem {c} {S} {SL : Semilattice S Q.t} {v : Level.t -> S} :
    interp_univ_cstr v c <-> clauses_sem v (LoopCheck.to_clauses (to_constraint c)).
  Proof.
    rw interp_rels_clauses_sem.
    rw relation_of_constraint_of_clause.
    rw /Clauses.ISL.interp_rels Forall_tip.
    destruct c as [[l []] r]; cbn => //.
    now rw interp_nes_union.
  Qed.

  Lemma interp_cstrs_clauses_sem {m} {S} {SL : Semilattice S Q.t} {v : Level.t -> S} :
    interp_univ_cstrs v (constraints m) <-> clauses_sem v (LoopCheck.clauses m).
  Proof.
    rw interp_univ_cstrs_relations.
    rw interp_rels_clauses_sem.
    now rw -[Clauses.relations_of_clauses _]equiv_constraints_clauses.
  Qed.

  Equations? init_model : univ_model :=
  init_model := {| model := LoopCheck.init_model;
                   constraints := UnivConstraintSet.empty |}.
  Proof.
    - move: H. now rw UnivConstraintSetFact.empty_iff.
    - move: H. now rw ClausesFact.empty_iff.
    - eapply LevelSet.singleton_spec in H. subst l. noconf H0.
  Qed.

  Lemma init_model_levels : levels init_model = LevelSet.singleton (Level.zero).
  Proof. now cbn. Qed.

  Lemma init_model_constraints : constraints init_model = UnivConstraintSet.empty.
  Proof. now cbn. Qed.

  Local Obligation Tactic := idtac.

  Equations? enforce m (c : UnivConstraint.t) : option _ :=
    enforce m c with inspect (LoopCheck.enforce m.(model) (to_constraint c)) :=
      | exist None eq => None
      | exist (Some (inl m')) eq => Some (inl {| model := m'; constraints := UnivConstraintSet.add c m.(constraints) |})
      | exist (Some (inr loop)) eq => Some (inr loop).
  Proof.
    - move=> c'.
      move/LoopCheck.enforce_clauses: eq0.
      rw /LoopCheck.clauses => ->. rw UnivConstraintSet.add_spec => -[].
      * move=> ->. clsets.
      * move=> hin.
        move: (repr_constraints m c' hin) => h. clsets.
    - move/LoopCheck.enforce_clauses: eq0.
      rw /LoopCheck.clauses => -> c'.
      rw UnivLoopChecking.Clauses.Clauses.union_spec => -[].
      * move/(repr_constraints_inv m c') => [] c2 [].
        exists c2. split => //.
        rw UnivConstraintSet.add_spec. now right.
      * move=> hin. exists c. split => //.
        rw UnivConstraintSet.add_spec. now left.
    - intros l c' hin hc'. apply UnivConstraintSet.add_spec. right. eapply repr_init; tea.
      apply enforce_levels in eq0. now rw -eq0.
  Qed.

  Definition univ_constraint_levels (c : UnivConstraint.t) :=
    let '(l, d, r) := c in
    LevelSet.union (Universe.levels l) (Universe.levels r).

  Lemma declared_univ_cstr_levels_spec ls c :
    declared_univ_cstr_levels ls c <->
    univ_constraint_levels c ⊂_lset ls.
  Proof.
    destruct c as [[l d] r].
    rw /declared_univ_cstr_levels /univ_constraint_levels.
    split.
    - move=> [] hl hr l'.
      rw LevelSet.union_spec. firstorder.
    - intros he; split => l'. specialize (he l').
      rw LevelSet.union_spec in he. firstorder.
      specialize(he l'). rw LevelSet.union_spec in he. firstorder.
  Qed.

  Definition constraint_levels (c : LoopCheck.constraint) :=
    LevelSet.union (NES.levels c.1.1) (NES.levels c.2).

  Lemma in_constraint_levels_to_constraint c :
    forall l, LevelSet.In l (constraint_levels (to_constraint c)) <->
      LevelSet.In l (univ_constraint_levels c).
  Proof.
    intros l; destruct c as [[l' d] r]; cbn.
    rw /constraint_levels. rw !LevelSet.union_spec. cbn.
    rw !levels_in_to_atoms. firstorder.
  Qed.

  Lemma in_to_clauses_levels c :
    forall l, LevelSet.In l (clauses_levels (LoopCheck.to_clauses c)) <->
      LevelSet.In l (constraint_levels c).
  Proof.
    intros l.
    destruct c as [[l' []] r] => //=; revgoals.
    - rw clauses_levels_union LevelSet.union_spec.
      rw /constraint_levels //= LevelSet.union_spec.
      rw !in_clause_levels_of_le. firstorder.
    - rw /constraint_levels //= LevelSet.union_spec.
      rw !in_clause_levels_of_le. firstorder.
  Qed.

  Lemma ndecl_nin_levels ls c :
    declared_univ_cstr_levels ls c <->
    clauses_levels (LoopCheck.to_clauses (to_constraint c)) ⊂_lset ls.
  Proof.
    rw declared_univ_cstr_levels_spec.
    split; intros h.
    - intros ?; rw in_to_clauses_levels in_constraint_levels_to_constraint. apply h.
    - etransitivity; tea. intros ?.
      now rw in_to_clauses_levels in_constraint_levels_to_constraint.
  Qed.

  Lemma enforce_not_none m c : enforce m c <> None <->
    declared_univ_cstr_levels (LoopCheck.levels (model m)) c.
  Proof.
    have := @LoopCheck.enforce_not_None (model m) (to_constraint c).
    rw /enforce.
    destruct inspect as [[[] | ] eq]. simpl.
    - intros. split => // _.
      rw ndecl_nin_levels. apply H. now rw eq.
    - intros. split => // _.
      rw ndecl_nin_levels. apply H. now rw eq.
    - intros. split => //=.
      now move/ndecl_nin_levels/H; rw eq.
  Qed.

  Lemma enforce_None m c :
    enforce m c = None <-> ~ declared_univ_cstr_levels (LoopCheck.levels m.(model)) c.
  Proof.
    rw /enforce.
    destruct inspect as [[[] | ] eq]. simpl.
    - intros. split => //.
      rw ndecl_nin_levels.
      rw -LoopCheck.enforce_not_None eq; elim. congruence.
    - intros. split => //=.
      rw ndecl_nin_levels.
      rw -LoopCheck.enforce_not_None eq; elim. congruence.
    - cbn. rw ndecl_nin_levels.
      rw -LoopCheck.enforce_not_None eq. split => //. congruence.
  Qed.

  Lemma enforce_model m c m' :
    enforce m c = Some (inl m') -> levels m = levels m' /\
      UnivConstraintSet.Equal (UnivConstraintSet.add c (constraints m)) (constraints m').
  Proof.
    funelim (enforce m c) => //=.
    move=> [=] <-; cbn. rw /levels //=.
    split.
    - clear H Heqcall. now move/LoopCheck.enforce_levels: eq0.
    - clear H Heqcall. reflexivity.
  Qed.

  Definition valuation_to_Z (v : Universes.valuation) : Level.t -> Z :=
    fun l => Z.of_nat (val v l).

  Lemma positive_valuation_to_Z v :
    positive_valuation (valuation_to_Z v).
  Proof.
    unfold positive_valuation, valuation_to_Z. intros; lia.
  Qed.

  Existing Instance Zopt_semi.

  Lemma interp_nes_valuation_to_Z_to_atoms v u :
    interp_nes (valuation_to_Z v) (to_atoms u) = Z.of_nat (Universes.val v u).
  Proof.
    move: u.
    apply: Universe.elim.
    - intros [l k]; rw to_atoms_singleton interp_nes_singleton //= val_singleton //=.
      rw /valuation_to_Z; cbn; lia_f_equal.
    - intros [l k] x hx hnin.
      rw to_atoms_add /valuation_to_Z !interp_nes_add_Z //= val_add //= hx; cbn.
      lia_f_equal.
  Qed.

  Lemma clauses_sem_satisfies0_equiv v cstr : clauses_sem (valuation_to_Z v) (LoopCheck.to_clauses (to_constraint cstr)) <-> satisfies0 v cstr.
  Proof.
    destruct cstr as [[l []] r]; cbn.
    - rw clauses_sem_leq !interp_nes_valuation_to_Z_to_atoms.
      split; cbn.
      * constructor; lia.
      * intros s; depelim s. lia.
    - rw clauses_sem_eq !interp_nes_valuation_to_Z_to_atoms.
      split; cbn.
      * constructor. lia.
      * intros s; depelim s. lia.
  Qed.

  Lemma clauses_sem_satisfies_equiv v cstrs : clauses_sem (valuation_to_Z v) (to_clauses cstrs) <-> satisfies v cstrs.
  Proof.
    unfold to_clauses.
    eapply UnivConstraintSetProp.fold_rec.
    - split; cbn.
      intro cs. red. intros cl hin. ucsets.
      intros cl hin. clsets.
    - intros x a s' s'' hin hnin hadd ih.
      rw clauses_sem_union ih.
      rw clauses_sem_satisfies0_equiv.
      eapply UnivConstraintSetProp.Add_Equal in hadd. rw hadd.
      rw UnivConstraintSetProp.add_union_singleton satisfies_union.
      split => -[]; split => //. red. intros c hin'.
      apply UnivConstraintSet.singleton_spec in hin'. now subst x.
      move: (a0 x) => /fwd. ucsets. trivial.
  Qed.

  Lemma satisfies_clauses_sem_to_Z v {m : univ_model} :
    satisfies v (constraints m) ->
    clauses_sem (valuation_to_Z v) (LoopCheck.clauses (UnivLoopChecking.model m)).
  Proof.
    have repr := repr_constraints_inv m.
    have repr_inv := repr_constraints m.
    move=> hs cl /[dup] hin /repr [] c [] /[dup] /repr_inv hr /hs sat.
    destruct c as [[l' d] r].
    apply clauses_sem_satisfies0_equiv in sat.
    red in sat. now move/sat.
  Qed.
(*
  Lemma interp_nes_valuation_to_Z v u :
    interp_nes (valuation_to_Z v) u <> None.
  Proof.
    move: u.
    apply: NES.elim.
    - intros [l k]. rewrite interp_nes_singleton //= val_singleton //=.
    - intros [l k] x hx hnin.
      rewrite !interp_nes_add_opt_Z //=.
      destruct interp_nes => //.
  Qed. *)

  Lemma enforce_inconsistent m (c : UnivConstraint.t) u :
    UnivLoopChecking.enforce m c = Some (inr u) -> ~ exists v, satisfies v (UnivConstraintSet.add c (constraints m)).
  Proof.
    funelim (UnivLoopChecking.enforce m c) => //=.
    move=> [=]; intros <-; cbn. clear H Heqcall.
    intros [v sat].
    have he := LoopCheck.enforce_inconsistent eq0.
    specialize (he (valuation_to_Z v)).
    forward he. apply positive_valuation_to_Z.
    rw clauses_sem_satisfies0_equiv in he.
    rw UnivConstraintSetProp.add_union_singleton satisfies_union in sat.
    destruct sat as [satc satcs].
    specialize (satc c). forward satc; try ucsets.
    forward he.
    { now apply satisfies_clauses_sem_to_Z. }
    destruct loop0 as [u incl hu]. cbn in he. contradiction.
  Qed.

  (** Enforces a set of constraints at once: the algorithm runs once on the union of the
      clauses of the model and those of the new constraints. (Enforcing them one at a time
      re-runs it on all the clauses each time, which is quadratic in the number of
      constraints.) *)
  Equations? enforce_constraints (m : univ_model) (cstrs : UnivConstraintSet.t) : option univ_model :=
    enforce_constraints m cstrs with
      inspect (LoopCheck.Impl.Abstract.enforce_clauses m.(model) (to_clauses cstrs)) :=
      | exist (Some (inl m')) eq =>
        Some {| model := m'; constraints := UnivConstraintSet.union cstrs m.(constraints) |}
      (* The constraints entail a loop *)
      | exist (Some (inr _)) eq => None
      (* The constraints mention undeclared levels *)
      | exist None eq => None.
  Proof.
    all: have hcls := LoopCheck.Impl.Abstract.enforce_clauses_clauses _ _ _ eq0.
    - move=> c. rw UnivConstraintSet.union_spec => -[hin|hin] cl incl;
      rw hcls Clauses.union_spec.
      * right. apply to_clauses_spec. now exists c.
      * left. now apply (repr_constraints m c hin).
    - move=> cl. rw hcls Clauses.union_spec => -[].
      * move/(repr_constraints_inv m cl) => [c [hin incl]].
        exists c. split => //. rw UnivConstraintSet.union_spec. now right.
      * move/to_clauses_spec => [c [hin incl]].
        exists c. split => //. rw UnivConstraintSet.union_spec. now left.
    - intros l c hin hc. rw UnivConstraintSet.union_spec. right. eapply repr_init; tea.
      apply LoopCheck.Impl.Abstract.enforce_clauses_levels in eq0.
      move: hin. rw /LoopCheck.levels. now rw eq0.
  Qed.

  Lemma enforce_constraints_levels m cstrs m' :
    enforce_constraints m cstrs = Some m' -> levels m' = levels m.
  Proof.
    funelim (enforce_constraints m cstrs) => //= -[= <-].
    exact (LoopCheck.Impl.Abstract.enforce_clauses_levels _ _ _ eq0).
  Qed.

  Lemma enforce_constraints_constraints m cstrs m' :
    enforce_constraints m cstrs = Some m' ->
    constraints m' = UnivConstraintSet.union cstrs (constraints m).
  Proof.
    funelim (enforce_constraints m cstrs) => //= -[= <-]. reflexivity.
  Qed.

  Lemma enforce_constraints_spec {m m' cstrs} :
    enforce_constraints m cstrs = Some m' -> levels m' = levels m /\
      constraints m' =_ucset UnivConstraintSet.union cstrs (constraints m).
  Proof.
    move=> h. split.
    - exact: enforce_constraints_levels h.
    - now rw (enforce_constraints_constraints _ _ _ h).
  Qed.

  Lemma enforce_constraints_None {m cstrs} :
    enforce_constraints m cstrs = None ->
    ~ (declared_univ_cstrs_levels (levels m) cstrs) \/
    ~ (exists v : Universes.valuation, satisfies v (UnivConstraintSet.union cstrs (constraints m))).
  Proof.
    funelim (enforce_constraints m cstrs) => //= _.
    - right. move=> [v /satisfies_union [satc satm]].
      apply: (LoopCheck.Impl.Abstract.enforce_clauses_inconsistent eq0).
      exists (valuation_to_Z v). split; first by apply positive_valuation_to_Z.
      apply clauses_sem_union. split.
      + exact: (satisfies_clauses_sem_to_Z v satm).
      + by apply/clauses_sem_satisfies_equiv.
    - left. move=> hdecl.
      apply: (proj2 (LoopCheck.Impl.Abstract.enforce_clauses_not_None (model m) (to_clauses cstrs)) _ eq0).
      move=> l /clauses_levels_spec [cl [/to_clauses_spec [c [hin incl]] hl]].
      move: (hdecl c hin) => /ndecl_nin_levels; apply.
      apply clauses_levels_spec. now exists cl.
  Qed.

  Lemma satisfies_singleton v x : satisfies v (UnivConstraintSet.singleton x) <-> satisfies0 v x.
  Proof.
    split.
    - move=>/(_ x) => /fwd //. ucsets.
    - move=> sat cl. now rw UnivConstraintSet.singleton_spec => ->.
  Qed.

  Lemma declared_init_constraint_of_level_spec {l c cstrs}:
    init_constraint_of_level l = Some c ->
    declared_init_constraint_of_level l (UnivConstraintSet.add c cstrs).
  Proof.
    rw /declared_init_constraint_of_level => ->. ucsets.
  Qed.

  Lemma declared_init_constraint_of_level_add' {l c cstrs}:
    declared_init_constraint_of_level l cstrs ->
    declared_init_constraint_of_level l (UnivConstraintSet.add c cstrs).
  Proof.
    rw /declared_init_constraint_of_level. destruct init_constraint_of_level => //. ucsets.
  Qed.

  Lemma init_constraint_spec {l c} :
    init_constraint_of_level l = Some c ->
    LoopCheck.to_clauses (to_constraint c) =_clset
    Clauses.singleton (LoopCheck.Impl.init_clause_of_level l).
  Proof.
    intros h.
    destruct l; cbn in h => //; noconf h.
    - intros l. cbn. unfold flip.
      rw Clauses.add_spec. cbn.
      rw /LoopCheck.Impl.init_clause_of_level.
      split. intros []. subst l.
      * apply Clauses.singleton_spec.
        f_equal.
        apply equal_exprsets => le.
        rw /to_atoms //=.
      * clsets.
      * move/Clauses.singleton_spec => -> //=.
        left. f_equal. unfold LevelExprSet.elt, Universes.Level.t.
        f_equal. apply equal_exprsets. rw /to_atoms //=.
    - intros l. cbn. unfold flip.
      rw Clauses.add_spec. cbn.
      rw /LoopCheck.Impl.init_clause_of_level.
      split. intros []. subst l.
      * apply Clauses.singleton_spec.
        f_equal.
        apply equal_exprsets => le.
        rw /to_atoms //=.
      * clsets.
      * move/Clauses.singleton_spec => -> //=.
        left. f_equal. unfold LevelExprSet.elt, Universes.Level.t.
        f_equal. apply equal_exprsets. rw /to_atoms //=.
  Qed.

  Lemma constraints_clauses m :
    forall c, UnivConstraintSet.In c (constraints m) -> Clauses.Subset (LoopCheck.to_clauses (to_constraint c)) (LoopCheck.clauses m).
  Proof.
    move=> c.
    move/repr_constraints => //.
  Qed.

  Definition init_constraints_of_levels ls :=
    LevelSet.fold (fun l cstrs =>
      match init_constraint_of_level l with
      | None => cstrs
      | Some c => UnivConstraintSet.add c cstrs
      end) ls UnivConstraintSet.empty.

  Lemma init_constraints_of_levels_spec ls :
    forall l, LevelSet.In l ls -> forall c, init_constraint_of_level l = Some c -> UnivConstraintSet.In c (init_constraints_of_levels ls).
  Proof.
    unfold init_constraints_of_levels.
    set fn := (fun (l0 : LevelSet.elt) (cstrs : UnivConstraintSet.t) =>
    match init_constraint_of_level l0 with
    | Some c0 => UnivConstraintSet.add c0 cstrs
    | None => cstrs
    end).
    pose P := fun ls f => forall l : LevelSet.elt,
      LevelSet.In l ls ->
      forall c : (Universe.t × ConstraintType.t_) × Universe.t,
      init_constraint_of_level l = Some c -> UnivConstraintSet.In c f.
    change (P ls (LevelSet.fold fn ls UnivConstraintSet.empty)).
    eapply LevelSetProp.fold_rec; subst P; cbn in *.
    - move=> s' he l hin. lsets.
    - move=> x a s' s'' hin hnin hadd ih l hinl c hinit.
      unfold fn.
      destruct (Classes.eq_dec l x).
      * subst. rw hinit. ucsets.
      * destruct (init_constraint_of_level x) eqn:ix.
        eapply UnivConstraintSet.add_spec. right.
        eapply ih; tea. move: (hadd l).
        move=> [] /(_ hinl) [] //=. congruence.
        eapply ih; tea.
        move: (hadd l).
        move=> [] /(_ hinl) [] //=. congruence.
  Qed.

  Lemma init_constraints_of_levels_spec_inv ls :
    forall c, UnivConstraintSet.In c (init_constraints_of_levels ls) ->
    exists l, LevelSet.In l ls /\ init_constraint_of_level l = Some c.
  Proof.
    unfold init_constraints_of_levels.
    eapply LevelSetProp.fold_rec.
    - ucsets.
    - move=> x a s' s'' hin hnin hadd ih c.
      destruct init_constraint_of_level eqn:hi.
      * move/UnivConstraintSet.add_spec => [->|].
        { exists x. split => //. now apply hadd. }
        case/ih => l -[] hin' hinit. exists l. split => //.
        apply hadd. now right.
      * case/ih => l -[] hin' hinit. exists l. split => //.
        apply hadd. now right.
  Qed.

  Instance init_constraints_of_levels_proper : Proper (LevelSet.Equal ==> UnivConstraintSet.Equal) (init_constraints_of_levels).
  Proof.
    intros l l' eqll' cl.
    split.
    - move/init_constraints_of_levels_spec_inv=> -[] i [].
      rw eqll' => hin hinit.
      eapply init_constraints_of_levels_spec; tea.
    - move/init_constraints_of_levels_spec_inv=> -[] i [].
      rw -eqll' => hin hinit.
      eapply init_constraints_of_levels_spec; tea.
  Qed.

  Lemma init_constraints_of_levels_add l c ls :
    init_constraint_of_level l = Some c ->
    init_constraints_of_levels (LevelSet.add l ls) =_ucset UnivConstraintSet.add c (init_constraints_of_levels ls).
  Proof.
    move=> hc cl.
    split.
    - move/init_constraints_of_levels_spec_inv=> -[] i [] /LevelSet.add_spec hin hinit.
      destruct hin; subst.
      * rw hc in hinit; noconf hinit.
        ucsets.
      * apply UnivConstraintSet.add_spec. right.
        eapply init_constraints_of_levels_spec; tea.
    - move/UnivConstraintSet.add_spec => [eq|hin].
      * subst. eapply init_constraints_of_levels_spec. apply LevelSet.add_spec. now left. exact hc.
      * apply init_constraints_of_levels_spec_inv in hin as [l0 []].
        eapply init_constraints_of_levels_spec; tea.
        now apply LevelSet.add_spec; right.
  Qed.

  Lemma declared_init_constraints {m} : forall l,
    LevelSet.In l (levels m) ->
    l = Level.zero \/ exists c, init_constraint_of_level l = Some c /\ UnivConstraintSet.In c (constraints m).
  Proof.
    move=> l.
    destruct (Classes.eq_dec l Level.zero).
    firstorder.
    move/(repr_init m) => h.
    right. destruct l; cbn in *.
    { elim n; reflexivity. }
    specialize (h _ eq_refl).
    eexists; split; trea.
    specialize (h _ eq_refl).
    eexists; split; trea.
  Qed.

  Lemma init_constraints_subset m : (init_constraints_of_levels (levels m)) ⊂_ucset (constraints m).
  Proof.
    move=> l /init_constraints_of_levels_spec_inv; case=> l' [] hin heq.
    now move/repr_init: hin => /(_ _ heq).
  Qed.

  Definition add_opt_cstr (c : option UnivConstraint.t) s :=
    match c with
    | None => s
    | Some c => UnivConstraintSet.add c s
    end.

  Equations? declare_level (m : univ_model) (l : Level.t) : option univ_model :=
  declare_level m l with inspect (LoopCheck.declare_level m.(model) l) :=
  { | exist (Some model) eq with inspect (init_constraint_of_level l) :=
    { | exist (Some c) eqc => Some {| model := model; constraints := UnivConstraintSet.add c m.(constraints) |}
      | exist None eqc => False_rect _ _ } ;
    | exist None eqdecl := None }.
  Proof.
    (* - move/LoopCheck.declare_level_levels: eq0 => -[] hnin.
      move/LoopCheck.enforce_levels: e => eq. rewrite eq. intros ->.
      have := declared_zero m. lsets.
    - move/LoopCheck.declare_level_levels: eq0 => -[] hnin eq l'.
      move/LoopCheck.enforce_levels: e => eq'. rewrite eq'.
      rewrite eq. rewrite LevelSet.add_spec => -[].
      * intros ->. now apply declared_init_constraint_of_level_spec.
      * intros. apply declared_init_constraint_of_level_add'.
        now apply declared_levels. *)
    - move/LoopCheck.declare_level_clauses: eq0 => eqcl.
      intros c'.
      rw UnivConstraintSet.add_spec => -[]; intros h; try subst;
      rw eqcl => l'; rw Clauses.add_spec.
      * rw init_constraint_spec; tea => //.
        rw Clauses.singleton_spec. auto.
      * right.
        now apply (repr_constraints _ _ h).
    - move/LoopCheck.declare_level_clauses: eq0 => ->.
      intros c'. rw Clauses.add_spec.
      move=> [] h.
      * exists c. split => //. ucsets.
        subst c'. rw init_constraint_spec; tea. clsets.
      * have [ec [? ?]] := repr_constraints_inv _ _ h. exists ec.
        split => //. ucsets.

    - intros l' c' hin heq.
      apply UnivConstraintSet.add_spec.
      destruct (Classes.eq_dec l l').
      * subst l'. rw eqc in heq. noconf heq. now left.
      * right.
        move/declare_level_levels: eq0 => [] hnin hl.
        eapply repr_init; tea. rw hl in hin.
        apply LevelSet.add_spec in hin. destruct hin => //. congruence.
    - destruct l; noconf eqc.
      move/declare_level_levels: eq0 => [] hnin _; apply hnin.
      eapply declared_zero.
  Qed.

  Lemma declare_level_None {l m}: declare_level m l = None <-> LevelSet.In l (levels m).
  Proof.
    funelim (declare_level m l) => //.
    - split => // _.
      clear H.
      now move/LoopCheck.declare_level_None: eqdecl.
    - split => //. rw -LoopCheck.declare_level_None. rw eq0 => //.
    - bang.
  Qed.

  Lemma declare_level_Some {l m m'}: declare_level m l = Some m' ->
    [/\ ~ LevelSet.In l (levels m), levels m' =_lset LevelSet.add l (levels m) &
      exists c, init_constraint_of_level l = Some c /\ constraints m' =_ucset UnivConstraintSet.add c (constraints m)].
  Proof.
    funelim (declare_level m l) => //.
    - move=> [=] <-. cbn.
      clear H H0 Heqcall. cbn. unfold levels. cbn.
      move/LoopCheck.declare_level_levels: eq0 => -[] nin eql.
      split => //. exists c. split => //.
    - bang.
  Qed.

  Definition declare_level_aux l (g : option univ_model) :=
    match g with
    | None => None
    | Some g => declare_level g l
    end.

  (* Import UnivLoopChecking. *)
  Lemma declare_level_aux_spec l g :
    declare_level_aux l g = None <-> (g = None \/ exists g', g = Some g' /\ LevelSet.In l (levels g')).
  Proof.
    destruct g => //=.
    - rw declare_level_None.
      split => //. right. exists u. split => //.
      now move=> [] // [] g' [] [=] ->.
    - split => //. move=> _. now left.
  Qed.

  Lemma declare_level_aux_Some l g g'' :
    declare_level_aux l g = Some g'' -> (exists g', g = Some g' /\ ~ LevelSet.In l (levels g') /\ levels g'' =_lset LevelSet.add l (levels g') /\
      exists c, init_constraint_of_level l = Some c /\ constraints g'' =_ucset UnivConstraintSet.add c (constraints g')).
  Proof.
    destruct g => //=.
    exists u. split => //. rw -declare_level_None H; split=> //.
    apply declare_level_Some in H as [] => //.
  Qed.

  Definition declare_levels_aux (g : option univ_model) (levels : LevelSet.t) : option univ_model :=
    LevelSet.fold declare_level_aux levels g.

  Definition declare_levels (g : univ_model) (levels : LevelSet.t) : option univ_model :=
    declare_levels_aux (Some g) levels.



  Hint Rewrite UnivConstraintSet.union_spec : set_specs.

  Lemma declare_levels_aux_spec og ls :
    match declare_levels_aux og ls with
    | None => og = None \/ exists l, LevelSet.In l ls /\ LevelSet.In l (option_get LevelSet.empty (option_map UnivLoopChecking.levels og))
    | Some g' => exists init, og = Some init /\ (forall l, LevelSet.In l ls -> ~ LevelSet.In l (levels init)) /\ levels g' =_lset LevelSet.union ls (levels init) /\
      constraints g' =_ucset UnivConstraintSet.union (init_constraints_of_levels ls) (constraints init)
    end.
  Proof.
    unfold declare_levels_aux.
    eapply LevelSetProp.fold_rec.
    - move=> s' he. destruct og => //. exists u. split => //.
      split. lsets. split => //. lsets.
      intros c. rsets. split; auto. intros []; auto.
      apply init_constraints_of_levels_spec_inv in H as [l [he' _]]; lsets.
      now left.
    - move=> x a s' s'' hin hnin hadd.
      destruct a.
      destruct (declare_level_aux) eqn: hd.
      move/declare_level_aux_Some: hd.
      + move=> [] g' [] [=] <- [] hnin' [hadd' [c [eqc hcstr']]].
        move=> [init [eqog [inv' [inv'' invc]]]].
        exists init. split => //. split.
        * move=> l /hadd [].
          { intros ->. intros hinl. lsets. }
          { intros inls'. now apply inv'. }
        * rw hadd' inv''.
          apply LevelSetProp.Add_Equal in hadd.
          split => //. rw hadd. lsets.
          rw hcstr' invc.
          rw hadd // init_constraints_of_levels_add; tea. ucsets.
      + move/declare_level_aux_spec: hd.
        intros [] => //. destruct H as [g' [[=] hin']]. subst g'.
        move=> [init [-> [inv [invl invc]]]]. right. cbn.
        rw invl in hin'. rsets. exists x. split => //. apply hadd. now left.
      + cbn. move=> [] h; [left|right]; auto.
        destruct h as [l [inls' cb]]. exists l. split => //.
        apply hadd. now right.
  Qed.

  Lemma declare_levels_spec g ls :
    match declare_levels g ls with
    | None => exists l, LevelSet.In l ls /\ LevelSet.In l (UnivLoopChecking.levels g)
    | Some g' => [/\ (forall l, LevelSet.In l ls -> ~ LevelSet.In l (levels g)),
       levels g' =_lset LevelSet.union ls (levels g) &
       constraints g' =_ucset UnivConstraintSet.union (init_constraints_of_levels ls) (constraints g)]
    end.
  Proof.
    have hs := declare_levels_aux_spec (Some g) ls.
    unfold declare_levels.
    destruct (declare_levels_aux (Some g) ls) => //.
    destruct hs as [init [[=] hl]]. now subst g.
    destruct hs => //.
  Qed.

  (* Lemma declare_levels_aux_clauses m l :
    LoopCheck.clauses (declare_levels_aux m l) =_clset
    LoopCheck.clauses m.
  Proof.
    rewrite /declare_levels_aux.
    eapply LevelSetProp.fold_rec.
    - move=> s' he. clsets.
    - move=> x a s' s'' hin hnin hadd heq.
      apply LevelSetProp.Add_Equal in hadd.
      destruct LoopCheck.declare_level eqn:hd => //.
      rewrite -heq.
      apply LoopCheck.declare_level_clauses in hd.
      unfold LoopCheck.clauses.
      now rewrite hd.
  Qed. *)

  Definition to_valuation (v : Level.t -> nat) : Universes.valuation :=
    {| valuation_mono := fun s => Pos.of_nat (v (Level.level s));
       valuation_poly := fun i => v (Level.lvar i);
    |}.

  Definition of_valuation V (v : Universes.valuation) : LevelMap.t nat :=
    let add_val l := LevelMap.add l (val v l) in
    LevelSet.fold add_val V (LevelMap.empty _).

  Definition wf_valuation V v :=
    forall l, LevelSet.In l V ->
    if l == Level.zero then v l = 0
    else if Level.is_global l then v l > 0
    else v l >= 0.

  Lemma wf_valuation_union {V V' v} : wf_valuation (V ∪ V') v -> wf_valuation V v /\ wf_valuation V' v.
  Proof.
    intros wf; split; intros l hin; specialize (wf l); apply wf; lsets.
  Qed.

  Lemma interp_prem_to_atom V {v} le :
    wf_valuation V v ->
    LevelSet.In (LevelExpr.level le) V ->
    interp_expr (to_Z_val v) (to_atom le) = Z.of_nat (val (to_valuation v) le).
  Proof.
    destruct le as [l k]; cbn.
    move => /(_ l) wf /wf.
    destruct l => //.
    - rw eqb_refl //= /to_Z_val; cbn. now move => ->.
    - cbn. rw /to_Z_val => hin. hnf in hin.
      change (Level.level t0) with (Universes.Level.level t0). lia.
    - cbn. unfold to_Z_val; cbn. lia.
  Qed.

  Lemma interp_nes_to_atoms {V v} (u : Universe.t) :
    wf_valuation V v ->
    LevelSet.Subset (Universe.levels u) V ->
    interp_nes (to_Z_val v) (to_atoms u) = Z.of_nat (Universes.val (to_valuation v) u).
  Proof.
    move: u.
    apply: Universe.elim.
    - intros [l k] => //= hin.
      rw to_atoms_singleton interp_nes_singleton.
      rw val_singleton Universe.levels_singleton => hwf.
      rw (interp_prem_to_atom V (l, k)) //.
      cbn in *; lsets.
    - move=> le x eq nin wf. specialize (eq wf).
      rw to_atoms_add interp_nes_add val_add.
      rw Universe.levels_add => hincl.
      forward eq by lsets.
      rw (interp_prem_to_atom V) //. cbn in *. apply hincl. rsets. now left.
      cbn. rw eq. unfold Universes.LevelExpr.t.
      lia.
  Qed.

  Lemma clauses_sem_val {V v} {l r : Universe.t} :
    wf_valuation V v ->
    LevelSet.Subset (Universe.levels l) V ->
    LevelSet.Subset (Universe.levels r) V ->
    clauses_sem (to_Z_val v) (clauses_of_le (to_atoms l) (to_atoms r)) ->
    Universes.val (to_valuation v) l <=
    Universes.val (to_valuation v) r.
  Proof.
    move=> wf decll declr.
    move/clauses_sem_clauses_of_le.
    have he := @interp_nes_to_atoms V v l wf decll.
    have he' := @interp_nes_to_atoms V v r wf declr.
    cbn in *. unfold Universes.LevelExpr.t in *. lia.
  Qed.

  Lemma clauses_sem_val_in_clauses {V v} {l r : Universe.t} :
    wf_valuation V v ->
    clauses_sem (to_Z_val v) (to_atoms l ⋞ to_atoms r) ->
    Universe.levels l ⊂_lset V ->
    Universe.levels r ⊂_lset V ->
    Universes.val (to_valuation v) l <= Universes.val (to_valuation v) r.
  Proof.
    move=> wf cls incl incl'.
    eapply clauses_sem_val; tea; etransitivity.
  Qed.

  Lemma declared_clauses_levels {m} {l r : Universe.t} {d} :
    LoopCheck.to_clauses (to_constraint (l, d, r)) ⊂_clset Impl.Abstract.clauses m ->
    Universe.levels l ⊂_lset (Impl.Abstract.levels m) /\
    Universe.levels r ⊂_lset (Impl.Abstract.levels m).
  Proof.
    intros; split.
    1-2:etransitivity; [|apply clauses_levels_declared].
    1-2:etransitivity; [|eapply clauses_levels_mon; tea].
    1-2:intros l';rw in_to_clauses_levels in_constraint_levels_to_constraint //=; lsets.
  Qed.

  Lemma wf_model_valuation (m : t) : wf_valuation (Impl.Abstract.levels m) (LoopCheck.valuation m).
  Proof.
    red. intros []; cbn.
    - intros hz. rw eqb_refl.
      eapply LoopCheck.model_valuation_zero.
    - move=> hin. hnf. now apply LoopCheck.model_valuation_global.
    - move=> hin. hnf. now apply LoopCheck.model_valuation_not_global.
  Qed.

  Lemma model_satisfies (m : univ_model) :
    satisfies (to_valuation (valuation m)) (constraints m).
  Proof.
    destruct m as [m cstrs repr repr_inv]. cbn.
    have val := model_valuation m.
    move=> cstr /repr /[dup]/(clauses_sem_subset val) cls incl.
    destruct cstr as [[l []] r]; cbn.
    - constructor. cbn in cls.
      eapply declared_clauses_levels in incl as [].
      eapply clauses_sem_val_in_clauses; tea.
      apply (wf_model_valuation m).
    - constructor. cbn in cls.
      rw clauses_sem_union in cls. destruct cls as [hl hr].
      eapply declared_clauses_levels in incl as [].
      eapply Nat.le_antisymm; eapply clauses_sem_val_in_clauses; tea.
      all:apply (wf_model_valuation m).
  Qed.

  Lemma of_valuation_spec V v :
    forall l k, LevelMap.MapsTo l k (of_valuation V v) <->
      (LevelSet.In l V /\ k = val v l).
  Proof.
    intros l k.
    rw /of_valuation.
    eapply LevelSetProp.fold_rec.
    - move=> s' he.
      rw LevelMapFact.F.empty_mapsto_iff.
      split => // -[] hin' _. lsets.
    - move=> x a s' s'' hin hnin hadd ih.
      rw LevelMapFact.F.add_mapsto_iff /Level.eq ih.
      rw hadd. firstorder; subst; auto.
      destruct (Classes.eq_dec x l); firstorder. subst. now left.
  Qed.

  Lemma interp_level_of_valuation {V v l} :
    LevelSet.In l V ->
    to_Z_val (to_val (of_valuation V v)) l = Z.of_nat (val v l).
  Proof.
    move=> hin.
    rw /to_Z_val /to_val.
    elim: find_spec => [k /of_valuation_spec []|] => //.
    { intros ? ->. reflexivity. }
    elim. exists (val v l). rw [LevelMap.Raw.MapsTo _ _ _]of_valuation_spec.
    split => //.
  Qed.


  Lemma to_of_valuation V v :
    forall l, LevelSet.In l.1 V -> val (to_valuation (to_val (of_valuation V v))) l = val v l.
  Proof.
    intros l hin.
    destruct l; cbn. f_equal.
    destruct e; cbn => //.
    all:unfold to_val;
    elim: (find_spec _ (of_valuation V v)).
    - move=> k H. eapply of_valuation_spec in H.
      destruct H as [hin' ->]. cbn in *. lia.
    - move=> hnin. cbn in *. elim hnin.
      exists (val v (Level.level t0)).
      rw [LevelMap.Raw.MapsTo _ _ _]of_valuation_spec.
      split => //.
    - move=> k H. eapply of_valuation_spec in H.
      destruct H as [hin' ->]. cbn in *. lia.
    - move=> hnin. cbn in *. elim hnin.
      exists (val v (Level.lvar n0)).
      rw [LevelMap.Raw.MapsTo _ _ _]of_valuation_spec.
      split => //.
  Qed.

  Lemma to_of_valuation_univ V v :
    forall u : Universe.t, LevelSet.Subset (Universe.levels u) V ->
    val (to_valuation (to_val (of_valuation V v))) u = val v u.
  Proof.
    apply: Universe.NES.elim.
    - move=> le incl.
      cbn.
      rw to_of_valuation.
      apply incl.
      rw Universe.levels_spec. exists le.2.
      now destruct le; apply Universes.LevelExprSet.singleton_spec.
      reflexivity.
    - move=> le u hincl hnin hincl'.
      have hl : Universe.levels u ⊂_lset V.
      { intros ? hin. apply hincl'.
        rw Universe.levels_spec in hin.
        destruct hin as [k hin].
        rw Universe.levels_spec. exists k.
        rw Universes.LevelExprSet.add_spec. now right. }
      rw !val_add // hincl //.
      forward hincl by assumption.
      rw to_of_valuation //.
      apply hincl'.
      rw Universe.levels_spec. exists le.2.
      rw Universes.LevelExprSet.add_spec. now left; destruct le.
  Qed.

  Lemma clauses_levels_mon {cls cls'} :
    cls ⊂_clset cls' ->
    clauses_levels cls ⊂_lset clauses_levels cls'.
  Proof.
    move=> sub l /clauses_levels_spec; rw clauses_levels_spec.
    firstorder.
  Qed.
  (* Lemma in_to_clauses_elem {l k a}  : *)

  Lemma wf_valuation_of_valuation V v : wf_valuation V (to_val (of_valuation V v)).
  Proof.
    move=> l hin.
    have [_ hof] := of_valuation_spec V v l (val v l).
    forward hof. split => //.
    destruct l; cbn.
    - hnf. rw /to_val.
      now rw (LevelMap.find_1 hof).
    - hnf. rw /to_val.
      rw (LevelMap.find_1 hof). cbn. lia.
    - hnf. rw /to_val.
      rw (LevelMap.find_1 hof). cbn. lia.
  Qed.

  Lemma in_to_clauses_sem {l r V v} :
    LevelSet.Subset (univ_constraint_levels (l, ConstraintType.Le, r)) V ->
    val v l <= val v r ->
    forall cl, LevelExprSet.Exists (fun lk : LevelExprSet.elt => cl = (to_atoms r, lk)) (to_levelexprzset l) ->
    clause_sem (to_Z_val (to_val (of_valuation V v))) cl.
  Proof.
    move=> hlev leq [prems concl].
    move=> [] [l'' k'] [] /to_levelexprzset_spec_2 [] inl' pos ->.
    cbn -[le].
    erewrite interp_nes_to_atoms.
    rw to_of_valuation_univ.
    { intros ? hin; apply hlev. cbn. lsets. }
    transitivity (Z.of_nat (val v l)).
    rw interp_level_of_valuation.
    { apply hlev; cbn.
      eapply LevelSet.union_spec; left. eapply Universe.levels_spec.
      now eexists. }
    have vle := val_In_le l v _ inl'. cbn in vle.
    cbn; u; lia.
    cbn; u; lia.
    apply wf_valuation_of_valuation.
    intros lr hin. apply hlev. cbn. lsets.
  Qed.

  Lemma satisfies_clauses_sem v {m : univ_model} V :
    LoopCheck.levels (UnivLoopChecking.model m) ⊂_lset V ->
    satisfies v (constraints m) ->
    clauses_sem (to_Z_val (to_val (of_valuation V v))) (LoopCheck.clauses (UnivLoopChecking.model m)).
  Proof.
    have repr := repr_constraints_inv m.
    have repr_inv := repr_constraints m.
    move=> hsub hs cl /[dup] hin /repr [] c [] /[dup] /repr_inv hr /hs sat.
    destruct c as [[l' d] r].
    move=> /[dup] intocl.
    rw LoopCheck.to_clauses_spec.
    depelim sat. cbn -[clause_sem].
    - apply in_to_clauses_sem; auto.
      cbn; intros le inr. apply hsub.
      apply (LoopCheck.clauses_levels_declared m).
      move/clauses_levels_mon: hr; apply.
      rw in_to_clauses_levels.
      rw in_constraint_levels_to_constraint //=.
    - cbn. move=> [].
      * apply in_to_clauses_sem; [|lia].
        cbn; intros le inr.
        apply hsub, (LoopCheck.clauses_levels_declared m).
        move/clauses_levels_mon: hr; apply.
        rw in_to_clauses_levels.
        rw in_constraint_levels_to_constraint //=.
      * apply in_to_clauses_sem; [|lia].
        cbn; intros le inr.
        apply hsub, (LoopCheck.clauses_levels_declared m).
        move/clauses_levels_mon: hr; apply.
        rw in_to_clauses_levels.
        rw in_constraint_levels_to_constraint //=. lsets.
  Qed.

  Lemma clauses_sem_satisfies {v V c} :
    univ_constraint_levels c ⊂_lset V ->
    clauses_sem (to_Z_val (to_val (of_valuation V v))) (LoopCheck.to_clauses (to_constraint c)) ->
    satisfies0 v c.
  Proof.
    have wfv := @wf_valuation_of_valuation V v.
    intros hin hsem. destruct c as [[l []] r]; cbn in *.
    - constructor.
      move/clauses_sem_clauses_of_le: hsem.
      erewrite !interp_nes_to_atoms; tea.
      rw !to_of_valuation_univ. lsets. lsets. cbn; lia.
      setoid_rewrite <- hin. lsets.
      setoid_rewrite <- hin. lsets.
    - constructor.
      rw clauses_sem_union in hsem. destruct hsem as [hsem hsem'].
      move/clauses_sem_clauses_of_le: hsem.
      move/clauses_sem_clauses_of_le: hsem'.
      erewrite !interp_nes_to_atoms; tea.
      rw !to_of_valuation_univ. lsets. lsets. cbn; lia.
      setoid_rewrite <- hin; lsets.
      setoid_rewrite <- hin; lsets.
  Qed.

  Lemma val_respects cls v : @respects _ _ Z _ (horn_semi cls) _ Zsemilattice (fun u => interp_nes v u).
  Proof.
    split; cbn.
    - intros n x. rw interp_add_prems; cbn. lia.
    - intros x y. rw interp_nes_union; cbn. lia.
  Qed.

  Definition check (m : univ_model) (c : UnivConstraint.t) : bool :=
    LoopCheck.check_constraint m.(UnivLoopChecking.model) (to_constraint c).
  Derive Signature for satisfies0.


  Section interp_nat.
    Import Semilattice.
    Import -(notations) Universe.
    Context {S : Type} {SL : Semilattice S nat}.
    Context (v : Level.t -> S).

    Definition interp_nat_cstr c :=
      let '(l, d, r) := c in
      match d with
      | ConstraintType.Le => interp_nes v l ≤ interp_nes v r
      | ConstraintType.Eq => interp_nes v l ≡ interp_nes v r
      end%Z.

    Definition interp_cstrs c := UnivConstraintSet.For_all interp_nat_cstr c.

  End interp_nat.

  Definition valid_relation rels c :=
    (forall S (SL : Semilattice S Q.t) (v : Level.t -> S), interp_rels v rels -> interp_rel v c).

  Definition valid_constraint rels c :=
    (forall S (SL : Semilattice S Q.t) (v : Level.t -> S), interp_rels v rels -> interp_z_cstr v c).

  Definition valid_cstrs p cstrs :=
    ZUnivConstraintSet.For_all (valid_constraint p) cstrs.

  Import Semilattice.
  Import ISL.

  Definition model_val (m : univ_model) := valuation m.

  Definition model_opt_val (m : univ_model) := (LoopCheck.Impl.Abstract.opt_valuation m.(model)).

  Definition model_Z_val (m : univ_model) := (to_Z_val (LoopCheck.valuation m)).

  Lemma interp_rels_of_m m : interp_rels (model_Z_val m) (relations_of_constraints (to_z_cstrs (constraints m))).
  Proof.
    have hv := (LoopCheck.model_valuation m).
    red.
    apply Forall_forall. move=> [l r] /relations_of_constraints_spec => -[cl [hin heq]].
    eapply to_z_cstrs_spec_2 in hin as [cstr [hin ->]].
    have hrepr := repr_constraints m _ hin.
    destruct cstr as [[l' []] r']; cbn in heq; noconf heq.
    - rw /interp_rel interp_nes_union. cbn in hrepr.
      eapply clauses_sem_subset in hv; tea.
      apply clauses_sem_clauses_of_le in hv. cbn in hv |- *.
      unfold model_Z_val in *. lia.
    - cbn in hrepr.
      eapply clauses_sem_subset in hv; tea.
      rw /Clauses.clauses_of_eq in hv.
      eapply clauses_sem_union in hv. destruct hv as [hv hv'].
      apply clauses_sem_clauses_of_le in hv.
      apply clauses_sem_clauses_of_le in hv'. cbn in hv, hv' |- *.
      unfold model_Z_val in *; lia.
  Qed.

  (** The constraints in the model are already valid. *)
  Lemma interp_univ_cstrs_of_m_Z m :
    interp_univ_cstrs (model_Z_val m) (constraints m).
  Proof.
    intros uc hin. red.
    have h := repr_constraints m _ hin.
    have hi := interp_rels_of_m m.
    red in hi. rw Forall_forall in hi.
    apply to_z_cstrs_spec_1 in hin as [cstrz [hin ->]].
    destruct uc as [[l []] r]; cbn. cbn in h.
    - move: (hi ((to_atoms l ∨ to_atoms r)%nes, to_atoms r)) => /fwd.
      { apply relations_of_constraints_spec. exists (to_atoms l, ConstraintType.Le, to_atoms r).
        cbn. split => //. }
     by rw /interp_rel interp_nes_union; unfold model_Z_val in *; cbn; lia.
    - move: (hi (to_atoms l, to_atoms r)) => /fwd.
      { apply relations_of_constraints_spec. exists (to_atoms l, ConstraintType.Eq, to_atoms r).
        cbn. split => //. }
      by [].
  Qed.


  Lemma to_valuation_val V (v : Level.t -> nat) (l : Universes.Level.t) :
    wf_valuation V v ->
    LevelSet.In l V ->
    v l = val (to_valuation v) l.
  Proof.
    move=> wf /wf.
    destruct l => //=.
    cbn. lia.
  Qed.

  Hint Rewrite Universe.levels_singleton : set_specs.

  (** Interpretation in the semilattice of natural numbers *)
  Lemma interp_nes_val {V} (v : Level.t -> nat) (u : Universe.t) :
    Universe.levels u ⊂_lset V ->
    wf_valuation V v ->
    Universe.interp_nes v u = Universes.val (to_valuation v) u.
  Proof.
    move: u. refine (Universe.interp_nes_elim v (fun u i => _ -> _ -> i = val (to_valuation v) u) _ _ _).
    - intros [l k]; rw val_singleton //= /val; rsets. cbn in *.
      rw /Universe.interp_expr (to_valuation_val V v) //; cbn. apply H; lsets.
    - move=>[l k] u k' ih hnin.
      rw Universe.levels_add //= => hincl wfv.
      rw val_add; cbn. rw (to_valuation_val V v) //; cbn. lsets.
      forward ih. lsets. specialize (ih wfv). lia.
  Qed.

  Lemma interp_univ_cstr_nat V {v} cl :
    wf_valuation V v -> declared_univ_cstr_levels V cl ->
    interp_univ_cstr (to_Z_val v) cl <-> interp_nat_cstr v cl.
  Proof.
    move=> wfv.
    destruct cl as [[l []] r] => //= decl;
    cbn; erewrite !interp_nes_to_atoms; tea;
    try rw !(@interp_nes_val V v) /model_val //; try (split; lia); intuition eauto.
  Qed.

  Lemma interp_univ_cstrs_nat V v cl :
    wf_valuation V v ->
    UnivConstraintSet.For_all (declared_univ_cstr_levels V) cl ->
    interp_univ_cstrs (to_Z_val v) cl <-> interp_cstrs v cl.
  Proof.
    move=> wfV hcl.
    split; move=> hin cl' /[dup]/hin => icl /hcl declcl.
    now rw -(interp_univ_cstr_nat V) //.
    now rw (interp_univ_cstr_nat V) //.
  Qed.

  Lemma interp_cstrs_of_m m :
    interp_cstrs (model_val m) (constraints m).
  Proof.
    have ha := interp_univ_cstrs_of_m_Z m.
    eapply interp_univ_cstrs_nat.
    - eapply wf_model_valuation.
    - move=> cstr /repr_constraints => hincl.
      apply ndecl_nin_levels.
      etransitivity; [|eapply clauses_levels_declared].
      now eapply clauses_levels_mon.
    - exact ha.
  Qed.

  Instance nat_opt_semi : Semilattice (option nat) nat := opt_semi Natsemilattice.

  Definition valid_Z_model m c :=
    forall (v : Level.t -> Z),
      positive_valuation v ->
      interp_univ_cstrs v (constraints m) -> interp_univ_cstr v c.

  Infix "⊩Z" := valid_Z_model (at level 70, no associativity).

  Definition to_nat_val (v : Level.t -> Z) :=
    fun l => Z.to_nat (v l).

  Definition valid_nat_model m c :=
    forall (v : Level.t -> nat),
    interp_cstrs v (constraints m) -> interp_nat_cstr v c.

  Infix "⊩𝐍" := valid_nat_model (at level 70, no associativity).

  Section InterpNatZ.
    Context (v : Level.t -> Z).
    Context (v' : Level.t -> nat).
    Context (hv : forall l, v l = Z.of_nat (v' l)).

    Lemma interp_nes_equiv u : interp_nes v (to_atoms u) = Z.of_nat (Universe.interp_nes v' u).
    Proof.
      move: u; apply: Universe.elim.
      - intros [l k]. rw to_atoms_singleton
          interp_nes_singleton Universe.interp_nes_singleton /interp_expr //=.
        rw (hv l). lia.
      - intros [l k] u he hnin.
        rw to_atoms_add
          interp_nes_add Universe.interp_nes_add /interp_expr //= he.
        rw (hv l). lia.
    Qed.

    Lemma interp_cstr_to_nat c :
      interp_nat_cstr v' c <-> interp_univ_cstr v c.
    Proof.
      destruct c as [[l []] r]; cbn;
      rw !interp_nes_equiv; lia.
    Qed.

    Lemma interp_cstrs_to_nat cstrs :
      interp_cstrs v' cstrs <-> interp_univ_cstrs v cstrs.
    Proof.
      rw /interp_cstrs /interp_univ_cstrs.
      split; now move=> hf c /hf /interp_cstr_to_nat.
    Qed.
  End InterpNatZ.

  Lemma valid_Z_valid_nat_model m c :
    valid_nat_model m c <-> valid_Z_model m c.
  Proof.
    split; intros hv v.
    - intros vpos.
      specialize (hv (to_nat_val v)).
      rw -(interp_cstrs_to_nat v (to_nat_val v)).
      rw /to_nat_val. intros l.
      specialize (vpos l). lia.
      rw -(interp_cstr_to_nat v (to_nat_val v)).
      rw /to_nat_val. intros l.
      specialize (vpos l). lia.
      exact hv.
    - rw (interp_cstrs_to_nat (to_Z_val v)) //.
      rw (interp_cstr_to_nat (to_Z_val v)) //.
      move: (hv (to_Z_val v)) => /fwd //.
      intros l; rw /to_Z_val. lia.
  Qed.

  Definition defined_valuation_of V (v : Level.t -> option nat) :=
    forall l, LevelSet.In l V -> exists x, v l = Some x.

  Theorem check_completeness {m : univ_model} {c} :
    declared_univ_cstr_levels (levels m) c ->
    check m c <-> m ⊩Z c.
  Proof.
    intros hwf.
    rw check_constraintS.
    now eapply ndecl_nin_levels in hwf.
    rw /valid_clauses_Z /valid_Z_model.
    setoid_rewrite interp_cstrs_clauses_sem; setoid_rewrite interp_cstr_clauses_sem.
    rw /valid_clauses. reflexivity.
  Qed.

  Theorem check_nat_completeness {m : univ_model} {c} :
    declared_univ_cstr_levels (levels m) c ->
    check m c <-> m ⊩𝐍 c.
  Proof.
    intros hwf.
    rw check_completeness //.
    now rw valid_Z_valid_nat_model.
  Qed.

  Lemma interp_univ_cstrs_of_m m :
    interp_univ_cstrs (model_opt_val m) (constraints m).
  Proof.
    rw interp_cstrs_clauses_sem.
    apply model_opt_Z_valuation.
  Qed.

  (** The current model must already imply the constraint. Note that the converse
      is not true: a constraint can be satisfied by chance in the model. *)
  (* Theorem check_implies {m c} :
    check m c -> interp_univ_cstr (to_Z_val (valuation m)) c.
  Proof.
    rewrite check_completeness => /(_ (model_opt_val m) (opt_valuation_of_model_pos) (interp_univ_cstrs_of_m m)).

  Qed. *)

  Definition valid_model m c :=
    (forall S (SL : Semilattice S Q.t) (v : Level.t -> S), interp_univ_cstrs v (constraints m) -> interp_univ_cstr v c).

  Infix "⊩" := valid_model (at level 70, no associativity).

  Theorem check_any_completeness {m : univ_model} {c} :
    check_entails (model m) (to_constraint c) <-> m ⊩ c.
  Proof.
    rw LoopCheck.check_entails_complete /LoopCheck.valid_entailments /valid_model.
    setoid_rewrite interp_cstrs_clauses_sem.
    split.
    - intros hv S s v hp.
      move: (hv S s v hp).
      now rw interp_cstr_clauses_sem.
    - intros hs S SL V hsem.
      move: (hs S SL V) => /fwd //.
      now rw interp_cstr_clauses_sem.
  Qed.

  Definition univ_constraints_levels cstrs :=
    UnivConstraintSet.fold (fun c => LevelSet.union (univ_constraint_levels c)) cstrs LevelSet.empty.

  Definition univ_constraints_levels_spec cstrs :
    forall l, LevelSet.In l (univ_constraints_levels cstrs) <-> exists c, UnivConstraintSet.In c cstrs /\ LevelSet.In l (univ_constraint_levels c).
  Proof.
    rw /univ_constraints_levels.
    eapply UnivConstraintSetProp.fold_rec.
    - intros ? ? ?. split; try lsets.
      intros [c [hin hin']]. ucsets.
    - move=> x a s' s'' hin hin' hadd ih l.
      rsets. eapply UnivConstraintSetProp.Add_Equal in hadd. setoid_rewrite hadd.
      intuition eauto.
      exists x. split => //. ucsets. apply ih in H0 as [c' []].
      exists c'. split; try ucsets. lsets.
      destruct H as [c []].
      move:H; rw UnivConstraintSet.add_spec=> -[].
      * now intros <-.
      * intros ins'. right. apply ih. exists c. now split.
  Qed.

  Lemma constraint_levels_declared {m : univ_model} : univ_constraints_levels (constraints m) ⊂_lset levels m.
  Proof.
    etransitivity; [|eapply clauses_levels_declared].
    intros l; rw univ_constraints_levels_spec => -[] c [] hin.
    revert l. change (univ_constraint_levels c ⊂_lset (clauses_levels (LoopCheck.clauses m))).
    etransitivity; [|eapply declared_univ_cstr_levels_spec]. reflexivity.
    move/repr_constraints: hin => hincl.
    apply ndecl_nin_levels. now apply clauses_levels_mon.
  Qed.

  Lemma declared_cstrs {m : univ_model} :
    UnivConstraintSet.For_all (declared_univ_cstr_levels (levels m)) (constraints m).
  Proof.
    intros cl hin. destruct cl as [[l d] r]. cbn. split.
    transitivity (univ_constraint_levels (l, d, r)); cbn; try lsets.
    transitivity (univ_constraints_levels (constraints m)) => //.
    intros ?; rw univ_constraints_levels_spec; firstorder.
    apply constraint_levels_declared.
    transitivity (univ_constraint_levels (l, d, r)); cbn; try lsets.
    transitivity (univ_constraints_levels (constraints m)) => //.
    intros ?; rw univ_constraints_levels_spec; firstorder.
    apply constraint_levels_declared.
  Qed.

  Theorem check_valid_nat {m : univ_model} {c} :
    check_entails (model m) (to_constraint c) -> (forall (v : Level.t -> nat), wf_valuation (levels m ∪ univ_constraint_levels c) v -> interp_cstrs v (constraints m) -> interp_nat_cstr v c).
  Proof.
    rw check_any_completeness.
    intros hv v wfv hp.
    have [wfm wfc] := wf_valuation_union wfv.
    move: (hv Z Zsemilattice (to_Z_val v)).
    erewrite interp_univ_cstr_nat; tea. apply.
    eapply interp_univ_cstrs_nat. exact wfm.
    { apply declared_cstrs. }
    exact hp.
    destruct c as [[l d] r]; cbn. split; lsets.
  Qed.

End UnivLoopChecking.
