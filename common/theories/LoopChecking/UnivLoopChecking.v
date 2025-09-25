(* Distributed under the terms of the MIT license. *)
(* This module provides an instantiation of the deciders for universe checking,
  i.e. for constraints on non-empty level expressions (l, k) where k ∈ 𝐍 *)

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

Module LS <: LevelSets.
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
  forall l k, LevelExprSet.In (l, k) (from_levelexprzset u) ->
  exists z, LevelExprZSet.In (l, z) u /\ k = Z.to_nat z.
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

Module UnivLoopChecking.
  Module LoopCheck := LoopChecking LS.
  Import LoopCheck.Impl.I.

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

  Program Definition from_atoms (u : NES.t) : Universe.t :=
    {| Universe.t_set := from_levelexprzset (NES.t_set u) |}.
  Next Obligation.
    apply Universe.NES.not_Empty_is_empty => he.
    eapply (NES.not_Empty_is_empty u). apply t_ne.
    intros [] hin.
    apply from_levelexprzset_spec in hin. now apply he in hin.
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
    rewrite /of_z_constraints.
    eapply ZUnivConstraintSetProp.fold_rec.
    - intros s' he cl; split. clsets.
      intros [cstr [hin ?]]. firstorder.
    - intros x a s' s'' hin hnin hadd h cl.
      rewrite Clauses.union_spec h.
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
    rewrite /to_clauses.
    eapply UnivConstraintSetProp.fold_rec.
    - intros s' he cl; split. clsets.
      intros [cstr [hin ?]]. firstorder.
    - intros x a s' s'' hin hnin hadd h cl.
      rewrite Clauses.union_spec h.
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
    rewrite /to_z_cstrs.
    eapply UnivConstraintSetProp.fold_rec.
    - now move=> s' he c /he.
    - intros x a s' s'' hin hnin hadd h cl.
      rw ZUnivConstraintSet.add_spec => /hadd [].
      * intros ->. eexists; split => //. now left.
      * move/h => [cstr [hin' incl]]. subst cstr.
        exists (to_constraint cl). firstorder.
  Qed.

  Lemma to_z_cstrs_spec_2 {cstrs} :
    forall c, ZUnivConstraintSet.In c (to_z_cstrs cstrs) ->
      (exists cstr, UnivConstraintSet.In cstr cstrs /\
       c = to_constraint cstr).
  Proof.
    rewrite /to_z_cstrs.
    eapply UnivConstraintSetProp.fold_rec.
    - move=> s' he c. zucsets.
    - intros x a s' s'' hin hnin hadd h c.
      rewrite ZUnivConstraintSet.add_spec => -[].
      * intros ->. eexists; split => //. apply hadd. now left.
      * move/h => [cstr [hin' incl]]. subst c.
        exists cstr. firstorder.
  Qed.

  Lemma to_clauses_of_z_constraints {cstrs} :
    to_clauses cstrs =_clset of_z_constraints (to_z_cstrs cstrs).
  Proof.
    intros l.
    rewrite to_clauses_spec of_z_constraints_spec.
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

  Record univ_model := {
    model : LoopCheck.model;
    constraints : UnivConstraintSet.t;
    repr_constraints : forall c, UnivConstraintSet.In c constraints ->
      Clauses.Subset (LoopCheck.to_clauses (to_constraint c)) (LoopCheck.Impl.Abstract.clauses model);
    repr_constraints_inv : forall cl, Clauses.In cl (LoopCheck.Impl.Abstract.clauses model) ->
      exists c, UnivConstraintSet.In c constraints /\ Clauses.In cl (LoopCheck.to_clauses (to_constraint c))
      }.

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

  Lemma in_to_atoms a u :
    LevelExprSet.In (a.1, Z.of_nat a.2) (to_atoms u) <-> Universes.LevelExprSet.In a u.
  Proof.
    destruct a as [l k].
    rewrite /to_atoms //=.
    split.
    - move/to_levelexprzset_spec_2 => [] hin _.
      now rewrite Nat2Z.id in hin.
    - now move/to_levelexprzset_spec_1.
  Qed.

  Lemma levels_in_to_atoms l u :
    LevelSet.In l (levels (to_atoms u)) <-> Universes.LevelSet.In l (Universe.levels u).
  Proof.
    rewrite levels_spec.
    rewrite /in_to_atoms.
    split.
    - move=> [] k. move/to_levelexprzset_spec_2 => [] hin _.
      apply Universe.levels_spec. now eexists.
    - rewrite Universe.levels_spec => -[] k hin.
      exists (Z.of_nat k). now rewrite (in_to_atoms (l, k)).
  Qed.

  Definition to_atom '(l, k) : LevelExpr.t := (l, Z.of_nat k).

  Lemma exists_to_atoms_spec f u :
    LevelExprSet.Exists f (to_atoms u) <->
    exists le, Universes.LevelExprSet.In le u /\ f (to_atom le).
  Proof.
    rewrite /to_atoms //=; split; rewrite /LevelExprSet.Exists.
    - move=> [] [] l k [] /to_levelexprzset_spec_2 [] hin hpos hf.
      eexists; split; tea. cbn. rewrite Z2Nat.id //.
    - move=> [] [] l k [] hin hf. exists (l, Z.of_nat k); split => //.
      now apply to_levelexprzset_spec_1.
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
  Proof.
    move: H. now rewrite UnivConstraintSetFact.empty_iff.
    move: H. now rewrite ClausesFact.empty_iff.
  Qed.

  Local Obligation Tactic := idtac.

  Local Definition declare_levels_aux m l :=
    LevelSet.fold (fun l m => match LoopCheck.declare_level m l return _ with None => m | Some m => m end) l m.

  Lemma declare_levels_aux_spec m l : LoopCheck.levels (declare_levels_aux m l) =_lset
    LevelSet.union l (LoopCheck.levels m).
  Proof.
    rewrite /declare_levels_aux.
    eapply LevelSetProp.fold_rec.
    - move=> s' he. lsets.
    - move=> x a s' s'' hin hnin hadd heq.
      apply LevelSetProp.Add_Equal in hadd.
      destruct LoopCheck.declare_level eqn:decl.
      * apply LoopCheck.declare_level_levels in decl as [hnin' ->].
        rewrite hadd heq. lsets.
      * apply LoopCheck.declare_level_None in decl.
        rewrite heq hadd.
        rewrite heq LevelSet.union_spec in decl.
        destruct decl => //. lsets.
  Qed.

  Lemma declare_levels_aux_clauses m l :
    LoopCheck.clauses (declare_levels_aux m l) =_clset LoopCheck.clauses m.
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
  Qed.

  (* We ignore errors here, which can happen only if the levels are already declared *)
  Program Definition declare_levels (m : univ_model) (l : LevelSet.t) :=
    {| model := declare_levels_aux m.(model) l; constraints := m.(constraints); |}.
  Next Obligation.
  Proof.
    intros m l c.
    rewrite [LoopCheck.Impl.Abstract.clauses _]declare_levels_aux_clauses => hin.
    move: (repr_constraints m c hin) => h.
    etransitivity; tea. reflexivity.
  Qed.
  Next Obligation.
    move=> m l cl.
    rewrite [LoopCheck.Impl.Abstract.clauses _]declare_levels_aux_clauses => hin.
    now exact: repr_constraints_inv m cl hin.
  Qed.

  Equations? enforce m (c : UnivConstraint.t) : option _ :=
    enforce m c with inspect (LoopCheck.enforce m.(model) (to_constraint c)) :=
      | exist None eq => None
      | exist (Some (inl m')) eq => Some (inl {| model := m'; constraints := UnivConstraintSet.add c m.(constraints) |})
      | exist (Some (inr loop)) eq => Some (inr loop).
  Proof.
    - move=> c'.
      move/LoopCheck.enforce_clauses: eq0.
      rewrite /LoopCheck.clauses => ->. rewrite UnivConstraintSet.add_spec => -[].
      * move=> ->. clsets.
      * move=> hin.
        move: (repr_constraints m c' hin) => h. clsets.
    - move/LoopCheck.enforce_clauses: eq0.
      rewrite /LoopCheck.clauses => -> c'.
      rewrite UnivLoopChecking.Clauses.Clauses.union_spec => -[].
      * move/(repr_constraints_inv m c') => [] c2 [].
        exists c2. split => //.
        rewrite UnivConstraintSet.add_spec. now right.
      * move=> hin. exists c. split => //.
        rewrite UnivConstraintSet.add_spec. now left.
  Qed.

  Lemma clauses_levels_union cls cls' : clauses_levels (Clauses.union cls cls') =_lset
    LevelSet.union (clauses_levels cls) (clauses_levels cls').
  Proof.
    intros l.
    rewrite clauses_levels_spec LevelSet.union_spec.
    rw Clauses.union_spec; rewrite !clauses_levels_spec.
    rw clause_levels_spec. firstorder.
  Qed.

  Definition univ_constraint_levels (c : UnivConstraint.t) :=
    let '(l, d, r) := c in
    LevelSet.union (Universe.levels l) (Universe.levels r).

  Lemma declared_univ_cstr_levels_spec ls c :
    declared_univ_cstr_levels ls c <->
    univ_constraint_levels c ⊂_lset ls.
  Proof.
    destruct c as [[l d] r].
    rewrite /declared_univ_cstr_levels /univ_constraint_levels.
    split.
    - move=> [] hl hr l'.
      rewrite LevelSet.union_spec. firstorder.
    - intros he; split => l'. specialize (he l').
      rewrite LevelSet.union_spec in he. firstorder.
      specialize(he l'). rewrite LevelSet.union_spec in he. firstorder.
  Qed.

  Definition constraint_levels (c : LoopCheck.constraint) :=
    LevelSet.union (levels c.1.1) (levels c.2).

  Lemma in_constraint_levels_to_constraint c :
    forall l, LevelSet.In l (constraint_levels (to_constraint c)) <->
      LevelSet.In l (univ_constraint_levels c).
  Proof.
    intros l; destruct c as [[l' d] r]; cbn.
    rewrite /constraint_levels. rewrite !LevelSet.union_spec. cbn.
    rewrite !levels_in_to_atoms. firstorder.
  Qed.

  Lemma in_to_clauses_levels c :
    forall l, LevelSet.In l (clauses_levels (LoopCheck.to_clauses c)) <->
      LevelSet.In l (constraint_levels c).
  Proof.
    intros l.
    destruct c as [[l' []] r] => //=; revgoals.
    - rewrite clauses_levels_union LevelSet.union_spec.
      rewrite /constraint_levels //= LevelSet.union_spec.
      rewrite !in_clause_levels_of_le. firstorder.
    - rewrite /constraint_levels //= LevelSet.union_spec.
      rewrite !in_clause_levels_of_le. firstorder.
  Qed.

  Lemma ndecl_nin_levels ls c :
    declared_univ_cstr_levels ls c <->
    clauses_levels (LoopCheck.to_clauses (to_constraint c)) ⊂_lset ls.
  Proof.
    rewrite declared_univ_cstr_levels_spec.
    split; intros h.
    - intros ?; rewrite in_to_clauses_levels in_constraint_levels_to_constraint. apply h.
    - etransitivity; tea. intros ?.
      now rewrite in_to_clauses_levels in_constraint_levels_to_constraint.
  Qed.

  Lemma enforce_not_none m c : enforce m c <> None <->
    declared_univ_cstr_levels (LoopCheck.levels (model m)) c.
  Proof.
    have := @LoopCheck.enforce_not_None (model m) (to_constraint c).
    rewrite /enforce.
    destruct inspect as [[[] | ] eq]. simpl.
    - intros. split => // _.
      rewrite ndecl_nin_levels. apply H. now rewrite eq.
    - intros. split => // _.
      rewrite ndecl_nin_levels. apply H. now rewrite eq.
    - intros. split => //=.
      now move/ndecl_nin_levels/H; rewrite eq.
  Qed.

  Lemma enforce_None m c :
    enforce m c = None <-> ~ declared_univ_cstr_levels (LoopCheck.levels m.(model)) c.
  Proof.
    rewrite /enforce.
    destruct inspect as [[[] | ] eq]. simpl.
    - intros. split => //.
      rewrite ndecl_nin_levels.
      rewrite -LoopCheck.enforce_not_None eq; elim. congruence.
    - intros. split => //=.
      rewrite ndecl_nin_levels.
      rewrite -LoopCheck.enforce_not_None eq; elim. congruence.
    - cbn. rewrite ndecl_nin_levels.
      rewrite -LoopCheck.enforce_not_None eq. split => //. congruence.
  Qed.

  Definition levels m := LoopCheck.levels m.(model).

  Lemma enforce_model m c m' :
    enforce m c = Some (inl m') -> levels m = levels m' /\
      UnivConstraintSet.Equal (UnivConstraintSet.add c (constraints m)) (constraints m').
  Proof.
    funelim (enforce m c) => //=.
    move=> [=] <-; cbn. rewrite /levels //=.
    split.
    - clear H Heqcall. now move/LoopCheck.enforce_levels: eq0.
    - clear H Heqcall. reflexivity.
  Qed.

  Definition to_valuation (v : Level.t -> nat) : valuation :=
    {| valuation_mono := fun s => Pos.of_nat (v (Level.level s));
       valuation_poly := fun i => v (Level.lvar i);
    |}.

  Definition of_valuation V (v : valuation) : LevelMap.t nat :=
    let add_val l := LevelMap.add l (val v l) in
    LevelSet.fold add_val V (LevelMap.empty _).

  Import LoopCheck.Impl.Abstract (clause_sem, clauses_sem, clauses_sem_union, to_val, to_Z_val).

  Lemma clauses_sem_subset {S} {SL : Semilattice.Semilattice S Q.t} {v cls cls'} : clauses_sem v cls -> cls' ⊂_clset cls -> clauses_sem v cls'.
  Proof.
    now move=> hall hsub cl /hsub.
  Qed.

  Import Semilattice.

  Lemma clauses_sem_clauses_of_le (V : Level.t -> Z) l r :
    clauses_sem V (clauses_of_le l r) ->
    (interp_prems V l ≤ interp_prems V r)%sl.
  Proof.
    rewrite /clauses_sem.
    intros hl. red in hl.
    setoid_rewrite clauses_of_le_spec in hl.
    move: l hl. apply: elim.
    - move => le he.
      rewrite interp_prems_singleton.
      move: (he (r, le)) => /fwd.
      exists le. split => //. now apply LevelExprSet.singleton_spec.
      cbn. lia.
    - intros le x ih hnin ih'.
      rewrite interp_prems_add.
      forward ih. intros x0 [x1 [hin ->]].
      move: (ih' (r, x1)) => /fwd. exists x1. split => //. apply LevelExprSet.add_spec. now right.
      auto.
      move: (ih' (r, le)) => /fwd. exists le. split => //.  apply LevelExprSet.add_spec. now left.
      cbn. cbn in ih. lia.
  Qed.

  Lemma to_atoms_singleton l k  : to_atoms (Universe.singleton (l, k)) = NES.singleton (l, Z.of_nat k).
  Proof.
    apply NES.equal_exprsets.
    rewrite /to_atoms //=.
  Qed.

  Lemma to_atoms_add le u : to_atoms (Universe.add le u) = NES.add (to_atom le) (to_atoms u).
  Proof. apply NES.equal_exprsets => //=.
    move=> [l k].
    rewrite LevelExprSet.add_spec.
    split.
    - move/to_levelexprzset_spec_2 => [].
      rewrite Universes.LevelExprSet.add_spec => -[<-|hin].
      * move=> pos.
        left. cbn. lia_f_equal.
      * move=> pos. right.
        apply to_levelexprzset_spec_1 in hin.
        rewrite Z2Nat.id // in hin.
    - move=> [eq|hin].
      destruct le; noconf eq.
      * apply to_levelexprzset_spec_1.
        rewrite Universes.LevelExprSet.add_spec.
        now left.
      * apply to_levelexprzset_spec_2 in hin as [hin pos].
        have [k' eq] : exists z, Z.of_nat z = k. exists (Z.to_nat k).
        rewrite Z2Nat.id //. subst k.
        apply to_levelexprzset_spec_1.
        rewrite Nat2Z.id in hin.
        rewrite Universes.LevelExprSet.add_spec. now right.
  Qed.

  Lemma interp_prem_to_atom v le : interp_expr (to_Z_val v) (to_atom le) = Z.of_nat (val (to_valuation v) le).
  Proof.
    destruct le => //=. cbn.
    destruct t0.
    - (* lzero is forced to have value 0, has it should stay maximal *) todo "handle lzero".
    - todo "handle monos".
    - cbn. unfold to_Z_val; cbn. lia.
  Qed.

  Lemma interp_prems_to_atoms v l : interp_prems (to_Z_val v) (to_atoms l) = Z.of_nat (Universes.val (to_valuation v) l).
  Proof.
    move: l.
    apply Universe.elim.
    - intros [l k].
      rewrite to_atoms_singleton interp_prems_singleton.
      rewrite val_singleton.
      now rewrite (interp_prem_to_atom v (l, k)).
    - intros le x eq nin.
      rewrite to_atoms_add interp_prems_add.
      rewrite val_add.
      rewrite interp_prem_to_atom. cbn in *.
      lia.
  Qed.

  Lemma clauses_sem_val m l r :
    clauses_sem (to_Z_val (LoopCheck.valuation m)) (clauses_of_le (to_atoms l) (to_atoms r)) ->
    Universes.val (to_valuation (LoopCheck.valuation m)) l <=
    Universes.val (to_valuation (LoopCheck.valuation m)) r.
  Proof.
    move/clauses_sem_clauses_of_le.
    have he := interp_prems_to_atoms (LoopCheck.valuation m) l.
    have he' := interp_prems_to_atoms (LoopCheck.valuation m) r.
    cbn in *. lia.
  Qed.

  Lemma model_satisfies m :
    satisfies (to_valuation (LoopCheck.valuation (model m))) (constraints m).
  Proof.
    destruct m as [m cstrs repr repr_inv]. cbn.
    have val := LoopCheck.model_valuation m.
    move=> cstr /repr /(clauses_sem_subset val).
    intros cls. destruct cstr as [[l []] r]; cbn.
    constructor. cbn in cls. now apply clauses_sem_val.
    constructor. cbn in cls.
    rewrite clauses_sem_union in cls. destruct cls as [hl hr].
    eapply Nat.le_antisymm; now apply clauses_sem_val.
  Qed.

  Lemma of_valuation_spec V v :
    forall l k, LevelMap.MapsTo l k (of_valuation V v) <->
      (LevelSet.In l V /\ k = val v l).
  Proof.
    intros l k.
    rewrite /of_valuation.
    eapply LevelSetProp.fold_rec.
    - move=> s' he.
      rewrite LevelMapFact.F.empty_mapsto_iff.
      split => // -[] hin' _. lsets.
    - move=> x a s' s'' hin hnin hadd ih.
      rewrite LevelMapFact.F.add_mapsto_iff /Level.eq ih.
      rewrite hadd. firstorder; subst; auto.
      destruct (Classes.eq_dec x l); firstorder. subst. now left.
  Qed.

  Lemma interp_level_of_valuation {V v l} :
    LevelSet.In l V ->
    to_Z_val (to_val (of_valuation V v)) l = Z.of_nat (val v l).
  Proof.
    move=> hin.
    rewrite /to_Z_val /to_val.
    elim: find_spec => [k /of_valuation_spec []|] => //.
    { intros ? ->. reflexivity. }
    elim. exists (val v l). rewrite [LevelMap.Raw.MapsTo _ _ _]of_valuation_spec.
    split => //.
  Qed.


  Lemma to_of_valuation V v :
    forall l, LevelSet.In l.1 V -> val (to_valuation (to_val (of_valuation V v))) l = val v l.
  Proof.
    intros l hin.
    destruct l; cbn. f_equal.
    destruct e; cbn => //. todo ("mono valuation").
    unfold to_val.
    destruct (find_spec (Level.lvar n0) (of_valuation V v)).
    - eapply of_valuation_spec in H.
      destruct H as [hin' ->]. cbn in *.
      reflexivity.
    - cbn in *. elim H.
      exists (val v (Level.lvar n0)).
      rewrite [LevelMap.Raw.MapsTo _ _ _]of_valuation_spec.
      split => //.
  Qed.

  Lemma to_of_valuation_univ V v :
    forall u : Universe.t, LevelSet.Subset (Universe.levels u) V ->
    val (to_valuation (to_val (of_valuation V v))) u = val v u.
  Proof.
    apply: Universe.NES.elim.
    - move=> le incl.
      cbn.
      rewrite to_of_valuation.
      apply incl.
      rewrite Universe.levels_spec. exists le.2.
      now destruct le; apply Universes.LevelExprSet.singleton_spec.
      reflexivity.
    - move=> le u hincl hnin hincl'.
      have hl : Universe.levels u ⊂_lset V.
      { intros ? hin. apply hincl'.
        rewrite Universe.levels_spec in hin.
        destruct hin as [k hin].
        rewrite Universe.levels_spec. exists k.
        rewrite Universes.LevelExprSet.add_spec. now right. }
      rewrite !val_add // hincl //.
      forward hincl by assumption.
      rewrite to_of_valuation //.
      apply hincl'.
      rewrite Universe.levels_spec. exists le.2.
      rewrite Universes.LevelExprSet.add_spec. now left; destruct le.
  Qed.

  Lemma clauses_levels_mon {cls cls'} :
    cls ⊂_clset cls' ->
    clauses_levels cls ⊂_lset clauses_levels cls'.
  Proof.
    move=> sub l /clauses_levels_spec; rewrite clauses_levels_spec.
    firstorder.
  Qed.
  (* Lemma in_to_clauses_elem {l k a}  : *)

  Definition check m (c : UnivConstraint.t) : bool :=
    LoopCheck.check m.(model) (to_constraint c).
  Derive Signature for satisfies0.

  Lemma in_to_clauses_sem {l r V v} :
    LevelSet.Subset (univ_constraint_levels (l, ConstraintType.Le, r)) V ->
    val v l <= val v r ->
    forall cl, LevelExprSet.Exists (fun lk : LevelExprSet.elt => cl = (to_atoms r, lk)) (to_levelexprzset l) ->
    clause_sem (to_Z_val (to_val (of_valuation V v))) cl.
  Proof.
    move=> hlev leq [prems concl].
    move=> [] [l'' k'] [] /to_levelexprzset_spec_2 [] inl' pos ->.
    cbn -[le]. rewrite interp_prems_to_atoms.
    rewrite to_of_valuation_univ.
    { intros ? hin; apply hlev. cbn. lsets. }
    transitivity (Z.of_nat (val v l)).
    rewrite interp_level_of_valuation.
    { apply hlev; cbn.
      eapply LevelSet.union_spec; left. eapply Universe.levels_spec.
      now eexists. }
    have vle := val_In_le l v _ inl'. cbn in vle.
    cbn; u; lia.
    cbn; u; lia.
  Qed.

  Lemma satisfies_clauses_sem v m V :
    LoopCheck.levels (model m) ⊂_lset V ->
    satisfies v (constraints m) ->
    clauses_sem (to_Z_val (to_val (of_valuation V v))) (LoopCheck.clauses (model m)).
  Proof.
    have repr := repr_constraints_inv m.
    have repr_inv := repr_constraints m.
    move=> hsub hs cl /[dup] hin /repr [] c [] /[dup] /repr_inv hr /hs sat.
    destruct c as [[l' d] r].
    move=> /[dup] intocl.
    rewrite LoopCheck.to_clauses_spec.
    depelim sat. cbn -[clause_sem].
    - apply in_to_clauses_sem; auto.
      cbn; intros le inr. apply hsub.
      apply (LoopCheck.clauses_levels_declared m.(model)).
      move/clauses_levels_mon: hr; apply.
      rewrite in_to_clauses_levels.
      rewrite in_constraint_levels_to_constraint //=.
    - cbn. move=> [].
      * apply in_to_clauses_sem; [|lia].
        cbn; intros le inr.
        apply hsub, (LoopCheck.clauses_levels_declared m.(model)).
        move/clauses_levels_mon: hr; apply.
        rewrite in_to_clauses_levels.
        rewrite in_constraint_levels_to_constraint //=.
      * apply in_to_clauses_sem; [|lia].
        cbn; intros le inr.
        apply hsub, (LoopCheck.clauses_levels_declared m.(model)).
        move/clauses_levels_mon: hr; apply.
        rewrite in_to_clauses_levels.
        rewrite in_constraint_levels_to_constraint //=. lsets.
  Qed.

  Lemma clauses_sem_satisfies {v V c} :
    univ_constraint_levels c ⊂_lset V ->
    clauses_sem (to_Z_val (to_val (of_valuation V v))) (LoopCheck.to_clauses (to_constraint c)) ->
    satisfies0 v c.
  Proof.
    intros hin hsem. destruct c as [[l []] r]; cbn in *.
    - constructor.
      move/clauses_sem_clauses_of_le: hsem.
      rewrite !interp_prems_to_atoms.
      rewrite !to_of_valuation_univ. lsets. lsets. cbn; lia.
    - constructor.
      rewrite clauses_sem_union in hsem. destruct hsem as [hsem hsem'].
      move/clauses_sem_clauses_of_le: hsem.
      move/clauses_sem_clauses_of_le: hsem'.
      rewrite !interp_prems_to_atoms.
      rewrite !to_of_valuation_univ. lsets. lsets. cbn; lia.
  Qed.

  Lemma val_respects cls v : @respects _ _ Z _ (horn_semi cls) _ Zsemilattice (fun u => interp_prems v u).
  Proof.
    split; cbn.
    - intros n x. rewrite interp_add_prems; cbn. lia.
    - intros x y. rewrite interp_prems_union; cbn. lia.
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
    rewrite /relations_of_constraints.
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
    rewrite /clauses_of_eq. split.
    - apply app_Forall.
      * apply Forall_forall => rel.
        have [he he'] := entails_L_relations_of_clauses_le l r.
        red in he, he'.
        rewrite Forall_forall in he'. move/he'.
        intros ent. destruct rel.
        eapply entails_L_all_one_trans; tea.
        constructor. apply entails_L_eq_le_1, entails_c; repeat constructor. constructor.
      * apply Forall_forall => rel.
        have [he he'] := entails_L_relations_of_clauses_le r l.
        red in he, he'.
        rewrite Forall_forall in he'. move/he'.
        intros ent. destruct rel.
        eapply entails_L_all_one_trans; tea.
        constructor. apply entails_L_eq_le_2, entails_c; repeat constructor. constructor.
    - constructor; [|constructor].
      apply entails_L_eq_antisym. split.
      * have [he he'] := entails_L_relations_of_clauses_le l r.
        eapply entails_L_rels_subset. depelim he. tea.
        red. intros r' hin. rewrite in_app_iff. now left.
      * have [he he'] := entails_L_relations_of_clauses_le r l.
        eapply entails_L_rels_subset. depelim he. tea.
        red. intros r' hin. rewrite in_app_iff. now right.
  Qed.

  Lemma entails_L_relations_of_clauses_eq l r :
    relations_of_clauses (l ≡ r) ⊫ℒ [l ≡ r].
  Proof.
    split.
    - constructor. apply entails_L_relations_of_clauses_eq. constructor.
    - apply Forall_forall => rel.
      move/relations_of_clauses_spec => [] prems [] concl [] hin ->.
      move: hin; rewrite /clauses_of_eq Clauses.union_spec => -[] hin.
      * setoid_rewrite equiv_L_rels_eq.
        eapply entails_L_rels_subset; revgoals.
        { intros rel'. rewrite in_app_iff. left. tea. }
        now eapply entails_L_in_cls.
      * setoid_rewrite equiv_L_rels_eq.
        eapply entails_L_rels_subset; revgoals.
        { intros rel'. rewrite in_app_iff. right. tea. }
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
    rewrite of_z_constraints_spec. exists cstr. split => //. now apply hsub.
  Qed.

  Lemma of_z_constraints_add x s :
    of_z_constraints (ZUnivConstraintSet.add x s) =_clset Clauses.union (LoopCheck.to_clauses x) (of_z_constraints s).
  Proof.
    move=> cl; split.
    - move/of_z_constraints_spec => -[] cstr [] hin incl.
      rewrite Clauses.union_spec. rewrite ZUnivConstraintSet.add_spec in hin.
      move: hin => [<-|]. now left.
      move=> ins. right. rewrite of_z_constraints_spec. exists cstr; split => //; now right.
    - rewrite Clauses.union_spec => -[]; destruct x as [[l []] r].
      * move/LoopCheck.to_clauses_spec => [] k [hin] ->.
        rewrite of_z_constraints_spec. eexists; split => //.
        rewrite ZUnivConstraintSet.add_spec; left; trea.
        cbn. now eapply in_clause_of_le.
      * intros hcl; rewrite of_z_constraints_spec //. eexists; split.
        rewrite ZUnivConstraintSet.add_spec; left; trea. exact hcl.
      * rewrite of_z_constraints_spec => -[] cstr [] hin heq.
        rewrite of_z_constraints_spec. exists cstr. split => //.
        rewrite ZUnivConstraintSet.add_spec; now right.
      * rewrite of_z_constraints_spec => -[] cstr [] hin heq.
        rewrite of_z_constraints_spec. exists cstr. split => //.
        rewrite ZUnivConstraintSet.add_spec; now right.
  Qed.

  Lemma relations_of_clauses_constraints_add {x s} :
    (relation_of_constraint x :: relations_of_clauses (of_z_constraints s)) ⊫ℒ
      (relations_of_clauses (of_z_constraints (ZUnivConstraintSet.add x s))).
  Proof.
    rewrite of_z_constraints_add relations_of_clauses_union.
    eapply (entails_L_all_union (x := [_])).
    2:{ reflexivity. }
    now rewrite relation_of_constraint_of_clause.
  Qed.

  Lemma rels_of_z_constraints_spec {cstrs} :
    relations_of_clauses (of_z_constraints cstrs) ⊫ℒ relations_of_constraints cstrs.
  Proof.
    rewrite /relations_of_constraints.
    have he := ZUnivConstraintSetProp.fold_rec
      (P := fun s f => relations_of_clauses (of_z_constraints s) ⊫ℒ f). apply: he.
    - split. constructor. red. apply Forall_forall => [] l r.
      eapply relations_of_clauses_spec in r as [prems [concl [hin heq]]]. subst l.
      eapply of_z_constraints_spec in hin as [cstr [hin ]]. now apply H in hin.
    - move=> x a s' s'' hin hnin hadd hr.
      rewrite entails_equiv_cons.
      split; [|split] => //.
      * have hins'' : ZUnivConstraintSet.In x s''.
        { apply hadd; now left. }
        rewrite -relation_of_constraint_of_clause.
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
        rewrite relations_of_clauses_constraints_add.
        eapply entails_L_clauses_subset_all.
        eapply of_z_constraints_subset.
        apply ZUnivConstraintSetProp.Add_Equal in hadd. now rewrite hadd.
  Qed.

  Lemma equiv_constraints_clauses m :
     relations_of_constraints (to_z_cstrs (constraints m)) ⊫ℒ Clauses.relations_of_clauses (LoopCheck.clauses (model m)).
  Proof.
    have repr := repr_constraints.
    have repr_inv := repr_constraints_inv.
    rewrite -rels_of_z_constraints_spec.
    rewrite -to_clauses_of_z_constraints.
    rewrite (@relations_of_clauses_eq (to_clauses (constraints m)) (LoopCheck.clauses (model m))) //.
    2:{ reflexivity. }
    intros cl; rewrite to_clauses_spec.
    split.
    - move=> [] cstrs [] /repr incl intocl.
      apply incl, intocl.
    - now move/repr_inv.
  Qed.

  (** Lifting interpretation to constraints (on Z). *)

  Section interp.
    Import Semilattice.
    Context {S : Type} {SL : Semilattice S Z}.
    Context (v : Level.t -> S).

    Definition interp_z_cstr c :=
      let '(l, d, r) := c in
      match d with
      | ConstraintType.Le => interp_prems v l ≤ interp_prems v r
      | ConstraintType.Eq => interp_prems v l ≡ interp_prems v r
      end%Z.

    Definition interp_univ_cstr c := interp_z_cstr (to_constraint c).
    Definition interp_univ_cstrs c := UnivConstraintSet.For_all interp_univ_cstr c.

  End interp.

  Section interp_nat.
    Import Semilattice.
    Import -(notations) Universe.
    Context {S : Type} {SL : Semilattice S nat}.
    Context (v : Level.t -> S).

    Definition interp_nat_cstr c :=
      let '(l, d, r) := c in
      match d with
      | ConstraintType.Le => interp_prems v l ≤ interp_prems v r
      | ConstraintType.Eq => interp_prems v l ≡ interp_prems v r
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

  Definition model_val m := (LoopCheck.valuation (model m)).

  Definition model_Z_val m := (to_Z_val (LoopCheck.valuation (model m))).

  Lemma interp_rels_of_m m : interp_rels (model_Z_val m) (relations_of_constraints (to_z_cstrs (constraints m))).
  Proof.
    have hv := (LoopCheck.model_valuation m.(model)).
    red.
    apply Forall_forall. move=> [l r] /relations_of_constraints_spec => -[cl [hin heq]].
    eapply to_z_cstrs_spec_2 in hin as [cstr [hin ->]].
    have hrepr := repr_constraints m _ hin.
    destruct cstr as [[l' []] r']; cbn in heq; noconf heq.
    - rewrite /interp_rel interp_prems_union. cbn in hrepr.
      eapply UnivLoopChecking.clauses_sem_subset in hv; tea.
      apply clauses_sem_clauses_of_le in hv. cbn in hv |- *.
      unfold model_Z_val in *. lia.
    - cbn in hrepr.
      eapply UnivLoopChecking.clauses_sem_subset in hv; tea.
      rewrite /Clauses.clauses_of_eq in hv.
      eapply clauses_sem_union in hv. destruct hv as [hv hv'].
      apply clauses_sem_clauses_of_le in hv.
      apply clauses_sem_clauses_of_le in hv'. cbn in hv, hv' |- *.
      unfold model_Z_val in *; lia.
  Qed.

  (** The constraints in the model are already valid. *)
  Lemma interp_univ_cstrs_of_m m :
    interp_univ_cstrs (model_Z_val m) (constraints m).
  Proof.
    intros uc hin. red.
    have h := repr_constraints m _ hin.
    have hi := interp_rels_of_m m.
    red in hi. rewrite Forall_forall in hi.
    apply to_z_cstrs_spec_1 in hin as [cstrz [hin ->]].
    destruct uc as [[l []] r]; cbn. cbn in h.
    - move: (hi ((to_atoms l ∨ to_atoms r)%nes, to_atoms r)) => /fwd.
      { apply relations_of_constraints_spec. exists (to_atoms l, ConstraintType.Le, to_atoms r).
        cbn. split => //. }
     by rewrite /interp_rel interp_prems_union; unfold model_Z_val in *; cbn; lia.
    - move: (hi (to_atoms l, to_atoms r)) => /fwd.
      { apply relations_of_constraints_spec. exists (to_atoms l, ConstraintType.Eq, to_atoms r).
        cbn. split => //. }
      by [].
  Qed.

  (** Equivalence of interpretations between constraints and relations derived from them *)

  Lemma interp_univ_cstrs_relations {S} {SL : Semilattice S Z} v cstrs :
    interp_univ_cstrs v cstrs <->
    interp_rels v (relations_of_constraints (to_z_cstrs cstrs)).
  Proof.
    rewrite /interp_univ_cstrs.
    split.
    - intros hf. red in hf. red.
      apply Forall_forall. move=> [l r] /relations_of_constraints_spec [[[l' d] r'] [hin heq]].
      cbn in heq; noconf heq. destruct d; noconf heq.
      * eapply to_z_cstrs_spec_2 in hin as [cstr [hin heq]].
        destruct cstr as [[] ?]; noconf heq. specialize (hf _ hin). cbn in hf.
        rewrite /interp_rel interp_prems_union; cbn in *. exact hf.
      * eapply to_z_cstrs_spec_2 in hin as [cstr [hin heq]].
        destruct cstr as [[] ?]; noconf heq. specialize (hf _ hin). cbn in hf.
        exact hf.
    - intros hi uc hin. red in hi. rewrite Forall_forall in hi.
      move: (hi (relation_of_constraint (to_constraint uc))) => /fwd.
      rewrite relations_of_constraints_spec; exists (to_constraint uc); split => //.
      now apply to_z_cstrs_spec_1 in hin as [cstrz [hin ->]].
      destruct uc as [[l []] r] => //=.
      rewrite interp_prems_union //=.
  Qed.

  Lemma interp_cstr_clauses_sem {c} {S} {SL : Semilattice S Q.t} {v : Level.t -> S} :
    interp_univ_cstr v c <-> clauses_sem v (LoopCheck.to_clauses (to_constraint c)).
  Proof.
    rewrite LoopCheck.Impl.Abstract.interp_rels_clauses_sem.
    rewrite relation_of_constraint_of_clause.
    rewrite /Clauses.ISL.interp_rels Forall_tip.
    destruct c as [[l []] r]; cbn => //.
    now rewrite interp_prems_union.
  Qed.

  Lemma interp_cstrs_clauses_sem {m} {S} {SL : Semilattice S Q.t} {v : Level.t -> S} :
    interp_univ_cstrs v (constraints m) <-> clauses_sem v (LoopCheck.clauses (model m)).
  Proof.
    rewrite interp_univ_cstrs_relations.
    rewrite LoopCheck.Impl.Abstract.interp_rels_clauses_sem.
    now rewrite -[Clauses.relations_of_clauses _]equiv_constraints_clauses.
  Qed.

  Lemma to_valuation_val (v : Level.t -> nat) (l : Universes.Level.t) : v l = val (to_valuation v) l.
  Proof.
    destruct l => //=.
    - todo "zero".
    - todo "mono".
  Qed.

  (** Interpretation in the semilattice of natural numbers *)
  Lemma interp_prems_val (v : Level.t -> nat) u :
    Universe.interp_prems v u = Universes.val (to_valuation v) u.
  Proof.
    move: u. refine (Universe.interp_prems_elim v (fun u i => i = val (to_valuation v) u) _ _ _).
    - now intros [l k]; rewrite val_singleton //= /val /Universe.interp_expr to_valuation_val; cbn.
    - move=>[l k] u k' -> hnin.
      rewrite val_add; cbn. now rewrite to_valuation_val; cbn.
  Qed.

  Lemma interp_univ_cstr_nat v cl :
    interp_univ_cstr (to_Z_val v) cl <-> interp_nat_cstr v cl.
  Proof.
    destruct cl as [[l []] r] => //=;
    cbn; rewrite !interp_prems_to_atoms !(interp_prems_val v) /model_val. split. all:lia.
  Qed.

  Lemma interp_univ_cstrs_nat v cl :
    interp_univ_cstrs (to_Z_val v) cl <-> interp_cstrs v cl.
  Proof.
    split; move=> hin cl' /hin; now rewrite interp_univ_cstr_nat.
  Qed.

  Lemma interp_cstrs_of_m m :
    interp_cstrs (model_val m) (constraints m).
  Proof.
    have ha := interp_univ_cstrs_of_m m.
    now apply interp_univ_cstrs_nat.
  Qed.

  Lemma entails_L_completeness {p l r} :
    (forall S (SL : Semilattice S Q.t) (v : Level.t -> S), interp_rels v p -> interp_prems v l ≡ interp_prems v r)%sl ->
    p ⊢ℒ l ≡ r.
  Proof.
    intros hv.
    specialize (hv _ (init_model p) (ids p)).
    forward hv.
    { apply interp_rels_init. }
    rewrite !interp_triv in hv.
    exact hv.
  Qed.

  Definition valid_model m c :=
    (forall S (SL : Semilattice S Q.t) (v : Level.t -> S), interp_univ_cstrs v (constraints m) -> interp_univ_cstr v c).

  Infix "⊩" := valid_model (at level 70, no associativity).

  Theorem check_completeness {m c} :
    check m c <-> m ⊩ c.
  Proof.
    rewrite LoopCheck.check_complete /LoopCheck.valid_entailments /valid_model.
    setoid_rewrite interp_cstrs_clauses_sem.
    split.
    - intros hv S s v hp.
      move: (hv S s v hp).
      now rewrite interp_cstr_clauses_sem.
    - intros hs S SL V hsem.
      move: (hs S SL V) => /fwd //.
      now rewrite interp_cstr_clauses_sem.
  Qed.

  Theorem check_valid_nat {m c} :
    check m c -> (forall (v : Level.t -> nat), interp_cstrs v (constraints m) -> interp_nat_cstr v c).
  Proof.
    rewrite check_completeness.
    intros hv v hp.
    move: (hv Z Zsemilattice (to_Z_val v)).
    rewrite interp_univ_cstr_nat; apply.
    now apply interp_univ_cstrs_nat.
  Qed.

End UnivLoopChecking.
