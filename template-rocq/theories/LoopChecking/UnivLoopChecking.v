(* Distributed under the terms of the MIT license. *)
(* This module provides an instantiation of the deciders for universe checking,
  i.e. for constraints on non-empty level expressions (l, k) where k ∈ 𝐍 *)

From Stdlib Require Import ssreflect ssrfun ssrbool.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils SemiLattice.
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
    unfold eq. decide equality; apply eq_dec.
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

  Lemma clauses_of_le_nempty l r : ~ Clauses.Empty (clauses_of_le l r).
  Proof.
    intros he. red in he. eapply he.
    rewrite !clauses_of_le_spec.
    exists (choose_prems l). split; trea.
    apply choose_prems_spec.
  Qed.

  Lemma to_clauses_ne c : ~ Clauses.Empty (LoopCheck.to_clauses c).
  Proof.
    intros he. red in he. destruct c as [[l []] r]; revgoals.
    - eapply he. apply LoopCheck.to_clauses_spec.
      right. exists (choose_prems r). split; trea. apply choose_prems_spec.
    - eapply he. apply LoopCheck.to_clauses_spec.
      exists (choose_prems l). split; trea. apply choose_prems_spec.
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
      rewrite UnivLoopChecking.Clauses.union_spec => -[].
      * move/(repr_constraints_inv m c') => [] c2 [].
        exists c2. split => //.
        rewrite UnivConstraintSet.add_spec. now right.
      * move=> hin. exists c. split => //.
        rewrite UnivConstraintSet.add_spec. now left.
  Qed.

  Lemma in_clause_levels_of_le lev l r : LevelSet.In lev (clauses_levels (clauses_of_le l r)) <->
    LevelSet.In lev (levels l) \/ LevelSet.In lev (levels r).
  Proof.
    rewrite clauses_levels_spec.
    setoid_rewrite clauses_of_le_spec.
    split.
    - intros [cl [hex hin]].
      apply clause_levels_spec in hin.
      destruct hex as [le [inl ->]]. cbn in *. destruct hin; auto. subst.
      left. now apply LoopCheck.Impl.in_levels.
    - move=> [] hin.
      * eapply levels_spec in hin as [k hin].
        exists (r, (lev, k)). split => //. exists (lev, k). split => //.
        apply clause_levels_spec. now right.
      * eapply levels_spec in hin as [k hin].
        exists (r, choose_prems l). split => //. exists (choose_prems l). split => //.
        apply choose_prems_spec.
        apply clause_levels_spec. left.
        apply levels_spec. now exists k.
  Qed.

  (* Lemma univ_in_add n u : Universes.LevelSet.Equal
    (Universe.levels (Universe.add_prems n u))
    (Universe.levels u).
  Proof.
    intros l. rewrite !Universe.levels_spec.
    rw Universe.add_spec.
    firstorder. subst n. destruct n; noconf H; cbn. now exists n0.
    exists (n + x), (l, x). split => //.
  Qed. *)

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

  Lemma clauses_sem_subset {v cls cls'} : clauses_sem v cls -> cls' ⊂_clset cls -> clauses_sem v cls'.
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

  Lemma to_atoms_singleton l k  : to_atoms (Universe.singleton (l, k)) = singleton (l, Z.of_nat k).
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

  Lemma clauses_sem_union v cls cls' : clauses_sem v (Clauses.Clauses.union cls cls') <->
    clauses_sem v cls /\ clauses_sem v cls'.
  Proof.
    unfold clauses_sem. split.
    intros hf. split; eapply clauses_sem_subset; tea; clsets.
    intros []. intros cl. rewrite Clauses.Clauses.union_spec.
    specialize (H cl). specialize (H0 cl). intros []; auto.
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
      rewrite interp_prem_to_atom. cbn. lia.
  Qed.

  Lemma clauses_sem_val m l r :
    clauses_sem (to_Z_val (to_val (LoopCheck.valuation m))) (clauses_of_le (to_atoms l) (to_atoms r)) ->
    Universes.val (to_valuation (to_val (LoopCheck.valuation m))) l <=
    Universes.val (to_valuation (to_val (LoopCheck.valuation m))) r.
  Proof.
    move/clauses_sem_clauses_of_le.
    have he := interp_prems_to_atoms (to_val (LoopCheck.valuation m)) l.
    have he' := interp_prems_to_atoms (to_val (LoopCheck.valuation m)) r.
    cbn in *. lia.
  Qed.

  Lemma model_satisfies m :
    satisfies (to_valuation (to_val (LoopCheck.valuation (model m)))) (constraints m).
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

  Lemma to_of_valuation V v :
    forall l, LevelSet.In l.1 V -> val (to_valuation (to_val (of_valuation V v))) l = val v l.
  Proof.
  Admitted.

  Lemma to_of_valuation_univ V v :
    forall u : Universe.t, LevelSet.Subset (Universe.levels u) V ->
    val (to_valuation (to_val (of_valuation V v))) u = val v u.
  Proof.
  Admitted.

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
      destruct (eq_dec x l); firstorder. subst. now left.
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

  Definition entails_cstr cstrs c :=
    entails_clauses (to_clauses cstrs) (LoopCheck.to_clauses (to_constraint c)).

  Definition entails_z_cstr cstrs c :=
    entails_clauses (of_z_constraints cstrs) (LoopCheck.to_clauses c).

  Definition entails_cstrs cstrs cstrs' :=
    entails_clauses (of_z_constraints cstrs) (of_z_constraints cstrs').

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

  (* Lemma to_z_cstrs_spec {cstrs} :
    forall c, UnivConstraintSet.In c cstrs <-> ZUnivConstraintSet.In (to_constraint c) (to_z_cstrs cstrs).
  Proof.
    intros c; split.
    - by move/to_z_cstrs_spec_1 => [] cstrz [] hin heq; subst cstrz.
    - move/to_z_cstrs_spec_2 => [] cstr [] hin heq.
      destruct c as [[] ?], cstr as [[] ?]; cbn in heq. noconf heq. *)


  Lemma check_valid m c :
    check m c <-> entails_cstr (constraints m) c.
  Proof.
    rewrite /check LoopCheck.check_spec.
    rewrite /entails_clauses.
    enough ((LoopCheck.clauses (model m)) =_clset (to_clauses (constraints m))).
    { split; intros ? ?.
      move/H0. now rewrite H.
      move/H0. now rewrite H. }
    intros cl.
    rewrite to_clauses_spec.
    split.
    - now move/(repr_constraints_inv m).
    - intros [cstr [hin incl]].
      eapply (repr_constraints m); tea.
  Qed.

  Lemma val_respects cls v : @respects _ _ Z _ (horn_semi cls) _ Zsemilattice (fun u => interp_prems v u).
  Proof.
    split; cbn.
    - intros n x. rewrite interp_add_prems; cbn. lia.
    - intros x y. rewrite interp_prems_union; cbn. lia.
  Qed.

  Definition valid_entailments cls cls' :=
    forall A {SL : Semilattice A Z} V, clauses_sem V cls -> clauses_sem V cls'.

  Lemma entails_cstr_spec cstrs c :
    (exists V, clauses_sem V (of_z_constraints cstrs)) ->
    entails_z_cstr cstrs c ->
      (forall cl, Clauses.In cl (LoopCheck.to_clauses c) ->
             valid_entailment (of_z_constraints cstrs) cl).
  Proof.
    rewrite /entails_cstr /entails_clauses.
    move=> ev hf cl /hf he. red.
    now eapply clauses_sem_entails in he.
  Qed.

  Definition relation_of_constraint c :=
    let '(l, d, r) := c in
    match d with
    | ConstraintType.Le => (l ∪ r, r)
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

  Definition presentation_of cstrs :=
    {| V := levels_of_z_constraints cstrs;
       C := relations_of_constraints cstrs |}.


  Definition presentation_of_clauses cls :=
    {| V := Clauses.clauses_levels cls;
       C := relations_of_clauses cls |}.


  Lemma entails_clauses_le {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Le, r) cstrs ->
    of_z_constraints cstrs ⊢a r → l.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    rewrite of_z_constraints_spec. eexists; split; tea.
    now apply in_clause_of_le.
  Qed.

  Lemma entails_clauses_eq_left {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Eq, r) cstrs ->
    of_z_constraints cstrs ⊢a r → l.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    rewrite of_z_constraints_spec. eexists; split; tea.
    rewrite LoopCheck.to_clauses_spec. left. exists l'. split => //.
  Qed.

  Lemma entails_clauses_eq_right {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Eq, r) cstrs ->
    of_z_constraints cstrs ⊢a l → r.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    rewrite of_z_constraints_spec. eexists; split; tea.
    rewrite LoopCheck.to_clauses_spec. right. exists l'. split => //.
  Qed.

  Lemma entails_clauses_eq_cstr {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Eq, r) cstrs ->
    of_z_constraints cstrs ⊢ℋ l ≡ r.
  Proof.
    intros hin.
    apply Theory.eq_antisym.
    split.
    - rewrite Theory.to_entails_all. now apply entails_clauses_eq_left.
    - rewrite Theory.to_entails_all. now apply entails_clauses_eq_right.
  Qed.

  Lemma entails_clauses_le_cstr {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Le, r) cstrs ->
    of_z_constraints cstrs ⊢ℋ l ⋞ r.
  Proof.
    intros hin.
    rewrite Theory.to_entails_all. now apply entails_clauses_le.
  Qed.

  Lemma presentation_of_clauses_spec cls prems concl :
    Clauses.In (prems, concl) cls ->
    In (NES.singleton concl ∨ prems, prems) (C (presentation_of_clauses cls)).
  Proof.
    rewrite /presentation_of_clauses //=.
    move/relations_of_clauses_spec_inv => //=.
  Qed.
    (* - move/relations_of_clauses_spec => [] prems' [] concl' [hin heq].
      have eqprems : prems = prems'.
      noconf heq. *)


  Lemma entails_L_clauses_all {cstrs s t} :
    (relations_of_clauses (of_z_constraints cstrs)) ⊢ℒ s ≡ t ->
    (relations_of_constraints cstrs) ⊢ℒ s ≡ t.
  Proof.
    induction 1; try solve [econstructor; eauto]. cbn in H.
    move/relations_of_clauses_spec: H => [prems [concl [hin heq]]].
    noconf heq.
    move/of_z_constraints_spec: hin => [cstr [hin hin']].
    destruct cstr as [[l d] r].
    eapply LoopCheck.to_clauses_spec in hin'.
    destruct d; eapply entails_L_le_eq.
    - destruct hin' as [? [hin' heq]]. noconf heq.
      eapply entails_L_le_trans with l.
      * now eapply entails_L_in.
      * constructor. cbn. rewrite relations_of_constraints_spec.
        eexists; split; tea. now cbn.
    - destruct hin' as [hin'|hin'];
      destruct hin' as [? [hin' heq]]; noconf heq.
      * eapply entails_L_le_trans with l.
        + now eapply entails_L_in.
        + eapply entails_L_eq_le_1.
          constructor. cbn. rewrite relations_of_constraints_spec.
          eexists; split; tea. cbn. now cbn.
      * eapply entails_L_le_trans with r.
        + now eapply entails_L_in.
        + eapply entails_L_eq_le_1. apply entails_sym.
          constructor. cbn. rewrite relations_of_constraints_spec.
          eexists; split; tea. cbn. now cbn.
  Qed.

  Lemma entails_L_clauses_le {cstrs s t} :
    entails_L_clauses (relations_of_clauses (of_z_constraints cstrs)) (s ⋞ t) ->
    relations_of_constraints cstrs ⊢ℒ s ≤ t.
  Proof.
    intros hf. do 2 red in hf. rw_in clauses_of_le_spec hf.
    eapply entails_L_split.
    move=> le hin.
    move: (hf (t, le)) => /fwd.
    { exists le; split => //. }
    move=> h; red in h. cbn in h.
    now eapply entails_L_clauses_all in h.
  Qed.

  Lemma entails_L_clauses_of_eq {cstrs s t} :
    entails_L_clauses (relations_of_clauses (of_z_constraints cstrs)) (s ≡ t) ->
    relations_of_constraints cstrs ⊢ℒ s ≡ t.
  Proof.
    intros hf. do 2 red in hf.
    eapply entails_L_eq_antisym.
    all: apply entails_L_clauses_le.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
  Qed.

  Definition entails_L_cstr p c :=
    let '(l, d, r) := c in
    match d with
    | ConstraintType.Le => p ⊢ℒ l ≤ r
    | ConstraintType.Eq => p ⊢ℒ l ≡ r
    end.

  Lemma entails_L_clauses_cstr {cstrs c} :
    entails_L_clauses (relations_of_clauses (of_z_constraints cstrs)) (LoopCheck.to_clauses c) ->
    entails_L_cstr (relations_of_constraints cstrs) c.
  Proof.
    destruct c as [[l []] r].
    - cbn. apply entails_L_clauses_le.
    - cbn. apply entails_L_clauses_of_eq.
  Qed.

  Definition entails_L_cstrs p cstrs :=
    ZUnivConstraintSet.For_all (entails_L_cstr p) cstrs.

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

    Definition interp_univ_cstrs c :=
      UnivConstraintSet.For_all interp_univ_cstr c.

  End interp.

  Structure semilattice :=
    { carrier :> Type;
      sl : Semilattice carrier Z }.

  Definition Z_semilattice := {| carrier := Z; sl := _ |}.

  Instance semlattice_Semilattice (s : semilattice) : Semilattice (carrier s) Z := sl s.

  Definition valid_relation rels c :=
    (forall (s : semilattice) (v : Level.t -> s), interp_rels v rels -> interp_rel v c).

  Definition valid_constraint rels c :=
    (forall (s : semilattice) (v : Level.t -> s), interp_rels v rels -> interp_z_cstr v c).

  Definition valid_cstrs p cstrs :=
    ZUnivConstraintSet.For_all (valid_constraint p) cstrs.


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
(*
  Lemma clauses_of_relations_of_z_constraints {cstrs} :
     Clauses.eq (clauses_of_relations (relations_of_constraints cstrs)) (of_z_constraints cstrs).
  Proof.
    intros cl; split. rewrite of_z_constraints_spec.
    - move/clauses_of_relations_spec => [[l r]] [] /relations_of_constraints_spec => -[] [[u []] v] [] hin heq //=.
      * cbn in heq. noconf heq.
        cbn. move/Clauses.union_spec. => -[] /clauses_of_le_spec => -[] le [].
        rewrite LevelExprSet.union_spec => -[] hin' eq.
        + rewrite eq. eexists; split; tea. rewrite LoopCheck.to_clauses_spec. exists le; split => //.
        + subst cl. eexists (u, ConstraintType.Le, v); split; tea. rewrite LoopCheck.to_clauses_spec. exists le; split => //. *)


  Lemma completeness_eq_cstrs cstrs s t :
    relations_of_constraints cstrs ⊢ℒ s ≡ t <->
    entails_z_cstr cstrs (s, ConstraintType.Eq, t).
  Proof.
    unfold entails_z_cstr.
    split.
    - intros h; depind h; cbn.
      * move: H => //=; rewrite relations_of_constraints_spec => -[] [[l' []] r'] [hin heq]; noconf heq.
        eapply Theory.le_spec.
        now apply entails_clauses_le_cstr.
        now eapply entails_clauses_eq_cstr.
      * eapply Theory.eq_refl.
      * now eapply Theory.eq_sym.
      * now eapply Theory.eq_trans.
      * now eapply Theory.succ_congr.
      * now eapply Theory.succ_inj.
      * now eapply Theory.join_congr_left.
      * eapply Theory.join_assoc.
      * eapply Theory.join_idem.
      * eapply Theory.join_comm.
      * eapply Theory.join_succ.
      * eapply Theory.succ_join.
    - move/entails_ℋ_entails_L; apply entails_L_clauses_of_eq.
  Qed.

  Lemma completeness_le cstrs s t :
    relations_of_constraints cstrs ⊢ℒ s ≤ t <->
    entails_z_cstr cstrs (s, ConstraintType.Le, t).
  Proof.
    unfold entails_z_cstr.
    split.
    - move/completeness_eq_cstrs. cbn.
      intros h; red in h. cbn in h.
      eapply Theory.le_spec. now rewrite /C.le.
    - move/entails_ℋ_entails_L. apply entails_L_clauses_le.
  Qed.

  Import LoopCheck.Impl.I.Model.Model.Clauses.FLS.

  Definition presentation_entails cstrs c :=
    let '(l, d, r) := to_constraint c in
    match d with
    | ConstraintType.Le => relations_of_constraints (to_z_cstrs cstrs) ⊢ℒ l ≤ r
    | ConstraintType.Eq => relations_of_constraints (to_z_cstrs cstrs) ⊢ℒ l ≡ r
    end.

  Lemma check_valid_pres m c :
    check m c <-> presentation_entails (constraints m) c.
  Proof.
    rewrite check_valid.
    destruct c as [[l []] r]; cbn.
    - rewrite completeness_le.
      rewrite /entails_cstr /entails_z_cstr.
      now rewrite to_clauses_of_z_constraints.
    - rewrite completeness_eq_cstrs.
      rewrite /entails_cstr /entails_z_cstr.
      now rewrite to_clauses_of_z_constraints.
  Qed.

  Section SemiLatticeInterp.
    Import Semilattice.


  Lemma presentation_entails_valid_eq {p l r} :
    p ⊢ℒ l ≡ r -> valid_constraint p (l, ConstraintType.Eq, r).
  Proof.
    move/presentation_entails_valid_rel.
    rewrite /valid_relation /valid_constraint /interp_z_cstr //=.
  Qed.

  Lemma presentation_entails_valid_le {p l r} :
    p ⊢ℒ l ≤ r -> valid_constraint p (l, ConstraintType.Le, r).
  Proof.
    rewrite /valid_constraint /interp_z_cstr //=.
    move/presentation_entails_valid_eq => vc v hc.
    specialize (vc v hc). cbn in vc.
    rewrite interp_prems_union in vc. apply vc.
  Qed.

  Lemma presentation_entails_valid {p c} :
    entails_L_cstr p c -> valid_constraint p c.
  Proof.
    destruct c as [[l []] r]; cbn.
    - apply presentation_entails_valid_le.
    - apply presentation_entails_valid_eq.
  Qed.

  Lemma presentation_entails_satisfies {p cstrs} :
    entails_L_cstrs p cstrs -> valid_cstrs p cstrs.
  Proof.
    intros ha c hin. specialize (ha c hin).
    now apply presentation_entails_valid.
  Qed.

  (* Lemma entails_L_cstrs_spec {p cstrs} :
    entails_L_cstrs p cstrs <-> entails_L_clauses p (of_z_constraints cstrs).
  Proof.
    rewrite /entails_L_cstrs.
    split => //.
    - intros hf cl hin.
      eapply of_z_constraints_spec in hin as [cstr' [hin hin']].
      specialize (hf cstr' hin).
      destruct cstr' as [[l []] r]. cbn in hf.
      eapply LoopCheck.to_clauses_spec in hin'.
      destruct hin' as [le [hin' eq]]. noconf eq. red. cbn.
      apply entails_L_le_trans with l => //. now eapply entails_L_in.
      cbn in hf.
      eapply LoopCheck.to_clauses_spec in hin'.
      destruct hin' as [[le [hin' eq]] | [le [hin' eq]]]; noconf eq; red; cbn.
      apply entails_L_le_trans with l => //. now eapply entails_L_in. now apply entails_L_eq_le_1.
      apply entails_L_le_trans with r => //. now eapply entails_L_in. now apply entails_L_eq_le_2.
    - intros hf c hin.
      admit.
  Admitted. *)


  (* Lemma model_valuation_of_cstrs : interp_rels (LoopCheck.valuation m) *)

  Definition model_Z_val m := (to_Z_val (to_val (LoopCheck.valuation (model m)))).


  Lemma interp_rels_of_m m : interp_rels (model_Z_val m) (relations_of_constraints (to_z_cstrs (constraints m))).
  Proof.
    have hv := (LoopCheck.model_valuation m.(model)).
    red.
    apply Forall_forall. move=> [l r] /relations_of_constraints_spec => -[cl [hin heq]].
    eapply to_z_cstrs_spec_2 in hin as [cstr [hin ->]].
    have hrepr := repr_constraints m _ hin.
    destruct cstr as [[l' []] r']; cbn in heq; noconf heq.
    - rewrite /interp_rel interp_prems_union. cbn in hrepr.
      eapply clauses_sem_subset in hv; tea.
      apply clauses_sem_clauses_of_le in hv. cbn in hv |- *.
      unfold model_Z_val in *. lia.
    - cbn in hrepr.
      eapply clauses_sem_subset in hv; tea.
      rewrite /Clauses.clauses_of_eq in hv.
      eapply clauses_sem_union in hv. destruct hv as [hv hv'].
      apply clauses_sem_clauses_of_le in hv.
      apply clauses_sem_clauses_of_le in hv'. cbn in hv, hv' |- *.
      unfold model_Z_val in *; lia.
  Qed.

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

  Lemma prop_dec (b : bool) P : b <-> P -> (b = false <-> ~ P).
  Proof. intuition. now subst b. destruct b => //. destruct (H (H0 eq_refl)). Qed.

  Definition invalid_cstr v c :=
    let '(l, d, r) := c in
    match d with
    | ConstraintType.Eq => interp_prems v (to_atoms l) <> interp_prems v (to_atoms r)
    | ConstraintType.Le => ~ (interp_prems v (to_atoms l) <= interp_prems v (to_atoms r))%Z
    end.

  Section Completeness.

    Definition add_presentation eq p :=
      {| V := p.(V); C := eq :: p.(C) |}.

    Definition relation_levels (r : rel) := NES.levels r.1 ∪ NES.levels r.2.

    Definition wf_presentation p :=
      forall r, List.In r p.(C) -> relation_levels r ⊂_lset p.(V).

    Definition levels_position (l : Level.t) (ls : LevelSet.t) i :=
      List.nth_error (LevelSet.elements ls) i = Some l.

    Equations level_position (l : Level.t) (ls : list Level.t) : option nat :=
    level_position l [] := None ;
    level_position l (x :: xs) with Level.eqb l x :=
      { | true => Some 0
        | false with level_position l xs :=
          | None => None
          | Some n => Some (S n) }.

    Definition levelexpr_pos (l : LevelExpr.t) (ls : LevelSet.t) :=
      match level_position l.1 (LevelSet.elements ls) with
      | None => 0
      | Some pos =>  LevelSet.cardinal ls * Z.to_nat l.2 + pos
      end.

    Section Enum.

    Inductive enumeration : premises × premises -> Type :=
    | enum_single le le' : enumeration (singleton le, singleton le')
    | enum_add_left le (u v : premises) : ~ LevelExprSet.In le u -> enumeration (u, v) -> enumeration (NES.add le u, v)
    | enum_add_right le (u v : premises) : ~ LevelExprSet.In le v -> enumeration (u, v) -> enumeration (u, NES.add le v).

    Lemma acc_enum : forall r, enumeration r.
    Proof.
      intros [l r].
      move: l r. apply: NES.elim.
      - intros le.
        apply: NES.elim.
        * intros le'. constructor.
        * intros le' x. now constructor.
      - intros le x ihr nin r. now constructor.
    Qed.
    End Enum.
  Definition strict_subset (s s' : LevelExprSet.t) :=
    LevelExprSet.Subset s s' /\ ~ LevelExprSet.Equal s s'.

(* Lemma strict_subset_incl (x y z : LevelSet.t) : LevelSet.Subset x y -> strict_subset y z -> strict_subset x z.
Proof.
  intros hs []. split => //. lsets.
  intros heq. apply H0. lsets.
Qed. *)

    Definition premises_strict_subset (x y : premises) := strict_subset x y.

    Definition ord := lexprod premises_strict_subset premises_strict_subset.
    Derive Signature for lexprod.

    Lemma premises_incl_singleton (u : premises) le :
      u ⊂_leset (singleton le) -> LevelExprSet.Equal u (singleton le).
    Proof.
      intros incl; split => //.
      - apply incl.
      - intros hin. eapply LevelExprSet.singleton_spec in hin. subst.
        move: u incl. apply: NES.elim.
        * intros le' hs. specialize (hs le'). forward hs. apply LevelExprSet.singleton_spec. lesets.
          apply LevelExprSet.singleton_spec in hs. subst le'.
          now apply LevelExprSet.singleton_spec.
        * intros le' x ih hnin hadd.
          rewrite LevelExprSet.add_spec. right; apply ih.
          intros ? hin. apply hadd. now rewrite LevelExprSet.add_spec; right.
    Qed.

    Lemma subset_add {a l x} :
      ~ LevelExprSet.In l a -> a ⊂_leset NES.add l x -> a ⊂_leset x.
    Proof.
      intros hnin; rewrite -union_add_singleton.
      move=> hsub lk /[dup]/hsub. rewrite union_spec.
      intros [] => //. apply LevelExprSet.singleton_spec in H. subst. contradiction.
    Qed.

    (* Lemma subset_add_2 {a l x} :
      LevelExprSet.In l a -> a ⊂_leset NES.add l x -> a ⊂_leset x.
    Proof.
      intros hnin; rewrite -union_add_singleton.
      move=> hsub lk /[dup]/hsub. rewrite union_spec.
      intros [] => //. apply LevelExprSet.singleton_spec in H. subst. contradiction.
    Qed. *)

    Section LevelExprSetCardinal.

    Import LevelExprSet.
    Import LevelExprSetProp.

    Lemma cardinal_1_is_singleton a : cardinal a = 1 <-> exists x, Equal a (singleton x).
    Proof. Admitted.

    Lemma premises_cardinal (p : premises) : cardinal p > 0.
    Proof. Admitted.

    Lemma not_Equal_exists_diff (p p' : premises) :
      p ⊂_leset p' -> ~ Equal p p' ->
      exists le, (In le p' /\ ~ In le p).
    Proof.
      intros hsub neq.
      pose c := choose (diff p' p).
      case hc : c => [elt|]. move/choose_spec1: hc.
      rewrite diff_spec => -[hin nin]. now exists elt.
      move/choose_spec2: hc => hc.
      have hsub' : p' ⊂_leset p. lesets. elim neq.
      lesets.
    Qed.

    Lemma premises_strict_subset_spec p p' : premises_strict_subset p p' <->
      (p ⊂_leset p') /\ exists le, In le p' /\ ~ In le p.
    Proof.
      split.
      - intros [hincl hneq]. split => //.
        now apply not_Equal_exists_diff.
      - intros [hincl [le [inp' ninp]]].
        split => // => he. rewrite -he in inp'. contradiction.
    Qed.

    Lemma premises_strict_subset_cardinal (p p' : premises) :
      premises_strict_subset p p' -> (cardinal p < cardinal p')%nat.
    Proof.
      rewrite premises_strict_subset_spec => -[incl [le [inp' ninp]]].
      eapply subset_cardinal_lt; tea.
    Qed.

    Lemma cardinal_add {le x} : ~ In le x -> cardinal (add le x) = 1 + cardinal x.
    Proof. lesets. Qed.

    Lemma premises_eq_singleton {a : premises} {x} : a = singleton x :> LevelExprSet.t -> a = NES.singleton x.
    Proof.
      intros he. rewrite -equal_exprsets. cbn. now rewrite he.
    Qed.

    Lemma premises_strict_subset_wf : well_founded premises_strict_subset.
    Proof.
      red. intros a.
      have hr : LevelExprSet.cardinal a <= LevelExprSet.cardinal a by lesets.
      revert hr. generalize a at 2 => a'. move: a' a.
      apply: NES.elim.
      - intros le a. rewrite NES.LevelExprSetProp.singleton_cardinal.
        have carda := premises_cardinal a => cardle.
        have : cardinal a = 1 by lia.
        rewrite cardinal_1_is_singleton => -[x heq].
        move/eq_leibniz/premises_eq_singleton: heq. intros ->.
        constructor. intros y hp.
        destruct hp. eapply premises_incl_singleton in H. contradiction.
      - intros le x accx hnin.
        intros a asub.
        constructor => y.
        move/premises_strict_subset_cardinal => hc.
        apply accx. rewrite cardinal_add // in asub. lia.
    Qed.
    End LevelExprSetCardinal.

    Lemma acc_ord r : Acc ord r.
    Proof.
      apply wf_lexprod; apply premises_strict_subset_wf.
    Qed.
    Instance ord_wf : WellFounded ord.
    Proof. red. exact acc_ord. Qed.

    Definition check_pres_clause p r :=
      LoopCheck.Impl.check_clauses (clauses_of_relations p) (clauses_of_eq r.1 r.2).

    Lemma check_pres_clause_spec p r : p ⊢ℒ r \/ ~ (p ⊢ℒ r).
    Proof. Admitted.

    Lemma premises_strict_subset_add {l} {u : premises} :
      ~ LevelExprSet.In l u -> premises_strict_subset u (NES.add l u).
    Proof.
      intros hnin; rewrite premises_strict_subset_spec.
      rewrite -union_add_singleton. setoid_rewrite union_spec. split.
      - intros l'. rewrite union_spec; lesets.
      - exists l; split => //. right; now apply LevelExprSet.singleton_spec.
    Qed.



  Class Decidable (A : Prop) := dec : A \/ ~ A.
  Arguments dec A {Decidable}.

  Instance dec_entails_L {p s t} : Decidable (p ⊢ℒ s ≡ t).
  Proof.
    red. eapply check_pres_clause_spec.
  Qed.

  Lemma contra_prop A B (decB : Decidable B) : (~ B -> ~ A) -> (A -> B).
  Proof. intros he a. destruct (dec B). exact H. specialize (he H). contradiction. Qed.

  Definition satisfiable (s : semilattice) (r : rels) :=
    exists v, interp_rels (SL := sl s) v r.

  Definition neg_r p e :=
    p ⊢ℒ add_prems 1 e.1 ≤ e.2 \/ p ⊢ℒ add_prems 1 e.2 ≤ e.1.

  Definition consistent (r : rels) :=
    ~ (exists e, r ⊢ℒ e /\ neg_r r e).

  (* Lemma not_provable_neg p l r : ~ (p ⊢ℒ l ≡ r) -> neg_r p l r.
  Proof.
    intros np. red.
    Admitted. *)


  Lemma entails_L_completeness {p l r} :
    (forall (s : semilattice) (v : Level.t -> s), interp_rels v p -> interp_prems v l ≡ interp_prems v r) ->
    p ⊢ℒ l ≡ r.
  Proof.
    intros hv.
    specialize (hv (initial_semilattice p) ids).
    forward hv.
    { apply interp_rels_init. }
    rewrite !interp_triv in hv.
    exact hv.
  Qed.

  Lemma check_completeness {m c} :
    LoopCheck.Impl.Abstract.check_clauses m c <-> (forall (s : semilattice) (v : Level.t -> s), clauses_sem v (LoopCheck.Impl.Abstract.clauses m) -> clauses_sem v c).
  Proof.
    rewrite LoopCheck.Impl.Abstract.check_clauses_spec.
    split.
    - move/entails_ℋ_entails_L.
      move=> ent s v hyps cl /ent.
      admit.
    - intros valid.
      Search entails_clauses.
      Set Printing All.
      rewrite /entails_L_clause.
  Qed.

  Lemma check_completeness {m c} :
    check m c <-> (forall (s : semilattice) (v : Level.t -> s), interp_univ_cstrs v (constraints m) -> interp_univ_cstr v c).
  Proof.
    destruct check eqn:hc.
    - split => // _ s v hu.
      eapply check_valid_pres in hc.
      destruct c as [[l []] r]; cbn in hc.
      * red in hu. have := presentation_entails_satisfies hc. v => /fwd.
        { admit. }
        rewrite interp_prems_union. cbn. lia.
      * have := presentation_entails_satisfies hc v => /fwd.

(*
  Lemma satisfies_entails_presentation {m c} :
    check m c = false <-> exists v, interp_univ_cstrs v (constraints m) -> invalid_cstr v c.
  Proof.
    split; revgoals.
    - intros [v hv].

      have vm := LoopCheck.model_valuation (model m).

      intros he. eapply presentation_entails_valid in he.
      red in he. intros v hv. apply (he v). cbn.
      now rewrite -interp_univ_cstrs_relations.
    - intros hv.
      have hvm := (LoopCheck.model_valuation m.(model)).
      red.
      specialize (hv (LoopCheck.valuation m.(model))).
      forward hv. apply interp_univ_cstrs_of_m. cbn in hv.
      destruct c as [[l []] r]; cbn in *.

      eapply





      apply interp_univ_cstrs_of_m.
      apply he. cbn.
      apply interp_rels_of_m.
    - move=> [v [ics ic]]. *)


  Lemma satisfies_entails_presentation {m c} :
    check m c <-> (forall v, interp_univ_cstrs v (constraints m) -> interp_univ_cstr v c).
  Proof.
    destruct check eqn:hc.
    - split => // _ v hu.
      eapply check_valid_pres in hc.
      destruct c as [[l []] r]; cbn in hc.
      * have := presentation_entails_satisfies hc v => /fwd.
        { admit. }
        rewrite interp_prems_union. cbn. lia.
      * have := presentation_entails_satisfies hc v => /fwd.


    rewrite check_
    split.
    -
    intros hv.
    have [v hc] : exists v, interp_rels v (C p).
    admit.
    specialize (hv _ hc).

    induction 1; cbn; move=> v hv.
    1:by red in hv; rewrite Forall_forall in hv; eapply hv in H.
    all:try specialize (IHentails_L _ hv).
    all:try specialize (IHentails_L1 _ hv).
    all:try specialize (IHentails_L2 _ hv).
    all:try lia; eauto.
    all:rewrite ?interp_add_prems ?interp_prems_union ?interp_add_prems; try lia.
    rewrite ?interp_add_prems in IHentails_L. lia.
  Qed.


End UnivLoopChecking.

(* Completeness try *)
(*


  Parameter ϕ : nat -> rel.
    Parameter ϕ_exists : forall r, exists n, ϕ n = r.
    Parameter ϕ_inj : forall n n', ϕ n = ϕ n' -> n = n'.

    Definition neg_r p e :=
      p ⊢ℒ add_prems 1 e.1 ≤ e.2 \/ p ⊢ℒ add_prems 1 e.2 ≤ e.1.

    (* Definition consistent (r : rels) :=
      ~ (exists e, r ⊢ℒ e /\ neg_r r e).

    Definition satisfiable (r : rels) :=
      exists v, interp_rels v r.

    Definition satisfiable_consistent {p} :
      satisfiable p -> consistent p.
    Proof.
      move=> [v it] [[l r] [hx [hnl|hnl]]];
      eapply presentation_entails_valid_eq in hx;
      eapply presentation_entails_valid_le in hnl;
      move: (hx _ it); move: (hnl _ it); cbn;
      rewrite !interp_add_prems; lia.
    Qed. *)

    (* Definition consistent' (Γ : rels) :=
      exists r, ~ (Γ ⊢ℒ r). *)

    Definition bottom (s : semilattice) :=
      exists x : s, add 1%Z x ≤ x.

    Notation "⟘" := (bottom _) : sl_scope.

    Definition consistent Γ :=
      ~ exists e, Γ ⊢ℒ e ≡ add_prems 1 e.

    Inductive 𝒮 (r : rels) : rels -> nat -> Prop :=
    | S_0 Γ : List.incl Γ r -> 𝒮 r Γ 0
    | S_incl Γ n : 𝒮 r Γ n ->
      (* ~ consistent (ϕ n :: Γ) ->  *)
      𝒮 r Γ (S n)
    | S_phi Γ n : 𝒮 r Γ n -> consistent (ϕ n :: Γ) -> 𝒮 r (ϕ n :: Γ) (S n).

    Definition 𝒮ω rs (Γ : rels) := exists (n: nat), 𝒮 rs Γ n.

    Definition in𝒮ω rs r := exists (n: nat) Γ, 𝒮 rs Γ n /\ Γ ⊢ℒ r.

    (* /\ Γ ⊢ℒ r *)

    Definition maximally_consistent (Γ : rels) :=
       consistent Γ /\ forall r, (~ consistent (r :: Γ) \/ Γ ⊢ℒ r).

    Definition satisfiable (s : semilattice) (r : rels) :=
      exists v, interp_rels (SL := sl s) v r.

    Lemma consistent_satisfiable Γ :
      satisfiable Z_semilattice Γ -> consistent Γ.
    Proof.
      move=> [v sat] [e].
      move/presentation_entails_valid_rel/(_ Z_semilattice v sat). cbn.
      rewrite interp_add_prems. change (add 1%Z (interp_prems v e)) with (Z.add 1 (interp_prems v e)).
      cbn -[Z.add]. lia.
    Qed.

    Section MaximallyConsistent.

      Lemma 𝒮ω_consistent_maximal Γ Γ' n : consistent Γ -> 𝒮 Γ Γ' n -> consistent Γ'.
       (* /\ (consistent' (ϕ n :: Γ') \/ Γ' ⊢ℒ ϕ n). *)
      Proof.
        move=> con sprf. induction sprf.
        - intros [e pe]. apply con. exists e.
          eapply entails_L_rels_subset; tea.
        - exact IHsprf.
        - intros [e neq].
          destruct H. now exists e.
      Qed.

      Definition 𝒮ω_exists rs (crs : consistent rs) n : exists Γ, 𝒮 rs Γ n.
      Proof.
        induction n.
        - exists rs. by constructor.
        - destruct IHn as [Γ' sn].
          destruct (check_pres_clause_spec Γ' (ϕ n)).
          * exists (ϕ n :: Γ'). apply S_phi => //.
            intros [e he]. apply 𝒮ω_consistent_maximal in sn => //.
            eapply entails_L_cut in H; tea.
            apply sn. now exists e.
          * exists Γ'. apply S_incl => //.
      Qed.

    Definition inSw rs r := exists n Γ, 𝒮 rs Γ n /\ Γ ⊢ℒ r.

    Import Semilattice.

    Lemma axiom_inSw {rs r} : rs ⊢ℒ r -> inSw rs r.
    Proof.
      intros hs. exists 0, rs; split. constructor. red; auto.
      exact: hs.
    Qed.

*)