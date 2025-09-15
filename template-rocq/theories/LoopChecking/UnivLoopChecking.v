(* Distributed under the terms of the MIT license. *)
(* This module provides an instantiation of the deciders for universe checking,
  i.e. for constraints on non-empty level expressions (l, k) where k ∈ 𝐍 *)

From Stdlib Require Import ssreflect ssrfun ssrbool.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.
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

  Definition choose_prems (u : premises) : LevelExpr.t := (to_nonempty_list u).1.
  Lemma choose_prems_spec u : LevelExprSet.In (choose_prems u) u.
  Proof.
    rewrite /choose_prems.
    have hs := to_nonempty_list_spec u.
    destruct to_nonempty_list. cbn.
    rewrite -LevelExprSet.elements_spec1 InA_In_eq -hs.
    now constructor.
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

  Definition to_valuation (v : LevelMap.t nat) : valuation :=
    {| valuation_mono := fun s => Pos.of_nat (option_get 0 (LevelMap.find (Level.level s) v));
       valuation_poly := fun i => option_get 0 (LevelMap.find (Level.lvar i) v)
    |}.

  Definition of_valuation V (v : valuation) : LevelMap.t nat :=
    let add_val l := LevelMap.add l (val v l) in
    LevelSet.fold add_val V (LevelMap.empty _).

  Lemma clauses_sem_subset {v cls cls'} : clauses_sem v cls -> cls' ⊂_clset cls -> clauses_sem v cls'.
  Proof.
    now move=> hall hsub cl /hsub.
  Qed.

  Lemma clauses_sem_clauses_of_le V l r :
    clauses_sem V (clauses_of_le l r) ->
    (interp_prems V l <= interp_prems V r)%Z.
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
      cbn. lia.
  Qed.

  Lemma to_atoms_singleton l k  : to_atoms (Universe.singleton (l, k)) = singleton (l, Z.of_nat k).
  Proof.
    apply NES.equal_exprsets.
    rewrite /to_atoms //=.
  Qed.

  Lemma to_atoms_add le u : to_atoms (Universe.add le u) = add (to_atom le) (to_atoms u).
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

  Lemma interp_prem_to_atom v le : interp_expr v (to_atom le) =  Z.of_nat (val (to_valuation v) le).
  Proof.
    destruct le => //=. cbn.
    destruct t0.
    - (* lzero is forced to have value 0, has it should stay maximal *) todo "handle lzero".
    - todo "handle monos".
    - cbn. unfold interp_level. destruct LevelMap.find eqn:he => //=. lia.
      lia.
  Qed.

  Lemma clauses_sem_union v cls cls' : clauses_sem v (Clauses.Clauses.union cls cls') <->
    clauses_sem v cls /\ clauses_sem v cls'.
  Proof.
    unfold clauses_sem. split.
    intros hf. split; eapply clauses_sem_subset; tea; clsets.
    intros []. intros cl. rewrite Clauses.Clauses.union_spec.
    specialize (H cl). specialize (H0 cl). intros []; auto.
  Qed.

  Lemma interp_prems_to_atoms v l : interp_prems v (to_atoms l) = Z.of_nat (Universes.val (to_valuation v) l).
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
      rewrite interp_prem_to_atom. lia.
  Qed.

  Lemma clauses_sem_val m l r :
    clauses_sem (LoopCheck.valuation m) (clauses_of_le (to_atoms l) (to_atoms r)) ->
    Universes.val (to_valuation (LoopCheck.valuation m)) l <= Universes.val (to_valuation (LoopCheck.valuation m)) r.
  Proof.
    move/clauses_sem_clauses_of_le.
    have he := interp_prems_to_atoms (LoopCheck.valuation m) l.
    have he' := interp_prems_to_atoms (LoopCheck.valuation m) r. lia.
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

  Lemma to_of_valuation V v :
    forall l, LevelSet.In l.1 V -> val (to_valuation (of_valuation V v)) l = val v l.
  Proof.
  Admitted.

  Lemma to_of_valuation_univ V v :
    forall u : Universe.t, LevelSet.Subset (Universe.levels u) V -> val (to_valuation (of_valuation V v)) u = val v u.
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
    interp_level (of_valuation V v) l = val v l.
  Proof.
    move=> hin.
    rewrite /interp_level.
    elim: find_spec => [k /of_valuation_spec []|] => //.
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
    clause_sem (of_valuation V v) cl.
  Proof.
    move=> hlev leq [prems concl].
    move=> [] [l'' k'] [] /to_levelexprzset_spec_2 [] inl' pos ->.
    cbn. rewrite interp_prems_to_atoms //=.
    rewrite to_of_valuation_univ.
    { intros ? hin; apply hlev. cbn. lsets. }
    transitivity (Z.of_nat (val v l)). lia.
    rewrite interp_level_of_valuation.
    { apply hlev; cbn.
      eapply LevelSet.union_spec; left. eapply Universe.levels_spec.
      now eexists. }
    have vle := val_In_le l v _ inl'. cbn in vle.
    by u; lia.
  Qed.

  Lemma satisfies_clauses_sem v m V :
    LoopCheck.levels (model m) ⊂_lset V ->
    satisfies v (constraints m) ->
    clauses_sem (of_valuation V v) (LoopCheck.clauses (model m)).
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
    clauses_sem (of_valuation V v) (LoopCheck.to_clauses (to_constraint c)) ->
    satisfies0 v c.
  Proof.
    intros hin hsem. destruct c as [[l []] r]; cbn in *.
    - constructor.
      move/clauses_sem_clauses_of_le: hsem.
      rewrite !interp_prems_to_atoms.
      rewrite !to_of_valuation_univ. lsets. lsets. lia.
    - constructor.
      rewrite clauses_sem_union in hsem. destruct hsem as [hsem hsem'].
      move/clauses_sem_clauses_of_le: hsem.
      move/clauses_sem_clauses_of_le: hsem'.
      rewrite !interp_prems_to_atoms.
      rewrite !to_of_valuation_univ. lsets. lsets. lia.
  Qed.

  Instance in_pred_closure_proper : Proper (Clauses.Equal ==> Logic.eq ==> impl) in_pred_closure.
  Proof.
    intros cls cls' eq ? cl -> h.
    induction h.
    - constructor. now rewrite -eq.
    - constructor.
  Qed.


  Instance proper_entails : Proper (Clauses.Equal ==> Logic.eq ==> impl) entails.
  Proof.
    intros cls cls' eq ? cl -> h.
    induction h.
    - constructor; auto.
    - econstructor 2; eauto.
      now rewrite -eq.
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

  Section Nat_Semilattice.
    Import Semilattice.
    Equations? nat_semilattice : semilattice :=
    nat_semilattice :=
      {| carrier := nat;
         eq := Logic.eq;
         succ x := S x;
         join x y := Nat.max x y |}.
    Proof.
      all:lia.
    Qed.
  End Nat_Semilattice.

  Section Z_Semilattice.
    Import Semilattice.
    Equations? Z_semilattice : semilattice :=
    Z_semilattice :=
      {| carrier := Z;
         eq := Logic.eq;
         succ x := Z.succ x;
         join x y := Z.max x y |}.
    Proof.
      all:lia.
    Qed.
  End Z_Semilattice.

  Lemma interp_prems_union {v x y} : interp_prems v (x ∨ y) = Z.max (interp_prems v x) (interp_prems v y).
  Proof.
    move: x; apply NES.elim.
    - intros []. rewrite univ_union_comm univ_union_add_singleton.
      now rewrite interp_prems_add interp_prems_singleton.
    - intros le' x ih hnin.
      rewrite univ_union_add_distr !interp_prems_add ih. lia.
  Qed.

  Lemma val_respects cls v : respects (leset_sl cls) Z_semilattice (fun u => interp_prems v u).
  Proof.
    split; cbn.
    - intros x. rewrite interp_add_prems. lia.
    - intros x y. rewrite interp_prems_union. lia.
  Qed.

  Definition valid_entailments cls cls' :=
    forall V, clauses_sem V cls -> clauses_sem V cls'.

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

  Import Semilattice.

  Record presentation :=
    { V : LevelSet.t;
      C : list (NES.t × NES.t); }.

  Inductive entails_L (p : presentation) : NES.t -> NES.t -> Prop :=
    | entails_c {l r} : List.In (l, r) p.(C) -> entails_L p l r
    | entails_refl {x} : entails_L p x x
    | entails_sym {x y} : entails_L p x y -> entails_L p y x
    | entails_trans {x y z} : entails_L p x y -> entails_L p y z -> entails_L p x z
    | entails_succ_congr {x y n} : entails_L p x y -> entails_L p (add_prems n x) (add_prems n y)
    | entails_join_congr {x y r} : entails_L p x y -> entails_L p (x ∨ r) (y ∨ r)
    | entails_assoc {x y z} : entails_L p ((x ∨ y) ∨ z) (x ∨ (y ∨ z))
    | entails_idem {x} : entails_L p (x ∨ x) x
    | entails_comm {x y} : entails_L p (x ∨ y) (y ∨ x)
    | entails_sub {x} : entails_L p (x ∨ succ_prems x) (succ_prems x)
    | entails_succ_inj {x y n} : entails_L p (add_prems n x) (add_prems n y) ->
      entails_L p x y
    | entails_succ_join {x y} : entails_L p (succ_prems (x ∨ y)) (succ_prems x ∨ succ_prems y).

  Definition entails_L_curry p eq := entails_L p eq.1 eq.2.

  Lemma entails_join_congr_all {p} {x x' y y'} : entails_L p x x' -> entails_L p y y' -> entails_L p (x ∨ y) (x' ∨ y').
  Proof.
    intros he he'.
    eapply entails_trans with (x' ∨ y).
    now apply entails_join_congr.
    rewrite (@univ_union_comm x' y) (@univ_union_comm x' y').
    now apply entails_join_congr.
  Qed.

  Lemma entails_join_congr_all_inv {p} {x x' y z} : entails_L p (x ∨ y) z -> entails_L p x x' -> entails_L p (x' ∨ y) z.
  Proof.
    intros he he'.
    eapply entails_trans with (x ∨ y) => //.
    apply entails_join_congr => //. now eapply entails_sym.
  Qed.

  Lemma entails_join_congr_all_inv_r {p} {x y y' z} : entails_L p (x ∨ y) z -> entails_L p y y' -> entails_L p (x ∨ y') z.
  Proof.
    intros he he'.
    eapply entails_trans with (x ∨ y) => //.
    rewrite !(@univ_union_comm x).
    apply entails_join_congr => //. now eapply entails_sym.
  Qed.

  Section pres_Semilattice.
    Import Semilattice.
    Context (p : presentation).

    Definition relations (c : list (NES.t × NES.t)) : Prop :=
      List.Forall (fun '(l, r) => l = r) c.

    Definition univ_le (u u' : premises) :=
      forall l k, LevelExprSet.In (l, k) u -> exists k', LevelExprSet.In (l, k') u /\ (k <= k')%Z.

    Lemma univ_le_refl u u' : u = u' -> univ_le u u'.
    Proof.
      intros <- l k hin; exists k; split => //; lia.
    Qed.

    Definition univ_eq u u' :=
      univ_le u u' /\ univ_le u' u.

    Lemma univ_eq_refl u u' : u = u' -> univ_eq u u'.
    Proof.
      split; apply univ_le_refl; tea. now symmetry.
    Qed.

    Equations? pres_semilattice : semilattice :=
    pres_semilattice :=
      {| carrier := NES.t;
         eq x y := relations p.(C) -> univ_eq x y;
         succ x := add_prems 1 x;
         join x y := univ_union x y |}.
    Proof.
      all:intros.
      - apply univ_eq_refl. now rewrite univ_union_assoc.
      - apply univ_eq_refl. now rewrite univ_union_comm.
      - split. intros l k; rewrite !LevelExprSet.union_spec.
        intros []; exists k; split => //; try lia;
          now rewrite univ_union_spec.
        intros l k hin. exists k. split => //. lia.
      - split. intros l k; rewrite !LevelExprSet.union_spec.
        intros []; exists k; split => //; try lia;
          now rewrite univ_union_spec.
        intros l k hin. exists k. split => //. lia.
      - split. intros l k hin. exists k. split => //. reflexivity.
        intros l k hin. exists k. split => //; reflexivity.
      - apply univ_eq_refl. now rewrite add_prems_univ_union.
    Qed.
  End pres_Semilattice.

  Definition entails_L_le p l r := (entails_L p (l ∨ r) r).
  Notation " p ⊢ℒ t ≼ u " := (entails_L_le p t u) (t, u at next level, at level 62, no associativity).
  Notation " p ⊢ℒ t ≈ u " := (entails_L p t u) (t, u at next level, at level 62, no associativity).

  Hint Constructors entails_L : entails_L.

  Lemma entails_L_le_refl p x :
    p ⊢ℒ x ≼ x.
  Proof.
    eapply entails_idem.
  Qed.

  Lemma entails_L_le_trans p x y z :
    p ⊢ℒ x ≼ y -> p ⊢ℒ y ≼ z -> p ⊢ℒ x ≼ z.
  Proof.
    intros le le'.
    eapply entails_trans. 2:exact le'.
    red in le, le'.
    eapply entails_trans with (x ∨ y ∨ z).
    rewrite univ_union_assoc. eapply entails_sym.
    eapply entails_join_congr_all => //. apply entails_refl.
    rewrite univ_union_assoc.
    eapply entails_trans with (x ∨ ((y ∨ y) ∨ z)).
    eapply entails_join_congr_all; auto with entails_L.
    rewrite univ_union_assoc -univ_union_assoc.
    now eapply entails_join_congr_all.
  Qed.

  Lemma subset_univ_union {u u' : premises} :
    u ⊂_leset u' -> u ∨ u' = u'.
  Proof.
    intros hincl; apply equal_exprsets => l.
    rewrite univ_union_spec. firstorder.
  Qed.

  Lemma incl_entails_L {cls} {u u' : premises} :
    u ⊂_leset u' -> cls ⊢ℒ u ≼ u'.
  Proof.
    move=> hincl; red.
    rewrite subset_univ_union //; auto with entails_L.
  Qed.

  Lemma entails_L_subset {cls} {prems prems' prems'' : premises} :
    cls ⊢ℒ prems ≼ prems' ->
    prems' ⊂_leset prems'' ->
    cls ⊢ℒ prems ≼ prems''.
  Proof.
    move=> heq /(@incl_entails_L cls).
    now eapply entails_L_le_trans.
  Qed.

  (* Section interp.
    Context (p : presentation).
    Let s := pres_semilattice p.
    Definition interp_atom le :=
      let '(l, k) := le in
      (singleton (l, 0)) (Z.to_nat k).

    Definition interp_univ l :=
      let '(e, u) := NES.to_nonempty_list l in
      List.fold_left (fun acc a => s.(join) (interp_atom a) acc) u (interp_atom e).

    Definition interp_cstr c :=
      let '(l, d, r) := c in
      match d with
      | ConstraintType.Le => le s (interp_univ l) (interp_univ r)
      | ConstraintType.Eq => s.(eq) (interp_univ l) (interp_univ r)
      end.

    Definition interp_cstrs c :=
      ZUnivConstraintSet.For_all (fun c => interp_cstr c) c.
  End interp. *)

  Definition relation_of_constraint c :=
    let '(l, d, r) := c in
    match d with
    | ConstraintType.Le => (univ_union l r, r)
    | ConstraintType.Eq => (l, r)
    end.

  Definition Zuniv_constraint_levels (c : ZUnivConstraint.t) :=
    let '(l, d, r) := c in
    LevelSet.union (NES.levels l) (NES.levels r).

  Definition relations_of_constraints c :=
    ZUnivConstraintSet.fold (fun c acc => relation_of_constraint c :: acc) c [].

  Lemma relations_of_constraints_spec {l r cstrs} : List.In (l, r) (relations_of_constraints cstrs) <->
    exists cl, ZUnivConstraintSet.In cl cstrs /\ (l, r) = relation_of_constraint cl.
  Proof. Admitted.

  Definition levels_of_z_constraints c :=
    ZUnivConstraintSet.fold (fun c acc => LevelSet.union (Zuniv_constraint_levels c) acc) c LevelSet.empty.

  Definition presentation_of cstrs :=
    {| V := levels_of_z_constraints cstrs;
       C := relations_of_constraints cstrs |}.

  Definition entails_L_clause p cl :=
    entails_L_le p (singleton (concl cl)) (premise cl).

  Definition relations_of_clauses c :=
    Clauses.fold (fun '(prems, concl) acc => (singleton concl ∨ prems, prems) :: acc) c [].

  Lemma relations_of_clauses_spec {cls} :
    forall eq, In eq (relations_of_clauses cls) ->
      exists prems concl, Clauses.In (prems, concl) cls /\
        eq = (NES.singleton concl ∨ prems, prems).
  Proof.
    rewrite /relations_of_clauses.
    eapply ClausesProp.fold_rec.
    - move=> s'he eq => //=.
    - move=> x a s' s'' hin hnin hadd ih eq.
      destruct x as [prems concl]. cbn.
      intros [<-|ina].
      * do 2 eexists. split => //. apply hadd. now left.
      * move: (ih _ ina) => [? [? []]]. do 2 eexists; split => //.
        apply hadd. now right. assumption.
  Qed.

  Lemma relations_of_clauses_spec_inv {cls} :
    forall cl, Clauses.In cl cls ->
    In (NES.singleton (concl cl) ∨ premise cl, premise cl) (relations_of_clauses cls).
  Proof.
    rewrite /relations_of_clauses.
    eapply ClausesProp.fold_rec.
    - move=> s'he eq => //=.
    - move=> x a s' s'' hin hnin hadd ih eq.
      destruct x as [prems concl]. cbn.
      rewrite hadd.
      intros [<-|ina].
      * cbn. now left.
      * move: (ih _ ina) => insing. now right.
  Qed.

  Definition presentation_of_clauses cls :=
    {| V := Clauses.clauses_levels cls;
       C := relations_of_clauses cls |}.

  Lemma in_pred_closure_entails_clause {cls cl} :
    in_pred_closure cls cl ->
    entails cls cl.
  Proof.
    destruct cl as [prems concl]; intros inp.
    eapply clause_cut; trea.
    constructor. now apply NES.add_spec.
  Qed.

  Lemma in_clause_of_le {le} {l r : premises} :
    LevelExprSet.In le l <->
    Clauses.Clauses.In (r, le) (l ⋞ r).
  Proof.
    rewrite clauses_of_le_spec.
    split.
    - exists le. split => //.
    - intros [lk [hin [=]]]. now subst le.
  Qed.

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


  Lemma add_idem {l x} : NES.add l (NES.add l x) = NES.add l x.
  Proof.
    apply equal_exprsets => l'.
    rewrite !NES.add_spec. firstorder.
  Qed.

  Lemma entails_L_idem_gen {le} {prems : premises} {p} :
    LevelExprSet.In le prems ->
    entails_L p ((singleton le) ∨ prems) prems.
  Proof.
    move: prems; apply: NES.elim.
    - move=> le' /LevelExprSet.singleton_spec <-.
      apply entails_idem.
    - move=> le' x hin hnin /LevelExprSet.add_spec [].
      * intros eq; subst le'.
        rewrite univ_union_comm univ_union_add_singleton.
        rewrite add_idem. apply entails_refl.
      * move/hin => heq.
        rewrite -!univ_union_add_singleton -univ_union_assoc.
        now apply entails_join_congr.
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


  Lemma in_pred_closure_entails_L {cls} cl :
    in_pred_closure cls cl ->
    entails_L_clause (presentation_of_clauses cls) cl.
  Proof.
    induction 1.
    - rewrite /entails_L_clause /entails_L_le.
      destruct cl as [prems concl]; cbn.
      rewrite -add_prems_singleton -add_prems_univ_union.
      apply entails_succ_congr.
      apply entails_c. now eapply presentation_of_clauses_spec.
    - change (x, (k + 1)%Z) with (add_expr 1 (x, k)).
      rewrite -add_prems_singleton. red; cbn.
      eapply entails_sub.
  Qed.

  Lemma entails_L_le_eq {cls l r} : cls ⊢ℒ l ≼ r -> cls ⊢ℒ l ∨ r ≈ r.
  Proof. trivial. Qed.

  Lemma entails_L_eq_le_1 {cls} {l r} : cls ⊢ℒ l ≈ r -> cls ⊢ℒ l ≼ r.
  Proof.
    intros eq; red.
    eapply (entails_join_congr_all_inv (x := r)).
    eapply entails_idem. now eapply entails_sym.
  Qed.

  Lemma entails_L_eq_le_2 {cls} {l r} : cls ⊢ℒ l ≈ r -> cls ⊢ℒ r ≼ l.
  Proof.
    intros eq; red.
    eapply entails_sym in eq. now eapply entails_L_eq_le_1 in eq.
  Qed.

  Lemma entails_L_eq_antisym {cls} {l r} : cls ⊢ℒ r ≼ l -> cls ⊢ℒ l ≼ r -> cls ⊢ℒ l ≈ r.
  Proof.
    unfold entails_L_le. intros le le'.
    eapply entails_trans with (l ∨ r) => //.
    apply entails_sym. now rewrite univ_union_comm.
  Qed.

  Lemma entails_L_le_join_l {p x x' r} :
    p ⊢ℒ x ≼ x' ->
    p ⊢ℒ x ∨ r ≼ x' ∨ r.
  Proof.
    intros le.
    red in le |- *.
    rewrite univ_union_assoc (@univ_union_comm r) univ_union_assoc -univ_union_assoc.
    eapply entails_join_congr_all => //.
    apply entails_idem.
  Qed.

  Lemma entails_L_le_congr {p x y x' y'} :
    p ⊢ℒ x ≼ x' ->
    p ⊢ℒ y ≼ y' ->
    p ⊢ℒ x ∨ y ≼ x' ∨ y'.
  Proof.
    move/(entails_L_le_join_l (r:=y)) => le le'.
    eapply entails_L_le_trans; tea.
    rewrite !(@univ_union_comm x').
    now eapply entails_L_le_join_l.
  Qed.

  Lemma entails_L_le_idem {p x} :
    p ⊢ℒ x ∨ x ≼ x.
  Proof.
    eapply entails_L_eq_le_1, entails_idem.
  Qed.

  Lemma entails_L_le_join {p x y z} :
    p ⊢ℒ x ≼ z ->
    p ⊢ℒ y ≼ z ->
    p ⊢ℒ x ∨ y ≼ z.
  Proof.
    move=> le le'.
    have := entails_L_le_congr le le' => comb.
    eapply entails_L_le_trans; tea.
    eapply entails_L_le_idem.
  Qed.

  Lemma entails_clause_pres {cls} cl :
    entails cls cl ->
    entails_L_clause (presentation_of_clauses cls) cl.
  Proof.
    intros h; induction h.
    - red.
      now apply entails_L_idem_gen.
    - move: IHh; rewrite -!univ_union_add_singleton.
      eapply in_pred_closure_entails_L in H.
      rewrite /entails_L_clause in H |- *; cbn in *.
      have hsub:= entails_L_subset H H0. red in hsub.
      move=> h'.
      eapply entails_L_le_trans. tea.
      move/entails_L_eq_le_1: hsub. now rewrite univ_union_comm.
  Qed.

  Definition entails_L_clauses cls cls' :=
    Clauses.For_all (entails_L_clause (presentation_of_clauses cls)) cls'.

  Lemma entails_clauses_pres {cls} cls' :
    cls ⊢ℋ cls' ->
    entails_L_clauses cls cls'.
  Proof.
    move=> h cl /h. apply entails_clause_pres.
  Qed.

  Lemma entails_L_clauses_eq {cls s t} :
    entails_L_clauses cls (s ≡ t) <->
    entails_L_clauses cls (s ⋞ t) /\ entails_L_clauses cls (t ⋞ s).
  Proof.
    rewrite /entails_L_clauses /clauses_of_eq.
    split.
    - intros ha; split => l; move:(ha l); rewrite Clauses.union_spec;
      intros he hle; apply he; now constructor.
    - intros [le le'] l.
      rewrite Clauses.union_spec; intros []; [apply le|apply le']; assumption.
  Qed.

  Lemma entails_L_split p (s t : premises) :
    (forall le, LevelExprSet.In le s -> p ⊢ℒ singleton le ≼ t) ->
    p ⊢ℒ s ≼ t.
  Proof.
    move: s; apply: NES.elim.
    - intros [l k] ih. eapply ih.
      now apply LevelExprSet.singleton_spec.
    - move=> le x h hnin ih.
      forward h.
      { move=> le' hin. move: (ih le') => /fwd //.
        eapply LevelExprSet.add_spec. now right. }
      specialize (ih le); forward ih.
      eapply LevelExprSet.add_spec; now left.
      rewrite -univ_union_add_singleton.
      now eapply entails_L_le_join.
  Qed.

  Lemma entails_L_le_left {p x y} :
    p ⊢ℒ x ≼ x ∨ y.
  Proof.
    red. rewrite -univ_union_assoc.
    eapply entails_join_congr_all. apply entails_idem. apply entails_refl.
  Qed.

  Lemma entails_L_le_right {p x y} :
    p ⊢ℒ y ≼ x ∨ y.
  Proof.
    rewrite univ_union_comm; apply entails_L_le_left.
  Qed.

  Lemma entails_L_in p l (t : premises) :
    LevelExprSet.In l t ->
    p ⊢ℒ NES.singleton l ≼ t.
  Proof.
    move: t; apply: NES.elim.
    - move=>[l' k] /LevelExprSet.singleton_spec => ->.
      apply entails_L_le_refl.
    - move=> le x h hnin /NES.add_spec [].
      * intros ->. rewrite -univ_union_add_singleton.
        apply entails_L_le_right.
      * move/h => hle.
        rewrite -univ_union_add_singleton.
        eapply entails_L_le_trans with x => //.
        apply entails_L_le_left.
  Qed.

  Lemma entails_L_clauses_all {cstrs s t} :
    (presentation_of_clauses (of_z_constraints cstrs)) ⊢ℒ s ≈ t ->
    (presentation_of cstrs) ⊢ℒ s ≈ t.
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
    entails_L_clauses (of_z_constraints cstrs) (s ⋞ t) ->
    presentation_of cstrs ⊢ℒ s ≼ t.
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
    entails_L_clauses (of_z_constraints cstrs) (s ≡ t) ->
    presentation_of cstrs ⊢ℒ s ≈ t.
  Proof.
    intros hf. do 2 red in hf.
    eapply entails_L_eq_antisym.
    all: apply entails_L_clauses_le.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
  Qed.

  Lemma completeness cstrs s t :
    presentation_of cstrs ⊢ℒ s ≈ t <->
    entails_z_cstr cstrs (s, ConstraintType.Eq, t).
  Proof.
    unfold entails_z_cstr.
    split.
    - induction 1; cbn.
      move: H => //=; rewrite relations_of_constraints_spec => -[] [[l' []] r'] [hin heq]; noconf heq.
      * eapply Theory.le_spec.
        now apply entails_clauses_le_cstr.
      * now eapply entails_clauses_eq_cstr.
      * eapply Theory.eq_refl.
      * now eapply Theory.eq_sym.
      * now eapply Theory.eq_trans.
      * now eapply Theory.succ_congr.
      * now eapply Theory.join_congr_left.
      * eapply Theory.join_assoc.
      * eapply Theory.join_idem.
      * eapply Theory.join_comm.
      * eapply Theory.join_succ.
      * now eapply Theory.succ_inj.
      * eapply Theory.succ_join.
    - move/entails_clauses_pres; apply entails_L_clauses_of_eq.
  Qed.

  Import LoopCheck.Impl.I.Model.Model.Clauses.FLS.

End UnivLoopChecking.
