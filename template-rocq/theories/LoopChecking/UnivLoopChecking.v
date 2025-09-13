(* Distributed under the terms of the MIT license. *)
(* This module provides an instantiation of the deciders for universe checking,
  i.e. for constraints on non-empty level expressions (l, k) where k ∈ 𝐍 *)

From Stdlib Require Import ssreflect ssrfun ssrbool.
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

  Definition to_cstr d := match d with
    | ConstraintType.Eq => LoopCheck.UnivEq
    | ConstraintType.Le => LoopCheck.UnivLe
    end.

  Definition to_constraint (x : UnivConstraint.t) : LoopCheck.constraint :=
    let '(l, d, r) := x in
    (to_atoms l, to_cstr d, to_atoms r).

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

  Lemma clauses_of_le_nempty l r : ~ Clauses.Empty (LoopCheck.clauses_of_le l r).
  Proof.
    intros he. red in he. eapply he.
    rewrite !LoopCheck.clauses_of_le_spec.
    exists (choose_prems l). split; trea.
    apply choose_prems_spec.
  Qed.

  Lemma to_clauses_ne c : ~ Clauses.Empty (LoopCheck.to_clauses c).
  Proof.
    intros he. red in he. destruct c as [[l []] r].
    eapply he. apply LoopCheck.to_clauses_spec.
    right. exists (choose_prems r). split; trea. apply choose_prems_spec.
    eapply he. apply LoopCheck.to_clauses_spec.
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

  Lemma in_clause_levels_of_le lev l r : LevelSet.In lev (clauses_levels (LoopCheck.clauses_of_le l r)) <->
    LevelSet.In lev (levels l) \/ LevelSet.In lev (levels r).
  Proof.
    rewrite clauses_levels_spec.
    setoid_rewrite LoopCheck.clauses_of_le_spec.
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
    destruct c as [[l' d] r] => //=.
    destruct d. rewrite clauses_levels_union LevelSet.union_spec.
    rewrite /constraint_levels //= LevelSet.union_spec.
    rewrite !in_clause_levels_of_le. firstorder.
    rewrite /constraint_levels //= LevelSet.union_spec.
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

  Lemma clauses_sem_subset {v cls cls'} : clauses_sem v cls -> cls' ⊂_clset cls -> clauses_sem v cls'.
  Proof.
    now move=> hall hsub cl /hsub.
  Qed.

  Lemma clauses_sem_clauses_of_le V l r :
    clauses_sem V (LoopCheck.clauses_of_le l r) ->
    (interp_prems V l <= interp_prems V r)%Z.
  Proof.
    rewrite /clauses_sem.
    intros hl. red in hl.
    setoid_rewrite LoopCheck.clauses_of_le_spec in hl.
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
  Proof. Admitted.

  Lemma to_atoms_add le u : to_atoms (Universe.add le u) = add (to_atom le) (to_atoms u).
  Proof. Admitted.

  Lemma interp_prem_to_atom v le : Z.to_nat (interp_expr v (to_atom le)) = val (to_valuation v) le.
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

  Lemma interp_prems_to_atoms v l : Z.to_nat (interp_prems v (to_atoms l)) = Universes.val (to_valuation v) l.
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
      rewrite -interp_prem_to_atom. lia.
  Qed.

  Lemma clauses_sem_val m l r :
    clauses_sem (LoopCheck.valuation m) (LoopCheck.clauses_of_le (to_atoms l) (to_atoms r)) ->
    Universes.val (to_valuation (LoopCheck.valuation m)) l <= Universes.val (to_valuation (LoopCheck.valuation m)) r.
  Proof.
    move/clauses_sem_clauses_of_le.
    have he := interp_prems_to_atoms (LoopCheck.valuation m) l.
    have he' := interp_prems_to_atoms (LoopCheck.valuation m) r. lia.
  Qed.

  Lemma model_satisfies m :
    exists V, satisfies V (constraints m).
  Proof.
    destruct m as [m cstrs repr repr_inv]. cbn.
    have val := LoopCheck.model_valuation m.
    exists (to_valuation (LoopCheck.valuation m)).
    move=> cstr /repr /(clauses_sem_subset val).
    intros cls. destruct cstr as [[l []] r]; cbn.
    constructor. cbn in cls. now apply clauses_sem_val.
    constructor. cbn in cls.
    rewrite clauses_sem_union in cls. destruct cls as [hl hr].
    eapply Nat.le_antisymm; now apply clauses_sem_val.
  Qed.

  Import LoopCheck.Impl.I.Model.Model.Clauses.FLS.

End UnivLoopChecking.
