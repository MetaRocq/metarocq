(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From MetaRocq.Common Require Import Interfaces.
From Equations Require Import Equations.
Set Equations Transparent.

Ltac rw l := rewrite_strat (topdown l).
Ltac rw_in l H := rewrite_strat (topdown l) in H.

Module Clauses (LS : LevelSets).
  Module Export FLS := FromLevelSets LS.

  Notation univ := nonEmptyLevelExprSet.
  Definition clause : Type := univ × LevelExpr.t.

  Module Clause.

  Definition t := clause.

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : RelationClasses.Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | lt_clause1 l e e' : LevelExpr.lt e e' -> lt_ (l, e) (l, e')
  | lt_clause2 l l' b b' : LevelExprSet.lt l.(t_set) l'.(t_set) -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : RelationClasses.StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X; subst. now eapply LevelExpr.lt_strorder in H1.
      eapply LevelExprSet.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2. unfold lt. subst. reflexivity.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match LevelExprSet.compare l1.(t_set) l2.(t_set) with
      | Eq => LevelExpr.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [? ?] [? ?]; cbn; repeat constructor.
    destruct (LevelExprSet.compare_spec n n0); repeat constructor; tas.
    eapply LevelExprSet.eq_leibniz in H. apply NonEmptySetFacts.eq_univ in H.
    subst. cbn in *.
    destruct (LevelExpr.compare_spec t0 t1); repeat constructor; tas. now subst.
  Qed.

  #[program] Global Instance reflect_eq_Z : ReflectEq Z := {
    eqb := Z.eqb
  }.
  Next Obligation.
    destruct (Z.eqb_spec x y); constructor => //.
  Qed.

  Global Instance reflect_t : ReflectEq t := reflect_prod _ _ .

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2} := Classes.eq_dec.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  End Clause.

  Module Clauses := MSetAVL.Make Clause.
  Module ClausesFact := WFactsOn Clause Clauses.
  Module ClausesProp := WPropertiesOn Clause Clauses.
  Module ClausesDecide := WDecide (Clauses).
  Ltac clsets := ClausesDecide.fsetdec.

  Definition clauses := Clauses.t.

  Lemma filter_add {p x s} : Clauses.Equal (Clauses.filter p (Clauses.add x s)) (if p x then Clauses.add x (Clauses.filter p s) else Clauses.filter p s).
  Proof.
    intros i.
    rewrite Clauses.filter_spec.
    destruct (eqb_spec i x); subst;
    destruct (p x) eqn:px; rewrite !Clauses.add_spec !Clauses.filter_spec; intuition auto || congruence.
  Qed.

  Local Instance proper_fold_transpose {A} (f : Clauses.elt -> A -> A) :
    transpose eq f ->
    Proper (Clauses.Equal ==> eq ==> eq) (Clauses.fold f).
  Proof.
    intros hf s s' Hss' x ? <-.
    eapply ClausesProp.fold_equal; tc; tea.
  Qed.
  Existing Class transpose.

  Lemma clauses_fold_filter {A} (f : Clauses.elt -> A -> A) (p : Clauses.elt -> bool) cls acc :
    transpose Logic.eq f ->
    Clauses.fold f (Clauses.filter p cls) acc =
    Clauses.fold (fun elt acc => if p elt then f elt acc else acc) cls acc.
  Proof.
    intros hf.
    symmetry. eapply ClausesProp.fold_rec_bis.
    - intros s s' a eq. intros ->.
      eapply ClausesProp.fold_equal; tc. auto.
      intros x.
      rewrite !Clauses.filter_spec.
      now rewrite eq.
    - now cbn.
    - intros.
      rewrite H1.
      rewrite filter_add.
      destruct (p x) eqn:px => //.
      rewrite ClausesProp.fold_add //.
      rewrite Clauses.filter_spec. intuition auto.
  Qed.

  Definition strict_subset (s s' : LevelSet.t) :=
    LevelSet.Subset s s' /\ ~ LevelSet.Equal s s'.

  Lemma strict_subset_incl (x y z : LevelSet.t) : LevelSet.Subset x y -> strict_subset y z -> strict_subset x z.
  Proof.
    intros hs []. split => //. lsets.
    intros heq. apply H0. lsets.
  Qed.

  Lemma strict_subset_cardinal s s' : strict_subset s s' -> LevelSet.cardinal s < LevelSet.cardinal s'.
  Proof.
    intros [].
    assert (LevelSet.cardinal s <> LevelSet.cardinal s').
    { intros heq. apply H0.
      intros x. split; intros. now apply H.
      destruct (LevelSet.mem x s) eqn:hin.
      eapply LevelSet.mem_spec in hin.
      auto. eapply LevelSetProp.FM.not_mem_iff in hin.
      exfalso.
      eapply LevelSetProp.subset_cardinal_lt in hin; tea.
      lia. }
    enough (LevelSet.cardinal s <= LevelSet.cardinal s') by lia.
    now eapply LevelSetProp.subset_cardinal.
  Qed.

  Definition premise (cl : clause) := fst cl.
  Definition concl (cl : clause) := snd cl.
  Extraction Inline premise concl.

  Definition clause_levels cl :=
    LevelSet.union (levels (premise cl)) (LevelSet.singleton (level (concl cl))).

  Definition clauses_levels (cls : clauses) : LevelSet.t :=
    Clauses.fold (fun cl acc => LevelSet.union (clause_levels cl) acc) cls LevelSet.empty.

  Lemma Clauses_In_elements l s :
    In l (Clauses.elements s) <-> Clauses.In l s.
  Proof.
    rewrite ClausesFact.elements_iff.
    now rewrite InA_In_eq.
  Qed.

  Lemma clauses_levels_spec_aux l cls acc :
    LevelSet.In l (Clauses.fold (fun cl acc => LevelSet.union (clause_levels cl) acc) cls acc) <->
    (exists cl, Clauses.In cl cls /\ LevelSet.In l (clause_levels cl)) \/ LevelSet.In l acc.
  Proof.
    eapply ClausesProp.fold_rec.
    - intros.
      intuition auto. destruct H1 as [k [hin hl]]. clsets.
    - intros x a s' s'' hin nin hadd ih.
      rewrite LevelSet.union_spec.
      split.
      * intros [hin'|].
        left. exists x. split => //.
        apply hadd. now left.
        apply ih in H.
        intuition auto.
        left. destruct H0 as [k Hk]. exists k. intuition auto. apply hadd. now right.
      * intros [[k [ins'' ?]]|inacc].
        eapply hadd in ins''. destruct ins''; subst.
        + now left.
        + right. apply ih. now left; exists k.
        + right. intuition auto.
  Qed.

  Lemma clauses_levels_spec l cls :
    LevelSet.In l (clauses_levels cls) <->
    exists cl, Clauses.In cl cls /\ LevelSet.In l (clause_levels cl).
  Proof.
    unfold clauses_levels.
    rewrite clauses_levels_spec_aux.
    intuition auto. lsets.
  Qed.

  Instance clauses_levels_proper : Proper (Clauses.Equal ==> LevelSet.Equal) clauses_levels.
  Proof.
    intros cl cl' eq x.
    rewrite !clauses_levels_spec.
    now setoid_rewrite eq.
  Qed.

  Lemma clause_levels_spec l cl :
    LevelSet.In l (clause_levels cl) <->
    LevelSet.In l (levels (premise cl)) \/ l = level (concl cl).
  Proof.
    unfold clause_levels.
    now rewrite LevelSet.union_spec LevelSet.singleton_spec.
  Qed.

  Definition clause_conclusion cl := level (concl cl).
End Clauses.
