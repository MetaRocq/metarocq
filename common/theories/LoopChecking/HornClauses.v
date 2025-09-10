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

  Notation premises := nonEmptyLevelExprSet.
  Definition clause : Type := premises × LevelExpr.t.

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
  Infix "⊂_clset" := Clauses.Subset (at level 70).

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
  Definition clauses_conclusions (cls : clauses) : LevelSet.t :=
    Clauses.fold (fun cl acc => LevelSet.add (level (concl cl)) acc) cls LevelSet.empty.

  #[export] Instance Clauses_For_All_proper : Proper (eq ==> Clauses.Equal ==> iff) Clauses.For_all.
  Proof.
    intros x y -> cl cl' eqcl.
    unfold Clauses.For_all. now setoid_rewrite eqcl.
  Qed.

  #[export] Instance Clauses_for_all_proper : Proper (eq ==> Clauses.Equal ==> eq) Clauses.for_all.
  Proof.
    intros x y -> cl cl' eqcl.
    apply iff_is_true_eq_bool.
    rewrite /is_true -!ClausesFact.for_all_iff. now rewrite eqcl.
  Qed.

  Lemma clauses_conclusions_spec a cls :
    LevelSet.In a (clauses_conclusions cls) <->
    exists cl, Clauses.In cl cls /\ level (concl cl) = a.
  Proof.
    unfold clauses_conclusions.
    eapply ClausesProp.fold_rec; clear.
    - move=> s' he /=. rewrite LevelSetFact.empty_iff.
      firstorder auto.
    - move=> cl ls cls' cls'' hin hnin hadd ih.
      rewrite LevelSet.add_spec. firstorder eauto.
      specialize (H0 x). cbn in H0.
      apply hadd in H1. firstorder eauto.
      subst. left. now destruct x.
  Qed.

  Definition premise_restricted_to W cl :=
    LevelSet.subset (levels (premise cl)) W.

  Definition clause_restricted_to W cl :=
    LevelSet.subset (levels (premise cl)) W &&
    LevelSet.mem (level (concl cl)) W.

  Definition restrict_clauses (cls : clauses) (W : LevelSet.t) :=
    Clauses.filter (clause_restricted_to W) cls.
  Infix "⇂" := restrict_clauses (at level 70). (* \downharpoonright *)

  Definition clauses_with_concl (cls : clauses) (concl : LevelSet.t) :=
    Clauses.filter (fun '(prem, concla) => LevelSet.mem (level concla) concl) cls.
  Infix "↓" := clauses_with_concl (at level 70). (* \downarrow *)

  Notation cls_diff cls W := (Clauses.diff (cls ↓ W) (cls ⇂ W)) (only parsing).

  Lemma in_restrict_clauses (cls : clauses) (concls : LevelSet.t) cl :
    Clauses.In cl (restrict_clauses cls concls) <->
    [/\ LevelSet.In (level (concl cl)) concls,
      LevelSet.Subset (levels (premise cl)) concls &
      Clauses.In cl cls].
  Proof.
    unfold restrict_clauses.
    rewrite Clauses.filter_spec.
    destruct cl. cbn.
    rewrite andb_true_iff LevelSet.subset_spec LevelSet.mem_spec.
    firstorder auto.
  Qed.

  Lemma restrict_clauses_subset (cls : clauses) (concls : LevelSet.t) : Clauses.Subset (restrict_clauses cls concls) cls.
  Proof.
    intros x; rewrite in_restrict_clauses; now intros [].
  Qed.

  Lemma in_clauses_with_concl (cls : clauses) (concls : LevelSet.t) cl :
    Clauses.In cl (clauses_with_concl cls concls) <->
    LevelSet.In (level (concl cl)) concls /\ Clauses.In cl cls.
  Proof.
    unfold clauses_with_concl.
    rewrite Clauses.filter_spec.
    destruct cl. rewrite LevelSet.mem_spec. cbn. firstorder eauto.
  Qed.

  Lemma clauses_conclusions_clauses_with_concl cls concl :
    LevelSet.Subset (clauses_conclusions (clauses_with_concl cls concl)) concl.
  Proof.
    intros x [cl []] % clauses_conclusions_spec.
    eapply in_clauses_with_concl in H as [].
    now rewrite H0 in H.
  Qed.

  Lemma clauses_conclusions_restrict_clauses cls W :
    LevelSet.Subset (clauses_conclusions (restrict_clauses cls W)) W.
  Proof.
    intros x [cl []] % clauses_conclusions_spec.
    eapply in_restrict_clauses in H as [].
    now rewrite H0 in H.
  Qed.

  Definition in_clauses_conclusions (cls : clauses) (x : Level.t): Prop :=
    exists cl, Clauses.In cl cls /\ (level cl.2) = x.

  Definition premise_min (l : premises) : Z :=
    let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
    fold_left (B:=LevelExpr.t) (fun min atom => Z.min atom.2 min) tl (hd.2).

  Definition premise_max (l : premises) : Z :=
    let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
    fold_left (B:=LevelExpr.t) (fun min atom => Z.max atom.2 min) tl (hd.2).

  Definition max_clause_premise (cls : clauses) :=
    Clauses.fold (fun cl acc => Z.max (premise_max (premise cl)) acc) cls 0%Z.

  Definition gain (cl : clause) : Z :=
    (concl cl).2 - (premise_min (premise cl)).

  Definition max_gain (cls : clauses) :=
    Clauses.fold (fun cl acc => Nat.max (Z.to_nat (gain cl)) acc) cls 0%nat.


  Lemma clauses_conclusions_diff cls s :
    clauses_conclusions (Clauses.diff cls (clauses_with_concl cls s)) ⊂_lset
    LevelSet.diff (clauses_conclusions cls) s.
  Proof.
    intros a. rewrite LevelSet.diff_spec !clauses_conclusions_spec.
    firstorder eauto.
    exists x; split => //.
    now rewrite Clauses.diff_spec in H.
    intros ha.
    rewrite Clauses.diff_spec in H; destruct H as [].
    apply H1.
    rewrite in_clauses_with_concl. split => //.
    now rewrite H0.
  Qed.

  Lemma clauses_conclusions_diff_left cls W cls' :
    clauses_conclusions (Clauses.diff (cls ↓ W) cls') ⊂_lset W.
  Proof.
    intros l.
    rewrite clauses_conclusions_spec.
    move=> [] cl. rewrite Clauses.diff_spec => [] [] [].
    move/in_clauses_with_concl => [] hin ? ? eq.
    now rewrite eq in hin.
  Qed.

  Lemma clauses_conclusions_diff_restrict cls W cls' :
    clauses_conclusions (Clauses.diff (cls ⇂ W) cls') ⊂_lset W.
  Proof.
    intros l.
    rewrite clauses_conclusions_spec.
    move=> [] cl. rewrite Clauses.diff_spec => [] [] [].
    move/in_restrict_clauses => [] hin ? ? ? eq.
    now rewrite eq in hin.
  Qed.

  Lemma clauses_empty_eq {s} : Clauses.Empty s -> Clauses.Equal s Clauses.empty.
  Proof. clsets. Qed.

  Lemma clauses_for_all_neg {p s}:
    ~~ Clauses.for_all p s <-> ~ Clauses.For_all p s.
  Proof.
    intuition auto.
    rewrite ClausesFact.for_all_iff in H0. red in H. now rewrite H0 in H.
    revert H. apply contra_notN.
    rewrite ClausesFact.for_all_iff //.
  Qed.

  Lemma clauses_for_all_exists {p s}:
    ~~ Clauses.for_all p s <-> Clauses.exists_ (fun x => ~~ p x) s.
  Proof.
    rewrite ClausesFact.for_all_b ClausesFact.exists_b.
    induction (Clauses.elements s).
    - cbn; auto. reflexivity.
    - cbn. rewrite negb_and. intuition auto.
      move/orP: H1 => [->|] //. move/H. intros ->. now rewrite orb_true_r.
      move/orP: H1 => [->|] //. move/H0. intros ->. now rewrite orb_true_r.
  Qed.

  Lemma max_gain_in cl cls :
    Clauses.In cl cls ->
    (Z.to_nat (gain cl) <= max_gain cls)%nat.
  Proof.
    intros hin.
    unfold max_gain. revert cl hin.
    eapply ClausesProp.fold_rec.
    - intros s' ise hin. firstorder eauto.
    - intros x a s' s'' xs nxs' hadd IH cl' hin'.
      eapply hadd in hin' as [].
      * subst x. lia.
      * specialize (IH _ H). lia.
  Qed.

  Definition max_gain_subset (cls cls' : Clauses.t) :
    cls ⊂_clset cls' ->
    (max_gain cls <= max_gain cls')%nat.
  Proof.
    unfold max_gain at 1.
    revert cls'.
    eapply ClausesProp.fold_rec.
    - intros s' ise sub. lia.
    - intros x a s' s'' xs nxs' hadd IH cls'' hs.
      specialize (IH cls''). forward IH. transitivity s'' => //.
      intros ??. now apply hadd.
      assert (incls'' : Clauses.In x cls'').
      { now apply hs, hadd. }
      apply max_gain_in in incls''. lia.
  Qed.

  Lemma max_clause_premise_spec cl cls :
    Clauses.In cl cls ->
    (premise_max (premise cl) <= max_clause_premise cls)%Z.
  Proof.
    intros hin.
    unfold max_clause_premise. revert cl hin.
    eapply ClausesProp.fold_rec.
    - intros s' ise hin. firstorder eauto.
    - intros x a s' s'' xs nxs' hadd IH cl' hin'.
      eapply hadd in hin' as [].
      * subst x. lia.
      * specialize (IH _ H). lia.
  Qed.

  Lemma non_W_atoms_ne W cl cls :
    Clauses.In cl (cls_diff cls W) ->
    LevelExprSet.is_empty (non_W_atoms W (premise cl)) = false.
  Proof.
    intros x.
    apply Clauses.diff_spec in x as [clw clr].
    eapply in_clauses_with_concl in clw as [clw incls].
    apply/negbTE.
    apply/(contra_notN _ clr).
    intros he. rewrite in_restrict_clauses. split => //.
    epose proof (@levels_exprs_non_W_atoms W (premise cl)).
    eapply LevelExprSetFact.is_empty_2 in he.
    intros x hin. eapply levelexprset_empty_levels in he. rewrite H in he.
    specialize (he x). rewrite LevelSet.diff_spec in he. intuition auto.
    rewrite -LevelSet.mem_spec in H1 |- *. destruct LevelSet.mem; intuition auto.
  Qed.

  Lemma clauses_levels_restrict_clauses cls W :
    clauses_levels (cls ⇂ W) ⊂_lset W.
  Proof.
    intros x [cl []] % clauses_levels_spec.
    eapply in_restrict_clauses in H as [hconc hprem incl].
    eapply clause_levels_spec in H0 as []. apply hprem, H. now subst x.
  Qed.

  Lemma clauses_conclusions_levels cls :
    clauses_conclusions cls ⊂_lset clauses_levels cls.
  Proof.
    intros x.
    rewrite clauses_conclusions_spec clauses_levels_spec.
    setoid_rewrite clause_levels_spec.
    firstorder auto.
  Qed.

  #[export] Instance clauses_conclusions_proper : Proper (Clauses.Equal ==> LevelSet.Equal) clauses_conclusions.
  Proof.
    intros cls cls' eq x.
    rewrite !clauses_conclusions_spec. now setoid_rewrite eq.
  Qed.

  Lemma clauses_conclusions_add cl cls :
    clauses_conclusions (Clauses.add cl cls) =_lset
    (LevelSet.singleton (level (concl cl)) ∪
      clauses_conclusions cls).
  Proof.
    intros x.
    rewrite LevelSet.union_spec !clauses_conclusions_spec.
    setoid_rewrite Clauses.add_spec; setoid_rewrite LevelSet.singleton_spec.
    firstorder eauto. subst. now left.
  Qed.

  Lemma clauses_conclusions_subset {cls cls'} :
    Clauses.Subset cls cls' ->
    clauses_conclusions cls ⊂_lset clauses_conclusions cls'.
  Proof.
    intros hsub x. rewrite !clauses_conclusions_spec.
    intuition eauto. destruct H as [cl []]; exists cl; split; try clsets; auto.
  Qed.


End Clauses.
