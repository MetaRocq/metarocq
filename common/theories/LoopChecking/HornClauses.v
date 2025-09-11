(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From MetaRocq.Common Require Import Common Interfaces.
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
  Module ClausesOrd := OrdProperties Clauses.

  Ltac clsets := ClausesDecide.fsetdec.
  Infix "⊂_clset" := Clauses.Subset (at level 70).
  Infix "=_clset" := Clauses.Equal (at level 70).

  Definition clauses := Clauses.t.

  Lemma filter_add {p x s} : Clauses.filter p (Clauses.add x s) =_clset if p x then Clauses.add x (Clauses.filter p s) else Clauses.filter p s.
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

  Lemma clauses_ne_exist cls : ~ Clauses.Empty cls -> exists cl, Clauses.In cl cls.
  Proof.
    intros ne.
    destruct (Clauses.choose cls) eqn:hc.
    - exists e. now apply Clauses.choose_spec1 in hc.
    - now apply Clauses.choose_spec2 in hc.
  Qed.

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

  Lemma clauses_levels_conclusions cls V : clauses_levels cls ⊂_lset V ->
    clauses_conclusions cls ⊂_lset V.
  Proof.
    intros hin x; rewrite clauses_conclusions_spec; move => [cl [hin' eq]]; apply hin.
    rewrite clauses_levels_spec. exists cl. split => //. subst x.
    rewrite clause_levels_spec. now right.
  Qed.

  Definition clauses_premises_levels (cls : clauses) : LevelSet.t :=
    Clauses.fold (fun cl acc => LevelSet.union (levels (premise cl)) acc) cls LevelSet.empty.

  Lemma clauses_premises_levels_spec_aux l cls acc :
    LevelSet.In l (Clauses.fold (fun cl acc => LevelSet.union (levels (premise cl)) acc) cls acc) <->
    (exists cl, Clauses.In cl cls /\ LevelSet.In l (levels (premise cl))) \/ LevelSet.In l acc.
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

  Lemma clauses_premises_levels_spec l cls :
    LevelSet.In l (clauses_premises_levels cls) <->
    exists cl, Clauses.In cl cls /\ LevelSet.In l (levels (premise cl)).
  Proof.
    unfold clauses_premises_levels.
    rewrite clauses_premises_levels_spec_aux.
    intuition auto. lsets.
  Qed.

  Lemma clauses_levels_premises cls V : clauses_levels cls ⊂_lset V ->
    clauses_premises_levels cls ⊂_lset V.
  Proof.
    intros hin x; rewrite clauses_premises_levels_spec; move => [cl [hin' eq]]; apply hin.
    rewrite clauses_levels_spec. exists cl. split => //.
    rewrite clause_levels_spec. now left.
  Qed.

  Lemma clauses_premises_levels_incl cls : clauses_premises_levels cls ⊂_lset clauses_levels cls.
  Proof.
    intros x; rewrite clauses_premises_levels_spec clauses_levels_spec; move => [cl [hin' eq]].
    exists cl; split => //.
    rewrite clause_levels_spec. now left.
  Qed.

  Lemma clauses_premises_levels_mon {cls cls'} : cls ⊂_clset cls' ->
    clauses_premises_levels cls ⊂_lset clauses_premises_levels cls'.
  Proof.
    intros hin x; rewrite !clauses_premises_levels_spec; move => [cl [hin' eq]].
    exists cl; split => //. now apply hin.
  Qed.

  Definition monotone_selector sel :=
    forall cls' cls, cls' ⊂_clset cls -> sel cls' ⊂_lset sel cls.

  Lemma clauses_levels_mon : monotone_selector clauses_levels.
  Proof.
    intros cls' cls hin x; rewrite !clauses_levels_spec; move => [cl [hin' eq]].
    exists cl; split => //. now apply hin.
  Qed.

  Lemma clauses_with_concl_union cls W W' :
    Clauses.Equal (cls ↓ (W ∪ W'))
      (Clauses.union (cls ↓ W) (cls ↓ W')).
  Proof.
    intros x. rewrite Clauses.union_spec !in_clauses_with_concl LevelSet.union_spec.
    firstorder.
  Qed.

  Lemma clauses_with_concl_subset cls W : (cls ↓ W) ⊂_clset cls.
  Proof. now intros ?; rewrite in_clauses_with_concl. Qed.

  Lemma union_diff_eq {cls cls'} : Clauses.Equal (Clauses.union cls (Clauses.diff cls' cls))
    (Clauses.union cls cls').
  Proof. clsets. Qed.

  Lemma union_restrict_with_concl {cls W} :
    Clauses.Equal (Clauses.union (cls ⇂ W) (cls ↓ W)) (cls ↓ W).
  Proof.
    intros cl. rewrite Clauses.union_spec.
    intuition auto.
    eapply in_clauses_with_concl.
    now eapply in_restrict_clauses in H0 as [].
  Qed.

  Lemma union_diff {cls W} :
    Clauses.Equal (Clauses.union (Clauses.diff (cls ↓ W) (cls ⇂ W)) (cls ⇂ W)) (cls ↓ W).
  Proof.
    now rewrite ClausesProp.union_sym union_diff_eq union_restrict_with_concl.
  Qed.

  Lemma union_diff_cls {cls W} :
    Clauses.Equal (Clauses.union (Clauses.diff (cls ↓ W) (cls ⇂ W)) cls) cls.
  Proof.
    intros ?. rewrite Clauses.union_spec Clauses.diff_spec in_restrict_clauses in_clauses_with_concl.
    firstorder.
  Qed.

  Lemma clauses_partition_spec {cls W allW conclW} :
    clauses_conclusions cls ⊂_lset W ->
    Clauses.partition (premise_restricted_to W) cls = (allW, conclW) ->
    (Clauses.Equal allW (cls ⇂ W)) /\
    (Clauses.Equal conclW (Clauses.diff cls (cls ⇂ W))).
  Proof.
    intros clW.
    destruct Clauses.partition eqn:eqp.
    intros [= <- <-].
    change t with (t, t0).1.
    change t0 with (t, t0).2 at 2.
    rewrite -eqp. clear t t0 eqp.
    split.
    - intros cl. rewrite Clauses.partition_spec1.
      rewrite in_restrict_clauses Clauses.filter_spec.
      rewrite /premise_restricted_to LevelSet.subset_spec. firstorder eauto.
      apply clW, clauses_conclusions_spec. now exists cl.
    - intros cl. rewrite Clauses.partition_spec2.
      rewrite Clauses.filter_spec Clauses.diff_spec.
      rewrite /premise_restricted_to. intuition auto.
      move/negbTE: H1. eapply eq_true_false_abs.
      eapply LevelSet.subset_spec.
      now eapply in_restrict_clauses in H as [].
      apply eq_true_not_negb. move/LevelSet.subset_spec => he.
      apply H1. apply in_restrict_clauses. split => //.
      apply clW, clauses_conclusions_spec. now exists cl.
  Qed.

  Lemma clauses_conclusions_eq cls W :
    clauses_conclusions cls ⊂_lset W ->
    Clauses.Equal cls (cls ↓ W).
  Proof.
    intros cl x.
    rewrite in_clauses_with_concl. intuition auto.
    apply cl, clauses_conclusions_spec. now exists x.
  Qed.

  Definition levelexprset_of_levels (ls : LevelSet.t) n : LevelExprSet.t :=
    LevelSet.fold (fun x => LevelExprSet.add (x, n)) ls LevelExprSet.empty.

  Lemma levelexprset_of_levels_spec {ls : LevelSet.t} {l k n} :
    LevelExprSet.In (l, k) (levelexprset_of_levels ls n) <-> LevelSet.In l ls /\ k = n.
  Proof.
    rewrite /levelexprset_of_levels.
    eapply LevelSetProp.fold_rec.
    - intros s' he. rewrite LevelExprSetFact.empty_iff. firstorder.
    - intros x a s' s'' hin hnin hadd ih.
      rewrite LevelExprSet.add_spec; unfold LevelExprSet.E.eq.
      firstorder eauto; try noconf H1 => //.
      apply hadd in H1. firstorder. subst. now left.
  Qed.

  #[program]
  Definition of_level_set (ls : LevelSet.t) n (hne : ~ LevelSet.Empty ls) : premises :=
    {| t_set := levelexprset_of_levels ls n |}.
  Next Obligation.
    apply not_Empty_is_empty => he. apply hne.
    intros l nin. specialize (he (l,n)). apply he.
    now rewrite levelexprset_of_levels_spec.
  Qed.

  Lemma of_level_set_union_spec {ls ls' n hne} hne' hne'' :
    of_level_set (ls ∪ ls') n hne =
    univ_union (of_level_set ls n hne') (of_level_set ls' n hne'').
  Proof.
    apply eq_univ_equal.
    intros [l k]. rewrite /of_level_set //= !levelexprset_of_levels_spec LevelExprSet.union_spec.
    rewrite !levelexprset_of_levels_spec LevelSet.union_spec. clear. firstorder.
  Qed.

  Lemma of_level_set_singleton l k hne : of_level_set (LevelSet.singleton l) k hne = singleton (l, k).
  Proof.
    apply eq_univ_equal. move=> [l' k'].
    rewrite /of_level_set //= levelexprset_of_levels_spec !LevelExprSet.singleton_spec LevelSet.singleton_spec /LevelSet.E.eq /LevelExprSet.E.eq.
    firstorder subst => //. now noconf H. now noconf H.
  Qed.

  Definition max_premise_of l (u : premises) : option Z :=
    LevelExprSet.fold (fun '(l', k) acc => if eqb l l' then
      max_opt_of Z.max (Some k) acc else acc) u None.

  Lemma max_premise_of_spec l k (u : premises) : LevelExprSet.In (l, k) u -> Some k ≤ max_premise_of l u.
  Proof.
    rewrite /max_premise_of.
    eapply LevelExprSetProp.fold_rec.
    - intros s' he hin. now apply he in hin.
    - intros x a s' s'' hin nin hadd hle.
      intros hs''. destruct x.
      apply hadd in hs'' as [].
      * noconf H. rewrite eqb_refl. destruct a; cbn. constructor. lia. reflexivity.
      * elim: eqb_spec; try intros ->;
        specialize (hle H); depelim hle; cbn; constructor; lia.
  Qed.

  Definition max_clause_premise_of l (cls : clauses) :=
    Clauses.fold (fun cl acc => max_opt_of Z.max (max_premise_of l (premise cl)) acc) cls None.

  Lemma max_clause_premise_of_spec l k cls :
    forall cl, Clauses.In cl cls -> LevelExprSet.In (l, k) (premise cl) -> Some k ≤ max_clause_premise_of l cls.
  Proof.
    rewrite /max_clause_premise_of => cl.
    eapply ClausesProp.fold_rec.
    - intros s' he hin. now apply he in hin.
    - intros x a s' s'' hin nin hadd hle.
      intros hs''. destruct x.
      apply hadd in hs'' as [].
      * noconf H. cbn. move/max_premise_of_spec.
        intros h; etransitivity; tea. destruct (max_premise_of l n), a; cbn; constructor; lia.
      * intros h; specialize (hle H h). depelim hle. cbn.
        destruct (max_premise_of l n); cbn; constructor; lia.
  Qed.

  Definition max_clause_premises cls :=
    let ls := clauses_levels cls in
    let fn l m := LevelMap.add l (max_clause_premise_of l cls) m in
    LevelSet.fold fn ls (LevelMap.empty _).

  Lemma max_clause_premises_spec l k cls :
    LevelMap.MapsTo l k (max_clause_premises cls) ->
    LevelSet.In l (clauses_levels cls) /\ k = max_clause_premise_of l cls.
  Proof.
    unfold max_clause_premises.
    eapply LevelSetProp.fold_rec.
    - intros s' he hm. now rewrite LevelMapFact.F.empty_mapsto_iff in hm.
    - intros x a s' s'' hin hnin hadd ih.
      rewrite LevelMapFact.F.add_mapsto_iff.
      intros [[-> [= <-]]|[]] => //.
      * split => //. apply hadd. now left.
      * split => //. apply hadd; now right. now apply ih.
  Qed.

  Lemma max_clause_premises_spec_inv cls :
    forall l, LevelSet.In l (clauses_levels cls) ->
    LevelMap.MapsTo l (max_clause_premise_of l cls) (max_clause_premises cls).
  Proof.
    unfold max_clause_premises.
    eapply LevelSetProp.fold_rec.
    - intros s' he hm. now move/he.
    - intros x a s' s'' hin hnin hadd ih l ls''.
      rewrite LevelMapFact.F.add_mapsto_iff.
      destruct (eq_dec x l). subst.
      * now left.
      * right. split => //. apply ih. eapply hadd in ls''. destruct ls''; auto. contradiction.
  Qed.

  Local Open Scope Z_scope.

  Definition add_expr n '((l, k) : LevelExpr.t) := (l, k + n).

  Lemma add_expr_add_expr n n' lk : add_expr n (add_expr n' lk) = add_expr (n + n') lk.
  Proof. destruct lk; unfold add_expr. f_equal; lia. Qed.
  Definition add_prems n s := map (add_expr n) s.

  Lemma In_add_prems k (prems : premises):
    forall le, LevelExprSet.In le (add_prems k prems) <->
      exists le', LevelExprSet.In le' prems /\ le = add_expr k le'.
  Proof.
    intros [l k'].
    now rewrite /add_prems map_spec.
  Qed.

  Lemma add_expr_inj {n e e'} : add_expr n e = add_expr n e' -> e = e'.
  Proof.
    destruct e, e'; cbn; intros [=].
    have eq: z = z0 by lia.
    now subst z0.
  Qed.

  Lemma add_prems_inj n prems prems' : add_prems n prems = add_prems n prems' -> prems = prems'.
  Proof.
    rewrite /add_prems => /eq_univ_equal hm.
    apply eq_univ_equal.
    intros [l k]. specialize (hm (l, k + n)).
    rewrite !map_spec in hm. destruct hm as [hl hr].
    split; intros hin.
    - forward hl. exists (l, k); split => //.
      destruct hl as [[] [hin' eq]].
      apply (@add_expr_inj n (l, k)) in eq. now noconf eq.
    - forward hr. exists (l, k); split => //.
      destruct hr as [[] [hin' eq]].
      apply (@add_expr_inj n (l, k)) in eq. now noconf eq.
  Qed.

  Lemma inj_add_prems_sub {n u u'} : add_prems n u ⊂_leset add_prems n u' -> u ⊂_leset u'.
  Proof.
    rewrite /add_prems.
    intros hm [l k]. specialize (hm (l, k + n)).
    rewrite !map_spec in hm.
    intros hin.
    forward hm. exists (l, k); split => //.
    destruct hm as [[] [hin' eq]].
    apply (@add_expr_inj n (l, k)) in eq. now noconf eq.
  Qed.

  Lemma add_prems_add_prems n n' lk : add_prems n (add_prems n' lk) = add_prems (n + n') lk.
  Proof. destruct lk; unfold add_prems.
    rewrite map_map. apply eq_univ_equal.
    intros x. rewrite !map_spec. cbn in *.
    firstorder eauto. subst. exists x0.
    firstorder eauto. now rewrite add_expr_add_expr.
    subst. exists x0.
    firstorder eauto. now rewrite add_expr_add_expr.
  Qed.

  Lemma add_prems_add {n lk prems} : add_prems n (add lk prems) = add (add_expr n lk) (add_prems n prems).
  Proof.
    apply eq_univ_equal. intros x.
    rewrite In_add_prems LevelExprSet.add_spec In_add_prems /LevelExprSet.E.eq; rw LevelExprSet.add_spec.
    firstorder. subst. red in H; subst x0. now left.
  Qed.

  Lemma add_prems_0 u : add_prems 0 u = u.
  Proof.
    rewrite /add_prems.
    apply eq_univ_equal.
    intros x. rewrite map_spec.
    split.
    - intros[e [hin ->]]. unfold add_expr. now destruct e; rewrite Z.add_0_r.
    - intros inu; exists x. split => //. destruct x. now rewrite /add_expr Z.add_0_r.
  Qed.

  Lemma add_prems_of_level_set k W k' prf :
    add_prems k (of_level_set W k' prf) = of_level_set W (k + k') prf.
  Proof.
    apply eq_univ_equal => [] [l n].
    rewrite In_add_prems /of_level_set //= levelexprset_of_levels_spec.
    split.
    - move=> [] [l' n']. rewrite levelexprset_of_levels_spec => [] [[inw eq] eq'].
      subst n'. noconf eq'. split => //. lia.
    - move=> [inW ->]. exists (l, k'). rewrite levelexprset_of_levels_spec.
      split => //. cbn. f_equal; lia.
  Qed.

  Definition add_clause n '((prems, concl) : clause) := (add_prems n prems, add_expr n concl).

  Lemma add_clause_add_clause n n' cl : add_clause n (add_clause n' cl) = add_clause (n + n') cl.
  Proof.
    destruct cl.
    unfold add_clause.
    now rewrite add_prems_add_prems add_expr_add_expr.
  Qed.

  Notation succ_expr := (add_expr 1).
  Notation succ_prems := (add_prems 1).
  Notation succ_clause := (add_clause 1).

  Arguments add_prems : simpl never.

  Lemma add_clause_inj {n x y} : add_clause n x = add_clause n y -> x = y.
  Proof.
    destruct x as [prems concl], y as [prems' concl']. cbn.
    apply: pair_inj. now move=> /add_prems_inj -> /add_expr_inj ->.
  Qed.
  Definition add_clauses n cls := ClausesProp.of_list (List.map (fun cl => add_clause n cl) (ClausesProp.to_list cls)).
  Notation succ_clauses := (add_clauses 1).
  Import SetoidList.

  Lemma add_clauses_spec {cl cls} n : Clauses.In cl cls <-> Clauses.In (add_clause n cl) (add_clauses n cls).
  Proof.
    unfold succ_clauses.
    rewrite ClausesProp.of_list_1 InA_In_eq in_map_iff.
    firstorder eauto.
    - exists cl; split => //. unfold ClausesProp.to_list. now eapply Clauses_In_elements.
    - eapply Clauses_In_elements in H0. apply add_clause_inj in H. now subst.
  Qed.

  Lemma in_add_clauses {cl cls} n : Clauses.In cl (add_clauses n cls) -> exists cl', Clauses.In cl' cls /\ cl = add_clause n cl'.
  Proof.
    unfold succ_clauses.
    rewrite ClausesProp.of_list_1 InA_In_eq in_map_iff.
    firstorder eauto.
    exists x; split => //. unfold ClausesProp.to_list. now eapply Clauses_In_elements.
  Qed.

  Lemma clauses_levels_add {n cls} : clauses_levels (add_clauses n cls) =_lset clauses_levels cls.
  Proof.
    intros l.
    rewrite clauses_levels_spec.
    split.
    - move=> [] cl [] /in_add_clauses [] cl' [] incl' ->.
      rewrite clause_levels_spec. cbn. destruct cl; cbn.
      intros h. apply clauses_levels_spec. exists cl'; split => //.
      move: h; case.
      move/levelexprset_levels_spec => [k].
      destruct cl'; cbn in * => /In_add_prems => [] [] x [].
      destruct x => hin [=] ->. intros ->.
      apply clause_levels_spec. left. apply levelexprset_levels_spec. now exists z.
      intros ->. apply clause_levels_spec; right. destruct cl' => //=. destruct t0 => //.
    - move/clauses_levels_spec => [] cl [] hin /clause_levels_spec [].
      * move=> /levelexprset_levels_spec => [] [k hin']; exists (add_clause n cl); split => //.
        now apply add_clauses_spec.
        apply clause_levels_spec. left.
        apply levelexprset_levels_spec. exists (k + n).
        destruct cl; cbn. apply In_add_prems. exists (l, k).
        split => //.
      * intros ->. exists (add_clause n cl); split => //. now apply add_clauses_spec.
        apply clause_levels_spec. right.
        destruct cl; cbn. destruct t => //.
  Qed.

  Lemma add_clause_0 cl : add_clause 0 cl = cl.
  Proof.
    destruct cl as [prems [concl k]]; cbn.
    f_equal. 2:now rewrite Z.add_0_r.
    unfold add_prems.
    eapply eq_univ_equal. intros [l k'].
    rewrite NonEmptySetFacts.map_spec.
    unfold add_expr. split.
    - intros [[] [hin heq]]. noconf heq. now rewrite Z.add_0_r.
    - exists (l, k'); split => //. now rewrite Z.add_0_r.
  Qed.

  Lemma add_clause_singleton n le concl k : add_clause n (singleton le, (concl, k)) = (singleton (add_expr n le), (concl, k + n)).
  Proof.
    rewrite /add_clause //=. f_equal.
    apply eq_univ_equal. intros le'. rewrite In_add_prems.
    rewrite_strat (topdown LevelExprSet.singleton_spec).
    unfold LevelExprSet.E.eq. firstorder. subst. reflexivity.
  Qed.

  Lemma add_prems_singleton n cl : add_prems n (singleton cl) = singleton (add_expr n cl).
  Proof.
    apply eq_univ_equal => [] [l k].
    rewrite In_add_prems LevelExprSet.singleton_spec.
    firstorder.
    - destruct x; noconf H0.
      eapply LevelExprSet.singleton_spec in H.
      now red in H; noconf H.
    - destruct cl. exists (t, z). split => //.
      red in H; noconf H. now apply LevelExprSet.singleton_spec.
  Qed.

  Lemma max_premise_of_spec_aux s l k :
    max_premise_of l s = k ->
    (forall k', LevelExprSet.In (l, k') s -> (Some k' ≤ k)) /\
    ((exists k', LevelExprSet.In (l, k') s /\ k = Some k') \/
      ((~ exists k', LevelExprSet.In (l, k') s) /\ k = None)).
  Proof.
    unfold max_premise_of.
    revert k.
    eapply LevelExprSetProp.fold_rec.
    - intros s' he k <-. cbn. split => //.
      * now move=> k' /he.
      * right; split => //. now move=> [] k' /he.
    - intros [l' k'] a s' s'' hin hnin hadd ih k.
      specialize (ih _ eq_refl) as [hle hex].
      intros hmax.
      split. move=> k'0 /hadd => [] [].
      { move=> [=] eq eq'. subst l' k'. rewrite eqb_refl in hmax.
        destruct a; cbn in hmax; subst; constructor; lia. }
      { move/hle. move: hmax. destruct (eqb_spec l l'); subst.
        intros <-. intros h; depelim h; cbn. constructor; lia.
        intros -> h; depelim h; constructor; lia. }
      destruct hex as [[k'' [hin' heq]]|nex]. subst a.
      { left. destruct (eqb_spec l l'). subst. exists (Z.max k' k''); split; trea.
        2:{ subst k. eexists; split => //. apply hadd. now right. }
        eapply hadd.
        destruct (Z.max_spec k' k'') as [[hlt ->]|[hle' ->]] => //. now right. now left. }
      destruct nex as [nex ->].
      destruct (eqb_spec l l'). subst. left. exists k'. split => //. apply hadd; now left.
      subst k. right. split => //.
      intros [k'' hin']. apply hadd in hin' as []. noconf H0. congruence.
      apply nex. now exists k''.
  Qed.

  Lemma max_premise_of_prems_max {l prems k} :
    max_premise_of l prems = Some k -> LevelExprSet.In (l, k) prems.
  Proof.
    destruct max_premise_of eqn:maxp => //. intros [= ->].
    apply max_premise_of_spec_aux in maxp as [hle hex].
    destruct hex as [[k' [hin [= ->]]]|hne] => //.
    destruct hne; congruence.
  Qed.

  Lemma max_premise_of_singleton l k : max_premise_of l (singleton (l, k)) = Some k.
  Proof.
    remember (max_premise_of l (singleton (l, k))) as mp. symmetry in Heqmp.
    apply max_premise_of_spec_aux in Heqmp as [hle hex].
    destruct hex as [[k' [hin heq]]|hne] => //.
    eapply LevelExprSet.singleton_spec in hin. now noconf hin.
    destruct hne as [nein ->]. elim nein.
    exists k. now eapply LevelExprSet.singleton_spec.
  Qed.

  Lemma max_premise_of_spec2 l k (u : premises) : LevelExprSet.In (l, k) u ->
    exists k', LevelExprSet.In (l, k') u /\ max_premise_of l u = Some k'.
  Proof.
    remember (max_premise_of l u) as mp. symmetry in Heqmp.
    apply max_premise_of_spec_aux in Heqmp as [hle hex].
    intros hin. destruct hex. firstorder.
    destruct H as [nein ->]. elim nein. now exists k.
  Qed.

  Lemma max_premise_of_spec_in l (u : premises) : LevelSet.In l (levels u) ->
    exists k, max_premise_of l u = Some k /\ LevelExprSet.In (l, k) u.
  Proof.
    intros hexi.
    remember (max_premise_of l u) as mp. symmetry in Heqmp.
    apply max_premise_of_spec_aux in Heqmp as [hle hex].
    destruct hex. destruct H as [l' [hin heq]]. subst mp.
    - eexists; split => //.
    - destruct H as [nein ->]. elim nein.
      now eapply levelexprset_levels_spec in hexi.
  Qed.

  Variant in_pred_closure cls : clause -> Prop :=
  | incls cl n : Clauses.In cl cls -> in_pred_closure cls (add_clause n cl)
  | predcl x k : in_pred_closure cls (singleton (x, k + 1), (x, k)).
  Derive Signature for in_pred_closure.

  Inductive entails (cls : clauses) : clause -> Prop :=
  | clause_in (prems : premises) (concl : LevelExpr.t) :
    LevelExprSet.In concl prems -> entails cls (prems, concl)
  | clause_cut prems' concl' prems concl :
    in_pred_closure cls (prems', concl') ->
    entails cls (add concl' prems, concl) ->
    LevelExprSet.Subset prems' prems ->
    entails cls (prems, concl).

  Definition entails_all cls (prems concls : premises) :=
    LevelExprSet.For_all (fun le => entails cls (prems, le)) concls.

  Notation " cls ⊢ prems → concl " := (entails cls (prems, concl)) (at level 20).
  Notation " cls ⊢a prems → concl " := (entails_all cls prems concl) (at level 20).

  Lemma in_pred_closure_equal cls (prems prems' : premises) concl :
    LevelExprSet.Equal prems prems' ->
    in_pred_closure cls (prems, concl) -> in_pred_closure cls (prems', concl).
  Proof.
    intros eq. apply NonEmptySetFacts.eq_univ_equal in eq. now subst prems.
  Qed.

  Lemma entails_equal cls (prems prems' : premises) concl :
    LevelExprSet.Equal prems prems' ->
    entails cls (prems, concl) -> entails cls (prems', concl).
  Proof.
    intros he en.
    replace prems' with prems => //.
    now apply eq_univ_equal.
  Qed.

  Lemma entails_plus cls c : entails cls c -> entails (succ_clauses cls) (succ_clause c).
  Proof.
    induction 1.
    - constructor. apply map_spec. exists concl0. split => //.
    - eapply clause_cut with (succ_prems prems') (succ_expr concl').
      + depelim H.
        * have -> : (succ_prems prems', succ_expr concl') = add_clause n (succ_clause cl).
          { destruct cl as [prems'' concl'']. cbn in H0. noconf H0.
            rewrite add_prems_add_prems add_expr_add_expr add_clause_add_clause.
            now rewrite Z.add_1_r Z.add_1_l. }
          constructor. now rewrite -add_clauses_spec.
        * have eq : (succ_prems (singleton (x, (k + 1)))) = (singleton (x, k + 1 + 1)).
          { apply eq_univ_equal. unfold succ_prems.
            intros le. rewrite map_spec LevelExprSet.singleton_spec.
            split.
            { intros [? [hin ->]].
              rewrite LevelExprSet.singleton_spec in hin. red in hin; subst x0.
              reflexivity. }
            { unfold LevelExprSet.E.eq. intros ->.
              exists (x, k + 1). split.
              now rewrite LevelExprSet.singleton_spec. reflexivity. } }
          rewrite eq. constructor 2.
      + unfold succ_clause in IHentails.
        eapply entails_equal; tea.
        intros x. rewrite /succ_prems. rewrite map_spec add_spec.
        setoid_rewrite add_spec. rewrite map_spec.
        firstorder eauto. subst. now left.
      + intros x. rewrite /succ_prems !map_spec.
        intros [e [hin ->]]. exists e. firstorder.
  Qed.


  Derive Signature for entails.

  Lemma entails_pred_closure {cls prems concl k} :
    cls ⊢ prems → (concl, 1 + k) -> cls ⊢ prems → (concl, k).
  Proof.
    intros he.
    Opaque Z.add.
    depind he.
    - eapply clause_cut.
      constructor.
      2:{ intros l hin. rewrite LevelExprSet.singleton_spec in hin. red in hin; subst l.
          rewrite Z.add_comm; exact H. }
      constructor.
      rewrite LevelExprSet.add_spec. lesets.
    - eapply clause_cut; tea.
  Qed.

  Lemma entails_pred_closure_n {cls prems concl k n} :
    entails cls (prems, (concl, k + Z.of_nat n)) -> entails cls (prems, (concl, k)).
  Proof.
    induction n in k |- *.
    - rewrite Z.add_0_r. tauto.
    - intros hen. rewrite Nat2Z.inj_succ in hen. rewrite Z.add_succ_r in hen.
      eapply IHn. move: hen.
      have -> : Z.succ (k + Z.of_nat n) = 1 + (k + Z.of_nat n) by lia.
      eapply entails_pred_closure.
  Qed.


  Lemma incls0 {cls cl} : Clauses.In cl cls -> in_pred_closure cls cl.
  Proof.
    intros hin.
    have hcl := incls _ _ 0 hin.
    now rewrite add_clause_0 in hcl.
  Qed.

  Lemma entails_in {cls cl} : Clauses.In cl cls -> entails cls cl.
  Proof.
    intros hin.
    destruct cl as [prems concl].
    eapply clause_cut.
    - now eapply incls0.
    - constructor. eapply LevelExprSet.add_spec. now left.
    - reflexivity.
  Qed.

  Lemma in_pred_closure_shift {cls cl} n : in_pred_closure cls cl -> in_pred_closure cls (add_clause n cl).
  Proof.
    destruct 1.
    - rewrite add_clause_add_clause. now constructor.
    - cbn. eapply in_pred_closure_equal with (singleton (x, k + 1 + n)).
      { intros le. rewrite In_add_prems; rewrite_strat (topdown LevelExprSet.singleton_spec).
        intuition auto. exists (x, k + 1). split => //.
        now destruct H as [le' [-> ->]]. }
      have -> : k + 1 + n = (k + n) + 1 by lia.
      constructor.
  Qed.

  (* Unused now *)
  Definition premises_of_level_set (l : LevelSet.t) :=
    LevelSet.fold (fun l acc => (l, 0) :: acc) l [].

  Lemma premises_of_level_set_spec l k V : LevelSet.In l V /\ k = 0 <-> In (l, k) (premises_of_level_set V).
  Proof.
    rewrite /premises_of_level_set.
    eapply LevelSetProp.fold_rec.
    - intros s' he. firstorder.
    - intros x a s' s'' hin hnin hadd ih.
      red in hadd. rewrite {}hadd.
      cbn. firstorder. subst. now left. noconf H1. now left. now noconf H1.
  Qed.

  Lemma premises_of_level_set_empty : premises_of_level_set LevelSet.empty = [].
  Proof.
    now rewrite /premises_of_level_set LevelSetProp.fold_empty.
  Qed.

  Lemma in_succ_add_premises {V u x k} : LevelExprSet.In (x, Z.of_nat (k + 1)) (add_list (premises_of_level_set V) u) -> LevelExprSet.In (x, Z.of_nat (k + 1)) u.
  Proof.
    rewrite add_list_spec. intros [hn|hn] => //.
    eapply premises_of_level_set_spec in hn as []. lia.
  Qed.


  Lemma entails_shift {cls cl} n : entails cls cl -> entails cls (add_clause n cl).
  Proof.
    induction 1.
    - unfold add_clause. constructor.
      rewrite In_add_prems. exists concl0. split => //.
    - eapply (clause_cut _ (add_prems n prems') (add_expr n concl')).
      2:{ unfold add_clause in *. eapply entails_equal; tea.
      intros le. setoid_rewrite In_add_prems. setoid_rewrite LevelExprSet.add_spec.
      setoid_rewrite In_add_prems.
      unfold LevelExprSet.E.eq. firstorder. subst. now left. }
      2:{ intros x. rewrite !In_add_prems. firstorder. }
      eapply (in_pred_closure_shift _ H).
  Qed.

  Lemma entails_subset cls (prems prems' : premises) concl : LevelExprSet.Subset prems prems' ->
    entails cls (prems, concl) ->
    entails cls (prems', concl).
  Proof.
    intros hsubt.
    intros H; revert prems' hsubt; depind H.
    - constructor. eapply hsubt, H.
    - intros prems'' hsub.
      eapply clause_cut. 2:eapply IHentails. tea.
      2:lesets. intros x; rewrite !LevelExprSet.add_spec. firstorder.
  Qed.

  Lemma entails_trans {cls prems concl concl'} :
    entails cls (prems, concl) ->
    entails cls (singleton concl, concl') ->
    entails cls (prems, concl').
  Proof.
    intros H; depind H.
    - intros he.
      depelim he.
      * rewrite LevelExprSet.singleton_spec in H0. red in H0; subst concl0.
        now constructor.
      * eapply (clause_cut _ prems'). tea.
        eapply entails_subset; tea.
        intros ?; rewrite !LevelExprSet.add_spec LevelExprSet.singleton_spec; firstorder.
        red in H2; subst a. now right. intros x. firstorder. apply H1 in H2.
        rewrite LevelExprSet.singleton_spec in H2. now red in H2; subst x.
    - intros he.
      specialize (IHentails concl'0 he).
      eapply clause_cut; tea.
  Qed.

  Lemma entails_weak {cls prem concl concl'} :
    entails cls (prem, concl) ->
    entails cls (add concl' prem, concl).
  Proof.
    intros H. depind H.
    - constructor. apply LevelExprSet.add_spec. now right.
    - eapply (clause_cut _ _ concl'); tea.
      rewrite add_comm. apply IHentails.
      intros x; rewrite LevelExprSet.add_spec. firstorder.
  Qed.

  Lemma entails_weak_union {cls prem concl concl'} :
    entails cls (prem, concl) ->
    entails cls (univ_union concl' prem, concl).
  Proof.
    intros hyp.
    move: concl'.
    apply: premises_elim.
    - intros le. rewrite univ_union_comm univ_union_add_singleton.
      now apply entails_weak.
    - intros le prems ih.
      rewrite univ_union_add_distr. intros _.
      now eapply entails_weak.
  Qed.

  Lemma entails_all_weak {cls prem concl concl'} :
    entails_all cls prem concl ->
    entails_all cls (add concl' prem) concl.
  Proof.
    intros hcl x hin.
    specialize (hcl _ hin). cbn in hcl.
    now apply entails_weak.
  Qed.

  Lemma entails_all_weak_union {cls prem concl concl'} :
    entails_all cls prem concl ->
    entails_all cls (univ_union concl' prem) concl.
  Proof.
    intros hcl x hin.
    specialize (hcl _ hin). cbn in hcl.
    now apply entails_weak_union.
  Qed.

  Lemma entails_all_weak' {cls prem concl concl'} :
    entails_all cls prem concl ->
    entails_all cls (add concl' prem) (add concl' concl).
  Proof.
    intros hcl x hin.
    eapply LevelExprSet.add_spec in hin as []. red in H; subst.
    - constructor. eapply LevelExprSet.add_spec. now left.
    - specialize (hcl _ H). cbn in hcl.
      now apply entails_weak.
  Qed.

  Lemma entails_cut_all {cls prems' concl' prems concls} :
    in_pred_closure cls (prems', concl') ->
    cls ⊢a add concl' prems → concls ->
    prems' ⊂_leset prems ->
    cls ⊢a prems → concls.
  Proof.
    intros inp he hp x hin.
    eapply clause_cut; tea.
    now apply he in hin.
  Qed.

  Lemma entails_all_subset {cls} {prems prems' prems'' : premises} :
    prems'' ⊂_leset prems' ->
    cls ⊢a prems → prems' ->
    cls ⊢a prems → prems''.
  Proof.
    intros incl ha x hin.
    eapply incl in hin. now apply ha in hin.
  Qed.

  Lemma entails_all_add cls prem l prems' :
    cls ⊢a prem → add l prems' <->
    cls ⊢ prem → l /\ cls ⊢a prem → prems'.
  Proof.
    rewrite /entails_all /LevelExprSet.For_all.
    setoid_rewrite LevelExprSet.add_spec; rewrite /LevelExprSet.E.eq.
    firstorder. now subst.
  Qed.

  Lemma entails_add {cls prems cl concl} :
    entails cls (prems, cl) ->
    entails cls (add cl prems, concl) ->
    entails cls (prems, concl).
  Proof.
    intros H; depind H.
    - intros he.
      depelim he.
      * rewrite LevelExprSet.add_spec in H0. destruct H0 as [].
        { red in H0; subst concl0. now constructor. }
        { now constructor. }
      * have eq : prems = add concl0 prems.
        { eapply eq_univ_equal. intros x; rewrite LevelExprSet.add_spec. firstorder. now red in H2; subst. }
        rewrite -eq in H1.
        eapply (clause_cut _ prems' _ prems). tea. 2:tea.
        now rewrite -eq in he.
    - intros he.
      eapply clause_cut. tea. eapply IHentails.
      rewrite add_comm. now eapply entails_weak.
      exact H1.
  Qed.

  Lemma entails_cumul_one {cls prems prems' concl} :
    entails_all cls prems prems' ->
    entails cls (univ_union prems prems', concl) ->
    entails cls (prems, concl).
  Proof.
    revert prems' prems concl.
    apply: premises_elim.
    - intros. specialize (H le). forward H by now apply LevelExprSet.singleton_spec.
      cbn in H.
      eapply entails_add; tea.
      now rewrite -univ_union_add_singleton.
    - intros le prems ih _ prem concl' hadd hadd'.
      rewrite univ_union_comm univ_union_add_distr -univ_union_comm -univ_union_add_distr in hadd'.
      eapply ih in hadd'. 2:{ apply entails_all_weak. apply entails_all_add in hadd as []. exact H0. }
      apply entails_all_add in hadd as [].
      eapply entails_add; tea.
  Qed.

  Lemma entails_all_cumul {cls prems prems' concl} :
    entails_all cls prems prems' ->
    entails_all cls (univ_union prems prems') concl ->
    entails_all cls prems concl.
  Proof.
    intros hp hc.
    intros x hin. apply hc in hin.
    eapply entails_cumul_one; tea.
  Qed.

  Lemma entails_all_one {cls prem concl concl'} :
    entails_all cls prem concl ->
    entails cls (concl, concl') ->
    entails cls (prem, concl').
  Proof.
    intros ha he.
    eapply entails_cumul_one; tea.
    now eapply entails_weak_union.
  Qed.

  Lemma entails_all_trans {cls prem concl concl'} :
    entails_all cls prem concl ->
    entails_all cls concl concl' ->
    entails_all cls prem concl'.
  Proof.
    intros ha he cl hin.
    apply he in hin.
    eapply entails_all_one; tea.
  Qed.

  Lemma entails_incr_shift cls concl k n :
    entails cls (singleton (concl, k), (concl, k + 1)) ->
    entails cls (singleton (concl, k), (concl, k + 1 + Z.of_nat n)).
  Proof.
    induction n in k |- *; auto.
    - now rewrite Z.add_0_r.
    - intros en.
      have hs := entails_shift 1 en. rewrite add_clause_singleton /= in hs.
      apply IHn in hs.
      eapply entails_trans; tea.
      now have -> : k + 1 + Z.of_nat (S n) = k + 1 + 1 + Z.of_nat n by lia.
  Qed.

  Lemma entails_incr_all cls concl k :
    entails cls (singleton (concl, k), (concl, k + 1)) ->
    forall k', entails cls (singleton (concl, k), (concl, k')).
  Proof.
    intros en k'.
    destruct (Z.lt_trichotomy k k') as [|[]]; subst; auto.
    - have ispos : 0 <= k' - k - 1 by lia.
      eapply (entails_incr_shift _ _ _ (Z.to_nat (k' - k - 1))) in en.
      assert (k + 1 + Z.of_nat (Z.to_nat (k' - k - 1)) = k') by lia. now rewrite H0 in en.
    - constructor. now rewrite LevelExprSet.singleton_spec.
    - have [k0 ->] : (exists kd : nat, k = k' + Z.of_nat kd). { exists (Z.to_nat (k - k')). lia. }
      eapply (entails_pred_closure_n (n:=k0)). constructor. now apply LevelExprSet.singleton_spec.
  Qed.

  Lemma entails_all_concl_union {cls prems concl concl'} :
    cls ⊢a prems → concl ->
    cls ⊢a prems → concl' ->
    cls ⊢a prems → univ_union concl concl'.
  Proof.
    intros l r.
    rewrite /entails_all.
    intros x. rewrite univ_union_spec. intros []. now apply l. now apply r.
  Qed.

  Lemma entails_all_union {cls prems concl prems' concl'} :
    cls ⊢a prems → concl ->
    cls ⊢a prems' → concl' ->
    cls ⊢a univ_union prems prems' → univ_union concl concl'.
  Proof.
    intros l r.
    apply entails_all_concl_union.
    rewrite univ_union_comm.
    now eapply entails_all_weak_union.
    now eapply entails_all_weak_union.
  Qed.


  Lemma entails_all_shift {cls : clauses} {prems concl : premises} (n : Z) :
    cls ⊢a prems → concl ->
    cls ⊢a add_prems n prems → add_prems n concl.
  Proof.
    intros cla cl.
    rewrite In_add_prems => [[le' [hin ->]]].
    eapply (entails_shift (cl := (prems, le'))).
    now apply cla in hin.
  Qed.

  Lemma in_pred_closure_subset {cls cls' prems concl} :
    in_pred_closure cls (prems, concl) ->
    cls ⊂_clset cls' ->
    in_pred_closure cls' (prems, concl).
  Proof.
    induction 1.
    - move/(_ _ H). now constructor.
    - constructor.
  Qed.

  Lemma entails_clauses_subset cls cls' prems concl :
    cls ⊢ prems → concl ->
    cls ⊂_clset cls' ->
    cls' ⊢ prems → concl.
  Proof.
    induction 1 in cls' |- * => incl.
    - now constructor.
    - eapply clause_cut.
      + eapply in_pred_closure_subset; tea.
      + now apply IHentails.
      + assumption.
  Qed.

  Lemma entails_all_clauses_subset cls cls' prems concl :
    cls ⊢a prems → concl ->
    cls ⊂_clset cls' ->
    cls' ⊢a prems → concl.
  Proof.
    intros d incl [l k].
    now move/d/entails_clauses_subset.
  Qed.

  Lemma entails_succ cls (u v : premises) :
    (forall l k, LevelExprSet.In (l, k) v -> exists k', LevelExprSet.In (l, k') u /\ k <= k') ->
    cls ⊢a u → v.
  Proof.
    intros hk [l k] hin.
    specialize (hk _ _ hin) as [k' [hin' le]].
    assert (exists n, k' = k + n) as [n ->] by (exists (k' - k); lia).
    eapply (entails_pred_closure_n (n := Z.to_nat n)).
    constructor. rewrite Z2Nat.id. lia. assumption.
  Qed.

  Lemma entails_all_tauto cls u : cls ⊢a u → u.
  Proof.
    intros x hin. now constructor.
  Qed.

  Lemma loop_any_successor cls u n :
    cls ⊢a u → succ_prems u ->
    cls ⊢a u → add_prems (Z.of_nat (S n)) u.
  Proof.
    induction n.
    - auto.
    - intros ass.
      specialize (IHn ass).
      have sh := entails_all_shift 1 IHn.
      eapply entails_all_trans. tea.
      rewrite add_prems_add_prems in sh.
      have eq : 1 + Z.of_nat (S n) = Z.of_nat (S (S n)) by lia.
      now rewrite eq in sh.
  Qed.

  Lemma entails_pred_closure_neg {cls u concl k p} :
    cls ⊢ u → (concl, k) ->
    cls ⊢ u → (concl, k + Z.neg p).
  Proof.
    intros ent.
    eapply (entails_pred_closure_n (n := Pos.to_nat p)).
    have eq : Z.neg p + Z.of_nat (Pos.to_nat p) = 0. lia.
    now rewrite -Z.add_assoc eq Z.add_0_r.
  Qed.

  Lemma loop_any cls u n :
    cls ⊢a u → succ_prems u ->
    cls ⊢a u → add_prems n u.
  Proof.
    destruct n.
    - rewrite add_prems_0. intros _. apply entails_all_tauto.
    - assert (exists n, Z.pos p = Z.of_nat n). exists (Pos.to_nat p). now rewrite Z_of_pos_alt.
      destruct H as [n ->]. destruct n. cbn. intros. rewrite add_prems_0. apply entails_all_tauto.
      apply loop_any_successor.
    - intros _ [l k]. rewrite In_add_prems.
      intros [[] [hin heq]]. rewrite /add_expr in heq. noconf heq.
      apply entails_pred_closure_neg.
      now constructor.
  Qed.

  Lemma succ_clauses_equiv cls prems concl :
    succ_clauses cls ⊢ succ_prems prems → succ_expr concl ->
    cls ⊢ prems → concl.
  Proof.
    intros ha; depind ha.
    - constructor.
      move: H.
      rewrite In_add_prems => [] [le [hin heq]].
      move/add_expr_inj: heq. now intros ->.
    - depelim H.
      + destruct cl as [prems concl]. noconf H0.
        eapply in_add_clauses in H as [[prems' concl'] [hin heq]].
        noconf heq.
        eapply (clause_cut _ (add_prems n prems') (add_expr n concl')). 2:eapply IHha.
        2:{ f_equal. rewrite !add_expr_add_expr. now rewrite add_prems_add add_expr_add_expr Z.add_comm. }
        exact: (incls cls (prems', concl') n hin).
        rewrite add_prems_add_prems in H1. rewrite Z.add_comm in H1.
        rewrite -(add_prems_add_prems 1 n prems') in H1.
        now move/inj_add_prems_sub: H1.
      + specialize (H0 (x, k + 1)). forward H0. now apply LevelExprSet.singleton_spec.
        eapply In_add_prems in H0 as [[l' k'] [hin heq]]. noconf heq.
        have eq: k' = k by lia. subst k'. clear H.
        eapply clause_cut. 2:eapply IHha. eapply (predcl _ x (k - 1)).
        2:{ intros x'. move/LevelExprSet.singleton_spec => ->. now have -> : k - 1 + 1 = k by lia. }
        f_equal. rewrite add_prems_add. f_equal.
        rewrite /succ_expr //=. lia_f_equal.
  Qed.

  Lemma entails_weak_list {cls prem concl concl'} :
    cls ⊢ prem → concl ->
    cls ⊢ add_list concl' prem → concl.
  Proof.
    intros hcl.
    induction concl' in prem, hcl |- *.
    - exact hcl.
    - cbn. eapply IHconcl'. now eapply entails_weak.
  Qed.

  Lemma entails_all_weak_list {cls prem concl concl'} :
    entails_all cls prem concl ->
    entails_all cls (add_list concl' prem) concl.
  Proof.
    intros hcl x hin.
    specialize (hcl _ hin). cbn in hcl.
    now eapply entails_weak_list.
  Qed.

  Lemma entails_all_succ_clauses cls prems concl :
    succ_clauses cls ⊢a succ_prems prems → succ_prems concl ->
    cls ⊢a prems → concl.
  Proof.
    intros ha l hin. specialize (ha (succ_expr l)). forward ha.
    eapply In_add_prems. exists l. split => //. cbn in ha.
    now eapply succ_clauses_equiv in ha.
  Qed.

  Definition entails_equiv cls u u' :=
    cls ⊢a u → u' /\ cls ⊢a u' → u.

  Notation "cls '⊢a' u ↔ u'" := (entails_equiv cls u u') (at level 90).


End Clauses.
