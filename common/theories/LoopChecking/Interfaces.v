(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From MetaRocq.Common Require Import LoopChecking.Common.
From Equations Require Import Equations.
Set Equations Transparent.

Module FMapOrderedType_from_UsualOrderedType (O : UsualOrderedType).
  Import O.
  Definition t := O.t.
  Definition eq : O.t -> O.t -> Prop := O.eq.
  Definition lt : O.t -> O.t -> Prop := O.lt.
  Definition eq_refl : forall x : O.t, eq x x := reflexivity.
  Definition eq_sym : forall x y : O.t, eq x y -> eq y x := fun x y H => symmetry H.

  Lemma eq_trans : forall x y z, O.eq x y -> O.eq y z -> O.eq x z.
  Proof. intros x y z. unfold O.eq. apply transitivity. Qed.
  Lemma lt_trans : forall x y z, O.lt x y -> O.lt y z -> O.lt x z.
  Proof. intros. eapply O.lt_strorder; tea. Qed.

  Lemma lt_not_eq : forall x y : O.t, lt x y -> ~ eq x y.
  Proof.
    intros x y H eq. do 2 red in eq. subst x. now eapply lt_strorder in H.
  Qed.

  Definition compare : forall x y : O.t, Compare lt eq x y.
  Proof.
    intros.
    case_eq (compare x y); intros.
    apply EQ. abstract (destruct (compare_spec x y) => //).
    apply LT. abstract (destruct (compare_spec x y) => //).
    apply GT. abstract (destruct (compare_spec x y) => //).
  Defined.

  Definition eq_dec : forall x y : O.t, {eq x y} + {~ eq x y} := eq_dec.
End FMapOrderedType_from_UsualOrderedType.

Module Type FMapOTInterface (E : UsualOrderedType).
  Module OT := FMapOrderedType_from_UsualOrderedType E.
  Include FMapInterface.Sfun OT.
End FMapOTInterface.

Module Type LevelSets.
  (* Signature of levels: decidable, ordered type *)
  Declare Module Level : LevelOrderedTypeWithReflect.
  Declare Module LevelSet : LevelSet_fun Level.
  Declare Module LevelExpr : LevelExprItf Level.
  Declare Module LevelExprSet : LevelExprSet_fun Level LevelExpr.
  Declare Module LevelMap : FMapOTInterface Level.
End LevelSets.

Module FromLevelSets (LS : LevelSets).
Export LS.

Definition level (e : LevelExpr.t) : Level.t := fst e.
Coercion level : LevelExpr.t >-> Level.t.
Extraction Inline level.

Definition levels (e : LevelExprSet.t) :=
LevelExprSet.fold (fun le => LevelSet.add (level le)) e LevelSet.empty.
Export LevelExprSet (nonEmptyLevelExprSet, t_set, t_ne).

Existing Instance Level.reflect_eq.

Module LevelSetFact := WFactsOn Level LevelSet.
Module LevelSetProp := WPropertiesOn Level LevelSet.
Module LevelSetDecide := LevelSetProp.Dec.
Module LevelMapFact := FMapFacts.WProperties_fun LevelMap.OT LevelMap.

Declare Scope levels_scope.

Ltac lsets := LevelSetDecide.fsetdec.
Notation "(=_lset)" := LevelSet.Equal (at level 0) : levels_scope.
Infix "=_lset" := LevelSet.Equal (at level 30) : levels_scope.
Infix "⊂_lset" := LevelSet.Subset (at level 70) : levels_scope.
Infix "⊂_leset" := LevelExprSet.Subset (at level 70) : levels_scope.
Infix "∪" := LevelSet.union (at level 70) : levels_scope.
Infix "=m" := LevelMap.Equal (at level 50) : levels_scope.
Notation "#| V |" := (LevelSet.cardinal V) : levels_scope.

Open Scope levels_scope.

Definition print_level_nat_map (m : LevelMap.t nat) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => Level.to_string l ^ " -> " ^ string_of_nat w) nl list.

Definition print_lset (l : LevelSet.t) :=
  let list := LevelSet.elements l in
  print_list Level.to_string " " list.

Module LevelExprSetFact := WFactsOn LevelExpr LevelExprSet.
Module LevelExprSetProp := WPropertiesOn LevelExpr LevelExprSet.

(* We have decidable equality w.r.t leibniz equality for sets of levels. *)
#[global, program] Instance levelexprset_reflect : ReflectEq LevelExprSet.t :=
  { eqb := LevelExprSet.equal }.
Next Obligation.
  destruct (LevelExprSet.equal x y) eqn:e; constructor.
  eapply LevelExprSet.equal_spec in e.
  now eapply LevelExprSet.eq_leibniz.
  intros e'.
  subst y.
  pose proof (@LevelExprSetFact.equal_1 x x).
  forward H. reflexivity. congruence.
Qed.

#[global] Instance levelexprset_eq_dec : Classes.EqDec LevelExprSet.t := Classes.eq_dec.

Derive NoConfusion for LevelExprSet.nonEmptyLevelExprSet.

(* We use uip on the is_empty condition *)
#[global, program] Instance nonEmptyLevelExprSet_reflect : ReflectEq nonEmptyLevelExprSet :=
  { eqb x y := eqb x.(t_set) y.(t_set) }.
Next Obligation.
  destruct (eqb_spec (t_set x) (t_set y)); constructor.
  destruct x, y; cbn in *. subst.
  now rewrite (uip t_ne0 t_ne1).
  intros e; subst x; apply H.
  reflexivity.
Qed.

(** This coercion allows to see the non-empty set as a regular [LevelExprSet.t] *)
Coercion t_set : nonEmptyLevelExprSet >-> LevelExprSet.t.
Module LevelExprSetDecide := WDecide (LevelExprSet).
Ltac lesets := LevelExprSetDecide.fsetdec.

Lemma levelset_not_Empty_is_empty s :
  LevelSet.is_empty s = false <-> ~ LevelSet.Empty s.
Proof.
  split.
  - intros H he. red in he. apply negbT in H. unshelve eapply (contraNnot _ H).
    3:exact he. intros ha. now apply LevelSetFact.is_empty_1.
  - intros ne. destruct LevelSet.is_empty eqn:he => //.
    eapply LevelSetFact.is_empty_2 in he. contradiction.
Qed.

Lemma in_singleton l : LevelSet.In l (LevelSet.singleton l).
Proof. lsets. Qed.

Lemma not_in_union_inv l ls ls' :
  ~ LevelSet.In l (LevelSet.union ls ls') ->
  ~ LevelSet.In l ls /\ ~ LevelSet.In l ls'.
Proof.
  rewrite LevelSet.union_spec. firstorder.
Qed.

Lemma levelmap_add_spec {A} (m m' : LevelMap.t A) {k v}:
  LevelMapFact.Add k v m m' ->
  m' =m LevelMap.add k v m.
Proof.
  trivial.
Qed.

Lemma not_empty_exists V : ~ LevelSet.Empty V -> exists l, LevelSet.In l V.
Proof.
  intros ne.
  destruct (LevelSet.choose V) eqn:ch. exists e.
  now eapply LevelSet.choose_spec1 in ch.
  now apply LevelSet.choose_spec2 in ch.
Qed.

Module NonEmptySetFacts.
  #[program] Definition singleton (e : LevelExpr.t) : nonEmptyLevelExprSet
    := {| t_set := LevelExprSet.singleton e |}.
  Next Obligation.
    apply negbTE.
    eapply (contra_notN (P := LevelExprSet.Empty (LevelExprSet.singleton e))).
    apply LevelExprSetFact.is_empty_2. intros ne. red in ne. specialize (ne e). lesets.
  Qed.

  Lemma not_Empty_is_empty s :
    ~ LevelExprSet.Empty s <-> LevelExprSet.is_empty s = false.
  Proof.
    split.
    - intro H. apply not_true_is_false. intro H'.
      apply H. now apply LevelExprSetFact.is_empty_2 in H'.
    - intros H he. red in he. apply negbT in H. unshelve eapply (contraNnot _ H).
      3:exact he. intros ha. now apply LevelExprSetFact.is_empty_1.
  Qed.

  Program Definition add (e : LevelExpr.t) (u : nonEmptyLevelExprSet) : nonEmptyLevelExprSet
    := {| t_set := LevelExprSet.add e u |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    eapply H. eapply LevelExprSet.add_spec.
    left; reflexivity.
  Qed.

  Lemma add_spec e u e' :
    LevelExprSet.In e' (add e u) <-> e' = e \/ LevelExprSet.In e' u.
  Proof.
    apply LevelExprSet.add_spec.
  Qed.

  Definition add_list : list LevelExpr.t -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet
    := List.fold_left (fun u e => add e u).

  Lemma add_list_spec l u e :
    LevelExprSet.In e (add_list l u) <-> In e l \/ LevelExprSet.In e u.
  Proof.
    unfold add_list. rewrite <- fold_left_rev_right.
    etransitivity. 2:{ eapply or_iff_compat_r. etransitivity.
                        2: apply @InA_In_eq with (A:=LevelExpr.t).
                        eapply InA_rev. }
    induction (List.rev l); cbn.
    - split. intuition. intros [H|H]; tas. invs H.
    - split.
      + intro H. apply add_spec in H. destruct H as [H|H].
        * left. now constructor.
        * apply IHl0 in H. destruct H as [H|H]; [left|now right].
          now constructor 2.
      + intros [H|H]. inv H.
        * apply add_spec; now left.
        * apply add_spec; right. apply IHl0. now left.
        * apply add_spec; right. apply IHl0. now right.
  Qed.

  Lemma elements_not_empty {u : nonEmptyLevelExprSet} : LevelExprSet.elements u <> [].
  Proof.
    rewrite -LevelExprSetProp.elements_Empty.
    move/LevelExprSetFact.is_empty_1.
    destruct u as [u1 u2]; cbn in *. congruence.
  Qed.

  Equations to_nonempty_list (u : nonEmptyLevelExprSet) : LevelExpr.t * list LevelExpr.t :=
  | u with inspect (LevelExprSet.elements u) := {
    | exist [] eqel => False_rect _ (elements_not_empty eqel)
    | exist (e :: l) _ => (e, l) }.

  Lemma singleton_to_nonempty_list e : to_nonempty_list (singleton e) = (e, []).
  Proof.
    funelim (to_nonempty_list (singleton e)). bang.
    clear H.
    pose proof (LevelExprSet.singleton_spec e1 e).
    rewrite LevelExprSetFact.elements_iff in H.
    rewrite InA_In_eq in H. rewrite e0 in H.
    destruct H. forward H. now left. noconf H. f_equal.
    pose proof (LevelExprSet.cardinal_spec (LevelExprSet.singleton e1)). rewrite e0 in H. cbn in H.
    rewrite LevelExprSetProp.singleton_cardinal in H.
    destruct l => //.
  Qed.

  Lemma to_nonempty_list_spec u :
    let '(e, u') := to_nonempty_list u in
    e :: u' = LevelExprSet.elements u.
  Proof.
    funelim (to_nonempty_list u). bang. now rewrite e0.
  Qed.

  Lemma to_nonempty_list_spec' u :
    (to_nonempty_list u).1 :: (to_nonempty_list u).2 = LevelExprSet.elements u.
  Proof.
    pose proof (to_nonempty_list_spec u).
    now destruct (to_nonempty_list u).
  Qed.

  Lemma In_to_nonempty_list (u : nonEmptyLevelExprSet) (e : LevelExpr.t) :
    LevelExprSet.In e u
    <-> e = (to_nonempty_list u).1 \/ In e (to_nonempty_list u).2.
  Proof.
    etransitivity. symmetry. apply LevelExprSet.elements_spec1.
    pose proof (to_nonempty_list_spec' u) as H.
    destruct (to_nonempty_list u) as [e' l]; cbn in *.
    rewrite <- H; clear. etransitivity. apply InA_cons.
    eapply or_iff_compat_l. apply InA_In_eq.
  Qed.

  Lemma In_to_nonempty_list_rev (u : nonEmptyLevelExprSet) (e : LevelExpr.t) :
    LevelExprSet.In e u
    <-> e = (to_nonempty_list u).1 \/ In e (List.rev (to_nonempty_list u).2).
  Proof.
    etransitivity. eapply In_to_nonempty_list.
    apply or_iff_compat_l. apply in_rev.
  Qed.


  Program Definition non_empty_union (u v : nonEmptyLevelExprSet) : nonEmptyLevelExprSet :=
    {| t_set := LevelExprSet.union u v |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    assert (HH: LevelExprSet.Empty u). {
      intros x Hx. apply (H x).
      eapply LevelExprSet.union_spec. now left. }
    apply LevelExprSetFact.is_empty_1 in HH.
    rewrite t_ne in HH; discriminate.
  Qed.


  Lemma eq_univ (u v : nonEmptyLevelExprSet) :
    u = v :> LevelExprSet.t -> u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
    now rewrite (uip_bool _ _ u2 v2).
  Qed.

  Lemma eq_univ_equal (u v : nonEmptyLevelExprSet) :
    LevelExprSet.Equal u v <-> u = v.
  Proof.
    split.
    - intro H. now apply eq_univ, LevelExprSet.eq_leibniz.
    - intros ->; reflexivity.
  Qed.

  Lemma eq_univ_elements (u v : nonEmptyLevelExprSet) :
    LevelExprSet.elements u = LevelExprSet.elements v -> u = v.
  Proof.
    intro H. apply eq_univ.
    destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
    eapply LevelExprSet.eq_leibniz. red.
    intros x. rewrite -!LevelExprSet.elements_spec1 H //.
  Qed.

  Lemma univ_expr_eqb_true_iff (u v : nonEmptyLevelExprSet) :
    LevelExprSet.equal u v <-> u = v.
  Proof.
    split.
    - intros.
      apply eq_univ_equal. now apply LevelExprSet.equal_spec.
    - intros ->. now apply LevelExprSet.equal_spec.
  Qed.

  Lemma univ_expr_eqb_comm (u v : nonEmptyLevelExprSet) :
    LevelExprSet.equal u v <-> LevelExprSet.equal v u.
  Proof.
    transitivity (u = v). 2: transitivity (v = u).
    - apply univ_expr_eqb_true_iff.
    - split; apply eq_sym.
    - split; apply univ_expr_eqb_true_iff.
  Qed.


  Lemma LevelExprSet_for_all_false f u :
    LevelExprSet.for_all f u = false -> LevelExprSet.exists_ (negb ∘ f) u.
  Proof.
    intro H. rewrite LevelExprSetFact.exists_b.
    rewrite LevelExprSetFact.for_all_b in H.
    all: try now intros x y [].
    induction (LevelExprSet.elements u); cbn in *; [discriminate|].
    apply andb_false_iff in H; apply orb_true_iff; destruct H as [H|H].
    left; now rewrite H.
    right; now rewrite IHl.
  Qed.

  Lemma LevelExprSet_For_all_exprs (P : LevelExpr.t -> Prop) (u : nonEmptyLevelExprSet)
    : LevelExprSet.For_all P u
      <-> P (to_nonempty_list u).1 /\ Forall P (to_nonempty_list u).2.
  Proof.
    etransitivity.
    - eapply iff_forall; intro e. eapply imp_iff_compat_r.
      apply In_to_nonempty_list.
    - cbn; split.
      + intro H. split. apply H. now left.
        apply Forall_forall. intros x H0.  apply H; now right.
      + intros [H1 H2] e [He|He]. subst e; tas.
        eapply Forall_forall in H2; tea.
  Qed.

  Lemma add_comm {le le' e} : add le (add le' e) = add le' (add le e).
  Proof.
    apply eq_univ_equal. intros x.
    rewrite !LevelExprSet.add_spec. firstorder.
  Qed.

  #[program]
  Definition univ_union (prems prems' : nonEmptyLevelExprSet) : nonEmptyLevelExprSet :=
    {| t_set := LevelExprSet.union prems prems' |}.
  Next Obligation.
    destruct prems, prems'; cbn.
    destruct (LevelExprSet.is_empty (LevelExprSet.union _ _)) eqn:ise => //.
    eapply LevelExprSetFact.is_empty_2 in ise.
    eapply not_Empty_is_empty in t_ne0, t_ne1.
    destruct t_ne0. lesets.
  Qed.

  Lemma univ_union_spec u u' l :
    LevelExprSet.In l (univ_union u u') <->
    LevelExprSet.In l u \/ LevelExprSet.In l u'.
  Proof.
    destruct u, u'; unfold univ_union; cbn.
    apply LevelExprSet.union_spec.
  Qed.

  Lemma univ_union_add_singleton u le : univ_union u (singleton le) = add le u.
  Proof.
    apply eq_univ_equal.
    intros x. rewrite univ_union_spec LevelExprSet.singleton_spec add_spec.
    intuition auto.
  Qed.

  Lemma univ_union_comm {u u'} : univ_union u u' = univ_union u' u.
  Proof.
    apply eq_univ_equal.
    intros x. rewrite !univ_union_spec.
    intuition auto.
  Qed.

  Lemma univ_union_add_distr {le u u'} : univ_union (add le u) u' = add le (univ_union u u').
  Proof.
    apply eq_univ_equal.
    intros x. rewrite !univ_union_spec !add_spec !univ_union_spec.
    intuition auto.
  Qed.

End NonEmptySetFacts.
Export NonEmptySetFacts.

Lemma diff_eq U V : LevelSet.diff V U =_lset V <-> LevelSet.inter V U =_lset LevelSet.empty.
Proof. split. lsets. lsets. Qed.

Lemma levelset_neq U V : LevelSet.equal U V = false -> ~ LevelSet.Equal U V.
Proof. intros eq heq % LevelSet.equal_spec. congruence. Qed.

Lemma levelset_union_same U : LevelSet.union U U =_lset U.
Proof. lsets. Qed.


Lemma LevelSet_In_elements l s :
  In l (LevelSet.elements s) <-> LevelSet.In l s.
Proof.
  rewrite LevelSetFact.elements_iff.
  now rewrite InA_In_eq.
Qed.

Lemma In_elements {x} {s : LevelExprSet.t} : LevelExprSet.In x s <-> List.In x (LevelExprSet.elements s).
Proof.
  split. now move/LevelExprSetFact.elements_1/InA_In_eq.
  now move/InA_In_eq/LevelExprSetFact.elements_2.
Qed.

Lemma not_mem l s : ~~ LevelSet.mem l s <-> ~ LevelSet.In l s.
Proof.
  split. apply contraNnot. apply LevelSet.mem_spec.
  eapply contra_notN; tea. now move/LevelSet.mem_spec.
Qed.

Definition non_W_atoms W (l : LevelExprSet.t) :=
  LevelExprSet.filter (fun lk => ~~ LevelSet.mem lk.1 W) l.

Lemma non_W_atoms_spec W l : forall x, LevelExprSet.In x (non_W_atoms W l) <-> LevelExprSet.In x l /\ ~ LevelSet.In x.1 W.
Proof.
  intros x. now rewrite /non_W_atoms LevelExprSet.filter_spec -not_mem.
Qed.

Lemma non_W_atoms_subset W l : non_W_atoms W l ⊂_leset l.
Proof. intros x. now rewrite /non_W_atoms LevelExprSet.filter_spec. Qed.

Lemma levels_exprs_non_W_atoms {W prem} :
  LevelSet.Equal (levels (non_W_atoms W prem)) (LevelSet.diff (levels prem) W).
Proof.
  intros e. unfold non_W_atoms.
  rewrite levelexprset_levels_spec LevelSet.diff_spec levelexprset_levels_spec.
  firstorder eauto.
  rewrite LevelExprSet.filter_spec in H. now exists x.
  rewrite LevelExprSet.filter_spec in H. destruct H.
  rewrite LevelSetFact.not_mem_iff.
  destruct LevelSet.mem => //.
  exists x.
  rewrite LevelExprSet.filter_spec. split => //.
  rewrite LevelSetFact.not_mem_iff in H0. now rewrite H0.
Qed.

Lemma levelexprset_empty_levels x : LevelExprSet.Empty x <-> LevelSet.Empty (levels x).
Proof.
  split.
  - intros he.
    intros l hin.
    eapply levelexprset_levels_spec in hin as [k hin]. lesets.
  - intros emp l hin. eapply emp. eapply (levelexprset_levels_spec l.1). exists l.2.
    now destruct l.
Qed.

Lemma nEmpty_exists ls : ~ (LevelSet.Empty ls) -> exists l, LevelSet.In l ls.
Proof.
  intros ne.
  destruct (LevelSet.choose ls) eqn:isempty. exists e.
  now apply LevelSet.choose_spec1 in isempty.
  now apply LevelSet.choose_spec2 in isempty.
Qed.

Lemma inLevelSet (ls : LevelSet.t) l : LevelSet.In l ls \/ ~ (LevelSet.In l ls).
Proof.
  lsets.
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

Lemma strict_subset_leq_right U V W :
  strict_subset U V -> V ⊂_lset W -> strict_subset U W.
Proof.
  intros [] le. split. lsets. intros eq. rewrite -eq in le.
  apply H0. lsets.
Qed.

Lemma strict_subset_leq_left U V W :
  U ⊂_lset V -> strict_subset V W -> strict_subset U W.
Proof.
  intros le []. split. lsets. intros eq. rewrite eq in le.
  apply H0. lsets.
Qed.

Lemma strict_subset_diff_incl V W W' :
  strict_subset W' W ->
  W ⊂_lset V ->
  W' ⊂_lset V ->
  strict_subset (LevelSet.diff V W) (LevelSet.diff V W').
Proof.
  intros [] lew lew'.
  split. lsets.
  intros eq.
  apply H0. lsets.
Qed.

Lemma diff_cardinal_inter V W : #|LevelSet.diff V W| = #|V| - #|LevelSet.inter V W|.
Proof.
  pose proof (LevelSetProp.diff_inter_cardinal V W). lia.
Qed.

Lemma diff_cardinal V W : W ⊂_lset V -> #|LevelSet.diff V W| = #|V| - #|W|.
Proof.
  intros hsub.
  rewrite diff_cardinal_inter LevelSetProp.inter_sym LevelSetProp.inter_subset_equal //.
Qed.

End FromLevelSets.