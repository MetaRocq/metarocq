(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils NonEmptyLevelExprSet SemiLattice.

From MetaRocq.Common Require Universes.
From MetaRocq.Common.LoopChecking Require Import Common Interfaces.
From Equations Require Import Equations.
Set Equations Transparent.

Module InitialSemilattice (LS : LevelSets).
  Import Q.
  Existing Instance comm_monoid.
  Existing Instance add_inj_eq.
  Export LS.
  Import NES.OfQ.
  Local Open Scope quantity.
  Import NES.
  Open Scope nes_scope.

  Import Semilattice.
  Import CommutativeMonoid.
  Existing Instance OfQ.add_inj_le.

  Definition rel := t × t.

  Declare Scope rel_scope.
  Delimit Scope rel_scope with rel.
  Bind Scope rel_scope with rel.
  Open Scope rel_scope.

  Definition rels := list rel.

  Record presentation :=
    { V : LevelSet.t;
      C : list (NES.t × NES.t); }.

  Infix "∨" := NES.union (at level 30) : nes_scope.
  Open Scope nes_scope.

  Definition rel_eq (x y : t) : rel := (x, y).
  Definition rel_le (x y : t) : rel := ((x ∨ y)%nes, y).

  Infix "≡" := rel_eq (at level 70, no associativity) : rel_scope.
  Infix "≤" := rel_le (at level 50, no associativity) : rel_scope.

  Reserved Notation " p ⊢ℒ r " (at level 72, no associativity).

  Inductive entails_L (p : rels) : NES.t × NES.t -> Prop :=
    | entails_c {l r} : List.In (l, r) p -> p ⊢ℒ l ≡ r
    | entails_refl {x} : p ⊢ℒ x ≡ x
    | entails_sym {x y} : p ⊢ℒ x ≡ y -> p ⊢ℒ y ≡ x
    | entails_trans {x y z} : p ⊢ℒ x ≡ y -> p ⊢ℒ y ≡ z -> p ⊢ℒ x ≡ z
    | entails_add_congr {x y n} : p ⊢ℒ x ≡ y -> p ⊢ℒ add_prems n x ≡ add_prems n y
    | entails_add_inj {n x y} : p ⊢ℒ (add_prems n x) ≡ (add_prems n y) -> p ⊢ℒ x ≡ y
    | entails_join_congr {x y r} : p ⊢ℒ x ≡ y -> p ⊢ℒ (x ∨ r) ≡ (y ∨ r)
    | entails_assoc {x y z} : p ⊢ℒ ((x ∨ y) ∨ z) ≡ (x ∨ (y ∨ z))
    | entails_idem {x} : p ⊢ℒ (x ∨ x) ≡ x
    | entails_comm {x y} : p ⊢ℒ (x ∨ y) ≡ (y ∨ x)
    | entails_sub {x} : p ⊢ℒ (x ∨ add_prems one x) ≡ (add_prems one x)
    | entails_add_join {n x y} : p ⊢ℒ (add_prems n (x ∨ y)) ≡ (add_prems n x ∨ add_prems n y)
    where " p ⊢ℒ r " := (entails_L p r%_rel).
  Derive Signature for entails_L.

  Definition entails_L_rels p q :=
    List.Forall (entails_L p) q.

  Notation " p ⊩ℒ q " := (entails_L_rels p q) (at level 72, no associativity) : rel_scope.

  Definition equiv_L_rels p q := p ⊩ℒ q /\ q ⊩ℒ p.

  Infix "⊫ℒ" := equiv_L_rels (no associativity, at level 72) : rel_scope.

  Lemma entails_join_congr_all {p} {x x' y y'} :
    p ⊢ℒ x ≡ x' -> p ⊢ℒ y ≡ y' -> p ⊢ℒ (x ∨ y) ≡ (x' ∨ y').
  Proof.
    intros he he'.
    eapply entails_trans with (x' ∨ y).
    now apply entails_join_congr.
    rewrite (@union_comm x' y) (@union_comm x' y').
    now apply entails_join_congr.
  Qed.

  Lemma entails_join_congr_all_inv {p} {x x' y z} : p ⊢ℒ (x ∨ y) ≡ z -> p ⊢ℒ x ≡ x' -> p ⊢ℒ (x' ∨ y) ≡ z.
  Proof.
    intros he he'.
    eapply entails_trans with (x ∨ y) => //.
    apply entails_join_congr => //. now eapply entails_sym.
  Qed.

  Lemma entails_join_congr_all_inv_r {p} {x y y' z} : p ⊢ℒ (x ∨ y) ≡ z -> p ⊢ℒ y ≡ y' -> p ⊢ℒ (x ∨ y') ≡ z.
  Proof.
    intros he he'.
    eapply entails_trans with (x ∨ y) => //.
    rewrite !(@union_comm x).
    apply entails_join_congr => //. now eapply entails_sym.
  Qed.

  Section pres_Semilattice.
    Import Semilattice.
    Context (p : presentation).

    Definition relations (c : list (NES.t × NES.t)) : Prop :=
      List.Forall (fun '(l, r) => l = r) c.


    Definition univ_le (u u' : t) :=
      forall l k, LevelExprSet.In (l, k) u -> exists k', LevelExprSet.In (l, k') u /\ (OfQ.le k k').

    Definition univ_eq u u' :=
      univ_le u u' /\ univ_le u' u.

    Infix "≌" := univ_eq (at level 70, no associativity).

    Lemma univ_le_refl u u' : u = u' -> univ_le u u'.
    Proof.
      intros <- l k hin; exists k; split => //. reflexivity.
    Qed.

    Lemma univ_eq_refl u u' : u = u' -> univ_eq u u'.
    Proof.
      split; apply univ_le_refl; tea. now symmetry.
    Qed.

    Lemma univ_eq_sym u u' : univ_eq u u' -> univ_eq u' u.
    Proof.
      move=> [] le le'. split; auto.
    Qed.

    Lemma univ_eq_trans u u' u'' : univ_eq u u' -> univ_eq u' u'' ->  univ_eq u u''.
    Proof.
      move=> [] le le' [] le0 le0'. split; auto.
    Qed.

    Lemma univ_add_le_inj {n u v} : univ_le (add_prems n u) (add_prems n v) -> univ_le u v.
    Proof.
      intros hle l k hin.
      red in hle.
      specialize (hle l).
      specialize (hle (CommutativeMonoid.add n k)).
      move: hle => /fwd.
      { apply In_add_prems. exists (l, k); split => //. }
      move=> [] k' [] /In_add_prems [] [] l' k2 [] inu [=] -> -> hle'.
      exists k2. split => //.
      now apply (inj k k2).
    Qed.

    Lemma univ_add_inj {n u v} : univ_eq (add_prems n u) (add_prems n v) -> univ_eq u v.
    Proof.
      move=> [] le le'. split; eauto using univ_add_le_inj.
    Qed.

    (* To model subsumption correctly, we need a larger relation than Leibniz equality.
      In other words, (x ∨ add 1 x) <> add 1 x.  *)
    Equations? pres_semilattice : Semilattice NES.t Q.t :=
    pres_semilattice :=
      {| eq x y := relations p.(C) -> univ_eq x y;
         add := add_prems;
         join x y := x ∪ y |}.
    Proof.
      all:intros.
      - split; red; intros.
        * now apply univ_eq_refl.
        * now apply univ_eq_sym, H.
        * now eapply univ_eq_trans; eauto.
      - rewrite add_prems_add_prems. now apply univ_eq_refl.
      - specialize (H H0). destruct H as [le le'].
        split; move=> l k /In_add_prems => -[[l' k'] [hin [=]]] -> ->.
        * exists (CommutativeMonoid.add n k'). split => //. apply In_add_prems.
          exists (l', k'). split => //. reflexivity.
        * exists (CommutativeMonoid.add n k')%Q; split => //. apply In_add_prems.
          exists (l', k'); split => //. reflexivity.
      - rewrite add_prems_0. now apply univ_eq_refl.
      - apply univ_eq_refl. now rewrite union_assoc.
      - apply univ_eq_refl. now rewrite union_comm.
      - split. intros l k; rewrite !LevelExprSet.union_spec.
        intros []; exists k; split => //; try lia.
        now rewrite union_spec. reflexivity.
        now rewrite union_spec. reflexivity.
        intros l k hin. exists k. split => //. reflexivity.
      - split. intros l k; rewrite !LevelExprSet.union_spec.
        intros []; exists k; split => //; try lia;
          now rewrite ?union_spec.
        intros l k hin. exists k. split => //. reflexivity.
      - split. intros l k hin. exists k. split => //. reflexivity.
        intros l k hin. exists k. split => //; reflexivity.
      - specialize (H H0). now eapply univ_add_inj.
      - apply univ_eq_refl. now rewrite add_prems_union.
    Qed.
  End pres_Semilattice.

  Hint Constructors entails_L : entails_L.

  Lemma entails_L_le_refl p x :
    p ⊢ℒ x ≤ x.
  Proof.
    eapply entails_idem.
  Qed.

  Lemma entails_L_le_trans p x y z :
    p ⊢ℒ x ≤ y -> p ⊢ℒ y ≤ z -> p ⊢ℒ x ≤ z.
  Proof.
    intros le le'.
    eapply entails_trans. 2:exact le'.
    eapply entails_trans with (x ∨ y ∨ z).
    rewrite union_assoc. eapply entails_sym.
    eapply entails_join_congr_all => //. apply entails_refl.
    rewrite union_assoc.
    eapply entails_trans with (x ∨ ((y ∨ y) ∨ z)).
    eapply entails_join_congr_all; auto with entails_L.
    rewrite union_assoc -union_assoc.
    now eapply entails_join_congr_all.
  Qed.

  Lemma subset_union {u u' : t} :
    u ⊂_leset u' -> u ∨ u' = u'.
  Proof.
    intros hincl; apply equal_exprsets => l.
    rewrite union_spec. firstorder.
  Qed.

  Lemma incl_entails_L {cls} {u u' : t} :
    u ⊂_leset u' -> cls ⊢ℒ u ≤ u'.
  Proof.
    move=> hincl. unfold rel_le.
    rewrite subset_union //; auto with entails_L.
  Qed.

  Lemma entails_L_subset {cls} {prems prems' prems'' : t} :
    cls ⊢ℒ prems ≤ prems' ->
    prems' ⊂_leset prems'' ->
    cls ⊢ℒ prems ≤ prems''.
  Proof.
    move=> heq /(@incl_entails_L cls).
    now eapply entails_L_le_trans.
  Qed.

  Lemma entails_L_rels_subset {rels rels' r} :
    rels ⊢ℒ r ->
    incl rels rels' ->
    rels' ⊢ℒ r.
  Proof.
    induction 1; try solve [econstructor; eauto].
  Qed.

  Lemma entails_L_c {rs r} : In r rs -> rs ⊢ℒ r.
  Proof. destruct r; apply entails_c. Qed.

  Lemma entails_L_clauses_cons {rs r rs'} :
    rs ⊢ℒ r -> rs ⊩ℒ rs' -> rs ⊩ℒ r :: rs'.
  Proof. intros h h'; now constructor. Qed.

  Lemma entails_L_clauses_incl {rs rs'} :
    incl rs rs' ->
    rs' ⊩ℒ rs.
  Proof.
    induction rs in rs' |- *.
    - constructor.
    - intros i. constructor. destruct a; eapply entails_c. apply i. now constructor.
      apply IHrs. intros r hin. apply i. now right.
  Qed.

  Instance entails_L_proper : Proper (equivlistA Logic.eq ==> Logic.eq ==> iff) entails_L.
  Proof.
    intros ?? eq ?? ->.
    red in eq. rw_in (@InA_In_eq rel) eq.
    split => h; eapply entails_L_rels_subset; tea; red; firstorder.
  Qed.

  Instance In_proper {A} : Proper (Logic.eq ==> equivlistA Logic.eq ==> iff) (@In A).
  Proof.
    intros x y -> l l' eq'.
    red in eq'. setoid_rewrite InA_In_eq in eq'. firstorder.
  Qed.

  Instance Forall_proper {A} (P : A -> Prop) : Proper (equivlistA Logic.eq ==> iff) (Forall P).
  Proof.
    intros x y eq.
    rewrite !Forall_forall.
    now setoid_rewrite eq.
  Qed.

  Instance Forall_ext_proper {A} : Proper ((Logic.eq ==> iff) ==> equivlistA Logic.eq ==> iff) (@Forall A).
  Proof.
    intros x y eq ? ? ->. red in eq.
    rewrite !Forall_forall.
    split; intros hyp ? hin. now rewrite -eq; trea.
    now rewrite eq; trea.
  Qed.

  Instance entails_L_rels_proper : Proper (equivlistA Logic.eq ==> equivlistA Logic.eq ==> iff) entails_L_rels.
  Proof.
    intros l l' h ?? h'. unfold entails_L_rels. split; now rewrite h h'.
  Qed.

  Instance entails_L_equiv_proper : Proper (equivlistA Logic.eq ==> equivlistA Logic.eq ==> iff) equiv_L_rels.
  Proof.
    intros l l' h ?? h'. split; split. 1-2:rewrite -h -h'; apply H.
    rewrite h h'; apply H.
    rewrite h h'; apply H.
  Qed.


  Lemma entails_equiv_cons {rs r rs'} : rs ⊫ℒ r :: rs' <-> rs ⊩ℒ [r] /\ rs ⊩ℒ rs' /\ r :: rs' ⊩ℒ rs.
  Proof.
    split.
    - move=> [] h; depelim h. intros hrs.
      split. constructor => //. constructor => //.
    - move=> [] rsr [] rsr' a.
      split => //. constructor => //. now depelim rsr.
  Qed.

  Lemma entails_L_le_eq {cls l r} : cls ⊢ℒ l ≤ r -> cls ⊢ℒ l ∨ r ≡ r.
  Proof. trivial. Qed.

  Lemma entails_L_eq_le_1 {cls} {l r} : cls ⊢ℒ l ≡ r -> cls ⊢ℒ l ≤ r.
  Proof.
    intros eq; unfold rel_le.
    eapply (entails_join_congr_all_inv (x := r)).
    eapply entails_idem. now eapply entails_sym.
  Qed.

  Lemma entails_L_eq_le_2 {cls} {l r} : cls ⊢ℒ l ≡ r -> cls ⊢ℒ r ≤ l.
  Proof.
    intros eq; unfold rel_le.
    eapply entails_sym in eq. now eapply entails_L_eq_le_1 in eq.
  Qed.

  Lemma entails_L_eq_antisym {cls} {l r} : (cls ⊢ℒ l ≤ r /\ cls ⊢ℒ r ≤ l) <-> cls ⊢ℒ l ≡ r.
  Proof.
    split.
    - unfold rel_le. intros [le le'].
      eapply entails_trans with (l ∨ r) => //.
      apply entails_sym. now rewrite union_comm.
    - intros eq; split. now apply entails_L_eq_le_1. now apply entails_L_eq_le_2.
  Qed.

  Lemma entails_L_le_join_l {p x x' r} :
    p ⊢ℒ x ≤ x' ->
    p ⊢ℒ (x ∨ r) ≤ (x' ∨ r).
  Proof.
    intros le.
    unfold rel_le in le |- *.
    rewrite union_assoc (@union_comm r) union_assoc -union_assoc.
    eapply entails_join_congr_all => //.
    apply entails_idem.
  Qed.

  Lemma entails_L_le_congr {p x y x' y'} :
    p ⊢ℒ x ≤ x' ->
    p ⊢ℒ y ≤ y' ->
    p ⊢ℒ x ∨ y ≤ x' ∨ y'.
  Proof.
    move/(entails_L_le_join_l (r:=y)) => le le'.
    eapply entails_L_le_trans; tea.
    rewrite !(@union_comm x').
    now eapply entails_L_le_join_l.
  Qed.

  Lemma entails_L_le_idem {p x} :
    p ⊢ℒ x ∨ x ≤ x.
  Proof.
    eapply entails_L_eq_le_1, entails_idem.
  Qed.

  Lemma entails_L_le_join {p x y z} :
    p ⊢ℒ x ≤ z ->
    p ⊢ℒ y ≤ z ->
    p ⊢ℒ x ∨ y ≤ z.
  Proof.
    move=> le le'.
    have := entails_L_le_congr le le' => comb.
    eapply entails_L_le_trans; tea.
    eapply entails_L_le_idem.
  Qed.

  Lemma entails_L_le_left {p x y} :
    p ⊢ℒ x ≤ x ∨ y.
  Proof.
    rewrite /rel_le. rewrite -union_assoc.
    eapply entails_join_congr_all. apply entails_idem. apply entails_refl.
  Qed.

  Lemma entails_L_le_right {p x y} :
    p ⊢ℒ y ≤ x ∨ y.
  Proof.
    rewrite union_comm; apply entails_L_le_left.
  Qed.

  Lemma entails_L_in p l (t : t) :
    LevelExprSet.In l t ->
    p ⊢ℒ NES.singleton l ≤ t.
  Proof.
    move: t; apply: NES.elim.
    - move=>[l' k] /LevelExprSet.singleton_spec => ->.
      apply entails_L_le_refl.
    - move=> le x h hnin /NES.add_spec [].
      * intros ->. rewrite -union_add_singleton.
        apply entails_L_le_right.
      * move/h => hle.
        rewrite -union_add_singleton.
        eapply entails_L_le_trans with x => //.
        apply entails_L_le_left.
  Qed.

  Import Semilattice.

  Section interp.
    Context {S : Type} {SL : Semilattice S Q.t}.
    Context (v : Level.t -> S).

    Definition interp_rel r :=
      let '(l, r) := r in
      interp_nes v l ≡ interp_nes v r.

    Definition interp_rels c :=
      List.Forall interp_rel c.

  End interp.

  Definition valid_relation rels c :=
    (forall S (SL : Semilattice S Q.t) (v : Level.t -> S), interp_rels v rels -> interp_rel v c).

  Definition valid_relations rels rels' :=
    (forall S (SL : Semilattice S Q.t) (v : Level.t -> S), interp_rels v rels -> interp_rels v rels').

  Lemma entails_L_valid {p r} :
    p ⊢ℒ r -> valid_relation p r.
  Proof.
    rewrite /valid_relation //=.
    destruct r as [l r] => //=.
    intros h; depind h; cbn; move=> S SL v hv.
    1:{ red in hv. rewrite Forall_forall in hv; eapply hv in H. exact H. }
    all:try specialize (IHh _ _ Logic.eq_refl S SL _ hv).
    all:try specialize (IHh1 _ _ Logic.eq_refl S SL _ hv).
    all:try specialize (IHh2 _ _ Logic.eq_refl S SL _ hv).
    all:try lia; eauto.
    all:rewrite ?interp_add_prems ?interp_nes_union ?interp_add_prems; try lia.
    - eapply reflexivity.
    - now eapply symmetry, IHh.
    - eapply transitivity; [eapply IHh1|eapply IHh2] => //.
    - now apply add_congr.
    - rewrite ?interp_add_prems in IHh.
      now apply add_inj in IHh.
    - now apply join_congr.
    - apply join_assoc.
    - apply join_idem.
    - apply join_comm.
    - apply (join_sub (Semilattice := SL)).
    - now apply add_join.
  Qed.

  Equations? init_model (rs : rels) : Semilattice t Q.t :=
  init_model rs := {|
        eq x y := rs ⊢ℒ x ≡ y;
        add := add_prems;
        join := union |}.
  Proof.
    all:intros. all:try solve [econstructor; eauto].
    - split; intros.
      * intros x. eapply entails_refl.
      * intros x y. eapply entails_sym.
      * intros x y z. eapply entails_trans.
    - rewrite add_prems_add_prems. eapply entails_refl.
    - rewrite add_prems_0. apply entails_refl.
  Defined.

  #[export] Existing Instance init_model.

  Definition ids (rs : rels) : Level.t -> t := (fun l : Level.t => singleton (l, zero)).

  Lemma interp_triv rs l : eq (Semilattice := init_model rs) (interp_nes (SL := init_model rs) (ids rs) l) l.
  Proof.
    move: l; apply: elim.
    - intros [l k].
      rewrite interp_nes_singleton //= /ids //=.
      rewrite add_prems_singleton //=. rewrite /add_expr //= comm neutral.
      apply entails_refl.
    - move=> [] l k x ih hnin.
      have ha := (interp_nes_add (SL := init_model rs) (ids rs) (l, k)).
      rewrite ha ih. rewrite /interp_expr. rewrite -union_add_singleton /ids.
      rewrite [add _ _]add_prems_singleton /add_expr comm neutral.
      apply (join_comm (Semilattice := init_model rs)).
  Qed.

  Lemma interp_rels_init rs : interp_rels (SL := init_model rs) (ids rs) rs.
  Proof.
    unfold interp_rels; unfold interp_rel. cbn.
    have ir : incl rs rs.
    { now intros l. }
    move: ir.
    generalize rs at 1 8.
    induction rs0; cbn.
    - constructor.
    - destruct a. constructor.
      * change (eq (Semilattice := init_model rs) (interp_nes (SL := init_model rs) (ids rs) t0) (interp_nes (SL := init_model rs) (ids rs) t1)).
        rewrite !interp_triv.
        constructor. apply ir. now constructor.
      * apply IHrs0. intros r hin; apply ir. now right.
  Qed.

  Definition valid {S} (SL : Semilattice S Q.t) v r :=
    interp_rel (SL := SL) v r.

  Lemma syntax_model rs r : valid (init_model rs) (ids rs) r <-> rs ⊢ℒ r.
  Proof.
    rewrite /valid.
    destruct r as [l r]. unfold interp_rel.
    rewrite !interp_triv; split; apply.
  Qed.

  Lemma valid_entails_L {p r} :
    valid_relation p r -> p ⊢ℒ r.
  Proof.
    rewrite /valid_relation.
    intros ha. apply syntax_model.
    destruct r as [l r]. cbn.
    change (eq (Semilattice := init_model p) (interp_nes (SL := init_model p) (ids p) l) (interp_nes (SL := init_model p) (ids p) r)).
    specialize (ha _ (init_model p) (ids p) (interp_rels_init p)).
    now cbn in ha.
  Qed.

  (* Entailment is complete, i.e. it does represent the free semilattice with an action from Q.t *)
  Lemma completeness {p r} :
    valid_relation p r <-> p ⊢ℒ r.
  Proof.
    split.
    - apply valid_entails_L.
    - apply entails_L_valid.
  Qed.

  Lemma completeness_all {p rs} :
    valid_relations p rs <-> entails_L_rels p rs.
  Proof.
    induction rs.
    - split. constructor. intros _; red. intros; constructor.
    - split. cbn.
      * intros vr. red. constructor.
        apply completeness. intros S s v hi.
        now move: (vr _ s v hi) => h; depelim h.
        apply IHrs. intros S s v hi. specialize (vr _ s v hi). now depelim vr.
      * intros ent; depelim ent.
        apply completeness in H.
        intros s v hi. constructor.
        now apply H. now apply IHrs.
  Qed.


  Open Scope rel_scope.

  Instance interp_rels_entails_proper {S} {SL : Semilattice S Q.t} V : Proper (entails_L_rels ==> impl) (interp_rels (S:=S) V).
  Proof.
    intros rs rs' hl.
    induction rs' in rs, hl |- *.
    * constructor.
    * intros H0. depelim hl. specialize (IHrs' _ hl H0). constructor => //.
      eapply entails_L_valid in H.
      now apply (H S SL V H0).
  Qed.

  Instance interp_rels_proper {S} {SL : Semilattice S Q.t} V : Proper (equiv_L_rels ==> iff) (interp_rels (S:=S) V).
  Proof.
    intros rs rs' [hl hr].
    split; now apply interp_rels_entails_proper.
  Qed.

  Lemma entails_L_all_tip {rs r} : rs ⊩ℒ [r] <-> rs ⊢ℒ r.
  Proof.
    split; intros h.
    - now depelim h.
    - constructor => //.
  Qed.

  Lemma entails_L_all_weaken {p q w} :
    p ⊩ℒ q -> w ++ p ⊩ℒ q.
  Proof.
    induction 1; constructor.
    eapply entails_L_rels_subset; tea => //.
    intros a hin. rewrite in_app_iff. now right.
    exact IHForall.
  Qed.

  Lemma entails_L_all_refl r : r ⊩ℒ r.
  Proof. induction r.
    - constructor.
    - constructor. destruct a; eapply entails_c. now constructor.
      now eapply (entails_L_all_weaken (w := [a])).
  Qed.

  Lemma entails_L_all_app {x y x' y'} :
    x ⊩ℒ x' -> y ⊩ℒ y' -> x ++ y ⊩ℒ x' ++ y'.
  Proof.
    intros hx hy.
    rewrite equivlistA_app_comm.
    induction hy.
    - rewrite app_nil_r.
      now eapply entails_L_all_weaken.
    - rewrite equivlistA_app_cons_comm. constructor.
      rewrite -equivlistA_app_comm. eapply entails_L_rels_subset; tea.
      move=> ?; rewrite in_app_iff; now right.
      rewrite (equivlistA_app_comm l x'). exact IHhy.
  Qed.

  Lemma entails_L_all_union {x y x' y'} :
    x ⊫ℒ x' -> y ⊫ℒ y' -> x ++ y ⊫ℒ x' ++ y'.
  Proof.
    intros [hx hx'] [hy hy'].
    split; now apply entails_L_all_app.
  Qed.

Lemma interp_rels_tip {S} {SL : Semilattice.Semilattice S Q.t} (v : Level.t -> S) r : interp_rels v [r] <-> interp_rel v r.
Proof.
  split.
  - now intros h; depelim h.
  - now constructor.
Qed.

End InitialSemilattice.
