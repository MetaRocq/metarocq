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

  Lemma entails_L_eq_antisym {cls} {l r} : cls ⊢ℒ r ≤ l -> cls ⊢ℒ l ≤ r -> cls ⊢ℒ l ≡ r.
  Proof.
    unfold rel_le. intros le le'.
    eapply entails_trans with (l ∨ r) => //.
    apply entails_sym. now rewrite union_comm.
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

    Definition interp_expr '(l, k) := (add k (v l))%Z.

    Definition interp_prems prems :=
      let '(hd, tl) := to_nonempty_list prems in
      fold_right (fun lk acc => join (interp_expr lk) acc) (interp_expr hd) tl.

    Definition interp_rel r :=
      let '(l, r) := r in
      interp_prems l ≡ interp_prems r.

    Definition interp_rels c :=
      List.Forall interp_rel c.

    Declare Scope sl_scope.
    Infix "≤" := le : sl_scope.
    Infix "≡" := eq : sl_scope.
    Local Open Scope sl_scope.

  End interp.

Section ForSemilattice.
  Import Semilattice.
  Import CommutativeMonoid.
  Context {A : Type} {V : Type} {CM : IsCommMonoid V} {SL : Semilattice A V}.
  Open Scope sl_scope.

  Lemma fold_right_max_in {a : A} {l : list A} n : In a l -> a ≤ (fold_right join n l).
  Proof.
    induction l.
    - now cbn.
    - intros [eq|inl]. subst a0. cbn. apply join_le_left.
      cbn. specialize (IHl inl). etransitivity; tea. apply join_le_right.
  Qed.

  Lemma fold_right_max_acc {n l} : n ≤ fold_right join n l.
  Proof.
    induction l.
    - now cbn.
    - cbn. etransitivity; tea. eapply join_le_right.
  Qed.

  Lemma fold_right_impl n l l' :
    (forall x, In x l -> In x l') -> fold_right join n l ≤ fold_right join n l'.
  Proof.
    induction l in l' |- *.
    - cbn. destruct l'; cbn. reflexivity.
      intros. have := @fold_right_max_acc n l'.
      etransitivity; tea; eapply join_le_right.
    - cbn; intros h.
      have inal' := (h a (or_introl Logic.eq_refl)).
      have := fold_right_max_in n inal'.
      specialize (IHl l').
      forward IHl.
      intros. apply h. now right.
      intros hle; rewrite join_le_left_eq. now split.
  Qed.

  Lemma fold_right_max_spec n l :
    let fn := fold_right join in
    (forall x, In x (n :: l) -> x ≤ fn n l).
  Proof.
    induction l; cbn.
    - intros x [] => //. now subst.
      (* exists n. firstorder. reflexivity. *)
    - cbn in IHl.
      intros x [|[]]; subst.
      * specialize (IHl x). forward IHl by auto.
        now apply join_le_right_trans.
      * apply join_le_left.
      * specialize (IHl x). forward IHl by auto.
        now apply join_le_right_trans.
  Qed.

  Lemma fold_right_equivlist_all_le n n' l l' :
    equivlistA Logic.eq (n :: l) (n' :: l') -> fold_right join n l ≤ fold_right join n' l'.
  Proof.
    intros eq.
    have hla := fold_right_max_spec n l.
    have hra := fold_right_max_spec n' l'.
    red in eq.
    setoid_rewrite InA_In_eq in eq.
    cbn in hra. setoid_rewrite <- eq in hra. clear -hra.
    move: hra; generalize (fold_right join n' l').
    clear.
    induction l.
    - cbn. intros a heq. apply heq. now left.
    - cbn. intros a' ih.
      specialize (IHl a'). forward IHl.
      { cbn; intros x []. subst. eapply ih. now left.
        apply ih. auto. }
      specialize (ih a). forward ih. { now right; left. }
      eapply join_le_left_eq; now split.
  Qed.

  Lemma fold_right_equivlist_all n n' l l' :
    equivlistA Logic.eq (n :: l) (n' :: l') -> fold_right join n l ≡ fold_right join n' l'.
  Proof.
    intros eq.
    apply eq_antisym; split; eapply fold_right_equivlist_all_le; auto.
    now symmetry.
  Qed.

  Lemma fold_right_comm acc l : l <> [] -> fold_right join acc l ≡ join acc (fold_right join (List.hd acc l) (List.tl l)).
  Proof.
    induction l in acc |- *.
    - intros; congruence.
    - intros _. cbn. destruct l; cbn. apply join_comm.
      cbn in IHl. rewrite (IHl acc). congruence.
      rewrite (IHl a). congruence.
      now rewrite -!join_assoc (join_comm a).
  Qed.

End ForSemilattice.

  Section OnInterp.
    Context {S : Type} {SL : Semilattice S Q.t}.

    (* There exists a valuation making all clauses true in the natural numbers *)
    Definition satisfiable (cls : rels) :=
      exists V, interp_rels V cls.

    (* Any valuation making all clauses valid in the given semilattice also satisfies the clause cl *)
    Definition entails_sem (cls : rels) (r : rel) :=
      forall V, interp_rels V cls -> interp_rel V r.

    Lemma interp_add_expr V n e :
      interp_expr V (add_expr n e) ≡ add n (interp_expr V e).
    Proof.
      destruct e as [l k]; cbn. now rewrite add_distr.
    Qed.

    Lemma interp_prems_singleton V e :
      interp_prems V (NES.singleton e) = interp_expr V e.
    Proof.
      rewrite /interp_prems.
      now rewrite singleton_to_nonempty_list /=.
    Qed.

    Lemma interp_prems_ge v (prems : t) :
      forall prem, LevelExprSet.In prem prems ->
      interp_expr v prem ≤ interp_prems v prems.
    Proof.
      intros.
      unfold interp_prems.
      have he := to_nonempty_list_spec prems.
      destruct to_nonempty_list.
      pose proof to_nonempty_list_spec'.
      rewrite In_elements in H. rewrite -he in H. clear H0 he. clear -H.
      destruct H. subst p.
      - induction l. cbn. auto.
        cbn. red. eapply join_idem. cbn.
        etransitivity; tea.
        apply join_le_right.
      - induction l in H |- *.
        now cbn in H.
        cbn in H. destruct H; subst; cbn.
        * cbn. apply join_le_left.
        * specialize (IHl H). etransitivity; tea. apply join_le_right.
    Qed.

    Lemma interp_prems_elements V u :
      interp_prems V u = fold_right join (interp_expr V (to_nonempty_list u).1) (List.map (interp_expr V) (to_nonempty_list u).2).
    Proof.
      rewrite /interp_prems.
      have he := to_nonempty_list_spec u.
      destruct to_nonempty_list.
      now rewrite fold_right_map.
    Qed.

    Lemma fold_right_interp {V : Level.t -> S} {x l x' l'} :
      equivlistA Logic.eq (x :: l) (x' :: l') ->
      fold_right join (interp_expr V x) (List.map (interp_expr V) l) ≡ fold_right join (interp_expr V x') (List.map (interp_expr V) l').
    Proof.
      intros eq. apply fold_right_equivlist_all.
      intros a. rewrite !InA_In_eq.
      rewrite !(in_map_iff (interp_expr V) (_ :: _)).
      setoid_rewrite <-InA_In_eq.
      split.
      - move=> [b [<- ]].
        eexists; split; trea. now apply eq in b0.
      - move=> [b [<- ]].
        eexists; split; trea. now apply eq in b0.
    Qed.

    Lemma equivlistA_add le u : let l := to_nonempty_list (NES.add le u) in
      equivlistA Logic.eq (l.1 :: l.2) (le :: LevelExprSet.elements u).
    Proof.
      have he := to_nonempty_list_spec (NES.add le u).
      destruct to_nonempty_list. cbn.
      intros x. rewrite he.
      rewrite !LevelExprSet.elements_spec1.
      split.
      - move/LevelExprSet.add_spec => [->|hin].
        now constructor. constructor 2. now apply LevelExprSet.elements_spec1.
      - intros h; depelim h; subst. now apply LevelExprSet.add_spec; left.
        apply LevelExprSet.add_spec. now apply LevelExprSet.elements_spec1 in h.
    Qed.

    Lemma interp_prems_add V le (u : t) :
      interp_prems V (NES.add le u) ≡ join (interp_expr V le) (interp_prems V u).
    Proof.
      rewrite 2!interp_prems_elements.
      erewrite fold_right_interp. 2:apply equivlistA_add.
      rewrite fold_right_comm.
      { apply map_nil, elements_not_empty. }
      apply join_congr_r. eapply fold_right_equivlist_all.
      have he := to_nonempty_list_spec u.
      destruct to_nonempty_list. rewrite -he //=.
    Qed.

    Lemma interp_prems_elim (P : t -> S -> Prop) V :
      Proper (Logic.eq ==> eq ==> iff) P ->
      (forall le, P (singleton le) (interp_expr V le)) ->
      (forall le u k, P u k -> ~ LevelExprSet.In le u -> P (NES.add le u) (join (interp_expr V le) k)) ->
      forall u, P u (interp_prems V u).
    Proof.
      intros prop hs hadd.
      eapply elim.
      - intros le. rewrite interp_prems_singleton. apply hs.
      - intros le prems ih hnin.
        rewrite interp_prems_add. now apply hadd.
    Qed.

    Lemma interp_add_prems V n e : interp_prems V (add_prems n e) ≡ add n (interp_prems V e).
    Proof.
      revert e.
      refine (interp_prems_elim (fun u z => interp_prems V (add_prems n u) ≡ add n z) _ _ _ _).
      - intros p p' eq a a' eq'.
        subst p'. now rewrite eq'.
      - intros le.
        rewrite add_prems_singleton interp_prems_singleton //=.
        destruct le; cbn. now rewrite add_distr.
      - intros le u k heq hnin.
        rewrite add_prems_add.
        rewrite interp_prems_add heq interp_add_expr.
        now rewrite add_join.
    Qed.

    Lemma interp_prems_in {V le} {u : t} :
      LevelExprSet.In le u -> interp_expr V le ≤ interp_prems V u.
    Proof.
      revert u.
      refine (interp_prems_elim (fun u z => LevelExprSet.In le u -> interp_expr V le ≤ z) V _ _ _).
      - intros ? ? <- x y eq. now rewrite eq.
      - intros le' u'.
        apply LevelExprSet.singleton_spec in u'. red in u'; subst.
        reflexivity.
      - move=> le' u z hz hnin /LevelExprSet.add_spec [->|hin].
        * apply join_le_left.
        * specialize (hz hin).
          now apply join_le_right_trans.
    Qed.

    Lemma interp_prems_union {v : Level.t -> S} {x y : t} :
      interp_prems v (x ∪ y) ≡
      join (interp_prems v x) (interp_prems v y).
    Proof.
      move: x; apply NES.elim.
      - intros []. rewrite union_comm union_add_singleton.
        now rewrite interp_prems_add interp_prems_singleton.
      - intros le' x ih hnin.
        rewrite union_add_distr !interp_prems_add ih. cbn.
        now rewrite join_assoc.
    Qed.

    Lemma clauses_sem_subset {u u' : t} : u ⊂_leset u' ->
      forall V, interp_prems V u ≤ interp_prems V u'.
    Proof.
      intros hsub V.
      revert u u' hsub.
      refine (interp_prems_elim (fun u z => forall u' : t, u ⊂_leset u' ->
        z ≤ interp_prems V u') V _ _ _).
      - intros ?? <- ?? eq.
        now setoid_rewrite eq.
      - intros le u' hsing.
        specialize (hsing le). forward hsing by now apply LevelExprSet.singleton_spec.
        now apply interp_prems_in.
      - intros le u k ih hin u' sub.
        have hle := sub le.
        specialize (ih u').
        forward ih. intros x hin'. apply sub. now apply LevelExprSet.add_spec; right.
        forward hle by now apply LevelExprSet.add_spec; left.
        have hi := interp_prems_in (V := V) hle.
        apply join_le_left_eq. split => //.
    Qed.

  End OnInterp.

  Structure semilattice :=
    { carrier :> Type;
      sl : Semilattice carrier Q.t }.

  (* Definition incr_semilattice : semilattice_on comm_monoid := {| carrier := Q.t; sl := _ |}. *)

  Instance semlattice_Semilattice (s : semilattice) : Semilattice (carrier s) Q.t := sl s.

  Definition valid_relation rels c :=
    (forall (s : semilattice) (v : Level.t -> s), interp_rels v rels -> interp_rel v c).

  Lemma entails_L_valid {p r} :
    p ⊢ℒ r -> valid_relation p r.
  Proof.
    rewrite /valid_relation //=.
    destruct r as [l r] => //=.
    intros h; depind h; cbn; move=> s v hv.
    1:{ red in hv. rewrite Forall_forall in hv; eapply hv in H. exact H. }
    all:try specialize (IHh _ _ Logic.eq_refl s _ hv).
    all:try specialize (IHh1 _ _ Logic.eq_refl s _ hv).
    all:try specialize (IHh2 _ _ Logic.eq_refl s _ hv).
    all:try lia; eauto.
    all:rewrite ?interp_add_prems ?interp_prems_union ?interp_add_prems; try lia.
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
    - apply (join_sub (Semilattice := sl s)).
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

  Definition initial_semilattice rs : semilattice :=
    {| carrier := NES.t; sl := init_model rs |}.

  Definition ids (rs : rels) : Level.t -> t := (fun l : Level.t => singleton (l, zero)).

  Lemma interp_triv rs l : eq (Semilattice := init_model rs) (interp_prems (SL := init_model rs) (ids rs) l) l.
  Proof.
    move: l; apply: elim.
    - intros [l k].
      rewrite interp_prems_singleton //= /ids //=.
      rewrite add_prems_singleton //=. rewrite comm neutral.
      apply entails_refl.
    - move=> [] l k x ih hnin.
      have ha := (interp_prems_add (SL := init_model rs) (ids rs) (l, k)).
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
      * change (eq (Semilattice := init_model rs) (interp_prems (SL := init_model rs) (ids rs) t0) (interp_prems (SL := init_model rs) (ids rs) t1)).
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
    change (eq (Semilattice := init_model p) (interp_prems (SL := init_model p) (ids p) l) (interp_prems (SL := init_model p) (ids p) r)).
    specialize (ha (initial_semilattice p) (ids p) (interp_rels_init p)).
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

End InitialSemilattice.
