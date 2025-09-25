(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun ZArith.
From Stdlib Require Import Program RelationClasses Morphisms SetoidList.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import MRPrelude MRClasses MRList.

Set Equations Transparent.

Module Semilattice.
  Declare Scope sl_scope.
  Open Scope sl_scope.
  Delimit Scope sl_scope with sl.
  Import CommutativeMonoid.
  Local Open Scope comm_monoid.

  Reserved Notation "x ≡ y" (at level 70).
  Class Semilattice (carrier : Type) (incr : Type) `{CM : IsCommMonoid incr} :=
    { eq : carrier -> carrier -> Prop where "x ≡ y" := (eq x y) : sl_scope;
      eq_equiv :: Equivalence eq;
      add : incr -> carrier -> carrier;
      join : carrier -> carrier -> carrier;
      add_distr n m x : add n (add m x) ≡ add (CommutativeMonoid.add n m) x;
      add_congr n x y : x ≡ y -> add n x ≡ add n y;
      add_neutral x : add 0 x ≡ x;
      join_assoc x y z : join (join x y) z ≡ join x (join y z);
      join_comm x y : join x y ≡ join y x;
      join_congr x x' y : x ≡ x' -> join x y ≡ join x' y;
      join_idem x : join x x ≡ x;
      join_sub x : join x (add 1 x) ≡ add 1 x;
      add_inj : forall n x y, add n x ≡ add n y -> x ≡ y;
      add_join : forall n x y, add n (join x y) ≡ join (add n x) (add n y);
    }.

  Notation "x ≡ y" := (eq x y) (at level 70) : sl_scope.

  Definition le {A incr} `{SL : Semilattice A incr} (x y : A) := join x y ≡ y.

  Infix "≤" := le (at level 50) : sl_scope.
  Infix "∨" := join (at level 30) : sl_scope.

  Definition lt {A} `{SL : Semilattice A} (x y : A) := add 1 x ≤ y.
  Infix "<" := lt (at level 70) : sl_scope.

  Class JoinDec (carrier : Type) `{SL : Semilattice carrier} :=
    { join_dec x y : (join x y ≡ x) \/ (join y x ≡ y) }.

  Local Open Scope sl_scope.
  Section Derived.
    Context {A : Type} {incr : Type} {CM : IsCommMonoid incr} {SL : Semilattice A incr}.

    Lemma join_congr_r x y y' : y ≡ y' -> join x y ≡ join x y'.
    Proof.
      intros he; etransitivity. apply join_comm.
      etransitivity. 2:apply join_comm. now apply join_congr.
    Qed.

    #[export] Instance proper_join : Proper (eq ==> eq ==> eq) join.
    Proof. intros x y ? x0 y0 ?. transitivity (join y x0).
      now apply join_congr. now apply join_congr_r.
    Qed.

    #[export] Instance proper_add : Proper (Logic.eq ==> eq ==> eq) add.
    Proof. intros x y ? x0 y0 ?. subst y. now apply add_congr. Qed.

    Lemma le_refl x : x ≤ x.
    Proof. apply join_idem. Qed.
    Lemma le_trans x y z : x ≤ y -> y ≤ z -> x ≤ z.
    Proof.
      unfold le; intros le le'. now rewrite -le' -join_assoc le.
    Qed.
    #[export] Instance le_preorder : PreOrder le.
    Proof.
      split.
      - intros ?; apply le_refl.
      - intros ? ? ?. apply le_trans.
    Qed.

    Lemma eq_antisym {x y} : x ≡ y <-> x ≤ y /\ y ≤ x.
    Proof.
      split.
      - intros he. split.
        red. rewrite -he. apply join_idem.
        red. rewrite -he. apply join_idem.
      - intros [le le'].
        red in le, le'. rewrite -le. rewrite -{1}le'.
        apply join_comm.
    Qed.

    #[export] Instance proper_le : Proper (eq ==> eq ==> iff) le.
    Proof. intros x y ? x0 y0 ?.
      apply eq_antisym in H0 as [].
      apply eq_antisym in H as [].
      split.
      - intros leq. transitivity x => //. transitivity x0 => //.
      - intros le. transitivity y => //. transitivity y0 => //.
    Qed.

    #[export] Instance po : PartialOrder eq le.
    Proof.
      split.
      - intros eq; split. now rewrite eq. red.
        now rewrite eq.
      - intros []. red in H0. apply eq_antisym. split => //.
    Qed.

    Lemma join_le_left {s t} : s ≤ s ∨ t.
    Proof.
      red. now rewrite -join_assoc join_idem.
    Qed.

    Lemma join_le_left_trans {s t u} : s ≤ t -> s ≤ t ∨ u.
    Proof. transitivity t => //. apply join_le_left. Qed.

    Lemma join_le_right {s t} : t ≤ s ∨ t.
    Proof.
      rewrite join_comm; apply join_le_left.
    Qed.

    Lemma join_le_right_trans {s t u} : s ≤ u -> s ≤ t ∨ u.
    Proof. transitivity u => //. apply join_le_right. Qed.

    Lemma join_le_left_eq {s t u} :
      s ∨ t ≤ u <-> s ≤ u /\ t ≤ u.
    Proof.
      split.
      - intros le; split; transitivity (s ∨ t) => //. apply join_le_left.
        apply join_le_right.
      - intros [le le']. red in le, le'. red.
        now rewrite join_assoc le' le.
    Qed.

    Lemma join_le_right_impl {s t u} :
      s ≤ t \/ s ≤ u -> s ≤ t ∨ u.
    Proof.
      intros [le|le]; red in le; red.
      now rewrite -join_assoc le.
      now rewrite (join_comm t) -join_assoc le.
    Qed.

    Lemma join_dec_spec {JD : @JoinDec A incr CM SL} (x y : A) :
      (x ≤ y /\ join x y ≡ y) \/ (y ≤ x /\ join x y ≡ x).
    Proof.
      destruct (join_dec x y).
      - right. split => //.
        red. now rewrite join_comm H.
      - left. split => //. red.
        rewrite join_comm H. reflexivity.
        rewrite join_comm H. reflexivity.
    Qed.

    Lemma le_add {n} {x y : A} : x ≤ y <-> add n x ≤ add n y.
    Proof.
      unfold le.
      split.
      - now rewrite -add_join => ->.
      - rewrite -add_join => h.
        now apply add_inj in h.
    Qed.

  End Derived.

  Section FoldSemilattice.
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
        move: (IHl l') => /fwd.
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
        * move: (IHl x) => /fwd; auto.
          now apply join_le_right_trans.
        * apply join_le_left.
        * move: (IHl x) => /fwd; auto.
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
        move: (IHl a') => /fwd.
        { cbn; intros x []. subst. eapply ih. now left.
          apply ih. auto. }
        move: (ih a) => /fwd. { now right; left. }
        intros ? ?; eapply join_le_left_eq; now split.
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

  End FoldSemilattice.

End Semilattice.
