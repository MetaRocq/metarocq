(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrfun ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From Equations Require Import Equations.
Set Equations Transparent.

Ltac rw l := rewrite_strat (topdown l).
Ltac rw_in l H := rewrite_strat (topdown l) in H.

Notation fwd := (ltac:(move=> /(_ _)/Wrap[])).

(* TODO move *)
Arguments exist {A P}.
Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

#[program] Global Instance reflect_eq_Z : ReflectEq Z := {
    eqb := Z.eqb
  }.
Next Obligation.
  destruct (Z.eqb_spec x y); constructor => //.
Qed.


Definition option_map2 {A} (f : A -> A -> A) (o o' : option A) : option A :=
  match o, o' with
  | Some x, Some y => Some (f x y)
  | None, Some _
  | Some _, None
  | None, None => None
  end.

Derive Signature for InA.

Lemma eqlistA_eq {A} (l l' : list A) : eqlistA Logic.eq l l' -> l = l'.
Proof.
  induction 1.
  - reflexivity.
  - now f_equal.
Qed.

#[export] Instance fold_left_ext {A B} : Proper (`=2` ==> eq ==> eq ==> eq) (@fold_left A B).
Proof.
  intros f g hfg ? ? -> ? ? ->.
  induction y in y0 |- *; cbn; auto. now rewrite (hfg y0 a).
Qed.

(* None is smaller than anything *)
Inductive opt_le {A} (le : relation A) : relation (option A) :=
| opt_le_some x y : le x y -> opt_le le (Some x) (Some y)
| opt_le_none_some x : opt_le le None x.
Derive Signature for opt_le.

Instance opt_le_refl {A} (le : relation A) : Reflexive le -> Reflexive (opt_le le).
Proof.
  intros hre x; induction x; constructor; reflexivity.
Qed.

Instance opt_le_trans {A} (le : relation A) : Transitive le -> Transitive (opt_le le).
Proof.
  intros hre x; induction x; destruct y as [y|]; intros z H H'; depelim H; depelim H'; constructor.
  now transitivity y.
Qed.


Class Commutative {A} (f : A -> A -> A) := comm : forall x y, f x y = f y x.
Instance option_map_2_comm {A} f : @Commutative A f -> @Commutative (option A) (option_map2 f).
Proof.
  intros com [x|] [y|] => //=. now rewrite comm.
Qed.

Instance Zmin_comm : Commutative Z.min := Z.min_comm.
Instance Zmax_comm : Commutative Z.max := Z.max_comm.

Instance nat_min_comm : Commutative Nat.min := Nat.min_comm.
Instance nat_max_comm : Commutative Nat.max := Nat.max_comm.

Class Associative {A} (f : A -> A -> A) := assoc : forall x y z, f x (f y z) = f (f x y) z.
Instance option_map_2_assoc {A} f : @Associative A f -> @Associative (option A) (option_map2 f).
Proof.
  intros assoc [x|] [y|] [z|]; cbn => //. now rewrite assoc.
Qed.

Instance nat_min_assoc : Associative Nat.min := Nat.min_assoc.
Instance nat_max_assoc : Associative Nat.max := Nat.max_assoc.


Instance Zmin_assoc : Associative Z.min := Z.min_assoc.
Instance Zmax_assoc : Associative Z.max := Z.max_assoc.

Lemma fold_left_comm {A B} (f : B -> A -> B) (l : list A) (x : A) (acc : B) :
  (forall x y z, f (f z x) y = f (f z y) x) ->
  fold_left f l (f acc x) = f (fold_left f l acc) x.
Proof.
  intros.
  induction l in acc, x |- *; cbn. auto.
  rewrite -IHl. f_equal. now rewrite H.
Qed.

Lemma fold_left_min_opt_comm {A} (f : A -> A -> A) l x acc :
  Associative f -> Commutative f ->
  fold_left (option_map2 f) l (option_map2 f acc x) = option_map2 f (fold_left (option_map2 f) l acc) x.
Proof.
  intros ass c. rewrite fold_left_comm => //.
  intros. rewrite -(assoc (f := option_map2 f)).
  rewrite -(assoc (f := option_map2 f) z y x0).
  f_equal. apply comm.
Qed.

Lemma fold_left_le {A B} {le} (f g : A -> B -> A) l :
  (forall acc acc'  x, In x l -> le acc acc' -> le (f acc x) (g acc' x)) ->
  forall acc acc', le acc acc' ->
  le (fold_left f l acc) (fold_left g l acc').
Proof.
  intros hfg.
  induction l => //. cbn. intros.
  apply IHl. intros. apply hfg => //. now right. apply hfg => //. now left.
Qed.

Local Open Scope nat_scope.
Lemma fold_left_ne_lt {A} (f g : nat -> A -> nat) l acc :
  (forall x y z, f (f z x) y = f (f z y) x) ->
  (forall x y z, g (g z x) y = g (g z y) x) ->
  l <> [] ->
  (forall acc acc' x, In x l -> (acc <= acc') -> (f acc x <= g acc' x)) ->
  (forall acc acc' x, In x l -> (acc < acc') -> (f acc x < g acc' x)) ->
  (exists x, In x l /\ forall acc acc', (acc <= acc') -> (f acc x < g acc' x)) ->
  fold_left f l acc < fold_left g l acc.
Proof.
  intros hf hg.
  generalize (Nat.le_refl acc).
  generalize acc at 2 4.
  induction l in acc |- * => //.
  intros.
  destruct l; cbn.
  { destruct H3 as [x []]. cbn in H3. destruct H3; subst => //.
    now eapply (H4 acc acc0). }
  cbn in IHl.
  rewrite hf hg.
  rewrite fold_left_comm //. rewrite (fold_left_comm g) //.
  destruct H3 as [min [hmin hfg]].
  destruct hmin as [<-|hel].
  - apply hfg. apply fold_left_le => //. intros; eapply H1 => //. now right; right.
    apply H1 => //. now right; left.
  - apply H2. now left. eapply IHl => //.
    * intros acc1 acc' x hin. apply (H1 acc1 acc' x). now right.
    * intros acc1 acc' x hin. apply (H2 acc1 acc' x). now right.
    * exists min. split => //.
Qed.

Notation min_opt := (option_map2 Z.min).

Infix "≤" := (opt_le Z.le) (at level 50).

Lemma opt_lt_le_trans x y z :
  opt_le Z.lt x y ->
  opt_le Z.le y z ->
  opt_le Z.lt x z.
Proof.
  intros [] H'; depelim H'; constructor. lia.
Qed.

Lemma opt_le_lt_trans {x y z} : opt_le Z.le x y -> opt_le Z.lt y z -> opt_le Z.lt x z.
Proof.
  destruct 1; intros H'; depelim H'; constructor. lia.
Qed.


Definition max_opt_of {A} (max : A -> A -> A) (x : option A) (y : option A) : option A :=
  match x, y with
  | Some x, Some y => Some (max x y)
  | Some x, None => Some x
  | _, _ => y
  end.

Lemma max_opt_of_spec {x y k'} : max_opt_of Z.max x y = k' ->
  (x ≤ y /\ k' = y) \/ (y ≤ x /\ k' = x).
Proof.
  destruct x, y; cbn; firstorder subst.
  - destruct (Z.max_spec z z0) as [[]|[]];
    [left|right]; split; try constructor; lia_f_equal.
  - right. split; constructor.
  - left. split; constructor.
  - left; split; constructor.
Qed.

Lemma max_opt_of_l {A} {f : A -> A -> A} l : max_opt_of f l None = l.
Proof.
  destruct l => //.
Qed.

Lemma max_opt_of_r {A} {f : A -> A -> A} l : max_opt_of f None l = l.
Proof.
  destruct l => //.
Qed.

Lemma max_opt_of_le_l z z' : z ≤ max_opt_of Z.max z z'.
Proof.
  destruct z, z'; cbn; constructor; lia.
Qed.

Lemma max_opt_of_le_r z z' : z' ≤ max_opt_of Z.max z z'.
Proof.
  destruct z, z'; cbn; constructor; lia.
Qed.

Lemma pair_inj {A B} (x x' : A) (y y' : B) P :
  (x = x' -> y = y' -> P) ->
  ((x, y) = (x', y') -> P).
Proof.
  now intros h [=].
Qed.

Lemma Zmin_opt_left x y : min_opt x y ≤ x.
Proof.
  destruct x as [x|], y as [y|]; constructor. lia.
Qed.

Lemma Zmin_opt_right x y : min_opt x y ≤ y.
Proof.
  destruct x as [x|], y as [y|]; constructor. lia.
Qed.

Lemma min_opt_spec x y z : min_opt x y = z -> (z = y \/ z = x).
Proof.
  destruct x as [x|], y as [y|], z as [z|]; cbn; intuition auto.
  - noconf H. pose proof (Zmin_irreducible x y). destruct H; intuition (f_equal; auto).
  - noconf H.
Qed.

Lemma fold_comm_assoc_nat x y z : option_map2 Nat.max x (option_map2 Nat.max y z) =
  option_map2 Nat.max y (option_map2 Nat.max x z).
Proof.
  now rewrite (assoc (f := option_map2 Nat.max)) (comm (f := option_map2 Nat.max) x y) -assoc.
Qed.

Lemma fold_comm_assoc x y z : option_map2 Z.max x (option_map2 Z.max y z) =
  option_map2 Z.max y (option_map2 Z.max x z).
Proof.
  now rewrite (assoc (f := option_map2 Z.max)) (comm (f := option_map2 Z.max) x y) -assoc.
Qed.

Local Open Scope Z_scope.
Lemma fold_right_max_in {a l} n : In a l -> a <= fold_right Z.max n l.
Proof.
  induction l.
  - now cbn.
  - intros [eq|inl]. subst a0. cbn. lia.
    cbn. specialize (IHl inl). lia.
Qed.

Lemma fold_right_max_acc {n l} : n <= fold_right Z.max n l.
Proof.
  induction l.
  - now cbn.
  - cbn. lia.
Qed.

Lemma fold_right_impl n l l' :
  (forall x, In x l -> In x l') -> fold_right Z.max n l <= fold_right Z.max n l'.
Proof.
  induction l in l' |- *.
  - cbn. destruct l'; cbn. lia.
    intros. have := @fold_right_max_acc n l'. lia.
  - cbn; intros h.
    have inal' := (h a (or_introl eq_refl)).
    have := fold_right_max_in n inal'.
    specialize (IHl l').
    forward IHl.
    intros. apply h. now right.
    lia.
Qed.

Lemma fold_right_max_spec n l :
  let fn := fold_right Z.max in
  (forall x, In x (n :: l) -> x <= fn n l) /\
  (exists x, In x (n :: l) /\ fn n l = x).
Proof.
  induction l; cbn.
  - split. intros x [] => //. now subst.
    exists n. firstorder.
  - cbn in IHl. destruct IHl as [h h'].
    split.
    intros x [|[]]; subst.
    * specialize (h x). forward h by auto. lia.
    * lia.
    * specialize (h x). forward h by auto. lia.
    * destruct h' as [x []]. exists (Z.max a x). rewrite -{4}H0. split => //.
      destruct H; subst.
      destruct (Z.max_spec a x) as [[]|[]]; firstorder; subst.
      destruct (Z.max_spec a (fold_right Z.max n l)) as [[]|[]]; firstorder; subst. rewrite H1.
      auto.
Qed.

Lemma fold_right_equivlist_all n n' l l' :
  equivlistA eq (n :: l) (n' :: l') -> fold_right Z.max n l = fold_right Z.max n' l'.
Proof.
  intros eq.
  have [hla [maxl [inmaxl eqmaxl]]] := fold_right_max_spec n l.
  have [hra [maxr [inmaxr eqmaxr]]] := fold_right_max_spec n' l'.
  rewrite eqmaxl eqmaxr.
  red in eq; setoid_rewrite InA_In_eq in eq.
  apply (eq _) in inmaxl. apply hra in inmaxl.
  apply eq in inmaxr. apply hla in inmaxr. lia.
Qed.

Lemma fold_right_comm acc l : l <> [] -> fold_right Z.max acc l = Z.max acc (fold_right Z.max (List.hd acc l) (List.tl l)).
Proof.
  induction l in acc |- *.
  - intros; congruence.
  - intros _. cbn. destruct l; cbn. lia.
    cbn in IHl. rewrite (IHl acc). congruence.
    rewrite (IHl a). congruence. lia.
Qed.

Lemma fold_left_map {A B C} (f : B -> A -> A) (g : C -> B) l acc :
  fold_left (fun acc l => f (g l) acc) l acc =
  fold_left (fun acc l => f l acc) (List.map g l) acc.
Proof.
  induction l in acc |- *; cbn; auto.
Qed.

Lemma option_map2_comm x y : option_map2 Z.min x y = option_map2 Z.min y x.
Proof.
  destruct x, y; cbn; lia_f_equal.
Qed.

Lemma option_map2_assoc x y z :
  option_map2 Z.min x (option_map2 Z.min y z) =
  option_map2 Z.min (option_map2 Z.min x y) z.
Proof.
  destruct x, y, z; cbn; lia_f_equal.
Qed.

Local Notation fn := (fold_left (option_map2 Z.min)).

Lemma fold_left_impl n l :
  (forall x, In x (n :: l) -> fn l n ≤ x) /\
  (exists x, In x (n :: l) /\ fn l n = x).
Proof.
  induction l in n |- *.
  - cbn. split; intros.
    destruct H => //. subst. reflexivity.
    exists n. split => //. now left.
  - cbn. split; intros.
    { destruct (IHl n) as [hle [min [hin heq]]].
    rewrite fold_left_comm.
    { now intros; rewrite -option_map2_assoc (option_map2_comm x0 y) option_map2_assoc. }
    repeat destruct H; subst.
    * specialize (hle n). forward hle. now left.
      transitivity (fn l n); auto. eapply Zmin_opt_left.
    * eapply Zmin_opt_right.
    * transitivity (fn l n); auto. apply Zmin_opt_left.
      apply hle. now right. }
    * specialize (IHl (option_map2 Z.min n a)).
      destruct IHl as [hle [min [hin heq]]]. subst min. eexists. split; trea.
      destruct hin.
      rewrite -H.
      destruct n, a; cbn; firstorder.
      destruct (Z.min_spec z z0) as [[? heq]|[? heq]].
      rewrite -{1}heq. now left. right; left. f_equal. lia.
      now right.
Qed.

Lemma fold_left_impl_eq n n' l l' :
  (forall x, In x (n :: l) <-> In x (n' :: l' )) ->
  fn l n = fn l' n'.
Proof.
  intros heq.
  destruct (fold_left_impl n l) as [hle [minl [hin heq']]].
  destruct (fold_left_impl n' l') as [hle' [minl' [hin' heq'']]].
  rewrite heq' heq''.
  specialize (hle minl'). forward hle. now apply heq.
  specialize (hle' minl). forward hle'. now apply heq.
  rewrite heq'' in hle'. rewrite heq' in hle. depelim hle'. depelim hle. f_equal; lia.
  now depelim hle.
Qed.

Lemma fold_left_comm_f {A} (f : A -> A -> A) n l :
  (forall x y, f x y = f y x) ->
  fold_left f l n = fold_left (flip f) l n.
Proof.
  induction l in n |- *; cbn; auto.
  intros hf. rewrite IHl //.
  unfold flip. now rewrite hf.
Qed.

Lemma nleq_optZ k k' : ~ k ≤ Some k' -> exists z, k = Some z /\ k' < z.
Proof.
  destruct k.
  - exists z. split => //. eapply Znot_ge_lt => hl; apply H. constructor. lia.
  - elim. constructor.
Qed.

Notation max_opt := (option_map2 Z.max).

Lemma max_opt_spec x y z : max_opt x y = Some z -> exists x' y', x = Some x' /\ y = Some y' /\ z = Z.max x' y'.
Proof.
  destruct x as [x|], y as [y|]; cbn; intuition eauto; try noconf H.
  exists x, y. auto.
Qed.

#[export] Instance And3P_proper : Proper (iff ==> iff ==> iff ==> iff) ssrbool.and3.
Proof.
  repeat intro. split; intros []; split; intuition auto.
Qed.

#[export] Instance And4P_proper : Proper (iff ==> iff ==> iff ==> iff ==> iff) ssrbool.and4.
Proof.
  repeat intro. split; intros []; split; intuition auto.
Qed.

#[export] Instance And5P_proper : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff) ssrbool.and5.
Proof.
  repeat intro. split; intros []; split; intuition auto.
Qed.

#[export, refine] Instance ge_refl : Reflexive Z.ge := _.
Proof. red. lia. Qed.

#[export, refine] Instance ge_trans : Transitive Z.ge := _.
Proof. red. lia. Qed.

