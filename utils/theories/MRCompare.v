From Stdlib Require Import ssreflect Extraction OrderedType Orders.
From Equations Require Import Equations.

Lemma CompareSpec_Proper : Proper (iff ==> iff ==> iff ==> Logic.eq ==> iff) CompareSpec.
Proof.
  intros A A' HA B B' HB C C' HC c c' [].
  destruct c; split; inversion 1; constructor; intuition.
Qed.

Definition compare_cont (c : comparison) (d : comparison) : comparison :=
  match c with
  | Datatypes.Lt => Datatypes.Lt
  | Datatypes.Eq => d
  | Datatypes.Gt => Datatypes.Gt
  end.
Extraction Inline compare_cont.

Local Notation " c ?? y " := (compare_cont c y) (at level 100).

Lemma compare_cont_CompOpp p q : CompOpp (compare_cont p q) = compare_cont (CompOpp p) (CompOpp q).
Proof.
  destruct p, q; cbn => //.
Qed.

Definition comparison_trans p q :=
  match p, q with
  | Datatypes.Eq, c => Some c
  | c, Datatypes.Eq => Some c
  | Datatypes.Lt, Datatypes.Gt => None
  | Datatypes.Gt, Datatypes.Lt => None
  | c, _ => Some c
  end.

Lemma compare_cont_trans {A} (cmp : A -> A -> comparison) :
  (forall c x y z, cmp x y = c -> cmp y z = c -> cmp x z = c) ->
  (forall x y, cmp x y = Datatypes.Eq -> x = y) ->
  forall c x y z q q' q'',
  (forall c, q = c -> q' = c -> q'' = c) ->
  compare_cont (cmp x y) q = c -> compare_cont (cmp y z) q' = c -> compare_cont (cmp x z) q'' = c.
Proof.
  intros Hc He c x y z q q' q'' Hqs.
  destruct (cmp x y) eqn:e.
  apply He in e. subst y.
  cbn. intros ->.
  destruct (cmp x z) eqn:e'; cbn.
  apply He in e'. subst z. now apply Hqs.
  all:auto.

  cbn. intros <-.
  destruct (cmp y z) eqn:e'; cbn.
  apply He in e'. subst z. rewrite e /= //. intros _.
  rewrite (Hc _ _ _ _ e e') /= //.
  discriminate. cbn. intros <-.
  destruct (cmp y z) eqn:e'; cbn => //.
  eapply He in e'; subst. intros ->. rewrite e //.
  intros _. rewrite (Hc _ _ _ _ e e') //.
Qed.

(** Facts about booleans, characters and strings *)

Module BoolOT <: UsualOrderedType.
  Definition t := bool.

  Definition compare (x y : bool) : comparison :=
    if x then if y then Eq else Gt else if y then Lt else Eq.

  Definition lt (x y : bool) :=
    if x then False else y = true.

  Definition compare_spec (x y : bool) : CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y.
    - constructor 1. reflexivity.
    - constructor 3. reflexivity.
    - constructor 2. reflexivity.
    - constructor 1. reflexivity.
  Defined.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    decide equality.
  Defined.

  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; cbn; unfold lt, complement; congruence.
    - intros x y z.
      destruct x, y, z; cbn; try congruence; auto.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y e z t e'. unfold eq in *; subst. reflexivity.
  Qed.

  (* Bonus *)
  Definition eqb (l1 l2 : t) : bool
    := match compare l1 l2 with Eq => true | _ => false end.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End BoolOT.

Abbreviation bool_compare := BoolOT.compare.

Local Ltac trd := cbn in *; try reflexivity; try discriminate.

Module ListOrderedType (A : UsualOrderedType) <: UsualOrderedType.
  Definition t := list A.t.
  Import List. Import ListNotations.

  Fixpoint compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | [], [] => Eq
    | hd :: tl, hd' :: tl' => compare_cont (A.compare hd hd') (compare tl tl')
    | [], _ :: _ => Lt
    | _, [] => Gt
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | lt_nil_cons hd tl : lt_ [] (hd :: tl)
  | lt_cons_cons_hd hd tl hd' tl' : A.lt hd hd' -> lt_ (hd :: tl) (hd' :: tl')
  | lt_cons_cons_tl hd tl tl' : lt_ tl tl' -> lt_ (hd :: tl) (hd :: tl').
  Derive Signature for lt_.
  Local Hint Constructors lt_ : core.

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros x X. depind X.
      * now eapply irreflexivity in H.
      * now apply IHX.
    - intros x y z.
      induction 1 in z |- *.
      * intros H; depelim H; constructor.
      * intros H'; depelim H'; constructor; auto.
        now transitivity hd'.
      * intros H'; depelim H'.
        + constructor; auto.
        + constructor 3. now apply IHlt_.
  Qed.

  Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y e z t e'. unfold eq in *; subst. reflexivity.
  Qed.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y; repeat constructor.
    cbn.
    destruct (A.compare_spec a t0); subst.
    - cbn. eapply CompareSpec_Proper.
      5: eapply IHx. 4: reflexivity.
      intuition auto; congruence.
      * intuition auto.
        { depelim H; auto. now apply irreflexivity in H. }
        { now constructor 3. }
      * intuition auto.
        { depelim H; auto. now apply irreflexivity in H. }
        { constructor 3; auto. }
    - cbn. repeat constructor; auto.
    - cbn. repeat constructor; auto.
  Qed.

  Lemma compare_eq x y : compare x y = Eq -> x = y.
  Proof.
    destruct (compare_spec x y); auto; congruence.
  Qed.

  Lemma compare_refl x : compare x x = Eq.
  Proof. destruct (compare_spec x x); auto; now apply irreflexivity in H. Qed.

  Lemma compare_sym x y : compare x y = CompOpp (compare y x).
  Proof.
    destruct (compare_spec x y);
    destruct (compare_spec y x); simpl; auto; subst; try congruence.
    all:try now apply irreflexivity in H.
    all:try now apply irreflexivity in H0.
    pose proof (transitivity H H0). now apply irreflexivity in H1.
    pose proof (transitivity H H0). now apply irreflexivity in H1.
  Qed.

  Lemma compare_lt_lt x y : compare x y = Lt <-> lt x y.
  Proof.
    split.
    - destruct (compare_spec x y); subst; try congruence.
    - intros hlt.
      destruct (compare_spec x y); subst; auto.
      * now apply irreflexivity in hlt.
      * eapply transitivity in H; eauto. now apply irreflexivity in H.
  Qed.

  Lemma compare_trans x y z c : compare x y = c -> compare y z = c -> compare x z = c.
  Proof.
    destruct (compare_spec x y); subst; intros <-;
    destruct (compare_spec y z); subst; try congruence.
    eapply transitivity in H0. 2:eassumption. intros _; now apply compare_lt_lt.
    eapply transitivity in H. 2:eassumption.
    apply compare_lt_lt in H. rewrite compare_sym H //.
  Qed.

  (* Bonus *)
  Definition eqb (l1 l2 : t) : bool
    := match compare l1 l2 with Eq => true | _ => false end.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Program Definition eqb_dec (x y : t) : { x = y } + { x <> y } :=
    match eqb x y with
    | true => left _
    | false => right _
    end.
  Next Obligation.
    unfold eqb in Heq_anonymous.
    destruct (compare x y) eqn:hc; try congruence.
    now eapply compare_eq in hc.
  Qed.
  Next Obligation.
    unfold eqb in Heq_anonymous.
    rewrite compare_refl in Heq_anonymous. now discriminate.
  Qed.

  Global Instance eq_dec : EqDec t := { eq_dec := eqb_dec }.

End ListOrderedType.

