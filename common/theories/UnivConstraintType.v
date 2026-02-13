From Stdlib Require Import OrdersAlt Structures.OrdersEx MSetList MSetAVL MSetFacts MSetProperties MSetDecide FMapAVL.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils MRMSets MRFSets NonEmptyLevelExprSet.
From MetaRocq.Common Require Import BasicAst config.
From Stdlib Require Import ssreflect.

From Equations Require Import Equations.

Module ConstraintType.
  Inductive t_ : Set := Le | Eq.
  Derive NoConfusion EqDec for t_.

  Definition t := t_.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | LeEq : lt_ Le Eq.
  Derive Signature for lt_.
  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X.
    - intros ? ? ? X Y; invs X; invs Y; constructor.
  Qed.

  Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | Le, Le => Datatypes.Eq
    | Le, Eq => Datatypes.Lt
    | Eq, Eq => Datatypes.Eq
    | Eq, _  => Datatypes.Gt
    end.

  Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y; repeat constructor.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. decide equality.
  Qed.
End ConstraintType.
