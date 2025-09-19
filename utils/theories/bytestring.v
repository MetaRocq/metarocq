(**
 * Copyright (C) 2020 BedRock Systems, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network,
 * see repository root for details.
 *)

From Stdlib Require Strings.String ssrbool.
From Stdlib Require Import ssreflect.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From Equations Require Import Equations.
Set Primitive Projections.
Set Default Proof Using "Type".
From MetaRocq.Utils Require Import MRCompare ReflectEq.
From MetaRocq.Utils Require ByteCompare ByteCompareSpec.
(** bytes *)

Definition byte_parse (b : Byte.byte) : Byte.byte := b.
Definition byte_print (b : Byte.byte) : Byte.byte := b.

Delimit Scope byte_scope with byte.
String Notation Byte.byte byte_parse byte_print : byte_scope.
Bind Scope byte_scope with Byte.byte.

Declare Scope bs_scope.
Delimit Scope bs_scope with bs.

(** bytestrings *)
Module String.
  Inductive t : Set :=
  | EmptyString
  | String (_ : Byte.byte) (_ : t).
  Bind Scope bs_scope with t.

  Fixpoint print (b : t) : list Byte.byte :=
    match b with
    | EmptyString => nil
    | String b bs => b :: print bs
    end.

  Fixpoint parse (b : list Byte.byte) : t :=
    match b with
    | nil => EmptyString
    | List.cons b bs => String b (parse bs)
    end.

  Lemma print_parse_inv:
    forall x : t, parse (print x) = x.
  Proof.
    induction x; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Fixpoint append (x y : t) : t :=
    match x with
    | EmptyString => y
    | String x xs => String x (append xs y)
    end.

  Notation "x ++ y" := (append x y) : bs_scope.

  Fixpoint to_string (b : t) : String.string :=
    match b with
    | EmptyString => Strings.String.EmptyString
    | String x xs => Strings.String.String (Ascii.ascii_of_byte x) (to_string xs)
    end.

  Fixpoint of_string (b : String.string) : t :=
    match b with
    | Strings.String.EmptyString => EmptyString
    | Strings.String.String x xs => String (Ascii.byte_of_ascii x) (of_string xs)
    end%bs.

  Fixpoint rev (acc s : t) : t :=
    match s with
    | EmptyString => acc
    | String s ss => rev (String s acc) ss
    end.

  (** *** Substrings *)

  (** [substring n m s] returns the substring of [s] that starts
      at position [n] and of length [m];
      if this does not make sense it returns [""] *)

  Fixpoint substring (n m : nat) (s : t) : t :=
    match n, m, s with
    | O, O, _ => EmptyString
    | O, S m', EmptyString => s
    | O, S m', String c s' => String c (substring 0 m' s')
    | S n', _, EmptyString => s
    | S n', _, String c s' => substring n' m s'
    end.

  Fixpoint prefix (s1 s2 : t) {struct s1} : bool :=
    match s1 with
    | EmptyString => true
    | String x xs =>
      match s2 with
      | EmptyString => false
      | String y ys =>
        if Byte.eqb x y then prefix xs ys
        else false
      end
    end%bs.

  Fixpoint index (n : nat) (s1 s2 : t) {struct s2} : option nat :=
    match s2 with
    | EmptyString =>
        match n with
        | 0 => match s1 with
              | EmptyString => Some 0
              | String _ _ => None
              end
        | S _ => None
        end
    | String _ s2' =>
        match n with
        | 0 =>
            if prefix s1 s2
            then Some 0
            else match index 0 s1 s2' with
                | Some n0 => Some (S n0)
                | None => None
                end
        | S n' => match index n' s1 s2' with
                  | Some n0 => Some (S n0)
                  | None => None
                  end
        end
    end%bs.

  Fixpoint length (l : t) : nat :=
    match l with
    | EmptyString => 0
    | String _ l => S (length l)
    end.

  Local Fixpoint contains (start: nat) (keys: list t) (fullname: t) :bool :=
    match keys with
    | List.cons kh ktl =>
      match index start kh fullname with
      | Some n => contains (n + length kh) ktl fullname
      | None => false
      end
    | List.nil => true
    end.

  Fixpoint eqb (a b : t) : bool :=
    match a , b with
    | EmptyString , EmptyString => true
    | String x xs , String y ys =>
      if ByteCompare.eqb x y then eqb xs ys else false
    | _ , _ => false
    end.

  Fixpoint compare (xs ys : t) : comparison :=
    match xs , ys with
    | EmptyString , EmptyString => Eq
    | EmptyString , _ => Lt
    | _ , EmptyString => Gt
    | String x xs , String y ys =>
      match ByteCompare.compare x y with
      | Eq => compare xs ys
      | x => x
      end
    end.

  Lemma eqb_compare xs ys : eqb xs ys = match compare xs ys with Eq => true | _ => false end.
  Proof.
    induction xs in ys |- *; destruct ys => /= //.
    rewrite ByteCompareSpec.eqb_compare.
    destruct ByteCompare.compare => //.
  Qed.

  Fixpoint concat (sep : t) (s : list t) : t :=
    match s with
    | nil => EmptyString
    | cons s nil => s
    | cons s xs => s ++ sep ++ concat sep xs
    end.

End String.

Definition bs := String.t.
Notation string := String.t.

Fixpoint to_bytes (s : string) : list Byte.byte :=
  match s with
  | String.EmptyString => nil
  | String.String b s => b :: to_bytes s
  end.

Bind Scope bs_scope with bs.

String Notation String.t String.parse String.print : bs_scope.

Notation "x ++ y" := (String.append x y) : bs_scope.

Import String.

(** comparison *)
From Stdlib Require Import Orders OrderedType OrdersAlt.

Lemma to_N_inj : forall x y, Byte.to_N x = Byte.to_N y <-> x = y.
Proof.
  split.
  2: destruct 1; reflexivity.
  intros.
  assert (Some x = Some y).
  { do 2 rewrite <- Byte.of_to_N.
    destruct H. reflexivity. }
  injection H0. auto.
Qed.

Module OT_byte <: OrderedType.OrderedType with Definition t := Byte.byte.
  Definition t := Byte.byte.
  Definition eq := @Logic.eq t.
  Definition lt := fun l r => ByteCompare.compare l r = Lt.
  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    intros; apply eq_refl.
  Qed.
  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    apply eq_sym.
  Qed.
  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    apply eq_trans.
  Qed.
  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    exact ByteCompareSpec.lt_trans.
  Qed.
  Theorem lt_not_eq : forall x y : t, lt x y -> not (eq x y).
  Proof.
    apply ByteCompareSpec.lt_not_eq.
  Qed.
  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
    refine  (
    match ByteCompare.compare x y as X return ByteCompare.compare x y = X -> OrderedType.Compare lt eq x y  with
    | Eq => fun pf => OrderedType.EQ _
    | Lt => fun pf => OrderedType.LT pf
    | Gt => fun pf => OrderedType.GT _
    end (Logic.eq_refl)).
    now apply ByteCompareSpec.compare_eq in pf.
    rewrite ByteCompareSpec.compare_opp in pf.
    apply CompOpp_iff in pf. apply pf.
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {not (eq x y)} := Classes.eq_dec.
End OT_byte.

Global Instance byte_eqdec : Classes.EqDec Byte.byte := _.

Module StringOT <: UsualOrderedType.
  Definition t := string.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition compare := String.compare.
  Definition lt x y : Prop := compare x y = Lt.

  Theorem compare_spec : forall x y, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y; simpl.
    - constructor; reflexivity.
    - constructor. reflexivity.
    - constructor. reflexivity.
    - unfold lt; simpl. destruct (ByteCompareSpec.compare_spec b b0); simpl.
      + subst. destruct (IHx y); constructor; eauto.
        congruence. now rewrite ByteCompareSpec.compare_eq_refl.
      + constructor; auto.
      + red in H. rewrite H. constructor; auto.
  Qed.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    reflexivity.
  Qed.
  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    eapply eq_sym.
  Qed.
  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    eapply eq_trans.
  Qed.
  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    induction x; destruct y; simpl; try congruence.
    - destruct z; congruence.
    - destruct (ByteCompareSpec.compare_spec b b0); subst.
      + destruct z; auto.
        destruct (ByteCompare.compare b0 b); auto.
        eauto.
      + destruct z; auto.
        red in H.
        destruct (ByteCompareSpec.compare_spec b0 b1).
        * subst. intros _. now rewrite H.
        * generalize (OT_byte.lt_trans _ _ _ H H0). unfold OT_byte.lt.
          intro X; rewrite X. auto.
        * congruence.
      + congruence.
  Qed.
  Theorem lt_not_eq : forall x y : t, lt x y -> not (eq x y).
  Proof.
    unfold lt, eq.
    intros. intro. subst.
    induction y; simpl in *; try congruence.
    rewrite ByteCompareSpec.compare_eq_refl in H. auto.
  Qed.

  #[global] Program Instance reflect_eq_string : ReflectEq t := {
    eqb := eqb
  }.
  Next Obligation.
    rename x into s, y into s'.
    destruct (eqb s s') eqn:e; constructor.
    - rewrite String.eqb_compare in e. fold (compare s s') in e.
      now destruct (compare_spec s s').
    - rewrite String.eqb_compare in e.
      fold (compare s s') in e.
      destruct (compare_spec s s') => //.
      now apply lt_not_eq. now apply not_eq_sym, lt_not_eq.
  Qed.

  Definition eq_dec : forall x y : t, {eq x y} + {not (eq x y)} := Classes.eq_dec.

  Lemma compare_eq : forall x y : string, compare x y = Eq <-> eq x y.
  Proof.
    intros.
    destruct (compare_spec x y); intuition auto; try congruence.
    - apply lt_not_eq in H; contradiction.
    - apply lt_not_eq in H. symmetry in H0. contradiction.
  Qed.

  Lemma compare_refl x : compare x x = Eq.
  Proof.
    now apply compare_eq.
  Qed.

  Lemma compare_lt : forall x y : string, compare x y = Lt <-> compare y x = Gt.
  Proof.
    intros x y.
    destruct (compare_spec x y).
    all:split; try congruence; subst.
    - intros hc.
      fold (compare y y) in hc. now rewrite compare_refl in hc.
    - intros _.
      destruct (compare_spec y x); subst.
      * eapply lt_not_eq in H. elim H; reflexivity.
      * eapply lt_trans in H; try eassumption.
        eapply lt_not_eq in H. elim H; reflexivity.
      * reflexivity.
  Qed.

  #[local] Instance lt_transitive : Transitive lt.
  Proof.
    red. eapply lt_trans.
  Qed.

  Lemma compare_sym (x y : string) : compare x y = CompOpp (compare y x).
  Proof.
    destruct (compare_spec x y).
    - subst.
      rewrite (proj2 (compare_eq _ _)); auto. reflexivity.
    - rewrite (proj1 (compare_lt _ _)); auto.
    - rewrite (proj2 (compare_lt _ _)); auto.
      red in H.
      now apply compare_lt.
  Qed.

  Lemma compare_trans (x y z : string) c : compare x y = c -> compare y z = c -> compare x z = c.
  Proof.
    destruct (compare_spec x y); subst; intros <-;
    destruct (compare_spec y z); subst; try congruence.
    eapply transitivity in H0. 2:eassumption. intros; apply H0.
    eapply transitivity in H. 2:eassumption.
    now apply compare_lt in H.
  Qed.

  Definition lt_irreflexive : Irreflexive lt.
  Proof.
    intro x. red; unfold lt.
    now rewrite compare_refl.
  Qed.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - apply lt_irreflexive.
    - apply lt_transitive.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold eq. intros x y e z t e'. subst; reflexivity.
  Qed.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End StringOT.

Module StringOTOrig := OrdersAlt.Backport_OT StringOT.

Notation string_compare := StringOT.compare.
Notation string_compare_eq := StringOT.compare_eq.
Notation CompareSpec_string := StringOT.compare_spec.

(** To perform efficient pretty printing, one needs to use a tree structure
  to avoid quadratic overhead of appending strings. *)
Module Tree.
  Local Open Scope bs_scope.
  Inductive t :=
  | string : String.t -> t
  | append : t -> t -> t.

  Coercion string : String.t >-> t.

  Infix "++" := append.

  Fixpoint to_rev_list_aux t acc :=
    match t with
    | string s => cons s acc
    | append s s' => to_rev_list_aux s' (to_rev_list_aux s acc)
    end.

  Fixpoint to_string_acc acc l :=
    match l with
    | nil => acc
    | cons s xs => to_string_acc (String.append s acc) xs
    end.

  Definition to_string t :=
    let l := to_rev_list_aux t nil in
    to_string_acc "" l.

  (* Definition test := "a" ++ "b" ++ "v" ++ "c".
  Eval compute in to_string test. *)

  (* Fixpoint to_string_acc t acc :=
    match t with
    | string s => String.append s acc
    | append s s' => to_string_acc s (to_string_acc s' acc)
    end.

  Definition to_string t := to_string_acc t "". *)

  Definition string_of_list_aux {A} (f : A -> t) (sep : t) (l : list A) :=
    let fix aux l :=
        match l return t with
        | nil => ""
        | cons a nil => f a
        | cons a l => f a ++ sep ++ aux l
      end
    in aux l.

  Definition string_of_list {A} (f : A -> t) l :=
    "[" ++ string_of_list_aux f "," l ++ "]".

  Definition print_list {A} (f : A -> t) (sep : t) (l : list A) : t :=
    string_of_list_aux f sep l.

  Fixpoint concat (sep : t) (s : list t) : t :=
    match s with
    | nil => EmptyString
    | cons s nil => s
    | cons s xs => s ++ sep ++ concat sep xs
    end.

  Definition parens (top : bool) (s : t) :=
    if top then s else "(" ++ s ++ ")".

End Tree.

(* Tests *)
(*

Local Open Scope bs_scope.
Import String.
Definition x := Eval compute in Tree.to_string (Tree.concat (Tree.string "") (List.repeat (Tree.string "frliqhgrnvcrlkejflqrjfljkl") 10000)).
Definition y := Eval compute in String.concat "" (List.repeat "frliqhgrnvcrlkejflqrjfljkl" 10000) ++ "'".

Time Eval compute in String.compare x y. (* 0.02s *)

Import String.
Fixpoint String.compare' (xs ys : bs) : comparison :=
  match xs , ys with
  | EmptyString, EmptyString => Eq
  | EmptyString , _ => Lt
  | _ , EmptyString => Gt
  | String x xs , String y ys =>
    match compare x y with
    | Eq => String.compare' xs ys
    | x => x
    end
  end.

Time Eval vm_compute in String.compare x y. (* 0.14s *)
Time Eval vm_compute in String.compare' x y. (* 0.03s~0.04s, i.e. more than 3 times faster *)
*)
