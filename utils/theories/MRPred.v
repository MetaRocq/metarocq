From Stdlib Require Import List Bool Arith ssreflect ssrbool Morphisms Lia.
From MetaRocq.Utils Require Import MRPrelude MRReflect MRList MRRelations MRProd MROption.
From Equations Require Import Equations.

Definition predA {A} (p q : pred A) : pred A := (fun i => p i ==> q i).

(*
Definition orP (p q : nat -> bool) (n : nat) : bool :=
  p n || q n.

Definition conjP (p q : nat -> bool) (n : nat) : bool :=
  p n && q n.

Definition implP (p q : nat -> bool) (n : nat) : bool :=
  p n ==> q n. *)

#[global] Instance orP_Proper {A} : Proper (`≐1` ==> `≐1` ==> `≐1`) (@predU A).
Proof.
  intros f g Hfg f' g' Hfg' i; rewrite /predU /=.
  now rewrite Hfg Hfg'.
Qed.

#[global] Instance andP_Proper A : Proper (`≐1` ==> `≐1` ==> `≐1`) (@predI A).
Proof.
  intros f g Hfg f' g' Hfg' i; rewrite /predI /=.
  now rewrite Hfg Hfg'.
Qed.

#[global] Instance implP_Proper {A} : Proper (`≐1` ==> `≐1` ==> `≐1`) (@predA A).
Proof.
  intros f g Hfg f' g' Hfg' i; rewrite /predA /=.
  now rewrite Hfg Hfg'.
Qed.

Lemma orPL (p q : nat -> bool) : predA p (predU p q) ≐1 xpredT.
Proof.
  intros i. rewrite /predA /predU /=.
  rewrite (ssrbool.implybE (p i)).
  destruct (p i) => //.
Qed.

Lemma orPR (p q : nat -> bool) i : q i -> (predU p q) i.
Proof.
  rewrite /predU /= => ->; rewrite orb_true_r //.
Qed.