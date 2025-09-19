From Stdlib Require Import Nat ZArith Bool.

From MetaRocq.Utils Require Export MRPrelude
        MRClasses
        MRReflect
        All_Forall
        MRArith
        MRCompare
        MREquality
        MRList
        MROption
        MRProd
        MRSquash
        MRRelations
        MRString
        MRTactics.InHypUnderBindersDo
        MRTactics.SpecializeUnderBindersBy
        MRTactics.Zeta1
        MRTactics.DestructHead
        MRTactics.SpecializeAllWays
        MRTactics.SplitInContext
        MRTactics.Head
        MRTactics.SpecializeBy
        MRTactics.UniquePose
        ReflectEq
        bytestring
        Show
.

Tactic Notation "destruct" "?" :=
  let E := fresh "E" in
  match goal with
    [ |- context[match ?X with _ => _ end]] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _] => destruct X eqn:E
  end.

Tactic Notation "destruct" "?" "in" hyp(H) :=
  let e := fresh "E" in
  match type of H with context [match ?x with _ => _ end] => destruct x eqn:e
  end.

Ltac cbnr := cbn; try reflexivity.

Ltac rdestruct H :=
  match type of H with
  | _ \/ _ => destruct H as [H|H]; [rdestruct H|rdestruct H]
  | _ /\ _ => let H' := fresh H in
            destruct H as [H|H']; [rdestruct H|rdestruct H']
  | prod _ _ => let H' := fresh H in
            destruct H as [H H']; rdestruct H; rdestruct H'
  | sigT _ => let H' := fresh H in
             destruct H as [H H']; rdestruct H; rdestruct H'
  | _ => idtac
  end.

(* This is an attempt to overcome the fact that auto/eauto *)
(* do not deal with products *)
Ltac rdest :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : prod _ _ |- _ => destruct H
  | H : sigT _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- prod _ _ => split
  | |- sigT _ => eexists
  end.

Tactic Notation "toProp" ident(H) :=
  match type of H with
  | is_true (_ <? _)%nat => apply PeanoNat.Nat.ltb_lt in H
  | is_true (_ <=? _)%nat => apply PeanoNat.Nat.leb_le in H
  | is_true (_ =? _)%nat => apply PeanoNat.Nat.eqb_eq in H
  | (_ <? _)%nat  = true => apply PeanoNat.Nat.ltb_lt in H
  | (_ <=? _)%nat = true => apply PeanoNat.Nat.leb_le in H
  | (_ =? _)%nat  = true => apply PeanoNat.Nat.eqb_eq in H
  | (_ <? _)%nat  = false => apply PeanoNat.Nat.ltb_ge in H
  | (_ <=? _)%nat = false => apply PeanoNat.Nat.leb_gt in H
  | (_ =? _)%nat  = false => apply PeanoNat.Nat.eqb_neq in H

  | is_true (_ <? _)%Z => apply Z.ltb_lt in H
  | is_true (_ <=? _)%Z => apply Z.leb_le in H
  | is_true (_ =? _)%Z => apply Z.eqb_eq in H
  | (_ <? _)%Z  = true => apply Z.ltb_lt in H
  | (_ <=? _)%Z = true => apply Z.leb_le in H
  | (_ =? _)%Z  = true => apply Z.eqb_eq in H
  | (_ <? _)%Z  = false => apply Z.ltb_ge in H
  | (_ <=? _)%Z = false => apply Z.leb_gt in H
  | (_ =? _)%Z  = false => apply Z.eqb_neq in H

  | is_true (_ && _) => apply andb_true_iff in H
  | (_ && _) = true  => apply andb_true_iff in H
  | (_ && _) = false  => apply andb_false_iff in H

  | is_true (_ || _) => apply orb_true_iff in H
  | (_ || _) = true  => apply orb_true_iff in H
  | (_ || _) = false  => apply orb_false_iff in H
  end.

Tactic Notation "toProp" :=
  match goal with
  | |- is_true (_ <? _)%nat => apply PeanoNat.Nat.ltb_lt
  | |- is_true (_ <=? _)%nat => apply PeanoNat.Nat.leb_le
  | |- is_true (_ =? _)%nat => apply PeanoNat.Nat.eqb_eq
  | |- (_ <? _)%nat  = true => apply PeanoNat.Nat.ltb_lt
  | |- (_ <=? _)%nat = true => apply PeanoNat.Nat.leb_le
  | |- (_ =? _)%nat  = true => apply PeanoNat.Nat.eqb_eq
  | |- ( _ <? _)%nat  = false => apply PeanoNat.Nat.ltb_ge
  | |- (_ <=? _)%nat = false => apply PeanoNat.Nat.leb_gt
  | |- (_ =? _)%nat  = false => apply PeanoNat.Nat.eqb_neq

  | |- is_true (_ <? _)%Z => apply Z.ltb_lt
  | |- is_true (_ <=? _)%Z => apply Z.leb_le
  | |- is_true (_ =? _)%Z => apply Z.eqb_eq
  | |- (_ <? _)%Z  = true => apply Z.ltb_lt
  | |- (_ <=? _)%Z = true => apply Z.leb_le
  | |- (_ =? _)%Z  = true => apply Z.eqb_eq
  | |- (_ <? _)%Z  = false => apply Z.ltb_ge
  | |- (_ <=? _)%Z = false => apply Z.leb_gt
  | |- (_ =? _)%Z  = false => apply Z.eqb_neq

  | |- is_true (_ && _) => apply andb_true_iff; split
  | |- (_ && _) = true => apply andb_true_iff; split

  | |- is_true (_ || _) => apply orb_true_iff
  | |- (_ || _) = true => apply orb_true_iff

  | H : _ |- _ => toProp H
  end.

Tactic Notation "toProp" ident(H) "as" simple_intropattern(X) :=
   match type of H with
   | is_true (_ && _) => apply andb_true_iff in H; destruct H as X
   | (_ && _) = true  => apply andb_true_iff in H; destruct H as X
   | (_ && _) = false  => apply andb_false_iff in H; destruct H as X

   | is_true (_ || _) => apply orb_true_iff in H; destruct H as X
   | (_ || _) = true  => apply orb_true_iff in H; destruct H as X
   | (_ || _) = false  => apply orb_false_iff in H; destruct H as X
   end.

Tactic Notation "toProp" "as" simple_intropattern(X) :=
  match goal with
  | H : _ |- _ => toProp H as X
  end.

Ltac rtoProp :=
  repeat match goal with
  | H : is_true (_ && _) |- _ => apply andb_and in H; destruct H
  | |- context [is_true (_ && _)] => rewrite andb_and
  end.

Ltac bool := rtoProp; intuition eauto.

Class Fuel := fuel : nat.

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Ltac inv H := inversion_clear H.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

#[global]
Hint Resolve Peano_dec.eq_nat_dec : eq_dec.

Ltac invs H := inversion H; subst; clear H.

Ltac generalize_eq x t :=
  set (x := t) in *; cut (x = t); [|reflexivity]; clearbody x.

Lemma if_true_false (b : bool) : (if b then true else false) = b.
  destruct b; reflexivity.
Qed.

Lemma iff_is_true_eq_bool (b b' : bool) :
  (b <-> b') -> b = b'.
Proof.
  destruct b, b'; cbnr; intros [H1 H2];
    try specialize (H1 eq_refl); try specialize (H2 eq_refl);
      discriminate.
Qed.

Axiom todo : string -> forall {A}, A.
Ltac todo s := exact (todo s).

From Stdlib Require Import Extraction.
Extract Constant todo => "fun s -> failwith (Caml_bytestring.caml_string_of_bytestring s)".

From Ltac2 Require Import Init.
From Ltac2 Require Control Ltac1.

Ltac2 gtry (tac : unit -> unit) :=
  Control.plus tac (fun _ => ()).

Ltac gtry tac :=
  let f := ltac2:(tac |- gtry (fun () => Ltac1.run tac)) in
  f tac.

Tactic Notation "gtry" tactic3(tac) := gtry tac.
