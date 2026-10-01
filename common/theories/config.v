(* Distributed under the terms of the MIT license. *)
From Stdlib Require CRelationClasses.
From Stdlib Require Import Bool RelationClasses Btauto.
From Stdlib.ssr Require Import ssreflect ssrbool.

Class checker_flags := {
  (* check_guard : bool ; *)

  (* Checking universe constraints iff [true] *)
  check_univs : bool ;

  (* Prop <= Type iff [true] *)
  prop_sub_type : bool ;

  (* If sort of indices are taken in account for the sort of inductive types *)
  indices_matter : bool ;

  (* Lets in constructor types are allowed iff [true] *)
  lets_in_constructor_types : bool ;

  (* Use the *unverified* eta rule in the checker *)
  with_eta : bool;
}.

(** Should correspond to Rocq *)
Local Instance default_checker_flags : checker_flags := {|
  check_univs := true ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true;
  with_eta := false;
|}.

Local Instance type_in_type : checker_flags := {|
  check_univs := false ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true;
  with_eta := false;
|}.

Local Instance extraction_checker_flags : checker_flags := {|
  check_univs := true ;
  prop_sub_type := false;
  indices_matter := false;
  lets_in_constructor_types := false;
  with_eta := false;
|}.

(** [cf1 -> cf2] means that typing under [cf1] implies typing under [cf2] *)
#[local] Definition impl (cf1 cf2 : checker_flags) : bool
  := implb cf2.(@check_univs) cf1.(@check_univs)
     && implb cf1.(@prop_sub_type) cf2.(@prop_sub_type)
     && implb cf2.(@indices_matter) cf1.(@indices_matter)
     && implb cf1.(@lets_in_constructor_types) cf2.(@lets_in_constructor_types).

#[local] Definition impl_reflb cf : impl cf cf = true.
Proof. rewrite /impl !implb_same ?orb_true_r //. Qed.
#[local] Definition impl_refl : Reflexive impl := impl_reflb.
#[local] Definition impl_crefl : CRelationClasses.Reflexive impl := impl_reflb.
#[local] Definition impl_trans : Transitive impl.
Proof.
  rewrite /impl => x y z; destruct x, y, z; cbn.
  rewrite !implb_orb.
  repeat match goal with
         | [ |- is_true (andb _ _) -> _ ] => move => /andP[]
         | [ |- is_true (orb _ _) -> _ ] => move => /orP[]
         | [ |- is_true (negb _) -> _ ] => let H := fresh in intro H; apply negbTE in H; subst => //=
         | [ |- is_true true -> _ ] => move => _
         | [ |- is_true false -> _ ] => move => //=
         | [ |- is_true ?x -> _ ] => is_var x; let H := fresh in intro H; cbv [is_true] in H; subst
         end.
  all: rewrite ?orb_true_l ?orb_true_r ?andb_false_l ?andb_false_r //.
Qed.
#[local] Definition impl_ctrans : CRelationClasses.Transitive impl := impl_trans.
#[global] Existing Instances
  impl_refl impl_crefl
  impl_trans impl_ctrans
| 100.

Definition laxest_checker_flags : checker_flags := {|
  check_univs := false ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true;
  with_eta := true;
|}.

Definition strictest_checker_flags : checker_flags := {|
  check_univs := true ;
  prop_sub_type := false;
  indices_matter := true;
  lets_in_constructor_types := false;
  with_eta := false;
|}.

Lemma laxest_checker_flags_laxest : forall cf, impl cf laxest_checker_flags.
Proof.
  intro cf; cbv; destruct cf.
  repeat match goal with
         | [ |- context[match ?x with _ => _ end] ] => case_eq x
         end; try reflexivity; congruence.
Qed.

Lemma strictest_checker_flags_strictest : forall cf, impl strictest_checker_flags cf.
Proof.
  intro cf; cbv; destruct cf.
  repeat match goal with
         | [ |- context[match ?x with _ => _ end] ] => case_eq x
         end; try reflexivity; congruence.
Qed.

(** can check everything that either one can check *)
Definition union_checker_flags (cf1 cf2 : checker_flags) : checker_flags
  := {| check_univs := andb cf2.(@check_univs) cf1.(@check_univs)
     ; prop_sub_type := orb cf1.(@prop_sub_type) cf2.(@prop_sub_type)
     ; indices_matter := andb cf2.(@indices_matter) cf1.(@indices_matter)
     ; lets_in_constructor_types := orb cf1.(@lets_in_constructor_types) cf2.(@lets_in_constructor_types)
     ; with_eta := orb cf1.(@with_eta) cf2.(@with_eta)
      |}.

(** can check everything that both can check *)
Definition inter_checker_flags (cf1 cf2 : checker_flags) : checker_flags
  := {| check_univs := orb cf2.(@check_univs) cf1.(@check_univs)
     ; prop_sub_type := andb cf1.(@prop_sub_type) cf2.(@prop_sub_type)
     ; indices_matter := orb cf2.(@indices_matter) cf1.(@indices_matter)
     ; lets_in_constructor_types := andb cf1.(@lets_in_constructor_types) cf2.(@lets_in_constructor_types)
     ; with_eta := andb cf1.(@with_eta) cf2.(@with_eta)
      |}.

Lemma union_checker_flags_spec cf1 cf2 (cf' := union_checker_flags cf1 cf2)
  : impl cf1 cf' /\ impl cf2 cf' /\ (forall cf'', impl cf1 cf'' -> impl cf2 cf'' -> impl cf' cf'').
Proof.
  destruct cf1, cf2; subst cf'.
  cbv.
  repeat split.
  3: intro cf''; destruct cf''.
  all: repeat first [ match goal with
                      | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
                      end
                    | reflexivity
                    | congruence ].
Qed.

Lemma inter_checker_flags_spec cf1 cf2 (cf' := inter_checker_flags cf1 cf2)
  : impl cf' cf1 /\ impl cf' cf2 /\ (forall cf'', impl cf'' cf1 -> impl cf'' cf2 -> impl cf'' cf').
Proof.
  destruct cf1, cf2; subst cf'.
  cbv.
  repeat split.
  3: intro cf''; destruct cf''.
  all: repeat first [ match goal with
                      | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
                      end
                    | reflexivity
                    | congruence ].
Qed.
