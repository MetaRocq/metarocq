(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import
  PCUICAst PCUICAstUtils PCUICTyping PCUICSafeLemmata PCUICValidity
  PCUICReduction PCUICEquality PCUICConfluence PCUICUnivSubstitutionConv
  PCUICUnivSubstitutionTyp.

From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect.

(** We assume normalization of the reduction.
    We state is as well-foundedness of the reduction.
*)

Record normalizing_flags {cf : checker_flags} : Prop :=
  { nor_check_univs :> check_univs }.

Existing Class normalizing_flags.

#[local] Instance default_normalizing :
  @normalizing_flags default_checker_flags.
Proof.
  now constructor.
Qed.

#[local] Instance extraction_normalizing :
  @normalizing_flags extraction_checker_flags.
Proof.
  now constructor.
Qed.

#[local] Instance weakening_config_normalizing {cf1 cf2} :
  config.impl cf2 cf1 -> @normalizing_flags cf1 -> @normalizing_flags cf2.
Proof.
  intros Hcf no.
  destruct cf1, cf2, no; constructor; cbv -[andb] in *.
  subst; simpl in *.
  revert Hcf; cbv [andb].
  repeat match goal with |- context[if ?b then _ else _] => is_var b; destruct b end.
  all: trivial.
Qed.

Class NormalizationIn {cf : checker_flags} {no : normalizing_flags} (Σ : global_env_ext) :=
  normalization_in :
    forall Γ t,
      welltyped Σ Γ t ->
      Acc (cored Σ Γ) t.
Class Normalization {cf : checker_flags} {no : normalizing_flags} :=
  normalization : forall Σ, wf_ext Σ -> NormalizationIn Σ.
#[export] Hint Mode NormalizationIn - - + : typeclass_instances.
#[export] Typeclasses Opaque Normalization.

(** Since we are working with name annotations, reduction is sensitive to names.
    In this section we provide cored' which corresponds to reduction up to
    α-renaming, as well as the necessary lemmata to show it is well-founded and
    can be used instead of the usual reduction as a measure.
*)

Section Alpha.

  Context {cf : checker_flags} {no : normalizing_flags}.
  Context (Σ : global_env_ext) {normalization : NormalizationIn Σ}.

  Abbreviation eqt u v := (∥ eq u v ∥). (* Can be made into alpha-equality, but not using PCUICEquality.eq_term_upto_univ_napp *)

  Definition cored' Γ u v :=
    exists u' v', cored Σ Γ u' v' /\ eqt u u' /\ eqt v v'.

  Lemma cored_alt :
    forall Γ u v,
      cored Σ Γ u v <~> ∥ Relation.trans_clos (red1 Σ Γ) v u ∥.
  Proof using Type.
    intros Γ u v.
    split.
    - intro h. induction h.
      + constructor. constructor. assumption.
      + destruct IHh as [ih]. constructor.
        eapply Relation.t_trans.
        * eassumption.
        * constructor. assumption.
    - intros [h]. induction h.
      + constructor. assumption.
      + eapply cored_trans'. all: eassumption.
  Qed.

  Local Instance substu_pres_eq {T} `{UnivSubst T} : SubstUnivPreserving eq (@eq T).
  Proof using Type.
    move => s u u' /cmp_universe_instance_eq -> //.
  Qed.

  Lemma cored'_postpone :
    forall Γ u v,
      cored' Γ u v ->
      exists u', cored Σ Γ u' v /\ eqt u u'.
  Proof using Type.
    intros Γ u v [u' [v' [r [[hu] [hv]]]]].
    apply cored_alt in r.
    destruct r as [r].
    induction r in u, v, hu, hv.
    - (* eapply red1_eq_alpha in r as [u' [r e]]. *)
      subst x. rename y into u'.
      exists u'. split.
      * constructor. assumption.
      * constructor. etransitivity. 1: eauto.
        now symmetry.
    - specialize (IHr1 y v).
      destruct IHr1 as [y' [h1 [e1]]]; auto.
      specialize (IHr2 u y').
      destruct IHr2 as [u' [h2 ?]]; auto.
      exists u'. split.
      + eapply cored_trans'. all: eauto.
      + assumption.
  Qed.

  Corollary cored_upto :
    forall Γ u v v',
      cored Σ Γ u v ->
      eqt v v' ->
      exists u', cored Σ Γ u' v' /\ eqt u u'.
  Proof using Type.
    intros Γ u v v' h e.
    eapply cored'_postpone.
    exists u, v. intuition eauto.
    - constructor. reflexivity.
    - destruct e; constructor; now symmetry.
  Qed.

  Lemma Acc_impl :
    forall A (R R' : A -> A -> Prop),
      (forall x y, R x y -> R' x y) ->
      forall x, Acc R' x -> Acc R x.
  Proof using Type.
    intros A R R' h x hx.
    induction hx as [x h1 h2].
    constructor. intros y hy.
    eapply h2. eapply h. assumption.
  Qed.

  Lemma Acc_cored_cored' :
    forall Γ u,
      Acc (cored Σ Γ) u ->
      forall u', eqt u u' -> Acc (cored' Γ) u'.
  Proof using Type.
    intros Γ u h. induction h as [u h ih].
    intros u' e. constructor. intros v [v' [u'' [r [[e1] [e2]]]]].
    assert (ee : eqt u'' u).
    { destruct e. constructor. symmetry; etransitivity; tea. }
    eapply cored_upto in r as hh. 2: exact ee.
    destruct hh as [v'' [r' [e']]].
    eapply ih.
    - eassumption.
    - destruct ee. constructor. symmetry; etransitivity; eassumption.
  Qed.

  Lemma normalization_upto :
    forall Γ u,
      welltyped Σ Γ u ->
      Acc (cored' Γ) u.
  Proof using normalization.
    intros Γ u h.
    apply normalization in h.
    eapply Acc_cored_cored'.
    - eassumption.
    - constructor; reflexivity.
  Qed.

  Lemma cored_eq_context_upto_names :
    forall Γ Δ u v,
      eq_context_upto_names Γ Δ ->
      cored Σ Γ u v ->
      cored Σ Δ u v.
  Proof using Type.
    intros Γ Δ u v e h.
    apply cored_alt in h as [h].
    induction h in Δ, e |- *.
    - constructor. eapply red1_eq_context_upto_names. all: eauto.
    - eapply cored_trans'.
      + eapply IHh2. assumption.
      + eapply IHh1. assumption.
  Qed.

  Lemma cored_cored' :
    forall Γ u v,
      cored Σ Γ u v ->
      cored' Γ u v.
  Proof using Type.
    intros Γ u v h.
    exists u, v. intuition eauto.
    - constructor. reflexivity.
    - constructor. reflexivity.
  Qed.

End Alpha.
