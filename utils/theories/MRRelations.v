(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From Equations.Type Require Import Relation Relation_Properties.
From Stdlib Require Import CRelationClasses.
Require RelationClasses.

#[global] Hint Mode Reflexive ! ! : typeclass_instances.

Infix "<~>" := iffT (at level 90).

Definition iffT_l {P Q} : P <~> Q -> P -> Q.
Proof.
  apply: fst.
Qed.
Coercion iffT_l : CRelationClasses.iffT >-> Funclass.

(** This allow to use implicit projections for move/ on "<~>" lemmas *)
Hint View for move/ fst|2.
Hint View for move/ snd|2.

Notation "'precompose'" := (fun R f x y => R (f x) (f y)) (only parsing).

Definition on_rel {A B} (R : A -> A -> Prop) (f : B -> A) : B -> B -> Prop :=
  fun x y => R (f x) (f y).

Definition on_Trel {A B} (R : A -> A -> Type) (f : B -> A) : B -> B -> Type :=
  fun x y => R (f x) (f y).

Abbreviation Trel_conj R S :=
  (fun x y => R x y * S x y)%type.

Abbreviation Trel_sig R S :=
  (fun x y => { r : R x y & S x y r })%type.

Abbreviation on_Trel_eq R f g :=
  (fun x y => (R (f x) (f y) * (g x = g y)))%type.

#[global]
Instance on_rel_refl {A B} (P : B -> B -> Prop) (f : A -> B) :
  RelationClasses.Reflexive P ->
  RelationClasses.Reflexive (on_rel P f).
Proof.
  intros refl u.
  apply refl.
Qed.

#[global]
Instance on_rel_sym {A B} (P : B -> B -> Prop) (f : A -> B) :
  RelationClasses.Symmetric P ->
  RelationClasses.Symmetric (on_rel P f).
Proof.
  intros sym u u'.
  apply sym.
Qed.

#[global]
Instance on_rel_trans {A B} (P : B -> B -> Prop) (f : A -> B) :
  RelationClasses.Transitive P ->
  RelationClasses.Transitive (on_rel P f).
Proof.
  intros trans u u' u''.
  apply trans.
Qed.

#[global]
Instance on_Trel_refl {A B} (P : B -> B -> Type) (f : A -> B) :
  Reflexive P ->
  Reflexive (on_Trel P f).
Proof.
  intros refl u.
  apply refl.
Qed.

#[global]
Instance on_Trel_sym {A B} (P : B -> B -> Type) (f : A -> B) :
  Symmetric P ->
  Symmetric (on_Trel P f).
Proof.
  intros sym u u'.
  apply sym.
Qed.

#[global]
Instance on_Trel_trans {A B} (P : B -> B -> Type) (f : A -> B) :
  Transitive P ->
  Transitive (on_Trel P f).
Proof.
  intros trans u u' u''.
  apply trans.
Qed.

Section Flip.
  Local Set Universe Polymorphism.
  Context {A : Type} (R : crelation A).

  Lemma flip_Reflexive : Reflexive R -> Reflexive (flip R).
  Proof using Type.
    intros HR x. unfold flip. apply reflexivity.
  Qed.

  Lemma flip_Symmetric : Symmetric R -> Symmetric (flip R).
  Proof using Type.
    intros HR x y. unfold flip. apply symmetry.
  Qed.

  Lemma flip_Transitive : Transitive R -> Transitive (flip R).
  Proof using Type.
    intros HR x y z xy yz.
    unfold flip in *. eapply HR; eassumption.
  Qed.

End Flip.

Definition commutes {A} (R S : relation A) :=
  forall x y z, R x y -> S x z -> { w & S y w * R z w}%type.

Lemma clos_t_rt {A} {R : A -> A -> Type} x y : trans_clos R x y -> clos_refl_trans R x y.
Proof.
  induction 1; try solve [econstructor; eauto].
Qed.


Arguments rt_step {A} {R} {x y}.
#[global] Polymorphic Hint Resolve rt_refl rt_step : core.


Definition clos_rt_monotone {A} (R S : relation A) :
  inclusion R S -> inclusion (clos_refl_trans R) (clos_refl_trans S).
Proof.
  move => incls x y.
  induction 1; solve [econstructor; eauto].
Qed.

Lemma relation_equivalence_inclusion {A} (R S : relation A) :
  inclusion R S -> inclusion S R -> relation_equivalence R S.
Proof. firstorder. Qed.

Lemma clos_rt_disjunction_left {A} (R S : relation A) :
  inclusion (clos_refl_trans R)
            (clos_refl_trans (relation_disjunction R S)).
Proof.
  apply clos_rt_monotone.
  intros x y H; left; exact H.
Qed.

Lemma clos_rt_disjunction_right {A} (R S : relation A) :
  inclusion (clos_refl_trans S)
            (clos_refl_trans (relation_disjunction R S)).
Proof.
  apply clos_rt_monotone.
  intros x y H; right; exact H.
Qed.

Global Instance clos_rt_trans A R : Transitive (@clos_refl_trans A R).
Proof.
  intros x y z H H'. econstructor 3; eauto.
Qed.

Global Instance clos_rt_refl A R : Reflexive (@clos_refl_trans A R).
Proof. intros x. constructor 2. Qed.

Lemma clos_refl_trans_prod_l {A B} (R : relation A) (S : relation (A * B)) :
  (forall x y b, R x y -> S (x, b) (y, b)) ->
  forall (x y : A) b,
    clos_refl_trans R x y ->
    clos_refl_trans S (x, b) (y, b).
Proof.
  intros. induction X0; try solve [econstructor; eauto].
Qed.

Lemma clos_refl_trans_prod_r {A B} (R : relation B) (S : relation (A * B)) a :
  (forall x y, R x y -> S (a, x) (a, y)) ->
  forall (x y : B),
    clos_refl_trans R x y ->
    clos_refl_trans S (a, x) (a, y).
Proof.
  intros. induction X0; try solve [econstructor; eauto].
Qed.

Lemma clos_rt_t_incl {A} {R : relation A} `{Reflexive A R} :
  inclusion (clos_refl_trans R) (trans_clos R).
Proof.
  intros x y. induction 1; try solve [econstructor; eauto].
Qed.

Lemma clos_t_rt_incl {A} {R : relation A} `{Reflexive A R} :
  inclusion (trans_clos R) (clos_refl_trans R).
Proof.
  intros x y. induction 1; try solve [econstructor; eauto].
Qed.

Lemma clos_t_rt_equiv {A} {R} `{Reflexive A R} :
  relation_equivalence (trans_clos R) (clos_refl_trans R).
Proof.
  apply relation_equivalence_inclusion.
  apply clos_t_rt_incl.
  apply clos_rt_t_incl.
Qed.

Global Instance relation_disjunction_refl_l {A} {R S : relation A} :
  Reflexive R -> Reflexive (relation_disjunction R S).
Proof.
  intros HR x. left; auto.
Qed.

Global Instance relation_disjunction_refl_r {A} {R S : relation A} :
  Reflexive S -> Reflexive (relation_disjunction R S).
Proof.
  intros HR x. right; auto.
Qed.

Global Instance clos_rt_trans_Symmetric A R :
  Symmetric R -> Symmetric (@clos_refl_trans A R).
Proof.
  intros X x y H. induction H; eauto.
  eapply clos_rt_trans; eassumption.
Qed.

Definition clos_sym {A} (R : relation A) := relation_disjunction R (flip R).

Global Instance clos_sym_Symmetric A R :
  Symmetric (@clos_sym A R).
Proof.
  intros x y []; [right|left]; assumption.
Qed.

Global Instance clos_refl_sym_trans_Symmetric A R :
  Symmetric (@clos_refl_sym_trans A R)
  := rst_sym R.

Global Instance clos_refl_sym_trans_Reflexive A R :
  Reflexive (@clos_refl_sym_trans A R)
  := rst_refl R.

Global Instance clos_refl_sym_trans_Transitive A R :
  Transitive (@clos_refl_sym_trans A R)
  := rst_trans R.

Global Instance relation_disjunction_Symmetric {A} {R S : relation A} :
  Symmetric R -> Symmetric S -> Symmetric (relation_disjunction R S).
Proof.
  intros HR HS x y [X|X]; [left|right]; eauto.
Qed.

Ltac rst_induction h :=
  induction h; [constructor|reflexivity|etransitivity].


(* Definition MR {T M} (R : M -> M -> Prop) (m : T -> M) (x y: T): Prop := R (m x) (m y). *)

(* From measure_wf of Program.Wf *)
Lemma wf_precompose {T M} (R : M -> M -> Prop) (m : T -> M) :
  well_founded R -> well_founded (precompose R m).
Proof with auto.
  unfold well_founded. intro wf.
  cut (forall (a: M) (a0: T), m a0 = a -> Acc (precompose R m) a0).
  + intros.
    now apply (H (m a)).
  + apply (@well_founded_ind M R wf (fun mm => forall a, m a = mm -> Acc _ a)).
    intros. apply Acc_intro.
    intros. rewrite H0 in H1. now apply (H (m y)).
Defined.
