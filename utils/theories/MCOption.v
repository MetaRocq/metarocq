From Coq Require Import List ssreflect ssrbool Arith Morphisms Relation_Definitions.

From MetaCoq.Utils Require Import MCPrelude MCList MCProd MCReflect ReflectEq.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Polymorphic Definition on_some {A} (P : A -> Type) (o : option A) :=
  match o with
  | Some t => P t
  | None => False
  end.

Definition on_Some {A} (P : A -> Prop) : option A -> Prop :=
  fun x => match x with
        | Some x => P x
        | None => False
        end.

Lemma on_SomeP {A} {P : A -> Prop} (opta : option A) : on_Some P opta -> ∑ a, opta = Some a /\ P a.
Proof.
  destruct opta as [a|]; [|intros []].
  intros h; exists a; split; [reflexivity|assumption].
Qed.


Polymorphic Definition on_some_or_none {A} (P : A -> Type) : option A -> Type :=
  fun x => match x with
        | Some x => P x
        | None => True
        end.

Definition on_Some_or_None {A} (P : A -> Prop) : option A -> Prop :=
  fun x => match x with
        | Some x => P x
        | None => True
        end.

Definition R_opt {A} (R : relation A) : relation (option A) :=
  fun x y => match x, y with
    | Some x, Some y => R x y
    | None, None => True
    | _, _ => False
  end.

Definition option_default {A B} (f : A -> B) (o : option A) (b : B) :=
  match o with Some x => f x | None => b end.

Lemma option_default_ext {A B} (f : A -> B) x1 x2 d :
  x1 = x2 -> option_default f x1 d = option_default f x2 d.
Proof.
  now intros ->.
Qed.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof.
  now intros [=].
Qed.


Fixpoint map_option_out {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | hd :: tl => match hd, map_option_out tl with
                | Some hd, Some tl => Some (hd :: tl)
                | _, _ => None
                end
  end.

Lemma map_option_out_Some_spec {A}
  : forall l l', @map_option_out A l = Some l' <-> l = map Some l'.
Proof.
  induction l as [|[?|]? IH], l' as [|? l'] => //=; try specialize (IH l').
  all: destruct map_option_out => //=.
  all: split; inversion 1; subst.
  all: intuition (congruence || subst).
Qed.

Lemma map_option_out_None_spec {A}
  : forall l, @map_option_out A l = None <-> (exists n, nth_error l n = Some None).
Proof.
  induction l as [|[?|]? IH] => //=.
  all: try destruct map_option_out => //=.
  all: split; [ inversion 1 | case; case; intros * => //= ]; subst.
  all: try now (exists 0).
  all: destruct IH as [IH0 IH1]; specialize (fun n pf => IH1 (ex_intro _ n pf)); cbn in *.
  all: firstorder (congruence || eauto).
  eexists (S _); cbn; tea.
Qed.

Lemma map_option_out_map_option_map {A} (l : list (option A)) (f : A -> A) :
  map_option_out (map (option_map f) l) =
  option_map (map f) (map_option_out l).
Proof.
  induction l; simpl; auto.
  destruct (option_map f a) eqn:fa.
  rewrite IHl. destruct (map_option_out l). simpl in *.
  destruct a; simpl in *; congruence.
  simpl. destruct a; reflexivity.
  destruct a; simpl in *; congruence.
Qed.

Lemma option_map_two {A B C} (f : A -> B) (g : B -> C) x
  : option_map g (option_map f x) = option_map (fun x => g (f x)) x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma option_map_ext {A B} (f g : A -> B) (H : forall x, f x = g x)
  : forall z, option_map f z = option_map g z.
Proof.
  intros []; cbn; congruence.
Qed.

#[global] Instance option_map_proper {A B} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@option_map A B).
Proof.
  intros f g Hfg x y <-. now apply option_map_ext.
Qed.

Lemma option_map_id {A} : option_map (@id A) =1 id.
Proof. by intros []. Qed.

Lemma nth_map_option_out {A B} (f : nat -> A -> option B) l l' i t : map_option_out (mapi f l) = Some l' ->
  nth_error l' i = Some t ->
  (∑ x, (nth_error l i = Some x) /\ (f i x = Some t)).
Proof.
  unfold mapi.
  rewrite -{3}(Nat.add_0_r i).
  generalize 0.
  induction l in i, l' |- *; intros n; simpl. intros [= <-]. rewrite nth_error_nil; discriminate.
  simpl. destruct (f n a) eqn:Heq => //.
  destruct (map_option_out (mapi_rec f l (S n))) eqn:Heq' => //.
  intros [= <-].
  destruct i; simpl. intros [= ->]. now exists a.
  specialize (IHl _ i _ Heq').
  now rewrite plus_n_Sm.
Qed.

Lemma map_option_out_length {A} (l : list (option A)) l' : map_option_out l = Some l' -> #|l| = #|l'|.
Proof.
  induction l in l' |- * => /=.
  now move=> [=] <-.
  simpl. destruct a; try discriminate.
  destruct map_option_out eqn:Heq; try discriminate.
  move=> [=] <-. by rewrite (IHl l0 eq_refl).
Qed.

Lemma map_option_out_impl {A B} (l : list A) (f g : A -> option B) x :
  (forall x y, f x = Some y -> g x = Some y) ->
  map_option_out (map f l) = Some x ->
  map_option_out (map g l) = Some x.
Proof.
  intros Hfg.
  induction l in x |- *; simpl; auto.
  destruct (f a) eqn:fa.
  - rewrite (Hfg _ _ fa).
    move: IHl; destruct map_option_out.
    * move=> H'. specialize (H' _ eq_refl).
      rewrite H'. congruence.
    * discriminate.
  - discriminate.
Qed.

Lemma option_map_Some {A B} (f : A -> B) (o : option A) x :
  option_map f o = Some x ->
  ∑ y, (o = Some y) /\ (x = f y).
Proof.
  destruct o => /= //.
  move=> [] <-. exists a; auto.
Qed.

Lemma reflect_option_default {A} {P : A -> Type} {p : A -> bool} :
  (forall x, reflectT (P x) (p x)) ->
  forall x, reflectT (option_default P x unit) (option_default p x true).
Proof.
  intros Hp x.
  destruct x => /= //. constructor. exact tt.
Qed.


(** Analogous to Forall, but for the [option] type *)
(* Helpful for induction principles and predicates on [term] *)
Inductive ForOption {A} (P : A -> Prop) : option A -> Prop :=
| fo_Some : forall t, P t -> ForOption P (Some t)
| fo_None : ForOption P None.
Derive Signature for ForOption.

Definition foroptb {A : Type} (p : A -> bool) (o : option A) : bool :=
  option_get true (option_map p o).

Definition foroptb2 {A : Type} (p : A -> A -> bool) (o o': option A) : bool :=
  match o, o' with
  | Some v, Some v' => p v v'
  | None, None => true
  | _, _ => false
  end.

#[global] Instance foroptb_proper A : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@foroptb A).
Proof.
  intros f g Hfg x y ->; rewrite /foroptb.
  destruct y; simpl; rewrite // ?Hfg.
Qed.

#[global] Instance foroptb_proper_pointwise A : Proper (`=1` ==> `=1`) (@foroptb A).
Proof.
  intros f g Hfg y; rewrite /foroptb.
  destruct y; simpl; rewrite // ?Hfg.
Qed.

Lemma foroptb_impl {A} (f g : A -> bool) x : (forall x, f x -> g x) -> foroptb f x -> foroptb g x.
Proof.
  move=> Hf; destruct x; simpl => //; apply Hf.
Qed.

(* Extension *)

Inductive option_extends {A} : relation (option A) :=
| option_ext_fill t : option_extends None (Some t)
| option_ext_keep t : option_extends (Some t) (Some t)
| option_ext_non : option_extends None None.
Derive Signature for option_extends.

Definition option_extendsb {A} {Aeq:ReflectEq A} (x y : option A) : bool :=
  match x, y with
  | None, Some _ => true
  | Some t1, Some t2 => t1 == t2
  | None, None => true
  | _, _ => false
  end.

Lemma option_extendsT {A} {Aeq : ReflectEq A} x y : reflect (@option_extends A x y) (option_extendsb x y).
Proof.
  destruct x as [x|], y as [y|]; cbn.
  1: generalize (eqb_spec x y); case: eqb => H.
  all: constructor.
  1: replace y with x by now inversion H.
  all: first [ constructor | inversion 1 ].
  { inversion H; congruence. }
Qed.

Lemma option_extends_spec {A} {Aeq : ReflectEq A} x y : option_extendsb x y <-> @option_extends A x y.
Proof.
  case: option_extendsT; intuition congruence.
Qed.

#[export] Instance option_extends_refl {A} : RelationClasses.Reflexive (@option_extends A).
Proof. intros []; constructor. Qed.

#[export] Instance option_extends_trans {A} : RelationClasses.Transitive (@option_extends A).
Proof.
  intros x y z [] H; inv H; constructor.
Qed.
