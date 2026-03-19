(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst.

From Stdlib Require Import ssreflect.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Abbreviation rtrans_clos := clos_refl_trans_n1.

Lemma All2_many_OnOne2 :
  forall A (R : A -> A -> Type) l l',
    All2 R l l' ->
    rtrans_clos (OnOne2 R) l l'.
Proof.
  intros A R l l' h.
  induction h.
  - constructor.
  - econstructor.
    + constructor. eassumption.
    + clear - IHh. rename IHh into h.
      induction h.
      * constructor.
      * econstructor.
        -- econstructor 2. eassumption.
        -- assumption.
Qed.

Definition tDummy := tVar String.EmptyString.
Definition dummy_branch : branch term := mk_branch [] tDummy.

(** ** Reduction *)

(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Rocq in Rocq [Barras'99].
*)

Arguments OnOne2 {A} P%_type l l'.

Definition set_pcontext (p : predicate term) (pctx' : context) : predicate term :=
  {| pparams := p.(pparams);
      puinst := p.(puinst);
      pcontext := pctx';
      preturn := p.(preturn) |}.

Definition set_pcontext_two {p x} x' :
  set_pcontext (set_pcontext p x') x = set_pcontext p x :=
  eq_refl.

Definition set_preturn (p : predicate term) (pret' : term) : predicate term :=
  {| pparams := p.(pparams);
      puinst := p.(puinst);
      pcontext := p.(pcontext);
      preturn := pret' |}.

Definition set_preturn_two {p} pret pret' : set_preturn (set_preturn p pret') pret = set_preturn p pret :=
  eq_refl.

Definition set_pparams (p : predicate term) (pars' : list term) : predicate term :=
  {| pparams := pars';
     puinst := p.(puinst);
     pcontext := p.(pcontext);
     preturn := p.(preturn) |}.

Definition set_pparams_two {p pars} pars' : set_pparams (set_pparams p pars') pars = set_pparams p pars :=
  eq_refl.

Definition map_decl_na (f : aname -> aname) (g : term -> term) d :=
  {| decl_name := f (decl_name d);
     decl_body := option_map g (decl_body d);
     decl_type := g (decl_type d) |}.

(** We do not allow alpha-conversion and P applies to only one of the
  fields in the context declaration. Used to define one-step context reduction. *)
Definition on_one_decl (P : term -> term -> Type)
  (d : context_decl) (d' : context_decl) : Type :=
  match d, d' with
  | {| decl_name := na; decl_body := None; decl_type := ty |},
    {| decl_name := na'; decl_body := None; decl_type := ty' |} =>
      na = na' × P ty ty'
  | {| decl_name := na; decl_body := Some b; decl_type := ty |},
    {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} =>
      na = na' ×
      ((P ty ty' × b = b') +
        (P b b' × ty = ty'))
  | _, _ => False
  end.

Notation on_one_decl1 P Γ := (on_one_decl (P Γ)).

Lemma on_one_decl_impl (P Q : term -> term -> Type) :
  (inclusion P Q) ->
  inclusion (on_one_decl P) (on_one_decl Q).
Proof.
  intros HP x y.
  destruct x as [na [b|] ty], y as [na' [b'|] ty']; simpl; firstorder auto.
Qed.

Lemma on_one_decl_map_na (P : context -> term -> term -> Type) f g :
  forall Γ,
    inclusion (on_one_decl (on_Trel (P (map (map_decl_na f g) Γ)) g))
    (on_Trel (on_one_decl (P (map (map_decl_na f g) Γ))) (map_decl_na f g)).
Proof.
  intros Γ x y.
  destruct x as [na [b|] ty], y as [na' [b'|] ty']; simpl in *; firstorder auto; subst; simpl;
    auto.
Qed.

Lemma on_one_decl_map (P : context -> term -> term -> Type) f :
  forall Γ,
    inclusion (on_one_decl (on_Trel (P (map (map_decl f) Γ)) f))
    (on_Trel (on_one_decl (P (map (map_decl f) Γ))) (map_decl f)).
Proof.
  intros Γ x y.
  destruct x as [na [b|] ty], y as [na' [b'|] ty']; simpl in *; firstorder auto; subst; simpl;
    auto.
Qed.

Lemma on_one_decl_mapi_context (P : context -> term -> term -> Type) f :
  forall Γ,
    inclusion (on_one_decl (on_Trel (P (mapi_context f Γ)) (f #|Γ|)))
    (on_Trel (on_one_decl (P (mapi_context f Γ))) (map_decl (f #|Γ|))).
Proof.
  intros Γ x y.
  destruct x as [na [b|] ty], y as [na' [b'|] ty']; simpl in *; firstorder auto; subst; simpl;
    auto.
Qed.

Lemma on_one_decl_test_impl (P Q : term -> term -> Type) (p : term -> bool) :
  forall d d',
    on_one_decl P d d' ->
    test_decl p d ->
    (forall x y, p x -> P x y -> Q x y) ->
    on_one_decl Q d d'.
Proof.
  intros [na [b|] ty] [na' [b'|] ty'] ond []%andb_and; simpl; firstorder auto.
Qed.

Section OnOne_local_2.
  Context (P : forall (Γ : context), context_decl -> context_decl -> Type).

  Inductive OnOne2_local_env : context -> context -> Type :=
  | onone2_localenv_cons_abs Γ na na' t t' :
      P Γ (vass na t) (vass na' t') ->
      OnOne2_local_env (Γ ,, vass na t) (Γ ,, vass na' t')
  | onone2_localenv_def Γ na na' b b' t t' :
      P Γ (vdef na b t) (vdef na' b' t') ->
      OnOne2_local_env (Γ ,, vdef na b t) (Γ ,, vdef na' b' t')
  | onone2_localenv_cons_tl Γ Γ' d :
      OnOne2_local_env Γ Γ' ->
      OnOne2_local_env (Γ ,, d) (Γ' ,, d).
End OnOne_local_2.

#[global]
Instance OnOne2_local_env_length {P ctx ctx'} :
  HasLen (OnOne2_local_env P ctx ctx') #|ctx| #|ctx'|.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma OnOne2_local_env_impl R S :
  (forall Δ, inclusion (R Δ) (S Δ)) ->
  inclusion (OnOne2_local_env R)
            (OnOne2_local_env S).
Proof.
  intros H x y H'.
  induction H'; try solve [econstructor; firstorder].
Qed.

Lemma OnOne2_local_env_ondecl_impl P Q :
  (forall Γ, inclusion (P Γ) (Q Γ)) ->
  inclusion (OnOne2_local_env (fun Γ => on_one_decl1 P Γ)) (OnOne2_local_env (fun Γ => on_one_decl1 Q Γ)).
Proof.
  intros HP. apply OnOne2_local_env_impl => Γ. apply on_one_decl_impl. easy.
Qed.

Lemma OnOne2_local_env_map R Γ Δ (f : aname -> aname) (g : term -> term) :
  OnOne2_local_env (fun Γ => on_Trel (R (map (map_decl_na f g) Γ)) (map_decl_na f g)) Γ Δ ->
  OnOne2_local_env R (map (map_decl_na f g) Γ) (map (map_decl_na f g) Δ).
Proof.
  unfold on_Trel in *; induction 1; simpl; try solve [econstructor; intuition auto].
Qed.

Lemma OnOne2_local_env_map_context R Γ Δ (f : term -> term) :
  OnOne2_local_env (fun Γ => on_Trel (R (map (map_decl f) Γ)) (map_decl f)) Γ Δ ->
  OnOne2_local_env R (map_context f Γ) (map_context f Δ).
Proof.
  unfold on_Trel in *; induction 1; simpl; try solve [econstructor; intuition auto].
Qed.

Lemma OnOne2_local_env_mapi_context R Γ Δ (f : nat -> term -> term) :
  OnOne2_local_env (fun Γ => on_Trel (R (mapi_context f Γ)) (map_decl (f #|Γ|))) Γ Δ ->
  OnOne2_local_env R (mapi_context f Γ) (mapi_context f Δ).
Proof.
  unfold on_Trel in *; induction 1; simpl; try solve [econstructor; intuition auto].
  rewrite -(length_of X). now constructor.
Qed.

Lemma test_context_k_impl {p q : nat -> term -> bool} {k k'} {ctx} :
  (forall n t, p n t -> q n t) ->
  k = k' ->
  test_context_k p k ctx -> test_context_k q k' ctx.
Proof.
  intros Hfg <-.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto;
  move/andb_and=> [testp testd]; rewrite (IHctx testp);
  eapply test_decl_impl; tea; eauto.
Qed.

Lemma OnOne2_local_env_test_context_k {P ctx ctx'} {k} {p q : nat -> term -> bool} :
  (forall n t, q n t -> p n t) ->
  OnOne2_local_env P ctx ctx' ->
  (forall Γ d d',
    P Γ d d' ->
    test_context_k q k Γ ->
    test_decl (q (#|Γ| + k)) d ->
    test_decl (p (#|Γ| + k)) d') ->
  test_context_k q k ctx ->
  test_context_k p k ctx'.
Proof.
  intros hq onenv HPq.
  induction onenv.
  * move=> /= /andb_and [testq testd].
    rewrite (test_context_k_impl _ _ testq) //.
    simpl; eauto.
  * move=> /= /andb_and [testq testd].
    rewrite (test_context_k_impl _ _ testq) //.
    simpl; eauto.
  * move=> /= /andb_and [testq testd].
    rewrite (IHonenv testq).
    eapply test_decl_impl; tea.
    intros x Hx. eapply hq.
    now rewrite -(length_of onenv).
Qed.

Lemma on_one_decl_test_decl (P : term -> term -> Type)
  (p q : term -> bool) d d' :
  (forall t, p t -> q t) ->
  (forall t t', P t t' -> p t -> q t') ->
  on_one_decl P d d' ->
  test_decl p d ->
  test_decl q d'.
Proof.
  intros Hp.
  unfold test_decl.
  destruct d as [na [b|] ty], d' as [na' [b'|] ty']; simpl in * => //;
   intuition auto; rtoProp;
    subst; simpl; intuition eauto.
Qed.

Lemma OnOne2_local_env_impl_test {P Q ctx ctx'} {k} {p : nat -> term -> bool} :
  OnOne2_local_env P ctx ctx' ->
  (forall Γ d d',
    P Γ d d' ->
    test_context_k p k Γ ->
    test_decl (p (#|Γ| + k)) d ->
    Q Γ d d') ->
  test_context_k p k ctx ->
  OnOne2_local_env Q ctx ctx'.
Proof.
  intros onenv HPq.
  induction onenv.
  * move=> /= /andb_and [testq testd].
    constructor; auto.
  * move=> /= /andb_and [testq testd].
    constructor; auto.
  * move=> /= /andb_and [testq testd].
    constructor; auto.
Qed.
