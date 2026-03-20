(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Universes Primitive Reflect
     Environment EnvironmentTyping.
(* From MetaRocq.Erasure Require Import BasicAst. *)
From Equations Require Import Equations.
From Stdlib Require Import ssreflect Utf8.
From Stdlib Require Import Uint63 SpecFloat.

Set Universe Polymorphism.

Section PrimModel.
  Universe i.
  Context {term : Type@{i}}.

  Record array_model : Type@{i} :=
  { array_default : term;
    array_value : list term }.
  Derive NoConfusion for array_model.
  Arguments array_model : clear implicits.

  #[global]
  Instance array_model_eqdec (e : EqDec term) : EqDec array_model.
  Proof. eqdec_proof. Qed.

  (* We use this inductive definition instead of the more direct case analysis
    [prim_model_of] so that [prim_model] can be used in the inductive definition
    of terms, otherwise it results in a non-strictly positive definition.
    *)
  Inductive prim_model : prim_tag -> Type@{i} :=
  | primIntModel (i : PrimInt63.int) : prim_model primInt
  | primFloatModel (f : PrimFloat.float) : prim_model primFloat
  | primStringModel (s : PrimString.string) : prim_model primString
  | primArrayModel (a : array_model) : prim_model primArray.

  Derive Signature NoConfusion NoConfusionHom for prim_model.

  Definition prim_model_of (p : prim_tag) : Type@{i} :=
    match p with
    | primInt => PrimInt63.int
    | primFloat => PrimFloat.float
    | primString => PrimString.string
    | primArray => array_model
    end.

  Definition prim_val : Type@{i} := ∑ t : prim_tag, prim_model t.
  Definition prim_val_tag (s : prim_val) := s.π1.
  Definition prim_val_model (s : prim_val) : prim_model (prim_val_tag s) := s.π2.

  Definition prim_int i : prim_val := (primInt; primIntModel i).
  Definition prim_float f : prim_val := (primFloat; primFloatModel f).
  Definition prim_string s : prim_val := (primString; primStringModel s).
  Definition prim_array a : prim_val := (primArray; primArrayModel a).

  Definition prim_model_val (p : prim_val) : prim_model_of (prim_val_tag p) :=
    match prim_val_model p in prim_model t return prim_model_of t with
    | primIntModel i => i
    | primFloatModel f => f
    | primStringModel s => s
    | primArrayModel a => a
    end.

  Lemma exist_irrel_eq {A} (P : A -> bool) (x y : sig P) :
    proj1_sig x = proj1_sig y -> x = y.
  Proof.
    destruct x as [x p], y as [y q]; simpl; intros ->.
    now destruct (uip p q).
  Qed.

  #[global]
  Instance reflect_eq_Z : ReflectEq Z := EqDec_ReflectEq _.

  Import ReflectEq.

  Local Obligation Tactic := idtac.

  Definition eqb_array {eqt : term -> term -> bool} (x y : array_model) :=
    forallb2 eqt x.(array_value) y.(array_value) &&
    eqt x.(array_default) y.(array_default).

  #[program,global]
  Instance reflect_eq_array {req : ReflectEq term}: ReflectEq (array_model) :=
    { eqb := eqb_array (eqt := eqb) }.
  Next Obligation.
    intros req [] []; cbn. unfold eqb_array. cbn.
    change (forallb2 eqb) with (eqb (A := list term)).
    case: eqb_spec => //=. intros ->.
    case: eqb_spec => //=. intros ->. constructor; auto.
    all:constructor; congruence.
  Qed.

  #[program,global]
  Instance reflect_eq_pstring : ReflectEq PrimString.string :=
    { eqb := (fun s1 s2 => match PrimString.compare s1 s2 with Eq => true | _ => false end) }.
  Next Obligation. discriminate. Qed.
  Next Obligation. discriminate. Qed.
  Next Obligation.
    intros s1 s2. simpl.
    destruct (PrimString.compare s1 s2) eqn:Hcmp; constructor.
    - by apply PString.compare_eq in Hcmp.
    - intros Heq%PString.compare_eq. rewrite Heq in Hcmp. inversion Hcmp.
    - intros Heq%PString.compare_eq. rewrite Heq in Hcmp. inversion Hcmp.
  Qed.

  Equations eqb_prim_model {req : term -> term -> bool} {t : prim_tag} (x y : prim_model t) : bool :=
    | primIntModel x, primIntModel y := ReflectEq.eqb x y
    | primFloatModel x, primFloatModel y := ReflectEq.eqb x y
    | primStringModel x, primStringModel y := ReflectEq.eqb x y
    | primArrayModel x, primArrayModel y := eqb_array (eqt:=req) x y.

  #[global, program]
  Instance prim_model_reflecteq {req : ReflectEq term} {p : prim_tag} : ReflectEq (prim_model p) :=
    {| ReflectEq.eqb := eqb_prim_model (req := eqb) |}.
  Next Obligation.
    intros. depelim x; depelim y; simp eqb_prim_model.
    case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
    case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
    case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
    change (eqb_array a a0) with (eqb a a0).
    case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
  Qed.

  #[global]
  Instance prim_model_eqdec {req : ReflectEq term} : forall p : prim_tag, EqDec (prim_model p) := _.

  Equations eqb_prim_val {req : term -> term -> bool} (x y : prim_val) : bool :=
    | (primInt; i), (primInt; i') := eqb_prim_model (req := req) i i'
    | (primFloat; f), (primFloat; f') := eqb_prim_model (req := req) f f'
    | (primString; s), (primString; s') := eqb_prim_model (req := req) s s'
    | (primArray; a), (primArray; a') := eqb_prim_model (req := req) a a'
    | x, y := false.

  #[global, program]
  Instance prim_val_reflect_eq {req : ReflectEq term} : ReflectEq (prim_val) :=
    {| ReflectEq.eqb := eqb_prim_val (req := eqb) |}.
  Next Obligation.
    intros. funelim (eqb_prim_val x y); simp eqb_prim_val.
    all: try by constructor; intros H; noconf H; auto.
    - change (eqb_prim_model i i') with (eqb i i').
      case: ReflectEq.eqb_spec; constructor; subst; auto. intros H; noconf H. cbn in n. auto.
    - change (eqb_prim_model f f') with (eqb f f').
      case: ReflectEq.eqb_spec; constructor; subst; auto. intros H; noconf H; auto.
    - change (eqb_prim_model s s') with (eqb s s').
      case: ReflectEq.eqb_spec; constructor; subst; auto. intros H; noconf H; auto.
    - change (eqb_prim_model a a') with (eqb a a').
      case: ReflectEq.eqb_spec; constructor; subst; auto. intros H; noconf H; auto.
  Qed.

  #[global]
  Instance prim_tag_model_eqdec {req : ReflectEq term} : EqDec (prim_val) := _.

  (** Printing *)

  Definition string_of_prim (soft : term -> string) (p : prim_val) : string :=
    match p.π2 return string with
    | primIntModel f => "(int: " ^ string_of_prim_int f ^ ")"
    | primFloatModel f => "(float: " ^ string_of_float f ^ ")"
    | primStringModel s => "(string: " ^ string_of_pstring s ^ ")"
    | primArrayModel a => "(array:" ^ soft a.(array_default) ^ " , " ^ string_of_list soft a.(array_value) ^ ")"
    end.

  Definition test_array_model (f : term -> bool) (a : array_model) : bool :=
    f a.(array_default) && forallb f a.(array_value).

  Definition test_prim (f : term -> bool) (p : prim_val) : bool :=
    match p.π2 return bool with
    | primIntModel f => true
    | primFloatModel f => true
    | primStringModel f => true
    | primArrayModel a => test_array_model f a
    end.

  Inductive primProp P : prim_val -> Type :=
    | primPropInt i : primProp P (primInt; primIntModel i)
    | primPropFloat f : primProp P (primFloat; primFloatModel f)
    | primPropString s : primProp P (primString; primStringModel s)
    | primPropArray a : P a.(array_default) × All P a.(array_value) ->
        primProp P (primArray; primArrayModel a).
  Derive Signature NoConfusion for primProp.

  Definition fold_prim {A} (f : A -> term -> A) (p : prim_val) (acc : A) : A :=
    match p.π2 return A with
    | primIntModel f => acc
    | primFloatModel f => acc
    | primStringModel f => acc
    | primArrayModel a => fold_left f a.(array_value) (f acc a.(array_default))
    end.
End PrimModel.
(* Scheme All for array_model. *)
(* Scheme All for prim_model. *)
Arguments array_model : clear implicits.
Arguments prim_val : clear implicits.

Section PrimOps.
  Universes i j.
  Context {term : Type@{i}} {term' : Type@{j}}.

  Definition map_array_model (f : term -> term') (a : array_model term) : array_model term' :=
    {| array_default := f a.(array_default);
      array_value := map f a.(array_value) |}.

  Definition map_prim (f : term -> term') (p : prim_val term) : prim_val term' :=
    match p.π2 return prim_val term' with
    | primIntModel f => (primInt; primIntModel f)
    | primFloatModel f => (primFloat; primFloatModel f)
    | primStringModel f => (primString; primStringModel f)
    | primArrayModel a => (primArray; primArrayModel (map_array_model f a))
    end.
End PrimOps.

Section primtheory.
  Universes i j k.
  Context {term : Type@{i}} {term' : Type@{j}} {term'' : Type@{k}} (g : term' -> term'') (f : term -> term') (p : prim_val term).

  Lemma map_prim_compose  :
    map_prim g (map_prim f p) = map_prim (g ∘ f) p.
  Proof.
    destruct p as [? []]; cbn; auto.
    do 2 f_equal. destruct a; rewrite /map_array_model //= map_map_compose //.
  Qed.
End primtheory.
#[global] Hint Rewrite @map_prim_compose : map all.

Lemma reflectT_forallb {A} {P : A -> Type} {p l} :
  (forall x, reflectT (P x) (p x)) ->
  reflectT (All P l) (forallb p l).
Proof.
  move=> hr; induction l; cbn; try constructor; eauto.
  case: (hr a) => /= // pa.
  - case: IHl; constructor; eauto.
    intros ha; apply f. now depelim ha.
  - constructor. intros ha; now depelim ha.
Qed.

Section primtheory.
  Universe i. Context {term : Type@{i}}.
  Context {p : prim_val term}.

  Lemma map_prim_id f :
    (forall x, f x = x) ->
    map_prim f p = p.
  Proof.
    destruct p as [? []]; cbn; auto.
    intros hf. do 2 f_equal. destruct a; rewrite /map_array_model //=; f_equal; eauto.
    rewrite map_id_f //.
  Qed.

  Lemma map_prim_id_prop f P :
    primProp P p ->
    (forall x, P x -> f x = x) ->
    map_prim f p = p.
  Proof.
    destruct p as [? []]; cbn; auto.
    intros hp hf. do 2 f_equal. destruct a; rewrite /map_array_model //=; f_equal; eauto; depelim hp.
    * eapply hf; intuition eauto.
    * eapply All_map_id. destruct p0 as [_ hp].
      eapply All_impl; tea.
  Qed.

  Lemma map_prim_eq {term'} {f g : term -> term'} :
    (forall x, f x = g x) ->
    map_prim f p = map_prim g p.
  Proof.
    destruct p as [? []]; cbn; auto.
    intros hf. do 2 f_equal. destruct a; rewrite /map_array_model //=; f_equal; eauto.
    now eapply map_ext.
  Qed.

  Lemma map_prim_eq_prop {term' P} {f g : term -> term'} :
    primProp P p ->
    (forall x, P x -> f x = g x) ->
    map_prim f p = map_prim g p.
  Proof.
    intros hp; depelim hp; subst; cbn; auto. intros hf.
    do 2 f_equal. destruct a; rewrite /map_array_model //=; f_equal; eauto.
    * eapply hf; intuition eauto.
    * destruct p0 as [_ hp].
      eapply All_map_eq.
      eapply All_impl; tea.
  Qed.

  Lemma test_prim_primProp P pr :
    (forall t, reflectT (P t) (pr t)) ->
    reflectT (primProp P p) (test_prim pr p).
  Proof.
    intros hr.
    destruct p as [? []]; cbn; repeat constructor => //.
    destruct a as []; cbn.
    rewrite /test_array_model /=.
    case: (hr array_default0) => //= hd.
    - case: (reflectT_forallb hr) => hv; repeat constructor; eauto.
      intros hp; depelim hp; intuition eauto.
    - constructor. intros hp; depelim hp; intuition eauto.
  Qed.

  Lemma test_prim_impl_primProp pr :
    test_prim pr p -> primProp pr p.
  Proof.
    case: (test_prim_primProp (fun x => pr x) pr) => //.
    intros t; destruct (pr t); constructor; eauto.
  Qed.

  Lemma primProp_impl_test_prim (pr : term -> bool) :
    primProp pr p -> test_prim pr p.
  Proof.
    case: (test_prim_primProp (fun x => pr x) pr) => //.
    intros t; destruct (pr t); constructor; eauto. eauto.
  Qed.

  Lemma primProp_conj {P Q} : primProp P p -> primProp Q p -> primProp (fun x => P x × Q x) p.
  Proof.
    destruct p as [? []]; cbn; repeat constructor; intuition eauto.
    now depelim X. now depelim X0.
    depelim X; depelim X0.
    now eapply All_mix.
  Qed.

  Lemma primProp_impl {P Q} : primProp P p -> (forall x, P x -> Q x) -> primProp Q p.
  Proof.
    intros hp hpq; destruct p as [? []]; cbn in *; intuition eauto; constructor.
    depelim hp; intuition eauto.
    eapply All_impl; tea.
  Qed.

  Lemma primProp_map {term' P} {f : term -> term'} :
    primProp (P ∘ f) p ->
    primProp P (map_prim f p).
  Proof.
    destruct p as [? []]; cbn in *; intuition eauto; constructor.
    depelim X; intuition eauto.
    eapply All_map, All_impl; tea. cbn; eauto.
  Qed.

  Lemma test_prim_map {term' pr} {f : term -> term'} :
    test_prim pr (map_prim f p) = test_prim (pr ∘ f) p.
  Proof.
    destruct p as [? []]; cbn in *; intuition auto.
    destruct a as []; rewrite /test_array_model //=. f_equal.
    rewrite forallb_map //.
  Qed.

  Lemma test_prim_eq_prop P pr pr' :
    primProp P p ->
    (forall x, P x -> pr x = pr' x) ->
    test_prim pr p = test_prim pr' p.
  Proof.
    destruct p as [? []]; cbn in *; intuition auto.
    destruct a as []; rewrite /test_array_model //=.
    depelim X; f_equal; intuition eauto.
    eapply All_forallb_eq_forallb; tea.
  Qed.

End primtheory.

#[global] Hint Rewrite @test_prim_map : map.
#[global] Hint Resolve map_prim_id map_prim_id_prop : all.
#[global] Hint Resolve map_prim_eq map_prim_eq_prop : all.
#[global] Hint Resolve primProp_impl primProp_map : all.
#[global] Hint Resolve test_prim_eq_prop : all.

Set Equations Transparent.

Section PrimIn.
  Universe i. Context {term : Type@{i}}.

  Equations InPrim (x : term) (p : prim_val term) : Prop :=
    | x | (primInt; primIntModel i) := False
    | x | (primFloat; primFloatModel _) := False
    | x | (primString; primStringModel _) := False
    | x | (primArray; primArrayModel a) :=
      x = a.(array_default) \/ In x a.(array_value).

  Lemma InPrim_primProp p P : (forall x, InPrim x p -> P x) -> primProp P p.
  Proof.
    intros hin.
    destruct p as [? []]; constructor.
    split. eapply hin; eauto. now left.
    cbn in hin.
    induction (array_value a); constructor.
    eapply hin. now right; left. eapply IHl.
    intros. eapply hin. intuition eauto. now right; right.
  Qed.

  Equations test_primIn (p : prim_val term) (f : forall x : term, InPrim x p -> bool) : bool :=
    | (primInt; primIntModel i) | _ := true
    | (primFloat; primFloatModel _) | _ := true
    | (primString; primStringModel _) | _ := true
    | (primArray; primArrayModel a) | f :=
      f a.(array_default) (or_introl eq_refl) && forallb_InP a.(array_value) (fun x H => f x (or_intror H)).

  Lemma test_primIn_spec p (f : term -> bool) :
    test_primIn p (fun x H => f x) = test_prim f p.
  Proof.
    funelim (test_primIn p (fun x H => f x)); cbn => //.
    rewrite forallb_InP_spec //.
  Qed.

  Equations map_primIn (p : prim_val term) (f : forall x : term, InPrim x p -> term) : prim_val term :=
    | (primInt; primIntModel i) | _ := (primInt; primIntModel i)
    | (primFloat; primFloatModel f) | _ := (primFloat; primFloatModel f)
    | (primString; primStringModel f) | _ := (primString; primStringModel f)
    | (primArray; primArrayModel a) | f :=
      (primArray; primArrayModel
        {| array_default := f a.(array_default) (or_introl eq_refl);
          array_value := map_InP a.(array_value) (fun x H => f x (or_intror H)) |}).

  Lemma map_primIn_spec p f :
    map_primIn p (fun x _ => f x) = map_prim f p.
  Proof.
    funelim (map_primIn p _); cbn => //.
    do 2 f_equal. unfold map_array_model; destruct a => //.
    rewrite map_InP_spec //.
  Qed.

End PrimIn.

#[global] Hint Rewrite @map_primIn_spec : map.

Unset Universe Polymorphism.

Inductive All2_Set {A B : Set} (R : A -> B -> Set) : list A -> list B -> Set :=
  All2_nil : All2_Set R [] []
| All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> All2_Set R l l' -> All2_Set R (x :: l) (y :: l').
Arguments All2_nil {_ _ _}.
Arguments All2_cons {_ _ _ _ _ _ _}.
Scheme All for All2_Set.
Derive Signature for All2_Set.
Derive NoConfusionHom for All2_Set.
#[global] Hint Constructors All2_Set : core.

Section All2_size.
  Context {A B : Set} (P : A -> B -> Set) (fn : forall x1 x2, P x1 x2 -> nat).
  Fixpoint all2_size {l1 l2} (f : All2_Set P l1 l2) : nat :=
  match f with
  | All2_nil => 0
  | All2_cons _ _ _ _ rxy rll' => fn _ _ rxy + all2_size rll'
  end.
End All2_size.

Lemma All2_Set_All2 {A B : Set} (R : A -> B -> Set) l l' : All2_Set R l l' -> All2 R l l'.
Proof.
  induction 1; constructor; auto.
Qed.
#[export] Hint Resolve All2_Set_All2 : core.

Coercion All2_Set_All2 : All2_Set >-> All2.

Lemma All2_All2_Set {A B : Set} (R : A -> B -> Set) l l' : All2 R l l' -> All2_Set R l l'.
Proof.
  induction 1; constructor; auto.
Qed.
#[export] Hint Immediate All2_All2_Set : core.

Set Equations Transparent.
Equations All2_over {A B : Set} {P : A → B → Set} {l : list A} {l' : list B} :
  All2_Set P l l' → (∀ (x : A) (y : B), P x y → Type) → Type :=
| All2_nil, _ := unit
| All2_cons rxy rll', Q => Q _ _ rxy × All2_over rll' Q.

Lemma All2_over_undep {A B : Set} {P : A → B → Set} {l : list A} {l' : list B} (a : All2_Set P l l') (Q : A -> B → Type) :
  All2_over a (fun x y _ => Q x y) <~> All2 Q l l'.
Proof.
  split.
  - induction a; cbn; constructor; intuition eauto.
  - induction a; cbn; intuition eauto; now depelim X.
Qed.

Section map_All2_dep.
  Context {A B : Set}.
  Context (P : A -> B -> Set).
  Context {hP : forall x y, P x y -> Type}.
  Context (F : forall x y (e : P x y), hP x y e).

  Equations map_All2_dep {l : list A} {l' : list B} (ev : All2_Set P l l') : All2_over ev hP :=
  | All2_nil := tt
  | All2_cons hd tl := (F _ _ hd, map_All2_dep tl).

End map_All2_dep.

Section onPrims.
  Inductive onPrims {term term' : Set} (R : term -> term' -> Set) : prim_val term -> prim_val term' -> Type :=
    | onPrimsInt i : onPrims R (primInt; primIntModel i) (primInt; primIntModel i)
    | onPrimsFloat f : onPrims R (primFloat; primFloatModel f) (primFloat; primFloatModel f)
    | onPrimsString s : onPrims R (primString; primStringModel s) (primString; primStringModel s)
    | onPrimsArray v def v' def' :
      R def def' ->
      All2_Set R v v' ->
      let a := {| array_default := def; array_value := v |} in
      let a' := {| array_default := def'; array_value := v' |} in
      onPrims R (primArray; primArrayModel a) (primArray; primArrayModel a').
  Derive Signature for onPrims.

  Variant onPrims_dep {term term' : Set} (R : term -> term' -> Set) (P : forall x y, R x y -> Type) : forall x y, onPrims R x y -> Type :=
  | onPrimsIntDep i : onPrims_dep R P (prim_int i) (prim_int i) (onPrimsInt R i)
  | onPrimsFloatDep f : onPrims_dep R P (prim_float f) (prim_float f) (onPrimsFloat R f)
  | onPrimsStringDep s : onPrims_dep R P (prim_string s) (prim_string s) (onPrimsString R s)
  | onPrimsArrayDep v def v' def'
    (ed : R def def')
    (ev : All2_Set R v v') :
    P _ _ ed ->
    All2_over ev P ->
    let a := {| array_default := def; array_value := v |} in
    let a' := {| array_default := def'; array_value := v' |} in
    onPrims_dep R P (prim_array a) (prim_array a') (onPrimsArray R v def v' def' ed ev).
  Derive Signature for onPrims_dep.

  Section map_onPrims.
    Context {term term' : Set}.
    Context {R : term -> term' -> Set}.
    Context {P : forall x y, R x y -> Type}.
    Context (F : forall x y (e : R x y), P x y e).

    Equations map_onPrims {p : prim_val term} {p' : prim_val term'} (ev : onPrims R p p') : onPrims_dep R P p p' ev :=
    | @onPrimsInt _ _ _ _ := onPrimsIntDep _ _ i;
    | @onPrimsFloat _ _ _ _ := onPrimsFloatDep _ _ f;
    | @onPrimsString _ _ _ _ := onPrimsStringDep _ _ s;
    | @onPrimsArray v def v' def' ed ev :=
      onPrimsArrayDep _ _ v def v' def' ed ev (F _ _ ed) (map_All2_dep _ F ev).
  End map_onPrims.

End onPrims.

(* Scheme All for onPrims. *)
(* Scheme All for onPrims_dep. *)
