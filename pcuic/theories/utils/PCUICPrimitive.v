(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Universes BasicAst Primitive Reflect
     Environment EnvironmentTyping.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect.
From Stdlib Require Import Uint63 SpecFloat.

Record array_model {term : Type} :=
  { array_universe : Universe.t;
    array_type : term;
    array_default : term;
    array_value : list term }.
Derive NoConfusion for array_model.

Arguments array_model : clear implicits.
#[global]
Instance array_model_eqdec {term} (e : EqDec term) : EqDec (array_model term).
Proof. eqdec_proof. Qed.

(* We use this inductive definition instead of the more direct case analysis
  [prim_model_of] so that [prim_model] can be used in the inductive definition
  of terms, otherwise it results in a non-strictly positive definition.
  *)
Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : PrimInt63.int) : prim_model term primInt
| primFloatModel (f : PrimFloat.float) : prim_model term primFloat
| primStringModel (s : PrimString.string) : prim_model term primString
| primArrayModel (a : array_model term) : prim_model term primArray.

Arguments primIntModel {term}.
Arguments primFloatModel {term}.
Arguments primStringModel {term}.
Arguments primArrayModel {term}.

Derive Signature NoConfusion NoConfusionHom for prim_model.

Definition prim_model_of (term : Type) (p : prim_tag) : Type :=
  match p with
  | primInt => PrimInt63.int
  | primFloat => PrimFloat.float
  | primString => PrimString.string
  | primArray => array_model term
  end.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.
Definition prim_val_tag {term} (s : prim_val term) := s.π1.
Definition prim_val_model {term} (s : prim_val term) : prim_model term (prim_val_tag s) := s.π2.

Definition prim_int {term} i : prim_val term := (primInt; primIntModel i).
Definition prim_float {term} f : prim_val term := (primFloat; primFloatModel f).
Definition prim_string {term} s : prim_val term := (primString; primStringModel s).
Definition prim_array {term} a : prim_val term := (primArray; primArrayModel a).

Definition prim_model_val {term} (p : prim_val term) : prim_model_of term (prim_val_tag p) :=
  match prim_val_model p in prim_model _ t return prim_model_of term t with
  | primIntModel i => i
  | primFloatModel f => f
  | primStringModel s => s
  | primArrayModel a => a
  end.

Lemma exist_irrel_eq {A} (P : A -> bool) (x y : sig P) : proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x p], y as [y q]; simpl; intros ->.
  now destruct (uip p q).
Qed.

#[global]
Instance reflect_eq_Z : ReflectEq Z := EqDec_ReflectEq _.

Local Obligation Tactic := idtac.
#[program]
#[global]
Instance reflect_eq_uint63 : ReflectEq uint63_model :=
  { eqb x y := Z.eqb (proj1_sig x) (proj1_sig y) }.
Next Obligation.
  cbn -[eqb].
  intros x y.
  elim: Z.eqb_spec. constructor.
  now apply exist_irrel_eq.
  intros neq; constructor => H'; apply neq; now subst x.
Qed.

#[global]
Instance reflect_eq_spec_float : ReflectEq SpecFloat.spec_float := EqDec_ReflectEq _.

Import ReflectEq.

Definition eqb_array {term} {equ : Universe.t -> Universe.t -> bool} {eqt : term -> term -> bool} (x y : array_model term) : bool :=
   equ x.(array_universe) y.(array_universe) &&
   forallb2 eqt x.(array_value) y.(array_value) &&
   eqt x.(array_default) y.(array_default) &&
   eqt x.(array_type) y.(array_type).

#[program,global]
Instance reflect_eq_array {term} {req : ReflectEq term}: ReflectEq (array_model term) :=
  { eqb := eqb_array (equ := eqb) (eqt := eqb) }.
Next Obligation.
  intros term req [] []; cbn. unfold eqb_array. cbn.
  change (forallb2 eqb) with (eqb (A := list term)).
  case: eqb_spec => //=. intros ->.
  case: eqb_spec => //=. intros ->.
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

Equations eqb_prim_model {term} {equ : Universe.t -> Universe.t -> bool} {req : term -> term -> bool} {t : prim_tag} (x y : prim_model term t) : bool :=
  | primIntModel x, primIntModel y := ReflectEq.eqb x y
  | primFloatModel x, primFloatModel y := ReflectEq.eqb x y
  | primStringModel x, primStringModel y := ReflectEq.eqb x y
  | primArrayModel x, primArrayModel y := eqb_array (equ := equ) (eqt:=req) x y.

#[global, program]
Instance prim_model_reflecteq {term} {req : ReflectEq term} {p : prim_tag} : ReflectEq (prim_model term p) :=
  {| ReflectEq.eqb := eqb_prim_model (equ := eqb) (req := eqb) |}.
Next Obligation.
  intros. depelim x; depelim y; simp eqb_prim_model.
  case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
  case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
  case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
  change (eqb_array a a0) with (eqb a a0).
  case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
Qed.

#[global]
Instance prim_model_eqdec {term} {req : ReflectEq term} : forall p : prim_tag, EqDec (prim_model term p) := _.

Equations eqb_prim_val {term} {equ : Universe.t -> Universe.t -> bool} {req : term -> term -> bool} (x y : prim_val term) : bool :=
  | (primInt; i), (primInt; i') := eqb_prim_model (equ := equ) (req := req) i i'
  | (primFloat; f), (primFloat; f') := eqb_prim_model (equ := equ) (req := req) f f'
  | (primString; s), (primString; s') := eqb_prim_model (equ := equ) (req := req) s s'
  | (primArray; a), (primArray; a') := eqb_prim_model (equ := equ) (req := req) a a'
  | x, y := false.

#[global, program]
Instance prim_val_reflect_eq {term} {req : ReflectEq term} : ReflectEq (prim_val term) :=
  {| ReflectEq.eqb := eqb_prim_val (equ := eqb) (req := eqb) |}.
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
Instance prim_tag_model_eqdec term {req : ReflectEq term} : EqDec (prim_val term) := _.

(** Printing *)

Definition string_of_prim {term} (soft : term -> string) (p : prim_val term) : string :=
  match p.π2 return string with
  | primIntModel f => "(int: " ^ string_of_prim_int f ^ ")"
  | primFloatModel f => "(float: " ^ string_of_float f ^ ")"
  | primStringModel s => "(string: " ^ string_of_pstring s ^ ")"
  | primArrayModel a => "(array:" ^ string_of_list soft a.(array_value) ^ ")"
  end.

(** Predicates *)

Inductive onPrim {term} (P : term -> Prop) : prim_val term -> Prop :=
  | onPrimInt i : onPrim P (primInt; primIntModel i)
  | onPrimFloat f : onPrim P (primFloat; primFloatModel f)
  | onPrimString s : onPrim P (primString; primStringModel s)
  | onPrimArray a :
    P a.(array_default) ->
    P a.(array_type) ->
    All P a.(array_value) ->
    onPrim P (primArray; primArrayModel a).
Derive Signature for onPrim.

Inductive onPrims {term} (eq_term : term -> term -> Type) Re : prim_val term -> prim_val term -> Type :=
  | onPrimsInt i : onPrims eq_term Re (primInt; primIntModel i) (primInt; primIntModel i)
  | onPrimsFloat f : onPrims eq_term Re (primFloat; primFloatModel f) (primFloat; primFloatModel f)
  | onPrimsString s : onPrims eq_term Re (primString; primStringModel s) (primString; primStringModel s)
  | onPrimsArray a a' :
    Re a.(array_universe) a'.(array_universe) ->
    eq_term a.(array_default) a'.(array_default) ->
    eq_term a.(array_type) a'.(array_type) ->
    All2 eq_term a.(array_value) a'.(array_value) ->
    onPrims eq_term Re (primArray; primArrayModel a) (primArray; primArrayModel a').
Derive Signature NoConfusion for onPrims.

Definition tPrimProp {term} (P : term -> Type) (p : PCUICPrimitive.prim_val term) : Type :=
  match p.π2 return Type with
  | primIntModel f => unit
  | primFloatModel f => unit
  | primStringModel s => unit
  | primArrayModel a => P a.(array_type) × P a.(array_default) × All P a.(array_value)
  end.


Inductive onPrims_dep {term} (eq_term : term -> term -> Type) (Re : Universe.t -> Universe.t -> Prop) (eq_term_dep : forall x y, eq_term x y -> Type) (Re' : forall a b, Re a b -> Type) : forall x y : prim_val term, onPrims eq_term Re x y -> Type :=
  | onPrimsInt_dep i : onPrims_dep eq_term Re eq_term_dep Re' (primInt; primIntModel i) (primInt; primIntModel i) (onPrimsInt eq_term Re i)
  | onPrimsFloat_dep f : onPrims_dep eq_term Re eq_term_dep Re' (primFloat; primFloatModel f) (primFloat; primFloatModel f) (onPrimsFloat _ _ f)
  | onPrimsString_dep s : onPrims_dep eq_term Re eq_term_dep Re' (primString; primStringModel s) (primString; primStringModel s) (onPrimsString _ _ s)
  | onPrimsArray_dep a a' :
    forall (hre : Re  a.(array_universe) a'.(array_universe))
    (eqdef : eq_term a.(array_default) a'.(array_default))
    (eqty : eq_term a.(array_type) a'.(array_type))
    (eqt : All2 eq_term a.(array_value) a'.(array_value)),
    Re' _ _ hre ->
    eq_term_dep _ _ eqdef ->
    eq_term_dep _ _ eqty ->
    All2_dep eq_term_dep eqt ->
    onPrims_dep eq_term Re eq_term_dep Re'
      (primArray; primArrayModel a) (primArray; primArrayModel a') (onPrimsArray _ _ a a' hre eqdef eqty eqt).
Derive Signature for onPrims_dep.

Set Equations Transparent.

Definition mapu_array_model {term term'} (fl : Universe.t -> Universe.t) (f : term -> term')
  (ar : array_model term) : array_model term' :=
  {| array_universe := fl ar.(array_universe);
      array_value := map f ar.(array_value);
      array_default := f ar.(array_default);
      array_type := f ar.(array_type) |}.

Equations mapu_prim {term term'} (f : Universe.t -> Universe.t) (g : term -> term')
  (p : PCUICPrimitive.prim_val term) : PCUICPrimitive.prim_val term' :=
| _, _, (primInt; primIntModel i) => (primInt; primIntModel i)
| _, _, (primFloat; primFloatModel fl) => (primFloat; primFloatModel fl)
| _, _, (primString; primStringModel s) => (primString; primStringModel s)
| f, g, (primArray; primArrayModel ar) =>
  (primArray; primArrayModel (mapu_array_model f g ar)).

Notation map_array_model := (mapu_array_model id).
Notation map_prim := (mapu_prim id).

Equations test_prim {term} (p : term -> bool) (p : prim_val term) : bool :=
| p, (primInt; _) => true
| p, (primFloat; _) => true
| p, (primString; _) => true
| p, (primArray; primArrayModel ar) =>
  List.forallb p ar.(array_value) && p ar.(array_default) && p ar.(array_type).

Equations test_primu {term} (p : Universe.t -> bool) (t : term -> bool) (p : prim_val term) : bool :=
| _, _, (primInt; _) => true
| _, _, (primFloat; _) => true
| _, _, (primString; _) => true
| p, pt, (primArray; primArrayModel ar) =>
  p ar.(array_universe) && forallb pt ar.(array_value) &&
  pt ar.(array_default) && pt ar.(array_type).

Lemma onPrims_map_prop {term term'} R R' Re p p' P f : @tPrimProp term P p ->
  onPrims R Re p p' ->
  (forall x y, P x -> R x y -> R' (f x) (f y)) ->
  onPrims (term:=term') R' Re (map_prim f p) (map_prim f p').
Proof.
  destruct p as [? []]; cbn; intros h e; depelim e; intros hf; constructor; cbn; intuition eauto.
  eapply All2_All_mix_left in a1; tea.
  eapply All2_map, All2_impl; tea; cbn; intuition eauto.
Qed.
