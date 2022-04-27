(* Distributed under the terms of the MIT license. *)
(* For primitive integers and floats  *)
From Stdlib Require Numbers.Cyclic.Int63.Uint63 Floats.PrimFloat Floats.FloatAxioms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Universes Kernames.
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

#[program,global] Instance reflect_prim_int : ReflectEq Numbers.Cyclic.Int63.Uint63.int :=
  { eqb := Numbers.Cyclic.Int63.Uint63.eqb }.
Next Obligation.
  destruct (Uint63.eqb x y) eqn:eq; constructor.
  now apply (Numbers.Cyclic.Int63.Uint63.eqb_spec x y) in eq.
  now apply (Numbers.Cyclic.Int63.Uint63.eqb_false_spec x y) in eq.
Qed.

Derive NoConfusion EqDec for SpecFloat.spec_float.

Local Obligation Tactic := idtac.

#[program,global]
Instance reflect_prim_float : ReflectEq PrimFloat.float :=
  { eqb x y := eqb (ReflectEq := EqDec_ReflectEq SpecFloat.spec_float) (FloatOps.Prim2SF x) (FloatOps.Prim2SF y) }.
Next Obligation.
  intros. cbn -[eqb].
  destruct (eqb_spec (ReflectEq := EqDec_ReflectEq SpecFloat.spec_float) (FloatOps.Prim2SF x) (FloatOps.Prim2SF y)) as [H|H]; constructor.
  now apply FloatAxioms.Prim2SF_inj.
  intros e; apply H. rewrite e.
  reflexivity.
Qed.

Definition eq_prop_level l1 l2 :=
  match l1, l2 with
  | PropLevel.lProp, PropLevel.lProp => true
  | PropLevel.lSProp, PropLevel.lSProp => true
  | _, _ => false
  end.

#[global, program] Instance reflect_prop_level : ReflectEq PropLevel.t := {
  eqb := eq_prop_level
}.
Next Obligation.
  destruct x, y.
  all: unfold eq_prop_level.
  all: try solve [ constructor ; reflexivity ].
  all: try solve [ constructor ; discriminate ].
Qed.

Definition eq_levels (l1 l2 : PropLevel.t + Level.t) :=
  match l1, l2 with
  | inl l, inl l' => eqb l l'
  | inr l, inr l' => eqb l l'
  | _, _ => false
  end.

#[global, program] Instance reflect_levels : ReflectEq (PropLevel.t + Level.t) := {
  eqb := eq_levels
}.
Next Obligation.
  destruct x, y.
  cbn -[eqb]. destruct (eqb_spec t t0). subst. now constructor.
  all:try (constructor; cong).
  cbn -[eqb]. destruct (eqb_spec t t0). subst; now constructor.
  constructor; cong.
Qed.


Definition eq_name na nb :=
  match na, nb with
  | nAnon, nAnon => true
  | nNamed a, nNamed b => eqb a b
  | _, _ => false
  end.

#[global, program] Instance reflect_name : ReflectEq name := {
  eqb := eq_name
}.
Next Obligation.
  intros x y. destruct x, y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - unfold eq_name. destruct (eqb_spec i i0); nodec.
    constructor. f_equal. assumption.
Qed.

Definition eq_relevance r r' :=
  match r, r' with
  | Relevant, Relevant => true
  | Irrelevant, Irrelevant => true
  | _, _ => false
  end.

#[global, program] Instance reflect_relevance : ReflectEq relevance := {
  eqb := eq_relevance
}.
Next Obligation.
  intros x y. destruct x, y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - simpl. now constructor.
Qed.

Definition eq_aname (na nb : binder_annot name) :=
  eqb na.(binder_name) nb.(binder_name) &&
  eqb na.(binder_relevance) nb.(binder_relevance).

#[global, program] Instance reflect_aname : ReflectEq aname := {
  eqb := eq_aname
}.
Next Obligation.
  intros x y. unfold eq_aname.
  destruct (eqb_spec x.(binder_name) y.(binder_name));
  destruct (eqb_spec x.(binder_relevance) y.(binder_relevance));
  constructor; destruct x, y; simpl in *; cong.
Qed.

Definition eq_def {A} `{ReflectEq A} (d1 d2 : def A) : bool :=
  match d1, d2 with
  | mkdef n1 t1 b1 a1, mkdef n2 t2 b2 a2 =>
    eqb n1 n2 && eqb t1 t2 && eqb b1 b2 && eqb a1 a2
  end.

#[global, program] Instance reflect_def : forall {A} `{ReflectEq A}, ReflectEq (def A) := {
  eqb := eq_def
}.
Next Obligation.
  intros A RA.
  intros x y. destruct x as [n1 t1 b1 a1], y as [n2 t2 b2 a2].
  unfold eq_def.
  destruct (eqb_spec n1 n2) ; nodec.
  destruct (eqb_spec t1 t2) ; nodec.
  destruct (eqb_spec b1 b2) ; nodec.
  destruct (eqb_spec a1 a2) ; nodec.
  cbn. constructor. subst. reflexivity.
Qed.

Definition eq_cast_kind (c c' : cast_kind) : bool :=
  match c, c' with
  | VmCast, VmCast
  | NativeCast, NativeCast
  | Cast, Cast => true
  | _, _ => false
  end.

#[global, program] Instance reflect_cast_kind : ReflectEq cast_kind :=
  { eqb := eq_cast_kind }.
Next Obligation.
  induction x, y. all: cbn. all: nodec.
  all: left. all: reflexivity.
Qed.



Definition eqb_case_info
  (ci ci' : BasicAst.case_info) :=
  let (ci_ind, ci_npar, ci_relevance) := ci in
  let (ci_ind', ci_npar', ci_relevance') := ci' in
  eqb ci_ind ci_ind' && eqb ci_npar ci_npar' && eqb ci_relevance ci_relevance'.

#[global, program] Instance reflect_case_info : ReflectEq case_info :=
  {| eqb := eqb_case_info |}.
Next Obligation.
  intros. destruct x as [ci_ind ci_npar ci_relevance], y as [ci_ind' ci_npar' ci_relevance']. cbn -[eqb].
  destruct (eqb_spec ci_ind ci_ind'); subst;
  destruct (eqb_spec ci_npar ci_npar'); subst;
    destruct (eqb_spec ci_relevance ci_relevance'); subst; constructor; congruence.
Qed.

Derive NoConfusion NoConfusionHom for sig.
Derive NoConfusion NoConfusionHom for prod.

Definition eqb_context_decl {term : Type} (eqterm : term -> term -> bool)
  (x y : BasicAst.context_decl term) :=
  let (na, b, ty) := x in
  let (na', b', ty') := y in
  eqb na na' && eq_option eqterm b b' && eqterm ty ty'.

#[global, program] Instance eq_decl_reflect {term} {Ht : ReflectEq term} : ReflectEq (BasicAst.context_decl term) :=
  {| eqb := eqb_context_decl eqb |}.
Next Obligation.
  intros. destruct x as [na b ty], y as [na' b' ty']. cbn -[eqb].
  change (eq_option eqb b b') with (eqb b b').
  destruct (eqb_spec na na'); subst;
    destruct (eqb_spec b b'); subst;
      destruct (eqb_spec ty ty'); subst; constructor; congruence.
Qed.

Definition eqb_recursivity_kind r r' :=
  match r, r' with
  | Finite, Finite => true
  | CoFinite, CoFinite => true
  | BiFinite, BiFinite => true
  | _, _ => false
  end.

#[global] Instance reflect_recursivity_kind : ReflectEq recursivity_kind.
Proof.
  refine {| eqb := eqb_recursivity_kind |}.
  destruct x, y; simpl; constructor; congruence.
Defined.

Definition eqb_ConstraintType x y :=
  match x, y with
  | ConstraintType.Le n, ConstraintType.Le m => Z.eqb n m
  | ConstraintType.Eq, ConstraintType.Eq => true
  | _, _ => false
  end.

#[global] Instance reflect_ConstraintType : ReflectEq ConstraintType.t.
Proof.
  refine {| eqb := eqb_ConstraintType |}.
  destruct x, y; simpl; try constructor; try congruence.
  destruct (Z.eqb_spec z z0); constructor. now subst.
  cong.
Defined.

#[global, program] Instance Z_as_int : ReflectEq Int.Z_as_Int.t :=
  { eqb := Z.eqb }.
Next Obligation.
  apply (reflect_reflectProp_2 Z.eqb_spec).
Qed.

Scheme level_lt_ind_dep := Induction for Level.lt_ Sort Prop.
Scheme level_expr_lt_ind_dep := Induction for LevelExpr.lt_ Sort Prop.
Scheme constraint_type_lt_ind_dep := Induction for ConstraintType.lt_ Sort Prop.
Scheme level_constraint_lt_ind_dep := Induction for LevelConstraint.lt_ Sort Prop.
Scheme constraint_lt_ind_dep := Induction for UnivConstraint.lt_ Sort Prop.
Derive Signature for UnivConstraint.lt_.
Derive Signature for le.
Set Equations With UIP.

Derive NoConfusion EqDec for comparison.

Lemma string_compare_irrel {s s'} {c} (H H' : string_compare s s' = c) : H = H'.
Proof.
  apply uip.
Qed.

Scheme le_ind_prop := Induction for le Sort Prop.

Lemma nat_le_irrel {x y : nat} (l l' : x <= y) : l = l'.
Proof.
  induction l using le_ind_prop; depelim l'.
  - reflexivity.
  - lia.
  - lia.
  - f_equal. apply IHl.
Qed.

Lemma lt_level_irrel {x y : Level.t} (l l' : Level.lt_ x y) : l = l'.
Proof.
  induction l using level_lt_ind_dep; depelim l'; auto.
  - now replace l with l0 by apply uip.
  - f_equal. apply nat_le_irrel.
Qed.

Lemma lt_levelexpr_irrel {x y : LevelExpr.t} (l l' : LevelExpr.lt_ x y) : l = l'.
Proof.
  induction l using level_expr_lt_ind_dep.
  - depelim l'; auto.
    * now replace l0 with l2 by now apply nat_le_irrel.
    * exfalso. now eapply RelationClasses.irreflexivity in l2.
  - depelim l'; auto.
    * exfalso. now eapply RelationClasses.irreflexivity in l0.
    * now replace l0 with l2 by now apply lt_level_irrel.
Qed.

From Coq Require Import ProofIrrelevance.

Lemma lt_universe_irrel {x y : Universe.t} (l l' : LevelExprSet.lt x y) : l = l'.
Proof.
  apply ProofIrrelevance.proof_irrelevance.
Qed.
  (* destruct l.
  induction l using level_expr_set_lt_ind_dep.
  - depelim l'; auto.
    * now replace l0 with l2 by now apply nat_le_irrel.
    * exfalso. now eapply RelationClasses.irreflexivity in l2.
  - depelim l'; auto.
    * exfalso. now eapply RelationClasses.irreflexivity in l0.
    * now replace l0 with l2 by now apply lt_level_irrel.
Qed. *)

Lemma constraint_type_lt_level_irrel {x y} (l l' : ConstraintType.lt_ x y) : l = l'.
Proof.
  induction l using constraint_type_lt_ind_dep; depelim l'; auto.
  f_equal. apply uip.
Qed.

From Stdlib Require Import RelationClasses.

Lemma constraint_lt_irrel (x y : UnivConstraint.t) (l l' : UnivConstraint.lt_ x y) : l = l'.
Proof.
  revert l'. induction l using constraint_lt_ind_dep.
  - intros l'. depelim l'. f_equal.
    apply lt_universe_irrel.
    now elim (irreflexivity (R:=ConstraintType.lt) l4).
    now elim (irreflexivity l4).
  - intros l'; depelim l'.
    now elim (irreflexivity (R:=ConstraintType.lt) l).
    now rewrite (constraint_type_lt_level_irrel l l4).
    now elim (irreflexivity l4).
  - intros l'; depelim l'.
    now elim (irreflexivity l).
    now elim (irreflexivity l).
    now rewrite (lt_universe_irrel l l4).
Qed.

Lemma levelconstraint_lt_irrel (x y : LevelConstraint.t) (l l' : LevelConstraint.lt_ x y) : l = l'.
Proof.
  revert l'. induction l using level_constraint_lt_ind_dep.
  - intros l'. depelim l'.
    now rewrite (lt_level_irrel l l4).
    now elim (irreflexivity (R:=ConstraintType.lt) l4).
    now elim (irreflexivity l4).
  - intros l'; depelim l'.
    now elim (irreflexivity (R:=ConstraintType.lt) l).
    now rewrite (constraint_type_lt_level_irrel l l4).
    now elim (irreflexivity l4).
  - intros l'; depelim l'.
    now elim (irreflexivity l).
    now elim (irreflexivity l).
    now rewrite (lt_level_irrel l l4).
Qed.

Module LevelSetsUIP.
  Import LevelSet.Raw.

  Fixpoint levels_tree_eqb (x y : LevelSet.Raw.t) :=
  match x, y with
  | LevelSet.Raw.Leaf, LevelSet.Raw.Leaf => true
  | LevelSet.Raw.Node h l o r, LevelSet.Raw.Node h' l' o' r' =>
    eqb h h' && levels_tree_eqb l l' && eqb o o' && levels_tree_eqb r r'
  | _, _ => false
  end.

  Scheme levels_tree_rect := Induction for LevelSet.Raw.tree Sort Type.

  #[global, program] Instance levels_tree_reflect : ReflectEq LevelSet.Raw.t :=
   {| eqb := levels_tree_eqb |}.
  Next Obligation.
    induction x using levels_tree_rect; destruct y; try constructor; auto; try congruence.
    cbn [levels_tree_eqb].
    destruct (eqb_spec t0 t2); try constructor; auto; try congruence.
    destruct (IHx1 y1); try constructor; auto; try congruence.
    destruct (eqb_spec t1 t3); try constructor; auto; try congruence.
    destruct (IHx2 y2); try constructor; auto; try congruence.
  Qed.

  Derive NoConfusion for LevelSet.Raw.tree.
  Derive Signature for LevelSet.Raw.bst.

  Definition eqb_LevelSet x y :=
    eqb (LevelSet.this x) (LevelSet.this y).

  Lemma ok_irrel (x : t) (o o' : Ok x) : o = o'.
  Proof.
    unfold Ok in *.
    induction o.
    - now depelim o'.
    - depelim o'. f_equal; auto.
      clear -l0 l2. red in l0, l2.
      extensionality y. extensionality inl.
      apply lt_level_irrel.
      extensionality y. extensionality inl.
      apply lt_level_irrel.
  Qed.

  #[global,program] Instance reflect_LevelSet : ReflectEq LevelSet.t :=
   {| eqb := eqb_LevelSet |}.
  Next Obligation.
    intros [thisx okx] [thisy oky].
    unfold eqb_LevelSet.
    cbn -[eqb].
    destruct (eqb_spec thisx thisy); subst; constructor.
    - f_equal. apply ok_irrel.
    - congruence.
  Qed.
End LevelSetsUIP.

Module ConstraintSetsUIP.
  Import ConstraintSet.Raw.

  Fixpoint cs_tree_eqb (x y : t) :=
    match x, y with
    | ConstraintSet.Raw.Leaf, ConstraintSet.Raw.Leaf => true
    | ConstraintSet.Raw.Node h l o r, ConstraintSet.Raw.Node h' l' o' r' =>
      eqb h h' && cs_tree_eqb l l' && eqb o o' && cs_tree_eqb r r'
    | _, _ => false
    end.

  Scheme cs_tree_rect := Induction for ConstraintSet.Raw.tree Sort Type.

  #[global,program] Instance cs_tree_reflect : ReflectEq ConstraintSet.Raw.t :=
   {| eqb := cs_tree_eqb |}.
  Next Obligation.
    induction x using cs_tree_rect; destruct y; try constructor; auto; try congruence.
    cbn [cs_tree_eqb].
    destruct (eqb_spec t0 t1); try constructor; auto; try congruence.
    destruct (IHx1 y1); try constructor; auto; try congruence.
    destruct (eqb_spec p p0); try constructor; auto; try congruence.
    destruct (IHx2 y2); try constructor; auto; try congruence.
  Qed.

  Definition eqb_ConstraintSet x y :=
    eqb (ConstraintSet.this x) (ConstraintSet.this y).

  Derive NoConfusion for ConstraintSet.Raw.tree.
  Derive Signature for ConstraintSet.Raw.bst.

  Lemma ok_irrel (x : t) (o o' : Ok x) : o = o'.
  Proof.
    unfold Ok in *.
    induction o.
    - now depelim o'.
    - depelim o'. f_equal; auto.
      clear -l0 l2. red in l0, l2.
      extensionality y. extensionality inl.
      apply levelconstraint_lt_irrel.
      extensionality y. extensionality inl.
      apply levelconstraint_lt_irrel.
  Qed.

  #[global,program] Instance reflect_ConstraintSet : ReflectEq ConstraintSet.t :=
   {| eqb := eqb_ConstraintSet |}.
  Next Obligation.
    intros [thisx okx] [thisy oky].
    unfold eqb_ConstraintSet. cbn.
    cbn -[eqb].
    destruct (eqb_spec thisx thisy); subst; constructor.
    - f_equal. apply ok_irrel.
    - congruence.
  Qed.

End ConstraintSetsUIP.

Ltac finish_reflect :=
  (repeat
    match goal with
    | |- context[eqb ?a ?b] => destruct (eqb_spec a b); [subst|constructor; congruence]
    end);
  constructor; trivial; congruence.

Definition eqb_sorts_decl x y :=
  match x, y with
  | Monomorphic_ctx, Monomorphic_ctx => true
  | Polymorphic_ctx cx, Polymorphic_ctx cy => eqb cx cy
  | _, _ => false
  end.

#[global,program] Instance reflect_universes_decl : ReflectEq universes_decl :=
 {| eqb := eqb_sorts_decl |}.
 Next Obligation.
   unfold eqb_sorts_decl.
   intros [] []; finish_reflect.
Qed.

Definition eqb_allowed_eliminations x y :=
  match x, y with
  | IntoSProp, IntoSProp
  | IntoPropSProp, IntoPropSProp
  | IntoSetPropSProp, IntoSetPropSProp
  | IntoAny, IntoAny => true
  | _, _ => false
  end.

#[global,program] Instance reflect_allowed_eliminations : ReflectEq allowed_eliminations :=
 {| eqb := eqb_allowed_eliminations |}.
Next Obligation.
 intros [] []; simpl; constructor; congruence.
Qed.

Local Infix "==?" := eqb (at level 20).

Definition eqb_Variance x y :=
  match x, y with
  | Variance.Irrelevant, Variance.Irrelevant
  | Variance.Covariant, Variance.Covariant
  | Variance.Invariant, Variance.Invariant => true
  | _, _ => false
  end.

#[global,program] Instance reflect_Variance : ReflectEq Variance.t :=
 {| eqb := eqb_Variance |}.
Next Obligation.
  intros [] []; constructor; congruence.
Qed.
