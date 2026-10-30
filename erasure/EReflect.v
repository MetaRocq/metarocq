From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Reflect.
From MetaRocq.Erasure Require Import EPrimitive EAst EInduction.
From Equations Require Import Equations.

Local Ltac finish :=
  let h := fresh "h" in
  right ;
  match goal with
  | e : ?t <> ?u |- _ =>
    intro h ; apply e ; now inversion h
  end.

Local Ltac fcase c :=
  let e := fresh "e" in
  case c ; intro e ; [ subst ; try (left ; reflexivity) | finish ].

Local Ltac term_dec_tac term_dec :=
  repeat match goal with
         | t : term, u : term |- _ => fcase (term_dec t u)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (eq_dec i i')
         | i : kername, i' : kername |- _ => fcase (eq_dec i i')
         | i : string, i' : kername |- _ => fcase (eq_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         | x : recursivity_kind, y : recursivity_kind |- _ => fcase (eq_dec x y)
         end.

Ltac nodec :=
  let bot := fresh "bot" in
  try solve [ constructor ; intro bot ; inversion bot ; subst ; tauto ].

Derive NoConfusion NoConfusionHom for term.

#[global]
Instance EqDec_term : EqDec term.
Proof.
  intro x; induction x using term_forall_list_ind ; intro t ;
    destruct t ; try (right ; discriminate).
  all: term_dec_tac term_dec.
  - left; reflexivity.
  - revert l0. induction X ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX l0) ; nodec.
        destruct (p t) ; nodec.
        subst. left. inversion e. reflexivity.
  - destruct (IHx t) ; nodec.
    subst; left; reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - revert args0. induction X ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX l0) ; nodec.
        destruct (p t) ; nodec.
        inversion e. subst; left; reflexivity.
  - destruct (IHx t) ; nodec.
    subst. revert brs. clear IHx.
    induction X ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX l0) ; nodec.
        destruct (p (snd p0)) ; nodec.
        destruct (eq_dec (fst x) (fst p0)) ; nodec.
        destruct x, p0.
        left.
        cbn in *. subst. inversion e. reflexivity.
  - destruct (IHx t) ; nodec.
    left. subst. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct m0.
      * right. discriminate.
      * destruct (p (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e0. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct m0.
      * right. discriminate.
      * destruct (p (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e0. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
  - destruct prim as [? []]; destruct p as [? []]; cbn ; nodec.
    + destruct (eq_dec i i0); nodec; subst; eauto.
    + destruct (eq_dec f f0); nodec; subst; eauto.
    + destruct (eq_dec s s0); nodec; subst; eauto.
    + destruct a as [? ?], a0 as [? ?]; cbn.
      depelim X. destruct p as [hd hv]. cbn in *.
      destruct (hd array_default); nodec; subst; eauto.
      revert array_value; induction hv; intros []; eauto; nodec.
      destruct (p t); subst; nodec.
      destruct (IHhv l0); nodec. noconf e; eauto.
  - destruct (IHx t); subst; nodec. now left.
  - destruct (IHx t); subst; nodec. now left.
Defined.

#[global]
Instance ReflectEq_term : ReflectEq.ReflectEq _ :=
  @EqDec_ReflectEq _ EqDec_term.

Definition eqb_constant_body (x y : constant_body) :=
  eqb (cst_body x) (cst_body y).

#[global, program]
Instance reflect_constant_body : ReflectEq constant_body :=
  {| eqb := eqb_constant_body |}.
Next Obligation.
Proof.
  revert x y; intros [] [].
  unfold eqb_constant_body.
  cbn -[eqb].
  finish_reflect.
Qed.

Definition eqb_constructor_body (x y : constructor_body) :=
  (x.(cstr_name), x.(cstr_nargs)) == (y.(cstr_name), y.(cstr_nargs)).

#[global, program]
Instance reflect_constructor_body : ReflectEq constructor_body :=
  {| eqb := eqb_constructor_body |}.
Next Obligation.
Proof.
  unfold eqb_constructor_body.
  destruct x, y; cbn.
  case: eqb_spec; intros H; constructor; congruence.
Qed.
Definition eqb_projection_body (x y : projection_body) :=
  x.(proj_name) == y.(proj_name).

#[global, program]
Instance reflect_projection_body : ReflectEq projection_body :=
  {| eqb := eqb_projection_body |}.
Next Obligation.
Proof.
  unfold eqb_projection_body.
  destruct x, y; cbn.
  case: eqb_spec; intros H; constructor; congruence.
Qed.

Definition eqb_one_inductive_body (x y : one_inductive_body) :=
  let (n, i, k, c, p) := x in
  let (n', i', k', c', p') := y in
  eqb n n' && eqb i i' && eqb k k' && eqb c c' && eqb p p'.

#[global]
Instance reflect_one_inductive_body : ReflectEq one_inductive_body.
Proof.
  refine {| eqb := eqb_one_inductive_body |}.
  intros [] [].
  unfold eqb_one_inductive_body; finish_reflect.
Defined.

Definition eqb_mutual_inductive_body (x y : mutual_inductive_body) :=
  let (f, n, b) := x in
  let (f', n', b') := y in
  eqb f f' && eqb n n' && eqb b b'.

#[global, program]
Instance reflect_mutual_inductive_body : ReflectEq mutual_inductive_body :=
  {| eqb := eqb_mutual_inductive_body |}.
Next Obligation.
Proof.
  revert x y; intros [] [].
  unfold eqb_mutual_inductive_body; finish_reflect.
Defined.

Definition eqb_global_decl x y :=
  match x, y with
  | ConstantDecl cst, ConstantDecl cst' => eqb cst cst'
  | InductiveDecl mib, InductiveDecl mib' => eqb mib mib'
  | _, _ => false
  end.

#[global, program]
Instance reflect_global_decl : ReflectEq global_decl :=
  {| eqb := eqb_global_decl |}.
Next Obligation.
Proof.
  revert x y.
  unfold eqb_global_decl.
  intros [] []; finish_reflect.
Defined.
