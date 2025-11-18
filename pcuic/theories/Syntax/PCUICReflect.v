(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

From MetaRocq.PCUIC Require Import PCUICAst PCUICInduction.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import EnvironmentReflect.
From MetaRocq.Common Require Export Reflect.

Open Scope pcuic.


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
         | u : sort, u' : sort |- _ => fcase (eq_dec u u')
         | x : Instance.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | x : Instance.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | x : list aname, y : list aname |- _ => fcase (eq_dec x y)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (eq_dec i i')
         | i : kername, i' : kername |- _ => fcase (eq_dec i i')
         | i : string, i' : kername |- _ => fcase (eq_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         | n : aname, n' : aname |- _ => fcase (eq_dec n n')
         | i : prim_val, j : prim_val |- _ => fcase (eq_dec i j)
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         | x : case_info, y : case_info |- _ =>
           fcase (eq_dec x y)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         end.

Derive NoConfusion NoConfusionHom for term.

Fixpoint eqb_term (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' && forallb2 eqb_term args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    eqb u u'

  | tApp u v, tApp u' v' => eqb_term u u' && eqb_term v v'

  | tConst c u, tConst c' u' =>
    eqb c c' && eqb u u'

  | tInd i u, tInd i' u' =>
    eqb i i' && eqb u u'

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    eqb u u'

  | tLambda na A t, tLambda na' A' t' =>
    eqb na na' && eqb_term A A' && eqb_term t t'

  | tProd na A B, tProd na' A' B' =>
    eqb na na' && eqb_term A A' && eqb_term B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb na na' && eqb_term B B' && eqb_term b b' && eqb_term u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_predicate_gen
      (fun u u' => eqb u u')
      (eqb_context_decl eqb_term)
      (eqb_term) p p' &&
    eqb_term c c' &&
    forallb2 (fun x y =>
      forallb2 (eqb_context_decl eqb_term) x.(bcontext) y.(bcontext) &&
      eqb_term (bbody x) (bbody y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' && eqb_term c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term x.(dtype) y.(dtype) &&
      eqb_term x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb x.(dname) y.(dname)) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term x.(dtype) y.(dtype) &&
      eqb_term x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb x.(dname) y.(dname)) mfix mfix'

  | tPrim p, tPrim p' => @eqb_prim_val _ eqb eqb_term p p'
  | _, _ => false
  end.

Lemma reflectProp_equiv {P Q} b : P <-> Q -> reflectProp P b <-> reflectProp Q b.
Proof.
  intros eqpq; split; intros []; constructor; intuition.
Qed.

Lemma reflectEq_andb {A B} {ra : ReflectEq A} {rb : ReflectEq B} {x x' : A} {y y' : B} :
  reflectProp ({| pr1 := x; pr2 := y |} = {| pr1 := x'; pr2 := y' |}) ((x == x') && (y == y')).
Proof.
  destruct (eqb_spec x x'); try constructor; try congruence.
  destruct (eqb_spec y y'); constructor; congruence.
Qed.

Lemma reflectEq_andb_3 {A B C} {ra : ReflectEq A} {rb : ReflectEq B} {rc : ReflectEq C} {x x' : A} {y y' : B} {z z' : C} :
  reflectProp ({| pr1 := x; pr2 := {| pr1 := y; pr2 := z |} |} = {| pr1 := x'; pr2 := {| pr1 := y'; pr2 := z' |} |}) ((x == x') && (y == y') && (z == z')).
Proof.
  destruct (eqb_spec x x'); try constructor; try congruence.
  destruct (eqb_spec y y'); try constructor; try congruence.
  destruct (eqb_spec z z'); try constructor; try congruence.
Qed.

Lemma reflectEq_andb_left {A B} {ra : ReflectEq A} {p : B -> B -> bool} {x x' : A} {y y' : B} :
  reflectProp (y = y') (p y y') ->
  reflectProp ({| pr1 := x; pr2 := y |} = {| pr1 := x'; pr2 := y' |}) ((x == x') && p y y').
Proof.
  intros hy.
  destruct (eqb_spec x x'); try constructor; try congruence.
  destruct hy; constructor; congruence.
Qed.

Lemma reflectEq_andb_right {A B} {ra : ReflectEq B} {p : A -> A -> bool} {x x' : A} {y y' : B} :
  reflectProp (x = x') (p x x') ->
  reflectProp ({| pr1 := x; pr2 := y |} = {| pr1 := x'; pr2 := y' |}) (p x x' && (y == y')).
Proof.
  intros hx.
  destruct hx; try constructor; try congruence.
  destruct (eqb_spec y y'); try constructor; try congruence.
Qed.

Lemma reflectProp_noConfusion {A} {noconf : NoConfusionPackage A} (x y : A) b : reflectProp (x = y) b <-> reflectProp (NoConfusion x y) b.
Proof.
  eapply reflectProp_equiv.
  split. eapply noConfusion_inv. eapply noConfusion.
Qed.

Lemma reflectProp_sigma_simpl {A B : Type} (x x' : A) (y y' : B) b :
  reflectProp (x = x' /\ y = y') b <->
  reflectProp ({| pr1 := x; pr2 := y|} = {| pr1 := x'; pr2 := y' |}) b.
Proof.
  eapply reflectProp_equiv. intuition auto; congruence.
Qed.

Lemma reflect_prop_list {A} {l l' : list A} {p : A -> A -> bool} :
  All (fun x : A => forall y : A, reflectProp (x = y) (p x y)) l ->
  reflectProp (l = l') (forallb2 p l l').
Proof.
  intros a; revert l'.
  induction a; intros []; cbn; try constructor; try congruence.
  destruct (IHa l0).
  destruct (p0 a0); try constructor; try congruence.
  rewrite andb_false_r. constructor; congruence.
Qed.

Local Ltac t := try constructor; intuition auto; try congruence.
Local Ltac t' := rewrite /= ?andb_false_r ?andb_true_r /=; t.

Lemma reflect_prop_context_decl d d' :
  ondecl (fun x : term => forall y : term, reflectProp (x = y) (eqb_term x y)) d ->
  reflectProp (d = d') (eqb_context_decl eqb_term d d').
Proof.
  intros []; cbn in *.
  destruct d as [na [b|] ty]; cbn in *; t';
  destruct d' as [na' [b'|] ty']; cbn in *; t';
  destruct (eqb_spec na na'); t'; destruct (r ty'); t'; destruct (o b'); t'.
Qed.

Transparent eqb_prim_model eqb_prim_val.

#[program,global] Instance eqb_term_reflect : ReflectEq term :=
  {| eqb := eqb_term |}.
Next Obligation.
Proof.
  induction x using term_forall_list_ind in y |- *; destruct y; try constructor; cbn; try congruence.
  all:apply reflectProp_noConfusion; cbn.
  all:try match goal with
    |- reflectProp _ _ => apply eqb_spec || apply reflectEq_andb || apply reflectEq_andb_3
  end.
  all:unfold eqb_predicate_gen.
  all:repeat match goal with
    [ H : forall foo, reflectProp (?x = _) _ |- context [eqb_term ?x ?y] ] => destruct (H y); t'
  end.
  all:try match goal with
    |- reflectProp _ (?x == ?y) => destruct (eqb_spec x y); t
  end.
  - apply reflectEq_andb_left.
    { now eapply reflect_prop_list. }
  - destruct (eqb_spec ind indn); t => /=.
    destruct (eqb_spec (puinst p) (puinst p0)); t'.
    destruct X as [? []]. red in X0.
    destruct (r (preturn p0)); t'.
    case: (reflect_prop_list (l':= pparams p0) a); t'.
    case: (reflect_prop_list (l:=l) (l' := brs)); t'.
    { eapply All_impl; tea; cbv beta. intros [bctx bbody] [].
      intros [bctx' bbody']; cbn in *.
      case: (reflect_prop_list (l' := bctx')); t'.
      eapply All_impl; tea; cbv beta; intros.
      now eapply reflect_prop_context_decl.
      destruct (r0 bbody'); t'. }
    case: (reflect_prop_list (l := pcontext p) (l' := pcontext p0)); t'.
    { eapply All_impl; tea; cbv beta. intros; now eapply reflect_prop_context_decl. }
    subst. destruct p, p0; cbn in *; congruence.
  - destruct (eqb_spec n idx); t'.
    case: (reflect_prop_list (l := m) (l' := mfix)); t'.
    red in X.
    { eapply All_impl; tea; cbv beta. intros []; cbn; intros [] []; cbn.
      destruct (r dtype0); t'.
      destruct (r0 dbody0); t'.
      destruct (eqb_spec rarg rarg0); t'.
      destruct (eqb_spec dname dname0); t'. }
  - destruct (eqb_spec n idx); t'.
    case: (reflect_prop_list (l := m) (l' := mfix)); t'.
    red in X.
    { eapply All_impl; tea; cbv beta. intros []; cbn; intros [] []; cbn.
      destruct (r dtype0); t'.
      destruct (r0 dbody0); t'.
      destruct (eqb_spec rarg rarg0); t'.
      destruct (eqb_spec dname dname0); t'. }
  - destruct p, p; cbn in *; destruct prim, p; cbn; nodec.
    case: eqb_spec; intros; subst; nodec. constructor; auto.
    case: eqb_spec; intros; subst; nodec. constructor; auto.
    case: eqb_spec; intros; subst; nodec. constructor; auto.
    destruct X as [eqty [eqd eqv]]. unfold eqb_array.
    destruct (eqty (array_type a0)); t'.
    destruct (eqd (array_default a0)); t'. 2:noconf H1; auto.
    2:{ noconf H0; auto. }
    case: eqb_spec; intros; subst; nodec; cbn.
    case: (reflect_prop_list eqv) => //. constructor; auto. f_equal. f_equal.
    destruct a, a0; cbn in *; congruence. nodec.
Qed.

#[global]
Instance EqDec_term : EqDec term := ReflectEq_EqDec _.

(** This is defined using reflect_list, so no issue of computing with proofs here. *)
#[global]
Instance eqb_ctx : ReflectEq context := _.

Definition eqb_predicate (p p' : predicate term) : bool :=
  eqb (p.(pparams), p.(puinst), p.(pcontext), p.(preturn)) (p'.(pparams), p'.(puinst), p'.(pcontext), p'.(preturn)).

#[program,global]
Instance reflect_eq_predicate : ReflectEq (predicate term) :=
  {| eqb := eqb_predicate |}.
Next Obligation.
Proof.
  unfold eqb_predicate. destruct x, y; cbn.
  case: eqb_spec; t.
Qed.

#[program, global] Instance branch_eq_dec : ReflectEq (branch term) :=
  { eqb br br' := eqb (br.(bcontext), br.(bbody)) (br'.(bcontext), br'.(bbody)) }.
Next Obligation.
Proof. destruct x, y; cbn; case: eqb_spec; t. Qed.

Definition eqb_context_decl (x y : context_decl) :=
  eqb (x.(decl_name), x.(decl_body), x.(decl_type))
    (y.(decl_name), y.(decl_body), y.(decl_type)).

#[program, global]
Instance eq_ctx : ReflectEq context_decl :=
  {| eqb := eqb_context_decl |}.
Next Obligation.
Proof.
  unfold eqb_context_decl.
  destruct x, y; cbn.
  case: eqb_spec; t'.
Qed.

Definition eqb_constant_body (x y : constant_body) :=
  let (tyx, bodyx, univx, relx) := x in
  let (tyy, bodyy, univy, rely) := y in
  eqb tyx tyy && eqb bodyx bodyy && eqb univx univy && eqb relx rely.

#[program, global]
Instance reflect_constant_body : ReflectEq constant_body :=
 {| eqb := eqb_constant_body |}.
Next Obligation.
  destruct x, y; unfold eqb_constant_body; finish_reflect.
Qed.

Local Infix "==?" := eqb (at level 20).

Definition eqb_constructor_body (x y : constructor_body) :=
  x.(cstr_name) ==? y.(cstr_name) &&
  x.(cstr_args) ==? y.(cstr_args) &&
  x.(cstr_indices) ==? y.(cstr_indices) &&
  x.(cstr_type) ==? y.(cstr_type) &&
  x.(cstr_arity) ==? y.(cstr_arity).

#[program, global]
Instance reflect_constructor_body : ReflectEq constructor_body :=
  {| eqb := eqb_constructor_body |}.
Next Obligation.
Proof.
  destruct x, y; cbn in *.
  unfold eqb_constructor_body; cbn -[eqb]. finish_reflect.
Qed.

Definition eqb_projection_body (x y : projection_body) :=
  (x.(proj_name), x.(proj_type), x.(proj_relevance)) ==
  (y.(proj_name), y.(proj_type), y.(proj_relevance)).

#[program, global]
Instance reflect_projection_body : ReflectEq projection_body :=
  {| eqb := eqb_projection_body |}.
Next Obligation.
Proof.
  unfold eqb_projection_body.
  case: eqb_spec.
  destruct x, y; cbn in *. constructor; auto. congruence.
  unfold eqb_constructor_body; cbn -[eqb]. finish_reflect.
Qed.

Definition eqb_one_inductive_body (x y : one_inductive_body) :=
  x.(ind_name) ==? y.(ind_name) &&
  x.(ind_indices) ==? y.(ind_indices) &&
  x.(ind_sort) ==? y.(ind_sort) &&
  x.(ind_type) ==? y.(ind_type) &&
  x.(ind_kelim) ==? y.(ind_kelim) &&
  x.(ind_ctors) ==? y.(ind_ctors) &&
  x.(ind_projs) ==? y.(ind_projs) &&
  x.(ind_relevance) ==? y.(ind_relevance).

#[program, global]
Instance reflect_one_inductive_body : ReflectEq one_inductive_body :=
  {| eqb := eqb_one_inductive_body |}.
Next Obligation.
Proof.
  destruct x, y; unfold eqb_one_inductive_body; cbn -[eqb]; finish_reflect.
Qed.

Definition eqb_mutual_inductive_body (x y : mutual_inductive_body) :=
  let (f, n, p, b, u, v) := x in
  let (f', n', p', b', u', v') := y in
  eqb f f' && eqb n n' && eqb b b' && eqb p p' && eqb u u' && eqb v v'.

#[program, global]
Instance reflect_mutual_inductive_body : ReflectEq mutual_inductive_body :=
  {| eqb := eqb_mutual_inductive_body |}.
Next Obligation.
Proof.
  destruct x, y; unfold eqb_mutual_inductive_body; finish_reflect.
Qed.

Definition eqb_global_decl x y :=
  match x, y with
  | ConstantDecl cst, ConstantDecl cst' => eqb cst cst'
  | InductiveDecl mib, InductiveDecl mib' => eqb mib mib'
  | _, _ => false
  end.

#[program, global]
Instance reflect_global_decl : ReflectEq global_decl :=
  {| eqb := eqb_global_decl |}.
Next Obligation.
Proof.
  unfold eqb_global_decl. destruct x, y; finish_reflect.
Qed.

Module PCUICTermDecide <: TermDecide PCUICTerm.
  #[export] Instance term_eq_dec : EqDec term := _.
  Include TermDecideReflectInstances PCUICTerm.
End PCUICTermDecide.

Module PCUICEnvironmentDecide <: EnvironmentDecide PCUICTerm PCUICEnvironment.
  #[export] Instance context_eq_dec : EqDec context := _.
  #[export] Instance constructor_body_eq_dec : EqDec constructor_body := _.
  #[export] Instance projection_body_eq_dec : EqDec projection_body := _.
  #[export] Instance one_inductive_body_eq_dec : EqDec one_inductive_body := _.
  #[export] Instance mutual_inductive_body_eq_dec : EqDec mutual_inductive_body := _.
  #[export] Instance constant_body_eq_dec : EqDec constant_body := _.
  #[export] Instance global_decl_eq_dec : EqDec global_decl := _.
  Include EnvironmentDecideReflectInstances PCUICTerm PCUICEnvironment.
End PCUICEnvironmentDecide.

Module PCUICEnvironmentReflect := EnvironmentReflect PCUICTerm PCUICEnvironment PCUICTermDecide PCUICEnvironmentDecide.
