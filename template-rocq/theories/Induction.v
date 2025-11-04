(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Environment.
From MetaRocq.Template Require Import Ast AstUtils.

(** * Deriving a compact induction principle for terms

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)


(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Prop,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), Forall P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall t : term, P t -> forall (c : cast_kind) (t0 : term), P t0 -> P (tCast t c t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, P t -> forall l : list term, Forall P l -> P (tApp t l)) ->
    (forall s (u : Instance.t), P (tConst s u)) ->
    (forall (i : inductive) (u : Instance.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : Instance.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (t : predicate term),
        tCasePredProp P P t -> forall t0 : term, P t0 -> forall l : list (branch term),
        tCaseBrsProp P l -> P (tCase ci t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall i, P (tInt i)) ->
    (forall f, P (tFloat f)) ->
    (forall s, P (tString s)) ->
    (forall u arr def ty, Forall P arr -> P def -> P ty -> P (tArray u arr def ty)) ->
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t;
    match goal with
      H : _ |- _ => apply H; auto
    end;
    try solve [match goal with
      |- _ P ?arg =>
      revert arg; fix aux_arg 1; intro arg;
        destruct arg; constructor; [|apply aux_arg];
          try split; apply auxt
    end].
  destruct type_info; split; cbn; [|now auto].
  revert pparams; fix aux_pparams 1.
  intros []; constructor; [apply auxt|apply aux_pparams].
Defined.

Lemma term_forall_list_rect :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall t : term, P t -> forall (c : cast_kind) (t0 : term), P t0 -> P (tCast t c t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, P t -> forall l : list term, All P l -> P (tApp t l)) ->
    (forall s (u : Instance.t), P (tConst s u)) ->
    (forall (i : inductive) (u : Instance.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : Instance.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (p0 : predicate term),
        tCasePredProp P P p0 -> forall t : term, P t -> forall l : list (branch term),
        tCaseBrsType P l -> P (tCase ci p0 t l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixType P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixType P P m -> P (tCoFix m n)) ->
    (forall i, P (tInt i)) ->
    (forall f, P (tFloat f)) ->
    (forall s, P (tString s)) ->
    (forall u arr def ty, All P arr -> P def -> P ty -> P (tArray u arr def ty)) ->
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t;
    match goal with
      H : _ |- _ => apply H; auto
    end;
    try solve [match goal with
      |- _ P ?arg =>
      revert arg; fix aux_arg 1; intro arg;
        destruct arg; constructor; [|apply aux_arg];
          try split; apply auxt
    end].
  destruct type_info; split; cbn; [|now auto].
  revert pparams; fix aux_pparams 1.
  intros []; constructor; [apply auxt|apply aux_pparams].
Defined.
