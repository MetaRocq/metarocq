(* Distributed under the terms of the MIT license. *)
From Stdlib Require CMorphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICReflect.

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import Morphisms CRelationClasses.
From Equations Require Import Equations.
Set Equations Transparent.

Fixpoint isFixLambda_app (t : term) : bool :=
  match t with
  | tApp (tFix _ _) _ => true
  | tApp (tLambda _ _ _) _ => true
  | tApp f _ => isFixLambda_app f
  | _ => false
  end.

Inductive fix_lambda_app_view : term -> term -> Type :=
| fix_lambda_app_fix mfix i l a : fix_lambda_app_view (mkApps (tFix mfix i) l) a
| fix_lambda_app_lambda na ty b l a : fix_lambda_app_view (mkApps (tLambda na ty b) l) a
| fix_lambda_app_other t a : ~~ isFixLambda_app (tApp t a) -> fix_lambda_app_view t a.
Derive Signature for fix_lambda_app_view.

Lemma view_lambda_fix_app (t u : term) : fix_lambda_app_view t u.
Proof.
  induction t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_lambda na t1 t2 [] u).
  destruct IHt1.
  pose proof (fix_lambda_app_fix mfix i (l ++ [t2]) a).
  change (tApp (mkApps (tFix mfix i) l) t2) with (mkApps (mkApps (tFix mfix i) l) [t2]).
  now rw -mkApps_app.
  pose proof (fix_lambda_app_lambda na ty b (l ++ [t2]) a).
  change (tApp (mkApps (tLambda na ty b) l) t2) with (mkApps (mkApps (tLambda na ty b) l) [t2]).
  now rw -mkApps_app.
  destruct t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_fix mfix idx [] u).
Defined.

Lemma eq_pair_transport {A B} (x y : A) (t : B y) (eq : y = x) :
  (x; eq_rect _ (fun x => B x) t _ eq) = (y; t) :> ∑ x, B x.
Proof.
  now destruct eq.
Qed.

Lemma view_lambda_fix_app_fix_app_sigma mfix idx l a :
  ((mkApps (tFix mfix idx) l); view_lambda_fix_app (mkApps (tFix mfix idx) l) a) =
  ((mkApps (tFix mfix idx) l); fix_lambda_app_fix mfix idx l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rw {1 2}mkApps_app.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tFix mfix idx) l) x) with (mkApps (mkApps (tFix mfix idx) l) [x]).
  now rw eq_pair_transport.
Qed.

Lemma view_lambda_fix_app_lambda_app_sigma na ty b l a :
  ((mkApps (tLambda na ty b) l); view_lambda_fix_app (mkApps (tLambda na ty b) l) a) =
  ((mkApps (tLambda na ty b) l); fix_lambda_app_lambda na ty b l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rw {1 2}mkApps_app.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tLambda na ty b) l) x) with (mkApps (mkApps (tLambda na ty b) l) [x]).
  now rw eq_pair_transport.
Qed.

Set Equations With UIP.

Lemma view_lambda_fix_app_fix_app mfix idx l a :
  view_lambda_fix_app (mkApps (tFix mfix idx) l) a =
  fix_lambda_app_fix mfix idx l a.
Proof.
  pose proof (view_lambda_fix_app_fix_app_sigma mfix idx l a).
  now noconf H.
Qed.

Lemma view_lambda_fix_app_lambda_app na ty b l a :
  view_lambda_fix_app (mkApps (tLambda na ty b) l) a =
  fix_lambda_app_lambda na ty b l a.
Proof.
  pose proof (view_lambda_fix_app_lambda_app_sigma na ty b l a).
  now noconf H.
Qed.

Create Rewrite HintDb rho.
#[global]
Hint Rewrite view_lambda_fix_app_fix_app view_lambda_fix_app_lambda_app : rho.

Equations construct_cofix_discr (t : term) : bool :=
construct_cofix_discr (tConstruct _ _ _) => true;
construct_cofix_discr (tCoFix _ _) => true;
construct_cofix_discr _ => false.
Transparent construct_cofix_discr.

Equations discr_construct_cofix (t : term) : Prop :=
  { | tConstruct _ _ _ => False;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct_cofix.

Inductive construct_cofix_view : term -> Type :=
| construct_cofix_construct ind u i : construct_cofix_view (tConstruct ind u i)
| construct_cofix_cofix mfix idx : construct_cofix_view (tCoFix mfix idx)
| construct_cofix_other t : discr_construct_cofix t -> construct_cofix_view t.

Equations view_construct_cofix (t : term) : construct_cofix_view t :=
{ | tConstruct ind u i => construct_cofix_construct ind u i;
  | tCoFix mfix idx => construct_cofix_cofix mfix idx;
  | t => construct_cofix_other t I }.

Lemma construct_cofix_discr_match {A} t cstr (cfix : mfixpoint term -> nat -> A) default :
  construct_cofix_discr t = false ->
  match t with
  | tConstruct ind c _ => cstr ind c
  | tCoFix mfix idx => cfix mfix idx
  | _ => default
  end = default.
Proof.
  destruct t => //.
Qed.

Equations discr_construct0_cofix (t : term) : Prop :=
  { | tConstruct _ u _ => u <> 0;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct0_cofix.

Inductive construct0_cofix_view : term -> Type :=
| construct0_cofix_construct ind i : construct0_cofix_view (tConstruct ind 0 i)
| construct0_cofix_cofix mfix idx : construct0_cofix_view (tCoFix mfix idx)
| construct0_cofix_other t : discr_construct0_cofix t -> construct0_cofix_view t.

Equations view_construct0_cofix (t : term) : construct0_cofix_view t :=
{ | tConstruct ind 0 i => construct0_cofix_construct ind i;
  | tCoFix mfix idx => construct0_cofix_cofix mfix idx;
  | t => construct0_cofix_other t _ }.

Lemma isFixLambda_app_mkApps t l : isFixLambda_app t -> isFixLambda_app (mkApps t l).
Proof.
  induction l using rev_ind; simpl; auto.
  rw mkApps_app.
  intros isf. specialize (IHl isf).
  simpl. rw IHl. destruct (mkApps t l); auto.
Qed.

Definition isFixLambda (t : term) : bool :=
  match t with
  | tFix _ _ => true
  | tLambda _ _ _ => true
  | _ => false
  end.

Inductive fix_lambda_view : term -> Type :=
| fix_lambda_lambda na b t : fix_lambda_view (tLambda na b t)
| fix_lambda_fix mfix i : fix_lambda_view (tFix mfix i)
| fix_lambda_other t : ~~ isFixLambda t -> fix_lambda_view t.

Lemma view_fix_lambda (t : term) : fix_lambda_view t.
Proof.
  destruct t; repeat constructor.
Qed.

Lemma isFixLambda_app_mkApps' t l x : isFixLambda t -> isFixLambda_app (tApp (mkApps t l) x).
Proof.
  induction l using rev_ind; simpl; auto.
  destruct t; auto. simpl => //.
  intros isl. specialize (IHl isl).
  simpl in IHl.
  now rw mkApps_app /=.
Qed.

Lemma bool_pirr (b b' : bool) (p q : b = b') : p = q.
Proof. noconf p. now noconf q. Qed.

Lemma view_lambda_fix_app_other t u (H : ~~ isFixLambda_app (tApp t u)) :
  view_lambda_fix_app t u = fix_lambda_app_other t u H.
Proof.
  induction t; simpl; f_equal; try apply uip.
  - simpl in H => //.
  - specialize (IHt1 H).
    rw IHt1. destruct t1; auto.
  - simpl in H => //.
Qed.