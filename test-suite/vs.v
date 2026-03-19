(* basic.v *)

From Stdlib Require Import BinPos.
From Stdlib Require Import Lia.
From Stdlib Require Import Recdef.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List Orders POrderedType.
From Stdlib Require Import Sorted.
From Stdlib Require Import Sorting.Mergesort.
From Stdlib Require Import Permutation.

Set Implicit Arguments.
Unset Strict Implicit.

Section option.
Variables (A B : Type) (h : A -> B) (f : A -> option B) (o : option A).

Definition omap := match o with Some a => Some (h a) | None => None end.

Definition obnd := match o with Some a => f a | None => None end.

End option.
Arguments omap [A B].
Arguments obnd [A B].

Definition isSome {A : Type} (o : option A) :=
  match o with Some _ => true | _ => false end.

Section comp.
Variables (A B C : Type) (g : B -> C) (f : A -> B) (a : A).

Definition compose := g (f a).

End comp.
Arguments compose [A B C].

(*new notation*)
(*Notation "f \o g" := (compose f g) (at level 54, right associativity).*)

(*for backwards compatibility*)
Infix "oo" := compose (at level 54, right associativity).

Import ListNotations.

Fixpoint zip_with_acc {A B : Type} acc (l1 : list A) (l2 : list B) :=
  match l1, l2 with
    | a :: l1', b :: l2' => (a, b) :: zip_with_acc acc l1' l2'
    | _, _ => acc
  end.

Definition zip {A B : Type} := @zip_with_acc A B [].

Section iter.
Variables (A : Type) (f : nat -> A -> A).

Fixpoint iter (n : nat) (a : A) :=
  match n with
    | O => a
    | S n' => iter n' (f n' a)
  end.

End iter.
Arguments iter [A].

Section tryfind.
Variables (A E B : Type) (f : A -> E + B).

Fixpoint tryfind (err : E) (l : list A) :=
  match l with
    | nil => inl _ err
    | a :: l' => match f a with
                   | inl err' => tryfind err' l'
                   | inr success as r => r
                 end
  end.

End tryfind.

Definition max (n m : nat) := if Nat.leb n m then m else n.

Definition maxs (l : list nat) := fold_left (fun m n => max m n) l 0.

Definition elemb (n : nat) := existsb (fun m => Nat.eqb n m).

(*positive lemmas*)

Lemma Ppred_decrease n : (n<>1)%positive -> (nat_of_P (Pos.pred n)<nat_of_P n)%nat.
Proof.
intros; destruct (Psucc_pred n) as [Hpred | Hpred]; try contradiction;
  pattern n at 2; rewrite <- Hpred; rewrite nat_of_P_succ_morphism; lia.
Defined.

Ltac Ppred_tac n :=
  apply Ppred_decrease; destruct n;
  let H := fresh "H" in intro H; try (inversion H||inversion H1); congruence.

Definition Pleb (x y : positive) :=
  match Pcompare x y Eq with
    | Lt => true
    | Eq => true
    | Gt => false
  end.

Lemma Pleb_Ple (x y : positive) : Pleb x y = true <-> Pos.le x y.
Proof.
unfold Pleb, Pos.le; split; intro H1.
intro H2. unfold Pos.compare in H2. rewrite H2 in H1.
discriminate.
unfold Pos.compare in H1.
destruct (Pos.compare_cont Eq x y); auto.
Qed.

(* N lemmas *)

Definition Nleb (x y : N) :=
  match N.compare x y with
    | Lt => true
    | Eq => true
    | Gt => false
  end.

Lemma Nleb_Nle (x y : N) : Nleb x y = true <-> N.le x y.
Proof.
unfold Nleb, N.le.  split; intro H1.
intro H2. rewrite H2 in H1. discriminate.
remember ((x ?= y)%N) as b; destruct b; auto.
Qed.

(*reverse comparison*)

Section revc.
Variables (A : Type) (c : A -> A -> comparison).

Definition revc a1 a2 :=
  match c a1 a2 with
    | Gt => Lt
    | Eq => Eq
    | Lt => Gt
  end.

End revc.

Inductive ret_kind (val : Type) : Type :=
| Success : val -> ret_kind val
| Failure : ret_kind val.

Arguments Success [val].
Arguments Failure {val}.

(* variables.v *)

Module Ident <: UsualOrderedType := Positive_as_OT.
Definition minid : Ident.t := xH.
Definition id2pos: Ident.t -> positive := fun x => x.
Lemma minid_eq: id2pos minid = 1%positive.
Proof. reflexivity. Qed.
Lemma Ilt_morphism: forall x y, Ident.lt x y -> Pos.lt (id2pos x) (id2pos y).
Proof. auto. Qed.
Definition another_var: Ident.t -> Ident.t := Pos.succ.

Definition Z2id (z : Z) : Ident.t :=
  match z with
    | Z0 => 1%positive
    | Zpos p => Pplus p 1%positive
    | Zneg _ => (* not quite right, but usable for debugging *) 1%positive
  end.

Definition add_id := Pplus.
(* Note: usually "Ident.lt x (another_var x)", but not always,
  if a finite set is used instead of Positive; if you
   are writing an algorithm, make sure by doing the comparison! *)


(** datatypes.v: Datatypes used throughout the development *)

Definition var : Type := Ident.t.

(** expr:
Program expressions *)

Inductive expr := Nil | Var : var -> expr.

(** pn_atom:
Pure (heap-independent) atoms *)

Inductive pn_atom := Equ : expr -> expr -> pn_atom | Nequ : expr -> expr -> pn_atom.

(** space_atom:
Spatial atoms are either next pointers or acyclic list segments. *)

Inductive space_atom :=
| Next : expr -> expr -> space_atom
| Lseg : expr -> expr -> space_atom.

(** assertion:
An assertion is composed of a list of pure atoms [pi], and a list of spatial
atoms [sigma].  [sigma] is interpreted as the _spatial_ conjunction of the
atoms, whereas [pi] asserts the conjunction of its pure atoms. *)

Inductive assertion : Type :=
  Assertion : forall (pi : list pn_atom) (sigma : list space_atom), assertion.

(** entailment:
An entailment is just a pair of assertions. Entailments are interpreted as:
In all models (pairs of heaps [h] and stacks [s]), the interpretation of the
assertion on the left implies the interpretation of the assertion on the right. *)

Inductive entailment : Type :=
  Entailment : assertion -> assertion -> entailment.

(** Various substitution functions:
 *)

Definition subst_var (i: var) (t: expr) (j: var) :=
  if Ident.eq_dec i j then t else Var j.

Definition subst_expr (i: var) (t: expr) (t': expr) :=
  match t' with
    | Nil => Nil
    | Var j => if Ident.eq_dec i j then t else t'
  end.

Definition subst_pn (i: var) (t: expr) (a: pn_atom) :=
 match a with
   | Equ t1 t2 => Equ (subst_expr i t t1) (subst_expr i t t2)
   | Nequ t1 t2 => Nequ (subst_expr i t t1) (subst_expr i t t2)
 end.

Definition subst_pns (i: var) (t: expr) (pa: list pn_atom)
  : list pn_atom := map (subst_pn i t) pa.

Definition subst_space (i: var) (t: expr) (a: space_atom) :=
  match a with
    | Next t1 t2 => Next (subst_expr i t t1) (subst_expr i t t2)
    | Lseg t1 t2 => Lseg (subst_expr i t t1) (subst_expr i t t2)
  end.

Definition subst_spaces (i: var) (t: expr)
  : list space_atom -> list space_atom := map (subst_space i t).

Definition subst_assertion (i: var) (e: expr) (a: assertion) :=
 match a with Assertion pi sigma =>
   Assertion (subst_pns i e pi) (subst_spaces i e sigma)
 end.

(* compare.v *)

Definition StrictCompSpec {A} (eq lt: A -> A -> Prop)
                          (cmp: A -> A -> comparison) :=
  StrictOrder lt /\ forall x y, CompSpec eq lt x y (cmp x y).

Definition CompSpec' {A} (cmp: A -> A -> comparison) :=
   StrictCompSpec (@Logic.eq A) (fun x y => Lt = cmp x y) cmp.

Ltac do_comp cspec x y := destruct (CompSpec2Type (proj2 cspec x y)).

Lemma lt_comp: forall {A} lt cmp,
             StrictCompSpec Logic.eq lt cmp ->
             forall x y: A,  (lt x y <-> Lt = cmp x y).
Proof.
intros.
  generalize H; intros [[?H ?H] _].
  do_comp H x y; intuition; subst; try discriminate; auto.
  contradiction (H0 y).
  contradiction (H0 _ (H1 _ _ _ l H2)).
Qed.

Lemma eq_comp: forall {A} lt cmp,
        StrictCompSpec Logic.eq lt cmp ->
       forall x y: A,   (x = y <-> Eq = cmp x y).
Proof.
 intros.
  generalize H; intros [[?H ?H] _].
  do_comp H x y; intuition; subst; try discriminate; auto;
  contradiction (H0 y).
Qed.

Lemma gt_comp: forall {A} lt cmp,
        StrictCompSpec Logic.eq lt cmp ->
        forall x y: A,   (lt x y <-> Gt = cmp y x).
Proof.
intros.
  generalize H; intros [[?H ?H] _].
  do_comp H x y; intuition; subst; try discriminate; auto.
  contradiction (H0 y).
  destruct (eq_comp H y y).
  rewrite <- H3 in H2; auto. inversion H2.
  do_comp H y x; subst; auto.
  contradiction (H0 x).
  contradiction (H0 _ (H1 _ _ _ l0 H2)).
  contradiction (H0 _ (H1 _ _ _ l H2)).
  rewrite (lt_comp H) in l; eauto.
  rewrite <- H2 in l; inversion l.
Qed.

Lemma comp_refl: forall {A} (cmp: A -> A -> comparison) (cspec: CompSpec' cmp),
      forall x, cmp x x = Eq.
Proof.
 intros.
 do_comp cspec x x; auto.
 destruct cspec as [[H _] _].
 contradiction (H _ e).
 destruct cspec as [[H _] _].
 contradiction (H _ e).
Qed.


Lemma comp_trans:  forall {A} (cmp: A -> A -> comparison) (cspec: CompSpec' cmp),
      forall x y z, Lt = cmp x y -> Lt = cmp y z -> Lt = cmp x z.
Proof.
 intros.
 destruct cspec as [[_ ?H] _].
 eapply H1; eauto.
Qed.

Definition isGe (c: comparison) := match c with Lt => False | _ => True end.
Definition isGeq cc := match cc with Lt => false | _ => true end.


Fixpoint insert {A: Type} (cmp: A -> A -> comparison) (a: A) (l: list A)
  : list A:=
  match l with
  | h :: t => if isGeq (cmp a h)
                 then a :: l
                 else h :: (insert cmp a t)
  | nil => a :: nil
  end.

Fixpoint rsort {A: Type} (cmp: A -> A -> comparison) (l: list A) : list A :=
  match l with nil => nil | h::t => insert cmp h (rsort cmp t)
  end.

Fixpoint insert_uniq {A: Type} (cmp: A -> A -> comparison) (a: A) (l: list A)
  : list A:=
  match l with
  | h :: t => match cmp a h with
              | Eq => l
              | Gt => a :: l
              | Lt => h :: (insert_uniq cmp a t)
              end
  | nil => a::nil
  end.

Fixpoint rsort_uniq {A: Type} (cmp: A -> A -> comparison) (l: list A)
  : list A :=
  match l with nil => nil | h::t => insert_uniq cmp h (rsort_uniq cmp t)
  end.

(*put somewhere else, maybe in datatypes.v*)
Lemma perm_insert {T} cmp (a : T) l : Permutation (insert cmp a l) (a :: l).
Proof with auto.
induction l; simpl; auto.
destruct (isGeq (cmp a a0)); try repeat constructor.
apply Permutation_refl.
apply Permutation_sym; apply Permutation_trans with (l' := a0 :: a :: l).
apply perm_swap. constructor; apply Permutation_sym...
Qed.

Fixpoint compare_list {A: Type} (f: A -> A -> comparison) (xl yl : list A)
  : comparison :=
  match xl , yl with
  | x :: xl', y :: yl' => match f x y with
                          | Eq => compare_list f xl' yl'
                          | c => c
                          end
  | nil , _ :: _ => Lt
  | _ :: _ , nil => Gt
  | nil, nil => Eq
  end.

Lemma Forall_sortu:
  forall  {A} (f: A -> Prop) (cmp: A -> A -> comparison) l,
    Forall f l -> Forall f  (rsort_uniq cmp l).
Proof.
induction l;  intros; try constructor.
simpl.
inversion  H; clear H; subst.
specialize (IHl H3).
clear H3; induction IHl.
simpl; constructor; auto.
simpl.
destruct (cmp a x); constructor; auto.
Qed.

Lemma rsort_uniq_in:
  forall {A} (R: A -> A -> comparison)
          (EQ: forall a b, (a=b) <-> (Eq = R a b))
          x l,
      List.In x (rsort_uniq  R l) <-> List.In x l.
Proof.
induction l; simpl; intros.
intuition.
rewrite <- IHl.
remember (rsort_uniq R l) as l'.
clear - EQ.
induction l'; simpl. intuition.
case_eq (R a a0); intros; simpl in *; subst; intuition.
symmetry in H; rewrite <- EQ in H.
simpl; subst; intuition.
Qed.



(* clauses.v *)
Unset Implicit Arguments.

From Stdlib Require Import ZArith List Recdef MSets.MSetInterface Sorting.Mergesort
               Permutation MSets.MSetAVL MSets.MSetRBT.

(** The clause datatype and related definitions and lemmas *)

(** pure_atom:
pure atoms *)

Inductive pure_atom := Eqv : expr -> expr -> pure_atom.

Local Definition var1 : var := Z2id 1.
Local Definition var0 : var := Z2id 0.
Local Definition var2 : var := Z2id 2.

Fixpoint list_prio {A} (weight: var) (l: list A) (p: var) : var :=
  match l with
  | nil => p
  | _::l' => list_prio weight l' (add_id weight p)
  end.

(** Weight the positive atoms 1 each, and the negative atoms 2 each.
    Then the highest-priority terms will be the positive unit clauses *)

Definition prio (gamma delta: list pure_atom) : var :=
    list_prio var2 gamma (list_prio var1 delta var0).

(** clause:
clauses are either pure (no spatial atoms), negative spatial (spatial atom on the left)
or positive spatial. *)

Inductive clause : Type :=
| PureClause : forall (gamma : list pure_atom) (delta : list pure_atom)
                         (priority : var)
                         (prio_ok: prio gamma delta = priority), clause
| PosSpaceClause : forall (gamma : list pure_atom) (delta : list pure_atom)
  (sigma : list space_atom), clause
| NegSpaceClause : forall (gamma : list pure_atom) (sigma : list space_atom)
  (delta : list pure_atom), clause.

Definition expr_cmp e e' : comparison :=
 match e, e' with
   | Nil , Nil => Eq
   | Nil, _ => Lt
   | _, Nil => Gt
   | Var v, Var v' => Ident.compare v v'
 end.

Lemma expr_cmp_rfl:
  forall e:expr, expr_cmp e e = Eq.
Proof.
  destruct e; try reflexivity.
  cbn. apply (proj2 (Pos.compare_eq_iff v v)). reflexivity.
Qed.

Lemma var_cspec : StrictCompSpec (@Logic.eq var) Ident.lt Ident.compare.
Proof. split; [apply Ident.lt_strorder|apply Ident.compare_spec]. Qed.
#[global]
Hint Resolve var_cspec : core.

Definition pure_atom_cmp (a a': pure_atom) : comparison :=
 match a, a' with
   | Eqv e1 e2, Eqv e1' e2' =>
     match expr_cmp e1 e1' with
       Eq => expr_cmp e2 e2' | c => c
     end
 end.

Lemma pure_atom_cmp_rfl:
  forall a:pure_atom, pure_atom_cmp a a = Eq.
Proof.
  destruct a. cbn. rewrite expr_cmp_rfl. rewrite expr_cmp_rfl. reflexivity.
Qed.

Lemma compare_list_pure_atom_cmp_rfl:
  forall delta, compare_list pure_atom_cmp delta delta = Eq.
Proof.
  induction delta. try reflexivity.
  cbn. rewrite pure_atom_cmp_rfl. assumption.
Qed.

Local Hint Rewrite @comp_refl using solve[auto] : comp.

Ltac comp_tac :=
    progress (autorewrite with comp in *; auto)
  || discriminate
  || solve [eapply comp_trans;  eauto]
  || subst
 || match goal with
  | H: Lt = ?A |- context [?A] => rewrite <- H
  | H: Gt = ?A |- context [?A] => rewrite <- H
  | H: Eq = ?A |- context [?A] => rewrite <- H
 end.


(** ordering expressions, atoms and clauses *)

Definition expr_order (t t': expr) := isGe (expr_cmp t t').

Inductive max_expr (t : expr) : pure_atom -> Prop :=
| mexpr_left : forall t', expr_order t t' -> max_expr t (Eqv t t')
| mexpr_right : forall t', expr_order t t' -> max_expr t (Eqv t' t).

Definition order_eqv_pure_atom (a: pure_atom) :=
  match a with
    | Eqv i j => match expr_cmp i j with Lt => Eqv j i | _ => Eqv i j end
  end.

Definition nonreflex_atom a :=
  match a with Eqv i j => match expr_cmp i j with Eq => false | _ => true end
  end.

Definition normalize_atoms pa :=
  rsort_uniq pure_atom_cmp (map order_eqv_pure_atom pa).

Definition mkPureClause (gamma delta: list pure_atom) : clause :=
  PureClause gamma delta _ (eq_refl _).

Definition order_eqv_clause (c: clause) :=
  match c with
  | PureClause pa pa' _ _ =>
    mkPureClause (normalize_atoms (filter nonreflex_atom pa))
                 (normalize_atoms pa')
  | PosSpaceClause pa pa' sa' =>
    PosSpaceClause (normalize_atoms (filter nonreflex_atom pa))
                   (normalize_atoms pa') sa'
  | NegSpaceClause pa sa pa' =>
    NegSpaceClause (normalize_atoms (filter nonreflex_atom pa)) sa
                   (normalize_atoms pa')
  end.

Definition mk_pureL (a: pn_atom) : clause :=
 match a with
 | Equ x y => mkPureClause nil (order_eqv_pure_atom(Eqv x y)::nil)
 | Nequ x y => mkPureClause (order_eqv_pure_atom(Eqv x y)::nil) nil
 end.

Fixpoint mk_pureR (al: list pn_atom) : list pure_atom * list pure_atom :=
 match al with
 | nil => (nil,nil)
 | Equ x y :: l' => match mk_pureR l' with (p,n) =>
                      (order_eqv_pure_atom(Eqv x y)::p, n) end
 | Nequ x y :: l' => match mk_pureR l' with (p,n) =>
                       (p, order_eqv_pure_atom(Eqv x y)::n) end
 end.

(** cnf:
clausal normal form *)

Definition cnf (en: entailment) : list clause :=
 match en with
  Entailment (Assertion pureL spaceL) (Assertion pureR spaceR) =>
   match mk_pureR pureR with (p,n) =>
     map mk_pureL pureL ++ (PosSpaceClause nil nil spaceL :: nil) ++
       match spaceL, spaceR with
       | nil, nil => mkPureClause p n :: nil
       | _, _ => NegSpaceClause p spaceR n :: nil
       end
   end
  end.

(** various comparison functions *)

Definition pure_atom_geq a b := isGeq (pure_atom_cmp a b).
Definition pure_atom_gt a b := match pure_atom_cmp a b with Gt => true | _ => false end.
Definition pure_atom_eq a b := match pure_atom_cmp a b with Eq => true | _ => false end.
Definition expr_lt a b := match expr_cmp a b with Lt => true | _ => false end.
Definition expr_eq a b := match expr_cmp a b with Eq => true | _ => false end.
Definition expr_geq a b := match expr_cmp a b with Lt => false | _ => true end.

Definition norm_pure_atom (a : pure_atom) :=
  match a with
    | Eqv i j => if expr_lt i j then Eqv j i else Eqv i j
  end.

Definition subst_pure (i: var) (t: expr) (a: pure_atom) :=
 match a with
   | Eqv t1 t2 => Eqv (subst_expr i t t1) (subst_expr i t t2)
 end.

Definition subst_pures (i: var) (t: expr) (pa: list pure_atom)
  : list pure_atom := map (subst_pure i t) pa.

Definition compare_space_atom (a b : space_atom) : comparison :=
 match a , b with
  | Next i j , Next i' j' => match expr_cmp i i' with Eq => expr_cmp j j' | c => c end
  | Next i j, Lseg i' j' =>
    match expr_cmp i i' with
    | Lt => Lt
    | Eq => Lt
    | Gt => Gt
    end
  | Lseg i j, Next i' j' =>
    match expr_cmp i i' with
    | Lt => Lt
    | Eq => Gt
    | Gt => Gt
    end
  | Lseg i j , Lseg i' j' => match expr_cmp i i' with Eq => expr_cmp j j' | c => c end
  end.


Definition compare_clause (cl1 cl2 : clause) : comparison :=
  match cl1 , cl2 with
  | PureClause neg pos _ _ , PureClause neg' pos' _ _ =>
    match compare_list pure_atom_cmp neg neg' with
    | Eq => compare_list pure_atom_cmp pos pos'
    | c => c
    end
  | PureClause _ _ _ _ , _ => Lt
  | _ , PureClause _ _ _ _ => Gt
  | PosSpaceClause gamma delta sigma , PosSpaceClause gamma' delta' sigma'
  | NegSpaceClause gamma sigma delta , NegSpaceClause gamma' sigma' delta' =>
    match compare_list pure_atom_cmp gamma gamma' with
    | Eq => match compare_list pure_atom_cmp delta delta' with
                 | Eq => compare_list compare_space_atom sigma sigma'
                 | c => c
                 end
    | c => c
    end
  | PosSpaceClause _ _ _ , NegSpaceClause _ _ _ => Lt
  | NegSpaceClause _ _ _ , PosSpaceClause _ _ _ => Gt
  end.

(***
Lemma compare_clause_rfl:
  forall (cl:clause), compare_clause cl cl = Eq.
Proof.
  destruct cl; subst.
  - induction gamma, delta; try reflexivity.
    + cbn. rewrite pure_atom_cmp_rfl.
      rewrite compare_list_pure_atom_cmp_rfl. reflexivity.
    + cbn. rewrite pure_atom_cmp_rfl.
      rewrite compare_list_pure_atom_cmp_rfl. reflexivity.
    + cbn. rewrite pure_atom_cmp_rfl.
      rewrite compare_list_pure_atom_cmp_rfl.
      rewrite pure_atom_cmp_rfl.
      rewrite compare_list_pure_atom_cmp_rfl. reflexivity.
  -
****)

Definition rev_cmp {A : Type} (cmp : A -> A -> comparison) :=
  fun a b => match cmp a b with Eq => Eq | Lt => Gt | Gt => Lt end.

Lemma rev_cmp_eq : forall {A : Type} (cmp : A -> A -> comparison) (x y : A),
  (forall x0 y0 : A, Eq = cmp x0 y0 -> x0 = y0) ->
  Eq = rev_cmp cmp x y -> x = y.
Proof.
intros until y; intros H H1.
unfold rev_cmp in H1. remember (cmp x y) as b.
destruct b;try solve[congruence].
apply H; auto.
Qed.

Definition prio1000 := Z2id 1000.
Definition prio1001 := Z2id 1001.

Definition clause_prio (cl : clause) : var :=
  match cl with
  | PureClause gamma delta prio _ => prio
  | PosSpaceClause _ _ _ => prio1000
  | NegSpaceClause gamma sigma delta => prio1001
  end%Z.


Definition compare_clause' (cl1 cl2 : clause) : comparison :=
  match Ident.compare (clause_prio cl1) (clause_prio cl2) with
  | Eq => compare_clause cl1 cl2
  | c => c
  end.

Lemma clause_cspec': CompSpec' compare_clause'.
Proof.
  unfold compare_clause', CompSpec', StrictCompSpec. split. constructor.
  - unfold Irreflexive, Reflexive, complement. intros.
    rewrite (proj2 (Pos.compare_eq_iff _ _)) in H; try reflexivity.
    admit.
  - admit.
  - intros. unfold CompSpec. admit.
Admitted.
#[global]
Hint Resolve clause_cspec' : core.

Definition clause_length (cl : clause) : Z :=
  match cl with
  | PureClause gamma delta _ _ => Zlength gamma + Zlength delta
  | PosSpaceClause gamma delta sigma =>
      Zlength gamma + Zlength delta + Zlength sigma
  | NegSpaceClause gamma sigma delta =>
      Zlength gamma + Zlength sigma + Zlength delta
  end%Z.

Definition compare_clause_length (cl1 cl2 : clause) :=
   Z.compare (clause_length cl1) (clause_length cl2).

Definition compare_clause'1 (cl1 cl2 : clause) : comparison :=
  match compare_clause_length cl1 cl2 with
  | Eq => compare_clause cl1 cl2
  | c => c
  end.


Module OrderedClause <: OrderedType
  with Definition t:=clause
  with Definition compare:=compare_clause'.

Definition t := clause.

Definition eq : clause -> clause -> Prop := Logic.eq.

Lemma eq_equiv : Equivalence eq.
Proof.  apply eq_equivalence. Qed.

Definition lt (c1 c2 : clause) := Lt = compare_clause' c1 c2.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof.
intros. constructor; unfold eq in H,H0; subst; auto.
Qed.

Definition compare := compare_clause'.

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.  destruct clause_cspec'; auto. Qed.

Lemma eq_dec : forall x y, {eq x y}+{~eq x y}.
Proof.
intros; unfold eq.
remember (compare x y) as j; destruct j.
destruct (CompSpec2Type (compare_spec x y)); try discriminate. left; auto.
right; intro; subst.
unfold compare in Heqj; rewrite comp_refl in Heqj; auto.
inversion Heqj.
do_comp clause_cspec' x y; subst; auto.
right; intro; subst. rewrite comp_refl in e; auto. inversion e.
right; intro; subst. rewrite comp_refl in e; auto. inversion e.
Defined.

Lemma lt_strorder : StrictOrder lt.
Proof. destruct clause_cspec'; auto. Qed.

End OrderedClause.

(* The clause database.  There are two alternate implementations.
  The first uses MSetAVL from the Rocq library, the second uses red-black trees.
  Since red-black trees match an enhanced interface MSetPlus,
  in the first implementation we define the additional operator(s) in terms
  of what's available in MSetAVL.
*)

(* First implementation *)

Module M1 : MSetInterface_S_Ext
   with Definition E.t := OrderedClause.t
   with Definition E.compare := OrderedClause.compare
   with Definition E.eq := OrderedClause.eq
   with Definition E.lt := OrderedClause.lt
   with Definition E.compare := OrderedClause.compare.
 Include MSetAVL.Make(OrderedClause).
 Definition remove_min (s: t) : option (elt * t) :=
   match min_elt s with
   | Some x => Some (x, remove x s)
   | None => None
  end.
 Lemma remove_min_spec1x: forall (s: t) k s',
    remove_min s = Some (k,s')  <->
    (min_elt s = Some k /\ remove k s = s').
  Proof.
   intros. unfold remove_min.
   case_eq (min_elt s); intros.
   intuition. inversion H0; clear H0; subst; auto.
     inversion H0; clear H0; subst; auto. inversion H1; clear H1; subst; auto.
     intuition; discriminate.
  Qed.
 Lemma remove_min_spec1: forall (s: t) k s',
    remove_min s = Some (k,s')  ->
    (min_elt s = Some k /\ Equal (remove k s) s').
 Proof. intros.
 destruct (remove_min_spec1x s k s') as [? _].
 destruct (H0 H); clear H0 H. split; auto. rewrite H2; intuition; auto with *.
 Qed.
 Lemma remove_min_spec2x: forall s, remove_min s = None <-> Empty s.
 Proof. unfold remove_min; intros.
   case_eq (min_elt s); intros.
  intuition; try discriminate.
  apply min_elt_spec1 in H.
  apply H0 in H; contradiction.
  apply min_elt_spec3 in H.
  intuition.
  Qed.
 Lemma remove_min_spec2: forall s, remove_min s = None -> Empty s.
 Proof. intros; apply remove_min_spec2x; auto.
 Qed.
Definition mem_add (x: elt) (s: t) : option t :=
 if mem x s then None else Some (add x s).

Lemma mem_add_spec:
    forall x s, mem_add x s = if mem x s then None else Some (add x s).
Proof. auto. Qed.
End M1.

(* Second implementation *)
Module M := MSetRBT.Make(OrderedClause).

Definition clause_list2set (l : list clause) : M.t :=
  fold_left (fun s0 c => M.add c s0) l M.empty.

Definition empty_clause : clause := mkPureClause nil nil.

Definition remove_trivial_atoms := filter (fun a =>
  match a with
  | Eqv e1 e2 => match expr_cmp e1 e2 with
                 | Eq => false
                 | _ => true
                 end
  end).

Definition subst_pures_delete (i: var) (e: expr)
  : list pure_atom -> list pure_atom :=
  remove_trivial_atoms oo subst_pures i e.

Definition isEq cc := match cc with Eq => true | _ => false end.

Definition eq_space_atom (a b : space_atom) : bool :=
  isEq (compare_space_atom a b).

Definition eq_space_atomlist (a b : list space_atom) : bool :=
  isEq (compare_list compare_space_atom a b).

Definition eq_var i j : bool := isEq (Ident.compare i j).

Definition drop_reflex_lseg : list space_atom -> list space_atom :=
  filter (fun sa =>
                    match sa with
                    | Lseg (Var x) (Var y) => negb (eq_var x y)
                    | Lseg Nil Nil => false
                    | _ => true
                    end).

Definition order_eqv_pure_atoms := map order_eqv_pure_atom.

Definition greater_than_expr (i: var) (e: expr) :=
  match e with Var j => match Ident.compare i j with Gt => true | _ => false end
                        | Nil => true
  end.

Definition greatereq_than_expr (i: var) (e: expr) :=
  match e with
  | Var j => match Ident.compare i j with Gt => true | Eq => true | Lt => false
             end
  | Nil => true
  end.

Definition greater_than_atom (s u : pure_atom) :=
  match s , u with
  | Eqv s t , Eqv u v =>
    ((expr_lt u s && (expr_geq s v || expr_geq t v)) ||
      (expr_lt v s && (expr_geq s u || expr_geq t u))) ||
    ((expr_lt u t && (expr_geq s v || expr_geq t v)) ||
      (expr_lt v t && (expr_geq s u || expr_geq t u)))
  end.

Definition greater_than_atoms (s : pure_atom) (delta : list pure_atom) :=
  forallb (fun u => greater_than_atom s u) delta.

Definition greater_than_all (i: var) : list pure_atom -> bool :=
  forallb (fun a => match a with Eqv x y =>
             andb (greater_than_expr i x) (greater_than_expr i y) end).

Definition subst_clause i e cl : clause :=
  match cl with
  | PureClause pa pa' _ _ =>
      mkPureClause (subst_pures_delete i e pa) (subst_pures i e pa')
  | NegSpaceClause pa sa pa' =>
      NegSpaceClause (subst_pures_delete i e pa) (subst_spaces i e sa)
                     (subst_pures i e pa')
  | PosSpaceClause pa pa' sa' =>
      PosSpaceClause (subst_pures_delete i e pa) (subst_pures i e pa')
                     (subst_spaces i e sa')
  end.


(* general functions that should be moved elsewhere *)

Definition ocons {A : Type} (o : option A) l :=
  match o with Some a => a :: l | None => l end.

Fixpoint omapl {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | a :: l' => ocons (f a) (omapl f l')
  | nil => nil
  end.

Fixpoint merge {A: Type} (cmp : A -> A -> comparison) l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      match cmp a1 a2 with
      | Eq => a1 :: merge cmp l1' l2'
      | Gt => a1 :: merge cmp l1' l2
      | _ => a2 :: merge_aux l2' end
  end
  in merge_aux l2.

Abbreviation sortu_atms := (rsort_uniq pure_atom_cmp).
Abbreviation insu_atm := (insert_uniq pure_atom_cmp).
Abbreviation sortu_clauses := (rsort_uniq compare_clause).

Lemma pure_clause_ext:
  forall gamma delta p Pp p' Pp',
     PureClause gamma delta p Pp = PureClause gamma delta p' Pp'.
Proof.
  intros. subst. auto.
Qed.

Lemma mem_spec': forall s x, M.mem x s = false <-> ~M.In x s.
Proof.
 intros. rewrite <- M.mem_spec. destruct (M.mem x s); intuition discriminate.
Qed.

Lemma is_empty_spec': forall s, M.is_empty s = false <-> ~M.Empty s.
Proof.
 intros. rewrite <- M.is_empty_spec. destruct (M.is_empty s); intuition discriminate.
Qed.

Lemma empty_set_elems':
  forall s, M.Empty s <-> M.elements s = nil.
Proof.
intros.
generalize (M.elements_spec1 s); intro.
destruct (M.elements s); intuition.
intros ? ?.
rewrite <- H in H1.
inversion H1.
contradiction (H0 e).
rewrite <- H. left; auto.
inversion H0.
Qed.

Lemma Melements_spec1: forall (s: M.t) x, List.In x (M.elements s) <-> M.In x s.
Proof.
intros.
rewrite <- M.elements_spec1.
induction (M.elements s); intuition;
try solve [inversion H].
simpl in H1. destruct H1; subst.
constructor; auto.
constructor 2; auto.
inversion H1; clear H1; subst; simpl; auto.
Qed.

From Stdlib Require Import Finite_sets_facts.

(* from msl/Axioms.v: *)

(** This file collects some axioms used throughout the Mechanized Semantic Library development.
  This file was developed in 2010 by Andrew W. Appel and Xavier Leroy, and harmonizes
  the axioms used by MSL and by the CompCert project.
 *)

Require Stdlib.Logic.ClassicalFacts.

(** * Extensionality axioms *)

(** The following [Require Export] gives us functional extensionality for dependent function types:
<<
Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
>>
and, as a corollary, functional extensionality for non-dependent functions:
<<
Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
>>
*)
Require Export Stdlib.Logic.FunctionalExtensionality.

(** For compatibility with earlier developments, [extensionality]
  is an alias for [functional_extensionality]. *)

Lemma extensionality:
  forall (A B: Type) (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. intros; apply functional_extensionality. auto. Qed.

(** We also assert propositional extensionality. *)

Axiom prop_ext: ClassicalFacts.prop_extensionality.

(** * Proof irrelevance *)

(** We also use proof irrelevance, which is a consequence of propositional
    extensionality. *)

Lemma proof_irr: ClassicalFacts.proof_irrelevance.
Proof.
  exact (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.

(* end msl/Axioms.v *)

Lemma Mcardinal_spec': forall s,   cardinal _ (Basics.flip M.In s) (M.cardinal s).
Proof.
 intros.
 rewrite (M.cardinal_spec s).
 generalize (M.elements_spec1 s); intro.
 replace (Basics.flip M.In s) with (Basics.flip (@List.In _) (M.elements s)).
 2:{
unfold Basics.flip; apply extensionality; intro x;
apply prop_ext; rewrite <- (H x).
clear; intuition.
apply SetoidList.In_InA; auto.
apply eq_equivalence.
rewrite SetoidList.InA_alt in H.
destruct H as [? [? ?]].
subst; auto. }
 clear H.
 generalize (M.elements_spec2w s); intro.
 remember (M.elements s) as l.
 clear s Heql.
 induction H.
 replace (Basics.flip (@List.In M.elt) (@nil clause)) with (@Empty_set M.elt).
 constructor 1.
 apply extensionality; intro; apply prop_ext; intuition; inversion H.
 simpl.
 replace (Basics.flip (@List.In M.elt) (@cons clause x l))
   with (Add M.elt (Basics.flip (@List.In _) l) x).
 constructor 2; auto.
 contradict H.
 simpl.
 apply SetoidList.In_InA; auto.
 apply eq_equivalence.
 clear.
 apply extensionality; intro; apply prop_ext; intuition.
 unfold Basics.flip; simpl.
 unfold Add in H. destruct H; auto.
 apply Singleton_inv in H. auto.
 simpl in H; destruct H; [right | left].
 apply Singleton_intro. auto.
 apply H.
Qed.

Lemma remove_decreases:
  forall giv unselected,
  M.In giv unselected ->
  M.cardinal  (M.remove giv unselected)  < M.cardinal  unselected.
Proof.
 intros.
 generalize (Mcardinal_spec' (M.remove giv unselected)); intro.
 generalize (Mcardinal_spec' unselected); intro.
 generalize (card_soustr_1 _ _ _ H1 _ H); intro.
 rewrite (cardinal_is_functional _ _ _ H0 _ _ H2).
 assert (M.cardinal unselected > 0).
 generalize (Mcardinal_spec' unselected); intro.
 inversion H3; clear H3; subst.
 assert (Empty_set M.elt giv). rewrite H5. unfold Basics.flip. auto.
 inversion H3.
 lia.
 lia.
 clear - H.
 apply extensionality;  intro x.
 unfold Basics.flip at 1.
 apply prop_ext; intuition.
rewrite M.remove_spec in H0.
destruct H0.
split.
unfold In, Basics.flip. auto.
intro.
apply Singleton_inv in H2.
subst. contradiction H1; auto.
destruct H0.
rewrite M.remove_spec.
split; auto.
intro.
subst.
apply H1; apply Singleton_intro.
auto.
Qed.

(** a second comparison function on clauses that meets the requirements
   of model generation *)

Definition pure_atom2pn_atom (b : bool) (a : pure_atom) :=
  match a with
  | Eqv e1 e2 => if b then Equ e1 e2 else Nequ e1 e2
  end.

Definition pn_atom_cmp (a1 a2 : pn_atom) : comparison :=
  match a1, a2 with
  | Equ e1 e2, Equ e1' e2' => pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  | Nequ e1 e2, Equ e1' e2' =>
    if expr_eq e1 e1' then Gt else pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  | Equ e1 e2, Nequ e1' e2' =>
    if expr_eq e1 e1' then Lt else pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  | Nequ e1 e2, Nequ e1' e2' => pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  end.

Definition pure_clause2pn_list (c : clause) :=
  match c with
  | PureClause gamma delta _ _ =>
    rsort pn_atom_cmp
      (map (pure_atom2pn_atom false) gamma ++ map (pure_atom2pn_atom true) delta)
  | _ => nil
  end.

Definition compare_clause2 (cl1 cl2 : clause) :=
  match cl1, cl2 with
  | PureClause _ _ _ _, PureClause _ _ _ _ =>
    compare_list pn_atom_cmp (pure_clause2pn_list cl1) (pure_clause2pn_list cl2)
  | _, _ => compare_clause cl1 cl2
  end.


Inductive ce_type := CexpL | CexpR | CexpEf.

(** Patch until Rocq extraction of sharing constraints is fixed *)

Module DebuggingHooks.

(* To add a new debugging hook, do the following:
   -define a new function equal to the identity on the type of whatever
   value you want to report
   -define a corresponding ML function with the same name in
     extract/debugging.ml to do the actual reporting
*)
Definition print_new_pures_set (s: M.t) := s.

Definition print_wf_set (s: M.t) := s.

Definition print_unfold_set (s: M.t) := s.

Definition print_inferred_list (l: list clause) := l.

Definition print_pures_list (l: list clause) := l.

Definition print_eqs_list (l: list clause) := l.

Definition print_spatial_model (c: clause) (R: list (var * expr)) := c.

Definition print_spatial_model2 (c c': clause) (R: list (var * expr)) := c'.

Definition print_ce_clause (R: list (var * expr)) (cl : clause) (ct : ce_type)
  := (R, cl, ct).

End DebuggingHooks.

Export DebuggingHooks.

#[global]
Hint Unfold print_new_pures_set print_wf_set print_inferred_list print_spatial_model
            print_pures_list print_eqs_list
  : DEBUG_UNFOLD.

(* model_type.v *)

(* cclosure.v *)
(** A little module for doing naive congruence closure; we don't need anything
    much fancier because in practice, for spatial entailments, we only discover
    a few new equalities in each call to the superposition subsystem.

    Pure entailments are another matter entirely, but for now we seem to be fine
    on those (see, eg, test/test.pure.entailments.sf) *)

Section cclosure.
Context (A B : Type).
Variables
  (A_cmp : A -> A -> comparison)
  (B_cmp : B -> B -> comparison)
  (fAB : A -> B).

Abbreviation canons := (list (A*B)).

(*Definition isEq (c : comparison) := match c with Eq => true | _ => false end.*)

Fixpoint lookC (a: A) (cs: canons) : B :=
  match cs with nil => fAB a
  | (a1, b1)::cs' => if isEq (A_cmp a a1) then b1
                     else lookC a cs'
  end.

Fixpoint rewriteC (b1 b2 : B) (cs: canons) : canons :=
  match cs with nil => nil
  | (a1, b1')::cs' =>
    let new_cs := rewriteC b1 b2 cs' in
    if isEq (B_cmp b1 b1') then (a1, b2)::new_cs else (a1, b1')::new_cs end.

Definition mergeC (a1 a2 : A) (cs: canons) : canons :=
  match lookC a1 cs, lookC a2 cs with b1, b2 =>
    if isEq (B_cmp b1 b2) then cs
    else (a1, b2)::(a2, b2)::rewriteC b1 b2 cs end.

End cclosure.

Abbreviation expr_get := (lookC _ _ expr_cmp (@id _)).
Abbreviation expr_merge := (mergeC _ _ expr_cmp expr_cmp (@id _)).

(* used internally *)
Local Abbreviation expr_rewriteC := (rewriteC expr _ expr_cmp).

Fixpoint cclose_aux (l : list clause) : list (expr * expr) :=
  match l with
  | PureClause nil [Eqv s t] _ _ :: l' => expr_merge s t (cclose_aux l')
  | _ => nil
  end.

Definition cclose (l : list clause) : list clause :=
  map (fun p => match p with (e1, e2) => mkPureClause nil [Eqv e1 e2] end)
    (cclose_aux l).

(* superpose_modelsat.v *)

Module Type SUPERPOSITION.

Definition model := list (var * expr).

Inductive superposition_result : Type :=
| Valid : superposition_result
| C_example : model -> M.t -> superposition_result
| Aborted : list clause -> superposition_result.

(** check:
-Check a pure entailment of the form [Pi ==> Pi']
-Returns, when a [C_example] is found, the model exhibiting the [C_example] and
 the final clause set (i.e., the set of clauses derived during proof search)
*)

Parameter check : entailment -> superposition_result * list clause * M.t*M.t.

(** check_clauseset:
Just like check, except we operate instead on an initial _set_ of clauses.
This function is the one called by the main theorem prover, veristar.v. *)

Parameter check_clauseset : M.t -> superposition_result * list clause * M.t*M.t.

(** is_model_of_PI:
Check whether R is a model of Pi+ /\ Pi-; used in the Veristar main loop *)

Parameter is_model_of_PI : model -> clause -> bool.

Parameter rewrite_by : expr -> expr -> pure_atom -> pure_atom.

Parameter demodulate : clause -> clause -> clause.

Parameter simplify : list clause -> clause -> clause.

Parameter simplify_atoms : list clause -> list space_atom -> list space_atom.

End SUPERPOSITION.

(** Module Superposition:
 *)

Module Superposition <: SUPERPOSITION.

Definition model := list (var * expr).

Inductive superposition_result : Type :=
| Valid : superposition_result
| C_example : model -> M.t -> superposition_result
| Aborted : list clause -> superposition_result.

(* side condition used in superposition rules below *)
(* begin hide *)
Definition pure_atom_gt1 a (l: list pure_atom) :=
  match l with b :: _ => pure_atom_gt a b | _ => true end.
(* end hide *)

(** ef:
Equality factoring *)

Fixpoint ef_aux neg u0 u v pos0 pos l0 : list clause :=
  match pos with
  | (Eqv s t as a2) :: pos' =>
    if expr_eq s u && greater_than_all u0 neg
    then mkPureClause
           (insu_atm (norm_pure_atom (Eqv v t)) neg)
           (insu_atm (norm_pure_atom (Eqv u t))
                 (merge pure_atom_cmp (List.rev pos0) pos)) ::
             ef_aux neg u0 u v (insu_atm a2 pos0) pos' l0
    else l0
  | nil => l0
  end.

Definition ef (cty : ce_type) (c : clause) l0 : list clause :=
  match cty, c with
  | CexpEf, PureClause neg (Eqv (Var u0 as u) v :: pos) _ _ =>
    if greater_than_all u0 neg then ef_aux neg u0 u v nil pos l0
    else l0
  | _, _ => l0
  end.

(** sp:
left and right superposition *)

Definition sp (cty : ce_type) (c d : clause) l0 : list clause :=
  match cty, c, d with
  (* negative (left) superposition *)
  | CexpL, PureClause (Eqv s' v :: neg') pos' _ _,
           PureClause neg (Eqv (Var s0 as s) t :: pos) _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && greater_than_all s0 neg
    then mkPureClause
      (insu_atm (norm_pure_atom (Eqv t v)) (merge pure_atom_cmp neg neg'))
      (merge pure_atom_cmp pos pos') :: l0
    else l0
  (* positive (right) superposition *)
  | CexpR, PureClause neg (Eqv (Var s0 as s) t :: pos) _ _,
           PureClause neg' (Eqv (Var s'0 as s') v :: pos') _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && pure_atom_gt1 (Eqv s' v) pos' &&
       pure_atom_gt (Eqv s t) (Eqv s' v) &&
       greater_than_all s0 neg && greater_than_all s'0 neg'
    then mkPureClause
      (merge pure_atom_cmp neg neg')
      (insu_atm (norm_pure_atom (Eqv t v)) (merge pure_atom_cmp pos pos')) :: l0
    else l0
  | _, _, _ => l0
  end.

(** Retractive rules:
    -demodulation (simplification by positive unit clauses),
    -equality resolution *)

(* u[s->t] *)
Definition rewrite_expr s t u := if expr_eq s u then t else u.

Definition rewrite_by s t atm :=
  match atm with Eqv u v =>
    if expr_eq s u then if expr_eq s v then norm_pure_atom (Eqv t t)
                        else norm_pure_atom (Eqv t v)
    else if expr_eq s v then norm_pure_atom (Eqv u t)
         else atm
  end.

Definition rewrite_in_space s t atm :=
  match atm with
  | Next u v => Next (rewrite_expr s t u) (rewrite_expr s t v)
  | Lseg u v => Lseg (rewrite_expr s t u) (rewrite_expr s t v)
  end.

Definition rewrite_clause_in_space c atm :=
  match c with
  | PureClause nil [Eqv s t] _ _ => rewrite_in_space s t atm
  | _ => atm
  end.

(** Rewrite by a positive unit clause *)

Definition demodulate (c d : clause) : clause :=
  match c, d with
  | PureClause nil [Eqv s t] _ _, PureClause neg pos _ _ =>
      mkPureClause (map (rewrite_by s t) neg) (map (rewrite_by s t) pos)
  | PureClause nil [Eqv s t] _ _, PosSpaceClause neg pos space =>
      PosSpaceClause (map (rewrite_by s t) neg) (map (rewrite_by s t) pos)
          (map (rewrite_in_space s t) space)
  | PureClause nil [Eqv s t] _ _, NegSpaceClause neg space pos =>
      NegSpaceClause (map (rewrite_by s t) neg) (map (rewrite_in_space s t) space)
          (map (rewrite_by s t) pos)
  | _, _ => d
  end.

(** Delete resolved negative atoms, i.e., atoms of the form [Eqv x x]
    lying in negative positions.  This is called equality resolution by some. *)

Definition delete_resolved (c : clause) : clause :=
  match c with
  | PureClause neg pos _ _ =>
     mkPureClause (sortu_atms (remove_trivial_atoms neg)) (sortu_atms pos)
  | _ => c
(*  | _ => mkPureClause nil [Eqv Nil Nil] (* impossible *)*)
  end.

(** Filter tautological clauses *)

Definition not_taut (c: clause) :=
  negb (match c with
        | PureClause neg pos _ _ =>
          existsb (fun a => existsb (fun b =>
                     pure_atom_eq a b) pos) neg ||
          existsb (fun a =>
            match a with Eqv e1 e2 => expr_eq e1 e2 end) pos
        | _ => false end).

(** Rewrite [c] by positive unit clauses in [l]. Delete resolved atoms
    from the resulting clause. Argument [l] is already sorted so no need to
    re-sort. *)

Definition simplify (l : list clause) (c : clause) : clause :=
  delete_resolved (fold_left (fun d c => demodulate c d) l c).

Definition simplify_atoms (l : list clause) (atms : list space_atom)
  : list space_atom :=
  fold_left (fun atms d => map (rewrite_clause_in_space d) atms) l atms.

(** Derive clauses from clause [c] and clauses [l] using [cty] inferences alone.
    Forward-simplify any resulting clauses using facts in [l] (note: we do no
    backward simplification here since this would greatly complicate the termination
    proof). *)

Definition infer (cty : ce_type) (c : clause) (l : list clause) : list clause :=
  print_inferred_list (rsort_uniq compare_clause
    (filter not_taut (map (simplify nil)
      (ef cty c (fold_left (fun l0 d => sp cty c d l0) l nil))))).

(** Model generation: build a candidate model for clauses [l] *)

Definition apply_model (R : model) (cl : clause) : clause :=
  fold_right (fun ve => subst_clause (fst ve) (snd ve)) cl R.

Definition is_model_of (R : model) (gamma delta : list pure_atom) : bool :=
  match fold_right (fun ve => subst_pures_delete (fst ve) (snd ve))
               (remove_trivial_atoms gamma) R,
          fold_right (fun ve => subst_pures (fst ve) (snd ve)) delta R with
  | _::_, _ => true
  | nil , delta' => negb (forallb nonreflex_atom delta')
  end.

(** Check whether R is a model of [Pi+ /\ Pi-]; used in the Veristar main loop *)

Definition is_model_of_PI (R: model) (nc : (*negative spatial*) clause) : bool :=
 match nc with NegSpaceClause pi_plus _ pi_minus =>
  match fold_right (fun ve =>
          subst_pures_delete (fst ve) (snd ve)) (remove_trivial_atoms pi_plus) R,
        fold_right (fun ve =>
          subst_pures (fst ve) (snd ve)) pi_minus R with
  | nil , pi_minus' => forallb nonreflex_atom pi_minus'
  | _ :: _ , _ => false
  end
 | _ => false
 end.

(** Is there a rewrite rule [v'->r] in [R] s.t. [v==v']? *)

Definition reduces (R: model) (v : var) :=
  existsb (fun ve' => if Ident.eq_dec v (fst ve') then true else false) R.

(** Does clause [cl] generate a new rewrite rule that must be added to the
    candidate model [R]? If so, return the rewrite rule paired with [cl]. Otherwise
    [cl] is a c-example for the current candidate model (invariant: [clause_generate
    R cl] is only called when [R] is [not] already a model for [cl]) so determine which
    type of c-example [cl] is, and return that as a value of [ce_type]. *)

Definition clause_generate (R : model) (cl : clause)
  : (var * expr * clause) + ce_type :=
  match cl with
  | PureClause gamma (Eqv (Var l' as l) r :: delta) _ _ as c' =>
      if greater_than_expr l' r && greater_than_all l' gamma &&
         greater_than_atoms (Eqv l r) delta
      then if reduces R l' then inr _ CexpR
           else if is_model_of (List.rev R) nil (map (rewrite_by l r) delta)
                then inr _ CexpEf else inl _ (l', r, cl)
      else inr _ CexpL
  | _ => inr _ CexpL
  end.

(** Construct a candidate model for [l] or fail with (1) the partial model built
    so far (for debugging); (2) the clause that failed; and (3) its [ce_type]. *)

Fixpoint partial_mod (R : model) (acc l : list clause)
  : (model * list clause) + (model * clause * ce_type) :=
  match l with
  | nil => inl _ (R, acc)
  | (PureClause gamma delta _ _) as cl :: l' =>
      if is_model_of (List.rev R) gamma delta then partial_mod R acc l'
      else match clause_generate R cl with
           | (inl (v, exp, cl')) => partial_mod ((v, exp) :: R) (cl' :: acc) l'
           | (inr cty) => inr _ (print_ce_clause R cl cty)
           end
  | _ => inl _ (R, acc)
  end.

Definition is_empty_clause (cl : clause) :=
  match cl with PureClause nil nil _ _ => true | _ => false end.

Definition is_unit_clause (cl : clause) :=
  match cl with PureClause nil (a :: nil) _ _ => true | _ => false end.

Lemma Ppred_decrease n : (n<>1)%positive -> (nat_of_P (Pos.pred n)<nat_of_P n)%nat.
Proof.
intros; destruct (Psucc_pred n) as [Hpred | Hpred]; try contradiction;
pattern n at 2; rewrite <- Hpred; rewrite nat_of_P_succ_morphism; lia.
Defined.

(* begin show *)

(** The Superpose main loop *)
Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind-cannot-build-inversion".

Function main (n : positive) (units l : list clause) {measure nat_of_P n}
  : superposition_result * list clause * M.t*M.t :=
  if Pos.eqb n 1 then (Aborted l, units, M.empty, M.empty)
  else if existsb is_empty_clause (map delete_resolved l)
       then (Valid, units, M.empty, M.empty)
       else match partition is_unit_clause l with (us, rs) =>
              let us' := cclose us in
              let l' := filter not_taut (map (simplify
                                (print_eqs_list us')) rs) in
                match partial_mod nil nil l' with
                | inl (R, selected) =>
                  (C_example R (clause_list2set selected), cclose (us'++units),
                      clause_list2set l', M.empty)
                | inr (R, cl, cty) =>
                  let r := infer cty cl l' in
                    main (Pos.pred n) (cclose (us'++units))
                         (print_pures_list
                           (rsort (rev_cmp compare_clause2) (r ++ l')))
                end
            end.
Proof.
  intro n.
  destruct (Pos.eqb_spec n 1).
  - easy.
  - intros. lia.
Qed.
(* Print Assumptions main.
Check main.
Check positive ->
       list clause ->
       list clause -> superposition_result * list clause * M.t * M.t. *)

(* end show *)

(** Convert a pure entailment to clausal-nf *)

Definition purecnf (en: entailment) : M.t :=
  match en with
    Entailment (Assertion pureL spaceL) (Assertion pureR spaceR) =>
    match mk_pureR pureL, mk_pureR pureR with (p, n), (p', n') =>
      let pureplus :=
        map (fun a => mkPureClause nil (norm_pure_atom a::nil)) p in
      let pureminus :=
        map (fun a => mkPureClause (norm_pure_atom a::nil) nil) n in
      let pureplus' := rsort_uniq pure_atom_cmp (map norm_pure_atom p') in
      let pureminus' := rsort_uniq pure_atom_cmp (map norm_pure_atom n') in
      let cl := mkPureClause pureplus' pureminus' in
        clause_list2set (cl :: pureplus ++ pureminus)
    end
  end.

Definition check (ent : entailment)
  : superposition_result * list clause * M.t*M.t :=
  main 1000000000 nil (print_pures_list
    (rsort (rev_cmp compare_clause2) (M.elements (purecnf ent)))).

Definition check_clauseset (s : M.t)
  : superposition_result * list clause * M.t*M.t :=
  main 1000000000 nil (print_pures_list
    (rsort (rev_cmp compare_clause2) (M.elements (M.filter not_taut s)))).

End Superposition.


Module HeapResolve.

(** Normalization Rules *)

Definition normalize1_3 (pc sc : clause) : clause :=
  match pc , sc with
  | PureClause gamma (Eqv (Var x) y :: delta) _ _,
    PosSpaceClause gamma' delta' sigma =>
        PosSpaceClause (rsort_uniq pure_atom_cmp (gamma++gamma'))
                       (rsort_uniq pure_atom_cmp (delta++delta'))
                       (subst_spaces x y sigma)
  | PureClause gamma (Eqv (Var x) y :: delta) _ _,
    NegSpaceClause gamma' sigma delta' =>
         NegSpaceClause (rsort_uniq pure_atom_cmp (gamma++gamma'))
                        (subst_spaces x y sigma)
                        (rsort_uniq pure_atom_cmp (delta++delta'))
  | _ , _  => sc
  end.

Definition normalize2_4 (sc : clause) : clause :=
  match sc with
  | PosSpaceClause gamma delta sigma =>
        PosSpaceClause gamma delta (drop_reflex_lseg sigma)
  | NegSpaceClause gamma sigma delta =>
        NegSpaceClause gamma (drop_reflex_lseg sigma) delta
  | _ => sc
  end.

Definition norm (s:  M.t) (sc: clause) : clause :=
  normalize2_4 (List.fold_right normalize1_3 sc
    (rsort (rev_cmp compare_clause2) (M.elements s))).

(** Wellformedness Rules *)

Fixpoint do_well1_2 (sc: list space_atom) : list (list pure_atom) :=
  match sc with
  | Next Nil _ :: sc' => nil :: do_well1_2 sc'
  | Lseg Nil y :: sc' => [Eqv y Nil] :: do_well1_2 sc'
  | _ :: sc' => do_well1_2 sc'
  | nil => nil
  end.

(** Next x ? \in sc *)
Fixpoint next_in_dom (x : Ident.t) (sc : list space_atom) : bool :=
  match sc with
  | nil => false
  | Next (Var x') y :: sc' =>
    if Ident.eq_dec x x' then true
    else next_in_dom x sc'
  | _ :: sc' => next_in_dom x sc'
  end.

(** Next x ? \in sc, ?=y *)
Fixpoint next_in_dom1 (x : Ident.t) (y : expr) (sc : list space_atom) : bool :=
  match sc with
  | nil => false
  | Next (Var x') y' :: sc' =>
    if Ident.eq_dec x x' then if expr_eq y y' then true
    else next_in_dom1 x y sc' else next_in_dom1 x y sc'
  | _ :: sc' => next_in_dom1 x y sc'
  end.

(** Next x ? \in sc, ?<>y *)

Fixpoint next_in_dom2 (x : Ident.t) (y : expr) (sc : list space_atom)
  : option expr :=
  match sc with
  | nil => None
  | Next (Var x') y' :: sc' =>
    if Ident.eq_dec x x' then if expr_eq y y' then next_in_dom2 x y sc'
                                 else Some y'
    else next_in_dom2 x y sc'
  | _ :: sc' => next_in_dom2 x y sc'
  end.

Fixpoint do_well3 (sc: list space_atom) : list (list pure_atom) :=
  match sc with
  | Next (Var x) y :: sc' =>
    if next_in_dom x sc'
      then nil :: do_well3 sc'
      else do_well3 sc'
  | _ :: sc' => do_well3 sc'
  | nil => nil
  end.

(** Lseg x ?, ?<>y *)

Fixpoint lseg_in_dom2 (x : Ident.t) (y : expr) (sc : list space_atom)
  : option expr :=
  match sc with
  | Lseg (Var x' as x0) y0 :: sc' =>
    if Ident.eq_dec x x'
      then if negb (expr_eq y0 y) then Some y0 else lseg_in_dom2 x y sc'
      else lseg_in_dom2 x y sc'
  | _ :: sc' => lseg_in_dom2 x y sc'
  | nil => None
  end.

Fixpoint lseg_in_dom_atoms (x : Ident.t) (sc : list space_atom)
  : list pure_atom :=
  match sc with
  | Lseg (Var x' as x0) y0 :: sc' =>
    if Ident.eq_dec x x'
      then order_eqv_pure_atom (Eqv x0 y0) :: lseg_in_dom_atoms x sc'
      else lseg_in_dom_atoms x sc'
  | _ :: sc' => lseg_in_dom_atoms x sc'
  | nil => nil
  end.

Fixpoint do_well4_5 (sc : list space_atom) : list (list pure_atom) :=
  match sc with
  | Next (Var x') y :: sc' =>
    let atms := map (fun a => [a]) (lseg_in_dom_atoms x' sc') in
      atms ++ do_well4_5 sc'
  | Lseg (Var x' as x0) y :: sc' =>
    let l0 := lseg_in_dom_atoms x' sc' in
      match l0 with
      | nil => do_well4_5 sc'
      | _ :: _ =>
        let atms := map (fun a => normalize_atoms [Eqv x0 y; a]) l0 in
          atms ++ do_well4_5 sc'
      end
  | _ as _ :: sc' => do_well4_5 sc'
  | nil => nil
  end.

Definition do_well (sc : list space_atom) : list (list pure_atom) :=
  do_well1_2 sc ++ do_well3 sc ++ do_well4_5 sc.

Definition do_wellformed (sc: clause) : M.t :=
 match sc with
 | PosSpaceClause gamma delta sigma =>
   let sigma' := rsort (rev_cmp compare_space_atom) sigma in
     clause_list2set
       (map (fun ats => mkPureClause gamma (normalize_atoms (ats++delta)))
         (do_well sigma'))
 | _ => M.empty
 end.

(** Unfolding Rules *)

Definition spatial_resolution (pc nc : clause) : M.t :=
  match pc , nc with
  | PosSpaceClause gamma' delta' sigma' , NegSpaceClause gamma sigma delta =>
    match eq_space_atomlist (rsort compare_space_atom sigma)
                            (rsort compare_space_atom sigma') with
    | true => M.singleton (order_eqv_clause (mkPureClause (gamma++gamma') (delta++delta')))
    | false => M.empty
      end
  | _ , _ => M.empty
  end.

Fixpoint unfolding1' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) z :: sigma2' =>
    if next_in_dom1 x' z sigma1
    (*need to reinsert since replacing lseg with next doesn't always preserve
    sorted order*)
      then
        (Eqv x z,
          insert (rev_cmp compare_space_atom) (Next x z) (rev sigma0 ++ sigma2'))
        :: unfolding1' (Lseg x z :: sigma0) sigma1 sigma2'
      else unfolding1' (Lseg x z :: sigma0) sigma1 sigma2'
  | a :: sigma2' => unfolding1' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding1 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding1' nil sigma1 sigma2 in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause gamma' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

Fixpoint unfolding2' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) z :: sigma2' =>
    match next_in_dom2 x' z sigma1 with
    | Some y =>
      (Eqv x z,
          insert (rev_cmp compare_space_atom) (Next x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z) (rev sigma0 ++ sigma2')))
        :: unfolding2' (Lseg x z :: sigma0) sigma1 sigma2'
    | None => unfolding2' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding2' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding2 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding2' nil sigma1 sigma2 in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause gamma' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

Fixpoint unfolding3' (sigma0 sigma1 sigma2 : list space_atom) :
  list (list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) Nil :: sigma2' =>
    match lseg_in_dom2 x' Nil sigma1 with
    | Some y =>
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y Nil) (rev sigma0 ++ sigma2'))
        :: unfolding3' (Lseg x Nil :: sigma0) sigma1 sigma2'
    | None => unfolding3' (Lseg x Nil :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding3' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding3 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding3' nil sigma1 sigma2 in
    let build_clause sigma2' := NegSpaceClause gamma' sigma2' delta' in
      map build_clause l0
  | _ , _ => nil
  end.

(** NPR's rule given in the paper. Confirmed unsound by NP.*)

Fixpoint unfolding4NPR' (sigma0 sigma1 sigma2 : list space_atom)
  : list (list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    match lseg_in_dom2 x' z sigma1 with
    | Some y =>
      if next_in_dom z' sigma1 then
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z) (rev sigma0 ++ sigma2'))
        :: unfolding4NPR' (Lseg x z :: sigma0) sigma1 sigma2'
      else unfolding4NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None => unfolding4NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding4NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfoldingNPR4 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding4NPR' nil sigma1 sigma2 in
    let build_clause sigma2' := NegSpaceClause gamma' sigma2' delta' in
      map build_clause l0
  | _ , _ => nil
  end.

(** Our rule; also suggested by NP. *)

Definition unfolding4 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding4NPR' nil sigma1 sigma2 in
    let GG' := rsort_uniq pure_atom_cmp (gamma ++ gamma') in
    let DD' := rsort_uniq pure_atom_cmp (delta ++ delta') in
    let build_clause sigma2' := NegSpaceClause GG' sigma2' DD' in
      map build_clause l0
  | _ , _ => nil
  end.


(** Unsound rule as given in NPR's paper *)

Fixpoint unfolding5NPR' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    match lseg_in_dom2 x' z sigma1 with
    | Some y =>
      let atms := lseg_in_dom_atoms z' sigma1 in
      let build_res atm :=
        (atm,
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z)
              (rev sigma0 ++ sigma2'))) in
        map build_res atms ++ unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None => unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding5NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding5NPR (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding5NPR' nil sigma1 sigma2 in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause gamma' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

(** Rule as given in NPR's paper, corrected variable uses *)

Definition unfolding5NPRALT' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    match lseg_in_dom2 x' z sigma1, lseg_in_dom2 x' z sigma1 with
    | Some y, _ =>
      let atms := lseg_in_dom_atoms z' sigma1 in
      let build_res atm :=
        (atm,
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z)
              (rev sigma0 ++ sigma2'))) in
        map build_res atms ++ unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None, _ => unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding5NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

(** Our version - also suggested by NP in his reply. *)

Definition unfolding5 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding5NPR' nil sigma1 sigma2 in
    let GG' := rsort_uniq pure_atom_cmp (gamma ++ gamma') in
    let DD' := rsort_uniq pure_atom_cmp (delta ++ delta') in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause GG' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) DD')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

(** Same as unfolding5NPR', but with added side-condition *)

Fixpoint unfolding6NPR' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    if Ident.eq_dec x' z' then unfolding6NPR' sigma0 sigma1 sigma2' else
    match lseg_in_dom2 x' z sigma1 with
    | Some y =>
      let atms := lseg_in_dom_atoms z' sigma1 in
      let build_res atm :=
        (atm,
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z)
              (rev sigma0 ++ sigma2'))) in
        map build_res atms ++ unfolding6NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None =>
       unfolding6NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding6NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding6 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding6NPR' nil sigma1 sigma2 in
    let GG' := rsort_uniq pure_atom_cmp (gamma ++ gamma') in
    let DD' := rsort_uniq pure_atom_cmp (delta ++ delta') in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause GG' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) DD')
      end in
      (map build_clause l0)
  | _ , _ => nil
  end.

Definition mem_add (x: M.elt) (s: M.t) : option M.t :=
 if M.mem x s then None else Some (M.add x s).

Definition add_list_to_set_simple (l: list M.elt) (s: M.t) : M.t :=
  fold_left (Basics.flip M.add) l s.

Fixpoint add_list_to_set (l: list M.elt) (s: M.t) : option M.t :=
 match l with
 | x::xs => match mem_add x s with
                  | None => add_list_to_set xs s
                  | Some s' => Some (add_list_to_set_simple xs s')
                  end
 | nil => None
 end.

Definition do_unfold' pc nc l :=
  unfolding1 pc nc ++
  unfolding2 pc nc ++ unfolding3 pc nc ++
  unfolding4 pc nc ++ unfolding6 pc nc ++ l.

Fixpoint do_unfold (n: nat) (pc : clause) (s : M.t) : M.t :=
  match n with
  | O => s
  | S n' =>
   match add_list_to_set  (M.fold (do_unfold' pc) s nil)  s with
   | Some s'' => do_unfold n' pc s''
   | None => s
   end
  end.

Definition unfolding (pc nc : clause) : M.t :=
  M.fold (fun c => M.union (spatial_resolution pc c))
            (do_unfold 500 pc (M.add nc M.empty)) M.empty.

End HeapResolve.


(* veristar.v *)

Import Superposition. Import HeapResolve.
Require Recdef.

(** The VeriStar interface *)

Inductive veristar_result :=
| Valid : veristar_result
| C_example : model -> veristar_result
| Aborted : list clause -> clause -> veristar_result.

Module Type VERISTAR.

Parameter check_entailment : entailment -> veristar_result.

End VERISTAR.

(** The VeriStar implementation *)

Module VeriStar.

Inductive veristar_result :=
| Valid : veristar_result
| C_example : model -> veristar_result
| Aborted : list clause -> clause -> veristar_result.

Definition pureb c := match c with PureClause _ _ _ _ => true | _ => false end.

Definition pure_clauses := filter pureb.

Definition is_empty_clause (c : clause) :=
  match c with PureClause nil nil _ _ => true | _ => false end.

Definition pures := M.filter pureb.

Lemma Ppred_decrease n :
  (n<>1)%positive -> (nat_of_P (Pos.pred n)<nat_of_P n)%nat.
Proof.
intros; destruct (Psucc_pred n) as [Hpred | Hpred]; try contradiction;
  pattern n at 2; rewrite <- Hpred; rewrite nat_of_P_succ_morphism; lia.
Qed.

(** Top-level redundancy elimination *)

Section RedundancyElim.
Context {A: Type}.
Variable (cmp: A -> A->comparison).
(*begin hide*)
Definition naive_sublist (l1 l2: list A) :=
  forallb (fun a => existsb (fun b => isEq (cmp a b)) l2) l1.
(*end hide*)

(** Linear time sublist for sorted lists *)

Fixpoint sublistg (l1 l2: list A) :=
  match l1, l2 with
  | a::l1', b::l2' => andb (isEq (cmp a b)) (sublistg l1' l2')
  | nil, _ => true
  | _::_, nil => false
  end.

Fixpoint sublist (l1 l2: list A) :=
  match l1, l2 with
  | a::l1', b::l2' =>
    if isEq (cmp a b) then sublistg l1' l2' else sublist l1 l2'
  | nil, _ => true
  | _::_, nil => false
  end.

End RedundancyElim.

Definition impl_pure_clause (c d: clause) :=
  match c, d with PureClause gamma delta _ _, PureClause gamma' delta' _ _ =>
    andb (sublist pure_atom_cmp gamma gamma')
             (sublist pure_atom_cmp delta delta')
  | _, _ => false
  end.

Definition relim1 (c: clause) (s: M.t) :=
  M.filter (fun d => negb (impl_pure_clause c d)) s.

Definition incorp (s t : M.t) :=
  M.union s (M.fold (fun c t0 => relim1 c t0) s t).

(** The main loop of the prover *)

(**************************
          Lemma the_loop_termination1:
forall (n : positive) (sigma : list space_atom) (nc : clause) (s : M.t),
(n =? 1)%positive = false ->
forall (p : superposition_result * list clause * M.t) (t : M.t)
  (p0 : superposition_result * list clause) (s_star : M.t)
  (s0 : superposition_result) (units : list clause) (R : model)
  (selected : M.t),
s0 = Superposition.C_example R selected ->
p0 = (Superposition.C_example R selected, units) ->
p = (Superposition.C_example R selected, units, s_star) ->
check_clauseset s = (Superposition.C_example R selected, units, s_star, t) ->
isEq
  (M.compare
     (incorp
        (print_wf_set
           (do_wellformed
              (print_spatial_model
                 (norm (print_wf_set selected)
                    (PosSpaceClause [] [] (simplify_atoms units sigma))) R)))
        s_star) s_star) = true ->
is_model_of_PI (rev R) (print_spatial_model (simplify units nc) R) = true ->
isEq
  (M.compare
     (incorp
        (print_wf_set
           (do_wellformed
              (print_spatial_model
                 (norm (print_wf_set selected)
                    (PosSpaceClause [] [] (simplify_atoms units sigma))) R)))
        s_star)
     (incorp
        (print_unfold_set
           (pures
              (unfolding
                 (print_spatial_model
                    (norm (print_wf_set selected)
                       (PosSpaceClause [] [] (simplify_atoms units sigma))) R)
                 (print_spatial_model2
                    (print_spatial_model
                       (norm (print_wf_set selected)
                          (PosSpaceClause [] [] (simplify_atoms units sigma)))
                       R) (norm selected (simplify units nc)) R))))
        (incorp
           (print_wf_set
              (do_wellformed
                 (print_spatial_model
                    (norm (print_wf_set selected)
                       (PosSpaceClause [] [] (simplify_atoms units sigma))) R)))
           s_star))) = false -> Pos.to_nat (Pos.pred n) < Pos.to_nat n.
Admitted.

Lemma the_loop_termination2:
forall (n : positive) (sigma : list space_atom),
forall s : M.t,
(n =? 1)%positive = false ->
forall (p : superposition_result * list clause * M.t) (t : M.t)
  (p0 : superposition_result * list clause) (s_star : M.t)
  (s0 : superposition_result) (units : list clause) (R : model)
  (selected : M.t),
s0 = Superposition.C_example R selected ->
p0 = (Superposition.C_example R selected, units) ->
p = (Superposition.C_example R selected, units, s_star) ->
check_clauseset s = (Superposition.C_example R selected, units, s_star, t) ->
isEq
  (M.compare
     (incorp
        (print_wf_set
           (do_wellformed
              (print_spatial_model
                 (norm (print_wf_set selected)
                    (PosSpaceClause [] [] (simplify_atoms units sigma))) R)))
        s_star) s_star) = false -> Pos.to_nat (Pos.pred n) < Pos.to_nat n.
Admitted.
************************)

(* begin show *)

Function the_loop
  (n: positive) (sigma: list space_atom) (nc: clause)
  (s: M.t) (cl: clause) {measure nat_of_P n} : veristar_result :=
  if Pos.eqb n 1 then Aborted (M.elements s) cl
  else match check_clauseset s with
  | (Superposition.Valid, units, _, _) => Valid
  | (Superposition.C_example R selected, units, s_star, _) =>
         let sigma' := simplify_atoms units sigma in
         let nc' := simplify units nc in
         let c := print_spatial_model (norm (print_wf_set selected)
                      (PosSpaceClause nil nil sigma')) R in
         let nu_s := incorp (print_wf_set (do_wellformed c)) s_star in
         if isEq (M.compare nu_s s_star)
         then if is_model_of_PI (List.rev R) (print_spatial_model nc' R)
              then let c' := print_spatial_model2 c (norm selected nc') R in
                   let pcns_u := pures (unfolding c c') in
                   let s_star' := incorp (print_unfold_set pcns_u) nu_s in
                   if isEq (M.compare nu_s s_star') then C_example R
                   else the_loop (Pos.pred n) sigma' nc' s_star' c
              else C_example R
         else the_loop (Pos.pred n) sigma' nc' nu_s c
  | (Superposition.Aborted l, units, _, _) => Aborted l cl
       end.
Admitted.
(**************
Proof.
intros; eapply the_loop_termination1; eauto.
intros; eapply the_loop_termination2; eauto.
Defined.
 *******************)
(* Print Assumptions the_loop. *)

(* end show *)
(* Required to work around Rocq bug #2613 *)

Definition check_entailment (ent: entailment) : veristar_result :=
  let s := clause_list2set (pure_clauses (map order_eqv_clause (cnf ent)))
  in match ent with
     | Entailment (Assertion pi sigma) (Assertion pi' sigma') =>
       match mk_pureR pi, mk_pureR pi' with
       | (piplus, piminus), (pi'plus, pi'minus) =>
           the_loop 1000000000 sigma (NegSpaceClause pi'plus sigma' pi'minus)
             (print_new_pures_set s) empty_clause
       end
     end.

End VeriStar.
(* Check VeriStar.check_entailment. *)


(* example.v *)

Import VeriStar.

Definition a := Var 1%positive.
Definition b := Var 2%positive.
Definition c := Var 3%positive.
Definition d := Var 4%positive.
Definition e := Var 5%positive.

Definition example_ent : entailment := Entailment
  (Assertion [Nequ c e] [Lseg a b ; Lseg a c ; Next c d ; Lseg d e])
  (Assertion nil [Lseg b c ; Lseg c e]).

Local Open Scope positive_scope.

Definition x (p : positive) := Var p.

(*
          ex868(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13)
  [x9 |-> x3 * lseg(x7, x8) * lseg(x1, x6) * x10 |-> x2 * x3 |-> x7 * lseg(x5, x10) * x4 |-> x9 * x13 |-> x5 * lseg(x8, x5) * x11 |-> x12 * x12 |-> x11 * x2 |-> x4 * lseg(x6, x3)] { } [lseg(x2, x10) * lseg(x12, x11) * lseg(x11, x12) * lseg(x6, x3) * lseg(x1, x6) * lseg(x13, x5) * lseg(x10, x2)]*)


Definition harder_ent :=
  Entailment
    (Assertion
       []
       [Next (x 9) (x 3);
         Lseg (x 7) (x 8);
         Lseg (x 1) (x 6);
         Next (x 10) (x 2);
         Next (x 3) (x 7);
         Lseg (x 5) (x 10);
         Next (x 4) (x 9);
         Next (x 13) (x 5);
         Lseg (x 8) (x 5);
         Next (x 11) (x 12);
         Next (x 12) (x 11);
         Next (x 2) (x 4);
         Lseg (x 6) (x 3)])
    (Assertion
       []
       [Lseg (x 2) (x 10);
         Lseg (x 12) (x 11);
         Lseg (x 11) (x 12);
         Lseg (x 6) (x 3);
         Lseg (x 1) (x 6);
         Lseg (x 13) (x 5);
         Lseg (x 10) (x 2)]).


(*ex971(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20)

     [x2 |-> x13 * lseg(x3, x6) * lseg(x10, x5) * x4 |-> x20 * x16 |-> x11 *
      lseg(x6, x14) * x20 |-> x11 * lseg(x17, x6) * lseg(x19, x13) * lseg(x11, x1) *
      x15 |-> x13 * x1 |-> x17 * x5 |-> x18 * lseg(x8, x5) * x7 |-> x13 * x14 |-> x2 *
      x18 |-> x6 * x12 |-> x17 * lseg(x13, x8) * x9 |-> x10]


     { }


     [lseg(x15, x2) * lseg(x4, x6) * lseg(x19, x13) * lseg(x10, x5) * lseg(x7, x13) *
      lseg(x2, x13) * lseg(x16, x11) * lseg(x3, x6) * lseg(x12, x17) * lseg(x9, x10)]
 *)

Definition harder_ent2 :=
  Entailment
    (Assertion
       []
       [Next (x 2) (x 13); Lseg (x 3) (x 6); Lseg (x 10) (x 5); Next (x 4) (x 20); Next (x 16) (x 11);
        Lseg (x 6) (x 14); Next (x 20) (x 11); Lseg (x 17) (x 6); Lseg (x 19) (x 13); Lseg (x 11) (x 1);
        Next (x 15) (x 13); Next (x 1) (x 17); Next (x 5) (x 18); Lseg (x 8) (x 5); Next (x 7) (x 13); Next (x 14) (x 2);
        Next (x 18) (x 6); Next (x 12) (x 17); Lseg (x 13) (x 8); Next (x 9) (x 10)])
    (Assertion
       []
       [Lseg (x 15) (x 2); Lseg (x 4) (x 6); Lseg (x 19) (x 13); Lseg (x 10) (x 5); Lseg (x 7) (x 13);
        Lseg (x 2) (x 13); Lseg (x 16) (x 11); Lseg (x 3) (x 6); Lseg (x 12) (x 17); Lseg (x 9) (x 10)]).

(* ex948(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20)

[x1 |-> x14 * x14 |-> x19 * x5 |-> x8 * x13 |-> x18 * lseg(x18, x13) * lseg(x15, x2) *
 x17 |-> x15 * x20 |-> x6 * x6 |-> x13 * lseg(x11, x19) * x7 |-> x12 * x10 |-> x17 *
 lseg(x16, x20) * x2 |-> x20 * x19 |-> x4 * lseg(x9, x3) * lseg(x8, x12) * lseg(x12, x20) *
 x4 |-> x6 * x3 |-> x20]

{ }

[lseg(x6, x18) * lseg(x4, x6) * lseg(x7, x6) * lseg(x1, x4) *
 lseg(x11, x19) * lseg(x18, x13) * lseg(x16, x20) * lseg(x10, x20) * lseg(x5, x12) *
 lseg(x3, x20) * lseg(x9, x3)] *)


Definition harder_ent3 :=
  Entailment
    (Assertion
       []
       [Next (x 1) (x 14); Next (x 14) (x 19); Next (x 5) (x 8); Next (x 13) (x 18); Lseg (x 18) (x 13); Lseg (x 15) (x 2);
        Next (x 17) (x 15); Next (x 20) (x 6); Next (x 6) (x 13); Lseg (x 11) (x 19); Next (x 7) (x 12); Next (x 10) (x 17);
        Lseg (x 16) (x 20); Next (x 2) (x 20); Next (x 19) (x 4); Lseg (x 9) (x 3); Lseg (x 8) (x 12); Lseg (x 12) (x 20);
       Next (x 4) (x 6); Next (x 3) (x 20)])
    (Assertion
       []
       [Lseg (x 6) (x 18); Lseg (x 4) (x 6); Lseg (x 7) (x 6); Lseg (x 1) (x 4);
        Lseg (x 11) (x 19); Lseg (x 18) (x 13); Lseg (x 16) (x 20); Lseg (x 10) (x 20); Lseg (x 5) (x 12);
        Lseg (x 3) (x 20); Lseg (x 9) (x 3)]).

Compute cnf example_ent.
Compute cnf harder_ent.
Compute cnf harder_ent2.
Compute cnf harder_ent3.
(* Compute check_entailment example_ent.
    ... doesn't work, because of opaque termination proofs ...
 *)

Definition example_myent := Entailment
  (Assertion nil nil)
  (Assertion [Equ a a] nil).
Definition ce_example_myent := check_entailment example_myent.

Definition example1_myent := Entailment
  (Assertion [Equ a b] nil)
  (Assertion [Equ b a] nil).
Definition ce_example1_myent := check_entailment example1_myent.

Definition example2_myent := Entailment
  (Assertion [Equ a b; Equ b c] nil)
  (Assertion [Equ c a] nil).
Definition ce_example2_myent := check_entailment example2_myent.

Definition example1_myfail := Entailment
  (Assertion nil nil)
  (Assertion [Equ a b] nil).
Definition ce_example1_myfail := check_entailment example1_myfail.

Definition example2_myfail := Entailment
  (Assertion [Equ b c] nil)
  (Assertion [Equ a b] nil).
Definition ce_example2_myfail := check_entailment example2_myfail.

Definition ce_example_ent := check_entailment example_ent.

Definition myMain :=
  map check_entailment
      [example_myent; example1_myent;
                        example2_myent;
                        example1_myfail; example1_myfail;
                          example_ent; harder_ent;
                            harder_ent2; harder_ent3].

Set Warnings "-extraction-opaque-accessed".
Extraction "myMain" myMain.

Definition ce_harder_ent := check_entailment harder_ent.
Definition ce_harder_ent2 := check_entailment harder_ent.
Definition ce_harder_ent3 := check_entailment harder_ent.



Definition main_h :=
  check_entailment harder_ent.

Definition main :=
  check_entailment example_ent
(*  map
    check_entailment
    [example_myent;
      example_ent;
      harder_ent] *)
       (*
        harder_ent;
        harder_ent2;
        harder_ent3 *).

Extraction "vs" main.

