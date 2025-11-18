(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import List ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.PCUIC Require Import PCUICSize.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils.
From Equations Require Import Equations.
Set Equations Transparent.

(** * Deriving a compact induction principle for terms

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)


(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Type,
    (P tBox) ->
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall (n : name) (t : term), P t -> P (tLambda n t)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> P (tLetIn n t t0)) ->
    (forall t u : term, P t -> P u -> P (tApp t u)) ->
    (forall s, P (tConst s)) ->
    (forall (i : inductive) (n : nat) (args : list term),
      All P args -> P (tConstruct i n args)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall l : list (list name * term),
        All (fun x => P x.2) l -> P (tCase p t l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tCoFix m n)) ->
    (forall p, primProp P p -> P (tPrim p)) ->
    (forall t, P t -> P (tLazy t)) ->
    (forall t, P t -> P (tForce t)) ->
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert args.
  fix auxl' 1.
  destruct args; constructor; [|apply auxl'].
  apply auxt.

  revert brs.
  fix auxl' 1.
  destruct brs; constructor; [|apply auxl'].
  apply auxt.

  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  apply auxt.

  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  apply auxt.

  destruct prim as [? []]; cbn => //; constructor.
  destruct a as [def v]; cbn.
  split. eapply auxt.
  revert v; fix auxv 1.
  destruct v; constructor; [apply auxt|apply auxv].
Defined.

Ltac applyhyp :=
  match goal with
    H : _ |- _ => apply H
  end.

Class Hyp (T : Type) := hyp : T.
#[global]
Hint Extern 10 (Hyp _) => exactly_once multimatch goal with H : _ |- _
=> exact H end : typeclass_instances.
Class AHyp (T : Type) := ahyp : T.
#[global]
Hint Extern 10 (AHyp _) => multimatch goal with H : _ |- _
=> eapply H; shelve end : typeclass_instances.

Ltac inv H :=
  inversion_clear H ||
  match H with
  | @hyp _ ?X => inversion_clear X
  | @ahyp _ ?X => inversion_clear X
  end.

Definition prim_size (f : term -> nat) (p : prim_val term) : nat :=
  match p.π2 with
  | primIntModel _ => 0
  | primFloatModel _ => 0
  | primStringModel _ => 0
  | primArrayModel a => f a.(array_default) + list_size f a.(array_value)
  end.

Fixpoint size (t : term) : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na M => S (size M)
  | tApp u v => S (size u + size v)
  | tLetIn na b b' => S (size b + size b')
  | tCase ind c brs => S (size c + list_size (fun x => size x.2) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (list_size (fun x => size (dbody x)) mfix)
  | tCoFix mfix idx => S (list_size (fun x => size (dbody x)) mfix)
  | tConstruct _ _ ignore_args => S (list_size size ignore_args)
  | tPrim p => S (prim_size size p)
  | tLazy t => S (size t)
  | tForce t => S (size t)
  | _ => 1
  end.

Lemma size_mkApps f l : size (mkApps f l) = size f + list_size size l.
Proof.
  induction l in f |- *; simpl; try lia.
  rewrite IHl. simpl. lia.
Qed.

Lemma InPrim_size x p : InPrim x p -> size x < S (prim_size size p).
Proof.
  destruct p as [? []]; cbn => //.
  intros [->|H]; try lia.
  eapply (In_size id size) in H; unfold id in H.
  change (fun x => size x) with size in H. lia.
Qed.

Lemma decompose_app_rec_size t l :
  let da := decompose_app_rec t l in
  size da.1 + list_size size da.2 = size t + list_size size l.
Proof.
  induction t in l |- *; cbn; try lia.
  rewrite IHt1; cbn. lia.
Qed.

Lemma decompose_app_size t :
  let da := decompose_app t in
  size da.1 + list_size size da.2 = size t.
Proof.
  unfold decompose_app.
  rewrite (decompose_app_rec_size t []); cbn. lia.
Qed.

(* We redefine these lemmas locally so they can be used to compute a spine view in Rocq itself *)
Local Lemma decompose_app_rec_inv {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  mkApps t l' = mkApps f l.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply/IHt1.
Defined.

Local Lemma decompose_app_inv {t f l} :
  decompose_app t = (f, l) -> t = mkApps f l.
Proof. by apply/decompose_app_rec_inv. Defined.

Local Lemma decompose_app_rec_notApp :
  forall t l u l',
    decompose_app_rec t l = (u, l') ->
    ~~ isApp u.
Proof.
  intros t l u l' e.
  induction t in l, u, l', e |- *.
  all: try (cbn in e ; inversion e ; reflexivity).
  cbn in e. eapply IHt1. eassumption.
Defined.

Local Lemma decompose_app_notApp :
  forall t u l,
    decompose_app t = (u, l) ->
    ~~ isApp u.
Proof.
  intros t u l e.
  eapply decompose_app_rec_notApp. eassumption.
Defined.

Local Lemma decompose_app_app t u f l : decompose_app (tApp t u) = (f, l) -> l <> [].
Proof.
  intros da.
  pose proof (decompose_app_inv da).
  intros ->. cbn in H. subst f.
  now move: (decompose_app_notApp _ _ _ da).
Defined.

Lemma size_mkApps_f {f l} (Hf : ~~ isApp f) (Hl : l <> []) : size f < size (mkApps f l).
Proof.
  rewrite size_mkApps.
  induction l; cbn; congruence || lia.
Qed.

Lemma size_mkApps_l {f l} (Hf : ~~ isApp f) (Hl : l <> []) : list_size size l < size (mkApps f l).
Proof.
  rewrite size_mkApps.
  destruct f => /= //; try lia.
Qed.

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Section All_rec.
  Context (P : term -> Type).
  Context {A} (proj : A -> term).

  Equations? All_rec (l : list A) (auxt : forall y, size y < (list_size (fun x => size (proj x)) l) -> P y) :
    All (fun x => P (proj x)) l :=
    All_rec [] auxt := All_nil;
    All_rec (x :: xs) auxt := All_cons (auxt (proj x) _) (All_rec xs (fun y H => auxt y _)).
  Proof.
    all:lia.
  Qed.
End All_rec.

Global Instance Wf_size_lt : WellFounded (MR lt size) := _.

Module MkAppsInd.
Section MkApps_rec.
  Context {P : term -> Type}.

  Context (pbox : P tBox)
    (prel : forall n : nat, P (tRel n))
    (pvar : forall i : ident, P (tVar i))
    (pevar : forall (n : nat) (l : list term), All P l -> P (tEvar n l))
    (plam : forall (n : name) (t : term), P t -> P (tLambda n t))
    (plet : forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> P (tLetIn n t t0))
    (papp : forall t u,
      ~~ isApp t -> u <> nil -> P t -> All P u -> P (mkApps t u))
    (pconst : forall s, P (tConst s))
    (pconstruct : forall (i : inductive) (n : nat) args, All P args -> P (tConstruct i n args))
    (pcase : forall (p : inductive * nat) (t : term),
        P t -> forall l : list (list name * term),
        All (fun x => P x.2) l -> P (tCase p t l))
    (pproj : forall (s : projection) (t : term), P t -> P (tProj s t))
    (pfix : forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tFix m n))
    (pcofix : forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tCoFix m n))
    (pprim : forall p, primProp P p -> P (tPrim p))
    (plazy : forall t, P t -> P (tLazy t))
    (pforce : forall t, P t -> P (tForce t)).

  Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

  Import EqNotations.

  Equations? rec (t : term) : P t by wf t (MR lt size) :=
    | tRel n => prel n
    | tVar n => pvar n
    | tEvar n l => pevar n l (All_rec P (fun x => x) l (fun x H => rec x))
    | tBox => pbox
    | tLambda n1 t => plam n1 t (rec t)
    | tLetIn n2 t0 t1 => plet n2 t0 (rec t0) t1 (rec t1)
    | tApp t2 t3 with inspect (decompose_app (tApp t2 t3)) :=
      { | exist (t, l) da :=
        let napp := decompose_app_notApp _ _ _ da in
        let nonnil := decompose_app_app _ _ _ _ da in
        let pt := rec t in
        let pl := All_rec P id l (fun x H => rec x) in
        rew _ in papp t l napp nonnil pt pl }
    | tConst k => pconst k
    | tConstruct i n  args => pconstruct i n _ (All_rec P id args (fun x H => rec x))
    | tCase ina c brs => pcase ina c (rec c) brs (All_rec P (fun x => x.2) brs (fun x H => rec x))
    | tProj p c => pproj p c (rec c)
    | tFix mfix idx => pfix mfix idx (All_rec P dbody mfix (fun x H => rec x))
    | tCoFix mfix idx => pcofix mfix idx (All_rec P dbody mfix (fun x H => rec x))
    | tPrim p => pprim p _
    | tLazy t => plazy t (rec t)
    | tForce t => pforce t (rec t).
  Proof.
    all:unfold MR; cbn; auto with arith. 4:lia.
    - clear -napp nonnil da rec.
      pose proof (decompose_app_size (tApp t2 t3)).
      rewrite da in H. cbn in H. rewrite <- H.
      abstract (destruct l; try congruence; cbn; lia).
    - clear -da rec H.
      pose proof (decompose_app_size (tApp t2 t3)).
      rewrite da in H0. cbn in H0. rewrite <- H0.
      unfold id in H. change (fun x => size x) with size in H. abstract lia.
    - clear -da. abstract (eapply decompose_app_inv in da; now symmetry).
    - destruct p as [? []]; cbn => //; constructor.
      destruct a as [def v]; cbn.
      split.
      * eapply rec; red; cbn. lia.
      * refine (All_rec P id v (fun x H => rec x _)); red; cbn.
        unfold id in H. change (fun x => size x) with size in H. lia.
  Qed.

  End MkApps_rec.

  Section MkApps_case.
  Context {P : term -> Type}.

  Context (pbox : P tBox)
    (prel : forall n : nat, P (tRel n))
    (pvar : forall i : ident, P (tVar i))
    (pevar : forall (n : nat) (l : list term), P (tEvar n l))
    (plam : forall (n : name) (t : term), P (tLambda n t))
    (plet : forall (n : name) (t : term), forall t0 : term, P (tLetIn n t t0))
    (papp : forall t u, ~~ isApp t -> u <> nil -> P (mkApps t u))
    (pconst : forall s, P (tConst s))
    (pconstruct : forall (i : inductive) (n : nat) args, P (tConstruct i n args))
    (pcase : forall (p : inductive * nat) (t : term) (l : list (list name * term)), P (tCase p t l))
    (pproj : forall (s : projection) (t : term), P (tProj s t))
    (pfix : forall (m : mfixpoint term) (n : nat), P (tFix m n))
    (pcofix : forall (m : mfixpoint term) (n : nat), P (tCoFix m n))
    (pprim : forall p, P (tPrim p))
    (plazy : forall t, P (tLazy t))
    (pforce : forall t, P (tForce t)).

  Import EqNotations.

  Equations case (t : term) : P t :=
    | tRel n => prel n
    | tVar n => pvar n
    | tEvar n l => pevar n l
    | tBox => pbox
    | tLambda n1 t => plam n1 t
    | tLetIn n2 t0 t1 => plet n2 t0 t1
    | tApp t2 t3 with inspect (decompose_app (tApp t2 t3)) :=
      { | exist (t, l) da :=
        let napp := decompose_app_notApp _ _ _ da in
        let nonnil := decompose_app_app _ _ _ _ da in
        rew [P] (eq_sym (decompose_app_inv da)) in papp t l napp nonnil }
    | tConst k => pconst k
    | tConstruct i n args => pconstruct i n args
    | tCase ina c brs => pcase ina c brs
    | tProj p c => pproj p c
    | tFix mfix idx => pfix mfix idx
    | tCoFix mfix idx => pcofix mfix idx
    | tPrim p => pprim p
    | tLazy t => plazy t
    | tForce t => pforce t.

  End MkApps_case.

End MkAppsInd.

(*Equations? head (t : term) : term
  by wf t (fun x y : term => size x < size y) :=
  | t with TermSpineView.view t :=
    { | TermSpineView.tApp f l Hf Hl => head f;
      | x => _ }.
Proof.
  7:{ apply size_mkApps_f; auto. }
  all:try match goal with [ _ : TermSpineView.t ?t |- _ ] => try exact t end.
Defined.

Lemma head_lemma t : head t = t.
Proof.
  funelim (head t); try reflexivity.
  2:{ unfold head_obligation_10. cbn. }*)

(*Module TermSpineView.

  Inductive t : Set :=
  | tBox       : t (* Represents all proofs *)
  | tRel       : nat -> t
  | tVar       : ident -> t (* For free variables (e.g. in a goal) *)
  | tEvar      : nat -> list term -> t
  | tLambda    : name -> term -> t
  | tLetIn     : name -> term (* the term *) -> term -> t
  | tApp       : forall (f : term) (l : list term), ~~ isApp f -> l <> nil -> t
  | tConst     : kername -> t
  | tConstruct : inductive -> nat -> t
  | tCase      : (inductive * nat) (* # of parameters *) ->
                term (* discriminee *) -> list (list name * term) (* branches *) -> t
  | tProj      : projection -> term -> t
  | tFix       : mfixpoint term -> nat -> t
  | tCoFix     : mfixpoint term -> nat -> t.

  Definition view : term -> t :=
    MkAppsInd.rec (P:=fun _ => t)
      tBox tRel tVar
      (fun n l _ => tEvar n l)
      (fun n t _ => tLambda n t)
      (fun n b _ t _ => tLetIn n b t)
      (fun f l napp nnil _ _ => tApp f l napp nnil)
      tConst
      tConstruct
      (fun p t pt l pl => tCase p t l)
      (fun p t pt => tProj p t)
      (fun mfix n _ => tFix mfix n)
      (fun mfix n _ => tCoFix mfix n).

  Definition size (v : t) : nat :=
    match v with
    | tRel i => 1
    | tEvar ev args => S (list_size size args)
    | tLambda na M => S (size M)
    | tApp u v _ _ => S (size u + list_size size v)
    | tLetIn na b b' => S (size b + size b')
    | tCase ind c brs => S (size c + list_size (fun x => size x.2) brs)
    | tProj p c => S (size c)
    | tFix mfix idx => S (list_size (fun x => size (dbody x)) mfix)
    | tCoFix mfix idx => S (list_size (fun x => size (dbody x)) mfix)
    | _ => 1
    end.

End TermSpineView.*)
