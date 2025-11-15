(* Distributed under the terms of the MIT license. *)
Set Warnings "-notation-overridden".

From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Unset Universe Checking.
From MetaRocq.Translations Require Import translation_utils times_bool_fun MiniHoTT.
Import MRMonadNotation.

Unset MetaRocq Strict Unquote Universe Mode.

MetaRocq Run (TC <- ImplementExisting emptyTC "paths" ;;
                     TC <- ImplementExisting TC "idpath" ;;
                     TC <- ImplementExisting TC "paths_ind" ;;
                     TC <- ImplementExisting TC "transport" ;;
                     TC <- ImplementExisting TC "sigT" ;;
                     TC <- ImplementExisting TC "projT1" ;;
                     TC <- ImplementExisting TC "projT2" ;;
                     TC <- ImplementExisting TC "existT" ;;
                     tmDefinition "eqTC" TC).
Next Obligation.
  tIntro A. tIntro x. tIntro y. exact (x = y).
Defined.
Next Obligation.
  tIntro A. tIntro x. exact 1.
Defined.
Next Obligation.
  tIntro A. tIntro a. tIntro P. tIntro t. tIntro y. tIntro p.
  exact (paths_ind a (fun y p => π1 (π1 P y) p) t y p).
Defined.
Next Obligation.
  tIntro A. tIntro P. tIntro x. tIntro y. tIntro p. tIntro t.
  exact (transport (π1 P) p t).
Defined.
Next Obligation.
  tIntro A. tIntro B. exact (sigT (π1 B)).
Defined.
Next Obligation.
  tIntro A. tIntro B. tIntro u. exact u.1.
Defined.
Next Obligation.
  tIntro A. tIntro B. tIntro u. exact u.2.
Defined.
Next Obligation.
  tIntro A. tIntro B. tIntro x. tIntro y. exact (x; y).
Defined.

Definition isequiv {A B} (f : A -> B) :=
  exists (g : B -> A) (H1 : forall x, paths (g (f x)) x), (forall y, paths (f (g y)) y).

Definition idequiv A : @isequiv A A (fun x => x).
  unshelve econstructor. exact (fun y => y).
  split; intro; exact 1.
Defined.

Definition equiv A B := exists f, @isequiv A B f.

Definition coe {A B} (p : A = B) : A -> B
  := transport idmap p.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y)
  : forall z : P y, p # p^ # z = z
  := paths_ind x (fun y p => forall z : P y, p # p^ # z = z) (fun z => 1) y p.

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x = y)
  : forall z : P x, p^ # p # z = z
  := paths_ind x (fun y p => forall z : P x, p^ # p # z = z) (fun z => 1) y p.

Definition id2equiv A B (p : A = B) : equiv A B.
  repeat unshelve econstructor.
  exact (transport idmap p).
  exact (transport idmap p^).
  all: unfold coe; intro.
  (* refine (paths_ind A (fun y p => forall z : A, p^ # p # z = z) (fun z => 1) B p _). *)
  (* refine (paths_ind A (fun y p => forall z : y, p # p^ # z = z) (fun z => 1) B p _). *)
  exact (transport_Vp idmap _ _).
  exact (transport_pV idmap _ _).
Defined.

Definition UA := forall A B, isequiv (id2equiv A B).

MetaRocq Run (TC <- Translate eqTC "isequiv" ;;
                     TC <- Translate TC "equiv" ;;
                     TC <- ImplementExisting TC "eq" ;;
                     TC <- Translate TC "inverse" ;;
                     tmDefinition "eqTC2" TC).
Next Obligation.
  tIntro A. tIntro x. tIntro y. exact (@eq A x y).
Defined.


Definition contr A := exists x : A, forall y, x = y.
Definition weakFunext
  := forall (A : Type) (P : A -> Type), (forall x, contr (P x)) -> contr (forall x, P x).

MetaRocq Run (TC <- Translate eqTC2 "contr" ;;
                     TC <- Translate TC "weakFunext" ;;
                     tmDefinition "eqTC3" TC).

Goal weakFunextᵗ -> False.
  intro H. tSpecialize H unit. tSpecialize H (pair (fun _ => unit) true).
  simple refine (let H' := π1 H _ in _).
  - tIntro x. lazy. exists tt. tIntro y; now destruct y.
  - lazy in H'. destruct H' as [H1 H2]; clear H.
    tSpecialize H2 (pair (π1 H1) (negb (π2 H1))).
    apply (f_equal π2) in H2. lazy in H2.
    set (π2 H1) in H2. change (b = negb b) in H2.
    destruct b; inversion H2.
Defined.

Definition retract A B := exists (f : A -> B) (g : B -> A), g o f == idmap.

Definition contr_retract {A B} (R : retract A B) (C : contr B) : contr A.
  destruct R as [f [g e]].
  exists (g C.1). intro y.
  refine (ap g _ @ e y).
  exact (C.2 (f y)).
Defined.

Definition postcompose_equiv
  := forall A B (e : equiv A B) A', isequiv (fun (g : A' -> A) => e.1 o g).

Definition UA_postcomposeequiv : UA -> postcompose_equiv.
  (* uses eta *)
Admitted.

Definition α {A} (P : A -> Type) := fun (g : A -> sigT P) => pr1 o g.

Definition contr_isequivα := forall A P, (forall x, contr (P x)) -> isequiv (@α A P).

Definition postcomposeequiv_αequiv
  : postcompose_equiv -> contr_isequivα.
  (* no eta ? *)
  intros H A P C.
  refine (H (sigT P) A (_; _) _).
  unshelve econstructor.
  exact (fun x => (x; (C x).1)).
  lazy. econstructor.
  intros [x y]. refine (path_sigma' P 1 _). exact ((C x).2 y).
  intro; exact 1.
Defined.

Definition fib {A B} (f : A -> B) y := exists x, f x = y.

Definition equiv_contrfib {A B} (f : A -> B) (Hf : isequiv f) y : contr (fib f y).
Admitted.

Definition contr_retractα
  := forall A P, (forall x, contr (P x)) -> retract (forall x : A, P x) (fib (α P) idmap).

Definition contr_retract_α : contr_retractα.
  intros A P H.
  simple refine (_; (_; _)).
  - intro f. exists (fun x => (x; f x)). exact 1.
  - intros [g p] x. refine (_ # (g x).2).
    exact (ap10 p x).
  - intro f; lazy. exact 1. (* uses eta! *)
Defined.

(* MetaRocq Run (TC <- TranslateRec eqTC3 contr_retractα ;; *)
(*                      TC <- ImplementExisting TC "contr_retract_α" ;; *)
(*                      tmDefinition "eqTC4" TC). *)
(* Next Obligation. *)
(*   tIntro A. tIntro P. tIntro H. *)
(*   simple refine (_; (_; _)). *)
(*   - tIntro f. exists (pair (fun x => (x; π1 f x)) (π2 f)). exact 1. *)
(*   - tIntro gp. refine (pair (fun x => _) (π2 gp.1)). *)
(*     refine (_ # ((π1 gp.1) x).2). all: lazy. *)
(*     exact (ap10 (ap π1 gp.2) x). *)
(*   - tIntro f; lazy. exact 1. *)
(* Defined. *)

Definition UA_postcomposeequiv' : UA -> postcompose_equiv.
  intros ua A B e X. repeat unshelve econstructor.
  - intros f x. exact (e.2.1 (f x)).
  - intro f.

  (* uses eta *)
Admitted.


Definition αequiv_weakfunext : contr_isequivα -> weakFunext.
  intros Hα A P H.
  refine (contr_retract _ _).
  2: exact (equiv_contrfib _ (Hα A P H) idmap).
  exact (contr_retract_α A P H).
Defined.
