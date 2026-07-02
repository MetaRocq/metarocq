From Stdlib Require Import Lists.List.
From MetaRocq.Quotation.ToPCUIC Require Export Init.
From MetaRocq.Utils Require Export bytestring. (* for display of quoted objects *)
From MetaRocq.Utils Require Export ReflectEq.
From MetaRocq.Utils Require Import All_Forall.
From Equations.Prop Require Import Classes.
Import ListNotations.

Export Quotation.ToPCUIC.Init.Instances.

#[export] Instance quote_True : ground_quotable True := ltac:(destruct 1; exact _).
#[export] Instance quote_False : ground_quotable False := ltac:(destruct 1; exact _).
#[export] Instance quote_byte : ground_quotable Byte.byte := ltac:(destruct 1; exact _).
#[export] Instance quote_Empty_set : ground_quotable Empty_set := ltac:(destruct 1; exact _).
#[export] Instance quote_unit : ground_quotable unit := ltac:(destruct 1; exact _).
#[export] Instance quote_bool : ground_quotable bool := ltac:(destruct 1; exact _).

#[export] Instance quote_eq {A} {qA : quotation_of A} {quoteA : ground_quotable A} {x y : A} : ground_quotable (x = y :> A) := ltac:(intros []; exact _).
#[export] Instance quote_eq_refl_l {A} {qA : quotation_of A} {x y : A} {qx : quotation_of x} : ground_quotable (x = y :> A) := ltac:(intros []; exact _).
#[export] Instance quote_eq_refl_r {A} {qA : quotation_of A} {x y : A} {qy : quotation_of y} : ground_quotable (x = y :> A) := ltac:(intro; subst; exact _).

#[export] Typeclasses Opaque not.

#[export] Hint Unfold is_true : quotation.
#[export] Hint Unfold lt : quotation.
#[export] Hint Unfold PeanoNat.Nat.lt : quotation.

#[export] Instance quote_eq_true {b} : ground_quotable (eq_true b) := ltac:(destruct 1; exact _).
#[export] Instance quote_BoolSpec {P Q : Prop} {b} {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (BoolSpec P Q b).
Proof.
  destruct b; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_nat : ground_quotable nat := ltac:(induction 1; exact _).
#[export] Polymorphic Instance quote_option {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (option A) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sum {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sum A B) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_prod {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (prod A B) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_list {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (list A) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quotation_of_list {A ls} {qA : quotation_of A} {qls : @All A quotation_of ls} : quotation_of ls := ltac:(induction qls; exact _).
#[export] Hint Extern 0 (@All ?A quotation_of ?ls) => assumption : typeclass_instances.
#[export] Instance quote_comparison : ground_quotable comparison := ltac:(destruct 1; exact _).
#[export] Instance quote_CompareSpec {Peq Plt Pgt : Prop} {qPeq : quotation_of Peq} {qPlt : quotation_of Plt} {qPgt : quotation_of Pgt} {quote_Peq : ground_quotable Peq} {quote_Plt : ground_quotable Plt} {quote_Pgt : ground_quotable Pgt} {c} : ground_quotable (CompareSpec Peq Plt Pgt c).
Proof.
  destruct c; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_CompareSpecT {Peq Plt Pgt : Prop} {qPeq : quotation_of Peq} {qPlt : quotation_of Plt} {qPgt : quotation_of Pgt} {quote_Peq : ground_quotable Peq} {quote_Plt : ground_quotable Plt} {quote_Pgt : ground_quotable Pgt} {c} : ground_quotable (CompareSpecT Peq Plt Pgt c) := ltac:(destruct 1; exact _).
(* Work around masking-absolute-name warning *)
Module Export Init.
  Module Decimal.
    #[export] Instance quote_uint : ground_quotable Decimal.uint := ltac:(induction 1; exact _).
    #[export] Instance quote_neq_uint {x y} : ground_quotable (x <> y :> Decimal.uint) := ground_quotable_neg_of_dec (@Decimal.uint_eq_dec x y).
  End Decimal.
  #[export] Existing Instances Decimal.quote_uint Decimal.quote_neq_uint.
  Module Hexadecimal.
    #[export] Instance quote_uint : ground_quotable Hexadecimal.uint := ltac:(induction 1; exact _).
    #[export] Instance quote_neq_uint {x y} : ground_quotable (x <> y :> Hexadecimal.uint) := ground_quotable_neg_of_dec (@Hexadecimal.uint_eq_dec x y).
  End Hexadecimal.
  #[export] Existing Instances Hexadecimal.quote_uint Hexadecimal.quote_neq_uint.
  Module Number.
    #[export] Instance quote_uint : ground_quotable Number.uint := ltac:(induction 1; exact _).
    #[export] Instance quote_neq_uint {x y} : ground_quotable (x <> y :> Number.uint) := ground_quotable_neg_of_dec (@Number.uint_eq_dec x y).
  End Number.
  #[export] Existing Instances Number.quote_uint Number.quote_neq_uint.
End Init.
#[export] Instance quote_and {A B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (A /\ B) := (ltac:(destruct 1; exact _)).

#[export] Instance quote_le {n m} : ground_quotable (le n m) := ground_quotable_of_dec (Compare_dec.le_dec n m).

#[export] Polymorphic Instance quote_sig {A} {P : A -> Prop} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sig A P) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sig2 {A} {P Q : A -> Prop} {qA : quotation_of A} {qP : quotation_of P} {qQ : quotation_of Q} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} {quoteQ : forall x, quotation_of x -> ground_quotable (Q x)} : ground_quotable (@sig2 A P Q) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sigT {A P} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sigT A P) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sigT2 {A} {P Q} {qA : quotation_of A} {qP : quotation_of P} {qQ : quotation_of Q} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} {quoteQ : forall x, quotation_of x -> ground_quotable (Q x)} : ground_quotable (@sigT2 A P Q) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sumbool {A B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sumbool A B) := ltac:(destruct 1; exact _).
#[export] Instance quote_sumor {A} {B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sumor A B) := ltac:(destruct 1; exact _).

Definition quote_or_dec {P Q : Prop} (dec : P \/ Q -> {P} + {Q}) {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (or P Q).
Proof.
  intro pf.
  destruct (dec pf).
  all: adjust_quotation_of_by_econstructor_then ltac:(fun _ => destruct pf; first [ eassumption | tauto ]) ltac:(fun _ => exact _).
Defined.
Definition quote_or_dec_l {P Q : Prop} (decP : {P} + {~P}) {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (or P Q).
Proof.
  destruct decP.
  all: intro pf; adjust_quotation_of_by_econstructor_then ltac:(fun _ => destruct pf; first [ eassumption | tauto ]) ltac:(fun _ => exact _).
Defined.
Definition quote_or_dec_r {P Q : Prop} (decQ : {Q} + {~Q}) {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (or P Q).
Proof.
  destruct decQ.
  all: intro pf; adjust_quotation_of_by_econstructor_then ltac:(fun _ => destruct pf; first [ eassumption | tauto ]) ltac:(fun _ => exact _).
Defined.

(* These are not possible *)
(*
#[export] Instance quote_or : ground_quotable or := ltac:(destruct 1; exact _). (A B:Prop) : Prop :=
#[export] Instance quote_ex : ground_quotable ex := ltac:(destruct 1; exact _). (A:Type) (P:A -> Prop) : Prop :=
#[export] Instance quote_ex2 : ground_quotable ex2 := ltac:(destruct 1; exact _). (A:Type) (P Q:A -> Prop) : Prop :=
#[export] Instance quote_inhabited : ground_quotable inhabited := ltac:(destruct 1; exact _). (A:Type) : Prop := inhabits : A -> inhabited A.
*)

#[export] Instance quote_neq_True {x y : True} : ground_quotable (x <> y).
Proof. destruct x, y; intro; exfalso; congruence. Defined.
#[export] Instance quote_neq_False {x y : False} : ground_quotable (x <> y) := ltac:(destruct x).
#[export] Instance quote_neq_byte {x y} : ground_quotable (x <> y :> Byte.byte) := ground_quotable_neg_of_dec (@Byte.byte_eq_dec x y).
#[export] Instance quote_neq_Empty_set {x y : Empty_set} : ground_quotable (x <> y) := ltac:(destruct x).
#[export] Instance quote_neq_unit {x y : unit} : ground_quotable (x <> y).
Proof. destruct x, y; intro; exfalso; congruence. Defined.
#[export] Instance quote_neq_bool {x y} : ground_quotable (x <> y :> bool) := ground_quotable_neg_of_dec (@Bool.bool_dec x y).
#[export] Instance quote_neq_nat {x y} : ground_quotable (x <> y :> nat) := ground_quotable_neg_of_dec (@PeanoNat.Nat.eq_dec x y).
Scheme Equality for comparison.
#[export] Instance quote_neq_comparison {x y} : ground_quotable (x <> y :> comparison) := ground_quotable_neg_of_dec (@comparison_eq_dec x y).

#[export] Instance quote_nle {n m} : ground_quotable (~le n m) := ground_quotable_neg_of_dec (Compare_dec.le_dec n m).

Definition option_eq_None_dec_r {A} {l : option A} : {l = None} + {l <> None}.
Proof. destruct l; [ right | left ]; try reflexivity; congruence. Defined.
Definition option_eq_None_dec_l {A} {l : option A} : {None = l} + {None <> l}.
Proof. destruct l; [ right | left ]; try reflexivity; congruence. Defined.
#[export] Instance quote_option_neq_None_r {A} {qA : quotation_of A} (l : option A) {ql : quotation_of l} : ground_quotable (l <> None)
  := ground_quotable_neg_of_dec option_eq_None_dec_r.
#[export] Instance quote_option_neq_None_l {A} {qA : quotation_of A} (l : option A) {ql : quotation_of l} : ground_quotable (None <> l)
  := ground_quotable_neg_of_dec option_eq_None_dec_l.
