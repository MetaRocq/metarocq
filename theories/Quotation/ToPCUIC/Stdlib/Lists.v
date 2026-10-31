From Stdlib Require Import Lists.List.
From Stdlib Require Import Lists.ListDec.
From MetaRocq.Utils Require Import ReflectEq.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init.
From Equations.Prop Require Import Classes.
Import ListNotations.
Local Open Scope list_scope.

(* not decidable *)
(*
#[export] Instance quote_Add {A a ls1 ls2} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (@Add A a ls1 ls2) := ltac:(destruct 1; exact _). (a:A) : list A -> list A -> Prop :=
#[export] Instance quote_NoDup {A} {qA : quotation_of A} {quoteA : ground_quotable A} {quote_neg_In : forall (a : A) ls, ground_quotable (~In a ls)} {ls} : ground_quotable (@NoDup A ls).
Proof.
  induction ls; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_Exists : ground_quotable Exists := ltac:(destruct 1; exact _). : list A -> Prop :=
 *)
#[export] Instance quote_Forall {A R ls} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x, ground_quotable (R x:Prop)} : ground_quotable (@Forall A R ls).
Proof.
  induction ls as [|a ls IH].
  all: adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_Forall2 {A B R lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall x y, ground_quotable (R x y:Prop)} : ground_quotable (@Forall2 A B R lsA lsB).
Proof.
  revert lsB; induction lsA as [|a lsA IH], lsB as [|b lsB].
  all: try solve [ intro pf; exfalso; inversion pf ].
  all: adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_ForallOrdPairs {A R ls} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y:Prop)} : ground_quotable (@ForallOrdPairs A R ls).
Proof.
  induction ls as [|a ls IH].
  all: adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_eqlistA {A R ls1 ls2} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y:Prop)} : ground_quotable (@SetoidList.eqlistA A R ls1 ls2).
Proof.
  revert ls2; induction ls1 as [|a ls1 IH], ls2 as [|b ls2].
  all: try solve [ intro pf; exfalso; inversion pf ].
  all: adjust_ground_quotable_by_econstructor_inversion ().
Defined.
(*
#[export] Instance quote_PermutationA : ground_quotable PermutationA := ltac:(destruct 1; exact _). : list A -> list A -> Prop :=
 *)
(*
#[export] Instance quote_memo_val : ground_quotable memo_val := ltac:(destruct 1; exact _). {A : nat -> Type} : Type :=
Co#[export] Instance quote_Stream : ground_quotable Stream := ltac:(destruct 1; exact _). (A : Type) :=
Co#[export] Instance quote_EqSt : ground_quotable EqSt := ltac:(destruct 1; exact _). (s1 s2: Stream) : Prop :=
#[export] Instance quote_Exists : ground_quotable Exists := ltac:(destruct 1; exact _). : Stream -> Prop :=
#[export] Instance quote_Exists : ground_quotable Exists := ltac:(destruct 1; exact _). ( x: Stream ) : Prop :=
Co#[export] Instance quote_ForAll : ground_quotable ForAll := ltac:(destruct 1; exact _). (x: Stream) : Prop :=
*)

Definition list_eq_nil_dec_r {A} {l : list A} : {l = []} + {l <> []}.
Proof. destruct l; [ left | right ]; try reflexivity; congruence. Defined.
Definition list_eq_nil_dec_l {A} {l : list A} : {[] = l} + {[] <> l}.
Proof. destruct l; [ left | right ]; try reflexivity; congruence. Defined.
#[export] Instance quote_list_neq_nil_r {A} {qA : quotation_of A} (l : list A) {ql : quotation_of l} : ground_quotable (l <> [])
  := ground_quotable_neg_of_dec list_eq_nil_dec_r.
#[export] Instance quote_list_neq_nil_l {A} {qA : quotation_of A} (l : list A) {ql : quotation_of l} : ground_quotable ([] <> l)
  := ground_quotable_neg_of_dec list_eq_nil_dec_l.

#[export] Instance quote_list_In {A x l} {decA : EqDec A} {qA : quotation_of A} {qx : quotation_of x} {ql : quotation_of l} {qdecA : quotation_of decA} : ground_quotable (@List.In A x l)
  := ground_quotable_of_dec (in_dec decA _ _).
