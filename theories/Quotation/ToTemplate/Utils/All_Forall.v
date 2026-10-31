From MetaRocq.Quotation.ToTemplate Require Import Stdlib.Init Stdlib.Lists.
From MetaRocq.Utils Require Import All_Forall.

#[export] Instance quote_All {A R ls} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x, ground_quotable (R x)} : ground_quotable (@All A R ls) := ltac:(induction 1; exact _).
#[export] Instance quote_Alli {A P n ls} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall n x, ground_quotable (P n x)} : ground_quotable (@Alli A P n ls) := ltac:(induction 1; exact _).
#[export] Instance quote_All2 {A B R lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall x y, ground_quotable (R x y)} : ground_quotable (@All2 A B R lsA lsB) := ltac:(induction 1; exact _).
Definition quote_All2_via_dep {A B R lsA lsB} {a : @All2 A B R lsA lsB} (qa : All2_dep (fun _ _ r => quotation_of r) a) {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : quotation_of a := ltac:(induction qa; exact _).

#[export] Hint Extern 0 (@quotation_of (@All2 ?A ?B ?R ?lsA ?lsB) ?x)
=> lazymatch goal with
   | [ H : All2_dep (fun _ _ r => quotation_of r) x |- _ ]
     => simple apply (@quote_All2_via_dep A B R lsA lsB x H)
   | _
     => simple apply @quote_ground;
        simple apply (@quote_All2 A B R lsA lsB)
   end : typeclass_instances.
#[export] Hint Extern 0 (All2_dep (fun _ _ r => quotation_of r) _) => assumption : typeclass_instances.
#[export] Hint Cut [
    ( _ * )
      quote_ground
      quote_All2
  ] : typeclass_instances.

#[export] Instance quote_All2_dep {A B R R' lsA lsB a} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {qR : quotation_of R'} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall x y, ground_quotable (R x y)} {quoteR' : forall x y r, ground_quotable (R' x y r)} : ground_quotable (@All2_dep A B R R' lsA lsB a) := ltac:(induction 1; exact _).
#[export] Instance quote_Forall2_dep {A B R R' lsA lsB a} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {qR : quotation_of R'} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall x y, ground_quotable (R x y:Prop)} {quoteR' : forall x y r, ground_quotable (R' x y r:Prop)} : ground_quotable (@Forall2_dep A B R R' lsA lsB a) := ltac:(induction 1 using Forall2_dep_rect; exact _).
#[export] Instance quote_All2i {A B R n lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall n x y, ground_quotable (R n x y)} : ground_quotable (@All2i A B R n lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_All3 {A B C R lsA lsB lsC} {qA : quotation_of A} {qB : quotation_of B} {qB : quotation_of C} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteC : ground_quotable C} {quoteR : forall x y z, ground_quotable (R x y z)} : ground_quotable (@All3 A B C R lsA lsB lsC) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2 {A R lsA lsB} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} : ground_quotable (@OnOne2 A R lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2i {A R n lsA lsB} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall n x y, ground_quotable (R n x y)} : ground_quotable (@OnOne2i A R n lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2All {A B P lsB lsA1 lsA2} {qA : quotation_of A} {qB : quotation_of B} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteP : forall b x y, ground_quotable (P b x y)} : ground_quotable (@OnOne2All A B P lsB lsA1 lsA2) := ltac:(induction 1; exact _).
#[export] Instance quote_All2i_len {A B R lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall n x y, ground_quotable (R n x y)} : ground_quotable (@All2i_len A B R lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_All_fold {A P ls} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x y, ground_quotable (P x y)} : ground_quotable (@All_fold A P ls) := ltac:(induction 1; exact _).
#[export] Instance quote_All2_fold {A P ls1 ls2} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x y z w, ground_quotable (P x y z w)} : ground_quotable (@All2_fold A P ls1 ls2) := ltac:(induction 1; exact _).
#[export] Instance quote_Forall3 {A B C R lsA lsB lsC} {qA : quotation_of A} {qB : quotation_of B} {qC : quotation_of C} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteC : ground_quotable C} {quoteR : forall x y z, ground_quotable (R x y z:Prop)} : ground_quotable (@Forall3 A B C R lsA lsB lsC).
Proof.
  revert lsB lsC; induction lsA as [|a lsA IH], lsB as [|b lsB], lsC as [|c lsC].
  all: try solve [ intro pf; exfalso; inversion pf ].
  all: adjust_ground_quotable_by_econstructor_inversion ().
Defined.
