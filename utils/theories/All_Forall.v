From Coq Require Import List Bool Arith ssreflect Morphisms Lia Utf8.
From MetaCoq.Utils Require Import MCPrelude MCReflect MCList MCRelations MCProd MCOption.
From Equations Require Import Equations.
Import ListNotations.

Derive Signature for Forall Forall2.

(** Combinators *)

(** Forall combinators in Type to allow building them by recursion *)
Inductive All {A} (P : A -> Type) : list A -> Type :=
    All_nil : All P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All P l -> All P (x :: l).
Arguments All {A} P%type _.
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.
Derive Signature NoConfusion for All.
#[global] Hint Constructors All : core.

Inductive Alli {A} (P : nat -> A -> Type) (n : nat) : list A -> Type :=
| Alli_nil : Alli P n []
| Alli_cons hd tl : P n hd -> Alli P (S n) tl -> Alli P n (hd :: tl).
Arguments Alli_nil {_ _ _}.
Arguments Alli_cons {_ _ _ _ _}.
Derive Signature for Alli.
Derive NoConfusionHom for Alli.
#[global] Hint Constructors Alli : core.

Inductive All2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  All2_nil : All2 R [] []
| All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> All2 R l l' -> All2 R (x :: l) (y :: l').
Arguments All2_nil {_ _ _}.
Arguments All2_cons {_ _ _ _ _ _ _}.
Derive Signature for All2.
Derive NoConfusionHom for All2.
#[global] Hint Constructors All2 : core.

Inductive All2_dep {A B : Type} {R : A -> B -> Type} (R' : forall a b, R a b -> Type) : forall {xs ys}, All2 R xs ys -> Type :=
| All2_dep_nil : All2_dep R' All2_nil
| All2_dep_cons : forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (rs : All2 R l l'),
    R' x y r -> All2_dep R' rs -> All2_dep R' (All2_cons r rs).
Arguments All2_dep_nil {_ _ _ _}.
Arguments All2_dep_cons {_ _ _ _ _ _ _ _ _ _} _ _.
Derive Signature for All2_dep.
Derive NoConfusionHom for All2_dep.
#[global] Hint Constructors All2_dep : core.

Inductive Forall2_dep {A B : Type} {R : A -> B -> Prop} (R' : forall a b, R a b -> Prop) : forall {xs ys}, Forall2 R xs ys -> Prop :=
| Forall2_dep_nil : Forall2_dep R' (@Forall2_nil _ _ _)
| Forall2_dep_cons : forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (rs : Forall2 R l l'),
    R' x y r -> Forall2_dep R' rs -> Forall2_dep R' (@Forall2_cons _ _ _ _ _ _ _ r rs).
Arguments Forall2_dep_nil {_ _ _ _}.
Arguments Forall2_dep_cons {_ _ _ _ _ _ _ _ _ _} _ _.
Derive Signature for Forall2_dep.
#[global] Hint Constructors Forall2_dep : core.

Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) (n : nat)
  : list A -> list B -> Type :=
| All2i_nil : All2i R n [] []
| All2i_cons :
    forall x y l r,
      R n x y ->
      All2i R (S n) l r ->
      All2i R n (x :: l) (y :: r).
Arguments All2i_nil {_ _ _ _}.
Arguments All2i_cons {_ _ _ _ _ _ _ _}.

Derive Signature NoConfusionHom for All2i.
#[global] Hint Constructors All2i : core.


Inductive All3 {A B C : Type} (R : A -> B -> C -> Type) : list A -> list B -> list C -> Type :=
  All3_nil : All3 R [] [] []
| All3_cons : forall (x : A) (y : B) (z : C) (l : list A) (l' : list B) (l'' : list C),
    R x y z -> All3 R l l' l'' -> All3 R (x :: l) (y :: l') (z :: l'').
Arguments All3_nil {_ _ _ _}.
Arguments All3_cons {_ _ _ _ _ _ _ _ _ _}.
Derive Signature NoConfusionHom for All3.
#[global] Hint Constructors All3 : core.

Definition invert_Forall2 {A B R l l'} (a : @Forall2 A B R l l')
  := match a in Forall2 _ l l'
           return
           match l, l' return @Forall2 A B R l l' -> Prop with
           | [], [] => fun a => Forall2_nil _ = a
           | [], _ | _, [] => fun _ => False
           | x :: xs, y :: ys
             => fun a => sigP (fun v => Forall2_cons _ _ (proj1 v) (proj2 v) = a)
           end a
     with
     | Forall2_nil _ => eq_refl
     | Forall2_cons _ _ r a => existP _ (conj r a) eq_refl
     end.
Import EqNotations.
Definition invert_Forall2_dep {A B R R' l l' a} (a' : @Forall2_dep A B R R' l l' a)
  := match a' in @Forall2_dep _ _ _ _ l l' a
           return
           match l, l' return forall a, @Forall2_dep A B R R' l l' a -> Prop with
           | [], [] => fun a a' => (rew [Forall2_dep _] invert_Forall2 a in Forall2_dep_nil) = a'
           | [], _ | _, [] => fun _ _ => False
           | x :: xs, y :: ys
             => fun a a' => sigP (fun v => (rew projP2 (invert_Forall2 a) in Forall2_dep_cons (proj1 v) (proj2 v)) = a')
           end a a'
     with
     | Forall2_dep_nil => eq_refl
     | Forall2_dep_cons r a => existP _ (conj r a) eq_refl
     end.

Definition Forall2_rect A B R (P : forall x y, Forall2 R x y -> Type)
  (Hn : P [] [] (@Forall2_nil _ _ _))
  (Hc : forall x y l l' r (a : Forall2 R l l'),
      P l l' a -> P (x :: l) (y :: l') (Forall2_cons _ _ r a))
  : forall l l' (a : @Forall2 A B R l l'), P l l' a.
Proof.
  fix F 1.
  destruct l as [|x xs], l' as [|y ys]; intro H;
    first [ specialize (F xs ys) | clear F ].
  all: generalize (invert_Forall2 H); cbn; try solve [ destruct 1 ].
  { intro; subst; exact Hn. }
  { intro H'.
    specialize (Hc x y xs ys (proj1 (projP1 H')) (proj2 (projP1 H')) (F _)).
    destruct (projP2 H').
    exact Hc. }
Defined.

Definition Forall2_rec A B R (P : forall x y, Forall2 R x y -> Set)
  (Hn : P [] [] (@Forall2_nil _ _ _))
  (Hc : forall x y l l' r (a : Forall2 R l l'),
      P l l' a -> P (x :: l) (y :: l') (Forall2_cons _ _ r a))
  : forall l l' (a : @Forall2 A B R l l'), P l l' a
  := @Forall2_rect A B R P Hn Hc.

Definition Forall2_dep_rect A B R R' (P : forall x y a, @Forall2_dep A B R R' x y a -> Type)
  (Hn : P [] [] (@Forall2_nil _ _ _) Forall2_dep_nil)
  (Hc : forall x y l l' r rs r' (a : Forall2_dep R' rs),
      P l l' rs a -> P (x :: l) (y :: l') (Forall2_cons _ _ r rs) (Forall2_dep_cons r' a))
  : forall l l' a (a' : @Forall2_dep A B R R' l l' a), P l l' a a'.
Proof.
  intros l l' a a'.
  induction a; generalize (invert_Forall2_dep a'); cbn.
  { intro; subst; exact Hn. }
  { intro H'.
    specialize (Hc _ _ _ _ _ _ (proj1 (projP1 H')) (proj2 (projP1 H')) (IHa _)).
    destruct (projP2 H').
    exact Hc. }
Defined.

Definition Forall2_dep_rec A B R R' (P : forall x y a, @Forall2_dep A B R R' x y a -> Set)
  (Hn : P [] [] (@Forall2_nil _ _ _) Forall2_dep_nil)
  (Hc : forall x y l l' r rs r' (a : Forall2_dep R' rs),
      P l l' rs a -> P (x :: l) (y :: l') (Forall2_cons _ _ r rs) (Forall2_dep_cons r' a))
  : forall l l' a (a' : @Forall2_dep A B R R' l l' a), P l l' a a'
  := @Forall2_dep_rect A B R R' P Hn Hc.

Section alli.
  Context {A} (p : nat -> A -> bool).
  Fixpoint alli (n : nat) (l : list A) : bool :=
  match l with
  | [] => true
  | hd :: tl => p n hd && alli (S n) tl
  end.
End alli.

Section Forallb2.
  Context {A B} (f : A -> B -> bool).

  Fixpoint forallb2 l l' :=
    match l, l' with
    | hd :: tl, hd' :: tl' => f hd hd' && forallb2 tl tl'
    | [], [] => true
    | _, _ => false
    end.

End Forallb2.

Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').
Derive Signature NoConfusion for OnOne2.

Inductive OnOne2i {A : Type} (P : nat -> A -> A -> Type) : nat -> list A -> list A -> Type :=
| OnOne2i_hd i hd hd' tl : P i hd hd' -> OnOne2i P i (hd :: tl) (hd' :: tl)
| OnOne2i_tl i hd tl tl' : OnOne2i P (S i) tl tl' -> OnOne2i P i (hd :: tl) (hd :: tl').
Derive Signature NoConfusion for OnOne2i.
#[global] Hint Constructors OnOne2i : core.

Inductive OnOne2All {A B : Type} (P : B -> A -> A -> Type) : list B -> list A -> list A -> Type :=
| OnOne2All_hd b bs hd hd' tl : P b hd hd' -> #|bs| = #|tl| -> OnOne2All P (b :: bs) (hd :: tl) (hd' :: tl)
| OnOne2All_tl b bs hd tl tl' : OnOne2All P bs tl tl' -> OnOne2All P (b :: bs) (hd :: tl) (hd :: tl').
Derive Signature NoConfusion for OnOne2All.
#[global] Hint Constructors OnOne2All : core.

Inductive All_fold {A} (P : list A -> A -> Type) : list A -> Type :=
  | All_fold_nil : All_fold P nil
  | All_fold_cons {d Γ} : All_fold P Γ -> P Γ d -> All_fold P (d :: Γ).
#[global] Hint Constructors All_fold : core.

Derive Signature NoConfusionHom for All_fold.
Inductive All2_fold {A} (P : list A -> list A -> A -> A -> Type)
            : list A -> list A -> Type :=
| All2_fold_nil : All2_fold P nil nil
| All2_fold_cons {d d' Γ Γ'} : All2_fold P Γ Γ' -> P Γ Γ' d d' -> All2_fold P (d :: Γ) (d' :: Γ').

Derive Signature NoConfusion for All2_fold.
#[global] Hint Constructors All2_fold : core.

Definition All_over {A B} (P : list B -> list B -> A -> A -> Type) (Γ Γ' : list B) :=
  fun Δ Δ' => P (Δ ++ Γ) (Δ' ++ Γ').

Definition size := nat.

Section All_size.
  Context {A} (P : A -> Type) (fn : forall x1, P x1 -> size).
  Fixpoint all_size {l1 : list A} (f : All P l1) : size :=
  match f with
  | All_nil => 0
  | All_cons px pl => fn _ px + all_size pl
  end.
End All_size.

Section Alli_size.
  Context {A} (P : nat -> A -> Type) (fn : forall n x1, P n x1 -> size).
  Fixpoint alli_size {l1 : list A} {n} (f : Alli P n l1) : size :=
  match f with
  | Alli_nil => 0
  | Alli_cons px pl => fn _ _ px + alli_size pl
  end.
End Alli_size.

Section All2_size.
  Context {A B} (P : A -> B -> Type) (fn : forall x1 x2, P x1 x2 -> size).
  Fixpoint all2_size {l1 l2} (f : All2 P l1 l2) : size :=
  match f with
  | All2_nil => 0
  | All2_cons rxy rll' => fn _ _ rxy + all2_size rll'
  end.
End All2_size.

Section All2i_size.
  Context {A B} (P : nat -> A -> B -> Type) (fn : forall i x1 x2, P i x1 x2 -> size).
  Fixpoint all2i_size {n l1 l2} (f : All2i P n l1 l2) : size :=
  match f with
  | All2i_nil => 0
  | All2i_cons rxy rll' => fn _ _ _ rxy + all2i_size rll'
  end.
End All2i_size.


(** Generic strategy for dealing with Forall/forall, etc, in a fully information-preserving way:

    1) Normalize towards [nth_error]
    2) Use [nth_error] rewriting lemmas
    3) optionally simplify and call eauto.
 *)

Local Ltac pose_rename H lem :=
  let H' := fresh in
  pose proof lem as H';
  clear H; rename H' into H.

Lemma nth_error_app_forall_iff A P l1 l2
  : (forall i x, @nth_error A (l1 ++ l2) i = Some x -> P i x)
      <~> ((forall i x, nth_error l1 i = Some x -> P i x)
             × (forall i x, nth_error l2 i = Some x -> P (#|l1| + i) x)).
Proof.
  split => [H|[H1 H2]]; [ split | ].
  { intros; eapply H; rewrite nth_error_app1 => //; eapply nth_error_Some; congruence. }
  { clear -H; let H' := fresh in intros ?? H'; eapply H; rewrite nth_error_app2 -?H' => //; f_equal; lia. }
  { intros i x H.
    apply nth_error_app_inv in H.
    destruct (lt_dec i #|l1|);
      [ apply H1
      | replace i with (#|l1| + (i - #|l1|)) by lia; apply H2 ].
    all: destruct H as [[??]|[??]]; try lia; auto. }
Qed.
Ltac simplify_nth_error_app_step :=
  match goal with
  | [ H : context[#|_ ++ _|] |- _ ] => rewrite app_length in H
  | [ |- context[#|_ ++ _|] ] => rewrite app_length
  | [ H : nth_error (_ ++ _) _ = Some _ |- _ ] => apply nth_error_app_inv in H
  | [ |- context[nth_error (_ ++ _) _] ] => rewrite nth_error_app_full
  | [ H : forall i x, nth_error (?l1 ++ ?l2) i = Some x -> @?P i x |- _ ]
    => pose_rename H (fst (@nth_error_app_forall_iff _ _ _ _) H)
  | [ H : (forall i x, nth_error (?l1 ++ ?l2) i = Some x -> @?P i x) -> False |- _ ]
    => pose_rename H (fun pf => H (snd (@nth_error_app_forall_iff _ _ _ _) pf))
  end.
Ltac simplify_nth_error_rev_step :=
  match goal with
  | [ H : context[#|rev _|] |- _ ] => rewrite rev_length in H
  | [ |- context[#|rev _|] ] => rewrite rev_length
  | [ H : context[#|List.rev _|] |- _ ] => rewrite List.rev_length in H
  | [ |- context[#|List.rev _|] ] => rewrite List.rev_length
  | [ H : context[nth_error (rev _) _] |- _ ] => rewrite nth_error_rev_full in H
  | [ |- context[nth_error (rev _) _] ] => rewrite nth_error_rev_full
  | [ H : context[nth_error (List.rev _) _] |- _ ] => rewrite nth_error_List_rev_full in H
  | [ |- context[nth_error (List.rev _) _] ] => rewrite nth_error_List_rev_full
  | [ H : forall i x, nth_error (@List.rev ?A ?l) i = Some x -> _ |- _ ]
    => let H' := fresh in
       (pose H' := X _ _ ltac:(rewrite <- nth_error_rev));
       clearbody H'; clear H; rename H' into H
  end.
Ltac simplify_nth_error_rev_map_step :=
  match goal with
  | [ H : context[#|rev_map _ _|] |- _ ] => rewrite rev_map_length in H
  | [ |- context[#|rev_map _ _|] ] => rewrite rev_map_length
  | [ H : context[nth_error (rev_map _ _) _] |- _ ] => rewrite nth_error_rev_map in H
  | [ |- context[nth_error (rev_map _ _) _] ] => rewrite nth_error_rev_map
  end.
Ltac simplify_nth_error_map_step :=
  match goal with
  | [ H : context[#|map _ _|] |- _ ] => rewrite map_length in H
  | [ |- context[#|map _ _|] ] => rewrite map_length
  | [ H : forall i x, nth_error (@map ?A ?B ?f ?l) i = Some x -> _ |- _ ]
    => pose proof (fun i x pf => H i _ (@map_nth_error A B f i l x pf));
       clear H
  | [ H : (forall i x, nth_error (@map ?A ?B ?f ?l) i = Some x -> @?P i x) -> False |- _ ]
    => assert ((forall i x, nth_error l i = Some x -> P i (f x)) -> False)
      by (clear -H;
          let H' := fresh in
          let i := fresh in
          intros H'; apply H; clear -H'; intros i *; specialize (H' i);
          rewrite nth_error_map; revert H'; destruct nth_error; cbn [option_map]; intro H'; inversion 1; subst; auto);
       clear H
  | [ H : context[nth_error (map _ _) _] |- _ ] => rewrite nth_error_map in H
  | [ |- context[nth_error (map _ _) _] ] => rewrite nth_error_map
  end.
Ltac simplify_nth_error_mapi_step :=
  match goal with
  | [ H : context[#|mapi _ _|] |- _ ] => rewrite mapi_length in H
  | [ |- context[#|mapi _ _|] ] => rewrite mapi_length
  | [ H : forall i x, nth_error (@mapi ?A ?B ?f ?l) i = Some x -> _ |- _ ]
    => pose proof (fun i x pf => H i _ (@mapi_nth_error A B f i l x pf));
       clear H
  | [ H : (forall i x, nth_error (@mapi ?A ?B ?f ?l) i = Some x -> @?P i x) -> False |- _ ]
    => assert ((forall i x, nth_error l i = Some x -> P i (f i x)) -> False)
      by (clear -H;
          let H' := fresh in
          let i := fresh in
          intros H'; apply H; clear -H'; intros i *; specialize (H' i);
          rewrite nth_error_mapi; revert H'; destruct nth_error; cbn [option_map]; intro H'; inversion 1; subst; auto);
       clear H
  | [ H : context[nth_error (mapi _ _) _] |- _ ] => rewrite nth_error_mapi in H
  | [ |- context[nth_error (mapi _ _) _] ] => rewrite nth_error_mapi
  end.
Ltac simplify_nth_error_mapi_rec_step :=
  match goal with
  | [ H : context[#|mapi_rec _ _ _|] |- _ ] => rewrite mapi_rec_length in H
  | [ |- context[#|mapi_rec _ _ _|] ] => rewrite mapi_rec_length
  | [ H : forall i x, nth_error (@mapi_rec ?A ?B ?f ?l ?k) i = Some x -> _ |- _ ]
    => pose proof (fun i x pf => H i _ (@mapi_rec_nth_error A B f i l x k pf));
       clear H
  | [ H : (forall i x, nth_error (@mapi_rec ?A ?B ?f ?l ?k) i = Some x -> @?P i x) -> False |- _ ]
    => assert ((forall i x, nth_error l i = Some x -> P i (f (i + k) x)) -> False)
      by (clear -H;
          let H' := fresh in
          let i := fresh in
          intros H'; apply H; clear -H'; intros i *; specialize (H' i);
          rewrite nth_error_mapi_rec; revert H'; destruct nth_error; cbn [option_map]; intro H'; inversion 1; subst; auto);
       clear H
  | [ H : context[nth_error (mapi_rec _ _ _) _] |- _ ] => rewrite nth_error_mapi_rec in H
  | [ |- context[nth_error (mapi_rec _ _ _) _] ] => rewrite nth_error_mapi_rec
  end.
Ltac simplify_nth_error_skipn_step :=
  match goal with
  | [ H : context[nth_error (skipn _ _) _] |- _ ] => rewrite nth_error_skipn in H
  | [ H : context[nth_error (skipn _ _) _] |- _ ] => setoid_rewrite nth_error_skipn in H
  | [ |- context[nth_error (skipn _ _) _] ] => rewrite nth_error_skipn
  end.
Ltac simplify_nth_error_firstn_step :=
  match goal with
  | [ H : context[nth_error (firstn _ _) _] |- _ ] => rewrite nth_error_firstn in H
  | [ H : context[nth_error (firstn _ _) _] |- _ ] => setoid_rewrite nth_error_firstn in H
  | [ |- context[nth_error (firstn _ _) _] ] => rewrite nth_error_firstn
  end.
Ltac simplify_nth_error_last_step :=
  let go T :=
    match T with
    | context[@last ?A ?l ?a]
      => let H := fresh in
         have : {l = []} + {l <> []}; [ clear; now destruct l; [ left | right ] | move => [H|H] ];
         [ assert (@last A l a = a) by now rewrite H
         | generalize (@nth_error_last A l a H) ];
         generalize dependent (@last A l a); intros; subst
    end in
  match goal with
  | [ H : ?T |- _ ] => go T
  | [ |- ?T ] => go T
  end.
Ltac simplify_nth_error_safe_nth_step :=
  let go T :=
    match T with
    | context[@safe_nth ?A ?l ?pf]
      => lazymatch pf with
         | exist ?P ?n ?isdecl
           => generalize (@nth_error_safe_nth A n l isdecl : nth_error l n = Some (safe_nth l (exist P n isdecl)));
              generalize dependent (safe_nth l (exist P n isdecl)); intros; subst
         | _ => destruct pf eqn:?; subst
         end
    end in
  match goal with
  | [ H : ?T |- _ ] => go T
  | [ |- ?T ] => go T
  end.
Ltac simplify_nth_error_map_option_out_step :=
  let go T :=
    match T with
    | context[@map_option_out ?A ?l]
      => let HS := fresh in
         let HN := fresh in
         pose proof (fun l' => proj1 (@map_option_out_Some_spec A l l')) as HS;
         pose proof (proj1 (@map_option_out_None_spec A l)) as HN;
         destruct (@map_option_out A l);
         first [ specialize (HS _ eq_refl) | clear HS ];
         first [ specialize (HN eq_refl) | clear HN ]
    end in
  match goal with
  | [ H : ?T |- _ ] => go T
  | [ |- ?T ] => go T
  end.
Ltac simplify_nth_error_saturate_diseq_step n' n :=
  assert_fails constr_eq n n';
  lazymatch goal with
  | [ H : n = n' |- _ ] => fail
  | [ H : n' = n |- _ ] => fail
  | [ H : n <> n' |- _ ] => fail
  | [ H : n' <> n |- _ ] => fail
  | [ H : n = n' -> False |- _ ] => fail
  | [ H : n' = n -> False |- _ ] => fail
  | _ => destruct (Nat.eqb_spec n n')
  end.
Ltac simplify_nth_error_saturate_diseq H' n :=
  repeat match type of H' with
    | context[_ <> ?n'] => simplify_nth_error_saturate_diseq_step n' n
    end.
Ltac simplify_nth_error_find_eq n' n :=
  first [ constr_eq n n'
        | lazymatch goal with
          | [ H : n = n' |- _ ] => idtac
          | [ H : n' = n |- _ ] => idtac
          end ].
Ltac simplify_nth_error_check_no_diseq H' n :=
  lazymatch type of H' with
  | context[_ <> n] => fail
  | _ => idtac
  end;
  match type of H' with
  | context[_ <> ?n']
    => tryif simplify_nth_error_find_eq n n' then fail 1 else fail
  | _ => idtac
  end.
Ltac simplify_nth_error_check_no_self_diseq H' n :=
  lazymatch type of H' with
  | context[n <> n] => fail
  | _ => idtac
  end;
  match type of H' with
  | context[n <> ?n']
    => tryif simplify_nth_error_find_eq n n' then fail 1 else fail
  | _ => idtac
  end;
  match type of H' with
  | context[?n' <> n]
    => tryif simplify_nth_error_find_eq n n' then fail 1 else fail
  | _ => idtac
  end;
  match type of H' with
  | context[?n' <> ?n'']
    => tryif first [ constr_eq n' n | constr_eq n'' n ]
      then (* already handled *) fail
      else tryif (simplify_nth_error_find_eq n n'; simplify_nth_error_find_eq n n'') then fail 1 else fail
  | _ => idtac
  end.
Ltac simplify_nth_error_case_step :=
  let destr c n :=
    (assert_fails has_evar (c n);
     first [ match goal with
             | [ H' : c ?n' = _ |- _ ] => simplify_nth_error_saturate_diseq_step n' n
             end
           | match goal with
             | [ H' : c ?n' = _ |- _ ] => tryif simplify_nth_error_find_eq n n' then fail 1 else fail
             | _ => idtac
             end;
             destruct (c n) eqn:? ]) in
  match goal with
  | [ H : context[match @nth_error ?A ?l ?i with _ => _ end] |- _ ] => destruct (@nth_error A l i) eqn:?
  | [ |- context[match @nth_error ?A ?l ?i with _ => _ end] ] => destruct (@nth_error A l i) eqn:?
  | [ H : context[@nth_error ?A ?ls ?n = _] |- _ ]
    => destr (@nth_error A ls) n
  | [ H : context[option_map _ (@nth_error ?A ?ls ?n)] |- _ ]
    => destr (@nth_error A ls) n; cbn [option_map] in *
  | [ |- context[@nth_error ?A ?ls ?n = _] ]
    => destr (@nth_error A ls) n
  | [ |- context[_ = @nth_error ?A ?ls ?n] ]
    => destr (@nth_error A ls) n
  | [ |- context[option_map _ (@nth_error ?A ?ls ?n)] ]
    => destr (@nth_error A ls) n; cbn [option_map] in *
  | [ H : nth_error ?ls ?n = Some _, H' : #|?ls| = #|?l| |- _ ]
    => destr (nth_error l) n
  | [ H : nth_error ?ls ?n = Some _, H' : #|?l| = #|?ls| |- _ ]
    => destr (nth_error l) n
  | [ H : nth_error ?ls ?n = None, H' : #|?ls| = #|?l| |- _ ]
    => destr (nth_error l) n
  | [ H : nth_error ?ls ?n = None, H' : #|?l| = #|?ls| |- _ ]
    => destr (nth_error l) n
  end.
Local Definition nth_error' {A} := Eval cbv [nth_error] in @nth_error A.
Global Arguments nth_error' {_} !_ !_ / .
Ltac simplify_nth_error_ctor_step :=
  first [ progress (change (@nth_error) with (@nth_error') in *;
                    cbn [nth_error'] in *;
                    change (@nth_error') with (@nth_error) in * )
        | rewrite nth_error_nil
        | match goal with
          | [ H : context[nth_error [] _] |- _ ] => rewrite nth_error_nil in H
          | [ H : context[nth_error (_ :: _) ?n] |- _ ] => is_var n; destruct n
          | [ |- context[nth_error (_ :: _) ?n] ] => is_var n; destruct n
          end ].
Ltac simplify_nth_error_fin_step :=
  first [ exfalso; assumption
        | congruence
        | match goal with
          | [ H : nth_error ?l ?x = Some _ |- _ ]
            => exfalso;
               lazymatch goal with
               | [ H' : ~x < #|l| |- _ ] => clear -H H'
               | [ H' : #|l| <= x |- _ ] => clear -H H'
               | [ H' : x = #|l| |- _ ] => clear -H H'
               | [ H' : #|l| = x |- _ ] => clear -H H'
               | _ => constr_eq x #|l|; clear -H
               end;
               apply nth_error_Some_length in H; auto; lia
          | [ H : ?x < ?y, H' : ?y <= ?x |- _ ] => exfalso; lia
          | [ H : ?x >= ?y |- _ ] => change (y <= x) in H
          | [ H : nth_error ?l ?i = None, H' : nth_error ?l' ?i = Some _ |- _ ]
            => let fin_with H'' :=
                 (exfalso; clear -H'' H H';
                  apply nth_error_Some_length in H';
                  apply nth_error_None in H) in
               lazymatch goal with
               | [ H'' : #|l| = #|l'| |- _ ] => fin_with H''
               | [ H'' : #|l'| = #|l| |- _ ] => fin_with H''
               | [ H'' : #|l| <> #|l'| |- _ ] => fail
               | [ H'' : #|l'| <> #|l| |- _ ] => fail
               | _ => is_var l; is_var l';
                      let H'' := fresh in
                      destruct (Nat.eq_dec (#|l|) (#|l'|)) as [H''|H''];
                      [ fin_with H''
                      | try (exfalso; lia) ]
               end
          end ].
Ltac simplify_nth_error_option_map_step :=
  match goal with
  | [ H : context[option_map ?f ?x = Some _] |- _ ] => destruct x eqn:?; cbv [option_map] in H
  | [ H : context[option_map ?f ?x = None] |- _ ] => destruct x eqn:?; cbv [option_map] in H
  | [ |- context[option_map ?f ?x = Some _] ] => destruct x eqn:?; cbv [option_map]
  | [ |- context[option_map ?f ?x = None] ] => destruct x eqn:?; cbv [option_map]
  end.
Ltac simplify_nth_error_specialize_step :=
  match goal with
  | [ H : forall x, ?y = Some x -> _, H' : ?y = Some _ |- _ ] => specialize (H _ H')
  | [ H : nth_error ?ls ?n = Some ?x, H' : context[nth_error ?ls _ = Some _ -> _] |- _ ]
    => progress simplify_nth_error_saturate_diseq H' n
  | [ H : nth_error ?ls ?n = Some ?x, H' : forall n' x', nth_error ?ls n' = Some x' -> _ |- _ ]
    => pose proof (fun n' x' pf' (pf : n' <> n) => H' n' x' pf');
       specialize (H' _ _ H);
       simplify_nth_error_check_no_self_diseq H' n
  | [ H : nth_error ?ls ?n = Some ?x, H' : forall n' x' x'', nth_error ?ls n' = Some x' -> nth_error ?ls' n' = Some x'' -> _ |- _ ]
    => pose proof (fun n' x' x'' pf0 pf1 (pf : n' <> n) => H' n' x' x'' pf0 pf1);
       specialize (fun x'' => H' _ _ x'' H);
       simplify_nth_error_check_no_self_diseq H' n
  | [ H : nth_error ?ls' ?n = Some ?x, H' : forall n' x' x'', nth_error ?ls n' = Some x' -> nth_error ?ls' n' = Some x'' -> _ |- _ ]
    => pose proof (fun n' x' x'' pf0 pf1 (pf : n' <> n) => H' n' x' x'' pf0 pf1);
       specialize (fun x' H'' => H' _ x' _ H'' H);
       simplify_nth_error_check_no_self_diseq H' n
  | [ H : nth_error ?ls' ?n = Some ?x, H' : forall n' x', nth_error ?ls n' = Some x' -> forall x'', nth_error ?ls' n' = Some x'' -> _ |- _ ]
    => pose proof (fun n' x' pf0 (pf : n' <> n) x'' pf1 => H' n' x' pf0 x'' pf1);
       specialize (fun x' H'' => H' _ x' H'' _ H);
       simplify_nth_error_check_no_self_diseq H' n
  | [ H : forall n x1 x2 p1 p2, S _ <> 0 -> _ |- _ ]
    => specialize (fun n x1 x2 p1 p2 => H n x1 x2 p1 p2 ltac:(congruence))
  | [ H : forall i x, nth_error (_ :: _) i = Some x -> _ |- _ ]
    => pose proof (H 0); specialize (fun i x => H (S i) x)
  | [ H : forall i x x', nth_error (_ :: _) i = Some x -> _ |- _ ]
    => pose proof (H 0); specialize (fun i x => H (S i) x)
  | [ H : forall i x x' x'', nth_error (_ :: _) i = Some x -> _ |- _ ]
    => pose proof (H 0); specialize (fun i x => H (S i) x)
  | [ H : forall x, Some ?v = Some x -> _ |- _ ] => specialize (H _ eq_refl)
  | [ H : forall x x', Some ?v = Some x -> _ |- _ ] => specialize (fun x' => H _ x' eq_refl)
  | [ H : forall i x x', nth_error _ i = Some x -> _ |- _ ]
    => specialize (fun i x pf x' => H i x x' pf)
  | [ H : forall i x x' x'', nth_error _ i = Some x -> _ |- _ ]
    => specialize (fun i x pf x' x'' => H i x x' x'' pf)
  end.
Ltac simplify_nth_error_eq_list_step :=
  match goal with
  | [ H : forall n x1 x2, nth_error ?l1 n = Some x1 -> nth_error ?l2 n = Some x2 -> x1 = x2 |- _ ]
    => first [ is_var l1 | is_var l2 ];
       (assert (l1 = l2) by now apply nth_error_Some_ext_iff); clear H
  | [ H : forall n x1, nth_error ?l1 n = Some x1 -> forall x2, nth_error ?l2 n = Some x2 -> x1 = x2 |- _ ]
    => first [ is_var l1 | is_var l2 ];
       (assert (l1 = l2) by now apply nth_error_Some_ext_iff); clear H
  | [ H : _ = _ :> list _ |- _ ]
    => rewrite <- nth_error_Some_ext_iff in H
  | [ |- _ = _ :> list _ ] => apply nth_error_ext_iff
  end.
Ltac simplify_nth_error_step :=
  first [ simplify_nth_error_ctor_step
        | simplify_nth_error_fin_step
        | simplify_nth_error_option_map_step
        | progress subst
        | progress cbn [length] in *
        | match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
          | [ H : ?x = Some _, H' : ?x = Some _ |- _ ] => rewrite H in H'
          | [ H : S _ = S _ |- _ ] => inversion H; clear H
          | [ H : S ?x <> S ?y |- _ ] => assert (x <> y) by (clear -H; congruence); clear H
          end
        | simplify_nth_error_specialize_step
        | simplify_nth_error_eq_list_step
        | match goal with
          | [ H : ?x < #|?l| -> _, H' : nth_error ?l ?x = Some _ |- _ ]
            => (idtac + (assert (x < #|l|) by now eapply nth_error_Some_length));
               forward H by assumption
          | [ H : nth_error ?l ?x = Some _, H' : nth_error ?l ?y = Some _ |- _ ]
            => destruct (@Nat.eqb_spec x y); try lia; [ progress subst | ]
          end
        | simplify_nth_error_app_step
        | simplify_nth_error_map_step
        | simplify_nth_error_mapi_step
        | simplify_nth_error_mapi_rec_step
        | simplify_nth_error_rev_map_step
        | simplify_nth_error_rev_step
        | simplify_nth_error_skipn_step
        | simplify_nth_error_firstn_step
        | simplify_nth_error_last_step
        | simplify_nth_error_safe_nth_step
        | simplify_nth_error_map_option_out_step
        | simplify_nth_error_case_step ].
Ltac simplify_nth_error := repeat simplify_nth_error_step.
Local Ltac simplify_nth_error_logic_step :=
  first [ match goal with
          | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
          | [ H : ?x <> ?y, H' : ?y <> ?x -> ?B |- _ ] => forward H' by (clear -H; easy)
          | [ H' : ?x <> S ?x -> ?B |- _ ] => forward H' by (clear; lia)
          | [ H' : S ?x <> ?x -> ?B |- _ ] => forward H' by (clear; lia)
          | [ H : ?x = ?x -> ?B |- _ ] => specialize (H eq_refl)
          | [ H : _ × _ -> _ |- _ ] => specialize (fun a b => H (a, b))
          | [ H : _ /\ _ -> _ |- _ ] => specialize (fun a b => H (conj a b))
          | [ H : forall x, ex _ -> _ |- _ ] => specialize (fun x y z => H x (ex_intro _ y z))
          | [ H : ?x = ?x |- _ ] => clear H
          | [ H : ?x <> ?x -> _ |- _ ] => clear H
          | [ H : S ?x <> S ?y -> ?B |- _ ]
            => assert (x <> y -> B) by (clear -H; intro; apply H; lia);
               clear H
          | [ H : #|?x| + 1 = #|?y| + 1 |- _ ]
            => lazymatch goal with
               | [ H : #|x| = #|y| |- _ ] => fail
               | _ => assert (#|x| = #|y|) by (clear -H; lia)
               end
          | [ H : #|?x| = #|?y|, H' : context[#|?x|] |- _ ]
            => lazymatch type of H' with
               | _ = _ :> nat => fail
               | _ = _ :> nat -> False => fail
               | _ <> _ :> nat => fail
               | _ => rewrite H in H'
               end
          | [ H : ?l <> nil |- _ ]
            => lazymatch goal with _ : #|l| <> 0 |- _ => fail | _ => idtac end;
               assert (#|l| <> 0) by now clear -H; move: H; case: l => //=
          | [ H : #|?l| <> 0 |- _ ]
            => lazymatch goal with _ : l <> [] |- _ => fail | _ => idtac end;
               assert (l <> []) by now clear -H; move: H; case: l => //=
          | [ H : #|?x| <> 0, H' : #|?x| = #|?y| |- _ ]
            => lazymatch goal with _ : #|y| <> 0 |- _ => fail | _ => idtac end;
               assert (#|y| <> 0) by now clear -H H'; move: H H'; case: x; case: y => //=
          | [ H : #|?x| <> 0, H' : #|?y| = #|?x| |- _ ]
            => lazymatch goal with _ : #|y| <> 0 |- _ => fail | _ => idtac end;
               assert (#|y| <> 0) by now clear -H H'; move: H H'; case: x; case: y => //=
          | [ H : context[?x + ?y] |- context[?y + ?x] ] => progress rewrite -> (@Nat.add_comm x y) in *
          | [ H : context[?y + ?x], H' : context[?x + ?y] |- _ ] => progress rewrite -> (@Nat.add_comm x y) in *
          | [ H : 0 <> S _ -> _ |- _ ] => specialize (H ltac:(congruence))
          | [ H : sigT _ |- _ ] => destruct H
          | [ H : ex _ |- _ ] => destruct H
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : _ × _ |- _ ] => destruct H
          | [ |- context[?x + ?y - ?x] ] => replace (x + y - x) with y by lia
          | [ H : context[?x + ?y - ?x] |- _ ] => replace (x + y - x) with y in H by lia
          | [ H : _ + _ |- _ ] => destruct H
          | [ H : sumbool _ _ |- _ ] => destruct H
          | [ H : _ \/ _ |- _ ] => destruct H
          | [ |- _ /\ _ ] => split
          | [ |- _ × _ ] => split
          | [ H : context[if ?x <? ?y then _ else _] |- _ ]
            => destruct (@Nat.ltb_spec0 x y)
          | [ |- context[if ?x <? ?y then _ else _] ]
            => destruct (@Nat.ltb_spec0 x y)
          | [ H : (?x < ?y /\ ?P) \/ (?x >= ?y /\ ?Q) |- _ ]
            => assert ({x < y /\ P} + {x >= y /\ Q})
              by (clear -H; destruct (lt_dec x y); [ left | right ]; destruct H => //; lia);
               clear H
          | [ |- is_true false ] => exfalso
          | [ |- true = false ] => exfalso
          | [ |- false = true ] => exfalso
          | [ |- Some _ = Some _ ] => apply f_equal
          end
        | progress intros ].
Local Ltac simplify_nth_error_logic := repeat first [ simplify_nth_error_step | simplify_nth_error_logic_step ].

Local Ltac handle_final_arith_step :=
  first [ match goal with
          | [ |- False ]
            => exactly_once (idtac; multimatch goal with H : _ -> False |- _ => apply H; clear H end)
          | [ H : ?Q (?P ?n ?x) |- ?Q (?P ?n' ?x') ]
            => cut (P n x = P n' x');
               [ move => <- //
               | now repeat (lia || f_equal) ]
          | [ H : ?P ?n ?x |- ?P ?n' ?x' ]
            => cut (P n x = P n' x');
               [ move => <- //
               | now repeat (lia || f_equal) ]
          | [ H : ?P ?n ?x ?y |- ?P ?n' ?x' ?y' ]
            => cut (P n x y = P n' x' y');
               [ move => <- //
               | now repeat (lia || f_equal) ]
          end ].
Local Ltac handle_final_arith := repeat handle_final_arith_step.

Lemma Forall_cons_iff A P x xs
  : @Forall A P (x :: xs) <-> (P x /\ @Forall A P xs).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma Forall_iff_nth_error A P l
  : @Forall A P l <-> (forall i d, nth_error l i = Some d -> P d).
Proof.
  rewrite Forall_nth.
  split => H i d; specialize (H i); [ specialize (H d) | ].
  all: move: (@nth_error_Some A l i) H.
  all: rewrite nth_nth_error.
  all: case: nth_error; eauto; intros *.
  all: move => <- H' //.
  all: inversion 1; subst; apply H'; congruence.
Qed.

Ltac Forall_to_nth_error_step :=
  match goal with
  | [ H : Forall _ _ |- _ ] => pose_rename H (proj1 (@Forall_iff_nth_error _ _ _) H)
  | [ H : Forall _ _ -> False |- _ ] => pose_rename H (fun pf => H (proj2 (@Forall_iff_nth_error _ _ _) pf))
  | [ |- Forall _ _ ] => apply Forall_iff_nth_error
  | [ H : context[~Forall _ _] |- _ ] => unfold not in H
  end.

Ltac In_to_nth_error_step :=
  match goal with
  | [ H : In _ _ |- _ ] => pose_rename H (proj1 (@In_iff_nth_error _ _ _) H)
  | [ H : In _ _ -> False |- _ ] => pose_rename H (fun pf => H (proj2 (@In_iff_nth_error _ _ _) pf))
  | [ |- In _ _ ] => apply In_iff_nth_error
  | [ H : context[In] |- _ ] => setoid_rewrite In_iff_nth_error in H
  | [ H : context[~In _ _] |- _ ] => unfold not in H
  | [ H : forall x, In x _ -> _ |- _ ]
    => specialize (fun n x pf => H x (@nth_error_In _ _ n x pf))
  end.

Lemma All_cons_iff A P x xs
  : @All A P (x :: xs) <~> (P x × @All A P xs).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma All_iff_nth_error A (P : A -> Type) l
  : All P l <~> (forall i x, nth_error l i = Some x -> P x).
Proof.
  split; induction l as [|?? IH].
  all: first [ inversion 1; subst | intro H; constructor; revert H ];
    intros; simplify_nth_error_logic.
Qed.

Ltac All_to_nth_error_step :=
  match goal with
  | [ H : All _ _ |- _ ] => pose_rename H (fst (@All_iff_nth_error _ _ _) H)
  | [ H : All _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@All_iff_nth_error _ _ _) pf))
  | [ |- All _ _ ] => apply All_iff_nth_error
  end.

Lemma Alli_cons_iff A P k x xs
  : @Alli A P k (x :: xs) <~> (P k x × @Alli A P (S k) xs).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma Alli_iff_nth_error A (P : nat -> A -> Type) k l
  : Alli P k l <~> (forall i x, nth_error l i = Some x -> P (k + i) x).
Proof.
  split; revert k; induction l as [|?? IH]; intro k; try specialize (IH (S k)).
  all: first [ inversion 1; subst | intro H; constructor; revert H ];
    intros; simplify_nth_error_logic; try (apply IH; clear IH; intros);
    now (rewrite Nat.add_0_r + rewrite -Nat.add_succ_comm + rewrite Nat.add_succ_comm + rewrite -> ?Nat.add_0_r in * ); tea.
Qed.

Ltac Alli_to_nth_error_step :=
  match goal with
  | [ H : Alli _ _ _ |- _ ] => pose_rename H (fst (@Alli_iff_nth_error _ _ _ _) H)
  | [ H : Alli _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@Alli_iff_nth_error _ _ _ _) pf))
  | [ |- Alli _ _ _ ] => apply Alli_iff_nth_error
  end.

Lemma Forall2_cons_iff A B P x xs y ys
  : @Forall2 A B P (x :: xs) (y :: ys) <-> (P x y /\ @Forall2 A B P xs ys).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma Forall2_iff_nth_error A B L1 L2 (P : A -> B -> Prop) :
  Forall2 P L1 L2
  <-> (#|L1| = #|L2|
        /\
          (forall n x1 x2, nth_error L1 n = Some x1
                           -> nth_error L2 n = Some x2
                           -> P x1 x2)).
Proof.
  revert L2; induction L1 as [|?? IH], L2 as [|? L2];
    try (rewrite Forall2_cons_iff IH; clear IH).
  all: cbn; split; try now inversion 1.
  all: simplify_nth_error_logic.
Qed.

Ltac Forall2_to_nth_error_step :=
  match goal with
  | [ H : Forall2 _ _ _ |- _ ] => pose_rename H (proj1 (@Forall2_iff_nth_error _ _ _ _ _) H)
  | [ H : Forall2 _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (proj2 (@Forall2_iff_nth_error _ _ _ _ _) pf))
  | [ |- Forall2 _ _ _ ] => apply Forall2_iff_nth_error
  | [ H : context[~Forall2 _ _ _] |- _ ] => unfold not in H
  end.

Lemma All2_cons_iff A B P x xs y ys
  : @All2 A B P (x :: xs) (y :: ys) <~> (P x y × @All2 A B P xs ys).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma All2_iff_nth_error A B L1 L2 (P : A -> B -> Type) :
  All2 P L1 L2
    <~> (#|L1| = #|L2|
          ×
            (forall n x1 x2, nth_error L1 n = Some x1
                             -> nth_error L2 n = Some x2
                             -> P x1 x2)).
Proof.
  revert L2; induction L1 as [|?? IH], L2 as [|? L2];
    try specialize (IH L2) as [? ?];
    try (etransitivity; [ now eapply All2_cons_iff | ]).
  all: cbn; split; try now inversion 1.
  all: simplify_nth_error_logic; eauto.
Qed.

Ltac All2_to_nth_error_step :=
  match goal with
  | [ H : All2 _ _ _ |- _ ] => pose_rename H (fst (@All2_iff_nth_error _ _ _ _ _) H)
  | [ H : All2 _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@All2_iff_nth_error _ _ _ _ _) pf))
  | [ |- All2 _ _ _ ] => apply All2_iff_nth_error
  end.

Lemma All2i_cons_iff A B P k x xs y ys
  : @All2i A B P k (x :: xs) (y :: ys) <~> (P k x y × @All2i A B P (S k) xs ys).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma All2i_iff_nth_error A B L1 L2 P k :
  @All2i A B P k L1 L2
    <~> (#|L1| = #|L2|
          ×
            (forall n x1 x2, nth_error L1 n = Some x1
                             -> nth_error L2 n = Some x2
                             -> P (k + n) x1 x2)).
Proof.
  revert L2 k; induction L1 as [|?? IH], L2 as [|? L2]; intro k;
    try specialize (IH L2 (S k));
    (tryif (etransitivity; [ now eapply All2i_cons_iff | ])
      then (etransitivity;
            [ split; [ intros [H0 H1]; eapply pair; [ exact H0 | apply IH in H1; exact H1 ] .. ] | ]; clear IH)
      else idtac).
  all: split; try now inversion 1.
  all: simplify_nth_error_logic; eauto.
  all: try now (rewrite Nat.add_0_r + rewrite -Nat.add_succ_comm + rewrite Nat.add_succ_comm + rewrite -> ?Nat.add_0_r in * ); tea.
Qed.

Ltac All2i_to_nth_error_step :=
  match goal with
  | [ H : All2i _ _ _ _ |- _ ] => pose_rename H (fst (@All2i_iff_nth_error _ _ _ _ _ _) H)
  | [ H : All2i _ _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@All2i_iff_nth_error _ _ _ _ _ _) pf))
  | [ |- All2i _ _ _ _ ] => apply All2i_iff_nth_error
  end.

Lemma All3_cons_iff A B C P x xs y ys z zs
  : @All3 A B C P (x :: xs) (y :: ys) (z :: zs) <~> (P x y z × @All3 A B C P xs ys zs).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma All3_iff_nth_error A B C L1 L2 L3 (P : A -> B -> C -> Type) :
  All3 P L1 L2 L3
    <~> (#|L1| = #|L2|
          × #|L1| = #|L3|
          ×
            (forall n x1 x2 x3, nth_error L1 n = Some x1
                                -> nth_error L2 n = Some x2
                                -> nth_error L3 n = Some x3
                                -> P x1 x2 x3)).
Proof.
  revert L2 L3; induction L1 as [|?? IH], L2 as [|? L2], L3 as [|? L3];
    try specialize (IH L2 L3) as [? ?];
    try (etransitivity; [ now eapply All3_cons_iff | ]).
  all: cbn; split; try now inversion 1.
  all: simplify_nth_error_logic; eauto.
Qed.

Ltac All3_to_nth_error_step :=
  match goal with
  | [ H : All3 _ _ _ _ |- _ ] => pose_rename H (fst (@All3_iff_nth_error _ _ _ _ _ _ _) H)
  | [ H : All3 _ _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@All3_iff_nth_error _ _ _ _ _ _ _) pf))
  | [ |- All3 _ _ _ _ ] => apply All3_iff_nth_error
  end.

Lemma forallb_Forall {A} (p : A -> bool) l
  : Forall p l <-> is_true (forallb p l).
Proof.
  split.
  induction 1; rewrite /= // H IHForall //.
  induction l; rewrite /= //. rewrite andb_and.
  intros [pa pl].
  constructor; auto.
Qed.

Lemma forallbP {A} (P : A -> Prop) (p : A -> bool) l :
  (forall x, reflect (P x) (p x)) ->
  reflect (Forall P l) (forallb p l).
Proof.
  intros Hp.
  apply iff_reflect; change (forallb p l = true) with (forallb p l : Prop); split.
  - induction 1; rewrite /= // IHForall // andb_true_r.
    now destruct (Hp x).
  - induction l; rewrite /= //. rewrite andb_and.
    intros [pa pl].
    constructor; auto. now destruct (Hp a).
Qed.

Ltac forallb_to_nth_error_step :=
  match goal with
  | [ H : is_true (forallb _ _) |- _ ] => apply forallb_Forall in H
  | [ |- is_true (forallb _ _) ] => apply forallb_Forall
  | [ H : forallb _ _ = true |- _ ] => apply forallb_Forall in H
  | [ |- forallb _ _ = true ] => apply forallb_Forall
  | [ |- context[@forallb ?A ?p ?l] ]
    => destruct (@forallbP A _ p l (fun _ => ssrbool.idP))
  | [ H : context[@forallb ?A ?p ?l] |- _ ]
    => destruct (@forallbP A _ p l (fun _ => ssrbool.idP))
  end.

Lemma allbiP {A} (P : nat -> A -> Type) (p : nat -> A -> bool) n l :
  (forall i x, reflectT (P i x) (p i x)) ->
  reflectT (Alli P n l) (alli p n l).
Proof.
  intros Hp.
  apply equiv_reflectT.
  - induction 1; rewrite /= // IHX // andb_true_r.
    now destruct (Hp n hd).
  - induction l in n |- *; rewrite /= //.
    move/andb_and => [pa pl].
    constructor; auto. now destruct (Hp n a).
Qed.

Lemma alli_Alli {A} (p : nat -> A -> bool) n l :
  alli p n l <~> Alli p n l.
Proof.
  destruct (allbiP p p n l).
  - intros. destruct (p i x); now constructor.
  - split; eauto.
  - split; eauto. by [].
Qed.

Ltac alli_to_nth_error_step :=
  match goal with
  | [ H : is_true (alli _ _ _) |- _ ] => apply alli_Alli in H
  | [ |- is_true (alli _ _ _) ] => apply alli_Alli
  | [ |- context[@alli ?A ?p ?k ?l] ]
    => destruct (@allbiP A _ p k l (fun _ _ => reflectT_pred _))
  | [ H : context[@alli ?A ?p ?k ?l] |- _ ]
    => destruct (@allbiP A _ p k l (fun _ _ => reflectT_pred _))
  end.

Lemma alli_ext {A} (p q : nat -> A -> bool) n (l : list A) :
  (forall i, p i =1 q i) ->
  alli p n l = alli q n l.
Proof.
  intros hfg.
  induction l in n |- *; simpl; auto.
  now rewrite IHl.
Qed.

#[global] Instance alli_proper {A} :
   Proper ((pointwise_relation nat (pointwise_relation A eq)) ==> eq ==> eq ==> eq) alli.
Proof.
  intros f g fg.
  intros ? ? -> ? ? ->.
  now apply alli_ext.
Qed.

Lemma forallb2_All2 {A B : Type} {p : A -> B -> bool}
      {l : list A} {l' : list B}:
  is_true (forallb2 p l l') -> All2 (fun x y => is_true (p x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; intros; try congruence.
  - constructor.
  - constructor. revert H; rewrite andb_and; intros [px pl]. auto.
    apply IHl. revert H; rewrite andb_and; intros [px pl]. auto.
Qed.

Lemma All2_forallb2 {A B : Type} {p : A -> B -> bool}
      {l : list A} {l' : list B} :
  All2 (fun x y => is_true (p x y)) l l' -> is_true (forallb2 p l l').
Proof.
  induction 1; simpl; intros; try congruence.
  rewrite andb_and. intuition auto.
Qed.

Lemma All2P {A B : Type} {p : A -> B -> bool} {l l'} :
  reflectT (All2 p l l') (forallb2 p l l').
Proof.
  apply equiv_reflectT. apply All2_forallb2. apply forallb2_All2.
Qed.

Ltac forallb2_to_nth_error_step :=
  match goal with
  | [ H : is_true (forallb2 _ _ _) |- _ ] => apply forallb2_All2 in H
  | [ |- is_true (forallb2 _ _ _) ] => apply All2_forallb2
  | [ |- context[@forallb2 ?A ?B ?p ?l ?l'] ]
    => destruct (@All2P A B p l l')
  | [ H : context[@forallb2 ?A ?B ?p ?l ?l'] |- _ ]
    => destruct (@All2P A B p l l')
  end.

Lemma OnOne2_cons_iff A P x xs y ys
  : @OnOne2 A P (x :: xs) (y :: ys) <~> ((xs = ys × P x y) + ((x = y) × @OnOne2 A P xs ys)).
Proof. split; inversion 1; subst; now intuition subst; constructor. Qed.

Lemma OnOne2_iff_nth_error A L1 L2 (P : A -> A -> Type) :
  OnOne2 P L1 L2
    <~> ({ n : nat &
                 { x1 : A & { x2 : A & nth_error L1 n = Some x1 × nth_error L2 n = Some x2 × P x1 x2 } }
                   × #|L1| = #|L2|
           × (forall n' x1 x2, nth_error L1 n' = Some x1
                                     -> nth_error L2 n' = Some x2
                                     -> n' <> n
                                     -> x1 = x2) }).
Proof.
  revert L2; induction L1 as [|?? IH], L2 as [|? L2];
    try specialize (IH L2);
    tryif (etransitivity; [ now eapply OnOne2_cons_iff | ])
    then (etransitivity;
          [ split; [ intros [H|[H0 H1]]; [ eapply inl; exact H | eapply inr, pair; [ exact H0 | apply IH in H1; exact H1 ] ] .. ]
          | ]; clear IH)
    else idtac.
  all: split; try now inversion 1.
  all: simplify_nth_error_logic; eauto; try lia.
  all: try now (exists 0 + eexists (S _)); repeat esplit; tea; simplify_nth_error_logic; eauto.
  all: try now right; repeat esplit; tea; simplify_nth_error_logic; eauto.
Qed.

Ltac OnOne2_to_nth_error_step :=
  match goal with
  | [ H : OnOne2 _ _ _ |- _ ] => pose_rename H (fst (@OnOne2_iff_nth_error _ _ _ _) H)
  | [ H : OnOne2 _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@OnOne2_iff_nth_error _ _ _ _) pf))
  | [ |- OnOne2 _ _ _ ] => apply OnOne2_iff_nth_error
  end.

Lemma OnOne2i_cons_iff A P x xs y ys k
  : @OnOne2i A P k (x :: xs) (y :: ys) <~> ((xs = ys × P k x y) + ((x = y) × @OnOne2i A P (S k) xs ys)).
Proof. split; inversion 1; subst; now intuition subst; constructor. Qed.

Lemma OnOne2i_iff_nth_error A L1 L2 P k :
  @OnOne2i A P k L1 L2
    <~> ({ n : nat &
                 { x1 : A & { x2 : A & nth_error L1 n = Some x1 × nth_error L2 n = Some x2 × P (k + n) x1 x2 } }
                   × #|L1| = #|L2|
           × (forall n' x1 x2, nth_error L1 n' = Some x1
                                     -> nth_error L2 n' = Some x2
                                     -> n' <> n
                                     -> x1 = x2) }).
Proof.
  revert L2 k; induction L1 as [|?? IH], L2 as [|? L2]; intro k;
    try specialize (IH L2 (S k));
    tryif (etransitivity; [ now eapply OnOne2i_cons_iff | ])
    then (etransitivity;
          [ split; [ intros [H|[H0 H1]]; [ eapply inl; exact H | eapply inr, pair; [ exact H0 | apply IH in H1; exact H1 ] ] .. ]
          | ]; clear IH)
    else idtac.
  all: split; try now inversion 1.
  all: simplify_nth_error_logic; eauto; try lia.
  all: try now (eexists 0 + eexists (S _) + constructor); repeat esplit; tea; (rewrite Nat.add_0_r + rewrite -Nat.add_succ_comm + rewrite Nat.add_succ_comm + rewrite -> Nat.add_0_r in * + idtac); tea; simplify_nth_error_logic; eauto.
Qed.

Ltac OnOne2i_to_nth_error_step :=
  match goal with
  | [ H : OnOne2i _ _ _ _ |- _ ] => pose_rename H (fst (@OnOne2i_iff_nth_error _ _ _ _ _) H)
  | [ H : OnOne2i _ _ _ _ |- _ ] => pose_rename H (fun pf => H (snd (@OnOne2i_iff_nth_error _ _ _ _ _) pf))
  | [ |- OnOne2i _ _ _ _ ] => apply OnOne2i_iff_nth_error
  end.

Lemma OnOne2All_cons_iff A B P b bs x xs y ys
  : @OnOne2All A B P (b :: bs) (x :: xs) (y :: ys) <~> ((xs = ys × #|bs| = #|xs| × P b x y) + ((x = y) × @OnOne2All A B P bs xs ys)).
Proof. split; inversion 1; subst; now intuition subst; constructor. Qed.

Lemma OnOne2All_iff_nth_error A B bs L1 L2 (P : B -> A -> A -> Type) :
  @OnOne2All A B P bs L1 L2
    <~> ({ n : nat &
                 { b : B & { x1 : A & { x2 : A & nth_error L1 n = Some x1 × nth_error L2 n = Some x2 × nth_error bs n = Some b × P b x1 x2 } } }
                   × #|L1| = #|L2|
           × #|bs| = #|L1|
           × (forall n' x1 x2, nth_error L1 n' = Some x1
                               -> nth_error L2 n' = Some x2
                               -> n' <> n
                               -> x1 = x2) }).
Proof.
  revert L2 bs; induction L1 as [|?? IH], L2 as [|? L2], bs as [|? bs];
    try specialize (IH L2 bs);
    tryif (etransitivity; [ now eapply OnOne2All_cons_iff | ])
    then (etransitivity;
          [ split; [ intros [H|[H0 H1]]; [ eapply inl; exact H | eapply inr, pair; [ exact H0 | apply IH in H1; exact H1 ] ] .. ]
          | ]; clear IH)
    else idtac.
  all: split; try now inversion 1.
  all: simplify_nth_error_logic; eauto; try lia.
  all: try now (exists 0 + eexists (S _)); repeat esplit; tea; simplify_nth_error_logic; eauto.
  all: try now right; repeat esplit; tea; simplify_nth_error_logic; eauto.
Qed.

Ltac OnOne2All_to_nth_error_step :=
  match goal with
  | [ H : OnOne2All _ _ _ _ |- _ ] => pose_rename H (fst (@OnOne2All_iff_nth_error _ _ _ _ _ _) H)
  | [ H : OnOne2All _ _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@OnOne2All_iff_nth_error _ _ _ _ _ _) pf))

  | [ |- OnOne2All _ _ _ _ ] => apply OnOne2All_iff_nth_error
  end.

Lemma All_fold_cons_iff A P x xs
  : @All_fold A P (x :: xs) <~> (P xs x × @All_fold A P xs).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma All_fold_iff_nth_error A P l
  : @All_fold A P l <~> (forall i x, nth_error l i = Some x -> P (skipn (S i) l) x).
Proof.
  split; induction l as [|?? IH]; cbn [skipn].
  all: first [ inversion 1; subst | intro H; constructor; revert H ].
  all: simplify_nth_error_logic.
  all: rewrite ?skipn_0; eauto.
Qed.

Ltac All_fold_to_nth_error_step :=
  match goal with
  | [ H : All_fold _ _ |- _ ] => pose_rename H (fst (@All_fold_iff_nth_error _ _ _) H)
  | [ H : All_fold _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@All_fold_iff_nth_error _ _ _) pf))
  | [ |- All_fold _ _ ] => apply All_fold_iff_nth_error
  end.

Lemma All2_fold_cons_iff A P x xs y ys
  : @All2_fold A P (x :: xs) (y :: ys) <~> (P xs ys x y × @All2_fold A P xs ys).
Proof. split; inversion 1; constructor; subst => //. Qed.

Lemma All2_fold_iff_nth_error A L1 L2 P :
  @All2_fold A P L1 L2
    <~> (#|L1| = #|L2|
          ×
            (forall n x1 x2, nth_error L1 n = Some x1
                             -> nth_error L2 n = Some x2
                             -> P (skipn (S n) L1) (skipn (S n) L2) x1 x2)).
Proof.
  revert L2; induction L1 as [|?? IH], L2 as [|? L2];
    try specialize (IH L2);
    tryif (etransitivity; [ now eapply All2_fold_cons_iff | ])
    then (etransitivity;
          [ split; [ intros [H0 H1]; eapply pair; [ exact H0 | apply IH in H1; exact H1 ] .. ]
          | ]; clear IH)
    else idtac.
  all: cbn; split; try now inversion 1.
  all: simplify_nth_error_logic; eauto.
Qed.

Ltac All2_fold_to_nth_error_step :=
  match goal with
  | [ H : All2_fold _ _ _ |- _ ] => pose_rename H (fst (@All2_fold_iff_nth_error _ _ _ _) H)
  | [ H : All2_fold _ _ _ -> False |- _ ] => pose_rename H (fun pf => H (snd (@All2_fold_iff_nth_error _ _ _ _) pf))
  | [ |- All2_fold _ _ _ ] => apply All2_fold_iff_nth_error
  end.

Ltac all_to_nth_error_step :=
  first [ Forall_to_nth_error_step
        | In_to_nth_error_step
        | All_to_nth_error_step
        | Alli_to_nth_error_step
        | Forall2_to_nth_error_step
        | All2_to_nth_error_step
        | All2i_to_nth_error_step
        | All3_to_nth_error_step
        | forallb_to_nth_error_step
        | alli_to_nth_error_step
        | forallb2_to_nth_error_step
        | OnOne2_to_nth_error_step
        | OnOne2i_to_nth_error_step
        | OnOne2All_to_nth_error_step
        | All_fold_to_nth_error_step
        | All2_fold_to_nth_error_step ].

Ltac all_to_nth_error := repeat all_to_nth_error_step.

Ltac all_via_nth_error_step := first [ all_to_nth_error_step | simplify_nth_error_step | simplify_nth_error_logic_step ].
Ltac all_via_nth_error := repeat all_via_nth_error_step.

Lemma alli_impl {A} (p q : nat -> A -> bool) n (l : list A) :
  (forall i x, p i x -> q i x) ->
  alli p n l -> alli q n l.
Proof. all_via_nth_error; eauto 7. Qed.

Lemma alli_shiftn {A} n k p (l : list A) :
  alli p (n + k) l = alli (fun i => p (n + i)) k l.
Proof.
  repeat (all_via_nth_error; handle_final_arith).
Qed.

Section alli.
  Context {A} (p q : nat -> A -> bool) (l l' : list A).

  Lemma alli_app n :
    alli p n (l ++ l') =
    alli p n l && alli p (#|l| + n) l'.
  Proof using Type.
    induction l in n |- *; simpl; auto.
    now rewrite IHl0 Nat.add_succ_r andb_assoc.
  Qed.

  Lemma alli_shift n :
    alli p n l = alli (fun i => p (n + i)) 0 l.
  Proof using Type.
    induction l in n, p |- *; simpl; auto.
    rewrite IHl0 (IHl0 _ 1) Nat.add_0_r.
    f_equal. apply alli_ext => x.
    now rewrite Nat.add_succ_r.
  Qed.

  Lemma alli_map {B} (f : B -> A) n bs : alli p n (map f bs) = alli (fun i => p i ∘ f) n bs.
  Proof using Type.
    induction bs in n |- *; simpl; auto.
    now rewrite IHbs.
  Qed.
End alli.

Lemma alli_mapi {A B} (f : nat -> A -> bool) (g : nat -> B -> A) n l :
  alli f n (mapi_rec g l n) = alli (fun i x => f i (g i x)) n l.
Proof.
  revert n; induction l => n; simpl; auto.
  now rewrite IHl.
Qed.

Lemma forallb2_refl :
  forall A (R : A -> A -> bool),
    (forall x, R x x) ->
    forall l, forallb2 R l l.
Proof.
  intros A R R_refl l.
  induction l.
  - reflexivity.
  - simpl. rewrite R_refl. assumption.
Qed.

Lemma forallb2_map :
  forall A B C D (R : A -> B -> bool) f g (l : list C) (l' : list D),
    forallb2 R (map f l) (map g l') =
    forallb2 (fun x y => R (f x) (g y)) l l'.
Proof.
  intros A B C D R f g l l'.
  induction l in l' |- *.
  - destruct l' => //.
  - destruct l' => /= //; rewrite IHl //.
Qed.

Lemma forall_map_spec {A B} {l} {f g : A -> B} :
  Forall (fun x => f x = g x) l <->
  map f l = map g l.
Proof.
  split.
  induction 1; simpl; trivial.
  now rewrite IHForall H.
  induction l => /= // [=] Ha Hl; constructor; auto.
Qed.

Lemma forall_map_id_spec {A} {l} {f : A -> A} :
  Forall (fun x => f x = x) l <-> map f l = l.
Proof.
  rewrite -{3}(map_id l). apply forall_map_spec.
Qed.

Lemma forallb_ext {A} (p q : A -> bool) : p =1 q -> forallb p =1 forallb q.
Proof.
  intros hpq l.
  induction l; simpl; auto.
  now rewrite (hpq a) IHl.
Qed.

#[global] Instance forallb_proper {A} : Proper (`=1` ==> eq ==> eq) (@forallb A).
Proof.
  intros f g Hfg ? ? ->. now apply forallb_ext.
Qed.

Lemma forallbP_cond {A} (P Q : A -> Prop) (p : A -> bool) l :
  Forall Q l ->
  (forall x, Q x -> reflect (P x) (p x)) -> reflect (Forall P l) (forallb p l).
Proof.
  intros HQ Hp.
  apply iff_reflect; split.
  - induction HQ; intros HP; depelim HP; rewrite /= // IHHQ // andb_true_r.
    now destruct (Hp x H).
  - induction HQ; rewrite /= //. move/andb_and => [pa pl].
    constructor; auto. now destruct (Hp _ H).
Qed.

Lemma nth_error_forallb {A} {p : A -> bool} {l : list A} {n x} :
  nth_error l n = Some x -> forallb p l -> p x.
Proof.
  intros Hnth HPl.
  induction l in n, Hnth, HPl |- * => //.
  - rewrite nth_error_nil in Hnth => //.
  - destruct n => /=; noconf Hnth.
    * now move: HPl => /= /andb_and.
    * eapply IHl; tea. now move: HPl => /andb_and.
Qed.

Lemma forallb_nth_error {A} P l n :
  @forallb A P l -> on_Some_or_None P (nth_error l n).
Proof.
  induction l in n |- *.
  - intros _. destruct n; constructor.
  - intro H. apply forallb_Forall in H.
    inv H. destruct n; cbn; auto.
    now apply forallb_Forall in H1; eauto.
Qed.

Lemma map_eq_inj {A B} (f g : A -> B) l: map f l = map g l ->
                                         All (fun x => f x = g x) l.
Proof.
  induction l. simpl. constructor. simpl. intros [=]. constructor; auto.
Qed.

(** Generic strategy for dealing with Forall/forall, etc:

    1) Move all boolean foralls into All/All2 (in the goal and the context).
    2) Merge all context Foralls into one
    3) Apply Forall implication
    4) optionally simplify and call eauto.
*)

Lemma Forall_mix {A} (P Q : A -> Prop) : forall l, Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
Proof.
  intros l Hl Hq. induction Hl; inv Hq; constructor; auto.
Qed.

Lemma Forall_skipn {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof.
  intros H. revert n; induction H; intros n. rewrite skipn_nil; auto.
  destruct n; simpl.
  - rewrite /skipn. constructor; auto.
  - now auto.
Qed.

Lemma Forall_firstn {A} (P : A -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof.
  intros H. revert n; induction H; intros n. rewrite firstn_nil; auto.
  destruct n; simpl.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma All2_refl {A} {P : A -> A -> Type} l :
  (forall x, P x x) ->
  All2 P l l.
Proof.
  intros HP. induction l; constructor; auto.
Qed.

Lemma forallb2_app {A B} (p : A -> B -> bool) l l' q q' :
  is_true (forallb2 p l l' && forallb2 p q q')
  -> is_true (forallb2 p (l ++ q) (l' ++ q')).
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  move=> /andb_and[/andb_and[pa pl] pq]. now rewrite pa IHl // pl pq.
Qed.

Lemma All2_map_equiv {A B C D} {R : C -> D -> Type} {f : A -> C} {g : B -> D} {l l'} :
  All2 (fun x y => R (f x) (g y)) l l' <~> All2 R (map f l) (map g l').
Proof.
  split.
  - induction 1; simpl; constructor; try congruence; try assumption.
  - induction l in l' |- *; destruct l'; intros H; depelim H; constructor; auto.
Qed.

Lemma All2_map {A B C D} {R : C -> D -> Type} {f : A -> C} {g : B -> D} {l l'} :
  All2 (fun x y => R (f x) (g y)) l l' -> All2 R (map f l) (map g l').
Proof. apply All2_map_equiv. Qed.

Lemma All2_map_inv {A B C D} {R : C -> D -> Type} {f : A -> C} {g : B -> D} {l l'} :
  All2 R (map f l) (map g l') -> All2 (fun x y => R (f x) (g y)) l l'.
Proof. apply All2_map_equiv. Qed.

(* Lemma All2_List_Forall_mix_left {A : Type} {P : A -> Prop} {Q : A -> A -> Prop} *)
(*       {l l' : list A} : *)
(*     Forall P l -> All2 Q l l' -> All2 (fun x y => P x /\ Q x y) l l'. *)
(* Proof. *)
(*   induction 2; simpl; intros; constructor. *)
(*   inv H; intuition auto. *)
(*   apply IHX. inv H; intuition auto. *)
(* Qed. *)

(* Lemma All2_List_Forall_mix_right {A : Type} {P : A -> Prop} {Q : A -> A -> Prop} *)
(*       {l l' : list A} : *)
(*     Forall P l' -> All2 Q l l' -> All2 (fun x y => P y /\ Q x y) l l'. *)
(* Proof. *)
(*   induction 2; simpl; intros; constructor. *)
(*   inv H; intuition auto. *)
(*   apply IHX. inv H; intuition auto. *)
(* Qed. *)

Lemma All2_All_mix_left {A B} {P : A -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l -> All2 Q l l' -> All2 (fun x y => (P x * Q x y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma All2_All_mix_right {A B} {P : B -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l' -> All2 Q l l' -> All2 (fun x y => (Q x y * P y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma All2i_All_mix_left {A B} {P : A -> Type} {Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All P l -> All2i Q n l l' -> All2i (fun i x y => (P x * Q i x y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma All2i_All_mix_right {A B} {P : B -> Type} {Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All P l' -> All2i Q n l l' -> All2i (fun i x y => (Q i x y * P y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma All2i_All2_mix_left {A B} {P : A -> B -> Type} {Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All2 P l l' -> All2i Q n l l' -> All2i (fun i x y => (P x y * Q i x y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma Forall_All {A : Type} (P : A -> Prop) l :
  Forall P l -> All P l.
Proof.
  induction l; intros H; constructor; auto. inv H. auto.
  apply IHl. inv H; auto.
Qed.

Lemma All_Forall {A : Type} (P : A -> Prop) l :
  All P l -> Forall P l.
Proof. induction 1; constructor; auto. Qed.

Lemma forallb_All {A} (p : A -> bool) l : is_true (forallb p l) -> All p l.
Proof.
  move/forallb_Forall. apply Forall_All.
Qed.

Lemma All_forallb {A} (p : A -> bool) l : All p l -> is_true (forallb p l).
Proof.
  move/All_Forall. apply forallb_Forall.
Qed.

Lemma All_firstn {A} {P : A -> Type} {l} {n} : All P l -> All P (firstn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All_skipn {A} {P : A -> Type} {l} {n} : All P l -> All P (skipn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All_app {A} {P : A -> Type} {l l'} : All P (l ++ l') -> All P l * All P l'.
Proof.
  induction l; simpl; auto. intros H; depelim H; constructor; intuition auto.
Qed.

Lemma All_app_inv {A} (P : A -> Type) l l' : All P l -> All P l' -> All P (l ++ l').
Proof.
  intros Hl Hl'. induction Hl. apply Hl'.
  constructor; intuition auto.
Defined.

Lemma All_True {A} l : All (fun x : A => True) l.
Proof.
  induction l; intuition auto.
Qed.

Lemma All_tip {A} {P : A -> Type} {a : A} : P a <~> All P [a].
Proof. split; intros. repeat constructor; auto. now depelim X. Qed.

Lemma All_mix {A} {P : A -> Type} {Q : A -> Type} {l} :
  All P l -> All Q l -> All (fun x => (P x * Q x)%type) l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma All2_All_left {A B} {P : A -> B -> Type} {Q : A -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q x) ->
  All Q l.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_All_right {A B} {P : A -> B -> Type} {Q : B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q y) ->
  All Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_right {A B} {P : B -> Type} {l : list A} {l'} :
  All2 (fun x y => P y) l l' -> All P l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_impl_All2 {A B} {P Q : A -> B -> Type} {l l'} :
    All2 P l l' ->
    All2 (fun x y => P x y -> Q x y) l l' ->
    All2 Q l l'.
Proof.
  induction 1; inversion 1; constructor; auto.
Qed.

Lemma All2_impl {A B} {P Q : A -> B -> Type} {l l'} :
    All2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    All2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_eq_eq {A} (l l' : list A) : l = l' -> All2 (fun x y => x = y) l l'.
Proof.
  intros ->. induction l';  constructor; auto.
Qed.

Lemma All2_reflexivity {A} {P : A -> A -> Type} :
  CRelationClasses.Reflexive P -> CRelationClasses.Reflexive (All2 P).
Proof.
  intros hp x. eapply All2_refl. intros; reflexivity.
Qed.

Lemma All2_symmetry {A} (R : A -> A -> Type) :
  CRelationClasses.Symmetric R ->
  CRelationClasses.Symmetric (All2 R).
Proof.
  intros HR x y l.
  induction l; constructor; auto.
Qed.

Lemma All2_transitivity {A} (R : A -> A -> Type) :
  CRelationClasses.Transitive R ->
  CRelationClasses.Transitive (All2 R).
Proof.
  intros HR x y z l; induction l in z |- *; auto.
  intros H; inv H. constructor; eauto.
Qed.

Lemma All2_apply {A B C} {D : A -> B -> C -> Type} {l : list B} {l' : list C} :
  forall (a : A),
    All2 (fun x y => forall a : A, D a x y) l l' ->
    All2 (fun x y => D a x y) l l'.
Proof.
  intros a all. eapply (All2_impl all); auto.
Qed.

Lemma All2_apply_arrow {A B C} {D : B -> C -> Type} {l : list B} {l' : list C} :
  A -> All2 (fun x y => A -> D x y) l l' ->
  All2 (fun x y => D x y) l l'.
Proof.
  intros a all. eapply (All2_impl all); auto.
Qed.

Lemma All2_apply_dep_arrow {B C} {A} {D : B -> C -> Type} {l : list B} {l' : list C} :
  All A l ->
  All2 (fun x y => A x -> D x y) l l' ->
  All2 D l l'.
Proof.
  intros a all.
  eapply All2_All_mix_left in all; tea.
  eapply (All2_impl all); intuition auto.
Qed.

Lemma All2_apply_dep_All {B C} {A} {D : C -> Type} {l : list B} {l' : list C} :
  All A l ->
  All2 (fun x y => A x -> D y) l l' ->
  All D l'.
Proof.
  intros a all.
  eapply All2_All_mix_left in all; tea.
  eapply All2_impl in all. 2:{ intros x y [ha hd]. exact (hd ha). }
  eapply All2_All_right; tea. auto.
Qed.


Lemma All2i_All_left {A B} {P : nat -> A -> B -> Type} {Q : A -> Type} {n l l'} :
  All2i P n l l' ->
  (forall i x y, P i x y -> Q x) ->
  All Q l.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2i_All_right {A B} {P : nat -> A -> B -> Type} {Q : B -> Type} {n l l'} :
  All2i P n l l' ->
  (forall i x y, P i x y -> Q y) ->
  All Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_dep_impl {A B} {P : A -> B -> Type} {P' Q' : forall a b, P a b -> Type} {l l'} {a : All2 P l l'} :
    All2_dep P' a ->
    (forall x y r, P' x y r -> Q' x y r) ->
    All2_dep Q' a.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All_refl {A} (P : A -> Type) l : (forall x, P x) -> All P l.
Proof.
  intros Hp; induction l; constructor; auto.
Qed.

Lemma All_rev_map {A B} (P : A -> Type) f (l : list B) : All (fun x => P (f x)) l -> All P (rev_map f l).
Proof. induction 1. constructor. rewrite rev_map_cons. apply All_app_inv; auto. Qed.

Lemma All_rev (A : Type) (P : A -> Type) (l : list A) : All P l -> All P (List.rev l).
Proof.
  induction l using rev_ind. constructor. rewrite rev_app_distr.
  simpl. intros X; apply All_app in X as [? ?]. inversion a0; intuition auto.
Qed.

Lemma All_rev_inv {A} (P : A -> Type) (l : list A) : All P (List.rev l) -> All P l.
Proof.
  induction l using rev_ind. constructor.
  intros. rewrite rev_app_distr in X. simpl.
  apply All_app in X as [Allx Alll]. inv Allx.
   apply All_app_inv; intuition eauto.
Qed.

Lemma All_impl_All {A} {P Q} {l : list A} : All P l -> All (fun x => P x -> Q x) l -> All Q l.
Proof. induction 1; inversion 1; constructor; intuition auto. Qed.

Lemma Alli_impl_Alli {A} {P Q} (l : list A) {n} : Alli P n l -> Alli (fun n x => P n x -> Q n x) n l -> Alli Q n l.
Proof. induction 1; inversion 1; constructor; intuition auto. Defined.

Lemma All_impl {A} {P Q} {l : list A} : All P l -> (forall x, P x -> Q x) -> All Q l.
Proof. induction 1; try constructor; intuition auto. Qed.

Lemma Alli_impl {A} {P Q} (l : list A) {n} : Alli P n l -> (forall n x, P n x -> Q n x) -> Alli Q n l.
Proof. induction 1; try constructor; intuition auto. Defined.

Lemma All_map {A B} {P : B -> Type} {f : A -> B} {l : list A} :
  All (fun x => P (f x)) l -> All P (map f l).
Proof. induction 1; constructor; auto. Qed.

Lemma All_map_inv {A B} (P : B -> Type) (f : A -> B) l : All P (map f l) -> All (fun x => P (f x)) l.
Proof. induction l; intros Hf; inv Hf; try constructor; eauto. Qed.

Lemma In_All {A} {P : A -> Type} l :
    (∀ x : A, In x l -> P x) -> All P l.
Proof.
  induction l; cbn; constructor; auto.
Qed.

Lemma All_nth_error :
  forall A P l i x,
    @All A P l ->
    nth_error l i = Some x ->
    P x.
Proof.
  intros A P l i x h e.
  induction h in i, x, e |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in e. inversion e. subst. clear e.
      assumption.
    + simpl in e. eapply IHh in e.
      assumption.
Qed.

Lemma Alli_mix {A} {P : nat -> A -> Type} {Q : nat -> A -> Type} {n l} :
  Alli P n l -> Alli Q n l -> Alli (fun n x => (P n x * Q n x)%type) n l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma Alli_All {A} {P : nat -> A -> Type} {Q : A -> Type} {l n} :
  Alli P n l ->
  (forall n x, P n x -> Q x) ->
  All Q l.
Proof. induction 1; constructor; eauto. Qed.

Lemma Alli_app {A} (P : nat -> A -> Type) n l l' : Alli P n (l ++ l') -> Alli P n l * Alli P (length l + n) l'.
Proof.
  induction l in n, l' |- *; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto. constructor; auto. eapply IHl; eauto.
  simpl. replace (S (#|l| + n)) with (#|l| + S n) by lia.
  eapply IHl; eauto.
Qed.

Lemma Alli_nth_error :
  forall A P k l i x,
    @Alli A P k l ->
    nth_error l i = Some x ->
    P (k + i) x.
Proof.
  intros A P k l i x h e.
  induction h in i, x, e |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in e. inversion e. subst. clear e.
      replace (n + 0) with n by lia.
      assumption.
    + simpl in e. eapply IHh in e.
      replace (n + S i) with (S n + i) by lia.
      assumption.
Qed.

Lemma forall_nth_error_All :
  forall {A} (P : A -> Type) l,
    (forall i x, nth_error l i = Some x -> P x) ->
    All P l.
Proof.
  intros A P l h.
  induction l.
  - constructor.
  - constructor.
    + specialize (h 0 a eq_refl). assumption.
    + eapply IHl. intros i x e. eapply (h (S i)). assumption.
Qed.

Lemma forall_nth_error_Alli :
  forall {A} (P : nat -> A -> Type) k l,
    (forall i x, nth_error l i = Some x -> P (k + i) x) ->
    Alli P k l.
Proof.
  intros A P k l h.
  induction l in k, h |- *.
  - constructor.
  - constructor.
    + specialize (h 0 a eq_refl). now rewrite Nat.add_0_r in h.
    + apply IHl. intros. specialize (h (S i) x H).
      simpl. now replace (S (k + i)) with (k + S i) by lia.
Qed.

Lemma Alli_mapi {A B} {P : nat -> B -> Type} (f : nat -> A -> B) k l :
  Alli (fun n a => P n (f n a)) k l <~> Alli P k (mapi_rec f l k).
Proof.
  split.
  { induction 1. simpl. constructor.
    simpl. constructor; eauto. }
  { induction l in k |- *. simpl. constructor.
    simpl. intros. inversion X. constructor; eauto. }
Qed.

Lemma Alli_shift {A} {P : nat -> A -> Type} k l :
  Alli (fun x => P (S x)) k l ->
  Alli P (S k) l.
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma Alli_rev {A} {P : nat -> A -> Type} k l :
  Alli P k l ->
  Alli (fun k' => P (Nat.pred #|l| - k' + k)) 0 (List.rev l).
Proof.
  revert k.
  induction l using rev_ind; simpl; intros; try constructor.
  eapply Alli_app in X. intuition.
  rewrite rev_app_distr. rewrite app_length.
  simpl. constructor.
  replace (Nat.pred (#|l| + 1) - 0) with #|l| by lia.
  inversion b. eauto. specialize (IHl _ a).
  eapply Alli_shift. eapply Alli_impl. eauto.
  simpl; intros.
  now replace (Nat.pred (#|l| + 1) - S n) with (Nat.pred #|l| - n) by lia.
Qed.

Lemma Alli_rev_inv {A: Type} (P : nat -> A -> Type) (k : nat) (l : list A) :
  Alli P k (List.rev l) ->
  Alli (fun k' : nat => P (Nat.pred #|l| - k' + k)) 0 l.
Proof.
  intros alli.
  eapply Alli_rev in alli. rewrite List.rev_involutive in alli.
  now len in alli.
Qed.

Lemma Alli_app_inv {A} {P} {l l' : list A} {n} : Alli P n l -> Alli P (n + #|l|) l' -> Alli P n (l ++ l').
Proof.
  induction 1; simpl; auto.  now rewrite Nat.add_0_r.
  rewrite Nat.add_succ_r. simpl in IHX.
  intros H; specialize (IHX H).
  constructor; auto.
Qed.

Lemma Alli_rev_nth_error {A} (l : list A) n P x :
  Alli P 0 (List.rev l) ->
  nth_error l n = Some x ->
  P (#|l| - S n) x.
Proof.
  induction l in x, n |- *; simpl.
  { rewrite nth_error_nil; discriminate. }
  move/Alli_app => [Alll Alla]. inv Alla. clear X0.
  destruct n as [|n'].
  - move=> [=] <-. rewrite List.rev_length Nat.add_0_r in X.
    now rewrite Nat.sub_0_r.
  - simpl. eauto.
Qed.

Lemma Alli_shiftn {A} {P : nat -> A -> Type} k l n :
  Alli (fun x => P (n + x)) k l -> Alli P (n + k) l.
Proof.
  induction 1; simpl; constructor; auto.
  now rewrite Nat.add_succ_r in IHX.
Qed.

Lemma Alli_shiftn_inv {A} {P : nat -> A -> Type} k l n :
  Alli P (n + k) l -> Alli (fun x => P (n + x)) k l.
Proof.
  induction l in n, k |- *; simpl; constructor; auto.
  inv X; auto. inv X; auto. apply IHl.
  now rewrite Nat.add_succ_r.
Qed.

Lemma Alli_All_mix {A} {P : nat -> A -> Type} (Q : A -> Type) k l :
  Alli P k l -> All Q l -> Alli (fun k x => (P k x) * Q x)%type k l.
Proof.
  induction 1; constructor; try inversion X0; intuition auto.
Qed.

Lemma OnOne2_All_mix_left {A} {P : A -> A -> Type} {Q : A -> Type} {l l'} :
  All Q l -> OnOne2 P l l' -> OnOne2 (fun x y => (P x y * Q x)%type) l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2_app {A} (P : A -> A -> Type) l tl tl' : OnOne2 P tl tl' -> OnOne2 P (l ++ tl) (l ++ tl').
Proof. induction l; simpl; try constructor; auto. Qed.

Lemma OnOne2_app_r {A} (P : A -> A -> Type) l l' tl :
  OnOne2 P l l' ->
  OnOne2 P (l ++ tl) (l' ++ tl).
Proof. induction 1; constructor; auto. Qed.

Lemma OnOne2_length {A} {P} {l l' : list A} : OnOne2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; congruence. Qed.

Lemma OnOne2_mapP {A B} {P} {l l' : list A} (f : A -> B) :
  OnOne2 (on_rel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. Qed.

Lemma OnOne2_map {A B} {P : B -> B -> Type} {l l' : list A} (f : A -> B) :
  OnOne2 (on_Trel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. Qed.

Lemma OnOne2_sym {A} (P : A -> A -> Type) l l' : OnOne2 (fun x y => P y x) l' l -> OnOne2 P l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2_exist {A} (P : A -> A -> Type) (Q : A -> A -> Type) l l' :
  OnOne2 P l l' ->
  (forall x y, P x y -> ∑ z, Q x z × Q y z) ->
  ∑ r, (OnOne2 Q l r × OnOne2 Q l' r).
Proof.
  intros H HPQ. induction H.
  - destruct (HPQ _ _ p). destruct p0.
    now exists (x :: tl); intuition constructor.
               - destruct IHOnOne2 as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.

(* Induction principle on OnOne2 when the relation also depends
     on one of the lists, and should not change.
   *)
Lemma OnOne2_ind_l :
  forall A (R : list A -> A -> A -> Type)
    (P : forall L l l', OnOne2 (R L) l l' -> Type),
    (forall L x y l (r : R L x y), P L (x :: l) (y :: l) (OnOne2_hd _ _ _ l r)) ->
    (forall L x l l' (h : OnOne2 (R L) l l'),
        P L l l' h ->
        P L (x :: l) (x :: l') (OnOne2_tl _ x _ _ h)
    ) ->
    forall l l' h, P l l l' h.
Proof.
  intros A R P hhd htl l l' h. induction h ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l3 l2 ->
    (forall x x' y, R1 x y -> R2 x' y -> ∑ z : A, R3 x z × R2 x' z) ->
    ∑ l4, OnOne2 R3 l1 l4 × All2 R2 l3 l4.
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (h _ _ _ p X) as hh.
    destruct hh as [? [? ?]].
    eexists. constructor.
      * constructor. eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
    eexists. constructor.
      * eapply OnOne2_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All_r :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l2 l3 ->
    (forall x x' y, R1 x y -> R2 y x' -> ∑ z : A, R3 x z × R2 z x') ->
    ∑ l4, ( OnOne2 R3 l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (h _ _ _ p X) as hh.
      destruct hh as [? [? ?]].
      eexists. split.
      * constructor. eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
      eexists. split.
      * eapply OnOne2_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2_split :
  forall A (P : A -> A -> Type) l l',
    OnOne2 P l l' ->
    ∑ x y u v,
      P x y ×
      (l = u ++ x :: v /\
      l' = u ++ y :: v).
Proof.
  intros A P l l' h.
  induction h.
  - exists hd, hd', [], tl.
    intuition eauto.
  - destruct IHh as [x [y [u [v ?]]]].
    exists x, y, (hd :: u), v.
    intuition eauto. all: subst. all: reflexivity.
Qed.

Lemma OnOne2_impl {A} {P Q} {l l' : list A} :
  OnOne2 P l l' ->
  (forall x y, P x y -> Q x y) ->
  OnOne2 Q l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Lemma OnOne2_nth_error {A} (l l' : list A) n t P :
  OnOne2 P l l' ->
  nth_error l n = Some t ->
  ∑ t', (nth_error l' n = Some t') *
  ((t = t') + (P t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  - intros [= ->]. exists hd'; intuition auto.
  - exists t. intuition auto.
  - destruct n; simpl; auto.
    intros [= ->]. exists t; intuition auto.
Qed.

Lemma OnOne2_nth_error_r {A} (l l' : list A) n t' P :
  OnOne2 P l l' ->
  nth_error l' n = Some t' ->
  ∑ t, (nth_error l n = Some t) *
  ((t = t') + (P t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  - intros [= ->]. exists hd; intuition auto.
  - exists t'. intuition auto.
  - destruct n; simpl; auto.
    intros [= ->]. exists t'; intuition auto.
Qed.



Lemma OnOne2_impl_All_r {A} (P : A -> A -> Type) (Q : A -> Type) l l' :
  (forall x y, Q x -> P x y -> Q y) ->
  OnOne2 P l l' -> All Q l -> All Q l'.
Proof.
  intros HPQ.
  induction 1; intros H; depelim H; constructor; auto.
  now eapply HPQ.
Qed.

Lemma OnOne2_All2_All2 {A : Type} {l1 l2 l3 : list A} {R1 R2 R3  : A -> A -> Type} :
  OnOne2 R1 l1 l2 ->
  All2 R2 l1 l3 ->
  (forall x y, R2 x y -> R3 x y) ->
  (forall x y z : A, R1 x y -> R2 x z -> R3 y z) ->
  All2 R3 l2 l3.
Proof.
  intros o. induction o in l3 |- *.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf'  _ _ _ p r). constructor; auto.
  eapply All2_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo _ H Hf).
  constructor; auto.
Qed.

Lemma OnOne2_All_All {A : Type} {l1 l2 : list A} {R1  : A -> A -> Type} {R2 R3 : A -> Type} :
  OnOne2 R1 l1 l2 ->
  All R2 l1 ->
  (forall x, R2 x -> R3 x) ->
  (forall x y : A, R1 x y -> R2 x -> R3 y) ->
  All R3 l2.
Proof.
  intros o. induction o.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf' _ _ p r). constructor; auto.
  eapply All_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo H Hf).
  constructor; auto.
Qed.

Lemma OnOne2i_All_mix_left {A} {P : nat -> A -> A -> Type} {Q : A -> Type} {i l l'} :
  All Q l -> OnOne2i P i l l' -> OnOne2i (fun i x y => (P i x y * Q x)%type) i l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2i_app {A} (P : nat -> A -> A -> Type) {i l tl tl'} :
  OnOne2i P (#|l| + i) tl tl' ->
  OnOne2i P i (l ++ tl) (l ++ tl').
Proof. induction l in i |- *; simpl; try constructor; eauto.
  eapply IHl. now rewrite Nat.add_succ_r.
Qed.

Lemma OnOne2i_app_r {A} (P : nat -> A -> A -> Type) i l l' tl :
  OnOne2i P i l l' ->
  OnOne2i P i (l ++ tl) (l' ++ tl).
Proof. induction 1; constructor; auto. Qed.

Lemma OnOne2i_length {A} {P} {i} {l l' : list A} : OnOne2i P i l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; congruence. Qed.

Lemma OnOne2i_mapP {A B} {P} {i} {l l' : list A} (f : A -> B) :
  OnOne2i (fun i => on_rel (P i) f) i l l' -> OnOne2i P i (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. Qed.

Lemma OnOne2i_map {A B} {P : nat -> B -> B -> Type} {i} {l l' : list A} (f : A -> B) :
  OnOne2i (fun i => on_Trel (P i) f) i l l' -> OnOne2i P i (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. Qed.

Lemma OnOne2i_sym {A} (P : nat -> A -> A -> Type) i l l' : OnOne2i (fun i x y => P i y x) i l' l -> OnOne2i P i l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2i_exist {A} (P : nat -> A -> A -> Type) (Q : nat -> A -> A -> Type) i l l' :
  OnOne2i P i l l' ->
  (forall i x y, P i x y -> ∑ z, Q i x z × Q i y z) ->
  ∑ r, (OnOne2i Q i l r × OnOne2i Q i l' r).
Proof.
  intros H HPQ. induction H.
  - destruct (HPQ _ _ _ p). destruct p0.
    now exists (x :: tl); intuition constructor.
               - destruct IHOnOne2i as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.

(* Induction principle on OnOne2i when the relation also depends
     on one of the lists, and should not change.
   *)
Lemma OnOne2i_ind_l :
  forall A (R : list A -> nat -> A -> A -> Type)
    (P : forall L i l l', OnOne2i (R L) i l l' -> Type),
    (forall L i x y l (r : R L i x y), P L i (x :: l) (y :: l) (OnOne2i_hd _ _ _ _ l r)) ->
    (forall L i x l l' (h : OnOne2i (R L) (S i) l l'),
        P L (S i) l l' h ->
        P L i (x :: l) (x :: l') (OnOne2i_tl _ i x _ _ h)
    ) ->
    forall i l l' h, P l i l l' h.
Proof.
  intros A R P hhd htl i l l' h. induction h ; eauto.
Qed.

Lemma OnOne2i_impl_exist_and_All :
  forall A i (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2i R1 i l1 l2 ->
    All2 R2 l3 l2 ->
    (forall i x x' y, R1 i x y -> R2 x' y -> ∑ z : A, R3 i x z × R2 x' z) ->
    ∑ l4, OnOne2i R3 i l1 l4 × All2 R2 l3 l4.
Proof.
  intros A i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (h _ _ _ _ p X) as hh.
    destruct hh as [? [? ?]].
    eexists. constructor.
      * constructor. eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
    eexists. constructor.
      * eapply OnOne2i_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2i_impl_exist_and_All_r :
  forall A i (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2i R1 i l1 l2 ->
    All2 R2 l2 l3 ->
    (forall i x x' y, R1 i x y -> R2 y x' -> ∑ z : A, R3 i x z × R2 z x') ->
    ∑ l4, ( OnOne2i R3 i l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (h _ _ _ _ p X) as hh.
      destruct hh as [? [? ?]].
      eexists. split.
      * constructor. eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
      eexists. split.
      * eapply OnOne2i_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2i_split :
  forall A (P : nat -> A -> A -> Type) i l l',
    OnOne2i P i l l' ->
    ∑ i x y u v,
      P i x y ×
      (l = u ++ x :: v /\
      l' = u ++ y :: v).
Proof.
  intros A P i l l' h.
  induction h.
  - exists i, hd, hd', [], tl.
    intuition eauto.
  - destruct IHh as [i' [x [y [u [v ?]]]]].
    exists i', x, y, (hd :: u), v.
    intuition eauto. all: subst. all: reflexivity.
Qed.

Lemma OnOne2i_impl {A} {P Q} {i} {l l' : list A} :
  OnOne2i P i l l' ->
  (forall i x y, P i x y -> Q i x y) ->
  OnOne2i Q i l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Lemma OnOne2i_nth_error {A} (l l' : list A) i n t P :
  OnOne2i P i l l' ->
  nth_error l n = Some t ->
  ∑ t', (nth_error l' n = Some t') *
  ((t = t') + (P (i + n)%nat t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  - intros [= ->]. exists hd'; rewrite Nat.add_0_r; intuition auto.
  - exists t. intuition auto.
  - destruct n; simpl; rewrite ?Nat.add_succ_r /=; auto.
    intros [= ->]. exists t; intuition auto.
    apply IHX.
Qed.

Lemma OnOne2i_nth_error_r {A} i (l l' : list A) n t' P :
  OnOne2i P i l l' ->
  nth_error l' n = Some t' ->
  ∑ t, (nth_error l n = Some t) *
  ((t = t') + (P (i + n)%nat t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  - intros [= ->]. rewrite Nat.add_0_r; exists hd; intuition auto.
  - exists t'. intuition auto.
  - destruct n; simpl; auto.
    intros [= ->]. exists t'; intuition auto.
    rewrite Nat.add_succ_r; apply IHX.
Qed.

Lemma OnOne2All_All_mix_left {A B} {P : B -> A -> A -> Type} {Q : A -> Type} {i l l'} :
  All Q l -> OnOne2All P i l l' -> OnOne2All (fun i x y => (P i x y * Q x)%type) i l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2All_All2_mix_left {A B} {P : B -> A -> A -> Type} {Q : B -> A -> Type} {i l l'} :
  All2 Q i l -> OnOne2All P i l l' -> OnOne2All (fun i x y => (P i x y * Q i x)%type) i l l'.
Proof.
  intros a; induction 1; constructor; try inv a; intuition.
Qed.

Lemma OnOne2All_app {A B} (P : B -> A -> A -> Type) {i i' l tl tl'} :
  OnOne2All P i tl tl' ->
  #|i'| = #|l| ->
  OnOne2All P (i' ++ i) (l ++ tl) (l ++ tl').
Proof. induction l in i, i' |- *; simpl; try constructor; eauto.
  destruct i' => //.
  intros. destruct i' => //. simpl. constructor.
  eapply IHl; auto.
Qed.
(*
Lemma OnOne2All_app_r {A} (P : nat -> A -> A -> Type) i l l' tl :
  OnOne2All P i l l' ->
  OnOne2All P i (l ++ tl) (l' ++ tl).
Proof. induction 1; simpl; constructor; auto. rewrite app_length. Qed.
*)
Lemma OnOne2All_length {A B} {P} {i : list B} {l l' : list A} : OnOne2All P i l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; congruence. Qed.

Lemma OnOne2All_length2 {A B} {P} {i : list B} {l l' : list A} : OnOne2All P i l l' -> #|i| = #|l|.
Proof. induction 1; simpl; congruence. Qed.

Lemma OnOne2All_mapP {A B I} {P} {i : list I} {l l' : list A} (f : A -> B) :
  OnOne2All (fun i => on_rel (P i) f) i l l' -> OnOne2All P i (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. now rewrite map_length. Qed.

Lemma OnOne2All_map {A I B} {P : I -> B -> B -> Type} {i : list I} {l l' : list A} (f : A -> B) :
  OnOne2All (fun i => on_Trel (P i) f) i l l' -> OnOne2All P i (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. now rewrite map_length. Qed.

Lemma OnOne2All_map_all {A B I I'} {P} {i : list I} {l l' : list A} (g : I -> I') (f : A -> B) :
  OnOne2All (fun i => on_Trel (P (g i)) f) i l l' -> OnOne2All P (map g i) (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. now rewrite !map_length. Qed.


Lemma OnOne2All_sym {A B} (P : B -> A -> A -> Type) i l l' : OnOne2All (fun i x y => P i y x) i l' l -> OnOne2All P i l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2All_exist {A B} (P : B -> A -> A -> Type) (Q : B -> A -> A -> Type) i l l' :
  OnOne2All P i l l' ->
  (forall i x y, P i x y -> ∑ z, Q i x z × Q i y z) ->
  ∑ r, (OnOne2All Q i l r × OnOne2All Q i l' r).
Proof.
  intros H HPQ. induction H.
  - destruct (HPQ _ _ _ p). destruct p0.
    now exists (x :: tl); intuition constructor.
               - destruct IHOnOne2All as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.

(* Induction principle on OnOne2All when the relation also depends
     on one of the lists, and should not change.
   *)
Lemma OnOne2All_ind_l :
  forall A B (R : list A -> B -> A -> A -> Type)
    (P : forall L i l l', OnOne2All (R L) i l l' -> Type),
    (forall L b bs x y l (r : R L b x y) (len : #|bs| = #|l|),
      P L (b :: bs) (x :: l) (y :: l) (OnOne2All_hd _ _ _ _ _ l r len)) ->
    (forall L b bs x l l' (h : OnOne2All (R L) bs l l'),
        P L bs l l' h ->
        P L (b :: bs) (x :: l) (x :: l') (OnOne2All_tl _ _ _ x _ _ h)
    ) ->
    forall i l l' h, P l i l l' h.
Proof.
  intros A B R P hhd htl i l l' h. induction h ; eauto.
Qed.

Lemma OnOne2All_impl_exist_and_All :
  forall A B (i : list B) (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2All R1 i l1 l2 ->
    All2 R2 l3 l2 ->
    (forall i x x' y, R1 i x y -> R2 x' y -> ∑ z : A, R3 i x z × R2 x' z) ->
    ∑ l4, OnOne2All R3 i l1 l4 × All2 R2 l3 l4.
Proof.
  intros A B i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (h _ _ _ _ p X) as hh.
    destruct hh as [? [? ?]].
    eexists. constructor.
      * constructor; eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
    eexists. constructor.
      * eapply OnOne2All_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2All_impl_exist_and_All_r :
  forall A B (i : list B) (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2All R1 i l1 l2 ->
    All2 R2 l2 l3 ->
    (forall i x x' y, R1 i x y -> R2 y x' -> ∑ z : A, R3 i x z × R2 z x') ->
    ∑ l4, ( OnOne2All R3 i l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A B i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (h _ _ _ _ p X) as hh.
      destruct hh as [? [? ?]].
      eexists. split.
      * constructor; eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
      eexists. split.
      * eapply OnOne2All_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2All_split :
  forall A B (P : B -> A -> A -> Type) i l l',
    OnOne2All P i l l' ->
    ∑ i x y u v,
      P i x y ×
      (l = u ++ x :: v /\
      l' = u ++ y :: v).
Proof.
  intros A B P i l l' h.
  induction h.
  - exists b, hd, hd', [], tl.
    intuition eauto.
  - destruct IHh as [i' [x [y [u [v ?]]]]].
    exists i', x, y, (hd :: u), v.
    intuition eauto. all: subst. all: reflexivity.
Qed.

Lemma OnOne2All_impl {A B} {P Q} {i : list B} {l l' : list A} :
  OnOne2All P i l l' ->
  (forall i x y, P i x y -> Q i x y) ->
  OnOne2All Q i l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Lemma OnOne2All_nth_error {A B} {i : list B} (l l' : list A) n t P :
  OnOne2All P i l l' ->
  nth_error l n = Some t ->
  ∑ t', (nth_error l' n = Some t') *
  ((t = t') + (∑ i', (nth_error i n = Some i') * P i' t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  - intros [= ->]. exists hd'. intuition auto. now right; exists b.
  - intros hnth. exists t; intuition auto.
  - destruct n; simpl; rewrite ?Nat.add_succ_r /=; auto.
    intros [= ->]. exists t; intuition auto.
Qed.

Lemma OnOne2All_nth_error_r {A B} (i : list B) (l l' : list A) n t' P :
  OnOne2All P i l l' ->
  nth_error l' n = Some t' ->
  ∑ t, (nth_error l n = Some t) *
  ((t = t') + (∑ i', (nth_error i n = Some i') * P i' t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  - intros [= ->]. exists hd; intuition auto.
    now right; exists b.
  - exists t'. intuition auto.
  - destruct n; simpl; auto.
    intros [= ->]. exists t'; intuition auto.
Qed.

Lemma OnOne2All_impl_All_r {A B} (P : B -> A -> A -> Type) (Q : A -> Type) i l l' :
  (forall i x y, Q x -> P i x y -> Q y) ->
  OnOne2All P i l l' -> All Q l -> All Q l'.
Proof.
  intros HPQ.
  induction 1; intros H; depelim H; constructor; auto.
  now eapply HPQ.
Qed.

Lemma OnOne2All_nth_error_impl {A B} (P : A -> B -> B -> Type) il l l' :
  OnOne2All P il l l' ->
  OnOne2All (fun i x y => (∑ ni, nth_error il ni = Some i) × P i x y) il l l'.
Proof.
  induction 1.
  - econstructor => //.
    split => //.
    exists 0; reflexivity.
  - constructor. eapply (OnOne2All_impl IHX).
    intros i x y [[ni hni] ?].
    split; auto. exists (S ni). apply hni.
Qed.

Lemma All2_Forall2 {A B} {P : A -> B -> Prop} {l l'} :
  All2 P l l' -> Forall2 P l l'.
Proof.
  induction 1; eauto.
Qed.

(* Bad! Uses template polymorphism. *)
Lemma Forall2_All2 {A B} {P : A -> B -> Prop} l l' : Forall2 P l l' -> All2 P l l'.
Proof.
  intros f; induction l in l', f |- *; destruct l'; try constructor; auto.
  elimtype False. inv f.
  elimtype False. inv f.
  inv f; auto.
  apply IHl. inv f; auto.
Qed.

Lemma All2_map_left_equiv {A B C} {P : A -> C -> Type} {l l'} {f : B -> A} :
  All2 (fun x y => P (f x) y) l l' <~> All2 P (map f l) l'.
Proof. intros. rewrite -{2}(map_id l'). eapply All2_map_equiv; eauto. Qed.

Lemma All2_map_right_equiv {A B C} {P : A -> C -> Type} {l l'} {f : B -> C} :
  All2 (fun x y => P x (f y)) l l' <~> All2 P  l (map f l').
Proof. intros. rewrite -{2}(map_id l). eapply All2_map_equiv; eauto. Qed.

Lemma All2_map_left {A B C} {P : A -> C -> Type} {l l'} {f : B -> A} :
  All2 (fun x y => P (f x) y) l l' -> All2 P (map f l) l'.
Proof. apply All2_map_left_equiv. Qed.

Lemma All2_map_right {A B C} {P : A -> C -> Type} {l l'} {f : B -> C} :
  All2 (fun x y => P x (f y)) l l' -> All2 P l (map f l').
Proof. apply All2_map_right_equiv. Qed.

Definition All2_map_left_inv {A B C} {P : A -> C -> Type} {l l'} {f : B -> A} :
  All2 P (map f l) l' -> All2 (fun x y => P (f x) y) l l' := (snd All2_map_left_equiv).
Definition All2_map_right_inv {A B C} {P : A -> C -> Type} {l l'} {f : B -> C} :
  All2 P l (map f l') -> All2 (fun x y => P x (f y)) l l' := (snd All2_map_right_equiv).

Lemma All2_undep {A B R R' l l' a}
  : @All2 A B R' l l' <~> @All2_dep A B R (fun x y _ => R' x y) l l' a.
Proof.
  split; [ induction a; inversion 1 | induction 1 ]; constructor; subst; eauto.
Qed.

Lemma Forall2_undep {A B R R' l l' a}
  : @Forall2 A B R' l l' <-> @Forall2_dep A B R (fun x y _ => R' x y) l l' a.
Proof.
  split; [ induction a using Forall2_rect; inversion 1 | induction 1 ]; constructor; subst; eauto.
Qed.

Lemma All2_All2_mix {A B} {P Q : A -> B -> Type} l l' :
  All2 P l l' ->
  All2 Q l l' ->
  All2 (fun x y => P x y × Q x y) l l'.
Proof.
  induction 1; intros H; depelim H; constructor; auto.
Qed.

Lemma All2_mix {A} {P Q : A -> A -> Type} {l l'} :
  All2 P l l' -> All2 Q l l' -> All2 (fun x y => (P x y * Q x y))%type l l'.
Proof.
  induction 1; intros HQ; inv HQ; constructor; eauto.
Qed.

Lemma All2_mix_inv {A} {P Q : A -> A -> Type} {l l'} :
  All2 (fun x y => (P x y * Q x y))%type l l' ->
  (All2 P l l' * All2 Q l l').
Proof.
  induction 1; split; constructor; intuition eauto.
Qed.


Ltac toAll :=
  match goal with
  | H : is_true (forallb _ _) |- _ => apply forallb_All in H

  | |- is_true (forallb _ _) => apply All_forallb

  | H : Forall _ ?x |- _ => apply Forall_All in H

  | |- Forall _ _ => apply All_Forall

  | H : Forall2 _ _ _ |- _ => apply Forall2_All2 in H

  | |- Forall2 _ _ _ => apply All2_Forall2

  | H : is_true (forallb2 _ _ _) |- _ => apply forallb2_All2 in H

  | |- is_true (forallb2 _ _ _) => apply All2_forallb2

  | [ H : All2_dep (fun x y _ => @?R' x y) ?a |- _ ] => apply (@All2_undep _ _ _ R' _ _ a) in H

  | [ |- All2_dep (fun x y _ => @?R' x y) ?a ] => apply (@All2_undep _ _ _ R' _ _ a)

  | [ H : Forall2_dep (fun x y _ => @?R' x y) ?a |- _ ] => apply (@Forall2_undep _ _ _ R' _ _ a) in H

  | [ |- Forall2_dep (fun x y _ => @?R' x y) ?a ] => apply (@Forall2_undep _ _ _ R' _ _ a)

  | H : All _ ?x, H' : All _ ?x |- _ =>
    apply (All_mix H) in H'; clear H

  | H : All2 _ ?x ?y, H' : All2 _ ?x ?y |- _ =>
    apply (All2_mix H) in H'; clear H

  | H : Alli _ _ ?x, H' : Alli _ _ ?x |- _ =>
    apply (Alli_mix H) in H'; clear H

  | H : All _ ?x, H' : All2 _ ?x _  |- _ =>
    apply (All2_All_mix_left H) in H'; clear H

  | H : All _ ?x, H' : All2 _ _ ?x  |- _ =>
    apply (All2_All_mix_right H) in H'; clear H

  | H : All _ ?x, H' : All2i _ _ ?x _  |- _ =>
    apply (All2i_All_mix_left H) in H'; clear H

  | H : All _ ?x, H' : All2i _ _ _ ?x  |- _ =>
    apply (All2i_All_mix_right H) in H'; clear H

  | |- All _ (map _ _) => apply All_map

  | H : All _ (map _ _) |- _ => apply All_map_inv in H

  | |- All _ (rev_map _ _) => apply All_rev_map

  | |- All _ (List.rev _) => apply All_rev

  | |- All2 _ (map _ _) (map _ _) => apply All2_map

  | |- All2 _ _ (map _ _) => apply All2_map_right

  | |- All2 _ (map _ _) _ => apply All2_map_left
  end.

Lemma All_map_eq {A B} {l} {f g : A -> B} :
  All (fun x => f x = g x) l ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Lemma All_map_id {A} {l} {f : A -> A} :
  All (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Ltac All_map :=
  match goal with
    |- map _ _ = map _ _ => apply All_map_eq
  | |- map _ _ = _ => apply All_map_id
  end.

Lemma forall_forallb_map_spec {A B : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHForall.
Qed.

Lemma forall_forallb_forallb_spec {A : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> is_true (f x)) -> is_true (forallb f l).
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and. intros [px pl] Hx. eauto.
Qed.


Lemma Forall_map {A B} (P : B -> Prop) (f : A -> B) l : Forall (fun x => P (f x)) l -> Forall P (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_map_inv {A B} (P : B -> Prop) (f : A -> B) l : Forall P (map f l) -> Forall (fun x => P (f x)) l.
Proof. induction l; intros Hf; inv Hf; try constructor; eauto. Qed.

Lemma Forall_impl_Forall {A} {P Q : A -> Prop} {l} :
  Forall P l -> Forall (fun x => P x -> Q x) l -> Forall Q l.
Proof.
  induction 1; inversion 1; constructor; auto.
Qed.

Lemma Forall_impl {A} {P Q : A -> Prop} {l} :
  Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_app {A} (P : A -> Prop) l l' : Forall P (l ++ l') -> Forall P l /\ Forall P l'.
Proof.
  induction l; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto.
Qed.

Lemma Forall_last {A} (P : A -> Prop) a l : l <> [] -> Forall P l -> P (last l a).
Proof.
  intros. induction H0.
  - congruence.
  - destruct l.
    + cbn. eauto.
    + cbn. eapply IHForall. congruence.
Qed.

Lemma All_safe_nth {A} {P : A -> Type} {Γ n} (isdecl : n < length Γ) : All P Γ ->
   P (safe_nth Γ (exist _ n isdecl)).
Proof.
  induction 1 in n, isdecl |- *.
  exfalso. inversion isdecl.
  destruct n. simpl. auto.
  simpl in *. eapply IHX.
Qed.


(* Lemma Alli_mapi {A B} (P : nat -> B -> Type) (f : nat -> A -> B) (l : list A) n : *)
(*   Alli (fun n x => P n (f n x)) n l -> Alli P n (mapi f l). *)
(* Proof. induction 1; constructor; auto. Qed. *)

Lemma All2i_impl {A B R R' n l l'} :
    @All2i A B R n l l' ->
    (forall i x y, R i x y -> R' i x y) ->
    All2i R' n l l'.
Proof.
  intros ha h.
  induction ha. 1: constructor.
  constructor. 2: assumption.
  eapply h. assumption.
Qed.

Ltac close_Forall :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : OnOne2i _ _ _ _ |- OnOne2i _ _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : OnOne2All _ _ _ _ |- OnOne2All _ _ _ _ => apply (OnOne2All_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : All2i _ _ _ _ |- All2i _ _ _ _ => apply (All2i_impl H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  | H : All2i _ _ _ _ |- All _ _ =>
    (apply (All2i_All_left H) || apply (All2i_All_right H)); clear H; simpl
  end.

Lemma All2_non_nil {A B} (P : A -> B -> Type) (l : list A) (l' : list B) :
  All2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma nth_error_forall {A} {P : A -> Prop} {l : list A} {n x} :
  nth_error l n = Some x -> Forall P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.

Lemma nth_error_all {A} {P : A -> Type} {l : list A} {n x} :
  nth_error l n = Some x -> All P l -> P x.
Proof.
  intros Hnth HPl.
  induction l in n, Hnth, HPl |- *. destruct n; discriminate.
  destruct n; cbn in Hnth.
  - inversion Hnth. subst. inversion HPl. eauto.
  - eapply IHl. eassumption. inversion HPl. eassumption.
Defined.

Lemma nth_error_alli {A} {P : nat -> A -> Type} {l : list A} {n x} {k} :
  nth_error l n = Some x -> Alli P k l -> P (k + n) x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *.
  destruct n; discriminate.
  revert Hnth. destruct n. intros [= ->]. now rewrite Nat.add_0_r.
  intros H'; eauto. rewrite <- Nat.add_succ_comm. eauto.
Qed.

Lemma All_map_id' {A} {P : A -> Type} {l} {f} :
  All P l ->
  (forall x, P x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; auto.
Qed.

Lemma Alli_mapi_spec {A B} {P : nat -> A -> Type} {l} {f g : nat -> A -> B} {n} :
  Alli P n l -> (forall n x, P n x -> f n x = g n x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq; f_equal; auto.
Qed.

Lemma Alli_mapi_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f n x = x) ->
  mapi_rec f l n = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma Alli_map_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma forallb_map {A B} (f : A -> B) (l : list A) p :
  forallb p (map f l) = forallb (fun x => p (f x)) l.
Proof.
  induction l in p, f |- *; simpl; rewrite ?andb_and;
    intuition (f_equal; auto).
Qed.

Lemma All_forallb' {A} P (l : list A) (p : A -> bool) :
  All P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma forallb_Forall' {A} (P : A -> Prop) (l : list A) p :
  is_true (forallb p l) ->
  (forall x, is_true (p x) -> P x) ->
  Forall P l.
Proof.
  induction l in p |- *; simpl. constructor.
  intros. constructor; eauto; rewrite -> andb_and in H; intuition eauto.
Qed.

Lemma forallb_skipn {A} (p : A -> bool) n l :
  is_true (forallb p l) ->
  is_true (forallb p (skipn n l)).
Proof.
  induction l in n |- *; destruct n; simpl; try congruence.
  intros. apply IHl. rewrite -> andb_and in H; intuition.
Qed.

Lemma Forall_forallb_eq_forallb {A} (P : A -> Prop) (p q : A -> bool) l :
  Forall P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Proof.
  induction 1; simpl; intuition (f_equal; auto).
Qed.

Lemma forallb2_length {A B} (p : A -> B -> bool) l l' : is_true (forallb2 p l l') -> length l = length l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  rewrite !andb_and. intros [Hp Hl]. erewrite IHl; eauto.
Qed.

Lemma map_option_Some X (L : list (option X)) t : map_option_out L = Some t -> All2 (fun x y => x = Some y) L t.
Proof.
  intros. induction L in t, H |- *; cbn in *.
  - inv H. econstructor.
  - destruct a. destruct (map_option_out L). all:inv H. eauto.
Qed.

Lemma Alli_map_option_out_mapi_Some_spec {A B} (f g : nat -> A -> option B) l t P :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some t) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some t.
Proof.
  unfold mapi. generalize 0.
  move => n Ha Hfg. move: t.
  induction Ha; try constructor; auto.
  move=> t /=. case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> [= <-]. now rewrite (IHHa _ E').
Qed.

(* TODO: move *)
Lemma All_mapi {A B} P f l k :
  Alli (fun i x => P (f i x)) k l -> All P (@mapi_rec A B f l k).
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma All_Alli {A} {P : A -> Type} {Q : nat -> A -> Type} {l n} :
  All P l ->
  (forall n x, P x -> Q n x) ->
  Alli Q n l.
Proof.
  intro H. revert n. induction H; constructor; eauto.
Qed.

Lemma All2_All_left_pack {A B} {P : A -> B -> Type} {l l'} :
  All2 P l l' -> Alli (fun i x => ∑ y, (nth_error l i = Some x /\ nth_error l' i = Some y) * P x y) 0 l.
Proof.
  intros HF. induction HF; constructor; intuition eauto.
  exists y; intuition eauto. clear -IHHF.
  revert IHHF. generalize l at 1 3. intros. apply Alli_shift.
  now simpl.
Qed.

Lemma map_option_out_All {A} P (l : list (option A)) l' :
  (All (on_Some_or_None P) l) ->
  map_option_out l = Some l' ->
  All P l'.
Proof.
  induction 1 in l' |- *; cbn; inversion 1; subst; try constructor.
  destruct x; [|discriminate].
  case_eq (map_option_out l); [|intro e; rewrite e in H1; discriminate].
  intros l0 e; rewrite e in H1; inversion H1; subst.
  constructor; auto.
Qed.

Lemma Forall_forallb {A} P (l : list A) (p : A -> bool) :
  Forall P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma Forall2_right {A B} (P : B -> Prop) (l : list A) (l' : list B) :
  Forall2 (fun x y => P y) l l' -> List.Forall (fun x => P x) l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall2_non_nil {A B} (P : A -> B -> Prop) (l : list A) (l' : list B) :
  Forall2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma Forall2_length {A B} {P : A -> B -> Prop} {l l'} : Forall2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma Forall2_app_r {A} (P : A -> A -> Prop) l l' r r' : Forall2 P (l ++ [r]) (l' ++ [r']) ->
                                                         (Forall2 P l l') /\ (P r r').
Proof.
  induction l in l', r |- *; simpl; intros; destruct l'; simpl in *; inversion H; subst.
  - intuition.
  - destruct l'; cbn in *.
    + inversion H5.
    + inversion H5.
  - destruct l; cbn in *.
    + inversion H5.
    + inversion H5.
  - specialize (IHl _ _ H5). intuition auto.
Qed.

Lemma Forall2_map_inv :
  forall {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A')
    (g : B -> B') (l : list A) (l' : list B),
    Forall2 R (map f l) (map g l') ->
    Forall2 (fun x y => R (f x) (g y)) l l'.
Proof.
  intros A B A' B' R f g l l' h.
  induction l in l', h |- * ; destruct l' ; try solve [ inversion h ].
  - constructor.
  - constructor.
    + inversion h. subst. assumption.
    + eapply IHl. inversion h. assumption.
Qed.

Lemma All2_length {A B} {P : A -> B -> Type} {l l'} : All2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma All2_nth_error_None {A B} {P : A -> B -> Type} {l l'} n :
  All2 P l l' ->
  nth_error l n = None ->
  nth_error l' n = None.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. auto.
Qed.

Lemma All2_app_inv_l : forall (A B : Type) (R : A -> B -> Type),
    forall l1 l2 r,
      All2 R (l1 ++ l2) r ->
      ∑ r1 r2,
        (r = r1 ++ r2)%list ×
        All2 R l1 r1 ×
        All2 R l2 r2.
Proof.
  intros. revert l2 r X. induction l1; intros; cbn in *.
  - exists [], r. eauto.
  - depelim X.
    apply IHl1 in X as (?&?&?&?&?).
    subst.
    eexists _, _.
    split; [|split; eauto]; auto.
Qed.

Lemma All2_app_inv_r :
  forall A B R l r1 r2,
    @All2 A B R l (r1 ++ r2) ->
    ∑ l1 l2,
      (l = l1 ++ l2)%list ×
      All2 R l1 r1 ×
      All2 R l2 r2.
Proof.
  intros A B R l r1 r2 h.
  induction r1 in l, r1, r2, h |- *.
  - exists [], l; eauto.
  - depelim h.
    apply IHr1 in h as (?&?&?&?&?).
    subst.
    eexists _, _.
    split; [|split; eauto]; auto.
Qed.

Lemma All2_app_inv :
  forall A B (P : A -> B -> Type) l1 l2 r1 r2,
    #|l1| = #|r1| ->
    All2 P (l1 ++ l2) (r1 ++ r2) ->
    All2 P l1 r1 × All2 P l2 r2.
Proof.
  intros A B P l1 l2 r1 r2 e h.
  apply All2_app_inv_l in h as (w1&w2&e1&h1&h2).
  apply app_inj_length_l in e1 as (->&->); auto.
  apply All2_length in h1.
  apply All2_length in h2.
  congruence.
Qed.

Lemma All2_rect_rev : forall (A B : Type) (R : A -> B -> Type) (P : forall (l : list A) (l0 : list B), Type),
    P [] [] ->
    (forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (a : All2 R l l'),
        P l l' -> P (l ++ [x])%list (l' ++ [y]))%list ->
    forall (l : list A) (l0 : list B) (a : All2 R l l0), P l l0.
Proof.
  intros. revert l0 a. induction l using rev_ind; cbn; intros.
  - inv a. eauto.
  - eapply All2_app_inv_l in a as (?&?&?&?&?). subst.
    inv a0. inv X2. eauto.
Qed.

Lemma All2_ind_rev : forall (A B : Type) (R : A -> B -> Type) (P : forall (l : list A) (l0 : list B), Prop),
    P [] [] ->
    (forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (a : All2 R l l'),
        P l l' -> P (l ++ [x])%list (l' ++ [y]))%list ->
    forall (l : list A) (l0 : list B) (a : All2 R l l0), P l l0.
Proof.
  intros.
  eapply All2_rect_rev; eauto.
Qed.

Lemma All2_app :
  forall (A B : Type) (R : A -> B -> Type),
  forall l1 l2 l1' l2',
    All2 R l1 l1' ->
    All2 R l2 l2' ->
    All2 R (l1 ++ l2) (l1' ++ l2').
Proof.
  induction 1 ; cbn ; eauto.
Qed.

Lemma All2_rev (A B : Type) (P : A -> B -> Type) l l' :
  All2 P l l' ->
  All2 P (List.rev l) (List.rev l').
Proof.
  induction 1. constructor.
  simpl. eapply All2_app; auto.
Qed.

Lemma All_All2_flex {A B} (P : A -> Type) (Q : A -> B -> Type) l l' :
  All P l ->
  (forall x y, In y l' -> P x -> Q x y) ->
  length l' = length l ->
  All2 Q l l'.
Proof.
  intros H1 H2 Hl.
  induction H1 in l', H2, Hl |- *; destruct l'; depelim Hl.
  - econstructor.
  - econstructor; firstorder. eapply IHAll; firstorder.
Qed.

Lemma All_All_All2 {A} (P Q : A -> Prop) l l' :
  All P l -> All Q l' -> #|l| = #|l'| -> All2 (fun x y => P x /\ Q y) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto => //.
  intros ha hb. specialize (IHl l'); depelim ha; depelim hb.
  constructor; auto.
Qed.

Lemma All2_impl_In {A B} {P Q : A -> B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, In x l -> In y l' -> P x y -> Q x y) ->
  All2 Q l l'.
Proof.
  revert l'. induction l; intros; inversion X.
  - econstructor.
  - subst. econstructor.  eapply X0. firstorder. firstorder. eauto.
    eapply IHl. eauto. intros.
    eapply X0. now right. now right. eauto.
Qed.

Lemma Forall2_skipn A B (P : A -> B -> Prop) l l' n:
  Forall2 P l l' -> Forall2 P (skipn n l) (skipn n l').
Proof.
  revert l l'; induction n; intros.
  - unfold skipn. eauto.
  - cbv [skipn]. fold (@skipn A n). fold (@skipn B n).
    inversion H; subst. econstructor.
    eauto.
Qed.

Lemma Forall2_nth_error_Some {A B} {P : A -> B -> Prop} {l l'} n t :
  Forall2 P l l' ->
  nth_error l n = Some t ->
  exists t' : B, (nth_error l' n = Some t') /\ P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. intros [= ->]. exists y. intuition auto.
  eauto.
Qed.

Lemma Forall2_impl {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma app_Forall :
  forall A P (l1 l2 : list A),
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 h1 h2.
  revert l2 h2.
  induction h1 ; intros l2 h2.
  - assumption.
  - cbn. constructor ; try assumption.
    eapply IHh1. assumption.
Qed.

Lemma rev_Forall :
  forall A P l,
    Forall P l ->
    Forall P (@List.rev A l).
Proof.
  intros A P l h.
  induction l.
  - cbn. constructor.
  - cbn. inversion h; subst.
    specialize (IHl ltac:(assumption)).
    eapply app_Forall ; try assumption.
    repeat constructor. assumption.
Qed.

Lemma Forall2_impl' {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    Forall (fun x => forall y, P x y -> Q x y) l ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor;
    inversion H1; intuition.
Qed.

Lemma Forall2_Forall {A R l} : @Forall2 A A R l l -> Forall (fun x => R x x) l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma All2_All {A R l} : @All2 A A R l l -> All (fun x => R x x) l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_Forall2 {A R l} : Forall (fun x => R x x) l -> @Forall2 A A R l l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_True {A} {P : A -> Prop} l : (forall x, P x) -> Forall P l.
Proof.
  intro H. induction l; now constructor.
Qed.

Lemma Forall2_True {A B} {R : A -> B -> Prop} l l'
  : (forall x y, R x y) -> #|l| = #|l'| -> Forall2 R l l'.
Proof.
  intro H. revert l'; induction l; simpl;
    intros [] e; try discriminate e; constructor.
  easy.
  apply IHl. now apply eq_add_S.
Qed.

Lemma Forall2_map {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A') (g : B -> B') l l'
  : Forall2 (fun x y => R (f x) (g y)) l l' -> Forall2 R (map f l) (map g l').
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall2_map_right {A B C} (P : A -> B -> Prop) (f : C -> B) (l : list A) (l' : list C) :
  Forall2 P l (map f l') <-> Forall2 (fun x y => P x (f y)) l l'.
Proof.
  split; intros.
  + eapply Forall2_map_inv. now rewrite map_id.
  + rewrite -(map_id l). now eapply Forall2_map.
Qed.

Lemma Forall2_and {A B} (R R' : A -> B -> Prop) l l'
  : Forall2 R l l' -> Forall2 R' l l' -> Forall2 (fun x y => R x y /\ R' x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l -> Forall2 (fun x y => P x /\ R x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and' {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l' -> Forall2 (fun x y => R x y /\ P y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall2_nth :
  forall A B P l l' n (d : A) (d' : B),
    Forall2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  - destruct h.
    + assumption.
    + assumption.
  - destruct h.
    + assumption.
    + simpl. apply IHn. assumption.
Qed.

Lemma Forall2_nth_error_Some_l :
  forall A B (P : A -> B -> Prop) l l' n t,
    nth_error l n = Some t ->
    Forall2 P l l' ->
    exists t',
      nth_error l' n = Some t' /\
      P t t'.
Proof.
  intros A B P l l' n t e h.
  induction n in l, l', t, e, h |- *.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. inversion e. subst.
      exists y. split ; auto.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. apply IHn with (l' := l') in e ; assumption.
Qed.

Lemma Forall2_nth_error_Some_r :
  forall A B (P : A -> B -> Prop) l l' n t,
    nth_error l' n = Some t ->
    Forall2 P l l' ->
    exists t',
      nth_error l n = Some t' /\
      P t' t.
Proof.
  intros A B P l l' n t e h.
  induction n in l, l', t, e, h |- *.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. inversion e. subst.
      exists x. split ; auto.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. apply IHn with (l := l) in e ; assumption.
Qed.

Lemma Forall2_nth_error_None_l :
  forall A B (P : A -> B -> Prop) l l' n,
    nth_error l n = None ->
    Forall2 P l l' ->
    nth_error l' n = None.
Proof.
  intros A B P l l' n e h.
  induction n in l, l', e, h |- *.
  - destruct h.
    + reflexivity.
    + cbn in e. discriminate e.
  - destruct h.
    + reflexivity.
    + cbn in e. cbn. eapply IHn ; eauto.
Qed.

Lemma Forall2_trans :
  forall A (P : A -> A -> Prop),
    RelationClasses.Transitive P ->
    RelationClasses.Transitive (Forall2 P).
Proof.
  intros A P hP l1 l2 l3 h1 h2.
  induction h1 in l3, h2 |- *.
  - inversion h2. constructor.
  - inversion h2. constructor.
    + eapply hP ; eauto.
    + eapply IHh1 ; eauto.
Qed.

Lemma Forall2_rev :
  forall A B R l l',
    @Forall2 A B R l l' ->
    Forall2 R (List.rev l) (List.rev l').
Proof.
  intros A B R l l' h.
  induction h.
  - constructor.
  - cbn. eapply Forall2_app ; eauto.
Qed.

(* Weak, would need some Forall2i *)
Lemma Forall2_mapi :
  forall A B A' B' (R : A' -> B' -> Prop) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    Forall2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    Forall2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi. generalize 0. intro i.
  induction h in i |- *.
  - constructor.
  - cbn. constructor ; eauto.
Qed.

Lemma All2_trans {A} (P : A -> A -> Type) :
  CRelationClasses.Transitive P ->
  CRelationClasses.Transitive (All2 P).
Proof.
  intros HP x y z H. induction H in z |- *.
  intros Hyz. inv Hyz. constructor.
  intros Hyz. inv Hyz. constructor; auto.
  now transitivity y.
Qed.

Lemma All2_trans' {A B C}
      (P : A -> B -> Type) (Q : B -> C -> Type) (R : A -> C -> Type)
      (H : forall x y z, P x y × Q y z -> R x z) {l1 l2 l3}
  : All2 P l1 l2 -> All2 Q l2 l3 -> All2 R l1 l3.
Proof.
  induction 1 in l3 |- *.
  - inversion 1; constructor.
  - inversion 1; subst. constructor; eauto.
Qed.

Lemma All2_nth :
  forall A B P l l' n (d : A) (d' : B),
    All2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  - destruct h.
    + assumption.
    + assumption.
  - destruct h.
    + assumption.
    + simpl. apply IHn. assumption.
Qed.

Lemma All2_mapi :
  forall A B A' B' (R : A' -> B' -> Type) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    All2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    All2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi. generalize 0. intro i.
  induction h in i |- *.
  - constructor.
  - cbn. constructor ; eauto.
Qed.

Lemma All2_skipn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (skipn n l) (skipn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.

Lemma All2_right_triv {A B} {l : list A} {l' : list B} P :
  All P l' -> #|l| = #|l'| -> All2 (fun _ b => P b) l l'.
Proof.
  induction 1 in l |- *.
  all: cbn.
  all: intros.
  all: destruct l.
  all: cbn in *.
  all: try (exfalso ; lia).
  all: try solve [ econstructor; eauto ].
Qed.

Lemma All_repeat {A} {n P} x :
  P x -> @All A P (repeat x n).
Proof.
  induction n; cbn; econstructor; eauto.
Qed.

Lemma Forall2_Forall_right {A B} {P : A -> B -> Prop} {Q : B -> Prop} {l l'} :
  Forall2 P l l' ->
  (forall x y, P x y -> Q y) ->
  Forall Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_from_nth_error A B L1 L2 (P : A -> B -> Type) :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                      -> nth_error L2 n = Some x2
                                      -> P x1 x2) ->
                All2 P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  - destruct L2; inv H. econstructor.
  - destruct L2; inversion H. econstructor.
    eapply (X 0); cbn; eauto. lia.
    eapply IHL1. eauto.
    intros. eapply (X (S n)); cbn; eauto. lia.
Qed.

Lemma All2_nth_error {A B} {P : A -> B -> Type} {l l'} n t t' :
  All2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Defined.

Lemma All2_dep_from_nth_error A B L1 L2 (P : A -> B -> Type) (P' : forall a b, P a b -> Type) (H : All2 P L1 L2) :
  (forall n x1 x2 (_ : n < #|L1|)
          (H1 : nth_error L1 n = Some x1)
          (H2 : nth_error L2 n = Some x2),
      P' x1 x2 (All2_nth_error n x1 x2 H H1 H2)) ->
  All2_dep P' H.
Proof.
  induction H; cbn; intro H'; constructor.
  { specialize (H' 0 _ _ ltac:(lia) eq_refl eq_refl); cbn in H'.
    exact H'. }
  { apply IHAll2; intros n x1 x2 Hn H1 H2.
    specialize (H' (S n) _ _ ltac:(lia) H1 H2); cbn in H'.
    exact H'. }
Qed.

Lemma All2_dep_nth_error {A B} {P : A -> B -> Type} {P' : forall a b, P a b -> Type} {l l'} n t t' {H : All2 P l l'}
  (H' : All2_dep P' H)
  (H1 : nth_error l n = Some t)
  (H2 : nth_error l' n = Some t') :
  P' t t' (All2_nth_error n t t' H H1 H2).
Proof.
  revert dependent n; induction H'; destruct n; cbn; try congruence.
  { intros H1 H2.
    set (k := f_equal _ H1); clearbody k; cbn in k; clear H1; subst.
    set (k := f_equal _ H2); clearbody k; cbn in k; clear H2; subst.
    cbn.
    assumption. }
  { exact (IHH' _). }
Qed.

Lemma Forall2_from_nth_error A B L1 L2 (P : A -> B -> Prop) :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                      -> nth_error L2 n = Some x2
                                      -> P x1 x2) ->
                Forall2 P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  - destruct L2; inv H. econstructor.
  - destruct L2; inversion H. econstructor.
    eapply (H0 0); cbn; eauto. lia.
    eapply IHL1. eauto.
    intros. eapply (H0 (S n)); cbn; eauto. lia.
Qed.

Lemma Forall2_nth_error {A B} {P : A -> B -> Prop} {l l'} n t t' :
  Forall2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Defined.

Lemma Forall2_dep_from_nth_error A B L1 L2 (P : A -> B -> Prop) (P' : forall a b, P a b -> Prop) (H : Forall2 P L1 L2) :
  (forall n x1 x2 (_ : n < #|L1|)
          (H1 : nth_error L1 n = Some x1)
          (H2 : nth_error L2 n = Some x2),
      P' x1 x2 (Forall2_nth_error n x1 x2 H H1 H2)) ->
  Forall2_dep P' H.
Proof.
  induction H using Forall2_rect; cbn; intro H'; constructor.
  { specialize (H' 0 _ _ ltac:(lia) eq_refl eq_refl); cbn in H'.
    exact H'. }
  { apply IHForall2; intros n x1 x2 Hn H1 H2.
    specialize (H' (S n) _ _ ltac:(lia) H1 H2); cbn in H'.
    exact H'. }
Qed.

Lemma Forall2_dep_nth_error {A B} {P : A -> B -> Prop} {P' : forall a b, P a b -> Prop} {l l'} n t t' {H : Forall2 P l l'}
  (H' : Forall2_dep P' H)
  (H1 : nth_error l n = Some t)
  (H2 : nth_error l' n = Some t') :
  P' t t' (Forall2_nth_error n t t' H H1 H2).
Proof.
  revert dependent n; induction H'; destruct n; cbn; try congruence.
  { intros H1 H2.
    set (k := f_equal _ H1); clearbody k; cbn in k; clear H1; subst.
    set (k := f_equal _ H2); clearbody k; cbn in k; clear H2; subst.
    cbn.
    assumption. }
  { exact (IHH' _). }
Qed.

From MetaCoq.Utils Require Import MCSquash.

Lemma All2_swap :
  forall A B R l l',
    @All2 A B R l l' ->
    All2 (fun x y => R y x) l' l.
Proof.
  intros A B R l l' h.
  induction h ; eauto.
Qed.

Lemma All2_firstn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (firstn n l) (firstn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.

Lemma All2_impl' {A B} {P Q : A -> B -> Type} {l : list A} {l' : list B}
  : All2 P l l' -> All (fun x => forall y, P x y -> Q x y) l -> All2 Q l l'.
Proof.
  induction 1. constructor.
  intro XX; inv XX.
  constructor; auto.
Defined.

Lemma All_All2 {A} {P : A -> A -> Type} {Q} {l : list A} :
  All Q l ->
  (forall x, Q x -> P x x) ->
  All2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

(* Should be All2_nth_error_Some_l *)
Lemma All2_nth_error_Some {A B} {P : A -> B -> Type} {l l'} n t :
  All2 P l l' ->
  nth_error l n = Some t ->
  { t' : B & (nth_error l' n = Some t') * P t t'}%type.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  intros [= ->]. exists y. intuition auto.
  eauto.
Qed.

Lemma All2_nth_error_Some_r {A B} {P : A -> B -> Type} {l l'} n t' :
  All2 P l l' ->
  nth_error l' n = Some t' ->
  ∑ t, nth_error l n = Some t × P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  intros [= ->]. exists x. intuition auto.
  eauto.
Qed.

Lemma All2_same {A} {P : A -> A -> Type} l : (forall x, P x x) -> All2 P l l.
Proof. induction l; constructor; auto. Qed.


Lemma All2_prod {A B} P Q (l : list A) (l' : list B) : All2 P l l' -> All2 Q l l' -> All2 (Trel_conj P Q) l l'.
Proof.
  induction 1; inversion 1; subst; auto.
Defined.

Lemma All2_prod_inv :
  forall A B (P : A -> B -> Type) Q l l',
    All2 (Trel_conj P Q) l l' ->
    All2 P l l' × All2 Q l l'.
Proof.
  intros A B P Q l l' h.
  induction h.
  - auto.
  - destruct IHh. destruct r.
    split ; constructor ; auto.
Qed.

Lemma All2_sym {A} (P : A -> A -> Type) l l' :
  All2 P l l' -> All2 (fun x y => P y x) l' l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_symP {A} (P : A -> A -> Type) :
  CRelationClasses.Symmetric P ->
  CRelationClasses.Symmetric (All2 P).
Proof.
  intros hP x y h. induction h.
  - constructor.
  - constructor ; eauto.
Qed.

Lemma All_All2_All2_mix {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' :
  All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' ->
  ∑ l''', All2 P l' l''' * All2 P l'' l'''.
Proof.
  intros H; induction H in l', l'' |- *;
  intros H' H''; inversion H'; inversion H''; subst.
  exists []; repeat constructor.
  destruct (IHAll _ _ X0 X2) as [? [? ?]]. destruct (p _ _ X X1) as [? [? ?]].
  exists (x1 :: x0). split; constructor; intuition auto.
Qed.

Lemma All2_nth_error_Some_right {A} {P : A -> A -> Type} {l l'} n t :
  All2 P l l' ->
  nth_error l' n = Some t ->
  { t' : A & (nth_error l n = Some t') * P t' t}%type.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. intros [= ->]. exists x. intuition auto.
  eauto.
Qed.

Lemma All_forallb_map_spec {A B : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHX.
Qed.

Lemma All_forallb_forallb_spec {A : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x) -> forallb f l.
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and. intros [px pl] Hx. eauto.
Qed.

Lemma All_forallb_eq_forallb {A} (P : A -> Type) (p q : A -> bool) l :
  All P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Proof.
  induction 1; simpl; intuition (f_equal; auto).
Qed.

Lemma forallb_nth {A} (l : list A) (n : nat) P d :
  forallb P l -> n < #|l| -> exists x, (nth n l d = x) /\ P x.
Proof.
  induction l in n |- *; destruct n; simpl; auto; try easy.
  move/andb_and => [pa pl] pn. exists a; easy.
  move/andb_and => [pa pl] pn. specialize (IHl n pl).
  apply IHl; lia.
Qed.

Lemma forallb_nth' {A} {l : list A} {P} n d :
  forallb P l -> {exists x, (nth n l d = x) /\ P x} + {nth n l d = d}.
Proof.
  intro H. destruct (le_lt_dec #|l| n) as [HH|HH].
  - rewrite nth_overflow; try assumption; now right.
  - left. eapply forallb_nth; assumption.
Qed.

Lemma forallb_impl {A} (p q : A -> bool) l :
  (forall x, In x l -> p x -> q x) -> forallb p l -> forallb q l.
Proof.
  intros H0 H1. eapply forallb_forall. intros x H2.
  eapply forallb_forall in H1; try eassumption.
  now eapply H0.
Qed.

Lemma forallb_iff {A} (p q : A -> bool) l :
  (forall x, In x l -> p x <-> q x) -> forallb p l = forallb q l.
Proof.
  intros H0. eapply Forall_forallb_eq_forallb with (P:=fun x => In x l).
  - now apply Forall_forall.
  - intros; eapply eq_true_iff_eq; eauto.
Qed.

Lemma All2_eq :
  forall A (l l' : list A),
    All2 eq l l' ->
    l = l'.
Proof.
  intros A l l' h.
  induction h ; eauto. subst. reflexivity.
Qed.


Lemma All_prod_inv :
  forall A P Q l,
    All (fun x : A => P x × Q x) l ->
    All P l × All Q l.
Proof.
  intros A P Q l h.
  induction h.
  - split ; auto.
  - destruct IHh, p.
    split ; constructor ; auto.
Qed.

Lemma All_pair {A} (P Q : A -> Type) l :
  All (fun x => P x × Q x) l <~> (All P l × All Q l).
Proof.
  split. induction 1; intuition auto.
  move=> [] Hl Hl'. induction Hl; depelim Hl'; intuition auto.
Qed.

Lemma All_prod :
  forall A P Q l,
    All P l ->
    All Q l ->
    All (fun x : A => P x × Q x) l.
Proof.
  intros A P Q l h1 h2.
  induction h1 in h2 |- *.
  - constructor.
  - inversion h2.
    specialize (IHh1 X0). auto.
Qed.

Lemma All2i_mapi :
  forall A B C D R f g l l',
    @All2i A B (fun i x y => R i (f i x) (g i y)) 0 l l' ->
    @All2i C D R 0 (mapi f l) (mapi g l').
Proof.
  intros A B C D R f g l l' h.
  unfold mapi.
  revert h.
  generalize 0. intros n h.
  induction h. 1: constructor.
  simpl. constructor. all: assumption.
Qed.

Lemma All2i_app :
  forall A B R n l1 l2 r1 r2,
    @All2i A B R n l1 r1 ->
    All2i R (n + #|l1|) l2 r2 ->
    All2i R n (l1 ++ l2) (r1 ++ r2).
Proof.
  intros A B R n l1 l2 r1 r2 h1 h2.
  induction h1 in r2, l2, h2 |- *.
  - simpl in *. replace (n + 0)%nat with n in h2 by lia. assumption.
  - simpl in *. constructor. 1: assumption.
    eapply IHh1. replace (S (n + #|l|))%nat with (n + S #|l|)%nat by lia.
    assumption.
Qed.

(* Lemma All2i_fnat :
  forall A B R n l r f,
    (forall n, f (S n) = S (f n)) ->
    @All2i A B R (f n) l r ->
    All2i (fun i x y => R (f i) x y) n l r.
Proof.
  intros A B R n l r f hf h.
  remember (f n) as m eqn:e.
  induction h in n, e |- *. 1: constructor.
  constructor.
  - rewrite <- e. assumption.
  - eapply IHh. rewrite hf. auto.

  (* dependent induction h. 1: constructor.
  constructor. 1: assumption.
  eapply IHh. *)
Qed. *)

Lemma All2i_mapi_rec {A B C D} (R : nat -> A -> B -> Type)
      (l : list C) (l' : list D) (f : nat -> C -> A) (g : nat -> D -> B) n :
  All2i (fun n x y => R n (f n x) (g n y)) n l l' ->
  All2i R n (mapi_rec f l n) (mapi_rec g l' n).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2i_trivial {A B} (R : nat -> A -> B -> Type) (H : forall n x y, R n x y) n l l' :
  #|l| = #|l'| -> All2i R n l l'.
Proof.
  induction l in n, l' |- *; destruct l'; simpl; try discriminate; intros; constructor; auto.
Qed.

Lemma All2i_rev :
  forall A B R l l' n,
    @All2i A B R n l l' ->
    All2i (fun i x y => R (n + #|l| - (S i)) x y) 0 (List.rev l) (List.rev l').
Proof.
  intros A B R l l' n h.
  induction h. 1: constructor.
  simpl. apply All2i_app.
  - eapply All2i_impl. 1: eassumption.
    simpl. intros ? ? ? ?.
    replace (n + S #|l| - S i) with (n + #|l| - i) by lia.
    assumption.
  - simpl. constructor. 2: constructor.
    rewrite List.rev_length.
    replace (n + S #|l| - S #|l|) with n by lia.
    assumption.
Qed.

Section All2i_len.

  (** A special notion of All2i indexed by the length of the rest of the lists *)

  Hint Constructors All2i : pcuic.

  Inductive All2i_len {A B : Type} (R : nat -> A -> B -> Type) : list A -> list B -> Type :=
    All2i_len_nil : All2i_len R [] []
  | All2i_len_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
          R (List.length l) x y -> All2i_len R l l' -> All2i_len R (x :: l) (y :: l').
  Hint Constructors All2i_len : core pcuic.

  Lemma All2i_len_app {A B} (P : nat -> A -> B -> Type) l0 l0' l1 l1' :
    All2i_len P l0' l1' ->
    All2i_len (fun n => P (n + #|l0'|)) l0 l1 ->
    All2i_len P (l0 ++ l0') (l1 ++ l1').
  Proof.
    intros H. induction 1; simpl. apply H.
    constructor. now rewrite app_length. apply IHX.
  Qed.

  Lemma All2i_len_length {A B} (P : nat -> A -> B -> Type) l l' :
    All2i_len P l l' -> #|l| = #|l'|.
  Proof. induction 1; simpl; lia. Qed.

  Lemma All2i_len_impl {A B} (P Q : nat -> A -> B -> Type) l l' :
    All2i_len P l l' -> (forall n x y, P n x y -> Q n x y) -> All2i_len Q l l'.
  Proof. induction 1; simpl; auto. Qed.

  Lemma All2i_len_rev {A B} (P : nat -> A -> B -> Type) l l' :
    All2i_len P l l' ->
    All2i_len (fun n => P (#|l| - S n)) (List.rev l) (List.rev l').
  Proof.
    induction 1. constructor. simpl List.rev.
    apply All2i_len_app. repeat constructor. simpl. rewrite Nat.sub_0_r. auto.
    simpl. eapply All2i_len_impl; eauto. intros. simpl in X0. now rewrite Nat.add_1_r.
  Qed.

  Lemma All2i_rev_ctx {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
    All2i_len R l l' -> All2i R 0 (List.rev l) (List.rev l').
  Proof.
    induction 1. simpl. constructor.
    simpl. apply All2i_app => //. simpl. rewrite List.rev_length. constructor; auto.
  Qed.

  Lemma All2i_rev_ctx_gen {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
    All2i R n l l' -> All2i_len (fun m => R (n + m)) (List.rev l) (List.rev l').
  Proof.
    induction 1. simpl. constructor.
    simpl. eapply All2i_len_app. constructor. now rewrite Nat.add_0_r. constructor.
    eapply All2i_len_impl; eauto. intros.
    simpl in *. rewrite [S _]Nat.add_succ_comm in X0. now rewrite Nat.add_1_r.
  Qed.

  Lemma All2i_rev_ctx_inv {A B} (R : nat -> A -> B -> Type) (l : list A) (l' : list B) :
    All2i R 0 l l' -> All2i_len R (List.rev l) (List.rev l').
  Proof.
    intros. eapply All2i_rev_ctx_gen in X. simpl in X. apply X.
  Qed.

End All2i_len.

Lemma All_sq {A} {P : A -> Type} {l}
  : All (fun x => ∥ P x ∥) l -> ∥ All P l ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.

Lemma All2_sq {A B} {R : A -> B -> Type} {l1 l2}
  : All2 (fun x y => ∥ R x y ∥) l1 l2 -> ∥ All2 R l1 l2 ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.

Lemma All_All2_refl {A : Type} {R} {l : list A} :
  All (fun x : A => R x x) l -> All2 R l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_app_r {A} (P : A -> A -> Type) l l' r r' :
  All2 P (l ++ [r]) (l' ++ [r']) -> (All2 P l l') * (P r r').
Proof.
  induction l in l' |- *; cbn in *; intro X.
  - destruct l'.
    + inversion X; intuition auto.
    + cbn in X. inversion X; subst. inversion X1.
      destruct l'; inversion H.
  - destruct l'; inversion X; subst.
    + destruct l; inversion X1.
    + apply IHl in X1. repeat constructor; intuition auto.
Qed.

Lemma Forall2_eq {A} l l'
  : @Forall2 A A eq l l' -> l = l'.
Proof.
  induction 1; congruence.
Qed.

Lemma Forall2_map' {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A') (g : B -> B') l l'
  : Forall2 R (map f l) (map g l') -> Forall2 (fun x y => R (f x) (g y)) l l'.
Proof.
  induction l in l' |- *.
  - destruct l'; inversion 1. constructor.
  - destruct l'; inversion 1. constructor; auto.
Qed.

Lemma Forall2_same :
  forall A (P : A -> A -> Prop) l,
    (forall x, P x x) ->
    Forall2 P l l.
Proof.
  intros A P l h.
  induction l.
  - constructor.
  - constructor.
    + eapply h.
    + assumption.
Qed.

Lemma Forall2_sym :
  forall A (P : A -> A -> Prop) l l',
    Forall2 P l l' ->
    Forall2 (fun x y => P y x) l' l.
Proof.
  intros A P l l' h.
  induction h.
  - constructor.
  - constructor. all: auto.
Qed.

Lemma forallb2_Forall2 :
  forall A B (p : A -> B -> bool) l l',
    forallb2 p l l' ->
    Forall2 (fun x y => p x y) l l'.
Proof.
  intros A B p l l' h.
  induction l in l', h |- *.
  - destruct l'. 2: discriminate.
    constructor.
  - destruct l'. 1: discriminate.
    simpl in h. move/andb_and: h => [? ?].
    constructor. all: auto.
Qed.

Lemma forallb2P {A B} (P : A -> B -> Prop) (p : A -> B -> bool) l l' :
  (forall x y, reflect (P x y) (p x y)) ->
  reflect (Forall2 P l l') (forallb2 p l l').
Proof.
  intros Hp.
  apply iff_reflect; change (forallb2 p l l' = true) with (forallb2 p l l' : Prop); split.
  - induction 1; rewrite /= // IHForall2 // andb_true_r.
    now destruct (Hp x y).
  - induction l in l' |- *; destruct l'; rewrite /= //. rewrite andb_and.
    intros [pa pl].
    constructor; auto. now destruct (Hp a b).
Qed.

(** All, All2 and In interactions. *)

Lemma All2_In {A B} (P : A -> B -> Type) l l' x : In x l ->
  All2 P l l' -> ∥ ∑ x', P x x' ∥.
Proof.
  induction 2; simpl in H => //.
  destruct H as [-> | H].
  constructor. now exists y.
  now eapply IHX.
Qed.

Lemma All2_In_right {A B} (P : A -> B -> Type) l l' x' : In x' l' ->
  All2 P l l' -> ∥ ∑ x, P x x' ∥.
Proof.
  induction 2; simpl in H => //.
  destruct H as [-> | H].
  constructor. now exists x.
  now eapply IHX.
Qed.

Lemma All_In {A} (P : A -> Type) l x : In x l ->
  All P l -> ∥ P x ∥.
Proof.
  induction 2; simpl in H => //.
  destruct H as [-> | H].
  now constructor.
  now eapply IHX.
Qed.

Lemma In_Forall {A} {P : A -> Prop} l :
  (forall x, In x l -> P x) ->
  Forall P l.
Proof.
  intros H; induction l; constructor; auto.
  now apply H; simpl. apply IHl.
  intros x xin; apply H; simpl; auto.
Qed.

Lemma All_forall {X Y} (f:X->Y->Prop) xs:
  All (fun a => forall b, f a b) xs ->
  (forall b, All (fun a => f a b) xs).
Proof.
  intros.
  induction X0.
  - constructor.
  - constructor.
    + apply p.
    + apply IHX0.
Qed.

Lemma All2i_map {A B C D} (R : nat -> C -> D -> Type) (f : A -> C) (g : B -> D) n l l' :
  All2i (fun i x y => R i (f x) (g y)) n l l' -> All2i R n (map f l) (map g l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. Qed.

Lemma All2i_map_right {B C D} (R : nat -> C -> D -> Type) (g : B -> D) n l l' :
  All2i (fun i x y => R i x (g y)) n l l' -> All2i R n l (map g l').
Proof. induction 1; simpl; constructor; try congruence; try assumption. Qed.

Lemma All2i_nth_impl_gen {A B} (R : nat -> A -> B -> Type) n l l' :
  All2i R n l l' ->
  All2i (fun i x y =>
    (if i <? n then False
    else nth_error l (i - n) = Some x) × R i x y) n l l'.
Proof.
  intros a. depind a.
  - constructor.
  - constructor.
    * simpl. destruct (Nat.ltb n n) eqn:ltb.
      + eapply Nat.ltb_lt in ltb. lia.
      + rewrite Nat.sub_diag. auto.
    * simpl. eapply (All2i_impl IHa).
      intros. destruct (Nat.ltb i (S n)) eqn:ltb; simpl in *; destruct X =>  //.
      apply Nat.ltb_nlt in ltb.
      destruct (Nat.ltb i n) eqn:ltb'; simpl in *.
      + eapply Nat.ltb_lt in ltb'. lia.
      + eapply Nat.ltb_nlt in ltb'.
        assert (i - n = S (i - S n)) as -> by lia. simpl. now rewrite e.
Qed.

Lemma All2i_nth_hyp {A B} (R : nat -> A -> B -> Type) l l' :
  All2i R 0 l l' ->
  All2i (fun i x y => nth_error l i = Some x × R i x y) 0 l l'.
Proof.
  intros a.
  eapply All2i_nth_impl_gen in a. simpl in a.
  eapply (All2i_impl a). intros.
  now rewrite Nat.sub_0_r in X.
Qed.

Lemma All2i_nth_error_l {A B} (P : nat -> A -> B -> Type) l l' n x k :
  All2i P k l l' ->
  nth_error l n = Some x ->
  ∑ c, nth_error l' n = Some c × P (k + n)%nat x c.
Proof.
  induction 1 in n |- *.
  * rewrite nth_error_nil => //.
  * destruct n.
    + simpl. intros [= <-].
      eexists; split; eauto. now rewrite Nat.add_0_r.
    + simpl. intros hnth. specialize (IHX _ hnth).
      now rewrite Nat.add_succ_r.
Qed.

Lemma All2i_nth_error_r {A B} (P : nat ->A -> B -> Type) l l' n x k :
  All2i P k l l' ->
  nth_error l' n = Some x ->
  ∑ c, nth_error l n = Some c × P (k + n)%nat c x.
Proof.
  induction 1 in n |- *.
  * rewrite nth_error_nil => //.
  * destruct n.
    + simpl. intros [= <-].
      eexists; split; eauto. now rewrite Nat.add_0_r.
    + simpl. intros hnth. specialize (IHX _ hnth).
      now rewrite Nat.add_succ_r.
Qed.

Lemma All2i_app_inv_l {X Y} (R : nat -> X -> Y -> Type) n xs xs' l :
  All2i R n (xs ++ xs') l ->
  ∑ ys ys',
  l = ys ++ ys' × All2i R n xs ys × All2i R (n + #|xs|) xs' ys'.
Proof.
  intros a.
  induction xs in n, xs, xs', l, a |- *.
  - cbn; rewrite Nat.add_0_r.
    eexists _, _.
    split; [|split; eauto; constructor].
    auto.
  - depelim a.
    apply IHxs in a as (?&?&->&?&?).
    cbn.
    rewrite Nat.add_succ_r.
    eexists _, _.
    split; [|split; eauto; constructor; eauto].
    auto.
Qed.

Lemma All2i_app_inv_r {X Y} (R : nat -> X -> Y -> Type) n l ys ys' :
  All2i R n l (ys ++ ys') ->
  ∑ xs xs',
  l = xs ++ xs' × All2i R n xs ys × All2i R (n + #|xs|) xs' ys'.
Proof.
  intros a.
  induction ys in n, l, ys', a |- *.
  - exists [], l.
    split; auto.
    cbn; rewrite Nat.add_0_r.
    split; eauto.
  - depelim a.
    apply IHys in a as (?&?&->&?&?).
    eexists (_ :: _), _.
    split; [reflexivity|].
    cbn; rewrite Nat.add_succ_r.
    split; eauto.
Qed.

Lemma All2i_length {X Y} (R : nat -> X -> Y -> Type) n xs ys :
  All2i R n xs ys ->
  #|xs| = #|ys|.
Proof.
  intros a.
  induction a; auto.
  cbn; lia.
Qed.

Lemma All2i_app_inv {X Y} (R : nat -> X -> Y -> Type) n xs xs' ys ys' :
  All2i R n (xs ++ xs') (ys ++ ys') ->
  #|xs| = #|ys| ->
                All2i R n xs ys × All2i R (n + #|xs|) xs' ys'.
Proof.
  intros a eq.
  apply All2i_app_inv_l in a as (?&?&leq&?&?).
  apply app_inj_length_l in leq as (?&?); subst; auto.
  apply All2i_length in a.
  apply All2i_length in a0.
  congruence.
Qed.

Lemma All2i_All2_All2i_All2i {A B C n} {P : nat -> A -> B -> Type} {Q : B -> C -> Type} {R : nat -> A -> C -> Type}
  {S : nat -> A -> C -> Type} {l l' l''} :
  All2i P n l l' ->
  All2 Q l' l'' ->
  All2i R n l l'' ->
  (forall n x y z, P n x y -> Q y z -> R n x z -> S n x z) ->
  All2i S n l l''.
Proof.
  intros a b c H.
  induction a in l'', b, c |- *; depelim b; depelim c; try constructor; auto.
  eapply H; eauto.
Qed.

Lemma All2i_All2_All2 {A B C} {P : nat -> A -> B -> Type} {Q R : B -> C -> Type} {n l l' l''} :
  All2i P n l l' ->
  All2 Q l' l'' ->
  (forall n x y z, P n x y -> Q y z -> R y z) ->
  All2 R l' l''.
Proof.
  induction 1 in l'' |- *; intros H; depelim H; constructor; eauto.
Qed.

Lemma All2_fold_from_nth_error A L1 L2 P :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                           -> nth_error L2 n = Some x2
                                           -> P (skipn (S n) L1) (skipn (S n) L2) x1 x2) ->
                @All2_fold A P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  - destruct L2; inv H. econstructor.
  - destruct L2; inversion H. econstructor.
    { apply IHL1; eauto.
      intros n x1 x2 ?; apply (X (S n)). lia. }
    { eapply (X 0); cbn; eauto. lia. }
Qed.

Lemma All2_fold_app {A} {P} {Γ Γ' Γl Γr : list A} :
  All2_fold P Γ Γl ->
  All2_fold (All_over P Γ Γl) Γ' Γr ->
  All2_fold P (Γ' ++ Γ) (Γr ++ Γl).
Proof.
  induction 2; auto; simpl; constructor; auto.
Qed.

Lemma All2_fold_length {A P} {Γ Γ' : list A} :
  All2_fold P Γ Γ' -> #|Γ| = #|Γ'|.
Proof.
  induction 1; cbn; congruence.
Qed.

Lemma All2_fold_impl {A P Q} {Γ Γ' : list A} :
  All2_fold P Γ Γ' -> (forall Γ Γ' d d', P Γ Γ' d d' -> Q Γ Γ' d d') ->
  All2_fold Q Γ Γ'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All_fold_app_inv {A} {P} (Γ Δ : list A) :
  All_fold P (Γ ++ Δ) ->
  All_fold P Δ × All_fold (fun Γ => P (Γ ++ Δ)) Γ.
Proof.
  induction Γ in Δ |- *; split; auto.
  depelim X. specialize (IHΓ Δ). intuition auto.
  depelim X. constructor; auto. specialize (IHΓ Δ); intuition auto.
Qed.

Lemma All2_fold_All_fold_mix_left {A} P Q (Γ Γ' : list A) :
  All_fold P Γ ->
  All2_fold Q Γ Γ' ->
  All2_fold (fun Γ Γ' d d' => P Γ d × Q Γ Γ' d d') Γ Γ'.
Proof.
  induction 1 in Γ' |- *; intros H; depelim H; constructor; auto.
Qed.

Lemma All2_fold_All_fold_mix_right {A} P Q (Γ Γ' : list A) :
  All_fold P Γ' ->
  All2_fold Q Γ Γ' ->
  All2_fold (fun Γ Γ' d d' => P Γ' d' × Q Γ Γ' d d') Γ Γ'.
Proof.
  induction 1 in Γ |- *; intros H; depelim H; constructor; auto.
Qed.

Lemma All2_fold_All_fold_mix_left_inv {A} P Q (Γ Γ' : list A) :
  All2_fold (fun Γ Γ' d d' => P Γ d × Q Γ Γ' d d') Γ Γ' ->
  All_fold P Γ × All2_fold Q Γ Γ'.
Proof.
  induction 1; split; constructor; intuition auto.
Qed.

Lemma All2_fold_All_right {A P} {Γ Γ' : list A} :
  All2_fold (fun _ Γ _ d => P Γ d) Γ Γ' ->
  All_fold P Γ'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_fold_All_left {A P} {Γ Γ' : list A} :
  All2_fold (fun Γ _ d _ => P Γ d) Γ Γ' ->
  All_fold P Γ.
Proof.
  induction 1; constructor; auto.
Qed.

Section All_fold.
  Context {A} {P : list A -> A -> Type}.

  Lemma All_fold_impl Q Γ :
    All_fold P Γ ->
    (forall Γ x, P Γ x -> Q Γ x) ->
    All_fold Q Γ.
  Proof using Type.
    induction 1; simpl; intros => //; constructor; eauto.
  Qed.

  Lemma All_fold_app Γ Δ :
    All_fold (fun Γ => P (Γ ++ Δ)) Γ ->
    All_fold P Δ ->
    All_fold P (Γ ++ Δ).
  Proof using Type.
    induction 1; simpl; intros => //.
    constructor; auto.
  Qed.
End All_fold.

Section Alli_All_fold.
  Context {A : Type}.
  Lemma Alli_All_fold {P : nat -> A -> Type} {n Γ} :
    Alli P n Γ <~>
    All_fold (fun Γ d => P (n + #|Γ|) d) (List.rev Γ).
  Proof using Type.
    split.
    - induction 1; simpl.
      + constructor.
      + eapply All_fold_app; simpl.
        2:constructor; simpl; auto.
        2:now rewrite Nat.add_0_r.
        eapply All_fold_impl; tea.
        simpl; intros.
        cbn. rewrite app_length /= Nat.add_1_r Nat.add_succ_r //.
    - induction Γ using rev_ind; simpl.
      + constructor.
      + rewrite List.rev_app_distr /=.
        intros a; depelim a. eapply Alli_app_inv => //; eauto.
        now constructor; [len in p|constructor].
  Qed.

  Lemma Alli_rev_All_fold (P : nat -> A -> Type) n Γ :
    Alli P n (List.rev Γ) ->
    All_fold (fun Γ d => P (n + #|Γ|) d) Γ.
  Proof using Type.
    move/Alli_All_fold.
    now rewrite List.rev_involutive.
  Qed.

  Lemma All_fold_Alli_rev (P : nat -> A -> Type) n Γ :
    All_fold (fun Γ d => P (n + #|Γ|) d) Γ ->
    Alli P n (List.rev Γ).
  Proof using Type.
    rewrite -{1}(List.rev_involutive Γ).
    now move/Alli_All_fold.
  Qed.
End Alli_All_fold.

Section All2_fold.
  Context {A} {P : list A -> list A -> A -> A -> Type}.

  Lemma All2_fold_All2 (Q : A -> A -> Type) {Γ Δ : list A} :
    All2_fold (fun _ _ => Q) Γ Δ <~>
    All2 Q Γ Δ.
  Proof using Type.
    split; induction 1; simpl; constructor; auto.
  Qed.

  Lemma All2_fold_refl: (forall Δ x, P Δ Δ x x) ->
    forall Δ : list A, All2_fold P Δ Δ.
  Proof using Type.
    intros HP.
    induction Δ; constructor; auto.
  Qed.

  Lemma All2_fold_trans  :
    (forall Γ Γ' Γ'' x y z,
        All2_fold P Γ Γ' ->
        All2_fold P Γ' Γ'' ->
        All2_fold P Γ Γ'' ->
        P Γ Γ' x y -> P Γ' Γ'' y z -> P Γ Γ'' x z) ->
    CRelationClasses.Transitive (All2_fold P).
  Proof using Type.
    intros HP x y z H. induction H in z |- *; auto;
    intros H'; depelim H';
      try constructor; eauto; hnf in H0; noconf H0; eauto.
  Qed.

  Lemma All2_fold_sym :
    (forall Γ Γ' x y,
        All2_fold P Γ Γ' ->
        All2_fold P Γ' Γ ->
        P Γ Γ' x y -> P Γ' Γ y x) ->
    CRelationClasses.Symmetric (All2_fold P).
  Proof using Type.
    intros HP x y H.
    induction H; constructor; auto.
  Qed.

  Lemma All2_fold_app_inv Γ Γ' Δ Δ' :
    #|Δ| = #|Δ'| ->
    All2_fold P (Δ ++ Γ) (Δ' ++ Γ') ->
    All2_fold P Γ Γ' * All2_fold (fun Δ Δ' => P (Δ ++ Γ) (Δ' ++ Γ')) Δ Δ'.
  Proof using Type.
    intros H.
    induction Δ in H, Δ', Γ, Γ' |- *;
    destruct Δ'; try discriminate.
    intuition auto.
    intros H'. simpl in H.
    specialize (IHΔ Γ Γ' Δ' ltac:(lia)).
    depelim H'; specialize (IHΔ H'); intuition auto;
    constructor; auto.
  Qed.

  Lemma All2_fold_app_inv_l Γ Γ' Δ Δ' :
    #|Γ| = #|Γ'| ->
    All2_fold P (Δ ++ Γ) (Δ' ++ Γ') ->
    All2_fold P Γ Γ' * All2_fold (fun Δ Δ' => P (Δ ++ Γ) (Δ' ++ Γ')) Δ Δ'.
  Proof using Type.
    intros H.
    induction Δ in H, Δ', Γ, Γ' |- *;
    destruct Δ'; try discriminate.
    intuition auto.
    intros H'; generalize (All2_fold_length H'). simpl. len. lia.
    intros H'; generalize (All2_fold_length H'). simpl. len. lia.
    intros H'. simpl in H.
    specialize (IHΔ Γ Γ' Δ' ltac:(lia)).
    depelim H'; specialize (IHΔ H'); intuition auto;
    constructor; auto.
  Qed.

  Lemma All2_fold_impl_ind {P' Γ Δ} :
    All2_fold P Γ Δ ->
    (forall Γ Δ d d',
      All2_fold P Γ Δ ->
      All2_fold P' Γ Δ ->
      P Γ Δ d d' ->
      P' Γ Δ d d') ->
    All2_fold P' Γ Δ.
  Proof using Type.
    intros cr Hcr.
    induction cr; constructor; intuition eauto.
  Qed.

  Lemma All2_fold_impl_len {Q} {Γ Δ : list A} :
    All2_fold P Γ Δ ->
    (forall Γ Δ T U, #|Γ| = #|Δ| -> P Γ Δ T U -> Q Γ Δ T U) ->
    All2_fold Q Γ Δ.
  Proof using Type.
    intros H HP. pose proof (All2_fold_length H).
    induction H; constructor; simpl; eauto.
  Qed.

  Lemma All2_fold_forallb2 (Pb : A -> A -> bool) Γ Δ :
    All2_fold (fun _ _ => Pb) Γ Δ ->
    forallb2 Pb Γ Δ.
  Proof using Type.
    induction 1; simpl; auto; now rewrite p IHX.
  Qed.

  Lemma All2_fold_nth {n Γ Γ' d} :
    All2_fold P Γ Γ' -> nth_error Γ n = Some d ->
    { d' & ((nth_error Γ' n = Some d') *
            let Γs := skipn (S n) Γ in
            let Γs' := skipn (S n) Γ' in
            All2_fold P Γs Γs' *
            P Γs Γs' d d')%type }.
  Proof using Type.
    induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
    - depelim Hrel.
      simpl. eexists; intuition eauto.
    - depelim Hrel.
      destruct (IHn _ _ _ Hrel H).
      cbn -[skipn] in *.
      eexists; intuition eauto.
  Qed.

  Lemma All2_fold_nth_r {n Γ Γ' d'} :
    All2_fold P Γ Γ' -> nth_error Γ' n = Some d' ->
    { d & ((nth_error Γ n = Some d) *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          All2_fold P Γs Γs' *
          P Γs Γs' d d')%type }.
  Proof using Type.
    induction n in Γ, Γ', d' |- *; destruct Γ'; intros Hrel H; noconf H.
    - depelim Hrel.
      simpl. eexists; intuition eauto.
    - depelim Hrel.
      destruct (IHn _ _ _ Hrel H).
      cbn -[skipn] in *.
      eexists; intuition eauto.
  Qed.

  Lemma All2_fold_prod {Q} {Γ Δ} :
    All2_fold P Γ Δ ->
    All2_fold Q Γ Δ ->
    All2_fold (fun Γ Δ x y => P Γ Δ x y × Q Γ Δ x y) Γ Δ.
  Proof using Type.
    induction 1; intros h; depelim h; constructor; auto.
  Qed.

  Lemma All2_fold_prod_inv {Q} {Γ Δ} :
    All2_fold (fun Γ Δ x y => P Γ Δ x y × Q Γ Δ x y) Γ Δ ->
    All2_fold P Γ Δ × All2_fold Q Γ Δ.
  Proof using Type.
    induction 1; split; constructor; intuition auto.
  Qed.

End All2_fold.

Lemma All_fold_prod {A} (P : list A -> A -> Type) Q Γ Δ :
  #|Γ| = #|Δ| ->
  All_fold P Γ ->
  All_fold P Δ ->
  (forall Δ Δ' x y,
    All_fold P Δ ->
    All_fold P Δ' ->
    All2_fold Q Δ Δ' -> P Δ x -> P Δ' y -> Q Δ Δ' x y) ->
  All2_fold Q Γ Δ.
Proof.
  intros hlen ha hb H.
  induction ha in Δ, hb, hlen |- *; depelim hb => //; constructor.
  - noconf hlen. now eapply IHha.
  - eauto.
Qed.

Lemma All2_fold_All_fold_mix {A P Q} {l l' : list A} :
  All2_fold P l l' ->
  All_fold Q l ->
  All_fold Q l' ->
  All2_fold (fun Γ Γ' x y => Q Γ x × Q Γ' y × P Γ Γ' x y) l l'.
Proof.
  induction 1; [constructor|] => l r; depelim l; depelim r; constructor; auto.
Qed.

Lemma All2_fold_All_fold_mix_inv {A} {P Q} {l l' : list A} :
  All2_fold (fun Γ Γ' x y => Q Γ x × Q Γ' y × P Γ Γ' x y) l l' ->
  All2_fold P l l' × All_fold Q l × All_fold Q l'.
Proof.
  induction 1; intuition (try constructor; auto).
Qed.

Lemma All_fold_All2_fold_impl {A} {P Q} {Γ : list A} :
  All_fold P Γ ->
  (forall Γ d, All_fold P Γ -> All2_fold Q Γ Γ -> P Γ d -> Q Γ Γ d d) ->
  All2_fold Q Γ Γ.
Proof.
  intros a H; induction a; constructor; auto.
Qed.

Lemma All_fold_All2_fold {A P} {Γ : list A} :
  All_fold (fun Γ d => P Γ Γ d d) Γ <~>
  All2_fold P Γ Γ.
Proof.
  split.
  - induction 1; simpl; constructor; intuition auto;
    now rewrite <-(All2_fold_length X).
  - intros H; depind H; constructor; auto.
Qed.

Lemma All_remove_last {A} (P : A -> Type) l : All P l -> All P (remove_last l).
Proof.
  intros. now eapply All_firstn.
Qed.

Lemma All3_map_all {A B C} {A' B' C'} P (l : list A') (l' : list B') (l'' : list C')
  (f : A' -> A) (g : B' -> B) (h : C' -> C) :
  All3 (fun x y z => P (f x) (g y) (h z)) l l' l'' ->
  All3 P (map f l) (map g l') (map h l'').
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma OnOne2All_All3 {A B} P Q (l : list A) (l' : list B) (l'' : list B) :
  (forall x y z, P x y z -> Q x y z) ->
  (forall x y, Q x y y) ->
  OnOne2All P l l' l'' ->
  All3 Q l l' l''.
Proof.
  intros H1 H2.
  induction 1; simpl; constructor; auto.
  induction tl in bs, e |- *; destruct bs => //; try constructor; auto.
Qed.

Set Equations Transparent.

Section map_All.
  Context {A B C} {Q : C -> Type} {P : C -> A  -> Prop}
    (fn : forall (x : A) , (forall (y:C),  Q y -> P y x) -> B).

  Equations? map_All (l : list A) (Hl : forall y, Q y -> ∥ All (P y) l ∥) : list B :=
  | [], _ := []
  | x :: xs, h := fn x _ :: map_All xs _.
  Proof. all:clear fn map_All.
    - specialize (h y X). sq. now depelim h.
    - specialize (h y X). sq. now depelim h.
  Qed.
End map_All.

Lemma All_map_All {A B C} {Q : C -> Type} {P : C -> A -> Prop}
  {Q' : B -> Type} {R : C -> A -> Prop}
  f args (ha: forall y : C, Q y -> ∥ All (R y) args ∥) :
  (forall y : C, Q y -> All (P y) args) ->
  (forall x y rx, P y x -> Q' (f x rx)) ->
  forall y, Q y -> All Q' (map_All f args ha).
Proof.
  funelim (map_All f args ha).
  - constructor.
  - intros ha hf y hy. pose proof (ha y hy). depelim X0. econstructor; eauto.
    eapply X; eauto. intros. eapply ha in X1. now depelim X1.
Qed.

Lemma map_All_length {A B C : Type} {Q : C -> Type} {P : C -> A -> Prop}
  (fn : forall x : A, (forall y : C, Q y -> P y x) -> B)
  (l : list A) (Hl : forall y : C, Q y -> ∥ All (P y) l ∥) :
  #|map_All fn l Hl| = #|l|.
Proof.
  funelim (map_All fn l Hl); cbn; congruence.
Qed.
#[export] Hint Rewrite @map_All_length : len.

Lemma nth_error_map_All {A B C} {Q : C -> Type} {P : C -> A  -> Prop}
  (fn : forall (x : A) , (forall (y:C),  Q y -> P y x) -> B) :
  forall l : list A, forall H : (forall y : C, Q y -> ∥ All (P y) l ∥),
  forall n x,
    nth_error l n = Some x ->
    exists D, nth_error (map_All fn l H) n = Some (fn x D).
Proof.
  intros.
  funelim (map_All fn l H).
  - destruct n; depelim H0.
  - destruct n; depelim H1.
    + eexists. reflexivity.
    + now eapply H.
Qed.

Lemma All2_map2_left {A B C D E} {P : E -> A -> Type} Q (R : B -> D -> Type) {f : B -> C -> E} {l l' l'' l'''} :
  All2 R l l''' ->
  All2 Q l' l'' ->
  #|l| = #|l'| ->
  (forall x y z w, R x w -> Q y z -> P (f x y) z) ->
  All2 P (map2 f l l') l''.
Proof.
  intros hb ha hlen hPQ.
  induction ha in l, l''', hlen, hb |- *; simpl; try constructor; auto.
  - destruct l => //. simpl. constructor.
  - destruct l => //.
    noconf hlen. depelim hb.
    specialize (IHha _ _ hb H).
    simpl. constructor; auto. eapply hPQ; eauto.
Qed.

Lemma All2_map2_left_All3 {A B C} {P : A -> A -> Type} {f : B -> C -> A} {l l' l''} :
  All3 (fun x y z => P (f x y) z) l l' l'' ->
  All2 P (map2 f l l') l''.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All3_impl {A B C} {P Q : A -> B -> C -> Type} {l l' l''} :
  All3 P l l' l'' ->
  (forall x y z, P x y z -> Q x y z) ->
  All3 Q l l' l''.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma map2_app {A B C} (f : A -> B -> C) l0 l0' l1 l1' :
  #|l0| = #|l1| -> #|l0'| = #|l1'| ->
  map2 f (l0 ++ l0') (l1 ++ l1') =
  map2 f l0 l1 ++ map2 f l0' l1'.
Proof.
  induction l0 in l0', l1, l1' |- *; simpl; auto.
  - destruct l1 => //.
  - destruct l1 => /= // [=] hl hl'.
    now rewrite IHl0.
Qed.

Lemma All1_map2_right_inv {A B C} R (g : A -> B -> C) l l' : #|l| = #|l'| ->  All2 R l (map2 g l l') ->  All2 (fun x y => R x (g x y)) l l'.
Proof.
  elim: l l'=> [|x xs ih] [|y ys] //= [=] eq z; try depelim z ; try constructor=> //.
  by apply: ih.
Qed.

Lemma All1_map2_right {A B C} R (g : A -> B -> C) l l' : All2 (fun x y => R x (g x y)) l l' -> All2 R l (map2 g l l').
Proof.
  elim: l l'=> [|x xs ih] [|y ys] //= z; try constructor ; try depelim z=>//.
  by apply: ih.
Qed.

Lemma All1i_map2_right {A B C} k R (g : A -> B -> C) l l' : All2i (fun i x y => R i x (g x y)) k l l' -> All2i R k l (map2 g l l').
Proof.
  elim: l l' k=> [|x xs ih] [|y ys] //= k z; try constructor ; try depelim z=>//.
  by apply: ih.
Qed.

Lemma All1i_Alli_mix_left {A B k Q R} {l : list A} {l' : list B}
  : Alli Q k l -> All2i R k l l' -> All2i (fun i x y => Q i x * R i x y)%type k l l'.
Proof.
  move=> + h; elim: h=> [n|n x y xs ys r rs ih] q; depelim q; constructor=> //.
  by apply: ih.
Qed.

Lemma All_Alli_swap_iff A B P
  : forall ls1 ls2 n, (@All A (fun x => @Alli B (P x) n ls1) ls2) <~> (@Alli B (fun n y => @All A (fun x => P x n y) ls2) n ls1).
Proof.
  induction ls1 as [|?? IH], ls2 as [|? ls2] => n; split.
  all: inversion 1; subst; repeat constructor => //=; try (apply IH; clear IH) => //.
  all: try match goal with H : _ |- _ => apply IH in H; clear IH end.
  all: repeat match goal with H : All _ (_ :: _) |- _ => inversion H; clear H; subst end.
  all: repeat match goal with H : Alli _ _ (_ :: _) |- _ => inversion H; clear H; subst end.
  all: repeat constructor.
  all: try now auto.
  all: try now eapply All_impl; tea; cbn; inversion 1; subst => //.
  all: repeat let H := multimatch goal with H : _ |- _ => H end in
         eapply All_impl_All; [ exact H | clear H ].
  all: now apply In_All; constructor => //.
Qed.

Lemma All_eta3 {A B C P} ls
  : @All (A * B * C)%type (fun '(a, b, c) => P a b c) ls <~> All (fun abc => P abc.1.1 abc.1.2 abc.2) ls.
Proof.
  split; induction 1; constructor => //=.
  all: repeat match goal with H : _ × _ |- _ => destruct H end => //.
Qed.

Local Ltac All2_All_swap_t_step :=
  first [ progress intros
        | progress subst
        | let is_ctor_list x :=
            lazymatch x with
            | nil => idtac
            | cons _ _ => idtac
            end in
          match goal with
          | [ H : All2 _ ?x ?y |- _ ]
            => first [ is_ctor_list x | is_ctor_list y ];
               inversion H; clear H
          | [ H : All2_fold _ ?x ?y |- _ ]
            => first [ is_ctor_list x | is_ctor_list y ];
               inversion H; clear H
          | [ H : All _ ?x |- _ ]
            => is_ctor_list x; inversion H; clear H
          | [ |- (_ :: _ = []) + _ ] => right
          | [ |- (?x = ?x) + _ ] => left
          end
        | exactly_once constructor
        | solve [ eauto
                | first [ eapply All2_impl | eapply All2_fold_impl | eapply All_impl ]; tea; cbn; intros *; (inversion 1 + constructor); subst; eauto ]
        | congruence
        | now apply All_refl; constructor
        | apply All2_from_nth_error => //; lia
        | progress cbn in *
        | match goal with
          | [ H : ?x <> ?x \/ ?A |- _ ]
            => (assert A by now destruct H); clear H
          end ].

Lemma All2_All_swap A B C P
  : forall ls1 ls2 ls3,
    @All2 A B (fun x y => @All C (P x y) ls1) ls2 ls3 -> @All C (fun z => @All2 A B (fun x y => P x y z) ls2 ls3) ls1.
Proof.
  induction ls1 as [|?? IH], ls2 as [|? ls2], ls3 as [|? ls3].
  all: repeat first [ All2_All_swap_t_step
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All_impl; [ eapply All_prod | intros ? [H1 H2]; constructor; first [ exact H1 | exact H2 ] ];
                      eauto; apply IH; clear IH ].
Qed.

Lemma All_All2_swap_sum A B C P
  : forall ls1 ls2 ls3,
    @All C (fun z => @All2 A B (fun x y => P x y z) ls2 ls3) ls1 -> (ls1 = []) + (@All2 A B (fun x y => @All C (P x y) ls1) ls2 ls3).
Proof.
  induction ls1 as [|?? IH], ls2 as [|? ls2], ls3 as [|? ls3].
  all: repeat first [ All2_All_swap_t_step
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All2_impl; [ eapply All2_prod | intros * [H1 H2]; constructor; first [ exact H1 | exact H2 ] ];
                      let IH' := fresh in
                      eauto; edestruct IH as [IH'|IH']; try (apply IH'; clear IH'); clear IH ].
Qed.

Lemma All_All2_swap A B C P
  : forall ls1 ls2 ls3,
    ls1 <> [] \/ List.length ls2 = List.length ls3 -> @All C (fun z => @All2 A B (fun x y => P x y z) ls2 ls3) ls1 -> @All2 A B (fun x y => @All C (P x y) ls1) ls2 ls3.
Proof.
  destruct ls1 as [|? ls1].
  { move => ls2 ls3 H _.
    assert (#|ls2| = #|ls3|) by now destruct H.
    apply All2_from_nth_error; eauto. }
  move => ls2 ls3 _; move: ls1 ls2 ls3.
  induction ls1 as [|?? IH], ls2 as [|? ls2], ls3 as [|? ls3].
  all: repeat first [ All2_All_swap_t_step
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All2_impl; [ eapply All2_prod | intros * [H1 H2]; constructor; first [ exact H1 | exact H2 ] ]
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All2_impl; [ eapply IH | ]; clear IH ].
Qed.

Lemma All2_fold_All_swap A B P
  : forall ls1 ls2 ls3,
    @All2_fold A (fun l1 l2 x y => @All B (P l1 l2 x y) ls1) ls2 ls3 -> @All B (fun z => @All2_fold A (fun l1 l2 x y => P l1 l2 x y z) ls2 ls3) ls1.
Proof.
  induction ls1 as [|?? IH], ls2 as [|? ls2], ls3 as [|? ls3].
  all: repeat first [ All2_All_swap_t_step
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All_impl; [ eapply All_prod | intros ? [H1 H2]; constructor; first [ exact H1 | exact H2 ] ];
                      eauto; apply IH; clear IH ].
Qed.

Lemma All_All2_fold_swap_sum A B P
  : forall ls1 ls2 ls3,
    @All B (fun z => @All2_fold A (fun l1 l2 x y => P l1 l2 x y z) ls2 ls3) ls1 -> (ls1 = []) + (@All2_fold A (fun l1 l2 x y => @All B (P l1 l2 x y) ls1) ls2 ls3).
Proof.
  induction ls1 as [|?? IH], ls2 as [|? ls2], ls3 as [|? ls3].
  all: repeat first [ All2_All_swap_t_step
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All2_fold_impl; [ eapply All2_fold_prod | intros * [H1 H2]; constructor; first [ exact H1 | exact H2 ] ];
                      let IH' := fresh in
                      eauto; edestruct IH as [IH'|IH']; try (apply IH'; clear IH'); clear IH ].
Qed.

Lemma All_All2_fold_swap A B P
  : forall ls1 ls2 ls3,
    ls1 <> [] \/ List.length ls2 = List.length ls3 -> @All B (fun z => @All2_fold A (fun l1 l2 x y => P l1 l2 x y z) ls2 ls3) ls1 -> @All2_fold A (fun l1 l2 x y => @All B (P l1 l2 x y) ls1) ls2 ls3.
Proof.
  destruct ls1 as [|? ls1].
  { move => ls2 ls3 H _.
    assert (#|ls2| = #|ls3|) by now destruct H.
    apply All2_fold_from_nth_error; eauto. }
  move => ls2 ls3 _; move: ls1 ls2 ls3.
  induction ls1 as [|?? IH], ls2 as [|? ls2], ls3 as [|? ls3].
  all: repeat first [ All2_All_swap_t_step
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All2_fold_impl; [ eapply All2_fold_prod | intros * [H1 H2]; constructor; first [ exact H1 | exact H2 ] ]
                    | let H1 := fresh in
                      let H2 := fresh in
                      eapply All2_fold_impl; [ eapply IH | ]; clear IH ].
Qed.

Lemma All2_map2_right {A B C} {l : list A} {l' : list B} (f : A -> B -> C) P :
  All2 (fun x y => P x (f x y)) l l' ->
  All2 P l (map2 f l l').
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma All2i_map2_right {A B C} {n} {l : list A} {l' : list B} (f : A -> B -> C) P :
  All2i (fun n x y => P n x (f x y)) n l l' ->
  All2i P n l (map2 f l l').
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma All2_map2_right_inv {A B C} R (g : A -> B -> C) l l' : #|l| = #|l'| ->  All2 R l (map2 g l l') ->  All2 (fun x y => R x (g x y)) l l'.
Proof.
  elim: l l'=> [|x xs ih] [|y ys] //= [=] eq z; try depelim z ; try constructor=> //.
  by apply: ih.
Qed.

Lemma All2i_Alli_mix_left {A B k Q R} {l : list A} {l' : list B}
  : Alli Q k l -> All2i R k l l' -> All2i (fun i x y => (Q i x * R i x y)%type) k l l'.
Proof.
  move=> + h; elim: h=> [n|n x y xs ys r rs ih] q; depelim q; constructor=> //.
  by apply: ih.
Qed.
