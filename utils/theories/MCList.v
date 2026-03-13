From Equations Require Import Equations.
From Coq Require Import Bool Arith Lia SetoidList Utf8.
From MetaCoq.Utils Require Import MCPrelude MCRelations.

Set Equations Transparent.

Export ListNotations.

Arguments firstn : simpl nomatch.
Arguments skipn : simpl nomatch.

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |").

#[global] Hint Rewrite map_length app_length List.rev_length : len.

Arguments nil {_}, _.

#[global] Instance proper_map_ho {A B} : Proper ((pointwise_relation A Logic.eq) ==> Logic.eq ==> Logic.eq)
  (@map A B).
Proof.
  intros f g Hfg x y ->. apply map_ext.
  apply Hfg.
Qed.

Lemma app_tip_assoc {A} (l : list A) x l' : (l ++ [x]) ++ l' = l ++ (x :: l').
Proof. now rewrite <- app_assoc. Qed.

Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.

Fixpoint mapi_rec {A B} (f : nat -> A -> B) (l : list A) (n : nat) : list B :=
  match l with
  | [] => []
  | hd :: tl => f n hd :: mapi_rec f tl (S n)
  end.

Definition mapi {A B} (f : nat -> A -> B) (l : list A) := mapi_rec f l 0.

Program Fixpoint safe_nth {A} (l : list A) (n : nat | n < List.length l) : A :=
  match l with
  | nil => _
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth tl n
    end
  end.
Next Obligation.
  exfalso. simpl in H. inversion H.
Defined.
Next Obligation.
  simpl in H. auto with arith.
Defined.

Fixpoint map2 {A B C} (f : A -> B -> C) (l : list A) (l' : list B) : list C :=
  match l, l' with
  | hd :: tl, hd' :: tl' => f hd hd' :: map2 f tl tl'
  | _, _ => []
  end.

Lemma map2_ext {A B C} (f g : A -> B -> C) (l : list A) (l' : list B) :
  (forall x y, f x y = g x y) ->
  map2 f l l' = map2 g l l'.
Proof.
  intros H.
  induction l in l' |- *; destruct l'; simpl; auto. f_equal; eauto.
Qed.

Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    now rewrite <- IHl.
Qed.

Definition rev {A} (l : list A) : list A :=
  let fix aux (l : list A) (acc : list A) : list A :=
      match l with
      | [] => acc
      | x :: l => aux l (x :: acc)
      end
  in aux l [].

Definition rev_map {A B} (f : A -> B) (l : list A) : list B :=
  let fix aux (l : list A) (acc : list B) : list B :=
      match l with
      | [] => acc
      | x :: l => aux l (f x :: acc)
      end
  in aux l [].

Fact rev_cons :
  forall {A} {l} {a : A},
    rev (a :: l) = (rev l ++ [a])%list.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [a]). rewrite IHl.
      change (a :: acc) with ([a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_map_cons :
  forall {A B} {f : A -> B} {l} {a : A},
    rev_map f (a :: l) = (rev_map f l ++ [f a])%list.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [f a]). rewrite IHl.
      change (f a :: acc) with ([f a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_length :
  forall {A} {l : list A},
    List.length (rev l) = List.length l.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) = (List.length acc + List.length l)%nat).
  { intro l. induction l ; intro acc.
    - cbn. auto with arith.
    - cbn. rewrite IHl. cbn. auto with arith.
  }
  intro l. apply h.
Defined.
#[global] Hint Rewrite @rev_length : len.

Fact rev_map_length :
  forall {A B} {f : A -> B} {l : list A},
    List.length (rev_map f l) = List.length l.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) =
                       (List.length acc + List.length l)%nat).
  { intro l. induction l ; intro acc.
    - cbn. auto with arith.
    - cbn. rewrite IHl. cbn. auto with arith.
  }
  intro l. apply h.
Defined.
#[global] Hint Rewrite @rev_map_length : len.

Fact rev_map_app :
  forall {A B} {f : A -> B} {l1 l2},
    (rev_map f (l1 ++ l2) = rev_map f l2 ++ rev_map f l1)%list.
Proof.
  intros A B f l1 l2. revert B f l2.
  induction l1 ; intros B f l2.
  - simpl. cbn. rewrite app_nil_r. reflexivity.
  - simpl. rewrite !rev_map_cons. rewrite IHl1.
    rewrite app_assoc. reflexivity.
Defined.

Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (fun x => g (f x)) l.
Proof. apply map_map. Qed.

Lemma map_id_f {A} (l : list A) (f : A -> A) :
  (forall x, f x = x) ->
  map f l = l.
Proof.
  induction l; intros; simpl; try easy.
  rewrite H. f_equal. eauto.
Qed.

Section Reverse_Induction.
  Context {A : Type}.
  Lemma rev_list_ind :
    forall P:list A-> Type,
      P [] ->
        (forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))) ->
        forall l:list A, P (Coq.Lists.List.rev l).
  Proof using Type.
    induction l; auto.
  Qed.

  Theorem rev_ind :
    forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof using Type.
    intros.
    generalize (rev_involutive l).
    intros E; rewrite <- E.
    apply (rev_list_ind P).
    auto.

    simpl.
    intros.
    apply (X0 a (List.rev l0)).
    auto.
  Qed.

End Reverse_Induction.

Lemma skipn_nil :
  forall {A} n, @skipn A n [] = [].
Proof.
  intros A [| n] ; reflexivity.
Qed.


Lemma skipn_S {A} a (l : list A) n : skipn (S n) (a :: l) = skipn n l.
Proof. reflexivity. Qed.

Lemma mapi_ext_size {A B} (f g : nat -> A -> B) l k :
  (forall k' x, k' < k + #|l| -> f k' x = g k' x) ->
  mapi_rec f l k = mapi_rec g l k.
Proof.
  intros Hl. generalize (Nat.le_refl k). generalize k at 1 3 4.
  induction l in k, Hl |- *. simpl. auto.
  intros. simpl in *. erewrite Hl; try lia.
  f_equal. eapply (IHl (S k)); try lia. intros. apply Hl. lia.
Qed.

Lemma map_ext_size {A B} (f g : nat -> A -> B) l :
  (forall k x, k < #|l| -> f k x = g k x) ->
  mapi f l = mapi g l.
Proof.
  intros Hl. unfold mapi. apply mapi_ext_size. simpl. auto.
Qed.

Lemma firstn_map {A B} n (f : A -> B) l : firstn n (map f l) = map f (firstn n l).
Proof.
  revert l; induction n. reflexivity.
  destruct l; simpl in *; congruence.
Qed.

Lemma mapi_rec_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) k l :
  mapi_rec g (mapi_rec f l k) k = mapi_rec (fun k x => g k (f k x)) l k.
Proof.
  induction l in k |- *; simpl; auto. now rewrite IHl.
Qed.

Lemma mapi_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) l :
  mapi g (mapi f l) = mapi (fun k x => g k (f k x)) l.
Proof. apply mapi_rec_compose. Qed.

Lemma map_ext {A B : Type} (f g : A -> B) (l : list A) :
  (forall x, f x = g x) ->
  map f l = map g l.
Proof.
  intros.
  induction l; trivial.
  intros. simpl. rewrite H. congruence.
Defined.

Require Import ssreflect.

Lemma map_skipn {A B} (f : A -> B) (l : list A) (n : nat) : map f (skipn n l) = skipn n (map f l).
Proof.
  elim: n l => l // IHn.
  by case => //.
Qed.

Lemma nth_error_map {A B} (f : A -> B) n l : nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  elim: n l; case => // IHn l /=.
  - by case: l => //.
  - by case => //.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) : l <> [] -> map f l <> [].
Proof. induction l; simpl; congruence. Qed.
#[global]
Hint Resolve map_nil : wf.

Inductive nth_error_Spec {A} (l : list A) (n : nat) : option A -> Type :=
| nth_error_Spec_Some x : nth_error l n = Some x -> n < length l -> nth_error_Spec l n (Some x)
| nth_error_Spec_None : length l <= n -> nth_error_Spec l n None.

Lemma mapi_rec_eqn {A B} (f : nat -> A -> B) (l : list A) a n :
  mapi_rec f (a :: l) n = f n a :: mapi_rec f l (S n).
Proof. simpl. f_equal. Qed.

Lemma nth_error_mapi_rec {A B} (f : nat -> A -> B) n k l :
  nth_error (mapi_rec f l k) n = option_map (f (n + k)) (nth_error l n).
Proof.
  induction l in n, k |- *.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + rewrite IHl. by rewrite <- Nat.add_succ_comm.
Qed.

Lemma nth_error_mapi {A B} (f : nat -> A -> B) n l :
  nth_error (mapi f l) n = option_map (f n) (nth_error l n).
Proof.
  unfold mapi; rewrite nth_error_mapi_rec.
  now rewrite -> Nat.add_0_r.
Qed.

Lemma nth_error_Some_length {A} {l : list A} {n t} : nth_error l n = Some t -> n < length l.
Proof. rewrite <- nth_error_Some. destruct (nth_error l n); congruence. Qed.

Lemma nth_error_Some_non_nil {A} (l : list A) (n : nat) (x : A) : nth_error l n = Some x -> l <> [].
Proof.
  destruct l, n; simpl; congruence.
Qed.

Lemma nth_error_Some' {A} l n : (∑ x : A, nth_error l n = Some x) <~> n < length l.
Proof.
  revert n. induction l; destruct n; simpl.
  - split; [now destruct 1 | intros H'; elimtype False; inversion H'].
  - split; [now destruct 1 | intros H'; elimtype False; inversion H'].
  - split; now intuition eauto with arith.
  - destruct (IHl n); split; intros; auto with arith.
Qed.

Lemma nth_error_spec {A} (l : list A) (n : nat) : nth_error_Spec l n (nth_error l n).
Proof.
  destruct nth_error eqn:Heq.
  constructor; auto. now apply nth_error_Some_length in Heq.
  constructor; auto. now apply nth_error_None in Heq.
Qed.

Lemma nth_error_app_left {A} (l l' : list A) n t : nth_error l n = Some t -> nth_error (l ++ l') n = Some t.
Proof. induction l in n |- *; destruct n; simpl; try congruence. auto. Qed.

Lemma nth_error_nil {A} n : nth_error (nil A) n = None.
Proof. destruct n; auto. Qed.
#[global] Hint Rewrite @nth_error_nil.

Fixpoint chop {A} (n : nat) (l : list A) :=
  match n with
  | 0 => ([], l)
  | S n =>
    match l with
    | hd :: tl =>
      let '(l, r) := chop n tl in
      (hd :: l, r)
    | [] => ([], [])
    end
  end.

Lemma nth_map' {A B} (f : A -> B) n l d d' :
  (d' = f d) ->
  nth n (map f l) d' = f (nth n l d).
Proof.
  induction n in l |- *; destruct l; simpl; auto.
Qed.

Lemma mapi_map {A B C} (f : nat -> B -> C) (l : list A) (g : A -> B) :
  mapi f (map g l) = mapi (fun i x => f i (g x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence.
Qed.

Lemma map_mapi {A B C} (f : nat -> A -> B) (l : list A) (g : B -> C) :
  map g (mapi f l) = mapi (fun i x => g (f i x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence.
Qed.

Lemma chop_map {A B} (f : A -> B) n l l' l'' :
  chop n l = (l', l'') -> chop n (map f l) = (map f l', map f l'').
Proof.
  induction n in l, l', l'' |- *; destruct l; try intros [= <- <-]; simpl; try congruence.
  destruct (chop n l) eqn:Heq. specialize (IHn _ _ _ Heq).
  intros [= <- <-]. now rewrite IHn. Qed.

Lemma chop_n_app {A} {l l' : list A} {n} : n = length l -> chop n (l ++ l') = (l, l').
Proof.
  intros ->. induction l; simpl; try congruence.
  now rewrite IHl.
Qed.

Lemma mapi_mapi {A B C} (g : nat -> A -> B) (f : nat -> B -> C) (l : list A) :
  mapi f (mapi g l) = mapi (fun n x => f n (g n x)) l.
Proof. unfold mapi. generalize 0. induction l; simpl; try congruence. Qed.


Lemma mapi_cst_map {A B} (f : A -> B) l : mapi (fun _ => f) l = map f l.
Proof.
  unfold mapi. generalize 0. induction l; cbn; auto. intros. now rewrite IHl.
Qed.

Lemma mapi_rec_ext {A B} (f g : nat -> A -> B) (l : list A) n :
  (forall k x, n <= k -> k < length l + n -> f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros Hfg. induction l in n, Hfg |- *; simpl; try congruence.
  intros. rewrite Hfg; simpl; try lia. f_equal.
  rewrite IHl; auto. intros. apply Hfg. simpl; lia. simpl. lia.
Qed.

Lemma mapi_ext {A B} (f g : nat -> A -> B) (l : list A) :
  (forall n x, f n x = g n x) ->
  mapi f l = mapi g l.
Proof. intros; now apply mapi_rec_ext. Qed.

Lemma mapi_rec_Sk {A B} (f : nat -> A -> B) (l : list A) k :
  mapi_rec f l (S k) = mapi_rec (fun n x => f (S n) x) l k.
Proof.
  induction l in k |- *; simpl; congruence.
Qed.

Lemma mapi_rec_add {A B : Type} (f : nat -> A -> B) (l : list A) (n k : nat) :
  mapi_rec f l (n + k) = mapi_rec (fun (k : nat) (x : A) => f (n + k) x) l k.
Proof.
  induction l in n, k |- *; simpl; auto.
  f_equal. rewrite (IHl (S n) k). rewrite mapi_rec_Sk.
  eapply mapi_rec_ext. intros. f_equal. lia.
Qed.

Lemma mapi_rec_app {A B} (f : nat -> A -> B) (l l' : list A) n :
  (mapi_rec f (l ++ l') n = mapi_rec f l n ++ mapi_rec f l' (length l + n))%list.
Proof.
  induction l in n |- *; simpl; try congruence.
  rewrite IHl. f_equal. now rewrite <- Nat.add_succ_comm.
Qed.

Lemma mapi_app {A B} (f : nat -> A -> B) (l l' : list A) :
  (mapi f (l ++ l') = mapi f l ++ mapi (fun n x => f (length l + n) x) l')%list.
Proof.
  unfold mapi; rewrite mapi_rec_app.
  f_equal. generalize 0.
  induction l'; intros. reflexivity. rewrite mapi_rec_eqn.
  change (S (length l + n)) with (S (length l) + n).
  rewrite (Nat.add_succ_comm _ n). now rewrite IHl'.
Qed.

Lemma rev_mapi_rec {A B} (f : nat -> A -> B) (l : list A) n k : k <= n ->
  List.rev (mapi_rec f l (n - k)) = mapi_rec (fun k x => f (Nat.pred (length l) + n - k) x) (List.rev l) k.
Proof.
  unfold mapi. revert n k.
  induction l using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite mapi_rec_app rev_app_distr; simpl. rewrite IHl; auto. simpl.
  rewrite app_length. simpl. f_equal. f_equal. lia. rewrite mapi_rec_Sk.
  apply mapi_rec_ext. intros. f_equal. rewrite List.rev_length in H1.
  rewrite Nat.add_1_r. simpl; lia.
Qed.

Lemma rev_mapi {A B} (f : nat -> A -> B) (l : list A) :
  List.rev (mapi f l) = mapi (fun k x => f (Nat.pred (length l) - k) x) (List.rev l).
Proof.
  unfold mapi. change 0 with (0 - 0) at 1.
  rewrite rev_mapi_rec; auto. now rewrite Nat.add_0_r.
Qed.

Lemma mapi_rec_rev {A B} (f : nat -> A -> B) (l : list A) n :
  mapi_rec f (List.rev l) n = List.rev (mapi (fun k x => f (length l + n - S k) x) l).
Proof.
  unfold mapi. revert n.
  induction l using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite IHl mapi_rec_app.
  simpl. rewrite rev_unit. f_equal.
  rewrite app_length. simpl. f_equal. lia.
  rewrite app_length. simpl.
  f_equal. eapply mapi_rec_ext. intros.
  f_equal. lia.
Qed.

Lemma mapi_rev {A B} (f : nat -> A -> B) (l : list A) :
  mapi f (List.rev l) = List.rev (mapi (fun k x => f (length l - S k) x) l).
Proof. unfold mapi at 1. rewrite mapi_rec_rev. now rewrite Nat.add_0_r. Qed.

Lemma mapi_rec_length {A B} (f : nat -> A -> B) (l : list A) n :
  length (mapi_rec f l n) = length l.
Proof. induction l in n |- *; simpl; try congruence. Qed.
#[global] Hint Rewrite @mapi_rec_length : len.

Lemma mapi_length {A B} (f : nat -> A -> B) (l : list A) :
  length (mapi f l) = length l.
Proof. apply mapi_rec_length. Qed.
#[global] Hint Rewrite @mapi_length : len.

Lemma mapi_cons {A B} (f : nat -> A -> B) a l :
  mapi f (a :: l) = f 0 a :: mapi (fun x => f (S x)) l.
Proof.
  now rewrite /mapi /= mapi_rec_Sk.
Qed.

Lemma mapi_nth {A B} (l : list A) (l' : list B) (default : A) : #|l| = #|l'| ->
    mapi (fun i _ => nth i l default) l' = l.
Proof.
  induction l' in l |- *; destruct l => /= //.
  simpl. intros [= Hl]. cbn. f_equal. now rewrite mapi_rec_Sk.
Qed.

Lemma skipn_length {A} n (l : list A) : length (skipn n l) = length l - n.
Proof.
  induction l in n |- *; destruct n; simpl; auto.
Qed.

Lemma combine_map_id {A B} (l : list (A * B)) :
 l = combine (map fst l) (map snd l).
Proof.
  induction l ; simpl; try easy.
  destruct a. now f_equal.
Qed.

Local Ltac invs H := inversion H; subst; clear H.

Lemma last_inv A (l1 l2 : list A) x y :
  (l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y)%list.
Proof.
  revert l2. induction l1; cbn; intros.
  - destruct l2; cbn in H; invs H. eauto. destruct l2; invs H2.
  - destruct l2; invs H. destruct l1; invs H2.
    eapply IHl1 in H2 as []. split; congruence.
Qed.

Lemma skipn_all2 :
  forall {A n} (l : list A),
    #|l| <= n ->
         skipn n l = [].
Proof.
  intros A n l h. revert l h.
  induction n ; intros l h.
  - destruct l.
    + reflexivity.
    + cbn in h. inversion h.
  - destruct l.
    + reflexivity.
    + simpl. apply IHn. cbn in h. lia.
Qed.

Lemma not_empty_map {A B} (f : A -> B) l : l <> [] -> map f l <> [].
Proof.
  intro H; destruct l; intro e; now apply H.
Qed.

Lemma nth_error_skipn_add A l m n (a : A) :
  nth_error l (m + n) = Some a ->
  nth_error (skipn m l) n = Some a.
Proof.
  induction m in n, l |- *.
  - cbn. destruct l; firstorder.
  - cbn. destruct l.
    + inversion 1.
    + eapply IHm.
Qed.

Lemma skipn_all_app :
  forall A (l1 l2 : list A),
    skipn #|l1| (l1 ++ l2) = l2.
Proof.
  intros A l1 l2.
  induction l1 in l2 |- *.
  - reflexivity.
  - simpl. eauto.
Qed.

Lemma rev_map_spec {A B} (f : A -> B) (l : list A) :
  rev_map f l = List.rev (map f l).
Proof.
  unfold rev_map.
  rewrite -(app_nil_r (List.rev (map f l))).
  generalize (@nil B).
  induction l; simpl; auto. intros l0.
  rewrite IHl. now rewrite -app_assoc.
Qed.

Lemma skipn_0 {A} (l : list A) : skipn 0 l = l.
Proof. reflexivity. Qed.

Lemma skipn_0_eq {A} (l : list A) n : n = 0 -> skipn n l = l.
Proof. intros ->; apply skipn_0. Qed.

Lemma skipn_n_Sn {A} n s (x : A) xs : skipn n s = x :: xs -> skipn (S n) s = xs.
Proof.
  induction n in s, x, xs |- *.
  - unfold skipn. now intros ->.
  - destruct s; simpl. intros H; discriminate. apply IHn.
Qed.

Lemma skipn_all {A} (l : list A) : skipn #|l| l = [].
Proof.
  induction l; simpl; auto.
Qed.

Lemma skipn_app_le {A} n (l l' : list A) : n <= #|l| -> skipn n (l ++ l') = skipn n l ++ l'.
Proof.
  induction l in n, l' |- *; simpl; auto.
  intros Hn. destruct n; try lia. reflexivity.
  intros Hn. destruct n. reflexivity.
  rewrite !skipn_S. apply IHl. lia.
Qed.

Lemma skipn_mapi_rec {A B} n (f : nat -> A -> B) k (l : list A) :
  skipn n (mapi_rec f l k) =
  mapi_rec f (skipn n l) (n + k).
Proof.
  induction n in f, l, k |- *.
  - now rewrite !skipn_0.
  - destruct l.
    * reflexivity.
    * simpl. rewrite IHn.
      now rewrite Nat.add_succ_r.
Qed.

Lemma skipn_map_length {A B} n (f : A -> B) (l : list A) :
  #|skipn n (map f l)| = #|skipn n l|.
Proof.
  now rewrite !List.skipn_length; len.
Qed.
#[global] Hint Rewrite @skipn_map_length : len.

Lemma firstn_ge {A} (l : list A) n : #|l| <= n -> firstn n l = l.
Proof.
  induction l in n |- *; simpl; intros; auto. now rewrite firstn_nil.
  destruct n; simpl. lia. rewrite IHl; auto. lia.
Qed.

Lemma firstn_0 {A} (l : list A) n : n = 0 -> firstn n l = [].
Proof.
  intros ->. reflexivity.
Qed.

Lemma skipn_firstn_skipn {A} (l : list A) n : skipn n (firstn (S n) l) ++ skipn (S n) l = skipn n l.
Proof.
  induction l in n |- *; simpl; auto. now rewrite app_nil_r.
  destruct n=> /=; auto.
Qed.

Lemma firstn_firstn_firstn {A} (l : list A) n : firstn n (firstn (S n) l) = firstn n l.
Proof.
  induction l in n |- *; simpl; auto.
  destruct n=> /=; auto. now rewrite IHl.
Qed.

Lemma skipn_eq_cons {A} n (l : list A) hd tl : skipn n l = hd :: tl ->
  (nth_error l n = Some hd) /\ (skipn (S n) l = tl).
Proof.
  induction n in l, hd, tl |- *.
  - rewrite skipn_0 => ->. now simpl.
  - destruct l as [|hd' tl'].
    * rewrite skipn_nil. discriminate.
    * simpl. apply IHn.
Qed.

Fixpoint split_at_aux {A} (n : nat) (acc : list A) (l : list A) : list A * list A :=
  match n with
  | 0 => (List.rev acc, l)
  | S n' =>
    match l with
    | [] => (List.rev acc, [])
    | hd :: l' => split_at_aux n' (hd :: acc) l'
    end
  end.

Definition split_at {A} (n : nat) (l : list A) : list A * list A :=
  split_at_aux n [] l.

Lemma split_at_aux_firstn_skipn {A} n acc (l : list A) : split_at_aux n acc l = (List.rev acc ++ firstn n l, skipn n l).
Proof.
  induction n in acc, l |- *; destruct l; simpl; auto.
  now rewrite app_nil_r.
  now rewrite app_nil_r.
  now rewrite app_nil_r.
  rewrite IHn. simpl.
  now rewrite -app_assoc /=.
Qed.

Lemma split_at_firstn_skipn {A} n (l : list A) : split_at n l = (firstn n l, skipn n l).
Proof.
  now rewrite /split_at split_at_aux_firstn_skipn /= //.
Qed.

Lemma rev_app :
  forall A (l l' : list A),
    (rev (l ++ l') = rev l' ++ rev l)%list.
Proof.
  intros A l l'.
  induction l in l' |- *.
  - simpl. change (rev (nil A)) with (nil A).
    rewrite app_nil_r. reflexivity.
  - simpl. rewrite rev_cons. rewrite IHl.
    rewrite rev_cons. rewrite app_assoc. reflexivity.
Qed.

Lemma rev_invol :
  forall A (l : list A),
    rev (rev l) = l.
Proof.
  intros A l. induction l ; eauto.
  rewrite rev_cons. rewrite rev_app. simpl.
  rewrite IHl. reflexivity.
Qed.

Lemma list_ind_rev :
  forall A (P : list A -> Prop),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l). clear l. intro l.
  induction l ; auto.
  rewrite rev_cons. eauto.
Qed.

Lemma list_rect_rev :
  forall A (P : list A -> Type),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l). clear l. intro l.
  induction l ; auto.
  rewrite rev_cons. eauto.
Qed.



Lemma last_app {A} (l l' : list A) d : l' <> [] -> last (l ++ l') d = last l' d.
Proof.
  revert l'. induction l; simpl; auto. intros.
  destruct l. simpl. destruct l'; congruence. simpl.
  specialize (IHl _ H). apply IHl.
Qed.

Lemma last_nonempty_eq {A} {l : list A} {d d'} : l <> [] -> last l d = last l d'.
Proof.
  induction l; simpl; try congruence.
  intros. destruct l; auto. apply IHl. congruence.
Qed.

Lemma nth_error_removelast {A} (args : list A) n :
  n < Nat.pred #|args| -> nth_error args n = nth_error (removelast args) n.
Proof.
  induction n in args |- *; destruct args; intros; auto.
  simpl. destruct args. inversion H. reflexivity.
  simpl. rewrite IHn. simpl in H. auto with arith.
  destruct args, n; reflexivity.
Qed.

Lemma nth_error_skipn {A} n (l : list A) i : nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l in n, i |- *; destruct n; simpl; auto.
    by case: i.
Qed.

Lemma nth_error_firstn {A} n (l : list A) i : nth_error (firstn n l) i = if (i <? n) then nth_error l i else None.
Proof.
  induction l in n, i |- *; destruct n; simpl; auto.
  all: rewrite ?nth_error_nil => //.
  all: try by case: Nat.ltb.
  move: (IHl n (pred i)).
  by case: i.
Qed.

Lemma skipn_skipn {A} n m (l : list A) : skipn n (skipn m l) = skipn (m + n) l.
Proof.
  induction m in n, l |- *. auto.
  simpl. destruct l. destruct n; reflexivity.
  now rewrite skipn_S skipn_S.
Qed.

Lemma skipn_nth_error {A} (l : list A) i :
  match nth_error l i with
  | Some a => skipn i l = a :: skipn (S i) l
  | None => skipn i l = []
  end.
Proof.
  induction l in i |- *. destruct i. reflexivity. reflexivity.
  destruct i. simpl. reflexivity.
  simpl. specialize (IHl i). destruct nth_error.
  rewrite [skipn _ _]IHl. reflexivity.
  rewrite [skipn _ _]IHl. reflexivity.
Qed.

Lemma nth_error_app_ge {A} (l l' : list A) (v : nat) :
  length l <= v ->
  nth_error (l ++ l') v = nth_error l' (v - length l).
Proof.
  revert v; induction l; simpl; intros.
  now rewrite Nat.sub_0_r.
  destruct v. lia.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_lt {A} (l l' : list A) (v : nat) :
  v < length l ->
  nth_error (l ++ l') v = nth_error l v.
Proof.
  revert v; induction l; simpl; intros. easy.
  destruct v; trivial.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_full {A} (l l' : list A) (v : nat) :
  nth_error (l ++ l') v = if v <? #|l| then nth_error l v else nth_error l' (v - #|l|).
Proof.
  case: Nat.ltb_spec0 => ?; first [ apply nth_error_app1 | apply nth_error_app2 ]; lia.
Qed.

Lemma nth_error_app_inv X (x : X) n l1 l2 :
  nth_error (l1 ++ l2) n = Some x -> (n < #|l1| /\ nth_error l1 n = Some x) \/ (n >= #|l1| /\ nth_error l2 (n - List.length l1) = Some x).
Proof.
  destruct (le_lt_dec #|l1| n).
  - intros. rewrite nth_error_app2 in H; eauto.
  - intros. rewrite nth_error_app1 in H; eauto.
Qed.


Lemma nth_error_rev {A} (l : list A) i : i < #|l| ->
  nth_error l i = nth_error (List.rev l) (#|l| - S i).
Proof.
  revert l. induction i. destruct l; simpl; auto.
  induction l using rev_ind; simpl. auto.
  rewrite rev_app_distr. simpl.
  rewrite app_length. simpl.
  replace (#|l| + 1 - 0) with (S #|l|) by lia. simpl.
  rewrite Nat.sub_0_r in IHl. auto with arith.

  destruct l. simpl; auto. simpl. intros. rewrite IHi. lia.
  assert (#|l| - S i < #|l|) by lia.
  rewrite nth_error_app_lt. rewrite List.rev_length; auto.
  reflexivity.
Qed.

Lemma nth_error_rev_inv {A} (l : list A) i :
  i < #|l| ->
  nth_error (List.rev l) i = nth_error l (#|l| - S i).
Proof.
  intros Hi.
  rewrite nth_error_rev ?List.rev_length; auto.
  now rewrite List.rev_involutive.
Qed.

Lemma nth_error_snoc {A} (l : list A) (a : A) (l' : list A) i :
  i = #|l| ->
  nth_error (l ++ a :: l') i = Some a.
Proof.
  intros ->.
  rewrite nth_error_app_ge; [easy|].
  now rewrite Nat.sub_diag.
Qed.

Lemma nth_error_last {A l a} : l <> [] -> nth_error l (Nat.pred #|l|) = Some (@last A l a).
Proof.
  induction l using rev_ind => // ?.
  rewrite app_length -Nat.add_pred_r //= Nat.add_0_r nth_error_snoc //= last_last //.
Qed.


Lemma map_inj :
  forall A B (f : A -> B) l l',
    (forall x y, f x = f y -> x = y) ->
    map f l = map f l' ->
    l = l'.
Proof.
  intros A B f l l' h e.
  induction l in l', e |- *.
  - destruct l' ; try discriminate. reflexivity.
  - destruct l' ; try discriminate. inversion e.
    f_equal ; eauto.
Qed.

Section ListSize.
  Context {A} (size : A -> nat).

  Fixpoint list_size (l : list A) : nat :=
    match l with
    | [] =>  0
    | a :: v => S (size a + list_size v)
    end.

  Lemma list_size_app (l l' : list A)
    : list_size (l ++ l') = list_size l + list_size l'.
  Proof using Type.
    induction l; simpl. reflexivity.
    rewrite IHl; lia.
  Qed.

  Lemma list_size_rev (l : list A)
    : list_size (rev l) = list_size l.
  Proof using Type.
    induction l; simpl. reflexivity.
    rewrite rev_cons list_size_app IHl; cbn; lia.
  Qed.

  Lemma list_size_length (l : list A)
    : list_size l >= length l.
  Proof using Type.
    induction l; simpl; lia.
  Qed.


End ListSize.

Section ListSizeMap.
  Context {A} (sizeA : A -> nat).
  Context {B} (sizeB : B -> nat).

  Lemma list_size_map (f : A -> B) l :
    list_size sizeB (map f l) = list_size (fun x => sizeB (f x)) l.
  Proof using Type.
    induction l; simpl; eauto.
  Qed.

  Lemma list_size_mapi_rec_eq (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi_rec f l k) = list_size sizeA l.
  Proof using Type.
    intro H. induction l in k |- *. reflexivity.
    simpl. rewrite IHl. rewrite H. lia.
  Qed.

  Lemma list_size_mapi_eq (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi f l) = list_size sizeA l.
  Proof using Type.
    unfold mapi. intros. now apply list_size_mapi_rec_eq.
  Qed.

  Lemma list_size_map_eq (l : list A) (f : A -> B) :
    (forall x, sizeA x = sizeB (f x)) ->
    list_size sizeB (map f l) = list_size sizeA l.
  Proof using Type.
    intros.
    induction l; simpl; auto.
  Qed.

  Lemma list_size_mapi_rec_le (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi_rec f l k) <= list_size sizeA l.
  Proof using Type.
    intro H. induction l in k |- *. reflexivity.
    simpl. specialize (H k a). specialize (IHl (S k)). lia.
  Qed.

  Lemma list_size_mapi_le (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi f l) <= list_size sizeA l.
  Proof using Type.
    unfold mapi. intros. now apply list_size_mapi_rec_le.
  Qed.

  Lemma list_size_map_le (l : list A) (f : A -> B) :
    (forall x, sizeB (f x) <= sizeA x) ->
    list_size sizeB (map f l) <= list_size sizeA l.
  Proof using Type.
    intros.
    induction l; simpl; auto. specialize (H a).
    lia.
  Qed.

End ListSizeMap.

Lemma list_size_map_hom {A} (size : A -> nat) (l : list A) (f : A -> A) :
  (forall x, size x = size (f x)) ->
  list_size size (map f l) = list_size size l.
Proof.
  intros.
  induction l; simpl; auto.
Defined.

Lemma InA_In_eq {A} x (l : list A) : InA Logic.eq x l <-> In x l.
Proof.
  etransitivity. eapply InA_alt.
  firstorder. now subst.
Qed.

Lemma forallb_rev {A} (p : A -> bool) l :
  forallb p (List.rev l) = forallb p l.
Proof.
  induction l using rev_ind; simpl; try congruence.
  rewrite rev_unit forallb_app. simpl. rewrite <- IHl.
  now rewrite andb_comm andb_true_r.
Qed.

Fixpoint unfold {A} (n : nat) (f : nat -> A) : list A :=
  match n with
  | 0 => []
  | S n => unfold n f ++ [f n]
  end.

Lemma mapi_irrel_list {A B} (f : nat -> A) (l l' : list B) :
  #|l| = #|l'| ->
  mapi (fun i (x : B) => f i) l = mapi (fun i x => f i) l'.
Proof.
  induction l in f, l' |- *; destruct l' => //; simpl; auto.
  intros [= eq]. unfold mapi. simpl. f_equal.
  rewrite !mapi_rec_Sk.
  now rewrite [mapi_rec _ _ _](IHl (fun x => (f (S x))) l').
Qed.

Lemma mapi_unfold {A B} (f : nat -> B) l : mapi (fun i (x : A) => f i) l = unfold #|l| f.
Proof.
  unfold mapi.
  induction l in f |- *; simpl; auto.
  rewrite mapi_rec_Sk.
  rewrite -IHl. rewrite -(mapi_rec_Sk (fun i x => f i) l 0).
  change [f #|l|] with (mapi_rec (fun i x => f i) [a] #|l|).
  rewrite -(Nat.add_0_r #|l|). rewrite -mapi_rec_app.
  change (f 0 :: _) with (mapi (fun i x => f i) (a :: l)).
  apply mapi_irrel_list. simpl. rewrite app_length /=; lia.
Qed.

Lemma unfold_length {A} (f : nat -> A) m : #|unfold m f| = m.
Proof.
  induction m; simpl; rewrite ?app_length /=; auto. lia.
Qed.
#[global] Hint Rewrite @unfold_length : len.

Lemma nth_error_unfold {A} (f : nat -> A) m n : n < m <-> nth_error (unfold m f) n = Some (f n).
Proof.
  induction m in n |- *; split; intros Hn; try lia.
  - simpl in Hn. rewrite nth_error_nil in Hn. discriminate.
  - destruct (Classes.eq_dec n m); [subst|].
    * simpl. rewrite nth_error_app_ge unfold_length // Nat.sub_diag /= //.
    * simpl. rewrite nth_error_app_lt ?unfold_length //; try lia.
      apply IHm; lia.
  - simpl in Hn. eapply nth_error_Some_length in Hn.
    rewrite app_length /= unfold_length in Hn. lia.
Qed.

Lemma nth_error_unfold_inv {A} (f : nat -> A) m n t : nth_error (unfold m f) n = Some t -> t = (f n).
Proof.
  induction m in n |- *; intros Hn; try lia.
  - simpl in Hn. rewrite nth_error_nil in Hn. discriminate.
  - simpl in Hn.
    pose proof (nth_error_Some_length Hn).
    rewrite app_length /= unfold_length in H.
    destruct (Classes.eq_dec n m); [subst|].
    * simpl. revert Hn. rewrite nth_error_app_ge unfold_length // Nat.sub_diag /= //; congruence.
    * simpl. revert Hn. rewrite nth_error_app_lt ?unfold_length //; try lia. auto.
Qed.

Lemma In_unfold_inj {A} (f : nat -> A) n i :
  (forall i j, f i = f j -> i = j) ->
  In (f i) (unfold n f) -> i < n.
Proof.
  intros hf.
  induction n; simpl => //.
  intros H; apply in_app_or in H.
  destruct H.
  - specialize (IHn H). lia.
  - simpl in H. destruct H; [apply hf in H|].
    * subst. auto.
    * destruct H.
Qed.

Lemma forallb_unfold {A} (f : A -> bool) (g : nat -> A) n :
  (forall x, x < n -> f (g x)) ->
  forallb f (unfold n g).
Proof.
  intros fg.
  induction n; simpl; auto.
  rewrite forallb_app IHn //.
  intros x lt; rewrite fg //. lia.
  rewrite /= fg //.
Qed.

Lemma forallb_mapi {A B} (p : B -> bool) (f : nat -> B) l :
  (forall i, i < #|l| -> p (f i)) ->
  forallb p (mapi (fun i (x : A) => f i) l).
Proof.
  intros Hp. rewrite (mapi_unfold f).
  induction #|l| in *; simpl; auto.
  rewrite forallb_app. simpl. now rewrite Hp // !andb_true_r.
Qed.

Lemma fold_left_andb_forallb {A} P l x :
  fold_left (fun b x => P x && b) l (P x) = @forallb A P (x :: l).
Proof.
  cbn. rewrite <- fold_left_rev_right. rewrite <- forallb_rev.
  induction (List.rev l); cbn.
  - now rewrite andb_true_r.
  - rewrite IHl0. rewrite !andb_assoc.
    f_equal. now rewrite andb_comm.
Qed.

Lemma nth_nth_error {A} n l (d : A) :
  nth n l d = match nth_error l n with
              | Some x => x
              | None => d
              end.
Proof.
  symmetry. apply nth_default_eq.
Qed.

Lemma nth_nth_error' {A} {i} {l : list A} {d v} :
  nth i l d = v ->
  (nth_error l i = Some v) +
  (nth_error l i = None /\ v = d).
Proof.
  move: i v. elim: l => [|hd tl IH] //.
  - case => /= //; now right.
  - case => /= // _ <-. now left.
Qed.

Lemma firstn_add {A} x y (args : list A) : firstn (x + y) args = firstn x args ++ firstn y (skipn x args).
Proof.
  induction x in y, args |- *. simpl. reflexivity.
  simpl. destruct args; simpl.
  now rewrite firstn_nil.
  rewrite IHx. now rewrite app_comm_cons.
Qed.

Lemma firstn_app_left_rem (A : Type) (n : nat) (l1 l2 : list A) k :
  k = #|l1| + n ->
  firstn k (l1 ++ l2) = l1 ++ firstn n l2.
Proof. intros ->; apply firstn_app_2. Qed.

Lemma firstn_app_left {A} n (l l' : list A) :
  n = #|l| ->
  firstn n (l ++ l') = l.
Proof.
  intros ->.
  rewrite firstn_app firstn_all Nat.sub_diag firstn_0 // app_nil_r //.
Qed.

Lemma skipn_all_app_eq {A} n (l l' : list A) : n = #|l| -> skipn n (l ++ l') = l'.
Proof.
  move->. apply skipn_all_app.
Qed.

Lemma rev_case {A} (P : list A -> Type) :
  P nil -> (forall l x, P (l ++ [x])) -> forall l, P l.
Proof.
  intros; now apply rev_ind.
Qed.

Lemma firstn_length_le_inv {A} n (l : list A) : #|firstn n l| = n -> n <= #|l|.
Proof.
  induction l in n |- *; simpl; auto with arith;
  destruct n; simpl; auto with arith. discriminate.
Qed.

Fixpoint map2i_rec {A B C} (f : nat -> A -> B -> C) i (l : list A) (l' : list B) : list C :=
  match l, l' with
  | hd :: tl, hd' :: tl' => f i hd hd' :: map2i_rec f (S i) tl tl'
  | _, _ => []
  end.
Definition map2i {A B C} (f : nat -> A -> B -> C) := map2i_rec f 0.

Lemma mapi_map2 {A B C D} (f : nat -> A -> B) (g : C -> D -> A) l l' :
  mapi f (map2 g l l') = map2i (fun i x y => f i (g x y)) l l'.
Proof.
  unfold mapi, map2i. generalize 0.
  induction l in l' |- *; intros; destruct l'; simpl; auto. f_equal.
  apply IHl.
Qed.

Lemma map2_mapi {A A' B B' C} (f : nat -> A -> B) (f' : nat-> A' -> B') (g : B -> B' -> C) l l' :
  map2 g (mapi f l) (mapi f' l') = map2i (fun i x y => g (f i x) (f' i y)) l l'.
Proof.
  unfold mapi, map2i. generalize 0.
  induction l in l' |- *; intros n; destruct l'; simpl; auto. f_equal.
  apply IHl.
Qed.

Lemma map2i_ext {A B C} (f g : nat -> A -> B -> C) l l' :
  (forall i x y, f i x y = g i x y) -> map2i f l l' = map2i g l l'.
Proof.
  intros Hfg.
  unfold map2i.
  generalize 0.
  induction l in l' |- *; destruct l'; simpl; auto.
  intros. f_equal; eauto.
Qed.

Lemma app_inj_length_r {A} (l l' r r' : list A) :
  app l r = app l' r' -> #|r| = #|r'| -> l = l' /\ r = r'.
Proof.
  induction r in l, l', r' |- *. destruct r'; intros; simpl in *; intuition auto; try discriminate.
  now rewrite !app_nil_r in H.
  intros. destruct r'; try discriminate.
  simpl in H.
  change (l ++ a :: r) with (l ++ [a] ++ r) in H.
  change (l' ++ a0 :: r') with (l' ++ [a0] ++ r') in H.
  rewrite !app_assoc in H. destruct (IHr _ _ _ H). now injection H0.
  subst. now apply app_inj_tail in H1 as [-> ->].
Qed.

Lemma app_inj_length_l {A} (l l' r r' : list A) :
  app l r = app l' r' -> #|l| = #|l'| -> l = l' /\ r = r'.
Proof.
  induction l in r, r', l' |- *. destruct l'; intros; simpl in *; intuition auto; try discriminate.
  intros. destruct l'; try discriminate. simpl in *. injection H as [= -> ?].
  specialize (IHl _ _ _ H).
  destruct IHl; intuition congruence.
Qed.

Equations map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B :=
map_In nil _ := nil;
map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  remember (fun (x : A) (_ : In x l) => f x) as g.
  funelim (map_In l g) => //; simpl; rewrite (H f0); trivial.
Qed.

Lemma rev_repeat {A : Type} (n : nat) (a : A) :
  List.rev (repeat a n) = repeat a n.
Proof.
  induction n.
  - reflexivity.
  - replace (S n) with (n + 1) at 2 by lia.
    cbn [repeat]. cbn. rewrite  IHn.
    now rewrite repeat_app.
Qed.


From MetaCoq.Utils Require Import ReflectEq.

Section SplitPrefix.
  Context {A : Type} `{ReflectEq A}.

  Equations split_prefix (l1 l2 : list A) : list A * list A * list A :=
  | nil, l2 => (nil, nil, l2)
  | l1 , nil => (nil, l1, nil)
  | a1 :: l1, a2 :: l2 with a1 == a2 => {
    | true with split_prefix l1 l2 => {
      | (prefix, l1', l2') => (a1 :: prefix, l1', l2')
      }
    | false => (nil, a1 :: l1, a2 :: l2)
    }.

  Lemma split_prefix_is_prefix l1 l2 :
    let '(prefix, l1', l2') := split_prefix l1 l2 in
    (l1 = prefix ++ l1') /\ (l2 = prefix ++ l2').
  Proof using Type.
    funelim (split_prefix l1 l2).
    1,2: simp split_prefix; now split.
    1,2: rewrite -Heqcall; split; try easy.
    1,2: rewrite Heq in Hind; destruct Hind.
    1: now subst.
    now rewrite (eqb_eq _ _ Heq0); subst.
  Qed.

  Definition is_prefix (l1 l2 : list A) := exists l', l2 = l1 ++ l'.

  Lemma nil_prefix l : is_prefix nil l.
  Proof using Type. now exists l. Qed.

  Lemma cons_prefix x l1 l2 : is_prefix l1 l2 -> is_prefix (x :: l1) (x :: l2).
  Proof using Type. move=> [l ->]; now exists l. Qed.

  Lemma is_prefix_nil l : is_prefix l nil -> l = nil.
  Proof using Type. move=> [?]; case l=> //. Qed.

  Lemma is_prefix_cons l x xs : is_prefix l (x :: xs) ->
                           l = nil \/ (exists l', l = x :: l' /\ is_prefix l' xs).
  Proof using Type.
    case: l x xs=> [|y ys ??[tl [= -> ->]]]; [now left| right].
    exists ys; split=> //; now exists tl.
  Qed.

  Lemma is_prefix_cons_inv x xs y ys :
    is_prefix (x :: xs) (y :: ys) -> x = y /\ is_prefix xs ys.
  Proof using Type.
    move=> [tl [= -> ->]]; split=> //; now exists tl.
  Qed.

  Local Notation "'Simp'" := ltac:(simp split_prefix) (only parsing) : ssripat_scope.

  Lemma split_prefix_maximal l1 l2 l :
    is_prefix l l1 -> is_prefix l l2 ->
    is_prefix l (fst (fst (split_prefix l1 l2))).
  Proof using Type.
    funelim (split_prefix l1 l2).
    - move=> /is_prefix_nil -> _; apply nil_prefix.
    - move=> _ /is_prefix_nil ->; apply nil_prefix.
    - move=> /is_prefix_cons [-> ?|]; first apply nil_prefix.
      move=> [? [-> ?]] /is_prefix_cons_inv [eqa ?].
      rewrite eqa eqb_refl in Heq; discriminate.
    - move=> /is_prefix_cons [-> ?|]; first apply nil_prefix.
      move=> [? [-> pr1]] /is_prefix_cons_inv [eqa pr2].
      rewrite -Heqcall; apply cons_prefix.
      move: Heqcall (Hind _ pr1 pr2)=> /Simp.
      rewrite eqa eqb_refl=> /Simp.
      move: (split_prefix l1 l2)=> -[[??]?] /Simp [= ->] //.
  Qed.

End SplitPrefix.

Section SplitSuffix.
  Context {A : Type} `{ReflectEq A}.

  Definition split_suffix (l1 l2 : list A) : list A * list A * list A :=
    let '(suffix, l1, l2) := split_prefix (rev l1) (rev l2) in
    (rev l1, rev l2, rev suffix).

  Lemma split_suffix_is_suffix l1 l2 :
    let '(l1', l2', suffix) := split_suffix l1 l2 in
    (l1 = l1' ++ suffix) /\ (l2 = l2' ++ suffix).
  Proof using Type.
    unfold split_suffix.
    pose proof (y := split_prefix_is_prefix (rev l1) (rev l2)).
    revert y.
    case: (split_prefix _ _)=> [[??] ?] [/(f_equal rev) + /(f_equal rev)].
    rewrite 2!rev_invol 2!rev_app //.
  Qed.

  Definition is_suffix (l1 l2 : list A) := exists l', l2 = l' ++ l1.

  Lemma is_suffix_is_prefix_rev l1 l2 :
    is_suffix l1 l2 -> is_prefix (rev l1) (rev l2).
  Proof using Type. move=> [l] /(f_equal rev) ->; exists (rev l); apply: rev_app. Qed.

  Lemma is_prefix_rev_is_suffix l1 l2 :
    is_prefix (rev l1) (rev l2) -> is_suffix l1 l2.
  Proof using Type.
    move=> [l] /(f_equal rev); rewrite rev_app 2! rev_invol.
    move=> ->; by exists (rev l).
  Qed.

  Lemma split_suffix_maximal l1 l2 l :
    is_suffix l l1 -> is_suffix l l2 ->
    is_suffix l (snd (split_suffix l1 l2)).
  Proof using Type.
    move=> /is_suffix_is_prefix_rev ll1 /is_suffix_is_prefix_rev ll2.
    apply: is_prefix_rev_is_suffix.
    pose proof (z := split_prefix_maximal (rev l1) (rev l2) (rev l) ll1 ll2).
    move: z; unfold split_suffix.
    case: (split_prefix _ _)=> [[??]?] /=; rewrite rev_invol //.
  Qed.
End SplitSuffix.

Section AllInP.
  Context {A : Type}.

  Equations forallb_InP (l : list A) (H : forall x : A, In x l -> bool) : bool :=
  | nil, _ := true ;
  | (cons x xs), H := (H x _) && (forallb_InP xs (fun x inx => H x _)).
End AllInP.

Lemma forallb_InP_spec {A} (f : A -> bool) (l : list A) :
  forallb_InP l (fun x _ => f x) = List.forallb f l.
Proof.
  remember (fun x _ => f x) as g.
  funelim (forallb_InP l g) => //; simpl. f_equal.
  now rewrite (H0 f).
Qed.

Section MapInP.
  Context {A B : Type}.

  Equations map_InP (l : list A) (f : forall x : A, In x l -> B) : list B :=
  map_InP nil _ := nil;
  map_InP (cons x xs) f := cons (f x _) (map_InP xs (fun x inx => f x _)).
End MapInP.

Lemma map_InP_spec {A B : Type} (f : A -> B) (l : list A) :
  map_InP l (fun (x : A) _ => f x) = List.map f l.
Proof.
  remember (fun (x : A) _ => f x) as g.
  funelim (map_InP l g) => //; simpl. f_equal. cbn in H.
  now rewrite (H f0).
Qed.

Lemma In_size {A B} {x : A} {l : list A} (proj : A -> B) (size : B -> nat) :
  In x l -> size (proj x) < S (list_size (size ∘ proj) l).
Proof.
  induction l; cbn => //.
  intros [->|hin]. lia. specialize (IHl hin); lia.
Qed.

Lemma app_tip_nil {A} (l : list A) (x : A) : (l ++ [x])%list <> [].
Proof.
  destruct l; cbn; congruence.
Qed.

Definition remove_last {A} (args : list A) :=
  List.firstn (#|args| - 1) args.

Lemma remove_last_app {A} (l : list A) x :
  remove_last (l ++ [x]) = l.
Proof.
  unfold remove_last. cbn. len.
  replace (#|l| + 1 -1) with #|l| by lia.
  rewrite firstn_app Nat.sub_diag /= firstn_all app_nil_r //.
Qed.

Lemma remove_last_last {A} (l : list A) (a : A) : l <> [] ->
  l = (remove_last l ++ [last l a])%list.
Proof.
  induction l using rev_ind.
  congruence.
  intros. rewrite remove_last_app last_last //.
Qed.

Lemma forallb_repeat {A} {p : A -> bool} {a : A} {n} :
  p a ->
  forallb p (repeat a n).
Proof.
  intros pa.
  induction n; cbn; auto.
  now rewrite pa IHn.
Qed.

Lemma map_repeat {A B} (f : A -> B) a n :
  map f (repeat a n) = repeat (f a) n.
Proof.
  induction n; cbn; congruence.
Qed.

Lemma map2_length :
  forall {A B C : Type} (f : A -> B -> C) (l : list A) (l' : list B), #| map2 f l l'| = min #|l| #|l'|.
Proof.
  intros. induction l in l' |- *; cbn.
  - reflexivity.
  - destruct l'; cbn in *. lia. rewrite IHl. lia.
Qed.

Lemma map2_map_l {A B C D} (f : A -> B) (g : B -> C -> D) (l : list A) (l' : list C) :
  map2 g (List.map f l) l' =
  map2 (fun x y => g (f x) y) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  * cbn. now f_equal.
Qed.

Lemma map2_diag {A B} (f : A -> A -> B) (l : list A) :
  map2 f l l = map (fun x => f x x) l.
Proof.
  elim: l=> [//|? ? /= -> //].
Qed.


Lemma map2_snd {A B} (l : list A) (l' : list B) :
  map2 (fun x y => x) l l' = firstn #|l'| l.
Proof.
  elim: l l'=> [|x xs ih] [|y ys] //=; congruence.
Qed.

Lemma length_nil {A} (l : list A) : #|l| = 0 -> l = [].
Proof. destruct l => //. Qed.

Inductive snoc_view {A : Type} : list A -> Type :=
| snoc_view_nil : snoc_view nil
| snoc_view_snoc l x : snoc_view (l ++ [x]).

Lemma snocP {A} (l : list A) : snoc_view l.
Proof.
  elim: l=> [|a l]; first constructor.
  case=> [|l' z];
  [exact: (snoc_view_snoc nil) | exact: (snoc_view_snoc (a :: l'))].
Qed.

Lemma hd_error_skipn_iff_In {A v ls}
  : (exists n, hd_error (@skipn A n ls) = Some v) <-> In v ls.
Proof.
  move: ls; elim => //=.
  1: setoid_rewrite skipn_nil; cbn; firstorder congruence.
  move => ?? <-.
  split.
  { move => [[|?]]; rewrite ?skipn_0 ?skipn_S => //=.
    1: move => [->].
    all: eauto. }
  { move => [->|[n H]]; [ exists 0 | exists (S n) ];
            rewrite ?skipn_0 ?skipn_S => //=. }
Qed.

Lemma cons_eq_iff A x xs y ys
  : x :: xs = y :: ys <-> ((x = y :> A) /\ xs = ys).
Proof. split; intuition congruence. Qed.

Lemma nth_error_Some_ext_iff A (l l' : list A)
  : (#|l| = #|l'| /\ (forall n d d', nth_error l n = Some d -> nth_error l' n = Some d' -> d = d')) <-> l = l'.
Proof.
  move: l'; induction l as [|?? IH], l' as [|? l'];
    try specialize (IH l'); cbn; try (rewrite cons_eq_iff -IH; clear IH).
  all: repeat first [ done
                    | match goal with
                      | [ H : _ /\ _ |- _ ] => destruct H
                      | [ H : forall n d d', nth_error (_ :: _) n = Some d -> _ |- _ ]
                        => pose proof (H 0); specialize (fun n => H (S n))
                      | [ H : nth_error (_ :: _) ?n = _ |- _ ] => is_var n; destruct n
                      end
                    | exactly_once constructor
                    | progress rewrite -> ?nth_error_nil in *
                    | progress intros
                    | progress cbn in *
                    | now eauto ].
Qed.

Lemma nth_error_ext_iff A (l l' : list A)
  : (forall n, nth_error l n = nth_error l' n) <-> l = l'.
Proof.
  move: l'; induction l as [|?? IH], l' as [|? l'];
    try specialize (IH l'); cbn; try (rewrite cons_eq_iff -IH; clear IH).
  all: repeat first [ done
                    | progress cbn in *
                    | congruence
                    | progress subst
                    | match goal with
                      | [ H : _ /\ _ |- _ ] => destruct H
                      | [ H : forall n, nth_error (_ :: _) n = _ |- _ ]
                        => pose proof (H 0); specialize (fun n => H (S n))
                      | [ H : forall n, _ = nth_error (_ :: _) n |- _ ]
                        => pose proof (H 0); specialize (fun n => H (S n))
                      | [ H : forall n, nth_error nil n = _ |- _ ]
                        => setoid_rewrite nth_error_nil in H
                      | [ |- context[nth_error (_ :: _) ?n] ] => is_var n; destruct n
                      end
                    | exactly_once constructor
                    | progress rewrite -> ?nth_error_nil in *
                    | progress intros ].
Qed.

Lemma In_iff_nth_error A x l : @In A x l <-> exists n, nth_error l n = Some x.
Proof.
  split; try case; intros *; first [ apply nth_error_In | apply In_nth_error ].
Qed.

Lemma List_rev_alt {A ls} : List.rev ls = @rev A ls.
Proof. rewrite rev_alt; reflexivity. Qed.

Lemma nth_error_rev_full {A ls i}
  : nth_error (@rev A ls) i = if i <? #|ls| then nth_error ls (#|ls| - S i) else None.
Proof.
  case: Nat.ltb_spec0 => ?.
  { rewrite -List_rev_alt nth_error_rev_inv //. }
  { rewrite nth_error_None rev_length; lia. }
Qed.

Lemma nth_error_List_rev_full {A ls i}
  : nth_error (@List.rev A ls) i = if i <? #|ls| then nth_error ls (#|ls| - S i) else None.
Proof.
  case: Nat.ltb_spec0 => ?.
  { rewrite nth_error_rev_inv //. }
  { rewrite nth_error_None List.rev_length; lia. }
Qed.

Lemma nth_error_rev_map {A B f ls i}
  : nth_error (@rev_map A B f ls) i = if i <? #|ls| then option_map f (nth_error ls (#|ls| - S i)) else None.
Proof.
  rewrite rev_map_spec nth_error_List_rev_full map_length nth_error_map //.
Qed.

Lemma nth_error_rev_Some {A ls i v}
  : nth_error (@rev A ls) i = Some v -> nth_error ls (#|ls| - S i) = Some v.
Proof.
  rewrite nth_error_rev_full; case: nth_error; case: Nat.ltb_spec0 => //=.
Qed.

Lemma nth_error_rev_Some_inv {A ls i v}
  : nth_error ls i = Some v -> nth_error (@rev A ls) (#|ls| - S i) = Some v.
Proof.
  rewrite nth_error_rev_full; case: Nat.ltb_spec0;
    try now case: ls => //=; rewrite ?nth_error_nil.
  intros H0 H1.
  assert (H : i < #|ls|) by now eapply nth_error_Some_length.
  now replace (#|ls| - S (#|ls| - S i)) with i by lia.
Qed.

Lemma nth_error_List_rev_Some {A ls i v}
  : nth_error (@List.rev A ls) i = Some v -> nth_error ls (#|ls| - S i) = Some v.
Proof.
  rewrite nth_error_List_rev_full; case: nth_error; case: Nat.ltb_spec0 => //=.
Qed.

Lemma nth_error_List_rev_Some_inv {A ls i v}
  : nth_error ls i = Some v -> nth_error (@List.rev A ls) (#|ls| - S i) = Some v.
Proof.
  rewrite nth_error_List_rev_full; case: Nat.ltb_spec0;
    try now case: ls => //=; rewrite ?nth_error_nil.
  intros H0 H1.
  assert (H : i < #|ls|) by now eapply nth_error_Some_length.
  now replace (#|ls| - S (#|ls| - S i)) with i by lia.
Qed.

Lemma nth_error_rev_map_Some {A B f ls i v}
  : nth_error (@rev_map A B f ls) i = Some v -> { v' : _ | nth_error ls (#|ls| - S i) = Some v' /\ f v' = v }.
Proof.
  rewrite nth_error_rev_map; case: nth_error; case: Nat.ltb_spec0 => //=.
  intros ? *; inversion 1; subst; eauto.
Qed.

Lemma nth_error_rev_map_Some_inv {A B f ls i v}
  : nth_error ls i = Some v -> nth_error (@rev_map A B f ls) (#|ls| - S i) = Some (f v).
Proof.
  rewrite nth_error_rev_map; case: Nat.ltb_spec0;
    try now case: ls => //=; rewrite ?nth_error_nil.
  intros H0 H1.
  assert (H : i < #|ls|) by now eapply nth_error_Some_length.
  replace (#|ls| - S (#|ls| - S i)) with i by lia.
  now rewrite H1.
Qed.

Lemma mapi_rec_nth_error {A B f n l d k}
  : nth_error l n = Some d -> nth_error (@mapi_rec A B f l k) n = Some (f (n + k) d).
Proof.
  move: l n k.
  elim => [|? l IH]; case => [|?] k.
  all: rewrite ?nth_error_nil => //=; try congruence.
  move => ?; rewrite IH => //.
  do 2 f_equal; lia.
Qed.

Lemma mapi_nth_error {A B f n l d}
  : nth_error l n = Some d -> nth_error (@mapi A B f l) n = Some (f n d).
Proof.
  rewrite /mapi => ?; erewrite mapi_rec_nth_error; tea; do 2 f_equal; lia.
Qed.

Lemma nth_error_cons_S {A x xs n}
  : @nth_error A (x :: xs) (S n) = nth_error xs n.
Proof. reflexivity. Qed.

Lemma nth_error_cons_O {A x xs}
  : @nth_error A (x :: xs) 0 = Some x.
Proof. reflexivity. Qed.
