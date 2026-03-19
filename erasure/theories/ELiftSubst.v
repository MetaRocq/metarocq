(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction.
From Stdlib Require Import ssreflect.

(** * Lifting and substitution for the AST

  Along with standard commutation lemmas.
  Definition of [closedn] (boolean) predicate for checking if
  a term is closed. *)

Local Open Scope erasure.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => if Nat.leb k i then tRel (n + i) else tRel i
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na M => tLambda na (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tLetIn na b b' => tLetIn na (lift n k b) (lift n (S k) b')
  | tCase ind c brs =>
    let brs' := List.map (fun br =>
      (br.1, lift n (#|br.1| + k) br.2)) brs in
    tCase ind (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k')) mfix in
    tCoFix mfix' idx
  | tBox => t
  | tVar _ => t
  | tConst _ => t
  | tConstruct ind i args => tConstruct ind i (map (lift n k) args)
  | tPrim p => tPrim (map_prim (lift n k) p)
  | tLazy t => tLazy (lift n k t)
  | tForce t => tForce (lift n k t)
  end.

Abbreviation lift0 n := (lift n 0).
Definition up := lift 1 0.

(** Parallel substitution: it assumes that all terms in the substitution live in the
    same context *)

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na M => tLambda na (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tLetIn na b b' => tLetIn na (subst s k b) (subst s (S k) b')
  | tCase ind c brs =>
    let brs' := List.map (fun br => (br.1, subst s (#|br.1| + k) br.2)) brs in
    tCase ind (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k')) mfix in
    tCoFix mfix' idx
  | tConstruct ind i args => tConstruct ind i (map (subst s k) args)
  | tPrim p => tPrim (map_prim (subst s k) p)
  | tLazy t => tLazy (subst s k t)
  | tForce t => tForce (subst s k t)
  | tBox => tBox
  | tVar n => tVar n
  | tConst c => tConst c
  end.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Abbreviation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Abbreviation subst10 t := (subst1 t 0).
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity) : erasure.

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ M => closedn (S k) M
  | tApp u v => closedn k u && closedn k v
  | tLetIn na b b' => closedn k b && closedn (S k) b'
  | tCase ind c brs =>
    let brs' := List.forallb (fun br => closedn (#|br.1| + k) br.2) brs in
    closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k')) mfix
  | tConstruct ind i args => forallb (closedn k) args
  | tPrim p => test_prim (closedn k) p
  | tLazy t => closedn k t
  | tForce t => closedn k t
  | _ => true
  end.

Abbreviation closed t := (closedn 0 t).

Abbreviation subst_rec N M k := (subst N k M) (only parsing).

From Stdlib Require Import PeanoNat.
Import Nat.

Lemma lift_rel_ge :
  forall k n p, p <= n -> lift k p (tRel n) = tRel (k + n).
Proof.
  intros; simpl in |- *.
  now elim (leb_spec p n).
Qed.

Lemma lift_rel_lt : forall k n p, p > n -> lift k p (tRel n) = tRel n.
Proof.
  intros; simpl in |- *.
  now elim (leb_spec p n).
Qed.

Lemma lift_rel_alt : forall n k i, lift n k (tRel i) = tRel (if Nat.leb k i then n + i else i).
Proof.
  intros; simpl. now destruct leb.
Qed.

Lemma subst_rel_lt : forall u n k, k > n -> subst u k (tRel n) = tRel n.
Proof.
  simpl in |- *; intros.
  elim (leb_spec k n); intro Hcomp; easy.
Qed.

Lemma subst_rel_gt :
  forall u n k, n >= k + length u -> subst u k (tRel n) = tRel (n - length u).
Proof.
  simpl in |- *; intros.
  elim (leb_spec k n). intros. destruct nth_error eqn:Heq.
  assert (n - k < length u) by (apply nth_error_Some; congruence). lia. reflexivity.
  lia.
Qed.

Unset SsrRewrite.

Lemma subst_rel_eq :
  forall (u : list term) n i t p,
    List.nth_error u i = Some t -> p = n + i ->
    subst u n (tRel p) = lift0 n t.
Proof.
  intros; simpl in |- *. subst p.
  elim (leb_spec n (n + i)). intros. assert (n + i - n = i) by lia. rewrite -> H1, H.
  reflexivity. intros. lia.
Qed.

#[global]
Hint Extern 0 (_ = _) => progress f_equal : all.
#[global]
Hint Unfold on_snd snd : all.

#[global] Hint Extern 10 =>
  match goal with
  | [ H : _ × _ |- _ ] => destruct H
  end : all.

#[global] Hint Extern 10 =>
  progress cbn beta match fix cofix iota zeta in * : all.

Lemma on_snd_eq_id_spec {A B} (f : B -> B) (x : A * B) :
  f (snd x) = snd x <->
  on_snd f x = x.
Proof.
  destruct x; simpl; unfold on_snd; simpl. split; congruence.
Qed.
#[global]
Hint Resolve -> on_snd_eq_id_spec : all.

Lemma map_def_eq_spec (f g : term -> term) (x : def term) :
  f (dbody x) = g (dbody x) ->
  map_def f x = map_def g x.
Proof.
  intros. unfold map_def; f_equal; auto.
Qed.
#[global]
Hint Resolve map_def_eq_spec : all.

Lemma map_def_id_spec (f : term -> term) (x : def term) :
  f (dbody x) = (dbody x) ->
  map_def f x = x.
Proof.
  intros. rewrite (map_def_eq_spec f id); auto. destruct x; auto.
Qed.
#[global]
Hint Resolve map_def_id_spec : all.

Lemma compose_map_def (f g : term -> term) :
  (map_def f) ∘ (map_def g) = map_def (f ∘ g).
Proof. reflexivity. Qed.

#[global]
Hint Extern 10 (_ < _)%nat => lia : all.
#[global]
Hint Extern 10 (_ <= _)%nat => lia : all.
#[global]
Hint Extern 10 (@eq nat _ _) => lia : all.

Ltac change_Sk :=
  repeat match goal with
    |- context [S (?x + ?y)] => progress change (S (x + y)) with (S x + y)
  end.

Ltac primProp :=
  repeat match goal with
    | [ H : (forall x, InPrim x _ -> _) |- _ ] => eapply InPrim_primProp in H
    | [ H : is_true (test_prim _ _) |- _ ] => eapply test_prim_impl_primProp in H
    | [ H : test_prim _ _ = true |- _ ] => eapply test_prim_impl_primProp in H
    | [ |- is_true (test_prim _ _) ] => eapply primProp_impl_test_prim
    | [ |- test_prim _ _ = true ] => eapply primProp_impl_test_prim
    | [ H : primProp ?P ?p, H' : primProp ?Q ?p |- _ ] =>
      let H'' := fresh in pose proof (H'' := primProp_conj H H'); clear H H'
    end.

Tactic Notation "solve_all_k" int(k) :=
  unfold tFixProp in *;
  primProp; autorewrite with map;
  repeat toAll; try All_map; try close_Forall;
  change_Sk; auto with all;
  intuition eauto k with all.

Ltac solve_all := solve_all_k 5.

Ltac nth_leb_simpl :=
  match goal with
    |- context [leb ?k ?n] => elim (leb_spec_Set k n); try lia; intros; simpl
  | |- context [nth_error ?l ?n] => elim (nth_error_spec l n); rewrite -> ?length_app, ?length_map;
                                    try lia; intros; simpl
  | H : context[nth_error (?l ++ ?l') ?n] |- _ =>
    (rewrite -> (nth_error_app_ge l l' n) in H by lia) ||
    (rewrite -> (nth_error_app_lt l l' n) in H by lia)
  | H : nth_error ?l ?n = Some _, H' : nth_error ?l ?n' = Some _ |- _ =>
    replace n' with n in H' by lia; rewrite -> H in H'; injection H'; intros; subst
  | _ => lia || congruence || solve [repeat (f_equal; try lia)]
  end.

Lemma lift0_id : forall M k, lift 0 k M = M.
Proof.
  intros M.
  elim M using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try (f_equal; auto; solve_all).

  - now elim (leb k n).
Qed.

Lemma lift0_p : forall M, lift0 0 M = M.
  intros; unfold lift in |- *.
  apply lift0_id; easy.
Qed.

#[global]
Hint Resolve -> on_snd_eq_spec : all.

Lemma simpl_lift :
  forall M n k p i,
    i <= k + n ->
    k <= i -> lift p i (lift n k M) = lift (p + n) k M.
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
      try (rewrite -> H, ?H0, ?H1; auto); try (f_equal; auto; solve_all).

  - elim (leb_spec k n); intros.
    now rewrite lift_rel_ge.
    now rewrite lift_rel_lt.
Qed.

Lemma simpl_lift0 : forall M n, lift0 (S n) M = lift0 1 (lift0 n M).
  now intros; rewrite simpl_lift.
Qed.

Lemma permute_lift :
  forall M n k p i,
    i <= k ->
    lift p i (lift n k M) = lift n (k + p) (lift p i M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all]; repeat nth_leb_simpl.
  f_equal; auto. solve_all.
  f_equal. rewrite Nat.add_assoc.
  rewrite H1; auto. lia.
Qed.

Lemma permute_lift0 :
  forall M k, lift0 1 (lift 1 k M) = lift 1 (S k) (lift0 1 M).
  intros.
  change (lift 1 0 (lift 1 k M) = lift 1 (1 + k) (lift 1 0 M))
    in |- *.
  rewrite permute_lift; easy.
Qed.

Lemma lift_isApp n k t : ~ isApp t = true -> ~ isApp (lift n k t) = true.
Proof.
  induction t; auto.
  intros.
  simpl. destruct leb; auto.
Qed.

Lemma map_non_nil {A B} (f : A -> B) l : l <> nil -> map f l <> nil.
Proof.
  intros. intro.
  destruct l; try discriminate.
  contradiction.
Qed.

Lemma isLambda_lift n k (bod : term) :
  isLambda bod = true -> isLambda (lift n k bod) = true.
Proof. destruct bod; simpl; try congruence. Qed.

Lemma isBox_lift n k (bod : term) :
  isBox bod = isBox (lift n k bod).
Proof. destruct bod; simpl; try congruence. destruct Nat.leb => //. Qed.

#[global]
Hint Resolve lift_isApp map_non_nil isLambda_lift : all.


Lemma simpl_subst_rec :
  forall M N n p k,
    p <= n + k ->
    k <= p -> subst N p (lift (List.length N + n) k M) = lift n k M.
Proof.
  intros M. induction M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
      try solve [f_equal; auto; solve_all]; repeat nth_leb_simpl.
Qed.

Lemma simpl_subst :
  forall N M n p, p <= n -> subst N p (lift0 (length N + n) M) = lift0 n M.
Proof. intros. rewrite simpl_subst_rec; auto. now rewrite Nat.add_0_r. lia. Qed.

Lemma lift_mkApps n k t l : lift n k (mkApps t l) = mkApps (lift n k t) (map (lift n k) l).
Proof.
  revert n k t; induction l; intros n k t. auto.
  simpl. rewrite (IHl n k (tApp t a)). reflexivity.
Qed.

Lemma commut_lift_subst_rec :
  forall M N n p k,
    k <= p ->
    lift n k (subst N p M) = subst N (p + n) (lift n k M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; try easy;
      rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all].

  - repeat nth_leb_simpl.
    rewrite -> simpl_lift by easy. f_equal; lia.
  - f_equal; auto; solve_all.
    rewrite Nat.add_assoc. f_equal. apply H1. lia.
Qed.

Lemma commut_lift_subst :
  forall M N k, subst N (S k) (lift0 1 M) = lift0 1 (subst N k M).
  now intros; rewrite commut_lift_subst_rec.
Qed.

Lemma distr_lift_subst_rec :
  forall M N n p k,
    lift n (p + k) (subst N p M) =
    subst (List.map (lift n k) N) p (lift n (p + length N + k) M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; match goal with
              |- context [tRel _] => idtac
            | |- _ => cbn -[plus]
            end; try easy;
      rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all].

  - unfold subst at 1. unfold lift at 4.
    repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    revert e0. intros [= <-].
    now rewrite (permute_lift x n0 k p 0).
  - f_equal; auto; solve_all.
    f_equal. rewrite !Nat.add_assoc.
    rewrite H0. f_equal.
Qed.

Lemma distr_lift_subst :
  forall M N n k,
    lift n k (subst0 N M) = subst0 (map (lift n k) N) (lift n (length N + k) M).
Proof.
  intros. pattern k at 1 3 in |- *.
  replace k with (0 + k); try easy.
  apply distr_lift_subst_rec.
Qed.

Lemma distr_lift_subst10 :
  forall M N n k,
    lift n k (subst10 N M) = subst10 (lift n k N) (lift n (S k) M).
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); try easy.
  apply distr_lift_subst_rec.
Qed.

Lemma subst_mkApps u k t l :
  subst u k (mkApps t l) = mkApps (subst u k t) (map (subst u k) l).
Proof.
  revert u k t; induction l; intros u k t; auto.
  intros. simpl mkApps at 1. simpl subst at 1 2.
  now rewrite IHl.
Qed.

Lemma subst1_mkApps u k t l : subst1 u k (mkApps t l) = mkApps (subst1 u k t) (map (subst1 u k) l).
Proof.
  apply subst_mkApps.
Qed.

Lemma distr_subst_rec :
  forall M N (P : list term) n p,
    subst P (p + n) (subst N p M) =
    subst (map (subst P n) N) p (subst P (p + length N + n) M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; match goal with
              |- context [tRel _] => idtac
            | |- _ => simpl
            end; try easy;
      rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all].

  - unfold subst at 2.
    repeat nth_leb_simpl.
    erewrite <- simpl_subst. f_equal. rewrite length_map. arith_congr. lia.
    rewrite nth_error_map in e0. rewrite e in e0.
    simpl in e0. injection e0 as <-.
    rewrite commut_lift_subst_rec. arith_congr. lia.
  - f_equal; auto; solve_all. f_equal.
    now rewrite -> !Nat.add_assoc, H0.
Qed.

Lemma distr_subst :
  forall P N M k,
    subst P k (subst0 N M) = subst0 (map (subst P k) N) (subst P (length N + k) M).
Proof.
  intros.
  pattern k at 1 3 in |- *.
  change k with (0 + k). hnf.
  apply distr_subst_rec.
Qed.

Lemma lift_closed n k t : closedn k t -> lift n k t = t.
Proof.
  revert k.
  elim t using term_forall_list_ind; intros; try easy;
    rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *; try solve [simpl lift; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.

  - rewrite lift_rel_lt; auto.
    revert H. elim (Nat.ltb_spec n0 k); intros; try easy.
Qed.

Lemma closed_upwards {k t} k' : closedn k t -> k' >= k -> closedn k' t.
Proof.
  revert k k'.
  elim t using term_forall_list_ind; intros; try lia;
    rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    simpl closed in *; unfold test_snd, test_def in *;
      try solve [(try f_equal; simpl; repeat (rtoProp; solve_all); eauto)].

  - elim (ltb_spec n k'); auto. intros.
    apply ltb_lt in H. lia.
Qed.

Lemma subst_empty k a : subst [] k a = a.
Proof.
  induction a in k |- * using term_forall_list_ind; simpl; try congruence;
    try solve [f_equal; eauto; solve_all].

  - elim (Nat.compare_spec k n); destruct (Nat.leb_spec k n); intros; try easy.
    subst. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. reflexivity.
    assert (n - k > 0) by lia.
    assert (exists n', n - k = S n'). exists (pred (n - k)). lia.
    destruct H2. rewrite H2. simpl. now rewrite Nat.sub_0_r.
Qed.

Lemma subst_closed n k t : closedn k t -> subst n k t = t.
Proof.
  revert k.
  elim t using term_forall_list_ind; intros; try easy;
    rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
  - cbn.
    revert H. elim (Nat.ltb_spec n0 k); intros; try easy.
    elim (Nat.leb_spec k n0); intros; try easy.
Qed.

(* Lemma lift_to_extended_list_k Γ k : forall k', *)
(*  to_extended_list_k Γ (k' + k) = map (lift0 k') (to_extended_list_k Γ k). *)
(* Proof. *)
(*   unfold to_extended_list_k. *)
(*   intros k'. rewrite !reln_alt_eq, !app_nil_r. *)
(*   induction Γ in k, k' |- *; simpl; auto. *)
(*   destruct a as [na [body|] ty]. *)
(*   now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k'). *)
(*   simpl. now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k'), map_app. *)
(* Qed. *)

Lemma simpl_subst_k (N : list term) (M : term) :
  forall k p, p = #|N| -> subst N k (lift p k M) = M.
Proof.
  intros. subst p. rewrite <- (Nat.add_0_r #|N|).
  rewrite -> simpl_subst_rec, lift0_id; auto.
Qed.

Lemma subst_app_decomp l l' k t :
  subst (l ++ l') k t = subst l' k (subst (List.map (lift0 (length l')) l) k t).
Proof.
  induction t in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
         eauto; solve_all).

  - repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0; intros <-.
    rewrite -> permute_lift by auto.
    rewrite <- (Nat.add_0_r #|l'|).
    rewrite -> simpl_subst_rec, lift0_id; auto with wf; try lia.
Qed.

Lemma subst_app_simpl l l' k t :
  subst (l ++ l') k t = subst l k (subst l' (k + length l) t).
Proof.
  induction t in k |- * using term_forall_list_ind; simpl; eauto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?map_prim_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc;
         eauto; solve_all; eauto).

  - repeat nth_leb_simpl.
    rewrite -> Nat.add_comm, simpl_subst; eauto.
  - f_equal. now rewrite -> H, Nat.add_assoc.
Qed.

Lemma isLambda_subst (s : list term) k (bod : term) :
  isLambda bod = true -> isLambda (subst s k bod) = true.
Proof.
  intros. destruct bod; try discriminate. reflexivity.
Qed.


Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert k.
  induction t in n, k' |- * using EInduction.term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    autorewrite with map;
    simpl closed in *; solve_all;
    unfold test_def, test_snd in *;
      try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.

  - elim (Nat.leb_spec k' n0); intros. simpl.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H. lia.
    simpl. elim (Nat.ltb_spec); auto. intros.
    apply Nat.ltb_lt in H. lia.
  - solve_all. rewrite Nat.add_assoc. eauto.
  - cbn. rewrite Nat.add_assoc. eauto.
  - cbn. rewrite Nat.add_assoc. eauto.
Qed.

Set SsrRewrite.

Lemma closedn_subst_eq s k k' t :
  forallb (closedn k) s ->
  closedn (k + k' + #|s|) t =
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. toAll. revert Hs.
  induction t in k' |- * using EInduction.term_forall_list_ind; intros;
    simpl in *;
    autorewrite with map => //;
    simpl closed in *; try change_Sk;
    unfold test_def in *; simpl in *.

  - elim (Nat.leb_spec k' n); intros. simpl.
    destruct nth_error eqn:Heq.
    -- rewrite closedn_lift.
       now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
       eapply nth_error_Some_length in Heq.
       eapply Nat.ltb_lt. lia.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. symmetry. apply Nat.ltb_lt. lia.
       apply nth_error_None in Heq. intros. symmetry. eapply Nat.ltb_nlt.
       intros H'. lia.
    -- simpl.
      elim: Nat.ltb_spec; symmetry. apply Nat.ltb_lt. lia.
      apply Nat.ltb_nlt. intro. lia.
  - eapply All_forallb_eq_forallb; tea; eauto.
  - specialize (IHt (S k')).
    rewrite <- Nat.add_succ_comm in IHt.
    rewrite IHt //.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2.
    rewrite IHt1 // IHt2 //.
  - solve_all.
  - eapply All_forallb_eq_forallb; eauto.
  - rewrite IHt //.
    f_equal. eapply All_forallb_eq_forallb; tea. cbn.
    intros. specialize (H (#|x.1| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k) in H.
    now rewrite !Nat.add_assoc.
  - solve_all.
  - eapply All_forallb_eq_forallb; tea. cbn.
    intros. specialize (H (#|m| + k')).
    now rewrite !Nat.add_assoc !(Nat.add_comm k) in H |- *.
  - eapply All_forallb_eq_forallb; tea. cbn.
    intros. specialize (H (#|m| + k')).
    now rewrite !Nat.add_assoc !(Nat.add_comm k) in H |- *.
  - solve_all.
  - solve_all.
  - solve_all.
Qed.

Lemma closedn_subst s k t :
  forallb (closedn k) s -> closedn (#|s| + k) t ->
  closedn k (subst0 s t).
Proof.
  intros.
  epose proof (closedn_subst_eq s k 0).
  rewrite Nat.add_0_r in H1.
  rewrite -H1 //. rewrite Nat.add_comm //.
Qed.
