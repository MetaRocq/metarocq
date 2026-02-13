(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction.
Import Nat.

(** * Commutation lemmas for the lifting and substitution operations.
  Definition of [closedn] (boolean) predicate for checking if
  a term is closed. *)

Derive Signature for Peano.le.

(** Assumptions contexts do not contain let-ins. *)

Inductive assumption_context : context -> Prop :=
| assumption_context_nil : assumption_context []
| assumption_context_vass na t Γ : assumption_context Γ -> assumption_context (vass na t :: Γ).

Derive Signature for assumption_context.

Create HintDb terms.

Ltac arith_congr := repeat (try lia; progress f_equal).

Ltac easy0 :=
  let rec use_hyp H :=
   (match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ * _ => exact H || destruct_hyp H
    | _ => try (solve [ inversion H ])
    end)
  with do_intro := (let H := fresh in
                    intro H; use_hyp H)
  with destruct_hyp H := (case H; clear H; do_intro; do_intro)
  in
  let rec use_hyps :=
   (match goal with
    | H:_ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ * _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ |- _ => solve [ inversion H ]
    | _ => idtac
    end)
  in
  let do_atom := (solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction | congruence]) in
  let rec do_ccl := (try do_atom; repeat (do_intro; try do_atom); try arith_congr; (solve [ split; do_ccl ])) in
  (solve [ do_atom | use_hyps; do_ccl ]) || fail "Cannot solve this goal".


#[global]
Hint Extern 10 (_ < _)%nat => lia : terms.
#[global]
Hint Extern 10 (_ <= _)%nat => lia : terms.
#[global]
Hint Extern 10 (@eq nat _ _) => lia : terms.

Ltac easy ::= easy0 || solve [intuition eauto 3 with core terms].

Notation subst_rec N M k := (subst N k M) (only parsing).

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

Lemma subst_rel_eq :
  forall (u : list term) n i t p,
    List.nth_error u i = Some t -> p = n + i ->
    subst u n (tRel p) = lift0 n t.
Proof.
  intros; simpl in |- *. subst p.
  elim (leb_spec n (n + i)). intros. assert (n + i - n = i) by lia. rewrite H1 H.
  reflexivity. intros. lia.
Qed.

Ltac nth_leb_simpl :=
  match goal with
    |- context [leb ?k ?n] => elim (leb_spec_Set k n); try lia; simpl
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
    try solve [(f_equal; auto; solve_all)].

  now elim (leb k n).
Qed.

Lemma map_lift0 l : map (lift0 0) l = l.
Proof. induction l; simpl; auto. now rewrite lift0_id. Qed.

Lemma lift0_p : forall M, lift0 0 M = M.
Proof. intro; apply lift0_id. Qed.

Lemma simpl_lift :
  forall M n k p i,
    i <= k + n ->
    k <= i -> lift p i (lift n k M) = lift (p + n) k M.
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; autorewrite with map;
      try (rewrite -> H, ?H0, ?H1; auto); try (f_equal; auto; solve_all).

  - elim (leb_spec k n); intros.
  + elim (leb_spec i (n0 + n)); intros; lia.
  + elim (leb_spec i n); intros; lia.
Qed.

Lemma simpl_lift0 : forall M n, lift0 (S n) M = lift0 1 (lift0 n M).
Proof. intros; now rewrite simpl_lift. Qed.

Lemma simpl_lift_ext n k p i :
  i <= k + n -> k <= i ->
  lift p i ∘ lift n k ≐1 lift (p + n) k.
Proof. intros ? ? ?; now apply simpl_lift. Qed.

#[global]
Hint Rewrite Nat.add_assoc : map.

Lemma permute_lift :
  forall M n k p i,
    i <= k ->
    lift p i (lift n k M) = lift n (k + p) (lift p i M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl;
      f_equal; try solve [solve_all]; repeat nth_leb_simpl.
Qed.

Lemma permute_lift0 :
  forall M k, lift0 1 (lift 1 k M) = lift 1 (S k) (lift0 1 M).
Proof.
  intros.
  change (lift 1 0 (lift 1 k M) = lift 1 (1 + k) (lift 1 0 M)).
  now rewrite permute_lift.
Qed.

Lemma lift_isApp n k t : ~ isApp t = true -> ~ isApp (lift n k t) = true.
Proof. induction t; auto. Qed.

Lemma isLambda_lift n k (bod : term) :
  isLambda bod = true -> isLambda (lift n k bod) = true.
Proof. now destruct bod. Qed.

#[global]
Hint Resolve lift_isApp map_nil isLambda_lift : all.

Lemma simpl_subst_rec :
  forall M N n p k,
    p <= n + k ->
    k <= p -> subst N p (lift (List.length N + n) k M) = lift n k M.
Proof.
  intros M. induction M using term_forall_list_ind;
    intros; simpl; autorewrite with map;
      try solve [f_equal; auto; solve_all]; repeat nth_leb_simpl.
Qed.

Lemma simpl_subst :
  forall N M n p, p <= n -> subst N p (lift0 (length N + n) M) = lift0 n M.
Proof.
  intros. rewrite simpl_subst_rec; auto.
  now rewrite Nat.add_0_r. lia.
Qed.

Lemma lift_mkApps n k t l :
  lift n k (mkApps t l) = mkApps (lift n k t) (map (lift n k) l).
Proof.
  revert n k t; induction l; intros n k t. auto.
  simpl. rewrite (IHl n k (tApp t a)). reflexivity.
Qed.

Lemma commut_lift_subst_rec M N n p k :
  k <= p -> lift n k (subst N p M) = subst N (p + n) (lift n k M).
Proof.
  revert N n p k; elim M using term_forall_list_ind; intros; cbnr;
    f_equal; auto; solve_all; rewrite ?Nat.add_succ_r -?Nat.add_assoc; eauto with all.

  - repeat nth_leb_simpl.
    rewrite -> simpl_lift by easy. f_equal; lia.
Qed.

Lemma commut_lift_subst M N k :
  subst N (S k) (lift0 1 M) = lift0 1 (subst N k M).
Proof.
  now intros; rewrite commut_lift_subst_rec.
Qed.

Lemma distr_lift_subst_rec M N n p k :
    lift n (p + k) (subst N p M) =
    subst (List.map (lift n k) N) p (lift n (p + length N + k) M).
Proof.
  revert N n p k; elim M using term_forall_list_ind; intros; cbnr;
    f_equal; auto; solve_all.

  - repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    invs e0. now rewrite (permute_lift x n0 k p 0).
Qed.

Lemma distr_lift_subst M N n k :
  lift n k (subst0 N M) = subst0 (map (lift n k) N) (lift n (length N + k) M).
Proof.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); try easy.
  apply distr_lift_subst_rec.
Qed.

Lemma distr_lift_subst10 M N n k :
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

Lemma subst1_mkApps u k t l :
  subst1 u k (mkApps t l) = mkApps (subst1 u k t) (map (subst1 u k) l).
Proof.
  apply subst_mkApps.
Qed.

Lemma distr_subst_rec M N (P : list term) n p :
  subst P (p + n) (subst N p M)
  = subst (map (subst P n) N) p (subst P (p + length N + n) M).
Proof.
  revert N P n p; elim M using term_forall_list_ind; intros;
    match goal with
    | |- context [tRel _] => idtac
    | |- _ => simpl
    end; try reflexivity;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def,
      ?length_map, ?Nat.add_assoc, ?map_predicate_map_predicate;
      try solve [f_equal; auto; solve_all].

  - unfold subst at 2.
    elim (leb_spec p n); intros.
    + destruct (nth_error_spec N (n - p)).
      ++ rewrite -> subst_rel_lt by lia.
         erewrite subst_rel_eq; try easy.
         2:rewrite -> nth_error_map, e; reflexivity.
         now rewrite commut_lift_subst_rec. lia.
      ++ unfold subst at 4.
         elim (leb_spec (p + length N + n0) n); intros; subst; try easy.
         destruct (nth_error_spec P (n - (p + length N + n0))).
         +++ erewrite subst_rel_eq. 2:eauto. 2:lia.
             assert (p + length N + n0 = length (map (subst P n0) N) + (p + n0))
               by (rewrite length_map; lia).
             rewrite H1. rewrite simpl_subst_rec; eauto; try lia.
         +++ rewrite !subst_rel_gt; rewrite ?length_map; try lia. f_equal; lia.
         +++ rewrite subst_rel_lt; try easy.
             rewrite -> subst_rel_gt; rewrite length_map. trivial. lia.
    + rewrite !subst_rel_lt; try easy.
Qed.

Lemma distr_subst P N M k :
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
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
      ?map_predicate_map_predicate, ?map_branch_map_branch;
    simpl closed in *;
    unfold test_predicate_k, test_def, test_branch_k in *;
    try solve [simpl lift; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
  - rewrite lift_rel_lt; auto.
    revert H. elim (Nat.ltb_spec n0 k); intros; try easy.
Qed.

Lemma closed_upwards {k t} k' : closedn k t -> k' >= k -> closedn k' t.
Proof.
  revert k k'.
  elim t using term_forall_list_ind; intros; try lia;
    autorewrite with map;
    simpl closed in *; unfold test_snd, test_def, test_predicate_k, test_branch_k in *;
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

Lemma subst_empty_eq k : subst [] k ≐1 id.
Proof. intros x; now rewrite subst_empty. Qed.

Lemma lift_to_extended_list_k Γ k : forall k',
    to_extended_list_k Γ (k' + k) = map (lift0 k') (to_extended_list_k Γ k).
Proof.
  unfold to_extended_list_k.
  intros k'. rewrite !reln_alt_eq !app_nil_r.
  induction Γ in k, k' |- *; simpl; auto.
  destruct a as [na [body|] ty].
  now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k').
  simpl. now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k'), map_app.
Qed.

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
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def,
                  ?length_map, ?map_predicate_map_predicate; eauto; solve_all).

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
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def,
                  ?length_map, ?Nat.add_assoc, ?map_predicate_map_predicate; solve_all).

  - repeat nth_leb_simpl.
    rewrite -> Nat.add_comm, simpl_subst; eauto.
Qed.

Lemma subst_app_simpl' (l l' : list term) (k : nat) (t : term) n :
  n = #|l| ->
  subst (l ++ l') k t = subst l k (subst l' (k + n) t).
Proof. intros ->; apply subst_app_simpl. Qed.

Lemma isLambda_subst (s : list term) k (bod : term) :
  isLambda bod = true -> isLambda (subst s k bod) = true.
Proof.
  intros. destruct bod; try discriminate. reflexivity.
Qed.

Lemma map_vass_map_def g l n k :
  mapi (fun i d => vass (dname d) (lift0 i (dtype d)))
       (map (map_def (lift n k) g) l)
  = mapi (fun i d => map_decl (lift n (i + k)) d)
         (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite -> permute_lift. f_equal; lia. lia.
Qed.

Definition fix_context_gen k mfix :=
  List.rev (mapi_rec (fun (i : nat) (d : def term) => vass (dname d) (lift0 i (dtype d))) mfix k).

Lemma lift_decl0 k d : map_decl (lift 0 k) d = d.
Proof.
  destruct d; destruct decl_body; unfold map_decl; simpl;
  f_equal; now rewrite ?lift0_id.
Qed.

Lemma lift0_context k Γ : lift_context 0 k Γ = Γ.
Proof.
  unfold lift_context, fold_context_k.
  rewrite rev_mapi. rewrite List.rev_involutive.
  unfold mapi. generalize 0 at 2. generalize #|List.rev Γ|.
  induction Γ; intros; simpl; trivial.
  rewrite lift_decl0; f_equal; auto.
Qed.

Lemma lift_context_length n k Γ : #|lift_context n k Γ| = #|Γ|.
Proof. apply fold_context_k_length. Qed.
#[global]
Hint Rewrite lift_context_length : lift len.

Definition lift_context_snoc0 n k Γ d : lift_context n k (d :: Γ) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof. unfold lift_context. now rewrite fold_context_k_snoc0. Qed.
#[global]
Hint Rewrite lift_context_snoc0 : lift.

Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold snoc. apply lift_context_snoc0.
Qed.
#[global]
Hint Rewrite lift_context_snoc : lift.

Lemma lift_context_alt n k Γ :
  lift_context n k Γ =
  mapi (fun k' d => lift_decl n (Nat.pred #|Γ| - k' + k) d) Γ.
Proof.
  unfold lift_context. apply: fold_context_k_alt.
Qed.

Lemma lift_context_app n k Γ Δ :
  lift_context n k (Γ ,,, Δ) = lift_context n k Γ ,,, lift_context n (#|Γ| + k) Δ.
Proof.
  unfold lift_context, fold_context_k, app_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.length_rev. f_equal. lia.
Qed.

Lemma lift_it_mkProd_or_LetIn n k ctx t :
  lift n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (lift_context_snoc n k ctx a).
  now destruct a as [na [b|] ty].
Qed.

Lemma lift_it_mkLambda_or_LetIn n k ctx t :
  lift n k (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (lift_context_snoc n k ctx a).
  now destruct a as [na [b|] ty].
Qed.

Lemma map_lift_lift n k l : map (fun x => lift0 n (lift0 k x)) l = map (lift0 (n + k)) l.
Proof. apply map_ext => x.
  rewrite simpl_lift; try lia. reflexivity.
Qed.

Lemma simpl_subst' :
  forall N M n p k, k = List.length N -> p <= n -> subst N p (lift0 (k + n) M) = lift0 n M.
Proof.
  intros. subst k. rewrite simpl_subst_rec; auto.
  + now rewrite Nat.add_0_r.
  + lia.
Qed.

Lemma subst_subst_lift (s s' : list term) n t : n = #|s| + #|s'| ->
  subst0 s (subst0 s' (lift0 n t)) = t.
Proof.
  intros ->. rewrite Nat.add_comm simpl_subst' //; try lia.
  now rewrite -(Nat.add_0_r #|s|) simpl_subst' // lift0_id.
Qed.

Lemma map_subst_lift_id s l : map (subst0 s ∘ lift0 #|s|) l = l.
Proof.
  induction l; simpl; auto.
  rewrite -{1}(Nat.add_0_r #|s|) simpl_subst'; auto.
  now rewrite lift0_id IHl.
Qed.

Lemma map_subst_lift_id_eq s l k : k = #|s| -> map (subst0 s ∘ lift0 k) l = l.
Proof. intros ->; apply map_subst_lift_id. Qed.

Lemma map_subst_lift_ext N n p k l :
  k = #|N| -> p <= n ->
  map (subst N p ∘ lift0 (k + n)) l = map (lift0 n) l.
Proof.
  intros -> pn.
  apply map_ext => x. now apply simpl_subst'.
Qed.

Lemma map_subst_subst_lift_lift (s s' : list term) k k' l : k + k' = #|s| + #|s'| ->
  map (fun t => subst0 s (subst0 s' (lift k k' (lift0 k' t)))) l = l.
Proof.
  intros H. eapply All_map_id. eapply All_refl => x.
  rewrite simpl_lift; try lia. rewrite subst_subst_lift //.
Qed.

Lemma nth_error_lift_context:
  forall (Γ' Γ'' : context) (v : nat),
    v < #|Γ'| -> forall nth k,
    nth_error Γ' v = Some nth ->
    nth_error (lift_context #|Γ''| k Γ') v = Some (lift_decl #|Γ''| (#|Γ'| - S v + k) nth).
Proof.
  induction Γ'; intros.
  - easy.
  - simpl. destruct v; rewrite lift_context_snoc0.
    + simpl. repeat f_equal; try lia. simpl in *. congruence.
    + simpl. apply IHΓ'; simpl in *; (lia || congruence).
Qed.

Lemma nth_error_lift_context_eq:
  forall (Γ' Γ'' : context) (v : nat) k,
    nth_error (lift_context #|Γ''| k Γ') v =
    option_map (lift_decl #|Γ''| (#|Γ'| - S v + k)) (nth_error Γ' v).
Proof.
  induction Γ'; intros.
  - simpl. unfold lift_context, fold_context_k; simpl. now rewrite nth_error_nil.
  - simpl. destruct v; rewrite lift_context_snoc0.
    + simpl. repeat f_equal; try lia.
    + simpl. apply IHΓ'; simpl in *; (lia || congruence).
Qed.

#[global]
Hint Rewrite subst_context_length : subst wf.

#[global]
Hint Rewrite subst_context_snoc : subst.

Lemma subst_decl0 k d : map_decl (subst [] k) d = d.
Proof.
  destruct d; destruct decl_body;
    unfold subst_decl, map_decl; simpl in *;
    f_equal; simpl; rewrite subst_empty; intuition trivial.
Qed.

Lemma subst0_context k Γ : subst_context [] k Γ = Γ.
Proof.
  unfold subst_context, fold_context_k.
  rewrite rev_mapi. rewrite List.rev_involutive.
  unfold mapi. generalize 0. generalize #|List.rev Γ|.
  induction Γ; intros; simpl; trivial.
  erewrite subst_decl0; f_equal; eauto.
Qed.

Lemma subst_context_snoc0 s Γ d : subst_context s 0 (Γ ,, d) = subst_context s 0 Γ ,, subst_decl s #|Γ| d.
Proof.
  unfold snoc. now rewrite subst_context_snoc Nat.add_0_r.
Qed.
#[global]
Hint Rewrite subst_context_snoc : subst.

Lemma subst_context_app s k Γ Δ :
  subst_context s k (Γ ,,, Δ) = subst_context s k Γ ,,, subst_context s (#|Γ| + k) Δ.
Proof.
  unfold subst_context, fold_context_k, app_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.length_rev. f_equal. lia.
Qed.

Lemma distr_lift_subst_context n k s Γ : lift_context n k (subst_context s 0 Γ) =
  subst_context (map (lift n k) s) 0 (lift_context n (#|s| + k) Γ).
Proof.
  rewrite !lift_context_alt !subst_context_alt.
  rewrite !mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl /subst_decl !compose_map_decl.
  apply map_decl_ext => y.
  rewrite !mapi_length Nat.add_0_r; autorewrite with len. unf_term.
  rewrite distr_lift_subst_rec; f_equal. f_equal. lia.
Qed.

Lemma skipn_subst_context n s k Γ : skipn n (subst_context s k Γ) =
  subst_context s k (skipn n Γ).
Proof.
  rewrite !subst_context_alt.
  rewrite skipn_mapi_rec. rewrite mapi_rec_add /mapi.
  apply mapi_rec_ext. intros.
  f_equal. rewrite List.length_skipn. lia.
Qed.

Lemma nth_error_extended_subst Γ k i :
  nth_error (extended_subst Γ k) i =
  match nth_error Γ i with
  | Some decl =>
    match decl_body decl with
    | None => Some (tRel (k + context_assumptions (List.firstn i Γ)))
    | Some body =>
      let s := extended_subst (List.skipn (S i) Γ) (context_assumptions (List.firstn i Γ) + k) in
      let b' := lift (context_assumptions (List.skipn (S i) Γ) +
        (context_assumptions (List.firstn i Γ) + k)) #|s| body in
      Some (subst0 s b')
    end
  | None => None
  end.
Proof.
  induction Γ in k, i |- *.
  - cbn. rewrite !nth_error_nil //.
  - rewrite skipn_S. cbn. destruct a as [na [] ty].
    cbn [decl_body].
    destruct i.
    + cbn => //.
    + cbn. rewrite IHΓ //.
    + cbn.
      destruct i.
      * cbn. lia_f_equal.
      * cbn. rewrite IHΓ.
        destruct nth_error => //.
        destruct (decl_body c) => //; try lia_f_equal.
        cbn. lia_f_equal.
Qed.

Lemma lift_extended_subst (Γ : context) k :
  extended_subst Γ k = map (lift0 k) (extended_subst Γ 0).
Proof.
  induction Γ as [|[? [] ?] ?] in k |- *; simpl; auto; unf_term.
  - rewrite IHΓ. f_equal.
    autorewrite with len.
    rewrite distr_lift_subst. f_equal.
    autorewrite with len. rewrite simpl_lift; lia_f_equal.
  - rewrite Nat.add_0_r; f_equal.
    rewrite IHΓ (IHΓ 1).
    rewrite map_map_compose. apply map_ext => x.
    rewrite simpl_lift; try lia.
    now rewrite Nat.add_1_r.
Qed.

Lemma lift_extended_subst' Γ k k' : extended_subst Γ (k + k') = map (lift0 k) (extended_subst Γ k').
Proof.
  induction Γ as [|[? [] ?] ?] in k |- *; simpl; auto.
  - rewrite IHΓ. f_equal.
    autorewrite with len.
    rewrite distr_lift_subst. f_equal.
    autorewrite with len. rewrite simpl_lift; lia_f_equal.
  - f_equal.
    rewrite (IHΓ (S k)) (IHΓ 1).
    rewrite map_map_compose. apply map_ext => x.
    rewrite simpl_lift; lia_f_equal.
Qed.

Lemma subst_extended_subst_k s Γ k k' : extended_subst (subst_context s k Γ) k' =
  map (subst s (k + context_assumptions Γ + k')) (extended_subst Γ k').
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; rewrite subst_context_snoc /=;
    autorewrite with len; f_equal; auto.
  - rewrite IHΓ.
    rewrite commut_lift_subst_rec; try lia.
    rewrite distr_subst. now len.
  - elim: Nat.leb_spec => //. lia.
  - rewrite (lift_extended_subst' _ 1 k') IHΓ.
    rewrite (lift_extended_subst' _ 1 k').
    rewrite !map_map_compose.
    apply map_ext.
    intros x.
    erewrite (commut_lift_subst_rec); lia_f_equal.
Qed.

Lemma extended_subst_app Γ Γ' :
  extended_subst (Γ ++ Γ') 0 =
  extended_subst (subst_context (extended_subst Γ' 0) 0
   (lift_context (context_assumptions Γ') #|Γ'| Γ)) 0 ++
   extended_subst Γ' (context_assumptions Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in |- *; simpl; auto.
  - autorewrite with len.
    rewrite IHΓ. simpl.  rewrite app_comm_cons.
    f_equal.
    erewrite subst_app_simpl'.
    2:autorewrite with len; reflexivity.
    simpl.
    rewrite lift_context_snoc subst_context_snoc /=.
    len. f_equal. f_equal.
    rewrite -{3}(Nat.add_0_r #|Γ|).
    erewrite <- (simpl_lift _ _ _ _ (#|Γ| + #|Γ'|)). all:try lia.
    rewrite distr_lift_subst_rec. autorewrite with len.
    f_equal. apply lift_extended_subst.
  - rewrite lift_context_snoc  subst_context_snoc /=. lia_f_equal.
    rewrite lift_extended_subst. rewrite IHΓ /=.
    rewrite map_app. rewrite !(lift_extended_subst _ (S _)).
    rewrite (lift_extended_subst _ (context_assumptions Γ)).
    rewrite map_map_compose.
    f_equal. apply map_ext. intros.
    rewrite simpl_lift; lia_f_equal.
Qed.

Lemma subst_context_comm s s' Γ :
  subst_context s 0 (subst_context s' 0 Γ) =
  subst_context (map (subst s 0) s' ++ s) 0 Γ.
Proof.
  intros.
  rewrite !subst_context_alt !mapi_compose.
  apply mapi_ext => i x.
  destruct x as [na [b|] ty] => //.
  - rewrite /subst_decl /map_decl /=; f_equal.
    + rewrite !mapi_length. f_equal. rewrite {2}Nat.add_0_r.
      rewrite subst_app_simpl.
      rewrite distr_subst_rec. rewrite Nat.add_0_r; f_equal; try lia.
      rewrite length_map. f_equal; lia.
    + rewrite mapi_length.
      rewrite subst_app_simpl.
      rewrite {2}Nat.add_0_r.
      rewrite distr_subst_rec. rewrite Nat.add_0_r; f_equal; try lia.
      rewrite length_map. f_equal; lia.
  - rewrite /subst_decl /map_decl /=; f_equal.
    rewrite !mapi_length. rewrite {2}Nat.add_0_r.
    rewrite subst_app_simpl.
    rewrite distr_subst_rec. rewrite Nat.add_0_r; f_equal; try lia.
    rewrite length_map. f_equal. lia.
Qed.

Lemma context_assumptions_subst s n Γ :
  context_assumptions (subst_context s n Γ) = context_assumptions Γ.
Proof. apply context_assumptions_fold. Qed.
#[global]
Hint Rewrite context_assumptions_subst : pcuic.

Lemma subst_app_context s s' Γ : subst_context (s ++ s') 0 Γ = subst_context s 0 (subst_context s' #|s| Γ).
Proof.
  induction Γ; simpl; auto.
  rewrite !subst_context_snoc /= /subst_decl /map_decl /=. simpl.
  rewrite IHΓ. f_equal. f_equal.
  - destruct a as [na [b|] ty]; simpl; auto.
    f_equal. rewrite subst_context_length Nat.add_0_r.
    now rewrite subst_app_simpl.
  - rewrite subst_context_length Nat.add_0_r.
    now rewrite subst_app_simpl.
Qed.

Lemma subst_app_context' (s s' : list term) (Γ : context) n :
  n = #|s| ->
  subst_context (s ++ s') 0 Γ = subst_context s 0 (subst_context s' n Γ).
Proof.
  intros ->; apply subst_app_context.
Qed.

Lemma map_subst_app_simpl l l' k (ts : list term) :
  map (subst l k ∘ subst l' (k + #|l|)) ts =
  map (subst (l ++ l') k) ts.
Proof.
  eapply map_ext. intros.
  now rewrite subst_app_simpl.
Qed.

Lemma simpl_map_lift x n k :
  map (lift0 n ∘ lift0 k) x =
  map (lift k n ∘ lift0 n) x.
Proof.
  apply map_ext => t.
  rewrite simpl_lift => //; try lia.
  rewrite simpl_lift; try lia.
  now rewrite Nat.add_comm.
Qed.

Lemma subst_it_mkProd_or_LetIn n k ctx t :
  subst n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_context n k ctx) (subst n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (subst_context_snoc n k ctx a). unfold snoc in e. rewrite e. clear e.
  simpl. rewrite -> IHctx.
  pose (subst_context_snoc n k ctx a). simpl. now destruct a as [na [b|] ty].
Qed.

Lemma map_subst_instance_to_extended_list_k u ctx k :
  to_extended_list_k (subst_instance u ctx) k
  = to_extended_list_k ctx k.
Proof.
  unfold to_extended_list_k.
  cut (map (subst_instance u) [] = []); [|reflexivity].
  unf_term. generalize (@nil term); intros l Hl.
  induction ctx in k, l, Hl |- *; cbnr.
  destruct a as [? [] ?]; cbnr; eauto.
Qed.

Lemma to_extended_list_k_subst n k c k' :
  to_extended_list_k (subst_context n k c) k' = to_extended_list_k c k'.
Proof.
  unfold to_extended_list_k. revert k'.
  unf_term. generalize (@nil term) at 1 2.
  induction c in n, k |- *; simpl; intros. 1: reflexivity.
  rewrite subst_context_snoc. unfold snoc. simpl.
  destruct a. destruct decl_body.
  - unfold subst_decl, map_decl. simpl.
    now rewrite IHc.
  - simpl. apply IHc.
Qed.

Lemma it_mkProd_or_LetIn_inj ctx s ctx' s' :
  it_mkProd_or_LetIn ctx (tSort s) = it_mkProd_or_LetIn ctx' (tSort s') ->
  ctx = ctx' /\ s = s'.
Proof.
  move/(f_equal (destArity [])).
  rewrite !destArity_it_mkProd_or_LetIn /=.
  now rewrite !app_context_nil_l => [= -> ->].
Qed.

Lemma destArity_spec ctx T :
  match destArity ctx T with
  | Some (ctx', s) => it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s)
  | None => True
  end.
Proof.
  induction T in ctx |- *; simpl; try easy.
  - specialize (IHT2 (ctx,, vass na T1)). now destruct destArity.
  - specialize (IHT3 (ctx,, vdef na T1 T2)). now destruct destArity.
Qed.

Lemma destArity_spec_Some ctx T ctx' s :
  destArity ctx T = Some (ctx', s)
  -> it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s).
Proof.
  pose proof (destArity_spec ctx T) as H.
  intro e; now rewrite e in H.
Qed.

(** Standard substitution lemma for a context with no lets. *)

Inductive nth_error_app_spec {A} (l l' : list A) (n : nat) : option A -> Type :=
| nth_error_app_spec_left x :
  nth_error l n = Some x ->
  n < #|l| ->
  nth_error_app_spec l l' n (Some x)
| nth_error_app_spec_right x :
  nth_error l' (n - #|l|) = Some x ->
  #|l| <= n < #|l| + #|l'| ->
  nth_error_app_spec l l' n (Some x)
| nth_error_app_spec_out : #|l| + #|l'| <= n -> nth_error_app_spec l l' n None.

Lemma nth_error_appP {A} (l l' : list A) (n : nat) : nth_error_app_spec l l' n (nth_error (l ++ l') n).
Proof.
  destruct (Nat.ltb n #|l|) eqn:lt; [apply Nat.ltb_lt in lt|apply Nat.ltb_nlt in lt].
  * rewrite nth_error_app_lt //.
    destruct (snd (nth_error_Some' _ _) lt) as [x eq].
    rewrite eq.
    constructor; auto.
  * destruct (Nat.ltb n (#|l| + #|l'|)) eqn:ltb'; [apply Nat.ltb_lt in ltb'|apply Nat.ltb_nlt in ltb'].
    + rewrite nth_error_app2; try lia.
      destruct nth_error eqn:hnth.
      - constructor 2; auto; try lia.
      - constructor.
        eapply nth_error_None in hnth. lia.
    + case: nth_error_spec => //; try lia.
      { intros. len in l0. lia. }
      len. intros. constructor. lia.
Qed.

Lemma nth_error_app_context (Γ Δ : context) (n : nat) :
  nth_error_app_spec Δ Γ n (nth_error (Γ ,,, Δ) n).
Proof.
  apply nth_error_appP.
Qed.

Lemma expand_lets_k_nil k t : expand_lets_k [] k t = t.
Proof. by rewrite /expand_lets_k /= subst_empty lift0_id. Qed.



