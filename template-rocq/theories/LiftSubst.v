(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Environment.
From MetaRocq.Template Require Import Ast AstUtils Induction WfAst.
From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

(** * Lifting and substitution for the AST

  Along with standard commutation lemmas.
  Definition of [closedn] (boolean) predicate for checking if
  a term is closed. *)

Definition up := lift 1 0.

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

Lemma lift0_id : forall M k, lift 0 k M = M.
Proof.
  intros M.
  elim M using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try (f_equal; auto; solve_all).
  now elim (leb k n).
Qed.

Lemma lift0_p : forall M, lift0 0 M = M.
Proof.
  intros; unfold lift in |- *.
  apply lift0_id; easy.
Qed.

Lemma simpl_lift :
  forall M n k p i,
    i <= k + n ->
    k <= i -> lift p i (lift n k M) = lift (p + n) k M.
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
      rewrite -> ?map_predicate_map_predicate;
      try (rewrite -> H, ?H0, ?H1; auto); try (f_equal; auto; solve_all).

  - elim (leb_spec k n); intros.
    + elim (leb_spec i (n0 + n)); intros; lia.
    + elim (leb_spec i n); intros; lia.
Qed.

Lemma simpl_lift0 : forall M n, lift0 (S n) M = lift0 1 (lift0 n M).
  now intros; rewrite simpl_lift.
Qed.


Lemma map_branches_k_map_branches_k
      {term term' term''}
      (f : nat -> term' -> term'')
      (g : branch term -> term -> term')
      (f' : term -> term')
      (l : list (branch term)) k :
  map (fun b => map_branch (f (#|bcontext (map_branch (g b) b)| + k)) (map_branch f' b)) l =
  map (fun b => map_branch (f (#|bcontext b| + k)) (map_branch f' b)) l.
Proof.
  eapply map_ext => b. rewrite map_branch_map_branch.
  now apply map_branch_eq_spec.
Qed.

Lemma permute_lift :
  forall M n k p i,
    i <= k ->
    lift p i (lift n k M) = lift n (k + p) (lift p i M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
      ?Nat.add_assoc, ?map_predicate_map_predicate, ?map_branches_map_branches; f_equal;
      try solve [auto; solve_all]; repeat nth_leb_simpl.
Qed.

Lemma permute_lift0 :
  forall M k, lift0 1 (lift 1 k M) = lift 1 (S k) (lift0 1 M).
  intros.
  change (lift 1 0 (lift 1 k M) = lift 1 (1 + k) (lift 1 0 M))
    in |- *.
  rewrite permute_lift; easy.
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

#[global]
Hint Resolve lift_isApp map_non_nil isLambda_lift : all.

Lemma mkApps_tApp t l :
  isApp t = false -> l <> nil -> mkApps t l = tApp t l.
Proof.
  intros.
  destruct l. simpl. contradiction.
  destruct t; simpl; try reflexivity.
  simpl in H. discriminate.
Qed.

Lemma simpl_subst_rec :
  forall Σ M (H : wf Σ M) N n p k,
    p <= n + k ->
    k <= p -> subst N p (lift (List.length N + n) k M) = lift n k M.
Proof.
  intros Σ M wfM. induction wfM using term_wf_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
                 ?map_predicate_map_predicate;
      try solve [f_equal; auto; solve_all]; repeat nth_leb_simpl.

  - rewrite IHwfM; auto.
    apply (lift_isApp n k) in H.
    rewrite mkApps_tApp; auto using map_non_nil.
    f_equal; solve_all.
Qed.

Lemma simpl_subst Σ :
  forall N M (H : wf Σ M) n p, p <= n -> subst N p (lift0 (length N + n) M) = lift0 n M.
Proof.  intros. erewrite simpl_subst_rec; eauto. now rewrite Nat.add_0_r. lia. Qed.

Lemma mkApps_tRel n a l : mkApps (tRel n) (a :: l) = tApp (tRel n) (a :: l).
Proof.
  simpl. reflexivity.
Qed.

Lemma lift_mkApps n k t l : lift n k (mkApps t l) = mkApps (lift n k t) (map (lift n k) l).
Proof.
  revert n k t; induction l; intros n k t; destruct t; try reflexivity.
  simpl. f_equal.
  now rewrite map_app.
Qed.

Lemma commut_lift_subst_rec :
  forall M N n p k,
    k <= p ->
    lift n k (subst N p M) = subst N (p + n) (lift n k M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; try easy;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc,
                 ?map_predicate_map_predicate;
      try solve [f_equal; auto; solve_all].

  - repeat nth_leb_simpl.
    rewrite -> simpl_lift by easy. f_equal; lia.
  - rewrite lift_mkApps. f_equal. auto.
    rewrite map_map_compose. solve_all.
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
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc,
                 ?map_predicate_map_predicate;
      try solve [f_equal; auto; solve_all].

  - unfold subst at 1. unfold lift at 4.
    repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    revert e0. intros [= <-].
    now rewrite (permute_lift x n0 k p 0).
  - rewrite lift_mkApps. f_equal; auto.
    rewrite map_map_compose; solve_all.
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
  revert u k t; induction l; intros u k t; destruct t; try reflexivity.
  intros. simpl mkApps at 1. simpl subst at 1 2. rewrite map_app. now rewrite -mkApps_app.
Qed.

Lemma subst1_mkApps u k t l : subst1 u k (mkApps t l) = mkApps (subst1 u k t) (map (subst1 u k) l).
Proof.
  apply subst_mkApps.
Qed.

Lemma distr_subst_rec Σ :
  forall M N (P : list term) (wfP : All (wf Σ) P) n p,
    subst P (p + n) (subst N p M) =
    subst (map (subst P n) N) p (subst P (p + length N + n) M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; match goal with
              |- context [tRel _] => idtac
            | |- _ => simpl
            end; try easy;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?Nat.add_assoc,
                 ?map_predicate_map_predicate;
      try solve [f_equal; auto; solve_all].

  - unfold subst at 2.
    elim (leb_spec p n); intros; try easy.

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
             rewrite H1. erewrite simpl_subst_rec; eauto; try lia.
             eapply nth_error_all in e; eauto.
         +++ rewrite !subst_rel_gt; rewrite ?length_map; try lia. f_equal; lia.
         +++ rewrite subst_rel_lt; try easy.
             rewrite -> subst_rel_gt; rewrite length_map. trivial. lia.
    + rewrite !subst_rel_lt; try easy.

  - rewrite !subst_mkApps. rewrite H; auto. f_equal.
    rewrite !map_map_compose. solve_all.
Qed.

Lemma distr_subst Σ :
  forall P (wfP : All (wf Σ) P) N M k,
    subst P k (subst0 N M) = subst0 (map (subst P k) N) (subst P (length N + k) M).
Proof.
  intros.
  pattern k at 1 3 in |- *.
  change k with (0 + k). hnf.
  eapply distr_subst_rec; eauto.
Qed.

Lemma lift_closed n k t : closedn k t -> lift n k t = t.
Proof.
  revert k.
  elim t using term_forall_list_ind; intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
               ?map_predicate_map_predicate;
    simpl closed in *;
    unfold test_def, test_predicate in *;
    try solve [simpl lift; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
  - rewrite lift_rel_lt; auto.
    revert H. elim (Nat.ltb_spec n0 k); intros; try easy.
  - simpl lift. f_equal. solve_all. unfold test_def in b. toProp. solve_all.
  - simpl lift. f_equal. solve_all. unfold test_def in b. toProp. solve_all.
Qed.

Lemma closed_upwards {k t} k' : closedn k t -> k' >= k -> closedn k' t.
Proof.
  revert k k'.
  elim t using term_forall_list_ind; intros; try lia;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
               ?map_predicate_map_predicate;
    simpl closed in *; unfold test_snd, test_def, test_predicate, test_branch in *;
      try solve [(try f_equal; simpl; repeat (rtoProp; solve_all); eauto)].

  - elim (ltb_spec n k'); auto. intros.
    apply ltb_lt in H. lia.
Qed.

Lemma subst_empty Σ k a : wf Σ a -> subst [] k a = a.
Proof.
  induction 1 in k |- * using term_wf_forall_list_ind; simpl; try congruence;
    try solve [f_equal; eauto; solve_all].

  - elim (Nat.compare_spec k n); destruct (Nat.leb_spec k n); intros; try easy.
    subst. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. reflexivity.
    assert (n - k > 0) by lia.
    assert (exists n', n - k = S n'). exists (pred (n - k)). lia.
    destruct H2. rewrite H2. simpl. now rewrite Nat.sub_0_r.
  - rewrite IHX. rewrite mkApps_tApp; eauto with wf.
    f_equal; solve_all.
Qed.

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

Lemma simpl_subst_k Σ (N : list term) (M : term) :
  wf Σ M -> forall k p, p = #|N| -> subst N k (lift p k M) = M.
Proof.
  intros. subst p. rewrite <- (Nat.add_0_r #|N|).
  erewrite simpl_subst_rec, lift0_id; eauto.
Qed.

Lemma subst_app_decomp Σ l l' k t :
  wf Σ t -> All (wf Σ) l ->
  subst (l ++ l') k t = subst l' k (subst (List.map (lift0 (length l')) l) k t).
Proof.
  intros wft wfl.
  induction wft in k |- * using term_wf_forall_list_ind; simpl; auto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
                             ?map_predicate_map_predicate;
         eauto; solve_all).

  - repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0; intros <-.
    rewrite -> permute_lift by auto.
    rewrite <- (Nat.add_0_r #|l'|).
    erewrite -> simpl_subst_rec, lift0_id; auto with wf; try lia. apply wf_lift.
    eapply nth_error_all in e; eauto.
Qed.

Lemma subst_app_simpl Σ l l' k t :
  wf Σ t -> All (wf Σ) l -> All (wf Σ) l' ->
  subst (l ++ l') k t = subst l k (subst l' (k + length l) t).
Proof.
  intros wft wfl wfl'.
  induction wft in k |- * using term_wf_forall_list_ind; simpl; eauto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
                             ?Nat.add_assoc, ?map_predicate_map_predicate;
         eauto; solve_all; eauto).

  - repeat nth_leb_simpl.
    erewrite -> Nat.add_comm, simpl_subst; eauto.
    eapply nth_error_all in e; eauto.
Qed.

Lemma isLambda_subst (s : list term) k (bod : term) :
  isLambda bod = true -> isLambda (subst s k bod) = true.
Proof.
  intros. destruct bod; try discriminate. reflexivity.
Qed.

Lemma map_vass_map_def g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (lift n k) g) l)) =
  (mapi (fun i d => map_decl (lift n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite permute_lift. lia. f_equal; lia.
Qed.
(*
Lemma noccur_between_subst k n t : noccur_between k n t ->
  closedn (n + k) t -> closedn k t.
Proof.
Qed.  *)                        (* TODO *)

Lemma strip_casts_lift n k t :
  strip_casts (lift n k t) = lift n k (strip_casts t).
Proof.
  induction t in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose  ?compose_on_snd ?compose_map_def ?length_map;
   f_equal; solve_all; eauto.

  - rewrite lift_mkApps IHt map_map_compose.
    f_equal; solve_all.
  - rewrite !map_predicate_map_predicate.
    unfold map_predicate. f_equal.
    solve_all. solve_all.
Qed.

Lemma mkApps_ex t u l : ∑ f args, Ast.mkApps t (u :: l) = Ast.tApp f args.
Proof.
  induction t; simpl; eexists _, _; reflexivity.
Qed.
(*
Lemma mkApps_tApp' f l l' : mkApps (tApp f l) l' = mkApps f (l ++ l').
Proof.
  induction l'; simpl. rewrite app_nil_r.  *)

Lemma list_length_ind {A} (P : list A -> Type) (p0 : P [])
  (pS : forall d Γ, (forall Γ', #|Γ'| <= #|Γ|  -> P Γ') -> P (d :: Γ))
  Γ : P Γ.
Proof.
  generalize (le_n #|Γ|).
  generalize #|Γ| at 2.
  induction n in Γ |- *.
  destruct Γ; [|simpl; intros; exfalso; lia].
  intros. apply p0.
  intros.
  destruct Γ; simpl in *.
  apply p0. apply pS. intros. apply IHn. simpl. lia.
Qed.

Lemma strip_casts_mkApps_tApp f l :
  isApp f = false ->
  strip_casts (mkApps f l) = strip_casts (tApp f l).
Proof.
  induction l. simpl; auto.
  intros.
  rewrite mkApps_tApp //.
Qed.

Lemma strip_casts_mkApps f l :
  isApp f = false ->
  strip_casts (mkApps f l) = mkApps (strip_casts f) (map strip_casts l).
Proof.
  intros Hf. rewrite strip_casts_mkApps_tApp //.
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
