(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction PCUICUnivSubst PCUICLiftSubst PCUICSigmaCalculus.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** * Lemmas about the [closedn] predicate *)

Lemma lift_decl_closed n k d : closed_decl k d -> lift_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /test_decl /lift_decl /map_decl /=; unf_term.
  - move/andP => [cb cty]. now rewrite !lift_closed //.
  - move=> cty; now rewrite !lift_closed //.
Qed.

Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /test_decl /=.
  - move/andP => /= [cb cty] k' lek'. do 2 rewrite (@closed_upwards k) //.
  - move=> cty k' lek'; rewrite (@closed_upwards k) //.
Qed.

Lemma alli_fold_context_k (p : nat -> context_decl -> bool) ctx f :
  (forall i d, p i d -> map_decl (f i) d = d) ->
  alli p 0 (List.rev ctx) ->
  fold_context_k f ctx = ctx.
Proof.
  intros Hf.
  rewrite /fold_context_k /mapi.
  generalize 0.
  induction ctx using rev_ind; simpl; intros n; auto.
  rewrite List.rev_app_distr /=.
  move/andP=> [] Hc Hd.
  rewrite Hf //; len. f_equal.
  now apply IHctx.
Qed.

Lemma closedn_ctx_cons n d Γ : closedn_ctx n (d :: Γ) = closedn_ctx n Γ && closed_decl (n + #|Γ|) d.
Proof.
  rewrite /=. rewrite Nat.add_comm. bool_congr.
Qed.

Lemma test_context_k_app (p : nat -> term -> bool) n Γ Γ' :
  test_context_k p n (Γ ,,, Γ') =
  test_context_k p n Γ && test_context_k p (n + #|Γ|) Γ'.
Proof.
  rewrite /app_context /= !test_context_k_eq List.rev_app_distr alli_app /=. f_equal.
  rewrite List.length_rev.
  rewrite Nat.add_0_r alli_shift.
  now setoid_rewrite Nat.add_assoc.
Qed.

Lemma closedn_ctx_app n Γ Γ' :
  closedn_ctx n (Γ ,,, Γ') =
  closedn_ctx n Γ && closedn_ctx (n + #|Γ|) Γ'.
Proof.
  now rewrite test_context_k_app.
Qed.

Lemma closed_ctx_lift n k ctx : closedn_ctx k ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  rewrite closedn_ctx_cons lift_context_snoc.
  simpl.
  move/andb_and => /= [Hctx Hd].
  f_equal. rewrite IHctx // lift_decl_closed // Nat.add_comm //.
Qed.

Lemma map_decl_closed_ext (f : term -> term) g k (d : context_decl) : closed_decl k d ->
  (forall x, closedn k x -> f x = g x) ->
  map_decl f d = map_decl g d.
Proof.
  destruct d as [? [?|] ?] => /= cl Hfg;
  unfold map_decl; simpl; f_equal.
  rewrite Hfg => //. unfold closed_decl in cl.
  simpl in cl. now move/andP: cl => [].
  move/andP: cl => [cl cl']. now rewrite Hfg.
  now rewrite Hfg.
Qed.

Lemma test_decl_map_decl (p : term -> bool) (f : term -> term) d :
  test_decl p (map_decl f d) = test_decl (p ∘ f) d.
Proof.
  rewrite /test_decl /map_decl; destruct d; simpl.
  now destruct decl_body.
Qed.

Lemma plus_minus' n m : n + m - m = n.
Proof. lia. Qed.

Lemma test_context_k_mapi (p : nat -> term -> bool) k (f : nat -> term -> term) ctx :
  test_context_k p k (mapi_context f ctx) =
  test_context_k (fun i t => p i (f (i - k) t)) k ctx.
Proof.
  induction ctx; simpl; auto.
  rewrite IHctx. f_equal. rewrite test_decl_map_decl.
  len. now setoid_rewrite plus_minus'.
Qed.
#[global]
Hint Rewrite test_context_k_mapi : map.

Lemma test_context_k_map (p : nat -> term -> bool) k (f : term -> term) ctx :
  test_context_k p k (map_context f ctx) =
  test_context_k (fun i t => p i (f t)) k ctx.
Proof.
  induction ctx; simpl; auto.
  rewrite IHctx. f_equal. rewrite test_decl_map_decl.
  now len.
Qed.
#[global]
Hint Rewrite test_context_k_map : map.

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert k.
  induction t in n, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    autorewrite with map;
    simpl closed in *; solve_all;
    unfold test_def, test_snd, test_predicate_k, test_branch_k in *;
    try eapply primProp_map;
      try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.

  - elim (Nat.leb_spec k' n0); intros. simpl.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H. lia.
    simpl. elim (Nat.ltb_spec); auto. intros.
    apply Nat.ltb_lt in H. lia.
Qed.

Lemma closedn_lift_inv n k k' t : k <= k' ->
                                   closedn (k' + n) (lift n k t) ->
                                   closedn k' t.
Proof.
  induction t in n, k, k' |- * using term_forall_list_ind; intros;
    simpl in *;
    autorewrite with map;
    simpl closed in *; repeat (rtoProp; simpl in *; solve_all); try change_Sk;
    unfold test_def, test_predicate_k, test_branch_k, shiftf in *;
    rewrite -> ?length_map, ?Nat.add_assoc in *;
    simpl in *; eauto 2 with all.

  - revert H0.
    elim (Nat.leb_spec k n0); intros. simpl in *.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. intros. lia.
    revert H1. simpl. elim (Nat.ltb_spec); auto. intros. apply Nat.ltb_lt. lia.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt3 n (S k) (S k')). eauto with all.
  - rtoProp. solve_all; unfold shiftf in *.
    * now len in H6.
    * eapply (i n (#|pcontext p| + k)). lia.
      now len in H3.
  - rtoProp. solve_all; unfold shiftf in *.
    * now len in H7.
    * eapply (b0 n (#|bcontext x| + k)); eauto; try lia.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')).
    now len in H1.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')). eauto with all.
Qed.

Lemma closedn_mkApps k f u:
  closedn k (mkApps f u) = closedn k f && forallb (closedn k) u.
Proof.
  induction u in k, f |- *; simpl; auto.
  - now rewrite andb_true_r.
  - now rewrite IHu /= andb_assoc.
Qed.

#[global] Remove Hints absurd_eq_true trans_eq_bool f_equal2_nat f_equal_nat : core.

Lemma closedn_subst_eq s k k' t :
  forallb (closedn k) s ->
  closedn (k + k' + #|s|) t =
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. solve_all. revert Hs.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    autorewrite with map => //;
    simpl closed in *; try change_Sk;
    unfold test_def, test_branch_k, test_predicate_k in *; simpl in *;
    solve_all.

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

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2.
    rewrite IHt1 // IHt2 //.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2.
    rewrite IHt1 // IHt2 //.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3.
    rewrite IHt1 // IHt2 // IHt3 //.
  - rewrite IHt //.
    f_equal; [|solve_all;f_equal]. f_equal. f_equal. f_equal.
    all:len; solve_all.
    * specialize (e (#|pcontext p| + k')).
      now rewrite Nat.add_assoc (Nat.add_comm k) in e.
    * specialize (b (#|bcontext x| + k')).
      now rewrite Nat.add_assoc (Nat.add_comm k) in b.
  - rewrite a //.
    specialize (b (#|m| + k')).
    rewrite Nat.add_assoc in b.
    rewrite (Nat.add_comm k #|m|) in b.
    rewrite b //.
  - rewrite a //.
    specialize (b (#|m| + k')).
    rewrite Nat.add_assoc in b.
    rewrite (Nat.add_comm k #|m|) in b.
    rewrite b //.
Qed.

Lemma closedn_subst_eq' s k k' t :
  closedn (k + k') (subst s k' t) ->
  closedn (k + k' + #|s|) t.
Proof.
  intros Hs. solve_all. revert Hs.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    autorewrite with map;
    simpl closed in *; repeat (rtoProp; f_equal; solve_all);  try change_Sk;
    unfold test_def, map_branch, test_branch, test_predicate in *; simpl in *; eauto 4 with all.

  - move: Hs; elim (Nat.leb_spec k' n); intros. simpl.
    destruct nth_error eqn:Heq.
    -- eapply Nat.ltb_lt.
       eapply nth_error_Some_length in Heq. lia.
    -- simpl. simpl in Hs.
       apply nth_error_None in Heq. apply Nat.ltb_lt.
       apply Nat.ltb_lt in Hs; lia.
    -- simpl in Hs. eapply Nat.ltb_lt in Hs.
       apply Nat.ltb_lt. lia.

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3. eauto.
  - move/andb_and: H => [hpar hret].
    rewrite !Nat.add_assoc in hret.
    specialize (i (#|pcontext p| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k) in i.
    simpl in *.  unfold test_predicate_k. simpl. solve_all.
    * now len in H5.
  - unfold test_branch_k in *. rtoProp; solve_all.
    * cbn in H4. now len in H4.
    * specialize (b0 (#|bcontext x| + k')).
      rewrite Nat.add_assoc (Nat.add_comm k) in b0.
      simpl in H2. len in H2. rewrite !Nat.add_assoc in H2. eauto.
  - move/andP: b => [hty hbod]. rewrite a0 //.
    specialize (b0 (#|m| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k #|m|) in b0.
    rewrite b0 //. now autorewrite with len in hbod.
  - move/andP: b => [hty hbod]. rewrite a0 //.
    specialize (b0 (#|m| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k #|m|) in b0.
    rewrite b0 //. now autorewrite with len in hbod.
Qed.

Lemma closedn_subst s k k' t :
  forallb (closedn k) s ->
  closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  intros; now rewrite -closedn_subst_eq.
Qed.

Lemma closedn_subst0 s k t :
  forallb (closedn k) s -> closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros.
  generalize (closedn_subst s k 0 t H).
  rewrite Nat.add_0_r. eauto.
Qed.

Lemma subst_closedn s k t : closedn k t -> subst s k t = t.
Proof.
  intros Hcl.
  pose proof (simpl_subst_rec t s 0 k k).
  intros. assert(Hl:=lift_closed (#|s| + 0) _ _ Hcl).
  do 2 (forward H; auto). rewrite Hl in H.
  rewrite H. now apply lift_closed.
Qed.

Lemma closedn_subst_instance k t u :
  closedn k (subst_instance u t) = closedn k t.
Proof.
  revert k.
  induction t in |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    autorewrite with map; len;
    unfold test_predicate_k, test_branch_k in *; solve_all.

  - unfold test_predicate_k, map_predicate; simpl.
    f_equal. f_equal. f_equal. f_equal.
    all: len; solve_all.
  - unfold test_def, map_def. simpl.
    do 3 (f_equal; intuition eauto).
  - unfold test_def, map_def. simpl.
    do 3 (f_equal; intuition eauto).
Qed.

Lemma closed_map_subst_instance n u l :
  forallb (closedn n) (map (subst_instance u) l) =
  forallb (closedn n) l.
Proof.
  induction l; simpl; auto.
  now rewrite closedn_subst_instance IHl.
Qed.

Lemma closedn_ctx_tip n d : closedn_ctx n [d] = closed_decl n d.
Proof. now rewrite test_context_k_eq /= andb_true_r Nat.add_0_r. Qed.


Lemma closedn_mkProd_or_LetIn n d T :
    closed_decl n d && closedn (S n) T = closedn n (mkProd_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; reflexivity.
Qed.

Lemma closedn_mkLambda_or_LetIn (Γ : context) d T :
    closed_decl #|Γ| d ->
    closedn (S #|Γ|) T -> closedn #|Γ| (mkLambda_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; simpl in *. unfold closed_decl.
  simpl. now move/andP => [] /= -> ->.
  simpl. now move/andP => [] /= _ -> ->.
Qed.

Lemma closedn_it_mkProd_or_LetIn n (ctx : list context_decl) T :
  closedn n (it_mkProd_or_LetIn ctx T) =
  closedn_ctx n ctx && closedn (n + #|ctx|) T.
Proof.
  induction ctx in n, T |- *. simpl.
  - now rewrite Nat.add_0_r.
  - rewrite closedn_ctx_cons.
    rewrite (IHctx n (mkProd_or_LetIn a T)) /= -closedn_mkProd_or_LetIn.
    now rewrite // plus_n_Sm andb_assoc.
Qed.

Lemma closedn_it_mkLambda_or_LetIn
      (Γ : context) (ctx : list context_decl) T :
    closedn_ctx #|Γ| ctx ->
    closedn (#|Γ| + #|ctx|) T -> closedn #|Γ| (it_mkLambda_or_LetIn ctx T).
Proof.
  induction ctx in Γ, T |- *. simpl.
  - now rewrite Nat.add_0_r.
  - rewrite closedn_ctx_cons; move/andP => [] cctx ca cT.
    apply (IHctx Γ (mkLambda_or_LetIn a T) cctx).
    simpl in cT. rewrite <- length_app.
    eapply closedn_mkLambda_or_LetIn;
      now rewrite length_app // plus_n_Sm.
Qed.


Lemma closed_subst_context n (Δ Δ' : context) t :
  closedn (n + #|Δ|) t ->
  Alli (fun i d => closed_decl (n + S #|Δ| + i) d) 0 (List.rev Δ') ->
  Alli (fun i d => closed_decl (n + #|Δ| + i) d) 0 (List.rev (subst_context [t] 0 Δ')).
Proof.
  induction Δ' in Δ |- *.
  intros. simpl. auto. constructor.
  destruct a as [? [] ?]; simpl.
  - intros. eapply Alli_app in X as [X X'].
    rewrite subst_context_snoc. simpl. eapply Alli_app_inv.
    eapply IHΔ'; eauto. constructor; [|constructor].
    simpl.
    rewrite /test_decl /map_decl /= Nat.add_0_r List.length_rev subst_context_length.
    inv X'. unfold test_decl in H0. simpl in H0.
    rewrite List.length_rev Nat.add_0_r in H0.
    move/andP: H0 => [Hl Hr];
    rewrite !closedn_subst /= ?H //; eapply closed_upwards; eauto; try lia.
  - intros. eapply Alli_app in X as [X X'].
    rewrite subst_context_snoc. simpl. eapply Alli_app_inv.
    eapply IHΔ'; eauto. constructor; [|constructor].
    simpl.
    rewrite /test_decl /map_decl /= Nat.add_0_r List.length_rev subst_context_length.
    inv X'. unfold test_decl in H0. simpl in H0.
    rewrite List.length_rev Nat.add_0_r in H0.
    rewrite !closedn_subst /= ?H //; eapply closed_upwards; eauto; try lia.
Qed.

Lemma closed_smash_context_gen n (Δ Δ' : context) :
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev Δ) ->
  Alli (fun i d => closed_decl (n + #|Δ| + i) d) 0 (List.rev Δ') ->
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev (smash_context Δ' Δ)).
Proof.
  induction Δ in Δ' |- *.
  intros. simpl. auto.
  simpl. eapply (Alli_impl _ X0). simpl. now rewrite Nat.add_0_r.
  destruct a as [? [] ?]; simpl.
  - intros. eapply Alli_app in X as [X X'].
    eapply IHΔ; eauto.
    inv X'. unfold closed_decl in H. simpl in H.
    rewrite List.length_rev Nat.add_0_r in H.
    clear X1. eapply closed_subst_context; auto.
    now move/andP: H => [].
  - intros. eapply Alli_app in X as [X X'].
    eapply IHΔ; eauto.
    inv X'. unfold closed_decl in H. simpl in H.
    rewrite List.length_rev Nat.add_0_r in H.
    clear X1. rewrite List.rev_app_distr.
    eapply Alli_app_inv; repeat constructor.
    now rewrite Nat.add_0_r /=.
    rewrite List.length_rev /=. clear -X0.
    apply Alli_shift, (Alli_impl _ X0). intros.
    eapply closed_decl_upwards; eauto; lia.
Qed.

Lemma closed_smash_context_unfold n (Δ : context) :
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev Δ) ->
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev (smash_context [] Δ)).
Proof.
  intros; apply (closed_smash_context_gen n _ []); auto. constructor.
Qed.

Lemma closedn_subst_instance_context {k Γ u} :
  closedn_ctx k (subst_instance u Γ) = closedn_ctx k Γ.
Proof.
  rewrite !test_context_k_eq.
  rewrite rev_subst_instance.
  rewrite alli_map.
  apply alli_ext; intros i [? [] ?]; unfold closed_decl, test_decl; cbn.
  all: now rewrite !closedn_subst_instance.
Qed.

Lemma closedn_ctx_spec k Γ : closedn_ctx k Γ <~> Alli (fun k => closed_decl k) k (List.rev Γ).
Proof.
  split.
  - induction Γ as [|d ?].
    + constructor.
    + rewrite closedn_ctx_cons => /andP [clΓ cld].
      simpl in *. eapply Alli_app_inv; simpl; eauto.
      repeat constructor. now rewrite List.length_rev.
  - induction Γ in k |- * => //.
    simpl. move/Alli_app => [clΓ cld].
    simpl. depelim cld. rewrite List.length_rev in i.
    now rewrite i IHΓ.
Qed.

Lemma closedn_smash_context (Γ : context) n :
  closedn_ctx n Γ ->
  closedn_ctx n (smash_context [] Γ).
Proof.
  intros.
  epose proof (closed_smash_context_unfold n Γ).
  apply closedn_ctx_spec. rewrite -(Nat.add_0_r n). apply Alli_shiftn, X.
  apply closedn_ctx_spec in H. rewrite -(Nat.add_0_r n) in H.
  now apply (Alli_shiftn_inv 0 _ n) in H.
Qed.

Definition closed_constructor_body mdecl (b : constructor_body) :=
  closedn_ctx (#|ind_bodies mdecl| + #|ind_params mdecl|) b.(cstr_args) &&
  forallb (closedn (#|ind_bodies mdecl| + #|ind_params mdecl| + #|b.(cstr_args)|)) b.(cstr_indices) &&
  closedn #|ind_bodies mdecl| b.(cstr_type).

Definition closed_inductive_body mdecl idecl :=
  closedn 0 idecl.(ind_type) &&
  closedn_ctx #|mdecl.(ind_params)| idecl.(ind_indices) &&
  forallb (closed_constructor_body mdecl) idecl.(ind_ctors) &&
  forallb (fun x => closedn (S (ind_npars mdecl)) x.(proj_type)) idecl.(ind_projs).

Definition closed_inductive_decl mdecl :=
  closed_ctx (ind_params mdecl) &&
  forallb (closed_inductive_body mdecl) (ind_bodies mdecl).

Set SimplIsCbn.


Lemma closedn_mapi_rec_ext (f g : nat -> context_decl -> context_decl) (l : context) n k' :
  closedn_ctx k' l ->
  (forall k x, n <= k -> k < length l + n ->
    closed_decl (k' + #|l|) x ->
    f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros cl Hfg.
  induction l in n, cl, Hfg |- *; simpl; try congruence.
  intros. rewrite Hfg; simpl; try lia.
  rewrite closedn_ctx_cons in cl.
  move/andP: cl => [cll clr]. eapply closed_decl_upwards; eauto. lia.
  f_equal.
  rewrite IHl; auto.
  rewrite closedn_ctx_cons in cl.
  now move/andP: cl => [].
  intros. apply Hfg. simpl; lia. simpl. lia. simpl.
  eapply closed_decl_upwards; eauto. lia.
Qed.


Lemma closed_declared_ind {Σ ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  closed_inductive_decl mdecl ->
  closed_inductive_body mdecl idecl.
Proof.
  intros [decli hnth] [clpars clbods]%andb_and.
  solve_all.
  now eapply nth_error_all in clbods; eauto.
Qed.


Lemma closedn_ctx_decl {Γ n d k} :
  closedn_ctx k Γ ->
  nth_error Γ n = Some d ->
  closed_decl (k + #|Γ| - S n) d.
Proof.
  intros clΓ hnth. eapply closedn_ctx_spec in clΓ.
  pose proof (nth_error_Some_length hnth).
  rewrite (nth_error_rev _ _ H) in hnth.
  eapply nth_error_alli in clΓ; eauto.
  simpl in clΓ. eapply closed_decl_upwards; eauto. lia.
Qed.

Arguments lift_context _ _ _ : simpl never.
Arguments subst_context _ _ _ : simpl never.

Lemma closedn_ctx_lift n k k' Γ : closedn_ctx k Γ ->
  closedn_ctx (n + k) (lift_context n k' Γ).
Proof.
  induction Γ as [|d ?]; cbn; auto; rewrite lift_context_snoc !closedn_ctx_cons /=;
    move/andP=> [clΓ cld]; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld; rewrite /test_decl. simpl.
  move/andP=> [clb clt]; apply andb_and; split.
  destruct (decl_body d) => /= //. simpl in clb |- *.
  eapply (closedn_lift n) in clb.
  autorewrite with len. now rewrite Nat.add_comm (Nat.add_comm n) Nat.add_assoc.
  eapply (closedn_lift n) in clt.
  autorewrite with len. now rewrite Nat.add_comm (Nat.add_comm n) Nat.add_assoc.
Qed.

Lemma closedn_ctx_subst k k' s Γ :
  closedn_ctx (k + k' + #|s|) Γ ->
  forallb (closedn k) s ->
  closedn_ctx (k + k') (subst_context s k' Γ).
Proof.
  induction Γ as [|d ?] in k' |- *; auto; rewrite subst_context_snoc !closedn_ctx_cons /=;
  move/andP=> [clΓ cld]  cls; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld; rewrite /test_decl. simpl.
  move/andP=> [clb clt]; apply andb_and; split.
  destruct (decl_body d) => /= //. simpl in clb |- *.
  rewrite -Nat.add_assoc [#|s| + _]Nat.add_comm Nat.add_assoc in clb.
  rewrite -(Nat.add_assoc k) in clb.
  eapply (closedn_subst s) in clb => //. rewrite Nat.add_assoc in clb.
  autorewrite with len. now rewrite (Nat.add_comm #|Γ|).
  rewrite -Nat.add_assoc [#|s| + _]Nat.add_comm Nat.add_assoc in clt.
  rewrite -(Nat.add_assoc k) in clt.
  eapply (closedn_subst s) in clt => //. rewrite Nat.add_assoc in clt.
  autorewrite with len. now rewrite (Nat.add_comm #|Γ|).
Qed.

Lemma map_subst_closedn (s : list term) (k : nat) l :
  forallb (closedn k) l -> map (subst s k) l = l.
Proof.
  induction l; simpl; auto.
  move/andP=> [cla cll]. rewrite IHl //.
  now rewrite subst_closedn.
Qed.

Lemma closedn_extended_subst_gen Γ k k' :
  closedn_ctx k Γ ->
  forallb (closedn (k' + k + context_assumptions Γ)) (extended_subst Γ k').
Proof.
  induction Γ as [|[? [] ?] ?] in k, k' |- *; auto; rewrite ?closedn_ctx_cons /=;
   move/andP => [clΓ /andP[clb clt]].
  - rewrite IHΓ //.
    epose proof (closedn_subst (extended_subst Γ k') (k' + k + context_assumptions Γ) 0).
    autorewrite with len in H. rewrite andb_true_r.
    eapply H; auto.
    replace (k' + k + context_assumptions Γ + #|Γ|)
    with (k + #|Γ| + (context_assumptions Γ + k')) by lia.
    eapply closedn_lift. eapply clb.
  - apply andb_and. split.
    * apply Nat.ltb_lt; lia.
    * specialize (IHΓ k (S k') clΓ).
      red. rewrite -IHΓ. f_equal. f_equal. lia.
Qed.

Lemma closedn_extended_subst Γ :
  closed_ctx Γ ->
  forallb (closedn (context_assumptions Γ)) (extended_subst Γ 0).
Proof.
  intros clΓ. now apply (closedn_extended_subst_gen Γ 0 0).
Qed.

Lemma closedn_ctx_expand_lets k Γ Δ :
  closedn_ctx k Γ ->
  closedn_ctx (k + #|Γ|) Δ ->
  closedn_ctx (k + context_assumptions Γ) (expand_lets_ctx Γ Δ).
Proof.
  intros clΓ clΔ.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite -(Nat.add_0_r (k + context_assumptions Γ)).
  eapply closedn_ctx_subst; len; simpl.
  replace (k + context_assumptions Γ + #|Γ|) with (context_assumptions Γ + (k + #|Γ|)) by lia.
  eapply closedn_ctx_lift => //.
  eapply forallb_impl. 2:eapply closedn_extended_subst_gen; eauto.
  simpl; auto.
Qed.

Lemma closed_ctx_expand_lets Γ Δ :
  closed_ctx (Γ ,,, Δ) ->
  closedn_ctx (context_assumptions Γ) (expand_lets_ctx Γ Δ).
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  intros cl.
  pose proof (closedn_ctx_subst (context_assumptions Γ) 0).
  rewrite Nat.add_0_r in H. apply: H.
  - simpl. len.
    rewrite closedn_ctx_lift //.
    rewrite closedn_ctx_app in cl. now move/andP: cl.
  - apply (closedn_extended_subst_gen Γ 0 0).
    rewrite closedn_ctx_app in cl.
    now move/andP: cl => [].
Qed.

#[global]
Hint Rewrite to_extended_list_k_length : len.

Lemma smash_context_subst Δ s n Γ : smash_context (subst_context s (n + #|Γ|) Δ) (subst_context s n Γ) =
  subst_context s n (smash_context Δ Γ).
Proof.
  revert Δ. induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  - now rewrite Nat.add_0_r.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /=. f_equal.
    rewrite !subst_context_alt !mapi_compose.
    apply mapi_ext=> n' x.
    destruct x as [na' [b'|] ty']; simpl.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      + rewrite Nat.add_0_r distr_subst_rec. simpl. lia_f_equal.
      + rewrite Nat.add_0_r distr_subst_rec; simpl. lia_f_equal.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      rewrite Nat.add_0_r distr_subst_rec /=. lia_f_equal.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /= // /subst_decl /map_decl /=.
    f_equal.
    rewrite subst_context_app. simpl.
    rewrite /app_context. f_equal.
    + lia_f_equal.
    + rewrite /subst_context // /fold_context_k /= /map_decl /=.
      lia_f_equal.
Qed.


Lemma smash_context_app_def Γ na b ty :
  smash_context [] (Γ ++ [{| decl_name := na; decl_body := Some b; decl_type := ty |}]) =
  smash_context [] (subst_context [b] 0 Γ).
Proof.
  now rewrite smash_context_app smash_context_acc /= subst_empty lift0_id lift0_context /=
    subst_context_nil app_nil_r (smash_context_subst []).
Qed.

Lemma smash_context_app_ass Γ na ty :
  smash_context [] (Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) =
  smash_context [] Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}].
Proof.
  rewrite smash_context_app smash_context_acc /= subst_context_lift_id //.
  now rewrite lift0_context.
Qed.

Lemma lift_context_add k k' n Γ : lift_context (k + k') n Γ = lift_context k n (lift_context k' n Γ).
Proof.
  induction Γ => //.
  rewrite !lift_context_snoc IHΓ; f_equal.
  destruct a as [na [b|] ty]; rewrite /lift_decl /map_decl /=; simpl; f_equal;
  len; rewrite simpl_lift //; try lia.
Qed.

Lemma distr_lift_subst_context_rec n k s Γ k' : lift_context n (k' + k) (subst_context s k' Γ) =
  subst_context (map (lift n k) s) k' (lift_context n (#|s| + k + k') Γ).
Proof.
  rewrite !lift_context_alt !subst_context_alt.
  rewrite !mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl /subst_decl !compose_map_decl.
  apply map_decl_ext => y. len.
  replace (Nat.pred #|Γ| - n' + (#|s| + k + k'))
    with ((Nat.pred #|Γ| - n' + k') + #|s| + k) by lia.
  rewrite -distr_lift_subst_rec. f_equal. lia.
Qed.

Lemma assumption_context_app_inv Γ Δ : assumption_context Γ -> assumption_context Δ ->
  assumption_context (Γ ++ Δ).
Proof.
  induction 1; cbn; try constructor; auto.
Qed.

Lemma closed_ctx_decl k d Γ : closedn_ctx k (d :: Γ) =
  closed_decl (k + #|Γ|) d && closedn_ctx k Γ.
Proof.
  now simpl; rewrite andb_comm Nat.add_comm.
Qed.

Lemma closedn_ctx_upwards k k' Γ :
  closedn_ctx k Γ -> k <= k' ->
  closedn_ctx k' Γ.
Proof.
  induction Γ; auto. rewrite !closed_ctx_decl /=.
  move/andb_and => [cla clΓ] le.
  rewrite (IHΓ clΓ le).
  rewrite (closed_decl_upwards _ _ cla) //. lia.
Qed.

Lemma closedn_expand_lets k (Γ : context) t :
  closedn (k + context_assumptions Γ) (expand_lets Γ t) ->
  closedn (k + #|Γ|) t.
Proof.
  revert k t.
  induction Γ as [|[na [b|] ty] Γ] using ctx_length_rev_ind; intros k t; simpl; auto.
  - now rewrite /expand_lets /expand_lets_k subst_empty lift0_id.
  - len.
    rewrite !expand_lets_vdef.
    specialize (H (subst_context [b] 0 Γ) ltac:(len; lia)).
    len in H.
    intros cl.
    specialize (H _ _ cl).
    eapply (closedn_subst_eq' _ k) in H.
    simpl in *. now rewrite Nat.add_assoc.
  - len.
    rewrite !expand_lets_vass. simpl. intros cl.
    specialize (H Γ ltac:(len; lia)).
    rewrite (Nat.add_comm _ 1) Nat.add_assoc in cl.
    now rewrite (Nat.add_comm _ 1) Nat.add_assoc.
Qed.


Ltac len' := rewrite_strat (topdown (repeat (old_hints len))).

Tactic Notation "len'" "in" hyp(id) :=
  rewrite_strat (topdown (repeat (old_hints len))) in id.

Lemma closedn_expand_lets_eq k (Γ : context) k' t :
  closedn_ctx k Γ ->
  closedn (k + k' + context_assumptions Γ) (expand_lets_k Γ k' t) =
  closedn (k + k' + #|Γ|) t.
Proof.
  revert k k' t.
  induction Γ as [|[na [b|] ty] Γ] using ctx_length_rev_ind; intros k k' t;
    rewrite ?closedn_ctx_app /= /id /=; simpl; auto.
  - now rewrite /expand_lets /expand_lets_k /= subst_empty lift0_id.
  - move/andb_and=> [cld clΓ]. len'.
    rewrite !expand_lets_k_vdef.
    simpl in cld |- *. move/andb_and: cld => /= [clb _].
    specialize (H (subst_context [b] 0 Γ) ltac:(len; lia)).
    len' in H; simpl in H. len.
    rewrite H /=.
    relativize k. eapply closedn_ctx_subst. simpl. 3:rewrite Nat.add_0_r //.
    now rewrite Nat.add_0_r. now rewrite /= clb.
    rewrite -Nat.add_assoc -closedn_subst_eq. simpl. now rewrite clb.
    simpl; lia_f_equal.
  - len'. move/andb_and => [clty clΓ].
    rewrite !expand_lets_k_vass. simpl.
    specialize (H Γ ltac:(len; lia) (S k)).
    rewrite Nat.add_assoc !Nat.add_succ_r !Nat.add_0_r. apply H.
    now rewrite Nat.add_1_r in clΓ.
Qed.

Lemma closedn_to_extended_list_k_up k Γ k' :
  k' + #|Γ| <= k ->
  forallb (closedn k) (to_extended_list_k Γ k').
Proof.
  move=> le. rewrite /to_extended_list_k.
  eapply Forall_forallb; eauto. 2:{ intros x H; eapply H. }
  eapply Forall_impl. eapply reln_list_lift_above. constructor.
  simpl; intros.
  destruct H as [n [-> leq]]. simpl.
  eapply Nat.ltb_lt. lia.
Qed.

Lemma closedn_to_extended_list_k Γ k :
  forallb (closedn (k + #|Γ|)) (to_extended_list_k Γ k).
Proof.
  now apply closedn_to_extended_list_k_up.
Qed.

Lemma closedn_to_extended_list Γ :
  forallb (closedn #|Γ|) (to_extended_list Γ).
Proof.
  rewrite /to_extended_list.
  apply (closedn_to_extended_list_k _ 0).
Qed.

Lemma closed_ind_predicate_context {Σ ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  closed_inductive_decl mdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (ind_predicate_context ind mdecl idecl).
Proof.
  intros decli cl.
  move: (closed_declared_ind decli cl).
  move/andP: cl => [] clpars _.
  move/andP => [] /andP [] /andP [] clty clinds _ _.
  rewrite /ind_predicate_context /=.
  apply/andP. split.
  - now eapply (closedn_ctx_expand_lets 0).
  - rewrite /test_decl /=; len.
    rewrite closedn_mkApps /= //.
    set foo := (X in forallb X _).
    relativize foo.
    eapply closedn_to_extended_list.
    now rewrite /foo; len.
Qed.

Lemma closed_inds {ind mdecl u} :
  forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  rewrite inds_spec. rewrite forallb_rev.
  unfold mapi.
  generalize 0 at 2.
  induction (ind_bodies mdecl); simpl; auto.
Qed.


Lemma closed_ind_closed_cstrs {Σ ind mdecl idecl} :
  closed_inductive_decl mdecl ->
  declared_inductive Σ ind mdecl idecl ->
  All (closed_constructor_body mdecl) (ind_ctors idecl).
Proof.
  intros []%andb_and.
  intros [decli hnth].
  solve_all. eapply nth_error_all in H0; tea.
  simpl in H0.
  move/andP: H0 => [] /andP []; solve_all.
Qed.


Lemma closed_ctx_app Γ Δ :
  closed_ctx (Γ ,,, Δ) ->
  closedn_ctx #|Γ| Δ.
Proof.
  rewrite PCUICClosed.test_context_k_app=> /andP [//].
Qed.

