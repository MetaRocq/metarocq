(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICPrimitive PCUICAst PCUICOnOne PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICCumulativity
  PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef PCUICWeakeningEnvConv
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars PCUICGuardCondition
  PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICViews
  PCUICTyping.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".

Lemma isConstruct_app_rename r t :
  isConstruct_app t = isConstruct_app (rename r t).
Proof.
  unfold isConstruct_app. unfold decompose_app. generalize (@nil term) at 1.
  change (@nil term) with (map (rename r) []). generalize (@nil term).
  induction t; simpl; auto.
  intros l l0. specialize (IHt1 (t2 :: l) (t2 :: l0)).
  now rewrite IHt1.
Qed.

Lemma is_constructor_rename x l r : is_constructor x l = is_constructor x (map (rename r) l).
Proof.
  rewrite /is_constructor nth_error_map.
  elim: nth_error_spec => //.
  move=> n hnth xl /=.
  now apply isConstruct_app_rename.
Qed.

Lemma isFixLambda_app_rename r t : ~~ isFixLambda_app t -> ~~ isFixLambda_app (rename r t).
Proof.
  induction t; simpl; auto.
  destruct t1; simpl in *; auto.
Qed.

Lemma construct_cofix_rename r t : discr_construct_cofix t -> discr_construct_cofix (rename r t).
Proof.
  destruct t; simpl; try congruence.
Qed.

Lemma rename_mkApps :
  forall f t l,
    rename f (mkApps t l) = mkApps (rename f t) (map (rename f) l).
Proof.
  intros f t l.
  autorewrite with sigma. f_equal.
Qed.

Lemma decompose_app_rec_rename r t l :
  forall hd args,
  decompose_app_rec t l = (hd, args) ->
  decompose_app_rec (rename r t) (map (rename r) l) = (rename r hd, map (rename r) args).
Proof.
  induction t in l |- *; simpl; try intros hd args [= <- <-]; auto.
  intros hd args e. now apply (IHt1 _ _ _ e).
Qed.

Lemma decompose_app_rename {r t hd args} :
  decompose_app t = (hd, args) ->
  decompose_app (rename r t) = (rename r hd, map (rename r) args).
Proof. apply decompose_app_rec_rename. Qed.

Lemma rename_subst_instance :
  forall u t f,
    rename f (subst_instance u t) = subst_instance u (rename f t).
Proof.
  intros u t f.
  rewrite /subst_instance /=.
  induction t in f |- * using term_forall_list_ind.
  all: try solve [
    simpl ;
    rewrite ?IHt ?IHt1 ?IHt2 ;
    easy
  ].
  - simpl. f_equal. induction X.
    + reflexivity.
    + simpl. f_equal ; easy.
  - simpl. rewrite IHt. f_equal.
    * unfold map_predicate, rename_predicate; destruct p; simpl; f_equal; solve_all.
    * induction X0.
      + reflexivity.
      + simpl. f_equal. 2: easy.
        destruct x. unfold rename_branch, map_branch. simpl in *.
        f_equal; solve_all.
  - simpl. f_equal.
    rewrite length_map.
    generalize #|m|. intro k.
    induction X. 1: reflexivity.
    destruct p, x. unfold map_def in *.
    simpl in *. f_equal. all: easy.
  - simpl. f_equal.
    rewrite length_map.
    generalize #|m|. intro k.
    induction X. 1: reflexivity.
    destruct p, x. unfold map_def in *.
    simpl in *. f_equal. all: easy.
  - simpl. f_equal. solve_all.
Qed.

Lemma rename_context_snoc0 :
  forall f Γ d,
    rename_context f (d :: Γ) =
    rename_context f Γ ,, rename_decl (shiftn #|Γ| f) d.
Proof.
  intros f Γ d.
  unfold rename_context. now rewrite fold_context_k_snoc0.
Qed.
#[global]
Hint Rewrite rename_context_snoc0 : sigma.

Lemma rename_context_snoc r Γ d : rename_context r (Γ ,, d) = rename_context r Γ ,, map_decl (rename (shiftn #|Γ| r)) d.
Proof.
  unfold snoc. apply rename_context_snoc0.
Qed.
#[global]
Hint Rewrite rename_context_snoc : sigma.

Lemma rename_context_alt r Γ :
  rename_context r Γ =
  mapi (fun k' d => map_decl (rename (shiftn (Nat.pred #|Γ| - k') r)) d) Γ.
Proof.
  unfold rename_context. apply: fold_context_k_alt.
Qed.


Lemma rename_context_telescope r Γ : List.rev (rename_context r Γ) = rename_telescope r (List.rev Γ).
Proof.
  rewrite !rename_context_alt /rename_telescope.
  rewrite mapi_rev.
  f_equal. apply mapi_ext => k' d.
  apply map_decl_ext => t. lia_f_equal.
Qed.

Lemma rename_subst0 :
  forall f l t,
    rename f (subst0 l t) =
    subst0 (map (rename f) l) (rename (shiftn #|l| f) t).
Proof.
  intros f l t.
  autorewrite with sigma.
  eapply inst_ext.
  now rewrite -ren_shiftn up_Upn Upn_comp; len.
Qed.

Lemma rename_subst10 :
  forall f t u,
    rename f (t{ 0 := u }) = (rename (shiftn 1 f) t){ 0 := rename f u }.
Proof.
  intros f t u.
  eapply rename_subst0.
Qed.

Lemma rename_context_nth_error :
  forall f Γ i decl,
    nth_error Γ i = Some decl ->
    nth_error (rename_context f Γ) i =
    Some (rename_decl (shiftn (#|Γ| - S i) f) decl).
Proof.
  intros f Γ i decl h.
  induction Γ in f, i, decl, h |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in h. inversion h. subst. clear h.
      rewrite rename_context_snoc0. simpl.
      f_equal. f_equal. f_equal. lia.
    + simpl in h. rewrite rename_context_snoc0. simpl.
      eapply IHΓ. eassumption.
Qed.

Lemma rename_context_decl_body :
  forall f Γ i body,
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    option_map decl_body (nth_error (rename_context f Γ) i) =
    Some (Some (rename (shiftn (#|Γ| - S i) f) body)).
Proof.
  intros f Γ i body h.
  destruct (nth_error Γ i) eqn: e. 2: discriminate.
  simpl in h.
  eapply rename_context_nth_error with (f := f) in e. rewrite e. simpl.
  destruct c as [na bo ty]. simpl in h. inversion h. subst.
  simpl. reflexivity.
Qed.

Lemma map_vass_map_def g l r :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (rename r) g) l)) =
  (mapi (fun i d => map_decl (rename (shiftn i r)) d)
        (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  sigma. rewrite -Upn_ren. now rewrite shiftn_Upn.
Qed.

Lemma rename_fix_context r :
  forall (mfix : list (def term)),
    fix_context (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix) =
    rename_context r (fix_context mfix).
Proof.
  intros mfix. unfold fix_context.
  rewrite map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (rename_context_alt r (fix_context mfix)).
  unfold map_decl. now rewrite mapi_length fix_context_length.
Qed.

Section Renaming.

Context `{cf : checker_flags}.

Lemma eq_term_upto_univ_rename Σ cmp_universe cmp_sort pb napp u v f :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp u v ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (rename f u) (rename f v).
Proof using Type.
  intros h.
  induction u in v, napp, pb, f, h |- * using term_forall_list_ind.
  all: dependent destruction h.
  all: try solve [
    simpl ; constructor ; eauto
  ].
  - simpl. constructor.
    induction X in a, args' |- *.
    + inversion a. constructor.
    + inversion a. subst. simpl. constructor.
      all: eauto.
  - simpl. constructor. all: eauto.
    * rewrite /rename_predicate.
      destruct X; destruct e as [? [? [ectx ?]]].
      rewrite (All2_length ectx). red.
      intuition auto; simpl; solve_all.
    * red in X0. unfold eq_branches, eq_branch in *. solve_all.
      rewrite -(All2_length a1).
      now eapply b0.
  - simpl. constructor. unfold eq_mfixpoint in *.
    apply All2_length in e as eq. rewrite <- eq.
    generalize #|m|. intro k.
    solve_all.
  - simpl. constructor. unfold eq_mfixpoint in *.
    apply All2_length in e as eq. rewrite <- eq.
    generalize #|m|. intro k.
    solve_all.
  - simpl. constructor.
    eapply onPrims_map_prop; tea. cbn; intuition eauto.
Qed.

Lemma urenaming_impl :
  forall (P P' : nat -> bool) Γ Δ f,
    (forall i, P' i -> P i) ->
    urenaming P Δ Γ f ->
    urenaming P' Δ Γ f.
Proof using Type.
  intros P P' Γ Δ f hP h.
  intros i decl p e.
  specialize (h i decl (hP _ p) e) as [decl' [h1 [h2 h3]]].
  exists decl'. split ; [| split ]; eauto.
Qed.

Lemma inst_closed σ k t : closedn k t -> t.[⇑^k σ] = t.
Proof using Type.
  intros Hs.
  induction t in σ, k, Hs |- * using term_forall_list_ind; intros; sigma;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_branch_map_branch,
      ?length_map, ?Nat.add_assoc in *;
      unfold test_def, map_branch, test_branch_k, test_predicate_k in *; simpl in *; eauto with all;
    simpl closed in *; repeat (rtoProp; f_equal; solve_all); try change_Sk.

  - revert Hs.
    unfold Upn.
    elim (Nat.ltb_spec n k) => //; intros; simpl in *.
    now apply subst_idsn_consn_lt.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt3 σ (S k) H0). rewrite -{2}IHt3. now sigma.
  - eapply map_predicate_shift_id_spec.
    * solve_all.
    * solve_all.
    * setoid_rewrite up_Upn; setoid_rewrite <- Upn_Upn.
      fold (shiftf (fun k => inst (⇑^k σ)) k). simpl; solve_all.
  - rtoProp. specialize (b0 σ (#|bcontext x| + k) H4).
    revert b0. now sigma.
  - rtoProp. specialize (b0 σ (#|m| + k) H0).
    revert b0. now sigma.
  - rewrite -Upn_Upn. eauto.
Qed.

Lemma rename_closedn :
  forall f n t,
    closedn n t ->
    rename (shiftn n f) t = t.
Proof using Type.
  intros f n t e.
  autorewrite with sigma.
  erewrite <- inst_closed with (σ := ren f) by eassumption.
  eapply inst_ext. intro i.
  unfold ren, shiftn, Upn, subst_consn, subst_compose, shift, shiftk.
  rewrite idsn_length.
  destruct (Nat.ltb_spec i n).
  - rewrite nth_error_idsn_Some. all: auto.
  - rewrite nth_error_idsn_None. 1: lia.
    simpl. reflexivity.
Qed.

Lemma rename_closed :
  forall f t,
    closed t ->
    rename f t = t.
Proof using Type.
  intros f t h.
  replace (rename f t) with (rename (shiftn 0 f) t).
  - apply rename_closedn. assumption.
  - now sigma.
Qed.

Lemma rename_closed_decl k f d : closed_decl k d -> map_decl (rename (shiftn k f)) d = d.
Proof using Type.
  rewrite /map_decl.
  destruct d as [? [] ?] => /=.
  - move/andP=> [] clt clty.
    rewrite !rename_closedn //.
  - move=> clt. rewrite !rename_closedn //.
Qed.

Lemma rename_closedn_ctx f n Γ :
  closedn_ctx n Γ ->
  rename_context (shiftn n f) Γ = Γ.
Proof using Type.
  rewrite test_context_k_eq /rename_context.
  apply alli_fold_context_k.
  intros. rewrite shiftn_add.
  intros. apply rename_closed_decl.
  now rewrite Nat.add_comm.
Qed.

Lemma rename_closedn_terms f n ts :
  forallb (closedn n) ts -> map (rename (shiftn n f)) ts = ts.
Proof using Type.
  solve_all. now apply rename_closedn.
Qed.

Lemma rename_closed_extended_subst f Γ :
  closed_ctx Γ ->
  map (rename (shiftn (context_assumptions Γ) f)) (extended_subst Γ 0) = extended_subst Γ 0.
Proof using Type.
  intros cl. apply rename_closedn_terms.
  now apply (closedn_extended_subst_gen Γ 0 0).
Qed.

Arguments Nat.sub !_ !_.

Lemma urenaming_vass :
  forall P Γ Δ na A f,
    urenaming P Γ Δ f ->
    urenaming (shiftnP 1 P) (Γ ,, vass na A) (Δ ,, vass na (rename f A)) (shiftn 1 f).
Proof using Type.
  intros P Γ Δ na A f h. unfold urenaming in *.
  intros [|i] decl hP e.
  - simpl in e. inversion e. subst. clear e.
    simpl. eexists. split. 1: reflexivity.
    repeat split.
    now sigma.
  - simpl in e. simpl.
    replace (i - 0) with i by lia.
    eapply h in e as [decl' [? [? [h1 h2]]]].
    2:{ unfold shiftnP in hP. simpl in hP. now rewrite Nat.sub_0_r in hP. }
    eexists. split. 1: eassumption.
    repeat split.
    + tas.
    + setoid_rewrite shiftn_1_S.
      rewrite -rename_compose h1.
      now sigma.
    + move: h2.
      destruct (decl_body decl) => /= //; destruct (decl_body decl') => /= //.
      setoid_rewrite shiftn_1_S => [=] h2.
      now rewrite -rename_compose h2; sigma.
Qed.


Lemma urenaming_vdef :
  forall P Γ Δ na b B f,
    urenaming P Γ Δ f ->
    urenaming (shiftnP 1 P) (Γ ,, vdef na b B) (Δ ,, vdef na (rename f b) (rename f B)) (shiftn 1 f).
Proof using Type.
  intros P Γ Δ na b B f h. unfold urenaming in *.
  intros [|i] decl hP e.
  - simpl in e. inversion e. subst. clear e.
    simpl. eexists. split. 1: reflexivity.
    repeat split.
    + now sigma.
    + simpl. now sigma.
  - simpl in e. simpl.
    replace (i - 0) with i by lia.
    eapply h in e as [decl' [? [? [h1 h2]]]].
    2:{ rewrite /shiftnP /= Nat.sub_0_r // in hP. }
    eexists. split. 1: eassumption.
    repeat split => //.
    + setoid_rewrite shiftn_1_S.
      rewrite -rename_compose h1.
      now sigma.
    + move: h2.
      destruct (decl_body decl) => /= //; destruct (decl_body decl') => /= //.
      setoid_rewrite shiftn_1_S => [=] h2.
      now rewrite -rename_compose h2; sigma.
Qed.

Lemma urenaming_ext :
  forall P P' Γ Δ f g,
    P ≐1 P' ->
    f ≐1 g ->
    urenaming P Δ Γ f ->
    urenaming P' Δ Γ g.
Proof using Type.
  intros P P' Γ Δ f g hP hfg h.
  intros i decl p e.
  rewrite <-hP in p.
  specialize (h i decl p e) as [decl' [? [h1 [h2 h3]]]].
  exists decl'. repeat split => //.
  - rewrite <- (hfg i). assumption.
  - rewrite <- (hfg i). rewrite <- h2.
    eapply rename_ext. intros j. symmetry. apply hfg.
  - move: h3. destruct (decl_body decl) => /= //.
    rewrite /rshiftk.
    destruct (decl_body decl') => /= //.
    intros [=]; f_equal.
    now setoid_rewrite <- (hfg _).
Qed.

Lemma renaming_extP P P' Σ Γ Δ f :
  P ≐1 P' ->
  renaming P Σ Γ Δ f -> renaming P' Σ Γ Δ f.
Proof using Type.
  intros hP; rewrite /renaming.
  intros []; split; eauto.
  eapply urenaming_ext; eauto. reflexivity.
Qed.

Lemma urenaming_context :
  forall P Γ Δ Ξ f,
    urenaming P Γ Δ f ->
    urenaming (shiftnP #|Ξ| P) (Γ ,,, Ξ) (Δ ,,, rename_context f Ξ) (shiftn #|Ξ| f).
Proof using Type.
  intros P Γ Δ Ξ f h.
  induction Ξ as [| [na [bo|] ty] Ξ ih] in Γ, Δ, f, h |- *.
  - simpl. eapply urenaming_ext. 3: eassumption.
    * now rewrite shiftnP0.
    * intros []. all: reflexivity.
  - simpl. rewrite rename_context_snoc.
    rewrite app_context_cons. simpl. unfold rename_decl. unfold map_decl. simpl.
    eapply urenaming_ext.
    3:{ eapply urenaming_vdef; tea. eapply ih; assumption. }
    * now rewrite shiftnP_add.
    * now rewrite shiftn_add.
  - simpl. rewrite rename_context_snoc.
    rewrite app_context_cons. simpl. unfold rename_decl. unfold map_decl. simpl.
    eapply urenaming_ext.
    3:{eapply urenaming_vass; tea. eapply ih; assumption. }
    * now rewrite shiftnP_add.
    * now rewrite shiftn_add.
Qed.

Definition rename_branch := (map_branch_shift rename shiftn).

(* TODO MOVE *)
Lemma isLambda_rename :
  forall t f,
    isLambda t ->
    isLambda (rename f t).
Proof using Type.
  intros t f h.
  destruct t.
  all: try discriminate.
  simpl. reflexivity.
Qed.

(* TODO MOVE *)
Lemma rename_unfold_fix :
  forall mfix idx narg fn f,
    unfold_fix mfix idx = Some (narg, fn) ->
    unfold_fix (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix) idx
    = Some (narg, rename f fn).
Proof using Type.
  intros mfix idx narg fn f h.
  unfold unfold_fix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h. clear h.
  simpl.
  f_equal. f_equal.
  rewrite rename_subst0. rewrite fix_subst_length.
  f_equal.
  unfold fix_subst. rewrite length_map.
  generalize #|mfix| at 2 3. intro n.
  induction n.
  - reflexivity.
  - simpl.
    f_equal. rewrite IHn. reflexivity.
Qed.

(* TODO MOVE *)
Lemma rename_unfold_cofix :
  forall mfix idx narg fn f,
    unfold_cofix mfix idx = Some (narg, fn) ->
    unfold_cofix (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix) idx
    = Some (narg, rename f fn).
Proof using Type.
  intros mfix idx narg fn f h.
  unfold unfold_cofix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h.
  simpl. f_equal. f_equal.
  rewrite rename_subst0. rewrite cofix_subst_length.
  f_equal.
  unfold cofix_subst. rewrite length_map.
  generalize #|mfix| at 2 3. intro n.
  induction n.
  - reflexivity.
  - simpl.
    f_equal. rewrite IHn. reflexivity.
Qed.

Definition rename_constructor_body mdecl f c :=
  map_constructor_body #|mdecl.(ind_params)| #|mdecl.(ind_bodies)|
   (fun k => rename (shiftn k f)) c.

(* TODO move *)
Lemma map2_set_binder_name_fold bctx f Γ :
  #|bctx| = #|Γ| ->
  map2 set_binder_name bctx (fold_context_k f Γ) =
  fold_context_k f (map2 set_binder_name bctx Γ).
Proof using Type.
  intros hl.
  rewrite !fold_context_k_alt mapi_map2 -{1}(map_id bctx).
  rewrite -mapi_cst_map map2_mapi.
  rewrite map2_length; len => //.
  eapply map2i_ext => i x y.
  rewrite hl.
  destruct y; reflexivity.
Qed.

Lemma rename_subst :
  forall f s n t,
    rename (shiftn n f) (subst s n t) =
    subst (map (rename f) s) n (rename (shiftn n (shiftn #|s| f)) t).
Proof using Type.
  intros f s n t.
  autorewrite with sigma.
  eapply inst_ext. intro i. unfold Upn.
  unfold ren, subst_consn, shiftn, subst_compose. simpl.
  rewrite nth_error_map.
  destruct (Nat.ltb_spec i n).
  - rewrite idsn_lt //. simpl.
    destruct (Nat.ltb_spec i n) => //. lia.
  - rewrite nth_error_idsn_None //.
    destruct (Nat.ltb_spec (i - n) #|s|).
    * rewrite nth_error_idsn_None //; try lia.
      len.
      replace (n + (i - n) - n) with (i - n) by lia.
      destruct nth_error eqn:hnth => /=.
      ** sigma. apply inst_ext.
        intros k. cbn.
        elim: (Nat.ltb_spec (n + k) n); try lia.
        intros. eapply nth_error_Some_length in hnth.
        unfold shiftk. lia_f_equal.
      ** eapply nth_error_None in hnth. lia.
    * len.
      replace (n + (#|s| + f (i - n - #|s|)) - n) with
        (#|s| + f (i - n - #|s|)) by lia.
      rewrite nth_error_idsn_None; try lia.
      destruct nth_error eqn:hnth.
      ** eapply nth_error_Some_length in hnth. lia.
      ** simpl.
        eapply nth_error_None in hnth.
        destruct nth_error eqn:hnth'.
        + eapply nth_error_Some_length in hnth'. lia.
        + simpl. unfold shiftk.
          case: Nat.ltb_spec; try lia.
          intros. lia_f_equal.
          assert (n + (i - n - #|s|) - n = (i - n - #|s|)) as -> by lia.
          lia.
Qed.

Lemma rename_context_subst f s Γ :
  rename_context f (subst_context s 0 Γ) =
  subst_context (map (rename f) s) 0 (rename_context (shiftn #|s| f) Γ).
Proof using Type.
  rewrite !rename_context_alt !subst_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /subst_decl !compose_map_decl.
  apply map_decl_ext => t.
  len.
  generalize (Nat.pred #|Γ| - i).
  intros.
  now rewrite rename_subst.
Qed.

Lemma rename_shiftnk :
  forall f n k t,
    rename (shiftn (n + k) f) (lift n k t) = lift n k (rename (shiftn k f) t).
Proof using Type.
  intros f n k t.
  rewrite !lift_rename.
  autorewrite with sigma.
  rewrite - !Upn_ren. sigma.
  rewrite Upn_compose.
  rewrite -Upn_Upn Nat.add_comm Upn_Upn Upn_compose.
  now rewrite shiftn_Upn.
Qed.

Lemma rename_context_lift f n k Γ :
  rename_context (shiftn (n + k) f) (lift_context n k Γ) =
  lift_context n k (rename_context (shiftn k f) Γ).
Proof using Type.
  rewrite !rename_context_alt !lift_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /lift_decl !compose_map_decl.
  apply map_decl_ext => t; len.
  generalize (Nat.pred #|Γ| - i).
  intros.
  rewrite shiftn_add.
  rewrite (Nat.add_comm n k) Nat.add_assoc Nat.add_comm.
  now rewrite rename_shiftnk shiftn_add.
Qed.

Lemma rename_inds f ind pu bodies : map (rename f) (inds ind pu bodies) = inds ind pu bodies.
Proof using Type.
  unfold inds.
  induction #|bodies|; simpl; auto. f_equal.
  apply IHn.
Qed.


End Renaming.

#[global] Instance rename_context_ext : Proper (`≐1` ==> Logic.eq ==> Logic.eq) rename_context.
Proof.
  intros f g Hfg x y ->.
  apply fold_context_k_ext => i t.
  now rewrite Hfg.
Qed.


Section Renaming2.

Context `{cf : checker_flags}.


Lemma rename_context_subst_instance f u Γ :
  rename_context f (subst_instance u Γ) =
  subst_instance u (rename_context f Γ).
Proof using Type. unfold rename_context.
  rewrite fold_context_k_map // [subst_instance _ _]map_fold_context_k.
  now setoid_rewrite rename_subst_instance.
Qed.

Lemma rename_context_subst_k f s k Γ :
  rename_context (shiftn k f) (subst_context s k Γ) =
  subst_context (map (rename f) s) k (rename_context (shiftn (k + #|s|) f) Γ).
Proof using Type.
  rewrite /rename_context /subst_context.
  rewrite !fold_context_k_compose.
  apply fold_context_k_ext => i t.
  rewrite shiftn_add.
  now rewrite rename_subst !shiftn_add Nat.add_assoc.
Qed.

Lemma rename_cstr_args mdecl f cdecl :
  cstr_args (rename_constructor_body mdecl f cdecl) =
  rename_context (shiftn (#|mdecl.(ind_params)| + #|ind_bodies mdecl|) f) (cstr_args cdecl).
Proof using Type.
  simpl. unfold rename_context.
  apply fold_context_k_ext => i t.
  now rewrite shiftn_add Nat.add_assoc.
Qed.

Lemma rename_reln f ctx n acc :
  forallb (closedn (n + #|ctx|)) acc ->
  map (rename (shiftn (n + #|ctx|) f)) (reln acc n ctx) =
  reln acc n ctx.
Proof using Type.
  induction ctx in n, acc |- *; simpl; auto.
  - intros clacc. solve_all. now rewrite rename_closedn.
  - intros clacc.
    destruct a as [? [] ?].
    * rewrite Nat.add_succ_r.
      change (S (n + #|ctx|)) with (S n + #|ctx|).
      rewrite Nat.add_1_r IHctx // /= -Nat.add_succ_r //.
    * rewrite Nat.add_succ_r Nat.add_1_r. rewrite (IHctx (S n)) /= // -Nat.add_succ_r //.
      simpl. rewrite clacc andb_true_r.
      eapply Nat.ltb_lt. lia.
Qed.

Lemma rename_to_extended_list f ctx :
  map (rename (shiftn #|ctx| f)) (to_extended_list ctx) = to_extended_list ctx.
Proof using Type.
  unfold to_extended_list, to_extended_list_k.
  now apply (rename_reln _ _ 0).
Qed.

Lemma to_extended_list_rename f ctx :
  to_extended_list (rename_context f ctx) = to_extended_list ctx.
Proof using Type.
  unfold to_extended_list, to_extended_list_k.
  now rewrite (reln_fold _ _ 0).
Qed.

Lemma rename_context_set_binder_name f ctx ctx' :
  #|ctx| = #|ctx'| ->
  rename_context f (map2 set_binder_name ctx ctx') =
  map2 set_binder_name ctx (rename_context f ctx').
Proof using Type.
  induction ctx in ctx' |- *; destruct ctx'; simpl; auto.
  rewrite !rename_context_snoc /= /snoc.
  intros [=]. f_equal; auto.
  rewrite /set_binder_name /map_decl /=; f_equal.
  - rewrite map2_length // H0 //.
  - rewrite map2_length // H0 //.
Qed.

Lemma rename_inst_case_context f pars puinst ctx :
  rename_context f (inst_case_context pars puinst ctx) =
  inst_case_context (map (rename f) pars) puinst
    (rename_context (shiftn #|pars| f) ctx).
Proof using Type.
  rewrite /inst_case_context.
  now rewrite rename_context_subst map_rev rename_context_subst_instance; len.
Qed.

Lemma rename_inst_case_context_wf f pars puinst ctx :
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pars| ctx ->
  rename_context f (inst_case_context pars puinst ctx) =
    inst_case_context (map (rename f) pars) puinst ctx.
Proof using Type.
  rewrite test_context_k_closed_on_free_vars_ctx => H.
  rewrite rename_inst_case_context. f_equal.
  now rewrite rename_closedn_ctx // closedn_ctx_on_free_vars.
Qed.

Lemma rename_cstr_branch_context f ind mdecl cdecl :
  closed_ctx (ind_params mdecl) ->
  rename_context (shiftn (context_assumptions (ind_params mdecl)) f) (cstr_branch_context ind mdecl cdecl) =
  cstr_branch_context ind mdecl (rename_constructor_body mdecl f cdecl).
Proof using Type.
  intros clctx.
  rewrite /cstr_branch_context.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite rename_context_subst.
  rewrite rename_closed_extended_subst //. f_equal.
  rewrite shiftn_add Nat.add_comm. len.
  rewrite rename_context_lift. f_equal.
  rewrite rename_context_subst_k rename_inds /=; len.
  setoid_rewrite <-Nat.add_assoc.
  now setoid_rewrite <-shiftn_add at 2.
Qed.

Lemma rename_case_branch_context_gen ind mdecl f p bctx cdecl :
  closed_ctx (ind_params mdecl) ->
  #|bctx| = #|cstr_args cdecl| ->
  #|pparams p| = context_assumptions (ind_params mdecl) ->
  rename_context f (case_branch_context ind mdecl p bctx cdecl) =
  case_branch_context ind mdecl (rename_predicate f p) bctx
    (rename_constructor_body mdecl f cdecl).
Proof using Type.
  intros clpars. unfold case_branch_context, case_branch_context_gen, pre_case_branch_context_gen.
  cbn -[fold_context_k].
  intros hlen hlen'.
  rewrite rename_context_set_binder_name; len => //. f_equal.
  rewrite rename_inst_case_context; f_equal.
  rewrite hlen' rename_cstr_branch_context //.
Qed.

Lemma forget_types_mapi_context (f : nat -> term -> term) (ctx : context) :
  forget_types (mapi_context f ctx) = forget_types ctx.
Proof using Type.
  now rewrite /forget_types map_mapi_context /= mapi_cst_map.
Qed.

Lemma forget_types_map_context (f : term -> term) (ctx : context) :
  forget_types (map_context f ctx) = forget_types ctx.
Proof using Type.
  now rewrite /forget_types map_map_compose.
Qed.

Lemma rename_closed_constructor_body mdecl cdecl f :
  closed_constructor_body mdecl cdecl ->
  rename_constructor_body mdecl f cdecl = cdecl.
Proof using Type.
  rewrite /closed_constructor_body /rename_constructor_body /map_constructor_body.
  move/andP=> [] /andP [] clctx clind clty.
  destruct cdecl; cbn -[fold_context_k] in *; f_equal.
  + move: clctx. rewrite test_context_k_eq.
    apply alli_fold_context_k => i d cldecl.
    rewrite rename_closed_decl //.
    red; rewrite -cldecl; lia_f_equal.
  + solve_all. rewrite rename_closedn //.
    red; rewrite -H. lia_f_equal.
  + now rewrite rename_closedn.
Qed.

Lemma rename_mkLambda_or_LetIn f d t :
  rename f (mkLambda_or_LetIn d t) =
  mkLambda_or_LetIn (rename_decl f d) (rename (shiftn 1 f) t).
Proof using Type.
  destruct d as [na [] ty]; rewrite /= /mkLambda_or_LetIn /=; f_equal.
Qed.

Lemma rename_it_mkLambda_or_LetIn f ctx t :
  rename f (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (rename_context f ctx) (rename (shiftn #|ctx| f) t).
Proof using Type.
  move: t.
  induction ctx; simpl => t.
  - now rewrite shiftn0.
  - rewrite /= IHctx rename_context_snoc /snoc /=. f_equal.
    now rewrite rename_mkLambda_or_LetIn /= shiftn_add; len.
Qed.

Lemma rename_mkProd_or_LetIn f d t :
  rename f (mkProd_or_LetIn d t) =
  mkProd_or_LetIn (rename_decl f d) (rename (shiftn 1 f) t).
Proof using Type.
  destruct d as [na [] ty]; rewrite /= /mkProd_or_LetIn /=; f_equal.
Qed.

Lemma rename_it_mkProd_or_LetIn f ctx t :
  rename f (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (rename_context f ctx) (rename (shiftn #|ctx| f) t).
Proof using Type.
  move: t.
  induction ctx; simpl => t.
  - now rewrite shiftn0.
  - rewrite /= IHctx rename_context_snoc /snoc /=. f_equal.
    now rewrite rename_mkProd_or_LetIn /= shiftn_add; len.
Qed.

Lemma rename_wf_predicate mdecl idecl f p :
  wf_predicate mdecl idecl p ->
  wf_predicate mdecl idecl (rename_predicate f p).
Proof using Type.
  intros []. split => //. now len.
Qed.

Lemma rename_wf_branch cdecl f br :
  wf_branch cdecl br ->
  wf_branch cdecl (rename_branch f br).
Proof using Type. intros x; exact x. Qed.

Lemma rename_wf_branches cdecl f brs :
  wf_branches cdecl brs ->
  wf_branches cdecl (map (rename_branch f) brs).
Proof using Type.
  unfold wf_branches, wf_branches_gen.
  intros h. solve_all.
Qed.

Lemma rename_compose f f' x : rename f (rename f' x) = rename (f ∘ f') x.
Proof using Type. now rewrite (rename_compose _ _ _). Qed.

Lemma rename_predicate_set_pparams f p params :
  rename_predicate f (set_pparams p params) =
  set_pparams (rename_predicate f p) (map (rename f) params).
Proof using Type. reflexivity. Qed.

(* Lemma rename_predicate_set_pcontext f p pcontext' :
  #|pcontext'| = #|p.(pcontext)| ->
  rename_predicate f (set_pcontext p pcontext') =
  set_pcontext (rename_predicate f p)
  (mapi_context (fun k => rename (shiftn k f)) pcontext').
Proof. rewrite /rename_predicate /= /set_pcontext. simpl. intros ->. reflexivity. Qed. *)

Lemma rename_predicate_set_preturn f p pret :
  rename_predicate f (set_preturn p pret) =
  set_preturn (rename_predicate f p) (rename (shiftn #|pcontext p| f) pret).
Proof using Type. reflexivity. Qed.

Lemma rename_extended_subst f Γ :
  map (rename (shiftn (context_assumptions Γ) f)) (extended_subst Γ 0) = extended_subst (rename_context f Γ) 0.
Proof using Type.
  induction Γ as [|[na [b|] ty] Γ]; auto; rewrite rename_context_snoc /=; len.
  - rewrite rename_subst0.
    rewrite IHΓ. len. f_equal. f_equal.
    now rewrite shiftn_add Nat.add_comm rename_shiftnk.
  - f_equal; auto.
    rewrite !(lift_extended_subst _ 1).
    rewrite map_map_compose.
    setoid_rewrite <- (shiftn_add 1 (context_assumptions Γ)).
    setoid_rewrite rename_shiftn.
    rewrite -map_map_compose. now f_equal.
Qed.

Lemma rename_iota_red :
  forall f p pars args br,
  #|skipn pars args| = context_assumptions br.(bcontext) ->
  closedn_ctx #|pparams p| br.(bcontext) ->
  rename f (iota_red pars p args br) =
  iota_red pars (rename_predicate f p) (map (rename f) args) (rename_branch f br).
Proof using Type.
  intros f p pars args br hlen hlen'.
  unfold iota_red.
  rewrite rename_subst0 map_rev map_skipn. f_equal.
  rewrite List.length_rev /expand_lets /expand_lets_k.
  rewrite rename_subst0. len.
  rewrite shiftn_add -hlen Nat.add_comm rename_shiftnk.
  rewrite hlen.
  relativize (context_assumptions _); [erewrite rename_extended_subst|now len].
  f_equal. f_equal.
  rewrite rename_inst_case_context. f_equal. f_equal.
  rewrite /inst_case_branch_context.
  now rewrite rename_closedn_ctx.
Qed.

Lemma red1_rename :
  forall P Σ Γ Δ u v f,
    wf Σ ->
    urenaming P Γ Δ f ->
    on_free_vars P u ->
    red1 Σ Γ u v ->
    red1 Σ Δ (rename f u) (rename f v).
Proof using cf.
  intros P Σ Γ Δ u v f wfΣ hf hav h.
  induction h using red1_ind_all in P, f, Δ, hav, hf |- *.
  all: try solve [
    try (cbn in hav; rtoProp);
    simpl ; constructor ; eapply IHh ;
    try eapply urenaming_vass ;
    try eapply urenaming_vdef ;
    eassumption
  ].
  all:simpl in hav |- *; try toAll.
  - rewrite rename_subst10. constructor.
  - rewrite rename_subst10. constructor.
  - destruct (nth_error Γ i) eqn:hnth; noconf H.
    unfold urenaming in hf.
    specialize hf with (1 := hav) (2 := hnth).
    destruct hf as [decl' [e' [? [hr hbo]]]].
    rewrite H /= in hbo.
    rewrite lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    sigma in H0. sigma. rewrite H0.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rewrite -rename_inst.
        now rewrite -(lift0_rename (S (f i)) _). }
    constructor. now rewrite e' /= hdecl.
  - rewrite rename_mkApps. simpl.
    rewrite rename_iota_red //.
    * rewrite length_skipn; lia.
    * change (bcontext br) with (bcontext (rename_branch f br)).
      move/and5P: hav => [_ _ _ _ hbrs].
      eapply nth_error_forallb in hbrs; tea. simpl in hbrs.
      move/andP: hbrs => [] clbctx clbod.
      rewrite closedn_ctx_on_free_vars.
      now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
    * constructor.
      + rewrite nth_error_map H /= //.
      + simpl. now len.
  - rewrite 2!rename_mkApps. simpl.
    econstructor.
    + eapply rename_unfold_fix. eassumption.
    + rewrite -is_constructor_rename. assumption.
  - rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_case.
    eapply rename_unfold_cofix. eassumption.
  - rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_proj.
    eapply rename_unfold_cofix. eassumption.
  - rewrite rename_subst_instance.
    econstructor.
    + eassumption.
    + rewrite rename_closed. 2: assumption.
      eapply declared_constant_closed_body. all: eauto.
  - rewrite rename_mkApps. simpl.
    econstructor. rewrite nth_error_map. rewrite H. reflexivity.
  - move/and4P: hav=> [hpars hret hc hbrs].
    rewrite rename_predicate_set_pparams. econstructor.
    simpl. eapply OnOne2_map. repeat toAll.
    eapply OnOne2_All_mix_left in X; eauto. solve_all. red; eauto.
  - move/and4P: hav=> [_ hret hpctx _].
    rewrite rename_predicate_set_preturn.
    eapply case_red_return; eauto.
    simpl.
    eapply IHh; eauto.
    rewrite /inst_case_predicate_context. rewrite /= /id.
    rewrite -rename_inst_case_context_wf //.
    relativize #|pcontext p|; [apply urenaming_context; tea|].
    now len.
  - move/and5P: hav=> [_ _ _ _ hbrs].
    eapply case_red_brs; eauto.
    eapply OnOne2_map. toAll.
    eapply OnOne2_All_mix_left in X; tea. clear hbrs.
    solve_all.
    simpl. red. split; auto.
    rewrite /inst_case_branch_context /=.
    rewrite -b0 //.
    eapply b1; tea.
    rewrite -rename_inst_case_context_wf //.
    relativize #|bcontext x|; [apply urenaming_context; tea|].
    now len.
  - eapply OnOne2_All_mix_left in X; eauto.
    constructor.
    eapply OnOne2_map. solve_all. red. eauto.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eauto.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply fix_red_body. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eapply b1.
    * rewrite rename_fix_context. rewrite <- fix_context_length.
      now eapply urenaming_context.
    * now len.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eauto.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply cofix_red_body. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eapply b1.
    * rewrite rename_fix_context. rewrite <- fix_context_length.
      now eapply urenaming_context.
    * now len.
  - constructor. eapply OnOne2_map. cbn in hav. rtoProp.
    unfold on_Trel; cbn. eapply forallb_All in H. eapply OnOne2_All_mix_left in X; tea.
    solve_all.
Qed.

Lemma red_on_free_vars {P : nat -> bool} {Σ:global_env_ext} {Γ u v} {wfΣ : wf Σ} :
  on_ctx_free_vars P Γ ->
  on_free_vars P u ->
  red Σ Γ u v ->
  on_free_vars P v.
Proof using Type.
  intros onΓ on r.
  induction r; auto.
  now eapply red1_on_free_vars.
Qed.

Lemma red_rename :
  forall P (Σ : global_env_ext) Γ Δ u v f,
    wf Σ ->
    urenaming P Γ Δ f ->
    on_ctx_free_vars P Γ ->
    on_free_vars P u ->
    red Σ Γ u v ->
    red Σ Δ (rename f u) (rename f v).
Proof using Type.
  intros.
  induction X1.
  - constructor. now eapply red1_rename.
  - reflexivity.
  - etransitivity.
    * eapply IHX1_1. eauto.
    * eapply IHX1_2. eapply red_on_free_vars; eauto.
Qed.

Lemma conv_renameP :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming P Γ Δ f ->
    on_free_vars P A ->
    on_free_vars P B ->
    on_ctx_free_vars P Γ ->
    Σ ;;; Γ |- A = B ->
    Σ ;;; Δ |- rename f A = rename f B.
Proof using Type.
  intros P Σ Γ Δ f A B hΣ hf hA hB hΓ h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
    + apply IHh.
      * eapply red1_on_free_vars; tea.
      * auto.
  - eapply cumul_red_r.
    + eapply IHh; eauto. eapply (red1_on_free_vars); tea.
    + eapply red1_rename. all: try eassumption.
Qed.

Lemma cumul_renameP :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming P Γ Δ f ->
    on_free_vars P A ->
    on_free_vars P B ->
    on_ctx_free_vars P Γ ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Δ |- rename f A <= rename f B.
Proof using Type.
  intros P Σ Γ Δ f A B hΣ hf hA hB hΓ h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
    + apply IHh.
      * eapply red1_on_free_vars; tea.
      * auto.
  - eapply cumul_red_r.
    + eapply IHh; eauto. eapply red1_on_free_vars; tea.
    + eapply red1_rename. all: try eassumption.
Qed.

End Renaming2.
