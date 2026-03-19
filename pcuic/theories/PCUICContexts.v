(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From Stdlib Require Import CRelationClasses ProofIrrelevance.
From MetaRocq.Common Require Import config Universes BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICEquality PCUICCumulativity PCUICReduction
     PCUICContextSubst PCUICUnivSubstitutionConv
     PCUICClosed PCUICSigmaCalculus PCUICSubstitution PCUICUnivSubstitutionTyp
     PCUICWeakeningTyp PCUICWeakeningConv PCUICGeneration PCUICUtils.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation_Properties.
From Stdlib Require Import ssreflect ssrbool.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

#[global]
Hint Rewrite Nat.add_0_r : len.

Lemma smash_context_subst_empty s n Γ :
  smash_context [] (subst_context s n Γ) =
  subst_context s n (smash_context [] Γ).
Proof. apply: (smash_context_subst []). Qed.

Lemma conv_context_smash {cf:checker_flags} Σ Γ Δ Δ' :
  assumption_context Δ ->
  All2_fold (fun Δ Δ' => conv_decls cumulSpec0 Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ' ->
  assumption_context Δ'.
Proof.
  intros Hass Hconv.
  induction Hass in Δ', Hconv |- *. depelim Hconv. constructor.
  depelim Hconv. depelim c; constructor; auto.
Qed.

Lemma smash_context_assumption_context {Γ Δ} :
  assumption_context Γ ->
  assumption_context (smash_context Γ Δ).
Proof.
  induction Δ in Γ |- *; simpl; auto.
  destruct a as [? [b|] ty]; auto.
  intros.
  eapply IHΔ. clear -H.
  induction H; simpl; auto. constructor.
  rewrite subst_context_snoc. constructor; auto.
  intros.
  eapply IHΔ.
  clear -H. induction H; simpl; auto. constructor. constructor.
  constructor. auto.
Qed.

#[global]
Hint Resolve smash_context_assumption_context : pcuic.
#[global]
Hint Constructors assumption_context : pcuic.

Lemma smash_assumption_context Γ :
  assumption_context Γ ->
  smash_context [] Γ = Γ.
Proof.
  induction Γ using rev_ind.
  - now reflexivity.
  - destruct x as [na [b|] ty].
    intros ass. eapply assumption_context_app in ass as []. exfalso; depelim a0.
    intros ass.
    rewrite smash_context_app_ass IHΓ. now eapply assumption_context_app in ass as [].
    reflexivity.
Qed.

Lemma smash_context_idempotent Γ :
  smash_context [] (smash_context [] Γ) = smash_context [] Γ.
Proof.
  rewrite smash_assumption_context //; pcuic.
Qed.

Lemma assumption_context_length ctx : assumption_context ctx ->
  context_assumptions ctx = #|ctx|.
Proof. induction 1; simpl; auto; lia. Qed.

#[global]
Hint Resolve assumption_context_length : pcuic.

Lemma map_subst_instance_to_extended_list_k u ctx k :
  map (subst_instance u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all.
  now destruct H as [n [-> _]].
Qed.

Lemma subst_instance_to_extended_list_k u l k
  : map (subst_instance u) (to_extended_list_k l k)
    = to_extended_list_k (subst_instance u l) k.
Proof.
  unfold to_extended_list_k.
  change [] with (map (subst_instance u) (@nil term)) at 2.
  generalize (@nil term). induction l as [|[aa [ab|] ac] bb] in k |- *.
  + reflexivity.
  + intros l; cbn. now rewrite IHbb.
  + intros l; cbn. now rewrite IHbb.
Qed.

Lemma context_subst_lift Γ p s n :
  context_subst Γ p s ->
  context_subst (lift_context n 0 Γ) (map (lift0 n) p) (map (lift0 n) s).
Proof.
  induction 1 in |- *; try constructor.
  rewrite lift_context_snoc map_app /=; constructor; auto.
  rewrite lift_context_snoc /= /lift_decl /map_decl /=.
  rewrite Nat.add_0_r.
  rewrite (context_subst_length X).
  rewrite distr_lift_subst Nat.add_0_r.
  now constructor.
Qed.

Derive Signature for subslet.

Lemma closedn_ctx_snoc k Γ d : closedn_ctx k (Γ ,, d) = closedn_ctx k Γ && closed_decl (#|Γ| + k) d.
Proof. reflexivity. Qed.

Lemma type_local_ctx_wf_local {cf:checker_flags} Σ Γ Δ s :
  wf_local Σ Γ ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s ->
  wf_local Σ (Γ ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto. now eapply lift_sorting_forget_univ.
Qed.

Lemma sorts_local_ctx_wf_local {cf:checker_flags} Σ Γ Δ s :
  wf_local Σ Γ ->
  sorts_local_ctx (lift_typing typing) Σ Γ Δ s ->
  wf_local Σ (Γ ,,, Δ).
Proof.
  induction Δ in s |- *; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto. pcuic.
  destruct s => //. destruct wfctx; eauto.
  destruct s => //. destruct wfctx. now eapply lift_sorting_forget_univ.
Qed.

Lemma instantiate_minductive {cf:checker_flags} Σ ind mdecl u Γ t T :
  wf Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  (Σ.1, ind_universes mdecl) ;;; Γ |- t : T ->
  Σ ;;; subst_instance u Γ |- subst_instance u t : subst_instance u T.
Proof.
  intros wfΣ isdecl Hu Ht.
  unshelve eapply declared_minductive_to_gen in isdecl; eauto.
  red in isdecl. eapply typing_subst_instance_decl in isdecl; eauto.
Qed.

Lemma type_local_ctx_instantiate {cf:checker_flags} Σ ind mdecl Γ Δ u s :
  wf Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  type_local_ctx (lift_typing typing) (Σ.1, ind_universes mdecl) Γ Δ s ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  type_local_ctx (lift_typing typing) Σ (subst_instance u Γ) (subst_instance u Δ) (subst_instance_sort u s).
Proof.
  intros Hctx Hu.
  induction Δ; simpl in *; intuition auto.
  { destruct Σ as [Σ univs]. eapply (wf_sort_subst_instance (Σ, ind_universes mdecl)); eauto. }
  destruct a as [na [b|] ty]; simpl; destruct X as (Hwfctx & Hj); split; eauto.
  all: eapply lift_typing_fu_impl with (1 := Hj) => //= ?? Hs; auto using relevance_subst_opt.
  all: eapply instantiate_minductive in Hs; eauto.
  all: now rewrite subst_instance_app in Hs.
Qed.

Lemma sorts_local_ctx_instantiate {cf:checker_flags} Σ ind mdecl Γ Δ u s :
  wf Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  sorts_local_ctx (lift_typing typing) (Σ.1, ind_universes mdecl) Γ Δ s ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  sorts_local_ctx (lift_typing typing) Σ (subst_instance u Γ) (subst_instance u Δ)
    (List.map (subst_instance_sort u) s).
Proof.
  intros Hctx Hu.
  induction Δ in s |- *; simpl in *; intuition auto.
  1: destruct s; simpl; intuition eauto.
  destruct a as [na [b|] ty]; simpl.
  2: destruct s => //=.
  all: destruct X as (Hwfctx & Hj); split; eauto.
  all: eapply lift_typing_fu_impl with (1 := Hj) => //= ?? Hs; auto using relevance_subst_opt.
  all: eapply instantiate_minductive in Hs; eauto.
  all: now rewrite subst_instance_app in Hs.
Qed.

Lemma subst_type_local_ctx {cf:checker_flags} Σ Γ Δ Δ' s ctxs :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ) ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Δ) Δ' ctxs ->
  subslet Σ Γ s Δ ->
  type_local_ctx (lift_typing typing) Σ Γ (subst_context s 0 Δ') ctxs.
Proof.
  intros wfΣ wfΓ X Hs. revert X.
  induction Δ'; simpl; auto.
  rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r.
  destruct a as [na [b|] ty]; simpl.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_f_impl with (1 := Hj) => //= ?? HT.
  all: now eapply substitution in HT.
Qed.

Lemma subst_sorts_local_ctx {cf:checker_flags} Σ Γ Δ Δ' s ctxs :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ) ->
  sorts_local_ctx (lift_typing typing) Σ (Γ ,,, Δ) Δ' ctxs ->
  subslet Σ Γ s Δ ->
  sorts_local_ctx (lift_typing typing) Σ Γ (subst_context s 0 Δ') ctxs.
Proof.
  intros wfΣ wfΓ X Hs. revert X.
  induction Δ' in ctxs |- *; simpl; auto.
  rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r.
  destruct a as [na [b|] ty]; simpl. 2: destruct ctxs => //=.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_f_impl with (1 := Hj) => //= ?? HT.
  all: now eapply substitution in HT.
Qed.

Lemma weaken_type_local_ctx {cf:checker_flags} Σ Γ Γ' Δ ctxs :
  wf Σ.1 ->
  wf_local Σ Γ ->
  type_local_ctx (lift_typing typing) Σ Γ' Δ ctxs ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Γ') Δ ctxs.
Proof.
  intros wfΣ wfΓ.
  induction Δ; simpl; auto.
  rewrite -app_context_assoc.
  destruct a as [na [b|] ty]; simpl.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_impl with (1 := Hj) => //= ?? HT.
  all: eapply (weaken_ctx Γ); auto.
Qed.

Lemma weaken_sorts_local_ctx {cf:checker_flags} Σ Γ Γ' Δ ctxs :
  wf Σ.1 ->
  wf_local Σ Γ ->
  sorts_local_ctx (lift_typing typing) Σ Γ' Δ ctxs ->
  sorts_local_ctx (lift_typing typing) Σ (Γ ,,, Γ') Δ ctxs.
Proof.
  intros wfΣ wfΓ.
  induction Δ in ctxs |- *; simpl; auto.
  rewrite -app_context_assoc.
  destruct a as [na [b|] ty]; simpl. 2: destruct ctxs => //.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_impl with (1 := Hj) => //= ?? HT.
  all: eapply (weaken_ctx Γ); auto.
Qed.

Lemma reln_app acc Γ Δ k : reln acc k (Γ ++ Δ) =
  reln (reln acc k Γ) (#|Γ| + k) Δ.
Proof.
  induction Γ in acc, Δ, k |- *; simpl; auto.
  destruct a as [na [b|] ty]. rewrite IHΓ. f_equal. lia.
  simpl. rewrite IHΓ. f_equal. lia.
Qed.

Lemma reln_acc acc k Γ : reln acc k Γ = reln [] k Γ ++ acc.
Proof.
  induction Γ in acc, k |- *; simpl; auto.
  destruct a as [na [b|] ty]. rewrite IHΓ. f_equal.
  rewrite IHΓ. rewrite [reln [_] _ _]IHΓ.
  now rewrite -app_assoc.
Qed.

Lemma to_extended_list_k_app Γ Δ k : to_extended_list_k (Γ ++ Δ) k =
  to_extended_list_k Δ (#|Γ| + k) ++ to_extended_list_k Γ k.
Proof.
  unfold to_extended_list_k. now rewrite reln_app reln_acc.
Qed.

Lemma to_extended_list_k_fold_context_k f Γ k :
  to_extended_list_k (fold_context_k f Γ) k = to_extended_list_k Γ k.
Proof.
  rewrite /to_extended_list_k.
  generalize (@nil term).
  induction Γ in k |- *.
  simpl; auto.
  intros.
  rewrite fold_context_k_snoc0. simpl.
  destruct a as [? [?|] ?] => /=; now rewrite IHΓ.
Qed.

Lemma to_extended_list_k_lift_context c k n k' :
  to_extended_list_k (lift_context n k c) k' = to_extended_list_k c k'.
Proof. now rewrite to_extended_list_k_fold_context_k. Qed.

Lemma reln_lift n k Γ : reln [] (n + k) Γ = map (lift0 n) (reln [] k Γ).
Proof.
  induction Γ in n, k |- *; simpl; auto.
  destruct a as [? [?|] ?]; simpl.
  now rewrite -IHΓ Nat.add_assoc.
  rewrite reln_acc  [reln [tRel k] _ _]reln_acc map_app /=.
  f_equal. now rewrite -IHΓ Nat.add_assoc.
Qed.

Lemma to_extended_list_length Γ : #|to_extended_list Γ| = context_assumptions Γ.
Proof. now rewrite /to_extended_list to_extended_list_k_length. Qed.
#[global]
Hint Rewrite to_extended_list_length : len.

Lemma map_subst_app_to_extended_list_k s s' ctx k  :
  k = #|s| ->
  map (subst0 (s ++ s')) (to_extended_list_k ctx k) =
  map (subst0 s') (to_extended_list_k ctx 0).
Proof.
  intros ->.
  rewrite /to_extended_list_k.
  rewrite -{1}(Nat.add_0_r #|s|) reln_lift map_map_compose.
  apply map_ext. intros x; simpl.
  rewrite subst_app_decomp.
  f_equal. rewrite -{1}(Nat.add_0_r #|s|) simpl_subst' ?lift0_id //.
  now rewrite length_map.
Qed.

Lemma subst_context_smash_context s k Γ Δ :
  subst_context s k (smash_context Γ Δ) =
  smash_context (subst_context s (#|Δ| + k) Γ) (subst_context s k Δ).
Proof.
  induction Δ as [|[? [] ?] ?] in Γ |- *; simpl; auto;
    rewrite subst_context_snoc; simpl.
  - rewrite IHΔ. f_equal.
    rewrite !subst_context_alt !mapi_mapi. apply mapi_ext. clear.
    intros n x. rewrite /subst_decl !compose_map_decl.
    eapply map_decl_ext. intros.
    autorewrite with len.
    generalize (Nat.pred #|Γ| - n). generalize (#|Δ| + k). clear.
    intros. rewrite distr_subst_rec. simpl. now rewrite -Nat.add_assoc.
  - rewrite IHΔ. f_equal.
    rewrite subst_context_app. simpl.  unfold app_context. f_equal.
Qed.

Section WfEnv.
  Context {cf} {Σ} {wfΣ : wf Σ}.

  Lemma wf_local_rel_smash_context_gen {Γ Δ Δ'} :
    wf_local Σ (Δ' ,,, Γ) ->
    wf_local_rel Σ (Δ' ,,, Γ) Δ ->
    wf_local_rel Σ Δ' (smash_context Δ Γ).
  Proof using wfΣ.
    induction Γ in Δ |- *; simpl; auto.
    intros wfΓ wfΔ. depelim wfΓ; simpl.
    - apply IHΓ; auto. eapply All_local_env_app; auto.
      + constructor; auto.
      + eapply All_local_env_impl; eauto. simpl; intros.
        now rewrite app_context_assoc.
    - apply IHΓ; auto.
      apply All_local_env_fold, All_local_env_impl with (1 := wfΔ).
      intros Γ' j X.
      apply lift_typing_f_impl with (1 := X) => // ?? HT.
      rewrite Nat.add_0_r.
      eapply (substitution (Γ':=[vdef na b t]) (s := [b])) in HT; eauto.
      rewrite -{1}(subst_empty 0 b).
      repeat constructor.
      rewrite !subst_empty.
      now eapply unlift_TermTyp.
  Qed.

  Lemma wf_local_rel_smash_context {Γ Δ} :
    wf_local Σ (Δ ,,, Γ) ->
    wf_local_rel Σ Δ (smash_context [] Γ).
  Proof using wfΣ.
    intros. eapply wf_local_rel_smash_context_gen; eauto. constructor.
  Qed.

  Lemma wf_local_smash_end Γ Δ :
    wf_local Σ (Γ ,,, Δ) -> wf_local Σ (Γ ,,, smash_context [] Δ).
  Proof using wfΣ.
    intros wf.
    apply All_local_env_app.
    now apply All_local_env_app_inv in wf.
    eapply wf_local_rel_smash_context; auto.
  Qed.

  Lemma wf_local_rel_empty Γ : wf_local_rel Σ [] Γ <~> wf_local Σ Γ.
  Proof using Type.
    split.
    - intros h. eapply (All_local_env_impl _ _ _ h). pcuicfo.
      red in X |- *. now rewrite app_context_nil_l in X.
    - intros h. eapply (All_local_env_impl _ _ _ h). pcuicfo.
      red in X |- *. now rewrite app_context_nil_l.
  Qed.

  Lemma wf_local_smash_context {Γ} :
    wf_local Σ Γ -> wf_local Σ (smash_context [] Γ).
  Proof using wfΣ.
    intros; apply wf_local_rel_empty. eapply wf_local_rel_smash_context.
      rewrite ?app_context_nil_l; eauto.
  Qed.

End WfEnv.

Local Open Scope sigma_scope.

Lemma context_subst_extended_subst Γ args s :
  context_subst Γ args s ->
  s = map (inst (List.rev args ⋅n ids)) (extended_subst Γ 0).
Proof.
  induction 1.
  - simpl; auto.
  - simpl.
    rewrite lift_extended_subst.
    rewrite map_map_compose.
    rewrite List.rev_app_distr. simpl. f_equal.
    rewrite IHX. apply map_ext.
    intros. autorewrite with sigma.
    apply inst_ext.
    rewrite subst_consn_subst_cons.
    now rewrite subst_cons_shift.
  - simpl.
    f_equal; auto. len.
    rewrite IHX.
    autorewrite with sigma.
    apply inst_ext. len.
    rewrite (Upn_eq _ (List.rev args ⋅n ids)).
    rewrite subst_consn_compose.
    rewrite PCUICInstConv.map_inst_idsn; len; try lia.
    rewrite subst_compose_assoc.
    rewrite -(context_subst_length2 X).
    rewrite subst_consn_shiftn; len => //.
    sigma. rewrite Upn_eq. sigma.
    rewrite PCUICInstConv.map_inst_idsn; len; try lia.
    rewrite -subst_compose_assoc shiftk_compose.
    rewrite -subst_consn_app.
    rewrite subst_consn_shiftn //. now len.
Qed.

Lemma map_subst_app_decomp (l l' : list term) (k : nat) (ts : list term) :
  map (subst (l ++ l') k) ts = map (fun x => subst l' k (subst (map (lift0 #|l'|) l) k x)) ts.
Proof.
  apply map_ext. apply subst_app_decomp.
Qed.

Lemma map_reln_ext (f g : term -> term) k Γ :
  (forall n, n < #|Γ| -> f (tRel (k + n)) = g (tRel (k + n))) ->
  map f (reln [] k Γ) = map g (reln [] k Γ).
Proof.
  intros Hf.
  induction Γ as [|[? [] ?] ?] in k, Hf |- *; simpl; auto.
  - rewrite reln_acc map_app. simpl.
    rewrite map_app /=. rewrite IHΓ //.
    intros. simpl in Hf. specialize (Hf (S n)).
    forward Hf. lia. rewrite -Nat.add_assoc. apply Hf.
  - rewrite reln_acc map_app. simpl.
    rewrite map_app /= IHΓ //.
    intros. simpl in Hf. specialize (Hf (S n)).
    forward Hf. lia. rewrite -Nat.add_assoc. apply Hf.
    f_equal. f_equal. specialize (Hf 0). simpl in Hf.
    forward Hf by lia. now rewrite Nat.add_0_r in Hf.
Qed.

Lemma extended_subst_to_extended_list_k Γ k :
  (map (subst (extended_subst Γ 0) k) (to_extended_list_k Γ k)) =
  to_extended_list_k (smash_context [] Γ) k.
Proof.
  unfold to_extended_list_k.
  induction Γ in k |- *. simpl. reflexivity.
  destruct a as [? [] ?]; simpl.
  - rewrite smash_context_acc //.
    rewrite reln_app. autorewrite with len. simpl.
    rewrite -IHΓ //. rewrite Nat.add_1_r.
    rewrite (reln_lift 1).
    clear.
    rewrite (map_subst_app_decomp [_]).
    rewrite -map_map_compose. f_equal.
    simpl.
    generalize (lift0 #|extended_subst Γ 0|
      (subst0 (extended_subst Γ 0) (lift (context_assumptions Γ) #|Γ| t))).
    intros t0.
    change 1 with #|[t0]|.
    generalize [t0]. clear.
    intros l. generalize (Nat.le_refl k).
    generalize k at 1 3.
    induction Γ as [|[? [] ?] ?] in k, l |- *; simpl. reflexivity.
    simpl. intros k0 le0. apply IHΓ. lia.
    intros k0 lek0. rewrite reln_acc map_app. simpl.
    rewrite map_app. simpl.
    elim: leb_spec_Set => Hle. f_equal. apply IHΓ. lia.
    f_equal. elim: nth_error_spec => [x Hx Hl|Hl]. lia.
    f_equal. lia. lia.
  - rewrite smash_context_acc //.
    simpl.
    rewrite reln_acc map_app.
    rewrite (reln_acc [_] _ (smash_context [] Γ)).
    simpl. rewrite Nat.leb_refl Nat.sub_diag /=. f_equal.
    rewrite -IHΓ //.
    2:{ do 2 f_equal; lia. }
    apply map_reln_ext => n Hn.
    rewrite lift_extended_subst //.
    replace (k + 1 + n) with (S (k + n)) by lia.
    simpl.
    elim: leb_spec_Set => Hle; [|lia].
    elim: leb_spec_Set => Hle'; [|lia].
    replace (S (k + n) - k) with (S n) by lia.
    replace (S (k + n) - (k + 1)) with n by lia.
    simpl.
    rewrite nth_error_map.
    elim: nth_error_spec => [x Hx Hlen|Hlen].
    simpl. rewrite simpl_lift; try lia. f_equal. simpl.
    autorewrite with len in Hlen. lia.
Qed.

Lemma assumption_context_fold f Γ :
  assumption_context Γ -> assumption_context (fold_context_k f Γ).
Proof.
  induction 1; simpl. constructor. rewrite fold_context_k_snoc0.
  now constructor.
Qed.

Lemma smash_context_app_expand Γ Δ Δ' :
  smash_context Γ (Δ ,,, Δ') =
  smash_context [] Δ ,,, expand_lets_ctx Δ (smash_context Γ Δ').
Proof.
  rewrite smash_context_app smash_context_acc.
  rewrite /expand_lets_k_ctx /app_context. f_equal.
Qed.

Lemma expand_lets_smash_context Γ Δ Δ' :
  expand_lets_ctx Γ (smash_context Δ Δ') =
  smash_context (expand_lets_k_ctx Γ #|Δ'| Δ) (expand_lets_ctx Γ Δ').
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite -smash_context_lift -smash_context_subst /=; len.
Qed.

Lemma expand_lets_k_ctx_nil Γ k : expand_lets_k_ctx Γ k [] = [].
Proof. reflexivity. Qed.

Lemma expand_lets_ctx_nil Γ : expand_lets_ctx Γ [] = [].
Proof. reflexivity. Qed.
#[global]
Hint Rewrite expand_lets_k_ctx_nil expand_lets_ctx_nil : pcuic.

Definition subst_let_expand args Δ T :=
  (subst0 args (expand_lets Δ T)).

Definition subst_context_let_expand args Δ Γ :=
  (subst_context args 0 (expand_lets_ctx Δ Γ)).

Definition subst_let_expand_tProd args Δ na T s :
  subst_let_expand args Δ (tProd na T (tSort s)) =
  tProd na (subst_let_expand args Δ T) (tSort s).
Proof.
  reflexivity.
Qed.

Definition subst_let_expand_mkApps s Δ f args :
  subst_let_expand s Δ (mkApps f args) =
  mkApps (subst_let_expand s Δ f) (map (subst_let_expand s Δ) args).
Proof.
  rewrite /subst_let_expand.
  now rewrite expand_lets_mkApps subst_mkApps map_map_compose.
Qed.

Definition subst_let_expand_tInd s Δ ind u :
  subst_let_expand s Δ (tInd ind u) = tInd ind u.
Proof. reflexivity. Qed.

Lemma subst_let_expand_it_mkProd_or_LetIn s Γ Δ u :
  subst_let_expand s Γ (it_mkProd_or_LetIn Δ (tSort u)) =
  it_mkProd_or_LetIn (subst_context_let_expand s Γ Δ) (tSort u).
Proof.
  rewrite /subst_let_expand /expand_lets.
  rewrite expand_lets_it_mkProd_or_LetIn /= subst_it_mkProd_or_LetIn /=.
  reflexivity.
Qed.

Lemma subst_lift_above s n k x : k = #|s| -> subst0 s (lift0 (n + k) x) = lift0 n x.
Proof.
  intros. rewrite Nat.add_comm. subst k. now rewrite simpl_subst.
Qed.

Lemma subst_let_expand_lift_id s Δ k x :
  k = #|Δ| ->
  #|s| = context_assumptions Δ ->
  subst_let_expand s Δ (lift0 k x) = x.
Proof.
  intros -> hl.
  rewrite /subst_let_expand /expand_lets /expand_lets_k.
  simpl.
  rewrite simpl_lift; len; try lia.
  rewrite subst_lift_above. now len.
  change (context_assumptions Δ) with (0 + context_assumptions Δ).
  rewrite subst_lift_above. len. now rewrite lift0_id.
Qed.

Lemma subslet_lift {cf} {Σ} {wfΣ : wf Σ} (Γ Δ : context) s Δ' :
  wf_local Σ (Γ ,,, Δ) ->
  subslet Σ Γ s Δ' ->
  subslet Σ (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  move=> wfl.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(subslet_length X).
  rewrite -distr_lift_subst. apply weakening; eauto.

  rewrite -(subslet_length X).
  rewrite distr_lift_subst. constructor; auto.
  rewrite - !distr_lift_subst. apply weakening; eauto.
Qed.

Lemma untyped_subslet_lift (Γ Δ : context) s Δ' :
  untyped_subslet Γ s Δ' ->
  untyped_subslet (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(untyped_subslet_length X).
  rewrite distr_lift_subst. constructor; auto.
Qed.

Lemma untyped_subslet_extended_subst Γ Δ :
  untyped_subslet (Γ ,,, smash_context [] Δ)
    (extended_subst Δ 0)
    (lift_context (context_assumptions Δ) 0 Δ).
Proof.
  induction Δ as [|[na [d|] ?] ?]; simpl; try constructor.
  * rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    len.
    constructor => //.
  * rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    constructor.
    rewrite (lift_extended_subst _ 1).
    rewrite -(lift_context_lift_context 1 _).
    eapply (untyped_subslet_lift _ [_]); eauto.
Qed.


Lemma subslet_extended_subst {cf} {Σ} {wfΣ : wf Σ} Γ Δ :
  wf_local Σ (Γ ,,, Δ) ->
  subslet Σ (Γ ,,, smash_context [] Δ)
    (extended_subst Δ 0)
    (lift_context (context_assumptions Δ) 0 Δ).
Proof.
  move=> wfΔ.
  eapply All_local_env_app_inv in wfΔ as [wfΓ wfΔ].
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; try constructor.
  * depelim wfΔ. repeat red in l, l0.
    specialize (IHΔ wfΔ).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    len.
    constructor => //.
    apply unlift_TermTyp in l.
    eapply (weakening_typing (Γ'' := smash_context [] Δ)) in l.
    len in l. simpl in l. simpl.
    2:{ eapply wf_local_smash_end; pcuic. }
    eapply (substitution (Δ := [])) in l; tea.
  * rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    depelim wfΔ.
    specialize (IHΔ wfΔ).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    assert (wf_local Σ (Γ ,,, smash_context [] Δ)).
    { eapply wf_local_smash_end. now eapply All_local_env_app. }
    assert (wf_local Σ (Γ ,,, smash_context [] Δ ,, mkdecl na None
        (subst0 (extended_subst Δ 0) (lift (context_assumptions Δ) #|Δ| decl_type)))).
    { simpl. constructor; tas.
      eapply lift_typing_f_impl with (f := fun t => _ (_ t)) (1 := l) => // ?? Hs.
      eapply (weakening_typing (Γ'' := smash_context [] Δ)) in Hs; tas.
      len in Hs.
      now eapply (substitution (Δ := [])) in Hs.
    }
    constructor.
    - rewrite (lift_extended_subst _ 1).
      rewrite -(lift_context_lift_context 1 _).
      eapply (subslet_lift _ [_]); eauto.
    - eapply meta_conv.
      econstructor; tas.
      reflexivity.
      simpl. rewrite (lift_extended_subst _ 1).
      rewrite distr_lift_subst. f_equal. len.
      now rewrite simpl_lift; try lia.
Qed.

Lemma typing_expand_lets {cf} {Σ} {wfΣ : wf Σ} Γ Δ t T :
  Σ ;;; Γ ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ |- expand_lets Δ t : expand_lets Δ T.
Proof.
  intros Ht.
  rewrite /expand_lets /expand_lets_k.
  pose proof (typing_wf_local Ht).
  eapply (weakening_typing (Γ'' := smash_context [] Δ)) in Ht.
  len in Ht. simpl in Ht. simpl.
  2:{ eapply wf_local_smash_end; pcuic. }
  eapply (substitution (Δ := [])) in Ht; tea.
  now eapply subslet_extended_subst.
Qed.

Lemma subst_context_let_expand_length s Γ Δ :
  #|subst_context_let_expand s Γ Δ| = #|Δ|.
Proof.
  now rewrite /subst_context_let_expand; len.
Qed.
#[global]
Hint Rewrite subst_context_let_expand_length : len.

Lemma to_extended_list_subst_context_let_expand s Γ Δ :
  to_extended_list (subst_context_let_expand s Γ Δ) =
  to_extended_list Δ.
Proof.
  rewrite /subst_context_let_expand /to_extended_list /expand_lets_ctx /expand_lets_k_ctx.
  now rewrite !to_extended_list_k_subst to_extended_list_k_lift_context.
Qed.

Lemma map2_set_binder_name_alpha (nas : list aname) (Δ Δ' : context) :
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas Δ ->
  eq_context_upto_names Δ Δ' ->
  eq_context_upto_names (map2 set_binder_name nas Δ) Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  constructor; auto. destruct r; subst; cbn; constructor; auto;
  now transitivity na.
Qed.

Abbreviation eq_names := (All2 (fun x y => x = (decl_name y))).

Lemma eq_names_subst_context nas Γ s k :
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * cbn. constructor.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance nas Γ u :
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

Lemma map2_set_binder_name_alpha_eq (nas : list aname) (Δ Δ' : context) :
  eq_names nas Δ' ->
  eq_context_upto_names Δ Δ' ->
  (map2 set_binder_name nas Δ) = Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  f_equal; auto. destruct r; subst; cbn; auto.
Qed.

Lemma sorts_local_ctx_app P Σ Γ Δ1 Δ2 us1 us2 :
  sorts_local_ctx P Σ Γ Δ1 us1 ->
  sorts_local_ctx P Σ (Γ ,,, Δ1) Δ2 us2 ->
  sorts_local_ctx P Σ Γ (Δ1 ,,, Δ2) (us2 ++ us1).
Proof.
  elim: Δ2 us2 Δ1 us1=> [|+ Δ2 ih].
  1: move=> [|u us2] //=.
  move=> [? [bdy|] ty] us2 Δ1 us1 /=.
  - rewrite app_context_assoc=> ? [? ?] ; split=> //.
    by apply: ih.
  - case: us2=> [|u us2] // ? [??] /=.
    rewrite app_context_assoc; split=> //.
    by apply: ih.
Qed.
