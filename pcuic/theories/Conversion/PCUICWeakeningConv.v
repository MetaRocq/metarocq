(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICTyping PCUICCumulativity
  PCUICClosed PCUICReduction
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICOnFreeVars
  PCUICClosedConv PCUICClosedTyp.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Implicit Types cf : checker_flags.

(** * Weakening lemmas for typing derivations.

  [weakening_*] proves weakening of typing, reduction etc... w.r.t. the *local*
  environment. *)

Set Default Goal Selector "!".
Generalizable Variables Σ Γ t T.

(* FIXME inefficiency in equations: using a very slow "pattern_sigma" to simplify an ws_cumul_pb between sigma types *)
Ltac Equations.CoreTactics.destruct_tele_eq H ::= noconf H.

Lemma closed_ctx_lift n k ctx : closed_ctx ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  rw closedn_ctx_cons lift_context_snoc0 /snoc.
  move/andb_and => /= [Hctx Hd].
  rw IHctx // lift_decl_closed //. now apply: closed_decl_upwards.
Qed.

Lemma weaken_nth_error_ge {Γ Γ' v Γ''} : #|Γ'| <= v ->
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (#|Γ''| + v) =
  nth_error (Γ ,,, Γ') v.
Proof.
  intros Hv.
  rewrite -> !nth_error_app_context_ge, ?lift_context_length.
  - f_equal. lia.
  - auto.
  - rw lift_context_length. lia.
  - rw lift_context_length. lia.
Qed.

Lemma weaken_nth_error_lt {Γ Γ' Γ'' v} : v < #|Γ'| ->
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') v =
  option_map (lift_decl #|Γ''| (#|Γ'| - S v)) (nth_error (Γ ,,, Γ') v).
Proof.
  simpl. intros Hv.
  rewrite -> !nth_error_app_context_lt.
  - rw nth_error_lift_context_eq.
    do 2 f_equal. lia.
  - lia.
  - now rw lift_context_length.
Qed.

Lemma lift_context_lift_context n k Γ : lift_context n 0 (lift_context k 0 Γ) =
  lift_context (n + k) 0 Γ.
Proof. rw !lift_context_alt.
  rw mapi_compose.
  apply mapi_ext.
  intros n' x.
  rw /lift_decl compose_map_decl.
  apply map_decl_ext => y.
  rw mapi_length; autorewrite with  len.
  rw simpl_lift //; lia.
Qed.

Lemma weakening_renaming P Γ Γ' Γ'' :
  urenaming P (Γ ,,, Γ') (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
    (lift_renaming #|Γ''| #|Γ'|).
Proof.
  intros i d hpi hnth.
  rw /lift_renaming.
  destruct (Nat.leb #|Γ'| i) eqn:leb; [apply Nat.leb_le in leb|eapply Nat.leb_nle in leb].
  - rw weaken_nth_error_ge //.
    exists d; split; auto.
    split; auto.
    split.
    * apply rename_ext => k. rw /rshiftk /lift_renaming.
      repeat nat_compare_specs.
    * destruct (decl_body d) => /= //.
      f_equal. apply rename_ext => k.
      rw /rshiftk; now nat_compare_specs.
  - rw weaken_nth_error_lt; try lia.
    rw hnth /=. eexists. split; [eauto|].
    simpl. rw !lift_rename !rename_compose /lift_renaming /rshiftk /=.
    repeat split.
    * apply rename_ext => k. now repeat nat_compare_specs.
    * destruct (decl_body d) => /= //. f_equal.
      rw lift_rename rename_compose /lift_renaming.
      apply rename_ext => k. simpl. now repeat nat_compare_specs.
Qed.

(* Variant lookup_decl_spec Γ Δ i : option context_decl -> Type :=
| lookup_head d : i < #|Δ| ->
  nth_error Δ i = Some d -> lookup_decl_spec Γ Δ i (Some d)
| lookup_tail d : #|Δ| <= i < #|Γ| + #|Δ| ->
  nth_error Γ (i - #|Δ|) = Some d ->
  lookup_decl_spec Γ Δ i (Some d)
| lookup_above : #|Γ| + #|Δ| <= i -> lookup_decl_spec Γ Δ i None.

Lemma lookup_declP Γ Δ i : lookup_decl_spec Γ Δ i (nth_error (Γ ,,, Δ) i).
Proof.
  destruct (Nat.ltb i #|Δ|) eqn:ltb.
  - apply Nat.ltb_lt in ltb.
    rewrite nth_error_app_lt //.
    destruct nth_error eqn:hnth.
    * constructor; auto.
    * apply nth_error_None in hnth. lia.
  - apply Nat.ltb_nlt in ltb.
    rewrite nth_error_app_ge; try lia.
    destruct nth_error eqn:hnth.
    * constructor 2; auto.
      apply nth_error_Some_length in hnth.
      split; lia.
    * constructor. eapply nth_error_None in hnth. lia.
Qed. *)

#[global]
Hint Rewrite rename_context_length : len.

(* Variant shiftn_spec k f i : nat -> Type :=
| shiftn_below : i < k -> shiftn_spec k f i i
| shiftn_above : k <= i -> shiftn_spec k f i (k + f (i - k)).

Lemma shiftn_P k f i : shiftn_spec k f i (shiftn k f i).
Proof.
  rewrite /shiftn.
  destruct (Nat.ltb i k) eqn:ltb.
  * apply Nat.ltb_lt in ltb.
    now constructor.
  * apply Nat.ltb_nlt in ltb.
    constructor. lia.
Qed. *)

Lemma rename_context_lift_context n k Γ :
  rename_context (lift_renaming n k) Γ = lift_context n k Γ.
Proof.
  rw /rename_context /lift_context.
  apply fold_context_k_ext => i t.
  now rw lift_rename shiftn_lift_renaming.
Qed.


Lemma smash_context_lift Δ k n Γ :
  smash_context (lift_context n (k + #|Γ|) Δ) (lift_context n k Γ) =
  lift_context n k (smash_context Δ Γ).
Proof.
  revert Δ. induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  - now rw Nat.add_0_r.
  - rw -IHΓ.
    rw lift_context_snoc /=. f_equal.
    rw !subst_context_alt !lift_context_alt !mapi_compose.
    apply mapi_ext=> n' x.
    destruct x as [na' [b'|] ty']; simpl.
    * rw !mapi_length /lift_decl /subst_decl /= /map_decl /=; f_equal.
      + f_equal. rw Nat.add_0_r distr_lift_subst_rec /=.
        lia_f_equal.
      + rw Nat.add_0_r distr_lift_subst_rec; simpl. lia_f_equal.
    * rw !mapi_length /lift_decl /subst_decl /= /map_decl /=; f_equal.
      rw Nat.add_0_r distr_lift_subst_rec /=.
      repeat (lia || f_equal).
  - rw -IHΓ.
    rw lift_context_snoc /= // /lift_decl /subst_decl /map_decl /=.
    f_equal.
    rw lift_context_app. simpl.
    rw /app_context; lia_f_equal.
    rw /lift_context // /fold_context_k /= /map_decl /=.
    now lia_f_equal.
Qed.

(* Lemma decompose_app_rec_lift n k t l :
  let (f, a) := decompose_app_rec t l in
  decompose_app_rec (lift n k t) (map (lift n k) l)  = (lift n k f, map (lift n k) a).
Proof.
  induction t in k, l |- *; simpl; auto with pcuic.
  - specialize (IHt1 k (t2 :: l)).
    destruct decompose_app_rec. now rewrite IHt1.
Qed.

Lemma decompose_app_lift n k t f a :
  decompose_app t = (f, a) -> decompose_app (lift n k t) = (lift n k f, map (lift n k) a).
Proof.
  generalize (decompose_app_rec_lift n k t []).
  unfold decompose_app. destruct decompose_app_rec.
  now move=> Heq [= <- <-].
Qed.
#[global]
Hint Rewrite decompose_app_lift using auto : lift.

Lemma lift_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (lift n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl.
  unfold isConstruct_app in *. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->.
  destruct t0; try discriminate || reflexivity.
Qed.
#[export] Hint Resolve lift_is_constructor : core.

#[global]
Hint Rewrite subst_instance_lift lift_mkApps distr_lift_subst distr_lift_subst10 : lift. *)

Definition lift_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => lift n (k' + k)) m.

Lemma lift_fix_context:
  forall (mfix : list (def term)) (n k : nat),
    fix_context (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) = lift_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rw PCUICLiftSubst.map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rw (lift_context_alt n k (fix_context mfix)).
  unfold lift_decl. now rw mapi_length fix_context_length.
Qed.

#[global]
Hint Rewrite <- lift_fix_context : lift.

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
#[global]
Hint Rewrite lift_it_mkProd_or_LetIn : lift.

Lemma to_extended_list_map_lift:
  forall (n k : nat) (c : context), to_extended_list c = map (lift n (#|c| + k)) (to_extended_list c).
Proof.
  intros n k c.
  pose proof (to_extended_list_lift_above c). unf_term.
  symmetry. solve_all.
  destruct H as [x' [-> Hx]]. simpl.
  destruct (leb_spec_Set (#|c| + k) x').
  - f_equal. lia.
  - reflexivity.
Qed.

Lemma weakening_red1 `{cf:checker_flags} {Σ} Γ Γ' Γ'' M N :
  wf Σ ->
  on_free_vars xpredT M ->
  red1 Σ (Γ ,,, Γ') M N ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros.
  rw !lift_rename.
  eapply red1_rename; eauto.
  eapply weakening_renaming.
Qed.

Lemma weakening_red `{cf:checker_flags} {Σ:global_env_ext} {wfΣ : wf Σ} {P Γ Γ' Γ'' M N} :
  on_ctx_free_vars P (Γ ,,, Γ') ->
  on_free_vars P M ->
  red Σ (Γ ,,, Γ') M N ->
  red Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros.
  rw !lift_rename.
  eapply red_rename; eauto.
  eapply weakening_renaming.
Qed.

Lemma weakening_red' `{cf:checker_flags} {Σ:global_env_ext} {wfΣ : wf Σ} {P Γ Γ' Γ'' M N} :
  on_ctx_free_vars P (Γ ,,, Γ') ->
  on_free_vars P M ->
  red Σ (Γ ,,, Γ') M N ->
  red Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  now eapply weakening_red.
Qed.

Lemma weakening_red_0 {cf} {Σ:global_env_ext} {wfΣ : wf Σ} {P Γ Γ' M N n} :
  n = #|Γ'| ->
  on_ctx_free_vars P Γ ->
  on_free_vars P M ->
  red Σ Γ M N ->
  red Σ (Γ ,,, Γ') (lift0 n M) (lift0 n N).
Proof. move=> -> onctx ont; eapply (weakening_red (Γ':=[])); tea. Qed.

(* TODO MOVE *)
(* Lemma fix_context_alt_length :
  forall l,
    #|fix_context_alt l| = #|l|.
Proof.
  intro l.
  unfold fix_context_alt.
  rewrite List.length_rev.
  rewrite mapi_length. reflexivity.
Qed. *)

Lemma weakening_cumul `{CF:checker_flags} {Σ Γ Γ' Γ'' M N} :
  wf Σ.1 ->
  on_free_vars xpredT M ->
  on_free_vars xpredT N ->
  on_ctx_free_vars xpredT (Γ ,,, Γ') ->
  Σ ;;; Γ ,,, Γ' |- M <= N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M <= lift #|Γ''| #|Γ'| N.
Proof.
  intros.
  rw !lift_rename -rename_context_lift_context.
  eapply cumul_renameP ; tea.
  rw rename_context_lift_context.
  now eapply weakening_renaming.
Qed.

(* Lemma destInd_lift n k t : destInd (lift n k t) = destInd t.
Proof.
  destruct t; simpl; try congruence.
Qed. *)

Lemma weakening_conv `{cf:checker_flags} :
  forall Σ Γ Γ' Γ'' M N,
    wf Σ.1 ->
    on_free_vars xpredT M ->
    on_free_vars xpredT N ->
    on_ctx_free_vars xpredT (Γ ,,, Γ') ->
    Σ ;;; Γ ,,, Γ' |- M = N ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M = lift #|Γ''| #|Γ'| N.
Proof.
  intros.
  rw !lift_rename -rename_context_lift_context.
  eapply conv_renameP ; tea.
  rw rename_context_lift_context.
  now eapply weakening_renaming.
Qed.

Lemma isType_on_free_vars {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T} :
  isType Σ Γ T -> on_free_vars xpredT T.
Proof.
  intros (_ & s & Hs & _).
  eapply subject_closed in Hs.
  rw closedP_on_free_vars in Hs.
  eapply on_free_vars_impl; tea => //.
Qed.

Lemma isType_on_ctx_free_vars {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T} :
  isType Σ Γ T -> on_ctx_free_vars xpredT Γ.
Proof.
  intros (_ & s & Hs & _).
  eapply typing_wf_local in Hs.
  eapply closed_wf_local in Hs; tea.
  eapply (closed_ctx_on_free_vars xpredT) in Hs.
  now eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
Qed.

Lemma weakening_conv_wt `{cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ'' M N} :
  isType Σ (Γ ,,, Γ') M -> isType Σ (Γ ,,, Γ') N ->
  Σ ;;; Γ ,,, Γ' |- M = N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M = lift #|Γ''| #|Γ'| N.
Proof.
  intros onM onN.
  eapply weakening_conv; tea.
  1-2:now eapply isType_on_free_vars.
  now eapply isType_on_ctx_free_vars in onM.
Qed.
