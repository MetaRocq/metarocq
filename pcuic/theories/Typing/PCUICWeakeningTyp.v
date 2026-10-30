(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICCumulativity
  PCUICClosed
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICRenameTyp PCUICOnFreeVars
  PCUICClosedConv PCUICClosedTyp PCUICWeakeningConv.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Implicit Types cf : checker_flags.

(** * Weakening lemmas for typing derivations.

  [weakening_*] proves weakening of typing, reduction etc... w.r.t. the *local*
  environment. *)

Set Default Goal Selector "!".
Generalizable Variables Σ Γ t T.

Lemma weakening_wf_local {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} :
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ').
Proof.
  intros wfΓ' wfΓ''.
  pose proof (env_prop_wf_local typing_rename_prop _ wfΣ _ wfΓ') as X. simpl in X.
  eapply All_local_env_app_inv in X as [XΓ XΓ'].
  apply All_local_env_app => //.
  rw /lift_context.
  apply All_local_env_fold.
  eapply (All_local_env_impl_ind XΓ').
  intros Δ j IH H; simpl.
  eapply lift_typing_f_impl => //.
  2: intros ?? Hf; rw -/(lift_context #|Γ''| 0 Δ).
  2: rw Nat.add_0_r; rw !lift_rename; apply Hf.
  eapply (H xpredT).
  split.
  + apply All_local_env_app; auto.
    apply All_local_env_fold, IH.
  + apply weakening_renaming.
Qed.

Lemma weakening_wf_local_eq {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ'' n} :
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->
  n = #|Γ''| ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context n 0 Γ').
Proof.
  intros ? ? ->; now apply weakening_wf_local.
Qed.

Lemma weakening_rename_typing `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} {t T} :
  wf_local Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |- t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, rename_context (lift_renaming #|Γ''| 0) Γ' |-
    rename (lift_renaming #|Γ''| #|Γ'|) t :
    rename (lift_renaming #|Γ''| #|Γ'|) T.
Proof.
  intros wfext Ht.
  eapply (typing_rename); eauto; rw rename_context_lift_context.
  - eapply weakening_wf_local; cbn; eauto with pcuic.
  - now apply weakening_renaming.
Qed.

Lemma weakening_typing `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} {t T} :
  wf_local Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |- t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T.
Proof.
  intros wfext Ht.
  rw !lift_rename.
  eapply (typing_rename); eauto.
  - eapply weakening_wf_local; eauto with pcuic.
  - now apply weakening_renaming.
Qed.

Lemma weakening `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  wf Σ.1 -> wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  eapply (weakening_typing (Γ' := [])); eauto.
Qed.

Lemma weaken_wf_local {cf:checker_flags} {Σ Δ} Γ :
  wf Σ.1 ->
  wf_local Σ Γ ->
  wf_local Σ Δ -> wf_local Σ (Γ ,,, Δ).
Proof.
  intros wfΣ wfΓ wfΔ.
  generalize (weakening_wf_local (Γ := []) (Γ'' := Γ) (Γ' := Δ)) => /=.
  rw !app_context_nil_l.
  move/(_ wfΔ wfΓ).
  rw closed_ctx_lift //.
  now eapply closed_wf_local.
Qed.


Lemma lift_declared_constant `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_constant Σ cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  intros wf declc.
  rw /map_constant_body; destruct decl; simpl; f_equal; rw ?lift_rename.
  - eapply declared_constant_closed_type in declc; eauto.
    now rw rename_closed.
  - destruct cst_body0 eqn:cb => /= //.
    f_equal.
    eapply declared_constant_closed_body in declc; simpl; eauto.
    now rw lift_rename rename_closed.
Qed.


(** Variant with more freedom on the length to apply it in backward-chainings. *)
Lemma weakening_length {cf:checker_flags} Σ Γ Γ' t T n :
  wf Σ.1 ->
  n = #|Γ'| ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof. intros wfΣ ->; now apply weakening. Qed.

Lemma weaken_ctx {cf:checker_flags} {Σ Γ t T} Δ :
  wf Σ.1 ->
  wf_local Σ Δ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Δ ,,, Γ |- t : T.
Proof.
  intros wfΣ wfΔ ty.
  epose proof (weakening_typing (Γ := [])).
  rw !app_context_nil_l in X.
  forward X by eauto using typing_wf_local.
  specialize (X ty).
  eapply typecheck_closed in ty as [_ [clΓ [clt clT]%andb_and]]; auto.
  rw !lift_closed // in X.
  now rw closed_ctx_lift in X.
Qed.

Lemma weakening_gen : forall (cf : checker_flags) (Σ : global_env_ext)
  (Γ Γ' : context) (t T : term) n, n = #|Γ'| ->
  wf Σ ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ;;; Γ |- t : T -> Σ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof.
  intros ; subst n; now apply weakening.
Qed.

(** Convenience lemma when going through instantiation for renaming.
    Δ is arbitrary here, it does not have to be the weakening of some other context. *)
Lemma shift_typing {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t T n Δ} :
  Σ ;;; Γ |- t : T ->
  wf_local Σ (Γ ,,, Δ) ->
  n = #|Δ| ->
  Σ ;;; Γ ,,, Δ |- t.[↑^n] : T.[↑^n].
Proof.
  intros ht hΔ ->.
  eapply meta_conv_all. 3-4:now rw -rename_inst -lift0_rename.
  2:reflexivity.
  eapply weakening_gen => //.
Qed.

Lemma lift_typing_weakening {cf : checker_flags} Σ Γ Γ' j :
  wf Σ.1 -> wf_local Σ (Γ ,,, Γ') ->
  lift_typing typing Σ Γ j ->
  lift_typing typing Σ (Γ ,,, Γ') (judgment_map (lift0 #|Γ'|) j).
Proof.
  intros wfΣ wfΓ Hj.
  apply lift_typing_f_impl with (1 := Hj) => // t T.
  now apply weakening.
Qed.

Lemma lift_typing_weaken_ctx {cf : checker_flags} Σ Γ Δ j :
  wf Σ.1 -> wf_local Σ Δ ->
  lift_typing typing Σ Γ j ->
  lift_typing typing Σ (Δ ,,, Γ) j.
Proof.
  intros wfΣ wfΔ Hj.
  apply lift_typing_impl with (1 := Hj) => t T.
  now apply weaken_ctx.
Qed.

Corollary All_mfix_wf {cf:checker_flags} Σ Γ mfix :
  wf Σ.1 -> wf_local Σ Γ ->
  All (fun d : def term => isTypeRel Σ Γ (dtype d) (dname d).(binder_relevance)) mfix ->
  wf_local Σ (Γ ,,, fix_context mfix).
Proof.
  move=> wfΣ wf a; move: wf.
  change (fix_context mfix) with (fix_context_gen #|@nil context_decl| mfix).
  change Γ with (Γ ,,, []).
  generalize (@nil context_decl) as Δ.
  rw /fix_context_gen.
  intros Δ wfΔ.
  eapply All_local_env_app; auto.
  induction a in Δ, wfΔ |- *; simpl; auto.
  1: now constructor.
  simpl.
  eapply All_local_env_app; auto.
  * constructor. 1: constructor.
    now eapply lift_typing_weakening in p.
  * specialize (IHa (Δ ,,, [vass (dname x) (lift0 #|Δ| (dtype x))])).
    rw length_app in IHa. simpl in IHa.
    forward IHa.
    + simpl; constructor; auto.
      now eapply lift_typing_weakening in p.
    + eapply All_local_env_impl; eauto.
      simpl; intros.
      rw app_context_assoc. apply X.
Qed.

Lemma lift_typing_weakening_skipn {cf:checker_flags} {Σ : global_env_ext} {n Γ j}
  (isdecl : n <= #|Γ|) :
  wf Σ -> wf_local Σ Γ ->
  lift_typing typing Σ (skipn n Γ) j ->
  lift_typing typing Σ Γ (judgment_map (lift0 n) j).
Proof.
  intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
  assert (n = #|firstn n Γ|).
  { rw firstn_length_le; auto with arith. }
  rw {3}H.
  now eapply lift_typing_weakening in wfty.
Qed.

Lemma All_local_env_nth_error_weaken {cf:checker_flags} {Σ : global_env_ext} {Γ n decl} :
  wf Σ -> wf_local Σ Γ ->
  nth_error Γ n = Some decl ->
  lift_typing typing Σ Γ (j_decl (map_decl (lift0 (S n)) decl)).
Proof using Type.
  intros hΣ hΓ e.
  eapply All_local_env_nth_error in e as hj; tea.
  apply nth_error_Some_length in e.
  now apply lift_typing_weakening_skipn in hj.
Qed.

Lemma isType_lift {cf:checker_flags} {Σ : global_env_ext} {n Γ ty}
  (isdecl : n <= #|Γ|):
  wf Σ -> wf_local Σ Γ ->
  isType Σ (skipn n Γ) ty ->
  isType Σ Γ (lift0 n ty).
Proof.
  now apply @lift_typing_weakening_skipn with (j := Typ _).
Qed.

Lemma isTypeRel_lift {cf:checker_flags} {Σ : global_env_ext} {n Γ ty r}
  (isdecl : n <= #|Γ|):
  wf Σ -> wf_local Σ Γ ->
  isTypeRel Σ (skipn n Γ) ty r ->
  isTypeRel Σ Γ (lift0 n ty) r.
Proof.
  now apply @lift_typing_weakening_skipn with (j := TypRel _ _).
Qed.
