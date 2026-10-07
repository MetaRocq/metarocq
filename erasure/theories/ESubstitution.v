
(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping
     PCUICGlobalEnv PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution
     PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICOnFreeVars PCUICElimination PCUICFirstorder.
From MetaRocq.Erasure Require Import EGlobalEnv Extract Prelim.

Local Set Keyed Unification.

Local Existing Instance config.extraction_checker_flags.

(** ** Global Weakening  *)

Lemma Is_type_extends (Σ : global_env_ext) Γ t :
  wf_local Σ Γ ->
  forall (Σ' : global_env), wf Σ -> wf Σ' -> PCUICEnvironment.extends Σ Σ' -> isErasable Σ Γ t -> isErasable (Σ', Σ.2) Γ t.
Proof.
  intros X0 Σ' X1 X2 ext [T []]. destruct Σ as [Σ]. cbn in *.
  exists T. split. change u with (snd (Σ,u)).
  eapply weakening_env; eauto.
  destruct s; eauto.
  destruct s as (u' & ? & ?).
  right. exists u'. split; eauto.
  change u with (snd (Σ,u)).
  eapply weakening_env; eauto.
Qed.

Lemma Is_proof_extends (Σ : global_env_ext) Γ t :
  wf_local Σ Γ ->
  forall Σ', wf Σ -> wf Σ' -> PCUICEnvironment.extends Σ Σ' -> Is_proof Σ Γ t -> Is_proof (Σ',Σ.2) Γ t.
Proof.
  intros X0 Σ' X1 X2 ext (x & x0 & ? & ? & ?).
  exists x, x0. repeat split; eauto.
  eapply weakening_env; eauto.
  eapply weakening_env; eauto.
Qed.

(* TODO: Figure out whether this lemma (and [Subsingleton]) should use [strictly_extends_decls] or [extends]. -Jason Gross *)
Lemma Subsingleton_extends:
  forall (Σ : global_env_ext) (ind : inductive)
    (mdecl : PCUICAst.PCUICEnvironment.mutual_inductive_body) (idecl : PCUICAst.PCUICEnvironment.one_inductive_body),

    PCUICAst.declared_inductive (fst Σ) ind mdecl idecl ->
    forall (Σ' : global_env),
      wf Σ' ->
      strictly_extends_decls Σ Σ' ->
      Subsingleton Σ ind -> Subsingleton (Σ', Σ.2) ind.
Proof.
  repeat intros ?.
  assert (strictly_extends_decls Σ Σ'0).
  { etransitivity; [ eassumption | ].
    repeat match goal with H : strictly_extends_decls _ _ |- _ => destruct H end.
    split; eauto. }
  edestruct H0; eauto. destruct H3.

  eapply weakening_env_declared_inductive in H; eauto; tc.
  destruct H, H1.
  pose (X1' := X1.1). unshelve eapply declared_minductive_to_gen in H, H1; eauto.
  eapply PCUICWeakeningEnv.extends_lookup in H1.
  3:{ cbn. apply extends_refl. } 2:eauto.
  unfold declared_minductive_gen in *.
  rewrite H1 in H. inversion H. subst. clear H.
  rewrite H3 in H4. inversion H4. subst. clear H4.
  split. eauto. econstructor. eauto.
Qed.

From Stdlib Require Import ssrbool.

(* TODO: Figure out whether this lemma (and [erases]) should use [strictly_extends_decls] or [extends]. -Jason Gross *)
Lemma erases_extends :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> strictly_extends_decls Σ Σ' -> forall t', erases Σ Γ t t' -> erases (Σ', Σ.2) Γ t t')
           (fun Σ Γ j =>
              forall Σ', wf Σ' -> strictly_extends_decls Σ Σ' ->
              lift_wf_term (fun t => forall t', erases Σ Γ t t' -> erases (Σ', Σ.2) Γ t t') j)
           (fun Σ Γ => wf_local Σ Γ).
Proof.
  apply typing_ind_env; intros; rename_all_hyps; auto.
  { destruct X as (Htm & s & (_ & Hty) & _). split; eauto. destruct j_term => //. cbn in *. now eapply Htm. }
  all: match goal with [ H : erases _ _ ?a _ |- _ ] => tryif is_var a then idtac else inv H end.
  all: try now (econstructor; eauto).
  all: try now (econstructor; eapply Is_type_extends; eauto; tc).
  - edestruct forall_Σ' as [Htm _]; tea. cbn in Htm.
    econstructor; eauto.
  - econstructor.
    move: H4; apply contraNN.
    unfold isPropositional.
    unfold PCUICAst.lookup_inductive.
    unshelve eapply declared_constructor_to_gen in isdecl; eauto.
    rewrite (PCUICAst.declared_inductive_lookup_gen isdecl.p1).
    destruct isdecl as [decli declc].
    eapply declared_inductive_from_gen in decli.
    eapply PCUICWeakeningEnv.weakening_env_declared_inductive in decli; tea; eauto; tc.
    unfold PCUICAst.lookup_inductive.
    unshelve eapply declared_inductive_to_gen in decli; eauto.
    now rewrite (PCUICAst.declared_inductive_lookup_gen decli).
  - econstructor. all:eauto.
    eapply Subsingleton_extends; eauto.
    eapply All2i_All2_All2; tea. cbv beta.
    intros n cdecl br br'.
    intros (? & ? & (? & ?) & (? & ?)) (? & ?); split; auto.
    rewrite <-(PCUICCasesContexts.inst_case_branch_context_eq a).
    eapply e; tea.
    now rewrite [_.1](PCUICCasesContexts.inst_case_branch_context_eq a).
  - econstructor. destruct isdecl. 2:eauto.
    eapply Subsingleton_extends; eauto. exact H.p1.
  - econstructor.
    eapply All2_All_mix_left in X3; eauto.
    eapply All2_impl. exact X3.
    intros ? ? [? [? []]]; tea.
    split; eauto. eapply o; eauto.
  - econstructor.
    eapply All2_All_mix_left in X3; eauto.
    eapply All2_impl. exact X3.
    intros ? ? [? [? []]]; tea.
    repeat split; eauto. now eapply o.
  - econstructor.
    induction H3; constructor.
    induction X2; constructor; depelim X1; eauto.
    depelim X0.
    eapply All2_All_mix_left in a0; eauto.
    eapply All2_impl. exact a0.
    cbn. intros ? ? [? ?]. eauto.
Qed.

Lemma erases_extends' (Σ:global_env_ext) Γ t T:
  wf Σ -> Σ ;;; Γ |- t : T ->
    forall Σ', wf Σ' -> strictly_extends_decls Σ Σ' -> forall t', erases Σ Γ t t' -> erases (Σ', Σ.2) Γ t t'.
Proof.
  intro; eapply erases_extends; eauto.
Defined.

(** ** Weakening *)

Lemma Is_type_weakening:
  forall (Σ : global_env_ext) (Γ Γ' Γ'' : context),
    wf_local Σ (Γ ,,, Γ') ->
    wf Σ ->
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    forall t : PCUICAst.term,
      isErasable Σ (Γ ,,, Γ') t -> isErasable Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| t).
Proof.
  intros. destruct X2 as (T & ? & ?).
  eexists. split. eapply weakening_typing; eauto.
  now apply All_local_env_app_inv in X1.

  destruct s as [? | [u []]].
  - left. clear - i. generalize (#|Γ''|), (#|Γ'|). induction T; cbn in *; intros; try now inv i.
  - right. exists u. split; eauto.
    eapply weakening_typing in t1; eauto.
    now apply All_local_env_app_inv in X1.
Qed.

From MetaRocq Require Import PCUIC.PCUICInversion.
Derive Signature for erases.

Lemma erases_ctx_ext (Σ : global_env_ext) Γ Γ' t t' :
  erases Σ Γ t t' -> Γ = Γ' -> erases Σ Γ' t t'.
Proof.
  intros. now subst.
Qed.

Lemma lift_inst_case_branch_context (Γ'' Γ' : context) p br :
  test_context_k
  (fun k : nat => on_free_vars (closedP k xpredT))
  #|pparams p| (bcontext br) ->
  inst_case_branch_context (map_predicate_k id (lift #|Γ''|) #|Γ'| p)
    (map_branch_k (lift #|Γ''|) id #|Γ'| br) =
    lift_context #|Γ''| #|Γ'| (inst_case_branch_context p br).
Proof.
  intros hctx.
  rewrite /inst_case_branch_context /= /id.
  rewrite -rename_context_lift_context.
  rewrite PCUICRenameConv.rename_inst_case_context_wf //.
  f_equal. apply map_ext => x.
  now setoid_rewrite <- PCUICSigmaCalculus.lift_rename.
Qed.

Lemma lift_isLambda n k t : isLambda t = isLambda (lift n k t).
Proof.
  destruct t => //.
Qed.

Lemma erases_weakening' (Σ : global_env_ext) (Γ Γ' Γ'' : context) (t T : term) t' :
    wf Σ ->
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    Σ ;;; Γ ,,, Γ' |- t : T ->
    Σ ;;; Γ ,,, Γ' |- t ⇝ℇ t' ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- (lift #|Γ''| #|Γ'| t) ⇝ℇ (ELiftSubst.lift #|Γ''| #|Γ'| t').
Proof.
  intros HΣ HΓ'' * H He.
  remember (Γ ,,, Γ') as Γ0 eqn:eqw.
  revert Γ Γ' Γ'' HΓ'' eqw t' He.
  revert Σ HΣ Γ0 t T H .
  apply (typing_ind_env (fun Σ Γ0 t T =>  forall Γ Γ' Γ'',
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    Γ0 = Γ ,,, Γ' ->
    forall t',
    Σ;;; Γ0 |- t ⇝ℇ t' ->
    _)
    (fun Σ Γ0 j =>  forall Γ Γ' Γ'',
      wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
      Γ0 = Γ ,,, Γ' ->
      lift_wf_term (fun t => forall t',
        Σ;;; Γ0 |- t ⇝ℇ t' -> Σ;;; Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t ⇝ℇ ELiftSubst.lift #|Γ''| #|Γ'| t')j )
    (fun Σ Γ => wf_local Σ Γ)
    );
    intros Σ wfΣ Γ0; intros; try subst Γ0; auto.
  { destruct X as (Htm & s & (_ & Hty) & _). split; eauto. destruct j_term => //. cbn in *. now eapply Htm. }
  all: match goal with [ H : erases _ _ ?a _ |- _ ] => tryif is_var a then idtac else inv H end.
  all: try now (cbn; econstructor; eauto).
  all: try now (econstructor; eapply Is_type_weakening; eauto).
  all:cbn.
  - destruct ?; econstructor.
  - econstructor.
    unfold app_context, snoc in *.
    pose proof (H Γ (vass na t :: Γ') Γ'').
    rewrite lift_context_snoc0 - plus_n_O in H0.
    eapply H0; eauto. cbn. econstructor.
    eauto. cbn. eapply lift_typing_f_impl with (1 := X0) => // ??. eapply weakening_typing.
    now apply All_local_env_app_inv in X3.
  - econstructor.
    + edestruct X1 as [Htm _]; tea; eauto.
    + pose proof (H Γ (vdef na b b_ty :: Γ') Γ'').
      rewrite lift_context_snoc0 -plus_n_O in H0.
      eapply H0; eauto. cbn. econstructor.
      eauto.
      eapply lift_typing_f_impl with (1 := X0) => // ??.
      eapply weakening_typing.
      now apply All_local_env_app_inv in X3.
  - econstructor.
    + eauto.
    + eapply H5; eauto.
    + red in H7.
      eapply Forall2_All2 in H7.
      eapply All2i_All2_mix_left in X6; tea.
      clear H6.
      eapply All2i_nth_hyp in X6.
      eapply All2_map.
      eapply All2i_All2_All2; tea; cbv beta.
      intros n cdecl br br'.
      intros (hnth & ? & ? & ? & (? & ?) & ? & ?) []. split => //.
      rewrite lift_inst_case_branch_context //.
      { rewrite test_context_k_closed_on_free_vars_ctx.
        eapply alpha_eq_on_free_vars. symmetry; tea.
        rewrite -closedn_ctx_on_free_vars.
        rewrite (wf_predicate_length_pars H0).
        rewrite (declared_minductive_ind_npars isdecl).
        eapply PCUICClosedTyp.closed_cstr_branch_context; tea. split; tea. }
      rewrite -app_context_assoc -{1}(Nat.add_0_r #|Γ'|) -(lift_context_app _ 0).
      assert (#|inst_case_branch_context p br| = #|bcontext br|).
      { rewrite /inst_case_branch_context. now len. }
      rewrite /map_branch_k /= -H6 -length_app.
      rewrite -e2 length_map -H6 -length_app.
      rewrite -(PCUICCasesContexts.inst_case_branch_context_eq a).
      eapply e.
      eapply weakening_wf_local => //.
      rewrite app_context_assoc //.
      now eapply All_local_env_app_inv in X7 as [].
      rewrite app_context_assoc. reflexivity.
      now rewrite [_.1](PCUICCasesContexts.inst_case_branch_context_eq a).
  - assert (HT : Σ;;; Γ ,,, Γ' |- PCUICAst.tFix mfix n : (decl.(dtype))).
    econstructor; eauto.

    eapply weakening_typing in HT; auto.
    2:{ apply All_local_env_app_inv in X4 as [X4 _]. eapply X4. }

    cbn in HT.
    eapply inversion_Fix in HT as (? & ? & ? & ? & ? & ? & ?) ; auto.
    clear a0 e.
    econstructor.
    eapply All2_map.
    eapply All2_impl. eapply All2_All_mix_left.
    eapply X3. eassumption. simpl.
    intros [] []. simpl. intros [IH [<- <- IH']].
    repeat split. unfold app_context in *.
    eapply isLambda_lift => //.
    eapply ELiftSubst.isLambda_lift => //.
    specialize (IH Γ (types ++ Γ') Γ'').
    subst types. rewrite length_app fix_context_length in IH.
    forward IH.
    { rewrite lift_context_app -plus_n_O. unfold app_context.
      eapply All_mfix_wf in a; auto.
      rewrite lift_fix_context in a.
      now rewrite <- !app_assoc. }
    forward IH. now rewrite [_ ,,, _]app_assoc.
    rewrite lift_fix_context.
    rewrite lift_context_app - plus_n_O in IH.
    unfold app_context in IH. rewrite <- !app_assoc in IH.
    rewrite (All2_length X5) in IH |- *.
    apply IH. apply e.

  - assert (HT : Σ;;; Γ ,,, Γ' |- PCUICAst.tCoFix mfix n : (decl.(dtype))).
    econstructor; eauto.

    eapply weakening_typing in HT; auto.
    2:{ apply All_local_env_app_inv in X4 as [X4 _]. eapply X4. }

    cbn in HT.
    eapply inversion_CoFix in HT as (? & ? & ? & ? & ? & ? & ?) ; auto. clear a0 e.

    econstructor.
    eapply All2_map.
    eapply All2_impl. eapply All2_All_mix_left.
    eapply X3. eassumption. simpl.
    intros [] []. simpl. intros [IH [<- [<- IH']]].
    repeat split. unfold app_context in *.
    specialize (IH Γ (types ++ Γ') Γ'').
    subst types. rewrite length_app fix_context_length in IH.
    forward IH.
    { rewrite lift_context_app -plus_n_O. unfold app_context.
      eapply All_mfix_wf in a; auto.
      rewrite lift_fix_context in a.
      now rewrite <- !app_assoc. }
    forward IH by now rewrite /app_context app_assoc.
    rewrite lift_fix_context.
    rewrite lift_context_app -plus_n_O in IH.
    unfold app_context in IH. rewrite <- !app_assoc in IH.
    rewrite (All2_length X5) in IH |- *.
    apply IH. apply IH'.

  - econstructor. depelim H4.
    depelim X3; repeat constructor.
    depelim X1; cbn. now eapply hdef.
    depelim X1. cbn. eapply All2_map.
    ELiftSubst.solve_all.
Qed.

Lemma erases_weakening (Σ : global_env_ext) (Γ Γ' : context) (t T : PCUICAst.term) t' :
  wf Σ ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t ⇝ℇ t' ->
  Σ ;;; Γ ,,, Γ' |- (lift #|Γ'| 0 t) ⇝ℇ (ELiftSubst.lift #|Γ'| 0 t').
Proof.
  intros.
  pose proof (typing_wf_local X1).
  eapply (erases_weakening' Σ Γ [] Γ'); cbn; eauto.
Qed.

Derive Signature for subslet.

Lemma is_type_subst (Σ : global_env_ext) Γ Γ' Δ a s :
  wf Σ -> subslet Σ Γ s Γ' ->
  (* Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  isErasable Σ (Γ ,,, Γ' ,,, Δ) a ->
  isErasable Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| a).
Proof.
  intros ? ? ? (T & HT & H).
  exists (subst s #|Δ| T). split.
  eapply substitution; eauto.
  destruct H as [ | (u & ? & ?) ].
  - left. generalize (#|Δ|). intros n.
    induction T in n, i |- *; (try now inv i); cbn in *; eauto.
  - right. exists u. split; eauto.
    eapply substitution in t; eauto.
Qed.

Local Ltac depelim_subslet H :=
  depelim_nosimpl H;
  try match goal with
  | |- _ :: _ = _ :: _ -> _ =>
    let Heq := fresh in intro Heq; apply cons_inj in Heq as [? ?]; subst
  end;
  simpl_dep_elim; unblock_goal.

Lemma substlet_typable (Σ : global_env_ext) Γ s Γ' n t :
  subslet Σ Γ s Γ' -> nth_error s n = Some t -> {T & Σ ;;; Γ |- t : T}.
Proof.
  induction n in s, t, Γ, Γ' |- *; intros; cbn in *.
  - destruct s. inv H.
    inv H. depelim_subslet X; eauto.
  - destruct s; inv H.
    depelim_subslet X. eapply IHn in H1. eauto.  eauto.
    eauto.
Qed.

Lemma erases_eq (Σ : global_env_ext) Γ Γ' t t' s s' :
  erases Σ Γ t t' ->
  Γ = Γ' ->
  t = s ->
  t' = s' ->
  erases Σ Γ' s s'.
Proof.
  now subst.
Qed.

Lemma subst_case_branch_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} ind (n : nat) mdecl idecl p br cdecl s k :
  PCUICAst.declared_constructor Σ (ind, n) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  PCUICEquality.eq_context_upto_names (bcontext br)
    (cstr_branch_context ind mdecl cdecl) ->
  subst_context s k (case_branch_context ind mdecl p (forget_types (bcontext br)) cdecl) =
  case_branch_context ind mdecl (map_predicate_k id (subst s) k p) (forget_types (bcontext br)) cdecl.
Proof.
  intros decl wfp a.
  rewrite (PCUICCasesContexts.inst_case_branch_context_eq a).
  rewrite subst_inst_case_context_wf.  rewrite test_context_k_closed_on_free_vars_ctx.
  eapply alpha_eq_on_free_vars. symmetry; eassumption.
  rewrite (wf_predicate_length_pars wfp).
  rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decl).  rewrite -closedn_ctx_on_free_vars.
  eapply PCUICClosedTyp.closed_cstr_branch_context; tea.
  epose proof (PCUICCasesContexts.inst_case_branch_context_eq (p := subst_predicate s k p) a).
  now rewrite H.
Qed.

Lemma erases_subst (Σ : global_env_ext) Γ Γ' Δ t s t' s' T :
  wf Σ ->
  subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- t ⇝ℇ t' ->
  All2 (erases Σ Γ) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Δ) |- (subst s #|Δ| t) ⇝ℇ ELiftSubst.subst s' #|Δ| t'.
Proof.
  intros HΣ HΔ Hs Ht He.
  remember (Γ ,,, Γ' ,,, Δ) as Γ0 eqn:eqw in Ht.
  revert Γ Γ' Δ t' s Hs HΔ He eqw.
  revert Σ HΣ Γ0 t T Ht.
  eapply (typing_ind_env (fun Σ Γ0 t T =>
                            forall (Γ Γ' : context) Δ t' (s : list PCUICAst.term),
                              wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
                              subslet Σ Γ s Γ' ->
                              Σ;;; Γ ,,, Γ' ,,, Δ |- t ⇝ℇ t' ->
                              Γ0 = Γ ,,, Γ' ,,, Δ ->
                              All2 (erases Σ Γ) s s' ->
                              Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t ⇝ℇ ELiftSubst.subst s' #|Δ| t'
         )
         (fun Σ Γ0 j =>
            forall (Γ Γ' : context) Δ t' (s : list PCUICAst.term),
            wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
            subslet Σ Γ s Γ' ->
            Γ0 = Γ ,,, Γ' ,,, Δ ->
            All2 (erases Σ Γ) s s' ->
            lift_wf_term (fun t =>
            Σ;;; Γ ,,, Γ' ,,, Δ |- t ⇝ℇ t' ->
            Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t ⇝ℇ ELiftSubst.subst s' #|Δ| t') j
         )
         (fun Σ Γ0 => wf_local Σ Γ0)
         );
    intros Σ wfΣ Γ0 wfΓ0; intros; simpl in * |-; auto; subst Γ0.
  { destruct X as (Htm & u & (_ & Hty) & _). split; eauto. destruct j_term => // ?. cbn in *. now eapply Htm. }
  - inv H0.
    + cbn. destruct ?. destruct ?.
      * eapply All2_nth_error_Some in X2; eauto.
        destruct X2 as (? & ? & ?).
        rewrite e.
        erewrite <- subst_context_length.
        eapply substlet_typable in X1 as []. 2:exact E0.
        eapply erases_weakening; eauto.
      * erewrite All2_length; eauto.
        eapply All2_nth_error_None in X2; eauto.
        rewrite X2. econstructor.
      * econstructor.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H0. econstructor. eapply is_type_subst; eauto.
  - inv H0. econstructor.
    eapply is_type_subst; eauto.
  - inv H0.
    + cbn. econstructor.
      specialize (H Γ Γ' (vass na t :: Δ) t'0 s).
      (* unfold app_context, snoc in *. *)
      rewrite subst_context_snoc0 in H.
      eapply H; eauto.
      cbn. econstructor. eauto.
      eapply lift_typing_f_impl with (1 := X0) => // ??. now eapply substitution.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H0.
    + cbn. econstructor.
      now edestruct X1; tea; eauto.
      specialize (H Γ Γ' (vdef na b b_ty :: Δ) t2' s).
      rewrite subst_context_snoc0 in H.
      eapply H; eauto.
      cbn. econstructor. eauto.
      eapply lift_typing_f_impl with (1 := X0) => // ??. now eapply substitution.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H2.
    + cbn. econstructor.
      eapply H0; eauto.
      eapply H1; eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H0. econstructor.
    eapply is_type_subst; eauto.
  - inv H0.
    + cbn. econstructor; auto.
    + econstructor.
      eapply is_type_subst; eauto.
  - depelim H8.
    + cbn. econstructor.
      * eauto.
      * eapply H5; eauto.
      * eapply All2_map.
        eapply All2_impl_In; eauto.
        intros. destruct H12, x, y. cbn in e0. subst. split; eauto.
        eapply In_nth_error in H10 as [].
        move: H7. rewrite /wf_branches.
        move/Forall2_All2 => hbrs.
        eapply All2_nth_error_Some_r in hbrs; tea.
        set (br := {| bcontext := _ |}).
        destruct hbrs as [cdecl [hnth wfbr]].
        eapply All2i_nth_error_r in X6; eauto.
        destruct X6 as (cdecl' & hnth' & eqctx & wfctx & (? & ?) & ? & ?).
        rewrite hnth in hnth'. depelim hnth'.
        move: e0. cbn -[inst_case_branch_context].
        intros e0.
        eapply typing_wf_local in t0.
        cbn in t0. move: t0.
        rewrite -/(app_context _ _).
        rewrite -app_context_assoc.
        move/(substitution_wf_local X8) => hwf.
        specialize (e0 _ _ _ t _ hwf X8).
        len in e0. cbn in e0.
        have := PCUICCasesContexts.inst_case_branch_context_eq (p:=p) eqctx => H7.
        rewrite /inst_case_branch_context /= in H7.
        forward e0.
        { move: e. cbn. rewrite /inst_case_branch_context /= -H7.
          now rewrite app_context_assoc. }
        forward e0.
        { now rewrite app_context_assoc. }
        forward e0 by tas.
        have:= (PCUICCasesContexts.inst_case_branch_context_eq (p:= (map_predicate_k (fun x0 : Instance.t => x0) (subst s) #|Δ| p))eqctx).
        cbn. rewrite /inst_case_branch_context /= => <-.
        move: e0.
        rewrite subst_context_app.
        rewrite /map_branch_k /= /id.
        rewrite /case_branch_context /case_branch_context_gen /=.
        rewrite map2_length. len.
        eapply Forall2_length in wfbr. now cbn in wfbr; len in wfbr.
        rewrite length_map Nat.add_0_r.
        rewrite -/(case_branch_context_gen ci mdecl (pparams p) (puinst p) (map decl_name bcontext) cdecl').
        rewrite -/(case_branch_context ci mdecl p (forget_types bcontext) cdecl').
        rewrite (subst_case_branch_context _ x _ idecl _ br) // length_map.
        rewrite app_context_assoc //.
    + econstructor.
      eapply is_type_subst; tea.

  - inv H1.
    + cbn. econstructor.
      * eauto.
      * eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H2.
    + cbn. econstructor.
      eapply All2_map.
      eapply All2_impl_In.
      eassumption.
      intros. destruct H4 as [? ? ? ?].
      repeat split; eauto.
      cbn. now eapply isLambda_subst.
      now eapply ELiftSubst.isLambda_subst.
      eapply In_nth_error in H2 as [].
      eapply nth_error_all in X3 as IH; eauto.
      eapply nth_error_all in X2 as Ht; eauto. apply unlift_TermTyp in Ht.
      specialize (IH Γ Γ' (Δ ,,, fix_context mfix)).
      rewrite app_context_assoc in IH |- *.
      eapply IH in e1; eauto.

      eapply erases_eq; eauto.
      * rewrite subst_context_app.
        rewrite <- plus_n_O.
        rewrite app_context_assoc. f_equal.
        now rewrite subst_fix_context.
      * cbn. now rewrite app_context_length fix_context_length.
      * cbn. now erewrite app_context_length, fix_context_length, All2_length.
      * pose proof (@substitution _ Σ _ Γ Γ' s (Δ ,,, fix_context mfix)).
        rewrite app_context_assoc in X9.
        eapply X9 in X5; eauto.
        eapply typing_wf_local.  eassumption.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H2.
    + cbn. econstructor.
      eapply All2_map.
      eapply All2_impl_In.
      eassumption.
      intros. destruct H4 as (? & ? & ?).
      repeat split; eauto.
      eapply In_nth_error in H2 as [].
      eapply nth_error_all in X3 as IH; eauto.
      eapply nth_error_all in X2 as Ht; eauto. apply unlift_TermTyp in Ht.
      specialize (IH Γ Γ' (Δ ,,, fix_context mfix)).
      rewrite app_context_assoc in IH.
      eapply IH in e1; eauto.

      eapply erases_eq; eauto.
      * rewrite subst_context_app.
        rewrite <- plus_n_O.
        rewrite app_context_assoc. f_equal.
        now rewrite subst_fix_context.
      * cbn. now rewrite app_context_length fix_context_length.
      * cbn. now erewrite app_context_length, fix_context_length, All2_length.
      * pose proof (@substitution _ Σ _ Γ Γ' s (Δ ,,, fix_context mfix)).
        rewrite app_context_assoc in X9.
        eapply X9 in X5; eauto.
        eapply typing_wf_local.  eassumption.
    + econstructor.
      eapply is_type_subst; eauto.
  - cbn. depelim H2.
    * cbn; constructor.
      depelim H2. depelim X4; depelim X1; repeat constructor; cbn; eauto.
      ELiftSubst.solve_all.
    * constructor. eapply is_type_subst in X3; tea.
      now cbn in X3.
  - eapply H; eauto.
Qed.

Lemma erases_subst0 (Σ : global_env_ext) Γ t s t' s' T :
  wf Σ -> wf_local Σ Γ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t ⇝ℇ t' ->
  subslet Σ [] s Γ ->
  All2 (erases Σ []) s s' ->
  Σ ;;; [] |- (subst s 0 t) ⇝ℇ ELiftSubst.subst s' 0 t'.
Proof.
  intros Hwf Hwfl Hty He Hall.
  change (@nil (BasicAst.context_decl term)) with (subst_context s 0 [] ++ nil).
  eapply erases_subst with (Γ' := Γ); eauto.
  - cbn. unfold app_context. rewrite app_nil_r. eassumption.
  - cbn. unfold app_context. rewrite app_nil_r. eassumption.
Qed.
