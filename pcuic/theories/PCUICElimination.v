(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCasesContexts
     PCUICTyping PCUICGlobalEnv
     PCUICLiftSubst PCUICInductives PCUICGeneration PCUICSpine
     PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICSubstitution PCUICUnivSubst PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICConversion PCUICCumulativity PCUICConfluence PCUICContexts
     PCUICSR PCUICInversion PCUICValidity PCUICSafeLemmata
     PCUICContextConversion PCUICContextConversionTyp
     PCUICCumulProp PCUICWellScopedCumulativity PCUICArities.
From MetaRocq.PCUIC Require Import PCUICInductiveInversion PCUICOnFreeVars PCUICEquality.

Require Equations.Prop.DepElim.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Definition Is_proof `{cf : checker_flags} Σ Γ t := ∑ T u, Σ ;;; Γ |- t : T × Σ ;;; Γ |- T : tSort u × Sort.is_propositional u.

(* TODO: Figure out whether [SingletonProp], [Computational], and [Subsingleton] should use [strictly_extends_decls] or [extends]. -Jason Gross *)
Definition SingletonProp `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      strictly_extends_decls Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      ∥Is_proof Σ' Γ (mkApps (tConstruct ind n u) args)∥ /\
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Definition Computational `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      strictly_extends_decls Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) -> False.

Definition Subsingleton `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf_ext Σ' ->
      strictly_extends_decls Σ Σ' ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) ->
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).


Lemma typing_spine_case_predicate {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {u params indices ps} {c} :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_sort Σ ps ->
  spine_subst Σ Γ params (List.rev params)
    (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_subst Σ Γ indices (List.rev indices)
    (subst_context_let_expand (List.rev params)
        (subst_instance u (ind_params mdecl))
        (smash_context [] (subst_instance u (ind_indices idecl)))) ->
  Σ ;;; Γ |- c : mkApps (tInd ci u) (params ++ indices) ->
  typing_spine Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps))
    (indices ++ [c]) (tSort ps).
Proof.
  intros.
  apply wf_arity_spine_typing_spine; split.
  now eapply isType_case_predicate.
  now eapply arity_spine_case_predicate; auto.
Qed.


Lemma pre_case_predicate_context_gen_eq {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {ps} {p} :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_sort Σ ps ->
  spine_subst Σ Γ (pparams p) (List.rev (pparams p))
    (smash_context [] (ind_params mdecl)@[puinst p]) ->
  Σ ⊢ Γ ,,, pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p) =
      Γ ,,, case_predicate_context' ci mdecl idecl p.
Proof.
  intros wf decli cu wfps sp.
  eapply alpha_eq_context_ws_cumul_ctx_pb.
  * eapply All2_app. 2:reflexivity.
    rw /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context.
    rw /case_predicate_context' /=. cbn.
    rw subst_context_snoc; len.
    constructor. unfold subst_decl, map_decl; cbn. relativize (subst _ _ _). 1: constructor. reflexivity. symmetry.
    rw subst_instance_mkApps subst_mkApps. f_equal. cbn.
    now rw [subst_instance_instance _ _](subst_instance_id_mdecl _ _ _ cu).
    rw [to_extended_list _]to_extended_list_k_app; len; rw !map_app.
    f_equal.
    rw subst_instance_to_extended_list_k.
    erewrite subst_to_extended_list_k. reflexivity.
    eapply inst_ctx_subst in sp.
    eapply PCUICContextSubst.make_context_subst_spec_inv. rw List.rev_involutive.
    now rw subst_instance_smash.
    rw subst_instance_to_extended_list_k /=.
    rw /expand_lets_ctx /expand_lets_k_ctx /=.
    rw subst_instance_subst_context subst_instance_lift_context.
    rw to_extended_list_k_subst to_extended_list_k_lift_context.
    rw PCUICLiftSubst.map_subst_instance_to_extended_list_k.
    erewrite <-to_extended_list_k_map_subst. reflexivity. lia.
    eapply All2_refl. reflexivity.
  * epose proof (isType_case_predicate (puinst p) (pparams p) ps wf decli cu wfps sp).
    eapply isType_it_mkProd_or_LetIn_inv in X.
    eapply isType_wf_local in X. fvs.
Qed.

Lemma elim_restriction_works_kelim1 {cf : checker_flags} {Σ : global_env_ext}
  {Γ T ci p c brs mdecl idecl} :
  wf_ext Σ ->
  declared_inductive Σ ci.(ci_ind) mdecl idecl ->
  Σ ;;; Γ |- tCase ci p c brs : T ->
  (Is_proof Σ Γ (tCase ci p c brs) -> False) ->
  ind_kelim idecl = IntoAny \/ ind_kelim idecl = IntoSetPropSProp.
Proof.
  intros wfΣ. pose wfΣ' := wfΣ.1. intros.
  assert (HT := X).
  eapply inversion_Case in X as [mdecl' [idecl' [isdecl' [indices [data cum]]]]]; eauto.
  destruct data.
  unshelve epose proof (H_ := declared_inductive_to_gen H); eauto.
  unshelve epose proof (isdecl'_ := declared_inductive_to_gen isdecl'); eauto.
  eapply declared_inductive_inj in isdecl'_ as []. 2:exact H_. subst.
  enough (~ (Sort.is_propositional ps)).
  { clear -wfΣ allowed_elim H1.
    apply wf_ext_consistent in wfΣ as (val&sat).
    unfold is_allowed_elimination, is_lSet in *.
    destruct (ind_kelim idecl); auto; destruct ps; cbn in *; try discriminate;
    intuition congruence. }
  intros Huf. apply H0.
  red. exists (mkApps ptm (indices ++ [c])); intuition auto.
  exists ps.
  assert (Σ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])).
  econstructor; eauto. repeat (split; auto).
  repeat split; auto. split; auto. split; auto. clear brs_ty.
  eapply type_mkApps. rw /ptm.
  eapply type_it_mkLambda_or_LetIn; tea.
  assert (wf Σ) by apply wfΣ.
  pose proof (PCUICInductiveInversion.isType_mkApps_Ind_smash H (validity scrut_ty)).
  forward X1. apply (wf_predicate_length_pars wf_pred).
  simpl in X1. destruct X1 as [sppars [spargs cu']].
  assert (eqctx' : eq_context_upto_names
  (Γ,,, case_predicate_context' ci mdecl idecl p)
  (Γ,,, predctx)).
  { eapply All2_app. 2:eapply All2_refl; reflexivity.
    eapply case_predicate_context_alpha => //; tea.
    destruct wf_pred. eapply Forall2_All2 in H2.
    depelim H2. rw H3. constructor; auto. }
  assert (Σ ⊢ Γ ,,, pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p) = Γ ,,, predctx).
  { transitivity (Γ ,,, case_predicate_context' ci mdecl idecl p); revgoals.
    * symmetry. eapply alpha_eq_context_ws_cumul_ctx_pb => //; fvs. now symmetry.
    * eapply pre_case_predicate_context_gen_eq; tea. pcuic.
      now eapply PCUICWfUniverses.typing_wf_sort in pret_ty. }
  unshelve epose proof (typing_spine_case_predicate (ps:=ps) _ H cons _ sppars). 1-2:shelve.
  * pcuic.
  * now eapply PCUICWfUniverses.typing_wf_sort in pret_ty.
  * rw -smash_context_subst_context_let_expand in X2.
    specialize (X2 spargs scrut_ty).
    eapply typing_spine_strengthen; tea; revgoals.
    + eapply ws_cumul_pb_it_mkProd_or_LetIn.
      eapply ws_cumul_ctx_pb_rel_app.
      now symmetry.
      apply ws_cumul_pb_refl; fvs.
    + eapply validity in pret_ty.
      eapply isType_it_mkProd_or_LetIn; tea.
Qed.

Lemma elim_sort_intype {cf:checker_flags} Σ mdecl ind idecl ind_indices cdecls :
  elim_sort_prop_ind cdecls = IntoAny ->
  on_constructors cumulSpec0 (lift_typing typing)
    (Σ, ind_universes mdecl) mdecl
    (inductive_ind ind) idecl ind_indices
    (ind_ctors idecl) cdecls ->
  (#|ind_ctors idecl| = 0) +
  (∑ cdecl cdecl_sorts,
    (ind_ctors idecl = [cdecl]) *
    (cdecls = [cdecl_sorts]) *
    (Forall Sort.is_propositional cdecl_sorts) *
    (on_constructor cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) mdecl
        (inductive_ind ind) idecl ind_indices cdecl cdecl_sorts))%type.
Proof.
  intros lein onc.
  induction onc; simpl in *.
  left; auto.
  destruct l' as [|c cs].
  - simpl in *. depelim onc.
    right.
    destruct forallb eqn:fo => //.
    eapply forallb_Forall in fo.
    eexists; eauto.
  - discriminate.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_full_inv {cf:checker_flags} Σ Γ Δ s args s' :
  wf Σ.1 ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) args (tSort s') ->
  leq_sort (global_ext_constraints Σ) s s'.
Proof.
  intros wfΣ.
  induction Δ using PCUICInduction.ctx_length_rev_ind in args |- *.
  - simpl. intros sp; dependent elimination sp as [spnil _ _ e|spcons isty isty' e _ sp].
    now eapply ws_cumul_pb_Sort_inv in e.
    now eapply ws_cumul_pb_Sort_Prod_inv in e.
  - rw it_mkProd_or_LetIn_app; destruct d as [na [b|] ty]; simpl.
    * intros sp.
      specialize (H (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)).
      eapply PCUICArities.typing_spine_letin_inv in sp; auto.
      rw /subst1 subst_it_mkProd_or_LetIn in sp. simpl in sp. eauto.
    * intros sp. dependent elimination sp as [spnil _ _ e|spcons isty isty' e tyhd sp];
        [now eapply ws_cumul_pb_Prod_Sort_inv in e|].
      specialize (H (subst_context [hd0] 0 Γ0) ltac:(now autorewrite with len) tl0).
      apply H.
      eapply PCUICArities.isType_tProd in isty as [? ?]; auto. cbn in *.
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqann conv cum]; auto. simpl in *.
      eapply typing_spine_strengthen; eauto; revgoals.
      eapply (substitution0_ws_cumul_pb (t:=hd0)) in cum; auto.
      simpl in cum.
      now rw /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in cum.
      unshelve eapply (isType_subst (Δ := [vass _ _]) (s := [hd0])) in i0.
      now rw subst_it_mkProd_or_LetIn in i0.
      eapply subslet_ass_tip. eapply (type_ws_cumul_pb (pb:=Conv)); tea. 1: now eapply isTypeRel_isType. now symmetry.
Qed.

Inductive All_local_assum (P : context -> term -> Type) : context -> Type :=
| localassum_nil :
    All_local_assum P []

| localassum_cons_abs Γ na t :
    All_local_assum P Γ ->
    P Γ t ->
    All_local_assum P (Γ ,, vass na t)

| localassum_cons_def Γ na b t :
    All_local_assum P Γ ->
    All_local_assum P (Γ ,, vdef na b t).

Derive Signature for All_local_assum.

Lemma All_local_assum_app P Γ Δ : All_local_assum P (Γ ++ Δ) ->
  All_local_assum P Δ *
  All_local_assum (fun Γ' => P (Δ ,,, Γ')) Γ.
Proof.
  induction Γ; simpl; constructor; intuition auto.
  constructor. depelim X; apply IHΓ; auto.
  depelim X; constructor; try apply IHΓ; auto.
Qed.

Lemma All_local_assum_subst {cf:checker_flags} (P Q : context -> term -> Type) c n k :
  All_local_assum Q c ->
  (forall Γ t,
      Q Γ t ->
      P (subst_context n k Γ) (subst n (#|Γ| + k) t)
  ) ->
  All_local_assum P (subst_context n k c).
Proof.
  intros Hq Hf.
  induction Hq in |- *; try econstructor; eauto;
    simpl; unfold snoc; rw subst_context_snoc; econstructor; eauto.
Qed.

Lemma wf_ext_wf {cf:checker_flags} Σ : wf_ext Σ -> wf Σ.
Proof. move=> wfe; apply wfe. Qed.
#[global]
Hint Resolve wf_ext_wf : core.

Lemma is_propositional_subst_instance u s :
  Sort.is_propositional (subst_instance_sort u s) = Sort.is_propositional s.
Proof. destruct s => //. Qed.

Lemma leq_sort_propositional_l {cf:checker_flags} ϕ u1 u2 :
  prop_sub_type = false ->
  leq_sort ϕ u1 u2 -> Sort.is_propositional u1 -> u1 = u2.
Proof.
  destruct u1 => //=.
  1: intros ->.
  all: destruct u2 => //=.
Qed.

Lemma isType_ws_cumul_ctx_pb {cf Σ Γ Δ T} {wfΣ : wf Σ}:
  isType Σ Γ T ->
  wf_local Σ Δ ->
  Σ ⊢ Γ = Δ ->
  isType Σ Δ T.
Proof.
  intros HT wf eq.
  apply lift_typing_impl with (1 := HT); intros ?? Hs.
  eapply closed_context_conversion; tea.
Qed.

Lemma typing_spine_proofs {cf:checker_flags} Σ Γ Δ ind u args' args T' s :
  wf_ext Σ ->
  Σ ;;; Γ |-  T' : tSort s ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args')) args T' ->
  ((All_local_assum (fun Γ' t =>
      (∑ s, (Σ ;;; Γ ,,, Γ' |- t : tSort s) * Sort.is_propositional s)%type) Δ ->
    ∥ All (Is_proof Σ Γ) args ∥) *
    (forall mdecl idecl
    (Hdecl : declared_inductive Σ.1 ind mdecl idecl),
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      ((Sort.is_propositional s -> s = subst_instance_sort u idecl.(ind_sort)) /\
       (prop_sub_type = false ->
        Sort.is_propositional (subst_instance_sort u idecl.(ind_sort)) ->
        s = subst_instance_sort u idecl.(ind_sort)))))%type.
Proof.
  intros wfΣ Ht. pose wfΣ' := wfΣ.1.
  induction Δ using PCUICInduction.ctx_length_rev_ind in Γ, args', args, T', Ht |- *; simpl; intros sp.
  - dependent elimination sp as [spnil _ _ e|spcons isty isty' e _ sp].
    split; [repeat constructor|].
    * eapply ws_cumul_pb_Ind_l_inv in e as [ui' [l' [red Req argeq]]] => //; auto.
      intros mdecl idecl decli cu.
      destruct (on_declared_inductive decli) as [onmind oib].
      eapply subject_reduction_closed in Ht; eauto.
      eapply inversion_mkApps in Ht as [A [tInd sp]]; auto.
      eapply inversion_Ind in tInd as [mdecl' [idecl' [wfΓ [decli' [cu' cum]]]]]; auto.
      unshelve epose proof (decli_ := declared_inductive_to_gen decli); eauto.
      unshelve epose proof (decli'_ := declared_inductive_to_gen decli'); eauto.
      destruct (declared_inductive_inj decli_ decli'_); subst mdecl' idecl'.
      clear decli'.
      eapply typing_spine_strengthen in sp. 3:tea.
      rw (oib.(ind_arity_eq)) in sp.
      rw !subst_instance_it_mkProd_or_LetIn in sp.
      rw -it_mkProd_or_LetIn_app in sp.
      eapply typing_spine_it_mkProd_or_LetIn_full_inv in sp; auto.
      split.
      revert sp.
      destruct s => //=; destruct ind_sort => //.
      intros propsub props.
      rw is_propositional_subst_instance in props.
      apply leq_sort_propositional_l in sp; eauto. subst s.
      now destruct (ind_sort idecl).
      now destruct (ind_sort idecl).
      now eapply isTypeRel_isType, declared_inductive_valid_type.

    * now eapply invert_cumul_ind_prod in e.

  - destruct d as [na [b|] ty].
    + rw it_mkProd_or_LetIn_app in sp.
      simpl in sp.
      eapply PCUICArities.typing_spine_letin_inv in sp => //; auto.
      rw /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
      specialize (H (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)).
      rw subst_mkApps in sp.
      specialize (H _ _ _ _ Ht sp).
      split.
      * intros prs;eapply All_local_assum_app in prs as [prd prs].
        depelim prd.
        apply H.
        clear -wfΣ prs.
        eapply All_local_assum_subst; eauto.
        simpl. intros.
        destruct X as [s [Ht2 isp]].
        exists s; pcuicfo.
        rw Nat.add_0_r. eapply (substitution (Γ' := [vdef na b ty]) (s := [b]) (Δ := Γ1) (T:=tSort s)); auto.
        eapply subslet_def_tip.
        eapply typing_wf_local in Ht2.
        rw app_context_assoc in Ht2. eapply All_local_env_app_inv in Ht2 as [Ht2 _].
        depelim Ht2. now apply unlift_TermTyp in l.
        now rw app_context_assoc in Ht2.
      * intros mdecl idec decli.
        now apply H.
    + rw it_mkProd_or_LetIn_app in sp.
      destruct args. split; [repeat constructor|].
      * dependent elimination sp as [spnil _ _ e].
        unfold mkProd_or_LetIn in e; simpl in e.
        eapply ws_cumul_pb_Prod_l_inv in e as [na' [dom' [codom' [red eqann conv cum]]]]; auto.
        eapply subject_reduction_closed in Ht; eauto.
        intros.
        pose proof (PCUICWfUniverses.typing_wf_sort wfΣ Ht).
        eapply inversion_Prod in Ht as [s1 [s2 [dom [codom cum']]]]; auto.
        specialize (H Γ0 ltac:(reflexivity) (Γ ,, vass na' dom') args' []).
        eapply (type_Cumul _ _ _ _ (tSort s)) in codom; cycle 1; eauto.
        { econstructor; pcuic. }
        { eapply ws_cumul_pb_Sort_inv in cum'.
          eapply cumul_Sort.  etransitivity; eauto. eapply leq_sort_product. }
        specialize (H _ codom).
        have eqctx : Σ ⊢ Γ ,, vass na ty = Γ ,, vass na' dom'.
        { constructor. apply ws_cumul_ctx_pb_refl. fvs. constructor; auto. }
        forward H.
        { constructor. eapply (isType_it_mkProd_or_LetIn_inv (Δ := [_])) in i.
          eapply isType_ws_cumul_ctx_pb; tea. pcuic.
          eapply isType_red in i0. 2:exact red.
          now eapply isType_tProd in i0 as [].
          eapply ws_cumul_pb_ws_cumul_ctx. now symmetry in eqctx. assumption. }
        destruct H. eapply a; tea.

      * simpl in sp. dependent elimination sp as [spcons isty isty' e tyhd sp].
        eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna conv cum]; auto. cbn in *.
        eapply isType_tProd in isty as [].
        have tyt : Σ ;;; Γ |- hd0 : ty.
        { eapply (type_ws_cumul_pb _ (U:=ty)) in tyhd => //. 1: now eapply isTypeRel_isType. now symmetry. }
        eapply (isType_subst (Δ := [_])) in i0; revgoals.
        { now eapply subslet_ass_tip. }
        eapply typing_spine_strengthen in sp; eauto.
        2:{ eapply (substitution0_ws_cumul_pb (t:=hd0)) in cum => //. }
        rw /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (H (subst_context [hd0] 0 Γ0) ltac:(now autorewrite with len)).
        rw subst_mkApps in sp. simpl in sp.
        specialize (H _ _ _ _ Ht sp).
        split.
        intros prs;eapply All_local_assum_app in prs as [prd prs].
        depelim prd.
        eapply (type_ws_cumul_pb (pb:=Conv) _ (U:=ty)) in tyhd.
        2:{ destruct s0 as [s' [Hs' _]]. eapply has_sort_isType; eauto. }
        2:now symmetry.
        destruct H as [H _].
        forward H. {
          clear -wfΣ prs tyt.
          eapply All_local_assum_subst; eauto.
          simpl. intros.
          destruct X as [s [Ht2 isp]].
          exists s; pcuicfo auto.
          rw Nat.add_0_r. eapply (substitution (Γ' := [vass na ty]) (s:=[hd0]) (Δ := Γ1) (T := tSort s)); auto.
          now eapply subslet_ass_tip.
          now rw app_context_assoc in Ht2. }
        sq. constructor; auto.
        red. destruct s0 as [s' [Ht' sprop]].
        exists ty, s'. intuition auto.
        intros. now eapply H; tea.
Qed.

Lemma check_ind_sorts_is_propositional {cf:checker_flags} (Σ : global_env_ext) mdecl idecl ind
  (onib : on_ind_body cumulSpec0 (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl (inductive_ind ind) idecl) :
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) ->
  Sort.is_propositional (ind_sort idecl) ->
  check_ind_sorts (lift_typing typing) (Σ.1, ind_universes mdecl)
    (PCUICEnvironment.ind_params mdecl) (PCUICEnvironment.ind_kelim idecl)
    (ind_indices idecl) (ind_cunivs onib) (ind_sort idecl) ->
  (#|ind_cunivs onib| <= 1) * All (fun cs => All Sort.is_propositional cs) (ind_cunivs onib).
Proof.
  intros kelim isp.
  unfold check_ind_sorts.
  destruct ind_sort => //=.
  + induction (ind_cunivs onib); simpl; auto; try discriminate.
    destruct l; simpl. intros; split; eauto. constructor; [|constructor].
    destruct forallb eqn:fo. eapply forallb_All in fo.
    eapply All_impl; eauto; simpl.
    destruct (ind_kelim idecl); intuition cbn in H; try congruence.
    intros leb.
    destruct (ind_kelim idecl); simpl in *; intuition congruence.
  + induction (ind_cunivs onib); simpl; auto; try discriminate.
    destruct (ind_kelim idecl); simpl in *; intuition congruence.
Qed.

Lemma sorts_local_ctx_All_local_assum_impl {cf:checker_flags} Σ
  (P : context -> context -> term -> Type) {Γ Δ cs} :
  (forall Γ' t s, In s cs -> Σ ;;; Γ ,,, Γ' |- t : tSort s  -> P Γ Γ' t) ->
  sorts_local_ctx (lift_typing typing) Σ Γ Δ cs ->
  All_local_assum (P Γ) Δ.
Proof.
  intros H.
  induction Δ in cs, H |- *; simpl; intros. constructor; intuition auto.
  destruct a as [na [b|] ty]; constructor; intuition auto.
  destruct cs => //; eauto.
  destruct cs => //; eauto. destruct X.
  eapply IHΔ. intros. apply (H Γ' t0 s0). right; eauto. all:auto.
  destruct cs => //. destruct X.
  eapply H. left; eauto. now apply unlift_TypUniv in l.
Qed.

Lemma In_map {A B} (f : A -> B) (l : list A) x :
  In x (map f l) ->
  exists y, In y l /\ x = f y.
Proof.
  induction l; simpl; auto.
  intros [<-|inl].
  - eexists; intuition eauto.
  - destruct (IHl inl). exists x0; intuition eauto.
Qed.

(* We prove that if the (partial) constructor application's type lands in Prop
   then the inductive type is in Prop and hence the constructor's sort is
   Prop. Finally, all its arguments are in Prop because we additionally know
   that elimination to any type is allowed. *)

Lemma Is_proof_mkApps_tConstruct `{cf : checker_flags} (Σ : global_env_ext) Γ ind n u mdecl idecl args :
  wf_ext Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) ->
  Is_proof Σ Γ (mkApps (tConstruct ind n u) args) ->
  #|ind_ctors idecl| <= 1 /\ ∥ All (Is_proof Σ Γ) (skipn (ind_npars mdecl) args) ∥.
Proof.
  intros HΣ decli kelim [tyc [tycs [hc [hty hp]]]].
  assert (wfΣ : wf Σ) by apply HΣ.
  eapply inversion_mkApps in hc as [? [hc hsp]]; auto.
  eapply inversion_Construct in hc as [mdecl' [idecl' [cdecl' [wfΓ [declc [cu cum']]]]]]; auto.
  destruct (on_declared_constructor declc) as [[oi oib] [cs [Hnth onc]]].
  set (onib := declared_inductive_inv _ _ _ _) in *.
  clearbody onib. clear oib.
  eapply typing_spine_strengthen in hsp; eauto.
  unshelve epose proof (decli_ := declared_inductive_to_gen decli); eauto.
  unshelve epose proof (declc_ := declared_inductive_to_gen declc); eauto.
pose proof (declared_inductive_inj decli_ declc_) as [-> ->].
  assert (isType Σ Γ (type_of_constructor mdecl cdecl' (ind, n) u)).
  { eapply PCUICInductiveInversion.declared_constructor_valid_ty in declc; eauto. }
  move: X hsp.
  unfold type_of_constructor.
  rw (onc.(cstr_eq)).
  rw !subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rw - {1}(firstn_skipn (ind_npars mdecl) args).
  rw !subst_instance_mkApps.
  simpl.
  autorewrite with len.
  rw !subst_mkApps.
  rw !subst_inds_concl_head.
  destruct decli. now apply nth_error_Some_length in H0.
  destruct (le_dec (ind_npars mdecl) #|args|).
  * intros X hsp.
    eapply PCUICSpine.typing_spine_inv in hsp as [parsub [sub sp]]; auto.
    2:{ rw context_assumptions_subst context_assumptions_subst_instance.
        rw firstn_length_le //. symmetry; eapply onNpars. eauto. }
    rw !subst_it_mkProd_or_LetIn in X, sp.
    rw !subst_mkApps in sp.
    simpl in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp.
    specialize (a _ _ declc cu) as [a a'].
    specialize (a hp).

    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    assert (Sort.is_propositional (ind_sort idecl)).
    { rw -(is_propositional_subst_instance_univ u) => //. now subst tycs. }
    apply check_ind_sorts_is_propositional in X1 as [nctors X1]; eauto.
    assert(#|ind_cunivs onib| = #|ind_ctors idecl|).
    clear X. clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rw X.
    rw H0 in nctors; split; auto.

    eapply nth_error_all in X1; eauto. simpl in X1.
    eapply sorts_local_ctx_instantiate in X0. 4:eapply cu.
    all: eauto.
    rw subst_instance_app in X0.
    eapply weaken_sorts_local_ctx in X0; eauto.
    eapply (subst_sorts_local_ctx _ _) in X0; eauto.
    3:{ eapply subslet_app.
      2:{ eapply weaken_subslet; auto. eapply PCUICArities.subslet_inds; eauto. }
      eapply sub. }
    2:{ eapply PCUICWeakeningTyp.weaken_wf_local; auto.
        edestruct (PCUICInductiveInversion.on_constructor_inst declc); eauto.
        destruct s0 as [inst [sp _]].
        rw !subst_instance_app in sp.
        now eapply wf_local_app_l in sp. }

    apply s.
    rw subst_app_context in X0.
    rw -(PCUICContextSubst.context_subst_length sub) in X0.
    autorewrite with len in X0.
    eapply (sorts_local_ctx_All_local_assum_impl Σ
      (fun Γ Γ' t =>
      ∑ s0 : sort, Σ;;; Γ ,,, Γ' |- t : tSort s0 × Sort.is_propositional s0)).
    2:eauto.
    intros. exists s0. intuition auto.
    eapply In_map in H1 as [cs' [ins ->]].
    rw is_propositional_subst_instance.
    eapply All_In in X1; eauto.
    sq. apply X1. apply decli.

  * intros _ sp.
    rw List.skipn_all2. lia.
    split; [|repeat constructor].
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    eapply check_ind_sorts_is_propositional in X0 as [nctors X1]; eauto.
    assert(#|ind_cunivs onib| = #|ind_ctors idecl|).
    clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rw X. now rw -H.
    rw -it_mkProd_or_LetIn_app in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp as [_ sp].
    specialize (sp _ _ decli cu) as [a a'].
    specialize (a hp).
    subst tycs. rw -(is_propositional_subst_instance u) //.
  * now eapply declared_constructor_valid_ty.
Qed.

Lemma elim_restriction_works_kelim `{cf : checker_flags} (Σ : global_env_ext) ind mind idecl :
  wf_ext Σ ->
  declared_inductive (fst Σ) ind mind idecl ->
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) -> Subsingleton Σ ind.
Proof.
  intros HΣ H indk.
  assert (wfΣ : wf Σ) by apply HΣ.
  destruct (on_declared_inductive H) as [[]]; eauto.
  intros ?. intros.
  unshelve epose proof (H_ := declared_inductive_to_gen H); eauto.
  unshelve epose proof (H0_ := declared_inductive_to_gen H0); eauto.
  eapply declared_inductive_inj in H_ as []; eauto; subst idecl0 mind.
  eapply Is_proof_mkApps_tConstruct in X1; tea.
  assert (wf Σ') by auto.
  now eapply weakening_env_declared_inductive; tc.
Qed.

Lemma elim_restriction_works `{cf : checker_flags} (Σ : global_env_ext) Γ T (ci : case_info) p c brs mind idecl :
  wf_ext Σ ->
  declared_inductive (fst Σ) ci mind idecl ->
  Σ ;;; Γ |- tCase ci p c brs : T ->
  (Is_proof Σ Γ (tCase ci p c brs) -> False) -> Subsingleton Σ ci.(ci_ind).
Proof.
  intros wfΣ decli HT H.
  eapply elim_restriction_works_kelim1 in HT; eauto.
  eapply elim_restriction_works_kelim; eauto.
  destruct (ind_kelim idecl); intuition congruence.
Qed.

Lemma declared_projection_projs_nonempty `{cf : checker_flags} {Σ : global_env_ext} {p mdecl idecl cdecl pdecl} :
  wf Σ ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  ind_projs idecl <> [].
Proof.
  intros. destruct H. destruct H0.
  destruct (ind_projs idecl); try congruence. destruct p.
  cbn in *. destruct proj_arg; inv H0.
Qed.

Lemma elim_restriction_works_proj_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T p c mind idecl :
  wf Σ ->
  declared_inductive (fst Σ) p.(proj_ind) mind idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> ind_kelim idecl = IntoAny.
Proof.
  intros X H X0 H0.
  eapply inversion_Proj in X0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?) ; auto.
  unshelve epose proof (H_ := declared_inductive_to_gen H); eauto.
  unshelve epose proof (d_ := declared_inductive_to_gen d); eauto.
  destruct (declared_inductive_inj H_ d_) as [-> ->].
  destruct x2. cbn in *.
  pose proof (declared_projection_projs_nonempty X d).
  pose proof (on_declared_projection d) as [_ onp].
  simpl in onp. subst.
  destruct ind_cunivs as [|? []]; try contradiction.
  1,3:now destruct onp as (((? & ?) & ?) & ?).
  destruct onp as (((? & ?) & ?) & ?). now inv o.
Qed.

Lemma elim_restriction_works_proj `{cf : checker_flags} (Σ : global_env_ext) Γ  p c mind idecl T :
  wf_ext Σ ->
  declared_inductive (fst Σ) p.(proj_ind) mind idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> Subsingleton Σ p.(proj_ind).
Proof.
  intros. eapply elim_restriction_works_kelim; eauto.
  eapply elim_restriction_works_proj_kelim1 in H0; eauto.
  intuition congruence.
Qed.

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.

Lemma eq_univ_prop_compare_sort_propositional Σ pb (s s' : sort) :
  Sort.is_propositional s' ->
  eq_univ_prop s s' ->
  compare_sort Σ pb s s'.
Proof using Hcf.
  destruct s' => //.
  all: unfold eq_univ_prop, compare_sort.
  all: destruct s, pb => //=.
  all: now rw Hcf.
Qed.

Lemma eq_univ_prop_compare_sort_propositional_r Σ pb (s s' : sort) :
  Sort.is_propositional s ->
  eq_univ_prop s s' ->
  compare_sort Σ pb s s'.
Proof using Hcf.
  destruct s => //.
  all: unfold eq_univ_prop, compare_sort.
  all: destruct s', pb => //=.
  all: now rw Hcf.
Qed.

Lemma leq_term_prop_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Sort.is_propositional u ->
  leq_sort (global_ext_constraints Σ) u' u.
Proof using Hcf.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto. 2: apply wfΣ.
  apply cumul_prop_sort in leq.
  now eapply eq_univ_prop_compare_sort_propositional with (pb := Cumul).
Qed.

Lemma leq_term_prop_sorted_r {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Sort.is_propositional u' ->
  leq_sort (global_ext_constraints Σ) u u'.
Proof using Hcf.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto. 2: apply wfΣ.
  apply cumul_prop_sort in leq.
  now eapply eq_univ_prop_compare_sort_propositional with (pb := Cumul).
Qed.

Lemma cumul_prop_inv (Σ : global_env_ext) Γ A B u u' :
  wf_ext Σ ->
  Sort.is_propositional u ->
  (((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u')) +
   ((Σ ;;; Γ |- B : tSort u) * (Σ ;;; Γ |- A : tSort u')))%type ->
  Σ ;;; Γ |- A <= B ->
  ((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u))%type.
Proof using Hcf.
  intros wfΣ propu.
  intros [[HA HB]|[HB HA]] cum; split; auto;
  apply cumul_alt in cum as [v [v' (redv & redv' & leq)]].
  - eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort.
    now eapply PCUICWfUniverses.typing_wf_sort in HA.
    pcuic. eapply cumul_Sort.
    eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_l; eauto.
  - eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_r in leq; eauto.
    eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort.
    now eapply PCUICWfUniverses.typing_wf_sort in HB.
    pcuic. eapply cumul_Sort; auto.
Qed.

Lemma unique_sorting_family {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.to_family s = Sort.to_family s'.
Proof using Hcf.
  intros wfΣ HT HU cum.
  apply ws_cumul_pb_forget in cum.
  eapply typing_cumul_term_prop in cum; tea.
  apply cumul_prop_sort in cum.
  move: cum.
  destruct s, s' => //=; cbn.
  all: now rw Hcf //.
Qed.

Lemma unique_sorting_equality_prop {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.is_prop s = Sort.is_prop s'.
Proof using Hcf.
  intros wfΣ HT HU cum.
  eapply unique_sorting_family in cum; tea.
  now destruct s, s'.
Qed.

Lemma unique_sorting_equality_prop_l {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.is_prop s -> Sort.is_prop s'.
Proof using Hcf.
  intros.
  erewrite <- unique_sorting_equality_prop; eassumption.
Qed.

Lemma unique_sorting_equality_prop_r {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.is_prop s' -> Sort.is_prop s.
Proof using Hcf.
  intros.
  erewrite unique_sorting_equality_prop; eassumption.
Qed.

Lemma unique_sorting_equality_sprop {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.is_sprop s = Sort.is_sprop s'.
Proof using Hcf.
  intros wfΣ HT HU cum.
  eapply unique_sorting_family in cum; tea.
  now destruct s, s'.
Qed.

Lemma unique_sorting_equality_sprop_l {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.is_sprop s -> Sort.is_sprop s'.
Proof using Hcf.
  intros.
  erewrite <- unique_sorting_equality_sprop; eassumption.
Qed.

Lemma unique_sorting_equality_sprop_r {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.is_sprop s' -> Sort.is_sprop s.
Proof using Hcf.
  intros.
  erewrite unique_sorting_equality_sprop; eassumption.
Qed.

Lemma unique_sorting_equality_propositional {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Sort.is_propositional s = Sort.is_propositional s'.
Proof using Hcf.
  intros wfΣ HT HU cum.
  eapply unique_sorting_family in cum; tea.
  now destruct s, s'.
Qed.

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Sort.is_prop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof using Hcf.
  intros.
  destruct X0 as (_ & s & Hs & _).
  eapply cumul_prop_inv in X2 as []; eauto.
  now apply Sort.is_prop_propositional.
Qed.

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Sort.is_prop u ->
  isType Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof using Hcf.
  intros.
  destruct X0 as (_ & s & Hs & _).
  eapply cumul_prop_inv in X1 as []; eauto.
  now apply Sort.is_prop_propositional.
Qed.

Lemma cumul_sprop1 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Sort.is_sprop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof using Hcf.
  intros.
  destruct X0 as (_ & s & Hs & _).
  eapply cumul_prop_inv in X2 as []; eauto.
  now apply Sort.is_sprop_propositional.
Qed.

Lemma cumul_sprop2 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Sort.is_sprop u ->
  isType Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof using Hcf.
  intros.
  destruct X0 as (_ & s & Hs & _).
  eapply cumul_prop_inv in X1 as []; eauto.
  now apply Sort.is_sprop_propositional.
Qed.

End no_prop_leq_type.
