(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSigmaCalculus (* for smash_context lemmas, to move *)
     PCUICSubstitution PCUICClosed PCUICClosedConv PCUICClosedTyp
     PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICEquality PCUICConfluence PCUICCasesContexts
     PCUICOnFreeVars PCUICContextConversion PCUICContextConversionTyp PCUICContextSubst
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICSpine PCUICInductives PCUICWellScopedCumulativity PCUICValidity.

From Equations.Type Require Import Relation_Properties.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Derive Subterm for term.
From Stdlib Require Import ssreflect.

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

#[global]
Hint Rewrite reln_length : len.

#[global] Hint Resolve f_equal_nat : arith.

Ltac substu := autorewrite with substu => /=.

Tactic Notation "substu" "in" hyp(id) :=
  autorewrite with substu in id; simpl in id.

Lemma conv_eq_ctx {cf:checker_flags} Σ Γ Γ' T U : Σ ;;; Γ |- T = U -> Γ = Γ' -> Σ ;;; Γ' |- T = U.
Proof. now intros H ->. Qed.

Ltac pcuic := intuition eauto 5 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 5 with pcuic || (try lia || congruence)]).

(** Inversion principle on constructor types following from validity. *)

Lemma declared_constructor_valid_ty {cf:checker_flags} Σ Γ mdecl idecl i n cdecl u :
  wf Σ.1 ->
  wf_local Σ Γ ->
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ Γ (type_of_constructor mdecl cdecl (i, n) u).
Proof.
  move=> wfΣ wfΓ declc Hu.
  eapply validity. eapply type_Construct; eauto.
Qed.

Lemma type_tFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f))  *
    wf_fixpoint Σ  mfix
  * (Σ ;;; Γ |- f : T') * (Σ ;;; Γ ⊢ T' ≤ T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  - unfold unfold_fix. rw e.
    specialize (nth_error_all e a0) as (_ & s & Hs & _).
    specialize (nth_error_all e a1) as (Hb & _). cbn in Hb, Hs.
    simpl.
    destruct decl as [name ty body rarg]; simpl in *.
    clear e.
    eexists _, _, _. split.
    + split.
      * eauto.
      * eapply (substitution (Δ :=  [])); simpl; eauto with wf.
        rename i into hguard. clear -f a a0 a1 hguard.
        pose proof a1 as a1'. apply All_rev in a1'.
        unfold fix_subst, fix_context. simpl.
        revert a1'. rewrite <- (@List.length_rev _ mfix).
        rw rev_mapi. unfold mapi.
        assert (#|mfix| >= #|List.rev mfix|) by (rw List.length_rev; lia).
        assert (He :0 = #|mfix| - #|List.rev mfix|) by (rw List.length_rev; auto with arith).
        rw {2}He. clear He. revert H.
        assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
        { intros. rw nth_error_rev. 1: auto.
          now rw List.length_rev List.rev_involutive. }
        revert H.
        generalize (List.rev mfix).
        intros l Hi Hlen H.
        induction H.
        ++ simpl. constructor.
        ++ simpl. constructor.
          ** unfold mapi in IHAll.
              simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
              apply IHAll.
              --- intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia.
              --- lia.
          ** clear IHAll.
              simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
              rw H0. rw simpl_subst_k.
              --- clear. induction l; simpl; auto with arith.
              --- eapply type_Fix; auto.
                  simpl in Hi. specialize (Hi 0). forward Hi.
                  +++ lia.
                  +++ simpl in Hi.
                      rw Hi. f_equal. lia.

    + rw simpl_subst_k.
      * now rw fix_context_length fix_subst_length.
      * eapply isType_ws_cumul_pb_refl; pcuic.
  - destruct (IHtyping1 wfΣ) as [T' [rarg [f [[unf fty] Hcumul]]]].
    exists T', rarg, f. intuition auto.
    etransitivity; eauto.
    eapply PCUICConversion.cumulSpec_cumulAlgo_curry in c; eauto; fvs.
Qed.

Lemma subslet_cofix {cf:checker_flags} (Σ : global_env_ext) Γ mfix :
  wf_local Σ Γ ->
  cofix_guard Σ Γ mfix ->
  All (on_def_type (lift_typing typing Σ) Γ) mfix ->
  All (on_def_body (lift_typing typing Σ) (fix_context mfix) Γ) mfix ->
  wf_cofixpoint Σ mfix -> subslet Σ Γ (cofix_subst mfix) (fix_context mfix).
Proof.
  intros wfΓ hguard types bodies wfcofix.
  pose proof bodies as X1. apply All_rev in X1.
  unfold cofix_subst, fix_context. simpl.
  revert X1. rewrite <- (@List.length_rev _ mfix).
  rw rev_mapi. unfold mapi.
  assert (#|mfix| >= #|List.rev mfix|) by (rw List.length_rev; lia).
  assert (He :0 = #|mfix| - #|List.rev mfix|) by (rw List.length_rev; auto with arith).
  rw {2}He. clear He. revert H.
  assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
  { intros. rw nth_error_rev. 1: auto.
    now rw List.length_rev List.rev_involutive. }
  revert H.
  generalize (List.rev mfix).
  intros l Hi Hlen H.
  induction H.
  ++ simpl. constructor.
  ++ simpl. constructor.
    ** unfold mapi in IHAll.
        simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
        apply IHAll.
        --- intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia.
        --- lia.
    ** clear IHAll.
        simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
        rw H0. rw simpl_subst_k.
        --- clear. induction l; simpl; auto with arith.
        --- eapply type_CoFix; auto.
            simpl in Hi. specialize (Hi 0). forward Hi.
            +++ lia.
            +++ simpl in Hi.
                rw Hi. f_equal. lia.
Qed.

Lemma type_tCoFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tCoFix mfix idx : T ->
  ∑ d, (nth_error mfix idx = Some d) *
    wf_cofixpoint Σ mfix *
    (Σ ;;; Γ |- subst0 (cofix_subst mfix) (dbody d) : (dtype d)) *
    (Σ ;;; Γ ⊢ dtype d ≤ T).
Proof.
  intros wfΣ H.
  apply typing_wf_local in H as wfΓ.
  apply inversion_CoFix in H as (decl & Hguard & Hnth & Htys & Hbods & Hwf & Hty); tas.
  exists decl. repeat (split; tea).
  eapply All_nth_error in Hbods as Hbod; tea.
  apply unlift_TermTyp in Hbod.
  eapply (substitution (s := cofix_subst mfix) (Δ := [])) in Hbod.
  2: now apply subslet_cofix; auto.
  simpl in Hbod.
  rw subst_context_nil /= in Hbod.
  eapply refine_type; eauto.
  rw simpl_subst_k //. len.
Qed.

Lemma wf_cofixpoint_all {cf:checker_flags} (Σ : global_env_ext) mfix :
  wf_cofixpoint Σ mfix ->
  ∑ mind, check_recursivity_kind (lookup_env Σ) mind CoFinite *
  All (fun d => ∑ ctx i u args, (dtype d) = it_mkProd_or_LetIn ctx (mkApps (tInd {| inductive_mind := mind; inductive_ind := i |} u) args)) mfix.
Proof.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  destruct mfix. discriminate.
  simpl.
  destruct (check_one_cofix d) as [ind|] eqn:hcof.
  intros eqr.
  exists ind.
  destruct (map_option_out (map check_one_cofix mfix)) eqn:eqfixes.
  move/andb_and: eqr => [eqinds rk].
  split; auto.
  constructor.
  - move: hcof. unfold check_one_cofix.
    destruct d as [dname dbody dtype rarg] => /=.
    destruct (decompose_prod_assum [] dbody) as [ctx concl] eqn:Hdecomp.
    apply decompose_prod_assum_it_mkProd_or_LetIn in Hdecomp.
    destruct (decompose_app concl) eqn:dapp.
    destruct (destInd t) as [[ind' u]|] eqn:dind.
    destruct ind' as [mind ind'].
    move=> [=] Hmind. subst mind.
    exists ctx, ind', u, l0.
    simpl in Hdecomp. rw Hdecomp.
    f_equal.
    destruct t; try discriminate.
    simpl in dind. noconf dind.
    apply decompose_app_inv in dapp => //.
    discriminate.
  - clear rk hcof.
    induction mfix in l, eqfixes, eqinds |- *. constructor.
    simpl in *.
    destruct (check_one_cofix a) eqn:hcof; try discriminate.
    destruct (map_option_out (map check_one_cofix mfix)) eqn:hcofs; try discriminate.
    noconf eqfixes.
    specialize (IHmfix _ eq_refl).
    simpl in eqinds.
    move/andb_and: eqinds => [eqk eql0].
    constructor; auto. clear IHmfix hcofs d.
    destruct a as [dname dbody dtype rarg] => /=.
    unfold check_one_cofix in hcof.
    destruct (decompose_prod_assum [] dbody) as [ctx concl] eqn:Hdecomp.
    apply decompose_prod_assum_it_mkProd_or_LetIn in Hdecomp.
    destruct (decompose_app concl) eqn:dapp.
    destruct (destInd t) as [[ind' u]|] eqn:dind.
    destruct ind' as [mind ind']. noconf hcof.
    exists ctx, ind', u, l.
    simpl in Hdecomp. rw Hdecomp.
    f_equal.
    destruct t; try discriminate.
    simpl in dind. noconf dind.
    apply decompose_app_inv in dapp => //.
    rw dapp. do 3 f_equal.
    symmetry.
    change (eq_kername ind k) with (ReflectEq.eqb ind k) in eqk.
    destruct (ReflectEq.eqb_spec ind k); auto.
    discriminate.
  - discriminate.
  - discriminate.
Qed.



Section OnConstructor.
  Context {cf:checker_flags} {Σ : global_env} {ind mdecl idecl cdecl}
    {wfΣ: wf Σ} (declc : declared_constructor Σ ind mdecl idecl cdecl).

  Lemma on_constructor_wf_args :
    wf_local (Σ, ind_universes mdecl)
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl).
  Proof using declc wfΣ.
    pose proof (on_declared_constructor declc) as [[onmind oib] [cunivs [hnth onc]]].
    pose proof (on_cargs onc). simpl in X.
    eapply sorts_local_ctx_wf_local in X => //. clear X.
    eapply weaken_wf_local => //.
    eapply wf_arities_context; eauto. eapply declc.
    now eapply onParams in onmind.
  Qed.

  Lemma on_constructor_subst :
    wf_global_ext Σ (ind_universes mdecl) *
    wf_local (Σ, ind_universes mdecl)
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl) *
    ∑ inst,
    spine_subst (Σ, ind_universes mdecl)
              (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
                cstr_args cdecl)
              ((to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
                (cstr_indices cdecl)) inst
            (ind_params mdecl ,,, ind_indices idecl).
  Proof using declc wfΣ.
    pose proof (on_declared_constructor declc) as [[onmind oib] [cunivs [hnth onc]]].
    pose proof (onc.(on_cargs)). simpl in X.
    split. split. split.
    2:{ eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); tea.
        clear hnth. unshelve eapply declared_constructor_to_gen in declc; eauto.
        try exact (inductive_mind ind.1). (* with rocq-prover/rocq#22182 this goal stays shelved and is solved by side effect *)
        eapply declc. }
    red. apply wfΣ.
    eapply sorts_local_ctx_wf_local in X => //. clear X.
    eapply weaken_wf_local => //.
    eapply wf_arities_context; eauto; eapply declc.
    now eapply onParams in onmind.
    destruct (on_ctype onc) as (_ & s & Hs & _).
    rw onc.(cstr_eq) in Hs.
    rw -it_mkProd_or_LetIn_app in Hs.
    eapply inversion_it_mkProd_or_LetIn in Hs => //.
    unfold cstr_concl_head in Hs. simpl in Hs.
    eapply inversion_mkApps in Hs as [A [ta sp]].
    eapply inversion_Rel in ta as [decl [wfΓ [nth cum']]].
    rw nth_error_app_ge in nth. len.
    len in nth.
    all:auto.
    assert ((#|ind_bodies mdecl| - S (inductive_ind ind.1) + #|ind_params mdecl| +
    #|cstr_args cdecl| -
    (#|cstr_args cdecl| + #|ind_params mdecl|)) = #|ind_bodies mdecl| - S (inductive_ind ind.1)) by lia.
    move: nth; rw H; clear H.
    case: nth_error_spec => // /= decl' Hdecl Hlen.
    intros [= ->].
    eapply (nth_errror_arities_context (Σ := (Σ, ind_universes mdecl)) declc) in Hdecl; eauto.
    rw Hdecl in cum'; clear Hdecl.
    assert(closed (ind_type idecl)).
    { pose proof (oib.(onArity)). rw (oib.(ind_arity_eq)) in X0 |- *.
      destruct X0 as (_ & s' & Hs & _). now apply subject_closed in Hs. }
    rw lift_closed in cum' => //.
    eapply typing_spine_strengthen in sp; simpl.
    3:tea.
    move: sp.
    rw (oib.(ind_arity_eq)).
    rw -it_mkProd_or_LetIn_app.
    move=> sp. simpl in sp.
    apply (arity_typing_spine (Σ := (Σ, ind_universes mdecl))) in sp as [Hlen' Hleq [inst Hinst]] => //.
    clear Hlen'.
    rw [_ ,,, _]app_context_assoc in Hinst.
    now exists inst.
    apply lift_typing_weaken_ctx with (Γ := []); tas.
    eapply isTypeRel_isType.
    apply oib.(onArity).
  Qed.
End OnConstructor.

Section OnConstructorExt.
  Context {cf} {Σ} {wfΣ : wf Σ} {ind mdecl idecl cdecl}
    (declc : declared_constructor Σ ind mdecl idecl cdecl).

  Lemma on_constructor_inst_wf_args u :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ ((ind_params mdecl)@[u] ,,, subst_context (ind_subst mdecl (fst ind) u) #|ind_params mdecl| (cstr_args cdecl)@[u]).
  Proof using declc wfΣ.
    intros cu.
    pose proof (on_constructor_wf_args declc).
    eapply wf_local_subst_instance in X; tea.
    rw -[X in X ,,, _]app_context_nil_l - !app_context_assoc app_context_assoc in X.
    rw !subst_instance_app_ctx /= in X.
    eapply substitution_wf_local in X.
    2:eapply (subslet_inds declc); tea.
    2:{ eapply (declared_inductive_wf_global_ext Σ.1 _ _ _ declc). }
    cbn in X. rw app_context_nil_l in X.
    rw subst_context_app Nat.add_0_r in X.
    rw closed_ctx_subst in X.
    rw closedn_subst_instance_context.
    eapply (declared_inductive_closed_params declc).
    now len in X.
  Qed.

  Lemma on_constructor_inst u :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ (subst_instance u
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) *
    ∑ inst,
    spine_subst Σ
            (subst_instance u
              (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
                cstr_args cdecl))
            (map (subst_instance u)
              (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
            map (subst_instance u) (cstr_indices cdecl)) inst
            (subst_instance u (ind_params mdecl) ,,,
            subst_instance u (ind_indices idecl)).
  Proof using declc wfΣ.
    intros cu.
    destruct (on_constructor_subst declc) as [[wfext wfl] [inst sp]].
    eapply wf_local_subst_instance in wfl; eauto. split=> //.
    eapply spine_subst_inst in sp; eauto.
    rw map_app in sp. rw -subst_instance_app_ctx.
    eexists ; eauto.
  Qed.
End OnConstructorExt.

Lemma on_constructor_inst_pars_indices {cf:checker_flags} {Σ ind u mdecl idecl cdecl Γ pars parsubst} :
  wf Σ.1 ->
  declared_constructor Σ.1 ind mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  spine_subst Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  wf_local Σ (subst_instance u (ind_params mdecl) ,,,
    subst_context (inds (inductive_mind ind.1) u (ind_bodies mdecl)) #|ind_params mdecl|
    (subst_instance u (cstr_args cdecl))) *
  ∑ inst,
  spine_subst Σ
          (Γ ,,, subst_context parsubst 0 (subst_context (ind_subst mdecl ind.1 u) #|ind_params mdecl|
            (subst_instance u (cstr_args cdecl))))
          (map (subst parsubst #|cstr_args cdecl|)
            (map (subst (ind_subst mdecl ind.1 u) (#|cstr_args cdecl| + #|ind_params mdecl|))
              (map (subst_instance u) (cstr_indices cdecl))))
          inst
          (lift_context #|cstr_args cdecl| 0
          (subst_context parsubst 0 (subst_instance u (ind_indices idecl)))).
Proof.
  move=> wfΣ declc cext sp.
  (* destruct (on_declared_constructor declc) as []. .declm oi oib onc *)
  destruct (on_constructor_inst declc u) as [wfl [inst sp']]; auto.
  rw !subst_instance_app in sp'.
  eapply spine_subst_app_inv in sp' as [spl spr]; auto.
  rw (spine_subst_extended_subst spl) in spr.
  rw subst_context_map_subst_expand_lets in spr; try now len.
  rw subst_instance_to_extended_list_k in spr.
  2:now len.
  rw lift_context_subst_context.
  rw app_assoc in spr.
  eapply spine_subst_subst_first in spr; eauto.
  2:eapply subslet_inds; eauto; eapply declc.
  len in spr.
  rw subst_context_app in spr.
  assert (closed_ctx (subst_instance u (ind_params mdecl)) /\ closedn_ctx #|ind_params mdecl| (subst_instance u (ind_indices idecl)))
  as [clpars clinds].
  { pose proof (on_minductive_wf_params_indices declc).
    eapply closed_wf_local in X => //.
    rw closedn_ctx_app in X; simpl; eauto;
    move/andb_and: X; intuition auto;
    now rw closedn_subst_instance_context. }
  assert (closedn_ctx (#|ind_params mdecl| + #|cstr_args cdecl|) (subst_instance u (ind_indices idecl)))
    as clinds'.
  { eapply closedn_ctx_upwards; eauto. lia. }
  rw closed_ctx_subst // in spr.
  rw (closed_ctx_subst (inds (inductive_mind ind.1) u (ind_bodies mdecl)) _ (subst_context (List.rev _) _ _)) in spr.
  { len.
    rw -(Nat.add_0_r (#|cstr_args cdecl| + #|ind_params mdecl|)).
    eapply closedn_ctx_subst. len.
    rw -(context_assumptions_subst_instance u).
    eapply closedn_ctx_expand_lets. eapply closedn_ctx_upwards; eauto. lia.
    len. eapply closedn_ctx_upwards; eauto. lia.
    rw forallb_rev.
    rw PCUICLiftSubst.map_subst_instance_to_extended_list_k.
    eapply closedn_to_extended_list_k. }
  len in spr. split => //. apply spr.
  eapply spine_subst_weaken in spr.
  2:eapply (spine_dom_wf _ _ _ _ _ sp); eauto.
  rw app_context_assoc in spr.
  eapply spine_subst_subst in spr; eauto. 2:eapply sp.
  len in spr.
  rw {4}(spine_subst_extended_subst sp) in spr.
  rw subst_context_map_subst_expand_lets_k in spr; try now len.
  rw List.length_rev. now rw -(context_subst_length2 sp).
  rw expand_lets_k_ctx_subst_id' in spr. now len. now len.
  rw -subst_context_map_subst_expand_lets_k in spr; try len.
  rw subst_subst_context in spr. len in spr.
  rw subst_extended_lift // in spr.
  rw lift_extended_subst in spr.
  rw (map_map_compose _ _ _ _ (subst (List.rev pars) _)) in spr.
  assert (map
              (fun x : term =>
               subst (List.rev pars) #|cstr_args cdecl|
                 (lift0 #|cstr_args cdecl| x))
              (extended_subst (subst_instance u (ind_params mdecl)) 0) =
              (map
              (fun x : term =>
              (lift0 #|cstr_args cdecl|
                (subst (List.rev pars) 0 x)))
              (extended_subst (subst_instance u (ind_params mdecl)) 0))
              ).
  eapply map_ext => x.
  now rw -(commut_lift_subst_rec _ _ _ 0).
  rw H in spr. clear H.
  rw -(map_map_compose  _ _  _ _ (lift0 #|cstr_args cdecl|)) in spr.
  rw -(spine_subst_extended_subst sp) in spr.
  rw subst_map_lift_lift_context in spr.
  rw -(context_subst_length sp).
  len.
  rw closed_ctx_subst //.
  rw (closed_ctx_subst (List.rev pars)) // in spr.
  eexists. eauto.
Qed.

Lemma mkApps_ind_typing_spine {cf:checker_flags} Σ Γ Γ' ind i
  inst ind' i' args args' :
  wf Σ.1 ->
  wf_local Σ Γ ->
  isType Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) inst
    (mkApps (tInd ind' i') args') ->
  ∑ instsubst,
  [× make_context_subst (List.rev Γ') inst [] = Some instsubst,
    #|inst| = context_assumptions Γ', ind = ind', cmp_ind_universes Σ ind #|args| i i',
    All2 (fun par par' => Σ ;;; Γ ⊢ par = par') (map (subst0 instsubst) args) args' &
    subslet Σ Γ instsubst Γ'].
Proof.
  intros wfΣ wfΓ; revert args args' ind i ind' i' inst.
  revert Γ'. refine (ctx_length_rev_ind _ _ _); simpl.
  - intros args args' ind i ind' i' inst wat Hsp.
    depelim Hsp.
    eapply ws_cumul_pb_Ind_l_inv in w as [i'' [args'' [? ?]]]; auto.
    eapply invert_red_mkApps_tInd in c as [? [eq ?]]; auto. solve_discr.
    exists nil.
    split; pcuic. clear i0.
    relativize (map (subst0 []) args).
    2:rw subst_empty_eq map_id //. clear i1.
    revert args' a0. clear -wfΣ wfΓ a.
    induction a; intros args' H; depelim H; constructor.
    transitivity y; auto. symmetry.
    now eapply red_conv. now eauto.
    now eapply invert_cumul_ind_prod in w.
  - intros d Γ' IH args args' ind i ind' i' inst wat Hsp.
    rw it_mkProd_or_LetIn_app in Hsp.
    destruct d as [na [b|] ty]; simpl in *; rw /mkProd_or_LetIn /= in Hsp.
    + rw context_assumptions_app /= Nat.add_0_r.
      eapply typing_spine_letin_inv in Hsp; auto.
      rw /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
      specialize (IH (subst_context [b] 0 Γ')).
      forward IH by rw subst_context_length; lia.
      rw subst_mkApps Nat.add_0_r in Hsp.
      specialize (IH (map (subst [b] #|Γ'|) args) args' ind i ind' i' inst).
      forward IH. {
        move: wat; rw it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
        eapply isType_tLetIn_red in wat; auto.
        now rw /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
        in wat. }
      rw context_assumptions_subst in IH.
      intuition auto.
      destruct X as [isub [Hisub Hinst Hind Hi Hargs Hs]].
      eexists. split; auto.
      eapply make_context_subst_spec in Hisub.
      eapply make_context_subst_spec_inv.
      rw List.rev_app_distr. simpl.
      rw List.rev_involutive.
      eapply (context_subst_subst [{| decl_name := na; decl_body := Some b;  decl_type := ty |}] [] [b] Γ').
      rw -{2}  (subst_empty 0 b). eapply context_subst_def. constructor.
      now rw List.rev_involutive in Hisub.
      now len in Hi.
      rw map_map_compose in Hargs.
      assert (map (subst0 isub ∘ subst [b] #|Γ'|) args = map (subst0 (isub ++ [b])) args) as <-.
      { eapply map_ext => x. simpl.
        assert(#|Γ'| = #|isub|).
        { apply make_context_subst_spec in Hisub.
          apply context_subst_length in Hisub.
          now rw List.rev_involutive subst_context_length in Hisub. }
        rw H.
        now rw -(subst_app_simpl isub [b] 0). }
      exact Hargs.
      eapply subslet_app; eauto. rw -{1}(subst_empty 0 b). repeat constructor.
      rw !subst_empty.
      rw it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in wat.
      now eapply isType_tLetIn_dom in wat.
    + rw context_assumptions_app /=.
      pose proof (typing_spine_WAT_concl Hsp).
      depelim Hsp; [now eapply invert_cumul_prod_ind in w|].
      eapply ws_cumul_pb_Prod_Prod_inv in w as [eqna conva cumulB].
      eapply (substitution_ws_cumul_pb (Γ' := [_]) (Γ'' := []) (s := [hd])) in cumulB; auto.
      rw /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
      specialize (IH (subst_context [hd] 0 Γ')).
      forward IH by rw subst_context_length; lia.
      specialize (IH (map (subst [hd] #|Γ'|) args) args' ind i ind' i' tl). all:auto.
      have isTypes: isType Σ Γ
      (it_mkProd_or_LetIn (subst_context [hd] 0 Γ')
          (mkApps (tInd ind i) (map (subst [hd] #|Γ'|) args))). {
        move: wat; rw it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
        eapply isType_tProd in wat as [isty wat].
        apply isTypeRel_isType in isty.
        eapply (isType_subst (Δ := [_]) (s := [hd])) in wat.
        now rw subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps in wat.
        eapply subslet_ass_tip. eapply type_ws_cumul_pb; tea. now symmetry. }
      rw subst_mkApps Nat.add_0_r in cumulB. simpl in *.
      rw context_assumptions_subst in IH.
      eapply typing_spine_strengthen in Hsp.
      3:eapply cumulB. all:eauto.
      intuition auto.
      destruct X1 as [isub [Hisub Htl Hind Hu Hargs Hs]].
      exists (isub ++ [hd]). rw List.rev_app_distr.
      len in Hu.
      split; auto. 2:lia.
      * apply make_context_subst_spec_inv.
        apply make_context_subst_spec in Hisub.
        rw List.rev_app_distr !List.rev_involutive in Hisub |- *.
        eapply (context_subst_subst [{| decl_name := na; decl_body := None; decl_type := ty |}] [hd] [hd] Γ'); auto.
        eapply (context_subst_ass _ [] []). constructor.
      * assert (map (subst0 isub ∘ subst [hd] #|Γ'|) args = map (subst0 (isub ++ [hd])) args) as <-.
      { eapply map_ext => x. simpl.
        assert(#|Γ'| = #|isub|).
        { apply make_context_subst_spec in Hisub.
          apply context_subst_length in Hisub.
          now rw List.rev_involutive subst_context_length in Hisub. }
        rw H.
        now rw -(subst_app_simpl isub [hd] 0). }
        now rw map_map_compose in Hargs.
      * eapply subslet_app; auto.
        constructor. constructor. rw subst_empty.
        rw it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in wat.
        eapply isType_tProd in wat as [Hty _]; auto.
        apply isTypeRel_isType in Hty.
        eapply type_ws_cumul_pb; eauto. now eapply ws_cumul_pb_eq_le.
      * pcuic.
Qed.

Lemma wf_cofixpoint_typing_spine {cf:checker_flags} (Σ : global_env_ext) Γ ind u mfix idx d args args' :
  wf Σ.1 -> wf_local Σ Γ ->
  wf_cofixpoint Σ mfix ->
  nth_error mfix idx = Some d ->
  isType Σ Γ (dtype d) ->
  typing_spine Σ Γ (dtype d) args (mkApps (tInd ind u) args') ->
  check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.
Proof.
  intros wfΣ wfΓ wfcofix Hnth wat sp.
  apply wf_cofixpoint_all in wfcofix.
  destruct wfcofix as [mind [cr allfix]].
  eapply nth_error_all in allfix; eauto.
  simpl in allfix.
  destruct allfix as [ctx [i [u' [args'' eqty]]]].
  rw {}eqty in sp wat.
  eapply mkApps_ind_typing_spine in sp; auto.
  destruct sp as [instsub [makes Hargs Hind Hu subs subsl]].
  now subst ind.
Qed.

Lemma Construct_Ind_ind_eq {cf:checker_flags} {Σ} (wfΣ : wf Σ.1):
  forall {Γ n i args u i' args' u' mdecl idecl cdecl},
  Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
  (i = i') *
  (* Universe instances match *)
  cmp_ind_universes Σ i (context_assumptions (ind_params mdecl) + #|cstr_indices cdecl|) u u' *
  consistent_instance_ext Σ (ind_universes mdecl) u *
  consistent_instance_ext Σ (ind_universes mdecl) u' *
  (#|args| = (ind_npars mdecl + context_assumptions cdecl.(cstr_args))%nat) *
  ∑ parsubst argsubst parsubst' argsubst',
    let parctx := (subst_instance u (ind_params mdecl)) in
    let parctx' := (subst_instance u' (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0
    ((subst_context (inds (inductive_mind i) u mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance u cdecl.(cstr_args))))) in
    let argctx2 := (subst_context parsubst' 0
    ((subst_context (inds (inductive_mind i) u' mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance u' cdecl.(cstr_args))))) in
    let argctx' := (subst_context parsubst' 0 (subst_instance u' idecl.(ind_indices))) in

    [× spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx,
    spine_subst Σ Γ (firstn (ind_npars mdecl) args') parsubst' parctx',
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx,
    spine_subst Σ Γ (skipn (ind_npars mdecl) args')  argsubst' argctx' &
    ∑ s,
      sorts_local_ctx (lift_typing typing) Σ Γ argctx2 s ×
      (** Parameters match *)
      ws_cumul_pb_terms Σ Γ (firstn mdecl.(ind_npars) args) (firstn mdecl.(ind_npars) args') ×

    (** Indices match *)
    ws_cumul_pb_terms Σ Γ
      (map (subst0 (argsubst ++ parsubst) ∘
      subst (inds (inductive_mind i) u mdecl.(ind_bodies)) (#|cdecl.(cstr_args)| + #|ind_params mdecl|)
      ∘ (subst_instance u))
        cdecl.(cstr_indices))
      (skipn mdecl.(ind_npars) args') ].
Proof.
  intros Γ n i args u i' args' u' mdecl idecl cdecl h declc.
  destruct (on_declared_constructor declc) as [[onmind onind] [? [_ onc]]].
  pose proof (validity h) as vi'.
  eapply inversion_mkApps in h; auto.
  destruct h as [T [hC hs]].
  apply inversion_Construct in hC
    as [mdecl' [idecl' [cdecl' [hΓ [isdecl [const htc]]]]]]; auto.
  assert (vty:=declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const).
  eapply typing_spine_strengthen in hs. 3:eapply htc. all:eauto.
  unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
  unshelve eapply declared_constructor_to_gen in isdecl; eauto.
  destruct (declared_constructor_inj isdecl declc') as [? [? ?]].
  subst mdecl' idecl' cdecl'. clear isdecl.
  pose proof (on_constructor_inst declc _ const).
  destruct declc as [decli declc].
  destruct onc as [argslength cdecl_eq [cs' t] cargs cinds]; simpl.
  simpl in *.
  unfold type_of_constructor in hs. simpl in hs.
  rw cdecl_eq in hs.
  rw !subst_instance_it_mkProd_or_LetIn in hs.
  rw !subst_it_mkProd_or_LetIn subst_instance_length Nat.add_0_r in hs.
  rw subst_instance_mkApps subst_mkApps subst_instance_length in hs.
  assert (Hind : inductive_ind i < #|ind_bodies mdecl|).
  { destruct decli.
    now eapply nth_error_Some_length in H0. }
  rw (subst_inds_concl_head i) in hs => //.
  rw -it_mkProd_or_LetIn_app in hs.
  assert(ind_npars mdecl = context_assumptions (ind_params mdecl)).
  { now pose (onNpars onmind). }
  assert (closed_ctx (ind_params mdecl)).
  { destruct onmind.
    red in onParams. now apply closed_wf_local in onParams. }
  eapply mkApps_ind_typing_spine in hs as [isubst [Hisubst Hargslen Hi Hu Hargs Hs]]; auto.
  subst i'.
  eapply (isType_mkApps_Ind_inv wfΣ decli) in vi' as (parsubst & argsubst & [spars sargs parlen argslen cons]) => //.
  split=> //. split=> //.
  split; auto. split => //.
  now len in Hu.
  now rw Hargslen context_assumptions_app !context_assumptions_subst !context_assumptions_subst_instance; lia.

  exists (skipn #|cdecl.(cstr_args)| isubst), (firstn #|cdecl.(cstr_args)| isubst).
  apply make_context_subst_spec in Hisubst.
  move: Hisubst.
  rw List.rev_involutive.
  move/context_subst_app.
  rw !subst_context_length !subst_instance_length.
  rw context_assumptions_subst context_assumptions_subst_instance -H.
  move=>  [argsub parsub].
  rw closed_ctx_subst in parsub.
  now rw closedn_subst_instance_context.
  eapply subslet_app_inv in Hs.
  move: Hs. len. intuition auto.
  rw closed_ctx_subst in a0 => //.
  now rw closedn_subst_instance_context.

  (*rewrite -Heqp in spars sargs. simpl in *. clear Heqp. *)
  exists parsubst, argsubst.
  assert(wfar : wf_local Σ
  (Γ ,,, subst_instance u' (arities_context (ind_bodies mdecl)))).
  { eapply weaken_wf_local => //.
    unshelve epose proof (declared_inductive_to_gen decli); eauto.
    eapply wf_local_instantiate => //; destruct decli; eauto.
    eapply wf_arities_context => //; eauto. }
  assert(wfpars : wf_local Σ (subst_instance u (ind_params mdecl))).
    { eapply on_minductive_wf_params => //; eauto. destruct decli; eauto. }

  split; auto; try split; auto.
  - apply weaken_wf_local => //.
  - pose proof (subslet_length a0). rw subst_instance_length in H1.
    rw -H1 -subst_app_context.
    eapply (substitution_wf_local (Γ' := subst_instance u (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))); eauto.
    rw subst_instance_app; eapply subslet_app; eauto.
    now rw closed_ctx_subst ?closedn_subst_instance_context.
    eapply (weaken_subslet (Γ' := [])) => //.
    now eapply subslet_inds; eauto.
    rw -app_context_assoc.
    eapply weaken_wf_local => //.
    rw -subst_instance_app_ctx.
    apply a.
  - exists (map (subst_instance_sort u') x). split.
    * move/onParams: onmind. rw /on_context.
      pose proof (@wf_local_instantiate _ Σ (InductiveDecl mdecl) (ind_params mdecl) u').
      move=> H'. eapply X in H'; eauto.
      clear -wfar wfpars wfΣ hΓ cons decli t cargs sargs H0 H' a spars a0.
      eapply (subst_sorts_local_ctx (Γ' := [])
      (Δ := subst_context (inds (inductive_mind i) u' (ind_bodies mdecl)) 0
        (subst_instance u' (ind_params mdecl)))) => //.
      simpl. eapply weaken_wf_local => //.
      rw closed_ctx_subst => //.
      now rw closedn_subst_instance_context.
      simpl. rw -(subst_instance_length u' (ind_params mdecl)).
      eapply (subst_sorts_local_ctx (Δ := subst_instance u' (arities_context (ind_bodies mdecl)))) => //.
      eapply weaken_wf_local => //.
      rw -app_context_assoc.
      eapply weaken_sorts_local_ctx => //.
      rw -subst_instance_app_ctx.
      eapply sorts_local_ctx_instantiate => //; destruct decli; eauto.
      eapply (weaken_subslet (Γ' := [])) => //.
      now eapply subslet_inds; eauto.
      rw closed_ctx_subst ?closedn_subst_instance_context. auto.
      apply spars.
      unshelve eapply declared_inductive_to_gen in decli; eauto.
    * move: (All2_firstn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
      move: (All2_skipn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
      clear Hargs.
      rw !map_map_compose !map_app.
      rw -map_map_compose.
      rw (firstn_app_left).
      { rw !length_map to_extended_list_k_length. lia. }
      rw skipn_all_app_eq ?lengths //.
      rw !map_map_compose.
      assert (#|cdecl.(cstr_args)| <= #|isubst|).
      apply context_subst_length in argsub.
      len in argsub.
      now apply firstn_length_le_inv.

      rw -(firstn_skipn #|cdecl.(cstr_args)| isubst).
      rw -[map _ (to_extended_list_k _ _)]
                (map_map_compose _ _ _ (subst_instance u)
                                (fun x => subst _ _ (subst _ _ x))).
      rw subst_instance_to_extended_list_k.
      rw -[map _ (to_extended_list_k _ _)]map_map_compose.
      rw -to_extended_list_k_map_subst.
      rw subst_instance_length. lia.
      rw map_subst_app_to_extended_list_k.
      rw firstn_length_le => //.

      erewrite subst_to_extended_list_k.
      rw map_lift0. split. eauto.
      rw firstn_skipn. rw firstn_skipn in All2_skipn.
      now rw firstn_skipn.

      apply make_context_subst_spec_inv. now rw List.rev_involutive.

  - rw it_mkProd_or_LetIn_app.
    unfold type_of_constructor in vty.
    rw cdecl_eq in vty. move: vty.
    rw !subst_instance_it_mkProd_or_LetIn.
    rw !subst_it_mkProd_or_LetIn subst_instance_length Nat.add_0_r.
    rw subst_instance_mkApps subst_mkApps subst_instance_length.
    rw subst_inds_concl_head. all:simpl; auto.
Qed.

Lemma Construct_Ind_ind_eq' {cf:checker_flags} {Σ} (wfΣ : wf Σ.1):
  forall {Γ n i args u i' args' u' },
  Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
  ∑ mdecl idecl cdecl,
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ×
  (i = i') *
  (* Universe instances match *)
  cmp_ind_universes Σ i (context_assumptions (ind_params mdecl) + #|cstr_indices cdecl|) u u' *
  consistent_instance_ext Σ (ind_universes mdecl) u *
  consistent_instance_ext Σ (ind_universes mdecl) u' *
  (#|args| = (ind_npars mdecl + context_assumptions cdecl.(cstr_args))%nat) *
  ∑ parsubst argsubst parsubst' argsubst',
    let parctx := (subst_instance u (ind_params mdecl)) in
    let parctx' := (subst_instance u' (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0
    ((subst_context (inds (inductive_mind i) u mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance u cdecl.(cstr_args))))) in
    let argctx2 := (subst_context parsubst' 0
    ((subst_context (inds (inductive_mind i) u' mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance u' cdecl.(cstr_args))))) in
    let argctx' := (subst_context parsubst' 0 (subst_instance u' idecl.(ind_indices))) in

    [× spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx,
    spine_subst Σ Γ (firstn (ind_npars mdecl) args') parsubst' parctx',
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx,
    spine_subst Σ Γ (skipn (ind_npars mdecl) args')  argsubst' argctx' &
    ∑ s,
      sorts_local_ctx (lift_typing typing) Σ Γ argctx2 s ×
      (** Parameters match *)
      ws_cumul_pb_terms Σ Γ (firstn mdecl.(ind_npars) args) (firstn mdecl.(ind_npars) args') ×

    (** Indices match *)
    ws_cumul_pb_terms Σ Γ
      (map (subst0 (argsubst ++ parsubst) ∘
      subst (inds (inductive_mind i) u mdecl.(ind_bodies)) (#|cdecl.(cstr_args)| + #|ind_params mdecl|)
      ∘ (subst_instance u))
        cdecl.(cstr_indices))
      (skipn mdecl.(ind_npars) args') ].
Proof.
  intros Γ n i args u i' args' u' X.
  eapply inversion_mkApps in X as X'. destruct X' as (? & X' & _).
  eapply inversion_Construct in X' as (mdecl & idecl & cdecl & ? & ? & ? & ?); eauto.
  exists mdecl, idecl, cdecl. split; eauto.
  eapply Construct_Ind_ind_eq; eauto.
Qed.

Notation "⋆" := ltac:(solve [pcuic]) (only parsing).

Abbreviation decl_ws_cumul_pb Σ Γ := (All_decls_alpha_pb Conv
  (fun pb (x0 y0 : term) => Σ ;;; Γ ⊢ x0 ≤[pb] y0)).

Lemma conv_decls_fix_context_gen {cf:checker_flags} Σ Γ mfix mfix1 :
  wf Σ.1 ->
  All2 (fun d d' => Σ ;;; Γ ⊢ d.(dtype) = d'.(dtype) × eq_binder_annot d.(dname) d'.(dname)) mfix mfix1 ->
  forall Γ' Γ'',
  Σ ⊢ Γ ,,, Γ' = Γ ,,, Γ'' ->
  ws_cumul_ctx_pb_rel Conv Σ (Γ ,,, Γ') (fix_context_gen #|Γ'| mfix) (fix_context_gen #|Γ''| mfix1).
Proof.
  intros wfΣ a Γ' Γ'' convctx.
  split. eauto with fvs.
  induction a in Γ', Γ'', convctx |- *. constructor. simpl.
  destruct r as [r eqann].

  assert(decl_ws_cumul_pb Σ (Γ ,,, Γ' ,,, [])
    (vass (dname x) (lift0 #|Γ'| (dtype x)))
    (vass (dname y) (lift0 #|Γ''| (dtype y)))).
  { constructor; tas.
    pose proof (All2_fold_length convctx).
    rw !length_app in H. assert(#|Γ'|  = #|Γ''|) by lia.
    rw -H0.
    apply (weakening_ws_cumul_pb (Γ' := [])); eauto with fvs. }

  apply All2_fold_app.
  constructor => //. constructor.
  eapply (All2_fold_impl (P:= (fun Δ Δ' : context =>
  decl_ws_cumul_pb Σ
    (Γ ,,, (vass (dname x) (lift0 #|Γ'| (dtype x)) :: Γ') ,,, Δ)))).
  eapply (IHa (vass _ _ :: Γ') (vass _ _ :: Γ'')).
  cbn; constructor => //. constructor; eauto.
  depelim X. eauto.
  intros. red.
  now rw ![_ ,,, _]app_context_assoc.
Qed.

Lemma conv_decls_fix_context {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ mfix mfix1} :
  wf_local Σ Γ ->
  All2 (fun d d' => Σ ;;; Γ ⊢ d.(dtype) = d'.(dtype) × eq_binder_annot d.(dname) d'.(dname)) mfix mfix1 ->
  All2_fold (fun Δ Δ' : context => decl_ws_cumul_pb Σ (Γ ,,, Δ))
    (fix_context mfix) (fix_context mfix1).
Proof.
  intros wfΓ a.
  apply (conv_decls_fix_context_gen _ _  _ _ wfΣ a [] []).
  eapply ws_cumul_ctx_pb_refl. eauto with fvs.
Qed.

Lemma isLambda_red1 Σ Γ b b' : isLambda b -> red1 Σ Γ b b' -> isLambda b'.
Proof.
  destruct b; simpl; try discriminate.
  intros _ red.
  depelim red.
  symmetry in H; apply mkApps_Fix_spec in H. simpl in H. intuition.
  constructor. constructor.
Qed.

Lemma declared_inductive_unique {Σ mdecl idecl p} (q r : declared_inductive_gen (lookup_env Σ) p mdecl idecl) : q = r.
Proof.
  unfold declared_inductive in q, r.
  destruct q, r.
  now rw (uip e e0) (uip d d0).
Qed.

Lemma declared_inductive_unique_sig {cf:checker_flags} {Σ ind mib decl mib' decl'}
      (decl1 : declared_inductive_gen (lookup_env Σ) ind mib decl)
      (decl2 : declared_inductive_gen (lookup_env Σ) ind mib' decl') :
  @sigmaI _ (fun '(m, d) => declared_inductive_gen (lookup_env Σ) ind m d)
          (mib, decl) decl1 =
  @sigmaI _ _ (mib', decl') decl2.
Proof.
  pose proof (declared_inductive_inj decl1 decl2) as (<-&<-).
  pose proof (declared_inductive_unique decl1 decl2) as ->.
  reflexivity.
Qed.

Lemma ws_cumul_ctx_pb_rel_context_assumptions {cf:checker_flags} P Γ Δ Δ' :
  ws_cumul_ctx_pb_rel Conv P Γ Δ Δ' ->
  context_assumptions Δ = context_assumptions Δ'.
Proof.
  move=> [] _. induction 1; auto.
  cbn.
  depelim p; cbn; lia.
Qed.

Lemma invert_Case_Construct {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥)
  {Γ ci ind' pred i u brs args T} :
  Σ ;;; Γ |- tCase ci pred (mkApps (tConstruct ind' i u) args) brs : T ->
  ci.(ci_ind) = ind' /\
  exists br,
    nth_error brs i = Some br /\
    (#|args| = ci.(ci_npar) + context_assumptions br.(bcontext))%nat.
Proof.
  destruct hΣ as [wΣ].
  intros h.
  apply inversion_Case in h as ih ; auto.
  destruct ih
    as [mdecl [idecl [isdecl [indices [cinv cum]]]]].
  destruct cinv.
  pose proof scrut_ty as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ scrut_ty declc); eauto.
  simpl in *.
  intuition auto.
  subst.
  destruct declc as (decli&nthctor).
  cbn in nthctor.
  unshelve eapply declared_inductive_to_gen in decli, isdecl; eauto.
  pose proof (declared_inductive_unique_sig isdecl decli) as H; noconf H.
  eapply All2i_nth_error_l in nthctor as H; eauto.
  destruct H as (br & nth & cc & ? & ? &?).
  exists br.
  split; auto.
  cbn in cc.
  assert (context_assumptions (bcontext br) = context_assumptions (cstr_branch_context ci mdecl cdecl')).
  { clear -cc. induction cc; simpl; auto. destruct r; cbn; auto. lia. }
  rw H.
  unfold cstr_branch_context, expand_lets_ctx, expand_lets_k_ctx.
  repeat (rw ?context_assumptions_subst_context
                  ?context_assumptions_lift_context
                  ?context_assumptions_subst_instance).
  congruence.
Qed.

Lemma Proj_Construct_ind_eq {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) {Γ i' p c u l T} :
  Σ ;;; Γ |- tProj p (mkApps (tConstruct i' c u) l) : T ->
  p.(proj_ind) = i'.
Proof.
  destruct hΣ as [wΣ].
  intros h.
  apply inversion_Proj in h ; auto.
  destruct h as [uni [mdecl [idecl [pdecl [args' [? [declp [hc [? ?]]]]]]]]].
  pose proof hc as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ hc declc); eauto.
  intuition auto.
Qed.

Lemma invert_Proj_Construct {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) {Γ p i' c u l T} :
  Σ ;;; Γ |- tProj p (mkApps (tConstruct i' c u) l) : T ->
  p.(proj_ind) = i' /\ c = 0 /\ p.(proj_npars) + p.(proj_arg) < #|l|.
Proof.
  intros h.
  assert (h' := h).
  apply Proj_Construct_ind_eq in h' as <-; auto.
  destruct hΣ as [wΣ].
  split; [reflexivity|].
  apply inversion_Proj in h ; auto.
  destruct h as [uni [mdecl [idecl [pdecl [args' [? [declp [hc [? ?]]]]]]]]].
  pose proof hc as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  unshelve epose proof (declp' := declared_projection_to_gen declp) ; eauto.
  unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
  pose proof (declared_inductive_unique_sig declp'.p1.p1 declc'.p1) as H; noconf H.
  cbn in H.
  clear H.
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ hc declc); eauto.
  simpl in X.
  destruct (on_declared_projection declp).
  set (oib := declared_inductive_inv _ _ _ _) in *.
  simpl in *.
  destruct declc.
  destruct p1 as [[[? ?] ?] ?].
  destruct p0.
  destruct (ind_cunivs oib) as [|? []] eqn:hctor in y; try contradiction.
  simpl in H. simpl in H0.
  rw e0 in H0.
  destruct c; simpl in H0 => //; noconf H0.
  intuition auto.
  2:{ rw nth_error_nil in H0. noconf H0. }
  rw b0.
  destruct declp as [decli [nthp parseq]].
  simpl in *. rw parseq. lia.
Qed.
Notation "!! t" := ltac:(refine t) (at level 10, t at level 200, only parsing).

Lemma isType_mkApps_Ind_smash {cf:checker_flags} {Σ Γ ind u params args} {wfΣ : wf Σ} {mdecl idecl} :
  declared_inductive Σ.1 ind mdecl idecl ->
  isType Σ Γ (mkApps (tInd ind u) (params ++ args)) ->
  #|params| = ind_npars mdecl ->
  let parctx := subst_instance u mdecl.(ind_params) in
  let argctx := subst_instance u idecl.(ind_indices) in
  spine_subst Σ Γ params (List.rev params) (smash_context [] parctx) ×
  spine_subst Σ Γ args (List.rev args) (smash_context [] (subst_context_let_expand (List.rev params) parctx argctx)) ×
  consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> isdecl isty hpars.
  pose proof (isType_wf_local isty).
  destruct isty as (_ & s & Hs & _).
  eapply invert_type_mkApps_ind in Hs as [sp cu]; tea.
  move=> parctx argctx.
  erewrite ind_arity_eq in sp.
  2: eapply PCUICInductives.oib ; eauto.
  rw !subst_instance_it_mkProd_or_LetIn in sp.
  rw -it_mkProd_or_LetIn_app /= in sp.
  eapply arity_typing_spine in sp as [hle hs [insts sp]]; tea.
  eapply spine_subst_smash in sp; tea.
  rw smash_context_app_expand in sp.
  rw List.rev_app_distr in sp.
  pose proof (declared_minductive_ind_npars isdecl) as hnpars.
  eapply spine_subst_app_inv in sp as [sppars spargs]; tea.
  2:{ rw context_assumptions_smash_context /=. len. }
  len in sppars. len in hle. len in spargs.
  simpl in *.
  assert (context_assumptions (ind_indices idecl) = #|List.rev args|) by (len; lia).
  rw H skipn_all_app in sppars, spargs.
  split => //. split => //.
  rw -(Nat.add_0_r #|List.rev args|) firstn_app_2 firstn_0 // app_nil_r in spargs.
  rw (smash_context_subst []).
  rw -(expand_lets_smash_context _ []).
  exact spargs.
Qed.

Lemma instantiate_subslet {cf Σ} {Γ s Δ} {c} {decl : global_decl} {u : Instance.t} {wfΣ : wf Σ.1} :
  lookup_env Σ.1 c = Some decl ->
	subslet (Σ.1, universes_decl_of_decl decl) Γ s Δ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  subslet Σ Γ@[u] s@[u] Δ@[u].
Proof.
  intros hl subs cu.
  induction subs.
  - constructor.
  - cbn. constructor; auto.
    cbn. rw -subst_instance_subst. eapply typing_subst_instance_decl; tea.
  - cbn. rw subst_instance_subst. constructor; auto.
    cbn. rw - !subst_instance_subst.
    eapply typing_subst_instance_decl; tea.
Qed.

Lemma instantiate_wf_subslet {cf Σ} {Γ s Δ} {c} {decl : global_decl} {u : Instance.t} {wfΣ : wf Σ.1} :
  lookup_env Σ.1 c = Some decl ->
	wf_subslet (Σ.1, universes_decl_of_decl decl) Γ s Δ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_subslet Σ Γ@[u] s@[u] Δ@[u].
Proof.
  intros hl [wf subs] cu.
  split.
  rw -subst_instance_app_ctx. eapply wf_local_instantiate; tea.
  now eapply instantiate_subslet.
Qed.

Lemma projection_context_gen_inst {cf} {Σ mdecl idecl ind u} :
  declared_inductive Σ.1 ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  (projection_context_gen ind mdecl idecl)@[u] =
  projection_context ind mdecl idecl u.
Proof.
  intros isdecl cu.
  rw /projection_context /projection_context_gen.
  rw /snoc /= -(subst_instance_smash _ _ []).
  cbn. f_equal. rw /map_decl /= /vass /=.
  f_equal. rw subst_instance_mkApps /=.
  rw subst_instance_to_extended_list. f_equal.
  cbn.
  now rw [subst_instance_instance _ _](subst_instance_id_mdecl _ _ _ cu).
Qed.

Lemma substitution_subslet {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ Γ' Δ s s' Δ'} :
  subslet Σ Γ s Δ ->
  wf_subslet Σ (Γ ,,, Δ ,,, Γ') s' Δ' ->
  wf_subslet Σ (Γ ,,, subst_context s 0 Γ') (map (subst s #|Γ'|) s') (subst_context s #|Γ'| Δ').
Proof.
  intros subl [wf subs].
  split.
  { rw -app_context_assoc.
    relativize #|Γ'|.
    erewrite <-subst_context_app. 2:lia.
    eapply substitution_wf_local; tea.
    now rw app_context_assoc. }
  clear wf.
  induction subs in s, subl |- *.
  * cbn. intros. constructor.
  * cbn. rw subst_context_snoc. constructor; auto.
    eapply substitution in t0; tea.
    cbn. rw -(subslet_length subs).
    now rw -distr_subst.
  * cbn. rw subst_context_snoc.
    eapply substitution in t0; tea.
    specialize (IHsubs _ subl).
    epose proof (cons_let_def _ _ _ _ _ _ _ IHsubs).
    rw !distr_subst in t0.
    specialize (X t0).
    rw -(subslet_length subs).
    now rw -distr_subst in X.
Qed.

Lemma weaken_wf_subslet {cf Σ} {wfΣ : wf Σ} s (Δ Γ Γ' : context) :
  wf_local Σ Γ →
  wf_subslet Σ Γ' s Δ →
  wf_subslet Σ (Γ,,, Γ') s Δ.
Proof.
  intros wfΓ [wf subs]. split.
  rw -app_context_assoc.
  eapply weaken_wf_local => //.
  eapply weaken_subslet; tea.
  now eapply All_local_env_app_inv in wf.
Qed.

Lemma on_projections_indices {mdecl i idecl cs} :
  on_projections mdecl (inductive_mind i) (inductive_ind i)
    idecl (ind_indices idecl) cs ->
    idecl.(ind_indices) = [].
Proof.
  move/on_projs_noidx. destruct ind_indices; try discriminate; auto.
Qed.


Lemma subslet_projs {cf:checker_flags} {Σ} {wfΣ : wf Σ} {i mdecl idecl args} :
  declared_inductive Σ.1 i mdecl idecl ->
  match ind_ctors idecl return Type with
  | [cs] =>
    on_projections mdecl (inductive_mind i) (inductive_ind i)
     idecl (ind_indices idecl) cs ->
     forall Γ t u,
     let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
     Σ;;; Γ |- t : mkApps (tInd i u) args ->
     wf_subslet Σ Γ
      (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cs)) t)
      (subst_context (List.rev args) 0
        (subst_context (extended_subst (ind_params mdecl)@[u] 0) 0
          (smash_context []
            (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
              #|ind_params mdecl| (subst_instance u (cstr_args cs))))))
  | _ => True
  end.
Proof.
  intros Hdecl.
  destruct ind_ctors as [|cs []] eqn:Heq; trivial.
  intros onp. simpl. intros Γ t u.
  rw (smash_context_subst []).
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cstr_args cs)).
  { destruct onp. lia. }
  intros Ht.
  epose proof (declared_projections_subslet _ Hdecl cs Heq onp _ (Nat.le_refl _)).
  have v := !!(validity Ht). eapply isType_mkApps_Ind_inv in v as [? [? []]]; tea; pcuic.
  unshelve epose proof (Hdecl' := declared_inductive_to_gen Hdecl); eauto.
  eapply (instantiate_wf_subslet (decl:=InductiveDecl mdecl)) in X; tea. 2:apply Hdecl'.
  move: X. rw Nat.sub_diag skipn_0.
  rw subst_instance_subst_context subst_instance_lift_context.
  rw subst_context_lift_context_comm //.
  rw (projection_context_gen_inst Hdecl) //.
  rw /projection_context.
  eapply spine_subst_smash in s.
  intros Hs.
  have wfΓ : wf_local Σ Γ by (eapply typing_wf_local; eauto).
  eapply weaken_wf_subslet in Hs;tea.
  eapply (substitution_subslet (Γ' := [_])) in Hs; tea.
  2:eapply s.
  move: Hs. cbn.
  rw subst_context_snoc /= /subst_decl /= /map_decl /= subst_mkApps /=.
  rw (spine_subst_subst_to_extended_list_k s).
  move: (on_projections_indices onp) => heq. rw heq in e0.
  cbn in e0.
  assert (#|args| = ind_npars mdecl).
  rw -(firstn_skipn (ind_npars mdecl) args) length_app e0 e //.
  rw firstn_all2 //. lia.
  move/(substitution_subslet (Γ := Γ) (Δ := [_]) (Γ' := []) (subslet_ass_tip Ht)).
  cbn.
  rw [(projs _ _ _)@[u]]projs_subst_instance projs_subst_above // subst_projs_inst.
  rw subst_instance_subst_context.
  rw instantiate_inds //. exact Hdecl.
  rw subst_context_lift_context_comm //.
  rw subst_context_lift_context_cancel //.
  rw subst_instance_extended_subst //.
  rw subst_instance_smash //.
Qed.

Ltac unf_env :=
  change PCUICEnvironment.it_mkProd_or_LetIn with it_mkProd_or_LetIn in *;
  change PCUICEnvironment.to_extended_list_k with to_extended_list_k in *;
  change PCUICEnvironment.ind_params with ind_params in *.

Derive Signature for positive_cstr.

Lemma positive_cstr_it_mkProd_or_LetIn mdecl i Γ Δ t :
  positive_cstr mdecl i Γ (it_mkProd_or_LetIn Δ t) ->
  All_local_env (fun Δ j => positive_cstr_arg mdecl (Γ ,,, Δ) (j_typ j))
    (smash_context [] Δ) *
  positive_cstr mdecl i (Γ ,,, smash_context [] Δ) (expand_lets Δ t).
Proof.
  revert Γ t; unfold expand_lets, expand_lets_k;
   induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; intros Γ t.
  - simpl; intuition auto. now rw subst_empty lift0_id.
  - rw it_mkProd_or_LetIn_app /=; intros H; depelim H.
    solve_discr. rw smash_context_app_def.
    rw /subst1 subst_it_mkProd_or_LetIn in H.
    specialize (X (subst_context [b] 0 Δ) ltac:(len; lia) _ _ H).
    simpl; len in X. len.
    destruct X; split; auto. simpl.
    rw extended_subst_app /= !subst_empty !lift0_id lift0_context.
    rw subst_app_simpl; len => /=.
    simpl.
    epose proof (distr_lift_subst_rec _ [b] (context_assumptions Δ) #|Δ| 0).
    rw !Nat.add_0_r in H0. now erewrite <- H0.
  - rw it_mkProd_or_LetIn_app /=; intros H; depelim H.
    solve_discr. rw smash_context_app_ass.
    specialize (X Δ ltac:(len; lia) _ _ H).
    simpl; len.
    destruct X; split; auto. simpl.
    eapply All_local_env_app.
    constructor; auto.
    eapply (All_local_env_impl _ _ _ a). intros; auto.
    now rw app_context_assoc. simpl.
    rw extended_subst_app /=.
    rw subst_app_simpl; len => /=.
    simpl.
    rw subst_context_lift_id.
    rw Nat.add_comm Nat.add_1_r subst_reli_lift_id.
    apply context_assumptions_length_bound. now rw app_context_assoc.
Qed.

Lemma closedn_expand Γ Δ x :
  closed_ctx Γ ->
  closedn (context_assumptions Δ + #|Γ|) (expand_lets Δ x) =
  closedn (context_assumptions Δ + context_assumptions Γ) (expand_lets (Γ ,,, Δ) x).
Proof.
  intros clΓ.
  rw /expand_lets.
  rw expand_lets_k_app /=.
  relativize (context_assumptions Δ + context_assumptions Γ).
  erewrite (closedn_expand_lets_eq 0) => /= //. now cbn.
Qed.

Lemma closedn_expand' (Γ Δ : context) x :
  closedn_ctx #|Γ| Δ ->
  closedn (context_assumptions Δ + #|Γ|) (expand_lets Δ x) ->
  closedn (#|Δ| + #|Γ|) x.
Proof.
  intros clΓ cl.
  eapply closed_upwards in cl.
  move: cl.
  rw /expand_lets.
  erewrite (closedn_expand_lets_eq #|Γ|) => /= //.
  now rw Nat.add_0_r Nat.add_comm.
  lia.
Qed.

Lemma positive_cstr_closed_indices {cf} {Σ} {wfΣ : wf Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (closedn (context_assumptions (cstr_args cdecl) + #|ind_params mdecl|))
    (map (expand_lets (cstr_args cdecl)) (cstr_indices cdecl)).
Proof.
  intros.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_ctype_positive)).
  rw onc.(cstr_eq) in X. unf_env.
  rw -it_mkProd_or_LetIn_app in X.
  eapply positive_cstr_it_mkProd_or_LetIn in X as [hpars hpos].
  rw app_context_nil_l in hpos.
  rw expand_lets_mkApps in hpos.
  unfold cstr_concl_head in hpos.
  have subsrel := expand_lets_tRel (#|ind_bodies mdecl| - S (inductive_ind i.1))
    (ind_params mdecl ,,, cstr_args cdecl). len in subsrel.
  rw (Nat.add_comm #|cstr_args cdecl|) Nat.add_assoc in subsrel.
  rw {}subsrel in hpos.
  depelim hpos; solve_discr.
  eapply All_map_inv in a.
  eapply All_app in a as [ _ a].
  eapply All_map; eapply (All_impl a); intros x; len.
  rw closedn_expand //.
  exact (declared_inductive_closed_params H).
Qed.

Lemma positive_cstr_arg_subst_instance {mdecl Γ} {t} u :
  positive_cstr_arg mdecl Γ t ->
  positive_cstr_arg mdecl (subst_instance u Γ) (subst_instance u t).
Proof.
  induction 1.
  - constructor 1; len.
    now rw closedn_subst_instance.
  - rw subst_instance_mkApps.
    econstructor 2; unfold mdecl_at_i in *; len => //; eauto.
    eapply All_map; solve_all.
    now rw closedn_subst_instance.
  - simpl. constructor 3; len => //.
    now rw subst_instance_subst in IHX.
  - simpl. constructor 4; len => //.
    now rw closedn_subst_instance.
Qed.

Import ssrbool.

Lemma invert_red_mkApps_tRel {cf} {Σ} {wfΣ : wf Σ} {Γ n d args t'} :
  nth_error Γ n = Some d -> decl_body d = None ->
  Σ ;;; Γ ⊢ mkApps (tRel n) args ⇝ t' ->
  ∑ args' : list term, t' = mkApps (tRel n) args' × red_terms Σ Γ args args'.
Proof.
  move=> hnth db [onΓ ont red].
  destruct Σ.
  move: ont. rw PCUICOnFreeVars.on_free_vars_mkApps /= => /andP[] // => onn onargs.
  unshelve eapply (red_mkApps_tRel (Γ := exist Γ onΓ) _ hnth db) in red as [args' [eq redargs]] => //.
  exists args'; split => //.
  cbn in redargs. solve_all.
  eapply into_closed_red; eauto.
Qed.

Lemma ws_cumul_pb_mkApps_tRel {cf} {Σ} {wfΣ : wf Σ} {Γ n d u u'} :
  nth_error Γ n = Some d -> decl_body d = None ->
  Σ ;;; Γ ⊢ mkApps (tRel n) u ≤ mkApps (tRel n) u' ->
  ws_cumul_pb_terms Σ Γ u u'.
Proof.
  intros Hnth Hd cum.
  pose proof (ws_cumul_pb_is_closed_context cum).
  eapply ws_cumul_pb_red in cum as [v' [v [redl redr leq]]].
  eapply invert_red_mkApps_tRel in redl as [args' [-> conv]]; eauto.
  eapply invert_red_mkApps_tRel in redr as [args'' [-> conv']]; eauto.
  eapply All2_trans. apply _.
  now eapply red_terms_ws_cumul_pb_terms.
  eapply eq_term_upto_univ_mkApps_l_inv in leq as [u'' [l' [[eqrel eqargs] eq']]].
  depelim eqrel. eapply mkApps_eq_inj in eq' as [_ ->] => //.
  etransitivity; [|symmetry; eapply red_terms_ws_cumul_pb_terms]; eauto.
  eapply closed_red_terms_open_right in conv.
  eapply closed_red_terms_open_right in conv'.
  eapply eq_terms_ws_cumul_pb_terms; eauto.
  all:solve_all.
Qed.

Lemma nth_error_subst_instance u Γ n :
  nth_error (subst_instance u Γ) n =
  option_map (map_decl (subst_instance u)) (nth_error Γ n).
Proof.
  now rw nth_error_map.
Qed.

Lemma ws_cumul_pb_terms_confl {cf} {Σ} {wfΣ : wf Σ} {Γ u u'} :
  ws_cumul_pb_terms Σ Γ u u' ->
  ∑ nf nf', (red_terms Σ Γ u nf * red_terms Σ Γ u' nf') * (All2 (eq_term Σ Σ) nf nf').
Proof.
  intros cv.
  induction cv.
  - exists [], []; intuition auto.
  - destruct IHcv as [nf [nf' [[redl redr] eq]]].
    eapply ws_cumul_pb_red in r as [x' [y' [redx redy eq']]].
    exists (x' :: nf), (y' :: nf'); intuition auto.
Qed.

Lemma closed_red_mkApps {cf} {Σ} {wfΣ : wf Σ} Γ f u u' :
  is_closed_context Γ ->
  is_open_term Γ f ->
  red_terms Σ Γ u u' ->
  Σ ;;; Γ ⊢ mkApps f u ⇝ mkApps f u'.
Proof.
  intros onΓ ont red.
  eapply into_closed_red; auto.
  - apply red_mkApps; auto.
    solve_all. apply X.
  - rw PCUICOnFreeVars.on_free_vars_mkApps ont.
    eapply closed_red_terms_open_left in red; solve_all.
Qed.

Lemma ws_cumul_pb_mkApps_eq {cf} {Σ} {wfΣ : wf Σ} Γ f f' u u' :
  is_closed_context Γ ->
  is_open_term Γ f ->
  is_open_term Γ f' ->
  compare_term_napp Σ Σ Cumul #|u| f f' ->
  ws_cumul_pb_terms Σ Γ u u' ->
  Σ ;;; Γ ⊢ mkApps f u ≤ mkApps f' u'.
Proof.
  intros onΓ onf onf' eqf equ.
  eapply ws_cumul_pb_red.
  eapply ws_cumul_pb_terms_confl in equ as [nf [nf' [[redl redr] eq]]] => //.
  exists (mkApps f nf), (mkApps f' nf').
  split.
  eapply closed_red_mkApps; eauto.
  eapply closed_red_mkApps; eauto.
  eapply eq_term_upto_univ_napp_mkApps.
  now rw Nat.add_0_r -(All2_length redl).
  apply eq.
Qed.

Lemma ws_cumul_pb_LetIn_inv {cf} {Σ} {wfΣ : wf Σ} {le Γ na na' b b' ty ty' t t'} :
  Σ ;;; Γ ⊢ tLetIn na b ty t ≤[le] tLetIn na' b' ty' t' ->
  Σ ;;; Γ ⊢ t {0 := b} ≤[le] t' {0 := b'}.
Proof.
  intros cum.
  eapply ws_cumul_pb_LetIn_l_inv; eauto.
  eapply ws_cumul_pb_LetIn_r_inv; eauto.
Qed.

Lemma ws_cumul_pb_LetIn_subst {cf} {Σ} {wfΣ : wf Σ} {le Γ na na' b b' ty ty' t t'} :
  is_open_term Γ (tLetIn na b ty t) ->
  is_open_term Γ (tLetIn na' b' ty' t') ->
  Σ ;;; Γ ⊢ t {0 := b} ≤[le] t' {0 := b'} ->
  Σ ;;; Γ ⊢ tLetIn na b ty t ≤[le] tLetIn na' b' ty' t'.
Proof.
  intros onl onr cum.
  transitivity (t {0 := b}).
  eapply red_ws_cumul_pb. eapply into_closed_red; eauto.
  eapply red1_red. econstructor. eauto with fvs.
  transitivity (t' {0 := b'}) => //.
  eapply red_ws_cumul_pb_inv.
  eapply into_closed_red; eauto.
  eapply red1_red; econstructor. eauto with fvs.
Qed.

(* A variant where the codomain cumulativity is in the "larger" context.
   Not valid under contravariant subtyping.
*)
Lemma ws_cumul_pb_Prod_Prod_inv_l {cf} {Σ} {wfΣ : wf Σ} Γ na na' A B A' B' :
  Σ ;;; Γ ⊢ tProd na A B ≤ tProd na' A' B' ->
  [× eq_binder_annot na na', Σ ;;; Γ ⊢ A = A' & Σ ;;; Γ ,, vass na A ⊢ B ≤ B'].
Proof.
  move/ws_cumul_pb_Prod_Prod_inv => []; split; auto.
  eapply ws_cumul_pb_ws_cumul_ctx; tea.
  constructor; auto. eapply ws_cumul_ctx_pb_refl. eauto with fvs.
  constructor; auto. exact p0.
Qed.

Lemma inds_is_open_terms (Γ : context) ind mdecl u :
  forallb (is_open_term Γ) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  move: (@closed_inds ind mdecl u).
  eapply forallb_impl. intros x _.
  rw -is_open_term_closed // => cl.
  eapply closed_upwards; tea; auto. len.
Qed.

Lemma inds_nth_error ind u l n t :
  nth_error (inds ind u l) n = Some t -> ∑ n, t = tInd {| inductive_mind := ind ; inductive_ind := n |} u.
Proof.
  unfold inds in *. generalize (#|l|). clear. revert t.
  induction n; intros.
  - destruct n. cbn in H. congruence. cbn in H. inv H.
    eauto.
  - destruct n0. cbn in H. congruence. cbn in H.
    eapply IHn. eauto.
Qed.


Lemma positive_cstr_arg_subst {cf} {Σ} {wfΣ : wf Σ} {ind mdecl idecl Γ t u u'} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  cmp_opt_variance (compare_universe Σ) Cumul (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  Σ ;;; subst_instance u (ind_arities mdecl) ,,, subst_instance u Γ ⊢ (subst_instance u t) ≤ (subst_instance u' t) ->
  positive_cstr_arg mdecl Γ t ->
  (Σ ;;; subst_context (ind_subst mdecl ind u) 0 (subst_instance u Γ) ⊢
    (subst (ind_subst mdecl ind u) #|Γ| (subst_instance u t)) ≤
     subst (ind_subst mdecl ind u') #|Γ| (subst_instance u' t)).
Proof.
  intros decli cu ru cl cum pos.
  pose proof (proj1 decli) as declm.
  induction pos.
  - rw -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
    eapply substitution_ws_cumul_pb in cum; eauto.
    2:{ eapply subslet_inds; eauto. }
    rw !subst_closedn ?closedn_subst_instance //.
    rw !subst_closedn ?closedn_subst_instance // in cum; len; auto.
    now rw app_context_nil_l in cum.

  - epose proof (ws_cumul_pb_is_closed_context cum).
    rw !subst_instance_mkApps !subst_mkApps in cum |- *.
    simpl in cum. eapply ws_cumul_pb_mkApps_tRel in cum; eauto; cycle 1.
    { destruct m as [? [? ?]].
      rw nth_error_app_ge // subst_instance_length //
         nth_error_subst_instance.
      unfold ind_arities, arities_context.
      rw rev_map_spec -map_rev.
      rw nth_error_map e0 /=. reflexivity. }
    1:trivial.
    rw -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
    eapply ws_cumul_pb_terms_subst in cum.
    3:{ eapply subslet_untyped_subslet, (subslet_inds (u:=u)); eauto. }
    3:{ eapply subslet_untyped_subslet, (subslet_inds (u:=u)); eauto. }
    2:{ rw app_context_nil_l; eauto with fvs.
        move: H. rw on_free_vars_ctx_app => /andP[] //. }
    2:{ pose proof (inds_is_open_terms [] ind mdecl u).
        solve_all. eapply All_All2; tea.
        cbn; intros. eapply ws_cumul_pb_refl; eauto. }
    rw app_context_nil_l // in cum. len in cum.
    rw /ind_subst.
    eapply ws_cumul_pb_mkApps_eq => //; destruct m as [? [? ?]].
    * move: cl. rw -is_closed_ctx_closed => cl.
      apply (closedn_ctx_subst 0 0). cbn. len.
      rw !closedn_subst_instance_context. rw /ind_arities in cl.
      move: cl. rw closedn_subst_instance_context closedn_ctx_app. len. move/andP=> []//.
      eapply closed_inds.
    * cbn. destruct (leb_spec_Set #|Γ| k); try lia.
      destruct (nth_error (inds _ _ _) _) eqn:hnth.
      eapply inds_nth_error in hnth as [n ->]. now cbn.
      eapply nth_error_None in hnth. len in hnth; lia.
    * cbn. destruct (leb_spec_Set #|Γ| k); try lia.
      destruct (nth_error (inds _ _ _) _) eqn:hnth.
      eapply inds_nth_error in hnth as [n ->]. now cbn.
      eapply nth_error_None in hnth. len in hnth; lia.
    * rw !length_map.
      simpl. destruct (Nat.leb #|Γ| k) eqn:eqle.
      eapply Nat.leb_le in eqle.
      rw /ind_subst !inds_spec !rev_mapi !nth_error_mapi.
      unshelve epose proof (declm' := declared_minductive_to_gen declm); eauto.
      rw H2 /=. simpl. constructor. simpl.
      unfold cmp_global_instance, cmp_global_instance_gen. simpl.
      assert(declared_inductive Σ {|
      inductive_mind := inductive_mind ind;
      inductive_ind := Nat.pred #|ind_bodies mdecl| - (k - #|Γ|) |} mdecl i).
      { split; auto. simpl. rw -H2 nth_error_rev; lia_f_equal. }
      unfold lookup_inductive.
      unshelve epose proof (H0' := declared_inductive_to_gen H3); eauto.
      rw (declared_inductive_lookup_gen H0') //.
      destruct (on_declared_inductive H3) as [onmind onind] => //. simpl in *.
      rw e /ind_realargs.
      rw !onind.(ind_arity_eq).
      rw !destArity_it_mkProd_or_LetIn /=. len; simpl.
      rw (Nat.leb_refl) //.
      eapply Nat.leb_nle in eqle. lia.
    * do 2 eapply All2_map. do 2 eapply All2_map_inv in cum.
      eapply All2_All in cum. apply All_All2_refl.
      solve_all.
      now rw !subst_closedn ?closedn_subst_instance // in b |- *.

  - simpl. simpl in cum.
    eapply ws_cumul_pb_LetIn_subst. eauto.
    { rw -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
      eapply substitution_ws_cumul_pb in cum.
      2:{ eapply (subslet_inds (u:=u)); eauto. }
      rw app_context_nil_l /= in cum.
      rw /ind_subst. eapply ws_cumul_pb_is_open_term_left in cum.
      now rw subst_instance_length in cum. }
    { eapply ws_cumul_pb_is_open_term_right in cum.
    { rw -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
      eapply is_open_term_subst_gen in cum.
      2:{ rw // app_context_nil_l //.
          rw - !is_closed_ctx_closed.
          now rw subst_instance_app_ctx in cl. }
          (* eapply wf_local_closed_context in cl. eauto with fvs. } *)
      { cbn -[PCUICOnFreeVars.on_free_vars] in cum.
        rw subst_instance_length app_context_nil_l in cum. eapply cum. }
      1-2:eapply inds_is_open_terms. len. len. } }
    rw !subst_instance_subst /= in IHpos.
    rw !distr_subst /= in IHpos. rw /subst1.
    eapply IHpos => //.
    eapply ws_cumul_pb_LetIn_inv in cum; eauto.

  - simpl in cum |- *.
    eapply ws_cumul_pb_Prod_Prod_inv_l in cum as [eqna dom codom]; eauto.
    eapply ws_cumul_pb_Prod; eauto.
    * rw -(app_context_nil_l (_ ,,, _)) app_context_assoc in dom.
      eapply substitution_ws_cumul_pb in dom; rw ?app_context_nil_l; eauto.
      2:{ eapply subslet_inds; eauto. }
      rw ?app_context_nil_l ?closedn_subst_instance // in dom.
      rw !subst_closedn ?closedn_subst_instance // in dom; len; auto.
      now rw !subst_closedn ?closedn_subst_instance.
    * cbn -[closedn_ctx] in IHpos. rw subst_context_snoc in IHpos.
      rw length_map Nat.add_0_r in IHpos. eapply IHpos; eauto.
      cbn. rw cl /=. len.
      rw closedn_subst_instance.
      eapply closed_upwards; eauto; lia.
Qed.

Lemma positive_cstr_closed_args_subst_arities {cf} {Σ} {wfΣ : wf Σ} {u u' Γ}
   {i ind mdecl idecl cdecl ind_indices cs} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  on_constructor cumulSpec0 (lift_typing typing) (Σ.1, ind_universes mdecl) mdecl i idecl ind_indices cdecl cs ->
  cmp_opt_variance (compare_universe Σ) Cumul (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
  closed_ctx (subst_instance u (ind_params mdecl)) ->
  wf_local Σ (subst_instance u (ind_arities mdecl ,,, smash_context [] (ind_params mdecl) ,,, Γ)) ->
  All_local_env (fun Γ j => positive_cstr_arg mdecl ([] ,,, (smash_context [] (ind_params mdecl) ,,, Γ)) (j_typ j)) Γ ->
  assumption_context Γ ->
  ws_cumul_ctx_pb_rel Cumul Σ (subst_instance u (ind_arities mdecl) ,,,
      subst_instance u
        (smash_context [] (PCUICEnvironment.ind_params mdecl)))
   (subst_instance u Γ) (subst_instance u' Γ) ->
  ws_cumul_ctx_pb_rel Cumul Σ (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl)))
    (subst_context (ind_subst mdecl ind u) (context_assumptions (ind_params mdecl)) (subst_instance u Γ))
    (subst_context (ind_subst mdecl ind u') (context_assumptions (ind_params mdecl)) (subst_instance u' Γ)).
Proof.
  intros * decli cu onc onv cl wf cpos ass.
  intros [clΓ cum].
  split.
  rw -is_closed_ctx_closed.
  rw subst_instance_smash.
  now apply closedn_smash_context.
  revert cum.
  induction cpos; simpl; rw ?subst_context_nil ?subst_context_snoc; try solve [constructor; auto].
  all:rw ?length_map; intros cv; depelim cv; depelim wf.
  eassert (isTypeRel Σ
  (subst_instance u (ind_arities mdecl) ,,,
   subst_instance u (smash_context [] (ind_params mdecl) ,,, Γ))
  (subst_instance u t) _).
  { rw -subst_instance_app_ctx app_context_assoc //. eassumption. }
  depelim a.
  all:constructor.
  - eapply IHcpos. auto. now depelim ass. apply cv.
  - constructor; auto. cbn in *.
    eapply positive_cstr_arg_subst in t0; eauto. len.
    move: t0.
    rw app_context_nil_l subst_instance_app_ctx subst_context_app.
    rw closed_ctx_subst //.
    rw subst_instance_smash.
    now apply closedn_smash_context.
    len.
    rw app_context_nil_l !subst_instance_app_ctx // app_context_assoc //.
    eapply ws_cumul_pb_is_closed_context in eqt.
    now rw is_closed_ctx_closed.
    rw app_context_nil_l !subst_instance_app_ctx // app_context_assoc //.
  - exfalso; now depelim ass.
  - exfalso; now depelim ass.
Qed.

Lemma positive_cstr_closed_args {cf} {Σ} {wfΣ : wf Σ} {u u'}
  {ind mdecl idecl cdecl} :
  declared_constructor Σ ind mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  cmp_opt_variance (compare_universe Σ) Cumul (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
 ws_cumul_ctx_pb_rel Cumul Σ (subst_instance u (ind_arities mdecl) ,,,
    subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))
 (smash_context []
    (subst_instance u
       (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
          (cstr_args cdecl))))
 (smash_context []
    (subst_instance u'
       (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
          (cstr_args cdecl)))) ->

  ws_cumul_ctx_pb_rel Cumul Σ (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl)))
      (subst_context (inds (inductive_mind ind.1) u (ind_bodies mdecl)) (context_assumptions (ind_params mdecl))
       (smash_context []
          (subst_instance u
             (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
                (cstr_args cdecl)))))
       (subst_context (inds (inductive_mind ind.1) u' (ind_bodies mdecl)) (context_assumptions (ind_params mdecl))
           ((smash_context []
          (subst_instance u'
             (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
                (cstr_args cdecl)))))).
Proof.
  intros * declc cu Ru cx.
  pose proof (on_declared_constructor declc) as [[onmind oib] [cs [? onc]]].
  pose proof (onc.(on_ctype_positive)) as cpos.
  rw onc.(cstr_eq) in cpos. unf_env.
  rw -it_mkProd_or_LetIn_app in cpos.
  eapply positive_cstr_it_mkProd_or_LetIn in cpos as [hpars _].
  rw smash_context_app_expand in hpars.
  eapply All_local_env_app_inv in hpars as [_hpars hargs].
  rw expand_lets_smash_context /= expand_lets_k_ctx_nil /= in hargs.
  eapply positive_cstr_closed_args_subst_arities in hargs; eauto.
  split.
  - rw !subst_instance_smash /ind_subst /= in hargs |- *.
    eapply hargs; eauto.
  - destruct hargs as [hargs hwf]. now rw !subst_instance_smash in hwf |- *.
  - eapply declc.
  - eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto; eapply declc.
  - rw -app_context_assoc. rw -(expand_lets_smash_context _ []).
    rw -smash_context_app_expand subst_instance_app_ctx subst_instance_smash.
    eapply wf_local_smash_end; eauto.
    rw -subst_instance_app_ctx app_context_assoc.
    now epose proof (on_constructor_inst declc _ cu) as [wfarpars _].
  - eapply smash_context_assumption_context. constructor.
  - now rw !(subst_instance_smash _ (expand_lets_ctx _ _)).
Qed.

Lemma red_subst_instance {cf:checker_flags} (Σ : global_env) (Γ : context) (u : Instance.t) (s t : term) :
  red Σ Γ s t ->
  red Σ (subst_instance u Γ) (subst_instance u s)
            (subst_instance u t).
Proof.
  intros H; apply clos_rt_rt1n in H.
  apply clos_rt1n_rt.
  induction H. constructor.
  eapply red1_subst_instance in r.
  econstructor 2. eapply r. auto.
Qed.

Lemma assumption_context_map f Γ :
  assumption_context Γ -> assumption_context (map_context f Γ).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma assumption_context_subst_instance u Γ :
  assumption_context Γ -> assumption_context (subst_instance u Γ).
Proof. apply assumption_context_map. Qed.

Section Betweenu.
  Context (start : nat) (k : nat).

  Definition betweenu_level (l : Level.t) :=
    match l with
    | Level.lvar n => (start <=? n) && (n <? start + k)%nat
    | _ => true
    end.

  Definition betweenu_level_expr (s : LevelExpr.t) :=
    betweenu_level (LevelExpr.get_level s).

  Definition betweenu_universe (u : Universe.t) :=
    LevelExprSet.for_all betweenu_level_expr u.

  Definition betweenu_sort (u : sort) :=
    match u with
    | sProp | sSProp => true
    | sType u => betweenu_universe u
    end.

  Definition betweenu_instance (u : Instance.t) :=
    forallb betweenu_universe u.

End Betweenu.

(** Universe-closed terms are unaffected by universe substitution. *)
Section UniverseClosedSubst.
  Lemma closedu_subst_instance_level_app u u' l
  : closedu_level #|u'| l -> subst_instance_level (u' ++ u) l = subst_instance_level u' l.
  Proof.
    destruct l; cbnr.
    intros Hn % Nat.ltb_lt.
    rw nth_error_app_lt //.
  Qed.

  Lemma closedu_subst_instance_level_expr_app u u' e
    : closedu_level_expr #|u'| e -> subst_instance_level_expr (u' ++ u) e = subst_instance_level_expr u' e.
  Proof.
    destruct e as [l b]; unfold subst_instance_level_expr; cbn.
    move/(@closedu_subst_instance_level_app u u' l) => -> //.
  Qed.

  Lemma closedu_subst_instance_universe_app u u' (e : Universe.t)
    : closedu_universe #|u'| e -> subst_instance (u' ++ u) e = subst_instance u' e.
  Proof.
    rw /subst_instance //= => hc.
    apply Universe.equal_exprsets => l.
    rw !In_subst_instance. firstorder. exists x; split => //.
    - rw closedu_subst_instance_level_expr_app in H0 => //.
      now move/LevelExprSet.for_all_spec: hc => /(_ x H).
    - exists x; split => //.
      rw closedu_subst_instance_level_expr_app //.
      now move/LevelExprSet.for_all_spec: hc => /(_ x H).
  Qed.

  Lemma closedu_subst_instance_level_lift u u' l
  : closedu_level #|u| l -> subst_instance_level (u' ++ u) (lift_level #|u'| l) = subst_instance_level u l.
  Proof.
    destruct l; cbnr.
    intros Hn % Nat.ltb_lt.
    rw nth_error_app_ge. lia.
    now have -> : #|u'| + n - #|u'| = n by lia.
  Qed.

  Abbreviation lift_level_expr n e := (lift_level n e.1, e.2).

  Lemma closedu_subst_instance_level_expr_lift u u' e
    : closedu_level_expr #|u| e -> subst_instance_level_expr (u' ++ u) (lift_level_expr #|u'| e) = subst_instance_level_expr u e.
  Proof.
    destruct e as [l b]; cbnr.
    move/closedu_subst_instance_level_lift => /(_ u').
    rw /subst_instance_level_expr //= => -> //.
  Qed.

  Lemma subst_instance_universe_eq i (u v : Universe.t) :
    (forall le, LevelExprSet.In le u -> LevelExprSet.Subset (subst_instance_level_expr i le) v) ->
    (forall le, LevelExprSet.In le v -> exists le', LevelExprSet.In le' u /\ LevelExprSet.In le (subst_instance_level_expr i le')) ->
    u@[i] = v.
  Proof.
    intros h h'.
    apply Universe.equal_exprsets => l.
    split.
    - move/In_subst_instance => -[] x' [] hin heq.
      eapply h; tea.
    - move/h' => -[] le' [] hin hs.
      apply In_subst_instance. exists le'. split => //.
  Qed.

  Lemma In_lift_universe le n u : LevelExprSet.In le (lift_universe n u) <->
    exists le', LevelExprSet.In le' u /\ le = lift_level_expr n le'.
  Proof.
    rw Universe.map_spec. firstorder.
  Qed.

  Lemma closedu_subst_instance_universe_lift u u' e
    : closedu_universe #|u| e -> subst_instance_universe (u' ++ u) (lift_universe #|u'| e) = subst_instance_universe u e.
  Proof.
    move/LevelExprSet.for_all_spec => hf.
    apply subst_instance_universe_eq.
    - move=> le /In_lift_universe -[] lel [] hin eq inl. subst le.
      rw closedu_subst_instance_level_expr_lift. now apply hf.
      move=> hin'; apply In_subst_instance. exists lel => //.
    - move=> le /In_subst_instance -[] x' [] hin.
      erewrite <- (closedu_subst_instance_level_expr_lift _ u'). 2:{ now apply hf. }
      destruct x'. cbn -[subst_instance_level_expr].
      exists (lift_level #|u'| t, n). split => //.
      eapply Universe.map_spec. eexists; split; trea. unfold on_fst. cbn. reflexivity.
  Qed.

  Lemma closedu_subst_instance_app u u' t
    : closedu_instance #|u'| t -> subst_instance (u' ++ u) t = subst_instance u' t.
  Proof.
    intro H. eapply forallb_All in H. apply All_map_eq.
    solve_all. now eapply closedu_subst_instance_universe_app.
  Qed.

  Lemma closedu_subst_instance_lift u u' t
    : closedu_instance #|u| t -> subst_instance (u' ++ u) (lift_instance #|u'| t) = subst_instance u t.
  Proof.
    intro H. eapply forallb_All in H.
    rw /subst_instance /subst_instance_instance /lift_instance map_map_compose. apply All_map_eq.
    solve_all. now eapply closedu_subst_instance_universe_lift.
  Qed.

End UniverseClosedSubst.

Lemma level_var_instance_length n i : #|level_var_instance n i| = #|i|.
Proof. rw /level_var_instance; len. Qed.
#[global]
Hint Rewrite level_var_instance_length : len.

Lemma lift_instance_length n i : #|lift_instance n i| = #|i|.
Proof. now rw /lift_instance; len. Qed.
#[global]
Hint Rewrite lift_instance_length : len.

Lemma variance_universes_insts {cf} {Σ mdecl l} :
  on_variance Σ (ind_universes mdecl) (Some l) ->
  ∑ v i i',
  [× variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i'),
    match ind_universes mdecl with
    | Monomorphic_ctx => False
    | Polymorphic_ctx (inst, cstrs) =>
      let cstrs := UnivConstraintSet.union (UnivConstraintSet.union cstrs (lift_constraints #|i| cstrs)) (variance_cstrs l i i')
      in v = Polymorphic_ctx (inst ++ inst, cstrs)
    end,
    consistent_instance_ext (Σ.1, v) (ind_universes mdecl) i,
    consistent_instance_ext (Σ.1, v) (ind_universes mdecl) i',
    #|i| = #|i'|, #|l| = #|i|,
    i' = abstract_instance (ind_universes mdecl),
    closedu_instance #|i'| i' &
    i = lift_instance #|i'| i'].
Proof.
  unfold variance_universes.
  destruct (ind_universes mdecl); simpl => //.
  destruct cst as [inst cstrs].
  intros [univs' [i [i' []]]].
  let e := match goal with H : Some _ = Some _ |- _ => H end in
  noconf e.
  do 3 eexists; split. trea. all:eauto. 1-3:len.
  repeat match goal with H : _ |- _ => progress len in H end.
  len.
  rw /closedu_instance /level_var_instance forallb_map forallb_mapi //.
  intros i hi. simpl. now elim: Nat.ltb_spec.
  now len.
Qed.

Lemma consistent_instance_poly_length {cf} {Σ} {wfΣ : wf Σ} {inst cstrs u} :
  consistent_instance_ext Σ (Polymorphic_ctx (inst, cstrs)) u ->
  #|u| = #|inst|.
Proof.
  rw /consistent_instance_ext /consistent_instance.
  intuition auto.
Qed.

Lemma consistent_instance_valid {cf} {Σ} {wfΣ : wf Σ} {inst cstrs u} :
  consistent_instance_ext Σ (Polymorphic_ctx (inst, cstrs)) u ->
  check_univs ->
  forall v, satisfies v (global_ext_constraints Σ) -> satisfies v (subst_instance_cstrs u cstrs).
Proof. rw /consistent_instance_ext /=; intros [_ [_ v]] cu.
    red in v. now rw cu in v.
Qed.

Definition closedu_cstr k (cstr : UnivConstraint.t) :=
  let '(l1, p, l2) := cstr in
  closedu_universe k l1 && closedu_universe k l2.

Definition closedu_cstrs k (cstrs : UCS.t) :=
  UCS.For_all (closedu_cstr k) cstrs.

Lemma LSet_in_poly_bounded l inst cstrs : LevelSet.In l (levels_of_udecl (Polymorphic_ctx (inst, cstrs))) ->
  closedu_level #|inst| l.
Proof.
  simpl.
  rw /mapi.
  change (#|inst|) with (0 + #|inst|).
  generalize 0.
  induction inst; simpl; auto.
  intros n emp. now eapply LevelSetFact.empty_iff in emp.
  intros n Hl.
  rewrite -> LS.add_spec in Hl.
  destruct Hl. subst.  simpl. apply Nat.ltb_lt; lia.
  specialize (IHinst _ H). now rw Nat.add_succ_r.
Qed.

Lemma bounded_poly_levels ls inst cstrs : LevelSet.Subset (Universe.levels ls) (levels_of_udecl (Polymorphic_ctx (inst, cstrs))) ->
  closedu_universe #|inst| ls.
Proof.
  move=> /subset_levels hs.
  apply LevelExprSet.for_all_spec; tc.
  move=> [l k] /hs. apply LSet_in_poly_bounded.
Qed.

Lemma LSet_in_global_bounded {cf:checker_flags} {Σ : global_env} {l} k :
  wf Σ -> LevelSet.In l (global_levels Σ) ->
  closedu_level k l.
Proof.
  simpl.
  intros wf. eapply not_var_global_levels in wf.
  intros hin. specialize (wf _ hin). simpl in wf.
  destruct l; simpl in *; congruence.
Qed.

Lemma bounded_global_levels {cf:checker_flags} {Σ : global_env} {ls} k :
  wf Σ -> LevelSet.Subset (Universe.levels ls) (global_levels Σ) ->
  closedu_universe k ls.
Proof.
  move=> wf /subset_levels hs.
  apply LevelExprSet.for_all_spec; tc.
  move=> [l k'] /hs. now apply LSet_in_global_bounded.
Qed.

Lemma bounded_poly_global_levels {cf:checker_flags} {Σ : global_env} {ls} inst cstrs :
  wf Σ -> LevelSet.Subset (Universe.levels ls) (LevelSet.union (levels_of_udecl (Polymorphic_ctx (inst, cstrs))) (global_levels Σ)) ->
  closedu_universe #|inst| ls.
Proof.
  move=> wf.
  move=> /subset_levels hs.
  apply LevelExprSet.for_all_spec; tc.
  move=> [l k'] /hs.
  rw LevelSet.union_spec => -[H|H].
  - rw /closedu_level_expr //=.
    eapply LSet_in_poly_bounded; tea.
  - eapply LSet_in_global_bounded; tea.
Qed.

Lemma on_udecl_prop_poly_bounded {cf:checker_flags} Σ inst cstrs :
  wf Σ ->
  on_udecl_prop Σ (Polymorphic_ctx (inst, cstrs)) ->
  closedu_cstrs #|inst| cstrs.
Proof.
  rw /on_udecl_prop.
  intros wfΣ nlevs.
  red.
  rw /closedu_cstrs.
  intros x incstrs.
  specialize (nlevs x incstrs).
  destruct x as [[l1 p] l2].
  destruct nlevs.
  unfold closedu_cstr. toProp;
  eapply bounded_poly_global_levels; tea.
Qed.

Lemma closedu_subst_instance_cstrs_app u u' cstrs :
  closedu_cstrs #|u| cstrs ->
  UCS.Equal (subst_instance_cstrs (u ++ u') cstrs) (subst_instance_cstrs u cstrs).
Proof.
  intros clcstra.
  intros c.
  rw !In_subst_instance_cstrs.
  firstorder eauto.
  subst c; exists x; split; auto.
  specialize (clcstra _ H0).
  simpl in *.
  destruct x as [[l c] r]; rw /subst_instance_univ_cstr; simpl.
  move/andb_and: clcstra => [cll clr].
  rw !closedu_subst_instance_universe_app //.

  subst c; exists x; split; auto.
  specialize (clcstra _ H0).
  simpl in *.
  destruct x as [[l c] r]; rw /subst_instance_univ_cstr; simpl.
  move/andb_and: clcstra => [cll clr].
  rw !closedu_subst_instance_universe_app //.
Qed.


Lemma In_lift_constraints u c ctrs :
  UCS.In c (lift_constraints u ctrs)
  <-> exists c', c = lift_constraint u c' /\ UCS.In c' ctrs.
Proof.
  unfold lift_constraints.
  rw UCS.fold_spec.
  transitivity (UCS.In c UCS.empty \/
                exists c', c = lift_constraint u c'
                      /\ In c' (UCS.elements ctrs)).
  - generalize (UCS.elements ctrs), UCS.empty.
    induction l; cbn.
    + firstorder.
    + intros t. etransitivity. 1: eapply IHl.
      split; intros [HH|HH].
      * destruct a as [[l1 a] l2]. apply UCS.add_spec in HH.
        destruct HH as [HH|HH]. 2: now left.
        right; eexists. split; [|left; reflexivity]. assumption.
      * destruct HH as [c' ?]. right; exists c'; intuition auto.
      * left. destruct a as [[l1 a] l2]. apply UCS.add_spec.
        now right.
      * destruct HH as [c' [HH1 [?|?]]]; subst.
        -- left. destruct c' as [[l1 c'] l2];
           apply UCS.add_spec; now left.
        -- right. exists c'. intuition.
  - rw UnivConstraintSetFact.empty_iff.
    transitivity (exists c', c = lift_constraint u c'
                        /\ In c' (UCS.elements ctrs)).
    1: intuition.
    apply iff_ex; intro. apply and_iff_compat_l. symmetry.
    etransitivity. 1: symmetry; eapply UCS.elements_spec1.
    etransitivity. 1: eapply SetoidList.InA_alt.
    split; intro; eauto.
    now destruct H as [? [[] ?]].
Qed.


Lemma closedu_subst_instance_cstrs_lift u u' cstrs :
  closedu_cstrs #|u'| cstrs ->
  UCS.Equal (subst_instance_cstrs (u ++ u') (lift_constraints #|u| cstrs)) (subst_instance_cstrs u' cstrs).
Proof.
  intros clcstra.
  intros c.
  rw !In_subst_instance_cstrs.
  firstorder eauto.
  - subst c.
    rewrite -> In_lift_constraints in H0.
    destruct H0 as [c' [-> inc']].
    exists c'. split; auto.
    specialize (clcstra _ inc').
    simpl in *.
    destruct c' as [[l c] r]; rw /subst_instance_univ_cstr; simpl.
    move/andb_and: clcstra => [cll clr].
    rw ![_@[_ ++ _]]closedu_subst_instance_universe_lift //.

  - subst c.
    exists (lift_constraint #|u| x).
    rewrite -> In_lift_constraints.
    pcuicfo eauto.
    specialize (clcstra _ H0).
    simpl in *.
    destruct x as [[l c] r]; rw /subst_instance_univ_cstr; simpl.
    move/andb_and: clcstra => [cll clr].
    rw ![_@[_ ++ _]]closedu_subst_instance_universe_lift //.
Qed.

Lemma subst_instance_cstrs_add u x c :
  UCS.Equal (subst_instance_cstrs u (UnivConstraintSet.add x c))
    (UnivConstraintSet.add (subst_instance_univ_cstr u x) (subst_instance_cstrs u c)).
Proof.
  intros cc.
  rw UnivConstraintSetFact.add_iff.
  rw !In_subst_instance_cstrs.
  intuition auto.
  destruct H as [c' [-> inc']].
  rewrite -> UnivConstraintSetFact.add_iff in inc'.
  destruct inc'; subst; intuition auto.
  right. eexists; intuition eauto.
  subst.
  exists x; intuition eauto.
  now rw UnivConstraintSetFact.add_iff.
  destruct H0 as [c' [-> ?]].
  eexists c'; split; firstorder eauto.
  now rw UnivConstraintSetFact.add_iff.
Qed.

Lemma subst_instance_variance_cstrs l u i i' :
  UCS.Equal (subst_instance_cstrs u (variance_cstrs l i i'))
    (variance_cstrs l (subst_instance u i) (subst_instance u i')).
Proof.
  induction l in u, i, i' |- *; simpl; auto;
  destruct i, i'; simpl => //.
  destruct a.
  - apply (IHl u i i').
  - rw -IHl.
    now rw subst_instance_cstrs_add.
  - rw -IHl.
    now rw subst_instance_cstrs_add.
Qed.

Lemma is_closed_subst_inst Γ u : is_closed_context Γ@[u] = is_closed_context Γ.
Proof.
  rw -(app_context_nil_l Γ@[u]).
  rw is_closed_context_subst_instance app_context_nil_l //.
Qed.

(** Morally, if variance_universes l = v i i' and cmp_universe_instance_variance l u u' then
  i and i' can be substituted respectively by u and u'.
    The hard part is to show that (Σ.1, v) can also be turned into Σ by instanciating
  i and i' by u and u'.
*)

Lemma ws_cumul_pb_inst_variance {cf} {le} {Σ} {wfΣ : wf Σ} {mdecl l v i i' u u' Γ} :
  on_udecl_prop Σ (ind_universes mdecl) ->
  on_variance Σ (ind_universes mdecl) (Some l) ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_universe_instance_variance (compare_universe Σ) Cumul l u u' ->
  forall t t',
  (Σ.1, v) ;;; Γ@[i] ⊢ t@[i] ≤[le] t'@[i'] ->
  Σ ;;; Γ@[u] ⊢ t@[u] ≤[le] t'@[u'].
Proof.
  intros onu onv vari cu cu' Ru t t'.
  intros cum.
  destruct Σ as [Σ univs].
  pose proof (variance_universes_insts onv) as (v' & ui & ui' & [hv cstrs cui cui' len0 len1 eqi']).
  rw vari in hv; noconf hv.
  subst i.
  pose proof (consistent_instance_length cu).
  pose proof (consistent_instance_length cu').
  have he : #|abstract_instance (ind_universes mdecl)| = #|i'|.
  { len. subst i'. len. }
  rw he in H H0.
  rw -H0 in cum.
  assert (subst_instance (u' ++ u) (lift_instance #|u'| i') = u) as subsu.
  { rw closedu_subst_instance_lift //.
    now rw H. rw eqi'.
    erewrite subst_instance_id_mdecl => //. eauto. }
  assert (subst_instance (u' ++ u) i' = u') as subsu'.
  { rw closedu_subst_instance_app //.
    rw H0 //. rw eqi' //.
    erewrite subst_instance_id_mdecl => //. eauto. }
  eapply (subst_instance_ws_cumul_pb (Σ, v) _ (u' ++ u)) in cum; auto.
  rw !subst_instance_two in cum.
  rw subst_instance_two_context in cum.
  now rw subsu subsu' in cum.
  unfold valid_constraints. destruct check_univs eqn:checku => //.
  unfold valid_constraints0.
  intros v0 sat.
  rw satisfies_subst_instance_ctr //.
  simpl in sat.
  generalize sat.
  unfold global_ext_constraints.
  rw satisfies_union /= => [[satcstrs satglob]].
  rw satisfies_union. split; auto.
  2:{ rw -satisfies_subst_instance_ctr //.
      rw equal_subst_instance_cstrs_mono //.
      red; apply monomorphic_global_constraint; auto. }
  destruct (ind_universes mdecl) as [|[inst cstrs']].
  { simpl in vari => //. }
  cbn in cstrs. subst v; cbn.
  rw !satisfies_union. len.
  len in len1.
  intuition auto.
  - rw -satisfies_subst_instance_ctr //.
    assert(UnivConstraintSet.Equal (subst_instance_cstrs u' cstrs')
        (subst_instance_cstrs (u' ++ u) cstrs')) as <-.
    { rw closedu_subst_instance_cstrs_app //.
      rw (consistent_instance_poly_length cu').
      eapply on_udecl_prop_poly_bounded; eauto. }
    eapply consistent_instance_valid in cu'; eauto.
  - rw -satisfies_subst_instance_ctr // -H0.
    assert(UnivConstraintSet.Equal (subst_instance_cstrs u cstrs')
        (subst_instance_cstrs (u' ++ u) (lift_constraints #|u'| cstrs'))) as <-.
    { rw closedu_subst_instance_cstrs_lift //.
      rw H -H0 (consistent_instance_poly_length cu').
      eapply on_udecl_prop_poly_bounded; eauto. }
    eapply consistent_instance_valid in cu; eauto.
  - rw -satisfies_subst_instance_ctr //.
    rw subst_instance_variance_cstrs //.
    rw -H0 subsu subsu'.
    assert (#|u| = #|u'|) as lenu by lia.
    assert (#|l| = #|u|) as lenlu. now rw len1 H.
    clear -checku Ru sat lenu lenlu.
    induction l in u, u', Ru, lenu, lenlu |- *. simpl in *. destruct u, u';
    intro; rw UnivConstraintSetFact.empty_iff //.
    destruct u, u' => //; simpl in *.
    depelim Ru. rename H into Ra.
    specialize (IHl u u' Ru). do 2 forward IHl by lia.
    destruct a => //; intros x; rw UnivConstraintSetFact.add_iff;
    intros [<-|inx]; auto.
    + do 3 red in Ra. rw checku in Ra;
      specialize (Ra _ sat); simpl in Ra.
      constructor. lia.
    + do 3 red in Ra. rw checku in Ra.
      specialize  (Ra _ sat).
      now constructor.
Qed.

Lemma All2_fold_inst {cf} {le} {Σ} {wfΣ : wf Σ} mdecl l v i i' u u' Γ' Γ :
  on_udecl_prop Σ (ind_universes mdecl) ->
  on_variance Σ (ind_universes mdecl) (Some l) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  cmp_universe_instance_variance (compare_universe Σ) Cumul l u u' ->
  ws_cumul_ctx_pb_rel le (Σ.1, v) (subst_instance i Γ') (subst_instance i Γ) (subst_instance i' Γ) ->
  ws_cumul_ctx_pb_rel le Σ (subst_instance u Γ') (subst_instance u Γ) (subst_instance u' Γ).
Proof.
  unfold cumul_ctx_rel.
  intros onu onv cu cu' vari Ru.
  induction Γ as [|[na [b|] ty] tl]; simpl.
  - constructor. destruct X.
    now rw !is_closed_subst_inst in i0 *.
    constructor.
  - intros H; depelim H.
    econstructor; auto.
    now rw !is_closed_subst_inst in i0 *.
    depelim a. simpl.
    rw -subst_instance_app_ctx in a, a0. simpl in a0 |- *.
    depelim a0.
    constructor; auto. apply IHtl; auto.
    red. split. 2:apply a. auto. constructor; try reflexivity.
    rw -subst_instance_app_ctx.
    eapply ws_cumul_pb_inst_variance; eauto.
    rw -subst_instance_app_ctx.
    cbn.
    eapply ws_cumul_pb_inst_variance; eauto.
  - intros H; depelim H; simpl in *. depelim a.
    constructor; auto.
    rw !is_closed_subst_inst // in i0 *.
    constructor; auto.
    now apply IHtl.
    rw -subst_instance_app_ctx in a0.
    rw -subst_instance_app_ctx.
    rw /map_decl /= in a0 *.
    depelim a0; constructor; eauto using ws_cumul_pb_inst_variance.
Qed.

Lemma forallb_closed_upwards k k' s :
  forallb (closedn k) s ->
  k <= k' ->
  forallb (closedn k') s.
Proof.
  intros H Hk.
  eapply All_forallb.
  eapply forallb_All in H. solve_all.
  eapply closed_upwards; eauto.
Qed.

Lemma subst_context_subst_context s k s' Γ :
  subst_context s k (subst_context s' 0 Γ) =
  subst_context (map (subst s k) s') 0 (subst_context s (k + #|s'|) Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto;
    rw !subst_context_snoc /= /subst_decl /map_decl /=; f_equal;
    auto; f_equal; len;
  rw distr_subst_rec; lia_f_equal.
Qed.

Lemma subst_context_subst_context_comm s k k' s' Γ :
  k' = k + #|s| ->
  subst_context s k (subst_context s' k' Γ) =
  subst_context s' k (subst_context (map (lift0 #|s'|) s) k Γ).
Proof.
  intros ->.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto;
    rw !subst_context_snoc /= /subst_decl /map_decl /=; f_equal;
    auto; f_equal; len;
    now rw Nat.add_assoc -subst_app_simpl subst_app_decomp.
Qed.

(* Lemma All2_fold_impl' (P Q : context -> context -> term -> term -> Type)
  (par par' : context) :
  All2_fold P par par' ->
  (forall (par0 par'0 : context) (o : option (term * term)) (x y : term),
  P par0 par'0 o x y -> Q par0 par'0 o x y) ->
  All2_fold Q par par'.
Proof.
  intros H HP; induction H; constructor; auto.
Qed. *)

Lemma map_map_subst_expand_lets (s : list term) (Γ : context) l k :
  context_assumptions Γ = #|s| ->
  map (subst (map (subst0 s) (extended_subst Γ 0)) k) l = map (subst s k ∘ expand_lets_k Γ k) l.
Proof. move=> ca; apply map_ext => x; apply map_subst_expand_lets_k => //. Qed.

#[global]
Hint Rewrite closedn_subst_instance : pcuic.

Lemma subst_conv_closed {le} {cf} {Σ} {wfΣ : wf Σ} {Γ Γ0 Γ1 Δ : context} {s s' : list term} {T U : term} :
  subslet Σ Γ s Γ0 ->
  subslet Σ Γ s' Γ1 ->
  #|s| = #|s'| ->
  closedn #|Δ| T ->
  closedn #|Δ| U ->
  Σ;;; Γ ,,, Γ0 ,,, Δ ⊢ T ≤[le] U ->
  Σ;;; Γ ,,, subst_context s 0 Δ ⊢ subst s #|Δ| T ≤[le] subst s' #|Δ| U.
Proof.
  intros subs subs' eqs clT clU.
  intros cum.
  pose proof (substitution_ws_cumul_pb (s:=s) subs cum).
  transitivity (subst s #|Δ| U) => //.
  clear X.
  rw !subst_closedn //.
  eapply ws_cumul_pb_refl.
  eapply is_closed_subst_context. eauto with fvs.
  now eapply subslet_open in subs.
  now rw (subslet_length subs).
  relativize U.
  instantiate (1 := subst s #|Δ| U).
  eapply is_open_term_subst; eauto with fvs.
  now eapply subslet_open in subs.
  now rw (subslet_length subs).
  rw !subst_closedn //.
Qed.

Lemma subst_instance_expand_lets u Γ t :
  subst_instance u (expand_lets Γ t) =
  expand_lets (subst_instance u Γ) (subst_instance u t).
Proof.
  rw /expand_lets /expand_lets_k.
  rw subst_instance_subst.
  rw subst_instance_extended_subst.
  f_equal.
  rw subst_instance_lift. len; f_equal.
Qed.

#[global]
Hint Rewrite subst_instance_expand_lets closedn_subst_instance : substu.

Lemma subst_instance_expand_lets_ctx u Γ Δ :
  subst_instance u (expand_lets_ctx Γ Δ) =
  expand_lets_ctx (subst_instance u Γ) (subst_instance u Δ).
Proof.
  rw /expand_lets_ctx /expand_lets_k_ctx.
  rw !subst_instance_subst_context !subst_instance_lift_context; len.
  now rw -subst_instance_extended_subst.
Qed.

Lemma cumul_ctx_relSpec_Algo {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'}
  (c : cumul_ctx_rel cumulSpec0 Σ Γ Δ Δ') :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  ws_cumul_ctx_pb_rel Cumul Σ Γ Δ Δ'.
Proof.
  intros wf wf'.
  eapply ws_cumul_ctx_pb_rel_app.
  apply into_ws_cumul_ctx_pb; eauto with fvs.
  apply All2_fold_app; auto. reflexivity.
  induction c; try solve[constructor; auto].
  move: wf; rw /= on_free_vars_ctx_snoc => /andP[] h0 h1.
  move: wf'; rw /= on_free_vars_ctx_snoc => /andP[] h2 h3.
  destruct p; constructor; inv_on_free_vars; auto.
  - eapply cumulSpec_cumulAlgo_curry in eqt; fvs.
    constructor; auto. now eapply ws_cumul_pb_forget in eqt.
    len. rw (All2_fold_length c). now len in h3.
  - eapply cumulSpec_cumulAlgo_curry in eqt; eauto.
    eapply convSpec_convAlgo_curry in eqb; eauto; fvs.
    constructor; auto.
    now apply ws_cumul_pb_forget in eqb.
    now apply ws_cumul_pb_forget in eqt.
    len. rw (All2_fold_length c) //. now len in H.
    len. rw (All2_fold_length c) //. now len in H0.
Qed.

Lemma into_ws_cumul_ctx_pb_rel {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'}
  (c : cumul_ctx_rel cumulAlgo_gen Σ Γ Δ Δ') :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  ws_cumul_ctx_pb_rel Cumul Σ Γ Δ Δ'.
Proof.
  intros wf wf'.
  eapply ws_cumul_ctx_pb_rel_app.
  apply into_ws_cumul_ctx_pb; eauto with fvs.
  apply All2_fold_app; auto. reflexivity.
Qed.

Lemma is_closed_context_weaken Γ Δ :
  is_closed_context Γ ->
  is_closed_context Δ ->
  is_closed_context (Γ ,,, Δ).
Proof.
  rw on_free_vars_ctx_app => -> /=.
  eapply on_free_vars_ctx_impl => //.
Qed.

Lemma cmp_global_instance_ind_inv {cf} {Σ} {wfΣ : wf Σ} cmp_universe pb ind mdecl idecl napp u u' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  declared_inductive Σ ind mdecl idecl ->
  cmp_global_instance Σ cmp_universe pb (IndRef ind) napp u u' ->
  ((context_assumptions (ind_indices idecl) + context_assumptions (ind_params mdecl) <= napp ×
    ∑ l, ind_variance mdecl = Some l ×
      cmp_universe_instance_variance cmp_universe pb l u u') +
  cmp_universe_instance (cmp_universe Conv) u u')%type.
Proof.
  intros Hsub decli.
  destruct (on_declared_inductive decli) as [onmind oib].
  unshelve epose proof (decli' := declared_inductive_to_gen decli); eauto.
  unfold cmp_global_instance, cmp_global_instance_gen, global_variance.
  rw (declared_inductive_lookup_gen decli').
  rw oib.(ind_arity_eq).
  rw !destArity_it_mkProd_or_LetIn. simpl.
  rw app_context_nil_l context_assumptions_app.
  elim: leb_spec_Set => // comp. 2: now right.
  destruct ind_variance eqn:indv => //. 2: now right.
  move/cmp_opt_variance_var_dec => [|H]. 1: now right.
  left.
  now repeat eexists.
Qed.

Lemma inductive_cumulative_indices {cf} {Σ} {wfΣ : wf Σ} :
  forall {ind mdecl idecl u u' napp},
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_ind_universes Σ ind napp u u' ->
  forall Γ pars pars' parsubst parsubst',
  spine_subst Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  spine_subst Σ Γ pars' parsubst' (subst_instance u' (ind_params mdecl)) ->
  ws_cumul_pb_terms Σ Γ pars pars' ->
  let indctx := subst_instance u idecl.(ind_indices) in
  let indctx' := subst_instance u' idecl.(ind_indices) in
  let pindctx := subst_context parsubst 0 indctx in
  let pindctx' := subst_context parsubst' 0 indctx' in
  ws_cumul_ctx_pb_rel Cumul Σ Γ (smash_context [] pindctx) (smash_context [] pindctx').
Proof.
  intros * decli.
  destruct (on_declared_inductive decli) as [onmind oib].
  intros cu cu' Ru Γ * spu spu' cpars *.
  unshelve epose proof (decli' := declared_inductive_to_gen decli); eauto.
  assert (onu : on_udecl_prop Σ (ind_universes mdecl)).
  { eapply (weaken_lookup_on_global_env' _ _ _ wfΣ (proj1 decli')). }
  unfold cmp_global_instance, cmp_global_instance_gen.
  assert (closed_ctx
    (subst_instance u
      (PCUICEnvironment.ind_params mdecl))) as clpu.
  { eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto.
    destruct decli; eauto. }
  assert (closed_ctx
  (subst_instance u'
    (PCUICEnvironment.ind_params mdecl)))  as clpu'.
  {  eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto.
     destruct decli; eauto. }
  assert (closed_ctx
    (subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))) as clspu.
  { rw subst_instance_smash. now eapply closedn_smash_context. }
  assert (wf_local Σ
  (smash_context []
     (subst_instance u (PCUICEnvironment.ind_params mdecl)) ,,,
   smash_context []
     (subst_instance u
        (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
           (ind_indices idecl))))).
  { pose proof (on_minductive_wf_params_indices_inst decli _ cu) as wf.
    eapply wf_local_smash_context in wf; auto.
    rw subst_instance_app_ctx smash_context_app_expand in wf.
    rw expand_lets_smash_context expand_lets_k_ctx_nil in wf.
    now rw subst_instance_expand_lets_ctx. }
  have clu' : is_closed_context (Γ,,, (ind_params mdecl)@[u']).
  { rw -is_closed_ctx_closed.
    rw closedn_ctx_app /=.
    rw (closed_wf_local _ (spine_dom_wf _ _ _ _ _ spu)) /=.
    eapply closedn_ctx_upwards; tea. lia. }
  eapply cmp_global_instance_ind_inv in Ru as [(comp & l & indv & Ru) | Ru]; tea; tc.
  { pose proof (oib.(onIndices)) as respv.
    rw indv in respv.
    simpl in respv.
    unfold ind_respects_variance in respv.
    destruct variance_universes as [[[v i] i']|] eqn:vu => //.
    pose proof (onVariance onmind) as onvari.
    rw indv in onvari.
    eapply cumul_ctx_relSpec_Algo in respv.
    2:{ move/wf_local_closed_context: X.
        rw - !(subst_instance_smash _ _ []).
        rw - !subst_instance_app_ctx !is_closed_subst_inst //.
        now rw expand_lets_smash_context. }
    2:{ move/wf_local_closed_context: X.
        rw - !(subst_instance_smash _ _ []).
        rw - !subst_instance_app_ctx !is_closed_context_subst_instance !is_closed_subst_inst //.
        rw !on_free_vars_ctx_app is_closed_subst_inst.
        rw expand_lets_smash_context /= //. len. }
    eapply All2_fold_inst in respv.
    7:eauto. all:eauto. move: respv.
    rw !expand_lets_smash_context.
    autorewrite with pcuic.
    rw !subst_instance_smash /= => args. cbn in args.
    eapply (weaken_ws_cumul_ctx_pb_rel (Γ := Γ)) in args => //; eauto with fvs.
    2:{ eapply wf_local_closed_context. apply spu. }
    pose proof (spine_subst_smash spu) as sspu.
    pose proof (spine_subst_smash spu') as sspu'.
    eapply (substitution_ws_cumul_ctx_pb_subst_conv (Γ := Γ) (Γ'' := []) (s := List.rev pars) (s' := List.rev pars')) in args.
    2:{ eapply All2_rev => //. }
    2:{ eapply subslet_untyped_subslet, sspu. }
    2:{ eapply subslet_untyped_subslet, sspu'. }
    2:{ eapply is_closed_context_smash_end => //. }
    move: args.
    rw subst_context_nil /= - !smash_context_subst /= subst_context_nil; len.
    rw !subst_instance_subst_context.
    rw !subst_instance_extended_subst.
    rw (subst_context_subst_context (List.rev pars)) /=; len.
    rw -(spine_subst_extended_subst spu).
    rw !subst_instance_lift_context. len.
    rw subst_context_lift_context_cancel.
    len. rw (context_subst_length2 spu); len; lia.
    rw (subst_context_subst_context (List.rev pars')) /=; len.
    rw -(spine_subst_extended_subst spu').
    len. rw subst_context_lift_context_cancel.
    len. rw (context_subst_length2 spu'); len; lia.
    now rw subst_context_nil. }
  simpl. intros.
  { rw /pindctx /pindctx' /indctx /indctx'.
    rw !(smash_context_subst []).
    eapply (substitution_ws_cumul_ctx_pb_subst_conv (Γ'' := [])); eauto.
    3:eapply subslet_untyped_subslet, spu.
    3:eapply subslet_untyped_subslet, spu'.
    2:{ eapply spine_subst_conv; eauto.
        eapply (weaken_ws_cumul_ctx_pb_rel (Γ' := [])).
        eapply spine_dom_wf in spu. eauto with fvs.
        eapply subst_instance_ws_cumul_ctx_pb_rel => //.
        rw app_context_nil_l //.
        rw closedn_subst_instance_context in clpu.
        now rw -is_closed_ctx_closed. }
    simpl.
    rw -(subst_instance_smash u _ []).
    rw -(subst_instance_smash u' _ []).
    eapply subst_instance_ws_cumul_ctx_pb_rel => //.
    rw -app_context_assoc.
    rw is_closed_context_weaken //.
    eapply spine_dom_wf in spu. eauto with fvs.
    rw -(is_closed_context_subst_instance _ _ u).
    rw -subst_instance_app_ctx.
    rw is_closed_subst_inst.
    eapply is_closed_context_smash_end.
    epose proof (declared_inductive_closed_pars_indices decli).
    now rw -is_closed_ctx_closed. }
Qed.

#[global] Hint Resolve declared_inductive_minductive : core.
#[global] Hint Resolve declared_constructor_inductive : core.

Lemma into_ws_cumul_pb_terms {cf} {Σ} {wfΣ : wf Σ} {Γ l l'} :
  All2 (convSpec Σ Γ) l l' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) l ->
  forallb (is_open_term Γ) l' ->
  ws_cumul_pb_terms Σ Γ l l'.
Proof.
  solve_all.
  eapply convSpec_convAlgo_curry in b0; tea.
Qed.

Lemma on_constructor_closed_indices {cf} {Σ} {wfΣ : wf Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (is_open_term (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) (cstr_indices cdecl).
Proof.
  intros.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  eapply ctx_inst_impl in X. 2: intros ??; apply unlift_TermTyp.
  now eapply ctx_inst_open_terms in X.
Qed.

Lemma positive_cstr_closed_indices' {cf} {Σ} {wfΣ : wf Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (closedn (context_assumptions (cstr_args cdecl) + context_assumptions (ind_params mdecl)))
    (map (expand_lets (ind_params mdecl ,,, cstr_args cdecl)) (cstr_indices cdecl)).
Proof.
  intros.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_ctype_positive)).
  rw onc.(cstr_eq) in X. unf_env.
  rw -it_mkProd_or_LetIn_app in X.
  eapply positive_cstr_it_mkProd_or_LetIn in X as [hpars hpos].
  rw app_context_nil_l in hpos.
  rw expand_lets_mkApps in hpos.
  unfold cstr_concl_head in hpos.
  have subsrel := expand_lets_tRel (#|ind_bodies mdecl| - S (inductive_ind i.1))
    (ind_params mdecl ,,, cstr_args cdecl). len in subsrel.
  rw (Nat.add_comm #|cstr_args cdecl|) Nat.add_assoc in subsrel.
  rw {}subsrel in hpos.
  depelim hpos; solve_discr.
  eapply All_map_inv in a.
  eapply All_app in a as [ _ a].
  eapply All_map; eapply (All_impl a); intros x; len.
Qed.

Lemma closedn_expand'' (Γ : context) x :
  closedn (context_assumptions Γ) (expand_lets Γ x) -> closedn #|Γ| x.
Proof.
  eapply (closedn_expand_lets 0).
Qed.

Lemma subst_context_expand_lets_k s Γ Δ :
  closed_ctx Γ ->
  subst_context s (context_assumptions Γ) (expand_lets_ctx Γ Δ) =
  expand_lets_ctx Γ (subst_context s #|Γ| Δ).
Proof.
  intros cl.
  rw /expand_lets_ctx /expand_lets_k_ctx.
  rw subst_subst_context.
  rw subst_context_lift_context_comm. len.
  f_equal.
  rw -subst_extended_subst.
  rw closed_ctx_subst //.
Qed.

(* For ease of application, avoiding to add a call to symmetry *)
Lemma ws_cumul_ctx_pb_wf_local {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ Γ' Δ :
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ Γ' ->
  Σ ⊢ Γ = Γ' ->
  wf_local Σ (Γ' ,,, Δ).
Proof.
  intros wf wf' e.
  eapply All_local_env_app => //.
  eapply All_local_env_app_inv in wf as [].
  eapply All_local_env_impl_ind; eauto.
  intros.
  rw -/(All_local_rel (lift_typing1 (typing Σ)) Γ' Γ0) /= in X, X0.
  apply lift_typing_impl with (1 := X0); intros ?? Hs.
  eapply closed_context_cumulativity; tea.
  eapply All_local_env_app=> //.
  eapply ws_cumul_ctx_pb_app_same; tea. 2:now symmetry.
  eapply All_local_env_app in X; tea.
  eauto with fvs.
Qed.

Lemma constructor_cumulative_indices {cf} {Σ} {wfΣ : wf Σ} :
  forall {c mdecl idecl cdecl u u' napp},
  declared_constructor Σ c mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_ind_universes Σ c.1 napp u u' ->
  forall Γ pars pars' parsubst parsubst',
  spine_subst Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  spine_subst Σ Γ pars' parsubst' (subst_instance u' (ind_params mdecl)) ->
  ws_cumul_pb_terms Σ Γ pars pars' ->
  let argctx :=
      (subst_context (ind_subst mdecl c.1 u) #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))
  in
  let argctx' :=
     (subst_context (ind_subst mdecl c.1 u') #|ind_params mdecl| (subst_instance u' (cstr_args cdecl)))
  in
  let pargctx := subst_context parsubst 0 argctx in
  let pargctx' := subst_context parsubst' 0 argctx' in
  ws_cumul_ctx_pb_rel Cumul Σ Γ (smash_context [] pargctx) (smash_context [] pargctx') *
  ws_cumul_pb_terms Σ (Γ ,,, smash_context [] pargctx)
    (map (subst parsubst (context_assumptions (cstr_args cdecl)))
      (map (expand_lets argctx) (map (subst_instance u) (cstr_indices cdecl))))
    (map (subst parsubst' (context_assumptions (cstr_args cdecl)))
      (map (expand_lets argctx') (map (subst_instance u') (cstr_indices cdecl)))).
Proof.
  intros * declc.
  destruct (on_declared_constructor declc) as [[onmind oib] [cs [hnth onc]]].
  intros cu cu' Ru Γ * spu spu' cpars *.
  unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
  assert (onu : on_udecl_prop Σ (ind_universes mdecl)).
  { eapply (weaken_lookup_on_global_env' _ _ _ wfΣ (proj1 (proj1 declc'))). }
  have clΓ : is_closed_context Γ.
  { apply spine_dom_wf in spu; eauto with fvs. }
  assert (closed_ctx
    (subst_instance u
      (PCUICEnvironment.ind_params mdecl))) as clpu.
  { eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto.
    destruct declc as [[] ?]; eauto.  }
  assert (closed_ctx
  (subst_instance u'
    (PCUICEnvironment.ind_params mdecl)))  as clpu'.
  { eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto.
    destruct declc as [[] ?]; eauto. }
  assert (closed_ctx
    (subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))) as clspu.
  { rw subst_instance_smash. now eapply closedn_smash_context. }
  have clΓparsu : is_closed_context (Γ ,,, (ind_params mdecl)@[u]).
  { apply spine_codom_wf in spu; eauto with fvs. }
  have clΓparsu' : is_closed_context (Γ ,,, (ind_params mdecl)@[u']).
  { apply spine_codom_wf in spu'; eauto with fvs. }
  eapply cmp_global_instance_ind_inv in Ru as [(comp & l & indv & Ru) | Ru]; eauto; tc.
  3: apply declc.p1.
  { pose proof (onc.(on_ctype_variance)) as respv.
    specialize (respv _ indv).
    simpl in respv.
    unfold cstr_respects_variance in respv.
    destruct variance_universes as [[[v i] i']|] eqn:vu => //.
    destruct respv as [args idx].
    pose proof (onVariance onmind) as onvari.
    rw indv in onvari.
    assert (wf_local Σ
    ((ind_arities mdecl)@[u],,, smash_context []
       (subst_instance u (PCUICEnvironment.ind_params mdecl)) ,,,
     smash_context []
       (subst_instance u
          (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
             (cstr_args cdecl))))).
    { pose proof (on_constructor_wf_args declc).
      eapply (wf_local_subst_instance _ _ _ u) in X; tea.
      2:{ apply (declared_inductive_wf_global_ext _ _ _ _ declc). }
      rw subst_instance_expand_lets_ctx.
      rw -(expand_lets_smash_context _ []).
      rw -app_context_assoc -(smash_context_app_expand []).
      eapply wf_local_smash_end.
      rw - !subst_instance_app_ctx app_context_assoc //. }
    apply cumul_ctx_relSpec_Algo in args; auto.
    2:{ move/wf_local_closed_context: X.
        rw - !(subst_instance_smash _ _ []).
        rw - !subst_instance_app_ctx !is_closed_subst_inst //.
        now rw expand_lets_smash_context. }
    2:{ move/wf_local_closed_context: X.
        rw - !(subst_instance_smash _ _ []).
        rw - !subst_instance_app_ctx !is_closed_context_subst_instance !is_closed_subst_inst //.
        rw !on_free_vars_ctx_app is_closed_subst_inst !on_free_vars_ctx_app.
        rw expand_lets_smash_context /= //. len. }
    split.
    { eapply All2_fold_inst in args. 7:eauto. all:eauto.
      rw !expand_lets_smash_context in args.
      autorewrite with pcuic in args.
      rw !subst_instance_smash /= in args.
      rw subst_instance_app_ctx in args.
      eapply positive_cstr_closed_args in args; eauto.
      2:{ rw indv. now simpl. }
      rw - !smash_context_subst !subst_context_nil in args.
      eapply (weaken_ws_cumul_ctx_pb_rel (Γ := Γ)) in args => //.
      pose proof (spine_subst_smash spu) as sspu.
      pose proof (spine_subst_smash spu') as sspu'.
      eapply (substitution_ws_cumul_ctx_pb_subst_conv (Γ := Γ) (Γ'' := []) (s := List.rev pars) (s' := List.rev pars')) in args.
      3:{ rw subst_instance_smash. eapply subslet_untyped_subslet, sspu. }
      3:{ eapply subslet_untyped_subslet, sspu'. }
      2:{ eapply All2_rev => //. }
      2:{ eapply spine_codom_wf in sspu'. eauto with fvs. }
      move: args.
      rw subst_context_nil /= - !smash_context_subst /= subst_context_nil; len.
      rw !subst_instance_subst_context.
      rw !subst_instance_extended_subst.
      rw (subst_context_subst_context (inds  _ u _)); len.
      rw (subst_context_subst_context (inds  _ u' _)); len.
      rw -(context_assumptions_subst_instance u).
      rw -(subst_extended_subst).
      rw (closed_ctx_subst (inds _ _ _)) //.
      rw (context_assumptions_subst_instance u).
      rw -(context_assumptions_subst_instance u').
      rw -(subst_extended_subst).
      rw (closed_ctx_subst (inds _ u' _)) //.
      rw (context_assumptions_subst_instance u').
      rw (subst_context_subst_context (List.rev pars)) /=; len.
      rw -(spine_subst_extended_subst spu).
      rw !subst_instance_lift_context. len.
      rw (subst_context_subst_context_comm (List.rev _)).
      len. rw (context_subst_length2 spu); len; lia.
      len. rw subst_context_lift_context_cancel.
      len. rw (context_subst_length2 spu); len; lia.
      rw (subst_context_subst_context (List.rev pars')) /=; len.
      rw -(spine_subst_extended_subst spu').
      rw (subst_context_subst_context_comm (List.rev pars')).
      len. rw (context_subst_length2 spu'); len; lia.
      len. rw subst_context_lift_context_cancel.
      len. rw (context_subst_length2 spu'); len; lia.
      now rw subst_context_nil.
    }
    { eapply into_ws_cumul_pb_terms in idx.
      2:{ eapply wf_local_closed_context in X. move: X.
          rw - !(subst_instance_smash _ _ []).
          rw - !subst_instance_app_ctx.
          rw !is_closed_subst_inst.
          rw smash_context_app_expand expand_lets_smash_context /=.
          rw expand_lets_k_ctx_nil // app_context_assoc //. }
      2:{ epose proof (positive_cstr_closed_indices declc) as cli.
          rw forallb_map. eapply All_map_inv in cli.
          solve_all.
          rw -is_open_term_closed. len.
          rw closedn_subst_instance.
          rw expand_lets_app.
          eapply closed_upwards; tea.
          erewrite (closedn_expand_lets_eq 0) => //. 2:lia.
          rw closedn_subst_instance_context in clpu => //. }
      2:{ epose proof (positive_cstr_closed_indices declc) as cli.
          rw forallb_map. eapply All_map_inv in cli.
          solve_all.
          rw -is_open_term_closed. len.
          rw closedn_subst_instance.
          rw expand_lets_app.
          eapply closed_upwards; tea.
          erewrite (closedn_expand_lets_eq 0) => //. 2:lia.
          rw closedn_subst_instance_context in clpu => //. }
      rw /pargctx /pargctx' (smash_context_subst []).
      rw (spine_subst_extended_subst spu) (spine_subst_extended_subst spu').
      rw !subst_context_map_subst_expand_lets_k.
      now rw -(context_subst_length2 spu); len.
      rw map_map_subst_expand_lets.
      now rw -(context_subst_length2 spu); len.
      rw -map_map_compose.
      rw map_map_subst_expand_lets.
      now rw -(context_subst_length2 spu'); len.
      simpl.
      rw -(map_map_compose _ _ _ _ (subst (List.rev pars') _)).
      evar (k : nat).
      replace (context_assumptions (cstr_args cdecl)) with k. subst k.
      unshelve eapply (ws_cumul_pb_terms_subst _ (spine_subst_smash spu) (spine_subst_smash spu')).
      { eapply is_closed_context_smash_end, is_closed_context_weaken.
        eapply spine_dom_wf in spu. eauto with fvs. eauto.
        now rw -is_closed_ctx_closed. }
      eapply All2_rev; eauto.
      2:{ subst k; len. }
      len. simpl.
      rw !map_map_compose; eapply All2_map.
      eapply All2_map_inv in idx.
      epose proof (positive_cstr_closed_indices' declc) as cli.
      eapply All_map_inv in cli.
      eapply All2_All in idx.
      eapply All_mix in idx; tea. clear cli.
      eapply All_All2; tea. solve_all.
      rename a into clx; rename b into cxy.
      rw -app_context_assoc. eapply weaken_ws_cumul_pb; eauto.

      (* eapply All_mix in idx; tea. clear cli. *)
      rw smash_context_app smash_context_acc in cxy.
      (* rename a into clx; rename b into cxy.
      rewrite -app_context_assoc. eapply weaken_ws_cumul_pb; eauto.
      rewrite subst_instance_app_ctx in cxy. *)
      eapply ws_cumul_pb_inst_variance in cxy. 7:eauto. all:eauto.
      (* rewrite !app_context_nil_l in X3. eapply X3 in cxy; clear X3; cycle 1. *)
      rw subst_instance_app_ctx in cxy.
      epose proof (subst_conv_closed (Γ := [])) as X3.
      rw !app_context_nil_l in X3. eapply X3 in cxy; clear X3; cycle 1.
      { eapply (subslet_inds (u:=u)); eauto. eapply declc.p1. }
      { eapply (subslet_inds (u:=u')); eauto. eapply declc.p1. }
      { now len. }
      { len. simpl. autorewrite with pcuic.
        now rw -context_assumptions_app in clx *. }
      { len. simpl. autorewrite with pcuic.
        now rw -context_assumptions_app in clx *. }
      len in cxy. autorewrite with substu in cxy.
      rw -context_assumptions_app in cxy.
      rw -{1}(context_assumptions_subst_instance u (_ ++ _)) in cxy.
      rw -{1}(context_assumptions_subst_instance u' (_ ++ _)) in cxy.
      rw -(expand_lets_subst_comm' _ _ 0) in cxy.
      { len. substu; cbn.
        rw -context_assumptions_app in clx.
        eapply closedn_expand'' in clx => //.
        now len in clx. }
      rw -(expand_lets_subst_comm' _ _ 0) in cxy.
      { len. substu; cbn.
        rw -context_assumptions_app in clx.
        eapply closedn_expand'' in clx => //.
        now len in clx. }
      rw !subst_instance_app_ctx in cxy.
      rw !subst_context_app in cxy. len in cxy.
      rw (closed_ctx_subst (inds _ _ _ )) // in cxy.
      rw (closed_ctx_subst (inds _ _ _ ) _ (subst_instance u (ind_params mdecl))) // in cxy.
      rw (closed_ctx_subst (inds _ _ _ ) _ (subst_instance u' (ind_params mdecl))) // in cxy.
      move: cxy.
      rw -/argctx -/argctx'.
      rw ![expand_lets _ _]expand_lets_k_app /= //.
      rw subst_instance_smash /= //. cbn.
      rw -/(expand_lets_k_ctx (ind_params mdecl) _ _).
      rw -/(expand_lets_ctx _ _).
      rw !subst_instance_subst_context !subst_instance_lift_context subst_instance_smash /=.
      rw subst_instance_extended_subst.
      rw -(context_assumptions_subst_instance u).
      rw -(subst_instance_length u).
      rw -/(expand_lets_k_ctx (ind_params mdecl)@[u] 0 (smash_context [] (cstr_args cdecl)@[u])).
      rw subst_context_expand_lets_k //.
      len. rw subst_context_smash_context; len. }
  }
  { simpl.
    assert (wf_local Σ Γ) by apply spu.
    epose proof (on_constructor_inst declc _ cu) as [wfargs spinst].
    split.
    { rw /pargctx /pargctx' /argctx /argctx'.
      rw !(smash_context_subst []).
      unshelve eapply (substitution_ws_cumul_ctx_pb_subst_conv (Γ'' := []) _ _ spu spu') => //.
      2:{ eapply spine_subst_conv; eauto.
          eapply subst_instance_ws_cumul_ctx_pb_rel; eauto with fvs.
          move: clΓparsu. now rw is_closed_context_subst_instance. }
      simpl.
      assert (subst_context (ind_subst mdecl c.1 u) 0 (subst_instance u (ind_params mdecl)) =
        (subst_instance u (ind_params mdecl))) as ispars.
      { rw closed_ctx_subst; eauto. }
      rw -ispars.
      rw -(subst_instance_length u (ind_params mdecl)).
      eapply (substitution_ws_cumul_ctx_pb_subst_conv (Γ := Γ)).
      3:{ eapply subslet_untyped_subslet, (weaken_subslet (Γ' := [])); eauto. eapply subslet_inds; eauto.
          eapply declc.p1. }
      3:{ eapply subslet_untyped_subslet, PCUICArities.weaken_subslet; eauto; eapply subslet_inds; eauto.
          eapply declc.p1. }
      3:{ simpl.
        rw !subst_instance_app_ctx in wfargs.
        apply is_closed_context_weaken => //.
        rw -app_context_assoc in wfargs.
        apply All_local_env_app_inv in wfargs as []; eauto with fvs.
        apply wf_local_closed_context in a; move: a.
        now rw !is_closed_subst_inst. }
      2:now eapply conv_inds.
      rw - !(subst_instance_smash _ _ []).
      eapply subst_instance_ws_cumul_ctx_pb_rel => //.
      rw - !app_context_assoc. eapply is_closed_context_weaken; auto.
      rw !app_context_assoc. apply is_closed_context_smash_end.
      rw -(is_closed_context_subst_instance _ (cstr_args cdecl) u).
      rw - !subst_instance_app_ctx. eauto with fvs. }
    { rw /pargctx.
      rw (smash_context_subst []).
      evar (i : nat).
      replace (context_assumptions (cstr_args cdecl)) with i. subst i.
      unshelve eapply (ws_cumul_pb_terms_subst _ spu spu'); eauto.
      eapply spine_subst_conv; eauto.
      eapply subst_instance_ws_cumul_ctx_pb_rel; eauto with fvs.
      move: clΓparsu. now rw is_closed_context_subst_instance.
      2:subst i; len; rw /argctx; len; reflexivity.
      rw /expand_lets /expand_lets_k.
      rw !map_map_compose.
      eapply All2_map.
      epose proof (positive_cstr_closed_indices' declc) as cli.
      eapply All_map_inv in cli. eapply All_All2; tea.
      cbn. intros.
      rw - !/(expand_lets_k _ _ _).
      have wfargctx :wf_local Σ (Γ,,, (ind_params mdecl)@[u],,, argctx).
      { rw -app_context_assoc. eapply weaken_wf_local => //.
        rw /argctx.
        exact (on_constructor_inst_wf_args declc _ cu). }
      have wfargctx' : wf_local Σ (Γ,,, (ind_params mdecl)@[u],,, argctx').
      { rw -app_context_assoc. eapply weaken_wf_local => //.
        rw /argctx'.
        epose proof (on_constructor_inst_wf_args declc _ cu').
        eapply ws_cumul_ctx_pb_wf_local; tea.
        apply (on_minductive_wf_params declc cu).
        eapply subst_instance_ws_cumul_ctx_pb.
        2:now symmetry.
        apply (on_minductive_wf_params declc cu'). }
      eapply (ws_cumul_pb_expand_lets_ws_cumul_ctx (pb:=Conv)) => //.
      apply into_ws_cumul_pb.
      { constructor.
        eapply eq_term_upto_univ_subst_instance; eauto; typeclasses eauto. }
      { eauto with fvs. }
      { rw /argctx.
        rw -is_open_term_closed. len.
        rw -context_assumptions_app in H.
        eapply closedn_expand'' in H => //.
        substu. eapply closed_upwards; tea. len. }
      { rw /argctx'.
        rw -is_open_term_closed. len.
        rw -context_assumptions_app in H.
        eapply closedn_expand'' in H => //.
        substu. eapply closed_upwards; tea. len. }
      rw /argctx /argctx'.
      eapply weaken_ws_cumul_ctx_pb_rel. eauto with fvs.
      rw /ind_subst.
      rw -(instantiate_inds declc cu).
      rw -(instantiate_inds declc cu').
      rw - !subst_instance_subst_context.
      eapply subst_instance_ws_cumul_ctx_pb_rel => //.
      epose proof (on_constructor_inst_wf_args declc _ cu).
      rw /ind_subst -(instantiate_inds declc cu) in X0.
      eapply wf_local_closed_context in X0; tea.
      rw -subst_instance_subst_context in X0.
      now rw is_closed_context_subst_instance in X0. }
  }
Qed.

Lemma assumption_context_expand_lets_ctx Γ Δ :
  assumption_context Δ ->
  assumption_context (expand_lets_ctx Γ Δ).
Proof.
  intros ass.
  rw /expand_lets_ctx /expand_lets_k_ctx.
  now do 2 apply assumption_context_fold.
Qed.

Lemma assumption_context_subst_context s k Γ :
  assumption_context Γ ->
  assumption_context (subst_context s k Γ).
Proof. apply assumption_context_fold. Qed.

Lemma assumption_context_lift_context s k Γ :
  assumption_context Γ ->
  assumption_context (lift_context s k Γ).
Proof. apply assumption_context_fold. Qed.

#[global]
Hint Resolve assumption_context_fold assumption_context_expand_lets_ctx
  smash_context_assumption_context assumption_context_nil assumption_context_subst_instance
  assumption_context_subst_context assumption_context_lift_context : pcuic.

Lemma subst_inds_smash_params {cf} {Σ} {wfΣ : wf Σ} {mdecl ind idecl u} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
    (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl))) =
    (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl))).
Proof.
  intros decli cu.
  rw closed_ctx_subst //.
  eapply closed_wf_local; eauto.
  rw subst_instance_smash /= //.
  eapply wf_local_smash_context; auto.
  destruct decli. eapply on_minductive_wf_params; pcuic.
Qed.

Lemma nth_error_expand_lets Γ Δ n :
  nth_error (expand_lets_ctx Γ Δ) n =
  option_map (map_decl (expand_lets_k Γ (#|Δ| - S n))) (nth_error Δ n).
Proof.
  rw /expand_lets_ctx /expand_lets_k_ctx nth_error_subst_context; len.
  relativize (context_assumptions Γ).
  erewrite (nth_error_lift_context_eq _ (smash_context [] Γ)).
  2:len; simpl; lia.
  simpl. destruct nth_error; simpl; auto.
  f_equal.
  rw /expand_lets_k /subst_decl /lift_decl compose_map_decl.
  eapply map_decl_ext => t.
  now len.
Qed.

Lemma subslet_projs_smash {cf:checker_flags} (Σ : global_env_ext) i mdecl idecl :
  forall (wfΣ : wf Σ.1)
  (Hdecl : declared_inductive Σ.1 i mdecl idecl),
  match ind_ctors idecl return Type with
  | [cdecl] =>
    on_projections mdecl (inductive_mind i) (inductive_ind i)
     idecl (ind_indices idecl) cdecl ->
     forall Γ t u,
     let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
     untyped_subslet Γ
     (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cdecl)) t)
     (lift_context 1 0 (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
        (context_assumptions (ind_params mdecl))
        (subst_instance u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cdecl))))))
  | _ => True
  end.
Proof.
  intros wfΣ Hdecl.
  destruct ind_ctors as [|cdecl []] eqn:hcdecl => //.
  intros onp. simpl. intros Γ t u.
  destruct onp.
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cstr_args cdecl)). lia.
  clear on_projs_all.
  induction (cstr_args cdecl) as [|[? [] ?] ?].
  - simpl. constructor.
  - simpl. apply IHc. now simpl in H.
  - simpl. rw smash_context_acc /=. simpl.
    rw /subst_decl {2}/map_decl /=.
    rw /expand_lets_ctx {1}/map_decl /= /expand_lets_k_ctx.
    rw !lift_context_snoc /= subst_context_snoc /=; len.
    rw !subst_context_snoc.
    rw lift_context_snoc.
    constructor. apply IHc. simpl in H. lia.
Qed.

Lemma projs_inst_0 ind n k : projs_inst ind n k (tRel 0) = projs ind n k.
Proof.
  induction k in n |- * => /= //.
  simpl. now f_equal.
Qed.

Lemma projection_cumulative_indices {cf} {Σ} {wfΣ : wf Σ} :
  forall {mdecl idecl cdecl p pdecl u u' },
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_ind_universes Σ p.(proj_ind) (ind_npars mdecl) u u' ->
  Σ ;;; projection_context p.(proj_ind) mdecl idecl u ⊢
    subst_instance u pdecl.(proj_type) ≤ subst_instance u' pdecl.(proj_type).
Proof.
  intros * declp onudecl cu cu' Ru.
  unshelve epose proof (declp' := declared_projection_to_gen declp); eauto.
  epose proof (declared_projection_constructor declp') as declc.
  unshelve epose proof (declc' := declared_constructor_from_gen declc); eauto.
  destruct (on_declared_constructor declc') as [_ [sort onc]].
  destruct declc'.
  unshelve epose proof (d' := declared_inductive_to_gen d); eauto.
  pose proof (declared_inductive_unique d' (let (x, _) := declp' in let (x, _) := x in x)).
  subst d'.
  epose proof (declared_projection_type_and_eq wfΣ declp).
  destruct (on_declared_projection declp).
  set (oib := declared_inductive_inv _ _ _ _) in p1. simpl in p1, X.
  destruct X as [[? ?] ?].
  destruct p1 as [[[H onps] onidx] onproj].
  simpl in *.
  destruct (ind_cunivs oib) as [|? []] eqn:cseq => //.
  destruct onc as []. noconf e1.
  simpl in *.
  destruct s as [idecl' [idecl'nth _ _ pty pty']].
  rw -pty.
  destruct declp' as [[[? ?] ?] ?]. red in H0.
  destruct p0 as [p0 _].
  epose proof (declared_projection_closed declp).
  pose proof (wf_projection_context _ _ declp cu) as wfpctx.
  eapply cmp_global_instance_ind_inv in Ru as [(comp & l & eqv & Ru) | Ru]; eauto; tc; revgoals.
  { eapply into_ws_cumul_pb; cycle 1.
    { eauto with fvs. }
    { rw -is_open_term_closed.
      all:rw closedn_subst_instance /projection_context; len; cbn; len.
      all:now rw -(declared_minductive_ind_npars declp). }
    { rw -is_open_term_closed.
      all:rw closedn_subst_instance /projection_context; len; cbn; len.
      all:now rw -(declared_minductive_ind_npars declp). }
    constructor. eapply eq_term_leq_term.
      eapply eq_term_upto_univ_subst_instance; eauto. all:tc. }
  simpl in Ru.
  pose proof (on_ctype_variance o _ eqv); eauto.
  red in X.
  destruct variance_universes as [[[udecl inst] inst']|] eqn:vu => //.
  destruct X as [onctx _]. simpl in onctx.
  assert (wf_local Σ
  ((ind_arities mdecl)@[u],,, smash_context []
      (subst_instance u (PCUICEnvironment.ind_params mdecl)) ,,,
    smash_context []
      (subst_instance u
        (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
            (cstr_args cdecl))))).
  { pose proof (on_constructor_wf_args declp).
    eapply (wf_local_subst_instance _ _ _ u) in X; tea.
    2:{ apply (declared_inductive_wf_global_ext _ _ _ _ declp). }
    rw subst_instance_expand_lets_ctx.
    rw -(expand_lets_smash_context _ []).
    rw -app_context_assoc -(smash_context_app_expand []).
    eapply wf_local_smash_end.
    rw - !subst_instance_app_ctx app_context_assoc //. }
  eapply cumul_ctx_relSpec_Algo in onctx; auto.
  2:{ move/wf_local_closed_context: X.
      rw - !(subst_instance_smash _ _ []).
      rw - !subst_instance_app_ctx !is_closed_subst_inst //.
      now rw expand_lets_smash_context. }
  2:{ move/wf_local_closed_context: X.
      rw - !(subst_instance_smash _ _ []).
      rw - !subst_instance_app_ctx !is_closed_context_subst_instance !is_closed_subst_inst //.
      rw !on_free_vars_ctx_app is_closed_subst_inst !on_free_vars_ctx_app.
      rw expand_lets_smash_context /= //. len. }
  eapply (All2_fold_inst  _ _ _ _ _ u u') in onctx; eauto.
  2:{ rw -eqv.
      eapply (onVariance p0). }
  rw subst_instance_app_ctx in onctx.
  epose proof (positive_cstr_closed_args declp cu) as hpos.
  rw eqv in hpos; simpl in hpos.
  forward hpos. 1: now right.
  rw - !(subst_instance_smash _ _ []) in hpos.
  rw - !(expand_lets_smash_context _ []) in hpos.
  apply hpos in onctx. clear hpos.
  destruct onctx as [onctx wfctx].
  eapply PCUICRedTypeIrrelevance.All2_fold_nth_ass in wfctx.
  2:{ rw nth_error_subst_context; len.
    simpl. rw nth_error_map nth_error_expand_lets.
    erewrite idecl'nth. simpl. reflexivity. }
  2:pcuic.
  move:wfctx => [decl' []].
  destruct idecl' as [na [b|] ty]; simpl => //.
  intros Hd [[] Hd'']; discriminate. simpl.
  rw nth_error_subst_context nth_error_map nth_error_expand_lets idecl'nth.
  rw !subst_instance_length !expand_lets_ctx_length !smash_context_length /=.
  simpl. move=> [= <-]. simpl.
  move=> [[Hd _] Hty].
  depelim Hty; simpl in *.
  move: eqt.
  rw subst_instance_smash. len. simpl.
  epose proof (subslet_projs_smash _ _ _ _ _ declp). rw e0 in X0.
  unfold projection_context.
  set (ind_decl := vass _ _).
  specialize (X0 onps (smash_context [] (subst_instance u (ind_params mdecl)) ,, ind_decl) (tRel 0) u).
  simpl in X0.
  eapply untyped_subslet_skipn in X0.
  rw skipn_lift_context in X0.
  move => Hty.
  eapply (weakening_ws_cumul_pb (Γ'' := [ind_decl])) in Hty; auto.
  simpl in Hty.
  eapply (untyped_substitution_ws_cumul_pb (Γ'' := [])) in Hty. 2:eapply X0.
  2:{ clear Hty.
      rw forallb_skipn //.
      clear. cbn. len. clear.
      induction (context_assumptions (cstr_args cdecl)); cbn => //. }
  2:{ clear Hty.
      rw -is_closed_ctx_closed.
      rw closedn_ctx_app /=; len.
      apply/andP; split. eapply closedn_smash_context.
      rw closedn_subst_instance_context.
      eapply (declared_inductive_closed_params declp).
      rw /ind_decl. cbn. rw closedn_mkApps /= //.
      relativize (context_assumptions _); [eapply closedn_to_extended_list|]. len. }
  move: Hty; rw subst_context_nil /=.
  rw length_skipn. len. simpl. len.
  rw /projection_type /=.
  fold (expand_lets_k (ind_params mdecl) p.(proj_arg) ty).
  rw projs_inst_skipn.
  assert (context_assumptions (cstr_args cdecl) -
    S (context_assumptions (cstr_args cdecl) - S p.(proj_arg)) = p.(proj_arg)) as -> by lia.
  clear X.
  rw subst_instance_subst.
  rw (subst_instance_subst u').
  rw !subst_instance_subst [subst_instance _ (projs _ _ _)]subst_instance_projs.
  rw - !subst_instance_subst.
  fold (expand_lets_k (ind_params mdecl) p.(proj_arg) ty).
  rw commut_lift_subst_rec => /lens.
  rw commut_lift_subst_rec => /lens.
  rw distr_subst projs_subst_above. lia.
  rw (instantiate_inds declp cu).
  rw subst_instance_subst.
  rw (instantiate_inds declp cu').
  rw subst_instance_subst.
  rw ![subst_instance _ (projs _ _ _)]subst_instance_projs.
  rw distr_subst projs_subst_above. lia.
  rw projs_length !Nat.add_succ_r Nat.add_0_r /= //.
  rw !subst_instance_lift // projs_inst_0 //.
  rw p0.(onNpars) //.
Qed.

Lemma wt_ind_app_variance {cf} {Σ} {wfΣ : wf Σ} {Γ ind u l}:
  isType Σ Γ (mkApps (tInd ind u) l) ->
  ∑ mdecl, (lookup_inductive Σ ind = Some mdecl) *
  (global_variance Σ (IndRef ind) #|l| = match ind_variance (fst mdecl) with Some var => Variance var | None => AllEqual end).
Proof.
  intros (_ & s & wat & _).
  eapply inversion_mkApps in wat as [ty [Hind Hargs]]; auto.
  eapply inversion_Ind in Hind as [mdecl [idecl [wfΓ [decli [cu cum]]]]]; auto.
  eapply typing_spine_strengthen in Hargs; eauto. clear cum.
  2: now eapply isTypeRel_isType, (declared_inductive_valid_type decli).
  exists (mdecl, idecl).
  assert (lookup_inductive Σ ind = Some (mdecl, idecl)).
  { destruct decli as [decli declmi].
    unshelve eapply declared_minductive_to_gen in decli; eauto.
    rw /lookup_inductive /lookup_inductive_gen. red in decli.
    rw /lookup_minductive /lookup_minductive_gen decli.
    now rw declmi. }
  split; auto.
  simpl. unfold lookup_inductive in H; rw H.
  destruct (on_declared_inductive decli) as [onmi oni]; auto.
  rw oni.(ind_arity_eq) in Hargs |- *.
  rw !destArity_it_mkProd_or_LetIn. simpl.
  rw app_context_nil_l.
  rw !subst_instance_it_mkProd_or_LetIn in Hargs.
  rw -it_mkProd_or_LetIn_app in Hargs.
  eapply arity_typing_spine in Hargs; auto.
  destruct Hargs as [Hl Hleq ?]. rw Hl.
  len. now rw Nat.leb_refl.
Qed.

Lemma ctx_inst_app_weak `{checker_flags} Σ (wfΣ : wf Σ.1) ind mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl)Γ (wfΓ : wf_local Σ Γ) params args u v:
  isType Σ Γ (mkApps (tInd ind u) args) ->
  consistent_instance_ext Σ (ind_universes mdecl) v ->
  ctx_inst Σ Γ params (List.rev (subst_instance v (ind_params mdecl))) ->
  Σ ;;; Γ ⊢ mkApps (tInd ind u) args ≤ mkApps (tInd ind v) (params ++ skipn (ind_npars mdecl) args) ->
  ctx_inst Σ Γ (params ++ skipn (ind_npars mdecl) args)
    (List.rev (subst_instance v (ind_params mdecl ,,, ind_indices idecl))).
Proof.
  intros isTy ? cparams cum.
  pose proof (wt_ind_app_variance isTy) as [mdecl' [idecl' gv]].
  unfold lookup_inductive in idecl'.
  unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
  rw (declared_inductive_lookup_gen isdecl') in idecl'. noconf idecl'.
  destruct isTy as (_ & ? & ty_args & _).
  eapply invert_type_mkApps_ind in ty_args as [ty_args ?] ; eauto.
  erewrite ind_arity_eq in ty_args.
  2: eapply PCUICInductives.oib ; eauto.

  assert (#|args| = ind_npars mdecl + context_assumptions (ind_indices idecl)).
  {
    repeat rw PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in ty_args.
    rw -it_mkProd_or_LetIn_app in ty_args.
    apply arity_typing_spine in ty_args as [eq _ _] ; auto.
    rw context_assumptions_app !context_assumptions_subst_instance in eq.
    erewrite declared_minductive_ind_npars.
    2: eapply declared_minductive_from_gen; eapply declared_inductive_minductive ; eauto.
    Unshelve. all:eauto. lia.
  }

  assert (cindices : ctx_inst Σ Γ (skipn (ind_npars mdecl) args) (subst_telescope (ctx_inst_sub cparams) 0
    (List.rev (subst_instance v (ind_indices idecl))))).
  {
    rw PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in ty_args.
    erewrite <- (firstn_skipn _ args) in ty_args.
    apply typing_spine_ctx_inst in ty_args as [cparargs ty_indices] ; auto.
    2:{ rw firstn_length_le.
        2:{ rw context_assumptions_subst_instance.
            symmetry.
            eapply onNpars.
            eapply on_declared_inductive ; eauto.

        }
        lia.
    }

    pose proof (declared_minductive_ind_npars isdecl).
    eapply invert_cumul_ind_ind in cum as [[_ Ruv] conv].
    rw -{1}(firstn_skipn (ind_npars mdecl) args) in conv.
    eapply All2_app_inv in conv as [convpars _].
    2:{ apply ctx_inst_length in cparams.
        rw context_assumptions_rev in cparams. len in cparams.
        rw List.length_firstn. lia. }
    unshelve epose proof (inductive_cumulative_indices isdecl c H0 Ruv Γ).
    specialize (X (firstn (ind_npars mdecl) args) params).
    unshelve epose proof (ctx_inst_spine_subst _ cparams); tea.
    { eapply weaken_wf_local; tea. eapply (on_minductive_wf_params isdecl); tea. }
    unshelve epose proof (ctx_inst_spine_subst _ cparargs); tea.
    { eapply weaken_wf_local; tea. eapply (on_minductive_wf_params isdecl); tea. }
    specialize (X _ _ X1 X0 convpars). simpl in X.
    rw subst_telescope_subst_context.
    eapply ctx_inst_smash.
    rw subst_instance_it_mkProd_or_LetIn in ty_indices.
    rw subst_it_mkProd_or_LetIn in ty_indices.
    rw -(app_nil_r (skipn (ind_npars mdecl) args)) in ty_indices.
    eapply typing_spine_ctx_inst in ty_indices as [argsi sp]; tea.
    - eapply ctx_inst_cumul; tea.
      apply (ctx_inst_smash.1 argsi).
      { apply All_local_env_app_inv. apply wf_local_smash_end; tea.
        eapply substitution_wf_local; tea. eapply X1.
        rw -app_context_assoc -subst_instance_app_ctx.
        eapply weaken_wf_local; tea.
        eapply (on_minductive_wf_params_indices_inst isdecl _ c). }
      { apply All_local_env_app_inv. apply wf_local_smash_end; tea.
        eapply substitution_wf_local; tea. eapply X0.
        rw -app_context_assoc -subst_instance_app_ctx.
        eapply weaken_wf_local; tea.
        eapply (on_minductive_wf_params_indices_inst isdecl _ H0). }
    - len. rw List.length_skipn. lia.
  }

  rw subst_instance_app_ctx List.rev_app_distr.
  now eapply (ctx_inst_app cparams).
Qed.

Lemma isType_it_mkProd_or_LetIn {cf:checker_flags} {Σ Γ Δ T} :
  wf Σ.1 ->
  isType Σ (Γ ,,, Δ) T ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T).
Proof.
  intros wfΣ. revert T.
  induction Δ as [|[na [b|] ty] Δ].
  - now simpl.
  - intros T Hty.
    rw /= /mkProd_or_LetIn /=.
    eapply IHΔ.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    have wf := typing_wf_local Hs.
    depelim wf.
    eapply type_Cumul'.
    econstructor; eauto. eapply isType_Sort; eauto.
    now eapply PCUICWfUniverses.typing_wf_sort in Hs.
    eapply convSpec_cumulSpec, red1_cumulSpec.
    repeat constructor.
  - intros T (_ & s & Hs & _).
    apply IHΔ.
    red.
    have wf := typing_wf_local Hs.
    depelim wf.
    pose proof (lift_sorting_extract l).
    eapply has_sort_isType with (s := Sort.sort_of_product _ s).
    econstructor; eauto.
Qed.

Lemma wf_set_binder_name {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {nas Δ} :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, map2 set_binder_name nas Δ).
Proof.
  intros ha wf.
  apply All_local_env_app_inv in wf as [wfΓ wfΔ].
  eapply All_local_env_app => //.
  induction wfΔ using All_local_rel_ind1 in nas, ha |- *; depelim ha; cbn. constructor.
  specialize (IHwfΔ _ ha).
  apply All_local_rel_snoc; tas.
  unfold set_binder_name at 2. cbn. rw e.
  apply lift_typing_impl with (1 := X) => // ?? Hs.
  eapply context_conversion; tea.
  1: now eapply All_local_env_app.
  eapply eq_binder_annots_eq_ctx in ha.
  eapply eq_context_upto_names_conv_context.
  eapply All2_app.
  2: reflexivity.
  symmetry; apply ha.
Qed.

Lemma WfArity_build_case_predicate_type {cf:checker_flags} {Σ Γ ci args mdecl idecl p ps} :
  wf Σ.1 ->
  declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci p.(puinst)) (pparams p ++ args)) ->
  let params := firstn (ind_npars mdecl) args in
  wf_sort Σ ps ->
  wf_predicate mdecl idecl p ->
  isWfArity Σ Γ (it_mkProd_or_LetIn (case_predicate_context ci mdecl idecl p) (tSort ps)).
Proof.
  intros wfΣ isdecl X params wfps wfp.
  split.
  2:{ eexists _, _. rw destArity_it_mkProd_or_LetIn. reflexivity. }
  rw /case_predicate_context /case_predicate_context_gen.
  have wfΓ := typing_wf_local X.2.π2.1.
  eapply isType_mkApps_Ind_inv in X; tea.
  destruct X as [parsubst [argsubst [sppars spargs parslen argslen cu]]].
  epose proof (isType_case_predicate (puinst p) (pparams p) ps wfΓ isdecl cu wfps).
  rw (firstn_app_left) /= ?app_nil_r in sppars.
  now rw (wf_predicate_length_pars wfp).
  eapply spine_subst_smash in sppars;tea. specialize (X sppars).
  eapply isType_it_mkProd_or_LetIn; eauto.
  eapply isType_Sort; auto.
  eapply wf_set_binder_name.
  now eapply wf_pre_case_predicate_context_gen.
  now eapply isType_it_mkProd_or_LetIn_wf_local in X.
Qed.

(*
Lemma leb_elim_prop_sort shapes f n cs :
  allowed_eliminations_subset f (elim_sort_prop_ind shapes) ->
  nth_error shapes n = Some cs ->
  allowed_eliminations_subset f (if is_propositional cs.(cdecl_sort) then IntoAny else IntoPropSProp).
Proof.
  destruct shapes as [|? []]; simpl.
  - rewrite nth_error_nil => //.
  - destruct n => // /= leb. simpl. now intros [= ->].
    simpl. rewrite nth_error_nil //.
  - destruct f => //.
    destruct is_propositional => //.
Qed.
*)

Lemma arity_spine_eq {cf:checker_flags} {Σ Γ T T'} : T = T' -> arity_spine Σ Γ T [] T'.
Proof.
  intros ->; constructor.
Qed.

Lemma forall_nth_error_All2i :
  forall {A B} (P : nat -> A -> B -> Type) k l l',
    #|l| = #|l'| ->
    (forall i x y, nth_error l i = Some x -> nth_error l' i = Some y -> P (k + i) x y) ->
    All2i P k l l'.
Proof.
  intros A B P k l l' eq h.
  induction l in k, eq, h, l' |- *.
  - destruct l' => //. constructor.
  - destruct l' => //. constructor.
    + specialize (h 0 a b eq_refl eq_refl). now rw Nat.add_0_r in h.
    + apply IHl. simpl in eq; lia. intros. specialize (h (S i) x y H H0).
      simpl. now replace (S (k + i)) with (k + S i) by lia.
Qed.


(*
Lemma idecl_binder_ind_binder {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind idecl mdecl p} :
  declared_inductive Σ ind mdecl idecl ->
  idecl_binder idecl = ind_binder ind idecl p.
Proof.
  move/declared_inductive_type.
  rewrite /idecl_binder => ->.
  rewrite /ind_binder. *)

Lemma subst_let_expand_app s Γ s' Δ k :
  k = #|Δ| ->
  #|s| = context_assumptions Γ ->
  subst0 s ∘
  subst0 (map (lift0 #|s|) s') ∘
    (expand_lets (expand_lets_ctx Γ Δ) ∘ expand_lets_k Γ k) ≐1
  subst_let_expand (s' ++ s) (Γ ,,, Δ).
Proof.
  intros hk hs t.
  rw /subst_let_expand /expand_lets.
  rw subst_app_decomp. f_equal.
  rw !expand_lets_k_0.
  rw expand_lets_app. len.

  rw /subst_context_let_expand /subst_let_expand_k.
  rw {1}/expand_lets_k.
  rw /expand_lets_ctx /expand_lets_k_ctx. len. subst k.
  relativize #|Δ|.
  erewrite expand_lets_subst_comm.
  len. 2:now len.
  rw expand_lets_lift.
  now rw -Nat.add_comm -/(expand_lets_k Γ (context_assumptions Δ) (expand_lets Δ t)).
Qed.

Lemma All2_fold_context_k P (f g : nat -> term -> term) ctx ctx' :
  All2_fold (fun Γ Γ' d d' => P (map_decl (f #|Γ|) d) (map_decl (g #|Γ'|) d')) ctx ctx' ->
  All2 P (fold_context_k f ctx) (fold_context_k g ctx').
Proof.
  induction 1. constructor.
  rw !fold_context_k_snoc0. now constructor.
Qed.

Lemma All2_sym {A B} (P : A -> B -> Type) (ctx : list A) (ctx' : list B) :
  All2 P ctx ctx' ->
  All2 (fun x y => P y x) ctx' ctx.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma isType_is_open_term {cf} {Σ} {wfΣ : wf Σ} Γ T : isType Σ Γ T -> is_open_term Γ T.
Proof.
  intros (_ & s & hs & _). now apply subject_is_open_term in hs.
Qed.
#[global] Hint Immediate isType_is_open_term : pcuic.

Lemma arity_spine_to_extended_list {cf} {Σ} {wfΣ : wf Σ} {Γ Δ} T :
  wf_local Σ (Γ ,,, Δ) ->
  isType Σ (Γ ,,, Δ) T ->
  arity_spine Σ (Γ ,,, Δ) (lift0 #|Δ| (it_mkProd_or_LetIn Δ T)) (to_extended_list Δ)
    T.
Proof.
  intros hty wf.
  rw lift_it_mkProd_or_LetIn Nat.add_0_r.
  pose proof (@all_rels_subst_lift _ _ _ Δ Γ [] T hty (wf_local_closed_context hty)).
  rw lift0_id in X. simpl in X.
  rw Nat.add_0_r in X.
  rw -(app_nil_r (to_extended_list Δ)).
  eapply arity_spine_it_mkProd_or_LetIn; tea.
  rw /to_extended_list /to_extended_list_k.
  eapply spine_subst_to_extended_list_k; tea.
  constructor => //.
  eapply ws_cumul_pb_eq_le. symmetry. apply X => //. eauto with pcuic.
Qed.

Lemma isType_subst_all_rels {cf} {Σ} {wfΣ : wf Σ} {Γ Δ} {T} :
  isType Σ (Γ ,,, Δ) T ->
  isType Σ (Γ ,,, Δ) (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| T)).
Proof.
  intros Hty.
  apply lift_sorting_it_impl_gen with Hty => // Hs.
  pose proof (typing_wf_local Hs).
  eapply weakening_typing in Hs; tea.
  rw -(app_nil_l (lift_context _ _ _)) -/(app_context _ _) app_context_assoc in Hs.
  eapply substitution in Hs; tea.
  eapply spine_subst_to_extended_list_k; tea.
Qed.

Lemma isType_all_rels_subst_lift {cf} {Σ} {wfΣ : wf Σ} {Γ Δ} {T} :
  isType Σ (Γ ,,, Δ) T ->
  Σ ;;; Γ,,, Δ  ⊢ T = subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| T).
Proof.
  intros isty.
  have wf := (isType_wf_local isty).
  epose proof (@all_rels_subst_lift _ _ _ Δ Γ [] T wf (wf_local_closed_context wf)
  ltac:(eauto with pcuic)).
  now rw lift0_id /= Nat.add_0_r in X.
Qed.

Lemma arity_spine_to_extended_list_app {cf} {Σ} {wfΣ : wf Σ} {Γ Δ} {T s T'} :
  wf_local Σ (Γ ,,, Δ) ->
  isType Σ (Γ ,,, Δ) T ->
  arity_spine Σ (Γ ,,, Δ) (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| T)) s T' ->
  arity_spine Σ (Γ ,,, Δ) (lift0 #|Δ| (it_mkProd_or_LetIn Δ T)) (to_extended_list Δ ++ s) T'.
Proof.
  intros isty wf.
  rw lift_it_mkProd_or_LetIn Nat.add_0_r.
  pose proof (isType_all_rels_subst_lift wf).
  intros sp.
  eapply arity_spine_it_mkProd_or_LetIn; tea.
  rw /to_extended_list /to_extended_list_k.
  eapply spine_subst_to_extended_list_k; tea.
Qed.

Lemma typing_spine_to_extended_list_app {cf} {Σ} {wfΣ : wf Σ} {Γ Δ} {T s T'} :
  typing_spine Σ (Γ ,,, Δ) T s T' ->
  typing_spine Σ (Γ ,,, Δ) (lift0 #|Δ| (it_mkProd_or_LetIn Δ T)) (to_extended_list Δ ++ s) T'.
Proof.
  rw lift_it_mkProd_or_LetIn Nat.add_0_r.
  intros sp.
  have isty := (typing_spine_isType_dom sp).
  eapply typing_spine_it_mkProd_or_LetIn'; tea.
  rw /to_extended_list /to_extended_list_k.
  eapply spine_subst_to_extended_list_k; tea.
  pcuic.
  eapply typing_spine_strengthen; tea.
  now eapply isType_subst_all_rels.
  eapply ws_cumul_pb_eq_le. symmetry.
  exact (isType_all_rels_subst_lift isty).
  rw -[X in lift _ X _](Nat.add_0_r #|Δ|).
  rw -lift_it_mkProd_or_LetIn.
  eapply isType_lift; tea. now len.
  pcuic.
  rw skipn_app List.skipn_all /= Nat.sub_diag skipn_0.
  now eapply isType_it_mkProd_or_LetIn.
Qed.

Lemma typing_spine_to_extended_list_k_app {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} {T s T'} :
  isType Σ (Γ ,,, Δ) T ->
  typing_spine Σ (Γ ,,, Δ ,,, Δ') (lift0 #|Δ'| T) s T' ->
  typing_spine Σ (Γ ,,, Δ ,,, Δ') (lift0 (#|Δ| + #|Δ'|) (it_mkProd_or_LetIn Δ T))
    (to_extended_list_k Δ #|Δ'| ++ s) T'.
Proof.
  intros isty sp.
  have wf := (typing_spine_wf_local sp).
  rw !lift_it_mkProd_or_LetIn Nat.add_0_r.
  eapply typing_spine_it_mkProd_or_LetIn'; tea.
  rw /to_extended_list /to_extended_list_k.
  rw -{1}(Nat.add_0_r #|Δ'|) reln_lift.
  rw -Nat.add_comm lift_context_add.
  eapply spine_subst_weakening;tea.
  eapply spine_subst_to_extended_list_k; tea.
  now apply All_local_env_app_inv in wf.
  destruct (All_local_env_app_inv wf) as [].
  epose proof (@all_rels_subst_lift _ _ _ _ _ Δ' T a).
  eapply typing_spine_strengthen; tea; revgoals.
  eapply ws_cumul_pb_eq_le; symmetry.
  rw -all_rels_lift Nat.add_comm.
  eapply X. 2:pcuic. eauto with fvs.

  clear X.
  apply lift_sorting_f_it_impl with (f := fun t => _ (_ t)) (tu := isty) => // Hs.
  eapply (weakening_typing) in Hs; tea.
  eapply (substitution (Δ := [])) in Hs.
  2:{ epose proof (spine_subst_to_extended_list_k a). apply X. }
  eapply (weakening_typing) in Hs; tea. len in Hs.
  rw distr_lift_subst in Hs. len in Hs.
  rw all_rels_length in Hs.
  rw simpl_lift in Hs; try lia.
  now rw Nat.add_comm.
  rw -(Nat.add_0_r #|Δ|) -lift_it_mkProd_or_LetIn Nat.add_0_r.
  rw -length_app.
  replace #|Δ ++ Δ'| with (#|Δ ,,, Δ'|).
  2:now len.
  eapply isType_lift; tea. now len.
  rw -app_context_assoc.
  rw skipn_app List.skipn_all /= Nat.sub_diag skipn_0.
  now eapply isType_it_mkProd_or_LetIn.
Qed.

Lemma subst_let_expand_lift s Γ n T :
  #|s| = context_assumptions Γ ->
  subst_let_expand (map (lift0 n) s) (lift_context n 0 Γ) (lift n #|Γ| T) =
  lift0 n (subst_let_expand s Γ T).
Proof.
  intros hs.
  rw /subst_let_expand -(Nat.add_0_r #|Γ|) expand_lets_lift /=.
  now rw distr_lift_subst hs Nat.add_0_r.
Qed.

Lemma subst_let_expand_closed_ctx_lift s Γ n T :
  #|s| = context_assumptions Γ ->
  closed_ctx Γ ->
  subst_let_expand (map (lift0 n) s) Γ (lift n #|Γ| T) =
  lift0 n (subst_let_expand s Γ T).
Proof.
  intros hs cl.
  now rw -{1}(closed_ctx_lift n 0 Γ) // subst_let_expand_lift.
Qed.


Lemma wf_case_predicate_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ mdecl idecl ci p } {args : list term} :
  declared_inductive Σ ci.(ci_ind) mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  wf_local Σ (Γ ,,, predctx).
Proof.
  intros isdecl Hc wfp predctx.
  epose proof (WfArity_build_case_predicate_type wfΣ isdecl Hc
    (PCUICWfUniverses.wf_sort_type1 Σ) wfp).
  destruct X.
  eapply isType_it_mkProd_or_LetIn_inv in i; tea.
  now eapply isType_wf_local in i.
Qed.

Lemma wf_pre_case_branch_context_gen {ci mdecl idecl cdecl} {p} {br} :
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  All2 (fun (x : binder_annot name) (y : context_decl) => eq_binder_annot x (decl_name y))
    (forget_types (bcontext br))
    (pre_case_branch_context_gen ci mdecl cdecl (pparams p) (puinst p)).
Proof.
  move=> [] hlen hp /Forall2_All2 a.
  rw /pre_case_branch_context_gen /cstr_branch_context.
  eapply All2_eq_binder_subst_context_inst.
  induction a. constructor.
  rw subst_context_snoc. constructor; auto.
Qed.

Definition case_branch_context_nopars ind mdecl puinst cdecl :=
  (subst_context (inds (inductive_mind ind) puinst (ind_bodies mdecl))
  #|ind_params mdecl|
  (subst_instance puinst (cstr_args cdecl))).

Lemma case_predicate_context_alpha {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl p Γ} :
  declared_inductive Σ.1 ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
  let parctx := subst_instance (puinst p) mdecl.(ind_params) in
  spine_subst Σ Γ p.(pparams) (List.rev p.(pparams)) (smash_context [] parctx) ->
  All2 (fun x y => eq_binder_annot x y.(decl_name))
     (forget_types (pcontext p))
    (idecl_binder idecl :: ind_indices idecl) ->
  eq_context_upto_names (case_predicate_context' ind mdecl idecl p)
    (case_predicate_context ind mdecl idecl p).
Proof.
  intros decli cu parctx sp.
  rw /case_predicate_context /case_predicate_context_gen /case_predicate_context'.
  rw /pre_case_predicate_context_gen.
  fold (ind_binder ind idecl p).
  intros a; depelim a.
  destruct (pcontext p) eqn:pctx => //. simpl.
  rw /ind_predicate_context /= /inst_case_context.
  rw subst_instance_cons.
  rw /= subst_context_snoc /=.
  constructor.
  { rw /= /subst_decl /map_decl /= /set_binder_name /=. relativize (subst _ _ _).
    1: constructor. red. simpl. simpl in e. red in e. simpl in e.
    rw -e. simpl in H. noconf H. reflexivity.
    simpl. rw subst_instance_mkApps subst_mkApps /=.
    f_equal. f_equal.
    now rw [subst_instance_instance _ _](subst_instance_id_mdecl _ _ _ cu).
    rw /to_extended_list to_extended_list_k_app.
    rw !map_app. f_equal.
    rw subst_instance_to_extended_list_k. len.
    erewrite subst_to_extended_list_k => //.
    eapply make_context_subst_spec_inv. rw List.rev_involutive.
    rw subst_instance_smash.
    apply sp.
    rw subst_instance_to_extended_list_k.
    rw /expand_lets_ctx /expand_lets_k_ctx.
    rw subst_instance_subst_context subst_instance_lift_context.
    rw to_extended_list_k_subst /= to_extended_list_k_lift_context.
    rw -to_extended_list_k_map_subst. len.
    now rw PCUICLiftSubst.map_subst_instance_to_extended_list_k. }
  eapply All2_symP. intros ? ? []; constructor; auto; now symmetry.
  eapply All2_map2_left_All3.
  simpl in H. noconf H.
  revert a. move: (map _ l0) => l a.
  induction a. constructor.
  rw /expand_lets_ctx /expand_lets_k_ctx.
  rw !lift_context_snoc /=.
  rw subst_context_snoc /= subst_instance_cons subst_context_snoc.
  constructor; auto.
  destruct y as [na [b|] ty]; constructor; simpl; auto; reflexivity.
Qed.

Lemma inst_case_predicate_context_alpha_eq {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wf Σ}
  {mdecl idecl ci p} :
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  eq_context_upto_names
    (map2 set_binder_name (forget_types (pcontext p))
      (inst_case_context (pparams p) (puinst p)
          (ind_predicate_context ci mdecl idecl)))
    (subst_context (List.rev (pparams p)) 0 (pcontext p)@[puinst p]).
Proof.
  intros a.
  eapply All2_trans. tc.
  { eapply eq_binder_annots_eq.
    rw /inst_case_context.
    apply All2_eq_binder_subst_context, All2_eq_binder_subst_instance.
    eapply All2_map_left, All2_impl; tea. intros x y []; auto. }
  { apply alpha_eq_subst_context, alpha_eq_subst_instance.
    now symmetry. }
Qed.

(* No need to worry about the name annotations in the proofs below, for all typing
  purposes we can work with the simpler context not involving the renaming *)
Lemma pre_case_branch_context_eq {cf}	{Σ} {wfΣ : wf Σ} {ind mdecl idecl params puinst bctx cdecl} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) puinst ->
  wf_branch_gen cdecl bctx ->
  eq_context_upto_names
    (pre_case_branch_context ind mdecl params puinst cdecl)
    (case_branch_context_gen ind mdecl params puinst bctx cdecl).
Proof.
  intros decli cu.
  unfold wf_branch_gen. intros wf%Forall2_All2.
  rw /pre_case_branch_context /case_branch_context_gen.
  symmetry. etransitivity.
  eapply eq_binder_annots_eq.
  rw /pre_case_branch_context_gen /inst_case_context /cstr_branch_context.
  eapply All2_eq_binder_subst_context_inst.
  now eapply All2_eq_binder_subst_context.
  rw /pre_case_branch_context_gen /inst_case_context /cstr_branch_context.
  eapply alpha_eq_subst_context.
  rw subst_instance_expand_lets_ctx subst_instance_subst_context.
  now rw (instantiate_inds decli cu) //.
Qed.

Lemma wf_case_branch_type {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) :
  declared_inductive Σ ci mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  Σ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  forall i cdecl br,
    declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
    wf_branch cdecl br ->
    let cstr_br_ctx := case_branch_context_nopars ci mdecl p.(puinst) cdecl in
    let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    [× wf_branch cdecl br,
       (* The branch context before substitution of parameters *)
       wf_local Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, cstr_br_ctx),
       wf_local Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, brctx'),
       wf_local Σ (Γ ,,, brctxty.1) &
       Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps].
Proof.
  intros isdecl Hc wfp bc Hp ptm wfpctx.
  unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
  destruct (WfArity_build_case_predicate_type wfΣ isdecl Hc (PCUICWfUniverses.typing_wf_sort _ Hp) wfp) as [wfty _].
  set wfcpc := wf_case_predicate_context isdecl Hc wfp. simpl in wfcpc. clearbody wfcpc.
  have clipars : closed_ctx (subst_instance (puinst p) (ind_params mdecl)).
  { rw closedn_subst_instance_context.
    eapply (declared_inductive_closed_params isdecl). }
  have wfΓ : (wf_local Σ Γ).
  { now apply isType_wf_local in Hc. }
  have lenpars : #|pparams p| =
      context_assumptions (subst_instance (puinst p) (ind_params mdecl)).
  { len. rw (wf_predicate_length_pars wfp) //.
    apply (declared_minductive_ind_npars isdecl). }
  eapply isType_mkApps_Ind_smash in Hc; tea.
  2:{ rw (declared_minductive_ind_npars isdecl). now len in lenpars. }
  destruct Hc as [sppars [spargs cu]].
  intros n cdecl br nth wfbr.
  set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
  destruct (on_declared_constructor nth) as [[onind oib] [cs [nthc onc]]].
  simpl in *.
  subst brctxty.
  unfold case_branch_type, case_branch_type_gen => /=.
  rw -/(case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl).

  assert (wfargs : wf_local (Σ.1, ind_universes mdecl)
  (arities_context (ind_bodies mdecl),,, ind_params mdecl,,, cstr_args cdecl)).
  { destruct onc. apply sorts_local_ctx_All_local_env in on_cargs => //.
    eapply weaken_wf_local => //.
    eapply (wf_arities_context' onind) => //.
    apply onind.(onParams). }
  assert (wfparscd : wf_local Σ
  (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
   case_branch_context_nopars ci mdecl (puinst p) cdecl)). {
    rw -app_context_assoc.
    eapply weaken_wf_local; tea.
    eapply (@wf_local_instantiate _ _ (InductiveDecl mdecl) _ p.(puinst)) in wfargs; tea.
    2:eapply isdecl'.
    rw !subst_instance_app in wfargs.
    rw - !/(app_context _ _) in wfargs.
    rw -(app_context_nil_l (_ ,,, _)) -app_context_assoc app_context_assoc in wfargs.
    eapply substitution_wf_local in wfargs; tea.
    2:eapply subslet_inds; tea.
    rw app_context_nil_l subst_context_app in wfargs.
    rw closed_ctx_subst in wfargs => //.
    rw /case_branch_context_nopars.
    now rw subst_instance_length Nat.add_0_r in wfargs. }
  assert (wf_local Σ (Γ ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)).
  { rw /case_branch_context /case_branch_context_gen.
    eapply wf_set_binder_name.
    { eapply wf_pre_case_branch_context_gen; tea. }
    eapply substitution_wf_local; tea. eapply sppars.
    rw /cstr_branch_context.
    rw subst_instance_expand_lets_ctx.
    eapply wf_local_expand_lets => //.
    rw subst_instance_subst_context.
    rw (instantiate_inds nth cu) //. }
  split => //.
  { eapply wf_set_binder_name => //.
    eapply All2_eq_binder_subst_context.
    eapply All2_eq_binder_subst_instance.
    now eapply Forall2_All2 in wfbr. }
  assert (wfparsargs : wf_local Σ
    (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
      subst_context (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
        #|ind_params mdecl| (subst_instance (puinst p) (cstr_args cdecl)))). {
    rw -app_context_assoc.
    eapply weaken_wf_local; tea.
    eapply (@wf_local_instantiate _ _ (InductiveDecl mdecl) _ p.(puinst)) in wfargs; tea.
    2:eapply isdecl'.
    rw !subst_instance_app in wfargs.
    rw - !/(app_context _ _) in wfargs.
    rw -(app_context_nil_l (_ ,,, _)) -app_context_assoc app_context_assoc in wfargs.
    eapply substitution_wf_local in wfargs; tea.
    2:eapply subslet_inds; tea.
    rw app_context_nil_l subst_context_app in wfargs.
    rw closed_ctx_subst in wfargs => //.
    now rw subst_instance_length Nat.add_0_r in wfargs. }
  assert (wfbrctx : wf_local Σ (Γ ,,, pre_case_branch_context ci mdecl p.(pparams) p.(puinst) cdecl)).
  { rw /case_branch_context /case_branch_context_gen.
    eapply substitution_wf_local; tea. eapply sppars.
    eapply wf_local_expand_lets => //. }
  eapply type_mkApps.
  relativize #|cstr_args cdecl|.
  eapply weakening; tea. rw /ptm.
  eapply type_it_mkLambda_or_LetIn. tea.
  rw case_branch_context_length //.
  now rw -(wf_branch_length wfbr).
  eapply wf_arity_spine_typing_spine; tea.
  split.
  { apply isType_lift => //. rw length_app; lia.
    rw skipn_all_app //. }
  rw /bc.
  rw lift_it_mkProd_or_LetIn /=.
  rw -(app_nil_r (_ ++ [_])).
  eapply arity_spine_it_mkProd_or_LetIn_smash => //.
  2:constructor.
  rw /bc.
  *eapply subslet_eq_context_alpha.
  { instantiate (1 := smash_context []
    (lift_context #|case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl| 0
      (case_predicate_context' ci mdecl idecl p))).
    apply alpha_eq_smash_context, alpha_eq_lift_context.
    epose proof (wf_pre_case_predicate_context_gen (ci:=ci) wfp).
    rw /inst_case_predicate_context.
    eapply All2_trans. tc.
    eapply case_predicate_context_alpha; tea.
    destruct wfp. apply Forall2_All2 in H0. tea.
    now eapply inst_case_predicate_context_eq in wfpctx. }
  rw map_map_compose.
  fold (subst_let_expand_k (List.rev (pparams p)) (subst_instance (puinst p) (ind_params mdecl)) #|cstr_args cdecl|).
  set (indices := map (subst (inds _ _ _) _) _).
  rw /case_predicate_context' lift_context_snoc.
  rw subst_context_length subst_instance_length expand_lets_ctx_length.
  rw (smash_context_app_expand _ _ [_]).
  cbn. rw List.rev_app_distr; cbn.
  rw expand_lets_ctx_tip; cbn.
  rw /lift_decl compose_map_decl; cbn.
  eapply (subslet_eq_context_alpha_dom (Γ:=  (Γ ,,, pre_case_branch_context ci.(ci_ind) mdecl p.(pparams) p.(puinst) cdecl))).
  { eapply All2_app.
    rw /case_branch_context //.
    eapply (pre_case_branch_context_eq (ind:=ci) nth cu wfbr).
    reflexivity. }
  pose proof (on_cindices onc).
  eapply ctx_inst_impl in X0. 2: intros ??; apply unlift_TermTyp.
  assert (spindices :
  spine_subst Σ
  (Γ,,, pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl)
  (map (subst (List.rev (pparams p)) #|cstr_args cdecl|)
     (map
        (expand_lets_k (subst_instance (puinst p) (ind_params mdecl))
           #|cstr_args cdecl|) indices))
  (map (subst (List.rev (pparams p)) #|cstr_args cdecl|)
     (map
        (expand_lets_k (subst_instance (puinst p) (ind_params mdecl))
           #|cstr_args cdecl|)
        (map
           (subst
              (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
              (#|ind_params mdecl| + #|cstr_args cdecl|))
           (map (subst_instance (puinst p)) (ctx_inst_sub X0)))))
  (subst_context (List.rev (pparams p)) #|cstr_args cdecl|
     (expand_lets_k_ctx (subst_instance (puinst p) (ind_params mdecl))
        #|cstr_args cdecl|
        (subst_instance (puinst p)
           (lift_context #|cstr_args cdecl| 0 (ind_indices idecl)))))).
  { unshelve epose proof (ctx_inst_spine_subst _ X0) as sp.
    { eapply weakening_wf_local => //.
      rw -app_context_assoc. apply weaken_wf_local => //.
      eapply (wf_arities_context isdecl).
      apply (on_minductive_wf_params_indices isdecl). }
    eapply spine_subst_inst in sp; tea.
    2:{ exact (declared_inductive_wf_global_ext _ _ _ _ isdecl). }
    rw !subst_instance_app_ctx in sp.
    rw -app_context_assoc in sp.
    eapply spine_subst_subst_first in sp; tea.
    2:eapply subslet_inds; tea.
    rw app_context_length !subst_instance_length in sp.
    rw subst_context_app subst_instance_length /= Nat.add_0_r in sp.
    rw closed_ctx_subst // in sp.
    eapply spine_subst_weaken in sp. 2:eapply wfΓ. all:tea.
    rw app_context_assoc in sp.
    rw Nat.add_comm in sp; fold indices in sp.
    eapply spine_subst_expand_lets in sp.
    rw subst_context_length subst_instance_length in sp.
    eapply spine_subst_subst in sp; tea.
    2:exact sppars.
    rw expand_lets_ctx_length subst_context_length subst_instance_length in sp.
    rw /subst_context_let_expand.
    rw (closed_ctx_subst (inds _ _ _) (#|ind_params mdecl| + _)) in sp.
    { rw closedn_subst_instance_context.
      rw Nat.add_comm; apply closedn_ctx_lift.
      pose proof (declared_inductive_closed_pars_indices isdecl).
      rw closedn_ctx_app in H.
      now move/andb_and: H => []. }
    exact sp. }
  constructor.
  - rw case_branch_context_length_args //.
    rw /indices.
    eapply spine_subst_smash in spindices; tea.
    rw subst_instance_expand_lets_ctx.
    rw lift_context_subst_context lift_context_expand_lets_ctx
      -subst_instance_lift_context.
    eapply inst_subslet in spindices.
    rw /subst_let_expand_k.
    rw /indices in spindices.
    now rw map_map_compose in spindices.
  - cbn [decl_type ind_binder].
    rw lift_mkApps expand_lets_mkApps.
    rw subst_mkApps. simpl.
    rw map_subst_let_expand_k.
    rw case_branch_context_length_args //.
    eapply meta_conv.
    { eapply type_mkApps.
      { econstructor; tea. }
      eapply wf_arity_spine_typing_spine; tea.
      split. { eapply validity. econstructor; eauto. }
      replace (type_of_constructor mdecl cdecl (ci.(ci_ind), n) (puinst p))
        with (lift0 #|cstr_args cdecl| (type_of_constructor mdecl cdecl (ci.(ci_ind), n) (puinst p))).
      2:{ rw lift_closed //. eapply (declared_constructor_closed_type nth). }
      unfold type_of_constructor.
      rw onc.(cstr_eq).
      simpl.
      rw subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
      rw lift_it_mkProd_or_LetIn.
      rw closed_ctx_lift.
      { rw closed_ctx_subst //. }
      eapply arity_spine_it_mkProd_or_LetIn_smash; tea.
      + rw closed_ctx_subst.
        rw closedn_subst_instance_context.
        eapply (declared_inductive_closed_params isdecl).
        rw -[smash_context [] _](closed_ctx_lift #|cstr_args cdecl| 0).
        { now apply closedn_smash_context. }
        rw -map_rev.
        relativize #|cstr_args cdecl|.
        eapply subslet_lift; tea. eapply sppars.
        now apply pre_case_branch_context_length_args.
      + rw subst_context_length Nat.add_0_r.
        rw subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
        rw -map_rev.
        relativize #|subst_instance (puinst p) (ind_params mdecl)|.
        erewrite subst_let_expand_closed_ctx_lift.
        2:{ now rw List.length_rev context_assumptions_subst_context. }
        3:now rw subst_context_length.
        2:{ rw closed_ctx_subst => //. }
        rw subst_let_expand_it_mkProd_or_LetIn.
        rw !subst_context_length !subst_instance_length.
        rw closed_ctx_subst //.
        set (cstr_ctx := subst_context_let_expand _ _ _).
        change cstr_ctx with
          (pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
        clear cstr_ctx.
        rw -{1}(@pre_case_branch_context_length_args ci mdecl (pparams p) (puinst p) cdecl).
        rw /to_extended_list /to_extended_list_k.
        relativize (reln [] 0 (cstr_args cdecl)).
        eapply arity_spine_to_extended_list => //.
        2:{ rw -/(to_extended_list_k _ 0) /pre_case_branch_context.
            rw /expand_lets_ctx /expand_lets_k_ctx /to_extended_list !to_extended_list_k_subst
              !to_extended_list_k_lift_context to_extended_list_k_subst
              PCUICLiftSubst.map_subst_instance_to_extended_list_k //. }
        rw /pre_case_branch_context /subst_let_expand_k.
        eapply has_sort_isType with (s := subst_instance p.(puinst) (ind_sort idecl)).
        relativize #|cstr_args cdecl|.
        eapply (substitution (s := List.rev (pparams p)) (T := tSort _)); tea.
        eapply sppars.
        all:rw expand_lets_ctx_length.
        2:rw subst_context_length subst_instance_length //.
        eapply (typing_expand_lets_gen (T:=tSort _)).
        rw subst_context_length subst_instance_length.
        rw -/(to_extended_list_k _ _).
        rw subst_cstr_concl_head.
        destruct isdecl. now eapply nth_error_Some_length in H0.
        eapply type_mkApps.
        econstructor; tea.
        rw -[subst_instance _ (ind_type idecl)](lift_closed (#|ind_params mdecl| + #|cstr_args cdecl|) 0).
        rw closedn_subst_instance.
        eapply (declared_inductive_closed_type _ _ _ _ _ isdecl).
        rw (declared_inductive_type isdecl).
        rw subst_instance_it_mkProd_or_LetIn subst_instance_app
          it_mkProd_or_LetIn_app.
        have wfs : wf_sort Σ (subst_instance_sort (puinst p) (ind_sort idecl)).
          by eapply (on_inductive_sort_inst isdecl _ cu).
        have wfparinds : wf_local Σ
            (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
              subst_instance (puinst p) (ind_indices idecl)).
        { rw -app_context_assoc -subst_instance_app_ctx.
          eapply weaken_wf_local; tea.
          eapply (on_minductive_wf_params_indices_inst isdecl _ cu). }
        relativize (#|ind_params mdecl| + #|cstr_args cdecl|).
        relativize (to_extended_list_k _ #|cstr_args cdecl|).
        eapply typing_spine_to_extended_list_k_app; tea.
        eapply isType_it_mkProd_or_LetIn; tea. simpl.
        eapply isType_Sort; tea.
        2:{ len. now rw PCUICLiftSubst.map_subst_instance_to_extended_list_k. }
        2:{ now len. }
        rw subst_context_length subst_instance_length lift_it_mkProd_or_LetIn /=.
        eapply typing_spine_it_mkProd_or_LetIn_close; tea.
        3:{ reflexivity. }
        2:{ eapply isType_it_mkProd_or_LetIn; tea.
            eapply isType_Sort.
            eapply (on_inductive_sort_inst isdecl _ cu).
            relativize #|cstr_args cdecl|.
            eapply weakening_wf_local => //. now len. }
        clear spindices.
        unshelve epose proof (ctx_inst_spine_subst _ X0) as sp.
        { eapply weakening_wf_local => //.
          rw -app_context_assoc. apply weaken_wf_local => //.
          eapply (wf_arities_context isdecl).
          apply (on_minductive_wf_params_indices isdecl). }
        eapply spine_subst_inst in sp; tea.
        2:{ exact (declared_inductive_wf_global_ext _ _ _ _ isdecl). }
        rw !subst_instance_app_ctx in sp.
        rw -app_context_assoc in sp.
        eapply spine_subst_subst_first in sp; tea.
        2:eapply subslet_inds; tea.
        rw app_context_length !subst_instance_length in sp.
        rw subst_context_app subst_instance_length /= Nat.add_0_r in sp.
        rw closed_ctx_subst // in sp.
        eapply spine_subst_weaken in sp. 2:eapply wfΓ. all:tea.
        rw app_context_assoc in sp.
        rw Nat.add_comm in sp |- *; fold indices in sp |- *.
        rw subst_instance_lift_context in sp.
        rw (closed_ctx_subst _ _ (lift_context #|cstr_args cdecl| _ _)) in sp.
        rw Nat.add_comm; eapply closedn_ctx_lift => //.
        epose proof (declared_inductive_closed_pars_indices isdecl).
        rw closedn_ctx_app in H. move/andb_and: H => [].
        now rw closedn_subst_instance_context.
        exact sp. }
    { rw Nat.add_0_r.
      rw subst_cstr_concl_head.
      { destruct isdecl. now eapply nth_error_Some_length in H0. }
      rw subst_let_expand_k_mkApps. cbn. f_equal.
      rw !map_app. f_equal.
      { rw -(PCUICLiftSubst.map_subst_instance_to_extended_list_k p.(puinst)).
        erewrite map_subst_let_expand_k_to_extended_list_lift.
        2:{ eapply sppars. }
        rw !map_map_compose.
        apply map_ext => t.
        rw simpl_lift; try lia.
        rw (Nat.add_comm #|cstr_args cdecl|).
        rw subst_let_expand_k_lift //.
        len => //. len.
        { clear spindices. apply ctx_inst_length in X0.
          rw context_assumptions_rev in X0. len in X0.
           } }
      { pose proof (positive_cstr_closed_indices nth).
        rw map_map_compose.
        rw -(Nat.add_0_r #|ind_indices idecl|) -to_extended_list_map_lift.
        relativize (to_extended_list (ind_indices idecl)).
        erewrite map_subst_let_expand_k_to_extended_list_lift.
        3:{ rw /expand_lets_ctx /expand_lets_k_ctx
              !to_extended_list_k_lift_context
              !to_extended_list_k_subst
              PCUICLiftSubst.map_subst_instance_to_extended_list_k
              !to_extended_list_k_subst to_extended_list_k_lift_context //. }
        2:{ eapply spine_subst_smash; tea.
            rw subst_instance_expand_lets_ctx.
            rw lift_context_subst_context lift_context_expand_lets_ctx
              -subst_instance_lift_context.
            rw /subst_let_expand_k -map_map_compose.
            now exact spindices. }
        rw {2}/subst_let_expand_k.
        rw map_lift0. rw /indices.
        rw !map_map_compose.
        rw Nat.add_comm.
        now rw /subst_let_expand_k. }
    }
Qed.

Lemma wf_case_branch_type' {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) :
  declared_inductive Σ ci mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := inst_case_predicate_context p in
  Σ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  forall i cdecl br,
    declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
    wf_branch cdecl br ->
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    wf_local Σ (Γ ,,, brctxty.1) ×
    Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps.
Proof.
  intros isdecl Hc wfp bc Hp ptm wfpctx.
  unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
  destruct (WfArity_build_case_predicate_type wfΣ isdecl Hc (PCUICWfUniverses.typing_wf_sort _ Hp) wfp) as [wfty _].
  set wfcpc := wf_case_predicate_context isdecl Hc wfp. simpl in wfcpc. clearbody wfcpc.
  have clipars : closed_ctx (subst_instance (puinst p) (ind_params mdecl)).
  { rw closedn_subst_instance_context.
    eapply (declared_inductive_closed_params isdecl). }
  have wfΓ : (wf_local Σ Γ).
  { now apply isType_wf_local in Hc. }
  have lenpars : #|pparams p| =
      context_assumptions (subst_instance (puinst p) (ind_params mdecl)).
  { len. rw (wf_predicate_length_pars wfp) //.
    apply (declared_minductive_ind_npars isdecl). }
  eapply isType_mkApps_Ind_smash in Hc; tea.
  2:{ rw (declared_minductive_ind_npars isdecl). now len in lenpars. }
  destruct Hc as [sppars [spargs cu]].
  intros n cdecl br nth wfbr.
  set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
  destruct (on_declared_constructor nth) as [[onind oib] [cs [nthc onc]]].
  simpl in *.
  subst brctxty.
  unfold case_branch_type, case_branch_type_gen => /=.
  rw -/(case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl).

  assert (wfargs : wf_local (Σ.1, ind_universes mdecl)
  (arities_context (ind_bodies mdecl),,, ind_params mdecl,,, cstr_args cdecl)).
  { destruct onc. apply sorts_local_ctx_All_local_env in on_cargs => //.
    eapply weaken_wf_local => //.
    eapply (wf_arities_context' onind) => //.
    apply onind.(onParams). }
  assert (wfparscd : wf_local Σ
  (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
   case_branch_context_nopars ci mdecl (puinst p) cdecl)). {
    rw -app_context_assoc.
    eapply weaken_wf_local; tea.
    eapply (@wf_local_instantiate _ _ (InductiveDecl mdecl) _ p.(puinst)) in wfargs; tea.
    2:eapply isdecl'.
    rw !subst_instance_app in wfargs.
    rw - !/(app_context _ _) in wfargs.
    rw -(app_context_nil_l (_ ,,, _)) -app_context_assoc app_context_assoc in wfargs.
    eapply substitution_wf_local in wfargs; tea.
    2:eapply subslet_inds; tea.
    rw app_context_nil_l subst_context_app in wfargs.
    rw closed_ctx_subst in wfargs => //.
    rw /case_branch_context_nopars.
    now rw subst_instance_length Nat.add_0_r in wfargs. }
  assert (wf_local Σ (Γ ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)).
  { rw /case_branch_context /case_branch_context_gen.
    eapply wf_set_binder_name.
    { eapply wf_pre_case_branch_context_gen; tea. }
    eapply substitution_wf_local; tea. eapply sppars.
    rw /cstr_branch_context.
    rw subst_instance_expand_lets_ctx.
    eapply wf_local_expand_lets => //.
    rw subst_instance_subst_context.
    rw (instantiate_inds nth cu) //. }
  split => //.
  assert (wfparsargs : wf_local Σ
    (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
      subst_context (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
        #|ind_params mdecl| (subst_instance (puinst p) (cstr_args cdecl)))). {
    rw -app_context_assoc.
    eapply weaken_wf_local; tea.
    eapply (@wf_local_instantiate _ _ (InductiveDecl mdecl) _ p.(puinst)) in wfargs; tea.
    2:eapply isdecl'.
    rw !subst_instance_app in wfargs.
    rw - !/(app_context _ _) in wfargs.
    rw -(app_context_nil_l (_ ,,, _)) -app_context_assoc app_context_assoc in wfargs.
    eapply substitution_wf_local in wfargs; tea.
    2:eapply subslet_inds; tea.
    rw app_context_nil_l subst_context_app in wfargs.
    rw closed_ctx_subst in wfargs => //.
    now rw subst_instance_length Nat.add_0_r in wfargs. }
  assert (wfbrctx : wf_local Σ (Γ ,,, pre_case_branch_context ci mdecl p.(pparams) p.(puinst) cdecl)).
  { rw /case_branch_context /case_branch_context_gen.
    eapply substitution_wf_local; tea. eapply sppars.
    eapply wf_local_expand_lets => //. }
  eapply type_mkApps.
  relativize #|cstr_args cdecl|.
  eapply weakening; tea. rw /ptm.
  eapply type_it_mkLambda_or_LetIn. tea.
  rw case_branch_context_length //.
  now rw -(wf_branch_length wfbr).
  eapply wf_arity_spine_typing_spine; tea.
  split.
  { apply isType_lift => //. rw length_app; lia.
    rw skipn_all_app //.
    eapply isType_it_mkProd_or_LetIn; tea.
    rw /bc. pcuic. }
  rw /bc.
  rw lift_it_mkProd_or_LetIn /=.
  rw -(app_nil_r (_ ++ [_])).
  eapply arity_spine_it_mkProd_or_LetIn_smash => //.
  2:constructor.
  rw /bc.
  * eapply subslet_eq_context_alpha.
  { instantiate (1 := smash_context []
    (lift_context #|case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl| 0
      (case_predicate_context' ci mdecl idecl p))).
    apply alpha_eq_smash_context, alpha_eq_lift_context.
    epose proof (wf_pre_case_predicate_context_gen (ci:=ci) wfp).
    rw /inst_case_predicate_context.
    eapply All2_trans. tc.
    eapply case_predicate_context_alpha; tea.
    destruct wfp. apply Forall2_All2 in H0. tea.
    now eapply inst_case_predicate_context_alpha_eq in wfpctx. }
  rw map_map_compose.
  fold (subst_let_expand_k (List.rev (pparams p)) (subst_instance (puinst p) (ind_params mdecl)) #|cstr_args cdecl|).
  set (indices := map (subst (inds _ _ _) _) _).
  rw /case_predicate_context' lift_context_snoc.
  rw subst_context_length subst_instance_length expand_lets_ctx_length.
  rw (smash_context_app_expand _ _ [_]).
  cbn. rw List.rev_app_distr; cbn.
  rw expand_lets_ctx_tip; cbn.
  rw /lift_decl compose_map_decl; cbn.
  eapply (subslet_eq_context_alpha_dom (Γ:=  (Γ ,,, pre_case_branch_context ci.(ci_ind) mdecl p.(pparams) p.(puinst) cdecl))).
  { eapply All2_app.
    rw /case_branch_context //.
    eapply (pre_case_branch_context_eq (ind:=ci) nth cu wfbr).
    reflexivity. }
  pose proof (on_cindices onc).
  eapply ctx_inst_impl in X0. 2: intros ??; apply unlift_TermTyp.
  assert (spindices :
  spine_subst Σ
  (Γ,,, pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl)
  (map (subst (List.rev (pparams p)) #|cstr_args cdecl|)
     (map
        (expand_lets_k (subst_instance (puinst p) (ind_params mdecl))
           #|cstr_args cdecl|) indices))
  (map (subst (List.rev (pparams p)) #|cstr_args cdecl|)
     (map
        (expand_lets_k (subst_instance (puinst p) (ind_params mdecl))
           #|cstr_args cdecl|)
        (map
           (subst
              (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
              (#|ind_params mdecl| + #|cstr_args cdecl|))
           (map (subst_instance (puinst p)) (ctx_inst_sub X0)))))
  (subst_context (List.rev (pparams p)) #|cstr_args cdecl|
     (expand_lets_k_ctx (subst_instance (puinst p) (ind_params mdecl))
        #|cstr_args cdecl|
        (subst_instance (puinst p)
           (lift_context #|cstr_args cdecl| 0 (ind_indices idecl)))))).
  { unshelve epose proof (ctx_inst_spine_subst _ X0) as sp.
    { eapply weakening_wf_local => //.
      rw -app_context_assoc. apply weaken_wf_local => //.
      eapply (wf_arities_context isdecl).
      apply (on_minductive_wf_params_indices isdecl). }
    eapply spine_subst_inst in sp; tea.
    2:{ exact (declared_inductive_wf_global_ext _ _ _ _ isdecl). }
    rw !subst_instance_app_ctx in sp.
    rw -app_context_assoc in sp.
    eapply spine_subst_subst_first in sp; tea.
    2:eapply subslet_inds; tea.
    rw app_context_length !subst_instance_length in sp.
    rw subst_context_app subst_instance_length /= Nat.add_0_r in sp.
    rw closed_ctx_subst // in sp.
    eapply spine_subst_weaken in sp. 2:eapply wfΓ. all:tea.
    rw app_context_assoc in sp.
    rw Nat.add_comm in sp; fold indices in sp.
    eapply spine_subst_expand_lets in sp.
    rw subst_context_length subst_instance_length in sp.
    eapply spine_subst_subst in sp; tea.
    2:exact sppars.
    rw expand_lets_ctx_length subst_context_length subst_instance_length in sp.
    rw /subst_context_let_expand.
    rw (closed_ctx_subst (inds _ _ _) (#|ind_params mdecl| + _)) in sp.
    { rw closedn_subst_instance_context.
      rw Nat.add_comm; apply closedn_ctx_lift.
      pose proof (declared_inductive_closed_pars_indices isdecl).
      rw closedn_ctx_app in H.
      now move/andb_and: H => []. }
    exact sp. }
  constructor.
  - rw case_branch_context_length_args //.
    rw /indices.
    eapply spine_subst_smash in spindices; tea.
    rw subst_instance_expand_lets_ctx.
    rw lift_context_subst_context lift_context_expand_lets_ctx
      -subst_instance_lift_context.
    eapply inst_subslet in spindices.
    rw /subst_let_expand_k.
    rw /indices in spindices.
    now rw map_map_compose in spindices.
  - cbn [decl_type ind_binder].
    rw lift_mkApps expand_lets_mkApps.
    rw subst_mkApps. simpl.
    rw map_subst_let_expand_k.
    rw case_branch_context_length_args //.
    eapply meta_conv.
    { eapply type_mkApps.
      { econstructor; tea. }
      eapply wf_arity_spine_typing_spine; tea.
      split. { eapply validity. econstructor; eauto. }
      replace (type_of_constructor mdecl cdecl (ci.(ci_ind), n) (puinst p))
        with (lift0 #|cstr_args cdecl| (type_of_constructor mdecl cdecl (ci.(ci_ind), n) (puinst p))).
      2:{ rw lift_closed //. eapply (declared_constructor_closed_type nth). }
      unfold type_of_constructor.
      rw onc.(cstr_eq).
      simpl.
      rw subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
      rw lift_it_mkProd_or_LetIn.
      rw closed_ctx_lift.
      { rw closed_ctx_subst //. }
      eapply arity_spine_it_mkProd_or_LetIn_smash; tea.
      + rw closed_ctx_subst.
        rw closedn_subst_instance_context.
        eapply (declared_inductive_closed_params isdecl).
        rw -[smash_context [] _](closed_ctx_lift #|cstr_args cdecl| 0).
        { now apply closedn_smash_context. }
        rw -map_rev.
        relativize #|cstr_args cdecl|.
        eapply subslet_lift; tea. eapply sppars.
        now apply pre_case_branch_context_length_args.
      + rw subst_context_length Nat.add_0_r.
        rw subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
        rw -map_rev.
        relativize #|subst_instance (puinst p) (ind_params mdecl)|.
        erewrite subst_let_expand_closed_ctx_lift.
        2:{ now rw List.length_rev context_assumptions_subst_context. }
        3:now rw subst_context_length.
        2:{ rw closed_ctx_subst => //. }
        rw subst_let_expand_it_mkProd_or_LetIn.
        rw !subst_context_length !subst_instance_length.
        rw closed_ctx_subst //.
        set (cstr_ctx := subst_context_let_expand _ _ _).
        change cstr_ctx with
          (pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
        clear cstr_ctx.
        rw -{1}(@pre_case_branch_context_length_args ci mdecl (pparams p) (puinst p) cdecl).
        rw /to_extended_list /to_extended_list_k.
        relativize (reln [] 0 (cstr_args cdecl)).
        eapply arity_spine_to_extended_list => //.
        2:{ rw -/(to_extended_list_k _ 0) /pre_case_branch_context.
            rw /expand_lets_ctx /expand_lets_k_ctx /to_extended_list !to_extended_list_k_subst
              !to_extended_list_k_lift_context to_extended_list_k_subst
              PCUICLiftSubst.map_subst_instance_to_extended_list_k //. }
        rw /pre_case_branch_context /subst_let_expand_k.
        eapply has_sort_isType with (s := subst_instance p.(puinst) (ind_sort idecl)).
        relativize #|cstr_args cdecl|.
        eapply (substitution (s := List.rev (pparams p)) (T := tSort _)); tea.
        eapply sppars.
        all:rw expand_lets_ctx_length.
        2:rw subst_context_length subst_instance_length //.
        eapply (typing_expand_lets_gen (T:=tSort _)).
        rw subst_context_length subst_instance_length.
        rw -/(to_extended_list_k _ _).
        rw subst_cstr_concl_head.
        destruct isdecl. now eapply nth_error_Some_length in H0.
        eapply type_mkApps.
        econstructor; tea.
        rw -[subst_instance _ (ind_type idecl)](lift_closed (#|ind_params mdecl| + #|cstr_args cdecl|) 0).
        rw closedn_subst_instance.
        eapply (declared_inductive_closed_type _ _ _ _ _ isdecl).
        rw (declared_inductive_type isdecl).
        rw subst_instance_it_mkProd_or_LetIn subst_instance_app
          it_mkProd_or_LetIn_app.
        have wfs : wf_sort Σ (subst_instance_sort (puinst p) (ind_sort idecl)).
          by eapply (on_inductive_sort_inst isdecl _ cu).
        have wfparinds : wf_local Σ
            (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
              subst_instance (puinst p) (ind_indices idecl)).
        { rw -app_context_assoc -subst_instance_app_ctx.
          eapply weaken_wf_local; tea.
          eapply (on_minductive_wf_params_indices_inst isdecl _ cu). }
        relativize (#|ind_params mdecl| + #|cstr_args cdecl|).
        relativize (to_extended_list_k _ #|cstr_args cdecl|).
        eapply typing_spine_to_extended_list_k_app; tea.
        eapply isType_it_mkProd_or_LetIn; tea. simpl.
        eapply isType_Sort; tea.
        2:{ len. now rw PCUICLiftSubst.map_subst_instance_to_extended_list_k. }
        2:{ now len. }
        rw subst_context_length subst_instance_length lift_it_mkProd_or_LetIn /=.
        eapply typing_spine_it_mkProd_or_LetIn_close; tea.
        3:{ reflexivity. }
        2:{ eapply isType_it_mkProd_or_LetIn; tea.
            eapply isType_Sort.
            eapply (on_inductive_sort_inst isdecl _ cu).
            relativize #|cstr_args cdecl|.
            eapply weakening_wf_local => //. now len. }
        clear spindices.
        unshelve epose proof (ctx_inst_spine_subst _ X0) as sp.
        { eapply weakening_wf_local => //.
          rw -app_context_assoc. apply weaken_wf_local => //.
          eapply (wf_arities_context isdecl).
          apply (on_minductive_wf_params_indices isdecl). }
        eapply spine_subst_inst in sp; tea.
        2:{ exact (declared_inductive_wf_global_ext _ _ _ _ isdecl). }
        rw !subst_instance_app_ctx in sp.
        rw -app_context_assoc in sp.
        eapply spine_subst_subst_first in sp; tea.
        2:eapply subslet_inds; tea.
        rw app_context_length !subst_instance_length in sp.
        rw subst_context_app subst_instance_length /= Nat.add_0_r in sp.
        rw closed_ctx_subst // in sp.
        eapply spine_subst_weaken in sp. 2:eapply wfΓ. all:tea.
        rw app_context_assoc in sp.
        rw Nat.add_comm in sp |- *; fold indices in sp |- *.
        rw subst_instance_lift_context in sp.
        rw (closed_ctx_subst _ _ (lift_context #|cstr_args cdecl| _ _)) in sp.
        rw Nat.add_comm; eapply closedn_ctx_lift => //.
        epose proof (declared_inductive_closed_pars_indices isdecl).
        rw closedn_ctx_app in H. move/andb_and: H => [].
        now rw closedn_subst_instance_context.
        exact sp. }
    { rw Nat.add_0_r.
      rw subst_cstr_concl_head.
      { destruct isdecl. now eapply nth_error_Some_length in H0. }
      rw subst_let_expand_k_mkApps. cbn. f_equal.
      rw !map_app. f_equal.
      { rw -(PCUICLiftSubst.map_subst_instance_to_extended_list_k p.(puinst)).
        erewrite map_subst_let_expand_k_to_extended_list_lift.
        2:{ eapply sppars. }
        rw !map_map_compose.
        apply map_ext => t.
        rw simpl_lift; try lia.
        rw (Nat.add_comm #|cstr_args cdecl|).
        rw subst_let_expand_k_lift //.
        len => //. len.
        { clear spindices. apply ctx_inst_length in X0.
          rw context_assumptions_rev in X0. len in X0.
           } }
      { pose proof (positive_cstr_closed_indices nth).
        rw map_map_compose.
        rw -(Nat.add_0_r #|ind_indices idecl|) -to_extended_list_map_lift.
        relativize (to_extended_list (ind_indices idecl)).
        erewrite map_subst_let_expand_k_to_extended_list_lift.
        3:{ rw /expand_lets_ctx /expand_lets_k_ctx
              !to_extended_list_k_lift_context
              !to_extended_list_k_subst
              PCUICLiftSubst.map_subst_instance_to_extended_list_k
              !to_extended_list_k_subst to_extended_list_k_lift_context //. }
        2:{ eapply spine_subst_smash; tea.
            rw subst_instance_expand_lets_ctx.
            rw lift_context_subst_context lift_context_expand_lets_ctx
              -subst_instance_lift_context.
            rw /subst_let_expand_k -map_map_compose.
            now exact spindices. }
        rw {2}/subst_let_expand_k.
        rw map_lift0. rw /indices.
        rw !map_map_compose.
        rw Nat.add_comm.
        now rw /subst_let_expand_k. }
    }
Qed.

Lemma wf_case_branches_types {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) brs :
  declared_inductive Σ ci mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := inst_case_predicate_context p in
  Σ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  wf_branches idecl brs ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  All2i (fun i cdecl br =>
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    wf_local Σ (Γ ,,, brctxty.1) ×
    Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps)
    0 (ind_ctors idecl) brs.
Proof.
  intros isdecl Hc wfp bc Hp ptm wfbrs conv.
  eapply forall_nth_error_All2i.
  now rw (Forall2_length wfbrs).
  intros n cdecl br nth nth'.
  eapply wf_case_branch_type'; tea.
  * split; auto.
  * red in wfbrs. eapply Forall2_All2 in wfbrs.
    eapply All2_nth_error in wfbrs; tea.
Qed.

Lemma wf_case_branches_types' {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) brs :
  declared_inductive Σ ci mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  Σ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  wf_branches idecl brs ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  All2i (fun i cdecl br =>
    let cstr_br_ctx := case_branch_context_nopars ci mdecl p.(puinst) cdecl in
    let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    [× wf_branch cdecl br, (* The branch context before substitution of parameters *)
      wf_local Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, cstr_br_ctx),
      wf_local Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, brctx'),
       (* The branch context after substitution of parameters *)
       wf_local Σ (Γ ,,, brctxty.1) &
       Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps])
    0 (ind_ctors idecl) brs.
Proof.
  intros isdecl Hc wfp bc Hp ptm wfbrs conv.
  destruct (WfArity_build_case_predicate_type wfΣ isdecl Hc (PCUICWfUniverses.typing_wf_sort _ Hp) wfp) as [wfty _].
  set wfcpc := wf_case_predicate_context isdecl Hc wfp. simpl in wfcpc. clearbody wfcpc.
  have clipars : closed_ctx (subst_instance (puinst p) (ind_params mdecl)).
  { rw closedn_subst_instance_context.
    eapply (declared_inductive_closed_params isdecl). }
  have wfΓ : (wf_local Σ Γ).
  { now apply isType_wf_local in Hc. }
  have lenpars : #|pparams p| =
      context_assumptions (subst_instance (puinst p) (ind_params mdecl)).
  { len. rw (wf_predicate_length_pars wfp) //.
    apply (declared_minductive_ind_npars isdecl). }
  eapply forall_nth_error_All2i.
  now rw (Forall2_length wfbrs).
  intros n cdecl br nth nth'.
  red in wfbrs. eapply Forall2_All2 in wfbrs.
  eapply All2_nth_error in wfbrs; tea.
  eapply wf_case_branch_type; tea.
  split; eauto.
Qed.

From MetaRocq.PCUIC Require Import PCUICContextSubst.

Lemma conv_betas_typed `{cf:checker_flags} (Σ : global_env_ext) (wfΣ: wf Σ) Γ Δ l t :
  isType Σ (Γ ,,, Δ) t ->
  ctx_inst Σ Γ l (List.rev Δ) ->
  Σ ;;; Γ |- mkApps (it_mkLambda_or_LetIn Δ t) l =s subst0 (mk_ctx_subst Δ l) t.
Proof.
  intros (_ & ps & tWty & _) instl.
  pose proof (wfΓ := typing_wf_local tWty).
  pose proof (ss := ctx_inst_spine_subst wfΓ instl).
  pose proof (eqsubst := mk_ctx_subst_spec' instl).
  rw eqsubst.
  apply: cumulAlgo_cumulSpec.
  apply: PCUICWellScopedCumulativity.wt_cumul_pb_ws_cumul_pb.
  constructor.
  + have?: Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : it_mkProd_or_LetIn Δ (tSort ps)
    by apply: PCUICGeneration.type_it_mkLambda_or_LetIn; eassumption.
    apply has_sort_isType with (s := ps); apply: PCUICSpine.type_mkApps; first eassumption.
    apply: typing_spine_it_mkProd_or_LetIn_close=> //=; first eassumption.
    apply: isType_it_mkProd_or_LetIn.
    exact: validity tWty.
  + apply:isType_subst; last (apply has_sort_isType with (s := ps); eassumption).
    exact: inst_subslet ss.
  + apply: PCUICCumulativity.red_conv.
    rw -eqsubst. apply: red_betas_typed; last eassumption.
    rw (ctx_inst_length instl) context_assumptions_rev //.
Qed.

Lemma ind_arity_relevant {cf : checker_flags} (Σ : global_env_ext) mdecl idecl :
  wf Σ.1 ->
  let ind_type := it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))) in
  isType Σ [] ind_type ->
  isTypeRel Σ [] ind_type rel_of_Type.
Proof.
  intros wfΣ ind_type (_ & s & Hs & _ & _).
  repeat (eexists; tea). cbn in Hs |- *.
  rw /ind_type in Hs.
  rw -it_mkProd_or_LetIn_app in Hs.
  eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs.
  apply inversion_Sort in Hs as (_ & _ & le); tea.
  apply ws_cumul_pb_Sort_inv in le.
  eapply leq_relevance; tea.
  eapply relevance_super.
Qed.


Lemma isTypeRel_cstr_type {cf : checker_flags} Σ mdecl idecl cdecl n :
  wf Σ.1 ->
  nth_error (ind_bodies mdecl) n = Some idecl ->
  (cstr_type cdecl =
        it_mkProd_or_LetIn
          (mdecl.(ind_params) ,,, cdecl.(cstr_args))
          (mkApps (tRel (#|mdecl.(ind_params) ,,, cdecl.(cstr_args)| + (#|ind_bodies mdecl| - S n)))
            (to_extended_list_k mdecl.(ind_params) #|cdecl.(cstr_args)| ++
            cdecl.(cstr_indices)))) ->
    idecl.(ind_type)
      = it_mkProd_or_LetIn mdecl.(ind_params)
          (it_mkProd_or_LetIn idecl.(ind_indices) (tSort idecl.(ind_sort))) ->
    isSortRel idecl.(ind_sort) idecl.(ind_relevance) ->
    ctx_inst Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cdecl.(cstr_args))
      cdecl.(cstr_indices)
      (List.rev (lift_context #|cdecl.(cstr_args)| 0 idecl.(ind_indices))) ->
  isType Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl) ->
  isTypeRel Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl) idecl.(ind_relevance).
Proof.
  intros wfΣ H -> e1 <- c (_ & s & Hs & _ & _).
  repeat (eexists; tea). cbn in Hs |- *.
  eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs.
  eapply PCUICValidity.inversion_mkApps in Hs as [tyapp [Happ Hsp]].
  apply inversion_Rel in Happ as (decl & wfΓ & hnth & cum); tas.
  eapply PCUICWeakeningTyp.All_local_env_nth_error_weaken in wfΓ as Hty; tea.
  rw nth_error_app_ge in hnth. lia.
  replace (#|ind_params mdecl,,, cstr_args cdecl| + (#|ind_bodies mdecl| - S n) - #|ind_params mdecl,,, cstr_args cdecl|) with (#|ind_bodies mdecl| - S n) in hnth by lia.
  pose proof (nth_error_Some_length H) as hlen. rw nth_error_rev // in H.
  eapply nth_error_arities_context in H. rw hnth in H.
  eapply PCUICSpine.typing_spine_strengthen in Hsp; tea. noconf H. clear cum hnth.
  cbn in Hsp.
  rw e1 !PCUICLiftSubst.lift_it_mkProd_or_LetIn -it_mkProd_or_LetIn_app /= in Hsp.
  eapply PCUICSpine.arity_typing_spine in Hsp as [_ leqs _]. now eapply leq_relevance; tea.
  noconf H. cbn in Hty |- *. now apply isTypeRel_isType in Hty.
Qed.

Lemma isType_of_constructor {cf : checker_flags} Σ mdecl idecl cdecl cstr u Γ :
  wf Σ.1 -> wf_local Σ Γ -> declared_constructor Σ.1 cstr mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isTypeRel Σ Γ (type_of_constructor mdecl cdecl cstr u) idecl.(ind_relevance).
Proof.
  intros wfΣ wfΓ isdecl h_cuu.
  pose proof (PCUICWeakeningEnvTyp.on_declared_constructor isdecl) as ((? & []) & ? & _ & []).
  unshelve eapply declared_constructor_to_gen in isdecl as isdeclgen; tea.
  eapply @lift_sorting_fu_it_impl with (f := fun x => _ (_ x)) (fu := fun x => x@[u]) (tu := on_ctype) => //=.
  1: apply relevance_subst.
  intro Hty.
  replace Γ with ([] ,,, Γ) by apply app_context_nil_l.
  replace (subst0 _ _) with (lift0 #|Γ| (type_of_constructor mdecl cdecl cstr u)).
  2: { rw PCUICLiftSubst.lift_closed //. eapply (PCUICClosedTyp.declared_constructor_closed_type isdecl). }
  change (tSort _@[u]) with (lift0 #|Γ| (tSort on_ctype.2.π1)@[u]).
  eapply @weakening with (Γ := []) => //.
  rw app_context_nil_l => //.
  destruct Σ as (Σ & φ).
  eapply typing_subst_instance' in Hty => //=; tea.
  change ((tSort _)@[u]) with (subst0 (inds (inductive_mind cstr.1) u (ind_bodies mdecl)) (tSort on_ctype.2.π1)@[u]).
  eapply @PCUICSubstitution.substitution with (Δ := []); tea.
  2: rw app_context_nil_l; apply Hty.
  2: { epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ _); eauto. now split. Unshelve. 2: apply isdeclgen.p1.p1. }
  eapply subslet_inds; tea. exact isdecl.
Qed.
