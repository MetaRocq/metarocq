(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst
     PCUICLiftSubst PCUICTyping PCUICSigmaCalculus
     PCUICClosed PCUICClosedConv PCUICClosedTyp PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp PCUICConfluence
     PCUICConversion PCUICContexts
     PCUICArities PCUICSpine PCUICInductives
     PCUICWellScopedCumulativity PCUICContexts PCUICWfUniverses.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.

Derive Signature for typing.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Arguments Nat.sub : simpl never.

Section Validity.
  Context `{cf : config.checker_flags}.

  Lemma isType_weaken_full : weaken_env_prop_full cumulSpec0 (lift_typing typing) (fun Σ Γ t T => isType Σ Γ T).
  Proof using Type.
    do 2 red. intros (Σ & φ) **.
    unshelve eapply weaken_env_prop_typing; cbn. 5: apply X2.
    all: assumption.
  Qed.

  Hint Resolve isType_weaken_full : pcuic.

  Lemma isType_extends (Σ : global_env) (Σ' : global_env) (φ : universes_decl) :
    wf Σ -> wf Σ' ->
    extends Σ Σ' ->
    forall Γ : context,
    forall t0 : term,
    isType (Σ, φ) Γ t0 -> isType (Σ', φ) Γ t0.
  Proof using Type.
    intros wfΣ wfΣ' ext Γ t Hty.
    eapply weaken_env_prop_typing; cbn; tas. 3: eassumption. all: assumption.
  Qed.

  Lemma isType_Sort_inv {Σ : global_env_ext} {Γ s} : wf Σ -> isType Σ Γ (tSort s) -> wf_sort Σ s.
  Proof using Type.
    intros wfΣ (_ & u & Hu & _).
    now eapply inversion_Sort in Hu as [? [? ?]].
  Qed.

  Lemma isWfArity_subst_instance_decl {Σ Γ T c decl u} :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isWfArity (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isWfArity Σ (subst_instance u Γ) (subst_instance u T).
  Proof using Type.
    destruct Σ as [Σ φ]. intros X X0 [isTy [ctx [s eq]]] X1.
    split. eapply isType_subst_instance_decl; eauto.
    exists (subst_instance u ctx), (subst_instance_sort u s).
    rewrite (subst_instance_destArity []) eq. intuition auto.
  Qed.

  Lemma isType_weakening {Σ Γ T} :
    wf Σ.1 ->
    wf_local Σ Γ ->
    isType Σ [] T ->
    isType Σ Γ T.
  Proof using Type.
    intros wfΣ wfΓ HT.
    now apply isType_weaken.
  Qed.

  Notation type_ctx := (type_local_ctx (lift_typing typing)).
  Lemma type_ctx_wf_univ Σ Γ Δ s : type_ctx Σ Γ Δ s -> wf_sort Σ s.
  Proof using Type.
    induction Δ as [|[na [b|] ty]]; simpl; auto with pcuic.
  Qed.
  Hint Resolve type_ctx_wf_univ : pcuic.

  Notation liat := ltac:(lia) (only parsing).

  Lemma eq_binder_annots_eq_ctx (Δ : context) (nas : list aname) :
    All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
    PCUICEquality.eq_context_upto_names (map2 set_binder_name nas Δ) Δ.
  Proof using Type.
    induction 1; cbn; constructor; auto.
    destruct y as [na [b|] t]; now constructor.
  Qed.

  Lemma eq_term_set_binder_name (Σ : global_env_ext) (Δ : context) T U (nas : list aname) :
    All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
    PCUICEquality.eq_term Σ Σ T U ->
    PCUICEquality.eq_term Σ Σ (it_mkProd_or_LetIn (map2 set_binder_name nas Δ) T) (it_mkProd_or_LetIn Δ U) .
  Proof using Type.
    intros a; unshelve eapply eq_binder_annots_eq_ctx in a; tea.
    induction a in T, U |- *.
    - auto.
    - rewrite /= /mkProd_or_LetIn.
      destruct r => /=; intros; eapply IHa;
      constructor; auto.
      all: reflexivity.
  Qed.

  Lemma All2_eq_binder_subst_context_inst l s k i Δ Γ :
    All2
      (fun (x : binder_annot name) (y : context_decl) =>
        eq_binder_annot x (decl_name y)) l Γ ->
    All2
      (fun (x : binder_annot name) (y : context_decl) =>
      eq_binder_annot x (decl_name y)) l
        (subst_context s k
          (subst_instance i
              (expand_lets_ctx Δ Γ))).
  Proof using Type.
    intros. eapply All2_map_right in X.
    depind X.
    * destruct Γ; [|done]. constructor.
    * destruct Γ => //.
      rewrite /expand_lets_ctx /expand_lets_k_ctx /=
        !lift_context_snoc; simpl.
      rewrite subst_context_snoc /= lift_context_length /=
        subst_instance_cons subst_context_snoc subst_instance_length
        subst_context_length lift_context_length.
        constructor. simpl. simpl in H. now noconf H.
        eapply IHX. simpl in H. now noconf H.
  Qed.

  Lemma wf_pre_case_predicate_context_gen {ci mdecl idecl} {p} :
    wf_predicate mdecl idecl p ->
    All2 (fun (x : binder_annot name) (y : context_decl) => eq_binder_annot x (decl_name y))
      (forget_types (pcontext p))
      (pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p)).
  Proof using Type.
    move=> [] hlen /Forall2_All2.
    rewrite /pre_case_predicate_context_gen /ind_predicate_context.
    intros a; depelim a.
    destruct (pcontext p); noconf H.
    cbn.
    rewrite /inst_case_context /= subst_instance_cons subst_context_snoc Nat.add_0_r /subst_decl /map_decl /=.
    constructor. cbn. apply e.
    now eapply All2_eq_binder_subst_context_inst.
  Qed.

  Lemma validity_wf_local {Σ} Γ Δ:
    All_local_rel (lift_typing typing Σ) Γ Δ ->
    ∑ xs, sorts_local_ctx (lift_typing typing) Σ Γ Δ xs.
  Proof using Type.
    induction 1.
    - exists []; cbn; auto.
    - destruct IHX as [xs Hxs].
      eexists (_ :: xs). cbn. split; auto.
      unshelve eapply lift_sorting_extract; tea.
    - destruct IHX as [xs Hxs].
      exists xs; cbn. split; auto.
  Qed.

  Import PCUICOnFreeVars.

  Theorem validity_env :
    env_prop (fun Σ Γ t T => isType Σ Γ T)
      (fun Σ Γ j => lift_sorting (fun _ T => isType Σ Γ T) (fun _ s => wf_sort Σ s) j)
      (fun Σ Γ => wf_local Σ Γ).
  Proof using Type.
    apply typing_ind_env; intros; rename_all_hyps.

    - apply lift_sorting_impl with (1 := X) => ?? [] HT //.
      apply/isType_Sort_inv.

    - assumption.

    - (* Rel *)
      destruct (All_local_env_nth_error X heq_nth_error) as (_ & s & Hs & _).
      eapply isType_lift; eauto.
      1: now apply nth_error_Some_length in heq_nth_error.
      now eapply has_sort_isType.

    - (* Universe *)
      eapply has_sort_isType with (s := Sort.super (Sort.super u)).
      constructor; auto.
      now apply wf_sort_super.

    - (* Product *)
      eapply has_sort_isType.
      apply unlift_TypUniv in X1; eapply isType_Sort_inv in X3; auto.
      econstructor; eauto.
      now apply wf_sort_product.

    - (* Lambda *)
      eapply lift_sorting_ex_it_impl_gen with X3 => // Hs.
      pose proof (lift_sorting_extract X0).
      eexists; split; constructor; eauto.

    - (* Let *)
      apply lift_sorting_it_impl_gen with X3 => // Hs.
      eapply type_Cumul.
      eapply type_LetIn; eauto.  econstructor; pcuic.
      eapply convSpec_cumulSpec, red1_cumulSpec; constructor.

    - (* Application *)
      apply lift_sorting_it_impl_gen with X3 => // Hs'.
      move: (typing_wf_sort wf Hs') => wfs.
      eapply (substitution0 (n := na) (T := tSort _)); eauto.
      apply inversion_Prod in Hs' as [na' [s1 [s2 [Hs Hle]]]]; tas.
      eapply (weakening_ws_cumul_pb (pb:=Cumul) (Γ' := []) (Γ'' := [vass na A])) in Hle; pcuic.
      simpl in Hle.
      eapply (type_ws_cumul_pb (pb:=Cumul)); eauto. pcuic.
      etransitivity; tea.
      eapply into_ws_cumul_pb => //.
      all:eauto with fvs.
      do 2 constructor.
      apply leq_sort_product.

    - (* Constant *)
      eapply declared_constant_inv in wf as Hc; eauto.
      apply lift_sorting_forget_body, lift_sorting_forget_rel in Hc.
      eapply isType_weakening; eauto.
      unshelve eapply declared_constant_to_gen in H; eauto.
      eapply isType_subst_instance_decl with (Γ:=[]); eauto. simpl.
      exact weaken_env_prop_typing.

     - (* Inductive type *)
      destruct (on_declared_inductive isdecl); pcuic.
      destruct isdecl.
      apply onArity, isTypeRel_isType in o0.
      eapply isType_weakening; eauto.
      unshelve eapply declared_minductive_to_gen in H; eauto.
      eapply isType_subst_instance_decl with (Γ:=[]); eauto.

    - (* Constructor type *)
      destruct (on_declared_constructor isdecl) as [[oni oib] [cs [declc onc]]].
      unfold type_of_constructor.
      pose proof (on_ctype onc) as Hc.
      apply isTypeRel_isType in Hc.
      eapply lift_typing_fu_impl with (f := fun t => _ (_ t)) (1 := Hc) => //= ?? Hs.
      2: now eapply relevance_subst_opt.
      eapply instantiate_minductive in Hs; eauto.
      2:(destruct isdecl as [[] ?]; eauto).
      simpl in Hs.
      eapply (weaken_ctx (Γ:=[]) Γ); eauto.
      eapply (substitution (Γ := []) (s := inds _ _ _) (Δ := [])); eauto.
      eapply subslet_inds; eauto. destruct isdecl; eauto.
      now rewrite app_context_nil_l.

    - (* Case predicate application *)
      assert (cu : consistent_instance_ext Σ (ind_universes mdecl) (puinst p)).
      { eapply (isType_mkApps_Ind_inv wf isdecl) in X7 as [parsubst [argsubst Hind]];
        repeat intuition auto. }
      eassert (ctx_inst Σ Γ _ (List.rev _)).
      { eapply ctx_inst_impl with (1 := X5); now intros t T [Hty _]. }
      clear X5; rename X6 into X5.
      unshelve epose proof (ctx_inst_spine_subst _ X5); tea.
      eapply weaken_wf_local; tea.
      now apply (on_minductive_wf_params_indices_inst isdecl _ cu).
      eapply spine_subst_smash in X6; tea.
      destruct (on_declared_inductive isdecl) as [onmind oib].
      rewrite /ptm. eapply has_sort_isType with (s := ps).
      eapply type_mkApps; eauto.
      eapply type_it_mkLambda_or_LetIn; tea.
      have typred : isType Σ Γ (it_mkProd_or_LetIn predctx (tSort ps)).
      { eapply All_local_env_app_inv in X2 as [_ onp].
        eapply validity_wf_local in onp as [xs Hs].
        eapply has_sort_isType.
        eapply type_it_mkProd_or_LetIn_sorts; tea.
        exact X3.2.π2.1. }
      have wfps : wf_sort Σ ps.
      { pcuic. }
      eapply typing_spine_strengthen; tea.
      2:{ rewrite /predctx /case_predicate_context /case_predicate_context_gen.
          eapply ws_cumul_pb_compare. 1-2:eauto with fvs.
          2:{ red.
              instantiate (1 :=
                it_mkProd_or_LetIn (pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p))
                    (tSort ps)).
            eapply PCUICEquality.eq_term_leq_term.
            eapply eq_term_set_binder_name. 2:reflexivity.
            now eapply wf_pre_case_predicate_context_gen. }
          rewrite subst_instance_app_ctx in X6.
          eapply spine_subst_smash_app_inv in X6 as [sppars spidx].
          epose proof (isType_case_predicate (puinst p) _ _ wfΓ isdecl cu wfps sppars).
          eauto with fvs. len.
          rewrite (wf_predicate_length_pars H0).
          now rewrite onmind.(onNpars). }
      eapply wf_arity_spine_typing_spine; auto.
      rewrite subst_instance_app_ctx in X6.
      eapply spine_subst_smash_app_inv in X6 as [sppars spidx].
      split; auto.
      apply (isType_case_predicate (puinst p) _ _ wfΓ isdecl cu wfps sppars).
      2:{ rewrite (wf_predicate_length_pars H0).
          rewrite context_assumptions_map.
          now rewrite onmind.(onNpars). }
      eapply arity_spine_case_predicate; tea.

    - (* Proj *)
      pose proof isdecl as isdecl'.
      eapply declared_projection_type in isdecl'; eauto.
      unshelve eapply isType_mkApps_Ind_inv in X2 as [parsubst [argsubst [sppar sparg
        lenpars lenargs cu]]]; eauto.
      2:eapply isdecl.p1.
      eapply lift_typing_fu_impl with (f := fun t => _ (_ t)) (1 := isdecl') => // ?? Hs.
      2: now eapply relevance_subst_opt.
      unshelve epose proof (isdecl_ := declared_projection_to_gen isdecl); eauto.
      eapply (typing_subst_instance_decl _ _ _ _ _ _ _ wf isdecl_.p1.p1.p1) in Hs; eauto.
      simpl in Hs.
      eapply (weaken_ctx Γ) in Hs; eauto.
      rewrite -heq_length in sppar. rewrite firstn_all in sppar.
      rewrite subst_instance_cons in Hs.
      rewrite subst_instance_smash in Hs. simpl in Hs.
      eapply spine_subst_smash in sppar => //.
      eapply (substitution (Δ := [_]) sppar) in Hs.
      simpl in Hs.
      eapply (substitution (Γ' := [_]) (s := [c]) (Δ := [])) in Hs.
      simpl in Hs. rewrite !(subst_app_simpl [c] (List.rev _)) /=. eassumption.
      constructor. constructor.
      simpl. rewrite subst_empty.
      rewrite subst_instance_mkApps subst_mkApps /=.
      rewrite [subst_instance_instance _ _](subst_instance_id_mdecl Σ u _ cu); auto.
      rewrite subst_instance_to_extended_list.
      rewrite subst_instance_smash.
      rewrite (spine_subst_subst_to_extended_list_k sppar).
      assumption.

    - (* Fix *)
      eapply isTypeRel_isType.
      eapply nth_error_all in X0; eauto.

    - (* CoFix *)
      eapply isTypeRel_isType.
      eapply nth_error_all in X0; eauto.

    - (* Primitive *)
      depelim X0; depelim X1; simp prim_type; cbn in *.
      1-3:destruct H1 as [hty hbod huniv]; eapply has_sort_isType with (s := _@[[]]); change (tSort ?s@[[]]) with (tSort s)@[[]];
          rewrite <- hty; refine (type_Const _ _ _ [] _ wfΓ H0 _); rewrite huniv //.
      set (s := sType (Universe.of_level (array_universe a))).
      destruct H1 as [hty' hbod huniv].
      eapply has_sort_isType with s.
      eapply (type_App _ _ _ _ (tSort s) (tSort s)); tea; cycle 1.
      + eapply (type_Const _ _ _ [array_universe a]) in H0; tea. rewrite hty' in H0. cbn in H0. exact H0.
        red. rewrite huniv. simpl. rtoProp; intuition eauto. eapply LevelSet.mem_spec. eapply (wfl (array_universe a, 0)). cbn. lsets.
        cbn. red. destruct check_univs => //. red. red. intros v H c. csets.
      + econstructor. 2: econstructor; eauto. 2: constructor; tas.
        all: repeat (eexists; tea; cbn).
        1,3: econstructor; eauto.
        all: apply relevance_super.

    - (* Conv *)
      now eapply has_sort_isType with (s := s).
  Qed.

End Validity.

Corollary validity {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> isType Σ Γ T.
Proof.
  intros. eapply validity_env; try eassumption.
Defined.

Lemma wf_local_validity `{cf : checker_flags} {Σ} {wfΣ : wf Σ} Γ Δ :
  wf_local Σ (Γ ,,, Δ) ->
  ∑ us, sorts_local_ctx (lift_typing typing) Σ Γ Δ us.
Proof.
  move=> wfΓΔ.
  apply: validity_wf_local.
  now apply: (All_local_env_app_inv _).2.
Qed.



(* To deprecate *)
Notation validity_term wf Ht := (validity (wfΣ:=wf) Ht).

(* This corollary relies strongly on validity to ensure
   every type in the derivation is well-typed.
   It should be used instead of the weaker [invert_type_mkApps],
   which is only used as a stepping stone to validity.
 *)
Lemma inversion_mkApps {cf} {Σ} {wfΣ :  wf Σ.1} {Γ f u T} :
  Σ ;;; Γ |- mkApps f u : T ->
  ∑ A, Σ ;;; Γ |- f : A × typing_spine Σ Γ A u T.
Proof.
  induction u in f, T |- *. simpl. intros.
  { exists T. intuition pcuic. eapply typing_spine_refl.
    now eapply validity in X. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - pose proof (validity Hf).
    eapply inversion_App in Hf as [na' [A' [B' [Hf' [Ha HA''']]]]]; tea.
    eexists _; intuition eauto.
    eapply validity in Hf'.
    econstructor; eauto with pcuic.
    constructor. all:eauto with pcuic.
    now eapply isType_apply in Hf'.
  - specialize (IHu (tApp f a) T).
    specialize (IHu Hf) as [T' [H' H'']].
    eapply inversion_App in H' as [na' [A' [B' [Hf' [Ha HA''']]]]]. 2:{ eassumption. }
    exists (tProd na' A' B'). intuition; eauto.
    eapply validity in Hf'.
    econstructor; eauto with wf.
    now eapply isType_ws_cumul_pb_refl.
    eapply isType_apply in Hf'; tea.
    eapply typing_spine_strengthen; tea.
Qed.

(** "Economical" typing rule for applications, not requiring to check the product type *)
Lemma type_App' {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t na A B u} :
  Σ;;; Γ |- t : tProd na A B ->
  Σ;;; Γ |- u : A -> Σ;;; Γ |- tApp t u : B {0 := u}.
Proof.
  intros Ht Hu.
  destruct (validity Ht) as (_ & s & Hs & _).
  eapply type_App; eauto.
Qed.

(** This principle is useful when the type [tty] is an arity (of the form [it_mkProd_or_LetIn _ (tSort _)]),
    as it avoids having to give intermediate well-typing and cumulativity proofs. *)
Lemma type_mkApps_arity {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t u tty T} :
  Σ;;; Γ |- t : tty ->
  arity_spine Σ Γ tty u T ->
  Σ;;; Γ |- mkApps t u : T.
Proof.
  intros Ht Hty.
  pose proof (validity Ht).
  eapply type_mkApps; tea.
  eapply wf_arity_spine_typing_spine; tea.
  constructor; tas.
Qed.
