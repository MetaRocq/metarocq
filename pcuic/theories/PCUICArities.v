(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses ProofIrrelevance ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICUnivSubstitutionConv
     PCUICUnivSubstitutionTyp
     PCUICCumulativity PCUICPosition PCUICEquality PCUICSigmaCalculus
     PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICClosed PCUICClosedTyp PCUICSubstitution PCUICWfUniverses
     PCUICWeakeningConv PCUICWeakeningTyp PCUICGeneration PCUICUtils PCUICContexts
     PCUICWellScopedCumulativity PCUICConversion PCUICOnFreeVars.

From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation_Properties.
From Equations Require Import Equations.

Implicit Types cf : checker_flags.

Abbreviation isWAT := (isWfArity typing).

Lemma isType_Sort {cf:checker_flags} {Σ Γ s} :
  wf_sort Σ s ->
  wf_local Σ Γ ->
  isType Σ Γ (tSort s).
Proof.
  intros wfs wfΓ.
  eapply has_sort_isType.
  econstructor; eauto.
Qed.
#[global] Hint Resolve isType_Sort : pcuic.

Definition wf_typing_spine {cf} {Σ Γ T args T'} :=
  isType Σ Γ T × typing_spine Σ Γ T args T'.

Lemma isArity_it_mkProd_or_LetIn Γ t : isArity t -> isArity (it_mkProd_or_LetIn Γ t).
Proof.
  intros isA. induction Γ using rev_ind; simpl; auto.
  rewrite it_mkProd_or_LetIn_app. simpl; auto.
  destruct x as [? [?|] ?]; simpl; auto.
Qed.

Inductive typing_spine {cf} Σ (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nil ty ty' :
    isType Σ Γ ty ->
    isType Σ Γ ty' ->
    Σ ;;; Γ ⊢ ty ≤ ty' ->
    typing_spine Σ Γ ty [] ty'

| type_spine_cons ty hd tl na A B B' :
    isType Σ Γ ty ->
    isType Σ Γ (tProd na A B) ->
    Σ ;;; Γ ⊢ ty ≤ tProd na A B ->
    Σ ;;; Γ |- hd : A ->
    typing_spine Σ Γ (subst10 hd B) tl B' ->
    typing_spine Σ Γ ty (hd :: tl) B'.

Derive Signature NoConfusion for typing_spine.

Lemma typing_spine_isType_codom {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T args U} :
  typing_spine Σ Γ T args U -> isType Σ Γ U.
Proof.
  induction 1; auto.
Qed.

Lemma subslet_inds_gen {cf} {Σ : global_env} {wfΣ : wf Σ} ind mdecl idecl :
  declared_inductive Σ ind mdecl idecl ->
  let u := abstract_instance (ind_universes mdecl) in
  subslet (Σ, ind_universes mdecl) [] (inds (inductive_mind ind) u (ind_bodies mdecl))
    (arities_context (ind_bodies mdecl)).
Proof.
  intros isdecl u.
  unfold inds.
  pose proof (proj1 isdecl) as declm'.
  apply on_declared_minductive in declm' as [oind oc]; auto.
  clear oc.
  assert (Alli (fun i x =>
  (Σ, ind_universes mdecl) ;;; [] |- tInd {| inductive_mind := inductive_mind ind; inductive_ind := i |} u : (ind_type x)) 0 (ind_bodies mdecl)).
  { apply forall_nth_error_Alli. intros.
    eapply Alli_nth_error in oind; eauto. simpl in oind.
    destruct oind. destruct onArity as (_ & s & Hs & _).
    unshelve eapply declared_inductive_to_gen in isdecl; eauto.
    eapply type_Cumul; eauto.
    econstructor; eauto. split; eauto with pcuic.
    unshelve eapply declared_minductive_from_gen; eauto with pcuic.
    eapply consistent_instance_ext_abstract_instance; eauto.
    eapply declared_inductive_wf_global_ext; eauto with pcuic.
    unshelve eapply declared_minductive_from_gen; eauto with pcuic.
    rewrite (subst_instance_ind_type_id Σ _ {| inductive_mind := inductive_mind ind; inductive_ind := i |}); eauto.
    unshelve eapply declared_inductive_from_gen; eauto with pcuic.
    reflexivity. }
  clear oind.
  revert X. clear onNpars.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4 5.
  induction l using rev_ind; simpl; first constructor.
  rewrite /subst_instance /= /map_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=.
  rewrite /= length_app /= Nat.add_1_r.
  constructor.
  - rewrite -rev_map_spec. apply IHl; try lia.
    eapply Alli_app in X; intuition auto.
  - eapply Alli_app in X as [oind Hx].
    depelim Hx. clear Hx.
    rewrite Nat.add_0_r in t.
    rewrite subst_closedn; auto.
    + eapply typecheck_closed in t as [? ?]; auto.
      destruct p as [? ?].
      now move/andb_and: i0=> [? ?].
Qed.

Section WfEnv.
  Context {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma ws_cumul_ctx_pb_vass {Γ Γ' na na' A A'} le :
    eq_binder_annot na na' ->
    Σ ⊢ Γ ≤[le] Γ' ->
    Σ ;;; Γ ⊢ A ≤[le] A' ->
    Σ ⊢ Γ ,, vass na A ≤[le] Γ' ,, vass na' A'.
  Proof using Type.
    repeat (constructor; auto).
  Qed.

  Lemma ws_cumul_ctx_pb_app {le Γ Γ' Δ Δ'} :
    #|Δ| = #|Δ'| ->
    Σ ⊢ Γ ,,, Δ ≤[le] Γ' ,,, Δ' <~>
    Σ ⊢ Γ ≤[le] Γ' × ws_cumul_ctx_pb_rel le Σ Γ Δ Δ'.
  Proof using wfΣ.
    move => hlen; split.
    - move/All2_fold_app_inv. move/(_ hlen) => [] onΓ onΔ; split => //.
      split; eauto with fvs.
    - move=> [] onΓ [_ onΔ].
      apply All2_fold_app; auto.
  Qed.


  Lemma invert_cumul_arity_l (Γ : context) (C : term) T :
    Σ;;; Γ ⊢ C ≤ T ->
    match destArity [] C with
    | Some (ctx, s) =>
      ∑ T' ctx' s',
        [× Σ ;;; Γ ⊢ T ⇝ T', (destArity [] T' = Some (ctx', s')),
          Σ ⊢ Γ ,,, smash_context [] ctx = Γ ,,, ctx' &
          leq_sort (global_ext_constraints Σ) s s']
    | None => unit
    end.
  Proof using wfΣ.
    intros CT.
    generalize (destArity_spec [] C). destruct destArity as [[ctx p]|].
    simpl. intros ->. 2:intros _; exact tt.
    revert Γ T CT.
    generalize (@le_n #|ctx|).
    generalize (#|ctx|) at 2. intros n; revert ctx.
    induction n; intros ctx Hlen Γ T HT.
    - destruct ctx; simpl in Hlen; try lia.
      eapply ws_cumul_pb_Sort_l_inv in HT as [u' [redT leqT]].
      exists (tSort u'), [], u'; split; auto.
      cbn. eapply ws_cumul_ctx_pb_refl; eauto with fvs.
    - destruct ctx using rev_ind.
      * eapply ws_cumul_pb_Sort_l_inv in HT as [u' [redT leqT]].
        exists (tSort u'), [], u'; split; auto; cbn.
        apply ws_cumul_ctx_pb_refl; eauto with fvs.
      * rewrite it_mkProd_or_LetIn_app in HT; simpl in HT.
        destruct x as [na [b|] ty]; unfold mkProd_or_LetIn in HT; simpl in *.
        + eapply ws_cumul_pb_LetIn_l_inv in HT; auto.
          unfold subst1 in HT; rewrite subst_it_mkProd_or_LetIn in HT.
          rewrite length_app /= Nat.add_1_r in Hlen.
          simpl in HT. specialize (IHn (subst_context [b] 0 ctx) ltac:(rewrite
          subst_context_length; lia) Γ T HT).
          destruct IHn as [T' [ctx' [s' [redT destT convctx leq]]]].
          clear IHctx.
          exists T', ctx', s'. split; auto.
          rewrite smash_context_app. simpl.
          now rewrite -smash_context_subst_empty.
        + eapply ws_cumul_pb_Prod_l_inv in HT; auto.
          rewrite -> length_app in Hlen.
          rewrite Nat.add_1_r in Hlen.
          destruct HT as [na' [A' [B' [redT convT HT]]]].
          specialize (IHn ctx ltac:(lia) (Γ ,, vass na' A') B').
          forward IHn. eapply ws_cumul_pb_ws_cumul_ctx; eauto.
          { apply ws_cumul_ctx_pb_vass; eauto. now symmetry.
            eapply ws_cumul_ctx_pb_refl. eauto with fvs.
            now symmetry. }
          clear IHctx.
          destruct IHn as [T' [ctx' [s' [redT' destT convctx leq]]]].
          exists (tProd na' A' T'), (ctx' ++ [vass na' A']), s'. split; auto. 2:simpl.
          -- transitivity (tProd na' A' B'); auto.
            split.
            3:eapply red_prod; [reflexivity|apply redT'].
            all:eauto with fvs.
          -- now rewrite destArity_app destT.
          -- rewrite smash_context_app /= .
            rewrite !app_context_assoc.
            assert (#|smash_context [] ctx| = #|ctx'|).
            { apply All2_fold_length in convctx.
              autorewrite with len in convctx |- *.
              simpl in convctx. simpl. lia. }
            etransitivity; tea.
            apply ws_cumul_ctx_pb_app; auto.
            split. apply ws_cumul_ctx_pb_vass; auto.
            apply ws_cumul_ctx_pb_refl; eauto with fvs.
            eapply ws_cumul_ctx_pb_app; eauto.
            eapply ws_cumul_ctx_pb_refl; eauto with fvs.
            eapply ws_cumul_ctx_pb_closed_left in convctx.
            move: convctx.
            rewrite !on_free_vars_ctx_app. autorewrite with fvs.
            move/andP => [] /andP[] -> /=; cbn; rewrite andb_true_r => onA' ->.
            rewrite shiftnP0 andb_true_r; eauto with fvs.
  Qed.

  Lemma isType_tProd {Γ} {na A B} :
    isType Σ Γ (tProd na A B) <~> (isTypeRel Σ Γ A na.(binder_relevance) × isType Σ (Γ,, vass na A) B).
  Proof.
    split; intro HH.
    - destruct HH as (_ & s & H & _).
      apply inversion_Prod in H; tas. destruct H as [s1 [s2 [HA [HB Hs]]]].
      apply lift_sorting_forget_univ in HA.
      split; pcuic.
    - destruct HH as [HA HB].
      pose proof (lift_sorting_extract HA).
      destruct HB as (_ & sB & HB & _).
      eapply has_sort_isType.
      econstructor; eassumption.
  Defined.

  Lemma type_ws_cumul_pb {pb Γ t} T {U} :
    Σ ;;; Γ |- t : T ->
    isType Σ Γ U ->
    Σ ;;; Γ ⊢ T ≤[pb] U ->
    Σ ;;; Γ |- t : U.
  Proof using Type.
    intros.
    eapply type_Cumul; tea. apply X0.2.π2.1.
    destruct pb.
    - eapply ws_cumul_pb_eq_le in X1.
      now eapply cumulAlgo_cumulSpec in X1.
    - now eapply cumulAlgo_cumulSpec.
  Qed.

  Lemma isType_tLetIn_red {Γ} (HΓ : wf_local Σ Γ) {na t A B}
    : isType Σ Γ (tLetIn na t A B) -> isType Σ Γ (B {0:=t}).
  Proof using wfΣ.
    intro HH.
    apply lift_sorting_it_impl_gen with HH => // H.
    assert (Hs := typing_wf_sort _ H).
    apply inversion_LetIn in H; tas. destruct H as (A' & Ht & HB & H).
    eapply (type_ws_cumul_pb (pb:=Cumul)) with (A' {0 := t}). eapply substitution_let in HB; eauto.
    * pcuic.
    * eapply ws_cumul_pb_Sort_r_inv in H as [s' [H H']].
      transitivity (tSort s'); eauto.
      eapply red_ws_cumul_pb.
      apply invert_red_letin in H as [H|H] => //.
      destruct H as (d' & ty' & b' & [reds ]).
      discriminate.
      repeat constructor; eauto with fvs.
  Qed.

  Lemma isType_tLetIn_dom {Γ} (HΓ : wf_local Σ Γ) {na t A B}
    : isType Σ Γ (tLetIn na t A B) -> Σ ;;; Γ |- t : A.
  Proof using wfΣ.
    intros (_ & s & H & _).
    apply inversion_LetIn in H; tas. destruct H as (A' & Ht & HB & H). now eapply unlift_TermTyp.
  Qed.

  Lemma wf_local_ass {Γ na A} :
    wf_local Σ Γ ->
    isTypeRel Σ Γ A na.(binder_relevance) ->
    wf_local Σ (Γ ,, vass na A).
  Proof using Type.
    constructor; eauto with pcuic.
  Qed.

  Lemma wf_local_def {Γ na d ty} :
    wf_local Σ Γ ->
    isTypeRel Σ Γ ty na.(binder_relevance) ->
    Σ ;;; Γ |- d : ty ->
    wf_local Σ (Γ ,, vdef na d ty).
  Proof using Type.
    constructor; eauto with pcuic.
    split; tas. apply X0.
  Qed.

  Hint Resolve wf_local_ass wf_local_def : pcuic.
  Hint Transparent snoc : pcuic.

  Lemma isType_apply {Γ na A B t} :
    isType Σ Γ (tProd na A B) ->
    Σ ;;; Γ |- t : A ->
    isType Σ Γ (B {0 := t}).
  Proof using wfΣ.
    move/isType_tProd => [hA hB] ht.
    eapply (isType_subst (Δ := [vass na A])); eauto with pcuic.
  Qed.

  Hint Resolve isType_wf_local : pcuic.

  Lemma typing_spine_letin_inv {Γ na b B T args S} :
    typing_spine Σ Γ (tLetIn na b B T) args S ->
    typing_spine Σ Γ (T {0 := b}) args S.
  Proof using wfΣ.
    intros Hsp.
    depelim Hsp.
    constructor; auto.
    eapply isType_tLetIn_red in i; eauto with pcuic.
    now eapply ws_cumul_pb_LetIn_l_inv in w.
    econstructor; eauto.
    eapply isType_tLetIn_red in i; eauto with pcuic.
    now eapply ws_cumul_pb_LetIn_l_inv in w.
  Qed.

  Lemma typing_spine_letin {Γ na b B T args S} :
    isType Σ Γ (tLetIn na b B T) ->
    typing_spine Σ Γ (T {0 := b}) args S ->
    typing_spine Σ Γ (tLetIn na b B T) args S.
  Proof using wfΣ.
    intros Hty Hsp.
    depelim Hsp.
    constructor; auto.
    - etransitivity; tea. eapply into_ws_cumul_pb.
      eapply red_cumul, red1_red, red_zeta. all:eauto with fvs.
    - econstructor; eauto.
      etransitivity; tea.
      eapply into_ws_cumul_pb.
      eapply red_cumul. eapply red1_red, red_zeta.
      all:eauto with fvs.
  Qed.

  Lemma typing_spine_weaken_concl {Γ T args S S'} :
    typing_spine Σ Γ T args S ->
    Σ ;;; Γ ⊢ S ≤ S' ->
    isType Σ Γ S' ->
    typing_spine Σ Γ T args S'.
  Proof using wfΣ.
    induction 1 in S' => cum.
    constructor; auto. transitivity ty'; auto.
    intros isType.
    econstructor; eauto.
  Qed.

  Lemma typing_spine_prod {Γ na b B T args S} :
    typing_spine Σ Γ (T {0 := b}) args S ->
    isType Σ Γ (tProd na B T) ->
    Σ ;;; Γ |- b : B ->
    typing_spine Σ Γ (tProd na B T) (b :: args) S.
  Proof using wfΣ.
    intros Hsp.
    depelim Hsp.
    econstructor; eauto with pcuic.
    - constructor; auto with pcuic.
    - intros Har.
      destruct (fst isType_tProd Har) as [? ?]; eauto using typing_wf_local.
      intros Hb.
      econstructor; eauto with pcuic.
      econstructor; revgoals; eauto with pcuic.
  Qed.

  Lemma typing_spine_WAT_concl {Γ T args S} :
    typing_spine Σ Γ T args S ->
    isType Σ Γ S.
  Proof using Type.
    induction 1; auto.
  Qed.

  Lemma typing_spine_isType_dom {Γ T args S} :
    typing_spine Σ Γ T args S ->
    isType Σ Γ T.
  Proof using Type.
    induction 1; auto.
  Qed.

  Lemma type_mkProd_or_LetIn {Γ} d {u t s} :
    lift_typing typing Σ Γ (j_decl_s d (Some u)) ->
    Σ ;;; Γ ,, d |- t : tSort s ->
    match decl_body d return Type with
    | Some b => Σ ;;; Γ |- mkProd_or_LetIn d t : tSort s
    | None => Σ ;;; Γ |- mkProd_or_LetIn d t : tSort (Sort.sort_of_product u s)
    end.
  Proof using wfΣ.
    destruct d as [na [b|] dty] => [Hd Ht|Hd Ht]; rewrite /mkProd_or_LetIn /=.
    - have wf := typing_wf_local Ht.
      depelim wf.
      eapply type_Cumul. econstructor; eauto.
      econstructor; eauto. now eapply typing_wf_sort in Ht; pcuic.
      eapply convSpec_cumulSpec, red1_cumulSpec. constructor.
    - have wf := typing_wf_local Ht.
      depelim wf; clear l.
      eapply type_Prod; eauto.
  Qed.

  Lemma type_it_mkProd_or_LetIn {Γ Γ' u t s} :
    wf_sort Σ u ->
    type_local_ctx (lift_typing typing) Σ Γ Γ' u ->
    Σ ;;; Γ ,,, Γ' |- t : tSort s ->
    Σ ;;; Γ |- it_mkProd_or_LetIn Γ' t : tSort (Sort.sort_of_product u s).
  Proof using wfΣ.
    revert Γ u s t.
    induction Γ'; simpl; auto; move=> Γ u s t wfu equ Ht.
    - eapply type_Cumul; eauto.
      econstructor; eauto using typing_wf_local with pcuic.
      eapply typing_wf_sort in Ht; auto with pcuic.
      eapply cumul_Sort. eapply leq_sort_product.
    - specialize (IHΓ' Γ  u (Sort.sort_of_product u s)); auto.
      unfold app_context in Ht.
      eapply type_Cumul.
      eapply IHΓ'; auto.
      destruct a as [na [b|] ty]; intuition auto.
      destruct a as [na [b|] ty]; cbn; destruct equ as (? & Hdecl).
      { apply typing_wf_local in Ht as XX. inversion XX; subst.
        pose proof (lift_sorting_extract Hdecl).
        eapply (type_mkProd_or_LetIn {| decl_body := Some b |}); eauto.
        eapply type_Cumul; eauto.
        econstructor; eauto with pcuic.
        eapply cumul_Sort. eapply leq_sort_product. }
      eapply (type_mkProd_or_LetIn {| decl_body := None |}) => /=; eauto.
      econstructor; eauto with pcuic.
      eapply typing_wf_local in Ht.
      depelim Ht; eapply All_local_env_app_inv in Ht; intuition auto.
      now rewrite sort_of_product_twice.
  Qed.

  Fixpoint sort_of_products us s :=
    match us with
    | [] => s
    | u :: us => sort_of_products us (Sort.sort_of_product u s)
    end.

  Lemma leq_sort_sort_of_products_mon {u u' v v'} :
    Forall2 (leq_sort Σ) u u' ->
    leq_sort Σ v v' ->
    leq_sort Σ (sort_of_products u v) (sort_of_products u' v').
  Proof using Type.
    intros hu; induction hu in v, v' |- *; simpl; auto with pcuic.
    intros lev. eapply IHhu.
    eapply leq_sort_product_mon => //.
  Qed.

  Lemma type_it_mkProd_or_LetIn_sorts {Γ Γ' us t s} :
    sorts_local_ctx (lift_typing typing) Σ Γ Γ' us ->
    Σ ;;; Γ ,,, Γ' |- t : tSort s ->
    Σ ;;; Γ |- it_mkProd_or_LetIn Γ' t : tSort (sort_of_products us s).
  Proof using wfΣ.
    revert Γ us s t.
    induction Γ'; simpl; auto; move=> Γ us s t equ Ht.
    - destruct us => //.
    - destruct a as [na [b|] ty]; intuition auto.
      * eapply IHΓ'; eauto.
        pose proof (lift_sorting_extract b0).
        eapply (type_mkProd_or_LetIn {| decl_body := Some b |}); eauto.
      * destruct us => //. destruct equ.
        simpl.
        eapply IHΓ'; eauto.
        apply (type_mkProd_or_LetIn {| decl_body := None |}) => /=; eauto.
  Qed.

  Lemma isType_it_mkProd_or_LetIn {Γ Γ' us t} :
    sorts_local_ctx (lift_typing typing) Σ Γ Γ' us ->
    isType Σ (Γ ,,, Γ') t ->
    isType Σ Γ (it_mkProd_or_LetIn Γ' t).
  Proof using cf Σ wfΣ.
    move=> equs [_ [s [ttyp _]]]; eapply @has_sort_isType with (s := sort_of_products us s).
    apply: type_it_mkProd_or_LetIn_sorts=> //.
  Qed.

  Hint Extern 4 (_ ;;; _ |- _ <= _) => reflexivity : pcuic.
  Ltac pcuic := eauto 5 with pcuic.

  Lemma subslet_app_closed {Γ s s' Δ Δ'} :
    subslet Σ Γ s Δ ->
    subslet Σ Γ s' Δ' ->
    closed_ctx Δ ->
    subslet Σ Γ (s ++ s') (Δ' ,,, Δ).
  Proof using Type.
    induction 1 in s', Δ'; simpl; auto; move=> sub' => /andb_and [clctx clt];
    try constructor; auto.
    - pose proof (subslet_length X). rewrite Nat.add_0_r in clt.
      rewrite /= -H in clt.
      rewrite subst_app_simpl /= (subst_closedn s') //.
    - pose proof (subslet_length X). rewrite Nat.add_0_r in clt.
      rewrite /= -H in clt. move/andb_and: clt => [clt clT].
      replace (subst0 s t) with (subst0 (s ++ s') t).
      + constructor; auto.
        rewrite !subst_app_simpl /= !(subst_closedn s') //.
      + rewrite !subst_app_simpl /= !(subst_closedn s') //.
  Qed.

  Hint Constructors subslet : core pcuic.

  Lemma subslet_app_inv {Γ Δ Δ' s} :
    subslet Σ Γ s (Δ ,,, Δ') ->
    subslet Σ Γ (skipn #|Δ'| s) Δ *
    subslet Σ Γ (firstn #|Δ'| s) (subst_context (skipn #|Δ'| s) 0 Δ').
  Proof using Type.
    intros sub. split.
    - induction Δ' in Δ, s, sub |- *; simpl; first by rewrite skipn_0.
      depelim sub; rewrite skipn_S; auto.
    - induction Δ' in Δ, s, sub |- *; simpl; first by constructor.
      destruct s; depelim sub.
      * rewrite subst_context_snoc. constructor; eauto.
        rewrite skipn_S Nat.add_0_r /=.
        assert(#|Δ'| = #|firstn #|Δ'| s|).
        { pose proof (subslet_length sub).
          rewrite app_context_length in H.
          rewrite firstn_length_le; lia. }
        rewrite {3}H.
        rewrite -subst_app_simpl.
        now rewrite firstn_skipn.
      * rewrite subst_context_snoc.
        rewrite skipn_S Nat.add_0_r /=.
        rewrite /subst_decl /map_decl /=.
        specialize (IHΔ' _ _ sub).
        epose proof (cons_let_def _ _ _ _ _ (subst (skipn #|Δ'| s0) #|Δ'| t0)
        (subst (skipn #|Δ'| s0) #|Δ'| T) IHΔ').
        assert(#|Δ'| = #|firstn #|Δ'| s0|).
        { pose proof (subslet_length sub).
          rewrite app_context_length in H.
          rewrite firstn_length_le; lia. }
        rewrite {3 6}H in X.
        rewrite - !subst_app_simpl in X.
        rewrite !firstn_skipn in X.
        specialize (X t1).
        rewrite {3}H in X.
        now rewrite - !subst_app_simpl firstn_skipn in X.
  Qed.

  Lemma subslet_inds {ind u mdecl idecl} :
    declared_inductive Σ.1 ind mdecl idecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    subslet Σ [] (inds (inductive_mind ind) u (ind_bodies mdecl))
      (subst_instance u (arities_context (ind_bodies mdecl))).
  Proof using wfΣ.
    intros isdecl univs.
    unfold inds.
    pose proof (proj1 isdecl) as declm.
    apply on_declared_minductive in declm as [oind oc]; auto.
    clear oc.
    assert (Alli (fun i x =>
      Σ ;;; [] |- tInd {| inductive_mind := inductive_mind ind; inductive_ind := i |} u : subst_instance u (ind_type x)) 0 (ind_bodies mdecl)).
    { apply forall_nth_error_Alli.
      econstructor; eauto. split; eauto. simpl. eapply isdecl. }
    clear oind.
    revert X. clear onNpars.
    generalize (le_n #|ind_bodies mdecl|).
    generalize (ind_bodies mdecl) at 1 3 4 5.
    induction l using rev_ind; simpl; first constructor.
    rewrite /subst_instance /= /map_context.
    simpl. rewrite /arities_context rev_map_spec /=.
    rewrite map_app /= rev_app_distr /=.
    rewrite {1}/map_decl /= length_app /= Nat.add_1_r.
    constructor.
    - rewrite -rev_map_spec. apply IHl; try lia.
      eapply Alli_app in X; intuition auto.
    - eapply Alli_app in X as [oind Hx].
      depelim Hx. clear Hx.
      rewrite Nat.add_0_r in t.
      rewrite subst_closedn; auto.
      + now eapply type_closed in t.
  Qed.

  Lemma weaken_subslet {s Δ Γ} :
    wf_local Σ Γ ->
    subslet Σ [] s Δ -> subslet Σ Γ s Δ.
  Proof using wfΣ.
    intros wfΔ.
    induction 1; constructor; auto.
    + eapply (weaken_ctx (Γ:=[]) Γ); eauto.
    + eapply (weaken_ctx (Γ:=[]) Γ); eauto.
  Qed.

  Set Default Goal Selector "1".

  Lemma isType_substitution_it_mkProd_or_LetIn {Γ Δ T s} :
    subslet Σ Γ s Δ ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    isType Σ Γ (subst0 s T).
  Proof using wfΣ.
    intros sub HT.
    apply lift_sorting_it_impl_gen with HT => // Hs.
    set (s' := HT.2.π1) in *; clearbody s'. clear HT.
    revert Γ s sub Hs.
    generalize (le_n #|Δ|).
    generalize #|Δ| at 2.
    induction n in Δ, T |- *.
    - destruct Δ; simpl; intros; try (exfalso; lia).
      depelim sub.
      rewrite subst_empty; auto.
    - destruct Δ using rev_ind; try clear IHΔ.
      + intros Hn Γ s sub; now depelim sub; rewrite subst_empty.
      + rewrite length_app Nat.add_1_r /= => Hn Γ s sub.
      pose proof (subslet_length sub). rewrite length_app /= Nat.add_1_r in H.
      have Hl : #|l| = #|firstn #|l| s|.
      { rewrite firstn_length_le; lia. }
      destruct x as [na [b|] ty] => /=;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.

      intros Hs.
      assert (wfs' := typing_wf_sort wfΣ Hs).
      eapply inversion_LetIn in Hs as (T' & wfT' & HT' & hlt); auto.
      eapply substitution_let in HT'; auto.
      eapply ws_cumul_pb_LetIn_l_inv in hlt; auto.
      pose proof (subslet_app_inv sub) as [subl subr].
      depelim subl. depelim subl. rewrite subst_empty in H0. rewrite H0 in subr.
      specialize (IHn (subst_context [b] 0 l) (subst [b] #|l| T) ltac:(rewrite subst_context_length; lia)).
      specialize (IHn _ _ subr).
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in HT'.
      rewrite !subst_empty in t0.
      forward IHn.
      eapply type_Cumul. eapply HT'. econstructor; intuition eauto using typing_wf_local with pcuic.
      eapply (cumulAlgo_cumulSpec _ (pb:=Cumul)), hlt. rewrite {2}Hl in IHn.
      now rewrite -subst_app_simpl -H0 firstn_skipn in IHn.

      intros Hs.
      assert (wfs' := typing_wf_sort wfΣ Hs).
      eapply inversion_Prod in Hs as (s1 & s2 & wfty & Hty & hlt); auto.
      pose proof (subslet_app_inv sub) as [subl subr].
      depelim subl; depelim subl. rewrite subst_empty in t0. rewrite H0 in subr.
      epose proof (substitution0 Hty t0).
      specialize (IHn (subst_context [t] 0 l) (subst [t] #|l| T)).
      forward IHn. rewrite subst_context_length; lia.
      specialize (IHn _ _ subr).
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in X.
      forward IHn.
      eapply type_Cumul. simpl in X. eapply X.
      econstructor; eauto with pcuic.
      eapply ws_cumul_pb_Sort_inv in hlt. eapply cumul_Sort.
      transitivity (Sort.sort_of_product s1 s2).
      eapply leq_sort_product. auto.
      rewrite {2}Hl in IHn.
      now rewrite -subst_app_simpl -H0 firstn_skipn in IHn.
  Qed.

  Lemma on_minductive_wf_params {ind mdecl} {u} :
    declared_minductive Σ.1 ind mdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ (subst_instance u (ind_params mdecl)).
  Proof using wfΣ.
    intros.
    unshelve epose proof (declared_minductive_to_gen H); eauto with pcuic.
    eapply (wf_local_instantiate (decl := InductiveDecl mdecl)); eauto.
    eapply on_declared_minductive in H; auto.
    now apply onParams in H.
  Qed.

  Lemma it_mkProd_or_LetIn_wf_local {Γ Δ T U} :
    Σ ;;; Γ |- it_mkProd_or_LetIn Δ T : U -> wf_local Σ (Γ ,,, Δ).
  Proof using wfΣ.
    move: Γ T U.
    induction Δ using rev_ind => Γ T U.
    + simpl. intros. now eapply typing_wf_local in X.
    + rewrite it_mkProd_or_LetIn_app.
      destruct x as [na [b|] ty]; cbn; move=> H.
      * apply inversion_LetIn in H as (A & wfty & HT & hlt); auto.
        eapply All_local_env_app. 1: eapply unlift_TermTyp in wfty; pcuic.
        eapply All_local_env_app. repeat (constructor; tea).
        apply IHΔ in HT.
        eapply All_local_env_app_inv in HT. intuition auto.
        eapply All_local_env_impl; eauto. simpl. intros.
        now rewrite app_context_assoc.
      * apply inversion_Prod in H as (s1 & s2 & wfty & HT & hlt); auto.
        eapply All_local_env_app. 1: eapply unlift_TypUniv in wfty; cbn in wfty; pcuic.
        eapply All_local_env_app. apply lift_sorting_forget_univ in wfty. repeat (constructor; tea).
        apply IHΔ in HT.
        eapply All_local_env_app_inv in HT. intuition auto.
        eapply All_local_env_impl; eauto. simpl. intros.
        now rewrite app_context_assoc.
  Qed.

  Lemma isType_it_mkProd_or_LetIn_wf_local {Γ Δ T} :
    isType Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_local Σ (Γ ,,, Δ).
  Proof using wfΣ.
    intros (_ & s & Hs & _).
    now eapply it_mkProd_or_LetIn_wf_local in Hs.
  Qed.

  Lemma isType_weaken {Γ T} :
    wf_local Σ Γ ->
    isType Σ [] T ->
    isType Σ Γ T.
  Proof using wfΣ.
    intros wfΓ HT.
    apply lift_typing_impl with (1 := HT) => ?? hs.
    eapply (weaken_ctx Γ) in hs; eauto.
  Qed.

  Lemma subst_telescope_subst_instance u s k Γ :
    subst_telescope (map (subst_instance u) s) k
      (subst_instance u Γ) =
    subst_instance u (subst_telescope s k Γ).
  Proof using Type.
    rewrite /subst_telescope /subst_instance /= /subst_instance_context /map_context.
    rewrite map_mapi mapi_map. apply mapi_ext.
    intros. rewrite !compose_map_decl; apply map_decl_ext => ?.
    now rewrite -subst_instance_subst.
  Qed.
End WfEnv.
