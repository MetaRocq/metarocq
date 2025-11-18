(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 CRelationClasses ProofIrrelevance.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICSigmaCalculus
     PCUICUnivSubst PCUICTyping PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICCumulativity PCUICPosition PCUICEquality
     PCUICInversion PCUICCumulativity PCUICReduction
     PCUICCasesContexts
     PCUICConfluence PCUICParallelReductionConfluence PCUICConversion PCUICContextConversion
     PCUICContextConversionTyp
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICClosed PCUICClosedTyp PCUICSubstitution PCUICContextSubst
     PCUICWellScopedCumulativity
     PCUICWeakeningConv PCUICWeakeningTyp PCUICGeneration PCUICUtils PCUICContexts
     PCUICArities.

From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation_Properties.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Derive Signature for ctx_inst.

Notation ctx_inst Σ := (ctx_inst (typing Σ)).

Ltac splits := repeat split.

Notation spnil isty isty' w := (type_spine_nil _ isty isty' w).
Arguments type_spine_cons {cf Σ Γ ty hd tl na A B B'} : rename.

Notation spcons isty isty' w tyhd sp := (@type_spine_cons _ _ _ _ _ _ _ _ _ _ isty isty' w tyhd sp).

Lemma typing_spine_eq {cf:checker_flags} Σ Γ ty s s' ty' :
  s = s' ->
  typing_spine Σ Γ ty s ty' ->
  typing_spine Σ Γ ty s' ty'.
Proof. now intros ->. Qed.

Lemma All2_fold_mapi_right P (Γ Δ : context) g :
  All2_fold (fun Γ Δ d d' =>
    P Γ (mapi_context g Δ) d (map_decl (g #|Γ|) d')) Γ Δ
  -> All2_fold P Γ (mapi_context g Δ).
Proof.
  induction 1; simpl; constructor; intuition auto;
  now rewrite <-(All2_fold_length X).
Qed.

Import PCUICOnFreeVars.

Lemma weakening_closed_red {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' Γ'' M N} :
  Σ ;;; Γ ,,, Γ' ⊢ M ⇝ N ->
  is_closed_context (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ⊢ lift #|Γ''| #|Γ'| M ⇝ lift #|Γ''| #|Γ'| N.
Proof.
  intros onf onctx.
  eapply into_closed_red.
  - destruct onf. eapply weakening_red; tea.
    now rewrite on_free_vars_ctx_on_ctx_free_vars.
  - eapply is_closed_context_lift; eauto with fvs.
  - eapply is_open_term_lift; eauto with fvs.
Qed.

Lemma subslet_eq_context_alpha {cf} {Σ Γ s Δ Δ'} :
  eq_context_upto_names Δ Δ' →
  subslet Σ Γ s Δ →
  subslet Σ Γ s Δ'.
Proof.
  intros eq subs.
  induction subs in Δ', eq |- *; depelim eq; try constructor.
  * depelim e; constructor; auto.
  * depelim e; subst; constructor; auto.
Qed.

Lemma wf_local_alpha {cf} {Σ} {wfΣ : wf Σ} Γ Γ' : eq_context_upto_names Γ Γ' ->
  wf_local Σ Γ ->
  wf_local Σ Γ'.
Proof.
  induction 1; intros h; depelim h; try constructor; auto.
  all:depelim r; constructor; subst; auto.
  all: rewrite -e.
  all: eapply lift_typing_impl; tea; intros t' T Hty.
  all: eapply context_conversion; eauto.
  all: now apply eq_context_upto_names_conv_context.
Qed.

Lemma subslet_eq_context_alpha_dom {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s Δ} :
  eq_context_upto_names Γ Γ' →
  subslet Σ Γ s Δ →
  subslet Σ Γ' s Δ.
Proof.
  intros eq subs.
  induction subs in Γ', eq |- *; try constructor.
  * now apply IHsubs.
  * eapply context_conversion; tea.
    eapply wf_local_alpha; tea. eapply typing_wf_local in t0. exact t0.
    now eapply eq_context_upto_names_conv_context.
  * now eapply IHsubs.
  * eapply context_conversion; tea.
    eapply wf_local_alpha; tea. eapply typing_wf_local in t0. exact t0.
    now eapply eq_context_upto_names_conv_context.
Qed.


Lemma subslet_app {cf:checker_flags} Σ Γ s s' Δ Δ' :
  subslet Σ Γ s (subst_context s' 0 Δ) ->
  subslet Σ Γ s' Δ' ->
  subslet Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
induction Δ in s, s', Δ' |- *; simpl; auto; move=> sub'.
- depelim sub'. auto.
- rewrite subst_context_snoc in sub' => sub''.
  move:(subslet_length sub') => /=.
  rewrite /snoc /= subst_context_length /= => Hlen.
  destruct a as [na [b|] ty].
  * depelim sub'; simpl in t0, Hlen.
    rewrite -subst_app_simpl' /=. lia.
    constructor. eauto.
    now rewrite - !subst_app_simpl' in t0; try lia.
  * rewrite /subst_decl /map_decl /snoc /= in sub'.
    depelim sub'; simpl in Hlen.
    rewrite - !subst_app_simpl' in t0; try lia.
    simpl; constructor; eauto.
Qed.

Lemma subslet_skipn {cf:checker_flags} Σ Γ s Δ n :
  subslet Σ Γ s Δ ->
  subslet Σ Γ (skipn n s) (skipn n Δ).
Proof.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    * rewrite !skipn_nil. constructor.
    * rewrite !skipn_S. auto.
    * rewrite !skipn_S. auto.
Qed.

Lemma untyped_subslet_skipn Γ s Δ n :
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ (skipn n s) (skipn n Δ).
Proof.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    * rewrite !skipn_nil. constructor.
    * rewrite !skipn_S. auto.
    * rewrite !skipn_S. auto.
Qed.

Lemma untyped_subslet_eq_subst Γ s s' Δ :
  untyped_subslet Γ s Δ -> s = s' ->
  untyped_subslet Γ s' Δ.
Proof. now intros H ->. Qed.

Lemma context_subst_app_inv {ctx ctx' : context} {args s : list term} :
  context_subst (subst_context (skipn #|ctx| s) 0 ctx)
    (skipn (context_assumptions ctx') args)
    (firstn #|ctx| s)
  × context_subst ctx' (firstn (context_assumptions ctx') args)	(skipn #|ctx| s) ->
  context_subst (ctx ++ ctx') args s.
Proof.
  move=> [Hl Hr].
  rewrite -(firstn_skipn (context_assumptions ctx') args).
  assert (lenctx' : context_assumptions ctx' + context_assumptions ctx = #|args|).
  { assert (lenctx'' : context_assumptions ctx' <= #|args|).
    move: (context_subst_assumptions_length Hr).
    rewrite length_firstn; lia.
    move: (context_subst_assumptions_length Hr).
    move: (context_subst_assumptions_length Hl).
    rewrite length_firstn length_skipn; try lia.
    intros H1 H2. rewrite context_assumptions_subst in H1. lia. }
  move: args s ctx' lenctx' Hl Hr.
  induction ctx => args s ctx' lenctx' Hl Hr.
  - simpl in *. depelim Hl. rewrite H app_nil_r. now rewrite skipn_0 in Hr.
  - simpl in *. destruct s as [|u s];
    simpl in *; rewrite subst_context_snoc0 in Hl; depelim Hl.
    simpl in H. noconf H.
    * destruct a as [na [b|] ty]; simpl in *; noconf H.
      rewrite skipn_S in Hl, Hr. destruct args using rev_case. rewrite skipn_nil in H0.
      apply (f_equal (@length _)) in H0. simpl in H0. autorewrite with len in H0.
      simpl in H0; lia. rewrite H0.
      rewrite skipn_app in H0.
      rewrite length_app /= in lenctx'.
      specialize (IHctx args s ctx'). forward IHctx by lia.
      assert (context_assumptions ctx' - #|args| = 0) by lia.
      rewrite H skipn_0 in H0. apply app_inj_tail in H0 as [Ha xu]. subst x.
      rewrite -Ha.
      rewrite -Ha in Hl. specialize (IHctx Hl).
      rewrite firstn_app in Hr |- *.
      rewrite H [firstn _ [u]]firstn_0 // app_nil_r in Hr |- *.
      specialize (IHctx Hr). rewrite app_assoc.
      now econstructor.
    * rewrite skipn_S in Hl, Hr, H.
      destruct a as [na' [b'|] ty']; simpl in *; noconf H.
      pose proof (context_subst_length Hl). rewrite subst_context_length in H.
      rewrite {3}H -subst_app_simpl [firstn #|ctx| _ ++ _]firstn_skipn. constructor.
      apply IHctx => //.
Qed.

Lemma ctx_inst_inst {cf:checker_flags} Σ ext u Γ i Δ  :
  wf_global_ext Σ.1 ext ->
  ctx_inst (Σ.1, ext) Γ i Δ ->
  consistent_instance_ext Σ ext u ->
  ctx_inst Σ (subst_instance u Γ)
    (map (subst_instance u) i)
    (subst_instance u Δ).
Proof.
  intros wfext ctxi cu.
  induction ctxi; simpl; constructor; auto.
  * destruct Σ as [Σ univs].
    eapply (typing_subst_instance'' Σ); eauto.
  * rewrite (subst_telescope_subst_instance u [i]).
    apply IHctxi.
  * rewrite (subst_telescope_subst_instance u [b]).
    apply IHctxi.
Qed.

Record spine_subst {cf:checker_flags} Σ Γ inst s (Δ : context) := mkSpineSubst {
  spine_dom_wf : wf_local Σ Γ;
  spine_codom_wf : wf_local Σ (Γ ,,, Δ);
  inst_ctx_subst :> context_subst Δ inst s;
  inst_subslet :> subslet Σ Γ s Δ }.
Arguments inst_ctx_subst {cf Σ Γ inst s Δ}.
Arguments inst_subslet {cf Σ Γ inst s Δ}.
#[global]
Hint Resolve inst_ctx_subst inst_subslet : pcuic.

Lemma spine_subst_eq {cf:checker_flags} {Σ Γ inst s Δ Δ'} :
  spine_subst Σ Γ inst s Δ ->
  Δ = Δ' ->
  spine_subst Σ Γ inst s Δ'.
Proof.
  now intros sp ->.
Qed.

Lemma spine_subst_inj_subst {cf:checker_flags} {Σ Γ inst s s' Δ} :
  spine_subst Σ Γ inst s Δ ->
  spine_subst Σ Γ inst s' Δ ->
  s = s'.
Proof.
  intros [_ _ c _] [_ _ c' _].
  induction c in s', c' |- *; depelim c'; simpl; auto.
  apply app_inj_tail in H as [-> ->].
  f_equal; eauto.
  specialize (IHc _ c'). now subst.
Qed.

Lemma make_context_subst_skipn {Γ args s s'} :
  make_context_subst Γ args s = Some s' ->
  skipn #|Γ| s' = s.
Proof.
  induction Γ in args, s, s' |- *.
  - destruct args; simpl; auto.
    + now intros [= ->].
    + now discriminate.
  - destruct a as [na [b|] ty]; simpl.
    + intros H.
      specialize (IHΓ _ _ _ H).
      now eapply skipn_n_Sn.
    + destruct args; try discriminate.
      intros Hsub.
      specialize (IHΓ _ _ _ Hsub).
      now eapply skipn_n_Sn.
Qed.

Inductive arity_spine {cf : checker_flags} (Σ : global_env_ext) (Γ : context) :
  term -> list term -> term -> Type :=
| arity_spine_nil ty : arity_spine Σ Γ ty [] ty
| arity_spine_conv ty ty' : isType Σ Γ ty' ->
  Σ ;;; Γ ⊢ ty ≤ ty' -> arity_spine Σ Γ ty [] ty'
| arity_spine_def : forall (tl : list term)
                      (na : aname) (A a B B' : term),
                    arity_spine Σ Γ (B {0 := a}) tl B' ->
                    arity_spine Σ Γ (tLetIn na a A B) tl B'
| arity_spine_ass : forall (hd : term) (tl : list term)
                      (na : aname) (A B B' : term),
                    Σ;;; Γ |- hd : A ->
                    arity_spine Σ Γ (B {0 := hd}) tl B' ->
                    arity_spine Σ Γ (tProd na A B) (hd :: tl) B'.

Derive Signature for arity_spine.

Record wf_arity_spine {cf:checker_flags} Σ Γ T args T' :=
{ wf_arity_spine_wf : isType Σ Γ T;
  wf_arity_spine_spine : arity_spine Σ Γ T args T' }.

#[global] Hint Resolve isType_wf_local : pcuic.

Lemma context_subst_subst Δ inst0 s Γ inst s'  :
  context_subst Δ inst0 s ->
  context_subst (subst_context s 0 Γ) inst s' ->
  context_subst (Δ ,,, Γ) (inst0 ++ inst) (s' ++ s).
Proof.
induction Γ in inst, s' |- *.
+ intros HΔ Hi. depelim Hi.
  now rewrite app_nil_r.
+ intros H' Hsub.
  rewrite subst_context_snoc0 in Hsub.
  destruct a as [na [b|] ty];
  depelim Hsub.
  - specialize (IHΓ _ _ H' Hsub).
    assert(#|Γ| = #|s0|) as ->.
    { apply context_subst_length in Hsub.
      now rewrite subst_context_length in Hsub. }
    rewrite -(subst_app_simpl s0 s 0 b).
    simpl. now constructor.
  - specialize (IHΓ _ _ H' Hsub).
    assert(#|Γ| = #|s0|).
    { apply context_subst_length in Hsub.
      now rewrite subst_context_length in Hsub. }
    rewrite app_assoc /=. now constructor.
Qed.

Section WfEnv.
  Context {cf} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma typing_spine_strengthen {Γ T args U} :
    typing_spine Σ Γ T args U ->
    forall T',
    isType Σ Γ T' ->
    Σ ;;; Γ ⊢ T' ≤ T ->
    typing_spine Σ Γ T' args U.
  Proof using wfΣ.
    induction 1 in |- *; intros T' isTy redT.
    - constructor; eauto. transitivity ty; auto.
    - specialize (IHX (B {0 := hd})).
      pose proof (isType_apply i0 t); tea.
      do 2 forward IHX by pcuic.
      eapply type_spine_cons; eauto.
      etransitivity; eauto.
  Qed.

  Lemma typing_spine_refl {Γ T} :
    isType Σ Γ T ->
    typing_spine Σ Γ T [] T.
  Proof using wfΣ.
    intros isty. constructor; auto.
    eauto with pcuic.
  Qed.

  Lemma inversion_mkApps_direct {Γ f u T} :
    isType Σ Γ T ->
    Σ ;;; Γ |- mkApps f u : T ->
    ∑ A s', Σ ;;; Γ |- f : A × Σ ;;; Γ |- A : tSort s' × typing_spine Σ Γ A u T.
  Proof using wfΣ.
    induction u in f, T |- *. simpl. intros.
    { destruct X as (_ & s & X & _). exists T, s. intuition pcuic. eapply typing_spine_refl. eapply has_sort_isType; eauto. }
    intros HT Hf. simpl in Hf.
    destruct u. simpl in Hf, IHu.
    - edestruct @inversion_App_size with (H := Hf) as (na' & A' & B' & s & Hf' & Ha & HA & _ & _ & _ & HA'''); tea.
      eexists _, _; intuition eauto.
      econstructor; eauto with pcuic.
      eapply isType_ws_cumul_pb_refl; eapply has_sort_isType; eauto.
      econstructor. all:eauto with pcuic.

      eapply inversion_Prod in HA as (? & ? & ? & ? & ?); tea.
      eapply isType_subst. econstructor. econstructor. rewrite subst_empty; eauto.
      econstructor; cbn; eauto.
    - specialize (IHu (tApp f a) T).
      unshelve epose proof (IHu _ Hf) as [T' [s' [H' [H''' H'']]]]; tea.
      edestruct @inversion_App_size with (H := H') as (na' & A' & B' & s & Hf' & Ha & HA & _ & _ & _ & HA'''); tea.
      exists (tProd na' A' B'). exists s. intuition; eauto.
      econstructor; eauto with wf.
      1,2: pcuic. 1:eapply isType_ws_cumul_pb_refl; pcuic.


      eapply typing_spine_strengthen; tea.

      eapply inversion_Prod in HA as (? & ? & ? & ? & ?); tea.
      eapply isType_subst. econstructor. econstructor. rewrite subst_empty; eauto.
      econstructor; cbn; eauto.
  Qed.

  Lemma subst_type_local_ctx {Γ Γ' Δ Δ' s ctxs} :
    wf_local Σ (Γ ,,, Δ ,,, Γ') ->
    type_local_ctx (lift_typing typing) Σ (Γ ,,, Δ ,,, Γ') Δ' ctxs ->
    subslet Σ Γ s Δ ->
    type_local_ctx (lift_typing typing) Σ (Γ ,,, subst_context s 0 Γ') (subst_context s #|Γ'| Δ') ctxs.
  Proof using wfΣ.
    induction Δ' in Γ' |- *; simpl; auto.
    destruct a as [na [b|] ty];
      rewrite subst_context_snoc /= /subst_decl /map_decl /=;
      simpl; intuition auto.
    2: rename b into b0.
    all: rewrite -app_context_assoc in b0.
    all: eapply lift_typing_substitution in b0; tea.
    all: rewrite subst_context_app app_context_assoc Nat.add_0_r in b0.
    all: now rewrite app_context_length in b0.
  Qed.

  Lemma subst_sorts_local_ctx {Γ Γ' Δ Δ' s ctxs} :
    wf_local Σ (Γ ,,, Δ ,,, Γ') ->
    sorts_local_ctx (lift_typing typing) Σ (Γ ,,, Δ ,,, Γ') Δ' ctxs ->
    subslet Σ Γ s Δ ->
    sorts_local_ctx (lift_typing typing) Σ (Γ ,,, subst_context s 0 Γ') (subst_context s #|Γ'| Δ') ctxs.
  Proof using wfΣ.
    induction Δ' in Γ', ctxs |- *; simpl; auto.
    destruct a as [na [b|] ty]; rewrite subst_context_snoc /= /subst_decl /map_decl /=;
      intuition auto.
    2: destruct ctxs => //=; destruct X0 as (a & b0); split; eauto.
    all: rewrite -app_context_assoc in b0.
    all: eapply lift_typing_substitution in b0; tea.
    all: rewrite subst_context_app app_context_assoc Nat.add_0_r in b0.
    all: now rewrite app_context_length in b0.
  Qed.

  Lemma wf_arity_spine_typing_spine {Γ T args T'} :
    wf_arity_spine Σ Γ T args T' ->
    typing_spine Σ Γ T args T'.
  Proof using wfΣ.
    intros [wf sp].
    have wfΓ := isType_wf_local wf.
    induction sp; try constructor; auto; pcuic.
    - eapply typing_spine_strengthen; eauto.
      2:{ eapply into_ws_cumul_pb.
          apply red_cumul. apply red1_red. constructor.
          1-2:eauto with fvs.
          eapply isType_tLetIn_red in wf; eauto with fvs. }
      now eapply isType_tLetIn_red in wf.
    - econstructor; eauto with pcuic.
      apply IHsp. now eapply isType_apply in wf => //.
  Qed.

  Import PCUICConversion.

  Lemma arity_typing_spine {Γ Γ' s inst s'} :
    typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') ->
    [× (#|inst| = context_assumptions Γ'), leq_sort (global_ext_constraints Σ) s s' &
      ∑ instsubst, spine_subst Σ Γ inst instsubst Γ'].
  Proof using wfΣ.
    revert s inst s'.
    (* assert (wf_local Σ Γ). now apply wf_local_app_l in wfΓ'. move X after wfΓ'.
    rename X into wfΓ. *)
    generalize (le_n #|Γ'|).
    generalize (#|Γ'|) at 2.
    induction n in Γ' |- *.
    - destruct Γ' using rev_ind; try clear IHΓ'; simpl; intros len s inst s' Hsp.
      + dependent elimination Hsp as [spnil _ _ cum|spcons isty isty' cum tyhd sp].
        ++ split=>//.
          now eapply ws_cumul_pb_Sort_inv in cum.
          exists []. split; try constructor; eauto with pcuic.
          all:now eapply isType_wf_local.
        ++ now eapply ws_cumul_pb_Sort_Prod_inv in cum.
      + rewrite length_app /= in len; exfalso; lia.
    - intros len s inst s' Hsp.
      destruct Γ' using rev_ind; try clear IHΓ'.
      -- dependent elimination Hsp as [spnil _ _ cum|spcons isty isty' cum tyhd sp].
        1:split; auto.
        --- now eapply ws_cumul_pb_Sort_inv in cum.
        --- exists []; split; try constructor; auto.
            all:now eapply isType_wf_local.
        --- now eapply ws_cumul_pb_Sort_Prod_inv in cum.
      -- rewrite length_app /= in len.
        destruct x as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
        + rewrite context_assumptions_app /= Nat.add_0_r.
          assert (Hsp' := Hsp).
          rewrite it_mkProd_or_LetIn_app /= in Hsp'.
          eapply typing_spine_letin_inv in Hsp'; auto.
          rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp'.
          eapply typing_spine_isType_dom in Hsp.
          eapply isType_it_mkProd_or_LetIn_wf_local in Hsp.
          specialize (IHn (subst_context [b] 0 l)).
          forward IHn by rewrite subst_context_length; lia.
          specialize (IHn s inst s' Hsp').
          rewrite context_assumptions_subst in IHn.
          destruct IHn as [instlen leq [instsubst [wfdom wfcodom cs subi]]].
          split => //.
          exists (instsubst ++ [subst0 [] b]).
          split; auto.
          * apply context_subst_app_inv. cbn.
            rewrite !skipn_0 {1}subst_empty.
            assert(#|l| <= n) by lia.
            pose proof (context_subst_length cs). rewrite subst_context_length in H0.
            rewrite !firstn_app_left //.
            split. now rewrite H0 skipn_all_app.
            rewrite H0 skipn_all_app. repeat constructor.
          * apply subslet_app; rewrite !subst_empty //.
            eapply subslet_def_tip.
            rewrite app_context_assoc /= in Hsp.
            apply wf_local_app_l in Hsp. depelim Hsp. now eapply unlift_TermTyp.
        + rewrite context_assumptions_app /=.
          assert (Hsp' := Hsp).
          rewrite it_mkProd_or_LetIn_app in Hsp'.
          dependent elimination Hsp' as [spnil typ tys cum|type_spine_cons typ tys cum tyhd sp].
          { now eapply ws_cumul_pb_Prod_Sort_inv in cum. }
          eapply ws_cumul_pb_Prod_Prod_inv in cum as [eqna conva cumulB].
          eapply (PCUICConversion.substitution_ws_cumul_pb (Γ' := [vass na0 A]) (Γ'':=[]) (s := [hd0])) in cumulB; auto.
          rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
          specialize (IHn (subst_context [hd0] 0 l)).
          forward IHn by rewrite subst_context_length; lia.
          specialize (IHn s tl0 s'). 2:pcuic.
          rewrite context_assumptions_subst in IHn.
          assert (Σ ;;; Γ |- hd0 : ty).
          { eapply type_ws_cumul_pb; tea.
            eapply isType_tProd in typ as []; eauto with pcuic.
            symmetry; pcuic. }
          eapply typing_spine_strengthen in sp.
          3:eapply cumulB.
          2:{ cbn in *.
              eapply isType_apply in typ; tea.
              now rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in typ. }
          all:pcuic.
          destruct X0 as [instlen leq [instsubst [wfdom wfcodom cs subi]]].
          split=> /= //; try lia.
          exists (instsubst ++ [hd0]).
          eapply typing_spine_isType_dom in Hsp.
          eapply isType_it_mkProd_or_LetIn_wf_local in Hsp.
          split; auto.
          * apply context_subst_app_inv. cbn.
            rewrite !skipn_S skipn_0.
            assert(#|l| <= n) by lia.
            pose proof (context_subst_length cs). rewrite subst_context_length in H0.
            rewrite !firstn_app_left //.
            split. now rewrite H0 skipn_all_app.
            rewrite H0 skipn_all_app. apply (context_subst_ass _ []). constructor.
          * apply subslet_app => //. now apply subslet_ass_tip.
  Qed.

(*Lemma typing_spine_it_mkProd_or_LetIn_gen {Γ Δ : context} {T args s s' args' T'} :
  make_context_subst (List.rev Δ) args s' = Some s ->
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  induction Δ using ctx_length_rev_ind in args, args', s, s', T |- *.
  - cbn. destruct args => // => [= <-].
    intros Hsp _ Hsub ist. cbn. depelim Hsub. rewrite subst_empty in Hsp. auto.
  - intros Hsub Hsp Hargs subs.
    rewrite context_assumptions_app in Hargs.
    destruct d as [na [b|] ty]; simpl in *.
    * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => Hty.
      rewrite Nat.add_0_r in Hargs.
      rewrite rev_app_distr in Hsub. simpl in Hsub.
      specialize (X (subst_context [b] 0 Γ0) ltac:(len; lia) (subst [b] #|Γ0| T)). _ _ _ _ _ Hsub Hsp Hargs).
      forward X.
      now rewrite it_mkProd_or_LetIn_app /=.
      eapply typing_spine_letin; auto.
      pose proof (subslet_app_inv subs) as.
      eapply isType_substitution_it_mkProd_or_LetIn
      p
      rewrite /subst1.
      now rewrite -subst_app_simpl.
    * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      rewrite rev_app_distr in Hsub.
      simpl in Hsub. destruct args; try discriminate.
      simpl in Hargs. rewrite Nat.add_1_r in Hargs. noconf Hargs.
      intros subs. rewrite app_context_assoc in subs.
      specialize (IHn Δ _ T args s _ ltac:(lia) Hsub Hsp H subs).
      intros Har.
      forward IHn. now rewrite it_mkProd_or_LetIn_app.
      eapply subslet_app_inv in subs as [subsl subsr].
      depelim subsl.
      have Hskip := make_context_subst_skipn Hsub.
      rewrite List.length_rev in Hskip. rewrite Hskip in H0; noconf H0.
      simpl; eapply typing_spine_prod; auto; first
      now rewrite /subst1 -subst_app_simpl.
      eapply isType_substitution_it_mkProd_or_LetIn in Har; eauto.
Qed.*)


  Lemma typing_spine_it_mkProd_or_LetIn_gen {Γ Δ Δ' : context} {T args s s' args' T'} :
    make_context_subst (List.rev Δ) args s' = Some s ->
    typing_spine Σ Γ (subst0 s T) args' T' ->
    #|args| = context_assumptions Δ ->
    subslet Σ Γ s (Δ' ,,, Δ) ->
    isType Σ Γ (subst0 s' (it_mkProd_or_LetIn Δ T)) ->
    typing_spine Σ Γ (subst0 s' (it_mkProd_or_LetIn Δ T)) (args ++ args') T'.
  Proof using wfΣ.
    generalize (le_n #|Δ|).
    generalize (#|Δ|) at 2.
    induction n in Δ, Δ', args, s, s', T |- *.
    - destruct Δ using rev_ind.
      + intros le Hsub Hsp.
        destruct args; simpl; try discriminate.
        simpl in Hsub. now depelim Hsub.
      + rewrite length_app /=; intros; exfalso; lia.
    - destruct Δ using rev_ind.
      1:intros le Hsub Hsp; destruct args; simpl; try discriminate;
      simpl in Hsub; now depelim Hsub.
      clear IHΔ.
      rewrite length_app /=; intros Hlen Hsub Hsp Hargs.
      rewrite context_assumptions_app in Hargs.
      destruct x as [na [b|] ty]; simpl in *.
      * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        rewrite Nat.add_0_r in Hargs.
        rewrite rev_app_distr in Hsub. simpl in Hsub.
        intros subs isty. rewrite app_context_assoc in subs.
        specialize (IHn l _ T args s _ ltac:(lia) Hsub Hsp Hargs subs).
        forward IHn.
        { eapply isType_tLetIn_red in isty; pcuic.
          move: isty. rewrite /subst1 -subst_app_simpl //. }
        eapply typing_spine_letin; auto.
        rewrite /subst1.
        now rewrite -subst_app_simpl.
      * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        rewrite rev_app_distr in Hsub.
        simpl in Hsub. destruct args; try discriminate.
        simpl in Hargs. rewrite Nat.add_1_r in Hargs. noconf Hargs.
        intros subs. rewrite app_context_assoc in subs.
        specialize (IHn l _ T args s _ ltac:(lia) Hsub Hsp H subs).
        intros Har.
        eapply subslet_app_inv in subs as [subsl subsr].
        depelim subsl.
        have Hskip := make_context_subst_skipn Hsub.
        rewrite List.length_rev in Hskip. rewrite Hskip in H0; noconf H0.
        forward IHn.
        { eapply isType_apply in Har; tea.
          now move: Har; rewrite /subst1 -subst_app_simpl. }
        simpl; eapply typing_spine_prod; auto; first
        now rewrite /subst1 -subst_app_simpl.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn {Γ Δ T args s args' T'} :
    make_context_subst (List.rev Δ) args [] = Some s ->
    typing_spine Σ Γ (subst0 s T) args' T' ->
    #|args| = context_assumptions Δ ->
    subslet Σ Γ s Δ ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using wfΣ.
    intros.
    pose proof (@typing_spine_it_mkProd_or_LetIn_gen Γ Δ [] T args s [] args' T'); auto.
    now rewrite subst_empty app_context_nil_l in X2.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn' {Γ Δ T args s args' T'} :
    spine_subst Σ Γ args s Δ ->
    typing_spine Σ Γ (subst0 s T) args' T' ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using wfΣ.
    intros. destruct X.
    eapply typing_spine_it_mkProd_or_LetIn; eauto.
    eapply make_context_subst_spec_inv. now rewrite List.rev_involutive.
    now pose proof (context_subst_length2 inst_ctx_subst0).
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_close_make_subst {Γ Δ T args s} :
    make_context_subst (List.rev Δ) args [] = Some s ->
    #|args| = context_assumptions Δ ->
    subslet Σ Γ s Δ ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args (subst0 s T).
  Proof using wfΣ.
    intros.
    pose proof (@typing_spine_it_mkProd_or_LetIn_gen Γ Δ [] T args s [] []); auto.
    rewrite app_nil_r subst_empty in X1. apply X1; eauto.
    eapply isType_substitution_it_mkProd_or_LetIn in X0; tea.
    constructor; pcuic.
    now rewrite app_context_nil_l.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_close {Γ Δ T args s T'} :
    spine_subst Σ Γ args s Δ ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    T' = (subst0 s T) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T'.
  Proof using wfΣ.
    intros [] H ->.
    eapply typing_spine_it_mkProd_or_LetIn_close_make_subst; eauto.
    eapply make_context_subst_spec_inv.
    now rewrite List.rev_involutive.
    now eapply context_subst_length2 in inst_ctx_subst0.
  Qed.

  Lemma spine_subst_conv {Γ inst insts Δ inst' insts' Δ'} :
    spine_subst Σ Γ inst insts Δ ->
    spine_subst Σ Γ inst' insts' Δ' ->
    ws_cumul_ctx_pb_rel Conv Σ Γ Δ Δ' ->
    ws_cumul_pb_terms Σ Γ inst inst' ->
    ws_cumul_pb_terms Σ Γ insts insts'.
  Proof using wfΣ.
    move=> [_ wf cs sl] [_ wf' cs' sl'] [clΓ cv].
    move: inst insts cs wf sl inst' insts' cs' sl'.
    induction cv; intros; depelim cs; depelim cs'.
    1:constructor; auto.
    all:depelim p.
    - apply All2_app_r in X as (?&?).
      depelim sl; depelim sl'; depelim wf; depelim wf'.
      specialize (IHcv wf' _ _ cs wf sl _ _ cs' sl' a1).
      constructor; auto.
    - depelim sl; depelim sl'; depelim wf; depelim wf'.
      specialize (IHcv wf' _ _ cs wf sl _ _ cs' sl' X).
      constructor; auto.
      eapply (substitution_ws_cumul_pb_subst_conv (Δ := [])); eauto using subslet_untyped_subslet with fvs.
  Qed.

  Lemma spine_subst_subst {Γ Γ0 Γ' i s Δ sub} :
    spine_subst Σ (Γ ,,, Γ0 ,,, Γ') i s Δ ->
    subslet Σ Γ sub Γ0 ->
    spine_subst Σ (Γ ,,, subst_context sub 0 Γ')
      (map (subst sub #|Γ'|) i) (map (subst sub #|Γ'|) s)
      (subst_context sub #|Γ'| Δ).
  Proof using wfΣ.
    move=> [wfl wfΔ cs subl] subs.
    split.
    eapply substitution_wf_local; eauto.
    pose proof (subst_context_app sub 0 Γ' Δ). rewrite Nat.add_0_r in H. rewrite -app_context_assoc -H.
    clear H.
    eapply substitution_wf_local; eauto. now rewrite app_context_assoc.
    clear subl wfl wfΔ.
    induction cs in Γ, Γ0, Γ', subs |- *; rewrite ?subst_context_snoc ?map_app; simpl; try constructor.
    eapply IHcs; eauto.
    specialize (IHcs _ _ Γ' subs).
    epose proof (context_subst_def _ _ _ na (subst sub (#|Γ1| + #|Γ'|) b) (subst sub (#|Γ1| + #|Γ'|) t) IHcs).
    rewrite /subst_decl /map_decl /=.
    rewrite distr_subst.
    now rewrite (context_subst_length cs) in X |- *.
    clear cs wfΔ.
    induction subl; rewrite ?subst_context_snoc ?map_app; simpl; try constructor; auto.
    - eapply substitution in t0; eauto. simpl.
      rewrite -(subslet_length subl).
      now rewrite -distr_subst.
    - eapply substitution in t0; eauto. simpl.
      rewrite -(subslet_length subl).
      rewrite !distr_subst in t0.
      epose proof (cons_let_def _  _ _ _ _  _ _ IHsubl t0).
      now rewrite - !distr_subst in X.
  Qed.

  Lemma spine_subst_subst_first {Γ Γ' i s Δ sub} :
    spine_subst Σ (Γ ,,, Γ') i s Δ ->
    subslet Σ [] sub Γ ->
    spine_subst Σ (subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (map (subst sub #|Γ'|) s)
    (subst_context sub #|Γ'| Δ).
  Proof using wfΣ.
    move=> sp subs.
    epose proof (@spine_subst_subst [] Γ Γ' i s Δ sub).
    rewrite !app_context_nil_l in X. apply X; auto.
  Qed.

  Lemma weaken_subslet {s Δ Γ Γ'} :
    wf_local Σ Γ -> wf_local Σ Γ' ->
    subslet Σ Γ' s Δ -> subslet Σ (Γ ,,, Γ') s Δ.
  Proof using wfΣ.
    intros wfΔ wfΓ'.
    induction 1; constructor; auto.
    + eapply (weaken_ctx Γ); eauto.
    + eapply (weaken_ctx Γ); eauto.
  Qed.

  Lemma spine_subst_weaken {Γ i s Δ Γ'} :
    wf_local Σ Γ' ->
    spine_subst Σ Γ i s Δ ->
    spine_subst Σ (Γ' ,,, Γ) i s Δ.
  Proof using wfΣ.
    move=> wfl [cs subl].
    split; auto.
    eapply weaken_wf_local => //.
    rewrite -app_context_assoc. eapply weaken_wf_local => //.
    eapply weaken_subslet; eauto.
  Qed.

  Lemma spine_subst_app_inv {Γ Δ Δ' inst inst' insts} :
    #|inst| = context_assumptions Δ ->
    spine_subst Σ Γ (inst ++ inst') insts (Δ ,,, Δ') ->
    spine_subst Σ Γ inst (skipn #|Δ'| insts) Δ *
    spine_subst Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ').
  Proof using wfΣ.
    intros len sp.
    destruct sp as [wfdom wfcodom cs subs].
    eapply context_subst_app in cs as [csl csr].
    rewrite skipn_all_app_eq in csl => //.
    rewrite firstn_app_left in csr => //.
    eapply subslet_app_inv in subs as [sl sr].
    split; split; auto. rewrite app_context_assoc in wfcodom.
    now eapply All_local_env_app_inv in wfcodom as [? ?].
    eapply substitution_wf_local; eauto.
    now rewrite app_context_assoc in wfcodom.
  Qed.

  Lemma spine_subst_smash_app_inv {Γ Δ Δ' δ δ'} :
    #|δ| = context_assumptions Δ ->
    spine_subst Σ Γ (δ ++ δ') (List.rev (δ ++ δ')) (smash_context [] (Δ ,,, Δ')) ->
    spine_subst Σ Γ δ (List.rev δ) (smash_context [] Δ) ×
    spine_subst Σ Γ δ' (List.rev δ')
      (subst_context_let_expand (List.rev δ) Δ (smash_context [] Δ')).
  Proof using wfΣ.
    intros hδ sp.
    rewrite smash_context_app_expand in sp.
    eapply spine_subst_app_inv in sp; eauto.
    2:{ rewrite context_assumptions_smash_context /= //. }
    rewrite expand_lets_ctx_length smash_context_length /= in sp.
    destruct sp as [sppars spidx].
    assert (lenidx : context_assumptions Δ' = #|δ'|).
    { pose proof (PCUICContextSubst.context_subst_length2 spidx). len in H. }
    assert (firstn (context_assumptions Δ')
          (List.rev (δ ++ δ')) = List.rev δ').
    { rewrite List.rev_app_distr.
      now rewrite firstn_app_left // List.length_rev. }
    assert (skipn (context_assumptions Δ')
      (List.rev (δ ++ δ')) = List.rev δ).
    { rewrite List.rev_app_distr.
      erewrite (skipn_all_app_eq) => //; rewrite List.length_rev //. }
    rewrite H H0 in spidx, sppars.
    split => //.
  Qed.

  Lemma spine_subst_inst {ext u Γ i s Δ}  :
    wf_global_ext Σ.1 ext ->
    spine_subst (Σ.1, ext) Γ i s Δ ->
    consistent_instance_ext Σ ext u ->
    spine_subst Σ (subst_instance u Γ)
      (map (subst_instance u) i)
      (map (subst_instance u) s)
      (subst_instance u Δ).
  Proof using wfΣ.
    intros wfext [wfdom wfcodom cs subsl] cu.
    split.
    eapply wf_local_subst_instance; eauto.
    rewrite -subst_instance_app_ctx.
    eapply wf_local_subst_instance; eauto.
    clear -cs cu wfext wfΣ.
    induction cs; simpl; rewrite ?map_app; try constructor; auto.
    rewrite subst_instance_cons; simpl.
    rewrite subst_instance_subst.
    constructor; auto.

    clear -subsl cu wfΣ wfext.
    induction subsl; simpl; rewrite ?subst_instance_subst; constructor; auto.
    * destruct Σ as [Σ' univs].
      rewrite -subst_instance_subst.
      eapply (typing_subst_instance'' Σ'); simpl; eauto.
    * rewrite - !subst_instance_subst. simpl.
      destruct Σ as [Σ' univs].
      eapply (typing_subst_instance'' Σ'); simpl; eauto.
  Qed.

  Lemma spine_subst_weakening {Γ i s Δ Γ'} :
    wf_local Σ (Γ ,,, Γ') ->
    spine_subst Σ Γ i s Δ ->
    spine_subst Σ (Γ ,,, Γ') (map (lift0 #|Γ'|) i) (map (lift0 #|Γ'|) s) (lift_context #|Γ'| 0 Δ).
  Proof using wfΣ.
    move=> wfl [cs subl].
    split; auto.
    eapply weakening_wf_local; eauto.
    now apply context_subst_lift.
    now apply subslet_lift.
  Qed.

  Lemma ctx_inst_length {P Γ args Δ} :
    PCUICTyping.ctx_inst P Γ args Δ ->
    #|args| = context_assumptions Δ.
  Proof using Type.
    induction 1; simpl; auto.
    rewrite /subst_telescope in IHX.
    rewrite context_assumptions_mapi in IHX. congruence.
    rewrite context_assumptions_mapi in IHX. congruence.
  Qed.

  Lemma ctx_inst_subst {Γ Γ0 Γ' i Δ sub} :
    ctx_inst Σ (Γ ,,, Γ0 ,,, Γ') i Δ ->
    subslet Σ Γ sub Γ0 ->
    ctx_inst Σ (Γ ,,, subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (subst_telescope sub #|Γ'| Δ).
  Proof using wfΣ.
    move=> ctxinst subs.
    induction ctxinst in sub, subs |- *.
    - simpl; intros; constructor; auto.
    - intros. rewrite subst_telescope_cons; simpl; constructor.
      * simpl. eapply substitution; eauto.
      * specialize (IHctxinst _ subs).
        now rewrite (subst_telescope_comm [i]).
    - intros. rewrite subst_telescope_cons; simpl; constructor.
      specialize (IHctxinst _ subs).
      now rewrite (subst_telescope_comm [b]).
  Qed.

  Lemma ctx_inst_weaken {Γ i Δ Γ'} :
    wf_local Σ Γ' ->
    ctx_inst Σ Γ i Δ ->
    ctx_inst Σ (Γ' ,,, Γ) i Δ.
  Proof using wfΣ.
    move=> wfl subl.
    induction subl; constructor; auto.
    now eapply (weaken_ctx Γ').
  Qed.

  Lemma make_context_subst_tele s s' Δ inst sub :
    make_context_subst (subst_telescope s' #|s| Δ) inst s = Some sub ->
    make_context_subst Δ inst (s ++ s') = Some (sub ++ s').
  Proof using Type.
    induction Δ in s, s', sub, inst |- *.
    simpl. destruct inst; try discriminate.
    intros [= ->]. reflexivity.
    rewrite subst_telescope_cons.
    destruct a as [na [b|] ty]; simpl in *.
    intros. specialize (IHΔ _ _ _ _ H).
    now rewrite -subst_app_simpl in IHΔ.
    destruct inst. discriminate.
    intros. now specialize (IHΔ _ _ _ _ H).
  Qed.

  Fixpoint ctx_inst_sub {cf:checker_flags} {Σ Γ Δ args} (c : ctx_inst Σ Γ args Δ) {struct c} : list term :=
    match c return _ with
    | ctx_inst_nil => []
    | ctx_inst_ass na t i inst Δ P c => ctx_inst_sub c ++ [i]
    | ctx_inst_def na b t inst Δ c => ctx_inst_sub c ++ [b]
    end.

  Lemma ctx_inst_sub_spec {Γ Δ args} (c : ctx_inst Σ Γ args Δ) :
    make_context_subst Δ args [] = Some (ctx_inst_sub c).
  Proof using Type.
    induction c; simpl; auto.
    now apply (make_context_subst_tele [] [i]) in IHc.
    apply (make_context_subst_tele [] [b]) in IHc.
    now rewrite subst_empty.
  Qed.

  Lemma subst_telescope_empty k Δ : subst_telescope [] k Δ = Δ.
  Proof using Type.
    unfold subst_telescope, mapi. generalize 0. induction Δ; simpl; auto.
    intros.
    destruct a as [na [b|] ty]; unfold map_decl at 1; simpl; rewrite !subst_empty.
    f_equal. apply IHΔ.
    f_equal. apply IHΔ.
  Qed.

  Lemma subst_telescope_app s k Γ Δ : subst_telescope s k (Γ ++ Δ) = subst_telescope s k Γ ++
    subst_telescope s (#|Γ| + k) Δ.
  Proof using Type.
    rewrite /subst_telescope /mapi.
    rewrite mapi_rec_app. f_equal. rewrite mapi_rec_add.
    apply mapi_rec_ext. intros. destruct x as [na [b|] ty]; simpl; f_equal; f_equal; lia.
  Qed.

  Hint Extern 0 => lia : lia.

  Lemma context_assumptions_subst_telescope s k Δ : context_assumptions (subst_telescope s k Δ) =
    context_assumptions Δ.
  Proof using Type.
    rewrite /subst_telescope /mapi. generalize 0.
    induction Δ; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto with lia.
    intros. specialize (IHΔ (S n)). lia.
  Qed.

  Lemma subst_app_telescope s s' k Γ :
    subst_telescope (s ++ s') k Γ = subst_telescope s k (subst_telescope s' (#|s| + k) Γ).
  Proof using Type.
    rewrite /subst_telescope /mapi.
    rewrite mapi_rec_compose.
    apply mapi_rec_ext. intros. destruct x as [na [b|] ty]; simpl; unfold map_decl; simpl; f_equal.
    rewrite subst_app_simpl. f_equal; f_equal. f_equal. lia.
    rewrite subst_app_simpl. f_equal; f_equal. lia.
    rewrite subst_app_simpl. f_equal; f_equal. lia.
  Qed.

  Lemma make_context_subst_length Γ args acc sub : make_context_subst Γ args acc = Some sub ->
    #|sub| = #|Γ| + #|acc|.
  Proof using Type.
    induction Γ in args, acc, sub |- *; simpl.
    destruct args; try discriminate. now intros [= ->].
    destruct a as [? [b|] ty] => /=. intros H.
    specialize (IHΓ _ _ _ H). simpl in IHΓ. lia.
    destruct args; try discriminate.
    intros H.
    specialize (IHΓ _ _ _ H). simpl in IHΓ. lia.
  Qed.

  Lemma subst_telescope_length s k Γ : #|subst_telescope s k Γ| = #|Γ|.
  Proof using Type.
    now rewrite /subst_telescope mapi_length.
  Qed.

  Lemma arity_spine_it_mkProd_or_LetIn {Γ Δ T args s args' T'} :
    spine_subst Σ Γ args s Δ ->
    arity_spine Σ Γ (subst0 s T) args' T' ->
    arity_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using Type.
    intros sp asp. destruct sp as [wfΓ _ cs subsl].
    move: Δ args s T cs subsl asp.
    induction Δ using ctx_length_rev_ind => args s T cs subsl asp.
    - depelim cs. depelim  subsl.
      now rewrite subst_empty in asp.
    - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      destruct d as [na [b|] ty]; simpl in *.
      * constructor. rewrite /subst1 subst_it_mkProd_or_LetIn.
        rewrite Nat.add_0_r.
        apply subslet_app_inv in subsl as [subsl subsl'].
        depelim subsl; depelim subsl.
        apply context_subst_app in cs as [cs cs'].
        simpl in *. rewrite skipn_0 in cs.
        specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _
          (subst [b] #|Γ0| T) cs subsl').
        rewrite subst_empty in H.
        rewrite H in X. apply X.
        rewrite -subst_app_simpl'.
        apply subslet_length in subsl'.
        now autorewrite with len in subsl'.
        rewrite -H.  now rewrite firstn_skipn.
      * apply subslet_app_inv in subsl as [subsl subsl'].
        depelim subsl; depelim subsl.
        apply context_subst_app in cs as [cs cs'].
        simpl in *.
        destruct args. depelim cs'.
        depelim cs'. discriminate.
        simpl in *. rewrite skipn_S skipn_0 in cs.
        rewrite subst_empty in t0.
        depelim cs'; depelim cs'. simpl in H; noconf H.
        rewrite H1 in H0. noconf H0.
        constructor; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn.
        rewrite Nat.add_0_r.
        specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _
        (subst [t1] #|Γ0| T) cs subsl').
        rewrite -{1}H1. apply X.
        rewrite -subst_app_simpl'.
        apply subslet_length in subsl'.
        now autorewrite with len in subsl'.
        rewrite -H1. now rewrite firstn_skipn.
  Qed.

  Lemma spine_subst_is_closed_context Γ args inst ctx :
    spine_subst Σ Γ args inst ctx ->
    is_closed_context Γ.
  Proof using wfΣ.
    now move=> [] /wf_local_closed_context.
  Qed.

  Lemma spine_subst_is_closed_context_codom Γ args inst ctx :
    spine_subst Σ Γ args inst ctx ->
    is_closed_context (Γ ,,, ctx).
  Proof using wfΣ.
    now move=> [] _ /wf_local_closed_context.
  Qed.
  Hint Resolve spine_subst_is_closed_context spine_subst_is_closed_context_codom : fvs.

  Lemma arity_spine_it_mkProd_or_LetIn_Sort {Γ ctx s s' args inst} :
    wf_sort Σ s' ->
    leq_sort Σ s s' ->
    spine_subst Σ Γ args inst ctx ->
    arity_spine Σ Γ (it_mkProd_or_LetIn ctx (tSort s)) args (tSort s').
  Proof using wfΣ.
    intros wfs le sp. rewrite -(app_nil_r args).
    eapply arity_spine_it_mkProd_or_LetIn => //.
    eauto. constructor.
    eapply isType_Sort; eauto.
    eapply sp. simpl.
    apply ws_cumul_pb_compare => //; eauto with pcuic fvs. now constructor.
  Qed.

  Lemma ctx_inst_subst_length {Γ} {Δ : context} {args} (c : ctx_inst Σ Γ args Δ) :
    #|ctx_inst_sub c| = #|Δ|.
  Proof using Type.
    induction c; simpl; auto; try lia;
    rewrite length_app IHc subst_telescope_length /=; lia.
  Qed.

  Lemma ctx_inst_app {Γ} {Δ : context} {Δ' args args'}
    (dom : ctx_inst Σ Γ args Δ) :
    ctx_inst Σ Γ args' (subst_telescope (ctx_inst_sub dom) 0 Δ') ->
    ctx_inst Σ Γ (args ++ args') (Δ ++ Δ').
  Proof using Type.
    induction dom in args', Δ' |- *; simpl.
    - now rewrite subst_telescope_empty.
    - rewrite subst_app_telescope /= ctx_inst_subst_length /= subst_telescope_length Nat.add_0_r /=.
      move/IHdom => IH.
      constructor => //.
      now rewrite subst_telescope_app Nat.add_0_r.
    - rewrite subst_app_telescope /= ctx_inst_subst_length /= subst_telescope_length Nat.add_0_r /=.
      move/IHdom => IH.
      constructor => //.
      now rewrite subst_telescope_app Nat.add_0_r.
  Qed.

  Lemma ctx_inst_app_inv {Γ} {Δ : context} {Δ' args}
    (c : ctx_inst Σ Γ args (Δ ++ Δ')) :
    ∑ (dom : ctx_inst Σ Γ (firstn (context_assumptions Δ) args) Δ),
      ctx_inst Σ Γ (skipn (context_assumptions Δ) args) (subst_telescope (ctx_inst_sub dom) 0 Δ').
  Proof using Type.
    revert args Δ' c.
    induction Δ using ctx_length_ind; intros.
    simpl. unshelve eexists. constructor.
    simpl. rewrite skipn_0. now rewrite subst_telescope_empty.
    depelim c; simpl.
    - specialize (X (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
      rewrite subst_telescope_app in c.
      specialize (X _ _ c).
      rewrite context_assumptions_subst_telescope in X.
      destruct X as [dom codom].
      unshelve eexists.
      constructor; auto. simpl.
      pose proof (ctx_inst_sub_spec dom) as Hsub.
      simpl in *. rewrite Nat.add_0_r in codom. rewrite skipn_S.
      rewrite subst_app_telescope.
      apply make_context_subst_length in Hsub.
      rewrite subst_telescope_length Nat.add_0_r in Hsub.
      now rewrite Hsub Nat.add_0_r.
    - specialize (X (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
      rewrite subst_telescope_app in c.
      specialize (X _ _ c).
      rewrite context_assumptions_subst_telescope in X.
      destruct X as [dom codom].
      unshelve eexists.
      constructor; auto. simpl.
      pose proof (ctx_inst_sub_spec dom) as Hsub.
      simpl in *. rewrite Nat.add_0_r in codom.
      rewrite subst_app_telescope.
      apply make_context_subst_length in Hsub.
      rewrite subst_telescope_length Nat.add_0_r in Hsub.
      now rewrite Hsub Nat.add_0_r.
  Qed.

  Lemma ctx_inst_sub_eq {Γ} {Δ : context} {Δ' args args'} (c : ctx_inst Σ Γ args Δ) (d : ctx_inst Σ Γ args' Δ') :
    args' = args ->
    Δ = Δ' -> ctx_inst_sub c = ctx_inst_sub d.
  Proof using Type.
    intros -> ->. induction c; depelim d; auto; simpl in *; now rewrite (IHc d).
  Qed.

  Lemma ctx_inst_app_sub {Γ} {Δ : context} {Δ' args} (c : ctx_inst Σ Γ args (Δ ++ Δ')) :
    let (dom, codom) := ctx_inst_app_inv c in
    ctx_inst_sub c = ctx_inst_sub codom ++ ctx_inst_sub dom.
  Proof using Type.
    destruct (ctx_inst_app_inv c).
    induction Δ using ctx_length_ind in Δ', c, x, args, c0 |- *. simpl in *. depelim x. simpl in *.
    rewrite app_nil_r; apply ctx_inst_sub_eq. now rewrite skipn_0.
    now rewrite subst_telescope_empty.
    simpl in *. destruct d as [na [b|] ty]; simpl in *.
    depelim c; simpl in *.
    depelim x; simpl in *.
    injection H0. discriminate. injection H0. discriminate.
    specialize (H (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    revert c. rewrite subst_telescope_app.
    intros c.
    specialize (H  _ _ c). simpl in *.
    revert H. rewrite context_assumptions_subst_telescope.
    intros.
    specialize (H x).
    revert c0. rewrite subst_app_telescope.
    rewrite (ctx_inst_subst_length x) subst_telescope_length.
    intros c1.
    now rewrite (H c1) app_assoc.

    depelim c; depelim x; simpl in *.
    specialize (H (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    revert c. rewrite subst_telescope_app. intros c.
    specialize (H _ _ c). simpl in *.
    revert H. rewrite context_assumptions_subst_telescope.
    intros.
    specialize (H x).
    revert c0. rewrite subst_app_telescope.
    rewrite (ctx_inst_subst_length x) subst_telescope_length.
    intros c1.
    now rewrite (H c1) app_assoc.
  Qed.

  Lemma ctx_inst_def {Γ args na b t} (c : ctx_inst Σ Γ args [vdef na b t]) :
    ((args = []) * (ctx_inst_sub c = [b]))%type.
  Proof using Type.
    depelim c; simpl in c. depelim c; simpl in *. constructor; simpl in *; auto.
  Qed.

  Lemma ctx_inst_ass {Γ args na t} (c : ctx_inst Σ Γ args [vass na t]) :
    ∑ i, ((args = [i]) * (typing Σ Γ i t) * (ctx_inst_sub c = [i]))%type.
  Proof using Type.
    depelim c; simpl in *.
    depelim c. exists i; constructor; auto.
  Qed.

  Lemma ctx_inst_spine_subst {Γ Δ args} :
    wf_local Σ (Γ ,,, Δ) ->
    forall ci : ctx_inst Σ Γ args (List.rev Δ),
    spine_subst Σ Γ args (ctx_inst_sub ci) Δ.
  Proof using wfΣ.
    move=> wfΔ ci.
    pose proof (ctx_inst_sub_spec ci) as msub.
    eapply make_context_subst_spec in msub.
    rewrite List.rev_involutive in msub.
    split; pcuic. now eapply All_local_env_app_inv in wfΔ as [].
    move: ci msub.
    induction Δ in wfΔ, args |- *.
    simpl. intros ci. depelim ci. constructor.
    intros. simpl in ci.
    pose proof (ctx_inst_app_sub ci).
    destruct (ctx_inst_app_inv ci). rewrite H in msub |- *.
    clear ci H.
    simpl in c.
    apply (@context_subst_app [a]) in msub.
    simpl in msub.
    destruct a as [na [b|] ty]; simpl in *.
    - pose proof (ctx_inst_def c) as [Hargs Hinst].
      rewrite Hinst in msub |- *. simpl in *.
      destruct msub as [subl subr].
      rewrite skipn_S skipn_0 in subr.
      generalize dependent x. rewrite context_assumptions_rev.
      intros.
      depelim wfΔ.
      specialize (IHΔ _ wfΔ _ subr). constructor; auto.
      apply unlift_TermTyp in l.
      eapply (substitution (Δ := [])); eauto.
    - pose proof (ctx_inst_ass c) as [i [[Hargs Hty] Hinst]].
      rewrite Hinst in msub |- *. simpl in *.
      destruct msub as [subl subr].
      rewrite skipn_S skipn_0 in subr subl.
      generalize dependent x. rewrite context_assumptions_rev.
      intros.
      depelim wfΔ.
      specialize (IHΔ _ wfΔ _ subr). constructor; auto.
  Qed.

  Lemma spine_subst_ctx_inst {Γ Δ args s} :
    spine_subst Σ Γ args s Δ ->
    ctx_inst Σ Γ args (List.rev Δ).
  Proof using Type.
    move=> [wfd _ cs subsl].
    induction subsl in args, cs |- *.
    - depelim cs. constructor.
    - depelim cs.
      specialize (IHsubsl _ cs).
      unshelve eapply ctx_inst_app; tea. cbn.
      rewrite /map_decl /=. repeat constructor.
      pose proof (ctx_inst_sub_spec IHsubsl) as msub.
      eapply make_context_subst_spec in msub.
      rewrite List.rev_involutive in msub.
      now pose proof (context_subst_fun cs msub); subst s.
    - depelim cs.
      specialize (IHsubsl _ cs). cbn.
      rewrite -(app_nil_r args).
      unshelve eapply ctx_inst_app; tea. cbn.
      rewrite /map_decl /=. repeat constructor.
  Qed.

End WfEnv.

Lemma subst_instance_rev u Γ :
  subst_instance u (List.rev Γ) = List.rev (subst_instance u Γ).
Proof.
  now rewrite /subst_instance /subst_instance_context /= /map_context List.map_rev.
Qed.

Lemma subst_telescope_subst_context s k Γ :
  subst_telescope s k (List.rev Γ) = List.rev (subst_context s k Γ).
Proof.
  rewrite /subst_telescope subst_context_alt.
  rewrite rev_mapi. apply mapi_rec_ext.
  intros n [na [b|] ty] le le'; rewrite /= /subst_decl /map_decl /=;
  rewrite List.length_rev Nat.add_0_r in le';
  f_equal. f_equal. f_equal. lia. f_equal; lia.
  f_equal; lia.
Qed.

Lemma lift_context_subst_context n s Γ: lift_context n 0 (subst_context s 0 Γ) =
  subst_context s n (lift_context n 0 Γ).
Proof.
  induction Γ in n, s |- *.
  - reflexivity.
  - rewrite !subst_context_snoc.
    rewrite !lift_context_snoc !subst_context_snoc.
    f_equal; auto.
    rewrite /lift_decl /subst_decl /map_decl.
    simpl. f_equal. unfold option_map. destruct (decl_body a).
    rewrite !subst_context_length lift_context_length Nat.add_0_r.
    rewrite commut_lift_subst_rec; auto. reflexivity.
    rewrite !subst_context_length lift_context_length Nat.add_0_r.
    rewrite commut_lift_subst_rec; auto.
Qed.

Lemma subst_app_context_gen s s' k Γ : subst_context (s ++ s') k Γ = subst_context s k (subst_context s' (k + #|s|) Γ).
Proof.
  induction Γ in k |- *; simpl; auto.
  rewrite !subst_context_snoc /= /subst_decl /map_decl /=. simpl.
  rewrite IHΓ. f_equal. f_equal.
  - destruct a as [na [b|] ty]; simpl; auto.
    f_equal. rewrite subst_context_length.
    now rewrite subst_app_simpl.
  - rewrite subst_context_length.
    now rewrite subst_app_simpl.
Qed.

Lemma closed_k_ctx_subst n k ctx : closedn_ctx k ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  simpl.
  move/andb_and => /= [Hctx Hd].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
Qed.

Fixpoint all_rels (Γ : context) (n : nat) (k : nat) :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>
      let s := all_rels vs (S n) k in
      (subst0 s (lift k #|s| b)) :: s
    | None => tRel n :: all_rels vs (S n) k
    end
  end.

Lemma all_rels_length Γ n k : #|all_rels Γ n k| = #|Γ|.
Proof.
  induction Γ in n, k |- *; simpl; auto.
  now destruct a as [? [?|] ?] => /=; simpl; rewrite IHΓ.
Qed.

Lemma nth_error_all_rels_spec Γ n k x i : nth_error (all_rels Γ n k) i = Some x ->
  ∑ decl, (nth_error Γ i = Some decl) *
    match decl_body decl with
    | Some b => x = subst0 (all_rels (skipn (S i) Γ) (S n + i) k) (lift k (#|Γ| - S i) b)
    | None => x = tRel (n + i)
    end.
Proof.
  induction Γ in n, k, i, x |- *.
  simpl. destruct i; simpl; discriminate.
  destruct i; simpl.
  destruct a as [? [?|] ?]; simpl.
  intros [= <-].
  eexists; split; eauto. simpl.
  now rewrite skipn_S skipn_0 Nat.add_0_r all_rels_length.
  intros [= <-].
  eexists; split; eauto. simpl.
  now rewrite Nat.add_0_r.
  intros. destruct (decl_body a);  try discriminate.
  rewrite skipn_S.
  specialize  (IHΓ _ _ _ _ H).
  rewrite Nat.add_succ_r. apply IHΓ.
  rewrite skipn_S.
  specialize  (IHΓ _ _ _ _ H).
  rewrite Nat.add_succ_r. apply IHΓ.
Qed.

Lemma subst_lift_lift s k t : subst0 (map (lift0 k) s) (lift k #|s| t) = lift0 k (subst0 s t).
Proof.
  now rewrite (distr_lift_subst_rec _ _ _ 0 0).
Qed.
#[global]
Hint Rewrite all_rels_length : len.

Lemma all_rels_lift (Δ : context) n : all_rels Δ n (n + #|Δ|) = map (lift0 n) (all_rels Δ 0 #|Δ|).
Proof.
  rewrite -{1}(Nat.add_0_r n).
  generalize 0 at 1 3. revert n.
  induction Δ at 1 3.
  simpl. auto.
  intros n n'.
  destruct a as [na [?|] ?]. simpl.
  f_equal.
  specialize (IHc n (S n')).
  rewrite Nat.add_succ_r in IHc.
  rewrite {1}IHc.
  rewrite all_rels_length.
  assert(#|all_rels c (S n') #|Δ| | = #|c|) by now autorewrite with len.
  rewrite -(simpl_lift _ _ _ _ #|c|); try lia.
  rewrite -{1}H.
  epose proof (distr_lift_subst _ _ n 0).
  rewrite Nat.add_0_r in H0. now erewrite <-H0.
  specialize (IHc n (S n')).
  now rewrite -IHc.
  simpl.
  f_equal.
  specialize (IHc n (S n')).
  now rewrite -IHc.
Qed.

Lemma all_rels_subst {cf:checker_flags} Σ Δ Γ t :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)).
Proof.
  intros wfΣ wf.
  assert(forall Γ' t (wf : wf_local Σ Γ'),
    ((All_local_env_over (typing Σ)
      (fun Γ' wfΓ' t T _ =>
        forall Γ Δ, Γ' = Γ ,,, Δ ->
        red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)))
        Γ' wf) *
        (match t with
        | Some t => forall Γ Δ, Γ' = Γ ,,, Δ ->
            red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t))
        | None => unit  end))).
  clear t Δ Γ wf. intros Γ' t.
  Subterm.rec_wf_rel IH (Γ', t) (Subterm.lexprod (precompose lt (@length context_decl))
     (precompose lt (fun x => match x with Some t => S (PCUICSize.size t) | None => 0 end))).
  simpl.
  rename pr1 into cf.
  rename pr0 into Σ.
  rename pr2 into wfΣ.
  rename pr3 into Γ.
  rename pr4 into t. clear H0.
  intros wf.
  split.
  - specialize (IH cf Σ wfΣ).
    destruct wf.
    constructor.
    constructor.
    apply (IH Γ t ltac:(left; simpl; lia) wf).
    intros; subst Γ.
    now apply (IH (Γ0 ,,, Δ) (Some t0) ltac:(left; simpl; lia) wf).
    constructor; auto.
    apply (IH Γ t ltac:(left; simpl; lia) wf).
    intros.
    now apply (IH Γ (Some b) ltac:(left; simpl; lia) wf).
    now apply (IH Γ (Some t0) ltac:(left; simpl; lia) wf).

  - destruct t; [|exact tt].
    intros Γ0 Δ ->.
    rename Γ0 into Γ.
    specialize (IH cf Σ).
    assert (All_local_env_over (typing Σ)
    (fun (Γ'0 : PCUICEnvironment.context) (_ : wf_local Σ Γ'0)
       (t T : term) (_ : Σ;;; Γ'0 |- t : T) =>
     forall Γ Δ : context,
     Γ'0 = Γ ,,, Δ ->
     red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)))
    _ wf).
    { specialize (IH wfΣ (Γ ,,, Δ) None).
      forward IH. simpl. right. lia.
      apply (IH wf). }
    clear IH.

  change (Γ ,,, Δ) with (Γ ,,, Δ ,,, []).
  rewrite -{3}(Nat.add_0_r #|Δ|).
  change 0 with #|@nil context_decl| at 2 3.
  generalize (@nil context_decl) as Δ'.

  induction t using term_ind_size_app; try solve [constructor]; intros Δ'.
  * simpl.
     destruct (leb_spec_Set (#|Δ|  +#|Δ'|) n); simpl.
    **
      elim: leb_spec_Set => Hle.
      destruct (nth_error_spec (all_rels Δ 0 #|Δ|) (#|Δ| + n - #|Δ'|));
      rewrite all_rels_length in l0 |- *. lia.
      assert (#|Δ| + n - #|Δ| = n) as -> by lia.
      reflexivity. lia.
    **
      elim: leb_spec_Set => Hle.
      destruct (nth_error_spec (all_rels Δ 0 #|Δ|) (n - #|Δ'|));
      rewrite all_rels_length in l0 |- *; try lia.
      eapply nth_error_all_rels_spec in e.
      destruct e as [decl [Hnth Hdecl]].
      destruct decl as [? [?|] ?]; simpl in Hdecl; subst x.
      assert (n = #|Δ'| + (n - #|Δ'|)). lia.
      rewrite {1}H.
      change (tRel  (#|Δ'| + (n - #|Δ'|))) with
          (lift0 #|Δ'| (tRel (n - #|Δ'|))).
      eapply (weakening_red (Γ' := [])); auto.
      { erewrite on_free_vars_ctx_on_ctx_free_vars; tea.
        clear X.
        now eapply wf_local_closed_context in wf. }
      { cbn. rewrite /PCUICOnFreeVars.shiftnP length_app. nat_compare_specs => //. }
      simpl.
      set (i := n - #|Δ'|) in *. clearbody i.
      clear l Hle H.

      etransitivity.
      + eapply red1_red. constructor.
        rewrite nth_error_app_lt; auto.
        rewrite Hnth. reflexivity.
      + rewrite -{1 3 4}(firstn_skipn (S i) Δ).
        rewrite app_context_assoc.
        assert (Hf:#|firstn (S i) Δ| = S i) by now rewrite firstn_length_le; lia.
        rewrite length_app Hf.
        rewrite all_rels_lift.
        erewrite <-(simpl_lift _ _ _ _ #|skipn (S i) Δ|); try lia.

        epose proof (distr_lift_subst (lift #|skipn (S i) Δ| (#|Δ| - S i) t)
        (all_rels (skipn (S i) Δ) 0 #|skipn (S i) Δ|) (S i) 0).
        rewrite Nat.add_0_r in H.
        autorewrite with len in H.
        rewrite -{}H.
        rewrite -{3 4}Hf.
        eapply (weakening_red (Γ' := [])); auto. simpl.
        { clear X; apply wf_local_closed_context in wf.
          move: wf.
          erewrite on_free_vars_ctx_on_ctx_free_vars.
          rewrite !on_free_vars_ctx_app => /andP[] onΓ. erewrite onΓ => /=.
          rewrite -{1}(firstn_skipn (S i) Δ) on_free_vars_ctx_app => /andP[] //.
        }
        { clear X; eapply (All_local_env_nth_error (n:=i)) in wf.
          2: rewrite nth_error_app_lt; eassumption.
          rewrite skipn_app in wf.
          replace (S i - #|Δ|) with 0 in wf. 2:lia.
          rewrite skipn_0 in wf.
          rewrite /= in wf.
          move: wf => [] /subject_closed //.
          rewrite is_open_term_closed //. }
        rewrite length_skipn; simpl.
        apply All_local_env_over_2 in X.
        eapply (All_local_env_nth_error (n:=i)) in X.
        2: rewrite nth_error_app_lt; eassumption.
        destruct X as ((Hb & Xb) & s & (Ht & Xt) & _).
        specialize (Xb Γ (skipn (S i) Δ)).
        forward Xb. rewrite skipn_app. unfold app_context. f_equal.
        assert(S i - #|Δ| = 0) by lia. rewrite H. apply skipn_0.
        now rewrite length_skipn in Xb; try lia.
        now rewrite length_skipn.
      + simpl. assert(#|Δ'| + (n - #|Δ'|) = n) as -> by lia.
        reflexivity.
      + reflexivity.

  * simpl; eapply red_evar.
    do 2 apply All2_map_right.
    apply (All_All2 X0); auto.

  * simpl. eapply red_prod. auto.
    specialize (IHt2 (Δ' ,, vass n t1)).
    now rewrite -Nat.add_succ_r.

  * simpl; eapply red_abs; auto.
    rewrite -Nat.add_succ_r.
    eapply (IHt2 (Δ' ,, vass n _)).

  * simpl; eapply red_letin; auto.
    rewrite -Nat.add_succ_r.
    eapply (IHt3 (Δ' ,, vdef n _ _)).

  * simpl; eapply red_app; auto.
  * simpl. rewrite map_branches_k_map_branches_k.
    relativize (subst_predicate _ _ _).
    eapply red_case.
    5:{ reflexivity. }
    all:auto.
    + rewrite map_map_compose.
      apply All2_map_right. solve_all.
    + destruct X0 as [? [? ?]].
      specialize (r (Δ' ,,, inst_case_predicate_context p)).
      rewrite app_context_assoc in r. len in r.
      cbn. relativize (#|pcontext p| + (_ + _)). eapply r. lia.
    + red in X1 |- *.
      eapply All2_map_right; cbn; solve_all.
      eapply All_All2; tea.
      cbn; intros; solve_all.
      specialize (b (Δ' ,,, inst_case_branch_context p x)).
      rewrite app_context_assoc in b.
      len. rewrite -Nat.add_assoc (Nat.add_comm #|Δ|) Nat.add_assoc.
      relativize (#|bcontext x| + _). rewrite Nat.add_comm. eapply b.
      now len.

  * simpl; eapply red_proj_c. auto.

  * simpl; eapply red_fix_congr.
    do 2 eapply All2_map_right.
    eapply (All_All2 X0); simpl; intuition auto.
    rewrite length_map.
    specialize (b (Δ' ,,, fix_context m)).
    autorewrite with len in b.
    rewrite Nat.add_shuffle3.
    now rewrite app_context_assoc in b.

  * simpl. eapply red_cofix_congr.
    do 2 eapply All2_map_right.
    eapply (All_All2 X0); simpl; intuition auto.
    rewrite length_map.
    specialize (b (Δ' ,,, fix_context m)).
    autorewrite with len in b.
    rewrite Nat.add_shuffle3.
    now rewrite app_context_assoc in b.

  * cbn. destruct p as [? []]; cbn => //=.
    eapply red_primArray_congr; cbn in *; intuition eauto. solve_all.
- specialize (X (Γ ,,, Δ)  (Some t) wf). simpl in X.
  apply X. reflexivity.
Qed.

Section WfEnv.
  Context {cf} {Σ} {wfΣ : wf Σ}.

  Lemma all_rels_subst_lift {Δ Γ Δ' t} :
    wf_local Σ (Γ ,,, Δ) ->
    is_closed_context (Γ ,,, Δ ,,, Δ') ->
    is_open_term (Γ ,,, Δ) t ->
    Σ ;;; Γ ,,, Δ ,,, Δ' ⊢ lift0 #|Δ'| t =
      subst0 (all_rels Δ #|Δ'| (#|Δ| + #|Δ'|)) (lift (#|Δ| + #|Δ'|) #|Δ| t).
  Proof using wfΣ.
    intros.
    rewrite Nat.add_comm.
    erewrite <-(simpl_lift _ _ _ _ #|Δ|); try lia.
    rewrite all_rels_lift.
    have dl := distr_lift_subst (lift #|Δ| #|Δ| t) (all_rels Δ 0 #|Δ|) #|Δ'| 0.
    rewrite Nat.add_0_r in dl.
    rewrite -{2}(all_rels_length Δ 0 #|Δ|) -{}dl.
    eapply (weakening_ws_cumul_pb (Γ'' := Δ') (Γ' := [])) => // /=.
    apply red_ws_cumul_pb.
    apply into_closed_red => //.
    eapply all_rels_subst; auto => //.
    eauto with fvs.
  Qed.

  Lemma lift_context0_app {n Γ Δ} : lift_context n 0 (Γ ,,, Δ) = lift_context n 0 Γ ,,, lift_context n #|Γ| Δ.
  Proof using Type.
    now rewrite lift_context_app Nat.add_0_r.
  Qed.

  Lemma spine_subst_to_extended_list_k {Δ Γ : context} :
    wf_local Σ (Γ ,,, Δ) ->
    spine_subst Σ (Γ ,,, Δ) (reln [] 0 Δ) (all_rels Δ 0 #|Δ|)
      (lift_context #|Δ| 0 Δ).
  Proof using wfΣ.
    move=> wf.
    assert (wf_local Σ (Γ,,, Δ,,, lift_context #|Δ| 0 Δ)).
    { apply weakening_wf_local; auto. }
    split; auto.
    { clear wf X.
      generalize 0 at 2 3.
      induction Δ at 2 3 4; intros n; rewrite ?lift_context_snoc0; simpl; auto.
      destruct a as [na [?|] ?]  => /=;
      rewrite /lift_decl /= /map_decl /=.
      specialize (IHc (S n)).
      eapply (context_subst_def _ _ _ _ (lift #|Δ| (#|c| + 0) t)) in IHc.
      rewrite Nat.add_1_r.
      rewrite all_rels_length.
      rewrite Nat.add_0_r in IHc |- *.
      apply IHc.
      rewrite reln_acc.
      constructor.
      specialize (IHc (S n)).
      now rewrite Nat.add_1_r. }

    move: X.
    generalize (@eq_refl _ Δ).
    change Δ with ([] ++ Δ) at 1 5.
    change 0 with (length (@nil context_decl)) at 2.
    generalize (@nil context_decl).
    induction Δ at 1 5 7 10; rewrite /= => l eql.
    - constructor.
    - specialize (IHc (l ++ [a])).
      rewrite -app_assoc in IHc. specialize (IHc eql).
      destruct a as [na [?|] ?]  => /=;
      rewrite lift_context_snoc /lift_decl /map_decl /=.
      * rewrite length_app /= Nat.add_1_r in IHc.
        rewrite all_rels_length Nat.add_0_r.
        intros X. specialize (IHc X).
        constructor; auto.
        assert (Some (Some t) = option_map decl_body (nth_error Δ #|l|)).
        destruct (nth_error_spec Δ #|l|).
        rewrite -eql in e.
        rewrite nth_error_app_ge in e. lia.
        rewrite Nat.sub_diag in e. simpl in e. noconf e. simpl. reflexivity.
        rewrite -eql in l0. autorewrite with len in l0. simpl in l0. lia.
        eapply (substitution (Δ := []) IHc); auto.
        rewrite lift_context0_app !app_context_assoc in X. cbn in X.
        eapply All_local_env_app_inv in X as [].
        rewrite lift_context_snoc0 Nat.add_0_r /= in a. cbn in a.
        depelim a. now apply unlift_TermTyp in l0.
      * rewrite length_app /= Nat.add_1_r in IHc.
        intros Hwf. specialize (IHc Hwf).
        constructor; auto.

        pose proof wf as wf'.
        rewrite -eql in wf'.
        rewrite !app_context_assoc in wf'.
        apply wf_local_app_l in wf'. depelim wf'.
        rewrite Nat.add_0_r.
        eapply type_ws_cumul_pb.
        constructor. auto.
        rewrite -eql nth_error_app_lt ?length_app /=; try lia.
        rewrite nth_error_app_ge // ?Nat.sub_diag //.
        apply lift_sorting_forget_rel in l0.
        apply lift_sorting_f_it_impl with (f := fun t => _ (_ t)) (tu := l0) => // Hs.
        set (s := l0.2.π1).
        change (tSort s) with
          (subst0 (all_rels c (S #|l|) #|Δ|) (lift #|Δ| #|c| (tSort s))).
        { eapply (substitution (Γ' := lift_context #|Δ| 0 c) (Δ := [])); cbn; auto.
          change (tSort s) with (lift #|Δ| #|c| (tSort s)).
          eapply (weakening_typing); eauto. }
        eapply ws_cumul_pb_eq_le. simpl.
        rewrite -{1}eql. simpl.
        rewrite !app_context_assoc.
        rewrite /app_context !app_assoc.

        epose proof (@all_rels_subst_lift c Γ
        (l ++ [{|decl_name := na; decl_body := None; decl_type := decl_type|}]) decl_type).
        assert (#|Δ| = #|c| + S #|l|).
        { rewrite -eql. autorewrite with len. simpl. lia. }
        rewrite H. rewrite length_app /= in X.
        rewrite Nat.add_1_r in X.
        unfold app_context in X.
        rewrite !app_tip_assoc /= in X.
        rewrite -app_assoc.
        forward X by auto.
        apply X; auto. all:eauto with fvs.
        rewrite -app_tip_assoc app_assoc -[(l ++ _) ++ _]app_assoc eql.
        eapply All_local_env_app_inv in Hwf as []. eauto with fvs.
  Qed.

  Lemma red_expand_let {Γ na b ty t} :
    wf_local Σ (Γ ,,, [vdef na b ty]) ->
    is_open_term (Γ ,,, [vdef na b ty]) t ->
    Σ ;;; Γ ,, vdef na b ty ⊢ t ⇝ lift0 1 (subst1 b 0 t).
  Proof using wfΣ.
    intros wfΓ ont.
    pose proof (all_rels_subst Σ [vdef na b ty] Γ t wfΣ wfΓ).
    simpl in X.
    rewrite subst_empty in X.
    rewrite distr_lift_subst.
    eapply into_closed_red => //; eauto with fvs.
  Qed.

  Lemma type_it_mkProd_or_LetIn_inv {Γ Δ t s} :
    Σ ;;; Γ |- it_mkProd_or_LetIn Δ t : tSort s ->
    ∑ Δs ts,
      [× sorts_local_ctx (lift_typing typing) Σ Γ Δ Δs,
          Σ ;;; Γ ,,, Δ |- t : tSort ts,
          wf_sort Σ s &
          leq_sort Σ (sort_of_products Δs ts) s].
  Proof using wfΣ.
    intros h. revert Γ t s h.
    induction Δ; intros.
    - exists [], s; splits. apply h. eauto with pcuic. apply leq_sort_refl.
    - destruct a as [na [b|] ty]; simpl in *;
      rewrite /mkProd_or_LetIn /= in h.
      * specialize (IHΔ _ _ _ h) as (Δs & ts & [sorts IHΔ leq]).
        exists Δs, ts.
        pose proof (PCUICWfUniverses.typing_wf_sort _ IHΔ) as wfts.
        eapply inversion_LetIn in IHΔ as (T & wfty & HT & hlt); auto.
        split; eauto.
        eapply (type_ws_cumul_pb (pb:=Cumul)). eapply HT. apply isType_Sort; pcuic.
        eapply ws_cumul_pb_LetIn_l_inv in hlt; auto.
        eapply ws_cumul_pb_Sort_r_inv in hlt as [u' [redu' cumu']].
        transitivity (tSort u').
        2:{ eapply ws_cumul_pb_compare; eauto with fvs.
            eapply typing_wf_local in HT. eauto with fvs.
            econstructor. eauto with fvs. }
        eapply ws_cumul_pb_red.
        exists (tSort u'), (tSort u'). split; auto.
        3:now constructor.
        transitivity (lift0 1 (T {0 := b})).
        eapply red_expand_let. pcuic.
        eapply type_closed in HT.
        rewrite -is_open_term_closed //.
        change (tSort u') with (lift0 1 (tSort u')).
        eapply (weakening_closed_red (Γ := Γ ,,, Δ) (Γ' := []) (Γ'' := [_])); auto with fvs.
        apply typing_wf_local in HT. eauto with fvs.
        eapply closed_red_refl; eapply typing_wf_local in HT; eauto with fvs.

      * specialize (IHΔ _ _ _ h) as (Δs & ts & [sorts IHΔ leq]).
        eapply inversion_Prod in IHΔ as (s1 & s2 & wfty & Ht & hlt); tea.
        exists (s1 :: Δs), s2. split; tea. split; tas.
        eapply ws_cumul_pb_Sort_inv in hlt.
        transitivity (sort_of_products Δs ts); auto using leq_sort_product.
        simpl. eapply leq_sort_sort_of_products_mon.
        eapply Forall2_same. reflexivity.
        exact: hlt.
  Qed.

  Lemma leq_sort_sort_of_products {u v} :
    leq_sort Σ v (sort_of_products u v).
  Proof using Type.
    induction u; simpl; auto.
    - reflexivity.
    - etransitivity; tea.
      eapply leq_sort_sort_of_products_mon => //.
      eapply Forall2_same. reflexivity.
      eapply leq_sort_product.
  Qed.

  Lemma inversion_it_mkProd_or_LetIn {Γ Δ t s} :
    Σ ;;; Γ |- it_mkProd_or_LetIn Δ t : tSort s ->
    Σ ;;; Γ ,,, Δ |- t : tSort s.
  Proof using wfΣ.
    move/type_it_mkProd_or_LetIn_inv => [Δs [ts [hΔ ht hs leq]]].
    eapply type_Cumul; tea. eapply type_Sort; pcuic.
    eapply cumul_Sort.
    transitivity (sort_of_products Δs ts); auto using leq_sort_product.
    apply leq_sort_sort_of_products.
  Qed.

  Lemma isType_it_mkProd_or_LetIn_app {Γ Δ Δ' args T s} :
    Σ ;;; Γ |- it_mkProd_or_LetIn (Δ ,,, Δ') T : tSort s ->
    subslet Σ Γ args (smash_context [] Δ) ->
    Σ ;;; Γ |- subst_let_expand args Δ (it_mkProd_or_LetIn Δ' T) : tSort s.
  Proof using wfΣ.
    intros Hs sub.
    move: Hs. rewrite it_mkProd_or_LetIn_app.
    move/inversion_it_mkProd_or_LetIn => Hs.
    eapply typing_expand_lets in Hs.
    eapply (PCUICSubstitution.substitution (Δ := [])) in Hs; tea.
  Qed.

  Arguments Nat.leb : simpl never.

  Lemma lift_to_extended_list_k n Γ : map (lift n #|Γ|) (to_extended_list_k Γ 0) =
    to_extended_list_k Γ 0.
  Proof using Type.
    rewrite /to_extended_list_k.
    change [] with (map (lift n #|Γ|) []) at 2.
    rewrite -(Nat.add_0_r #|Γ|).
    generalize 0.
    move:(@nil term).
    induction Γ; simpl; auto.
    intros l n'.
    destruct a as [? [?|] ?].
    specialize (IHΓ l (S n')).
    rewrite Nat.add_succ_r in IHΓ.
    now rewrite Nat.add_1_r IHΓ.
    specialize (IHΓ (tRel n' :: l) (S n')).
    rewrite Nat.add_succ_r in IHΓ.
    rewrite Nat.add_1_r IHΓ. cbn -[leb].
    destruct (leb_spec_Set (S (#|Γ| + n')) n'). lia.
    reflexivity.
  Qed.

  Lemma reln_subst acc s Γ k :
    reln (map (subst s (k + #|Γ|)) acc) k (subst_context s 0 Γ) =
    map (subst s (k + #|Γ|)) (reln acc k Γ).
  Proof using Type.
    induction Γ in acc, s, k |- *; simpl; auto.
    rewrite subst_context_snoc.
    simpl.
    destruct a as [? [?|] ?]; simpl in *.
    specialize (IHΓ acc s (S k)).
    rewrite Nat.add_succ_r !Nat.add_1_r -IHΓ.
    f_equal.
    specialize (IHΓ (tRel k :: acc) s (S k)).
    rewrite Nat.add_succ_r !Nat.add_1_r -IHΓ.
    f_equal.
    simpl.
    destruct (leb_spec_Set (S (k + #|Γ|)) k). lia.
    reflexivity.
  Qed.

  Lemma subst_context_telescope s k Γ : subst_context s k Γ = List.rev (subst_telescope s k (List.rev Γ)).
  Proof using Type.
    now rewrite subst_telescope_subst_context List.rev_involutive.
  Qed.

  Lemma ctx_inst_sub_to_extended_list_k Γ args Δ :
    forall inst : ctx_inst Σ Γ args Δ,
    map (subst0 (ctx_inst_sub inst)) (to_extended_list_k (List.rev Δ) 0) = args.
  Proof using Type.
    induction inst; simpl; rewrite /to_extended_list_k; auto.
    rewrite reln_app. simpl.
    have len := ctx_inst_subst_length inst0.
    rewrite subst_telescope_length in len.
    rewrite List.length_rev.
    f_equal.
    rewrite nth_error_app_ge. lia.
    assert(#|Δ| + 0 - 0 - #|ctx_inst_sub inst0| = 0) as -> by lia.
    cbn. apply lift0_id.
    rewrite -{2}IHinst.
    rewrite -map_subst_app_simpl.
    rewrite -map_map_compose. f_equal.
    simpl. unfold to_extended_list_k.
    epose proof (reln_subst [] [i] (List.rev Δ) 0). simpl in H.
    rewrite subst_context_telescope in H.
    rewrite List.rev_involutive in H. rewrite H.
    now rewrite List.length_rev len.

    rewrite reln_app. simpl.
    have len := ctx_inst_subst_length inst0.
    rewrite subst_telescope_length in len.
    rewrite -{2}IHinst.
    rewrite -map_subst_app_simpl.
    rewrite -map_map_compose. f_equal.
    simpl. unfold to_extended_list_k.
    epose proof (reln_subst [] [b] (List.rev Δ) 0). simpl in H.
    rewrite subst_context_telescope in H.
    rewrite List.rev_involutive in H. rewrite H.
    now rewrite List.length_rev len.
  Qed.

  Lemma spine_subst_subst_to_extended_list_k {Γ args s Δ} :
    spine_subst Σ Γ args s Δ ->
    map (subst0 s) (to_extended_list_k Δ 0) = args.
  Proof using Type.
    intros [_ _ sub _].
    rewrite /to_extended_list_k.
    rewrite -(map_lift0 args).
    generalize 0 at 1 2 3.
    induction sub; simpl; auto.
    intros n.
    rewrite reln_acc.
    rewrite !map_app.
    simpl. rewrite Nat.leb_refl Nat.sub_diag /=.
    simpl.
    f_equal. rewrite -IHsub.
    rewrite reln_lift.
    rewrite (reln_lift 1).
    rewrite -{4}(Nat.add_0_r n).
    rewrite (reln_lift n 0).
    rewrite !map_map_compose.
    apply map_ext.
    intros x. rewrite (subst_app_decomp [a] s).
    f_equal. simpl.
    rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
    rewrite simpl_subst_k //.

    intros n.
    rewrite -IHsub.
    rewrite reln_lift.
    rewrite (reln_lift 1).
    rewrite -{4}(Nat.add_0_r n).
    rewrite (reln_lift n 0).
    rewrite !map_map_compose.
    apply map_ext.
    intros x. rewrite (subst_app_decomp [subst0 s b] s).
    f_equal. simpl.
    rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
    rewrite simpl_subst_k //.
  Qed.

  Lemma spine_subst_subst_to_extended_list_k_gen {Γ args s Δ Δ'} :
    spine_subst Σ Γ args s Δ ->
    to_extended_list_k Δ 0 = to_extended_list_k Δ' 0 ->
    map (subst0 s) (to_extended_list_k Δ' 0) = args.
  Proof using Type.
    intros sp <-; eapply spine_subst_subst_to_extended_list_k; eauto.
  Qed.

  Lemma arity_spine_eq {Γ T T'} :
    isType Σ Γ T' ->
    T = T' -> arity_spine Σ Γ T [] T'.
  Proof using Type. intros H ->; constructor;auto. Qed.

  Lemma typing_spine_wf_local {Γ T args T'} :
    typing_spine Σ Γ T args T' ->
    wf_local Σ Γ.
  Proof using Type.
    move/typing_spine_isType_dom; pcuic.
  Qed.
  Hint Resolve typing_spine_wf_local : pcuic.

  Lemma substitution_ws_cumul_pb_vass {pb : conv_pb} {Γ} {a na ty M N} :
    Σ ;;; Γ |- a : ty ->
    Σ ;;; Γ,, vass na ty ⊢ M ≤[pb] N ->
    Σ ;;; Γ ⊢ M{0 := a} ≤[pb] N{0 := a}.
  Proof using wfΣ.
    intros ha hm.
    eapply (PCUICConversion.substitution_ws_cumul_pb (Γ' := [vass na ty]) (s := [a]) (Γ'':=[])); eauto with pcuic.
  Qed.

  Lemma substitution_ws_cumul_pb_vdef {pb : conv_pb} {Γ} {a na ty M N} :
    wf_local Σ (Γ ,, vdef na a ty) ->
    Σ ;;; Γ,, vdef na a ty ⊢ M ≤[pb] N ->
    Σ ;;; Γ ⊢ M{0 := a} ≤[pb]  N{0 := a}.
  Proof using wfΣ.
    intros ha hm.
    eapply (PCUICConversion.substitution_ws_cumul_pb (Γ' := [vdef na a ty]) (s := [a]) (Γ'':=[])); eauto with pcuic.
    eapply subslet_def_tip. depelim ha. now apply unlift_TermTyp in l.
  Qed.

  Lemma subst0_it_mkProd_or_LetIn s Γ T : subst s 0 (it_mkProd_or_LetIn Γ T) =
    it_mkProd_or_LetIn (subst_context s 0 Γ) (subst s #|Γ| T).
  Proof using Type.
    now rewrite subst_it_mkProd_or_LetIn Nat.add_0_r.
  Qed.

  Lemma typing_spine_inv {Γ Δ : context} {T args args' T'} :
    #|args| = context_assumptions Δ ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
    ∑ args_sub,
      spine_subst Σ Γ args args_sub Δ *
      typing_spine Σ Γ (subst0 args_sub T) args' T'.
  Proof using wfΣ.
    intros len.
    revert args len T.
    induction Δ as [|d Δ] using ctx_length_rev_ind; intros args. simpl.
    destruct args; simpl; try discriminate.
    - intros _ T sp; exists []. split; [repeat constructor|.. ]; auto; rewrite ?subst_empty //.
      all:pcuic.
    - rewrite context_assumptions_app => eq T sp.
      assert (wfΓΔ := isType_it_mkProd_or_LetIn_wf_local (Δ := Δ ++ [d])
        (typing_spine_isType_dom sp)).
      rewrite it_mkProd_or_LetIn_app in sp.
      destruct d as [? [b|] ?]; simpl in *.
      + rewrite Nat.add_0_r in eq.
        eapply typing_spine_letin_inv in sp => //.
        rewrite /subst1 subst_it_mkProd_or_LetIn in sp.
        specialize (X (subst_context [b] 0 Δ) ltac:(now autorewrite with len)).
        specialize (X args ltac:(now rewrite context_assumptions_subst)).
        rewrite Nat.add_0_r in sp.
        destruct (X _ sp) as [args_sub [sps sp']].
        exists (args_sub ++ [b]); split; auto; [constructor|..]; pcuic.
        * eapply context_subst_app_inv.
          simpl. rewrite skipn_0.
          move: (context_subst_length sps).
          len.
          move=> eq'. rewrite eq'.
          rewrite skipn_all_app firstn_app_left //.
          split; auto. apply sps. rewrite -{2}(subst_empty 0 b).
          constructor. constructor.
        * eapply subslet_app => //. eapply sps.
          rewrite -{1}(subst_empty 0 b).
          repeat constructor. rewrite !subst_empty.
          eapply All_local_env_app_inv in wfΓΔ as [_ wf].
          eapply All_local_env_app_inv in wf as [wfd _].
          depelim wfd. now eapply unlift_TermTyp.
        * rewrite subst_app_simpl.
          move: (context_subst_length sps).
          now  autorewrite with len => <-.

      + rewrite /mkProd_or_LetIn /= in sp.
        destruct args as [|a args]; simpl in eq; try lia.
        specialize (X (subst_context [a] 0 Δ) ltac:(now autorewrite with len)).
        specialize (X args ltac:(now rewrite context_assumptions_subst)).
        specialize (X (subst [a] #|Δ| T)).
        dependent elimination sp as [spcons isty isty' e tyhd sp].
        eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna conv cum]; auto.
        eapply (substitution_ws_cumul_pb_vass (a:=hd0)) in cum; auto.
        assert (Σ ;;; Γ |- hd0 : decl_type).
        { eapply (type_ws_cumul_pb (pb:=Conv)); tea. 2:now symmetry.
          now eapply isType_tProd in isty as []; eauto with pcuic. }
        eapply isType_apply in isty; tea.
        eapply typing_spine_strengthen in sp. 3:tea. 2:tas.
        rewrite /subst1 subst0_it_mkProd_or_LetIn in sp; auto.
        specialize (X sp).
        destruct X as [args_sub [sps sp']].
        exists (args_sub ++ [hd0]); split; auto; [constructor|..]; pcuic.
        * eapply context_subst_app_inv.
          simpl. rewrite skipn_S skipn_0.
          move: (context_subst_length sps). len.
          move=> eq'. rewrite eq'.
          rewrite skipn_all_app firstn_app_left //.
          split; auto. apply sps.
          eapply (context_subst_ass _ []). constructor.
        * eapply subslet_app => //. eapply sps.
          rewrite -{1}(subst_empty 0 hd0).
          repeat constructor. now rewrite !subst_empty.
        * rewrite subst_app_simpl.
          move: (context_subst_length sps).
          now autorewrite with len => <-.
  Qed.

  Arguments ctx_inst_nil {typing} {Γ}.
  Arguments PCUICTyping.ctx_inst_ass {typing} {Γ} {na t i inst Δ}.
  Arguments PCUICTyping.ctx_inst_def {typing} {Γ} {na b t inst Δ}.

  Lemma spine_subst_ctx_inst_sub {Γ args argsub Δ} (sp : spine_subst Σ Γ args argsub Δ) :
    ctx_inst_sub (spine_subst_ctx_inst sp) = argsub.
  Proof using Type.
    set (ci := spine_subst_ctx_inst sp).
    pose proof (ctx_inst_sub_spec ci).
    eapply make_context_subst_spec in H. rewrite List.rev_involutive in H.
    now rewrite (context_subst_fun sp H).
  Qed.

  Lemma typing_spine_ctx_inst {Γ Δ : context} {T args args' T'} :
    #|args| = context_assumptions Δ ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
    ∑ argsi : ctx_inst Σ Γ args (List.rev Δ),
      typing_spine Σ Γ (subst0 (ctx_inst_sub argsi) T) args' T'.
  Proof using wfΣ.
    move=> len /(typing_spine_inv len) [argsub [sp Hargs']].
    exists (spine_subst_ctx_inst sp).
    now rewrite spine_subst_ctx_inst_sub.
  Qed.

  Lemma typing_spine_app {Γ ty args na A B arg} :
    typing_spine Σ Γ ty args (tProd na A B) ->
    Σ ;;; Γ |- arg : A ->
    typing_spine Σ Γ ty (args ++ [arg]) (B {0 := arg}).
  Proof using wfΣ.
    intros H; revert arg.
    dependent induction H.
    - intros arg Harg. simpl. econstructor; eauto.
      eapply isType_apply in i0; tea.
      constructor; auto. eauto with fvs pcuic.
    - intros arg Harg.
      econstructor; eauto.
  Qed.

  Lemma typing_spine_nth_error {Γ Δ T args n arg concl} :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args concl ->
    nth_error args n = Some arg ->
    (n < context_assumptions Δ) ->
    ∑ decl, (nth_error (smash_context [] Δ) (context_assumptions Δ - S n) = Some decl) *
      (Σ ;;; Γ |- arg : subst0 (List.rev (firstn n args)) (decl_type decl)).
  Proof using wfΣ.
    revert n args T.
    induction Δ using ctx_length_rev_ind => /= // n args T.
    - simpl. lia.
    - rewrite it_mkProd_or_LetIn_app context_assumptions_app.
      destruct d as [na [b|] ty]; simpl.
      + move=> sp. rewrite /= Nat.add_0_r. simpl.
        eapply typing_spine_letin_inv in sp => //.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [b] 0 Γ0) ltac:(len; lia) n args _ sp).
        rewrite context_assumptions_subst in X.
        move=> Hnth Hn. specialize (X Hnth Hn) as [decl [nthsmash Hty]].
        exists decl; split; auto.
        rewrite smash_context_app. simpl.
        now rewrite -(smash_context_subst []) /= subst_context_nil.
      + simpl.
        move=> sp.
        dependent elimination sp as [spnil _ _ _|spcons isty isty' e e' sp]; rewrite ?nth_error_nil //.
        destruct n as [|n']; simpl.
        * move=> [=] eq; subst hd0.
          move=> Hctx. exists {| decl_name := na; decl_body := None; decl_type := ty |}.
          rewrite smash_context_app. simpl.
          rewrite nth_error_app_ge; rewrite smash_context_length /=. lia.
          assert(context_assumptions Γ0 + 1 - 1 - context_assumptions Γ0 = 0) as -> by lia.
          split; auto. rewrite subst_empty.
          pose proof (isType_wf_local isty).
          eapply ws_cumul_pb_Prod_Prod_inv in e as [conv cum]; auto.
          eapply (type_ws_cumul_pb (pb:=Conv)); eauto.
          eapply isType_tProd in isty as [dom codom]; eauto with pcuic. cbn in *.
          now symmetry.
        * move=> Hnth Hn'.
          pose proof (isType_wf_local isty).
          eapply isType_tProd in isty as [dom' codom']; auto. cbn in *.
          eapply ws_cumul_pb_Prod_Prod_inv in e as [conv cum e]; auto. simpl in codom'.
          assert (Σ ;;; Γ |- hd0 : ty).
          { eapply (type_ws_cumul_pb (pb:=Conv)); eauto with pcuic. now symmetry. }
          unshelve eapply (isType_subst (Δ:=[vass na ty]) (s := [hd0])) in codom'.
          2:{ now eapply subslet_ass_tip. }
          specialize (X (subst_context [hd0] 0 Γ0) ltac:(autorewrite with len; lia)).
          eapply substitution_ws_cumul_pb_vass in e; tea.
          specialize (X n' tl0 (subst [hd0] #|Γ0| T)).
          forward X.
          rewrite -subst0_it_mkProd_or_LetIn.
          eapply typing_spine_strengthen; eauto.
          specialize (X Hnth).
          forward X by (rewrite context_assumptions_subst; lia).
          destruct X as [decl [Hnth' Hty]].
          rewrite (smash_context_subst []) nth_error_subst_context in Hnth'.
          rewrite smash_context_app. simpl.
          rewrite context_assumptions_subst in Hnth'.
          replace (context_assumptions Γ0  + 1 - S (S n')) with
            (context_assumptions Γ0 - S n') by lia.
          rewrite nth_error_app_context_lt ?smash_context_length. lia.
          destruct (nth_error (smash_context [] Γ0) _) eqn:Heq; try discriminate.
          simpl in Hnth'. exists c; split; auto.
          noconf Hnth'.
          rewrite /= smash_context_length /= in Hty.
          replace ((context_assumptions Γ0 - S (context_assumptions Γ0 - S n') + 0))
            with n' in Hty by lia.
          rewrite subst_app_simpl /= List.length_rev firstn_length_le.
          now eapply nth_error_Some_length in Hnth.
          assumption.
  Qed.

  Import PCUICInstDef PCUICInstConv.

  Local Open Scope sigma.

  Lemma spine_subst_smash {Γ inst s Δ} :
    spine_subst Σ Γ inst s Δ ->
    spine_subst Σ Γ inst (List.rev inst) (smash_context [] Δ).
  Proof using wfΣ.
    intros [].
    assert (context_subst (smash_context [] Δ) inst (List.rev inst)).
    { apply closed_wf_local in spine_dom_wf0.
      clear -inst_ctx_subst0 spine_dom_wf0. induction inst_ctx_subst0.
      constructor. rewrite List.rev_app_distr /=.
      rewrite smash_context_acc. simpl.
      constructor. auto.
      simpl. rewrite smash_context_acc. simpl. auto.
      auto. }
    split; auto.
    - eapply All_local_env_app; auto.
      eapply wf_local_rel_smash_context; auto.
    - induction inst_subslet0 in inst, inst_ctx_subst0, spine_codom_wf0 |- *.
      depelim inst_ctx_subst0.
      + constructor.
      + depelim inst_ctx_subst0.
        simpl. rewrite smash_context_acc.
        simpl. rewrite List.rev_app_distr.
        depelim spine_codom_wf0.
        constructor. now apply IHinst_subslet0.
        eapply meta_conv. eauto.
        simpl.
        autorewrite with sigma.
        apply inst_ext.
        unfold Upn. rewrite subst_consn_compose.
        autorewrite with sigma.
        apply subst_consn_proper.
        2:{ (rewrite subst_consn_shiftn; try now autorewrite with len); [].
            autorewrite with sigma.
            rewrite subst_consn_shiftn //.
            rewrite List.length_rev.
            now apply context_subst_length2 in inst_ctx_subst0. }
        clear -inst_ctx_subst0.
        rewrite map_inst_idsn. now autorewrite with len.
        now apply context_subst_extended_subst.
      + simpl. rewrite smash_context_acc.
        simpl. depelim spine_codom_wf0.
        depelim inst_ctx_subst0; apply IHinst_subslet0; auto.
  Qed.

  Lemma ctx_inst_sub_subst {Γ Δ : context} {args} :
    forall ci : ctx_inst Σ Γ args (List.rev Δ),
    ctx_inst_sub ci = map (subst0 (List.rev args)) (extended_subst Δ 0).
  Proof using Type.
    intros ci.
    pose proof (ctx_inst_sub_spec ci).
    eapply make_context_subst_spec in H.
    revert H. generalize (ctx_inst_sub ci). clear ci.
    intros l cs.
    apply context_subst_extended_subst in cs.
    rewrite List.rev_involutive in cs.
    rewrite cs. apply map_ext => t.
    now rewrite subst0_inst.
  Qed.

  Lemma typing_spine_ctx_inst_smash {Γ Δ : context} {T args args' T'} :
    #|args| = context_assumptions Δ ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
    spine_subst Σ Γ args (List.rev args) (smash_context [] Δ) *
      typing_spine Σ Γ (subst_let_expand (List.rev args) Δ T) args' T'.
  Proof using wfΣ.
    intros.
    pose proof (typing_spine_isType_dom X).
    eapply isType_it_mkProd_or_LetIn_wf_local in X0.
    eapply typing_spine_ctx_inst in X as [argsi sp]; tea.
    unshelve epose proof (ctx_inst_spine_subst _ argsi).
    1: now pcuic.
    pose proof (spine_subst_smash X). split => //.
    rewrite (ctx_inst_sub_subst argsi) in sp.
    rewrite /subst_let_expand.
    rewrite /expand_lets /expand_lets_k /=.
    rewrite distr_subst. len.
    rewrite simpl_subst_k. now len.
    assumption.
  Qed.

  Lemma shift_subst_consn_tip t : ↑ ∘s ([t] ⋅n ids) ≐1 ids.
  Proof using Type.
    rewrite /subst_consn; intros [|i] => /= //.
  Qed.


  Lemma subst_context_lift_id Γ k : subst_context [tRel 0] k (lift_context 1 (S k) Γ) = Γ.
  Proof using Type.
    rewrite subst_context_alt lift_context_alt.
    rewrite mapi_compose.
    replace Γ with (mapi (fun k x => x) Γ) at 2.
    2:unfold mapi; generalize 0; induction Γ; simpl; intros; auto; congruence.
    apply mapi_ext.
    len.
    intros n [? [?|] ?]; unfold lift_decl, subst_decl, map_decl; simpl.
    generalize (Nat.pred #|Γ| - n).
    intros.
    now rewrite !Nat.add_succ_r !subst_rel0_lift_id.
    now rewrite !Nat.add_succ_r !subst_rel0_lift_id.
  Qed.

  Lemma subst_extended_subst s Γ : extended_subst (subst_context s 0 Γ) 0 =
    map (subst s (context_assumptions Γ)) (extended_subst Γ 0).
  Proof using Type.
    induction Γ as [|[na [b|] ty] Γ]; simpl; auto; rewrite subst_context_snoc /=;
      autorewrite with len; rewrite ? (lift_extended_subst _ 1); f_equal; auto.
    - rewrite IHΓ.
      rewrite commut_lift_subst_rec. auto.
      rewrite distr_subst. now autorewrite with len.
    - rewrite IHΓ.
      rewrite !map_map_compose. apply map_ext.
      intros x.
      erewrite (commut_lift_subst_rec). lia_f_equal.
      lia.
  Qed.

  Lemma map_subst_extended_subst_lift_to_extended_list_k Γ :
  map (subst0 (extended_subst Γ 0)) (map (lift (context_assumptions Γ) #|Γ|)
    (to_extended_list Γ)) = to_extended_list (smash_context [] Γ).
  Proof using Type.
    induction Γ as [|[na [b|] ty] ?]; cbn; auto.
    rewrite (reln_lift 1).
    rewrite -[reln [] 0 (smash_context [] Γ)]IHΓ.
    rewrite !map_map_compose. apply map_ext => x.
    rewrite -Nat.add_1_r -(permute_lift _ _ _ 1). lia.
    rewrite (subst_app_decomp [_]).
    rewrite simpl_subst_k /= //.
    rewrite reln_acc (reln_lift 1) map_app /=.
    rewrite smash_context_acc /= (reln_acc [tRel 0]) (reln_lift 1) map_app /=.
    f_equal.
    rewrite -[reln [] 0 (smash_context [] Γ)]IHΓ.
    rewrite !map_map_compose. apply map_ext => x.
    rewrite -(Nat.add_1_r #|Γ|) -(permute_lift _ _ _ 1). lia.
    rewrite (subst_app_decomp [_]).
    rewrite simpl_subst_k /= //.
    rewrite lift_extended_subst.
    rewrite distr_lift_subst. f_equal.
    autorewrite with len. rewrite simpl_lift; lia_f_equal.
  Qed.

  Lemma arity_spine_it_mkProd_or_LetIn_smash {Γ Δ T args args' T'} :
    subslet Σ Γ (List.rev args) (smash_context [] Δ) ->
    arity_spine Σ Γ (subst_let_expand (List.rev args) Δ T) args' T' ->
    arity_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using Type.
    intros subsl asp.
    rewrite /subst_let_expand /expand_lets /expand_lets_k in asp.
    move: Δ T args subsl asp.
    induction Δ using ctx_length_rev_ind => T args subsl asp.
    - simpl in subsl. simpl in asp. rewrite subst_empty lift0_id in asp. depelim subsl.
      rewrite /= H !subst_empty in asp. destruct args => //.
      simpl in H. apply (f_equal (@List.length _)) in H. simpl in H.
      rewrite length_app /= in H. lia.
    - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      destruct d as [na [b|] ty]; simpl in *.
      * constructor. rewrite /subst1 subst_it_mkProd_or_LetIn.
        rewrite Nat.add_0_r.
        rewrite smash_context_app smash_context_acc /= in subsl.
        rewrite  lift0_id /= subst_context_nil app_nil_r
          lift0_context in subsl.
        rewrite -(smash_context_subst []) /= subst_context_nil in subsl.
        rewrite subst_empty in subsl.
        apply (X (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)
          (subst [b] #|Γ0| T) _ subsl).
        rewrite extended_subst_app /= in asp.
        rewrite !subst_empty lift0_id lift0_context in asp.
        erewrite subst_app_simpl' in asp.
        2:now autorewrite with len.
        simpl in asp. autorewrite with len in asp.
        simpl in asp.
        autorewrite with len.
        now rewrite -{1}(Nat.add_0_r #|Γ0|) distr_lift_subst_rec /= Nat.add_0_r.
      * simpl in *. len in asp.
        simpl in asp.
        assert (len:=subslet_length subsl).
        len in len. simpl in len.
        rewrite Nat.add_1_r in len.
        rewrite smash_context_app smash_context_acc /= in subsl.
        rewrite subst_context_lift_id in subsl.
        eapply subslet_app_inv in subsl as [subsl subsr].
        destruct args; simpl in * => //.
        noconf len.
        len in subsl; len in subsr. simpl in *.
        rewrite -H in subsl subsr. rewrite skipn_all_app_eq ?List.length_rev in subsl subsr => //.
        rewrite (firstn_app_left) ?firstn_0 ?app_nil_r ?List.length_rev in subsr => //.
        depelim subsl.
        constructor. now rewrite subst_empty in t1.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
        rewrite -(smash_context_subst []) /= in subsr.
        apply (X (subst_context [t] 0 Γ0) ltac:(now autorewrite with len)
          (subst [t] #|Γ0| T) _ subsr).
        rewrite extended_subst_app /= in asp.
        rewrite subst_context_lift_id in asp.
        erewrite subst_app_simpl' in asp.
        2:now autorewrite with len.
        simpl in asp.
        autorewrite with len.
        rewrite -{1}(Nat.add_0_r #|Γ0|) distr_lift_subst_rec /= Nat.add_0_r.
        move: asp. rewrite subst_app_simpl /=; autorewrite with len.
        rewrite distr_subst. autorewrite with len.
        rewrite (distr_subst_rec _ _ [t]).
        cbn [map]. rewrite -H. erewrite (subst_rel_eq _ _ 0) =>//.
        simpl; autorewrite with len.
        rewrite (Nat.add_1_r #|args|).
        erewrite <-(simpl_lift T #|args| _ 1 (#|Γ0| + 1 + #|args|)).
        all:try lia.
        rewrite (simpl_subst_k) //.
        now rewrite subst_extended_subst H.
  Qed.

  (** This shows that we can promote an argument spine for a given context to
      a spine for a context whose types are higher in the cumulativity relation.
  *)

  Lemma subslet_cumul {pb Δ args Γ Γ'} :
    assumption_context Γ -> assumption_context Γ' ->
    wf_local Σ (Δ ,,, Γ) ->
    wf_local Σ (Δ ,,, Γ') ->
    ws_cumul_ctx_pb_rel pb Σ Δ Γ Γ' ->
    subslet Σ Δ args Γ -> subslet Σ Δ args Γ'.
  Proof using wfΣ.
    intros ass ass' wf wf' a2.
    destruct a2.
    induction a in wf, wf', args, ass, ass' |- *.
    - inversion 1; constructor.
    - intros subsl; depelim subsl.
      2:{ exfalso; inv ass. }
      specialize (IHa s).
      forward IHa by now depelim ass.
      forward IHa by now depelim ass'.
      depelim wf.
      depelim wf'.
      2:{ exfalso; inv ass'. }
      specialize (IHa wf wf' subsl).
      constructor; auto.
      eapply type_ws_cumul_pb; eauto. depelim p.
      eapply isType_subst. exact IHa. eauto with pcuic.
      depelim p.
      eapply (PCUICConversion.substitution_ws_cumul_pb (s:=s) (Γ' := Γ) (Γ'' := [])); eauto.
  Qed.

  Lemma spine_subst_cumul {Δ args Γ Γ'} :
    assumption_context Γ -> assumption_context Γ' ->
    wf_local Σ (Δ ,,, Γ) ->
    wf_local Σ (Δ ,,, Γ') ->
    ws_cumul_ctx_pb_rel Cumul Σ Δ Γ Γ' ->
    spine_subst Σ Δ args (List.rev args) Γ ->
    spine_subst Σ Δ args (List.rev args) Γ'.
  Proof using wfΣ.
    intros ass ass' wf wf' a2.
    intros []; split; auto.
    - clear -a2 ass ass' inst_ctx_subst0.
      revert inst_ctx_subst0; generalize (List.rev args).
      intros l ctxs.
      induction ctxs in ass, Γ', ass', a2 |- *; depelim a2; try (simpl in H; noconf H); try constructor; auto.
      * depelim a. constructor.
      * depelim a. depelim a0. econstructor. eapply IHctxs. now depelim ass.
        now depelim ass'. red. split => //.
      * exfalso; depelim ass.
    - eapply subslet_cumul. 6:eauto. all:eauto.
  Qed.

  Lemma type_mkApps {Γ t u T t_ty} :
    Σ ;;; Γ |- t : t_ty ->
    typing_spine Σ Γ t_ty u T ->
    Σ ;;; Γ |- mkApps t u : T.
  Proof using Type.
    intros Ht Hsp.
    revert t Ht. induction Hsp; simpl; auto.
    intros t Ht. eapply type_ws_cumul_pb; eauto.

    intros.
    specialize (IHHsp (tApp t0 hd)). apply IHHsp.
    destruct i as (_ & s & Hs & _).
    eapply type_App; eauto. eapply i0.2.π2.1.
    eapply type_ws_cumul_pb; eauto.
  Qed.

  Lemma pre_type_mkApps_arity {Γ t u tty T} :
    Σ;;; Γ |- t : tty -> isType Σ Γ tty ->
    arity_spine Σ Γ tty u T ->
    Σ;;; Γ |- mkApps t u : T.
  Proof using wfΣ.
    intros Ht Hty Har.
    eapply type_mkApps; tea.
    eapply wf_arity_spine_typing_spine.
    constructor; tas.
  Qed.

  Lemma map_subst_extended_subst Γ k :
    map (subst0 (List.rev (to_extended_list_k Γ k))) (extended_subst Γ 0) =
    all_rels Γ k 0.
  Proof using Type.
    unfold to_extended_list_k.
    induction Γ in k |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl.
    f_equal. len.
    rewrite lift0_id.
    rewrite distr_subst. autorewrite with len.
    rewrite simpl_subst_k. len.
    rewrite IHΓ. now rewrite Nat.add_1_r.
    rewrite IHΓ. now rewrite Nat.add_1_r.
    rewrite reln_acc List.rev_app_distr /=.
    rewrite (map_subst_app_decomp [tRel k]).
    simpl. f_equal. rewrite lift_extended_subst.
    rewrite map_map_compose -IHΓ. apply map_ext.
    intros x. f_equal. now rewrite Nat.add_1_r.
    len. simpl.
    rewrite simpl_subst // lift0_id //.
  Qed.

  Lemma subst_ext_list_ext_subst Γ k' k t :
    subst (List.rev (to_extended_list_k Γ k)) k'
      (subst (extended_subst Γ 0) k'
        (lift (context_assumptions Γ) (k' + #|Γ|) t)) =
    subst (all_rels Γ k 0) k' t.
  Proof using Type.
    epose proof (distr_subst_rec _ _ _ 0 _).
    rewrite Nat.add_0_r in H. rewrite -> H. clear H.
    len.
    rewrite simpl_subst_k. now len.
    now rewrite map_subst_extended_subst.
  Qed.

  Lemma expand_lets_ctx_o_lets Γ k k' Δ :
    subst_context (List.rev (to_extended_list_k Γ k)) k' (expand_lets_k_ctx Γ k' Δ) =
    subst_context (all_rels Γ k 0) k' Δ.
  Proof using Type.
    revert k k'; induction Δ using rev_ind; simpl; auto.
    intros k k'; rewrite expand_lets_k_ctx_decl /map_decl /=.
    rewrite !subst_context_app /=.
    simpl; unfold app_context.
    f_equal. specialize (IHΔ k (S k')). simpl in IHΔ.
    rewrite -IHΔ.
    destruct x; simpl.
    destruct decl_body; simpl in * => //.
    unfold subst_context, fold_context_k; simpl.
    f_equal.
    unfold expand_lets_k, subst_context => /=.
    unfold map_decl; simpl. unfold map_decl. simpl. f_equal.
    destruct (decl_body x); simpl. f_equal.
    now rewrite subst_ext_list_ext_subst. auto.
    now rewrite subst_ext_list_ext_subst.
  Qed.

  Lemma subst_subst_context s k s' Γ :
    subst_context s k (subst_context s' 0 Γ) =
    subst_context (map (subst s k) s') 0 (subst_context s (#|s'| + k) Γ).
  Proof using Type.
    rewrite !subst_context_alt.
    rewrite !mapi_compose; len.
    eapply mapi_ext. intros n x.
    rewrite /subst_decl !compose_map_decl.
    apply map_decl_ext. intros t.
    rewrite Nat.add_0_r.
    remember (Nat.pred #|Γ| - n) as i.
    rewrite distr_subst_rec. lia_f_equal.
  Qed.

  Lemma closed_ctx_subst n k ctx : closedn_ctx k ctx = true -> subst_context n k ctx = ctx.
  Proof using Type.
    induction ctx in n, k |- *; auto.
    simpl.
    move/andb_and => /= [Hctx Hd].
    rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
  Qed.

  Lemma expand_lets_k_ctx_subst_id' Γ k Δ :
    closed_ctx Γ ->
    closedn_ctx #|Γ| Δ ->
    expand_lets_k_ctx Γ k (subst_context (List.rev (to_extended_list_k Γ k)) 0
      (expand_lets_ctx Γ Δ)) =
    subst_context (List.rev (to_extended_list_k (smash_context [] Γ) k)) 0
      (expand_lets_ctx Γ Δ).
  Proof using Type.
    intros clΓ clΔ.
    assert (closed_ctx (Γ ,,, Δ)).
    { rewrite closedn_ctx_app clΓ //. }
    rewrite {1}/expand_lets_k_ctx.
    rewrite PCUICClosed.closed_ctx_lift.
    rewrite -(Nat.add_0_r (k + #|Γ|)).
    eapply closedn_ctx_subst. simpl; len'.
    eapply closedn_ctx_expand_lets. eapply closedn_ctx_upwards; tea. lia.
    rewrite forallb_rev. now eapply closedn_to_extended_list_k.
    rewrite subst_subst_context. len'.
    rewrite map_rev extended_subst_to_extended_list_k.
    rewrite (closed_ctx_subst _ (context_assumptions Γ + k)) //.
    rewrite Nat.add_comm. eapply closedn_ctx_expand_lets => //.
    eapply closedn_ctx_upwards; eauto. lia.
  Qed.

  Local Set SimplIsCbn.

  Lemma subst_lift1 x s : (subst0 (x :: s) ∘ lift0 1) ≐1 subst0 s.
  Proof using Type.
    intros t. erewrite <- PCUICParallelReduction.subst_skipn'.
    rewrite lift0_id. simpl. now rewrite skipn_S skipn_0.
    lia. simpl. lia.
  Qed.

  Lemma map_subst_lift1 x s l : map (subst0 (x :: s) ∘ lift0 1) l = map (subst0 s) l.
  Proof using Type.
    apply map_ext. apply subst_lift1.
  Qed.

  Lemma subst_extended_lift Γ k :
    closed_ctx Γ ->
    map (subst0 (List.rev (to_extended_list_k (smash_context [] Γ) k)))
      (extended_subst Γ 0) = extended_subst Γ k.
  Proof using Type.
    induction Γ in k |- *; intros cl; simpl; auto.
    destruct a as [na [b|] ty] => /=.
    len.
    rewrite closed_ctx_decl in cl. move/andb_and: cl => [cld clΓ].
    simpl. f_equal.
    rewrite distr_subst. len.
    simpl in cld.
    rewrite IHΓ //. f_equal.
    rewrite simpl_subst_k ?lengths // lift_closed //. now move/andb_and: cld => /= //.
    rewrite IHΓ //.

    cbn -[nth_error] => /=. rewrite nth_error_rev; len.
    rewrite List.rev_involutive /=.
    rewrite smash_context_acc /=.
    f_equal; auto. rewrite reln_acc /=.
    rewrite nth_error_app_ge; len.
    replace (context_assumptions Γ - 0 - context_assumptions Γ) with 0 by lia.
    now simpl.
    rewrite reln_acc List.rev_app_distr /=.
    rewrite lift_extended_subst.
    rewrite map_map_compose.
    rewrite map_subst_lift1.
    rewrite closed_ctx_decl in cl. move/andb_and: cl => [cld clΓ].
    now rewrite IHΓ // Nat.add_1_r.
  Qed.

  Lemma closed_subst_map_lift s n k t :
    closedn (#|s| + k) t ->
    subst (map (lift0 n) s) k t = subst s (n + k) (lift n k t).
  Proof using Type.
    intros cl.
    sigma.
    eapply inst_ext_closed; tea.
    intros x Hx.
    rewrite -Upn_Upn Nat.add_comm Upn_Upn Upn_compose shiftn_Upn; sigma.
    now rewrite !Upn_subst_consn_lt; len; try lia.
  Qed.

  Lemma subst_map_lift_lift_context (Γ : context) k s :
    closedn_ctx #|s| Γ ->
    subst_context (map (lift0 k) s) 0 Γ =
    subst_context s k (lift_context k 0 Γ).
  Proof using Type.
    induction Γ as [|[? [] ?] ?] in k |- *; intros cl; auto;
      rewrite lift_context_snoc !subst_context_snoc /= /subst_decl /map_decl /=;
      rewrite closed_ctx_decl in cl;  move/andb_and: cl => [cld clΓ].
    - rewrite IHΓ //. f_equal. f_equal. f_equal;
      len.
      rewrite closed_subst_map_lift //. now move/andb_and: cld => /=.
      lia_f_equal.
      len.
      rewrite closed_subst_map_lift //. now move/andb_and: cld => /=.
      lia_f_equal.
    - f_equal. apply IHΓ => //.
      f_equal; len. rewrite closed_subst_map_lift //.
      lia_f_equal.
  Qed.

  Lemma subst_context_lift_context_comm (Γ : context) n k k' s :
    k' = k + n ->
    subst_context s k' (lift_context n k Γ) =
    lift_context n k (subst_context s k Γ).
  Proof using Type.
    intros ->; induction Γ as [|[? [] ?] ?] in |- *; auto;
      rewrite !lift_context_snoc !subst_context_snoc !lift_context_snoc /=
        /subst_decl /lift_decl /map_decl /=.
    - rewrite IHΓ //. f_equal. f_equal. f_equal; len.
      rewrite commut_lift_subst_rec. lia. lia_f_equal.
      len.
      rewrite commut_lift_subst_rec. lia. lia_f_equal.
    - f_equal. apply IHΓ => //.
      f_equal; len. rewrite commut_lift_subst_rec //; try lia.
      lia_f_equal.
  Qed.

  Lemma spine_subst_extended_subst {Γ inst s Δ} :
    spine_subst Σ Γ inst s Δ ->
    s = map (subst0 (List.rev inst)) (extended_subst Δ 0).
  Proof using Type.
    intros [_ _ sp _]. now apply context_subst_subst_extended_subst in sp.
  Qed.


  Lemma spine_subst_app {Γ Δ Δ' inst inst' insts} :
    #|inst| = context_assumptions Δ ->
    wf_local Σ (Γ ,,, Δ ,,, Δ') ->
    spine_subst Σ Γ inst (skipn #|Δ'| insts) Δ ->
    spine_subst Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') ->
    spine_subst Σ Γ (inst ++ inst') insts (Δ ,,, Δ').
  Proof using Type.
    intros len wf [wfdom wfcodom cs subst] [wfdom' wfcodom' cs' subst'].
    split; auto.
    now rewrite app_context_assoc.
    eapply context_subst_app_inv; split; auto.
    rewrite skipn_all_app_eq; try lia. auto.
    rewrite (firstn_app_left) ?Nat.add_0_r // firstn_0 // app_nil_r //.
    rewrite -(firstn_skipn #|Δ'| insts).
    eapply subslet_app; auto.
  Qed.
  Lemma context_assumptions_lift {n k Γ} : context_assumptions (lift_context n k Γ) = context_assumptions Γ.
  Proof using Type. apply context_assumptions_fold. Qed.
  Lemma context_assumptions_subst {n k Γ} : context_assumptions (subst_context n k Γ) = context_assumptions Γ.
  Proof using Type. apply context_assumptions_fold. Qed.
  Hint Rewrite @context_assumptions_lift @context_assumptions_subst : len.

  Lemma ws_cumul_ctx_pb_rel'_context_assumptions {pb} {Γ} {Δ Δ'} :
    All2_fold
      (fun Γ' _ : context =>
        All_decls_alpha_pb pb
          (fun pb (x y : term) => Σ ;;; Γ,,, Γ' ⊢ x ≤[pb] y)) Δ Δ' ->
    context_assumptions Δ = context_assumptions Δ'.
  Proof using Type.
    induction 1; auto.
    depelim p; simpl; auto. lia.
  Qed.

  Lemma ws_cumul_ctx_pb_rel_context_assumptions {pb} {Γ} {Δ Δ'} :
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    context_assumptions Δ = context_assumptions Δ'.
  Proof using Type.
    intros []. now eapply ws_cumul_ctx_pb_rel'_context_assumptions.
  Qed.

  (* Lemma subslet_subs {cf} {Σ} {wfΣ : wf Σ} {Γ i Δ Δ'} :
  ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
  ctx_inst Σ Γ i (Li *)

  Lemma ws_cumul_pb_expand_lets_k {pb} {Γ Δ Γ'} {T T'} :
    wf_local Σ (Γ ,,, Δ) ->
    Σ ;;; Γ ,,, Δ ,,, Γ' ⊢ T ≤[pb] T' ->
    Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' ⊢
      expand_lets_k Δ #|Γ'| T ≤[pb] expand_lets_k Δ #|Γ'| T'.
  Proof using wfΣ.
    intros wf cum.
    rewrite -app_context_assoc in cum.
    eapply (weakening_ws_cumul_pb (Γ'' := smash_context [] Δ)) in cum; tea.
    rewrite /expand_lets /expand_lets_k.
    rewrite lift_context_app in cum.
    rewrite app_context_assoc in cum.
    eapply substitution_ws_cumul_pb in cum; tea.
    len in cum; tea.
    destruct (All_local_env_app_inv wf).
    simpl.
    len.
    now eapply PCUICContexts.subslet_extended_subst.
    eapply wf_local_smash_end in wf. eauto with fvs.
  Qed.

  Lemma ws_cumul_pb_expand_lets {pb} {Γ} {Δ} {T T'} :
    wf_local Σ (Γ ,,, Δ) ->
    Σ ;;; Γ ,,, Δ ⊢ T ≤[pb] T' ->
    Σ ;;; Γ ,,, smash_context [] Δ ⊢ expand_lets Δ T ≤[pb] expand_lets Δ T'.
  Proof using wfΣ.
    intros wf cum.
    eapply (weakening_ws_cumul_pb (Γ'' := smash_context [] Δ)) in cum; tea.
    rewrite /expand_lets /expand_lets_k.
    eapply (PCUICConversion.substitution_ws_cumul_pb (Γ'' := [])) in cum; tea. len in cum; tea.
    destruct (All_local_env_app_inv wf).
    simpl.
    len.
    now eapply PCUICContexts.subslet_extended_subst.
    eapply wf_local_smash_end in wf. eauto with fvs.
  Qed.

  Lemma ws_cumul_pb_terms_lift {Γ Δ args args'} :
    is_closed_context (Γ,,, Δ) ->
    ws_cumul_pb_terms Σ Γ args args' ->
    ws_cumul_pb_terms Σ (Γ ,,, Δ) (map (lift0 #|Δ|) args) (map (lift0 #|Δ|) args').
  Proof using wfΣ.
    intros onctx conv.
    eapply All2_map.
    eapply (All2_impl conv).
    intros x y eqxy.
    eapply (weakening_ws_cumul_pb (Γ' := [])) => //.
  Qed.

  Lemma ws_cumul_pb_le_le {pb Γ T T'} :
    Σ ;;; Γ ⊢ T ≤[pb] T' -> Σ ;;; Γ ⊢ T ≤ T'.
  Proof using Type.
    destruct pb; eauto.
    eapply ws_cumul_pb_eq_le.
  Qed.

  Lemma ws_cumul_ctx_pb_le_le {pb Γ Γ'} :
    Σ ⊢ Γ ≤[pb] Γ' -> Σ ⊢ Γ ≤ Γ'.
  Proof using Type.
    intros a; eapply All2_fold_impl; tea.
    cbn; intros.
    depelim X; constructor; auto.
    now eapply ws_cumul_pb_le_le.
    now eapply ws_cumul_pb_le_le.
  Qed.

  Lemma ws_cumul_ctx_pb_eq_le {pb Γ Δ} :
    Σ ⊢ Γ = Δ -> Σ ⊢ Γ ≤[pb] Δ.
  Proof using Type.
    destruct pb; eauto.
    apply ws_cumul_ctx_pb_le_le.
  Qed.

  Lemma subslet_ws_cumul_ctx_pb {pb} {Γ Γ' Δ Δ'} {s} :
    wf_local Σ (Γ ,,, Δ) ->
    wf_local Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pb_rel pb Σ Γ Δ' Δ ->
    subslet Σ (Γ ,,, Δ) s Γ' ->
    subslet Σ (Γ ,,, Δ') s Γ'.
  Proof using wfΣ.
    intros wfl wfr cumul.
    induction 1; constructor; auto.
    * eapply context_cumulativity; tea.
      eapply ws_cumul_ctx_pb_rel_app in cumul.
      eapply ws_cumul_ctx_pb_le_le in cumul.
      now apply ws_cumul_ctx_pb_forget in cumul.
    * eapply context_cumulativity; tea.
      eapply ws_cumul_ctx_pb_rel_app in cumul.
      eapply ws_cumul_ctx_pb_le_le in cumul.
      now apply ws_cumul_ctx_pb_forget in cumul.
  Qed.

  Arguments on_free_vars_ctx _ _ : simpl never.

  Lemma ws_cumul_ctx_pb_rel_conv_extended_subst {pb} {Γ Δ Δ'} :
    wf_local Σ (Γ ,,, Δ) ->
    wf_local Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    ws_cumul_pb_terms Σ (Γ ,,, smash_context [] Δ) (extended_subst Δ 0) (extended_subst Δ' 0) ×
    ws_cumul_ctx_pb_rel pb Σ Γ (smash_context [] Δ) (smash_context [] Δ').
  Proof using wfΣ.
    intros wfl wfr [clΓ cum].
    assert (is_closed_context (Γ ,,, smash_context [] Δ)).
    { eapply wf_local_smash_end in wfl. eauto with fvs. }
    induction cum in |- *; simpl; auto.
    - split; constructor => //. constructor.
    - depelim p; simpl;
      depelim wfl; depelim wfr;
      specialize (IHcum wfl wfr) as [conv cum'];
      try assert (is_closed_context (Γ,,, smash_context [] Γ0)) by
       (rewrite /= smash_context_acc /= on_free_vars_ctx_snoc in H; now move/andP: H) => //.
      all:auto.
      * split; try constructor; auto.
        + eapply ws_cumul_pb_refl => //. cbn. len.
        + rewrite !(lift_extended_subst _ 1).
          move: H.
          rewrite /= ![smash_context [_] _]smash_context_acc /= /map_decl /= => ha.
          eapply (ws_cumul_pb_terms_lift (Δ := [_])) => //.
        + move: H; simpl; rewrite /= !(smash_context_acc _ [_]) /=;
          constructor; auto.
          apply cum'. rewrite /map_decl /=.
          constructor; auto.
          eapply ws_cumul_pb_expand_lets in eqt; tea.
          etransitivity;tea. rewrite /expand_lets /expand_lets_k. simpl.
          rewrite -(length_of cum).
          rewrite -(ws_cumul_ctx_pb_rel'_context_assumptions cum).
          move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
          change (Γ ,,, smash_context [] Γ0) with (Γ ,,, smash_context [] Γ0 ,,, []).
          eapply (substitution_ws_cumul_pb_subst_conv (Δ := [])); tea.
          { now eapply subslet_untyped_subslet, PCUICContexts.subslet_extended_subst. }
          { eapply subslet_untyped_subslet, subslet_ws_cumul_ctx_pb. 3:tea.
            now eapply wf_local_smash_end.
            now eapply wf_local_smash_end.
            now eapply PCUICContexts.subslet_extended_subst. }
          relativize (context_assumptions Γ').
          eapply is_closed_context_lift; tea; eauto with fvs. len.
          now rewrite -(ws_cumul_ctx_pb_rel'_context_assumptions cum).
          eapply ws_cumul_pb_refl.
          rewrite -[context_assumptions Γ0](smash_context_length []).
          eapply is_closed_context_lift; tea; eauto with fvs.
          rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
          rewrite context_assumptions_smash_context /=.
          rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
          relativize #|Γ0|.
          eapply is_open_term_lift.
          destruct l0 as (_ & s & Hs & _). eapply subject_closed in Hs.
          rewrite is_open_term_closed in Hs. move: Hs.
          now rewrite !length_app -(All2_fold_length cum). reflexivity.
      * split; auto.
        constructor; auto.
        len.
        eapply ws_cumul_pb_expand_lets in eqb; tea.
        etransitivity; tea.
        rewrite /expand_lets /expand_lets_k. simpl.
        rewrite -(length_of cum).
        rewrite -(ws_cumul_ctx_pb_rel'_context_assumptions cum).
        move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
        change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
        cbn. rewrite smash_context_acc /=.
        change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
        eapply (substitution_ws_cumul_pb_subst_conv (Δ := [])); tea.
        { now eapply subslet_untyped_subslet, PCUICContexts.subslet_extended_subst. }
        { eapply subslet_untyped_subslet, subslet_ws_cumul_ctx_pb. 3:tea.
          now eapply wf_local_smash_end.
          now eapply wf_local_smash_end.
          now eapply PCUICContexts.subslet_extended_subst. }
        relativize (context_assumptions Γ').
        eapply is_closed_context_lift; tea; eauto with fvs. len.
        now rewrite -(ws_cumul_ctx_pb_rel'_context_assumptions cum).
        eapply ws_cumul_pb_refl.
        rewrite -[context_assumptions Γ0](smash_context_length []).
        eapply is_closed_context_lift; tea; eauto with fvs.
        rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
        rewrite context_assumptions_smash_context /=.
        rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
        relativize #|Γ0|.
        eapply is_open_term_lift.
        eapply unlift_TermTyp, subject_closed in l0.
        rewrite is_open_term_closed in l0. move: l0.
        now rewrite !length_app -(All2_fold_length cum). reflexivity.
  Qed.


  Lemma ws_cumul_ctx_pb_rel_smash {pb} {Γ Δ Δ'} :
    wf_local Σ (Γ ,,, Δ) ->
    wf_local Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    ws_cumul_ctx_pb_rel pb Σ Γ (smash_context [] Δ) (smash_context [] Δ').
  Proof using wfΣ.
    now intros; apply ws_cumul_ctx_pb_rel_conv_extended_subst.
  Qed.

  Lemma ws_cumul_pb_terms_ws_cumul_ctx {pb} {Γ Δ Δ'} {ts ts'} :
    wf_local Σ (Γ ,,, Δ) ->
    wf_local Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    ws_cumul_pb_terms Σ (Γ ,,, Δ') ts ts' ->
    ws_cumul_pb_terms Σ (Γ ,,, Δ) ts ts'.
  Proof using wfΣ.
    intros wfl wfr cum conv.
    eapply (All2_impl conv).
    intros x y xy.
    eapply ws_cumul_pb_ws_cumul_ctx.
    now eapply ws_cumul_ctx_pb_rel_app in cum.
    assumption.
  Qed.

  Lemma ws_cumul_ctx_pb_rel_length {pb Γ Δ Δ'} :
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    #|Δ| = #|Δ'|.
  Proof using Type. intros []. apply (length_of a). Qed.

  Lemma is_closed_context_smash_end {Γ Δ} :
    is_closed_context (Γ ,,, Δ) ->
    is_closed_context (Γ ,,, smash_context [] Δ).
  Proof using Type.
    rewrite - !is_closed_ctx_closed.
    rewrite !closedn_ctx_app /= => /andP[] ->.
    eapply closedn_smash_context.
  Qed.

  Hint Resolve is_closed_context_smash_end : fvs.

  Lemma ws_cumul_pb_expand_lets_ws_cumul_ctx {pb le'} {Γ} {Δ Δ'} {T T'} :
    wf_local Σ (Γ ,,, Δ) ->
    wf_local Σ (Γ ,,, Δ') ->
    Σ ;;; Γ ,,, Δ ⊢ T ≤[le'] T' ->
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    Σ ;;; Γ ,,, smash_context [] Δ ⊢ expand_lets Δ T ≤[le'] expand_lets Δ' T'.
  Proof using wfΣ.
    intros wfl wfr cum cumΓ.
    rewrite /expand_lets /expand_lets_k.
    rewrite -(ws_cumul_ctx_pb_rel_length cumΓ) /=.
    rewrite -(ws_cumul_ctx_pb_rel_context_assumptions cumΓ).
    change (Γ ,,, smash_context [] Δ) with (Γ ,,, smash_context [] Δ ,,, []).
    eapply (substitution_ws_cumul_pb_subst_conv (Δ := [])); tea.
    3:{ eapply ws_cumul_ctx_pb_rel_conv_extended_subst; tea. }
    * eapply subslet_untyped_subslet, PCUICContexts.subslet_extended_subst; tea.
    * eapply subslet_untyped_subslet, subslet_ws_cumul_ctx_pb; cycle 2.
      + eapply ws_cumul_ctx_pb_rel_smash; tea.
      + eapply PCUICContexts.subslet_extended_subst; tea.
      + now eapply wf_local_smash_end.
      + now eapply wf_local_smash_end.
    * simpl.
      rewrite -(ws_cumul_ctx_pb_rel_context_assumptions cumΓ).
      rewrite -[context_assumptions _](smash_context_length [] Δ).
      eapply is_closed_context_lift; eauto with fvs.
    * rewrite -[context_assumptions _](smash_context_length [] Δ).
      eapply weakening_ws_cumul_pb => //; eauto with fvs.
  Qed.

  Lemma ctx_inst_cumul {pb Γ i Δ Δ'} :
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    ctx_inst Σ Γ i (List.rev Δ) ->
    wf_local_rel Σ Γ Δ ->
    wf_local_rel Σ Γ Δ' ->
    ctx_inst Σ Γ i (List.rev Δ').
  Proof using wfΣ.
    intros [clΓ a].
    induction a in i |- *; intros ci.
    - depelim ci. constructor.
    - simpl in ci. eapply PCUICSpine.ctx_inst_app_inv in ci as [dom codom].
      depelim p.
      * simpl in codom. depelim codom.
        simpl in codom. depelim codom. cbn in t1.
        destruct i as [|i t0] using rev_case.
        { rewrite skipn_nil in H => //. }
        assert (context_assumptions (List.rev Γ0) = #|i|).
        apply (f_equal (@length _)) in H. simpl in H.
        rewrite List.length_skipn length_app /= in H. lia.
        rewrite skipn_all_app_eq // in H. noconf H.
        intros HΔ; depelim HΔ.
        intros HΔ'; depelim HΔ'.
        destruct l0 as (_ & s & Hs & _). simpl.
        rewrite (ctx_inst_sub_subst dom) in t1.
        rewrite firstn_app_left // in dom.
        specialize (IHa _ dom HΔ HΔ').
        eapply (ctx_inst_app IHa).
        simpl. constructor; [|constructor].
        rewrite (ctx_inst_sub_subst IHa).
        rewrite firstn_app_left // in t1.
        simpl.
        rewrite context_assumptions_rev in H0.
        assert (context_assumptions Γ' = #|i|) by now rewrite -(ws_cumul_ctx_pb_rel'_context_assumptions a).
        rewrite map_subst_expand_lets in t1; len=> //.
        rewrite map_subst_expand_lets; len=> //.
        unshelve epose proof (ctx_inst_spine_subst _ IHa); tea.
        now eapply typing_wf_local in Hs.
        eapply spine_subst_smash in X; tea.
        eapply type_ws_cumul_pb; tea.
        + eapply typing_expand_lets in Hs.
          eapply (substitution (s := List.rev i) (Δ := [])) in Hs; tea.
          simpl in Hs. eapply has_sort_isType. now rewrite subst_context_nil /= in Hs.
          exact X.
        + unshelve epose proof (ctx_inst_spine_subst _ dom); tea.
          eapply All_local_env_app; tea. now eapply typing_wf_local.
          pose proof (spine_codom_wf _ _ _ _ _ X0).
          eapply spine_subst_smash in X0; tea.
          eapply (PCUICConversion.substitution_ws_cumul_pb (Γ := Γ) (Γ'' := []) X0).
          simpl.
          eapply ws_cumul_pb_expand_lets_ws_cumul_ctx; tea.
          now eapply typing_wf_local in Hs. split; tea.
    * simpl in codom. depelim codom.
      simpl in codom. depelim codom.
      assert (context_assumptions (List.rev Γ0) = #|i|).
      pose proof (ctx_inst_length dom).
      apply (f_equal (@length _)) in H. simpl in H.
      rewrite List.length_skipn /= in H.
      apply firstn_length_le_inv in H0. lia.
      rewrite H0 in H, dom. rewrite firstn_all in dom.
      intros HΔ; depelim HΔ.
      intros HΔ'; depelim HΔ'.
      destruct l as (Hb & s & Hs & _). simpl in *.
      destruct l0 as (Hb' & s' & Hs' & _). simpl in *.
      specialize (IHa _ dom).
      forward IHa. apply All_local_env_app_inv; pcuic.
      forward IHa. apply All_local_env_app_inv; pcuic.
      rewrite -(app_nil_r i).
      eapply (ctx_inst_app IHa).
      rewrite (ctx_inst_sub_subst IHa) /=.
      repeat constructor.
  Qed.

  Lemma subst_context_rev_subst_telescope s k Γ :
    subst_context s k (List.rev Γ) = List.rev (subst_telescope s k Γ).
  Proof using Type.
    induction Γ in s, k |- *.
    - simpl; auto.
    - rewrite subst_telescope_cons /= subst_context_app IHΓ.
      reflexivity.
  Qed.

  Lemma ctx_inst_smash_acc {Γ i Δ} :
    ctx_inst Σ Γ i Δ <~>
    ctx_inst Σ Γ i (List.rev (smash_context [] (List.rev Δ))).
  Proof using Type.
    split.
    - induction 1.
      + constructor.
      + simpl.
        rewrite smash_context_app_ass. len.
        rewrite List.rev_app_distr /=.
        constructor. auto.
        rewrite subst_telescope_subst_context.
        rewrite -smash_context_subst /=; len.
        now rewrite subst_context_rev_subst_telescope.
      + simpl. rewrite smash_context_app_def.
        now rewrite subst_context_rev_subst_telescope.
    - induction Δ using ctx_length_ind in i |- *; simpl; auto.
      destruct d as [na [b|] ty] => /=.
      * rewrite smash_context_app_def /=.
        rewrite subst_context_rev_subst_telescope.
        intros ctxi. constructor.
        apply X => //. now rewrite subst_telescope_length //.
      * rewrite smash_context_app_ass List.rev_app_distr /=.
        intros ctxi; depelim ctxi.
        constructor => //.
        apply X. rewrite subst_telescope_length //.
        rewrite subst_telescope_subst_context in ctxi.
        rewrite -(smash_context_subst []) in ctxi.
        now rewrite subst_context_rev_subst_telescope in ctxi.
  Qed.

  Lemma ctx_inst_smash {Γ i Δ} :
    ctx_inst Σ Γ i (List.rev Δ) <~>
    ctx_inst Σ Γ i (List.rev (smash_context [] Δ)).
  Proof using Type.
    split; intros.
    - apply (fst ctx_inst_smash_acc) in X. now rewrite List.rev_involutive in X.
    - apply (snd ctx_inst_smash_acc). now rewrite List.rev_involutive.
  Qed.

  Lemma subst_context_subst_telescope s k Γ :
    subst_context s k (List.rev Γ) = List.rev (subst_telescope s k Γ).
  Proof using Type.
    rewrite /subst_telescope subst_context_alt.
    rewrite rev_mapi. apply mapi_rec_ext.
    intros n [na [b|] ty] le le'; rewrite /= /subst_decl /map_decl /=;
    rewrite List.length_rev Nat.add_0_r in le'; len; lia_f_equal.
  Qed.

  Lemma ws_cumul_ctx_pb_rel_trans {pb Γ Δ Δ' Δ''} :
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
    ws_cumul_ctx_pb_rel pb Σ Γ Δ' Δ'' ->
    ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ''.
  Proof using wfΣ.
    move/ws_cumul_ctx_pb_rel_app => h /ws_cumul_ctx_pb_rel_app h'.
    apply ws_cumul_ctx_pb_rel_app.
    now etransitivity.
  Qed.

  Lemma OnOne2_ctx_inst {pb} {P} {Γ inst inst' Δ} :
    (forall Γ Δ' Δ s s', wf_local Σ (Γ ,,, Δ' ,,, Δ) ->
    subslet Σ Γ (List.rev s) Δ' ->
    subslet Σ Γ (List.rev s') Δ' ->
    OnOne2 (P Σ Γ) s s' ->
    ws_cumul_ctx_pb pb Σ (Γ ,,, subst_context (List.rev s) 0 Δ)
      (Γ ,,, subst_context (List.rev s') 0 Δ)) ->
    wf_local Σ (Γ ,,, (List.rev Δ)) ->
    PCUICTyping.ctx_inst
      (fun (Γ : context) (t T : term) =>
      forall u : term, P Σ Γ t u -> Σ;;; Γ |- u : T) Γ inst Δ ->
    ctx_inst Σ Γ inst Δ ->
    OnOne2 (P Σ Γ) inst inst' ->
    ctx_inst Σ Γ inst' Δ.
  Proof using wfΣ.
    intros HP wf c.
    induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
    - depelim o.
    - depelim o. constructor. apply t0. auto.
      rewrite -(List.rev_involutive Δ).
      rewrite subst_telescope_subst_context.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      eapply ctx_inst_cumul.
      2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
          rewrite -subst_telescope_subst_context List.rev_involutive. exact ctxi. }
      eapply ws_cumul_ctx_pb_rel_app.
      eapply (HP _ _ _ [i] [hd']); tea.
      repeat constructor. now rewrite subst_empty. repeat constructor.
      now rewrite subst_empty. constructor. auto.
      eapply All_local_env_app_inv. eapply substitution_wf_local; tea.
      repeat (constructor; tea). rewrite subst_empty; tea.
      eapply All_local_env_app_inv. eapply substitution_wf_local; tea.
      repeat (constructor; tea). rewrite subst_empty; tea. now eapply t0.
      constructor; auto. eapply IHc.
      rewrite -subst_context_subst_telescope.
      eapply substitution_wf_local; tea.
      repeat (constructor; tea). rewrite subst_empty; tea.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      exact wf. tas. tas.
    - constructor. eapply IHc; eauto.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      rewrite -subst_context_subst_telescope.
      eapply substitution_wf_local; tea.
      repeat (constructor; tea). eapply subslet_def_tip.
      eapply All_local_env_app_inv in wf as [wf _]. depelim wf. now eapply unlift_TermTyp.
  Qed.

  Lemma All2_ctx_inst {pb} {P} {Γ inst inst' Δ} :
    (forall Γ Δ' Δ s s', wf_local Σ (Γ ,,, Δ' ,,, Δ) ->
    subslet Σ Γ (List.rev s) Δ' ->
    subslet Σ Γ (List.rev s') Δ' ->
    All2 (P Σ Γ) s s' ->
    ws_cumul_ctx_pb pb Σ (Γ ,,, subst_context (List.rev s) 0 Δ)
      (Γ ,,, subst_context (List.rev s') 0 Δ)) ->
    wf_local Σ (Γ ,,, (List.rev Δ)) ->
    PCUICTyping.ctx_inst
      (fun (Γ : context) (t T : term) =>
      forall u : term, P Σ Γ t u -> Σ;;; Γ |- u : T) Γ inst Δ ->
    ctx_inst Σ Γ inst Δ ->
    All2 (P Σ Γ) inst inst' ->
    ctx_inst Σ Γ inst' Δ.
  Proof using wfΣ.
    intros HP wf c.
    induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
    - depelim o. constructor.
    - depelim o. constructor. apply t0. auto.
      rewrite -(List.rev_involutive Δ).
      rewrite subst_telescope_subst_context.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      eapply ctx_inst_cumul.
      2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
          rewrite -subst_telescope_subst_context List.rev_involutive. eapply IHc => //.
          rewrite -subst_context_subst_telescope.
          eapply substitution_wf_local; tea.
          repeat (constructor; tea). rewrite subst_empty; tea. }
      eapply ws_cumul_ctx_pb_rel_app.
      eapply (HP _ _  _ [i] [y]); tea.
      repeat constructor. now rewrite subst_empty.
      now apply subslet_ass_tip.
      now repeat constructor.
      * eapply All_local_env_app_inv. eapply substitution_wf_local; tea.
        now apply subslet_ass_tip.
      * eapply All_local_env_app_inv. eapply substitution_wf_local; tea.
        now apply subslet_ass_tip.
    - constructor. eapply IHc; eauto.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      rewrite -subst_context_subst_telescope.
      eapply substitution_wf_local; tea.
      repeat (constructor; tea). eapply subslet_def_tip.
      eapply All_local_env_app_inv in wf as [wf _]. depelim wf. now eapply unlift_TermTyp.
  Qed.

  Lemma ctx_inst_open_terms Γ args Δ :
    ctx_inst Σ Γ args Δ ->
    All (is_open_term Γ) args.
  Proof using wfΣ.
    induction 1; try constructor; eauto using subject_is_open_term.
  Qed.

  Lemma subslet_open_terms Γ s Δ :
    subslet Σ Γ s Δ ->
    All (is_open_term Γ) s.
  Proof using wfΣ.
    induction 1; try constructor; eauto using subject_is_open_term.
  Qed.

  Lemma ctx_inst_eq_context {Γ Δ : context} {args args'} :
    wf_local Σ (Γ ,,, List.rev Δ) ->
    PCUICTyping.ctx_inst
          (fun (Γ : context) (u A : term) =>
          forall v : term, upto_names' u v -> Σ;;; Γ |- v : A) Γ args Δ ->
    ctx_inst Σ Γ args Δ ->
    All2 upto_names' args args' ->
    ctx_inst Σ Γ args' Δ.
  Proof using wfΣ.
    intros wf ctxi ctxi' a.
    eapply All2_ctx_inst; tea.
    2:exact ctxi. 2:auto.
    cbn; clear -wfΣ; intros.
    eapply substitution_ws_cumul_ctx_pb.
    now eapply subslet_untyped_subslet.
    now eapply subslet_untyped_subslet.
    eapply All2_rev.
    move/All_local_env_app_inv: X => [] /All_local_env_app_inv[] /wf_local_closed_context clΓ0 _ _.
    eapply subslet_open_terms, All_rev_inv in X0.
    eapply subslet_open_terms, All_rev_inv in X1.
    solve_all. eapply into_ws_cumul_pb; tea.
    constructor. now apply upto_names_impl_eq_term.
    all:eauto with fvs.
  Qed.

End WfEnv.

Lemma spine_subst_vass `{cf: checker_flags} Σ Γ s t σ Δ na A :
  wf Σ.1 ->
  spine_subst Σ Γ s σ Δ ->
  lift_typing typing Σ (Γ ,,, Δ) (j_vass na A) ->
  Σ ;;; Γ |- t : subst0 σ A ->
  spine_subst Σ Γ (s ++ [t]) (t :: σ) (Δ ,, vass na A).
Proof.
  move=> wfΣ sss Atyp ttyp; move: (sss)=> [????].
  change (?x ,, ?y) with (x ,,, [ y ]).
  apply: spine_subst_app=> //=.
  + apply: PCUICContextSubst.context_subst_length2; eassumption.
  + apply: localenv_cons_abs=> //.
  + rewrite /skipn /subst_context /fold_context_k /= /map_decl /=.
    constructor=> //=.
    * apply: localenv_cons_abs=> //.
      apply: isTypeRel_subst; eassumption.
    * apply: (PCUICContextSubst.context_subst_ass [] [] [] na _ t); constructor.
    * econstructor; first constructor.
      by rewrite PCUICLiftSubst.subst_empty.
Qed.

Lemma wf_local_nth_isTypeRel {cf} {Σ} {Γ n d} :
  wf_local Σ Γ ->
  nth_error Γ n = Some d ->
  isTypeRel Σ (skipn (S n) Γ) d.(decl_type) d.(decl_name).(binder_relevance).
Proof.
  intros Hwf hnth.
  eapply All_local_env_nth_error in Hwf; tea.
  now apply lift_sorting_forget_body in Hwf.
Qed.


Lemma spine_subst_vass' `{cf:checker_flags} Σ Γ s t σ Δ na A :
  wf Σ.1 ->
  spine_subst Σ Γ s σ Δ ->
  wf_local Σ (Γ ,,, Δ ,, vass na A) ->
  (spine_subst Σ Γ s σ Δ ->
    isType Σ Γ (subst0 σ A) ->
    Σ ;;; Γ |- t : subst0 σ A) ->
  spine_subst Σ Γ (s ++ [t]) (t :: σ) (Δ ,, vass na A).
Proof.
  move=> wfΣ sss Atyp /(_ sss) ttyp; apply: spine_subst_vass=> //.
  2: apply: ttyp; apply: isType_subst; first (apply: inst_subslet; eassumption).
  all: exact (wf_local_nth_isTypeRel (n := 0) Atyp eq_refl).
Qed.

Lemma mk_ctx_subst_spec' `{cf : checker_flags} {Σ Γ Δ args} (c : ctx_inst Σ Γ args (List.rev Δ)) :
  mk_ctx_subst Δ args = ctx_inst_sub c.
Proof.
  apply: context_subst_fun.
  - apply: mk_ctx_subst_spec; by rewrite (ctx_inst_length c) context_assumptions_rev.
  - move: (ctx_inst_sub_spec c)=> /make_context_subst_spec.
    rewrite {1}rev_involutive //.
Qed.

Section ClosedSpineSubst.
  Context `{cf: checker_flags}.

  Lemma closed_subslet {Σ} {wfΣ : wf Σ.1} {Γ s Δ} : subslet Σ Γ s Δ -> forallb (closedn #|Γ|) s.
  Proof using cf.
    move=> z; depind z=> //=; rewrite IHz andb_true_r;
    apply: PCUICClosedTyp.subject_closed; eassumption.
  Qed.


  Lemma closed_spine_subst {Σ} {wfΣ : wf Σ.1} {Γ inst s Δ} :
    spine_subst Σ Γ inst s Δ -> forallb (closedn #|Γ|) s.
  Proof using cf. move=> /inst_subslet; apply: closed_subslet.  Qed.

  Lemma closed_spine_subst_inst {Σ} {wfΣ : wf Σ.1} {Γ inst s Δ} :
    spine_subst Σ Γ inst s Δ -> forallb (closedn #|Γ|) inst.
  Proof using cf.
    move=> /spine_subst_smash /closed_spine_subst; by rewrite forallb_rev.
  Qed.
End ClosedSpineSubst.
