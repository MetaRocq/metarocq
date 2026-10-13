From Stdlib Require Import Bool List Arith Lia.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICInversion PCUICInductives PCUICInductiveInversion PCUICEquality PCUICUnivSubst PCUICClosed PCUICSubstitution PCUICValidity PCUICCumulativity PCUICInductives PCUICWfUniverses PCUICContexts PCUICSpine PCUICSR PCUICWellScopedCumulativity PCUICConversion PCUICOnFreeVars PCUICWeakeningTyp PCUICUnivSubstitutionTyp PCUICClosedTyp PCUICUnivSubstitutionConv.
From MetaRocq.PCUIC Require Import BDTyping.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

(** Various generic lemmas missing from the MetaRocq library *)

Lemma All2i_prod (A B : Type) (P Q : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
  All2i P n l l' -> All2i Q n l l' -> All2i (fun i x y => (P i x y) × (Q i x y)) n l l'.
Proof.
  intros AP.
  dependent induction AP.
  1: constructor.
  intros AQ.
  inversion_clear AQ.
  constructor ; auto.
Qed.

Lemma All_local_env_app_l P Γ Γ' : All_local_env P (Γ ,,, Γ') -> All_local_env P Γ.
Proof.
  induction Γ'.
  1: auto.
  cbn.
  intros all.
  inversion all ; auto.
Qed.

Lemma wf_local_rel_subst1 `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Δ Γ na b t Γ' :
      wf_local_rel Σ Δ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local_rel Σ Δ (Γ ,,, subst_context [b] 0 Γ').
Proof.
  induction Γ' as [|d Γ']; [now inversion 1|].
  change (d :: Γ') with (Γ' ,, d).
  destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
  - rewrite subst_context_snoc0. simpl.
    inversion HH; subst; cbn in *.
    change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
    assert (subslet Σ (Δ ,,, Γ) [b] [vdef na b t]). {
      pose proof (cons_let_def Σ (Δ ,,, Γ) [] [] na b t) as XX.
      rewrite !subst_empty in XX. apply XX. constructor.
      apply All_local_env_app_l in X. inversion X; subst; cbn in * ; now eapply unlift_TermTyp.
    }
    constructor; cbn; auto.
    1: apply IHΓ' ; exact X.
    apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
    rewrite !app_context_assoc in Hs |- *.
    eapply substitution; tea.
  - rewrite subst_context_snoc0. simpl.
    inversion HH; subst; cbn in *.
    change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
    assert (subslet Σ (Δ ,,, Γ) [b] [vdef na b t]). {
      pose proof (cons_let_def Σ (Δ ,,, Γ) [] [] na b t) as XX.
      rewrite !subst_empty in XX. apply XX. constructor.
      apply All_local_env_app_l in X. inversion X; subst; cbn in *; now eapply unlift_TermTyp. }
    constructor; cbn; auto.
    1: apply IHΓ' ; exact X.
    apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
    rewrite !app_context_assoc in Hs |- *.
    eapply substitution; tea.
Qed.

Lemma wf_rel_weak `{checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) Γ (wfΓ : wf_local Σ Γ) Γ' :
  wf_local Σ Γ' -> wf_local_rel Σ Γ Γ'.
Proof.
  induction Γ' as [|[? []] ?].
  - by constructor.
  - intros wfl. inversion_clear wfl.
    constructor.
    + apply IHΓ'. assumption.
    + apply lift_typing_impl with (1 := X0) => // ?? Hs.
      apply weaken_ctx ; eauto.
  - intros wfl. inversion_clear wfl.
    constructor.
    + apply IHΓ'. assumption.
    + apply lift_typing_impl with (1 := X0) => // ?? Hs.
      apply weaken_ctx ; eauto.
Qed.

Lemma wf_local_local_rel `{checker_flags} Σ Γ Γ' : wf_local Σ (Γ ,,, Γ') -> wf_local_rel Σ Γ Γ'.
Proof.
  intro wfΓ.
  apply All_local_env_app_inv in wfΓ as [_ wfr] => //.
Qed.

Section BDToPCUICTyping.

  (** We work in a fixed, well-formed global environment*)

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  (** The predicates we wish to prove, note the extra well-formedness hypothesis on the context
  and type whenever they are inputs to the algorithm *)

  Let Pinfer Γ t T :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : T.

  Let Psort Γ t u :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : (tSort u).

  Let Pprod Γ t na A B :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : tProd na A B.

  Let Pind Γ ind t u args :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : mkApps (tInd ind u) args.

  Let Pcheck Γ t T :=
    wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t : T.

  Let PΓ Γ :=
    wf_local Σ Γ.

  Let PΓ_rel Γ Γ' :=
    wf_local Σ Γ -> wf_local_rel Σ Γ Γ'.

  Let Pj Γ j :=
    wf_local Σ Γ -> lift_typing typing Σ Γ j.

  (** Preliminary lemmas to go from a bidirectional judgement to the corresponding undirected one *)

  Lemma bd_wf_local Γ (all: wf_local_bd Σ Γ) :
    All_local_env_over_sorting (checking Σ) (infering_sort Σ)
      (fun Γ _ t T _ => Pcheck Γ t T)
      (fun Γ _ t s _ => Psort Γ t s)
      Γ all ->
    wf_local Σ Γ.
  Proof using Type.
    intros allo ; induction allo.
    all: constructor; tas.
    all: apply lift_sorting_it_impl with tu => //= Ht; eauto.
    apply Hc; cbn; auto.
    now eapply has_sort_isType, Hs.
  Qed.

  Lemma bd_wf_local_rel Γ (wfΓ : wf_local Σ Γ) Γ' (all: wf_local_bd_rel Σ Γ Γ') :
    All_local_env_over_sorting
      (fun Δ => checking Σ (Γ,,,Δ))
      (fun Δ => infering_sort Σ (Γ,,,Δ))
      (fun Δ _ t T _ => Pcheck (Γ,,,Δ) t T)
      (fun Δ _ t s _ => Psort (Γ,,,Δ) t s)
      Γ' all ->
    wf_local_rel Σ Γ Γ'.
  Proof using Type.
    intros allo ; induction allo.
    all: constructor; tas.
    all: apply All_local_env_app in IHallo; tas.
    all: apply lift_sorting_it_impl with tu => //= Ht; eauto.
    apply Hc; cbn; auto.
    now eapply has_sort_isType, Hs.
  Qed.

  Lemma ctx_inst_impl Γ (wfΓ : wf_local Σ Γ) (Δ : context) (wfΔ : wf_local_rel Σ Γ (List.rev Δ)) :
    forall args, PCUICTyping.ctx_inst Pcheck Γ args Δ -> ctx_inst Σ Γ args Δ.
  Proof using wfΣ.
    revert wfΔ.
    induction Δ using ctx_length_ind.
    1: intros _ ? d ; inversion_clear d ; constructor.
    intros wfΔ args ctxi ; inversion ctxi.
    - subst d.
      subst.
      cbn in wfΔ.
      assert (isTypeRel Σ Γ t na.(binder_relevance)).
      {
        eapply All_local_rel_app_inv in wfΔ as [wfd _].
        inversion_clear wfd.
        eassumption.
      }
      apply isTypeRel_isType in X2 as X2'.
      constructor ; auto.
      apply X ; auto.
      1: by rewrite subst_telescope_length ; reflexivity.
      rewrite -(rev_involutive Γ0) -subst_context_telescope.
      cbn in wfΔ.
      apply All_local_rel_app_inv in wfΔ as [].
      apply wf_local_local_rel.
      eapply substitution_wf_local ; eauto.
      1: repeat constructor.
      1: rewrite subst_empty ; eauto.
      apply All_local_env_app.
      1: constructor ; eauto.
      eassumption.
    - subst d.
      subst.
      cbn in wfΔ.
      assert (isType Σ Γ t).
      {
        eapply All_local_rel_app_inv in wfΔ as [wfd _].
        inversion_clear wfd.
        now eapply lift_sorting_forget_body, lift_sorting_forget_rel.
      }
      constructor ; auto.
      apply X ; auto.
      1: by rewrite subst_telescope_length ; reflexivity.
      rewrite -(rev_involutive Γ0) -subst_context_telescope.
      rewrite <- app_nil_r.
      eapply wf_local_rel_subst1.
      cbn in wfΔ |- *.
      eassumption.
  Qed.

  (** The big theorem, proven by mutual induction using the custom induction principle *)
  Theorem bidirectional_to_pcuic : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind Pj PΓ PΓ_rel.
  Proof using wfΣ.
    apply bidir_ind_env.

    - intros. intro.
      apply lift_sorting_it_impl with X.
      2: intros [_ IH]; now apply IH.
      destruct j_term => //=.
      intros [_ IH]; apply IH; tas.
      apply lift_sorting_forget_univ, lift_sorting_forget_rel, lift_sorting_forget_body in X.
      apply lift_sorting_it_impl_gen with X => //.
      intros [_ IH']; now apply IH'.

    - intros. eapply bd_wf_local. eassumption.

    - intros. intro. eapply bd_wf_local_rel ; eassumption.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.
      apply X2.
      constructor. 1: by auto.
      eapply lift_sorting_forget_univ. now eapply X0.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - red ; intros.
      eapply type_App' ; auto.
      apply X2 ; auto.
      specialize (X0 X3).
      apply validity in X0 as (_ & s & X0 & _).
      apply inversion_Prod in X0 as (s1 & s2 & X0 & _).
      2: done.
      eapply lift_sorting_forget_rel, lift_sorting_forget_univ; eassumption.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - intros ; intro.

      assert (cparams : ctx_inst Σ Γ (pparams p) (List.rev (ind_params mdecl)@[puinst p])).
      { apply ctx_inst_impl ; auto.
        rewrite rev_involutive.
        apply wf_rel_weak ; auto.
        move: (H) => [decl ?].
        pose proof (decl' := declared_minductive_to_gen (wfΣ := wfΣ) decl).
        eapply wf_local_subst_instance_decl ; eauto.
        eapply All_local_env_app_inv.
        now eapply on_minductive_wf_params_indices.
      }

      assert (cum : Σ;;; Γ ⊢ mkApps (tInd ci u) args ≤
        mkApps (tInd ci (puinst p)) (pparams p ++ skipn (ci_npar ci) args)).
      {
        eapply ws_cumul_pb_mkApps_eq.
        1-3: fvs.
        - now constructor.
        - eapply type_is_open_term in X0 ; eauto.
          move: X0.
          rewrite on_free_vars_mkApps -{-3}(firstn_skipn (ci_npar ci) args)
          forallb_app /= => /andP [? ?].
          apply All2_app ; tea.
          + assert (forallb (is_open_term Γ) p.(pparams)).
            {
              eapply All_forallb'.
              1: now eapply ctx_inst_closed.
              intros.
              by rewrite -is_open_term_closed.
            }
            solve_all.
            eapply into_ws_cumul_pb ; tea.
            fvs.
          + now apply ws_cumul_pb_terms_refl ; fvs.
      }

      assert (ctx_inst Σ Γ (pparams p ++ skipn (ci_npar ci) args)
        (List.rev (subst_instance (puinst p) (ind_params mdecl,,, ind_indices idecl)))).
      {
        rewrite -H0.
        eapply ctx_inst_app_weak ; eauto.
        1: eapply validity ; auto.
        now rewrite H0.
      }

      assert (isType Σ Γ (mkApps (tInd ci (puinst p))
        (pparams p ++ skipn (ci_npar ci) args))).
      {
        eapply has_sort_isType.
        eapply type_mkApps_arity.
        1: econstructor ; eauto.
        erewrite PCUICGlobalMaps.ind_arity_eq.
        2: by eapply PCUICInductives.oib ; eauto.
        rewrite !subst_instance_it_mkProd_or_LetIn -it_mkProd_or_LetIn_app -subst_instance_app - (app_nil_r (pparams p ++ skipn (ci_npar ci) args)).
        eapply arity_spine_it_mkProd_or_LetIn ; auto.
        - unshelve apply ctx_inst_spine_subst ; auto.
          apply weaken_wf_local ; auto.
          eapply on_minductive_wf_params_indices_inst ; eauto.
        - cbn.
          constructor.
      }

      assert (wf_local Σ (Γ,,,case_predicate_context ci mdecl idecl p)).
      {
        eapply wf_case_predicate_context ; tea.
      }
      pose proof X12 as (_ & ? & X12' & _).
      econstructor ; eauto.
      2-3: split ; eauto.
      1: now eapply type_Cumul ; eauto ; apply cumulAlgo_cumulSpec in cum.

      eapply All2i_impl.
      1:{ apply All2i_prod ; [eassumption|idtac].
          eapply wf_case_branches_types' ; eauto.
      }
      intros * ((?&?&?&?&Hbody)&[]).
      split ; tea.
      intros brctxty.
      fold predctx in brctxty.
      fold ptm in brctxty.
      repeat split ; auto.
      apply Hbody ; auto.
      eapply has_sort_isType.
      eassumption.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

      + clear H H0 H1 X.
        apply All_impl with (1 := X0) => d Hd.
        specialize (Hd X3).
        apply lift_sorting_it_impl with Hd => //.

      + have Htypes : All (fun d => isTypeRel Σ Γ (dtype d) (dname d).(binder_relevance)) mfix.
        { apply All_impl with (1 := X0) => d Hd.
          specialize (Hd X3).
          apply lift_sorting_it_impl with Hd => //.
        }
        have wfΓ' : wf_local Σ (Γ,,,fix_context mfix) by apply All_mfix_wf.

        remember (fix_context mfix) as Γ' eqn:e.
        clear H H0 H1 e.
        apply All_mix with (1 := Htypes) in X2.
        apply All_impl with (1 := X2) => d [] isTy Hd.
        specialize (Hd wfΓ').
        apply lift_sorting_it_impl with Hd => //=.

    - red ; intros ; econstructor ; eauto.
      + clear H H0 H1 X.
        apply All_impl with (1 := X0) => d Hd.
        specialize (Hd X3).
        apply lift_sorting_it_impl with Hd => //.

      + have Htypes : All (fun d => isTypeRel Σ Γ (dtype d) (dname d).(binder_relevance)) mfix.
        { apply All_impl with (1 := X0) => d Hd.
          specialize (Hd X3).
          apply lift_sorting_it_impl with Hd => //.
        }
        have wfΓ' : wf_local Σ (Γ,,,fix_context mfix) by apply All_mfix_wf.

        remember (fix_context mfix) as Γ' eqn:e.
        clear H H0 H1 e.
        apply All_mix with (1 := Htypes) in X2.
        apply All_impl with (1 := X2) => d [] isTy Hd.
        specialize (Hd wfΓ').
        apply lift_sorting_it_impl with Hd => //=.

    - red; intros.
      econstructor; eauto.
      depelim X0; try solve [ constructor; eauto ].
      unfold Pcheck in hty, hdef.
      do 2 forward hty; tas. 1: eapply has_sort_isType; now econstructor.
      do 2 forward hdef; tas. 1: now eapply has_sort_isType.
      constructor; eauto.
      solve_all. eapply X6; eauto. now eapply has_sort_isType.

    - red ; intros.
      now eapply type_reduction.

    - red ; intros.
      now eapply type_reduction.

    - red ; intros.
      now eapply type_reduction.

    - red ; intros.
      destruct X3 as (_ & ? & ? & _).
      econstructor ; eauto.
      eapply (cumulAlgo_cumulSpec _ (pb := Cumul)), into_ws_cumul_pb ; tea.
      + fvs.
      + now eapply type_is_open_term.
      + now eapply subject_is_open_term.
  Qed.

End BDToPCUICTyping.

(** The user-facing theorems, directly following from the previous one *)

Theorem infering_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t : T.
Proof.
  intros.
  apply bidirectional_to_pcuic.
  all: assumption.
Qed.

Theorem checking_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t ◃ T -> Σ ;;; Γ |- t : T.
Proof.
  intros wfΓ HT Ht. revert wfΓ HT.
  apply bidirectional_to_pcuic.
  all: assumption.
Qed.

Theorem infering_sort_typing `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹□ u -> Σ ;;; Γ |- t : tSort u.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuic.
  assumption.
Qed.

Theorem infering_sort_isType `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹□ u -> isType Σ Γ t.
Proof.
  intros wfΓ Ht.
  repeat (eexists; tea).
  now apply infering_sort_typing.
Qed.

Theorem infering_sort_isTypeRel `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹□ u -> isTypeRel Σ Γ t (relevance_of_sort u).
Proof.
  intros wfΓ Ht.
  repeat (eexists; tea).
  now apply infering_sort_typing.
Qed.

Theorem einfering_sort_isType `{checker_flags} (Σ : global_env_ext) Γ t (wfΣ : wf Σ) :
  wf_local Σ Γ -> (∑ u, Σ ;;; Γ |- t ▹□ u) -> isType Σ Γ t.
Proof.
  intros wfΓ [u Ht].
  now eapply infering_sort_isType.
Qed.

Theorem isTypebd_isType `{checker_flags} (Σ : global_env_ext) Γ j (wfΣ : wf Σ) :
  wf_local Σ Γ -> lift_sorting (checking Σ Γ) (infering_sort Σ Γ) j -> isType Σ Γ (j_typ j).
Proof.
  intros wfΓ (_ & s & Hs & _).
  now eapply infering_sort_isType.
Qed.

Theorem lift_sorting_lift_typing `{cf : checker_flags} (Σ : global_env_ext) Γ j (wfΣ : wf Σ) :
  wf_local Σ Γ -> lift_sorting (checking Σ Γ) (infering_sort Σ Γ) j -> lift_typing typing Σ Γ j.
Proof.
  intros wfΓ Hj.
  apply lift_sorting_it_impl with Hj.
  2: intros H; now apply infering_sort_typing, H.
  destruct j_term => //=.
  intros H; apply checking_typing; tas.
  now apply isTypebd_isType in Hj.
Qed.

Theorem infering_prod_typing `{checker_flags} (Σ : global_env_ext) Γ t na A B (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹Π (na,A,B) -> Σ ;;; Γ |- t : tProd na A B.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuic.
  assumption.
Qed.

Theorem infering_ind_typing `{checker_flags} (Σ : global_env_ext) Γ t ind u args (wfΣ : wf Σ) :
wf_local Σ Γ -> Σ ;;; Γ |- t ▹{ind} (u,args) -> Σ ;;; Γ |- t : mkApps (tInd ind u) args.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuic.
  assumption.
Qed.

Theorem wf_local_bd_typing `{checker_flags} (Σ : global_env_ext) Γ (wfΣ : wf Σ) :
  wf_local_bd Σ Γ -> wf_local Σ Γ.
Proof.
  apply bidirectional_to_pcuic.
  assumption.
Qed.

Theorem wf_local_bd_rel_typing `{checker_flags} (Σ : global_env_ext) Γ Γ' (wfΣ : wf Σ) :
  wf_local Σ Γ -> wf_local_bd_rel Σ Γ Γ' -> wf_local_rel Σ Γ Γ'.
Proof.
  intros.
  now apply bidirectional_to_pcuic.
Qed.

Theorem ctx_inst_bd_typing `{checker_flags} (Σ : global_env_ext) Γ l Δ (wfΣ : wf Σ) :
  wf_local Σ (Γ,,,Δ) ->
  PCUICTyping.ctx_inst (checking Σ) Γ l (List.rev Δ) ->
  PCUICTyping.ctx_inst (typing Σ) Γ l (List.rev Δ).
Proof.
  intros wfΓ inl.
  rewrite -(List.rev_involutive Δ) in wfΓ.
  remember (List.rev Δ) as Δ'.
  clear HeqΔ'.
  induction inl in wfΓ |- *.
  - constructor.
  - assert (Σ ;;; Γ |- i : t).
    {
      rewrite /= app_context_assoc in wfΓ.
      eapply All_local_env_app_inv in wfΓ as [wfΓ _].
      inversion wfΓ ; subst.
      apply isTypeRel_isType in X0.
      now apply checking_typing.
    }
    constructor ; tea.
    eapply IHinl.
    rewrite /= app_context_assoc in wfΓ.
    rewrite -subst_context_rev_subst_telescope.
    eapply substitution_wf_local ; tea.
    constructor.
    1: constructor.
    now rewrite subst_empty.
  - constructor.
    eapply IHinl.
    rewrite /= app_context_assoc in wfΓ.
    rewrite -subst_context_rev_subst_telescope.
    eapply substitution_wf_local ; tea.
    rewrite -{1}(subst_empty 0 b).
    constructor.
    1: constructor.
    rewrite !subst_empty.
    eapply All_local_env_app_inv in wfΓ as [wfΓ _].
    inversion wfΓ ; subst.
    now eapply unlift_TermTyp.
Qed.
