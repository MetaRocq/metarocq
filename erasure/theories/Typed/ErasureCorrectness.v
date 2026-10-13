From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Erasure.Typed Require Import Erasure.
From MetaRocq.Erasure.Typed Require Import ExAst.
From Equations Require Import Equations.
From MetaRocq.Erasure Require Import EDeps.
From MetaRocq.Erasure Require Import ESubstitution.
From MetaRocq.Erasure Require Import Extract.
From MetaRocq.Erasure Require Import ErasureFunction ErasureFunctionProperties.
From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.PCUIC Require Import PCUICSR.
From MetaRocq.PCUIC Require Import PCUICTyping.
From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames.
From Stdlib Require Import List.

Import ListNotations.
Import PCUICEnvironment.

Module P := PCUICEnvironment.
Module E := EAst.

Notation "Σ 'p⊢' s ⇓ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Local Ltac invert_wf :=
  match goal with
  | [H : wf _ |- _] => inversion H;subst;clear H;cbn in *
  | [H : on_global_env _ _ _ |- _] => inversion H;subst;clear H;cbn in *
  | [H : on_global_decls _ _ _ _ (_ :: _) |- _] => inversion H;subst;clear H;cbn in *
  end.

Section ECorrect.

  Existing Instance config.extraction_checker_flags.
  Context {no: @PCUICSN.normalizing_flags config.extraction_checker_flags}.
  Context {X_type : PCUICWfEnv.abstract_env_impl} {X : projT1 (projT2 X_type)}.
  Context {normalising_in:
    forall Σ : global_env_ext, wf_ext Σ -> PCUICWfEnv.abstract_env_ext_rel X Σ -> PCUICSN.NormalizationIn Σ}.

Lemma erase_ind_body_correct Σ wfΣ kn mib oib wf :
  erases_one_inductive_body oib (trans_oib (@erase_ind_body X_type X _ _ Σ wfΣ kn mib oib wf)).
Proof.
  unfold erases_one_inductive_body, trans_oib, erase_ind_body; simpl.
  apply and_assoc.
  split; [|intuition auto].
  split.
  - unfold trans_ctors.
    rewrite map_map_In.
    unshelve erewrite (map_In_ext (fun x _ => (mkConstructor (cstr_name x) (cstr_arity x)))) by (now intros; destruct decompose_arr).
    induction ind_ctors; cbn; [now constructor|].
    constructor; [easy|].
    apply IHl.
  - induction P.ind_projs; [now constructor|].
    cbn.
    constructor; [easy|].
    apply IHl.
Qed.

Lemma erase_ind_body_wellformed Σ wfΣ kn mib oib wf :
  EWellformed.wf_inductive (trans_oib (@erase_ind_body X_type X _ _ Σ wfΣ kn mib oib wf)).
Proof.
  generalize (erase_ind_body_correct _ wfΣ _ _ _ wf).
  set (oib' := trans_oib _). clearbody oib'.
  induction 1.
  unfold EWellformed.wf_inductive.
  destruct H0.
  unfold EWellformed.wf_projections.
  destruct wf as [[i []]].
  destruct oib, oib'; cbn in *.
  destruct ind_projs1; eauto.
  depelim H0. destruct ind_ctors1; eauto.
  now depelim H.
  destruct ind_ctors1; eauto. cbn. depelim H. depelim H0.
  depelim onProjections; cbn in *. depelim onConstructors. depelim onConstructors. depelim o; cbn in *.
  destruct H. rewrite <- H. eapply Forall2_length in H2. rewrite <- H2, on_projs_all. rewrite <- cstr_args_length.
  apply eqb_refl. depelim H. now depelim H0.
Qed.

Lemma erase_ind_correct Σ wfΣ kn mib wf :
  erases_mutual_inductive_body mib (trans_mib (@erase_ind X_type X _ _ Σ wfΣ kn mib wf)).
Proof.
  unfold trans_mib, erase_ind.
  cbn.
  split; [|easy].
  cbn.
  generalize (Erasure.erase_ind_obligation_1 Σ kn mib wf).
  intros wfobl.
  induction P.ind_bodies; [constructor|].
  cbn in *.
  constructor; auto.
  apply erase_ind_body_correct.
Qed.

End ECorrect.

Opaque erase_type flag_of_type ErasureFunction.wf_reduction.
Import ssreflect.

Section EEnvCorrect.

Import PCUICWfEnv PCUICWfEnvImpl.

Existing Instance config.extraction_checker_flags.
Existing Instance PCUICSN.extraction_normalizing.
Context {X_type : PCUICWfEnv.abstract_env_impl} {X : X_type.π1}.
Context {normalising_in:
  forall Σ : global_env_ext, wf_ext Σ -> PCUICWfEnv.abstract_env_rel X Σ -> PCUICSN.NormalizationIn Σ}.

Lemma erase_global_decls_deps_recursive_correct_gen decls univs retro wfΣ include ignore_deps :
  let Σ := mk_global_env univs decls retro in
  (forall k, ignore_deps k = false) ->
  forall include', KernameSet.Subset include' include ->
  (forall k, KernameSet.In k include' -> P.lookup_env Σ k <> None) ->
  includes_deps Σ (trans_env (erase_global_decls_deps_recursive (X_type := X_type) (X := X) decls univs retro wfΣ include ignore_deps)) include'.
Proof.
  cbn.
  intros no_ignores include' sub all_in.
  induction decls as [|(kn, decl) Σ0 IH] in X_type, X, univs, decls, retro, wfΣ, all_in, include, include', sub |- *.
  { intros kn isin. cbn.
    now apply all_in in isin. }
  simpl in *.
  match goal with
  | |- context[erase_global_decl _ ?wfΣarg _ ?wfdeclarg] =>
      set (wfΣext := wfΣarg) in *;
        set (wfdecl := wfdeclarg) in *; clearbody wfdecl
  end.
  match goal with
  | |- context[erase_global_decls_deps_recursive _ _ _ ?wfΣarg] =>
    set (wfΣprev := wfΣarg) in *; clearbody wfΣprev
  end.

  rewrite no_ignores;cbn.
  destruct KernameSet.mem eqn:mem; cycle 1.
  - intros kn' isin.
    change {| P.universes := univs; P.declarations := (kn, wfdecl) :: Σ0; P.retroknowledge := retro |} with
      (add_global_decl {| P.universes := univs; P.declarations := Σ0; P.retroknowledge := retro|} (kn, wfdecl)).
    pose proof (abstract_env_ext_wf _ wfΣext) as [].
    pose proof (abstract_env_exists X) as [[Σfull hfull]].
    pose proof (abstract_env_wf _ hfull) as [wffull].
    apply global_erases_with_deps_weaken; auto.
    { pose proof (wfΣ _ hfull). now subst Σfull. }
    set (prf := (fun (Σ : global_env) => _)).
    eapply IH; eauto.
    intros k kisin.
    specialize (all_in _ kisin).
    unfold eq_kername in *.
    apply sub in kisin.
    apply KernameSet.mem_spec in kisin.
    destruct (Kername.reflect_kername) as [k_eq H].
    destruct (H k kn);congruence.
  - cbn in *.
    intros k isin.
    destruct (Kername.eq_dec k kn) as [->|]; cycle 1.
    { change {| P.universes := univs; P.declarations := (kn, wfdecl) :: Σ0; P.retroknowledge := retro |} with
      (add_global_decl {| P.universes := univs; P.declarations := Σ0; P.retroknowledge := retro |} (kn, wfdecl)).
      pose proof (abstract_env_ext_wf _ wfΣext) as [].
      pose proof (abstract_env_exists X) as [[Σfull hfull]].
      pose proof (abstract_env_wf _ hfull) as [wffull].
      apply global_erases_with_deps_cons; auto.
      { pose proof (wfΣ _ hfull). now subst Σfull. }
      eapply (IH _ _ _ _ wfΣprev _ (KernameSet.singleton k)).
      - intros ? ?.
        eapply KernameSet.singleton_spec in H; subst a.
        apply KernameSet.union_spec.
        right. now apply sub.
      - specialize (all_in _ isin).
        intros isink <-%KernameSet.singleton_spec.
        apply KernameSet.mem_spec in isin.
        unfold eq_kername in *.
        destruct (Kername.reflect_kername) as [k_eq H].
        destruct (H isink kn);congruence.

      - now apply KernameSet.singleton_spec. }

    cbn.
    destruct wfdecl; [left|right].
    all: unfold declared_constant, declared_minductive,
         P.declared_constant, P.declared_minductive; cbn.
    unfold Erasure.erase_constant_decl.
    all: unfold eq_kername in *.
    all: try rewrite eq_kername_refl.
    + eexists; split; [left;reflexivity|].
    unfold erase_constant_decl.
    destruct flag_of_type.
      destruct conv_ar.
      * destruct c eqn:Hc; cbn in *.
        destruct cst_body0 eqn:Hcb; cbn in *; cycle 1.
        { eexists; split;cbn; unfold EGlobalEnv.declared_constant;cbn.
          now rewrite eq_kername_refl. cbn.
          intuition congruence. }

        eexists. split;cbn; unfold EGlobalEnv.declared_constant;cbn.
        now rewrite eq_kername_refl.
        split; last first.
        { intros ? H.
          noconf H.
          constructor. }

        pose proof (abstract_env_ext_wf _ wfΣext) as [].
        pose proof (abstract_env_exists X) as [[Σfull hfull]].
        pose proof (abstract_env_wf _ hfull) as [wffull].
        (* pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop hpop]].
        pose proof (abstract_env_wf _ hpop) as [wfpop].
        eapply abstract_pop_decls_correct in hpop; tea. *)


        destruct c0 as [ctx univ [r]].
        destruct r.
        eapply @type_reduction with (B := mkNormalArity ctx univ) in clrel_rel; eauto.
        cbn in *.
        constructor.
        eapply (Is_type_extends (({| P.universes := univs; P.declarations := Σ0; P.retroknowledge := retro |}, _))).
        constructor. eapply X0. clear wfΣext. specialize (wfΣ _ hfull). now subst Σfull.
        { eapply extends_decls_extends_subrel, strictly_extends_decls_extends_decls.
           unfold strictly_extends_decls; trea. eexists. cbn; auto. eexists [_].
           cbn. reflexivity. reflexivity. } eauto.
        eexists.
        split; [eassumption|].
        left.
        apply isArity_mkNormalArity.
        clear wfΣext. specialize (wfΣ _ hfull). subst Σfull.
        depelim wffull; cbn in *. depelim o0. depelim o1. now eapply unlift_TermTyp.
      * eexists; split;cbn; unfold EGlobalEnv.declared_constant;cbn.
        now rewrite eq_kername_refl.
        unfold trans_cst; cbn.
        destruct c; cbn in *.
        destruct cst_body0; cbn in *; cycle 1.
        { intuition congruence. }

        match goal with
        | |- context[erase _ _ _ _ ?p] =>
          set (twt := p) in *; clearbody twt
        end.
        set (wfext := abstract_make_wf_env_ext _ _ _).
        (* destruct wfdecl as [wfdecl]. *)
        split.
        -- set (decl' := ConstantDecl _) in *.
          pose proof (abstract_env_ext_wf _ wfΣext) as [].
          pose proof (abstract_env_exists X) as [[Σfull hfull]].
          pose proof (abstract_env_wf _ hfull) as [wffull].
          pose proof (wfΣ _ hfull).
          pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop hpop]].
          pose proof (abstract_env_wf _ hpop) as [wfpop].
          eapply abstract_pop_decls_correct in hpop; tea.
          2:{ intros. pose proof (abstract_env_irr _ hfull H0). subst Σfull Σ. cbn. now eexists. }
          subst Σfull. destruct hpop as [? []]. cbn in *. subst.
          destruct Σpop as [univspop Σpop retropop]; cbn in *.
          (* pose proof (abstract_make_wf_env_ext_correct _ wfext).
           destruct wfdecl as [wfdecl onud].
          eapply @type_reduction with (B := cst_type0) in wfdecl as wfdecl1; eauto.
         2:{ depelim wfΣ. depelim o0. depelim o2. now cbn in on_global_decl_d. } *)

           eapply (erases_extends (_, _)); eauto.
           1:{ depelim wffull. depelim o0. depelim o1. eapply unlift_TermTyp. now cbn in on_global_decl_d. }
           1:{ eexists. reflexivity. eexists [_]; reflexivity. reflexivity. }
           now apply erases_erase.
        -- intros.
           noconf H.
           assert (unfold_add_gd : forall univs decls (decl : kername × global_decl),
                      add_global_decl (mk_global_env univs decls retro) decl = {| P.universes := univs; P.declarations := decl :: decls; P.retroknowledge := retro |}) by reflexivity.
           rewrite -{1}unfold_add_gd.
           repeat invert_wf.
           pose proof (abstract_env_ext_wf _ wfΣext) as [].
           pose proof (abstract_env_exists X) as [[Σfull hfull]].
           pose proof (abstract_env_wf _ hfull) as [wffull].
           pose proof (wfΣ _ hfull).
           pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop hpop]].
           pose proof (abstract_env_wf _ hpop) as [wfpop].
           eapply abstract_pop_decls_correct in hpop; tea.
           2:{ intros. pose proof (abstract_env_irr _ hfull H0). subst Σfull Σ. cbn. now eexists. }
           subst Σfull. destruct hpop as [? []]. cbn in *. subst.
           destruct Σpop as [univspop Σpop retropop]; cbn in *.
           apply erases_deps_cons;eauto;cbn in *.
           { now depelim wfpop. }
           { now depelim wffull. }
           depelim wffull. cbn in *. depelim o0. depelim o1. cbn in on_global_decl_d.
           eapply (@erase_global_erases_deps (_, _)); eauto.
           now eapply unlift_TermTyp.
           now apply erases_erase.
           eapply IH.
           ++ intros ? isin'.
              apply KernameSet.union_spec; left.
              now apply KernameSet.union_spec; right.
           ++ intros ? isin'.
              eapply term_global_deps_spec in isin' as [(? & ?)]; eauto.
              ** cbn in *. congruence.
              ** now eapply unlift_TermTyp.
              ** now apply erases_erase.
    + eexists _, _; split; [left; reflexivity|]; split.
      unfold EGlobalEnv.declared_minductive;cbn.
      now rewrite eq_kername_refl.
      cbn in *.
      apply erase_ind_correct.
Qed.

Lemma erase_global_decls_deps_recursive_correct decls univs retro wfΣ include ignore_deps :
  let Σ := mk_global_env univs decls retro in
  (forall k, ignore_deps k = false) ->
  (forall k, KernameSet.In k include -> P.lookup_env Σ k <> None) ->
  includes_deps Σ (trans_env (erase_global_decls_deps_recursive (X_type := X_type) (X := X) decls univs retro wfΣ include ignore_deps)) include.
Proof.
  intros; eapply erase_global_decls_deps_recursive_correct_gen; eauto. reflexivity.
Qed.

End EEnvCorrect.
