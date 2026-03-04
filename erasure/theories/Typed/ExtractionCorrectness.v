From Stdlib Require Import List ssreflect ssrbool.
From MetaRocq.Erasure.Typed Require Import ErasureCorrectness.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Erasure.Typed Require Import Extraction.
From MetaRocq.Erasure.Typed Require Import Optimize.
From MetaRocq.Erasure.Typed Require Import OptimizeCorrectness.
From MetaRocq.Erasure.Typed Require Import OptimizePropDiscr.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import WcbvEvalAux.
From Equations Require Import Equations.
From MetaRocq.Erasure Require Import ErasureCorrectness.
From MetaRocq.Erasure Require Import ErasureFunction.
From MetaRocq.Erasure Require Import ErasureFunctionProperties.
From MetaRocq.Erasure Require Import EWcbvEval.
From MetaRocq.Erasure Require Import Extract.
From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.PCUIC Require Import PCUICSafeLemmata.
From MetaRocq.PCUIC Require Import PCUICTyping.
From MetaRocq.PCUIC Require Import PCUICInversion.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import utils.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ⇓ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma wf_squash {Σ} :
  ∥wf_ext Σ∥ ->
  ∥wf Σ∥.
Proof. intros []. now constructor. Qed.

Lemma lookup_env_In d Σ : wf Σ -> In d (PEnv.declarations Σ) -> forall d', In d' (PEnv.declarations Σ) ->
  fst d = fst d' -> snd d = snd d'.
Proof using Type.
  intros [_].
  destruct Σ as [univs decls retro]; cbn in *.
  induction o in d |- *; auto.
  - intros H; inversion H.
  - intros [H|H].
    + subst. cbn.
      intros d' [H'|H']; subst; auto.
      intros eq.
      destruct o0 as [fresh _ _ _].
      subst kn. eapply P.fresh_global_iff_not_In in fresh.
      eapply (in_map fst) in H'.
      now apply fresh in H'.
    + intros d' [H'|H'] eq; subst; cbn in *; auto.
      subst.
      destruct o0 as [fresh _ _ _].
      eapply P.fresh_global_iff_not_In in fresh.
      eapply (in_map fst) in H.
      now apply fresh in H.
Qed.

Lemma lookup_global_In_wf d Σ : wf Σ ->
  In d (PEnv.declarations Σ) -> P.lookup_global (PEnv.declarations Σ) d.1 <> None.
Proof using Type.
  intros wfΣ. destruct d as [kn decl].
  intros hin. eapply (in_map fst) in hin.
  intros hne; rewrite <- P.lookup_global_None in hne. contradiction.
Qed.

Lemma global_erased_with_deps_erases_deps_tConst Σ Σer kn cst :
  wf Σ ->
  P.declared_constant Σ kn cst ->
  global_erased_with_deps Σ Σer kn ->
  erases_deps Σ Σer (E.tConst kn).
Proof.
  intros wf decl glob.
  destruct glob as [(?&?&?&?&?&?)|(?&?&?&?&?)].
  - econstructor; eauto.
  - unfold P.declared_constant, PCUICAst.declared_minductive in *.
    eapply lookup_env_In in decl; tea. now cbn in decl. auto.
Qed.

Module PEnv := PCUICAst.PCUICEnvironment.
Import PCUICWfEnv ErasureFunction ErasureFunctionProperties.

Lemma extends_trans Σ Σ' Σ'' :
  EGlobalEnv.extends Σ Σ' ->
  EGlobalEnv.extends Σ' Σ'' ->
  EGlobalEnv.extends Σ Σ''.
Proof.
  intros e e' kn h h'.
  eapply e in h'. now eapply e' in h'.
Qed.

(* Lemma trans_global_decl_erase {X_type X} :
  trans_global_decl (@Erasure.erase_global_decl X_type X Σ prf kn decl ond) = *)

Lemma filter_deps_ext deps deps' l :
  KernameSet.Equal deps deps' ->
  filter_deps deps l = filter_deps deps' l.
Proof.
  induction l as [|[kn d] decls] in deps, deps' |- *; cbn; auto.
  destruct (KernameSet.mem kn deps) eqn:e.
  eapply KernameSet.mem_spec in e.
  intros kne. eapply kne in e. eapply KernameSet.mem_spec in e. rewrite e.
  rewrite (IHdecls _ _ kne); eauto. destruct d. f_equal. eapply IHdecls. now rewrite kne.
  f_equal.
  intros hne.
  destruct (KernameSet.mem kn deps') eqn:e'.
  rewrite <- hne in e'. congruence.
  now eapply IHdecls.
Qed.

Lemma extends_cons_right Σ Σ' kn d :
  EGlobalEnv.fresh_global kn Σ ->
  EGlobalEnv.extends Σ Σ' ->
  EGlobalEnv.extends Σ ((kn, d) :: Σ').
Proof.
  intros hf he kn' d' hl.
  cbn.
  destruct (eqb_spec kn' kn). subst.
  now eapply EGlobalEnv.lookup_env_Some_fresh in hl.
  now eapply he in hl.
Qed.
Import EnvMap.

Opaque Erasure.flag_of_type.

Lemma erase_erasable {X_type X nin Γ t wt} :
  (forall Σ, abstract_env_ext_rel X Σ -> ∥ isErasable Σ Γ t ∥) ->
  @erase X_type X nin Γ t wt = EAst.tBox.
Proof.
  intros his.
  rewrite erase_equation_1.
  destruct inspect_bool. now cbn.
  exfalso.
  move/negP: i => hi. apply hi.
  now apply/is_erasableP.
Qed.

Lemma one_inductive_body_eq x y :
  x.(E.ind_name) = y.(E.ind_name) ->
  x.(E.ind_propositional) = y.(E.ind_propositional) ->
  x.(E.ind_kelim) = y.(E.ind_kelim) ->
  x.(E.ind_ctors) = y.(E.ind_ctors) ->
  x.(E.ind_projs) = y.(E.ind_projs) ->
  x = y.
Proof.
  destruct x, y; cbn in *; intros; f_equal; eauto.
Qed.

Lemma fresh_global_filter_deps {X_type X} {decls nin prf} {kn deps}:
  EnvMap.fresh_global kn decls ->
  EGlobalEnv.fresh_global kn (filter_deps deps (@erase_global X_type X decls nin prf)).
Proof.
  induction 1 in X_type, X, nin, prf, deps |- *; cbn.
  - constructor.
  - destruct x as [kn' []]; cbn in H |- *;
    destruct (KernameSet.mem kn' deps).
    + constructor. now cbn. eapply IHForall.
    + eapply IHForall.
    + constructor. now cbn. eapply IHForall.
    + eapply IHForall.
Qed.

Lemma trans_env_erase_global_decls {X_type X} decls nin eq univs retro prf deps deps' ignored :
  (forall k, ignored k = false) ->
  KernameSet.Subset deps deps' ->
  EnvMap.fresh_globals decls ->
  EGlobalEnv.extends
    (filter_deps deps (@erase_global X_type X decls nin eq))
    (trans_env (@Erasure.erase_global_decls_deps_recursive X_type X decls univs retro prf deps' ignored)).
Proof.
  induction decls in X_type, X, deps, deps', ignored, eq, nin, prf |- *.
  - now cbn.
  - cbn. intros hign hsub hf. depelim hf.
    destruct d; cbn [map filter_deps];
      try set (er := Erasure.erase_global_decl _ _ _ _ _);
      try set (er' := erase_constant_decl _ _ _ _);
      try set (prf' := fun (Σ : PCUICAst.PCUICEnvironment.global_env) => _);
      try set (prf'' := fun (Σ : PCUICAst.PCUICEnvironment.global_env) => _).
    + destruct (KernameSet.mem kn deps) eqn:e.
      * assert (KernameSet.mem kn deps') as ->.
        { eapply KernameSet.mem_spec in e.
          now apply KernameSet.mem_spec. }
        assert (trans_global_decl er = E.ConstantDecl er'.1) as H0.
        { subst er er'. clear.
          destruct c as [ty [] rel].
          2:{ cbn.
            unfold Erasure.erase_constant_decl, Erasure.erase_constant_decl_clause_1.
            destruct (Erasure.flag_of_type), conv_ar; try congruence; reflexivity. }
          unfold erase_constant_decl, erase_constant_body.
          cbn -[erase Erasure.erase_constant_decl abstract_make_wf_env_ext].
          unfold Erasure.erase_constant_decl, Erasure.erase_constant_decl_clause_1.
          destruct (Erasure.flag_of_type), conv_ar; try congruence.
          { cbn in c.
            epose proof (Erasure.conv_arity_Is_conv_to_Arity c).
            set (Σ := {| PEnv.universes := _ |}) in *.
            set (Σ' := {| PEnv.universes := _ ; PEnv.declarations := decls |}) in *.
            rewrite erase_erasable.
            intros ? HΣ.
            destruct H as [ar [[] isar]].
            set (obl := fun (Σ : PCUICAst.PCUICEnvironment.global_env) _ => _) in HΣ.
            eapply Erasure.abstract_eq_wf in prf as [HΣ' [wf]].
            pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop hΣpop]].
            eapply abstract_make_wf_env_ext_correct in HΣ; tea. subst Σ0.
            eapply abstract_pop_decls_correct in hΣpop; tea.
            2:{ intros. pose proof (abstract_env_irr _ HΣ' H). subst Σ0. cbn. now eexists. }
            destruct hΣpop as [? []]. destruct Σpop; cbn in *. subst.
            depelim wf. depelim o0. depelim o1. cbn in on_global_decl_d.
            sq. exists ar. split; [|now left].
            unshelve eapply PCUICSR.type_reduction. 4:apply X0. constructor; eauto. now eapply unlift_TermTyp.
            reflexivity. }
        { cbn [trans_global_decl]. unfold trans_cst, cst_body.
          unfold erase_constant_body; cbn -[erase]. do 3 f_equal.
          eapply erase_irrel_global_env.
          clear; intros ?? h1 h2.
          pose proof (abstract_env_exists (abstract_pop_decls X)) as [[[] hΣpop]].
          split; intros.
          do 2 (erewrite <- abstract_env_lookup_correct'; tea).
          eapply abstract_make_wf_env_ext_correct in H; tea.
          eapply abstract_make_wf_env_ext_correct in h2; tea. congruence.
          do 2 (erewrite abstract_primitive_constant_correct; tea).
          eapply abstract_make_wf_env_ext_correct in H; tea.
          eapply abstract_make_wf_env_ext_correct in h2; tea. congruence. } }
        rewrite <- H0.
        eapply extends_cons.
        unfold trans_env in IHdecls.
        eapply (IHdecls _ _ _ _ prf''); eauto. cbn [negb].
        rewrite hign /=.
        intros kn'.
        rewrite !KernameSet.union_spec.
        intuition eauto.
        change (constant_decls_deps er'.1) with (global_decl_deps (E.ConstantDecl er'.1)) in H2. rewrite -H0 in H2.
        clear -H2. destruct er as [[ty []] | |[]]; cbn in *; rewrite ?KernameSet.union_spec in H2 *;
          intuition auto; knset.
      * destruct (KernameSet.mem kn deps') eqn:e'.
        rewrite hign. cbn [map].
        eapply extends_cons_right.
        now eapply fresh_global_filter_deps.
        eapply IHdecls; eauto. cbn -[er]. intros kn'. rewrite !KernameSet.union_spec. intuition eauto.
        eapply IHdecls; eauto.
    + destruct (KernameSet.mem kn deps) eqn:e.
      * assert (KernameSet.mem kn deps') as ->.
        { eapply KernameSet.mem_spec in e.
          now apply KernameSet.mem_spec. }
        cbn [map]. cbn in er.
        assert (trans_global_decl er = E.InductiveDecl (erase_mutual_inductive_body m)) as H0.
        { clear. subst er.
          unfold trans_global_decl. f_equal.
          unfold trans_mib, erase_mutual_inductive_body.
          f_equal.
          unfold Erasure.erase_ind. cbn.
          rewrite map_map_In.
          pose proof (Erasure.abstract_eq_wf _ _ _ prf) as [h [wf]].
          eapply map_mapIn_eq. intros x hin.
          destruct x. unfold erase_one_inductive_body. cbn -[Erasure.erase_ind_body].
          eapply one_inductive_body_eq.
          1-3:reflexivity.
          { cbn [E.ind_ctors trans_oib]. rewrite /trans_ctors.
            unfold Erasure.erase_ind_body.
            cbn [ExAst.ind_ctors]. rewrite map_map_In.
            eapply map_mapIn_eq.
            intros [] hin'.
            destruct decompose_arr; reflexivity. }
          { cbn. rewrite map_In_spec map_map_compose //. } }
        rewrite -H0.
        eapply extends_cons.
        eapply IHdecls; eauto.
        intros kn'; knset.
      * destruct (KernameSet.mem kn deps') eqn:e'.
        rewrite hign. cbn [map].
        eapply extends_cons_right. now eapply fresh_global_filter_deps.
        eapply IHdecls; eauto. cbn -[er]. intros kn'. rewrite !KernameSet.union_spec. intuition eauto.
        eapply IHdecls; eauto.
Qed.

Lemma wf_trans_inductives (m : PCUICAst.PCUICEnvironment.mutual_inductive_body) {X_type X no nin} Σ hΣ kn prf :
  forallb EWellformed.wf_inductive (map trans_oib (@Erasure.erase_ind X_type X no nin Σ hΣ kn m prf).(ind_bodies)).
Proof.
  destruct m.
  cbn.
  set (prf' := Erasure.erase_ind_obligation_1 _ _ _ _). clearbody prf'.
  rewrite forallb_map.
  set (fn := fun oib _ => _).
  assert (forall x y, EWellformed.wf_inductive (trans_oib (fn x y))).
  { intros [] hin. unfold fn.
    apply (@erase_ind_body_wellformed no X_type X nin Σ hΣ kn _ _ (prf' _ hin)). }
  clear -H. clearbody fn. clear -H.
  induction ind_bodies; cbn => //.
  rewrite IHind_bodies; eauto. rewrite andb_true_r; eauto.
Qed.

Lemma wf_erase_global_decl :
  forall (H := EWellformed.all_env_flags)
        X_type X
        (k : kername) (g : PCUICAst.PCUICEnvironment.global_decl)
         (decls : list (kername * PCUICAst.PCUICEnvironment.global_decl))
         (univs : Universes.ContextSet.t) retros prf w wt (Σex : global_env) prf' seeds ignored,
    let eg := (@Erasure.erase_global_decl X_type
    (abstract_make_wf_env_ext X (PCUICAst.PCUICLookup.universes_decl_of_decl g) prf)
    ({| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |},
      PCUICAst.PCUICLookup.universes_decl_of_decl g)
    w k g wt) in
    (forall kn, ignored kn = false) ->
    Σex = @Erasure.erase_global_decls_deps_recursive X_type X decls univs retros prf'
      (KernameSet.union (Erasure.decl_deps eg) seeds) ignored ->
    EWellformed.wf_glob (trans_env Σex) ->
    EWellformed.wf_global_decl
      (trans_env Σex)
      (trans_global_decl eg) = true.
Proof.
  intros H X_type X k g decls univs retros prf w wt Σex prf' seeds ignored eg hign eqex wf_global.
  revert eqex. subst eg.
  unfold Erasure.erase_global_decl.
  destruct g.
  - destruct (Erasure.erase_constant_decl) eqn:Hdecl.
    * unfold Erasure.erase_constant_decl,Erasure.erase_constant_decl_clause_1 in *.
      destruct (Erasure.flag_of_type), conv_ar; try congruence.
      inversion Hdecl;subst;clear Hdecl.
      unfold trans_global_decl,trans_cst.
      cbn [EWellformed.wf_global_decl].
      unfold MROption.option_default.
      destruct EAst.cst_body eqn:heq => //.
      set (deps := KernameSet.union _ _).
      unshelve eapply (erase_constant_body_correct'' (X_type := X_type) (decls := decls) seeds) in heq as [[t0 [T [[] ?]]]].
      shelve. 4:exact w. intros. eapply Erasure.fake_normalization; tea.
      { intros. now rewrite (prf' _ H0). }
      intros ->. cbn.
      eapply EWellformed.extends_wellformed; tea.
      set (prf'' := fun _ => _). clearbody prf''. cbn in prf''.
      rewrite erase_global_deps_erase_global.
      eapply trans_env_erase_global_decls; tea. subst deps. cbn [Erasure.decl_deps cst_body cst_type].
      intros kn'. rewrite !KernameSet.union_spec. intuition eauto.
      pose proof (abstract_env_ext_wf _ w) as [].
      eapply (PCUICWfEnvImpl.wf_fresh_globals _ X0).
    * intros ->. cbn.
      destruct o => //=.
  - intros he => /=.
    eapply wf_trans_inductives.
Qed.

Import EEtaExpandedFix.

Lemma includes_deps_equiv Σ Σ' deps deps' :
  KernameSet.Equal deps deps' ->
  includes_deps Σ Σ' deps ->
  includes_deps Σ Σ' deps'.
Proof.
  unfold includes_deps.
  intros eq hn kn. now rewrite <-eq.
Qed.

Lemma expanded_erase (cf := config.extraction_checker_flags)
  (no := PCUICSN.normalizing_flags)
  {X_type X} univs wfΣ t wtp ignored :
  (forall kn, ignored kn = false) ->
  forall Σ prf', abstract_env_rel X Σ -> PCUICEtaExpand.expanded Σ [] t ->
  let X' :=  abstract_make_wf_env_ext X univs wfΣ in
  forall normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> PCUICSN.NormalizationIn Σ,
  let et := (@erase X_type X' normalization_in' [] t wtp) in
  let deps := EAstUtils.term_global_deps et in
  expanded (trans_env (@Erasure.erase_global_decls_deps_recursive X_type X Σ.(PEnv.declarations) Σ.(PEnv.universes) Σ.(PEnv.retroknowledge) prf' deps ignored)) [] et.
Proof.
  intros hign Σ heq wf hexp X' normalization_in'.
  pose proof (abstract_env_wf _ wf) as [wf'].
  pose proof (abstract_env_ext_exists X') as [[? wfmake]].
  pose proof (abstract_env_ext_wf _ wfmake) as [].
  pose proof (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfmake). subst x.
  eapply (expanded_erases (Σ := (Σ, univs))); tea.
  eapply (erases_erase (X := X')); eauto.
  destruct (wtp _ wfmake).
  eapply (erase_global_erases_deps (Σ := (Σ, univs))); eauto.
  eapply erases_erase; eauto. cbn. destruct Σ.
  eapply erase_global_decls_deps_recursive_correct_gen => //=.
  intros k H0.
  eapply term_global_deps_spec in H0; tea. 2:eapply X0.
  cbn in H0. destruct H0 as [[decl hl]]. now rewrite hl.
  now eapply erases_erase.
Qed.

Lemma expanded_erase_global_decl :
  forall (H := EWellformed.all_env_flags)
        X_type X
        (k : kername) (g : PCUICAst.PCUICEnvironment.global_decl)
         env prf w wt (Σex : global_env) prf' seeds ignored,
    let eg := (@Erasure.erase_global_decl X_type
    (abstract_make_wf_env_ext X (PCUICAst.PCUICLookup.universes_decl_of_decl g) prf) (env, PCUICAst.PCUICLookup.universes_decl_of_decl g)
    w k g wt) in
    (forall kn, ignored kn = false) ->
    Σex = @Erasure.erase_global_decls_deps_recursive X_type X env.(PEnv.declarations) env.(PEnv.universes) env.(PEnv.retroknowledge) prf'
      (KernameSet.union (Erasure.decl_deps eg) seeds) ignored ->
    expanded_global_env (trans_env Σex) ->
    PCUICEtaExpand.expanded_decl env g ->
    expanded_decl (trans_env Σex) (trans_global_decl eg).
Proof.
  intros H X_type X k g [univs decls retros] prf w wt Σex prf' seeds ignored eg hign eqex wf_global; cbn in *.
  revert eqex. subst eg.
  set (Σ := {| PEnv.universes := _ |}) in *.
  pose proof (abstract_env_exists X) as [[Σ' hΣ]].
  pose proof (prf' _ hΣ). subst Σ'. destruct (prf _ hΣ) as [wfΣ].
  unfold Erasure.erase_global_decl.
  destruct g.
  - destruct (Erasure.erase_constant_decl) eqn:Hdecl.
    * unfold Erasure.erase_constant_decl,Erasure.erase_constant_decl_clause_1 in *.
      destruct (Erasure.flag_of_type), conv_ar; try congruence.
      inversion Hdecl;subst;clear Hdecl.
      unfold trans_global_decl,trans_cst.
      cbn [EWellformed.wf_global_decl].
      unfold MROption.option_default.
      destruct EAst.cst_body eqn:heq => //.
      set (deps := KernameSet.union _ _).
      destruct c as [ty [b|] cunivs rel]. 2:cbn in heq => //.
      intros eq []. cbn in expanded_body. move: eq.
      unshelve eapply (erase_constant_body_correct'' (X_type := X_type) (decls := decls) seeds) in heq as [[t0' [T [[] ?]]]].
      shelve. 4:exact w. intros. eapply Erasure.fake_normalization; tea.
      { intros. now rewrite (prf' _ H0). }
      intros ->. cbn. destruct p as [[eq ?] ?]. cbn in eq. noconf eq.
      eapply expanded_erases; tea. apply wfΣ. cbn. clear i. cbn.
      eapply (erase_global_erases_deps (Σ := (Σ, cunivs))); eauto. cbn.
      set (ert := Erasure.erase_type _ _ _ _) in deps. clearbody ert.
      cbn in deps. clear wf_global.
      eapply erase_global_decls_deps_recursive_correct_gen => //.
      { subst deps. knset. }
      intros.
      cbn in e.
      eapply term_global_deps_spec in H0; tea. 2:eapply wfΣ.
      cbn in H0. destruct H0 as [[decl hl]]. now rewrite hl.
    * intros ->. cbn.
      destruct o => //=. cbn in Hdecl. cbn.
      intros; constructor.
  - intros he => //=.
Qed.

Transparent Erasure.flag_of_type.

Ltac invert_wf :=
  match goal with
  | [H : wf _ |- _] => sq; inversion H;subst;clear H;cbn in *
  | [H : P.on_global_decls _ _ _ _ (_ :: _) |- _] => inversion H;subst;clear H;cbn in *
  | [H : P.on_global_decls_data _ _ _ _ _ _ _ |- _] => inversion H; subst; clear H; cbn in *
  end.

Lemma wf_erase_global_decls_recursive (H := EWellformed.all_env_flags) :
  forall X_type X decls univs retros w seeds (ignored : kername -> bool),
    (forall k, ignored k = false) ->
    let Σex := @Erasure.erase_global_decls_deps_recursive X_type X decls univs retros w seeds ignored in
    EWellformed.wf_glob (trans_env Σex).
Proof.
  intros X_type X decls univs retros w seeds ignored hign ?.
  subst Σex.
  revert seeds.
  induction decls in X_type, X, w |- *;intros seeds;auto;try constructor.
  simpl.
  destruct a;simpl.
  destruct (KernameSet.mem _ _);cbn.
  - unfold MRProd.test_snd;cbn.
    constructor.
    * unfold trans_env in *;cbn in *.
      apply IHdecls.
    * cbn.
      remember (KernameSet.union _ _) as kns.
      rewrite hign in Heqkns. cbn in Heqkns.
      remember (Erasure.erase_global_decls_deps_recursive decls univs _ _ _ _) as Σex.
      assert (EWellformed.wf_glob (trans_env Σex)) by now subst Σex.
      rewrite -/(trans_env _).
      eapply wf_erase_global_decl; eauto. rewrite HeqΣex. f_equal. exact Heqkns.
    * sq.
      apply OptimizePropDiscr.trans_env_fresh_global.
      apply fresh_globals_erase_global_decl_rec.
      change decls with (PEnv.declarations
        {| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |}).
      eapply Erasure.abstract_eq_wf in w as [? []].
      apply PCUICWfEnvImpl.wf_fresh_globals; eauto.
      eapply Erasure.wf_pop_decl in X0; trea. eapply X0.
      apply fresh_global_erase_global_decl_rec.
      eapply Erasure.abstract_eq_wf in w as [? []].
      eapply PCUICWfEnvImpl.wf_fresh_globals in X0. now depelim X0.
  - apply IHdecls.
Qed.

Lemma expanded_erase_global_decls_recursive (H := EWellformed.all_env_flags) :
  forall X_type X decls univs retros w seeds (ignored : kername -> bool),
    (forall k, ignored k = false) ->
    let Σex := @Erasure.erase_global_decls_deps_recursive X_type X decls univs retros w seeds ignored in
    PCUICEtaExpand.expanded_global_declarations univs retros decls ->
    expanded_global_env (trans_env Σex).
Proof.
  intros X_type X decls univs retros w seeds ignored hign ?.
  subst Σex.
  revert seeds.
  induction decls in X_type, X, w |- *;intros seeds;auto;try constructor.
  simpl.
  destruct a;simpl.
  destruct (KernameSet.mem _ _);cbn.
  - unfold MRProd.test_snd;cbn.
    constructor.
    * unfold trans_env in *;cbn in *.
      depelim H0.
      now apply IHdecls.
    * cbn. depelim H0. cbn in H1.
      remember (KernameSet.union _ _) as kns.
      rewrite hign in Heqkns. cbn in Heqkns.
      remember (Erasure.erase_global_decls_deps_recursive decls univs _ _ _ _) as Σex.
      eapply expanded_erase_global_decl; tea. cbn. erewrite <- Heqkns. exact HeqΣex. subst Σex.
      eapply IHdecls; eauto.
  - intros H0; depelim H0. eapply IHdecls; eauto.
Qed.

Lemma optimize_correct `{EWellformed.EEnvFlags} Σ fgΣ t v :
  ELiftSubst.closed t = true ->
  EGlobalEnv.closed_env (trans_env Σ) = true ->
  EWellformed.wf_glob (trans_env Σ) ->
  @EWcbvEval.eval default_wcbv_flags (trans_env Σ) t v ->
  @EWcbvEval.eval
      (EWcbvEval.disable_prop_cases opt_wcbv_flags)
      (trans_env (map (on_snd (remove_match_on_box_decl (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)))) Σ))
      (EOptimizePropDiscr.remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) t)
      (EOptimizePropDiscr.remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) v).
Proof.
  intros cl_t cl_env wfg ev.
  remember (EEnvMap.GlobalContextMap.make _ _) as Σ0.
  assert (trans_env (map (on_snd (remove_match_on_box_decl Σ0)) Σ) =
    EOptimizePropDiscr.remove_match_on_box_env Σ0) as ->.
  { cbn. rewrite /trans_env HeqΣ0 map_map_compose. cbn. rewrite /trans_env.
    rewrite map_map_compose /on_snd. cbn. eapply map_ext.
    intros [[] []]; cbn. destruct c as [[] []] => //. reflexivity.
    do 2 f_equal. rewrite /EOptimizePropDiscr.remove_match_on_box_constant_decl /=.
    now destruct o; cbn. }
  unshelve eapply (EOptimizePropDiscr.remove_match_on_box_correct (fl := default_wcbv_flags) (Σ := Σ0));subst;cbn;eauto.
Qed.


Theorem extract_correct
        (H := EWellformed.all_env_flags)
        (wfl := opt_wcbv_flags)
        (Σ : P.global_env_ext) (wfΣ : ∥wf_ext Σ∥)
        kn ui ind c ui' ignored exΣ :
  axiom_free Σ ->
  welltyped Σ [] (P.tConst kn ui) ->
  Σ p⊢ P.tConst kn ui ⇓ P.tConstruct ind c ui' ->
  (isErasable Σ [] (P.tConstruct ind c ui') -> False) ->
  (forall k, ignored k = false) ->
  extract_pcuic_env
    (pcuic_args extract_within_coq)
    Σ (wf_squash wfΣ) (KernameSet.singleton kn) ignored = Ok exΣ ->
  ∥trans_env exΣ e⊢ E.tConst kn ⇓ E.tConstruct ind c []∥.
Proof.
  intros ax [T wt] ev not_erasable no_ignores ex.
  cbn -[dearg_transform] in *.
  destruct dearg_transform eqn:dt; cbn -[dearg_transform] in *; [|congruence].
  injection ex as ->.
  destruct wfΣ.
  eapply erases_correct with
    (Σ' := trans_env (Erasure.erase_global_decls_deps_recursive (PCUICAst.PCUICEnvironment.declarations Σ)
               (PCUICAst.PCUICEnvironment.universes Σ) _ _
               (KernameSet.singleton kn) ignored)) in ev as (erv&erase_to&[erev]);eauto.
  + depelim erase_to;[|easy].
    constructor.
    eapply dearg_transform_correct; eauto.
    clear dt.
    eapply (@optimize_correct _ _ _ (tConst kn) (tConstruct ind c []));eauto.
    * remember (Erasure.erase_global_decls_deps_recursive _ _ _ _ _ _) as eΣ.
      assert (EWellformed.wf_glob (trans_env eΣ)).
      { subst eΣ. now eapply wf_erase_global_decls_recursive. }
      now apply EWellformed.wellformed_closed_env.
    * eapply wf_erase_global_decls_recursive; auto.
  + now eexists.
  + eapply inversion_Const in wt as (?&?&?&?&?); auto.
    clear dt.
    eapply global_erased_with_deps_erases_deps_tConst; eauto.
    destruct Σ as [Σ0 univ_decls].
    destruct Σ0 as [univs Σ1].
    apply wf_ext_wf in w as w1. cbn.
    eapply erase_global_decls_deps_recursive_correct;eauto.
    * unfold PCUICAst.declared_constant in *.
      cbn.
      intros ? ->%KernameSet.singleton_spec;cbn in *.
      intros eq. set (env := {| PEnv.declarations := Σ1 |}) in *.
      eapply (lookup_global_In_wf _ env) in d; eauto.
    * now apply KernameSet.singleton_spec.
    Unshelve. eapply fresh_globals_erase_global_decl_rec.
      now eapply PCUICWfEnvImpl.wf_fresh_globals.
Qed.

From Stdlib Require Import String.
Local Open Scope string_scope.

Import MonadNotation.

Definition compute_masks overridden_masks do_trim_const_masks do_trim_ctor_masks Σ : result dearg_set bytestring.string :=
  let (const_masks, ind_masks) := Utils.timed "Dearg analysis" (fun _ => analyze_env overridden_masks Σ) in
  let const_masks := (if do_trim_const_masks then trim_const_masks else id) const_masks in
  let ind_masks := (if do_trim_ctor_masks then trim_ind_masks else id) ind_masks in
  throwIf (negb (is_expanded_env ind_masks const_masks Σ))
    "Erased environment is not expanded enough for dearging to be provably correct"%bs ;;
  throwIf (negb (valid_masks_env ind_masks const_masks Σ))
    "Analysis produced masks that ask to remove live arguments"%bs ;;
  Ok (Build_dearg_set const_masks ind_masks).

Import PCUICWfEnvImpl PCUICAst.PCUICEnvironment.

Program Definition make_env {Σ} (wfΣ : ∥wf_ext Σ∥) :=
  @abstract_make_wf_env_ext _ (optimized_abstract_env_impl (guard := Erasure.fake_guard_impl_instance)) (PCUICWfEnvImpl.build_wf_env_from_env Σ (map_squash fst wfΣ)) Σ.2 _.

Program Definition erase_env {Σ} wfΣ seeds ignore :=
  Erasure.erase_global_decls_deps_recursive (X_type := PCUICWfEnvImpl.optimized_abstract_env_impl (guard := Erasure.fake_guard_impl_instance))
    (X := PCUICWfEnvImpl.build_wf_env_from_env Σ wfΣ)
    (declarations Σ) (universes Σ) (retroknowledge Σ) _ seeds ignore.
  Next Obligation.
    destruct Σ => //.
  Qed.

Program Definition erase_term {Σ} (wfΣ : ∥wf_ext Σ∥) (t : PCUICAst.term) (w : welltyped Σ [] t) : term :=
  let wfext := make_env wfΣ in
  (erase _ wfext (normalization_in := _) [] t _).
  Next Obligation.
    refine (let 'sq wfΣ := wfΣ in let nin := Erasure.fake_normalization Σ wfΣ in _).
    eapply nin. destruct Σ. apply H.
  Qed.

  Next Obligation.
    destruct Σ. apply w.
  Qed.

Lemma remove_match_on_box_env_lemma {Σ} (wfΣ : ∥ wf Σ ∥) seeds ignore :
  fresh_globals (erase_env wfΣ seeds ignore).
Proof.
  destruct wfΣ.
  unfold erase_env.
  now eapply fresh_globals_erase_global_decl_rec, wf_fresh_globals.
Qed.

Lemma remove_match_on_box_trans_env {Σ} (wfΣ : ∥ wf Σ ∥) seeds ignore :
  EnvMap.fresh_globals (trans_env (erase_env wfΣ seeds ignore)).
Proof.
  destruct wfΣ.
  unfold erase_env.
  eapply OptimizePropDiscr.remove_match_on_box_env_obligation_1.
  now eapply fresh_globals_erase_global_decl_rec, wf_fresh_globals.
Qed.

Import EWellformed.
Theorem extract_correct_gen
        (H := EWellformed.all_env_flags)
        (wfl := default_wcbv_flags)
        (Σ : P.global_env_ext) (wfΣ : ∥wf_ext Σ∥)
        t v ignored masks
        overridden_masks
        do_trim_const_masks do_trim_ctor_masks
        :
  axiom_free Σ ->
  forall wt : welltyped Σ [] t,
  Σ p⊢ t ⇓ v ->
  (isErasable Σ [] t -> False) ->
  (forall k, ignored k = false) ->
  let t' := erase_term wfΣ t wt in
  let deps := (EAstUtils.term_global_deps t') in
  let erΣ := erase_env (map_squash fst wfΣ) deps ignored in
  let gerΣ := EEnvMap.GlobalContextMap.make (trans_env erΣ)
  (trans_env_fresh_globals erΣ (remove_match_on_box_env_lemma (map_squash fst wfΣ) deps ignored)) in
  let erΣ := remove_match_on_box_env erΣ (remove_match_on_box_env_lemma _ deps ignored) in
  compute_masks overridden_masks do_trim_const_masks do_trim_ctor_masks erΣ = Ok masks ->
  let t'' := EOptimizePropDiscr.remove_match_on_box gerΣ t' in
  valid_cases (ind_masks masks) t'' ->
  is_expanded (ind_masks masks) (const_masks masks) t'' ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\
  ∥ EWcbvEval.eval (wfl := opt_wcbv_flags) (trans_env (dearg_env masks erΣ)) (dearg_term masks t'') (dearg_term masks (EOptimizePropDiscr.remove_match_on_box gerΣ v')) ∥.
Proof.
  intros ax [T wt] ev not_erasable no_ignores t' deps er ger er' hmas t'' vcs isexp.
  cbn -[dearg_transform] in *.
  destruct wfΣ.
  unfold erase_term, make_env in t'.
  set (e := abstract_make_wf_env_ext _ _ _) in *.
  pose proof (abstract_env_ext_exists e) as [[Σe he]].
  match goal with
  [H := context [ @erase ?X_type ?X ?nin ?Γ t ?wt ] |- _ ] =>
   pose proof (@erases_erase X_type X nin Γ t wt _ he)
  end.
  cbn in he. subst Σe. destruct Σ as [Σ univs]; cbn [fst snd] in *.
  assert (wv : welltyped (Σ, univs) [] v).
  { eexists. eapply PCUICClassification.subject_reduction_eval; tea. }
  eapply erases_correct with (Σ' := trans_env er) in ev as (erv&erase_to&[erev]);eauto.
  2:{ now eexists. }
  * exists erv. split => //.
    sq.
    eapply dearg_transform_gen_correct; eauto.
    + assert (EWellformed.wf_glob (trans_env er')).
      { subst er'. rewrite trans_env_remove_match_on_box_env.
        eapply EOptimizePropDiscr.remove_match_on_box_env_wf => //.
        now eapply wf_erase_global_decls_recursive. }
      now apply EWellformed.wellformed_closed_env.
    + subst t''.
      eapply EOptimizePropDiscr.closed_remove_match_on_box.
      eapply EWellformed.wellformed_closed.
      unshelve eapply (erase_wellformed_weaken (declarations Σ) _ _ _ (Γ:=[])).
      2:{ cbn; congruence. } 2:exact deps. intros.
      now eapply Erasure.fake_normalization.
    + subst t'' t'.
      rewrite trans_env_remove_match_on_box_env.
      unshelve eapply (EOptimizePropDiscr.remove_match_on_box_correct (fl := default_wcbv_flags)) => //=.
      { cbn. now eapply wf_erase_global_decls_recursive. }
      { simpl. eapply EWellformed.wellformed_closed_env.
        now eapply wf_erase_global_decls_recursive. }
      eapply wellformed_closed.
      unshelve eapply (erase_wellformed_weaken (declarations Σ) _ _ _ (Γ := [])).
      2:{ cbn; congruence. } 2:exact deps. intros. eapply Erasure.fake_normalization; eauto.
  * eapply erase_global_erases_deps; tea.
    subst er. unfold erase_env.
    set (obl := fun (Σ' : global_env) => _).
    destruct Σ; cbn [declarations retroknowledge universes] in *.
    eapply (erase_global_decls_deps_recursive_correct _ _ _ obl); eauto.
    intros k hin.
    eapply term_global_deps_spec in hin; tea. red in hin. destruct hin as [[decl eq]].
    cbn in eq. cbn. now rewrite eq. cbn. eapply w.
Qed.

Theorem extract_correct_gen'
        (H := EWellformed.all_env_flags)
        (wfl := opt_wcbv_flags)
        (Σ : ExAst.global_env) t v masks
        overridden_masks do_trim_const_masks do_trim_ctor_masks :
  EGlobalEnv.closed_env (trans_env Σ) ->
  ELiftSubst.closedn 0 t ->
  trans_env Σ e⊢ t ⇓ v ->
  compute_masks overridden_masks do_trim_const_masks do_trim_ctor_masks Σ = Ok masks ->
  valid_cases (ind_masks masks) t ->
  is_expanded (ind_masks masks) (const_masks masks) t ->
  ∥ EWcbvEval.eval (trans_env (dearg_env masks Σ)) (dearg_term masks t) (dearg_term masks v) ∥.
Proof.
  intros cle clt ev hmas vcs isexp.
  sq.
  eapply dearg_transform_gen_correct; eauto.
Qed.

(* Print Assumptions extract_correct. *)

(** There are some assumptions of which almost all are in MetaRocq.
    From this project is only assume_env_wellformed assumption which is
    used to assume that the environments we extract are
    wellformed. MetaRocq's safe checker does not run from within Rocq, so
    we cannot type check the environments. However, our environments
    are unquoted directly from Rocq's kernel where they are already
    welltyped, so this is justified (and the same assumption is used in
    MetaRocq when they run their erasure).

    The rest of the assumptions are normal MetaRocq assumptions
    (which are justified in Rocq Rocq Correct!).

    [JMeq.JMeq_eq] leaks from the use of some tactics and probably can be avoided.
 *)
