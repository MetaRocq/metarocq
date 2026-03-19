From Equations Require Import Equations.
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Ast TypingWf WfAst TermEquality EtaExpand TemplateProgram.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCumulativity
     PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration
     PCUICCasesContexts PCUICEtaExpand
     PCUICProgram.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC TemplateToPCUICCorrectness.

Tactic Notation "wf_inv" ident(H) simple_intropattern(p) :=
(eapply WfAst.wf_inv in H; progress cbn in H; try destruct H as p) ||
(apply WfAst.wf_mkApps_napp in H; [|easy]; try destruct H as p).

Local Hint Constructors expanded : expanded.

Lemma expanded_context_map2_bias_left Σ n bctx ctx :
  #|ctx| = #|bctx| ->
  expanded_context Σ n ctx ->
  expanded_context Σ n
     (map2_bias_left set_binder_name dummy_decl bctx ctx).
Proof.
  unfold expanded_context.
  intros hl.
  rewrite map2_map2_bias_left //.
  intros [a]. sq.
  induction a in bctx, hl |- *; try econstructor; auto.
  - cbn. destruct bctx; constructor.
  - destruct bctx => //.
    cbn. constructor; auto. cbn.
    destruct (decl_body d); constructor => //. depelim p.
    cbn in hl. assert (#|Γ| = #|bctx|) by lia.
    rewrite map2_length //. now rewrite -H0.
Qed.

Import PCUICWeakeningEnv.

Lemma declared_minductive_expanded {cf:checker_flags} Σ {wfΣ : wf Σ} c mdecl :
  expanded_global_env Σ ->
  declared_minductive Σ c mdecl ->
  exists Σ', ∥ strictly_extends_decls Σ' Σ ∥ /\ expanded_minductive_decl Σ' mdecl.
Proof.
  unfold expanded_global_env.
  intros decl H. unshelve eapply declared_minductive_to_gen in H; eauto.
  clear wfΣ. move:decl H. unfold declared_minductive_gen, lookup_env.
  destruct Σ as [univs Σ]; cbn.
  intros exp; induction exp; cbn in * => //.
  destruct decl as [kn d]; cbn.
  destruct (eqb_spec c kn). intros [= ->].
  subst c. eexists. split ; [|exact H]. sq. red. split => //. cbn.
  eexists. cbn. instantiate (1:= [_]); reflexivity.
  intros hl; destruct (IHexp  hl). exists x. intuition auto.
  sq. eapply strictly_extends_decls_trans; tea.
  split => //. now exists [(kn, d)].
Qed.

Lemma declared_constructor_expanded {cf:checker_flags} {Σ} {wfΣ : wf Σ} {c mdecl idecl cdecl} :
  expanded_global_env Σ ->
  declared_constructor Σ c mdecl idecl cdecl ->
  exists Σ', ∥ strictly_extends_decls Σ' Σ ∥ /\ expanded_minductive_decl Σ' mdecl /\ expanded_constructor_decl Σ' mdecl cdecl.
Proof.
  intros exp [[decli hnth] hnth'].
  eapply declared_minductive_expanded in decli; eauto.
  destruct decli as [Σ' [ext exp']]. exists Σ'; split => //. split => //.
  destruct exp' as [hp hb]. solve_all.
  eapply nth_error_all in hb; tea.
  destruct hb as [hb]. solve_all.
  eapply nth_error_all in hb; tea.
Qed.

Lemma expanded_extended_subst {Σ Γ Δ} :
  expanded_context Σ Γ Δ ->
  forall n,
  Forall (expanded Σ (repeat 0 (n + context_assumptions Δ) ++ Γ)) (extended_subst Δ n).
Proof.
  intros [a]; induction a. cbn. constructor.
  cbn. destruct d as [na [b|] ty]; cbn in *. constructor; auto.
  { cbn. eapply (expanded_subst _ _ 0 _ []) => //. cbn. rewrite -/(repeat _ _).
    specialize (IHa n). solve_all.
    len. rewrite repeat_app Nat.add_comm.
    eapply expanded_lift. 1-2:now len; rewrite !repeat_length.
    now depelim p. }
  constructor; auto.
  eapply (expanded_tRel _ _ _ _ []) => //. cbn.
  rewrite nth_error_app_lt. rewrite repeat_length. lia.
  rewrite nth_error_repeat //. lia.
  specialize (IHa (S n)).
  now rewrite Nat.add_succ_r.
Qed.

Lemma expanded_let_expansion {Σ} {Δ : context} {Γ t} :
  expanded_context Σ Γ Δ ->
  expanded_context Σ (repeat 0 #|Δ| ++ Γ) t ->
  expanded_context Σ (repeat 0 (context_assumptions Δ) ++ Γ) (expand_lets_ctx Δ t).
Proof.
  rewrite /expanded_context.
  intros [aΔ] [a]; sq.
  unfold expand_lets_ctx, expand_lets_k_ctx.
  do 2 eapply PCUICParallelReduction.All_fold_fold_context_k.
  eapply All_fold_impl; tea. cbn.
  intros Γ' x f. destruct (decl_body x) => //; constructor.
  len. depelim f.
  eapply expanded_subst. now rewrite repeat_length.
  clear -aΔ. eapply (expanded_extended_subst (sq aΔ) 0).
  len. rewrite app_assoc -repeat_app. eapply expanded_lift. len. now rewrite !repeat_length.
  now rewrite repeat_length. rewrite repeat_app -app_assoc //.
Qed.

Lemma expanded_context_subst {Σ} {Δ Δ' : list nat} {Γ s k t} :
  #|s| = #|Δ'| ->
  #|Δ| = k ->
  Forall (expanded Σ Γ) s ->
  expanded_context Σ (Δ ++ repeat 0 #|Δ'| ++ Γ) t ->
  expanded_context Σ (Δ ++ Γ) (subst_context s k t).
Proof.
  intros hs hs' has.
  rewrite /expanded_context.
  intros [aΔ]; sq.
  eapply PCUICParallelReduction.All_fold_fold_context_k.
  eapply All_fold_impl; tea. cbn.
  intros Γ' x f. destruct (decl_body x) => //; constructor.
  len. depelim f. rewrite app_assoc.
  eapply expanded_subst. len. rewrite repeat_length. lia. solve_all. auto.
  now rewrite -app_assoc hs.
Qed.

Lemma expanded_inds {Σ Γ ind u bodies} : Forall (expanded Σ Γ) (inds ind u bodies).
Proof.
  unfold inds. induction #|bodies|; cbn; auto. constructor => //. constructor.
Qed.

Implicit Types (cf : checker_flags).

Lemma expanded_weakening {cf} {Σ Σ' Γ t} :
  wf Σ' -> extends Σ Σ' -> expanded Σ Γ t -> expanded Σ' Γ t.
Proof.
  intros wfΣ ext.
  eapply expanded_ind; intros.
  all:try solve [econstructor; eauto].
  - econstructor; eauto. solve_all. sq. eapply All_fold_impl; tea; cbn.
    intros ? ? []; constructor; auto. now rewrite <- repeat_app.
  - eapply expanded_tFix; tea; eauto. solve_all.
  - eapply expanded_tConstruct_app; tea.
    eapply weakening_env_declared_constructor; tea.
Qed.

Lemma expanded_context_weakening {cf} {Σ Σ' Γ t} :
  wf Σ' -> extends Σ Σ' -> expanded_context Σ Γ t -> expanded_context Σ' Γ t.
Proof.
  intros wfΣ ext.
  intros [a]; sq.
  eapply All_fold_impl; tea; cbn; eauto.
  intros ?? []; constructor.
  eapply expanded_weakening; eauto.
Qed.

Lemma expanded_bcontext {cf} Σ ind k mdecl idecl cdecl bctx bbody :
  wf Σ ->
  PCUICEtaExpand.expanded_global_env Σ ->
  #|cstr_branch_context ind mdecl cdecl| = #|bctx| ->
  declared_constructor Σ (ind, k) mdecl idecl cdecl ->
  expanded_context Σ (repeat 0 (context_assumptions mdecl.(ind_params))) (bcontext (trans_branch ind mdecl cdecl bctx bbody)).
Proof.
  intros wfΣ expΣ hl declc.
  eapply expanded_context_map2_bias_left => //.
  destruct (declared_constructor_expanded expΣ declc) as [Σ' [ext [expm expc]]].
  destruct expm as [hp hb]. destruct expc as [hargs].
  unfold cstr_branch_context.
  epose proof (expanded_let_expansion hp (t:=(subst_context
  (inds (inductive_mind ind) (abstract_instance (ind_universes mdecl))
     (ind_bodies mdecl)) #|ind_params mdecl|
  (cstr_args cdecl)))).
  rewrite !app_nil_r in H. forward H.
  epose proof (expanded_context_subst (Γ := []) (Δ' := repeat 0 #|ind_bodies mdecl|)).
  rewrite !app_nil_r in H0. eapply H0; rewrite ?repeat_length //. len. apply expanded_inds.
  rewrite -repeat_app. exact hargs.
  destruct ext. eapply expanded_context_weakening; tea; tc.
Qed.

Lemma trans_expanded {cf : checker_flags} {Σ} {wfΣ :Template.Typing.wf Σ} Γ T  :
  let Σ' := trans_global_env Σ in
  WfAst.wf Σ T ->
  PCUICEtaExpand.expanded_global_env Σ' ->
  EtaExpand.expanded Σ Γ T ->
  expanded Σ' Γ (trans Σ' T).
Proof.
  intros Σ' wf expΣ' exp. revert wf.
  induction exp; intros wf; cbn -[Σ']; eauto using expanded.
  all: try now (wf_inv wf []; eauto using expanded).
  - wf_inv wf ?. eapply expanded_tRel with (args := []). eauto. lia. econstructor.
  - wf_inv wf [[[]]]. eapply expanded_tRel. eauto. len. solve_all.
  - wf_inv wf [[[]]]. econstructor. solve_all.
  - wf_inv wf []. cbn. eapply expanded_mkApps with (args := [_]); cbn; eauto using expanded. econstructor.
    eapply expanded_tRel with (args := []). reflexivity. lia. econstructor.
  - try now (wf_inv wf [[]]; eauto using expanded).
  - wf_inv wf [[[]]].
    forward IHexp; eauto.
    eapply expanded_mkApps; eauto. 2:solve_all.
    destruct f7; cbn in *; eauto.
    destruct TransLookup.lookup_inductive as [[] | ]; cbn; eauto.
  - wf_inv wf []. eapply forall_decls_declared_constructor in H; eauto. 2: now eapply template_to_pcuic_env.
    eapply expanded_tConstruct_app with (args := []).
    eauto. cbn. unfold trans_local. now rewrite context_assumptions_map. econstructor.
  - wf_inv wf (mdecl' & idecl' & []). eapply forall_decls_declared_inductive in d; eauto. 2: now eapply template_to_pcuic_env.
    unfold Σ'.
    erewrite trans_lookup_inductive, declared_inductive_lookup; eauto.
    econstructor; eauto. cbn.
    + solve_all.
    + cbn. eapply All2_nth_hyp in a1.
      eapply All_Forall, All2_All_map2, All2_map.
      eapply Forall_All in H2. eapply All2_All_mix_right in a1; tea.
      eapply All2_impl; tea. intros x y. cbv beta. intros [[i [Hi []]] ?].
      split.
      { rewrite length_map. relativize #|Ast.pparams type_info|.
        eapply expanded_bcontext => //.
        - now eapply template_to_pcuic_env.
        - len. eapply All2_length in a2. len in a2.
        - split; tea. cbn; rewrite nth_error_map. erewrite Hi => //.
        - cbn. tea. rewrite context_assumptions_map. now rewrite e0. }
      * cbn. rewrite map2_bias_left_length. now eapply e1.
    + eapply template_to_pcuic_env; eauto.
    + apply template_to_pcuic_env; eauto.
  - now (wf_inv wf [[]]; eauto using expanded).
  - wf_inv wf [[]]. wf_inv w ?. eapply expanded_tFix.
    + solve_all.
      * rewrite trans_isLambda //.
      * revert H2. cbn. now rewrite mapi_cst_map rev_map_spec map_map.
    + solve_all.
    + destruct args; cbn; congruence.
    + now rewrite nth_error_map H5.
    + now simpl_list.
  - wf_inv wf ?. econstructor. solve_all.
  - wf_inv wf [[[]]]. eapply forall_decls_declared_constructor in H; eauto. 2: now eapply template_to_pcuic_env.
    eapply expanded_tConstruct_app. eauto. cbn. unfold trans_local. now rewrite length_map context_assumptions_map. solve_all.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor.
  - wf_inv wf [[] ?]. repeat cbn; constructor. constructor; cbn; eauto. solve_all.
Qed.


Lemma wf_cons_inv {cf} Σ' (Σ : global_declarations) d :
  wf (set_declarations Σ' (d :: Σ)) -> wf (set_declarations Σ' Σ).
Proof.
  intros []. split => //. now depelim o0.
Qed.

Lemma template_wf_cons_inv {cf} univs retro (Σ : Ast.Env.global_declarations) d :
  Typing.wf {| Ast.Env.universes := univs; Ast.Env.declarations := d :: Σ;
    Ast.Env.retroknowledge := retro |} ->
  let Σ' := {| Ast.Env.universes := univs; Ast.Env.declarations := Σ;
    Ast.Env.retroknowledge := retro |} in
  Typing.wf Σ' × Typing.on_global_decl Typing.cumul_gen (WfAst.wf_decl_pred) (Σ', Ast.universes_decl_of_decl d.2) d.1 d.2
  × ST.on_udecl univs (Ast.universes_decl_of_decl d.2).
Proof.
  intros wf; split.
  destruct wf. split => //. now depelim o0.
  eapply typing_wf_wf in wf. depelim wf.
  cbn in o0. depelim o0. cbn. destruct o1. split => //.
Qed.

Lemma trans_global_env_cons univs retro (Σ : Ast.Env.global_declarations) decl :
  trans_global_env {| S.Env.universes := univs; S.Env.declarations := decl :: Σ; S.Env.retroknowledge := retro |} =
  let Σ' := trans_global_env {| S.Env.universes := univs; S.Env.declarations := Σ; S.Env.retroknowledge := retro |} in
  add_global_decl Σ' (decl.1, trans_global_decl Σ' decl.2).
Proof. reflexivity. Qed.

Arguments trans_global_env : simpl never.

Lemma All_fold_map (P : context -> context_decl -> Type) (f : Ast.Env.context_decl -> context_decl) ctx :
  All_fold P (map f ctx) <~> All_fold (fun Γ d => P (map f Γ) (f d)) ctx.
Proof.
  induction ctx.
  - split; constructor.
  - cbn. split; intros H; depelim H; constructor; auto; now apply IHctx.
Qed.

Lemma All_fold_All_mix_left (P : S.Env.context -> S.Env.context_decl -> Type) (Q : S.Env.context_decl -> Type) ctx :
  All_fold P ctx ->
  All Q ctx ->
  All_fold (fun Γ d => Q d × P Γ d) ctx.
Proof.
  induction 1; cbn; intros. constructor.
  depelim X0. constructor; auto.
Qed.

Lemma expanded_trans_local {cf} {Σ} {wfΣ : Typing.wf Σ} Γ ctx :
  expanded_global_env (trans_global_env Σ) ->
  All (WfAst.wf_decl Σ) ctx ->
  EtaExpand.expanded_context Σ Γ ctx ->
  expanded_context (trans_global_env Σ) Γ (trans_local (trans_global_env Σ) ctx).
Proof.
  rewrite /expanded_context.
  intros etaΣ wfctx [a]; split.
  unfold trans_local.
  eapply All_fold_map.
  eapply All_fold_All_mix_left in a; tea.
  eapply All_fold_impl; tea; cbv beta; intros ??; cbn; unfold WfAst.wf_decl;
    intros [wf Hd]; revert Hd wf; intros []; intros [];  constructor; len.
  eapply trans_expanded in H; auto.
Qed.

Lemma wf_context_sorts {cf} {Σ ctx ctx' cunivs} {wfΣ : Typing.wf_ext Σ} :
  Typing.sorts_local_ctx WfAst.wf_decl_pred Σ ctx ctx' cunivs ->
  All (WfAst.wf_decl Σ) ctx'.
Proof.
  induction ctx' in cunivs |- *; cbn; auto.
  destruct a as [na [b|] ty].
  intros [? ?]. constructor; auto. eauto.
  destruct cunivs => //.
  intros [? ?]. constructor; auto. eauto.
Qed.

Lemma expanded_trans_global_env {cf} Σ {wfΣ : Typing.wf_ext Σ} :
  EtaExpand.expanded_global_env Σ ->
  expanded_global_env (trans_global_env Σ).
Proof.
  destruct Σ as [[univs Σ] udecl].
  cbn -[trans_global_env]. unfold EtaExpand.expanded_global_env; cbn -[trans_global_env].
  intros etaenv; induction etaenv.
  - constructor; auto.
  - destruct wfΣ as [wfΣ onudecl].
    eapply template_wf_cons_inv in wfΣ as [].
    forward IHetaenv by tea. split => //.
    rewrite trans_global_env_cons. set (Σ' := trans_global_env _ ).
    cbv zeta. constructor. apply IHetaenv.
    cbn -[add_global_decl trans_global_env].
    destruct decl as [kn []]; cbn in *; depelim H => //.
    * unfold trans_constant_body; cbn.
      constructor. cbn. destruct p.
      red in o.
      destruct (Ast.Env.cst_body c); cbn => //. cbn in expanded_body.
      eapply trans_expanded in expanded_body; eauto.
      rewrite -/Σ' in expanded_body. now rewrite -eta_global_env.
      red in o. now destruct o.
    * rewrite -eta_global_env.
      constructor.
      + cbn. eapply expanded_trans_local in expanded_params => //.
        destruct p; destruct o. now eapply TypingWf.All_local_env_wf_decls.
      + cbn. destruct p.
        move: o.(Typing.onInductives). destruct o. intros oni.
        eapply All_Forall. eapply Forall_All in expanded_ind_bodies.
        eapply Alli_All_mix in oni; tea. clear expanded_ind_bodies.
        eapply All_map, Alli_All; tea; cbv beta.
        intros n oib []. move: (Typing.onConstructors o).
        intros onc. red in onc.
        destruct e as [expc]. constructor. eapply Forall_All in expc.
        eapply All2_All_mix_left in onc; tea. clear expc. solve_all.
        cbn. solve_all.
        destruct a as [expargs expty]. constructor.
        { cbn. eapply expanded_trans_local in expargs; eauto.
          move: expargs. len.
          move: b.(Typing.on_cargs) => onargs.
          eapply @wf_context_sorts in onargs; tea.
          cbn. split => /= //. exact w. }
Qed.

Import TemplateProgram.

Lemma expanded_trans_program {cf : checker_flags} p (t : wt_template_program p) :
  EtaExpand.expanded_program p ->
  expanded_pcuic_program (trans_template_program p).
Proof.
  intros [etaenv etat].
  destruct t as [? [T HT]]. split.
  unshelve eapply expanded_trans_global_env => //; tc.
  unshelve eapply trans_expanded => //; tc. eapply w.
  now unshelve eapply TypingWf.typing_wf in HT.
  eapply expanded_trans_global_env => //.
Qed.
