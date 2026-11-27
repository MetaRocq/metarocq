(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst Transform.
From MetaRocq.Erasure Require EAst EAstUtils EGlobalEnv EWcbvEval EWellformed
  EConstructorsAsBlocks ERemoveParams EFirstorder EReorderCstrs EPrimitive
  EInduction EOptimizePropDiscr.
From MetaRocq.Erasure Require Import EEnvMap.
From MetaRocq.Erasure.Typed Require ExAst Optimize OptimizeCorrectness
  DeargFirstorder.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure
  ErasureCorrectness Readback.
From MetaRocq.ErasurePlugin.transforms Require Import GuardedToUnguardedFix
  RemoveParams ConstructorsAsBlocks ReorderCstrs RebuildWfEnv.
Import MetaRocq.Common.Transform.Transform.

#[local] Existing Instance config.extraction_checker_flags.

(** * Correctness of the typed erasure pipeline on first-order values

  The typed pipeline ([verified_typed_erasure_pipeline]) erases to typed
  λ□, removes the cases on propositions and removes the dead arguments of
  constants and constructors (dearging), before the verified λ□ passes.
  The masks of dearging remove nothing from the constructors of first-order
  inductive types ([MetaRocq.Erasure.Typed.DeargFirstorder]): the
  first-order theorem of the untyped pipeline holds for the typed one. *)

(** ** Constructor reordering with the empty mapping is the identity *)

Lemma reorder_nil t : EReorderCstrs.reorder [] t = t.
Proof.
  induction t using EInduction.term_forall_list_ind; simp reorder; cbn;
    f_equal => //.
  all: try solve [ELiftSubst.solve_all].
Qed.

Lemma reorder_env_nil Σ : EReorderCstrs.reorder_env [] Σ = Σ.
Proof.
  induction Σ as [|[kn []] Σ IH]; cbn => //; f_equal => //.
  - rewrite /EReorderCstrs.reorder_decl /=. destruct c as [[b|]] => //=.
    rewrite /EReorderCstrs.reorder_constant_decl /=. now rewrite reorder_nil.
  - rewrite /EReorderCstrs.reorder_decl /=. destruct m as [fin np bodies].
    rewrite /EReorderCstrs.reorder_inductive_decl
      /EReorderCstrs.reorder_one_ind /=.
    now rewrite mapi_cst_map map_id.
Qed.

(** ** The λ□ part of the typed pipeline on first-order values *)

Lemma tail_readback econf v :
  ETransform.readback (verified_lambdabox_etransform_tail econf) v =
  blocks_readback v.
Proof.
  cbn. repeat (unfold ETransform.compose_readback; cbn).
  destruct (Erasure.inlining econf); cbn;
    destruct blocks_readback; reflexivity.
Qed.

(** [ERemoveParams.strip] only looks at the declarations of the
    environment. *)
Lemma strip_fo_decls (Σ Σ' : GlobalContextMap.t) w :
  GlobalContextMap.global_decls Σ = GlobalContextMap.global_decls Σ' ->
  EFirstorder.firstorder_evalue Σ w ->
  ERemoveParams.strip Σ w = ERemoveParams.strip Σ' w.
Proof.
  intros he. move: w. apply: EFirstorder.firstorder_evalue_elim; intros.
  rewrite !ERemoveParams.strip_mkApps //= -he.
  have hl := lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ H.
  rewrite hl. f_equal. rewrite !skipn_map. apply map_ext_Forall. exact H1.
Qed.

Lemma obseq_tail_compile econf (P : EProgram.eprogram_env) prQ p' w v' :
  obseq (ETransform.tr (verified_lambdabox_etransform_tail econf))
    (ERemoveParams.strip_program P) prQ p' (ERemoveParams.strip P.1 w) v' ->
  EFirstorder.firstorder_evalue P.1 w ->
  ∥ EFirstorder.firstorder_ind_value P.1
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip P.1 w) []) ∥ ->
  v' = EConstructorsAsBlocks.compile_evalue_box
    (ERemoveParams.strip P.1 w) [].
Proof.
  destruct P as [Σ t]. cbn [fst snd]. intros obs fo foi.
  pose proof prQ as [[wfs _] _].
  set (E := verified_lambdabox_etransform_tail econf) in *.
  have foq : fo_evalue (ERemoveParams.strip_program (Σ, w)).
  { split; [now apply strip_firstorder|].
    eapply EFirstorder.firstorder_ind_value_is_coind; [|exact foi].
    intros kn. apply ERemoveParams.is_coind_strip. }
  have hrb := ETransform.readback_obseq E
    (ERemoveParams.strip_program (Σ, t)) _ p' (ERemoveParams.strip Σ w) v'
    foq obs.
  apply (ETransform.readback_inj E _ _ (ERemoveParams.strip Σ w)) => //.
  rewrite tail_readback.
  apply (blocks_readback_compile
    (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags)
    (EEnvMap.GlobalContextMap.make (ERemoveParams.strip_env Σ)
      (EProgram.wf_glob_fresh _ wfs))) => //.
  now apply strip_firstorder.
Qed.

(** With the empty mapping of inductive types, the λ□ part of the typed
    pipeline compiles first-order values exactly. *)
Lemma obseq_typed_lambdabox_compile econf
  (p : EProgram.inductives_mapping × EProgram.eprogram_env) pr p' w v' :
  p.1 = [] ->
  obseq (verified_lambdabox_typed_pipeline econf) p pr p' w v' ->
  EFirstorder.firstorder_evalue p.2.1 w ->
  ∥ EFirstorder.firstorder_ind_value p.2.1
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip p.2.1 w) []) ∥ ->
  v' = EConstructorsAsBlocks.compile_evalue_box
    (ERemoveParams.strip p.2.1 w) [].
Proof.
  destruct p as [m [Σ t]]. cbn [fst snd]. intros -> obs fo foi.
  move: obs. unfold verified_lambdabox_typed_pipeline.
  cbn [obseq compose reorder_cstrs_transformation rebuild_wf_env_transform
    guarded_to_unguarded_fix remove_params_optimization].
  intros [v4 [[v3 [[v2 [[v1 [e1 e2]] e3]] e4]] obs]].
  cbn [fst] in e1. rewrite reorder_nil in e1. subst v1 v2 v3.
  unfold run, time in e4, obs.
  match type of e4 with _ = ERemoveParams.strip (?P).1 _ =>
    set (P3 := P) in * end.
  have hS : GlobalContextMap.global_decls P3.1 =
    GlobalContextMap.global_decls Σ.
  { rewrite /P3.
    do 4 (unfold run, time; cbn [transform compose
      reorder_cstrs_transformation rebuild_wf_env_transform
      guarded_to_unguarded_fix fst snd GlobalContextMap.global_decls
      GlobalContextMap.make EReorderCstrs.reorder_program to_program]).
    apply reorder_env_nil. }
  subst v4.
  have es := strip_fo_decls Σ P3.1 w (eq_sym hS) fo.
  have fo3 : EFirstorder.firstorder_evalue P3.1 w
    by rewrite /EGlobalEnv.lookup_env hS.
  have foi3 : ∥ EFirstorder.firstorder_ind_value P3.1
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip P3.1 w) []) ∥.
  { rewrite -es.
    eapply EFirstorder.firstorder_ind_value_is_coind; [|exact foi].
    intros kn. rewrite /EGlobalEnv.is_coind /EGlobalEnv.lookup_inductive_kind
      /EGlobalEnv.lookup_minductive. now rewrite hS. }
  rewrite es. exact (obseq_tail_compile econf P3 _ p' w v' obs fo3 foi3).
Qed.

(** ** The constructors of first-order values *)

(** The constructors of a compiled value belong to inductive types
    satisfying [P]. *)
Inductive fo_block_in (P : kername -> Prop) : EAst.term -> Prop :=
| fo_block_in_C i n args : P (inductive_mind i) ->
  Forall (fo_block_in P) args -> fo_block_in P (EAst.tConstruct i n args).

(** [kn] is a first-order inductive type of [Σ]. *)
Definition fo_ind_kn (Σ : PCUICAst.PCUICEnvironment.global_env) kn :=
  exists m, PCUICAst.PCUICEnvironment.lookup_env Σ kn =
    Some (PCUICAst.PCUICEnvironment.InductiveDecl m) /\
    @PCUICFirstorder.firstorder_mutind
      (PCUICFirstorder.firstorder_env'
        (PCUICAst.PCUICEnvironment.declarations Σ)) m.

(** The constructors of a value of a first-order inductive type belong to
    first-order inductive types. *)
Lemma firstorder_value_fo_block
  (Σ : PCUICAst.PCUICEnvironment.global_env_ext)
  {wfΣ : PCUICTyping.wf Σ.1} v :
  PCUICFirstorder.firstorder_value Σ [] v ->
  forall i u args,
  PCUICTyping.typing Σ [] v (PCUICAst.mkApps (PCUICAst.tInd i u) args) ->
  PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i ->
  fo_block_in (fo_ind_kn Σ.1) (compile_value_box Σ.1 v []).
Proof.
  intros fo. move: v fo.
  apply: PCUICFirstorder.firstorder_value_inds.
  intros i n ui u args pandi hty hargs IH nprop i' u' args' Hty Hfo.
  apply PCUICValidity.inversion_mkApps in Hty as Hcon; auto.
  destruct Hcon as (?&typ_ctor& spine).
  apply PCUICInversion.inversion_Construct in typ_ctor
    as (?&?&?&?&?&?&?); auto.
  eapply @PCUICInductiveInversion.Construct_Ind_ind_eq
    with (mdecl := x0) in Hty as Hty'; eauto.
  destruct Hty' as (([[[]]] & ?)  & ? & ? & ? & ? & _). subst.
  eapply PCUICSpine.typing_spine_strengthen in spine. 3: eauto.
  2: eapply PCUICInductiveInversion.declared_constructor_valid_ty; eauto.
  eapply PCUICFirstorder.firstorder_args in spine; eauto.
  have hnp := pcuic_lookup_inductive_pars_declared Σ i' n x0 x1 x2 wfΣ d.
  rewrite (compile_value_box_mkApps hnp) app_nil_r.
  constructor.
  - move: Hfo. rewrite /PCUICFirstorder.firstorder_ind.
    pose proof d as [[hm _] _].
    unshelve eapply PCUICTyping.declared_minductive_to_gen in hm.
    3:exact wfΣ.
    rewrite /PCUICAst.declared_minductive_gen in hm. rewrite hm.
    intros h. now exists x0.
  - apply Forall_skipn. apply Forall_map. clear -IH spine.
    induction spine; [constructor|].
    inv IH. constructor; [|now apply IHspine].
    eapply H; tea.
Qed.

Lemma fo_evalue_in_of_block (P : kername -> Prop) (Σer : GlobalContextMap.t)
  w :
  EFirstorder.firstorder_evalue Σer w ->
  fo_block_in P (ERemoveParams.compile_evalue_box_strip Σer w []) ->
  DeargFirstorder.fo_evalue_in P (GlobalContextMap.global_decls Σer) w.
Proof.
  move: w. apply: EFirstorder.firstorder_evalue_elim.
  intros i n args npars nargs hl _ IH hlen hb.
  have hp := lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ hl.
  rewrite (ERemoveParams.compile_evalue_box_strip_mkApps (npars := npars))
    in hb.
  { now rewrite GlobalContextMap.lookup_inductive_pars_spec. }
  rewrite app_nil_r in hb. depelim hb.
  econstructor; tea.
  rewrite skipn_map in H0. apply Forall_map_inv in H0.
  eapply Forall_impl; [eapply Forall_and; [exact IH|exact H0]|].
  intros x [hx hx']. now apply hx.
Qed.

(** ** The inductive types of the typed erased environment *)

Lemma map_map_In {A B C} (l : list A) (g : forall x, In x l -> B)
  (f : B -> C) (h : A -> C) :
  (forall x hx, f (g x hx) = h x) -> map f (map_In l g) = map h l.
Proof.
  funelim (map_In l g); cbn => //. intros hf. f_equal; [apply hf|].
  apply H. intros; apply hf.
Qed.

(** Typed and untyped erasure agree on inductive types. *)
Lemma trans_mib_erase_ind {X_type : PCUICWfEnv.abstract_env_impl}
  {X : X_type.π2.π1} {no ni} rΣ wfrΣ kn mib wt :
  ExAst.trans_mib (@Erasure.erase_ind X_type X no ni rΣ wfrΣ kn mib wt) =
  ErasureFunction.erase_mutual_inductive_body mib.
Proof.
  rewrite /ExAst.trans_mib /ErasureFunction.erase_mutual_inductive_body.
  cbn [ExAst.ind_finite ExAst.ind_npars ExAst.ind_bodies Erasure.erase_ind].
  f_equal. apply map_map_In => oib hin.
  rewrite /ExAst.trans_oib /ErasureFunction.erase_one_inductive_body.
  rewrite /Erasure.erase_ind_body.
  cbn [ExAst.ind_name ExAst.ind_kelim ExAst.ind_propositional
    ExAst.ind_ctors ExAst.ind_projs].
  f_equal.
  - rewrite /ExAst.trans_ctors. apply map_map_In => c hc.
    cbv beta zeta. destruct ExAst.decompose_arr. reflexivity.
  - apply map_map_In => p hp. reflexivity.
Qed.

Lemma ExAst_lookup_env_In (Σ : ExAst.global_env) kn d :
  ExAst.lookup_env Σ kn = Some d -> exists b, In (kn, b, d) Σ.
Proof.
  rewrite /ExAst.lookup_env.
  destruct find as [[[kn' b] d']|] eqn:hf => //= [[<-]].
  apply find_some in hf as [hin heq]. cbn in heq.
  apply eqb_eq in heq. subst. now exists b.
Qed.

Lemma typed_erase_preserves_inductives
  {X_type : PCUICWfEnv.abstract_env_impl}
  {X : X_type.π1} (Σp : PCUICAst.PCUICEnvironment.global_env) univs retro
  prop incl ign :
  EnvMap.EnvMap.fresh_globals (PCUICAst.PCUICEnvironment.declarations Σp) ->
  erase_preserves_inductives Σp
    (ExAst.trans_env (@Erasure.erase_global_decls_deps_recursive X_type X
      (PCUICAst.PCUICEnvironment.declarations Σp) univs retro prop incl
      ign)).
Proof.
  intros fr kn d d' hl hl'.
  rewrite OptimizeCorrectness.lookup_env_trans_env in hl.
  destruct ExAst.lookup_env as [[|m|]|] eqn:he; noconf hl.
  apply ExAst_lookup_env_In in he as [b hin].
  destruct (DeargFirstorder.erase_global_decls_deps_recursive_ind _ _ _ _ _
    _ _ _ _ hin)
    as [prefix [tail [mib [hdecls [X' [no' [ni' [wfr [wt ->]]]]]]]]].
  rewrite trans_mib_erase_ind.
  move: hl'. rewrite /PCUICAst.PCUICEnvironment.lookup_env.
  rewrite (DeargFirstorder.fresh_lookup_global_In _ kn
    (PCUICAst.PCUICEnvironment.InductiveDecl mib) fr).
  { rewrite hdecls. apply in_or_app. right. now left. }
  now intros [= ->].
Qed.

(** ** Environments with the same inductive types *)

Definition same_inds (Σ1 Σ2 : EAst.global_declarations) :=
  forall kn, EGlobalEnv.lookup_minductive Σ1 kn =
    EGlobalEnv.lookup_minductive Σ2 kn.

Lemma same_inds_lookup_constructor_pars_args Σ1 Σ2 i n :
  same_inds Σ1 Σ2 ->
  EGlobalEnv.lookup_constructor_pars_args Σ1 i n =
  EGlobalEnv.lookup_constructor_pars_args Σ2 i n.
Proof.
  intros h. rewrite /EGlobalEnv.lookup_constructor_pars_args
    /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive.
  now rewrite h.
Qed.

Lemma same_inds_firstorder_evalue Σ1 Σ2 w :
  same_inds Σ1 Σ2 -> EFirstorder.firstorder_evalue Σ1 w ->
  EFirstorder.firstorder_evalue Σ2 w.
Proof.
  intros h. move: w. apply: EFirstorder.firstorder_evalue_elim; intros.
  econstructor; tea.
  now rewrite -(same_inds_lookup_constructor_pars_args _ _ _ _ h).
Qed.

Lemma same_inds_fo_evalue_in P Σ1 Σ2 w :
  same_inds Σ1 Σ2 -> DeargFirstorder.fo_evalue_in P Σ1 w ->
  DeargFirstorder.fo_evalue_in P Σ2 w.
Proof.
  intros h. move: w. apply: DeargFirstorder.fo_evalue_in_elim; intros.
  econstructor; tea.
  now rewrite -(same_inds_lookup_constructor_pars_args _ _ _ _ h).
Qed.

Lemma same_inds_cstrip Σ1 Σ2 w acc :
  same_inds Σ1 Σ2 ->
  DeargFirstorder.cstrip Σ1 w acc = DeargFirstorder.cstrip Σ2 w acc.
Proof.
  intros h. induction w in acc |- *; cbn => //.
  - now rewrite IHw2 IHw1.
  - rewrite /EGlobalEnv.lookup_inductive_pars. now rewrite h.
Qed.

Lemma same_inds_is_coind Σ1 Σ2 kn :
  same_inds Σ1 Σ2 -> EGlobalEnv.is_coind Σ1 kn = EGlobalEnv.is_coind Σ2 kn.
Proof.
  intros h. rewrite /EGlobalEnv.is_coind /EGlobalEnv.lookup_inductive_kind.
  now rewrite h.
Qed.

Lemma same_inds_remove_match_on_box_typed m Σ :
  same_inds (ExAst.trans_env (remove_match_on_box_typed_env m Σ))
    (ExAst.trans_env Σ).
Proof.
  intros kn.
  rewrite /EGlobalEnv.lookup_minductive
    !OptimizeCorrectness.lookup_env_trans_env.
  rewrite /remove_match_on_box_typed_env /ExAst.lookup_env.
  induction Σ as [|[[kn' b] d] Σ IH]; cbn => //.
  destruct (kn == kn'); cbn; [destruct d => //|exact IH].
Qed.

(** Maps commuting with constructor applications change first-order values
    only in their parameters. *)
Lemma fo_map_cstrip (f : EAst.term -> EAst.term) Σ' P w :
  (forall i n args, f (EAst.mkApps (EAst.tConstruct i n []) args) =
    EAst.mkApps (EAst.tConstruct i n []) (map f args)) ->
  DeargFirstorder.fo_evalue_in P Σ' w ->
  DeargFirstorder.fo_evalue_in P Σ' (f w) /\
  DeargFirstorder.cstrip Σ' (f w) [] = DeargFirstorder.cstrip Σ' w [].
Proof.
  intros hf. move: w. apply: DeargFirstorder.fo_evalue_in_elim.
  intros i n args npars nargs hl hp _ IH hlen.
  rewrite hf.
  have hpars :=
    lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ hl.
  split.
  - econstructor; tea; [|now len].
    rewrite -map_skipn. apply Forall_map. eapply Forall_impl; tea.
    now intros x [].
  - rewrite !(DeargFirstorder.cstrip_mkApps _ _ _ _ _ _ _ hpars) !app_nil_r.
    f_equal. rewrite map_map -!map_skipn. apply map_ext_Forall.
    eapply Forall_impl; tea. now intros x [].
Qed.

Lemma remove_match_on_box_construct (Σ : GlobalContextMap.t) i n args :
  EOptimizePropDiscr.remove_match_on_box Σ
    (EAst.mkApps (EAst.tConstruct i n []) args) =
  EAst.mkApps (EAst.tConstruct i n [])
    (map (EOptimizePropDiscr.remove_match_on_box Σ) args).
Proof.
  rewrite EOptimizePropDiscr.remove_match_on_box_mkApps.
  now simp remove_match_on_box.
Qed.

(** ** Dearging *)

(** The masks of the dearging checks remove nothing from the constructors
    of the inductive types satisfying [P], if their initial masks do not. *)
Lemma check_dearging_precond_ok (P : kername -> Prop) cf Σ t masks :
  check_dearging_precond cf Σ t = Some masks ->
  (forall kn b mibx, In (kn, b, ExAst.InductiveDecl mibx) Σ -> P kn ->
    DeargFirstorder.mm_ok (DeargFirstorder.init_mib_masks mibx)) ->
  forall kn mm,
    Optimize.get_mib_masks (Optimize.ind_masks masks) kn = Some mm ->
    P kn -> DeargFirstorder.mm_ok mm.
Proof.
  intros hc hinit kn mm hmm hp.
  move: hc. rewrite /check_dearging_precond.
  destruct EGlobalEnv.closed_env => //.
  rewrite /ExtractionCorrectness.compute_program_masks /Utils.timed.
  destruct Optimize.analyze_program as [cms ims] eqn:ha. cbn.
  have hok :=
    DeargFirstorder.analyze_program_ok P (overridden_masks cf) Σ t hinit.
  rewrite ha /= in hok.
  have hok' : DeargFirstorder.inds_ok P
    ((if do_trim_ctor_masks cf then Optimize.trim_ind_masks else id) ims).
  { destruct do_trim_ctor_masks => //.
    now apply DeargFirstorder.trim_ind_masks_ok. }
  destruct Optimize.is_expanded_env; cbn => //.
  destruct Optimize.valid_masks_env; cbn => //.
  destruct (_ && _) => // [= he]. subst masks. cbn in hmm.
  exact (hok' _ _ (DeargFirstorder.get_mib_masks_In _ _ _ hmm) hp).
Qed.

(** Dearging keeps first-order values, up to their parameters. *)
Lemma dearg_stage cf (Σ : ExAst.global_env) t w (P : kername -> Prop) :
  (forall kn b mibx, In (kn, b, ExAst.InductiveDecl mibx) Σ -> P kn ->
    DeargFirstorder.mm_ok (DeargFirstorder.init_mib_masks mibx)) ->
  DeargFirstorder.fo_evalue_in P (ExAst.trans_env Σ) w ->
  let mo := check_dearging_precond cf Σ t in
  let Σd := (dearg ((mo, Σ), t)).1 in
  let wd := (dearg ((mo, Σ), w)).2 in
  [/\ DeargFirstorder.fo_evalue_in P Σd wd,
    DeargFirstorder.cstrip Σd wd [] =
      DeargFirstorder.cstrip (ExAst.trans_env Σ) w [] &
    forall kn, EGlobalEnv.is_coind Σd kn =
      EGlobalEnv.is_coind (ExAst.trans_env Σ) kn].
Proof.
  intros hinit fo. cbn zeta. rewrite /dearg /=.
  destruct check_dearging_precond as [masks|] eqn:hc; cbn => //.
  have [_ [hv _]] := check_dearging_precond_spec cf Σ t masks hc.
  have hok := check_dearging_precond_ok P cf Σ t masks hc hinit.
  rewrite /OptimizeCorrectness.dearg_env /OptimizeCorrectness.dearg_term
    -OptimizeCorrectness.trans_env_debox.
  destruct (DeargFirstorder.dearg_fo_evalue _ _ P hok Σ w hv fo) as [h1 h2].
  split => //. intros kn.
  apply OptimizeCorrectness.is_coind_trans_env_dearg_env.
Qed.

(** The constructors of the let-expanded value of a program of a first-order
    inductive type belong to first-order inductive types of the let-expanded
    environment. *)
Lemma expand_lets_fo_block (Σ : PCUICAst.PCUICEnvironment.global_env_ext)
  t v i u args :
  PCUICTyping.wf_ext Σ ->
  PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args) ->
  PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i ->
  PCUICWcbvEval.eval Σ.1 t v ->
  fo_block_in (fo_ind_kn (PCUICExpandLets.trans_global_env Σ.1))
    (compile_value_box (PCUICExpandLets.trans_global_env Σ.1)
      (PCUICExpandLets.trans v) []).
Proof.
  intros wf ty fo ev.
  have tyv : PCUICTyping.typing Σ [] v
    (PCUICAst.mkApps (PCUICAst.tInd i u) args).
  { eapply PCUICClassification.subject_reduction_eval; eauto. }
  have hv : PCUICFirstorder.firstorder_value Σ [] v.
  { eapply PCUICFirstorder.firstorder_value_spec; tea. apply wf.
    constructor. eapply PCUICWcbvEval.eval_to_value; tea. }
  have eqtr : PCUICExpandLets.trans v = v.
  { clear -hv. move: v hv. eapply PCUICFirstorder.firstorder_value_inds.
    intros. rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
    f_equal. ELiftSubst.solve_all. }
  have hv' : PCUICFirstorder.firstorder_value
    (PCUICExpandLets.trans_global_env Σ.1, Σ.2) [] v.
  { eapply PCUICExpandLetsCorrectness.expand_lets_preserves_fo in hv; eauto.
    now rewrite eqtr in hv. }
  have hty : PCUICTyping.typing (PCUICExpandLets.trans_global_env Σ.1, Σ.2)
    [] v
    (PCUICAst.mkApps (PCUICAst.tInd i u) (map PCUICExpandLets.trans args)).
  { rewrite -eqtr. eapply PCUICExpandLetsCorrectness.expand_lets_sound in tyv.
    now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in tyv. }
  have hfo : PCUICFirstorder.firstorder_ind
    (PCUICExpandLets.trans_global_env Σ.1, Σ.2)
    (PCUICFirstorder.firstorder_env
      (PCUICExpandLets.trans_global_env Σ.1, Σ.2)) i.
  { move: fo. rewrite /PCUICFirstorder.firstorder_ind /=
      PCUICExpandLetsCorrectness.trans_lookup /=.
    destruct PCUICAst.PCUICEnvironment.lookup_env => //. destruct g => //=.
    eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind.
    eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
  have wf' : PCUICTyping.wf (PCUICExpandLets.trans_global_env Σ.1).
  { exact (@PCUICExpandLetsCorrectness.trans_wf extraction_checker_flags Σ
      wf.1). }
  rewrite eqtr.
  exact (firstorder_value_fo_block (PCUICExpandLets.trans_global_env Σ.1, Σ.2)
    (wfΣ := wf') v hv' _ _ _ hty hfo).
Qed.

(** ** The typed pipeline theorem *)

#[local] Existing Instance PCUICSN.extraction_normalizing.

Section TypedPipelineTheorem.
  Import PCUICProgram.

  Context {guard : PCUICWfEnvImpl.abstract_guard_impl}.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.
  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.
  Variable v : PCUICAst.term.
  Variable i : inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.
  Variable Normalisation :
    (forall Σ, PCUICTyping.wf_ext Σ -> PCUICSN.NormalizationIn Σ).
  Variable typing :
    ∥ PCUICTyping.typing Σ [] t
        (PCUICAst.mkApps (PCUICAst.tInd i u) args) ∥.
  Variable fo :
    PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.
  Variable Heval : ∥ PCUICWcbvEval.eval Σ t v ∥.
  Variable econf : erasure_configuration.

  Lemma precond_typed :
    pre (verified_typed_erasure_pipeline econf) ([], (Σ, t)).
  Proof.
    hnf. destruct typing. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. eauto.
    - intros. red. intros. now eapply Normalisation.
  Qed.

  Let Σ_t := (transform (verified_typed_erasure_pipeline econf) ([], (Σ, t))
    precond_typed).1.
  Let t_t := (transform (verified_typed_erasure_pipeline econf) ([], (Σ, t))
    precond_typed).2.
  Let v_t := compile_value_box (PCUICExpandLets.trans_global_env Σ) v [].

  (** The typed pipeline compiles the program to a program evaluating to the
      compilation of [v]. *)
  Theorem verified_typed_erasure_pipeline_theorem :
    ∥ EWcbvEval.eval (wfl := EWcbvEvalNamed.extraction_wcbv_flags)
        Σ_t t_t v_t ∥.
  Proof.
    subst Σ_t t_t. generalize precond_typed.
    unfold verified_typed_erasure_pipeline. cbv zeta.
    intros pr. destruct_compose. intros pr1.
    move: pr1. destruct_compose. intros pr2 pr1.
    move: pr1; move: pr2. destruct_compose. intros pr3 pr2 pr1.
    move: pr1; move: pr2; move: pr3. destruct_compose.
    intros pr4 pr3 pr2 pr1.
    move: pr1; move: pr2; move: pr3; move: pr4. destruct_compose.
    intros pr5 pr4 pr3 pr2 pr1.
    move: pr1; move: pr2; move: pr3; move: pr4; move: pr5. destruct_compose.
    intros pr6 pr5 pr4 pr3 pr2 pr1.
    match type of pr6 with pre _ ?P => set (p1 := P) in * end.
    match type of pr5 with pre _ ?P => set (p2 := P) in * end.
    match type of pr4 with pre _ ?P => set (p3 := P) in * end.
    match type of pr3 with pre _ ?P => set (p4 := P) in * end.
    match type of pr2 with pre _ ?P => set (p5 := P) in * end.
    match type of pr1 with pre _ ?P => set (p6 := P) in * end.
    match goal with p1 := transform ?T _ _ |- _ =>
      have [v1 [ev1 e1]] := preservation T _ v pr Heval end.
    have [v2 [ev2 e2]] := preservation _ _ v1 pr6 ev1.
    have [v3 [ev3 e3]] := preservation _ _ v2 pr5 ev2.
    have [v4 [ev4 e4]] := preservation _ _ v3 pr4 ev3.
    have [v5 [ev5 e5]] := preservation _ _ v4 pr3 ev4.
    have [v6 [ev6 e6]] := preservation _ _ v5 pr2 ev5.
    have [v7 [ev7 e7]] := preservation _ _ v6 pr1 ev6.
    cbn [obseq pcuic_expand_lets_transform_mapping
      PCUICTransform.pcuic_expand_lets_transform
      typed_erase_transform_mapping typed_erase_transform
      remove_match_on_box_typed_transform_mapping
      remove_match_on_box_typed_transform dearging_checks_transform_mapping
      dearging_checks_transform dearging_transform_mapping dearging_transform
      rebuild_wf_env_transform_mapping rebuild_wf_env_transform]
      in e1, e2, e3, e4, e5, e6.
    subst v4 v6.
    (* The typed erasure *)
    have hpost2 := correctness _ _ pr6.
    pose proof pr6 as [_ [[[wfp _]] _]].
    have hΣex : exists X_type X univs retro prop incl ign,
      p2.2.1 = @Erasure.erase_global_decls_deps_recursive X_type X
        (PCUICAst.PCUICEnvironment.declarations p1.2.1) univs retro prop incl
        ign.
    { rewrite /p2. cbn [transform typed_erase_transform_mapping
        typed_erase_transform snd fst].
      rewrite /erase_program_typed. do 7 eexists. reflexivity. }
    have fr := PCUICWfEnvImpl.wf_fresh_globals _ wfp.1.
    have hpres : erase_preserves_inductives p1.2.1 (ExAst.trans_env p2.2.1).
    { destruct hΣex as [X_type [X [univs [retro [prop [incl [ign ->]]]]]]].
      now apply typed_erase_preserves_inductives. }
    destruct hpost2 as [_ [[wfg wft] _]].
    destruct ev2 as [ev2].
    have hww := EWcbvEval.eval_wellformed (efl := EWellformed.all_env_flags)
      _ eq_refl wfg _ v2 wft ev2.
    set (Σer := GlobalContextMap.make (ExAst.trans_env p2.2.1)
      (EProgram.wf_glob_fresh _ wfg)).
    destruct typing as [ty]. destruct Heval as [hev].
    have fov0 := fo_value_pars_firstorder_ind Σ t v i u args HΣ ty fo hev.
    have fov : fo_value_pars p1.2.1 v1.
    { rewrite e1. exact (fo_value_pars_trans Σ v (PCUICTyping.wf_ext_wf _ HΣ)
        fov0). }
    destruct (erases_fo_value_pars p1.2.1 Σer v1 wfp fov hpres v2 e2 hww)
      as [fow ecomp foi].
    set (P := fo_ind_kn p1.2.1.1).
    have hfb : fo_block_in P (compile_value_box p1.2.1 v1 []).
    { rewrite e1. exact (expand_lets_fo_block Σ t v i u args HΣ ty fo hev). }
    have fo2 : DeargFirstorder.fo_evalue_in P (ExAst.trans_env p2.2.1) v2.
    { apply (fo_evalue_in_of_block P Σer v2 fow). now rewrite ecomp. }
    (* The removal of the cases on propositions *)
    match type of e3 with _ = EOptimizePropDiscr.remove_match_on_box ?M _ =>
      set (Mrm := M) in e3 end.
    have [fo3 cs3] := fo_map_cstrip _ (ExAst.trans_env p2.2.1) P v2
      (remove_match_on_box_construct Mrm) fo2.
    rewrite -e3 in fo3 cs3.
    have hs3 : same_inds (ExAst.trans_env p2.2.1) (ExAst.trans_env p3.2.1).
    { intros kn. symmetry.
      exact (same_inds_remove_match_on_box_typed _ p2.2.1 kn). }
    have fo3' := same_inds_fo_evalue_in _ _ _ _ hs3 fo3.
    have hinit : forall kn b mibx,
      In (kn, b, ExAst.InductiveDecl mibx) p3.2.1 -> P kn ->
      DeargFirstorder.mm_ok (DeargFirstorder.init_mib_masks mibx).
    { intros kn b mibx hin hp.
      have hin' : In (kn, b, ExAst.InductiveDecl mibx) p2.2.1.
      { move: hin.
        change p3.2.1 with (remove_match_on_box_typed_env Mrm p2.2.1).
        rewrite /remove_match_on_box_typed_env.
        intros hin; apply in_map_iff in hin as [[[kn' b'] d] [e hin]].
        cbn in e. injection e as -> -> e.
        destruct d; cbn in e; try discriminate e.
        injection e as ->. exact hin. }
      destruct hΣex as [X_type [X [univs [retro [prop [incl [ign he]]]]]]].
      rewrite he in hin'.
      exact (DeargFirstorder.erase_global_decls_deps_recursive_mm_ok _ _ _
        _ _ _ _ _ _ fr hin' hp). }
    (* Dearging *)
    have [fo5 cs5 co5] := dearg_stage (dearging_config econf) p3.2.1 p3.2.2
      v3 P hinit fo3'.
    have fo5' : DeargFirstorder.fo_evalue_in P p5.2.1 v5.
    { rewrite e5. exact fo5. }
    have cs5' : DeargFirstorder.cstrip p5.2.1 v5 [] =
      DeargFirstorder.cstrip (ExAst.trans_env p3.2.1) v3 [].
    { rewrite e5. exact cs5. }
    (* The λ□ part *)
    have fo6 : EFirstorder.firstorder_evalue p6.2.1 v5 :=
      DeargFirstorder.fo_evalue_in_firstorder _ _ _ fo5'.
    have hc : EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip p6.2.1 v5) [] = compile_value_box p1.2.1 v1 [].
    { rewrite (compile_evalue_strip p6.2.1 v5 fo6)
        DeargFirstorder.compile_evalue_box_strip_cstrip.
      change (GlobalContextMap.global_decls p6.2.1) with p5.2.1.
      rewrite cs5' (same_inds_cstrip _ _ _ _ (fun kn => eq_sym (hs3 kn))) cs3.
      rewrite -ecomp DeargFirstorder.compile_evalue_box_strip_cstrip.
      reflexivity. }
    have foi6 : ∥ EFirstorder.firstorder_ind_value p6.2.1
      (EConstructorsAsBlocks.compile_evalue_box
        (ERemoveParams.strip p6.2.1 v5) []) ∥.
    { rewrite hc. eapply EFirstorder.firstorder_ind_value_is_coind;
        [|exact foi].
      intros kn. change (EGlobalEnv.is_coind p5.2.1 kn = EGlobalEnv.is_coind
        (ExAst.trans_env p2.2.1) kn).
      rewrite co5. exact (eq_sym (same_inds_is_coind _ _ _ hs3)). }
    have hv7 := obseq_typed_lambdabox_compile econf p6 pr1 _ v5 v7 eq_refl e7
      fo6 foi6.
    have hvt : compile_value_box p1.2.1 v1 [] = v_t.
    { rewrite e1. exact (compile_value_box_trans Σ v
        (PCUICTyping.wf_ext_wf _ HΣ) fov0). }
    rewrite hv7 hc hvt in ev7. exact ev7.
  Qed.
End TypedPipelineTheorem.
