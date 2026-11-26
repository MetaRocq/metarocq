(* Distributed under the terms of the MIT license. *)
(** * First-order values through MetaRocq's untyped erasure pipeline, from Template programs

    MetaRocq's [ErasureCorrectness.verified_erasure_pipeline_theorem] states that, for a PCUIC
    program of a first-order inductive type, the verified erasure pipeline computes the erasure
    of its value. This file proves a Template-level variant of it, for the untyped pipeline
    [Erasure.erasure_pipeline_mapping] (with an empty inductive mapping), in terms of the
    observational relation of the pipeline. It is a composition of:

    - a Template-level notion of first-order inductive types ([firstorder_ind], mirroring
      [PCUICFirstorder]) and of axiom-free environments, preserved by eta-expansion and by the
      translation to PCUIC ([eta_firstorder_ind], [trans_firstorder_ind], [eta_axiom_free],
      [trans_axiom_free]);
    - the fact that a first-order value is a tree of fully applied constructors
      ([pcuic_fo_tree_spec], [untrans_constructor_tree]), which eta-expansion leaves unchanged
      ([eta_expand_constructor_tree]), so that the eta-expanded program is still typed at the
      first-order inductive type ([typing_full_constructor_red]): MetaRocq only assumes that
      eta-expansion preserves well-typedness
      ([Erasure.assume_welltyped_template_program_expansion]);
    - the PCUIC-level result for [verified_erasure_pipeline]
      ([verified_erasure_pipeline_firstorder], from [v_t_spec], [obseq_lambdabox_firstorder] and
      [firstorder_erases_deterministic]), transported to the mapping variant
      [verified_erasure_pipeline_mapping] with an empty mapping
      ([verified_erasure_pipeline_mapping_firstorder]).

    The final theorem is [erasure_pipeline_mapping_firstorder]. Besides the erased value, it
    states that this value is a first-order value of the erased environment
    ([firstorder_evalue_block]) none of whose constructors belongs to a coinductive type
    ([ECoInductiveToInductive.firstorder_ind_value]).

    The last section describes the passes that may follow MetaRocq's pipeline on first-order
    values: constant-to-value translation, lazy and box implementation and the translation of
    coinductive types leave them unchanged, while
    unboxing unboxes their singleton constructors ([unbox_fo]). *)

From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Transform.
From MetaRocq.Template Require Import Ast Typing WcbvEval EtaExpand TemplateProgram.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC TemplateToPCUICCorrectness
  TemplateToPCUICWcbvEval PCUICTransform.
From MetaRocq.PCUIC Require PCUICAst PCUICTyping PCUICFirstorder PCUICClassification
  PCUICWcbvEval PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAst EGlobalEnv ErasureFunctionProperties EReorderCstrs.
From MetaRocq.Erasure Require Import EFirstorder.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure ErasureCorrectness.
From MetaRocq.ErasurePlugin.transforms Require Import RebuildWfEnv ReorderCstrs.
From MetaRocq.Erasure Require EEnvMap EConstantsToValues EImplementBox EImplementLazyForce
  ECoInductiveToInductive EUnboxing.
From MetaRocq.SafeChecker Require PCUICSafeReduce.

Import PCUICProgram Common.Transform.Transform.

Local Set Warnings "-notation-overridden".

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

(** ** First-order inductive types in Template programs

    These definitions mirror the ones of [PCUICFirstorder] on Template environments. *)

Section TemplateFirstorder.
  Context {Σb : list (kername × bool)}.

  Definition firstorder_type (n k : nat) (t : term) :=
    match (AstUtils.decompose_app t).1, (AstUtils.decompose_app t).2 with
    | tInd (mkInd nm i) u, [] =>
      match PCUICFirstorder.plookup_env Σb nm with Some b => b | None => false end
    | tRel i, [] => (k <=? i) && (i <? n + k)
    | _, _ => false
    end.

  Definition firstorder_con mind (c : constructor_body) :=
    let inds := #|mind.(ind_bodies)| in
    alli (fun k '({| decl_body := b ; decl_type := t ; decl_name := n|}) =>
      firstorder_type inds k t) 0
      (List.rev (c.(cstr_args) ++ mind.(ind_params)))%list.

  Definition firstorder_oneind mind (ind : one_inductive_body) :=
    forallb (firstorder_con mind) ind.(ind_ctors) && negb (Sort.is_level (ind_sort ind)).

  Definition firstorder_mutind (mind : mutual_inductive_body) :=
    ~~ (mind.(ind_finite) == CoFinite) &&
    forallb (firstorder_oneind mind) mind.(ind_bodies).

End TemplateFirstorder.

Definition firstorder_ind (Σ : global_env) (Σb : list (kername × bool)) (i : inductive) :=
  match lookup_env Σ (inductive_mind i) with
  | Some (InductiveDecl mind) => @firstorder_mutind Σb mind
  | _ => false
  end.

Fixpoint firstorder_env' (Σ : global_declarations) :=
  match Σ with
  | nil => []
  | (nm, ConstantDecl _) :: Σ' =>
    let Σb := firstorder_env' Σ' in
    ((nm, false) :: Σb)
  | (nm, InductiveDecl mind) :: Σ' =>
    let Σb := firstorder_env' Σ' in
    ((nm, @firstorder_mutind Σb mind) :: Σb)
  end.

Definition firstorder_env (Σ : global_env) :=
  firstorder_env' Σ.(declarations).

(** Template programs without axioms *)
Definition axiom_free (Σ : global_env) :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.

(** *** Preservation by eta-expansion *)

Lemma firstorder_con_types {Σb} mind c :
  @firstorder_con Σb mind c =
  alli (fun k t => @firstorder_type Σb #|ind_bodies mind| k t) 0
    (map decl_type (List.rev (cstr_args c ++ ind_params mind))).
Proof.
  rewrite /firstorder_con alli_map. apply alli_ext => k [] //.
Qed.

Lemma map_decl_type_eta_context Σ n Γ :
  map decl_type (eta_context Σ n Γ) = map decl_type Γ.
Proof.
  rewrite /eta_context. generalize (fun n0 => EtaExpand.eta_expand Σ (repeat None (n0 + n))).
  intros f. induction Γ => //=. now rewrite IHΓ.
Qed.

Lemma eta_firstorder_mutind {Σb} (Σ : GlobalEnvMap.t) m :
  @firstorder_mutind Σb (eta_minductive_decl Σ m) = @firstorder_mutind Σb m.
Proof.
  rewrite /firstorder_mutind /=. f_equal.
  rewrite forallb_map. apply forallb_ext => idecl.
  rewrite /firstorder_oneind /= forallb_map. f_equal. apply forallb_ext => cdecl.
  rewrite !firstorder_con_types /= length_map !map_rev !map_app.
  now rewrite !map_decl_type_eta_context.
Qed.

Lemma eta_firstorder_env' (Σ : GlobalEnvMap.t) decls :
  firstorder_env' (eta_global_declarations Σ decls) = firstorder_env' decls.
Proof.
  induction decls as [|[kn []] decls IH] => //=; rewrite IH //.
  now rewrite eta_firstorder_mutind.
Qed.

Lemma eta_lookup_env (Σ : GlobalEnvMap.t) kn :
  lookup_env (eta_expand_global_env Σ) kn =
  option_map (eta_global_declaration Σ) (lookup_env Σ kn).
Proof. apply lookup_global_map_on_snd. Qed.

Lemma eta_firstorder_ind (Σ : GlobalEnvMap.t) i :
  firstorder_ind (eta_expand_global_env Σ) (firstorder_env (eta_expand_global_env Σ)) i =
  firstorder_ind Σ (firstorder_env Σ) i.
Proof.
  rewrite /firstorder_ind eta_lookup_env /firstorder_env /= eta_firstorder_env'.
  destruct lookup_env as [[]|] => //=. apply eta_firstorder_mutind.
Qed.

Lemma eta_axiom_free (Σ : GlobalEnvMap.t) :
  axiom_free Σ -> axiom_free (eta_expand_global_env Σ).
Proof.
  intros ax c decl. rewrite /declared_constant /= /eta_global_declarations.
  move/in_map_iff => [[kn [cb|m]] [heq hin]]; cbn in heq; try discriminate.
  injection heq as -> <-. move: (ax _ _ hin). rewrite /eta_global_decl /=. now destruct cst_body.
Qed.

(** *** Preservation by the translation to PCUIC *)

Module PE := PCUICAst.PCUICEnvironment.

Lemma trans_global_decls_cons env d ds :
  PE.declarations (trans_global_decls env (d :: ds)) =
  (d.1, trans_global_decl (trans_global_decls env ds) d.2) ::
    PE.declarations (trans_global_decls env ds).
Proof. reflexivity. Qed.

Lemma trans_global_env_lookup (Σ : global_env) kn :
  match lookup_env Σ kn with
  | Some d => exists Σ', PE.lookup_env (trans_global_env Σ) kn = Some (trans_global_decl Σ' d)
  | None => PE.lookup_env (trans_global_env Σ) kn = None
  end.
Proof.
  destruct Σ as [univs decls retro].
  rewrite /lookup_env /PE.lookup_env /trans_global_env /=.
  induction decls as [|[kn' d] decls IH] => //=.
  destruct (kn == kn') => //. now eexists.
Qed.

Lemma trans_firstorder_type {Σb Σb'} T n k t :
  (forall kn, PCUICFirstorder.plookup_env Σb kn = Some true ->
    PCUICFirstorder.plookup_env Σb' kn = Some true) ->
  @firstorder_type Σb n k t -> @PCUICFirstorder.firstorder_type Σb' n k (trans T t).
Proof.
  intros hle. rewrite /firstorder_type /PCUICFirstorder.firstorder_type.
  destruct t => //=.
  - destruct args; [|by destruct t0 => //=; destruct ind]. cbn. destruct t0 => //=.
    destruct ind as [nm i]. destruct PCUICFirstorder.plookup_env as [[]|] eqn:hl => //.
    now rewrite (hle _ hl).
  - destruct ind as [nm i]. destruct PCUICFirstorder.plookup_env as [[]|] eqn:hl => //.
    now rewrite (hle _ hl).
Qed.

Lemma pcuic_firstorder_con_types {Σb} mind c :
  @PCUICFirstorder.firstorder_con Σb mind c =
  alli (fun k t => @PCUICFirstorder.firstorder_type Σb #|PE.ind_bodies mind| k t) 0
    (map decl_type (List.rev (PE.cstr_args c ++ PE.ind_params mind))).
Proof.
  rewrite /PCUICFirstorder.firstorder_con alli_map. apply alli_ext => k [] //.
Qed.

Lemma map_decl_type_trans_local T Γ :
  map decl_type (trans_local T Γ) = map (trans T) (map decl_type Γ).
Proof. rewrite /trans_local !map_map //. Qed.

Lemma trans_firstorder_mutind {Σb Σb'} T m :
  (forall kn, PCUICFirstorder.plookup_env Σb kn = Some true ->
    PCUICFirstorder.plookup_env Σb' kn = Some true) ->
  @firstorder_mutind Σb m -> @PCUICFirstorder.firstorder_mutind Σb' (trans_minductive_body T m).
Proof.
  intros hle. rewrite /firstorder_mutind /PCUICFirstorder.firstorder_mutind /=.
  move/andP => [-> hb] /=. rewrite forallb_map. solve_all.
  move: H. rewrite /firstorder_oneind /PCUICFirstorder.firstorder_oneind /=.
  move/andP => [hc ->]. rewrite andb_true_r forallb_map. solve_all.
  move: H. rewrite firstorder_con_types pcuic_firstorder_con_types /= length_map.
  rewrite !map_rev !map_app !map_decl_type_trans_local -!map_app -map_rev alli_map.
  rewrite -map_rev alli_map -map_rev alli_map.
  apply alli_impl => k ty. now apply trans_firstorder_type.
Qed.

Lemma trans_firstorder_env' (Σ : global_env) :
  forall kn, PCUICFirstorder.plookup_env (firstorder_env Σ) kn = Some true ->
  PCUICFirstorder.plookup_env
    (PCUICFirstorder.firstorder_env' (PE.declarations (trans_global_env Σ))) kn = Some true.
Proof.
  destruct Σ as [univs decls retro]. rewrite /firstorder_env /trans_global_env /=.
  induction decls as [|[kn' []] decls IH] => kn //=.
  - destruct (kn == kn') => //. apply IH.
  - destruct (kn == kn'); [|apply IH]. intros [= h]. f_equal.
    eapply trans_firstorder_mutind; [exact IH|exact h].
Qed.

Lemma trans_firstorder_ind (Σ : global_env) univs i :
  firstorder_ind Σ (firstorder_env Σ) i ->
  PCUICFirstorder.firstorder_ind (trans_global (Σ, univs))
    (PCUICFirstorder.firstorder_env (trans_global (Σ, univs))) i.
Proof.
  rewrite /firstorder_ind /PCUICFirstorder.firstorder_ind /=.
  have := trans_global_env_lookup Σ (inductive_mind i).
  destruct lookup_env as [[|m]|] => //. intros [Σ' ->] => /=.
  eapply trans_firstorder_mutind, trans_firstorder_env'.
Qed.

Lemma trans_axiom_free (Σ : global_env) :
  axiom_free Σ -> PCUICClassification.axiom_free (trans_global_env Σ).
Proof.
  destruct Σ as [univs decls retro].
  rewrite /axiom_free /PCUICClassification.axiom_free /declared_constant
    /PCUICAst.declared_constant /trans_global_env /=.
  induction decls as [|[kn' d] decls IH] => /= ax c decl //.
  intros [heq|hin].
  - destruct d as [cb|m]; cbn in heq; try discriminate. injection heq as <- <-.
    move: (ax kn' cb (or_introl eq_refl)). cbn. now destruct cst_body.
  - refine (IH _ c decl hin). intros c' d' hin'. apply (ax c' d'). now right.
Qed.

(** ** First-order values in PCUIC

    A first-order value is a tree of fully applied constructors, all of first-order inductive
    types (hence not coinductive). This strengthens [PCUICFirstorder.firstorder_value_spec], which
    does not record that the inductive types of the subtrees are first-order. *)

Section PCUICFirstorderTree.
  Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICFirstorder.

  Inductive pcuic_fo_tree (Σ : global_env_ext) : term -> Prop :=
  | pcuic_fo_tree_node ind c ui args mdecl idecl cdecl :
    declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
    #|args| = ind_npars mdecl + context_assumptions (cstr_args cdecl) ->
    firstorder_ind Σ (firstorder_env Σ) ind ->
    Forall (pcuic_fo_tree Σ) args ->
    pcuic_fo_tree Σ (mkApps (tConstruct ind c ui) args).

  Lemma pcuic_fo_tree_spec (Σ : global_env_ext) t i u args :
    PCUICTyping.wf Σ ->
    PCUICTyping.typing Σ [] t (mkApps (tInd i u) args) ->
    PCUICWcbvEval.value Σ t ->
    firstorder_ind Σ (firstorder_env Σ) i ->
    pcuic_fo_tree Σ t.
  Proof.
    intros wfΣ Hty Hval Hfo.
    have hfo := firstorder_value_spec Σ t i u args wfΣ localenv_nil Hty Hval Hfo.
    clear Hval. revert i u args Hty Hfo. move: t hfo.
    apply: (firstorder_value_inds Σ []).
    intros i0 n ui u0 args0 pandi hty0 hargs IH hprop i u args Hty Hfo.
    destruct (PCUICInductiveInversion.Construct_Ind_ind_eq' wfΣ Hty)
      as [mdecl [idecl [cdecl [declc [[[[[-> _] _] _] hlen] _]]]]].
    econstructor; tea.
    { unshelve eapply PCUICTyping.declared_constructor_to_gen; eauto. }
    apply PCUICValidity.inversion_mkApps in Hty as (A & typ_ctor & spine); auto.
    apply inversion_Construct in typ_ctor as (mdecl' & idecl' & cdecl' & _ & declc' & cu & cum);
      auto.
    eapply PCUICSpine.typing_spine_strengthen in spine. 3: exact cum.
    2: eapply PCUICInductiveInversion.declared_constructor_valid_ty; eauto.
    eapply firstorder_args in spine; eauto.
    clear -IH spine.
    remember (type_of_constructor _ _ _ _) as T eqn:eqT. clear eqT.
    induction spine; constructor; inv IH; eauto.
  Qed.

End PCUICFirstorderTree.

(** ** Types of fully applied constructors *)

Section ConstructorTyping.
  Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
    PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
    PCUICSR PCUICInversion PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
    PCUICSigmaCalculus PCUICContextConversion
    PCUICUnivSubst PCUICCumulativity PCUICConfluence
    PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
    PCUICConversion PCUICValidity PCUICInductives
    PCUICInductiveInversion PCUICGlobalEnv PCUICWellScopedCumulativity PCUICWeakeningEnvTyp
    PCUICProgress.

  (** The type of a fully applied constructor reduces to an application of its inductive
      type. *)
  Lemma typing_full_constructor_red {Σ : global_env_ext} {wfΣ : PCUICTyping.wf Σ}
    {ind c u args T} {mdecl idecl cdecl} :
    declared_constructor Σ (ind, c) mdecl idecl cdecl ->
    #|args| = ind_npars mdecl + context_assumptions (cstr_args cdecl) ->
    PCUICTyping.typing Σ [] (mkApps (tConstruct ind c u) args) T ->
    ∑ u' args', PCUICReduction.red Σ [] T (mkApps (tInd ind u') args').
  Proof.
    intros declc hlen hc.
    pose proof (validity hc).
    eapply PCUICSpine.inversion_mkApps_direct in hc as [A' [u' [s' [hs hsp]]]]; eauto.
    eapply inversion_Construct in s' as [mdecl' [idecl' [cdecl' [wf [declc' [cu cum]]]]]]; tea.
    unshelve epose proof (declc_ := declared_constructor_to_gen declc); eauto.
    unshelve epose proof (declc'_ := declared_constructor_to_gen declc'); eauto.
    destruct (PCUICGlobalEnv.declared_constructor_inj declc_ declc'_) as [? []].
    subst mdecl' idecl' cdecl'.
    clear declc'.
    eapply typing_spine_strengthen in hsp. 3:exact cum.
    2:{ eapply validity. econstructor; tea. }
    unfold type_of_constructor in hsp.
    destruct (on_declared_constructor declc) as [[] [cunivs [_ onc]]].
    rewrite onc.(cstr_eq) in hsp.
    rewrite <-it_mkProd_or_LetIn_app in hsp.
    rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn in hsp.
    epose proof (subst_cstr_concl_head ind u mdecl (cstr_args cdecl) (cstr_indices cdecl)).
    cbn in H.
    unfold cstr_concl in hsp. cbn in hsp. len in hsp. rewrite H in hsp. clear H.
    all: try exact (declared_constructor_ind_decl declc).
    rewrite -(app_nil_r args) in hsp.
    eapply typing_spine_inv in hsp as [args_sub [_ hsp]].
    2:{ len. rewrite hlen. now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars declc). }
    depelim hsp. rewrite subst_mkApps /= in w.
    eapply PCUICConversion.ws_cumul_pb_Ind_l_inv in w as [ui' [l' [hred _ _]]].
    exists ui', l'. apply hred.
  Qed.

End ConstructorTyping.

Lemma firstorder_evalue_block_extends Σ Σ' t :
  EGlobalEnv.extends Σ Σ' -> firstorder_evalue_block Σ t -> firstorder_evalue_block Σ' t.
Proof.
  intros ext; move: t.
  apply: firstorder_evalue_block_elim => i n args hl _ ih.
  constructor => //.
  move: hl; rewrite /EGlobalEnv.lookup_constructor_pars_args /EGlobalEnv.lookup_constructor
    /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive.
  move: (ext (inductive_mind i)).
  now case: EGlobalEnv.lookup_env => // a; move/(_ _ eq_refl) ->.
Qed.

Section CompileValueBox.
  Import PCUICAst PCUICAstUtils PCUICFirstorder.

  Lemma pcuic_fo_tree_ind' (Σ : global_env_ext) (P : term -> Prop) :
    (forall ind c ui args mdecl idecl cdecl,
      declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
      #|args| = ind_npars mdecl + context_assumptions (cstr_args cdecl) ->
      firstorder_ind Σ (firstorder_env Σ) ind ->
      Forall (pcuic_fo_tree Σ) args -> Forall P args ->
      P (mkApps (tConstruct ind c ui) args)) ->
    forall t, pcuic_fo_tree Σ t -> P t.
  Proof.
    intros hP. fix IH 2. intros t [ind c ui args mdecl idecl cdecl hd hl hf hargs].
    eapply hP; eauto. clear -IH hargs. induction hargs; constructor; auto.
  Qed.

  (** The compiled value is built from constructors of inductive types that are not
      coinductive in [Σ'] *)
  Lemma compile_value_box_firstorder_ind_value (Σ : global_env_ext) (Σ' : EAst.global_context) t :
    (forall ind, firstorder_ind Σ (firstorder_env Σ) ind ->
      EGlobalEnv.is_coind Σ' (inductive_mind ind) = false) ->
    pcuic_fo_tree Σ t ->
    ∥ ECoInductiveToInductive.firstorder_ind_value Σ'
        (compile_value_box (PCUICExpandLets.trans_global_env Σ.1) t []) ∥.
  Proof.
    intros hco. induction 1 using pcuic_fo_tree_ind'.
    rewrite (compile_value_box_mkApps (npars := ind_npars mdecl)).
    { rewrite /pcuic_lookup_inductive_pars PCUICExpandLetsCorrectness.trans_lookup.
      destruct H as [[hm _] _]. red in hm. now rewrite hm. }
    have [hargs] : ∥ All (ECoInductiveToInductive.firstorder_ind_value Σ')
      (map (flip (compile_value_box (PCUICExpandLets.trans_global_env Σ.1)) []) args) ∥.
    { clear -H3. induction H3 as [|x l [hx] _ [hl]]; cbn; sq; constructor; auto. }
    sq. constructor; [now apply hco|]. rewrite app_nil_r. now apply All_skipn.
  Qed.

End CompileValueBox.

(** ** Trees of fully applied constructors in Template programs *)

Inductive template_constructor_tree (Σ : global_env) : term -> Prop :=
| template_constructor_tree_node ind c u args mdecl idecl cdecl :
  declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
  #|args| = ind_npars mdecl + context_assumptions (cstr_args cdecl) ->
  Forall (template_constructor_tree Σ) args ->
  template_constructor_tree Σ (mkApps (tConstruct ind c u) args).

Lemma template_constructor_tree_ind' (Σ : global_env) (P : term -> Prop) :
  (forall ind c u args mdecl idecl cdecl,
    declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
    #|args| = ind_npars mdecl + context_assumptions (cstr_args cdecl) ->
    Forall (template_constructor_tree Σ) args -> Forall P args ->
    P (mkApps (tConstruct ind c u) args)) ->
  forall t, template_constructor_tree Σ t -> P t.
Proof.
  intros hP. fix IH 2. intros t [ind c u args mdecl idecl cdecl hd hl hargs].
  eapply hP; eauto. clear -IH hargs. induction hargs; constructor; auto.
Qed.

(** Eta-expansion is the identity on trees of fully applied constructors *)
Lemma eta_expand_constructor_tree (Σ : GlobalEnvMap.t) v :
  template_constructor_tree Σ v -> EtaExpand.eta_expand Σ [] v = v.
Proof.
  induction 1 using template_constructor_tree_ind'.
  have hl : GlobalEnvMap.lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl).
  { rewrite GlobalEnvMap.lookup_constructor_spec. destruct H as [[hm hi] hc].
    rewrite /Ast.lookup_constructor /lookup_constructor_gen /lookup_inductive_gen
      /lookup_minductive_gen. red in hm. now rewrite hm /= hi /= hc. }
  destruct args as [|a args].
  - cbn. rewrite /eta_constructor hl /eta_single. cbn in H0. rewrite -H0 /=.
    reflexivity.
  - cbn [mkApps EtaExpand.eta_expand].
    have -> : map (EtaExpand.eta_expand Σ []) (a :: args) = a :: args.
    { clear -H2. induction H2; cbn; congruence. }
    rewrite /eta_constructor hl /eta_single -H0 Nat.sub_diag /=.
    cbn. rewrite app_nil_r lift0_p. f_equal. f_equal.
    clear. induction args; cbn; rewrite ?lift0_p; congruence.
Qed.

Lemma eta_constructor_tree (Σ : GlobalEnvMap.t) v :
  template_constructor_tree Σ v -> template_constructor_tree (eta_expand_global_env Σ) v.
Proof.
  induction 1 using template_constructor_tree_ind'.
  econstructor.
  - destruct H as [[hm hi] hc]. red in hm.
    split; [split|].
    + red. rewrite eta_lookup_env hm. reflexivity.
    + cbn. rewrite nth_error_map hi. reflexivity.
    + cbn. rewrite nth_error_map hc. reflexivity.
  - cbn. now rewrite -eta_context_assumptions.
  - exact H2.
Qed.

Lemma trans_mkApps_tConstruct T ind c u args :
  trans T (mkApps (tConstruct ind c u) args) =
  PCUICAst.mkApps (PCUICAst.tConstruct ind c u) (map (trans T) args).
Proof. now destruct args. Qed.

(** The translation of a tree of constructors does not depend on the environment *)
Lemma trans_constructor_tree_env Σ T T' v :
  template_constructor_tree Σ v -> trans T v = trans T' v.
Proof.
  induction 1 using template_constructor_tree_ind'.
  rewrite !trans_mkApps_tConstruct. f_equal.
  clear -H2. induction H2; cbn; congruence.
Qed.

Lemma context_assumptions_trans_local T Γ :
  PCUICAst.PCUICEnvironment.context_assumptions (trans_local T Γ) = context_assumptions Γ.
Proof. induction Γ as [|[na [b|] ty] Γ IH] => //=; now rewrite IH. Qed.

Lemma trans_declared_constructor (Σ : global_env) ind c mdecl idecl cdecl :
  declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
  exists Σ', PCUICAst.declared_constructor_gen (PE.lookup_env (trans_global_env Σ)) (ind, c)
    (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl)
    (trans_constructor_body Σ' cdecl).
Proof.
  intros [[hm hi] hc]. red in hm.
  have := trans_global_env_lookup Σ (inductive_mind ind). rewrite hm => [[Σ' hl]].
  exists Σ'. split; [split|].
  - exact hl.
  - cbn. now rewrite nth_error_map hi.
  - cbn. now rewrite nth_error_map hc.
Qed.

Lemma untrans_declared_constructor (Σ : global_env) ind c mdecl' idecl' cdecl' :
  PCUICAst.declared_constructor_gen (PE.lookup_env (trans_global_env Σ)) (ind, c)
    mdecl' idecl' cdecl' ->
  exists Σ' mdecl idecl cdecl,
    [/\ declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl,
      mdecl' = trans_minductive_body Σ' mdecl & cdecl' = trans_constructor_body Σ' cdecl].
Proof.
  intros [[hm hi] hc]. red in hm.
  have := trans_global_env_lookup Σ (inductive_mind ind).
  destruct lookup_env as [[|mdecl]|] eqn:hl.
  - intros [Σ' hl']. rewrite hm in hl'. discriminate.
  - intros [Σ' hl']. rewrite hm in hl'. injection hl' as ->.
    cbn in hi. rewrite nth_error_map in hi.
    destruct (nth_error (ind_bodies mdecl) _) as [idecl|] eqn:hi' => //. cbn in hi.
    injection hi as <-.
    cbn in hc. rewrite nth_error_map in hc.
    destruct (nth_error (ind_ctors idecl)) as [cdecl|] eqn:hc' => //. cbn in hc.
    injection hc as <-.
    exists Σ', mdecl, idecl, cdecl. split => //.
  - rewrite hm. discriminate.
Qed.

(** A Template term whose translation is a tree of first-order constructors is a tree of
    fully applied constructors. *)
Lemma untrans_constructor_tree (Σ : global_env) univs v :
  WfAst.wf Σ v ->
  pcuic_fo_tree (trans_global (Σ, univs)) (trans (trans_global_env Σ) v) ->
  template_constructor_tree Σ v.
Proof.
  induction v using term_forall_list_ind; intros hwf htree;
    inversion htree as [ind' c' ui args mdecl' idecl' cdecl' hd hlen _ hargs heq];
    have hdec := f_equal PCUICAstUtils.decompose_app heq;
    rewrite PCUICAstUtils.decompose_app_mkApps // in hdec;
    cbn in hdec; try discriminate.
  3:{ destruct TransLookup.lookup_inductive as [[]|] in hdec; cbn in hdec; discriminate. }
  2:{ injection hdec as -> -> -> ->.
      apply untrans_declared_constructor in hd as (Σ' & m & idc & cd & [hd' -> ->]).
      change (tConstruct i n u) with (mkApps (tConstruct i n u) []).
      econstructor; [exact hd'| |constructor]. cbn in hlen |- *.
      now rewrite context_assumptions_trans_local in hlen. }
  depelim hwf.
  rewrite /PCUICAstUtils.decompose_app PCUICAstUtils.decompose_app_rec_mkApps in hdec.
  destruct v; cbn in hdec; try discriminate.
  2:{ destruct TransLookup.lookup_inductive as [[]|] in hdec; cbn in hdec; discriminate. }
  injection hdec as -> -> -> ->. rewrite app_nil_r in hlen hargs.
  apply untrans_declared_constructor in hd as (Σ' & m & idc & cd & [hd' -> ->]).
  destruct l as [|a0 l] => //.
  change (tApp (tConstruct ind idx u) (a0 :: l)) with (mkApps (tConstruct ind idx u) (a0 :: l)).
  econstructor; [exact hd'| |].
  - cbn in hlen |- *. rewrite length_map context_assumptions_trans_local in hlen. exact hlen.
  - clear -H a hargs. remember (a0 :: l) as l'. clear Heql'.
    induction H; constructor; depelim a; depelim hargs; eauto.
Qed.

(** ** The mapping variant of the verified erasure pipeline, with an empty mapping *)

Lemma reorder_nil t : EReorderCstrs.reorder [] t = t.
Proof.
  induction t using EInduction.term_forall_list_ind; simp reorder; f_equal; solve_all.
  rewrite /EReorderCstrs.reorder_branches /=. solve_all.
Qed.

Lemma reorder_env_nil Σ : EReorderCstrs.reorder_env [] Σ = Σ.
Proof.
  rewrite /EReorderCstrs.reorder_env.
  induction Σ as [|[kn []] Σ IH] => //=; rewrite IH; f_equal.
  - rewrite /EReorderCstrs.reorder_decl /= /EReorderCstrs.reorder_constant_decl.
    destruct c as [[b|]] => //=. now rewrite reorder_nil.
  - rewrite /EReorderCstrs.reorder_decl /= /EReorderCstrs.reorder_inductive_decl.
    destruct m as [fin np bds]; cbn. do 3 f_equal.
    rewrite /EReorderCstrs.reorder_one_ind /=. clear. rewrite /mapi. generalize 0.
    induction bds => //= n. now rewrite IHbds.
Qed.

Lemma transform_eq {env env' term term' value value' : Type} {eval eval'}
  (o : Transform.t env env' term term' value value' eval eval') x y px py :
  x = y -> transform o x px = transform o y py.
Proof. intros ->. f_equal. apply proof_irrelevance. Qed.

Lemma rebuild_reorder_erase_program {efl : EWellformed.EEnvFlags} (p : pcuic_program)
  nin nin' nin2 nin2' wt wt' w :
  rebuild_wf_env (efl := efl)
    (EReorderCstrs.reorder_program []
      (to_program (@erase_program fake_guard_impl p nin nin' wt))) w =
  @erase_program fake_guard_impl p nin2 nin2' wt'.
Proof.
  have <- : wt = wt' by apply proof_irrelevance.
  have <- : nin = nin2 by apply proof_irrelevance.
  have <- : nin' = nin2' by apply proof_irrelevance.
  rewrite /rebuild_wf_env /EReorderCstrs.reorder_program /=.
  move: (EProgram.wf_glob_fresh _ _). rewrite reorder_env_nil reorder_nil.
  rewrite /erase_program /erase_pcuic_program /=. intros f. f_equal.
  apply EEnvMap.GlobalContextMap.make_irrel.
Qed.

Lemma verified_erasure_pipeline_mapping_transform econf (Σ : global_env_ext_map) t pr pr' :
  transform (verified_erasure_pipeline_mapping econf) ([], (Σ, t)) pr =
  transform (verified_erasure_pipeline econf) (Σ, t) pr'.
Proof.
  unfold verified_erasure_pipeline_mapping, verified_erasure_pipeline,
    verified_lambdabox_pipeline_mapping.
  do 4 (cbn [transform compose]; unfold run, time).
  cbn [transform pcuic_expand_lets_transform_mapping erase_transform_mapping
    reorder_cstrs_transformation rebuild_wf_env_transform pcuic_expand_lets_transform
    erase_transform fst snd].
  apply transform_eq, rebuild_reorder_erase_program.
Qed.

Lemma obseq_eq {env env' term term' value value' : Type} {eval eval'}
  (o : Transform.t env env' term term' value value' eval eval') x y px py p1 p2 v1 v2 v' :
  x = y -> p1 = p2 -> v1 = v2 -> obseq o x px p1 v1 v' -> obseq o y py p2 v2 v'.
Proof. intros -> -> ->. now have -> : px = py by apply proof_irrelevance. Qed.

Lemma verified_erasure_pipeline_mapping_obseq econf (Σ : global_env_ext_map) t pr pr' v v' :
  obseq (verified_erasure_pipeline_mapping econf) ([], (Σ, t)) pr
    (transform (verified_erasure_pipeline_mapping econf) ([], (Σ, t)) pr) v v' ->
  obseq (verified_erasure_pipeline econf) (Σ, t) pr'
    (transform (verified_erasure_pipeline econf) (Σ, t) pr') v v'.
Proof.
  intros h.
  have e := verified_erasure_pipeline_mapping_transform econf Σ t pr pr'.
  move: h e.
  generalize (transform (verified_erasure_pipeline_mapping econf) ([], (Σ, t)) pr) as P1.
  generalize (transform (verified_erasure_pipeline econf) (Σ, t) pr') as P2.
  move: pr pr'.
  unfold verified_erasure_pipeline_mapping, verified_erasure_pipeline,
    verified_lambdabox_pipeline_mapping.
  intros pr pr' P2 P1.
  do 4 (cbn [obseq compose]; unfold run, time).
  cbn [transform obseq pcuic_expand_lets_transform_mapping erase_transform_mapping
    reorder_cstrs_transformation rebuild_wf_env_transform pcuic_expand_lets_transform
    erase_transform fst snd].
  intros [v1 [h1 [v2 [[v3 [hv3 hv3']] h4]]]] e.
  exists v1. split => //. subst v3 v2.
  move: h4. apply obseq_eq => //.
  all: do 2 (cbn [transform compose]; unfold run, time).
  all: cbn [transform pcuic_expand_lets_transform_mapping erase_transform_mapping
    reorder_cstrs_transformation rebuild_wf_env_transform pcuic_expand_lets_transform
    erase_transform fst snd].
  - apply rebuild_reorder_erase_program.
  - apply reorder_nil.
Qed.

Section pipeline_obseq.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.

  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.
  Variable axfree : PCUICClassification.axiom_free Σ.
  Variable v : PCUICAst.term.

  Variable i : Kernames.inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.

  Variable Normalisation : (forall Σ, PCUICTyping.wf_ext Σ -> PCUICSN.NormalizationIn Σ).

  Variable typing : ∥PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args)∥.

  Variable fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Variable econf : erasure_configuration.

  Let v_t := compile_value_box (PCUICExpandLets.trans_global_env Σ) v [].

  Lemma v_fo_tree : pcuic_fo_tree Σ v.
  Proof.
    destruct typing as [ty], Heval as [ev].
    eapply pcuic_fo_tree_spec; tea. apply HΣ.
    eapply PCUICClassification.subject_reduction_eval; tea.
    eapply PCUICWcbvEval.eval_to_value; tea.
  Qed.

  Lemma firstorder_ind_not_cofinite pr ind :
    PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) ind ->
    EGlobalEnv.is_coind (transform (verified_erasure_pipeline econf) (Σ, t) pr).1
      (inductive_mind ind) = false.
  Proof.
    have -> : pr = precond Σ t _ HΣ expΣ expt typing Normalisation econf
      by apply proof_irrelevance.
    rewrite /EGlobalEnv.is_coind /EGlobalEnv.lookup_inductive_kind /EGlobalEnv.lookup_minductive.
    destruct EGlobalEnv.lookup_env as [[|m]|] eqn:hl => //=.
    eapply (@verified_erasure_pipeline_lookup_env_in Σ t _ HΣ expΣ expt typing Normalisation
      econf _ _ eq_refl eq_refl) in hl as [decl' [hl' hd]].
    have := PCUICExpandLetsCorrectness.trans_lookup Σ.1 (inductive_mind ind).
    rewrite /PCUICAst.PCUICEnvironment.lookup_env /= hl'.
    rewrite /PCUICFirstorder.firstorder_ind /PCUICAst.PCUICEnvironment.lookup_env.
    clear hl'.
    destruct PCUICAst.PCUICEnvironment.lookup_global as [[|mi]|]; cbn; intros heq;
      try discriminate; injection heq as ->; cbn in hd; try contradiction; subst m; cbn.
    move=> _. by case: (PCUICAst.PCUICEnvironment.ind_finite mi).
  Qed.

  Lemma verified_erasure_pipeline_obseq_firstorder pr v' :
    obseq (verified_erasure_pipeline econf) (Σ, t) pr
      (transform (verified_erasure_pipeline econf) (Σ, t) pr) v v' ->
    v' = v_t.
  Proof.
    intros obs. subst v_t.
    rewrite (v_t_spec Σ HΣ expΣ t expt axfree v i u args Normalisation typing fo Heval econf).
    set (pre := precond2 _ _ _ _ _ _ _ _ _ _ _) in *. clearbody pre.
    move: obs. unfold verified_erasure_pipeline. intros obs.
    cbn [obseq compose] in obs.
    unfold run, time in obs.
    decompose [ex and prod] obs. clear obs.
    subst.
    cbn [obseq compose erase_transform] in *.
    cbn [obseq compose pcuic_expand_lets_transform] in *.
    subst.
    move: b b0.
    repeat destruct_compose.
    intros.
    move: b b0.
    cbn [transform erase_transform] in *.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    unfold run, time.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    cbn [transform erase_transform] in *.
    intros obs b0.
    destruct Heval as [Heval'].
    pose proof typing as [typing']. pose proof typing as [typing''].
    eapply PCUICClassification.subject_reduction_eval in typing'; tea.
    eapply PCUICExpandLetsCorrectness.pcuic_expand_lets in typing'.
    2:{ apply HΣ. }
    2:{ apply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in typing'.
    unfold PCUICExpandLets.expand_lets_program in *.
    set (em := build_global_env_map _) in *.
    unfold erase_program.
    set (f := map_squash _ _). cbn in f.
    destruct H. destruct s as [[]].
    set (wfe := build_wf_env_from_env em (map_squash (PCUICTyping.wf_ext_wf (em, Σ.2))
      (map_squash fst (conj (sq (w, s)) a).p1))).
    eapply (ErasureFunctionProperties.firstorder_erases_deterministic optimized_abstract_env_impl
      wfe Σ.2) in b0. 3:tea.
    2:{ cbn. reflexivity. }
    2:{ eapply PCUICExpandLetsCorrectness.trans_wcbveval. eapply PCUICWcbvEval.eval_closed; tea.
        apply HΣ. clear -typing'' HΣ. now eapply PCUICClosedTyp.subject_closed in typing''.
        eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in Heval'. }
    2:{ clear -fo. revert fo. rewrite /PCUICFirstorder.firstorder_ind /=.
        rewrite PCUICExpandLetsCorrectness.trans_lookup.
        destruct PCUICAst.PCUICEnvironment.lookup_env => //.
        destruct g => //=.
        eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind.
        eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
    rewrite b0 in obs.
    (* The erased value and its inductives are first-order, as required to observe it through
       the cofixpoint translation *)
    destruct (erase_v_firstorder Σ HΣ expΣ t expt axfree v i u args Normalisation typing fo Heval
      econf (conj (sq (w, s)) a)) as [fov E hpres].
    destruct (v_t_firstorder_ind Σ HΣ t v i u args typing fo Heval _ hpres) as [foiv].
    rewrite -E in foiv.
    match type of obs with
    | obseq _ ?P _ _ _ _ => pose proof (v_t_firstorder_ind Σ HΣ t v i u args typing fo Heval
        (EEnvMap.GlobalContextMap.global_decls P.1)) as foit
    end.
    forward foit.
    { apply (erase_transform_preserves_inductives (PCUICExpandLets.expand_lets_program (Σ, t))). }
    destruct foit as [foit]. rewrite -E in foit.
    symmetry. eapply obseq_lambdabox_firstorder; revgoals.
    1: exact foit. 1: exact foiv. 1: exact fov.
    unfold erase_pcuic_program. cbn [fst snd]. exact obs.
    have [hexpΣ hexpt] :=
      PCUICExpandLetsCorrectness.expanded_expand_lets_program
        (cf := extraction_checker_flags) (Σ, t) (HΣ, (_; typing''))
        (conj expΣ expt).
    eapply extends_erase_pcuic_program;
      [exact (ErasureFunction.expanded_global_env_cofix_lambdas _ hexpΣ)
      |exact (ErasureFunction.expanded_cofix_lambdas _ _ _ hexpt)|..]. cbn.
    unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (cf := extraction_checker_flags)
      (Σ := (Σ.1, Σ.2))).
    { now eapply PCUICExpandLetsCorrectness.trans_wf. }
    { clear -HΣ typing''. now eapply PCUICClosedTyp.subject_closed in typing''. }
    cbn. 2:cbn. exact Heval'.
    now eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ).
    pose proof (PCUICExpandLetsCorrectness.expand_lets_sound typing'') as X1.
    rewrite PCUICExpandLetsCorrectness.trans_mkApps in X1. eapply X1.
    cbn. eapply (PCUICExpandLetsCorrectness.trans_firstorder_ind Σ); eauto.
    Unshelve. exact extraction_checker_flags. apply HΣ.
    apply PCUICExpandLetsCorrectness.trans_wf, HΣ.
  Qed.

  (** The main result of this section: the erased value is the erasure of [v] (with parameters
      removed), it is a first-order value in the erased environment, and none of its
      constructors belongs to a coinductive type. *)
  Lemma verified_erasure_pipeline_firstorder pr v' :
    obseq (verified_erasure_pipeline econf) (Σ, t) pr
      (transform (verified_erasure_pipeline econf) (Σ, t) pr) v v' ->
    let Σ' := (transform (verified_erasure_pipeline econf) (Σ, t) pr).1 in
    v' = v_t /\ firstorder_evalue_block Σ' v' /\
    ∥ ECoInductiveToInductive.firstorder_ind_value Σ' v' ∥.
  Proof.
    intros obs Σ'. have -> := verified_erasure_pipeline_obseq_firstorder pr v' obs.
    split => //. split.
    - eapply firstorder_evalue_block_extends;
        [|apply (verified_erasure_pipeline_firstorder_evalue_block Σ HΣ expΣ t expt axfree v i u
                   args Normalisation typing fo Heval econf)].
      subst Σ'.
      have -> : pr = precond Σ t _ HΣ expΣ expt typing Normalisation econf
        by apply proof_irrelevance.
      exact (@verified_erasure_pipeline_extends Σ HΣ expΣ t expt axfree v i u args Normalisation
        typing fo Heval econf eq_refl eq_refl).
    - exact (compile_value_box_firstorder_ind_value Σ Σ' v
        (fun ind => firstorder_ind_not_cofinite pr ind) v_fo_tree).
  Qed.

End pipeline_obseq.

(** The same result for the variant of the pipeline with inductive mappings, with an empty
    mapping. *)
Theorem verified_erasure_pipeline_mapping_firstorder (Σ : global_env_ext_map)
  (HΣ : PCUICTyping.wf_ext Σ) (expΣ : PCUICEtaExpand.expanded_global_env Σ.1)
  (t : PCUICAst.term) (expt : PCUICEtaExpand.expanded Σ.1 [] t)
  (axfree : PCUICClassification.axiom_free Σ) (v : PCUICAst.term) i u args
  (Normalisation : forall Σ, PCUICTyping.wf_ext Σ -> PCUICSN.NormalizationIn Σ)
  (typing : ∥ PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args) ∥)
  (fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i)
  (Heval : ∥ PCUICWcbvEval.eval Σ t v ∥) econf pr v' :
  obseq (verified_erasure_pipeline_mapping econf) ([], (Σ, t)) pr
    (transform (verified_erasure_pipeline_mapping econf) ([], (Σ, t)) pr) v v' ->
  let Σ' := (transform (verified_erasure_pipeline_mapping econf) ([], (Σ, t)) pr).1 in
  v' = compile_value_box (PCUICExpandLets.trans_global_env Σ) v [] /\
  firstorder_evalue_block Σ' v' /\
  ∥ ECoInductiveToInductive.firstorder_ind_value Σ' v' ∥.
Proof.
  set (pr' := precond Σ t _ HΣ expΣ expt typing Normalisation econf).
  intros obs Σ'.
  apply (verified_erasure_pipeline_mapping_obseq _ _ _ _ pr') in obs.
  subst Σ'. rewrite (verified_erasure_pipeline_mapping_transform econf Σ t pr pr').
  exact (verified_erasure_pipeline_firstorder Σ HΣ expΣ t expt axfree v i u args Normalisation
    typing fo Heval econf pr' v' obs).
Qed.

(** ** The Template-level theorem *)

Lemma obseq_compose_inv {env env' env'' term term' term'' value value' value'' : Type}
  {eval : Transform.program env term -> value -> Prop}
  {eval' : Transform.program env' term' -> value' -> Prop}
  {eval'' : Transform.program env'' term'' -> value'' -> Prop}
  (o : Transform.t env env' term term' value value' eval eval')
  (o' : Transform.t env' env'' term' term'' value' value'' eval' eval'') hpp g pr g' v v' :
  obseq (Transform.compose o o' hpp) g pr g' v v' ->
  exists v'', obseq o g pr (run o g pr) v v'' /\
    obseq o' (run o g pr) (hpp _ (correctness o _ pr)) g' v'' v'.
Proof. intros [v'' [h1 h2]]. now exists v''. Qed.

Lemma compile_value_box_ext Σ Σ' t acc :
  (forall ind, pcuic_lookup_inductive_pars Σ ind = pcuic_lookup_inductive_pars Σ' ind) ->
  compile_value_box Σ t acc = compile_value_box Σ' t acc.
Proof.
  intros hΣ. induction t in acc |- *; cbn => //.
  - rewrite IHt1 IHt2 //.
  - now rewrite hΣ.
Qed.

Lemma lookup_inductive_pars_eta (Σ : GlobalEnvMap.t) ind :
  pcuic_lookup_inductive_pars
    (PCUICExpandLets.trans_global_env (trans_global_env (eta_expand_global_env Σ))) ind =
  pcuic_lookup_inductive_pars (trans_global_env Σ) ind.
Proof.
  rewrite /pcuic_lookup_inductive_pars PCUICExpandLetsCorrectness.trans_lookup.
  have h1 := trans_global_env_lookup (eta_expand_global_env Σ) (inductive_mind ind).
  have h2 := trans_global_env_lookup Σ (inductive_mind ind).
  rewrite eta_lookup_env in h1.
  destruct (lookup_env Σ (inductive_mind ind)) as [[]|]; cbn in h1, h2.
  - destruct h1 as [? ->], h2 as [? ->]. reflexivity.
  - destruct h1 as [? ->], h2 as [? ->]. reflexivity.
  - now rewrite h1 h2.
Qed.

(** The core of the Template-level theorem, on the program computed by the first passes of the
    pipeline (eta-expansion and translation to PCUIC). *)
Lemma template_firstorder_core econf (p : Ast.Env.program) (Σm : GlobalEnvMap.t)
  (PP : Transform.program EProgram.inductives_mapping pcuic_program) pr i u args v va v' P'
  (Normalisation : forall Σ, PCUICTyping.wf_ext Σ -> PCUICSN.NormalizationIn Σ) :
  let Σ1 := trans_global (empty_ext (eta_expand_global_env Σm)) in
  GlobalEnvMap.env Σm = p.1 ->
  PP = ([], (Σ1, trans Σ1 (EtaExpand.eta_expand Σm [] p.2))) ->
  va = trans Σ1 (EtaExpand.eta_expand Σm [] v) ->
  P' = transform (verified_erasure_pipeline_mapping econf) PP pr ->
  ∥ wt_template_program p ∥ ->
  ∥ wt_pcuic_program PP.2 ∥ ->
  PCUICEtaExpand.expanded_pcuic_program PP.2 ->
  axiom_free p.1 ->
  ∥ empty_ext p.1 ;;; [] |- p.2 : mkApps (tInd i u) args ∥ ->
  firstorder_ind p.1 (firstorder_env p.1) i ->
  eval_template_program p v ->
  eval_pcuic_program PP.2 va ->
  obseq (verified_erasure_pipeline_mapping econf) PP pr P' va v' ->
  let Σ' := P'.1 in
  v' = compile_value_box (trans_global_env p.1) (trans (trans_global_env p.1) v) [] /\
  firstorder_evalue_block Σ' v' /\
  ∥ ECoInductiveToInductive.firstorder_ind_value Σ' v' ∥.
Proof.
  intros Σ1 henv -> -> -> [[wfp [T0 hT0]]] [[wfΣ1 [T1 hT1]]] [expΣ1 expt1] hax [hty] hfo [hev]
    [hev1] obs Σ'.
  cbn [fst snd] in *.
  have wfp1 : wf p.1 by apply wfp.
  (* The source program and its value, in the PCUIC translation of the source environment *)
  set (Σ0 := trans_global (empty_ext p.1)).
  have wfΣ0 : PCUICTyping.wf Σ0 by apply template_to_pcuic_env.
  have hty0 := template_to_pcuic_typing (Σ := empty_ext p.1) [] _ _ wfp1 hty.
  change (PCUICTyping.typing Σ0 [] (trans (trans_global_env p.1) p.2)
    (trans (trans_global_env p.1) (mkApps (tInd i u) args))) in hty0.
  rewrite trans_mkApps in hty0. cbn [trans] in hty0.
  have [hwft _] := TypingWf.typing_wf (empty_ext p.1) wfp1 _ _ _ hty.
  have hev0 := trans_wcbvEval (wfΣ := wfp1) _ _ wfΣ0 hwft hev.
  have htyv0 := @PCUICClassification.subject_reduction_eval _ Σ0 wfΣ0 _ _ _ hty0 hev0.
  have hfo0 := trans_firstorder_ind p.1 Monomorphic_ctx i hfo.
  have htree0 : pcuic_fo_tree Σ0 (trans (trans_global_env p.1) v).
  { eapply pcuic_fo_tree_spec; [exact wfΣ0|exact htyv0| |exact hfo0].
    eapply PCUICWcbvEval.eval_to_value; exact hev0. }
  (* The value is a tree of fully applied constructors, unchanged by eta-expansion *)
  have hwfv := eval_wf (wfΣ := wfp1) hwft hev.
  have htree := untrans_constructor_tree _ _ _ hwfv htree0.
  clear hT0 hty hev hwft.
  have htreem : template_constructor_tree Σm v by rewrite henv.
  have heta := eta_expand_constructor_tree Σm v htreem.
  rewrite heta in hev1 obs.
  have htree1 := eta_constructor_tree Σm v htreem.
  have [ind [c [ui [argsv [mdecl [idecl [cdecl [heqv [hd hlen]]]]]]]]] :
    exists ind c ui argsv mdecl idecl cdecl, v = mkApps (tConstruct ind c ui) argsv /\
      declared_constructor_gen (lookup_env (eta_expand_global_env Σm)) (ind, c)
        mdecl idecl cdecl /\
      #|argsv| = ind_npars mdecl + context_assumptions (cstr_args cdecl).
  { destruct htree1 as [ind c ui argsv mdecl idecl cdecl hd hlen _].
    now exists ind, c, ui, argsv, mdecl, idecl, cdecl. }
  have hind : ind = i.
  { move: htyv0. rewrite heqv trans_mkApps_tConstruct => htyv0.
    now destruct
      (@PCUICInductiveInversion.Construct_Ind_ind_eq' _ Σ0 wfΣ0 _ _ _ _ _ _ _ _ htyv0)
      as [? [? [? [? [[[[[-> _] _] _] _] _]]]]]. }
  subst ind.
  (* The eta-expanded and translated program is typed at the inductive type *)
  destruct (trans_declared_constructor _ _ _ _ _ _ hd) as [Σ'' hd1].
  have hva : trans Σ1 v = PCUICAst.mkApps (PCUICAst.tConstruct i c ui) (map (trans Σ1) argsv).
  { now rewrite heqv trans_mkApps_tConstruct. }
  have htyva := @PCUICClassification.subject_reduction_eval _ Σ1 wfΣ1.1 _ _ _ hT1 hev1.
  rewrite hva in htyva.
  have hlen1 : #|map (trans Σ1) argsv| =
    PE.ind_npars (trans_minductive_body Σ'' mdecl) +
    PE.context_assumptions (PE.cstr_args (trans_constructor_body Σ'' cdecl)).
  { cbn. rewrite length_map hlen context_assumptions_trans_local //. }
  have [u' [args' hred]] := typing_full_constructor_red (Σ := Σ1) (wfΣ := wfΣ1.1)
    (PCUICTyping.declared_constructor_from_gen hd1) hlen1 htyva.
  have hty1 := @PCUICSR.type_reduction _ Σ1 wfΣ1.1 _ _ _ _ hT1 hred.
  (* First-order inductive and absence of axioms *)
  have hfo1 : PCUICFirstorder.firstorder_ind Σ1 (PCUICFirstorder.firstorder_env Σ1) i.
  { apply trans_firstorder_ind. rewrite eta_firstorder_ind henv //. }
  have hax1 : PCUICClassification.axiom_free Σ1.
  { apply trans_axiom_free, eta_axiom_free. now rewrite henv. }
  destruct (verified_erasure_pipeline_mapping_firstorder Σ1 wfΣ1 expΣ1 _ expt1 hax1 _ i u' args'
    Normalisation (sq hty1) hfo1 (sq hev1) econf pr v' obs) as [-> rest].
  split => //.
  rewrite (trans_constructor_tree_env _ Σ1 (trans_global_env p.1) _ htree).
  apply compile_value_box_ext => ind.
  rewrite lookup_inductive_pars_eta henv //.
Qed.

Theorem erasure_pipeline_mapping_firstorder econf (p : Ast.Env.program) pr i u args v v'
  (Normalisation : forall Σ, PCUICTyping.wf_ext Σ -> PCUICSN.NormalizationIn Σ) :
  axiom_free p.1 ->
  ∥ empty_ext p.1 ;;; [] |- p.2 : mkApps (tInd i u) args ∥ ->
  firstorder_ind p.1 (firstorder_env p.1) i ->
  eval_template_program_mapping ([], p) v ->
  obseq (erasure_pipeline_mapping econf) ([], p) pr
    (run (erasure_pipeline_mapping econf) ([], p) pr) v v' ->
  let Σ' := (run (erasure_pipeline_mapping econf) ([], p) pr).1 in
  v' = compile_value_box (trans_global_env p.1) (trans (trans_global_env p.1) v) [] /\
  firstorder_evalue_block Σ' v' /\
  ∥ ECoInductiveToInductive.firstorder_ind_value Σ' v' ∥.
Proof.
  intros hax hty hfo hev obs Σ'.
  have hpres := preservation pre_erasure_pipeline_mapping ([], p) v pr hev.
  have hpost := correctness pre_erasure_pipeline_mapping ([], p) pr.
  have hwt : ∥ wt_template_program p ∥ := proj1 (proj2 pr).
  unfold erasure_pipeline_mapping in obs, Σ'.
  apply obseq_compose_inv in obs as (va & obspre & obs).
  destruct hpres as [va' [hevp obspre']].
  set (PP := run pre_erasure_pipeline_mapping ([], p) pr) in *.
  unfold pre_erasure_pipeline_mapping in obspre, obspre'.
  apply obseq_compose_inv in obspre as (vb & obsb & obspre).
  apply obseq_compose_inv in obspre' as (vb' & obsb' & obspre').
  apply obseq_compose_inv in obsb as (vc & obsc & obsb).
  apply obseq_compose_inv in obsb' as (vc' & obsc' & obsb').
  cbn [obseq build_template_program_env_mapping eta_expand_mapping template_to_pcuic_mapping
    build_template_program_env Erasure.eta_expand template_to_pcuic_transform]
    in obsc, obsb, obspre, obsc', obsb', obspre'.
  subst.
  match type of obs with context [EtaExpand.eta_expand ?S [] _] => set (Σm := S) in * end.
  match type of obs with
  | obseq _ _ ?prx ?P' ?va _ =>
    apply (template_firstorder_core econf p Σm PP prx i u args vc' va v' P' Normalisation)
  end; first [assumption | reflexivity | apply hpost].
Qed.


(** * The λ□ passes on trees of constructors *)

(** Whether constructor [c] of [ind] is unboxed by [EUnboxing] in the erased environment [Σ] *)
Definition is_unboxable_ctor (Σ : EAst.global_context) (ind : inductive) (c : nat) : bool :=
  match c with
  | O =>
    match EGlobalEnv.lookup_constructor Σ ind 0%nat with
    | Some (_, idecl, cdecl) => EUnboxing.unboxable idecl cdecl
    | None => false
    end
  | S _ => false
  end.

(** [EUnboxing.unbox], on trees of constructors *)
Fixpoint unbox_fo (Σ : EAst.global_context) (t : EAst.term) : EAst.term :=
  match t with
  | EAst.tConstruct ind c args =>
    if is_unboxable_ctor Σ ind c then
      match args with
      | [a] => unbox_fo Σ a
      | _ => EAst.tConstruct ind c (map (unbox_fo Σ) args)
      end
    else EAst.tConstruct ind c (map (unbox_fo Σ) args)
  | _ => t
  end.

Lemma unbox_fo_constr Σ ind c args :
  ~~ (is_unboxable_ctor Σ ind c && (#|args| =? 1)%nat) ->
  unbox_fo Σ (EAst.tConstruct ind c args) = EAst.tConstruct ind c (map (unbox_fo Σ) args).
Proof.
  cbn. destruct is_unboxable_ctor => //. now destruct args as [|? []].
Qed.

Lemma map_id_tree (f : EAst.term -> EAst.term) l :
  Forall (fun x => f x = x) l -> map f l = l.
Proof. induction 1; cbn; congruence. Qed.

Lemma consts_to_values_tree Σw t :
  firstorder_evalue_block Σw t -> EConstantsToValues.consts_to_values t = t.
Proof.
  induction 1 using firstorder_evalue_block_elim. cbn. f_equal. now apply map_id_tree.
Qed.

Lemma implement_lazy_force_tree Σw t :
  firstorder_evalue_block Σw t -> EImplementLazyForce.implement_lazy_force t = t.
Proof.
  induction 1 using firstorder_evalue_block_elim. simp implement_lazy_force. rewrite ?map_InP_spec.
  f_equal. now apply map_id_tree.
Qed.

Lemma implement_box_tree Σw t :
  firstorder_evalue_block Σw t -> EImplementBox.implement_box t = t.
Proof.
  induction 1 using firstorder_evalue_block_elim. simp implement_box. rewrite ?map_InP_spec.
  f_equal. now apply map_id_tree.
Qed.

Lemma coinductive_trans_tree (Σ : EEnvMap.GlobalContextMap.t) t :
  ECoInductiveToInductive.firstorder_ind_value (EEnvMap.GlobalContextMap.global_decls Σ) t ->
  ECoInductiveToInductive.trans Σ t = t.
Proof.
  revert t. apply: ECoInductiveToInductive.firstorder_ind_value_rect => ind c args hco _ IH.
  cbn. rewrite EEnvMap.GlobalContextMap.is_coind_spec hco map_id_tree //.
  now apply All_Forall.
Qed.

Lemma unbox_tree (Σ : EEnvMap.GlobalContextMap.t) Σw t :
  firstorder_evalue_block Σw t ->
  EUnboxing.unbox Σ t = unbox_fo (EEnvMap.GlobalContextMap.global_decls Σ) t.
Proof.
  induction 1 using firstorder_evalue_block_elim. rename i into ind, n into c. simp unbox.
  have hu : EUnboxing.is_unboxable Σ ind c =
    is_unboxable_ctor (EEnvMap.GlobalContextMap.global_decls Σ) ind c.
  { destruct c; simp is_unboxable => //=. rewrite EEnvMap.GlobalContextMap.lookup_constructor_spec.
    destruct EGlobalEnv.lookup_constructor as [[[]]|] => //. }
  destruct (PCUICSafeReduce.inspect (EUnboxing.is_unboxable Σ ind c)) as [[] hunb].
  all: have e := eq_trans hunb hu; cbn [unbox_fo]; rewrite -e.
  all: have hmap : map (EUnboxing.unbox Σ) args =
    map (unbox_fo (EEnvMap.GlobalContextMap.global_decls Σ)) args
    by (clear -H1; induction H1; cbn; congruence).
  - destruct args as [|a [|a' args]]; simp unbox; rewrite ?hmap //. now inversion H1.
  - simp unbox. now rewrite hmap.
Qed.

(** The constructor environment seen by [is_unboxable_ctor] is preserved by maps on
    declarations that keep the bodies of inductive declarations *)
Lemma is_unboxable_ctor_map (f : EAst.global_decl -> EAst.global_decl) Σ ind c :
  (forall d, match d, f d with
    | EAst.InductiveDecl m, EAst.InductiveDecl m' => EAst.ind_bodies m' = EAst.ind_bodies m
    | EAst.ConstantDecl _, EAst.ConstantDecl _ => True
    | _, _ => False
    end) ->
  is_unboxable_ctor (map (on_snd f) Σ) ind c = is_unboxable_ctor Σ ind c.
Proof.
  intros hf. destruct c as [|c] => //. cbn.
  unfold EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive.
  rewrite ECoInductiveToInductive.lookup_env_map_snd.
  destruct EGlobalEnv.lookup_env as [d|] => //=.
  specialize (hf d). destruct d as [cb|m]; destruct (f _) as [cb'|m'] => //=.
  rewrite hf. destruct nth_error => //=. destruct EAst.ind_ctors => //.
Qed.

Lemma unbox_fo_tree Σw Σ t :
  firstorder_evalue_block Σw t -> firstorder_evalue_block Σw (unbox_fo Σ t).
Proof.
  induction 1 using firstorder_evalue_block_elim. cbn.
  have hmap : Forall (firstorder_evalue_block Σw) (map (unbox_fo Σ) args).
  { clear -H1. induction H1; constructor; auto. }
  have hcstr : firstorder_evalue_block Σw (EAst.tConstruct i n (map (unbox_fo Σ) args))
    by constructor; rewrite ?length_map.
  destruct is_unboxable_ctor; [destruct args as [|a [|]]|] => //.
  now inversion H1.
Qed.

Lemma unbox_fo_ext Σ Σ' Σw t :
  (forall ind c, is_unboxable_ctor Σ ind c = is_unboxable_ctor Σ' ind c) ->
  firstorder_evalue_block Σw t -> unbox_fo Σ t = unbox_fo Σ' t.
Proof.
  intros hΣ. induction 1 using firstorder_evalue_block_elim. cbn. rewrite hΣ.
  have -> : map (unbox_fo Σ) args = map (unbox_fo Σ') args.
  { clear -H1. induction H1; cbn; congruence. }
  destruct is_unboxable_ctor => //. destruct args as [|a [|]] => //. now inversion H1.
Qed.

Lemma is_unboxable_ctor_consts_to_values Σ ind c :
  is_unboxable_ctor (EConstantsToValues.consts_to_values_env Σ) ind c = is_unboxable_ctor Σ ind c.
Proof.
  apply (is_unboxable_ctor_map EConstantsToValues.consts_to_values_global_decl). by case.
Qed.
