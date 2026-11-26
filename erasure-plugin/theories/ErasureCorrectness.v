(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaRocq.PCUIC Require Import PCUICNormal.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureCorrectness EPretty Extract EProgram EConstructorsAsBlocks.
From MetaRocq.Erasure Require Import EWcbvEvalNamed ErasureFunction ErasureFunctionProperties.
From MetaRocq.Erasure Require Import EFirstorder.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From MetaRocq.ErasurePlugin.transforms Require Import GuardedToUnguardedFix
  RebuildWfEnv RemoveParams RemoveMatchOnBox InlineProjections
  ConstructorsAsBlocks CoInductiveToInductive PushForce ReorderCstrs Unboxing
  ConstsToValues Inlining ImplementBox ImplementLazyForce.
Import EProgram PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Common.Transform.Transform.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

Import EWcbvEval.

Lemma transform_compose_assoc
  {env env' env'' env''' term term' term'' term''' value value' value'' value''' : Type}
  {eval eval' eval'' eval'''}
  (o : t env env' term term' value value' eval eval')
  (o' : t env' env'' term' term'' value' value'' eval' eval'')
  (o'' : t env'' env''' term'' term''' value'' value''' eval'' eval''')
  (prec : forall p, post o p -> pre o' p)
  (prec' : forall p, post o' p -> pre o'' p) :
  forall x p1,
    transform (compose o (compose o' o'' prec') prec) x p1 =
    transform (compose (compose o o' prec) o'' prec') x p1.
Proof.
  cbn. intros.
  unfold run, time.
  f_equal. f_equal.
  apply proof_irrelevance.
Qed.

Lemma obseq_compose_assoc
  {env env' env'' env''' term term' term'' term''' value value' value'' value''' : Type}
  {eval eval' eval'' eval'''}
  (o : t env env' term term' value value' eval eval')
  (o' : t env' env'' term' term'' value' value'' eval' eval'')
  (o'' : t env'' env''' term'' term''' value'' value''' eval'' eval''')
  (prec : forall p, post o p -> pre o' p)
  (prec' : forall p, post o' p -> pre o'' p) :
  forall x p1 p2 v1 v2, obseq (compose o (compose o' o'' prec') prec) x p1 p2 v1 v2 <->
      obseq (compose (compose o o' prec) o'' prec') x p1 p2 v1 v2.
Proof.
  cbn. intros.
  unfold run, time.
  intros. firstorder. exists x1. split.
  exists x0. split => //.
  assert (correctness o' (transform o x p1)
  (prec (transform o x p1) (correctness o x p1)) =
  (Transform.Transform.compose_obligation_1 o o' prec x p1)). apply proof_irrelevance.
  now rewrite -H.

  exists x1. split => //.
  exists x0. split => //.
  assert (correctness o' (transform o x p1)
  (prec (transform o x p1) (correctness o x p1)) =
  (Transform.Transform.compose_obligation_1 o o' prec x p1)). apply proof_irrelevance.
  now rewrite H.
Qed.

(* Lemma obseq_compose_id
  {env env' term term' value value' : Type}
  {eval eval'}
  (o : t env env' term term' value term' eval eval')
  (o' : self_transform env' term' eval' eval')
  (prec : forall p, post o p -> pre o' p) :
  forall x p1 p2 v1 v2, obseq (compose o (optional_self_transform false o') prec) x p1 p2 v1 v2 <->
      obseq o x p1 p2 v1 v2.
Proof.
  cbn. intros.
  unfold run, time.
  intros. firstorder. subst v2. exists x1. split.
  exists x0. split => //.
  assert (correctness o' (transform o x p1)
  (prec (transform o x p1) (correctness o x p1)) =
  (Transform.Transform.compose_obligation_1 o o' prec x p1)). apply proof_irrelevance.
  now rewrite -H.

  exists x1. split => //.
  exists x0. split => //.
  assert (correctness o' (transform o x p1)
  (prec (transform o x p1) (correctness o x p1)) =
  (Transform.Transform.compose_obligation_1 o o' prec x p1)). apply proof_irrelevance.
  now rewrite H.
Qed. *)

Import EEnvMap.GlobalContextMap.

Ltac destruct_compose :=
  match goal with
  |- context [ transform (compose ?x ?y ?pre) ?p ?pre' ] =>
    let pre'' := fresh in
    let H := fresh in
    destruct (transform_compose x y pre p pre') as [pre'' H];
    rewrite H; clear H; revert pre''
    (* rewrite H'; clear H'; *)
    (* revert pre'' *)
  end.

Ltac destruct_compose_no_clear :=
    match goal with
    |- context [ transform (compose ?x ?y ?pre) ?p ?pre' ] =>
      let pre'' := fresh in
      let H := fresh in
      destruct (transform_compose x y pre p pre') as [pre'' H];
      rewrite H; revert pre'' H
    end.

Lemma rebuild_wf_env_irr {efl : EWellformed.EEnvFlags} p wf p' wf' :
  p.1 = p'.1 ->
  (rebuild_wf_env p wf).1 = (rebuild_wf_env p' wf').1.
Proof.
  destruct p as [], p' as [].
  cbn. intros <-.
  unfold make. f_equal. apply proof_irrelevance.
Qed.


From MetaRocq.Erasure Require Import Erasure Extract ErasureFunction.
From MetaRocq.PCUIC Require Import PCUICTyping.

Lemma firstorder_value_cofix_lambdas {cf : checker_flags} Σ Γ v :
  PCUICFirstorder.firstorder_value Σ Γ v -> cofix_lambdas v.
Proof.
  revert v.
  apply: (PCUICFirstorder.firstorder_value_inds Σ Γ
    (fun v => cofix_lambdas v)) => i n ui u args pandi _ _ IH _.
  rewrite cofix_lambdas_mkApps /=. now apply forallb_Forall.
Qed.

Lemma extends_erase_pcuic_program (efl := EWcbvEval.default_wcbv_flags) {guard : abstract_guard_impl} (Σ : global_env_ext_map) t v nin nin' nin0 nin0'
  wf wf' ty ty' i u args :
  cofix_lambdas_env Σ -> cofix_lambdas t ->
  PCUICWcbvEval.eval Σ t v ->
  axiom_free Σ ->
  Σ ;;; [] |- t : PCUICAst.mkApps (PCUICAst.tInd i u) args ->
  @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i ->
  let pt := @erase_pcuic_program guard (Σ, t) nin0 nin0' wf' ty' in
  let pv := @erase_pcuic_program guard (Σ, v) nin nin' wf ty in
  EGlobalEnv.extends pv.1 pt.1 /\ ∥ eval pt.1 pt.2 pv.2 ∥ /\ firstorder_evalue pt.1 pv.2.
Proof.
  intros hcld hclt ev axf ht fo.
  unfold cofix_lambdas_env in hcld.
  cbn -[erase_pcuic_program].
  unfold erase_pcuic_program.
  set (prf0 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (prf1 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (prf2 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (prf3 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (prf4 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (prf5 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (prf6 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (env' := build_wf_env_from_env _ _).
  set (env := build_wf_env_from_env _ _).
  set (X := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
  set (X' := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
  unfold erase_global_fast.
  set (prf7 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (et := ErasureFunction.erase _ _ _ _ _).
  set (et' := ErasureFunction.erase _ _ _ _ _).
  destruct Σ as [Σ ext].
  cbn -[et et' PCUICWfEnv.abstract_make_wf_env_ext] in *.
  unshelve (epose proof erase_global_deps_fast_erase_global_deps as [norm eq];
    erewrite eq).
  { cbn. now intros ? ->. }
  unshelve (epose proof erase_global_deps_fast_erase_global_deps as [norm' eq'];
  erewrite eq').
  { cbn. now intros ? ->. }
  set (prf := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)). cbn in prf.
  rewrite (ErasureFunction.erase_global_deps_irr optimized_abstract_env_impl (EAstUtils.term_global_deps et) env' env _ prf prf).
  { cbn. now intros ? ? -> ->. }
  clearbody prf0 prf1 prf2 prf3 prf4 prf5 prf6 prf7.
  epose proof (erase_correct_strong optimized_abstract_env_impl (v:=v) env ext prf2
    (PCUICAst.PCUICEnvironment.declarations Σ) norm' prf hcld hclt prf6 X
    eq_refl axf ht fo).
  pose proof wf as [].
  forward H by unshelve (eapply PCUICClassification.wcbveval_red; tea).
  forward H. {
    intros [? hr].
    eapply PCUICNormalization.firstorder_value_irred; tea. cbn.
    eapply PCUICFirstorder.firstorder_value_spec; tea. apply X0. constructor.
    eapply PCUICClassification.subject_reduction_eval; tea.
    eapply PCUICWcbvEval.eval_to_value; tea. }
  destruct H as [wt' [[] hfo]].
  split => //.
  eapply (erase_global_deps_eval optimized_abstract_env_impl env env' ext).
  exact hcld.
  unshelve erewrite (ErasureFunction.erase_irrel_global_env (X_type:=optimized_abstract_env_impl) (t:=v)); tea.
  red. intros. split; reflexivity.
  split => //.
  sq. unfold et', et.
  unshelve erewrite (ErasureFunction.erase_irrel_global_env (X_type:=optimized_abstract_env_impl) (t:=v)); tea.
  red. intros. split; reflexivity.
  subst et et' X X'.
  unshelve erewrite (ErasureFunction.erase_irrel_global_env (X_type:=optimized_abstract_env_impl) (t:=v)); tea.
  red. intros. split; reflexivity.
Qed.

Definition pcuic_lookup_inductive_pars Σ ind :=
  match PCUICAst.PCUICEnvironment.lookup_env Σ (Kernames.inductive_mind ind) with
  | Some (PCUICAst.PCUICEnvironment.InductiveDecl mdecl) => Some mdecl.(PCUICAst.PCUICEnvironment.ind_npars)
  | _ => None
  end.

Fixpoint compile_value_box Σ (t : PCUICAst.term) (acc : list EAst.term) : EAst.term :=
  match t with
  | PCUICAst.tApp f a => compile_value_box Σ f (compile_value_box Σ a [] :: acc)
  | PCUICAst.tConstruct i n _ =>
    match pcuic_lookup_inductive_pars Σ i with
    | Some npars => EAst.tConstruct i n (skipn npars acc)
    | None => EAst.tVar "error"
    end
  | _ => EAst.tVar "error"
  end.

From Equations Require Import Equations.

Import EWcbvEval.
Arguments erase_global_deps _ _ _ _ _ : clear implicits.
Arguments erase_global_deps_fast _ _ _ _ _ _ : clear implicits.

Section PCUICProof.
  Import PCUICAst.PCUICEnvironment.

  Definition erase_preserves_inductives Σ Σ' :=
    (forall kn decl decl', EGlobalEnv.lookup_env Σ' kn = Some (EAst.InductiveDecl decl) ->
    lookup_env Σ kn = Some (PCUICAst.PCUICEnvironment.InductiveDecl decl') ->
    decl = erase_mutual_inductive_body decl').

  Definition erase_decl_equal cmp decl decl' :=
    match decl, decl' with
        EAst.InductiveDecl decl , InductiveDecl decl' => decl = cmp decl'
      | EAst.ConstantDecl _ , ConstantDecl _ => True
      | _ , _ => False
    end.

  Lemma lookup_env_in_erase_global_deps X_type X deps decls kn normalization_in prf decl :
    EnvMap.EnvMap.fresh_globals decls ->
    EGlobalEnv.lookup_env (erase_global_deps X_type deps X decls normalization_in prf).1 kn = Some decl ->
    exists decl', lookup_global decls kn = Some decl' /\
                  erase_decl_equal erase_mutual_inductive_body decl decl'.
  Proof.
    induction decls in deps, X, normalization_in, prf |- *; cbn [erase_global_deps] => //.
    destruct a => //. destruct g => //.
    - case: (knset_mem_spec k deps) => // hdeps.
      cbn [EGlobalEnv.lookup_env fst lookup_env lookup_global].
      { destruct (eqb_spec kn k) => //.
        intro hl; depelim hl; cbn. intro e; noconf e.
        eexists; split; eauto. cbn; eauto.
        intros hl. cbn. eapply IHdecls. now depelim hl. }
      { intros hl. depelim hl.
        intros hl'.
        eapply IHdecls in hl. destruct hl.
        exists x.
        cbn.
        destruct (eqb_spec kn k) => //. subst k.
        destruct H0.
        now eapply PCUICWeakeningEnv.lookup_global_Some_fresh in H0.
        exact hl'. }
    - intros hf; depelim hf.
      case: (knset_mem_spec k deps) => // hdeps.
      cbn [EGlobalEnv.lookup_env fst lookup_env lookup_global].
      { destruct (eqb_spec kn k) => //; cbn.
        intros hl. noconf hl. subst k. eexists; split; cbn; eauto. cbn; eauto.
        intros hl'. eapply IHdecls => //. tea. }
      { intros hl'. eapply IHdecls in hf; tea. destruct hf.
        exists x.
        cbn.
        destruct (eqb_spec kn k) => //. subst k.
        destruct H0.
        now eapply PCUICWeakeningEnv.lookup_global_Some_fresh in H0. }
    Qed.

  Lemma erase_tranform_firstorder (wfl := default_wcbv_flags)
    {p : Transform.program global_env_ext_map PCUICAst.term} {pr v i u args}
    {normalization_in : PCUICSN.NormalizationIn p.1} :
    forall (wt : p.1 ;;; [] |- p.2 : PCUICAst.mkApps (PCUICAst.tInd i u) args),
    axiom_free p.1 ->
    @PCUICFirstorder.firstorder_ind p.1 (PCUICFirstorder.firstorder_env p.1) i ->
    PCUICWcbvEval.eval p.1 p.2 v ->
    forall ep, transform erase_transform p pr = ep ->
      erase_preserves_inductives p.1 ep.1 /\
      ∥ EWcbvEval.eval ep.1 ep.2 (compile_value_erase v []) ∥ /\
      firstorder_evalue ep.1 (compile_value_erase v []).
  Proof.
    destruct p as [Σ t]; cbn.
    intros ht ax fo ev [Σe te]; cbn.
    unfold erase_program, erase_pcuic_program.
    set (obl := ETransform.erase_pcuic_program_obligation_6 _ _ _ _ _ _).
    move: obl.
    rewrite /erase_global_fast.
    set (prf0 := fun (Σ0 : global_env) => _).
    set (prf1 := fun (Σ0 : global_env_ext) => _).
    set (prf2 := fun (Σ0 : global_env_ext) => _).
    set (prf3 := fun (Σ0 : global_env) => _).
    set (prf4 := fun n (H : n < _) => _).
    set (gext := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
    set (et := erase _ _ _ _ _).
    set (g := build_wf_env_from_env _ _).
    assert (hprefix: forall Σ0 : global_env, PCUICWfEnv.abstract_env_rel g Σ0 -> declarations Σ0 = declarations g).
    { intros Σ' eq; cbn in eq. rewrite eq; reflexivity. }
    destruct (@erase_global_deps_fast_erase_global_deps (EAstUtils.term_global_deps et) optimized_abstract_env_impl g
      (declarations Σ) prf4 prf3 hprefix) as [nin' eq].
    cbn [fst snd].
    rewrite eq.
    set (eg := erase_global_deps _ _ _ _ _ _).
    intros obl.
    have hcld := expanded_global_env_cofix_lambdas _ (proj1 (proj1 (proj2 pr))).
    have hclt := expanded_cofix_lambdas _ _ _ (proj2 (proj1 (proj2 pr))).
    epose proof (@erase_correct_strong optimized_abstract_env_impl g Σ.2 prf0
      t v i u args _ _ hprefix prf1 hcld hclt prf2 Σ eq_refl ax ht fo).
    pose proof (proj1 pr) as [[]].
    forward H. eapply PCUICClassification.wcbveval_red; tea.
    assert (PCUICFirstorder.firstorder_value Σ [] v).
    { eapply PCUICFirstorder.firstorder_value_spec; tea. apply w. constructor.
      eapply PCUICClassification.subject_reduction_eval; tea.
      eapply PCUICWcbvEval.eval_to_value; tea. }
    forward H.
    { intros [v' redv]. eapply PCUICNormalization.firstorder_value_irred; tea. }
    destruct H as [wt' [ev' fo']].
    assert (erase optimized_abstract_env_impl (PCUICWfEnv.abstract_make_wf_env_ext (X_type:=optimized_abstract_env_impl) g Σ.2 prf0) [] v wt' =
      compile_value_erase v []).
    { clear -H0.
      clearbody prf0 prf1.
      destruct pr as [].
      destruct s as [[]].
      epose proof (erases_erase (X_type := optimized_abstract_env_impl) wt' _
        eq_refl (firstorder_value_cofix_lambdas _ _ _ H0)).
      eapply erases_firstorder' in H; eauto. }
    rewrite H in ev', fo'.
    intros [=]; subst te Σe.
    split => //.
    cbn. subst eg.
    intros kn decl decl' hl hl'.
    eapply lookup_env_in_erase_global_deps in hl as [decl'' [hl eq']].
    rewrite /lookup_env hl in hl'. now noconf hl'.
    eapply wf_fresh_globals, w.
  Qed.

  Lemma erase_transform_preserves_inductives (p : pcuic_program) pr :
    erase_preserves_inductives p.1 (transform erase_transform p pr).1.
  Proof.
    destruct p as [Σ t]. cbn.
    unfold erase_program, erase_pcuic_program. cbn [fst snd].
    rewrite /erase_global_fast.
    match goal with
    |- context [erase_global_deps_fast ?deps ?X_type ?X ?decls
        ?normalization_in ?hprefix ] =>
      have heq := @erase_global_deps_fast_erase_global_deps deps X_type X
        decls normalization_in hprefix
    end; cbn in heq.
    specialize (heq (fun Σ eq => f_equal declarations eq)).
    destruct heq as [nin' eq]; rewrite eq; clear eq.
    intros kn decl decl' hl hl'.
    eapply lookup_env_in_erase_global_deps in hl as [decl'' [hl eq']].
    rewrite /lookup_env hl in hl'. now noconf hl'.
    destruct pr as [[[w ?]] ?]. eapply wf_fresh_globals, w.
  Qed.
End PCUICProof.
Lemma erase_transform_fo_gen (p : pcuic_program) pr :
  PCUICFirstorder.firstorder_value p.1 [] p.2 ->
  forall ep, transform erase_transform p pr = ep ->
  ep.2 = compile_value_erase p.2 [].
Proof.
  destruct p as [Σ t]. cbn.
  intros hev ep <-. move: hev pr.
  unfold erase_program, erase_pcuic_program; cbn -[erase PCUICWfEnv.abstract_make_wf_env_ext].
  intros fo pr.
  set (prf0 := fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _).
  set (prf1 := fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _).
  clearbody prf0 prf1.
  destruct pr as [].
  destruct s as [[]].
  epose proof (erases_erase (X_type := optimized_abstract_env_impl) prf1 _
    eq_refl (firstorder_value_cofix_lambdas _ _ _ fo)).
  eapply erases_firstorder' in H; eauto.
Qed.

Lemma erase_transform_fo (p : pcuic_program) pr :
  PCUICFirstorder.firstorder_value p.1 [] p.2 ->
  transform erase_transform p pr = ((transform erase_transform p pr).1, compile_value_erase p.2 []).
Proof.
  intros fo.
  set (tr := transform _ _ _).
  change tr with (tr.1, tr.2). f_equal.
  eapply erase_transform_fo_gen; tea. reflexivity.
Qed.

Import MetaRocq.Common.Transform.
From Stdlib Require Import Morphisms.


Inductive is_eta_fix_application Σ : EAst.term -> Prop :=
| mk_is_eta_fix_application f a : EEtaExpandedFix.isEtaExp Σ [] f -> is_eta_fix_application Σ (EAst.tApp f a).
Derive Signature for is_eta_fix_application.

Inductive is_eta_application Σ : EAst.term -> Prop :=
| mk_is_eta_application f a : EEtaExpanded.isEtaExp Σ f -> is_eta_application Σ (EAst.tApp f a).
Derive Signature for is_eta_application.

Definition compile_app f t :=
  match t with
  | EAst.tApp fn a => EAst.tApp (f fn) (f a)
  | _ => f t
  end.
  Fixpoint forallbi {A} (f : nat -> A -> bool) n l :=
    match l with
    | [] => true
    | hd :: tl => f n hd && forallbi f (S n) tl
    end.

(* TODO Move, in optimizeCorrectness as well *)
Lemma forallbi_Alli {A} (f : nat -> A -> bool) n l :
  Alli f n l <~> forallbi f n l.
Proof.
  split.
  - induction 1; cbn; auto.
  - induction l in n |- *; cbn; auto.
    * constructor.
    * move/andP => [] hf hl. constructor; eauto.
Qed.

Lemma forallb_mapi_forallbi {A B} p (f : nat -> A -> B) n l :
  forallb p (mapi_rec f l n) <~> forallbi (fun i x => p (f i x)) n l.
Proof.
  split.
  - induction l in n |- *; cbn; auto. move/andP => [] ->; eauto.
  - induction l in n |- *; cbn; auto. move/andP => [] ->; eauto.
Qed.

Lemma forallb_forallbi {A} (f : A -> bool) l :
  forallb f l = forallbi (fun i => f) 0 l.
Proof.
  generalize 0.
  induction l; simpl; auto => n. bool_congr. eauto.
Qed.

Lemma forallbi_impl {A} (f g : nat -> A -> bool) n l :
  (forall n x, f n x -> g n x) ->
  forallbi f n l -> forallbi g n l.
Proof.
  intros hfg.
  induction l in n |- *; simpl; auto; move/andP => [] /hfg -> //=; eauto.
Qed.


Section PCUICInv.
  Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICWcbvEval PCUICWellScopedCumulativity PCUICEtaExpand.
  Import PCUIC.PCUICConversion PCUICSigmaCalculus PCUICExpandLetsCorrectness.

  Definition is_vdef (d : context_decl) := match d with {| decl_body := None |} => false | _ => true end.

  Lemma red_vdefs_tProd {Σ Γ ctx concl na dom codom} :
      wf_ext Σ ->
      forallb is_vdef ctx ->
      Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx concl ⇝ tProd na dom codom ->
      Σ ;;; Γ ⊢ expand_lets ctx concl ⇝ tProd na dom codom.
  Proof.
    intros wfΣ. revert ctx concl. apply: PCUICInduction.ctx_length_rev_ind => [concl|d ctx IH concl].
    - rewrite expand_lets_nil //.
    - rewrite forallb_app /= andb_true_r => /andP[] hctx hdef.
      rewrite it_mkProd_or_LetIn_app. destruct d as [na' [b|] ty] => //=.
      cbn. rewrite expand_lets_vdef.
      move/(invert_red_letin (cf := extraction_checker_flags) (wfΣ := wfΣ)) => [[d' [ty' [b' []]]]|] //.
      rewrite [T.subst10 _ _]PCUICLiftSubst.subst_it_mkProd_or_LetIn Nat.add_0_r.
      eapply IH. now len. clear -hctx.
      rewrite subst_context_alt.
      { rewrite forallb_mapi_forallbi. rewrite forallb_forallbi in hctx.
        eapply forallbi_impl; tea.
        intros n [na [b'|] ty]; cbn; eauto. auto. }
  Qed.

  (* Constructors are impossible as they are eta expanded. Primitives can't have type Prod.
     Fix and CoFix must be unreducible (that's the value hypothesis). *)
  Lemma closed_prod_type {Σ : global_env_ext} {f na A B} {wfΣ : wf_ext Σ}
    (wf : Σ ;;; [] |- f : PCUICAst.tProd na A B) :
    value Σ f ->
    expanded Σ [] f ->
    match decompose_app f with
    | (tLambda na ty b, []) => True
    | (tInd i u, args) => True
    | (tFix mfix idx, args) => True
    | (tCoFix mfix idx, args) => True
    | _ => False
    end.
  Proof.
    induction 1 using value_values_ind.
    - destruct t0 => //.
      + eapply inversion_Sort in wf as [? []]; eauto.
        now eapply ws_cumul_pb_Sort_Prod_inv in w0.
      + eapply inversion_Prod in wf as [? [? [? []]]]; eauto.
        now eapply ws_cumul_pb_Sort_Prod_inv in w.
      +(* Constructor case: due to eta expansion *)
        cbn. intros exp. depelim exp.
        now rewrite nth_error_nil in H0.
        destruct f; solve_discr. noconf H2. now cbn in H0.
        solve_discr. solve_discr.
        cbn in H1. assert (context_assumptions (cstr_args cdecl) = 0). lia.
        assert (ind_npars mind = 0). lia.
        eapply inversion_Construct in wf as [mdecl [idecl' [cdecl' [wf [hd [cu hty]]]]]]; eauto.
        unshelve eapply declared_constructor_to_gen in hd, H0; tea; eauto. 3,6:eapply wfΣ.
        eapply PCUICGlobalEnv.declared_constructor_inj in H0; tea. destruct H0 as [? []]; subst.
        unfold type_of_constructor in hty.
        eapply declared_constructor_from_gen in hd.
        destruct (PCUICWeakeningEnvTyp.on_declared_constructor hd) as [[onmib onind] [univs [[]]]].
        destruct onmib, o. rewrite H4 in onNpars.
        cbn in on_lets_in_type.
        move: hty. rewrite cstr_eq.
        rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
        rewrite PCUICLiftSubst.subst_it_mkProd_or_LetIn.
        move/ws_cumul_pb_Prod_r_inv => [na' [dom' [codom' []]]] hred eqb eqdom cumcod; move: hred.
        set (pars := subst_context _ _ _).
        rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
        rewrite PCUICLiftSubst.subst_it_mkProd_or_LetIn.
        set (args := subst_context _ _ _).
        assert (forallb is_vdef pars).
        { clear -onNpars. subst pars.
          generalize 0.
          induction (ind_params mdecl) using rev_ind; cbn; intros n'. now rewrite subst_context_nil.
          rewrite PCUICUnivSubstitutionConv.subst_instance_app.
          rewrite context_assumptions_app /= in onNpars.
          destruct x as [na [d|] ty]; cbn in * => //; try lia. cbn.
          rewrite PCUICSubstitution.subst_context_app' /= forallb_app.
          rewrite IHc //. lia. }
        assert (forallb is_vdef args).
        { clear -H3. subst args.
          generalize 0.
          induction (cstr_args cdecl) using rev_ind; cbn; intros n'. now rewrite subst_context_nil.
          rewrite PCUICUnivSubstitutionConv.subst_instance_app.
          rewrite context_assumptions_app /= in H3.
          destruct x as [na [d|] ty]; cbn in * => //; try lia. cbn.
          rewrite PCUICSubstitution.subst_context_app' /= forallb_app. cbn.
          rewrite -Nat.add_assoc.
          rewrite IHc //. lia. }
        rewrite -it_mkProd_or_LetIn_app.
        move/red_vdefs_tProd. rewrite forallb_app H0 H5 //=.
        rewrite /cstr_concl. len. rewrite PCUICSubstitution.subst_cstr_concl_head.
        destruct hd. destruct H6. now eapply nth_error_Some_length in H8.
        rewrite expand_lets_mkApps //=. cbn.
        intros h. specialize (h eq_refl).
        eapply invert_red_mkApps_tInd in h as [args' []]. solve_discr.
    - eapply inversion_Prim in wf as [prim_ty [cdecl []]]; eauto.
      now eapply invert_cumul_prim_type_prod in w; tea.
    - clear X1. depelim X.
      move/expanded_mkApps_inv'.
      rewrite arguments_mkApps head_mkApps /=. intros [expargs [mind' [idecl' [cdecl' []]]]].
      unshelve eapply declared_constructor_to_gen in H0. 3:eapply wfΣ.
      eapply PCUICGlobalEnv.declared_constructor_inj in d; tea. destruct d as [? []]; subst.
      rewrite /cstr_arity in l.
      all:rewrite decompose_app_mkApps //.
      eapply PCUICValidity.inversion_mkApps in wf as (? & ? & ?).
      eapply inversion_Construct in t0 as [mdecl [idecl'' [cdecl' [wf [hd [cu hty]]]]]]; eauto.
      eapply PCUICSpine.typing_spine_strengthen in t1. 3:tea.
      2:{ eapply PCUICValidity.validity. econstructor; eauto. }
      clear hty.
      unfold type_of_constructor in t1.
      unshelve eapply declared_constructor_to_gen in hd. 3:apply wfΣ.
      eapply (PCUICGlobalEnv.declared_constructor_inj H0) in hd as [? []]; subst.
      eapply declared_constructor_from_gen in H0.
      destruct (PCUICWeakeningEnvTyp.on_declared_constructor H0) as [[onmib onind] [univs [[]]]].
      destruct onmib, o.
      cbn in on_lets_in_type.
      move: t1. rewrite cstr_eq.
      rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
      rewrite PCUICLiftSubst.subst_it_mkProd_or_LetIn.
      set (pars := subst_context _ _ _).
      rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
      rewrite PCUICLiftSubst.subst_it_mkProd_or_LetIn.
      set (args' := subst_context _ _ _).
      (* move/ws_cumul_pb_Prod_r_inv => [na' [dom' [codom' []]]] hred eqb eqdom cumcod; move: hred. *)
      rewrite /cstr_concl. len. rewrite PCUICSubstitution.subst_cstr_concl_head.
      destruct H0. destruct H0. now eapply nth_error_Some_length in H3.
      rewrite -it_mkProd_or_LetIn_app.
      rewrite -onNpars in l, H1.
      move/PCUICClassification.typing_spine_smash.
      rewrite expand_lets_mkApps.
      have lenargs : #|args| = context_assumptions (ind_params mind') + context_assumptions (cstr_args cdecl') by lia.
      move/(PCUICClassification.typing_spine_all_inv _).
      intros h; forward h. rewrite context_assumptions_smash_context /= context_assumptions_app.
      rewrite /args' /pars. now len.
      rewrite expand_lets_mkApps PCUICLiftSubst.subst_mkApps /= in h.
      move: h => [] h _; move: h.
      move/ws_cumul_pb_Prod_r_inv => [na' [dom' [codom' []]]] hred eqb eqdom cumcod; move: hred.
      move/invert_red_mkApps_tInd => [args'' [heq]]. solve_discr.
  Qed.

  Lemma pcuic_eval_function `{WcbvFlags} (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map) f v na A B
    (wfΣ : wf_ext Σ) (wf : Σ ;;; [] |- f : PCUICAst.tProd na A B) :
    expanded_global_env Σ ->
    expanded Σ [] f ->
    eval Σ f v ->
    match decompose_app v with
    | (tLambda na ty b, []) => True
    | (tInd i u, args) => True
    | (tFix mfix idx, args) => True
    | (tCoFix mfix idx, args) => True
    | _ => False
    end.
  Proof.
    intros expΣ exp ev.
    assert (expanded Σ [] v).
    { eapply (expanded_red (Σ := Σ)); tea. exact wfΣ.
      2:eapply (PCUICClassification.wcbveval_red (Σ := Σ)); tea.
      intros ??; now rewrite nth_error_nil. }
    eapply PCUICClassification.subject_reduction_eval in wf; tea.
    eapply eval_to_value in ev.
    eapply closed_prod_type; tea.
  Qed.

  Lemma nisErasable_eval {Σ : global_env_ext} {t t'} {wfΣ : wf Σ} :
    nisErasable Σ [] t ->
    eval Σ t t' ->
    nisErasable Σ [] t'.
  Proof.
    intros [nf [s [hty norm nisa hs nonprop]]] ev.
    eapply PCUICClassification.subject_reduction_eval in hty. 2:eassumption.
    exists nf, s; split => //.
  Qed.

  (** A cofixpoint applied to arguments at a product type is not
      saturated: its type is still a product. *)
  Lemma typing_cofix_prod_unsaturated {Σ : global_env_ext} {wfΣ : wf Σ}
    {mfix idx args na A B} :
    Σ ;;; [] |- mkApps (tCoFix mfix idx) args : tProd na A B ->
    ∑ d, nth_error mfix idx = Some d × #|args| < rarg d.
  Proof.
    intros tyarg.
    eapply PCUICValidity.inversion_mkApps in tyarg as [A' [Hcof sp]]; auto.
    eapply inversion_CoFix in Hcof
      as (d & _ & hnth & a & _ & wfcofix & cum); auto.
    exists d; split => //.
    eapply nth_error_all in a; eauto.
    simpl in a.
    apply isTypeRel_isType in a.
    eapply PCUICSpine.typing_spine_strengthen in sp; eauto.
    destruct (PCUICInductiveInversion.wf_cofixpoint_rarg wfcofix hnth)
      as (ctx & ind & u & indargs & da & ->).
    eapply PCUICClassification.wf_cofixpoint_spine in sp
      as (Γ' & concl & da' & s); eauto.
    rewrite da in da'. noconf da'.
    move: s => [ind' [u' [indargs' [[eqc _] hlen]]]].
    move: hlen. elim: Nat.ltb_spec => Hargs hlen => //.
    destruct hlen as [hl cum']. exfalso. subst.
    rewrite expand_lets_mkApps PCUICLiftSubst.subst_mkApps /= in cum'.
    now eapply invert_cumul_ind_prod in cum'.
  Qed.

End PCUICInv.

Section ErasureFunction.
  Import PCUICAst PCUICAst.PCUICEnvironment PCUIC.PCUICConversion PCUICArities PCUICSpine PCUICOnFreeVars PCUICWellScopedCumulativity.
  Import EAst EAstUtils EWcbvEval EArities.

  Lemma typing_spine_isArity {Σ : global_env_ext} {Γ T args T'} {wfΣ :  wf Σ} :
    wf_local Σ Γ ->
    typing_spine Σ Γ T args T' ->
    isArity T ->
    exists ar, ∥ typing_spine Σ Γ T args ar ∥ /\ isArity ar.
  Proof.
    intros wfΓ sp isa.
    unshelve epose proof (PCUICClassification.isArity_typing_spine _ sp); eauto.
    forward H.
    { exists T. split; eauto. sq.
      pose proof (typing_spine_isType_dom sp).
      eapply PCUICContextConversion.closed_red_refl; fvs. }
    destruct H as [ar [[redar] isa']]. exists ar; split => //. sq.
    eapply typing_spine_weaken_concl; tea. now eapply red_ws_cumul_pb.
    eapply typing_spine_isType_codom in sp. eapply isType_red; tea.
    eapply redar.
  Qed.

  Lemma erase_function_strict (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map) f v v' na A B
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr :
    ∥ nisErasable Σ [] f ∥ ->
    PCUICWcbvEval.eval Σ f v ->
    let (Σ', f') := transform erase_transform (Σ, f) pr in
    eval Σ' f' v' -> isFunctionS v' = true.
  Proof.
    intros [ne]. destruct wf as [hty].
    intros evf.
    unfold transform, erase_transform.
    destruct pr as [pre [[expΣ expt] [norm norm']]]. destruct pre as [[wfΣ wft]].
    eapply nisErasable_eval in ne; tea.
    eapply nisErasable_spec in ne; eauto.
    eapply PCUICClassification.subject_reduction_eval in hty as hty'; tea.
    unfold erase_program, erase_pcuic_program.
    set (Σ' := build_wf_env_from_env _ _).
    set (env' := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
    set (obl := (fun Σ (wfΣ : _) => _)) at 5.
    set (obl' := (fun Σ => _)) at 12.
    cbn -[env'].
    set (wtf := (fun Σ => _)) at 13. change obl' with wtf. clear obl'. clearbody wtf.
    set (eqdecls := (fun Σ => _)) at 9. clearbody eqdecls.
    set (deps := term_global_deps _).
    set (nin := (fun (n : nat) => _)). clearbody nin.
    epose proof (@erase_global_deps_fast_erase_global_deps deps optimized_abstract_env_impl Σ' (PCUICAst.PCUICEnvironment.declarations Σ) nin _ _) as [nin2 eq].
    rewrite /erase_global_fast. erewrite eq. clear eq nin.
    set (eg := erase_global_deps _ _ _ _ _ _).

    have hcld := expanded_global_env_cofix_lambdas _ expΣ.
    have hclt := expanded_cofix_lambdas _ _ _ expt.
    unshelve epose proof (erase_correct optimized_abstract_env_impl Σ' Σ.2 _
      f v _ _ deps _ eqdecls hcld hclt _ eq_refl _ eq_refl _ Σ eq_refl); eauto.
    { eapply Kernames.KernameSet.subset_spec. rewrite /deps -/env'. cbn [fst snd]. apply Kernames.KernameSetProp.subset_refl. }
    { cbn => ? -> //. }
    destruct H as [v'' [ervv'' [ev]]].
    eset (eg' := erase_global_deps _ _ _ _ _ _) in ev.
    replace eg with eg'. 2:{ rewrite /eg /eg'. eapply reflexivity. }
    intros ev'.
    assert (v' = v''). { epose proof (eval_deterministic ev). symmetry. eapply H.
      set(er := erase _ _ _ _ _) in ev'.
      set(er' := erase _ _ _ _ _).
      replace er' with er. exact ev'.
      rewrite /er /er' /env'. apply reflexivity. }
    subst v''. cbn in ev.
    eapply pcuic_eval_function in evf; tea.
    destruct (PCUICAstUtils.decompose_app v) eqn:da.
    eapply PCUICAstUtils.decompose_app_inv in da. cbn in da.
    move: evf. destruct t0 => //; cbn in da; subst v. 1:destruct l => //. 1-4:intros _.
    - clear -ne ervv''. depelim ervv''. cbn => //. elim ne. sq. exact X.
    - clear -wfΣ hty' ne. elim ne.
      assert (exists mdecl idecl, PCUICAst.declared_inductive Σ ind mdecl idecl) as [mdecl [idecl decli]].
      { eapply PCUICValidity.inversion_mkApps in hty' as [? [hty _]]. clear -hty.
        depind hty; eauto. }
      eapply PCUICInductives.invert_type_mkApps_ind in hty' as [sp cu]; eauto.
      pose proof (typing_spine_isArity ltac:(constructor) sp).
      forward H.
      { apply (PCUICUnivSubstitutionTyp.isArity_subst_instance ui).
        now eapply isArity_ind_type. }
      destruct H as [ar [[spar] isa']].
      sq.
      eexists; cbn. split.
      eapply PCUICSpine.type_mkApps. econstructor; eauto with pcuic. exact spar.
      now left.
    - clear -wfΣ hty' ne ervv''.
      assert (exists mfix' l', v' = EAst.mkApps (EAst.tFix mfix' idx) l') as [mfix' [l' ->]].
      { eapply ErasureProperties.erases_mkApps_inv in ervv'' as [[L1 [L2 [L2' [? [? [? []]]]]]]|[f'[L'[eq [erf erargs]]]]].
        - subst l v'. elim ne. destruct H0. rewrite PCUICAstUtils.mkApps_app. eapply Is_type_app; [eauto|eauto| |eauto].
          now rewrite -PCUICAstUtils.mkApps_app.
        - depelim erf. do 2 eexists; trea. subst v'.
          elim ne. eapply Is_type_app; eauto. }
      now rewrite /isFunctionS /cofix_unsaturated /isFunction /isFixApp
        !head_mkApps decompose_app_mkApps //= orb_true_r.
    - clear -wfΣ hty' ne ervv''.
      destruct (typing_cofix_prod_unsaturated (wfΣ := wfΣ) hty')
        as [d [hnth hlt]].
      assert (exists mfix' l' d',
        [/\ v' = EAst.mkApps (EAst.tCoFix mfix' idx) l',
          nth_error mfix' idx = Some d', EAst.rarg d' = BasicAst.rarg d &
          #|l'| = #|l|]) as (mfix' & l' & d' & [-> hnth' hr hlen]).
      { eapply ErasureProperties.erases_mkApps_inv in ervv'' as [[L1 [L2 [L2' [? [? [? []]]]]]]|[f'[L'[eq [erf erargs]]]]].
        - subst l v'. elim ne. destruct H0. rewrite PCUICAstUtils.mkApps_app. eapply Is_type_app; [eauto|eauto| |eauto].
          now rewrite -PCUICAstUtils.mkApps_app.
        - depelim erf.
          + eapply All2_nth_error_Some in X as [d' [hnth' []]]; tea.
            exists mfix', L', d'. split => //.
            now eapply Forall2_length in erargs.
          + subst v'. elim ne. eapply Is_type_app; eauto. }
      rewrite /isFunctionS /cofix_unsaturated /isFunction /isFixApp
        !head_mkApps decompose_app_mkApps //= hnth' orb_true_r /=.
      apply Nat.ltb_lt. lia.
  Qed.

  Lemma erase_function (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map) f v v' na A B
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr :
    ∥ nisErasable Σ [] f ∥ ->
    PCUICWcbvEval.eval Σ f v ->
    let (Σ', f') := transform erase_transform (Σ, f) pr in
    eval Σ' f' v' -> isFunction v' = true.
  Proof.
    intros ne ev.
    generalize (erase_function_strict Σ f v v' na A B wf pr ne ev).
    destruct transform. intros h ev'. now move/andP: (h ev') => [].
  Qed.

  Lemma pcuic_function_value (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) {Σ : global_env_ext} {f na A B}
    (wfΣ : wf_ext Σ) (axfree : axiom_free Σ) (wf : Σ ;;; [] |- f : PCUICAst.tProd na A B) : { v & PCUICWcbvEval.eval Σ f v }.
  Proof.
    eapply (PCUICNormalization.wcbv_normalization wfΣ axfree wf). Unshelve.
    exact PCUICSN.extraction_normalizing.
    now eapply PCUICSN.normalization.
  Qed.

  Lemma erase_function_to_function_strict (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map) f v' na A B
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr :
    axiom_free Σ ->
    ∥ nisErasable Σ [] f ∥ ->
    let (Σ', f') := transform erase_transform (Σ, f) pr in
    eval Σ' f' v' -> isFunctionS v' = true.
  Proof.
    intros axfree nise.
    destruct pr as [[]]. destruct wf.
    epose proof (pcuic_function_value w.1 axfree X) as [v hv].
    eapply erase_function_strict; tea. now sq.
  Qed.

  Lemma erase_function_to_function (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map) f v' na A B
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr :
    axiom_free Σ ->
    ∥ nisErasable Σ [] f ∥ ->
    let (Σ', f') := transform erase_transform (Σ, f) pr in
    eval Σ' f' v' -> isFunction v' = true.
  Proof.
    intros axfree nise.
    destruct pr as [[]]. destruct wf.
    epose proof (pcuic_function_value w.1 axfree X) as [v hv].
    eapply erase_function; tea. now sq.
  Qed.

End ErasureFunction.


Import EWellformed.

Lemma compile_value_box_mkApps {Σ i n ui args npars acc} :
  pcuic_lookup_inductive_pars Σ i = Some npars ->
  compile_value_box Σ (PCUICAst.mkApps (PCUICAst.tConstruct i n ui) args) acc =
  EAst.tConstruct i n (skipn npars (List.map (flip (compile_value_box Σ) []) args ++ acc)).
Proof.
  revert acc; induction args using rev_ind.
  - intros acc. cbn. intros ->. reflexivity.
  - intros acc. rewrite PCUICAstUtils.mkApps_app /=. cbn.
    intros hl.
    now rewrite IHargs // map_app /= -app_assoc /=.
Qed.

Derive Signature for firstorder_evalue.

Section PCUICenv.
  Import PCUICAst.
  Import PCUICEnvironment.

  Lemma pres_inductives_lookup Σ Σ' i n mdecl idecl cdecl :
    wf Σ ->
    erase_preserves_inductives Σ Σ' ->
    declared_constructor Σ (i, n) mdecl idecl cdecl ->
    forall npars nargs, EGlobalEnv.lookup_constructor_pars_args Σ' i n = Some (npars, nargs) ->
    npars = mdecl.(ind_npars) /\ nargs = cdecl.(cstr_arity).
  Proof.
    intros wf he.
    rewrite /declared_constructor /declared_inductive.
    intros [[declm decli] declc].
    unshelve eapply declared_minductive_to_gen in declm. 3:exact wf. red in declm.
    intros npars nargs. rewrite /EGlobalEnv.lookup_constructor_pars_args.
    rewrite /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive.
    destruct EGlobalEnv.lookup_env eqn:e => //=.
    destruct g => //.
    eapply he in declm; tea. subst m. cbn.
    rewrite nth_error_map decli /=.
    rewrite nth_error_map declc /=. intuition congruence.
  Qed.
End PCUICenv.

Lemma lookup_constructor_pars_args_lookup_inductive_pars Σ i n npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  EGlobalEnv.lookup_inductive_pars Σ (Kernames.inductive_mind i) = Some npars.
Proof.
  rewrite /EGlobalEnv.lookup_constructor_pars_args /EGlobalEnv.lookup_inductive_pars.
  rewrite /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive.
  destruct EGlobalEnv.lookup_minductive => //=.
  destruct nth_error => //=. destruct nth_error => //=. congruence.
Qed.

Lemma compile_evalue_erase (Σ : PCUICAst.PCUICEnvironment.global_env_ext) (Σ' : EEnvMap.GlobalContextMap.t) v :
  wf Σ.1 ->
  PCUICFirstorder.firstorder_value Σ [] v ->
  firstorder_evalue Σ' (compile_value_erase v []) ->
  erase_preserves_inductives (PCUICAst.PCUICEnvironment.fst_ctx Σ) Σ' ->
  ERemoveParams.compile_evalue_box_strip Σ' (compile_value_erase v []) [] = compile_value_box (PCUICAst.PCUICEnvironment.fst_ctx Σ) v [].
Proof.
  move=> wf fo fo' hΣ; move: v fo fo'.
  apply: PCUICFirstorder.firstorder_value_inds.
  intros i n ui u args pandi hty hargs ih isp.
  eapply PCUICInductiveInversion.Construct_Ind_ind_eq' in hty as [mdecl [idecl [cdecl [declc _]]]] => //.
  rewrite compile_value_erase_mkApps.
  intros fo'. depelim fo'. EAstUtils.solve_discr. noconf H1. noconf H2.
  assert (npars = PCUICAst.PCUICEnvironment.ind_npars mdecl).
  { now eapply pres_inductives_lookup in declc; tea. }
  subst npars.
  rewrite (compile_value_box_mkApps (npars := PCUICAst.PCUICEnvironment.ind_npars mdecl)).
  { destruct declc as [[declm decli] declc].
    unshelve eapply declared_minductive_to_gen in declm. 3:exact wf.
    rewrite /PCUICAst.declared_minductive_gen in declm.
    rewrite /pcuic_lookup_inductive_pars // declm //. }
  rewrite (ERemoveParams.compile_evalue_box_strip_mkApps (npars := PCUICAst.PCUICEnvironment.ind_npars mdecl)) //.
  rewrite lookup_inductive_pars_spec //.
  eapply lookup_constructor_pars_args_lookup_inductive_pars; tea.
  rewrite !app_nil_r. f_equal.
  rewrite app_nil_r skipn_map in H0.
  eapply Forall_map_inv in H0.
  eapply (Forall_skipn _ (PCUICAst.PCUICEnvironment.ind_npars mdecl)) in ih.
  rewrite !skipn_map /flip map_map.
  ELiftSubst.solve_all.
Qed.


Import EAstUtils.
Import EInlining.

Lemma isFunctionS_strip Σ t :
  isFunctionS t -> isFunctionS (ERemoveParams.strip Σ t).
Proof.
  apply isFunctionS_hom.
  - intros hd args napp h. rewrite ERemoveParams.strip_mkApps //.
    now destruct hd.
  - intros. now simp strip.
  - intros. now simp strip.
  - intros. now simp strip.
Qed.

Lemma expand_lets_function (wfl := default_wcbv_flags)
  {guard_impl : abstract_guard_impl}
  (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map) K f na A B
  (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr :
  let (Σ', f') := transform (pcuic_expand_lets_transform K) (Σ, f) pr in
  ∥ Σ' ;;; [] |- f' : PCUICExpandLets.trans (PCUICAst.tProd na A B) ∥.
Proof.
  unfold transform, pcuic_expand_lets_transform. cbn.
  destruct pr as [[[]] ?].
  sq.
  eapply PCUICExpandLetsCorrectness.pcuic_expand_lets in wf; eauto.
  now eapply PCUICExpandLetsCorrectness.trans_wf.
Qed.

Lemma transform_erase_pres_term
  (p p' : program global_env_ext_map PCUICAst.term) pre pre' :
  extends_global_env p.1 p'.1 ->
  p.2 = p'.2 ->
  (transform erase_transform p pre).2 =
  (transform erase_transform p' pre').2.
Proof.
  destruct p as [ctx t], p' as [ctx' t']. cbn.
  intros hg heq; subst t'. eapply ErasureFunction.erase_irrel_global_env.
  eapply equiv_env_inter_hlookup.
  intros ? ?; cbn. intros -> ->. cbn. now eapply extends_global_env_equiv_env.
Qed.

(** ** The verified pipeline on erased programs

  [verified_lambdabox_pipeline] is the erasure stage
  ([guarded_to_unguarded_fix], [remove_params_optimization]) followed by
  [ETransform.tr (verified_lambdabox_etransform econf)]: its properties are
  the fields of [verified_lambdabox_etransform]. *)

Lemma obseq_lambdabox_function {guard : abstract_guard_impl}
  (Σt Σ'v : EProgram.eprogram_env) econf
  pr (pr' : pre (verified_lambdabox_pipeline econf) Σ'v) p' v' :
  EGlobalEnv.extends Σ'v.1 Σt.1 ->
  obseq (verified_lambdabox_pipeline econf) Σt pr p' Σ'v.2 v' ->
  isFunctionS Σ'v.2 ->
  value (wfl := final_wcbv_flags) p'.1 v' ->
  isFunction v'.
Proof.
  intros ext obs hf hv.
  move: obs. unfold verified_lambdabox_pipeline.
  cbn [obseq compose guarded_to_unguarded_fix remove_params_optimization].
  intros [v2 [[v1 [-> ->]] obs]].
  have := ETransform.obseq_function _ _ _ _ _ _ obs (isFunctionS_strip _ _ hf).
  now move/andP => [].
Qed.

Lemma transform_lambdabox_pres_term {guard : abstract_guard_impl} p p' pre pre'
  econf :
  extends_eprogram_env p p' ->
  (transform (verified_lambdabox_pipeline econf) p pre).2 =
  (transform (verified_lambdabox_pipeline econf) p' pre').2.
Proof.
  intros hext.
  exact (proj2 (verified_lambdabox_pipeline_extends' _ p p' pre pre' hext)).
Qed.

Lemma etransform_pre_irrel_eq {env env' : Type}
  {eval : Transform.program env EAst.term -> EAst.term -> Prop}
  {eval' : Transform.program env' EAst.term -> EAst.term -> Prop}
  {ext ext' fo fo' eta eta'}
  (o : @ETransform.t env env' eval eval' ext ext' fo fo' eta eta')
  (q q' : Transform.program env EAst.term)
  (hq : pre (ETransform.tr o) q) (hq' : pre (ETransform.tr o) q') :
  q = q' ->
  transform (ETransform.tr o) q hq = transform (ETransform.tr o) q' hq'.
Proof.
  intros ->. apply ETransform.transform_pre_irrel.
Qed.

Lemma strip_program_tApp {efl : EWellformed.EEnvFlags}
  (Σ : EEnvMap.GlobalContextMap.t) t u :
  EEtaExpanded.isEtaExp Σ t ->
  ERemoveParams.strip_program (Σ, EAst.tApp t u) =
  (ERemoveParams.strip_env Σ,
    EAst.tApp (ERemoveParams.strip Σ t) (ERemoveParams.strip Σ u)).
Proof.
  intros etat. rewrite /ERemoveParams.strip_program /=. f_equal.
  exact (ERemoveParams.strip_mkApps_etaexp _ [u] etat).
Qed.

Lemma transform_lambda_box_eta_app {guard : abstract_guard_impl}
  (Σer : EEnvMap.GlobalContextMap.t) t u pre econf :
  EEtaExpandedFix.isEtaExp Σer [] t ->
  exists pre' pre'',
  transform (verified_lambdabox_pipeline econf) (Σer, EAst.tApp t u) pre =
  ((transform (verified_lambdabox_pipeline econf) (Σer, EAst.tApp t u) pre).1,
    EAst.tApp (transform (verified_lambdabox_pipeline econf) (Σer, t) pre').2
      (transform (verified_lambdabox_pipeline econf) (Σer, u) pre'').2).
Proof.
  intros etat.
  destruct pre as [[wfΣ wft] [expΣ expt]].
  pose proof wft as wft'. cbn in wft'. move/andP: wft' => [wft1 wfu1].
  have expt' := EEtaExpandedFix.expanded_isEtaExp _ _ _ expt.
  have etau := EEtaExpandedFix.isEtaExpFix_tApp_arg _ _ _ _ expt'.
  have etat' := EEtaExpanded.isEtaExpFix_isEtaExp _ _ _ etat.
  unshelve eexists.
  { split; split => //. cbn. now eapply EEtaExpandedFix.isEtaExp_expanded. }
  unshelve eexists.
  { split; split => //. cbn. now eapply EEtaExpandedFix.isEtaExp_expanded. }
  unfold verified_lambdabox_pipeline.
  cbn [transform compose]. unfold run, time.
  set (E := verified_lambdabox_etransform econf).
  match goal with
  | |- transform (ETransform.tr E) ?q ?hq = (_, EAst.tApp
      (transform (ETransform.tr E) ?qt ?hqt).2
      (transform (ETransform.tr E) ?qu ?hqu).2) =>
    set (Q := q) in *; set (HQ := hq) in *
  end.
  have eQ : Q = (ERemoveParams.strip_env Σer,
    EAst.tApp (ERemoveParams.strip Σer t) (ERemoveParams.strip Σer u)).
  { exact (strip_program_tApp (efl := all_env_flags) Σer t u etat'). }
  have hq' := eq_rect _ (pre (ETransform.tr E)) HQ _ eQ.
  rewrite (etransform_pre_irrel_eq E Q _ HQ hq' eQ).
  have eta' :
    is_eta_app (ERemoveParams.strip_env Σer, ERemoveParams.strip Σer t).
  { rewrite /is_eta_app /=. eapply EEtaExpanded.expanded_isEtaExp.
    eapply ERemoveParams.strip_expanded.
    now eapply EEtaExpanded.isEtaExp_expanded. }
  destruct (ETransform.transform_app E _ _ _ hq' eta') as [prt [pru ->]].
  cbn [fst snd]. do 2 f_equal; apply f_equal, etransform_pre_irrel_eq;
    reflexivity.
Qed.

Section PCUICErase.
  Import PCUICAst PCUICAstUtils PCUICEtaExpand PCUICWfEnv.

  Definition lift_wfext (Σ : global_env_ext_map) (wfΣ : ∥ wf_ext Σ ∥) :
    let wfe := build_wf_env_from_env Σ.1 (map_squash (wf_ext_wf Σ) wfΣ) in
    (forall Σ' : global_env, Σ' ∼ wfe -> ∥ wf_ext (Σ', Σ.2) ∥).
  Proof.
    intros wfe; cbn; intros ? ->. apply wfΣ.
  Qed.

  (* (forall Σ : global_env, Σ ∼ X -> ∥ wf_ext (Σ, univs) ∥) *)
  Lemma snd_erase_pcuic_program {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (nin' : wf_ext p.1 -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    exists wt' nin'', (@erase_pcuic_program guard_impl p nin nin' wfΣ wt).2 = erase optimized_abstract_env_impl (normalization_in := nin'') Xext [] p.2 wt'.
  Proof.
    unfold erase_pcuic_program.
    cbn -[erase]. do 2 eexists. eapply ErasureFunction.erase_irrel_global_env.
    red. cbn. intros. split => //.
    Unshelve. intros ? ->. destruct wt as [[T wt]]. now econstructor.
    destruct wfΣ.
    intros ? ? ->. now eapply nin.
  Qed.

  Definition wt'_erase_pcuic_program {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    forall Σ : global_env_ext, Σ ∼_ext abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) wfe p.1.2 (fun (Σ0 : global_env) (H : Σ0 ∼ wfe) => ETransform.erase_pcuic_program_obligation_1 guard_impl p wfΣ Σ0 H) -> welltyped Σ [] p.2.
    intros.
    refine ((let 'sq s as wt' := wt return (wt' = wt -> welltyped Σ [] p.2) in
      let '(T; ty) as s0 := s return (sq s0 = wt -> welltyped Σ [] p.2) in
          fun _ : sq (T; ty) = wt => iswelltyped (eq_rect (p.1 : global_env_ext) (fun Σ0 : global_env_ext => Σ0;;; [] |- p.2 : T) ty Σ (ETransform.erase_pcuic_program_obligation_3 guard_impl p wfΣ Σ H)))
         eq_refl).
  Defined.

  Definition erase_nin {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) :=
    fun (Σ : global_env_ext) (H : wf_ext Σ) (H0 : Σ = abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) (build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ)) p.1.2 (fun (Σ0 : global_env) (H0 : Σ0 = p.1.1) => ETransform.erase_pcuic_program_obligation_1 guard_impl p wfΣ Σ0 H0)) =>
    ETransform.erase_pcuic_program_obligation_2 guard_impl p nin wfΣ Σ H H0 .

  Lemma fst_erase_pcuic_program {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (nin' : wf_ext p.1 -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl (guard := guard_impl)) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    let nin'' := erase_nin p nin wfΣ in
    let er := erase optimized_abstract_env_impl (normalization_in := nin'') Xext [] p.2 (wt'_erase_pcuic_program p wfΣ wt) in
    exists hprefix nin2 hfr,
    (@erase_pcuic_program guard_impl p nin nin' wfΣ wt).1 =
    make (erase_global_deps optimized_abstract_env_impl (term_global_deps er) wfe (declarations p.1) nin2 hprefix).1 hfr.
  Proof.
    intros.
    unfold erase_pcuic_program. rewrite -/wfe -/nin' -/Xext.
    cbn -[erase abstract_make_wf_env_ext].
    set (er' := erase _ _ _ _ _).
    assert (er = er').
    { subst er er'.
      eapply ErasureFunction.erase_irrel_global_env.
      red. cbn. intros. split => //. }
    rewrite /erase_global_fast.
    set(prf := fun (n : nat) => _).
    set(prf' := fun (Σ : global_env) => _).
    unshelve eexists. intros ? ->; reflexivity.
    epose proof (@erase_global_deps_fast_erase_global_deps (term_global_deps er') optimized_abstract_env_impl wfe (declarations p.1) _ _ _) as [nin2 eq].
    exists nin2.
    set(prf'' := fun (Σ : global_env) => _).
    set(prf''' := ETransform.erase_pcuic_program_obligation_6 _ _ _ _ _ _).
    cbn zeta in prf'''. unfold erase_global_fast in prf'''.
    clearbody prf'''.
    revert prf'''. rewrite eq -H. intros prf'''.
    exists prf'''. f_equal.
    Unshelve. apply prf'.
  Qed.

  Lemma fst_erase_pcuic_program' {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (nin' : wf_ext p.1 -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    expanded_global_env p.1 ->
    expanded p.1 [] p.2 ->
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl (guard := guard_impl)) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    forall wt' nin'',
    let er := erase optimized_abstract_env_impl (normalization_in := nin'') Xext [] p.2 wt' in
    EEtaExpandedFix.expanded (@erase_pcuic_program guard_impl p nin nin' wfΣ wt).1 [] er.
  Proof.
    intros.
    unfold erase_pcuic_program. rewrite -/wfe -/nin' -/Xext.
    cbn -[erase abstract_make_wf_env_ext].
    set (er' := erase _ _ _ _ _).
    assert (er = er') as <-.
    { subst er er'.
      eapply ErasureFunction.erase_irrel_global_env.
      red. cbn. intros. split => //. }
    rewrite /erase_global_fast.
    epose proof erase_global_deps_fast_erase_global_deps as [nin2 eq].
    erewrite eq. clear eq.
    eapply expanded_erase; revgoals; tea. cbn. reflexivity.
    Unshelve. cbn; intros ? ->; reflexivity.
  Qed.

  Lemma erase_eta_app (Σ : global_env_ext_map) t u pre :
    ~ ∥ isErasable Σ [] (tApp t u) ∥ ->
    PCUICEtaExpand.expanded Σ [] t ->
    exists pre' pre'',
    let trapp := transform erase_transform (Σ, PCUICAst.tApp t u) pre in
    let trt := transform erase_transform (Σ, t) pre' in
    let tru := transform erase_transform (Σ, u) pre'' in
    EEtaExpandedFix.isEtaExp trt.1 [] trt.2 /\
    EGlobalEnv.extends trt.1 trapp.1 /\
    EGlobalEnv.extends tru.1 trapp.1 /\
    trapp = (trapp.1, EAst.tApp trt.2 tru.2).
  Proof.
    intros er etat.
    unshelve eexists.
    { destruct pre as [[] []]. cbn in *. split => //. 2:split => //.
      destruct X. split. split => //. destruct s as [appty tyapp].
      eapply PCUICInversion.inversion_App in tyapp as [na [A [B [hp [hu hcum]]]]]. now eexists.
      cbn. apply w.
      destruct H; split => //. }
    unshelve eexists.
    { destruct pre as [[] []]. cbn in *. split => //. 2:split => //.
      destruct X. split. split => //. destruct s as [appty tyapp].
      eapply PCUICInversion.inversion_App in tyapp as [na [A [B [hp [hu hcum]]]]]. now eexists.
      cbn. apply w.
      destruct H; split => //. cbn. cbn in H1. now eapply expanded_tApp_arg in H1. }
    have etaΣ : PCUICEtaExpand.expanded_global_env Σ.
    { exact (proj1 (proj1 (proj2 pre))). }
    have hcld : cofix_lambdas_decls (declarations Σ).
    { exact (expanded_global_env_cofix_lambdas _ etaΣ). }
    unfold transform, erase_transform. cbn -[erase_program].
    unfold erase_program.
    set (prf := map_squash _ _); clearbody prf.
    set (prf0 := map_squash _ _); clearbody prf0.
    set (prf1 := map_squash _ _); clearbody prf1.
    set (prf2 := map_squash _ _); clearbody prf2.
    set (prf3 := map_squash _ _); clearbody prf3.
    set (prf4 := map_squash _ _); clearbody prf4.
    set (erp := erase_pcuic_program (_, tApp _ _) _ _).
    destruct erp eqn:heq. f_equal. subst erp.
    pose proof (f_equal snd heq). cbn -[erase_pcuic_program] in H.
    rewrite -{}H.
    match goal with
    [ |- context [ @erase_pcuic_program ?guard (?Σ, tApp ?t ?u) ?nin ?nin' ?prf ?prf' ] ] =>
    destruct (snd_erase_pcuic_program (Σ, tApp t u) nin nin' prf prf') as [wt' [nin'' ->]]
    end. cbn [fst snd].
    rewrite (erase_mkApps _ _ [u]).
    { cbn; intros ? ->. destruct prf4 as [[? hu]]. repeat constructor. cbn in hu. eexists. exact hu. }
    intros.
    cbn [E.mkApps erase_terms].
    match goal with
    [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
    destruct (snd_erase_pcuic_program p nin nin' prf prf') as [wt'' [nin''' ->]]
    end.
    split; [|split; [|split]].
    - cbn [fst snd]. eapply EEtaExpandedFix.expanded_isEtaExp.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        epose proof (fst_erase_pcuic_program' p nin nin' prf prf' etaΣ etat)
      end.
      eapply H.
    - clear -er heq hcld. apply (f_equal fst) in heq. cbn [fst] in heq.
      rewrite -heq. clear -er hcld.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf := nin); clearbody ninprf;
        set (ninprf' := nin'); clearbody ninprf';
        epose proof (fst_erase_pcuic_program p ninprf ninprf' prf prf')
      end.
      destruct H as [hpref [ning [hfr ->]]].
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf0 := nin); clearbody ninprf0;
        set (ninprf0' := nin'); clearbody ninprf0';
        epose proof (fst_erase_pcuic_program p ninprf0 ninprf0' prf prf')
      end.
      destruct H as [hpref' [ning' [hfr' ->]]].
      cbn -[erase_global_deps term_global_deps erase abstract_make_wf_env_ext build_wf_env_from_env].
      rewrite !erase_global_deps_erase_global.
      (* assert (wfg : wf_glob (erase_global (build_wf_env_from_env Σ.1 (map_squash (wf_ext_wf Σ) prf))). *)
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. exact hcld. }
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. exact hcld. }
      assert (prf = prf1) by apply proof_irrelevance.
      assert (hpref = hpref') by apply proof_irrelevance. subst prf1 hpref'.
      assert (ning = ning') by apply proof_irrelevance. subst ning'.
      eapply extends_filter_impl.
      2:{ eapply erase_global_wf_glob. exact hcld. }
      intros x. unfold flip.
      clear -er.
      set (env := abstract_make_wf_env_ext _ _ _).
      match goal with
      [ |- context [ @erase ?X_type ?X ?nin ?G (tApp _ _) ?wt ] ] =>
        unshelve epose proof (@erase_mkApps X_type X nin G t [u] wt (wt'_erase_pcuic_program (Σ, t) prf prf0))
      end.
      assert (hargs : forall Σ : global_env_ext, Σ ∼_ext env -> ∥ All (welltyped Σ []) [u] ∥).
      { cbn; intros ? ->. do 2 constructor; auto. destruct prf. destruct prf2 as [[T HT]]. eapply PCUICInversion.inversion_App in HT as HT'.
        destruct HT' as [na [A [B [Hp []]]]]. now eexists. eapply w. }
      specialize (H hargs).
      forward H by repeat constructor.
      forward H. { cbn; intros ? ->. exact er. }
      rewrite H. rewrite term_global_deps_mkApps. intros hin. eapply KernameSet.mem_spec.
      rewrite global_deps_union. eapply KernameSet.union_spec. left.
      eapply KernameSet.mem_spec in hin. clear -hin.
      set (er0 := @erase _ _ _ _ _ _) in hin.
      set (er1 := @erase _ _ _ _ _ _).
      assert (er0 = er1). { unfold er0, er1. eapply ErasureFunction.erase_irrel_global_env. intro. cbn. intros -> ? ->; cbn; intuition eauto. }
      now rewrite -H.
    - clear -prf0 er heq etat hcld. apply (f_equal fst) in heq.
      cbn [fst] in heq.
      rewrite -heq. clear -er etat prf0 hcld.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf := nin); clearbody ninprf;
        set (ninprf' := nin'); clearbody ninprf';
        epose proof (fst_erase_pcuic_program p ninprf ninprf' prf prf')
      end.
      destruct H as [hpref [ning [hfr ->]]].
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf0 := nin); clearbody ninprf0;
        set (ninprf0' := nin'); clearbody ninprf0';
        epose proof (fst_erase_pcuic_program p ninprf0 ninprf0' prf prf')
      end.
      destruct H as [hpref' [ning' [hfr' ->]]].
      cbn -[erase_global_deps term_global_deps erase abstract_make_wf_env_ext build_wf_env_from_env].
      rewrite !erase_global_deps_erase_global.
      (* assert (wfg : wf_glob (erase_global (build_wf_env_from_env Σ.1 (map_squash (wf_ext_wf Σ) prf))). *)
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. exact hcld. }
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. exact hcld. }
      assert (prf3 = prf1) by apply proof_irrelevance.
      assert (hpref = hpref') by apply proof_irrelevance. subst prf1 hpref'.
      assert (ning = ning') by apply proof_irrelevance. subst ning'.
      eapply extends_filter_impl.
      2:{ eapply erase_global_wf_glob. exact hcld. }
      intros x. unfold flip.
      clear -er prf0.
      set (env := abstract_make_wf_env_ext _ _ _).
      match goal with
      [ |- context [ @erase ?X_type ?X ?nin ?G (tApp _ _) ?wt ] ] =>
        unshelve epose proof (@erase_mkApps X_type X nin G t [u] wt (wt'_erase_pcuic_program (Σ, t) prf3 prf0))
      end.
      assert (hargs : forall Σ : global_env_ext, Σ ∼_ext env -> ∥ All (welltyped Σ []) [u] ∥).
      { cbn; intros ? ->. do 2 constructor; auto. destruct prf4 as [[T HT]]. eexists; eapply HT. }
      specialize (H hargs).
      forward H by repeat constructor.
      forward H. { cbn; intros ? ->. exact er. }
      rewrite H. rewrite term_global_deps_mkApps. intros hin. eapply KernameSet.mem_spec.
      rewrite global_deps_union. eapply KernameSet.union_spec. right. cbn [erase_terms].
      eapply KernameSet.mem_spec in hin. clear -hin.
      set (er0 := @erase _ _ _ _ _ _) in hin.
      set (er1 := @erase _ _ _ _ _ _).
      assert (er0 = er1). { unfold er0, er1. eapply ErasureFunction.erase_irrel_global_env. intro. cbn. intros -> ? ->; cbn; intuition eauto. }
      rewrite -H. cbn. rewrite global_deps_union. eapply KernameSet.union_spec. now left.
    - f_equal. f_equal. eapply ErasureFunction.erase_irrel_global_env. red. cbn. intros; split => //.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
      destruct (snd_erase_pcuic_program p nin nin' prf prf') as [wt''' [nin'''' ->]]
      end. eapply ErasureFunction.erase_irrel_global_env. red. cbn. intros; split => //.
      - intros. constructor.
      - now cbn; intros ? ->.
      - cbn; intros ? ->. destruct prf0 as [[? wtt]]. eexists; apply wtt.
  Qed.

  Lemma expand_lets_eta_app (Σ : global_env_ext_map) t u K pre :
    ~ ∥ isErasable Σ [] (tApp t u) ∥ ->
    PCUICEtaExpand.expanded Σ [] t ->
    exists pre' pre'',
    transform (pcuic_expand_lets_transform K) (Σ, PCUICAst.tApp t u) pre =
    ((transform (pcuic_expand_lets_transform K) (Σ, PCUICAst.tApp t u) pre).1,
      tApp (transform (pcuic_expand_lets_transform K) (Σ, t) pre').2
        (transform (pcuic_expand_lets_transform K) (Σ, u) pre'').2).
  Proof.
    intros er etat.
    unshelve eexists.
    { destruct pre as [[] []]. cbn in *. split => //. 2:split => //.
      destruct X. split. split => //. destruct s as [appty tyapp].
      eapply PCUICInversion.inversion_App in tyapp as [na [A [B [hp [hu hcum]]]]]. now eexists.
      cbn. apply w.
      destruct H; split => //. }
    unshelve eexists.
    { destruct pre as [[] []]. cbn in *. split => //. 2:split => //.
      destruct X. split. split => //. destruct s as [appty tyapp].
      eapply PCUICInversion.inversion_App in tyapp as [na [A [B [hp [hu hcum]]]]]. now eexists.
      cbn. apply w.
      destruct H; split => //. cbn. cbn in H1. now eapply expanded_tApp_arg in H1. }
    reflexivity.
  Qed.

  Lemma isErasable_lets (p : pcuic_program) :
    wf p.1 ->
    isErasable p.1 [] p.2 -> isErasable (PCUICExpandLets.expand_lets_program p).1 []
      (PCUICExpandLets.expand_lets_program p).2.
  Proof.
    intros wfΣ. destruct p as [Σ t]. cbn.
    unfold isErasable.
    intros [T [tyT pr]].
    eapply (PCUICExpandLetsCorrectness.expand_lets_sound (cf := extraction_checker_flags)) in tyT.
    exists (PCUICExpandLets.trans T). split => //.
    destruct pr => //. left => //. now rewrite PCUICExpandLetsCorrectness.isArity_trans in i. right.
    destruct s as [u []]; exists u; split => //.
    eapply (PCUICExpandLetsCorrectness.expand_lets_sound (cf := extraction_checker_flags)) in t0.
    now cbn in t0.
  Qed.

  Import PCUICWellScopedCumulativity PCUICFirstorder PCUICNormalization PCUICReduction PCUIC.PCUICConversion PCUICPrincipality.
  Import PCUICExpandLets PCUICExpandLetsCorrectness.
  Import PCUICOnFreeVars PCUICSigmaCalculus.

  Lemma nisErasable_lets (p : pcuic_program) :
    wf_ext p.1 ->
    nisErasable p.1 [] p.2 ->
    nisErasable (PCUICExpandLets.expand_lets_program p).1 []
      (PCUICExpandLets.expand_lets_program p).2.
  Proof.
    intros wfΣ.  destruct p as [Σ t]. cbn in *.
    unfold nisErasable.
    intros [T [u [Hty Hnf Har Hsort Hprop]]].
    pose proof (PCUICExpandLetsCorrectness.expand_lets_sound (cf := extraction_checker_flags) Hty).
    exists (PCUICExpandLets.trans T), u. split => //.
    cbn. eapply (proj2 (trans_ne_nf Σ [] _) Hnf). eapply PCUICClosedTyp.subject_is_open_term; tea.
    now rewrite -isArity_trans.
    now eapply (PCUICExpandLetsCorrectness.expand_lets_sound (cf := extraction_checker_flags)) in Hsort.
  Qed.

  (* Beware, this internally uses preservation of observations and determinism of evaluation
     from the canonical evaluation of [f] in the source to the evaluation in the target.
    *)
  Lemma transform_erasure_pipeline_function
    (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map)
    {f v' na A B}
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr econf :
    axiom_free Σ ->
    ∥ nisErasable Σ [] f ∥ ->
    let tr := transform (verified_erasure_pipeline econf) (Σ, f) pr in
    eval (wfl := extraction_wcbv_flags) tr.1 tr.2 v' -> isFunction v' = true.
  Proof.
    intros axfree nise.
    unfold verified_erasure_pipeline.
    rewrite -!transform_compose_assoc.
    pose proof (expand_lets_function Σ (fun p : global_env_ext_map =>
    (wf_ext p -> PCUICSN.NormalizationIn p) /\
    (wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p)) f na A B wf pr).
    destruct_compose. intros pre.
    set (trexp := transform (pcuic_expand_lets_transform _) _ _) in *.
    eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ) in axfree.
    have nise' : ∥ nisErasable trexp.1 [] trexp.2 ∥.
    destruct pr as [[[]] ?], nise. sq; now eapply nisErasable_lets.
    change (trans_global_env _) with (global_env_ext_map_global_env_ext trexp.1).1 in axfree.
    clearbody trexp. clear nise pr wf Σ f. destruct trexp as [Σ f].
    pose proof pre as pre'; destruct pre' as [[[wf _]] _].
    pose proof (map_squash (pcuic_function_value wf axfree) H) as [[v ev]].
    epose proof (Transform.preservation erase_transform).
    specialize (H0 _ v pre (sq ev)).
    revert H0.
    destruct_compose. intros pre' htr.
    destruct htr as [v'' [ev' _]].
    epose proof (erase_function_to_function_strict _ f v'' _ _ _ H pre
      axfree nise').
    set (tre := transform erase_transform _ _) in *. clearbody tre.
    cbn -[transform obseq].
    intros ev2. red in ev'. destruct ev'.
    epose proof (Transform.preservation (verified_lambdabox_pipeline econf)).
    destruct tre as [Σ' f'].
    specialize (H2 _ v'' pre' (sq H1)) as [finalv [[evfinal] obseq]].
    pose proof (eval_deterministic evfinal ev2). subst v'.
    have prev : Transform.pre (verified_lambdabox_pipeline econf) (Σ', v'').
    { clear -wfl pre' H1. cbn in H1.
      destruct pre' as [[] []]. split; split => //=.
      eapply EWcbvEval.eval_wellformed; eauto.
      eapply EEtaExpandedFix.isEtaExp_expanded.
      eapply (@EEtaExpandedFix.eval_etaexp wfl); eauto.
      now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
      now eapply EEtaExpandedFix.expanded_isEtaExp. }
    specialize (H0 H1).
    exact (obseq_lambdabox_function (guard := guard_impl) (Σ', f') (Σ', v'')
      econf pre' prev _ finalv ltac:(cbn; red; tauto) obseq H0
      (eval_to_value _ _ evfinal)).
  Qed.

  
  (* This version provides the evaluation proof. *)
  Lemma transform_erasure_pipeline_function'
    (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map)
    {f na A B}
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr econf :
    axiom_free Σ ->
    ∥ nisErasable Σ [] f ∥ ->
    let tr := transform (verified_erasure_pipeline econf) (Σ, f) pr in
    exists v, ∥ eval (wfl := extraction_wcbv_flags) tr.1 tr.2 v ∥ /\ isFunction v = true.
  Proof.
    intros axfree nise.
    unfold verified_erasure_pipeline.
    rewrite -!transform_compose_assoc.
    pose proof (expand_lets_function Σ (fun p : global_env_ext_map =>
    (wf_ext p -> PCUICSN.NormalizationIn p) /\
    (wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p)) f na A B wf pr).
    destruct_compose. intros pre.
    set (trexp := transform (pcuic_expand_lets_transform _) _ _) in *.
    eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ) in axfree.
    have nise' : ∥ nisErasable trexp.1 [] trexp.2 ∥.
    destruct pr as [[[]] ?], nise. sq; now eapply nisErasable_lets.
    change (trans_global_env _) with (global_env_ext_map_global_env_ext trexp.1).1 in axfree.
    clearbody trexp. clear nise pr wf Σ f. destruct trexp as [Σ f].
    pose proof pre as pre'; destruct pre' as [[[wf _]] _].
    pose proof (map_squash (pcuic_function_value wf axfree) H) as [[v ev]].
    epose proof (Transform.preservation erase_transform).
    specialize (H0 _ v pre (sq ev)).
    revert H0.
    destruct_compose. intros pre' htr.
    destruct htr as [v'' [ev' _]].
    epose proof (erase_function_to_function_strict _ f v'' _ _ _ H pre
      axfree nise').
    set (tre := transform erase_transform _ _) in *. clearbody tre.
    cbn -[transform obseq].
    red in ev'. destruct ev'.
    epose proof (Transform.preservation (verified_lambdabox_pipeline econf)).
    destruct tre as [Σ' f'].
    specialize (H2 _ v'' pre' (sq H1)) as [finalv [[evfinal] obseq]].
    exists finalv.
    split. now sq.
    have prev : Transform.pre (verified_lambdabox_pipeline econf) (Σ', v'').
    { clear -wfl pre' H1. cbn in H1.
      destruct pre' as [[] []]. split; split => //=.
      eapply EWcbvEval.eval_wellformed; eauto.
      eapply EEtaExpandedFix.isEtaExp_expanded.
      eapply (@EEtaExpandedFix.eval_etaexp wfl); eauto.
      now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
      now eapply EEtaExpandedFix.expanded_isEtaExp. }
    specialize (H0 H1).
    exact (obseq_lambdabox_function (guard := guard_impl) (Σ', f') (Σ', v'')
      econf pre' prev _ finalv ltac:(cbn; red; tauto) obseq H0
      (eval_to_value _ _ evfinal)).
  Qed.

  Lemma expand_lets_transform_env K p p' pre pre' :
    p.1 = p'.1 ->
    (transform (pcuic_expand_lets_transform K) p pre).1 =
    (transform (pcuic_expand_lets_transform K) p' pre').1.
  Proof.
    unfold transform, pcuic_expand_lets_transform. cbn. now intros ->.
  Qed.

  Opaque erase_transform.

  Lemma extends_eq Σ Σ0 Σ' : EGlobalEnv.extends Σ Σ' -> Σ = Σ0 -> EGlobalEnv.extends Σ0 Σ'.
  Proof. now intros ext ->. Qed.

  Lemma erasure_pipeline_extends_app (Σ : global_env_ext_map) t u pre econf :
    ∥ nisErasable Σ [] (tApp t u) ∥ ->
    PCUICEtaExpand.expanded Σ [] t ->
    exists pre' pre'',
    let trapp := transform (verified_erasure_pipeline econf) (Σ, PCUICAst.tApp t u) pre in
    let trt := transform (verified_erasure_pipeline econf) (Σ, t) pre' in
    let tru := transform (verified_erasure_pipeline econf) (Σ, u) pre'' in
    (EGlobalEnv.extends trt.1 trapp.1 /\ EGlobalEnv.extends tru.1 trapp.1) /\
    trapp = (trapp.1, EAst.tApp trt.2 tru.2).
  Proof.
    intros ner exp.
    unfold verified_erasure_pipeline.
    destruct_compose.
    set (K:= (fun p : global_env_ext_map => (wf_ext p -> PCUICSN.NormalizationIn p) /\ (wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p))).
    intros H.
    assert (ner' : ~ ∥ isErasable Σ [] (tApp t u) ∥).
    { destruct ner as [ner]. destruct pre, s. eapply nisErasable_spec in ner => //. eapply w. }
    destruct (expand_lets_eta_app _ _ _ K pre ner' exp) as [pre' [pre'' eq]].
    exists pre', pre''.
    set (tr := transform _ _ _).
    destruct tr eqn:heq. cbn -[transform].
    replace t0 with tr.2. assert (heq_env:tr.1=g) by now rewrite heq. subst tr.
    2:{ now rewrite heq. }
    clear heq. revert H.
    destruct_compose_no_clear. rewrite eq. intros pre3 eq2 pre4.
    epose proof (erase_eta_app _ _ _ pre3) as H0.
    pose proof (correctness (pcuic_expand_lets_transform K) (Σ, tApp t u) pre).
    destruct H as [[wtapp] [expapp Kapp]].
    pose proof (correctness (pcuic_expand_lets_transform K) (Σ, t) pre').
    destruct H as [[wtt] [expt Kt]].
    forward H0.
    { clear -wtapp ner eq. apply (f_equal snd) in eq. cbn [snd] in eq. rewrite -eq.
      destruct pre as [[wtp] rest].
      destruct ner as [ner]. eapply (nisErasable_lets (Σ, tApp t u)) in ner.
      eapply nisErasable_spec in ner => //. cbn.
      apply wtapp. apply wtp. }
    forward H0 by apply expt.
    destruct H0 as [pre'0 [pre''0 [eta [extapp [extapp' heq]]]]].
    split.
    { rewrite <- heq_env. cbn -[transform].
      pose proof (EProgram.TransformExt.preserves_obs _ _ _ (t:=verified_lambdabox_pipeline_extends' econf)).
      unfold extends_eprogram in H.
      split.
      { repeat (destruct_compose; intros). eapply verified_lambdabox_pipeline_extends.
        repeat (destruct_compose; intros). cbn - [transform].
        generalize dependent pre3. rewrite <- eq.
        cbn [transform pcuic_expand_lets_transform expand_lets_program].
        unfold expand_lets_program. cbn [fst snd].
        intros pre3. cbn in pre3. intros <-. intros.
        assert (pre'0 = H1). apply proof_irrelevance. subst H1.
        exact extapp. }
      { repeat (destruct_compose; intros). eapply verified_lambdabox_pipeline_extends.
        repeat (destruct_compose; intros). cbn - [transform].
        generalize dependent pre3. rewrite <- eq.
        cbn [transform pcuic_expand_lets_transform expand_lets_program].
        unfold expand_lets_program. cbn [fst snd].
        intros pre3. cbn in pre3. intros <-. intros.
        assert (pre''0 = H1). apply proof_irrelevance. subst H1.
        exact extapp'. } }
    set (tr := transform _ _ _).
    destruct tr eqn:heqtr. cbn -[transform]. f_equal.
    replace t1 with tr.2. subst tr.
    2:{ now rewrite heqtr; cbn. }
    clear heqtr.
    move: pre4.
    rewrite heq. intros h.
    epose proof (transform_lambda_box_eta_app _ _ _ h econf).
    forward H. { cbn [fst snd].
      clear -eq eta extapp. revert pre3 extapp.
      rewrite -eq. pose proof (correctness _ _ pre'0).
      destruct H as [? []]. cbn [fst snd] in eta |- *. revert pre'0 H H0 H1 eta. rewrite eq.
      intros. cbn -[transform] in H1. cbn -[transform].
      eapply EEtaExpandedFix.expanded_isEtaExp in H1.
      eapply EEtaExpandedFix.isEtaExp_extends; tea.
      pose proof (correctness _ _ pre3). apply H2. }
    destruct H as [prelam [prelam' eqlam]]. rewrite eqlam.
    rewrite snd_pair. clear eqlam.
    destruct_compose_no_clear.
    intros hlt heqlt. symmetry.
    apply f_equal2.
    eapply transform_lambdabox_pres_term.
    split. rewrite fst_pair.
    { destruct_compose_no_clear. intros H eq'. clear -extapp.
      eapply extends_eq; tea. do 2 f_equal. clear extapp.
      change (transform (pcuic_expand_lets_transform K) (Σ, tApp t u) pre).1 with
        (transform (pcuic_expand_lets_transform K) (Σ, t) pre').1 in pre'0 |- *.
      revert pre'0.
      rewrite -surjective_pairing. intros pre'0. f_equal. apply proof_irrelevance. }
    rewrite snd_pair.
    destruct_compose_no_clear. intros ? ?.
    eapply transform_erase_pres_term.
    rewrite fst_pair.
    { red. cbn. split => //. } reflexivity.
    destruct_compose_no_clear. intros hu heqlu.
    eapply transform_lambdabox_pres_term.
    split. rewrite fst_pair.
    { unfold run, time. destruct_compose_no_clear. intros H eq'. clear -extapp'.
      assert (pre''0 = H). apply proof_irrelevance. subst H. apply extapp'. }
    cbn [snd run]. unfold run, time.
    destruct_compose_no_clear. intros ? ?.
    eapply transform_erase_pres_term. cbn [fst].
    { red. cbn. split => //. } reflexivity.
  Qed.

Transparent erase_transform.

End PCUICErase.

Lemma compile_evalue_strip (Σer : EEnvMap.GlobalContextMap.t) p :
  firstorder_evalue Σer p ->
  EConstructorsAsBlocks.compile_evalue_box (ERemoveParams.strip Σer p) [] = ERemoveParams.compile_evalue_box_strip Σer p [].
Proof.
  move: p.
  apply: firstorder_evalue_elim; intros.
  rewrite ERemoveParams.strip_mkApps //=.
  rewrite (lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ H).
  rewrite EConstructorsAsBlocks.compile_evalue_box_mkApps.
  rewrite (ERemoveParams.compile_evalue_box_strip_mkApps (npars:=npars)).
  pose proof (lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ H).
  rewrite lookup_inductive_pars_spec //.
  rewrite !app_nil_r !skipn_map. f_equal.
  rewrite map_map.
  ELiftSubst.solve_all.
Qed.

Arguments PCUICFirstorder.firstorder_ind _ _ : clear implicits.

(** ** First-order values and the translation of cofixpoints

  The translation of cofixpoints observes values up to
  [ECoInductiveToInductive.crel]. First-order values are built from
  constructors of first-order inductive types only, which are not
  coinductive: these values are left unchanged by the translation and are
  related to themselves only. *)

Section FirstorderInd.
  Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICFirstorder.
  Import PCUICValidity.

  (** The blocks of the compilation of a first-order value belong to
      first-order inductive types. *)
  Lemma compile_value_box_firstorder_ind {Σ : global_env_ext} {wfΣ : wf Σ}
    (Σ' : E.global_context) v :
    (forall i, firstorder_ind Σ (firstorder_env Σ) i ->
      EGlobalEnv.is_coind Σ' (Kernames.inductive_mind i) = false) ->
    firstorder_value Σ [] v ->
    forall i u args, Σ ;;; [] |- v : mkApps (tInd i u) args ->
    firstorder_ind Σ (firstorder_env Σ) i ->
    ∥ ECoInductiveToInductive.firstorder_ind_value Σ'
        (compile_value_box Σ v []) ∥.
  Proof.
    intros hco fo. move: v fo.
    apply: firstorder_value_inds.
    intros i n ui u args pandi hty hargs IH nprop i' u' args' Hty Hfo.
    apply inversion_mkApps in Hty as Hcon; auto.
    destruct Hcon as (?&typ_ctor& spine).
    apply inversion_Construct in typ_ctor as (?&?&?&?&?&?&?); auto.
    pose proof d as [[d' _] _]. red in d'. cbn in *.
    unfold PCUICEnvironment.fst_ctx in *.
    eapply @PCUICInductiveInversion.Construct_Ind_ind_eq
      with (mdecl := x0) in Hty as Hty'; eauto.
    destruct Hty' as (([[[]]] & ?)  & ? & ? & ? & ? & _). subst.
    eapply PCUICSpine.typing_spine_strengthen in spine. 3: eauto.
    2: eapply PCUICInductiveInversion.declared_constructor_valid_ty; eauto.
    eapply firstorder_args in spine; eauto.
    assert (hpars : exists npars,
      pcuic_lookup_inductive_pars Σ i' = Some npars).
    { move: Hfo. rewrite /firstorder_ind /pcuic_lookup_inductive_pars.
      destruct PCUICEnvironment.lookup_env as [[]|] => //. now eexists. }
    destruct hpars as [npars hpars].
    rewrite (compile_value_box_mkApps hpars) app_nil_r.
    enough (∥ All (fun a => ECoInductiveToInductive.firstorder_ind_value Σ'
      (compile_value_box Σ a [])) args ∥) as [hall].
    { constructor. constructor; eauto.
      eapply All_skipn. eapply All_map. exact hall. }
    clear c0 c1 e0 w Hty hty hargs hpars.
    induction spine.
    - repeat constructor.
    - inv IH.
      match goal with
      | H : forall i u args, _ -> _ -> ∥ _ ∥ |- _ =>
        destruct (H _ _ _ t0 i2) as [hhd]
      end.
      destruct (IHspine ltac:(assumption)) as [htl].
      repeat constructor; auto.
  Qed.
End FirstorderInd.

Lemma erase_preserves_inductives_is_coind
  (Σ : PCUICAst.PCUICEnvironment.global_env_ext) Σ' i :
  erase_preserves_inductives Σ.1 Σ' ->
  PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i ->
  EGlobalEnv.is_coind Σ' (Kernames.inductive_mind i) = false.
Proof.
  intros hpres.
  rewrite /PCUICFirstorder.firstorder_ind /EGlobalEnv.is_coind
    /EGlobalEnv.lookup_inductive_kind /EGlobalEnv.lookup_minductive.
  destruct PCUICAst.PCUICEnvironment.lookup_env as [[|mind]|] eqn:hl => //.
  destruct (EGlobalEnv.lookup_env Σ' _) as [[|mind']|] eqn:hl' => //=.
  rewrite (hpres _ _ _ hl' hl) /=.
  move/andP => [] hfin _. now destruct PCUICAst.PCUICEnvironment.ind_finite.
Qed.

Lemma lambdabox_readback econf v :
  ETransform.readback (verified_lambdabox_etransform econf) v =
  blocks_readback v.
Proof.
  cbn. repeat (unfold ETransform.compose_readback; cbn).
  destruct (Erasure.inlining econf); cbn;
    destruct blocks_readback; reflexivity.
Qed.

Lemma strip_firstorder (Σ : EEnvMap.GlobalContextMap.t) p :
  firstorder_evalue Σ p ->
  firstorder_evalue (ERemoveParams.strip_env Σ) (ERemoveParams.strip Σ p).
Proof.
  move: p. apply: firstorder_evalue_elim; intros.
  rewrite ERemoveParams.strip_mkApps //.
  cbn -[EGlobalEnv.lookup_inductive_pars].
  rewrite (lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ H).
  eapply ERemoveParams.lookup_constructor_pars_args_strip in H.
  econstructor; tea. rewrite skipn_0 /= skipn_map.
  ELiftSubst.solve_all. len.
  rewrite skipn_map. len. rewrite length_skipn. lia.
Qed.

Lemma fo_evalue_strip (Σer : EEnvMap.GlobalContextMap.t) p :
  firstorder_evalue Σer p ->
  ECoInductiveToInductive.firstorder_ind_value Σer
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip Σer p) []) ->
  fo_evalue (ERemoveParams.strip_program (Σer, p)).
Proof.
  intros fo foi. split; [now apply strip_firstorder|].
  eapply firstorder_ind_value_is_coind; [|exact (sq foi)].
  intros kn. apply ERemoveParams.is_coind_strip.
Qed.

Lemma transform_lambda_box_firstorder (Σer : EEnvMap.GlobalContextMap.t)
  econf p pre :
  firstorder_evalue Σer p ->
  ECoInductiveToInductive.firstorder_ind_value Σer
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip Σer p) []) ->
  (transform (verified_lambdabox_pipeline econf) (Σer, p) pre).2 =
  EConstructorsAsBlocks.compile_evalue_box (ERemoveParams.strip Σer p) [].
Proof.
  intros fo foi. unfold verified_lambdabox_pipeline.
  cbn [transform compose]. unfold run, time.
  set (E := verified_lambdabox_etransform econf).
  match goal with
  | |- (transform (ETransform.tr E) ?q ?hq).2 = _ =>
    set (Q := q) in *; set (HQ := hq) in *
  end.
  have foq : fo_evalue Q by exact (fo_evalue_strip Σer p fo foi).
  pose proof HQ as [[wfs _] _].
  apply (ETransform.readback_inj E _ _ (ERemoveParams.strip Σer p)).
  - rewrite (ETransform.transform_fo E _ HQ foq).
    exact (ETransform.readback_fo E Q HQ foq).
  - rewrite lambdabox_readback.
    apply (blocks_readback_compile
      (efl := ERemoveParams.switch_no_params all_env_flags)
      (EEnvMap.GlobalContextMap.make (ERemoveParams.strip_env Σer)
        (wf_glob_fresh _ wfs))) => //.
    exact (proj1 foq).
Qed.

Lemma transform_lambda_box_firstorder_block
  (p : program EEnvMap.GlobalContextMap.t EAst.term) econf pre :
  firstorder_evalue p.1 p.2 ->
  ECoInductiveToInductive.firstorder_ind_value p.1
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip p.1 p.2) []) ->
  let tr := transform (verified_lambdabox_pipeline econf) p pre in
  firstorder_evalue_block tr.1 tr.2.
Proof.
  destruct p as [Σer p]. cbn [fst snd].
  intros fo foi.
  unfold verified_lambdabox_pipeline.
  cbn [transform compose]. unfold run, time.
  set (E := verified_lambdabox_etransform econf).
  match goal with
  | |- firstorder_evalue_block (transform (ETransform.tr E) ?q ?hq).1 _ =>
    set (Q := q) in *; set (HQ := hq) in *
  end.
  have foq : fo_evalue Q by exact (fo_evalue_strip Σer p fo foi).
  rewrite (ETransform.transform_fo E _ HQ foq).
  exact (proj1 (ETransform.preserves_fo E Q HQ foq)).
Qed.

Lemma obseq_lambdabox_firstorder (Σt Σ'v : EProgram.eprogram_env) econf
  pr pr' p' v' :
  EGlobalEnv.extends Σ'v.1 Σt.1 ->
  obseq (verified_lambdabox_pipeline econf) Σt pr p' Σ'v.2 v' ->
  firstorder_evalue Σ'v.1 Σ'v.2 ->
  ECoInductiveToInductive.firstorder_ind_value Σ'v.1
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip Σ'v.1 Σ'v.2) []) ->
  ECoInductiveToInductive.firstorder_ind_value Σt.1
    (EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip Σ'v.1 Σ'v.2) []) ->
  (transform (verified_lambdabox_pipeline econf) Σ'v pr').2 = v'.
Proof.
  intros ext obs fo foi foit.
  destruct Σt as [Σ t], Σ'v as [Σ' v]. cbn [fst snd] in *.
  rewrite transform_lambda_box_firstorder //.
  pose proof pr as [[wfΣ _] _]. pose proof pr' as [[wfΣ' wfv] _].
  have es : ERemoveParams.strip Σ' v = ERemoveParams.strip Σ v.
  { exact (ERemoveParams.strip_extends (efl := all_env_flags) eq_refl ext
      wfΣ 0 v wfv). }
  have [wfs _] := ERemoveParams.strip_program_wf (efl := all_env_flags)
    eq_refl eq_refl (Σ', v) (conj wfΣ' wfv).
  move: obs. unfold verified_lambdabox_pipeline.
  cbn [obseq compose guarded_to_unguarded_fix remove_params_optimization].
  intros [v2 [[v1 [-> ->]] obs]].
  set (E := verified_lambdabox_etransform econf) in *.
  have foq :
    fo_evalue (ERemoveParams.strip_env Σ, ERemoveParams.strip Σ v).
  { split. apply strip_firstorder. now eapply firstorder_evalue_extends.
    cbn [fst snd]. rewrite -es.
    eapply firstorder_ind_value_is_coind; [|exact (sq foit)].
    intros kn. apply ERemoveParams.is_coind_strip. }
  symmetry.
  apply (ETransform.readback_inj E _ _ (ERemoveParams.strip Σ v)).
  - unfold run, time in obs.
    cbn [transform compose guarded_to_unguarded_fix
      remove_params_optimization] in obs.
    unfold run, time in obs. cbn [fst] in obs.
    exact (ETransform.readback_obseq E (ERemoveParams.strip_program (Σ, t))
      _ p' (ERemoveParams.strip Σ v) v' foq obs).
  - rewrite lambdabox_readback -es.
    apply (blocks_readback_compile
      (efl := ERemoveParams.switch_no_params all_env_flags)
      (EEnvMap.GlobalContextMap.make (ERemoveParams.strip_env Σ')
        (wf_glob_fresh _ wfs))) => //.
    now apply strip_firstorder.
Qed.

Section pipeline_cond.

  Variable Σ : global_env_ext_map.
  Variable t : PCUICAst.term.
  Variable T : PCUICAst.term.

  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.

  Variable typing : ∥PCUICTyping.typing Σ [] t T∥.

  Variable Normalisation : (forall Σ, wf_ext Σ -> PCUICSN.NormalizationIn Σ).
  Variable econf : erasure_configuration.

  Lemma precond : pre (verified_erasure_pipeline econf) (Σ, t).
  Proof.
    hnf. destruct typing. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. eauto.
    - intros. red. intros. now eapply Normalisation.
  Qed.

  Variable v : PCUICAst.term.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Lemma precond2 : pre (verified_erasure_pipeline econf) (Σ, v).
  Proof.
    cbn. destruct typing, Heval. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. split; eauto.
      eexists.
      eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply (PCUICClassification.wcbveval_red (Σ := Σ)) in X; tea.
      eapply PCUICEtaExpand.expanded_red in X; tea. apply HΣ.
      intros ? ?; rewrite nth_error_nil => //.
    - cbn. intros wf ? ? ? ? ? ?. now eapply Normalisation.
  Qed.

  Let Σ_t := (transform (verified_erasure_pipeline econf) (Σ, t) precond).1.
  Let t_t := (transform (verified_erasure_pipeline econf) (Σ, t) precond).2.
  Let Σ_v := (transform (verified_erasure_pipeline econf) (Σ, v) precond2).1.
  Let v_t := compile_value_box (PCUICExpandLets.trans_global_env Σ) v [].

  Lemma lookup_inline
    (efl := EConstructorsAsBlocks.switch_cstr_as_blocks
      (EInlineProjections.disable_projections_env_flag
        (ERemoveParams.switch_no_params all_env_flags))) p pr kn :
    EGlobalEnv.lookup_env
      (transform (ETransform.tr (optional_etransform (Erasure.inlining econf)
        (inlining_etransform (efl := efl) eq_refl econf))) p pr).1 kn =
    option_map (if econf.(Erasure.inlining)
      then inline_global_decl (inline_env econf.(inlined_constants) p.1).2
      else fun x => x) (EGlobalEnv.lookup_env p.1 kn).
  Proof.
    clear -efl.
    destruct econf as [? ? ? []]; cbn.
    - unfold inline_program; destruct_inline_env; cbn.
      eapply EInlining.lookup_env_inline. apply pr.
    - now rewrite option_map_id.
  Qed.

  Opaque compose.
  Lemma verified_erasure_pipeline_lookup_env_in kn decl
    (efl := ERemoveParams.switch_no_params all_env_flags)
    {has_rel : has_tRel} {has_box : has_tBox} :
    EGlobalEnv.lookup_env Σ_t kn = Some decl ->
   exists decl',
    PCUICAst.PCUICEnvironment.lookup_global
      (PCUICExpandLets.trans_global_decls
        (PCUICAst.PCUICEnvironment.declarations Σ.1)) kn = Some decl'
    /\  erase_decl_equal (fun decl =>
           ECoInductiveToInductive.trans_inductive_decl
             (ERemoveParams.strip_inductive_decl
               (erase_mutual_inductive_body decl)))
           decl decl'.
  Proof.
  unfold Σ_t, verified_erasure_pipeline.
  repeat rewrite -transform_compose_assoc.
  destruct_compose; intro. cbn.
  destruct_compose; intro. cbn.
  set (erase_program _ _).
  unfold verified_lambdabox_pipeline.
  repeat rewrite -transform_compose_assoc.
  repeat (destruct_compose; intro).
  set (transform (guarded_to_unguarded_fix _) _ _) as t1.
  set (transform (remove_params_optimization _ _ _) _ _) as t2.
  (* Split the λ□ [ETransform] into its passes *)
  unfold verified_lambdabox_etransform, verified_lambdabox_etransform_tail.
  cbn [ETransform.tr ETransform.compose].
  repeat rewrite -transform_compose_assoc.
  repeat (destruct_compose; intro).
  match goal with H : pre (ETransform.tr (push_force_etransform _ _)) _ |- _ =>
    revert H end.
  repeat (rewrite -transform_compose_assoc || destruct_compose).
  intros.
  match goal with H : pre (ETransform.tr (push_force_etransform _ _)) _ |- _ =>
    generalize dependent H end.
  repeat (destruct_compose; intro).
  clear Σ_v t_t v_t.
  match goal with |- context [transform ?x t2 ?h] =>
    set (p3 := transform x t2 h) in * end.
  match goal with |- context [transform ?x p3 ?h] =>
    set (p4 := transform x p3 h) in * end.
  match goal with |- context [transform ?x p4 ?h] =>
    set (p5 := transform x p4 h) in * end.
  match goal with |- context [transform ?x p5 ?h] =>
    set (p6 := transform x p5 h) in * end.
  match goal with |- context [transform ?x p6 ?h] =>
    set (p7 := transform x p6 h) in * end.
  match goal with |- context [transform ?x p7 ?h] =>
    set (p8 := transform x p7 h) in * end.
  match goal with |- context [transform ?x p8 ?h] =>
    set (p9 := transform x p8 h) in * end.
  match goal with |- context [transform ?x p9 ?h] =>
    set (p10 := transform x p9 h) in * end.
  intros Hpf hl. revert hl.
  (* Push forces *)
  unfold transform at 1. cbn -[transform].
  rewrite EPushForce.lookup_env_force_opt.
  (* Coinductives to inductives *)
  unfold transform at 1. cbn -[transform].
  rewrite (ECoInductiveToInductive.lookup_env_trans
    (efl := EConstructorsAsBlocks.switch_cstr_as_blocks
      (EInlineProjections.disable_projections_env_flag efl))).
  { match goal with
    | H : pre (ETransform.tr (coinductive_to_inductive_etransform _)) _ |- _ =>
      apply H end. }
  set (trd := ECoInductiveToInductive.trans_decl _).
  subst p10. unfold transform at 1. cbn -[transform].
  (* Inlining *)
  subst p9. rewrite lookup_inline.
  set (eenv := inline_env _ _). clearbody eenv.
  (* Constructors as blocks *)
  subst p8. unfold transform at 1. cbn -[transform].
  rewrite EConstructorsAsBlocks.lookup_env_transform_blocks.
  set (EConstructorsAsBlocks.transform_blocks_decl _).
  subst p7. unfold transform at 1. cbn -[transform].
  (* Inline projections *)
  subst p6. unfold transform at 1. cbn -[transform].
  erewrite EInlineProjections.lookup_env_optimize.
  2: { match goal with
       | H : pre (ETransform.tr (inline_projections_etransform _ _) ▷ _) _
         |- _ => apply H end. }
  set (EInlineProjections.optimize_decl _).
  subst p5. unfold transform at 1. cbn -[transform].
  (* Remove match on box *)
  subst p4. unfold transform at 1. cbn -[transform].
  erewrite EOptimizePropDiscr.lookup_env_remove_match_on_box.
  2: { match goal with
       | H : pre (ETransform.tr (remove_match_on_box_etransform _) ▷ _) _
         |- _ => apply H end. }
  set (EOptimizePropDiscr.remove_match_on_box_decl _).
  subst p3. unfold transform at 1. cbn -[transform].
  (* Remove parameters, guarded to unguarded fixpoints *)
  subst t2. unfold transform at 1. cbn -[transform].
  subst t1. unfold transform at 1. cbn -[transform].
  rewrite EUnboxing.lookup_env_map_snd.
  set (ERemoveParams.strip_decl _).
  (* Erasure *)
  rewrite erase_global_deps_fast_spec.
  2: { cbn. intros ? He. rewrite He. eauto. }
  intro hdecl.
  set (EAstUtils.term_global_deps _).
  set (build_wf_env_from_env _ _).
  set (o := EGlobalEnv.lookup_env _ _).
  case_eq o. 2: { intros ?. inversion 1. }
  intros decl' Heq hd.
  unshelve epose proof
    (Hlookup := lookup_env_in_erase_global_deps optimized_abstract_env_impl w
      t0 _ kn _ hdecl decl' _ Heq).
  { epose proof (hfr := wf_fresh_globals _ HΣ). clear - hfr.
    revert hfr. cbn. set (Σ.1). induction 1; econstructor; eauto.
    cbn. clear -H. induction H; econstructor; eauto. }
  destruct Hlookup as [decl'' [? hdecl']]. exists decl''; split ; eauto.
  cbn in hd. injection hd as hd'. subst decl.
  set (b := Erasure.inlining econf). clearbody b.
  clear -hdecl'.
  now destruct b, decl' , decl''.
  Qed.

End pipeline_cond.


Section pipeline_theorem.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.

  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.
  Variable axfree : axiom_free Σ.
  Variable v : PCUICAst.term.

  Variable i : Kernames.inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.

  Variable Normalisation :  (forall Σ, wf_ext Σ -> PCUICSN.NormalizationIn Σ).

  Variable typing : ∥PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args)∥.

  Variable fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Lemma fo_v : PCUICFirstorder.firstorder_value Σ [] v.
  Proof.
    destruct typing, Heval. sq.
    eapply PCUICFirstorder.firstorder_value_spec; eauto.
    - eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply PCUICWcbvEval.eval_to_value; eauto.
  Qed.

  Variable econf : erasure_configuration.

  Let Σ_t := (transform (verified_erasure_pipeline econf) (Σ, t) (precond _ _ _ _ expΣ expt typing _ econf)).1.
  Let t_t := (transform (verified_erasure_pipeline econf) (Σ, t) (precond _ _ _ _ expΣ expt typing _ econf)).2.
  Let Σ_v := (transform (verified_erasure_pipeline econf) (Σ, v) (precond2 _ _ _ _ expΣ expt typing _ econf _ Heval)).1.
  Let v_t := compile_value_box (PCUICExpandLets.trans_global_env Σ) v [].

  Lemma verified_erasure_pipeline_extends (efl := ERemoveParams.switch_no_params all_env_flags)
   {has_rel : has_tRel} {has_box : has_tBox} :
   EGlobalEnv.extends Σ_v Σ_t.
  Proof.
  unfold Σ_v, Σ_t. unfold verified_erasure_pipeline.
  repeat (destruct_compose; intro). destruct typing as [typing'], Heval.
  cbn [transform compose pcuic_expand_lets_transform] in *.
  unfold run, time.
  cbn [transform erase_transform] in *.
  set (erase_program _ _). set (erase_program _ _).
  eapply verified_lambdabox_pipeline_extends.
  have [hexpΣ hexpt] :=
    PCUICExpandLetsCorrectness.expanded_expand_lets_program
      (cf := extraction_checker_flags) (Σ, t) (HΣ, (_; typing'))
      (conj expΣ expt).
  eapply extends_erase_pcuic_program;
    [exact (expanded_global_env_cofix_lambdas _ hexpΣ)
    |exact (expanded_cofix_lambdas _ _ _ hexpt)|..]; eauto.
    unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (cf := extraction_checker_flags) (Σ := (Σ.1, Σ.2))).
    { now eapply PCUICExpandLetsCorrectness.trans_wf. }
    { clear -HΣ typing'. now eapply PCUICClosedTyp.subject_closed in typing'. }
    assumption.
    now eapply PCUICExpandLetsCorrectness.trans_axiom_free.
    pose proof (PCUICExpandLetsCorrectness.expand_lets_sound typing').
    rewrite PCUICExpandLetsCorrectness.trans_mkApps in X. eapply X.
    move: fo. clear.
    { rewrite /PCUICFirstorder.firstorder_ind /=.
      rewrite PCUICExpandLetsCorrectness.trans_lookup.
      destruct PCUICAst.PCUICEnvironment.lookup_env => //.
      destruct g => //=.
      eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind.
      eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
  Qed.


  Lemma v_t_spec : v_t = (transform (verified_erasure_pipeline econf) (Σ, v) (precond2 _ _ _ _ expΣ expt typing _ econf _ Heval)).2.
  Proof.
    unfold v_t. generalize fo_v. set (pre := precond2 _ _ _ _ _ _ _ _ _ _ _) in *. clearbody pre.
    intros hv.
    unfold verified_erasure_pipeline.
    rewrite -transform_compose_assoc.
    destruct_compose.
    cbn [transform pcuic_expand_lets_transform].
    rewrite (PCUICExpandLetsCorrectness.expand_lets_fo _ _ hv).
    cbn [fst snd].
    intros h.
    destruct_compose.
    destruct typing as [typing'], Heval.
    assert (eqtr : PCUICExpandLets.trans v = v).
    { clear -hv.
      move: v hv.
      eapply PCUICFirstorder.firstorder_value_inds.
      intros.
      rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
      f_equal. ELiftSubst.solve_all. }
    assert (PCUICFirstorder.firstorder_value (PCUICExpandLets.trans_global_env Σ.1, Σ.2) [] v).
    { eapply PCUICExpandLetsCorrectness.expand_lets_preserves_fo in hv; eauto. now rewrite eqtr in hv. }

    assert (Normalisation': PCUICSN.NormalizationIn (PCUICExpandLets.trans_global Σ)).
    { destruct h as [[] ?]. apply H0. cbn. apply X0. }
    set (Σ' := build_global_env_map _).
    set (p := transform erase_transform _ _).
    pose proof (@erase_tranform_firstorder _ h v i u (List.map PCUICExpandLets.trans args) Normalisation').
    forward H0.
    { cbn. rewrite -eqtr.
      eapply (PCUICClassification.subject_reduction_eval (Σ := Σ)) in X; tea.
      eapply PCUICExpandLetsCorrectness.expand_lets_sound in X.
      now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in X. }
    forward H0. { cbn. now eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ). }
    forward H0.
    { cbn. clear -HΣ fo.
      move: fo. eapply PCUICExpandLetsCorrectness.trans_firstorder_ind. }
    forward H0. { cbn. rewrite -eqtr.
      unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ := Σ)); tea. exact extraction_checker_flags.
      apply HΣ. apply PCUICExpandLetsCorrectness.trans_wf, HΣ.
      2:{ eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X. }
      eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
      unshelve apply (PCUICClosedTyp.subject_closed typing'). }
    specialize (H0 _ eq_refl).
    rewrite /p.
    rewrite erase_transform_fo //.
    set (Σer := (transform erase_transform _ _).1).
    cbn [fst snd]. intros pre'.
    symmetry.
    destruct Heval as [Heval'].
    assert (firstorder_evalue Σer (compile_value_erase v [])).
    { apply H0. }
    assert (E : EConstructorsAsBlocks.compile_evalue_box
      (ERemoveParams.strip Σer (compile_value_erase v [])) [] =
      compile_value_box (PCUICExpandLets.trans_global_env Σ) v []).
    { rewrite compile_evalue_strip //.
      destruct pre as [[wt] ?]. destruct wt.
      apply (compile_evalue_erase (PCUICExpandLets.trans_global Σ) Σer) => //.
      { cbn. now eapply (@PCUICExpandLetsCorrectness.trans_wf extraction_checker_flags Σ). }
      destruct H0. cbn -[transform erase_transform] in H0. apply H0. }
    assert (hty : PCUICTyping.typing (PCUICExpandLets.trans_global Σ) [] v
      (PCUICAst.mkApps (PCUICAst.tInd i u)
        (List.map PCUICExpandLets.trans args))).
    { rewrite -eqtr.
      eapply (PCUICClassification.subject_reduction_eval (Σ := Σ)) in X; tea.
      eapply PCUICExpandLetsCorrectness.expand_lets_sound in X.
      now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in X. }
    unshelve epose proof (compile_value_box_firstorder_ind
      (Σ := PCUICExpandLets.trans_global Σ) Σer v _ H _ _ _ hty _) as [foi].
    { cbn. now eapply (@PCUICExpandLetsCorrectness.trans_wf
        extraction_checker_flags Σ). }
    { intros i0 hfo. eapply erase_preserves_inductives_is_coind; tea.
      apply H0. }
    { now eapply PCUICExpandLetsCorrectness.trans_firstorder_ind. }
    rewrite transform_lambda_box_firstorder // E //.
  Qed.

  Import PCUICWfEnv.


  (** The compiled value is built from constructors of first-order
      inductive types, which are not coinductive. *)
  Lemma v_t_firstorder_ind Σ' :
    erase_preserves_inductives (PCUICExpandLets.trans_global_env Σ.1) Σ' ->
    ∥ ECoInductiveToInductive.firstorder_ind_value Σ'
        (compile_value_box (PCUICExpandLets.trans_global_env Σ) v []) ∥.
  Proof.
    intros hpres. generalize fo_v. intros hv.
    pose proof typing as [typing']. pose proof Heval as [Heval'].
    assert (eqtr : PCUICExpandLets.trans v = v).
    { clear -hv.
      move: v hv.
      eapply PCUICFirstorder.firstorder_value_inds.
      intros.
      rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
      f_equal. ELiftSubst.solve_all. }
    assert (PCUICFirstorder.firstorder_value (PCUICExpandLets.trans_global_env Σ.1, Σ.2) [] v).
    { eapply PCUICExpandLetsCorrectness.expand_lets_preserves_fo in hv; eauto. now rewrite eqtr in hv. }
    assert (hty : PCUICTyping.typing (PCUICExpandLets.trans_global Σ) [] v
      (PCUICAst.mkApps (PCUICAst.tInd i u)
        (List.map PCUICExpandLets.trans args))).
    { rewrite -eqtr.
      eapply (PCUICClassification.subject_reduction_eval (Σ := Σ)) in Heval';
        tea.
      eapply PCUICExpandLetsCorrectness.expand_lets_sound in Heval'.
      now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in Heval'. }
    unshelve eapply (compile_value_box_firstorder_ind
      (Σ := PCUICExpandLets.trans_global Σ) Σ' v _ H _ _ _ hty _).
    { cbn. now eapply (@PCUICExpandLetsCorrectness.trans_wf
        extraction_checker_flags Σ). }
    { intros i0 hfo.
      eapply (erase_preserves_inductives_is_coind
        (PCUICExpandLets.trans_global Σ)); [exact hpres|exact hfo]. }
    { now eapply PCUICExpandLetsCorrectness.trans_firstorder_ind. }
  Qed.

  (** The erasure of the first-order value [v] *)
  Lemma erase_v_firstorder
    (pre1 : pre erase_transform (PCUICExpandLets.expand_lets_program (Σ, v))) :
    let ep := transform erase_transform
      (PCUICExpandLets.expand_lets_program (Σ, v)) pre1 in
    [/\ firstorder_evalue ep.1 ep.2,
      EConstructorsAsBlocks.compile_evalue_box (ERemoveParams.strip ep.1 ep.2) [] =
      compile_value_box (PCUICExpandLets.trans_global_env Σ) v [] &
      erase_preserves_inductives (PCUICExpandLets.trans_global_env Σ.1) ep.1].
  Proof.
    generalize fo_v. intros hv.
    destruct typing as [typing']. pose proof (Heval' := Heval). sq.
    assert (eqtr : PCUICExpandLets.trans v = v).
    { clear -hv.
      move: v hv.
      eapply PCUICFirstorder.firstorder_value_inds.
      intros.
      rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
      f_equal. ELiftSubst.solve_all. }
    assert (PCUICFirstorder.firstorder_value (PCUICExpandLets.trans_global_env Σ.1, Σ.2) [] v).
    { eapply PCUICExpandLetsCorrectness.expand_lets_preserves_fo in hv; eauto. now rewrite eqtr in hv. }
    assert (Normalisation': PCUICSN.NormalizationIn (PCUICExpandLets.trans_global Σ)).
    { destruct pre1 as [[w] a]. apply a. cbn. apply w. }
    set (Σ' := build_global_env_map (PCUICExpandLets.trans_global_env Σ.1)).
    set (p := transform erase_transform _ _).
    pose proof (@erase_tranform_firstorder _ pre1 v i u (List.map PCUICExpandLets.trans args) Normalisation').
    forward H0.
    { cbn.
      eapply (PCUICClassification.subject_reduction_eval (Σ := Σ)) in Heval'; tea.
      eapply PCUICExpandLetsCorrectness.expand_lets_sound in Heval'.
      now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in Heval'. }
    forward H0. { now eapply PCUICExpandLetsCorrectness.trans_axiom_free. }
    forward H0.
    { cbn. clear -HΣ fo.
      move: fo.
      rewrite /PCUICFirstorder.firstorder_ind /= PCUICExpandLetsCorrectness.trans_lookup /=.
      destruct PCUICAst.PCUICEnvironment.lookup_env => //. destruct g => //=.
      eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind. eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
    forward H0. { cbn. rewrite -eqtr.
      unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ := Σ)); tea. exact extraction_checker_flags.
      apply HΣ. apply PCUICExpandLetsCorrectness.trans_wf, HΣ.
      2:{ rewrite eqtr. eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in Heval'. }
      eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
      unshelve apply (PCUICClosedTyp.subject_closed typing'). now rewrite eqtr. }
    specialize (H0 _ eq_refl).
    assert (eqp : p.2 = compile_value_erase v []).
    { rewrite /p.
      rewrite (erase_transform_fo_gen _ pre1
        ltac:(cbn; rewrite eqtr; exact H) _ eq_refl).
      cbn. now rewrite eqtr. }
    cbn zeta. rewrite eqp.
    set (Σer := (transform erase_transform _ _).1) in *.
    assert (firstorder_evalue Σer (compile_value_erase v [])).
    { apply H0. }
    split => //.
    - rewrite compile_evalue_strip //.
      apply (compile_evalue_erase (PCUICExpandLets.trans_global Σ) Σer) => //.
      { cbn. now eapply (@PCUICExpandLetsCorrectness.trans_wf
          extraction_checker_flags Σ). }
      apply H0.
    - apply H0.
  Qed.

  Lemma verified_erasure_pipeline_firstorder_evalue_block :
    firstorder_evalue_block Σ_v v_t.
  Proof.
    rewrite v_t_spec.
    unfold Σ_v.
    unfold verified_erasure_pipeline.
    repeat rewrite -transform_compose_assoc.
    destruct_compose.
    cbn [transform pcuic_expand_lets_transform].
    intros pre1. destruct_compose. intros pre2.
    destruct (erase_v_firstorder pre1) as [fov E hpres].
    destruct (v_t_firstorder_ind _ hpres) as [foi].
    apply transform_lambda_box_firstorder_block => //.
    now rewrite E.
  Qed.

  Lemma verified_erasure_pipeline_theorem :
    ∥ eval (wfl := extraction_wcbv_flags) Σ_t t_t v_t ∥.
  Proof.
    hnf.
    pose proof (preservation (verified_erasure_pipeline econf) (Σ, t)) as Hcorr.
    unshelve eapply Hcorr in Heval as Hev. eapply precond; eauto.
    destruct Hev as [v' [[H1] H2]].
    move: H2.
    rewrite v_t_spec.
    set (pre := precond2 _ _ _ _ _ _ _ _ _ _ _) in *. clearbody pre.
    subst v_t Σ_t t_t.
    revert H1.
    unfold verified_erasure_pipeline.
    intros.
    revert H1 H2. clear Hcorr.
    intros ev obs.
    cbn [obseq compose] in obs.
    unfold run, time in obs.
    decompose [ex and prod] obs. clear obs.
    subst.
    cbn [obseq compose erase_transform] in *.
    cbn [obseq compose pcuic_expand_lets_transform] in *.
    subst.
    move: ev b.
    repeat destruct_compose.
    intros.
    move: b.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    cbn [transform erase_transform] in *.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    unfold run, time.
    cbn [obseq compose constructors_as_blocks_transformation] in *.
    cbn [obseq run compose rebuild_wf_env_transform] in *.
    cbn [obseq compose inline_projections_optimization] in *.
    cbn [obseq compose remove_match_on_box_trans] in *.
    cbn [obseq compose remove_params_optimization] in *.
    cbn [obseq compose guarded_to_unguarded_fix] in *.
    cbn [obseq compose erase_transform] in *.
    cbn [obseq compose pcuic_expand_lets_transform] in *.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    cbn [transform erase_transform] in *.
    destruct Heval.
    pose proof typing as [typing']. pose proof typing as [typing''].
    eapply PCUICClassification.subject_reduction_eval in typing'; tea.
    eapply PCUICExpandLetsCorrectness.pcuic_expand_lets in typing'.
    rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in typing'.
    destruct H1.
    (* pose proof (abstract_make_wf_env_ext) *)
    unfold PCUICExpandLets.expand_lets_program.
    set (em := build_global_env_map _).
    unfold erase_program.
    set (f := map_squash _ _). cbn in f.
    destruct H. destruct s as [[]].
    set (wfe := build_wf_env_from_env em (map_squash (PCUICTyping.wf_ext_wf (em, Σ.2)) (map_squash fst (conj (sq (w0, s)) a).p1))).
    destruct Heval.
    eapply (ErasureFunctionProperties.firstorder_erases_deterministic optimized_abstract_env_impl wfe Σ.2) in b0. 3:tea.
    2:{ cbn. reflexivity. }
    2:{ eapply PCUICExpandLetsCorrectness.trans_wcbveval. eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
        clear -typing'' HΣ. now eapply PCUICClosedTyp.subject_closed in typing''.
        eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X0. }
    (* 2:{ clear -fo. cbn. now eapply (PCUICExpandLetsCorrectness.trans_firstorder_ind Σ). }
        eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X. } *)
    2:{ clear -fo. revert fo. rewrite /PCUICFirstorder.firstorder_ind /=.
        rewrite PCUICExpandLetsCorrectness.trans_lookup.
        destruct PCUICAst.PCUICEnvironment.lookup_env => //.
        destruct g => //=.
        eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind. eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
    2:{ apply HΣ. }
    2:{ apply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    destruct (erase_v_firstorder (conj (sq (w0, s)) a)) as [fov E hpres].
    destruct (v_t_firstorder_ind _ hpres) as [foiv].
    rewrite -E in foiv.
    match goal with
    | |- obseq _ ?P _ _ _ _ -> _ =>
      pose proof (v_t_firstorder_ind P.1) as foit
    end.
    forward foit.
    { apply (erase_transform_preserves_inductives
        (PCUICExpandLets.expand_lets_program (Σ, t))). }
    destruct foit as [foit]. rewrite -E in foit.
    rewrite b0. intros obs. constructor.
    match goal with [ H1 : eval _ _ ?v1 |- eval _ _ ?v2 ] => enough (v2 = v1) as -> by exact ev end.
    eapply obseq_lambdabox_firstorder; revgoals.
    1:exact foit. 1:exact foiv. 1:exact fov.
    unfold erase_pcuic_program. cbn [fst snd]. exact obs.
    Unshelve. all:eauto.
    2:{ eapply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    clear obs b0 ev e w.
    have [hexpΣ hexpt] :=
      PCUICExpandLetsCorrectness.expanded_expand_lets_program
        (cf := extraction_checker_flags) (Σ, t) (HΣ, (_; typing''))
        (conj expΣ expt).
    eapply extends_erase_pcuic_program;
      [exact (expanded_global_env_cofix_lambdas _ hexpΣ)
      |exact (expanded_cofix_lambdas _ _ _ hexpt)|..]. cbn.
    unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (cf := extraction_checker_flags) (Σ := (Σ.1, Σ.2))).
    { now eapply PCUICExpandLetsCorrectness.trans_wf. }
    { clear -HΣ typing''. now eapply PCUICClosedTyp.subject_closed in typing''. }
    cbn. 2:cbn. exact X0.
    now eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ).
    pose proof (PCUICExpandLetsCorrectness.expand_lets_sound typing'').
    rewrite PCUICExpandLetsCorrectness.trans_mkApps in X1. eapply X1.
    cbn. eapply (PCUICExpandLetsCorrectness.trans_firstorder_ind Σ); eauto.
  Qed.

End pipeline_theorem.
