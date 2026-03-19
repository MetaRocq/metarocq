(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Erasure Require Import EPrimitive ELiftSubst EGlobalEnv EWcbvEval Extract Prelim
     ESubstitution EArities EDeps.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICGlobalEnv PCUICAst
  PCUICAstUtils PCUICConversion PCUICSigmaCalculus
  PCUICClosed PCUICClosedTyp
  PCUICWeakeningEnv PCUICWeakeningEnvTyp
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICLiftSubst
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICCanonicity
  PCUICUnivSubst PCUICViews
  PCUICCumulativity PCUICSafeLemmata
  PCUICArities PCUICInductiveInversion
  PCUICContextConversion PCUICContextConversionTyp
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICValidity
  PCUICContexts PCUICEquality PCUICSpine
  PCUICInductives.
From MetaRocq.PCUIC Require Import PCUICTactics.

From Equations.Prop Require Import DepElim.

Local Set Keyed Unification.

Local Existing Instance config.extraction_checker_flags.

(* Properties of PCUIC *)

Lemma isLambda_subst_instance t u : isLambda t -> isLambda t@[u].
Proof. destruct t => //. Qed.

Lemma wf_local_rel_conv:
  forall Σ : global_env × universes_decl,
    wf Σ.1 ->
    forall Γ Γ' : context,
      All2_fold (conv_decls cumulAlgo_gen Σ) Γ Γ' ->
      forall Γ0 : context, wf_local Σ Γ' -> wf_local_rel Σ Γ Γ0 -> wf_local_rel Σ Γ' Γ0.
Proof.
  intros Σ wfΣ Γ Γ' X1 Γ0 ? w0.
  apply All_local_env_impl_ind with (1 := w0) => Δ j wfΓ' Hj.
  apply lift_typing_impl with (1 := Hj) => t T HT.
  eapply context_conversion with (Γ ,,, Δ); eauto.
  - eapply All_local_env_app; eauto.
  - eapply conv_context_app_same; eauto.
Qed.

Lemma conv_context_wf_local_app {A B A'} {Σ : global_env_ext} {wfΣ : wf Σ} :
  wf_local Σ (A ,,, B) -> wf_local Σ A' -> conv_context cumulAlgo_gen Σ A A' -> wf_local Σ (A' ,,, B).
Proof.
  intros wfab wfa' cv.
  eapply All_local_env_app => //.
  eapply wf_local_rel_conv; tea.
  now eapply All_local_env_app_inv.
Qed.


Lemma type_closed_subst {Σ t T} u : wf_ext Σ ->
  Σ ;;; [] |- t : T ->
  subst1 t 0 u = PCUICCSubst.csubst t 0 u.
Proof.
  intros wfΣ tc.
  apply subject_closed in tc; auto.
  rewrite PCUICCSubst.closed_subst; auto.
Qed.


(** Generic Properties of erasure *)
Lemma erases_ext_eq Σ Σ' Γ Γ' t1 t1' t2 t2' :
  Σ ;;; Γ |- t1 ⇝ℇ t2 ->
  Σ = Σ'-> Γ = Γ' -> t1 = t1' -> t2 = t2' ->
  Σ' ;;; Γ' |- t1' ⇝ℇ t2'.
Proof.
  intros. now subst.
Qed.

(** ** Erasure and applications  *)

Lemma erases_App (Σ : global_env_ext) Γ f L t :
  erases Σ Γ (tApp f L) t ->
  (t = EAst.tBox × squash (isErasable Σ Γ (tApp f L)))
  \/ exists f' L', t = EAst.tApp f' L' /\
            erases Σ Γ f f' /\
            erases Σ Γ L L'.
Proof.
  intros. generalize_eqs H.
  revert f L.
  inversion H; intros; try congruence; subst.
  - invs H4. right. repeat eexists; eauto.
  - left. split; eauto. now sq.
Qed.

Lemma erases_mkApps (Σ : global_env_ext) Γ f f' L L' :
  erases Σ Γ f f' ->
  Forall2 (erases Σ Γ) L L' ->
  erases Σ Γ (mkApps f L) (EAst.mkApps f' L').
Proof.
  intros. revert f f' H; induction H0; cbn; intros; eauto.
  eapply IHForall2. econstructor. eauto. eauto.
Qed.

Lemma erases_mkApps_inv (Σ : global_env_ext) Γ f L t :
  Σ;;; Γ |- mkApps f L ⇝ℇ t ->
  (exists L1 L2 L2', L = L1 ++ L2 /\
                squash (isErasable Σ Γ (mkApps f L1)) /\
                erases Σ Γ (mkApps f L1) EAst.tBox /\
                Forall2 (erases Σ Γ) L2 L2' /\
                t = EAst.mkApps EAst.tBox L2'
  )
  \/ exists f' L', t = EAst.mkApps f' L' /\
            erases Σ Γ f f' /\
            Forall2 (erases Σ Γ) L L'.
Proof.
  intros. revert f H ; induction L; cbn in *; intros.
  - right. exists t, []. cbn. repeat split; eauto.
  - eapply IHL in H; eauto.
    destruct H as [ (? & ? & ? & ? & ? & ? & ? & ?)  | (? & ? & ? & ? & ?)].
    + subst. left. exists (a :: x), x0, x1. destruct H0. repeat split; eauto.
    + subst.
      eapply erases_App in H0 as [ (-> & []) | (? & ? & ? & ? & ?)].
      * left. exists [a], L, x0. cbn. repeat split; eauto. now constructor.
      * subst. right. exists x1, (x2 :: x0). repeat split; eauto.
Qed.

Lemma is_FixApp_erases Σ Γ t t' :
  Σ;;; Γ |- t ⇝ℇ t' ->
  negb (isFixApp t) -> negb (EAstUtils.isFixApp t').
Proof.
  induction 1; cbn; try congruence.
  - unfold isFixApp, head in *. cbn. clear IHerases2.
    cbn. rewrite PCUICAstUtils.fst_decompose_app_rec.
    unfold EAstUtils.isFixApp. now rewrite EAstUtils.head_tApp.
Qed.

Lemma is_ConstructApp_erases Σ Γ t t' :
  Σ;;; Γ |- t ⇝ℇ t' ->
  negb (isConstructApp t) -> negb (EAstUtils.isConstructApp t').
Proof.   induction 1; cbn; try congruence.
- unfold isConstructApp in *. clear IHerases2.
  cbn. rewrite head_tapp.
  unfold EAstUtils.isConstructApp in *.
  cbn. now rewrite EAstUtils.head_tApp.
Qed.

Lemma is_PrimApp_erases Σ Γ t t' :
  Σ;;; Γ |- t ⇝ℇ t' ->
  negb (isPrimApp t) -> negb (EAstUtils.isPrimApp t').
Proof.   induction 1; cbn; try congruence.
- unfold isPrimApp in *. clear IHerases2.
  cbn. rewrite head_tapp.
  unfold EAstUtils.isPrimApp in *.
  cbn. now rewrite EAstUtils.head_tApp.
Qed.

Lemma erases_isLambda {Σ Γ t u} :
  Σ ;;; Γ |- t ⇝ℇ u -> isLambda t -> EAst.isLambda u || EAstUtils.isBox u.
Proof.
  intros hf.
  induction hf => //.
Qed.

(** ** Preliminaries on arities and proofs

  The erasure relation enjoys substitutivity with terms and universes, weakening, closure under reduction.
  It also preserves scoping of terms

*)

(** *** Erasure is stable under context conversion *)

Lemma Is_type_conv_context (Σ : global_env_ext) (Γ : context) t (Γ' : context) :
  wf Σ -> wf_local Σ Γ -> wf_local Σ Γ' ->
  conv_context cumulAlgo_gen Σ Γ Γ' -> isErasable Σ Γ t -> isErasable Σ Γ' t.
Proof.
  intros.
  destruct X3 as (? & ? & ?). red.
  exists x. split. eapply context_conversion. 3:eapply X2. all:eauto.
  destruct s as [? | [u []]].
  - left. eauto.
  - right. exists u. split; eauto. eapply context_conversion in X2; eauto.
Qed.

#[global]
Hint Resolve Is_type_conv_context : core.

Lemma erases_context_conversion :
  env_prop
  (fun (Σ : global_env_ext) (Γ : context) (t T : PCUICAst.term) =>
      forall Γ' : context,
        conv_context cumulAlgo_gen Σ Γ Γ' ->
        wf_local Σ Γ' ->
        forall t', erases Σ Γ t t' -> erases Σ Γ' t t')
  (fun (Σ : global_env_ext) (Γ : context) j =>
    forall Γ' : context,
      conv_context cumulAlgo_gen Σ Γ Γ' ->
      wf_local Σ Γ' ->
      lift_wf_term (fun t => forall t', erases Σ Γ t t' -> erases Σ Γ' t t') j)
  (fun Σ Γ => wf_local Σ Γ)
        .
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; auto.
  { destruct X as (Htm & u & (_ & Hty) & _). split; eauto. destruct j_term => // ?. cbn in *. now eapply Htm. }
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else invs H end.
  all: try now (econstructor; eauto).
  - econstructor. eapply h_forall_Γ'0.
    econstructor. eauto. now constructor.
    constructor; auto.
    eapply lift_typing_impl with (1 := X0) => ?? HT.
    eapply context_conversion. 3:eauto. all:eauto.
  - econstructor.
    now edestruct forall_Γ'; tea; eauto.
    eapply h_forall_Γ'0.
    econstructor. eauto. now constructor.
    constructor; auto.
    eapply lift_typing_impl with (1 := X0) => ?? HT.
    eapply context_conversion. 3:eauto. all:eauto.
  - econstructor. eauto. eauto.
    eapply (All2i_All2_All2 X6 X5).
    intros ? ? ? (? & ?) (? & ? & (? & ?) & ? & ?) (? & ?).
    split. 2: assumption.
    rewrite <- (PCUICCasesContexts.inst_case_branch_context_eq a).
    eapply e.
    + rewrite case_branch_type_fst.
      eapply conv_context_app_same; eauto.
    + eapply typing_wf_local.
      eapply context_conversion.
      * exact t1.
      * eapply conv_context_wf_local_app; eauto.
      * eapply conv_context_app_same; eauto.
    + now rewrite case_branch_type_fst (PCUICCasesContexts.inst_case_branch_context_eq a).
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. exact X3. eassumption.
    intros. cbn in *.
    destruct X7 as [IH []].
    split; intuition auto.
    eapply IH.
    + subst types.
      eapply conv_context_app_same; auto.
    + eapply conv_context_wf_local_app; eauto.
    + assumption.
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. exact X3. eassumption.
    intros. cbn in *.
    destruct X7 as [IH []].
    split; intuition auto.
    eapply IH.
    + subst types. eapply conv_context_app_same; auto.
    + subst types. eapply conv_context_wf_local_app; eauto.
    + assumption.
  - econstructor. depelim H3; constructor. depelim X4; depelim X1; constructor; eauto.
    solve_all.
Qed.


(** ** isErasable is stable under universe instantiation *)

Lemma isErasable_subst_instance (Σ : global_env_ext) Γ T univs u :
  wf_ext_wk Σ ->  wf_local Σ Γ ->
  wf_local (Σ.1, univs) (subst_instance u Γ) ->
  isErasable Σ Γ T ->
  consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
  isErasable (Σ.1,univs) (subst_instance u Γ) (subst_instance u T).
Proof.
  intros. destruct X2 as (? & ? & [ | (? & ? & ?)]).
  - eapply typing_subst_instance in t; eauto.
    eexists. split.
    + eapply t; tas.
    + left. eapply isArity_subst_instance. eauto.
  - eapply typing_subst_instance in t; eauto.
    eexists. split.
    + eapply t; tas.
    + right.
      eapply typing_subst_instance in t0; eauto.
      eexists. split.
      * eapply t0; tas.
      * now rewrite is_propositional_subst_instance.
Qed.

(** ** Erasure is stable under instantiation of universes  *)

Lemma fix_context_subst_instance:
  forall (mfix : list (BasicAst.def term)) (u : Instance.t),
    map (map_decl (subst_instance u))
        (fix_context mfix) =
    fix_context
      (map
         (map_def (subst_instance u)
                  (subst_instance u)) mfix).
Proof.
  intros mfix. unfold fix_context. intros.
  rewrite map_rev.
  rewrite mapi_map.
  rewrite map_mapi. f_equal. eapply mapi_ext. intros. cbn.
  unfold map_decl. cbn. unfold vass.
  rewrite subst_instance_lift. reflexivity.
Qed.

Lemma erases_subst_instance0
  : env_prop (fun Σ Γ t T => wf_ext_wk Σ ->
                           forall t' u univs,
                             wf_local (Σ.1, univs) (subst_instance u Γ) ->
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (subst_instance u Γ) |- subst_instance u t ⇝ℇ t')
    (fun Σ Γ j => wf_ext_wk Σ ->
        forall u univs,
        wf_local (Σ.1, univs) (subst_instance u Γ) ->
        consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
        lift_wf_term (fun t => forall t', Σ ;;; Γ |- t ⇝ℇ t' -> (Σ.1,univs) ;;; (subst_instance u Γ) |- subst_instance u t ⇝ℇ t') j)
    (fun Σ Γ => wf_local Σ Γ).
Proof.
  apply typing_ind_env; intros; cbn -[subst_instance] in *; auto.
  { destruct X as (Htm & s & (_ & Hty) & _). split; eauto. destruct j_term => // ?. cbn in *. now eapply Htm. }
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else invs H end.
  all: try now (econstructor; eauto 2 using isErasable_subst_instance).
  - cbn. econstructor.
    eapply H in X3; eauto. apply X3.
    cbn. econstructor. eauto.
    eapply lift_typing_fu_impl with (1 := X0) => // ?? HT; eauto using relevance_subst_opt.
    now apply typing_subst_instance.
  - cbn. econstructor.
    now edestruct X1; tea; eauto.
    eapply H in X3; eauto. exact X3.
    cbn. econstructor. eauto.
    eapply lift_typing_fu_impl with (1 := X0) => // ?? HT; eauto using relevance_subst_opt.
    now apply typing_subst_instance.
  - unfold subst_instance.
    cbn [subst_instance_constr]. econstructor; eauto.
    eapply All2_map_left.
    eapply (All2i_All2_All2 X6 X9).
    intros ? ? [] [] (? & ? & (? & ?) & (? & ?)) (? & ?). split.
    2: now cbn in *.
    cbn -[app_context] in *. fold (subst_instance u bbody).
    eapply erases_ext_eq.
    2, 4, 5: reflexivity. eapply e; eauto.
    + eapply typing_subst_instance_wf_local; eauto.
      destruct Σ; eassumption.
    + rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
    + rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
      rewrite subst_instance_app. unfold app_context. f_equal.
      now rewrite inst_case_branch_context_subst_instance.
  - assert (Hw :  wf_local (Σ.1, univs) (subst_instance u (Γ ,,, types))).
    { eapply typing_subst_instance_wf_local; eauto. destruct Σ as [Σ Σu].
      now eapply All_mfix_wf. }

    cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left. eapply X3. eassumption.
    intros d d' [IH []]; cbn in *.
    split; auto.
    now eapply isLambda_subst_instance.
    eapply IH in e1.
    rewrite subst_instance_app in e1. subst types. 2:eauto.
    eapply erases_ctx_ext. eassumption. unfold app_context.
    f_equal.
    eapply fix_context_subst_instance. all: eauto.

  - assert (Hw :  wf_local (Σ.1, univs) (subst_instance u (Γ ,,, types))).
    { eapply typing_subst_instance_wf_local; eauto. destruct Σ as [Σ Σu].
      now eapply All_mfix_wf. }

  cbn. econstructor; eauto.
  eapply All2_map_left.
  eapply All2_impl. eapply All2_All_mix_left. eapply X3. eassumption.
  intros d d' [IH (? & ? & ?)]; cbn in *.
  repeat split; eauto.
  eapply IH in e1.
  rewrite subst_instance_app in e1; eauto. subst types. 2:eauto.
  eapply erases_ctx_ext. eassumption. unfold app_context.
  f_equal.
  eapply fix_context_subst_instance. all: eauto.

  - cbn; constructor. depelim H5.
    depelim X1; depelim X4; repeat constructor; cbn; eauto.
    solve_all.
Qed.

Lemma erases_subst_instance :
  forall Σ : global_env_ext, wf_ext_wk Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall t' u univs,
  wf_local (Σ.1, univs) (subst_instance u Γ) ->
   consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (subst_instance u Γ) |- subst_instance u t ⇝ℇ t'.
Proof.
  intros Σ X Γ X0 t T X1 t' u univs H H0 H1.
  unshelve eapply (erases_subst_instance0 Σ _ Γ _ _ _); tea; eauto.
Qed.

Lemma erases_subst_instance'' Σ φ Γ t T u univs t' :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, univs) ;;; Γ |- t ⇝ℇ t' ->
  (Σ, φ) ;;; subst_instance u Γ
            |- subst_instance u t ⇝ℇ  t'.
Proof.
  intros X X0. intros.
  eapply (erases_subst_instance (Σ, univs)); tas.
  eapply typing_wf_local; eassumption. eauto.
  eapply typing_wf_local.
  eapply typing_subst_instance''; eauto.
Qed.

Lemma erases_subst_instance_decl Σ Γ t T c decl u t' :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |- t : T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |- t ⇝ℇ t' ->
   Σ ;;; subst_instance u Γ
            |- subst_instance u t ⇝ℇ  t'.
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  eapply erases_subst_instance''; tea. split; tas.
  eapply weaken_lookup_on_global_env'; tea.
Qed.

(** Erasure preserves scoping *)

Lemma erases_closed Σ Γ  a e : PCUICAst.closedn #|Γ| a -> Σ ;;; Γ |- a ⇝ℇ e -> ELiftSubst.closedn #|Γ| e.
Proof.
  remember #|Γ| as Γl eqn:Heq.
  intros cla era.
  revert Γ e era Heq.
  pattern Γl, a.
  match goal with
  |- ?P Γl a => simpl; eapply (term_closedn_list_ind P); auto; clear
  end; simpl; intros; subst k;
    match goal with [H:erases _ _ _ _ |- _] => depelim H end; trivial;
    simpl; try solve [solve_all].
  - now apply Nat.ltb_lt.
  - apply andb_and. split; eauto.
    eapply All_forallb. unfold tCaseBrsProp_k in X0.
    eapply All2_All_mix_left in X1; eauto.
    close_Forall. intros [] []. cbn in *. intros.
    solve_all. subst. rewrite length_map. eapply b0. eauto.
    rewrite app_context_length. cbn.
    now rewrite inst_case_branch_context_length.
  - epose proof (All2_length X0).
    solve_all. destruct b. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite length_app fix_context_length.
  - epose proof (All2_length X0).
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite length_app fix_context_length.
  - depelim H. depelim X0; solve_all.
    depelim X; solve_all. eapply primProp_impl_test_prim.
    constructor; intuition eauto. solve_all.
Qed.

(** Auxilliary notion of wellformedness on PCUIC to prove that erased terms are wellformed *)

Section wellscoped.
  Import PCUICAst PCUICGlobalEnv.

  Definition lookup_constant Σ kn :=
    match PCUICEnvironment.lookup_env Σ kn with
    | Some (ConstantDecl d) => Some d
    | _ => None
    end.
  Import MonadNotation.

  Section Def.
  Context (Σ : global_env).
  Import ssrbool.

  Definition wf_brs ind brsl :=
    match lookup_inductive Σ ind with
    | Some (mib, oib) => #|oib.(ind_ctors)| == brsl
    | None => false
    end.

  Fixpoint wellformed (t : term) : bool :=
  match t with
  | tRel i => true
  | tPrim p => test_prim wellformed p
  | tEvar ev args => List.forallb (wellformed) args
  | tLambda _ N M => wellformed N && wellformed M
  | tApp u v => wellformed u && wellformed v
  | tLetIn na b ty b' => wellformed b && wellformed ty && wellformed b'
  | tCase ind p c brs =>
    let brs' := forallb (wellformed ∘ bbody) brs in
    wf_brs ind.(ci_ind) #|brs| && wellformed c && brs'
  | tProj p c => isSome (lookup_projection Σ p) && wellformed c
  | tFix mfix idx =>
    (idx <? #|mfix|) &&
    List.forallb (test_def (wellformed) (fun b => (isLambda b) && wellformed b)) mfix
  | tCoFix mfix idx =>
    (idx <? #|mfix|) &&
    List.forallb (test_def wellformed wellformed) mfix
  | tConst kn _ => isSome (lookup_constant Σ kn)
  | tConstruct ind c _ => isSome (lookup_constructor Σ ind c)
  | tVar _ => true
  | tInd ind _  => isSome (lookup_inductive Σ ind)
  | tSort _ => true
  | tProd na ty1 ty2 => wellformed ty1 && wellformed ty2
  end.
  End Def.

  Arguments lookup_projection : simpl never.
  Lemma typing_wellformed :
    env_prop (fun Σ Γ a A => wellformed Σ a)
        (fun Σ _ j => lift_wfb_term (wellformed Σ) j)
        (fun Σ Γ => True).
  Proof.
    eapply typing_ind_env; cbn; intros => //.
    { destruct X as (Htm & _ & (_ & Hty) & _). unfold lift_wfb_term. rewrite Hty andb_true_r. destruct j_term => //. apply Htm. }
    all:try unfold lift_wfb_term in *; rtoProp; intuition auto.
    - unshelve eapply declared_constant_to_gen in H0; eauto.
      red in H0. rewrite /lookup_constant /lookup_constant_gen H0 //.
    - unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      unfold lookup_inductive. now rewrite (declared_inductive_lookup_gen isdecl).
    - unshelve eapply declared_constructor_to_gen in isdecl; eauto.
      unfold lookup_constructor. rewrite (declared_constructor_lookup_gen isdecl) //.
    - unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      rewrite /wf_brs.
      unfold lookup_inductive. rewrite (declared_inductive_lookup_gen isdecl).
      red in H9. apply Forall2_length in H9. now apply Nat.eqb_eq.
    - red in H9. eapply Forall2_All2 in H9.
      eapply All2i_All2_mix_left in X4; tea. clear H9.
      solve_all.
    - unshelve eapply declared_projection_to_gen in isdecl; eauto.
      unfold lookup_projection. now rewrite (declared_projection_lookup_gen isdecl).
    - now eapply nth_error_Some_length, Nat.ltb_lt in H0.
    - move/andb_and: H2 => [] hb _.
      unfold on_def_body, on_def_type, test_def in *. cbn in *.
      solve_all.
    - now eapply nth_error_Some_length, Nat.ltb_lt in H0.
    - unfold on_def_body, on_def_type, test_def in *. cbn in *.
      solve_all.
    - depelim X0; solve_all; constructor; eauto.
  Qed.

  Lemma welltyped_wellformed {Σ : global_env_ext} {wfΣ : wf Σ} {Γ a} : welltyped Σ Γ a -> wellformed Σ a.
  Proof.
    intros []. eapply typing_wellformed; tea.
  Qed.

End wellscoped.

Import EWellformed.

Section trans_lookups.
  Context {Σ : global_env_ext} {Σ'} (g : globals_erased_with_deps Σ Σ').


  (* TODO simplify using lookup_*_declared lemmas *)
  Lemma trans_lookup_constant kn : isSome (lookup_constant Σ kn) -> isSome (EGlobalEnv.lookup_constant Σ' kn).
  Proof using g.
    unfold lookup_constant.
    destruct (lookup_env Σ kn) as [[]|] eqn:hl => //.
    destruct g as [? _]. destruct (H kn c) as [? [? ?]].
    eapply declared_constant_from_gen; eauto.
    erewrite EGlobalEnv.declared_constant_lookup; eauto.
  Qed.

  Lemma trans_lookup_inductive kn mib oib :
    lookup_inductive Σ kn = Some (mib, oib) ->
    exists mib' oib', EGlobalEnv.lookup_inductive Σ' kn = Some (mib', oib') /\ #|oib.(ind_ctors)| = #|oib'.(EAst.ind_ctors)|.
  Proof. destruct g.
    destruct (lookup_inductive Σ kn) as [[]|] eqn:hl => /= // [=]. intros -> ->.
    eapply lookup_inductive_declared in hl.
    eapply declared_inductive_from_gen in hl.
    specialize (H0 kn mib oib hl) as [? [? [d er]]].
    exists x, x0.
    split. now rewrite (EGlobalEnv.declared_inductive_lookup d).
    depelim er. depelim hl. depelim d.
    eapply Forall2_nth_error_left in H4 as [x' []]; tea.
    rewrite H3 in H4. noconf H4. depelim H6. now apply Forall2_length in H4.
  Qed.

  Lemma trans_lookup_constructor kn c : isSome (lookup_constructor Σ kn c) -> isSome (EGlobalEnv.lookup_constructor Σ' kn c).
  Proof using g.
    destruct g.
    destruct (lookup_constructor Σ kn c) as [[[]]|] eqn:hl => /= // _.
    eapply (lookup_constructor_declared_gen (id:=(kn,c))) in hl.
    eapply declared_constructor_from_gen in hl.
    specialize (H0 _ _ _ hl.p1) as [mdecl' [idecl' [decli hl']]].
    destruct hl', hl. cbn in * |-.
    destruct H2. eapply Forall2_nth_error_left in H0 as [? [? [erc erp]]]; tea.
    eapply Forall2_nth_error_left in erc as [? [? ?]]; tea.
    destruct decli as [declm decli]. rewrite H0 in decli. noconf decli.
    erewrite (EGlobalEnv.declared_constructor_lookup (id:=(kn,c))) => //.
    split; tea. split; tea.
  Qed.

  Lemma lookup_projection_lookup_constructor {p mdecl idecl cdecl pdecl} :
    lookup_projection Σ p = Some (mdecl, idecl, cdecl, pdecl) ->
    lookup_constructor Σ p.(proj_ind) 0 = Some (mdecl, idecl, cdecl).
  Proof using Type.
    rewrite /lookup_projection /lookup_projection_gen /lookup_constructor.
    destruct lookup_constructor_gen as [[[? ?] ?]|]=> //=.
    now destruct nth_error => //.
  Qed.

  Lemma trans_lookup_projection p :
    isSome (lookup_projection Σ p) ->
    isSome (EGlobalEnv.lookup_projection Σ' p).
  Proof using g.
    destruct g.
    destruct (lookup_projection Σ p) as [[[[]]]|] eqn:hl => /= // _.
    pose proof (lookup_projection_lookup_constructor hl) as lc.
    unfold lookup_projection, lookup_projection_gen in hl. unfold lookup_constructor in lc.
    rewrite lc in hl.
    eapply (lookup_constructor_declared_gen (id:=(_,_))) in lc.
    eapply declared_constructor_from_gen in lc.
    specialize (H0 _ _ _ lc.p1) as [mdecl' [idecl' [decli hl']]].
    destruct hl', lc.
    destruct H2.
    destruct (nth_error (ind_projs o)) eqn:hnth => //. noconf hl.
    eapply Forall2_nth_error_left in H0 as [? [? [erc [erp ?]]]]; tea.
    destruct decli. rewrite H7 in H0; noconf H0.
    eapply Forall2_nth_error_left in erc as [? [? ?]]; tea.
    eapply Forall2_nth_error_left in erp as [? [? ?]]; tea.
    rewrite /EGlobalEnv.lookup_projection /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive.
    rewrite (EGlobalEnv.declared_minductive_lookup H6); cbn -[nth_error]; rewrite H7 H0 H9 //.
  Qed.

End trans_lookups.

Lemma erases_wellformed {Σ : global_env_ext} {wfΣ : wf Σ} {Γ a e} : welltyped Σ Γ a -> Σ ;;; Γ |- a ⇝ℇ e ->
  forall Σ', globals_erased_with_deps Σ Σ' -> @EWellformed.wellformed EWellformed.all_env_flags Σ' #|Γ| e.
Proof.
  intros wf.
  generalize (welltyped_wellformed wf).
  destruct wf. eapply subject_closed in X. move: X.
  remember #|Γ| as Γl eqn:Heq.
  intros cla wfa era.
  revert Γ e wfa era Heq.
  pattern Γl, a.
  match goal with
  |- ?P Γl a => simpl; eapply (term_closedn_list_ind P); auto; clear
  end; simpl; intros; subst k;
    match goal with [H:erases _ _ _ _ |- _] => depelim H end; trivial;
    simpl; try solve [solve_all].
  - now apply Nat.ltb_lt.
  - eapply trans_lookup_constant in wfa; tea.
  - eapply trans_lookup_constructor in wfa; tea. now rewrite wfa.
  - move/andP: wfa => [] /andP[] lookup wfc wfbrs.
    apply/andP. split. apply/andP. split; eauto.
    { rewrite /wf_brs.
      move: lookup. rewrite /ErasureProperties.wf_brs.
      destruct lookup_inductive as [[mib oib]|] eqn:hli => //.
      eapply trans_lookup_inductive in hli as [mib' [oib' [-> <-]]]; tea.
      move/Nat.eqb_eq ->. apply All2_length in X1. now apply Nat.eqb_eq. }
    eapply All_forallb. unfold tCaseBrsProp_k in X0.
    eapply All2_All_mix_left in X1; eauto.
    eapply forallb_All in wfbrs.
    eapply All2_All_mix_left in X1; eauto.
    close_Forall. intros [] []; move=> [] wf. cbn in *. intros.
    solve_all. subst. rewrite length_map. eapply b; eauto.
    rewrite app_context_length. cbn.
    now rewrite inst_case_branch_context_length.
  - move/andP: wfa => [] hl hc.
    apply/andP; split.
    now eapply trans_lookup_projection in hl.
    eauto.
  - epose proof (All2_length X0).
    unfold EWellformed.wf_fix_gen.
    rewrite -H0. move/andP: wfa => [] ->.
    move/forallb_All. cbn. intros wfa.
    solve_all. destruct b.
    destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite fix_context_length in b1.
    move/andP: b0 => //; eauto. move=> [] wft /andP[] isl wf; eauto.
    eapply b1; tea. eapply b. now rewrite length_app fix_context_length.
  - epose proof (All2_length X0).
    unfold EWellformed.wf_fix_gen.
    rewrite -H0. move/andP: wfa => [] ->.
    move/forallb_All. cbn. intros wfa.
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite fix_context_length in b.
    eapply b. now move: b0 => /andP[]. eauto. now rewrite length_app fix_context_length. tea.
  - depelim H. solve_all. primProp.
    depelim X0; depelim X1; repeat constructor; cbn; intuition eauto. solve_all.
Qed.

Lemma eval_empty_brs {wfl : EWcbvEval.WcbvFlags} Σ ci p e : Σ ⊢ E.tCase ci p [] ⇓ e -> False.
Proof.
  intros He.
  depind He.
  - clear -e2. now rewrite nth_error_nil in e2.
  - clear -e2. now rewrite nth_error_nil in e2.
  - discriminate.
  - eapply IHHe2.
  - cbn in i. discriminate.
Qed.

Lemma eval_case_tBox_inv {wfl : EWcbvEval.WcbvFlags} {Σ ci e brs} :
  Σ ⊢ E.tCase ci EAst.tBox brs ⇓ e ->
  ∑ n br, brs = [(n, br)] × inductive_isprop_and_pars Σ ci.1 = Some (true, ci.2) ×
  Σ ⊢ ECSubst.substl (repeat EAst.tBox #|n|) br ⇓ e.
Proof.
  intros He.
  depind He.
  - depelim He1. clear -H. symmetry in H. exfalso.
    destruct args using rev_case. discriminate.
    rewrite EAstUtils.mkApps_app in H. discriminate.
  - depelim He1.
  - exists n, f4. intuition auto.
  - depelim He1. clear -H. symmetry in H. exfalso.
    destruct args using rev_case. discriminate.
    rewrite EAstUtils.mkApps_app in H. discriminate.
  - cbn in i. discriminate.
Qed.

Lemma eval_case_eval_discr {wfl : EWcbvEval.WcbvFlags} {Σ ci c c' e brs} :
  Σ ⊢ E.tCase ci c brs ⇓ e ->
  Σ ⊢ c ⇓ c' ->
  Σ ⊢ E.tCase ci c' brs ⇓ e.
Proof.
  intros He Hc.
  depind He.
  - pose proof (EWcbvEval.eval_deterministic He1 Hc). subst c'.
    econstructor; eauto. now eapply EWcbvEval.value_final, EWcbvEval.eval_to_value.
  - pose proof (EWcbvEval.eval_deterministic He1 Hc). subst c'.
    eapply EWcbvEval.eval_iota_block; eauto. now eapply EWcbvEval.value_final, EWcbvEval.eval_to_value.
  - pose proof (EWcbvEval.eval_deterministic He1 Hc). subst c'.
    eapply EWcbvEval.eval_iota_sing; tea. now constructor.
  - pose proof (EWcbvEval.eval_deterministic He1 Hc). subst c'.
    eapply EWcbvEval.eval_cofix_case; tea.
    now eapply EWcbvEval.value_final, EWcbvEval.eval_to_value.
  - cbn in i. discriminate.
Qed.

Lemma eval_case_eval_inv_discr {wfl : EWcbvEval.WcbvFlags} {Σ ci c c' e brs} :
  Σ ⊢ E.tCase ci c brs ⇓ e ->
  Σ ⊢ c' ⇓ c ->
  Σ ⊢ E.tCase ci c' brs ⇓ e.
Proof.
  intros He Hc.
  depind He.
  - pose proof (eval_trans' Hc He1); subst discr.
    econstructor; eauto.
  - pose proof (eval_trans' Hc He1); subst discr.
    now econstructor; eauto.
  - pose proof (eval_trans' Hc He1); subst discr.
    eapply EWcbvEval.eval_iota_sing; tea.
  - pose proof (eval_trans' Hc He1); subst discr.
    eapply EWcbvEval.eval_cofix_case; tea.
  - cbn in i. discriminate.
Qed.

Lemma eval_proj_eval_inv_discr {wfl : EWcbvEval.WcbvFlags} {Σ p c c' e} :
  Σ ⊢ E.tProj p c ⇓ e ->
  Σ ⊢ c' ⇓ c ->
  Σ ⊢ E.tProj p c' ⇓ e.
Proof.
  intros He Hc.
  depind He.
  - pose proof (eval_trans' Hc He1); subst discr.
    econstructor; eauto.
  - pose proof (eval_trans' Hc He1); subst discr.
    now econstructor; tea.
  - pose proof (eval_trans' Hc He1); subst discr.
    now econstructor; tea.
  - pose proof (eval_trans' Hc He); subst discr.
    now econstructor; tea.
  - cbn in i. discriminate.
Qed.
