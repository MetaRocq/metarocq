(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Environment Transform config BasicAst uGraph.
From MetaRocq.Template Require Pretty Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICWeakeningEnvSN.
Set Warnings "+notation-overridden".
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureCorrectness Extract EOptimizePropDiscr
  ERemoveParams EProgram.
From MetaRocq.Erasure Require Import ErasureFunction ErasureFunctionProperties.
From MetaRocq.TemplatePCUIC Require Import PCUICTransform.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform ERemoveParams.
Import EEnvMap EGlobalEnv EWellformed.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env :=
  {| wf_env_reference := {| reference_impl_env := Σ.(trans_env_env); reference_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.

Notation NormalizationIn_erase_pcuic_program_1 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p -> PCUICSN.NormalizationIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p)
       (only parsing).

Notation NormalizationIn_erase_pcuic_program_2 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p)
       (only parsing).

(* TODO: Where should this go? *)
#[local]
Lemma reference_impl_env_iter_pop_eq'
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  (wfe' := ErasureFunction.iter reference_pop (S n) (reference_impl_env wfe))
  : reference_impl_env X' = wfe'.
Proof.
  subst X' wfe'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local]
Lemma reference_impl_env_iter_pop_eq
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  : reference_impl_env X'
    = {| PCUICAst.PCUICEnvironment.universes := PCUICAst.PCUICEnvironment.universes (reference_impl_env wfe)
      ; PCUICAst.PCUICEnvironment.declarations := skipn (S n) (PCUICAst.PCUICEnvironment.declarations (reference_impl_env wfe))
      ; PCUICAst.PCUICEnvironment.retroknowledge := PCUICAst.PCUICEnvironment.retroknowledge (reference_impl_env wfe) |}.
Proof.
  subst X'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local] Lemma erase_pcuic_program_normalization_helper
  (cf := config.extraction_checker_flags) (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl} (p : global_env_ext_map)
  {normalization_in : NormalizationIn_erase_pcuic_program_1 p}
  {normalization_in_adjust_universes : NormalizationIn_erase_pcuic_program_2 p}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p ∥)
  : (let wfe := build_wf_env_from_env p.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p ∥)) in
     forall n : nat,
       n < #|PCUICAst.PCUICEnvironment.declarations p.1|
      -> forall kn cb pf,
        hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
          Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
        forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
          PCUICTyping.wf_ext Σ ->
          Σ
            ∼_ext @abstract_make_wf_env_ext extraction_checker_flags
            (@optimized_abstract_env_impl extraction_checker_flags _) wfe
            (PCUICAst.PCUICEnvironment.cst_universes cb) pf -> PCUICSN.NormalizationIn Σ)
    /\
      (let wfe := build_wf_env_from_env p.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p ∥)) in
       forall n : nat,
         n < #|PCUICAst.PCUICEnvironment.declarations p.1|
        -> let X' :=
             ErasureFunction.iter abstract_pop_decls (S n) wfe in
           forall kn cb pf,
             hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
               Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
             let Xext :=
               @abstract_make_wf_env_ext extraction_checker_flags
                 (@optimized_abstract_env_impl extraction_checker_flags _) X'
                 (PCUICAst.PCUICEnvironment.cst_universes cb) pf in
             forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
               PCUICTyping.wf_ext Σ -> Σ ∼_ext Xext -> PCUICSN.NormalizationIn Σ).
Proof.
  match goal with |- ?A /\ ?B => cut (A /\ (A -> B)); [ tauto | ] end.
  cbv beta zeta; split.
  all: cbn; intros; subst;
    repeat match goal with
      | [ H : forall x, x = _ -> _ |- _ ] => specialize (H _ eq_refl)
      | [ H : squash _ |- _ ] => destruct H
      | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
      end.
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalizationIn _ |- _ => revert H end.
    eapply normalization_in_adjust_universes; try assumption.
    cbv [PCUICSN.NormalizationIn]; cbn.
    let H := match goal with H : PCUICTyping.wf_ext _ |- _ => H end in
    rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
    [ eapply PCUICAst.NoDup_on_global_decls, H
    | eexists; eassumption ]. }
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalizationIn _ |- _ => revert H end.
    move => normalization_in.
    rewrite reference_impl_env_iter_pop_eq.
    repeat match goal with H : _ |- _ => rewrite reference_impl_env_iter_pop_eq in H end.
    eapply normalization_in_adjust_universes in normalization_in; eauto; revgoals.
    { repeat match goal with H : PCUICTyping.wf_ext _ |- _ => destruct H end;
        split; eassumption. }
    { let H := multimatch goal with H : PCUICTyping.wf_ext _ |- _ => H end in
      rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
      [ eapply PCUICAst.NoDup_on_global_decls, H
      | eexists; eassumption ]. }
    revert normalization_in.
    apply PCUICWeakeningEnvSN.weakening_env_normalization_in; eauto;
      try match goal with H : PCUICTyping.wf_ext _ |- _ => refine (@PCUICTyping.wf_ext_wf _ _ H) end.
    apply PCUICAst.PCUICEnvironment.extends_decls_extends, PCUICAst.PCUICEnvironment.strictly_extends_decls_extends_decls; split; cbn; try reflexivity.
    eauto using firstn_skipn. }
Qed.

Local Obligation Tactic := program_simpl.

Program Definition erase_pcuic_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalization_in : NormalizationIn_erase_pcuic_program_1 p.1}
  {normalization_in_adjust_universes : NormalizationIn_erase_pcuic_program_2 p.1}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) wfΣ) in
  let wfext := @abstract_make_wf_env_ext _ optimized_abstract_env_impl wfe p.1.2 _ in
  let t := ErasureFunction.erase (normalization_in:=_) optimized_abstract_env_impl wfext nil p.2
    (fun Σ wfΣ => let '(sq (T; ty)) := wt in PCUICTyping.iswelltyped ty) in
  let Σ' := ErasureFunctionProperties.erase_global_fast (normalization_in:=_) optimized_abstract_env_impl
    (EAstUtils.term_global_deps t) wfe (p.1.(PCUICAst.PCUICEnvironment.declarations)) _ in
    (EEnvMap.GlobalContextMap.make Σ'.1 _, t).

Next Obligation. unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto. Defined.
Next Obligation.
  eapply wf_glob_fresh.
  eapply ErasureFunctionProperties.erase_global_fast_wf_glob.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
Defined.

Local Obligation Tactic := idtac.

Import Extract.

Definition erase_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalization_in normalization_in_adjust_universes}
  (wtp : ∥ wt_pcuic_program (cf:=config.extraction_checker_flags) p ∥)
  : eprogram_env :=
  @erase_pcuic_program guard p normalization_in normalization_in_adjust_universes (map_squash fst wtp) (map_squash snd wtp).

Lemma expanded_erase_program {guard : abstract_guard_impl} p {normalization_in normalization_in_adjust_universes} (wtp : ∥ wt_pcuic_program p ∥) :
  PCUICEtaExpand.expanded_pcuic_program p ->
  EEtaExpandedFix.expanded_eprogram_env (@erase_program guard p normalization_in normalization_in_adjust_universes wtp).
Proof.
  intros [etaenv etat]. split;
  unfold erase_program, erase_pcuic_program.
  eapply ErasureFunctionProperties.expanded_erase_global_fast, etaenv; try reflexivity; eauto.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  apply: (ErasureFunctionProperties.expanded_erase_fast (X_type:=optimized_abstract_env_impl)).
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  reflexivity. exact etat.
Qed.

Lemma expanded_eprogram_env_expanded_eprogram_cstrs p :
  EEtaExpandedFix.expanded_eprogram_env p ->
  EEtaExpanded.expanded_eprogram_env_cstrs p.
Proof.
  move=> [] etaenv etat.
  apply /andP.
  split.
  - eapply EEtaExpanded.isEtaExpFix_env_isEtaExp_env. now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  - eapply EEtaExpanded.isEtaExpFix_isEtaExp. now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

Local Obligation Tactic := try solve [ eauto ].

Program Definition erase_transform {guard : abstract_guard_impl} : Transform.t _ _ PCUICAst.term EAst.term PCUICAst.term EAst.term
  eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=
     ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
     /\ PCUICEtaExpand.expanded_pcuic_program p
     /\ NormalizationIn_erase_pcuic_program_1 p.1
     /\ NormalizationIn_erase_pcuic_program_2 p.1 ;
   transform p hp := let nhs := proj2 (proj2 hp) in
                     @erase_program guard p (proj1 nhs) (proj2 nhs) (proj1 hp) ;
   post p := [/\ wf_eprogram_env all_env_flags p & EEtaExpandedFix.expanded_eprogram_env p];
   obseq p hp p' v v' := let Σ := p.1 in Σ ;;; [] |- v ⇝ℇ v' |}.

Next Obligation.
  cbn -[erase_program].
  intros ? p (wtp&etap&?&?).
  destruct erase_program eqn:e.
  split.
  - unfold erase_program, erase_pcuic_program in e.
    set (egf := erase_global_fast _ _ _ _ _) in e.
    set (ef := erase _ _ _ _ _) in e.
    cbn -[egf ef] in e. injection e. intros <- <-.
    split.
    eapply erase_global_fast_wf_glob; eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
    apply: (erase_wellformed_fast (X_type:=optimized_abstract_env_impl)); eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  - rewrite -e. cbn.
    now eapply expanded_erase_program.
Qed.

Next Obligation.
  red. move=> guard p v [[wf [T [HT1 HT2]]]]. unfold eval_pcuic_program, eval_eprogram.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; try now destruct wf; eauto.
  destruct p as [Σ t].
  intros [ev].
  destruct erase_program eqn:e.
  unfold erase_program, erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  destruct wf; cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  assert (ev' :forall Σ0 : PCUICAst.PCUICEnvironment.global_env, Σ0 = Σ' -> PCUICWcbvEval.eval Σ0 t v).
  { intros; now subst. }
  eapply (erase_correct optimized_abstract_env_impl Σ' Σ.2 _ _ _ _ _ (EAstUtils.term_global_deps _)) in ev'.
  4:{ erewrite <- erase_global_deps_fast_spec. reflexivity. }
  all:trea.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev' as [v' [he [hev]]]. exists v'; split => //.
  red. cbn.
  sq. exact hev. Unshelve.
  { intros; cbn in *.
    subst Σ'.
    multimatch goal with
    | [ H : _ |- _ ] => eapply H
    end; try eassumption;
    rewrite reference_impl_env_iter_pop_eq;
    repeat match goal with H : _ |- _ => rewrite reference_impl_env_iter_pop_eq in H end;
    assumption. }
  cbn; intros. sq. now subst.
Qed.

(** Typed erasure variant, using erasure but also keeping type information useful for later optimizations,
    e.g., de-arging. *)

Definition typed_erasure_pre (p : pcuic_program) :=
  ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
  /\ PCUICEtaExpand.expanded_pcuic_program p
  /\ NormalizationIn_erase_pcuic_program_1 p.1
  /\ NormalizationIn_erase_pcuic_program_2 p.1.

From MetaRocq.Erasure.Typed Require Import Erasure ExAst Optimize ExtractionCorrectness OptimizeCorrectness.
From MetaRocq.Erasure Require Import EWellformed.
From MetaRocq.PCUIC Require Import PCUICTyping.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
Set Equations Transparent.
Equations? erase_program_typed guard (p : pcuic_program) (pre : typed_erasure_pre p) : ExAst.global_env * EAst.term :=
 erase_program_typed guard p pre :=
  let wfΣ : ∥ wf_ext p.1 ∥ := _ in
  let X := PCUICWfEnvImpl.build_wf_env_from_env p.1 (map_squash fst wfΣ) in
  let t' := erase_term wfΣ p.2 _ in
  (erase_global_decls_deps_recursive
    (X_type := PCUICWfEnvImpl.optimized_abstract_env_impl (guard := guard))
    (X := X) (PEnv.declarations p.1) (PEnv.universes p.1) (PEnv.retroknowledge p.1)
    (fun Σ' eq => _)
    (EAstUtils.term_global_deps t') (fun _ => false), t').
Proof.
  - destruct pre0. destruct H. destruct X. now sq.
  - destruct pre0 as [[[wf []]] _]. now eexists.
  - cbn in eq. rewrite eq. clear; destruct p.1; cbn in *.
    set(x := eval_eprogram_env).
    destruct g; cbn in *.
    now destruct trans_env_env; cbn.
Qed.

Definition trans_ex_prog (p : ExAst.global_env * EAst.term) : EAst.global_context * EAst.term :=
  (ExAst.trans_env p.1, p.2).

Definition eval_typed_eprogram fl :=
  (fun p v => ∥ @EWcbvEval.eval fl (ExAst.trans_env p.1) p.2 v ∥).

Program Definition typed_erase_transform (guard := fake_guard_impl_instance) :
  Transform.t _ _ PCUICAst.term EAst.term PCUICAst.term EAst.term
  eval_pcuic_program (eval_typed_eprogram EWcbvEval.default_wcbv_flags) :=
 {| name := "typed erasure";
    pre p :=
     ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
     /\ PCUICEtaExpand.expanded_pcuic_program p
     /\ NormalizationIn_erase_pcuic_program_1 p.1
     /\ NormalizationIn_erase_pcuic_program_2 p.1 ;
   transform p hp := erase_program_typed guard p hp ;
   post p := [/\ wf_eprogram all_env_flags (trans_ex_prog p) &
     EEtaExpandedFix.expanded_eprogram (trans_ex_prog p)];
   obseq p hp p' v v' := let Σ := p.1 in Σ ;;; [] |- v ⇝ℇ v' |}.

Next Obligation.
  cbn -[erase_program].
  intros p (wtp&etap&?&?).
  destruct erase_program_typed eqn:e.
  split.
  - unfold erase_program_typed, erase_pcuic_program in e.
    set (egf := erase_global_decls_deps_recursive _ _ _ _ _ _) in e.
    unfold erase_term in e.
    set (ef := erase _ _ _ _ _) in e.
    cbn -[egf ef] in e. injection e. intros <- <-. clear e.
    unfold trans_ex_prog in *.
    split.
    now eapply wf_erase_global_decls_recursive.
    cbn [fst snd].
    eapply extends_wellformed.
    now eapply wf_erase_global_decls_recursive.
    2:unshelve eapply (erase_wellformed_weaken (PEnv.declarations p.1) _ _ _ (Γ:=[])); tea.
    4:exact KernameSet.empty.
    2:{ intros. now eapply Erasure.fake_normalization. }
    2:{ abstract (cbn; destruct p; destruct g; cbn; congruence). }
    rewrite erase_global_deps_erase_global.
    eapply trans_env_erase_global_decls; eauto.
    intros kn hin. rewrite KernameSet.union_spec in hin. destruct hin; [knset|].
    unfold erase_term.
    match goal with
    | [ H : context [@erase ?X_type ?X ?nin ?G ?t ?wt ] |- context [ @erase ?X_type' ?X' ?nin' ?G' ?t' ?wt' ] ] =>
      rewrite -(@erase_irrel_global_env X_type X nin X_type' X' nin' G t wt wt'); eauto
    end.
    red. cbn. intros; subst; intuition eauto.
    destruct wtp. eapply wf_fresh_globals, w.
  - move: e. rewrite /erase_program_typed.
    intros [= <- <-]. unfold trans_ex_prog; cbn -[trans_env].
    red. split; cbn -[trans_env].
    eapply expanded_erase_global_decls_recursive; eauto. eapply etap.
    eapply expanded_erase => //; eauto. eapply etap.
Qed.

Next Obligation.
  intros guard.
  set (cf := extraction_checker_flags).
  cbn. red.
  move=> p v [[wf [T [HT1 HT2]]]]. unfold eval_pcuic_program, eval_typed_eprogram.
  unfold erase_program_typed.
  set (er := erase_global_decls_deps_recursive _ _ _ _ _ _).
  set (et := erase_term _ _ _).
  unshelve edestruct (erase_pcuic_program_normalization_helper); cbn in *; try now destruct wf; eauto.
  destruct p as [Σ t].
  intros [ev].
  cbn in ev. clear H0.
  unfold erase_term, make_env in et.
  set (e := abstract_make_wf_env_ext _ _ _) in *.
  cbn [fst snd] in et.
  pose proof (abstract_env_ext_exists e) as [[Σe he]].
  match goal with
  [H := context [ @erase ?X_type ?X ?nin ?Γ t ?wt ] |- _ ] =>
   pose proof (@erases_erase X_type X nin Γ t wt _ he)
  end.
  cbn in he. subst Σe. destruct Σ as [Σ univs]; cbn [fst snd] in *.
  assert (wv : welltyped (Σ, univs) [] v).
  { destruct wf. destruct s. eexists. eapply PCUICClassification.subject_reduction_eval; tea. }
  eapply ErasureCorrectness.erases_correct with (Σ := (trans_env_env Σ, univs)) (Σ' := trans_env er) in ev as (erv&erase_to&[erev]);eauto.
  - apply wf.
  - destruct wf. destruct s; now eexists.
  - destruct wf as [wf []]. eapply erase_global_erases_deps; tea.
    subst er.
    set (obl := fun Σ' => _).
    set (obl' := fun Σ' => _).
    destruct Σ. destruct trans_env_env. cbn -[build_wf_env_from_env e] in *.
    eapply (ErasureCorrectness.erase_global_decls_deps_recursive_correct _ _ _ _); eauto.
    intros k hin.
    eapply term_global_deps_spec in hin; tea. red in hin. destruct hin as [[decl eq]].
    cbn in eq. cbn. now rewrite eq. cbn. eapply wf.
Qed.

(** De-arging requires first the removal of match-on-box which allows getting rid of all
  dependencies on propositional inductive types. *)
Import EOptimizePropDiscr OptimizePropDiscr EWcbvEval.

Definition remove_match_on_box_typed_env m (Σ : global_env) :=
  map (on_snd (remove_match_on_box_decl m)) Σ.

Definition map_of_typed_global_env (p : global_env) (fr : fresh_globals p) :=
  GlobalContextMap.make (trans_env p) (OptimizePropDiscr.remove_match_on_box_env_obligation_1 p fr).

Definition pre_remove_match_on_box_typed efl (p : global_env * term) : Prop :=
  wf_eprogram efl (trans_ex_prog p) /\ EEtaExpandedFix.expanded_eprogram (trans_ex_prog p).

Lemma fresh_global_trans kn g : EnvMap.EnvMap.fresh_global kn (trans_env g) -> fresh_global kn g.
Proof.
  induction g as [ | [[kn' b] d] tl]; cbn; auto; constructor; eauto.
  - now depelim H.
  - depelim H. eapply Forall_map_inv in H0. ELiftSubst.solve_all.
Qed.

Lemma pre_remove_match_on_box_typed_fresh efl p : pre_remove_match_on_box_typed efl p -> fresh_globals p.1.
Proof.
  intros []. destruct H. eapply wf_glob_fresh in H.
  revert H. clear.
   destruct p; cbn. clear.
  intros h; depind h.
  - destruct g; noconf H. constructor.
  - destruct g0; noconf H0. destruct p as [[kn' b] d'].
    constructor; eauto. now eapply fresh_global_trans.
Qed.

Lemma map_trans_env Σ m : map (on_snd (EOptimizePropDiscr.remove_match_on_box_decl m)) (trans_env Σ) = trans_env (map (on_snd (OptimizePropDiscr.remove_match_on_box_decl m)) Σ).
Proof.
  induction Σ; cbn => //=.
  destruct a as [[kn b] d]; cbn. f_equal.
  unfold on_snd. cbn. f_equal. destruct d => //. destruct o => //.
  now apply IHΣ.
Qed.

Definition remove_match_on_box_program_typed efl (p : global_env * term) (pre : pre_remove_match_on_box_typed efl p) : global_env * term :=
  let m := map_of_typed_global_env p.1 (pre_remove_match_on_box_typed_fresh efl p pre) in
  (remove_match_on_box_typed_env m p.1, EOptimizePropDiscr.remove_match_on_box m p.2).
Import EOptimizePropDiscr.

Program Definition remove_match_on_box_typed_transform {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _  EAst.term EAst.term _ _ (eval_typed_eprogram fl) (eval_typed_eprogram (disable_prop_cases fl)) :=
  {| name := "optimize_prop_discr";
    transform p pr := remove_match_on_box_program_typed efl p pr ;
    pre p := pre_remove_match_on_box_typed efl p;
    post p := pre_remove_match_on_box_typed efl p;
    obseq p hp p' v v' := v' = EOptimizePropDiscr.remove_match_on_box (map_of_typed_global_env p.1 (pre_remove_match_on_box_typed_fresh efl p hp)) v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - cbn in *. unfold trans_ex_prog in *. cbn [fst snd] in *.
    unfold remove_match_on_box_program_typed; cbn [fst snd].
    cbn.
    rewrite trans_env_remove_match_on_box_env.
    split.
    + eapply remove_match_on_box_env_wf => //.
      cbn. eapply wfp.
    + cbn -[remove_match_on_box_env].
      rewrite /map_of_typed_global_env.
      set (obl := trans_env_fresh_globals _ _).
      set (obl' := OptimizePropDiscr.remove_match_on_box_env_obligation_1 _ _).
      assert (obl = obl') by apply proof_irrelevance. clearbody obl obl'; subst obl'.
      eapply remove_match_on_box_wellformed_irrel. cbn. eapply wfp.
      eapply remove_match_on_box_wellformed => //=. apply wfp. apply wfp.
  - rewrite /trans_ex_prog /= /remove_match_on_box_typed_env. cbn.
    rewrite -map_trans_env. unfold trans_ex_prog in *. cbn -[trans_env] in *.
    set (e' := map_of_typed_global_env _ _).
    eapply (remove_match_on_box_program_expanded_fix (e', t) wfp).
    unfold e'. unfold map_of_typed_global_env. red. cbn. eapply etap.
Qed.

Next Obligation.
  red. move=> fl wcon efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  cbn -[trans_env] in ev.
  unfold eval_typed_eprogram, remove_match_on_box_program_typed. cbn -[trans_env].
  set (obl := pre_remove_match_on_box_typed_fresh _ _ _).
  eapply (EOptimizePropDiscr.remove_match_on_box_correct (Σ := map_of_typed_global_env _ obl) t v) in ev; cbn -[trans_env]; eauto.
  eexists; split => //. rewrite -map_trans_env. now sq.
  apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
  Unshelve. eauto.
Qed.

Record dearging_config :=
  { overridden_masks : kername -> option bitmask;
    do_trim_const_masks : bool;
    do_trim_ctor_masks : bool }.

Definition check_dearging_precond (cf : dearging_config) Σ t :=
  if closed_env (trans_env Σ) then
    match ExtractionCorrectness.compute_masks cf.(overridden_masks) cf.(do_trim_const_masks) cf.(do_trim_ctor_masks) Σ with
    | ResultMonad.Ok masks =>
      if valid_cases (ind_masks masks) t && is_expanded (ind_masks masks) (const_masks masks) t then Some masks else None
    | _ => None
    end
  else None.

Lemma check_dearging_precond_spec cf env t d :
  check_dearging_precond cf env t = Some d ->
  closed_env (trans_env env) /\
  valid_masks_env (ind_masks d) (const_masks d) env /\
  is_expanded_env (ind_masks d) (const_masks d) env /\
  valid_cases (ind_masks d) t
  /\ is_expanded (ind_masks d) (const_masks d) t.
Proof.
  unfold check_dearging_precond.
  destruct closed_env => //.
  unfold ExtractionCorrectness.compute_masks, Utils.timed.
  destruct analyze_env eqn:eqm => //.
  destruct is_expanded_env eqn:isex => //.
  destruct valid_masks_env eqn:vm => //=.
  destruct valid_cases eqn:vc => //=.
  destruct is_expanded eqn:ise => //=.
  intros [= <-]; cbn; intuition.
Qed.

Definition check_dearging_trans cf p :=
  ((check_dearging_precond cf p.1 p.2, p.1), p.2).

Definition eval_typed_eprogram_masks fl :=
  (fun (p : (option dearg_set * global_env) * term) v => ∥ @EWcbvEval.eval fl (ExAst.trans_env p.1.2) p.2 v ∥).

Definition post_dearging_checks efl cf (p : (option dearg_set × global_env) × term) :=
  (p.1.1 = check_dearging_precond cf p.1.2 p.2) /\
  wf_eprogram efl (trans_env p.1.2, p.2) /\ EEtaExpandedFix.expanded_eprogram (trans_env p.1.2, p.2).

Program Definition dearging_checks_transform {efl : EEnvFlags} cf {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_typed_eprogram opt_wcbv_flags) (eval_typed_eprogram_masks opt_wcbv_flags) :=
  {| name := "dearging";
    transform p _ := check_dearging_trans cf p ;
    pre p := pre_remove_match_on_box_typed efl p;
    post := post_dearging_checks efl cf;
    obseq p hp p' v v' := v' = v |}.
Next Obligation.
  cbn. intros. split => //.
Qed.
Next Obligation.
  cbn. intros. red. cbn. intros. exists v; split => //.
Qed.

Section Dearging.
  Import Optimize OptimizeCorrectness.

  Definition dearg (p : (option dearg_set × global_env) * term) : global_context * term :=
    match p.1.1 with
    | Some masks => (trans_env (dearg_env masks p.1.2), dearg_term masks p.2)
    | None => (trans_env p.1.2, p.2)
    end.

  Program Definition dearging_transform (efl := all_env_flags) cf :
    Transform.t _ _  EAst.term EAst.term _ _ (eval_typed_eprogram_masks opt_wcbv_flags) (eval_eprogram opt_wcbv_flags) :=
    {| name := "dearging";
      transform p _ := dearg p ;
      pre p := post_dearging_checks efl cf p;
      post p := wf_eprogram efl p /\ EEtaExpandedFix.expanded_eprogram p ;
      obseq p hp p' v v' := v' = (dearg (p.1, v)).2 |}.

  Next Obligation.
  Proof.
    cbn. intros.
    unfold dearg.
    destruct p. rewrite H.
    destruct check_dearging_precond eqn:eqp; cbn => //.
    destruct input as [[masks env] t]. cbn -[trans_env Optimize.dearg_env] in *.
    subst masks. destruct H0 as [wf exp].
    eapply check_dearging_precond_spec in eqp. intuition.
    - split; cbn.
      unfold dearg_env.
      eapply wf_glob_debox.
      eapply wf_glob_dearg; eauto.
      eapply wf.
      rewrite /dearg_env. rewrite -trans_env_debox.
      eapply wellformed_dearg; eauto.
      eapply wf.
    - rewrite /dearg_env -trans_env_debox. split; cbn.
      eapply expanded_dearg_env; tea. apply exp.
      eapply EEtaExpandedFix.isEtaExp_expanded, expanded_dearg; eauto.
      apply EEtaExpandedFix.expanded_isEtaExp, exp.
  Qed.

  Next Obligation.
    cbn. intros. red.
    intros p v [he [wfe exp]]. unfold eval_typed_eprogram_masks.
    intros [ev].
    unfold dearg. rewrite he.
    destruct (check_dearging_precond) as [masks|] eqn:cpre.
    * eapply (extract_correct_gen' _ _ _ masks cf.(overridden_masks) cf.(do_trim_const_masks) cf.(do_trim_ctor_masks)) in ev as ev'.
      destruct ev' as [ev'].
      eexists. split. red. sq. cbn. exact ev'. auto.
      - destruct wfe. now eapply wellformed_closed_env.
      - destruct wfe. now eapply wellformed_closed.
      - move: cpre. unfold check_dearging_precond. destruct closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct (_ && _) => //. congruence.
      - move: cpre. rewrite /check_dearging_precond.
        destruct closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct valid_cases eqn:vc => //. cbn.
        destruct is_expanded => //. now intros [= ->].
      - move: cpre. rewrite /check_dearging_precond.
        destruct closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct valid_cases eqn:vc => //. cbn.
        destruct is_expanded eqn:ise => //. now intros [= ->].
    * exists v. cbn. split => //.
  Qed.

End Dearging.


Section PCUICEnv. (* Locally reuse the short names for PCUIC environment handling *)
Import PCUICAst.PCUICEnvironment.

Lemma build_wf_env_from_env_eq {cf : checker_flags} (guard : abstract_guard_impl) (Σ : global_env_ext_map) (wfΣ : ∥ PCUICTyping.wf_ext Σ ∥) :
  let wfe := build_wf_env_from_env Σ (map_squash (PCUICTyping.wf_ext_wf Σ) wfΣ) in
  forall Σ' : global_env, Σ' ∼ wfe -> declarations Σ' = declarations Σ.
Proof.
  cbn; intros. rewrite H. reflexivity.
Qed.

Definition extends_global_env (Σ Σ' : global_env_ext_map) :=
  [/\ (forall kn decl, lookup_env Σ kn = Some decl ->lookup_env Σ' kn = Some decl),
      Σ.(universes) = Σ'.(universes), Σ.2 = Σ'.2 & Σ.(retroknowledge) = Σ'.(retroknowledge)].

Definition extends_pcuic_program (p p' : pcuic_program) :=
  extends_global_env p.1 p'.1 /\ p.2 = p'.2.
Import ErasureFunction.
Import PCUICAst.

Lemma strictly_extends_lookups {cf:checker_flags} (X X' : wf_env) (Σ Σ' : global_env) :
  (forall (kn : kername) (decl decl' : global_decl), lookup_env Σ' kn = Some decl -> lookup_env Σ kn = Some decl' -> decl = decl') ->
  retroknowledge Σ = retroknowledge Σ' ->
  strictly_extends_decls X Σ -> strictly_extends_decls X' Σ' ->
  PCUICTyping.wf Σ -> PCUICTyping.wf Σ' ->
  equiv_env_inter X' X.
Proof.
  intros hl hr [] [] wf wf'.
  split.
  - intros kn d.
    unfold lookup_env in *.
    destruct s as [? eq], s0 as [? eq'].
    rewrite eq' eq in hl.
    intros decl' hl' hl''.
    specialize (hl kn d decl').
    eapply wf_fresh_globals in wf.
    eapply wf_fresh_globals in wf'.
    rewrite eq in wf; rewrite eq' in wf'.
    eapply lookup_global_app_wf in hl'; tea.
    eapply lookup_global_app_wf in hl''; tea.
    eauto.
  - rewrite /primitive_constant. now rewrite e0 e2 hr.
Qed.


Lemma lookup_env_In_map_fst Σ kn decl : EGlobalEnv.lookup_env Σ kn = Some decl -> In kn (map fst Σ).
Proof.
  induction Σ; cbn => //.
  case: eqb_spec.
  + intros -> [= <-]. now left.
  + intros _ hl. eauto.
Qed.

End PCUICEnv.

#[local] Obligation Tactic := idtac.

(** This transformation is the identity on terms but changes the evaluation relation to one
    where fixpoints are not guarded. It requires eta-expanded fixpoints and evaluation
    to use the guarded fixpoint rule as a precondition. *)

Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).

Program Definition guarded_to_unguarded_fix {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram_env fl) (eval_eprogram_env (EWcbvEval.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints";
    transform p pre := p;
    pre p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    post p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    obseq p hp p' v v' := v' = v |}.
Next Obligation. cbn. eauto. Qed.
Next Obligation.
  cbn.
  move=> fl wcon efl wguard [Σ t] v [wfp [etae etat]]. cbn in *.
  intros [ev]. exists v. split => //.
  red. sq. cbn in *.
  unshelve eapply EEtaExpandedFix.eval_opt_to_target => //. auto. 2:apply wfp.
  now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

#[global]
Instance guarded_to_unguarded_fix_extends {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  TransformExt.t (guarded_to_unguarded_fix (wcon:=wcon) wguard) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ?. now rewrite /transform /=.
Qed.

#[global]
Instance guarded_to_unguarded_fix_extends' {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  TransformExt.t (guarded_to_unguarded_fix (wcon:=wcon) wguard) extends_eprogram_env extends_eprogram_env.
Proof.
  red. intros p p' pr pr' [? ?]. now rewrite /transform /=.
Qed.

Definition rebuild_wf_env {efl} (p : eprogram) (hwf : wf_eprogram efl p): eprogram_env :=
  (GlobalContextMap.make p.1 (wf_glob_fresh p.1 (proj1 hwf)), p.2).

Definition preserves_expansion with_fix p :=
  if with_fix then EEtaExpandedFix.expanded_eprogram p
  else EEtaExpanded.expanded_eprogram_cstrs p.

Definition preserves_expansion_env with_fix p :=
  if with_fix then EEtaExpandedFix.expanded_eprogram_env p
  else EEtaExpanded.expanded_eprogram_env_cstrs p.

Program Definition rebuild_wf_env_transform {fl : EWcbvEval.WcbvFlags} {efl} (with_exp with_fix : bool) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram fl) (eval_eprogram_env fl) :=
  {| name := "rebuilding environment lookup table";
     pre p := wf_eprogram efl p /\ (with_exp -> preserves_expansion with_fix p);
     transform p pre := rebuild_wf_env p (proj1 pre);
     post p := wf_eprogram_env efl p /\ (with_exp -> preserves_expansion_env with_fix p);
     obseq p hp p' v v' := v = v' |}.
Next Obligation.
  cbn. unfold preserves_expansion, preserves_expansion_env.
  intros fl efl [] [] input [wf exp]; cbn; split => //.
Qed.
Next Obligation.
  cbn. intros fl efl [] [] input v [] ev p'; exists v; split => //.
Qed.

#[global]
Instance rebuild_wf_env_extends {fl : EWcbvEval.WcbvFlags} {efl : EEnvFlags} with_exp with_fix :
  TransformExt.t (rebuild_wf_env_transform with_exp with_fix) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. red. now rewrite /transform /=.
Qed.

#[global]
Instance rebuild_wf_env_extends' {fl : EWcbvEval.WcbvFlags} {efl : EEnvFlags} with_exp with_fix :
  TransformExt.t (rebuild_wf_env_transform with_exp with_fix) extends_eprogram extends_eprogram_env.
Proof.
  red. intros p p' pr pr' [? ?]. now rewrite /transform /=.
Qed.

Program Definition remove_params_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (using a view)";
    transform p pre := ERemoveParams.strip_program p;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = (ERemoveParams.strip p.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  split. now eapply ERemoveParams.strip_program_wf.
  now eapply ERemoveParams.strip_program_expanded.
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //. now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

#[global]
Instance remove_params_extends {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  TransformExt.t (remove_params_optimization (wcon:=wcon)) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /= /strip_program.
  red. cbn -[strip_env strip]. eapply strip_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance remove_params_extends' {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  TransformExt.t (remove_params_optimization (wcon:=wcon)) extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /strip_program. rewrite eq.
  red. cbn -[strip_env strip]. split. eapply strip_extends_env => //. apply pr. apply pr'.
  cbn -[strip_env strip]. eapply strip_extends => //. apply pr'. rewrite -eq. apply pr.
Qed.

Program Definition remove_params_fast_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (using accumulators)";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = (ERemoveParams.strip p.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  split.
  now eapply (ERemoveParams.strip_program_wf (Σ, t)).
  now eapply (ERemoveParams.strip_program_expanded (Σ, t)).
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //.
  now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

#[global]
Instance remove_params_fast_extends {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  TransformExt.t (remove_params_fast_optimization (wcon:=wcon)) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  rewrite -!ERemoveParams.Fast.strip_env_fast.
  eapply strip_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance remove_params_fast_extends' {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  TransformExt.t (remove_params_fast_optimization (wcon:=wcon)) extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. rewrite eq.
  rewrite -!ERemoveParams.Fast.strip_env_fast -!ERemoveParams.Fast.strip_fast.
  split => /=. eapply strip_extends_env => //. apply pr. apply pr'.
  eapply strip_extends => //. apply pr'. rewrite -eq. apply pr.
Qed.

Import EOptimizePropDiscr EWcbvEval.

Program Definition remove_match_on_box_trans {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _  EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram (disable_prop_cases fl)) :=
  {| name := "optimize_prop_discr";
    transform p _ := remove_match_on_box_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram efl p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = EOptimizePropDiscr.remove_match_on_box p.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply remove_match_on_box_program_wf.
  - now eapply remove_match_on_box_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EOptimizePropDiscr.remove_match_on_box_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
  Unshelve. eauto.
Qed.

#[global]
Instance remove_match_on_box_extends  {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (remove_match_on_box_trans (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
  Proof.
  red. intros p p' pr pr' ext. rewrite /transform /= /remove_match_on_box_program.
  eapply remove_match_on_box_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance remove_match_on_box_extends'  {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (remove_match_on_box_trans (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /remove_match_on_box_program. split.
  eapply remove_match_on_box_extends_env => //. apply pr. apply pr'.
  rewrite -eq.
  eapply wellformed_remove_match_on_box_extends; eauto. apply pr. apply pr'.
Qed.

From MetaRocq.Erasure Require Import EInlineProjections.

Program Definition inline_projections_optimization {fl : WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} (efl := switch_no_params all_env_flags)
  {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "primitive projection inlining";
    transform p _ := EInlineProjections.optimize_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (disable_projections_env_flag efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = EInlineProjections.optimize p.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EInlineProjections.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  cbn. eapply wfe. Unshelve. auto.
Qed.

#[global]
Instance inline_projections_optimization_extends {fl : WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} (efl := switch_no_params all_env_flags)
  {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (inline_projections_optimization (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /= /optimize_program /=.
  eapply optimize_extends_env => //. apply pr. apply pr'.
Qed.

#[global]
Instance inline_projections_optimization_extends' {fl : WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} (efl := switch_no_params all_env_flags)
  {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (inline_projections_optimization (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /optimize_program /=. split.
  eapply optimize_extends_env => //. apply pr. apply pr'.
  rewrite -eq.
  eapply wellformed_optimize_extends; eauto. apply pr. apply pr'.
Qed.

From MetaRocq.Erasure Require Import EConstructorsAsBlocks.

Program Definition constructors_as_blocks_transformation {efl : EEnvFlags}
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram_env target_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming to constuctors as blocks";
    transform p _ := EConstructorsAsBlocks.transform_blocks_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_cstr_as_blocks efl) p ;
    obseq p hp p' v v' := v' = EConstructorsAsBlocks.transform_blocks p.1 v |}.

Next Obligation.
  move=> efl hasapp hasrel hasbox haspars hascstrs [Σ t] [] [wftp wft] /andP [etap etat].
  cbn in *. split.
  - eapply transform_wf_global; eauto.
  - eapply transform_wellformed; eauto.
Qed.
Next Obligation.
  red. move=> efl hasapp hasrel hasbox haspars hascstrs [Σ t] /= v [[wfe1 wfe2] wft] [ev].
  eexists. split; [ | eauto].
  unfold EEtaExpanded.expanded_eprogram_env_cstrs in *.
  revert wft. move => /andP // [e1 e2].
  econstructor.
  cbn -[transform_blocks].
  eapply transform_blocks_eval; cbn; eauto.
Qed.

#[global]
Instance constructors_as_blocks_extends (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  TransformExt.t (constructors_as_blocks_transformation (has_app := has_app) (has_rel := has_rel) (has_box := has_box) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks))
  (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  eapply transform_blocks_env_extends => //. apply pr. apply pr'.
Qed.

#[global]
Instance constructors_as_blocks_extends' (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  TransformExt.t (constructors_as_blocks_transformation (has_app := has_app) (has_rel := has_rel) (has_box := has_box) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks))
  extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. split.
  eapply transform_blocks_env_extends => //. apply pr. apply pr'.
  unfold transform_blocks_program => /=.
  rewrite -eq.
  eapply transform_blocks_extends; eauto. apply pr. apply pr'.
Qed.

From MetaRocq.Erasure Require ECoInductiveToInductive.

Program Definition coinductive_to_inductive_transformation (efl : EEnvFlags)
  {has_app : has_tApp} {has_box : has_tBox} {has_rel : has_tRel} {has_pars : has_cstr_params = false}
  {has_cstrblocks : cstr_as_blocks = true} :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram_env block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming co-inductive to lazy inductive types";
    transform p _ := ECoInductiveToInductive.trans_program p ;
    pre p := wf_eprogram_env efl p ;
    post p := wf_eprogram efl p ;
    obseq p hp p' v v' := v' = ECoInductiveToInductive.trans p.1 v |}.

Next Obligation.
  move=> efl hasapp hasbox hasrel haspars hascstrs [Σ t] [wftp wft].
  cbn in *. eapply ECoInductiveToInductive.trans_program_wf; eauto. split => //.
Qed.
Next Obligation.
  red. move=> efl hasapp hasbox hasrel haspars hascstrs [Σ t] /= v [wfe1 wfe2] [ev].
  eexists. split; [ | eauto].
  econstructor.
  cbn -[transform_blocks].
  eapply ECoInductiveToInductive.trans_correct; cbn; eauto.
  eapply wellformed_closed_env, wfe1.
  Unshelve. all:eauto.
Qed.

#[global]
Instance coinductive_to_inductive_transformation_ext (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = true} :
  TransformExt.t (coinductive_to_inductive_transformation efl (has_app := has_app) (has_rel := has_rel)
    (has_box := has_box) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks))
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  eapply ECoInductiveToInductive.trust_cofix.
Qed.

#[global]
Instance coinductive_to_inductive_transformation_ext' (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {has_box : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = true} :
  TransformExt.t (coinductive_to_inductive_transformation efl (has_app := has_app) (has_rel := has_rel)
    (has_box := has_box) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks))
    extends_eprogram_env extends_eprogram.
Proof.
  red. intros p p' pr pr' ext. rewrite /transform /=.
  eapply ECoInductiveToInductive.trust_cofix.
Qed.

From MetaRocq.Erasure Require Import EReorderCstrs.

Definition eval_eprogram_mapping (wfl : WcbvFlags) (p : inductives_mapping * eprogram) t :=
  eval_eprogram wfl p.2 t.

Definition eval_eprogram_env_mapping (wfl : WcbvFlags) (p : inductives_mapping * eprogram_env) t :=
  eval_eprogram_env wfl p.2 t.

Definition to_program (e : eprogram_env) : eprogram :=
  (e.1, e.2).

Program Definition reorder_cstrs_transformation {efl : EEnvFlags} {wca : cstr_as_blocks = false} {has_app : has_tApp}
  (wfl : WcbvFlags) {wcon : with_constructor_as_block = false} :
  Transform.t _ _ _ EAst.term _ _
    (eval_eprogram_env_mapping wfl) (eval_eprogram wfl) :=
  {| name := "reorder inductive constructors ";
    transform p _ := EReorderCstrs.reorder_program p.1 (to_program p.2) ;
    pre p := [/\ wf_eprogram_env efl p.2, EEtaExpandedFix.expanded_eprogram_env p.2 & wf_inductives_mapping p.2.1 p.1] ;
    post p := wf_eprogram efl p /\ EEtaExpandedFix.expanded_eprogram p;
    obseq p hp p' v v' := v' = EReorderCstrs.reorder p.1 v |}.

Next Obligation.
  move=> efl wca hasapp wfl wcb [m p] [wfp exp wfm]. split => //.
  now unshelve eapply reorder_program_wf. cbn.
  now eapply reorder_program_expanded_fix.
Qed.
Next Obligation.
  red. intros efl wca hasapp wfl wcb [m p] v [wfp wfm] evp.
  destruct evp as [ev].
  unshelve eapply EReorderCstrs.optimize_correct in ev; trea.
  2,3:apply wfp.
  exists (reorder m v). split => //.
Qed.

#[global]
Instance reorder_cstrs_transformation_ext {efl : EEnvFlags} (wca : cstr_as_blocks = false) (has_app : has_tApp) (wfl : WcbvFlags)
  {wcon : with_constructor_as_block = false} :
  TransformExt.t (reorder_cstrs_transformation (wca := wca) (has_app := has_app) wfl (wcon:=wcon))
    (fun p p' => p.1 = p'.1 /\ extends p.2.1 p'.2.1) (fun p p' => extends p.1 p'.1).
Proof.
  red. intros p p' pr pr' [eq ext].
  red; cbn. rewrite -eq. eapply EReorderCstrs.optimize_extends_env; eauto.
  move: pr'; cbn. now intros []. apply pr. apply pr'.
Qed.

#[global]
Instance reorder_cstrs_transformation_ext' {efl : EEnvFlags} (wca : cstr_as_blocks = false) (has_app : has_tApp) (wfl : WcbvFlags)
  {wcon : with_constructor_as_block = false} :
  TransformExt.t (reorder_cstrs_transformation (wca := wca) (has_app := has_app) wfl (wcon:=wcon))
    (fun p p' => p.1 = p'.1 /\ extends_eprogram_env p.2 p'.2) extends_eprogram.
Proof.
  red. intros p p' pr pr' [eq [ext eq']]. cbn.
  red. cbn. rewrite -eq -eq'. split => //. eapply EReorderCstrs.optimize_extends_env; eauto.
  move: pr'; cbn. now intros []. apply pr. apply pr'.
Qed.

From MetaRocq.Erasure Require Import EUnboxing.

Axiom trust_unboxing_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall (input : Transform.program _ term),
  wf_eprogram_env efl input -> wf_eprogram efl (unbox_program input).
Axiom trust_unboxing_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ term)
  (v : term),
  wf_eprogram_env efl p ->
  eval_eprogram_env wfl p v -> exists v' : term, eval_eprogram wfl (unbox_program p) v' /\ v' = unbox p.1 v.

Program Definition unbox_transformation (efl : EEnvFlags) (wfl : WcbvFlags)  :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram_env wfl) (eval_eprogram wfl) :=
  {| name := "unbox singleton constructors ";
    transform p _ := EUnboxing.unbox_program p ;
    pre p := wf_eprogram_env efl p ;
    post p := wf_eprogram efl p ;
    obseq p hp p' v v' := v' = unbox p.1 v |}.

Next Obligation.
  move=> efl wfl m. cbn. now apply trust_unboxing_wf.
Qed.
Next Obligation.
  red. eapply trust_unboxing_pres.
Qed.

#[global]
Axiom trust_unbox_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (unbox_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).

#[global]
Axiom trust_unbox_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (unbox_transformation efl wfl)
    extends_eprogram_env extends_eprogram.

Program Definition optional_transform {env env' term term' value value' eval eval'} (activate : bool)
  (tr : Transform.t env env' term term' value value' eval eval') :
  if activate then Transform.t env env' term term' value value' eval eval'
  else Transform.t env env term term value value eval eval :=
  if activate return if activate then Transform.t env env' term term' value value' eval eval'
  else Transform.t env env term term value value eval eval
  then tr
  else
  {| name := ("skipped " ^ tr.(name));
     transform p pr := p;
     pre := tr.(pre) ;
     post := tr.(pre) ;
     obseq p hp p' v v' := v' = v |}.
Next Obligation.
  intros. cbn. exact p.
Defined.
Next Obligation.
 cbn. intros. red. intros. exists v. split => //.
Defined.

Program Definition optional_self_transform {env term eval} (activate : bool)
  (tr : Transform.self_transform env term eval eval) :
  Transform.self_transform env term eval eval :=
  if activate return Transform.self_transform env term eval eval
  then tr
  else
  {| name := ("skipped " ^ tr.(name));
     transform p pr := p;
     pre := tr.(pre) ;
     post := tr.(pre) ;
     obseq p hp p' v v' := v' = v |}.
Next Obligation.
  intros. cbn. exact p.
Defined.
Next Obligation.
 cbn. intros. red. intros. exists v. split => //.
Defined.

#[global]
Instance optional_self_transformation_ext {env term eval} activate tr extends :
  TransformExt.t tr extends extends ->
  TransformExt.t (@optional_self_transform env term eval activate tr) extends extends.
Proof.
  red; intros. destruct activate; cbn in * => //. now apply H.
Qed.
