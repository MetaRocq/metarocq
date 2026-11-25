(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From MetaRocq.Erasure.StepIndex Require Import Tactics Utils SubstLemmas Values Primitives EvalStepIndex.
From Stdlib Require Import Relations.Relations.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".


(** [EWcbvEval] counterpart of [force Σ v ind c cargs]: a case analysis or
    a projection on a term evaluating to [term_of_val v] behaves as on the
    constructor block [tConstruct ind c (map term_of_val cargs)]. *)
Definition forces {wfl : WcbvFlags} Σ (v : value) ind c (cargs : list value)
  : Type :=
  (∀ discr pars cdecl brs br res,
    EWcbvEval.eval Σ discr (term_of_val v) ->
    constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
    nth_error brs c = Some br ->
    #|cargs| = pars + cdecl.(cstr_nargs) ->
    #|skipn pars (map term_of_val cargs)| = #|br.1| ->
    EWcbvEval.eval Σ (iota_red pars (map term_of_val cargs) br) res ->
    EWcbvEval.eval Σ (tCase (ind, pars) discr brs) res) ×
  (∀ discr p cdecl a res,
    EWcbvEval.eval Σ discr (term_of_val v) ->
    ind = proj_ind p ->
    c = 0 ->
    constructor_isprop_pars_decl Σ (proj_ind p) 0 =
      Some (false, proj_npars p, cdecl) ->
    #|cargs| = proj_npars p + cstr_nargs cdecl ->
    nth_error (map term_of_val cargs) (proj_npars p + proj_arg p) = Some a ->
    EWcbvEval.eval Σ a res ->
    EWcbvEval.eval Σ (tProj p discr) res).


Lemma forces_construct {wfl : WcbvFlags} Σ ind c cargs :
  with_constructor_as_block ->
  forces Σ (vConstruct ind c cargs) ind c cargs.
Proof.
  intros hblock. split.
  - intros discr pars cdecl brs br res ev isp hnth len len' evi.
    eapply EWcbvEval.eval_iota_block; tea.
    now rewrite length_map.
  - intros discr p cdecl a res ev -> -> isp len hnth eva.
    eapply EWcbvEval.eval_proj_block; tea.
    now rewrite length_map.
Qed.


(** One unfolding step: this is where the rules [EWcbvEval.eval_cofix_case]
    and [EWcbvEval.eval_cofix_proj] are used. *)
Lemma forces_cofix {efl : EEnvFlags} {wfl : WcbvFlags} Σ mfix idx env args fn
  v ind c cargs :
  cstr_as_blocks ->
  with_constructor_as_block ->
  has_tApp ->
  wellformed_val Σ (vCoFixClos mfix idx env args) ->
  wellformed_val Σ v ->
  cunfold_cofix mfix idx = Some fn ->
  EWcbvEval.eval Σ
    (substlg
      (map term_of_val (List.rev args ++ cofix_env mfix env ++ env)) 0
      (mkApps (lift0 #|args| fn) (map tRel (List.rev (seq 0 #|args|)))))
    (term_of_val v) ->
  forces Σ v ind c cargs ->
  forces Σ (vCoFixClos mfix idx env args) ind c cargs.
Proof.
  intros hCstrBlcs hCstrBlcs' h_app hwf hwfv heq1 evbody [hcase hproj].
  pose proof (value_term_of_val _ _ hCstrBlcs' h_app hwfv) as val_v.
  apply value_final in val_v.
  unfold cunfold_cofix in heq1.
  destruct (nth_error mfix idx) as [d|] eqn:heq; last easy.
  cbn in heq1. injection heq1 as <-.
  pose proof (substlg_cofix_clos_body _ _ _ _ _ _ hCstrBlcs h_app hwf heq)
    as hbody.
  rewrite hbody in evbody.
  split.
  - intros discr pars cdecl brs br res ev isp hnth len len' evi.
    eapply EWcbvEval.eval_cofix_case with (bv := term_of_val v).
    + now simple.
    + unfold EGlobalEnv.cunfold_cofix; simple.
      reflexivity.
    + now simple.
    + eapply hcase; tea.
  - intros discr p cdecl a res ev -> -> isp len hnth eva.
    eapply EWcbvEval.eval_cofix_proj with (bv := term_of_val v).
    + now simple.
    + unfold EGlobalEnv.cunfold_cofix; simple.
      reflexivity.
    + now simple.
    + eapply hproj; tea; reflexivity.
Qed.


(** The main statement, together with its companion for [force] (see
    [force_SI_forces] below). *)
Lemma eval_SI_eval {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ e v n :
  cstr_as_blocks ->
  with_constructor_as_block ->
  ~~ with_guarded_fix ->
  has_tApp ->
  has_tRel ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ #|Γ| e ->
  eval Σ Γ e v n ->
  EWcbvEval.eval Σ (substlg (map term_of_val Γ) 0 e) (term_of_val v).
Proof.
  intros hCstrBlcs hCstrBlcs' h_unguarded h_app h_rel wf_Σ wf_env wf_e
    heval.
  revert wf_env wf_e.
  induction heval using eval_rect with
    (Pf := fun v ind c cargs _ _ =>
      wellformed_val Σ v -> forces Σ v ind c cargs);
    [intros wf_env wf_e; simple; try now econstructor.. | |].
  - econstructor.
    + now apply IHheval1; simple.
    + now apply IHheval2; simple.
  - assert (wellformed_val Σ v).
    { now eapply wf_env, nth_error_In. }
    assert (closed (term_of_val v)).
    { now eapply wellformed_closed, wellformed_val_wellformed. }
    erewrite substlg_tRel; simple; try eassumption || reflexivity.
    now apply value_final, value_term_of_val.
  - econstructor; simple.
    + now apply IHheval1; simple.
    + now apply IHheval2; simple.
    + assert (wellformed_val Σ a').
      { now eapply eval_SI_wellformed_val; simple; try eassumption. }
      apply eval_SI_wellformed_val in heval1 as wf_cls_b_Γ'; simple; try easy.
      rewrite -substlg_csubst_commute; simple; try easy.
      * now eapply wellformed_closed, wellformed_val_wellformed.
      * intros. now eapply wellformed_closed, wellformed_val_wellformed.
      * now apply IHheval3; simple.
  - econstructor.
    + now apply IHheval1; simple.
    + assert (wellformed_val Σ b0').
      { now eapply eval_SI_wellformed_val; simple. }
      rewrite -substlg_csubst_commute; simple; try easy.
      * now eapply wellformed_closed, wellformed_val_wellformed.
      * intros. now eapply wellformed_closed, wellformed_val_wellformed.
      * now apply IHheval2; simple.
  - assert (forallb (wellformed_val Σ) (List.rev args)).
    { simple. intros x hIn%in_rev.
      apply eval_SI_wellformed_val in heval1; simple; try easy. }
    assert (forallb (closedn 0) (map term_of_val (List.rev args))).
    { simple. intros x hIn.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    assert (forallb (closedn 0) (map term_of_val Γ)).
    { simple. intros x hIn.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    econstructor; first assumption; simple; try easy.
    + now apply IHheval1; simple.
    + now simple.
    + simple.
    + unfold iota_red; simple.
      replace #|br.1| with (#|map term_of_val (List.rev args)| + 0) by now simple.
      rewrite substlg_app; simple.
      apply IHheval2; simple; try easy.
      * now intros x [?|?]%in_app_or.
      * rewrite e3. now eapply wf_e, nth_error_In.
  - eapply eval_proj_block; try eassumption.
    + apply IHheval; now simple.
    + now simple.
    + now simple.
    + apply value_final, value_term_of_val; try easy.
      apply eval_SI_wellformed_val in heval; simple; try easy.
      now eapply heval, nth_error_In. 
  - unfold cunfold_fix in e0.
    destruct (nth_error mfix idx) as [[? []]|] eqn:heq; simple; try easy.
    injection e0 as e0; subst.
    eapply eval_fix'; simple.
    + now destruct with_guarded_fix.
    + now apply IHheval1; simple.
    + unfold EGlobalEnv.cunfold_fix in *; now simple.
    + now apply IHheval2; simple.
    + assert (wellformed_val Σ av).
      { apply eval_SI_wellformed_val in heval2; simple; easy. }
      apply eval_SI_wellformed_val in heval1 as wf_clos; simple; try easy.
      unfold wf_fix, test_def in wf_clos; simple.
      rewrite fix_subst_map. simple.
      eapply EWcbvEval.eval_beta.
      { simple. now constructor. }
      { apply value_final, value_term_of_val; simple. }
      rewrite -substlg_csubst_commute; simple; try easy.
      { eapply wellformed_closed, wellformed_val_wellformed; simple. easy. }
      { intros ? hIn%in_rev%in_seq.
        simple. intros [] hIn'.
        unfold test_def; simple.
        apply closed_substlg; simple; try easy.
        - intros ? (? & ? & ?)%in_map_iff k; subst.
          now eapply wellformed_closed, wellformed_val_wellformed, wf_clos.
        - now apply wf_clos, wellformed_closed in hIn'. }
      simple.
      rewrite fix_env_map in IHheval3.
      simple.
      rewrite substlg_csubst_commute //.
      { now eapply wellformed_closed, wellformed_val_wellformed. }
      { simple. intros n hIn%in_rev%in_seq. simple.
        intros ? ?.
        unfold test_def; simple.
        apply closed_substlg; simple; try easy.
        - intros ? (? & ? & ?)%in_map_iff k; subst.
          now eapply wellformed_closed, wellformed_val_wellformed, wf_clos.
        - now eapply wellformed_closed, wf_clos. }
      unshelve epose proof IHheval3 _ _ as IH3.
      { simple; split; try easy.
        intros ? [(x & ? & hIn%in_rev%in_seq)%in_map_iff | hIn]%in_app_iff; subst.
        - simple; unfold wf_fix; simple; repeat split; try easy.
          now apply Nat.ltb_lt.
        - now apply wf_clos. } 
      { apply nth_error_In, wf_clos in heq; now simple. }
      simple.
      assert (∀ x, 0 <= x < #|mfix| -> wellformed Σ 0 (substlg (map term_of_val Γ') 0 (tFix mfix x))).
      { intros. apply wellformed_substlg; simple; try easy.
        - intros ? (x' & ? & hIn)%in_map_iff k; subst.
          now apply wellformed_val_wellformed, wf_clos.
        - unfold wf_fix; simple; repeat split; try easy.
          now apply Nat.ltb_lt. }
      rewrite map_map_compose substlg_csubst_commute in IH3; simple; try easy.
      { now eapply wellformed_closed, wellformed_val_wellformed. }
      { intros ? [(x & ? & hIn%in_rev%in_seq)%in_map_iff | (x & ? & hIn)%in_map_iff]%in_app_iff; subst.
        - now eapply wellformed_closed.
        - now eapply wellformed_closed, wellformed_val_wellformed, wf_clos. }
      rewrite -substlg_app in IH3; simple; try easy.
      { intros x ?%in_rev%in_seq.
        now eapply wellformed_closed, wellformed_up. }
      { intros x hIn. now eapply wellformed_closed, wellformed_val_wellformed. }
      erewrite map_ext; first eassumption.
      intros; now simple.
  - rewrite mkApps_app.
    eapply eval_app_cong.
    + now apply IHheval1; simple.
    + destruct with_guarded_fix; first easy.
      destruct args using list_rect_rev; simple.
      rewrite mkApps_app; simple.
      unfold isPrimApp, isConstructApp, isLazyApp.
      now rewrite head_tApp head_mkApps.
    + now apply IHheval2; simple.
  - assert (wellformed_val Σ (vCoFixClos mfix idx env args)) as hwf.
    { now eapply eval_SI_wellformed_val; simple; try eassumption. }
    assert (wellformed_val Σ (vConstruct ind c cargs)) as hwfc.
    { eapply force_SI_wellformed_val; last exact e2; easy. }
    destruct (IHheval2 hwf) as [hcase _].
    assert (forallb (wellformed_val Σ) (List.rev cargs)).
    { simple. intros x hIn%in_rev. now apply hwfc. }
    assert (forallb (closedn 0) (map term_of_val (List.rev cargs))).
    { simple. intros x hIn.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    assert (forallb (closedn 0) (map term_of_val Γ)).
    { simple. intros x hIn.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    eapply hcase; simple; try easy.
    + now apply IHheval1; simple.
    + unfold iota_red; simple.
      replace #|br.1| with (#|map term_of_val (List.rev cargs)| + 0)
        by now simple.
      rewrite substlg_app; simple.
      apply IHheval3; simple; try easy.
      * now intros x [?|?]%in_app_or.
      * rewrite e6. now eapply wf_e, nth_error_In.
  - assert (wellformed_val Σ (vCoFixClos mfix idx env args)) as hwf.
    { now eapply eval_SI_wellformed_val; simple; try eassumption. }
    assert (wellformed_val Σ (vConstruct (proj_ind p) 0 cargs)) as hwfc.
    { eapply force_SI_wellformed_val; last exact e2; easy. }
    destruct (IHheval0 hwf) as [_ hproj].
    eapply hproj; try eassumption; try reflexivity.
    + simple. now apply IHheval; simple.
    + now simple.
    + apply value_final, value_term_of_val; try easy.
      simple. now eapply hwfc, nth_error_In.
  - econstructor; try easy.
    apply IHheval; try easy.
    pose proof lookup_env_wellformed wf_Σ isdecl.
    simple.
  - rewrite /lookup_constructor_pars_args e /= in wf_e.
    econstructor; simple; try easy.
    rewrite hCstrBlcs in wf_e; simple.
    clear l.
    destruct wf_e as [_ [_ wf_e]]. induction a; simple; try easy.
    destruct IHa.
    constructor.
    + now apply e0; simple.
    + now apply IHa0.
  - constructor.
    inversion evih; subst; unfold map_prim, test_prim, test_array_model in *; simple; repeat split; try easy; constructor; last first.
    { now apply H3; simple. }
    destruct wf_e as [? wf_e].
    clear H H3 H4 H5 H6. 
    revert ev0 wf_e wf_env X. clear.
    unfold test_prim, test_array_model; simple.
    induction ev0; simple; try easy.
    intros wf_e wf_Γ [? ?].
    simple.
    constructor; simple; try easy.
    + now apply e; simple. 
    + now apply IHev0; simple.
  - econstructor.
    + now apply IHheval1; simple.
    + assert (wellformed_val Σ (vLazy t' Γ')).
      { now eapply eval_SI_wellformed_val; simple. }
      apply IHheval2; now simple.
  - intros hwf. now apply forces_construct.
  - intros hwf.
    pose proof (wf_cofix_clos_env _ _ _ _ _ hwf) as wf_cenv.
    pose proof (wf_cofix_clos_body _ _ _ _ _ _ h_app h_rel hwf heq1)
      as wf_body.
    assert (wellformed_val Σ v) as hwfv.
    { eapply eval_SI_wellformed_val; last exact heval; easy. }
    eapply forces_cofix; tea; auto.
Qed.


(** Companion of [eval_SI_eval] for the forcing judgment. *)
Lemma force_SI_forces {efl : EEnvFlags} {wfl : WcbvFlags} Σ v ind c cargs n :
  cstr_as_blocks ->
  with_constructor_as_block ->
  ~~ with_guarded_fix ->
  has_tApp ->
  has_tRel ->
  wf_glob Σ ->
  wellformed_val Σ v ->
  force Σ v ind c cargs n ->
  forces Σ v ind c cargs.
Proof.
  intros hCstrBlcs hCstrBlcs' h_unguarded h_app h_rel wf_Σ hwf hforce.
  revert hwf.
  induction hforce using force_rect with (P := fun _ _ _ _ _ => True);
    try exact I; intros hwf; first now apply forces_construct.
  pose proof (wf_cofix_clos_env _ _ _ _ _ hwf) as wf_cenv.
  pose proof (wf_cofix_clos_body _ _ _ _ _ _ h_app h_rel hwf heq1)
    as wf_body.
  assert (wellformed_val Σ v) as hwfv.
  { eapply eval_SI_wellformed_val; last eassumption; easy. }
  eapply forces_cofix; tea; auto.
  eapply eval_SI_eval; tea.
Qed.
