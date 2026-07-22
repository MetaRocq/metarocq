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


Lemma eval_SI_eval {efl : EEnvFlags} {wfl : WcbvFlags} Σ Γ e v n :
  ~~ has_cstr_params ->
  cstr_as_blocks ->
  with_constructor_as_block ->
  ~~ with_guarded_fix ->
  has_tApp ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ #|Γ| e ->
  eval Σ Γ e v n ->
  EWcbvEval.eval Σ (substlg (map term_of_val Γ) 0 e) (term_of_val v).
Proof.
  intros hCstrParams hCstrBlcs hCstrBlcs' h_unguarded h_app wf_Σ wf_env wf_e heval.
  induction heval; simple; try now econstructor.
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
    + now rewrite e2; simple.
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
  - unfold cunfold_cofix in heq1.
    destruct (nth_error mfix idx) eqn:heq; last easy; simple.
    injection heq1 as ?; subst.
    apply eval_SI_wellformed_val in heval1 as hwf; simple; last easy.
      unfold wf_fix, test_def in hwf; simple.
      repeat split; simple; try easy.
    assert (forallb (wellformed_val Σ) (cofix_env mfix env ++ env)).
    { rewrite cofix_env_map; simple.
      intros x [(? & ? & ?%in_rev%in_seq)%in_map_iff| hIn]%in_app_iff; subst; simple; last easy.
      simple; unfold wf_fix, test_def; simple.
      repeat split; try easy.
      now apply Nat.ltb_lt. }
    assert (wellformed Σ (#|mfix| + #|env|) (mkApps (dbody d) (map term_of_val args))).
    { rewrite wellformed_mkApps; simple; split; last first.
      { now intros; apply wellformed_val_wellformed. }
      now apply nth_error_In in heq. }
    eapply EWcbvEval.eval_cofix_case.
    + apply IHheval1; now simple.
    + unfold EGlobalEnv.cunfold_cofix; simple.
      reflexivity.
    + unshelve epose proof IHheval2 _ _; simple; try easy.
      eapply EWcbvEval.eval_iota_block; simple; try easy.
      { lazymatch goal with
        | h: EWcbvEval.eval _ ?e1 (tConstruct _ _ _)
          |- EWcbvEval.eval _ ?e2 (tConstruct _ _ _) =>
            assert (e1 = e2) as <-; last easy
        end.
        simple. f_equal; last first.
        - rewrite map_map_compose.
          apply All_map_eq. simple.
          intros arg hIn.
          assert (closed (term_of_val arg)) as h_closed.
          { now eapply wellformed_closed, wellformed_val_wellformed.  }
          now eapply substlg_closed.
        - rewrite cofix_subst_map cofix_env_map. simple.
          rewrite -substlg_app; simple.
          { intros ? ?%in_rev%in_seq.
            simple. intros ? ?.
            unfold test_def.
            apply closed_substlg; simple; last now eapply wellformed_closed.
            intros ? (? & ? & ?)%in_map_iff ?; subst.
            now eapply wellformed_closed, wellformed_val_wellformed. }
          { intros. now eapply wellformed_closed, wellformed_val_wellformed. }
          f_equal. rewrite map_map_compose.
          apply map_ext.
          intros; simple.
          reflexivity. }
      { now simple. }
      { now simple. }
      unshelve epose proof IHheval3 _ _; simple; try easy.
      { intros ? [?%in_rev | ?]%in_app_iff; last easy.
        now apply eval_SI_wellformed_val in heval2; simple. }
      { rewrite heq5. now apply nth_error_In in heq3. }
      lazymatch goal with
      | h: EWcbvEval.eval _ ?e1 (term_of_val _)
        |- EWcbvEval.eval _ ?e2 (term_of_val _) =>
          assert (e1 = e2) as <-; last easy
      end.
      unfold iota_red; simple.
      rewrite -substlg_app.
      { apply eval_SI_wellformed_val in heval2; simple; try easy.
        intros x hIn%in_rev. now eapply wellformed_closed, wellformed_val_wellformed. }
      { simple. intros ? ?.
        now eapply wellformed_closed, wellformed_val_wellformed. }
      do 2 f_equal; now simple.
  - unfold cunfold_cofix in heq1.
    destruct (nth_error mfix idx) eqn:heq; last easy; simple.
    injection heq1 as ?; subst.
    apply eval_SI_wellformed_val in heval1 as hwf; simple; last easy.
      unfold wf_fix, test_def in hwf; simple.
      repeat split; simple; try easy.
    assert (forallb (wellformed_val Σ) (cofix_env mfix env ++ env)).
    { rewrite cofix_env_map; simple.
      intros x [(? & ? & ?%in_rev%in_seq)%in_map_iff| hIn]%in_app_iff; subst; simple; last easy.
      simple; unfold wf_fix, test_def; simple.
      repeat split; try easy.
      now apply Nat.ltb_lt. }
    assert (wellformed Σ (#|mfix| + #|env|) (mkApps (dbody d) (map term_of_val args))).
    { rewrite wellformed_mkApps; simple; split; last first.
      { now intros; apply wellformed_val_wellformed. }
      now apply nth_error_In in heq. }
    eapply EWcbvEval.eval_cofix_proj.
    + apply IHheval1; now simple.
    + unfold EGlobalEnv.cunfold_cofix; simple.
      reflexivity.
    + unshelve epose proof IHheval2 _ _; simple; try easy.
      eapply EWcbvEval.eval_proj_block; simple; try easy.
      { lazymatch goal with
        | h: EWcbvEval.eval _ ?e1 (tConstruct _ _ _)
          |- EWcbvEval.eval _ ?e2 (tConstruct _ _ _) =>
            assert (e1 = e2) as <-; last easy
        end.
        simple. f_equal; last first.
        - rewrite map_map_compose.
          apply All_map_eq. simple.
          intros arg hIn.
          assert (closed (term_of_val arg)) as h_closed.
          { now eapply wellformed_closed, wellformed_val_wellformed.  }
          now eapply substlg_closed.
        - rewrite cofix_subst_map cofix_env_map. simple.
          rewrite -substlg_app; simple.
          { intros ? ?%in_rev%in_seq.
            simple. intros ? ?.
            unfold test_def.
            apply closed_substlg; simple; last now eapply wellformed_closed.
            intros ? (? & ? & ?)%in_map_iff ?; subst.
            now eapply wellformed_closed, wellformed_val_wellformed. }
          { intros. now eapply wellformed_closed, wellformed_val_wellformed. }
          f_equal. rewrite map_map_compose.
          apply map_ext.
          intros; simple.
          reflexivity. }
      { now simple. }
      { rewrite heq2. now simple. }
      apply value_final, value_term_of_val; simple.
      apply nth_error_In in heq5.
      now apply eval_SI_wellformed_val in heval2; simple.
  - econstructor; try easy.
    apply IHheval; try easy.
    pose proof lookup_env_wellformed wf_Σ isdecl.
    simple.
  - rewrite /lookup_constructor_pars_args e /= in wf_e.
    rewrite hCstrBlcs in wf_e; simple.
    econstructor; simple; try easy.
    { symmetry. now apply eqb_eq. }
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
Qed.
