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
  cstr_as_blocks ->
  with_constructor_as_block ->
  ~~ with_guarded_fix ->
  has_tApp ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ #|Γ| e ->
  eval Σ Γ e v n ->
  EWcbvEval.eval Σ (substl (map term_of_val Γ) e) (term_of_val v).
Proof.
  intros hCstrBlcs hCstrBlcs' h_unguarded h_app wf_Σ wf_env wf_e heval.
  induction heval; simple; try now econstructor.
  - econstructor.
    + now apply IHheval1; simple.
    + now apply IHheval2; simple.
  - assert (wellformed_val Σ v).
    { now eapply wf_env, nth_error_In. }
    assert (closed (term_of_val v)).
    { now eapply wellformed_closed, wellformed_val_wellformed. }
    erewrite substl_tRel; simple; try eassumption || reflexivity.
    now apply value_final, value_term_of_val.
  - econstructor; simple.
    + now apply IHheval1; simple.
    + now apply IHheval2; simple.
    + rewrite /substl /= in IHheval3.
      assert (wellformed_val Σ a').
      { now eapply eval_SI_wellformed_val; simple; try eassumption. }
      apply eval_SI_wellformed_val in heval1 as wf_cls_b_Γ'; simple; try easy.
      rewrite -fold_csubst_csubst_commute; simple; try easy.
      * now eapply wellformed_closed, wellformed_val_wellformed.
      * intros. now eapply wellformed_closed, wellformed_val_wellformed.
      * now apply IHheval3; simple.
  - econstructor.
    + now apply IHheval1; simple.
    + assert (wellformed_val Σ b0').
      { now eapply eval_SI_wellformed_val; simple. }
      rewrite -fold_csubst_csubst_commute; simple; try easy.
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
      unfold substl.
      replace #|br.1| with (#|map term_of_val (List.rev args)| + 0) by now simple.
      rewrite fold_left_csubst_app; simple.
      simple. rewrite -map_app.
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
      rewrite fold_left_map_def; fold csubst; simple.
      rewrite fix_subst_map.
      simple.
      erewrite (map_ext (fold_left _ _)); last first.
      { intros x. rewrite fold_left_map_def; fold csubst. reflexivity. }
      rewrite fold_left_csubst_tLambda.
      simple.
      eapply EWcbvEval.eval_beta.
      { simple. now constructor. }
      { apply value_final, value_term_of_val; simple. }
      rewrite -fold_csubst_csubst_commute; simple; try easy.
      { eapply wellformed_closed, wellformed_val_wellformed; simple. easy. }
      { intros ? hIn%in_rev%in_seq.
        simple.
        intros [] hIn'.
        unfold test_def; simple.
        rewrite Nat.add_0_r.
        apply closed_fold_left_csubst; simple; try easy.
        - intros ? (? & ? & ?)%in_map_iff k; subst.
          now eapply wellformed_closed, wellformed_val_wellformed, wf_clos.
        - now apply wf_clos, wellformed_closed in hIn'. }
      simple.
      rewrite fix_env_map in IHheval3.
      simple.
      rewrite fold_csubst_csubst_commute //.
      { now eapply wellformed_closed, wellformed_val_wellformed. }
      { simple. intros n hIn%in_rev%in_seq. simple.
        intros ? ?.
        unfold test_def; simple.
        rewrite Nat.add_0_r.
        apply closed_fold_left_csubst; simple; try easy.
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
      unfold substl in IH3; simple.
      assert (∀ x, 0 <= x < #|mfix| -> wellformed Σ 0 (substl (map term_of_val Γ') (tFix mfix x))).
      { intros. apply wellformed_fold_left_csubst; simple; try easy.
        - intros ? (x' & ? & hIn)%in_map_iff k; subst.
          now apply wellformed_val_wellformed, wf_clos.
        - unfold wf_fix; simple; repeat split; try easy.
          now apply Nat.ltb_lt. }
      rewrite map_app map_map_compose fold_csubst_csubst_commute in IH3; simple; try easy.
      { now eapply wellformed_closed, wellformed_val_wellformed. }
      { intros ? [(x & ? & hIn%in_rev%in_seq)%in_map_iff | (x & ? & hIn)%in_map_iff]%in_app_iff; subst.
        - now eapply wellformed_closed.
        - now eapply wellformed_closed, wellformed_val_wellformed, wf_clos. }
      rewrite -fold_left_csubst_app in IH3; simple; try easy.
      { intros x ?%in_rev%in_seq.
        now eapply wellformed_closed, wellformed_up. }
      { intros x hIn. now eapply wellformed_closed, wellformed_val_wellformed. }
      rewrite Nat.add_1_r in IH3.
      erewrite map_ext; first eassumption.
      intros; simple.
      erewrite map_ext; first reflexivity.
      intros; simple;
      now rewrite fold_left_map_def.
  - apply eval_mkApps_CoFix; try easy.
    rewrite wellformed_mkApps // in wf_e.
    simple.
    destruct wf_e as [? wf_args].
    induction a in wf_args, IHa |- *; simple; try easy.
    destruct IHa.
    constructor.
    + apply e; now simple.
    + now apply IHa0.
  - unfold cunfold_cofix in heq1.
    destruct (nth_error mfix idx) eqn:heq; last easy; simple.
    injection heq1 as ?; subst.
    apply eval_SI_wellformed_val in heval1 as wf_cofix_clos; simple; try easy.
    unfold wf_fix, test_def in wf_cofix_clos; simple.
    assert (forallb (wellformed_val Σ) (cofix_env mfix env ++ env)).
    { simple. rewrite cofix_env_map.
      intros x [(? & ? & hIn%in_rev%in_seq)%in_map_iff | hIn]%in_app_iff; simple; last easy.
      subst. simple; unfold wf_fix; simple; repeat split; try easy.
      now apply Nat.ltb_lt. }
    assert (wellformed Σ (#|mfix| + #|env|) (mkApps (dbody d) (map term_of_val args))).
    { apply nth_error_In in heq.
      rewrite wellformed_mkApps; simple; split; try easy.
      intros ? ?. now apply wellformed_val_wellformed. }
    assert (forallb (wellformed_val Σ) con_args).
    { apply eval_SI_wellformed_val in heval2; intros; now simple. }
    eapply EWcbvEval.eval_cofix_case.
    + now apply IHheval1; simple.
    + unfold EGlobalEnv.cunfold_cofix.
      simple; reflexivity.
    + econstructor; first now destruct with_constructor_as_block.
      * rewrite fold_left_map_def; fold csubst; simple.
        erewrite map_ext; last first.
        { intros. rewrite fold_left_map_def; fold csubst; simple. reflexivity. }
        unfold substl.
        rewrite cofix_subst_map.
        simple.
        match goal with
        | |- context[fold_left _ ?f'] => set l := f'
        end.
        replace #|mfix| with (#|l| + 0) by now unfold l; simple.
        rewrite fold_left_csubst_app.
        { simple.
          intros ? (x & ? & hIn%in_rev%in_seq)%in_map_iff; subst.
          erewrite map_ext; last first.
          { intros ?; rewrite -fold_left_map_def. reflexivity. }
          simple.
          intros d' hIn'.
          unfold test_def.
          rewrite fold_left_map_def; simple.
          rewrite Nat.add_0_r.
          apply closed_fold_left_csubst; simple.
          - intros ? (? & ? & ?)%in_map_iff ?; subst.
            now eapply wellformed_closed, wellformed_val_wellformed.
          - now eapply wellformed_closed. }
        { simple.
          intros x hIn.
          now eapply wellformed_closed, wellformed_val_wellformed. }
        fold (substl (l ++ map term_of_val env) (dbody d)).
        assert (l = map term_of_val (cofix_env mfix env)) as heq'.
        { subst l.
          rewrite cofix_env_map map_map_compose.
          apply map_ext.
          intros n. simple.
          f_equal. apply map_ext.
          intros d'.
          now rewrite fold_left_map_def. }
        rewrite heq' -map_app.
        assert (map term_of_val args = (map (substl (map term_of_val (cofix_env mfix env ++ env))) (map term_of_val args))) as heq''.
        { assert (forallb (λ a, closed (term_of_val a)) args) as h_closed.
          { simple. intros a hIn. now eapply wellformed_closed, wellformed_val_wellformed. }
          match goal with
          | |- map _ _ = map (substl ?f) _ => generalize f
          end.
          intros σ.
          induction args as [| a args IH] in h_closed |- *; simple; try easy.
          f_equal; last first.
          { now apply IH. }
          assert (closed (term_of_val a)) as h_closed_a by easy.
          unfold substl.
          induction σ in h_closed_a |- *; simple; try easy.
          now rewrite csubst_closed. }
        rewrite heq''.
        now apply IHheval2; simple.
      * eassumption.
      * simple. reflexivity.
      * simple.
      * simple.
      * unfold iota_red.
        simple.
        unfold substl.
        replace #|br.1| with (#|map term_of_val (List.rev con_args)| + 0) by now simple.
        rewrite fold_left_csubst_app.
        { simple.
          intros x hIn%in_rev.
          now eapply wellformed_closed, wellformed_val_wellformed. }
        { simple.
          intros x hIn.
          now eapply wellformed_closed, wellformed_val_wellformed. }
        rewrite -map_app.
        apply IHheval3.
        { simple. now intros x [ hIn%in_rev |hIn]%in_app_iff. }
        rewrite heq5.
        now eapply wf_e, nth_error_In.
  - rewrite /substl /= in IHheval. econstructor; try easy.
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
Qed.
