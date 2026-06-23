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
  cstr_as_blocks = with_constructor_as_block ->
  with_guarded_fix = false ->
  has_tApp ->
  wf_glob Σ ->
  forallb (wellformed_val Σ) Γ ->
  wellformed Σ #|Γ| e ->
  eval Σ Γ e v n ->
  EWcbvEval.eval Σ (substl (map term_of_val Γ) e) (term_of_val v).
Proof.
  intros ? h_unguarded h_app wf_Σ wf_env wf_e heval.
  induction heval; simple; try now econstructor.
  - econstructor.
    + now apply IHheval1; simple.
    + now apply IHheval2; simple.
  - induction Γ in n, e, h_app, wf_env, wf_e |- *; destruct n; try easy.
    + unfold substl. cbn.
      simpl in e. injection e as ->.
      fold (substl (map term_of_val Γ) (term_of_val v)).
      assert (closed (term_of_val v)).
      { eapply wellformed_closed, wellformed_val_wellformed; simple; easy. }
      unfold substl.
      clear IHΓ.
      induction Γ.
      * simple. now apply value_final, value_term_of_val.
      * simple. rewrite csubst_closed //.
        apply IHΓ; simple.
        intros; now apply wf_env.
    + now apply IHΓ; simple.
  - econstructor; simple.
    + now apply IHheval1; simple.
    + now apply IHheval2; simple.
    + rewrite /substl /= in IHheval3.
      assert (wellformed_val Σ a').
      { now eapply eval_SI_wellformed_val; simple; try eassumption. }
      apply eval_SI_wellformed_val in heval1 as wf_cls_b_Γ'; simple; try easy.
      match goal with
      | h: context[EWcbvEval.eval Σ ?a (term_of_val res)]
        |- EWcbvEval.eval Σ ?b (term_of_val res) =>
        replace b with a; first apply h
      end; simple; try easy.
      apply fold_csubst_csubst_commute; simple; try easy.
      * eapply wellformed_closed.
        now eapply wellformed_val_wellformed.
      * intros. eapply wellformed_closed.
        now eapply wellformed_val_wellformed. 
  - econstructor.
    + now apply IHheval1; simple.
    + assert (wellformed_val Σ b0').
      { now eapply eval_SI_wellformed_val; simple. }
      match goal with
      | h: context[EWcbvEval.eval Σ ?a (term_of_val res)]
        |- EWcbvEval.eval Σ ?b (term_of_val res) =>
        replace b with a; first apply h
      end; simple; try easy.
      apply fold_csubst_csubst_commute; simple; try easy.
      * eapply wellformed_closed.
        now eapply wellformed_val_wellformed.
      * intros. eapply wellformed_closed.
        now eapply wellformed_val_wellformed. 
  - assert (forallb (wellformed_val Σ) (List.rev args)).
    { simple. intros x hIn%in_rev.
      apply eval_SI_wellformed_val in heval1; simple; try easy. }
    assert (forallb (closedn 0) (map term_of_val (List.rev args))).
    { simple. intros x hIn.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    assert (forallb (closedn 0) (map term_of_val Γ)).
    { simple. intros x hIn.
      now eapply wellformed_closed, wellformed_val_wellformed. }
    destruct with_constructor_as_block eqn:heq; rewrite ->H in *.
    { econstructor; first assumption; simple; try easy.
      - now apply IHheval1; simple.
      - now simple.
      - simple.
      - unfold iota_red; simple.
        unfold substl.
        replace #|br.1| with (#|map term_of_val (List.rev args)| + 0) by now simple.
        rewrite fold_left_csubst_app; simple.
        simple. rewrite -map_app.
        apply IHheval2; simple; try easy.
        + now intros x [?|?]%in_app_or.
        + rewrite e3. now eapply wf_e, nth_error_In. }
    { econstructor; first assumption; simple; try easy.
      - now apply IHheval1; simple.
      - now simple.
      - simple.
      - unfold iota_red; simple.
        unfold substl.
        replace #|br.1| with (#|map term_of_val (List.rev args)| + 0) by now simple.
        rewrite fold_left_csubst_app. simple.
        simple. rewrite -map_app.
        apply IHheval2; simple; try easy.
        + now intros x [?|?]%in_app_or.
        + rewrite e3. now eapply wf_e, nth_error_In. }
  - rewrite H cstr_blcks in IHheval.
    eapply eval_proj_block; try eassumption.
    + apply IHheval; now simple.
    + now simple.
    + now simple.
    + apply value_final, value_term_of_val; try easy.
      apply eval_SI_wellformed_val in heval; simple; try easy.
      now eapply heval, nth_error_In. 
  - rewrite /substl /= in IHheval1, IHheval2, IHheval3.
    unfold cunfold_fix in e0.
    destruct (nth_error mfix idx) as [[? []]|] eqn:heq; simple; try easy.
    injection e0 as e0; subst.
    eapply eval_fix'; simple.
    + now apply IHheval1; simple.
    + unfold EGlobalEnv.cunfold_fix in *; now simple.
    + now apply IHheval2; simple.
    + assert (wellformed_val Σ av).
      { apply eval_SI_wellformed_val in heval2; simple; easy. }
      unfold map_def; simple.
      replace (
        dbody 
          (fold_left (λ b t0, {| 
            dname := EAst.dname b; 
            dbody := csubst t0 #|mfix| (dbody b);
            rarg := EAst.rarg b |}) (map term_of_val Γ')
            {| dname := dname; dbody := tLambda na fn; rarg := rarg |}))
      with 
      (tLambda na 
        (fold_left 
          (λ b t0, csubst t0 (S #|mfix|) b) 
          (map term_of_val Γ')
          fn)
      ); last first.
      { induction Γ' in fn |- *; now simple. }
      eapply EWcbvEval.eval_beta.
      { simple. now constructor. }
      { apply value_final, value_term_of_val; simple. }
      rewrite -fold_csubst_csubst_commute; simple; try easy.
      { eapply wellformed_closed, wellformed_val_wellformed; simple. easy. }
      { intros x hIn.
        set mfix' := (map _ _) in hIn.
        pose proof closed_fix_subst mfix'; simple.
        apply H1; simple.
        intros ?. rewrite in_map_iff.
        intros (x' & <- & hIn').
        unfold test_def, mfix'.
        simple.
        apply eval_SI_wellformed_val in heval1; simple; try easy.
        unfold wf_fix, test_def in *; simple.
        replace (
            dbody 
              (fold_left 
                (λ b t0, {| dname := EAst.dname b; dbody := csubst t0 #|mfix| (dbody b); rarg := EAst.rarg b |}) 
                (map term_of_val Γ') x')
        ) with (
          (fold_left (λ b t0, csubst t0 #|mfix| b) (map term_of_val Γ') (dbody x'))
        ); simple; last first.
        { clear.
          induction Γ' in x' |- *; simple; try easy.
          now rewrite -IHΓ'. }
        assert (closedn (#|mfix| + #|Γ'|) (dbody x')).
        { now eapply wellformed_closed. }
        revert H2.
        clear mfix' hIn H1.
        generalize #|mfix| as n.
        assert (∀ v n, In v Γ' → closedn n (term_of_val v)) as h_closed'.
        { intros. apply (@closed_upwards 0); last easy.
          eapply wellformed_closed, wellformed_val_wellformed; easy. }
        revert h_closed'. clear.
        intros h_closed' n h_closed.
        induction Γ' in n, h_closed, h_closed' |- *; simple.
        rewrite fold_csubst_csubst_commute; simple; try easy.
        unshelve epose proof IHΓ' _ (S n) _; try easy.
        { now rewrite Nat.add_succ_r in h_closed. }
        simple. rewrite ->Nat.add_0_r in *.
        eapply closed_csubst_test; now simple. }
      
      assert (forallb (wellformed_val Σ) Γ').
      { apply eval_SI_wellformed_val in heval1; now simple. }
      assert (forallb (wellformed_val Σ) (fix_env mfix Γ')).
      { simple. apply eval_SI_wellformed_val in heval1; simple; try easy.
        intros x hIn.
        revert hIn heval1. clear.
        unfold wf_fix, test_def; simple.
        intros hIn (((h_fix & wf_Γ') & wf_mfix) & h_lt & wf_body).
        unfold fix_env in hIn.
        set (
          f_aux mfix := fix aux (n : nat) : list value :=
            match n with
            | 0 => []
            | S n0 => vRecClos mfix n0 Γ' :: aux n0
            end
        ).
        fold (f_aux mfix) in hIn.
        remember #|mfix| as n eqn:heq in hIn.
        assert (n <= #|mfix|) by (subst; reflexivity).
        clear heq.
        induction n; simple; try easy.
        destruct hIn as [<- | hIn]; simple; try easy.
        unfold wf_fix, test_def; simple; repeat split; try easy.
        now apply Nat.ltb_lt. }
      match goal with
      | h : context[EWcbvEval.eval Σ ?t1 ?res] 
        |- EWcbvEval.eval Σ ?t2 ?res =>
          replace t2 with t1; first apply h
      end; simple; try easy.
      * split; first easy.
        now intros x [? | ?]%in_app_iff.
      * apply eval_SI_wellformed_val in heval1; simple; try easy.
        unfold wf_fix, test_def in heval1; simple.
        destruct heval1 as [_ [_ h]].
        unshelve epose proof h {| dname := dname; dbody := tLambda na fn; rarg := rarg |} _.
        { now eapply nth_error_In. }
        simple; try easy.
      * assert (
          map term_of_val (fix_env mfix Γ') =
            fix_subst (map (fold_left (λ (b : def term) t0, {| dname := EAst.dname b; dbody := csubst t0 #|mfix| (dbody b); rarg := EAst.rarg b |})
            (map term_of_val Γ')) mfix)
        ) as heq'.
        { clear. unfold fix_subst, fix_env; simple.
          match goal with
          | |- map _ (?f1 _) = ?f2 _ => 
              set (aux1 := f1);
              set (aux2 := f2)
          end.
          generalize #|mfix| as n.
          induction n; simple; try easy.
          now f_equal. }
        rewrite -heq'.
      
        rewrite !fold_csubst_csubst_commute; simple; try easy; try solve[
          try intros x [? | ?]%in_app_iff; intros; eapply wellformed_closed, wellformed_val_wellformed; simple; easy
        ].
        f_equal.
        rewrite map_app -fold_left_csubst_app; simple; try solve[
          try intros x [? | ?]%in_app_iff; intros; eapply wellformed_closed, wellformed_val_wellformed; simple; easy
        ].
        now rewrite Nat.add_1_r.
  - apply eval_mkApps_CoFix; try easy.
    rewrite wellformed_mkApps // in wf_e.
    simple.
    destruct wf_e as [? wf_args].
    induction a in wf_args, IHa |- *; simple; try easy.
    destruct IHa.
    constructor.
    + apply e; now simple.
    + now apply IHa0.
  - rewrite /substl /= in IHheval. econstructor; try easy.
    apply IHheval; try easy.
    pose proof lookup_env_wellformed wf_Σ isdecl.
    simple.
  - rewrite wellformed_mkApps in wf_e; simple; rewrite /lookup_constructor_pars_args e /= in wf_e.
    assert (cstr_as_blocks = false) as heq. 
    { now rewrite H -(negb_involutive with_constructor_as_block) c_as_bks. }
    rewrite ->heq in *.
    eapply eval_mkApps_Construct; simple; try easy.
    { apply eval_atom; now simple. }
    destruct wf_e as [_ wf_e]. induction a; simple; try easy.
    destruct IHa.
    constructor.
    + now apply e0; simple.
    + now apply IHa0.
  - rewrite /lookup_constructor_pars_args e /= in wf_e.
    rewrite ->H, c_as_bks in *.
    econstructor; simple; try easy.
    { simple. symmetry. now apply eqb_eq. }
    destruct wf_e as [_ [_ wf_e]]. induction a; simple; try easy.
    destruct IHa.
    constructor.
    + now apply e0; simple.
    + now apply IHa0.
  - constructor.
    inversion evih; subst; unfold map_prim, test_prim, test_array_model in *; simple; repeat split; try easy; constructor; last first.
    { now apply H4; simple. }
    destruct wf_e as [? wf_e].
    clear H0 H4 H5 H6 H7. 
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
