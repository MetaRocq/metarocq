(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICTyping PCUICWeakeningConv PCUICWeakeningTyp PCUICCases
     PCUICCumulativity PCUICReduction
     PCUICParallelReduction PCUICEquality PCUICUnivSubstitutionConv
     PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextReduction PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICGuardCondition PCUICClosedTyp.

From Stdlib Require Import CRelationClasses ssreflect ssrbool.
From Equations Require Import Equations.

Arguments red_ctx : clear implicits.

Ltac my_rename_hyp h th :=
  match th with
    | (typing _ _ ?t _) => fresh "type" t
    | (All_local_env (@typing _) _ ?G) => fresh "wf" G
    | (All_local_env (@typing _) _ _) => fresh "wf"
    | (All_local_env _ _ ?G) => fresh "H" G
    | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

#[global]
Hint Resolve conv_refl' : pcuic.
Arguments skipn : simpl never.

Definition closed_red_ctx Σ Γ Γ' :=
  All2_fold (fun Γ _ => All_decls (closed_red Σ Γ)) Γ Γ'.

Notation "Σ ⊢ Γ ⇝ Δ" := (closed_red_ctx Σ Γ Δ) (at level 50, Γ, Δ at next level,
  format "Σ  ⊢  Γ  ⇝  Δ") : pcuic.

Lemma closed_red_ctx_red_ctx {Σ Γ Γ'} :
  Σ ⊢ Γ ⇝ Γ' -> red_ctx Σ Γ Γ'.
Proof.
  intros a; eapply All2_fold_impl; tea.
  cbn; intros ?????.
  eapply All_decls_impl; tea => t t'.
  now move=> [].
Qed.
Coercion closed_red_ctx_red_ctx : closed_red_ctx >-> red_ctx.

#[global]
Hint Constructors red1 : pcuic.
#[global]
Hint Resolve refl_red : pcuic.

Section ContextReduction.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Local Definition red1_red_ctxP Γ Γ' :=
    (forall n b b',
        option_map decl_body (nth_error Γ n) = Some (Some b) ->
        option_map decl_body (nth_error Γ' n) = Some (Some b') ->
        @red_ctx Σ (skipn (S n) Γ) (skipn (S n) Γ') ->
        ∑ t, red Σ (skipn (S n) Γ') b t * red Σ (skipn (S n) Γ') b' t).

  Lemma red_ctx_skip i Γ Γ' :
    red1_red_ctxP Γ Γ' ->
    red1_red_ctxP (skipn i Γ) (skipn i Γ').
  Proof using Type.
    rewrite /red1_red_ctxP => H n b b'.
    rewrite !nth_error_skipn => H0 H1.
    specialize (H (i + n)).
    rewrite !skipn_skipn. rewrite - !Nat.add_succ_comm.
    move=> H'.
    eapply H; auto.
  Qed.

  Lemma All2_fold_over_red_refl {Γ Δ} :
    All2_fold (on_decls (fun (Δ _ : context) (t u : term) => red Σ (Γ ,,, Δ) t u)) Δ Δ.
  Proof using Type. induction Δ as [|[na [b|] ty]]; econstructor; try red; auto.
    constructor; reflexivity. constructor; reflexivity.
  Qed.

  Lemma All2_fold_red_refl {Δ} :
    All2_fold (on_decls (fun (Δ _ : context) (t u : term) => red Σ Δ t u)) Δ Δ.
  Proof using Type.
    induction Δ as [|[na [b|] ty]]; econstructor; try red; auto;
    constructor; reflexivity.
  Qed.

  Derive Signature for assumption_context.

  Lemma red1_red_ctxP_app {Γ Γ' Δ} :
    red1_red_ctxP Γ Γ' ->
    red1_red_ctxP (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof using Type.
    induction Δ as [|[na [b|] ty] Δ]; intros; auto.
    - case.
      * move=> bod bod' => /= [=] -> [=] ->. rewrite !skipn_S !skipn_0. exists bod'.
        split; reflexivity.
      * move=> /= n bod b' hn hn' r.
        specialize (IHΔ X n bod b' hn hn' r) as [t [redl redr]].
        exists t. rewrite !skipn_S in r |- *. split; auto.
    - case; move => n b b' //. eapply IHΔ. apply X.
  Qed.

  Ltac t := split; [eapply red1_red; try econstructor; eauto|try constructor]; eauto with pcuic.
  Ltac u := intuition eauto with pcuic.

  Lemma red_ctx_app Γ Γ' Δ :
    red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof using Type.
    intros h; eapply All2_fold_app => //.
    eapply All2_fold_refl. intros Δ' ?. reflexivity.
  Qed.
  Hint Resolve red_ctx_app : pcuic.

  Lemma red_ctx_on_free_vars P Γ Γ' :
    red_ctx Σ Γ Γ' ->
    on_free_vars_ctx P Γ ->
    on_free_vars_ctx P Γ'.
  Proof using wfΣ.
    move=> /red_ctx_red_context r onΓ.
    pose proof (All2_fold_length r).
    move: r => /red_context_on_ctx_free_vars.
    move: onΓ. now rewrite - !on_free_vars_ctx_on_ctx_free_vars -H.
  Qed.

  Lemma red1_red_ctx_aux {Γ Γ' T U} :
    red1 Σ Γ T U ->
    on_free_vars xpredT T ->
    on_free_vars_ctx xpredT Γ ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof using wfΣ.
    intros r onT onΓ H. revert onT onΓ Γ' H.
    simpl in *. induction r using red1_ind_all; intros; auto with pcuic;
    repeat inv_on_free_vars_xpredT.
    all:try solve [eexists; t].
    all:try specialize (IHr ltac:(tea) ltac:(eauto with fvs)).
    all:try destruct (IHr _ ltac:(tea) ltac:(tea)) as [? [? ?]]; auto.

    - pose proof H.
      eapply nth_error_pred1_ctx_l in H as [body' [? ?]]; eauto.
      rewrite -(firstn_skipn (S i) Γ').
      assert (i < #|Γ'|). destruct (nth_error Γ' i) eqn:Heq; noconf e. eapply nth_error_Some_length in Heq. lia.
      move: (All2_fold_length H0) => Hlen.
      specialize (X _ _ _ H1 e). forward X. eapply All2_fold_app_inv.
      instantiate (1 := firstn (S i) Γ').
      instantiate (1 := firstn (S i) Γ).
      rewrite !length_firstn. lia.
      now rewrite !(firstn_skipn (S i) _).
      destruct X as [x' [bt b't]]. exists (lift0 (S i) x').
      split; eauto with pcuic.
      * etransitivity. eapply red1_red. constructor.
        rewrite firstn_skipn. eauto. cbn in *.
        eapply red_ctx_on_free_vars in onΓ. 2:tea.
        eapply weakening_red_0; eauto.
        rewrite firstn_length_le //.
        erewrite on_free_vars_ctx_on_ctx_free_vars.
        rewrite -(firstn_skipn (S i) Γ') on_free_vars_ctx_app in onΓ.
        now move/andP: onΓ => [].
        destruct (nth_error Γ' i) eqn:hnth => //.
        epose proof (nth_error_on_free_vars_ctx xpredT 0 Γ' i c).
        forward H2. rewrite addnP0. eauto with fvs.
        forward H2 by auto.
        specialize (H2 hnth). noconf e.
        move/andP: H3 => [] /=. rewrite H /=.
        rewrite PCUICInstConv.addnP_xpredT shiftnP_xpredT //.
      * epose proof (red_ctx_on_free_vars _ _ _ H0 onΓ).
        eapply weakening_red_0; eauto.
        rewrite firstn_length_le //.
        erewrite on_free_vars_ctx_on_ctx_free_vars.
        rewrite -(firstn_skipn (S i) Γ') on_free_vars_ctx_app in H2.
        now move/andP: H2 => [].
        destruct (nth_error Γ i) eqn:hnth => //.
        epose proof (nth_error_on_free_vars_ctx xpredT 0 Γ i c).
        forward H3. rewrite addnP0. eauto with fvs.
        forward H3 by auto.
        specialize (H3 hnth). noconf H1.
        move/andP: H3 => [] /=. rewrite H /=.
        eauto with fvs.

    - exists (tLambda na x N). split; apply red_abs; auto.

    - destruct (IHr (Γ' ,, vass na N)). constructor; pcuic. constructor; pcuic.
      case => ? ? /= //. apply X.
      exists (tLambda na N x). split; apply red_abs; u.

    - exists (tLetIn na x t b'). split; eapply red_letin; auto.
    - specialize (IHr (Γ' ,, vdef na b t)).
      forward IHr. constructor; eauto. constructor; auto.
      destruct IHr as [? [? ?]].
      case. move=> b0 b1 [] <- [] <- H'. exists b; auto.
      apply X.
      exists (tLetIn na b t x). split; eapply red_letin; auto.
    - solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (red Σ Γ')) in X as [pars' [ol or]].
      exists (tCase ci (set_pparams p pars') c brs). u.
      apply red_case_pars. eapply OnOne2_All2; tea => /= //.
      change (set_pparams p pars') with (set_pparams (set_pparams p params') pars').
      apply red_case_pars => /=. eapply OnOne2_All2; tea => /= //.
      intros; u.
    - destruct (IHr (Γ' ,,, inst_case_predicate_context p)).
      now eapply red_ctx_app => //.
      now eapply red1_red_ctxP_app.
      destruct p5.
      eexists. split. eapply red_case_p; tea.
      change (set_preturn p x) with (set_preturn (set_preturn p preturn') x).
      eapply red_case_p; tea.
    - exists (tCase ind p x brs). u; now apply red_case_c.
    - solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _
        (fun br br' => on_Trel_eq (red Σ (Γ' ,,, inst_case_branch_context p br)) bbody bcontext br br')) in X.
        destruct X as [brs'' [? ?]].
        eexists. split; eapply red_case_one_brs; eauto;
        solve_all.
        intros. intuition eauto.
        inv_on_free_vars_xpredT.
        specialize (b1 ltac:(eauto with fvs)).
        forward b1. eapply on_free_vars_ctx_inst_case_context_xpredT; eauto with fvs. solve_all.
        now rewrite test_context_k_closed_on_free_vars_ctx in a0.
        specialize (b1 (Γ' ,,, inst_case_branch_context p y)) as [body' [rl rr]].
        + rewrite /inst_case_branch_context -b0. now eapply red_ctx_app => //.
        + rewrite /inst_case_branch_context -b0. now eapply red1_red_ctxP_app.
        + exists {| bcontext := bcontext x; bbody := body' |}; cbn; split; rewrite -?b;
          intuition eauto.
          rewrite /inst_case_branch_context b0 //.
    - exists (tProj p x). u; now eapply red_proj_c.
    - exists (tApp x M2). u; now eapply red_app.
    - exists (tApp M1 x). u; now eapply red_app.
    - exists (tProd na x M2). u; now eapply red_prod.
    - specialize (IHr (Γ' ,, vass na M1)) as [? [? ?]].
      constructor; pcuic. constructor; auto. case => //.
      exists (tProd na M1 x). u; now eapply red_prod.
    - eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (red Σ Γ')) in X.
      destruct X as [rl [l0 l1]].
      eexists; split; eapply red_evar; eauto.
      eapply OnOne2_All2; eauto.
      eapply OnOne2_All2; eauto.
      simpl; intros.
      intuition eauto.
    - eapply OnOne2_All_mix_left in X; tea.
       eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto. inv_on_free_vars_xpredT.
      specialize (b1 H0 onΓ).
      destruct (b1 _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros.
      intuition auto. inv_on_free_vars_xpredT.
      specialize (b1 ltac:(eauto with fvs) ltac:(eauto with fvs) (Γ' ,,, fix_context mfix0)). forward b1.
      eapply All2_fold_app => //. apply All2_fold_over_red_refl.
      forward b1. now eapply red1_red_ctxP_app.
      destruct b1 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
    - eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto. inv_on_free_vars_xpredT.
      destruct (b1 byfvs byfvs _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros. intuition auto. inv_on_free_vars_xpredT.
      specialize (b1 byfvs byfvs (Γ' ,,, fix_context mfix0)). forward b1.
      eapply All2_fold_app => //. apply All2_fold_over_red_refl.
      forward b1. eapply red1_red_ctxP_app => //.
      destruct b1 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
    - eapply forallb_All in a. eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (red Σ Γ')) in X. destruct X as [values' []].
      eexists; split.
      eapply red_primArray_value, OnOne2_All2; tea; intuition eauto.
      change (set_array_value arr values') with (set_array_value (set_array_value arr value) values').
      eapply red_primArray_value, OnOne2_All2; tea; intuition eauto.
      intros; intuition eauto.
    - eexists; split.
      + eapply red_primArray_default; tea.
      + now eapply (red_primArray_default (set_array_default arr def) x).
    - eexists; split.
      + eapply red_primArray_type; tea.
      + now eapply (red_primArray_type (set_array_type arr ty) x).
  Qed.

  Hint Resolve red_ctx_on_free_vars : fvs.

  Lemma red_red_ctx' {Γ : closed_context} Γ' {T : open_term Γ} {U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof using wfΣ.
    intros r rc rP. destruct T as [T hT]; cbn in *; induction r.
    - eapply red1_red_ctx_aux; eauto with fvs.
    - exists x; split; auto.
    - destruct IHr1 as [xl [redl redr]]; eauto with fvs.
      destruct IHr2 as [xr [redl' redr']]; eauto with fvs.
      assert (on_free_vars_ctx xpred0 Γ'). eapply red_ctx_on_free_vars; tea. eauto with fvs.
      pose proof (All2_fold_length rc).
      unshelve epose proof (red_confluence (Γ := exist Γ' _) (t := exist y _) redr redl'); cbn; eauto with fvs.
      rewrite -H0; eauto with fvs.
      destruct X as [v' [redxl redxr]].
      exists v'. split; [transitivity xl|transitivity xr]; auto.
  Qed.

  Lemma red_red_ctx_aux' {Γ : closed_context} {Γ'} :
    @red_ctx Σ Γ Γ' -> red1_red_ctxP Γ Γ'.
  Proof using wfΣ.
    destruct Γ as [Γ onΓ].
    intros X. cbn in *.
    induction Γ in Γ', X, onΓ |- *.
    - depelim X.
      intros n t t'. rewrite nth_error_nil //.
    - depelim X.
      move: onΓ; rewrite on_free_vars_ctx_snoc => /andP /= [onΓ ond].
      depelim a0.
      + specialize (IHΓ byfvs _ X).
        case => n b b' /= //.
        simpl. apply IHΓ.
      + specialize (IHΓ byfvs _ X).
        case.
        * move=> b0 b1 [] <- [] <- H.
          rewrite skipn_S /skipn /= in H.
          move/andP: ond => /= [] onb ont.
          eapply (@red_red_ctx' (exist Γ onΓ) _ (exist b onb)) in H; eauto.
        * simpl. eapply IHΓ.
  Qed.

  Lemma red_red_ctx {Γ : closed_context} {Γ'} {T : open_term Γ} {U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof using wfΣ.
    intros. eapply red_red_ctx', red_red_ctx_aux'; eauto.
  Qed.

End ContextReduction.

Definition inj_closed (Γ : context) (o : on_free_vars_ctx xpred0 Γ) : closed_context :=
  exist Γ o.
Arguments inj_closed Γ & o.

Definition inj_open {Γ : closed_context} (t : term) (o : on_free_vars (shiftnP #|Γ| xpred0) t) : open_term Γ :=
  exist t o.
Arguments inj_open {Γ} & t o.

#[global] Hint Resolve red_ctx_on_free_vars : fvs.

Lemma red_ctx_on_free_vars_term {Σ P Γ Γ' t} :
  red_ctx Σ Γ Γ' ->
  on_free_vars (shiftnP #|Γ| P) t ->
  on_free_vars (shiftnP #|Γ'| P) t.
Proof.
  intros r. now rewrite (All2_fold_length r).
Qed.
#[global] Hint Resolve red_ctx_on_free_vars_term : fvs.

#[global]
Instance closed_red_trans Σ Γ : Transitive (closed_red Σ Γ).
Proof.
  intros x y z.
  induction 1. destruct 1. split; eauto with fvs.
  now transitivity y.
Qed.

Definition compare_context {cf} Σ pb :=
  PCUICEquality.compare_context Σ Σ pb.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Abbreviation conv_context := (All2_fold (conv_decls Σ)).
  Abbreviation cumul_context := (All2_fold (cumul_decls Σ)).

  Hint Resolve conv_ctx_refl' cumul_ctx_refl' : pcuic.

  Lemma fill_pb {Γ : closed_context} {pb} {t u : open_term Γ} {t' u'} :
    compare_term Σ.1 Σ pb t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * compare_term Σ Σ pb t'' u''.
  Proof using wfΣ.
    intros tu tt' uu'.
    eapply red_eq_term_upto_univ_l in tu; try exact tt'. all:try tc.
    destruct tu as [u'' [uu'' t'u'']].
    destruct (red_confluence uu' uu'') as [unf [ul ur]].
    eapply red_eq_term_upto_univ_r in t'u''; try exact ur; try tc.
    destruct t'u'' as [t'' [t't'' t''unf]].
    exists t'', unf. intuition auto.
  Qed.

  Lemma fill_le {Γ : closed_context} {t u : open_term Γ} {t' u'} :
    leq_term Σ.1 Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * leq_term Σ Σ t'' u''.
  Proof using wfΣ.
    apply fill_pb.
  Qed.

  Lemma fill_eq {Γ : closed_context} {t u : open_term Γ} {t' u'} :
    eq_term Σ.1 Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * eq_term Σ.1 Σ t'' u''.
  Proof using wfΣ.
    apply fill_pb.
  Qed.

  Lemma red_ctx_ws_cumul_ctx_pb {l Γ Γ'} : Σ ⊢ Γ ⇝ Γ' -> Σ ⊢ Γ ≤[l] Γ'.
  Proof using wfΣ.
    induction 1; constructor; auto.
    depelim p; constructor; eauto with fvs; pcuic.
  Qed.

  Lemma red_ctx_closed_left {Γ Γ'} : Σ ⊢ Γ ⇝ Γ' -> is_closed_context Γ.
  Proof using Type.
    induction 1; simpl; auto.
    rewrite on_free_vars_ctx_snoc IHX /=.
    destruct p; eauto with fvs.
  Qed.

  Lemma red_ctx_closed_right {Γ Γ'} : Σ ⊢ Γ ⇝ Γ' -> is_closed_context Γ'.
  Proof using wfΣ.
    induction 1; simpl; auto.
    rewrite on_free_vars_ctx_snoc IHX /=.
    destruct p; rewrite -(All2_fold_length X); cbn; eauto with fvs.
    eapply closed_red_open_right in c.
    eapply closed_red_open_right in c0.
    eauto with fvs.
  Qed.
  Hint Resolve red_ctx_closed_left red_ctx_closed_right : fvs.

  Lemma red_compare_term_l {pb Γ} {u v u' : term} :
    compare_term Σ Σ pb u u' ->
    red Σ Γ u v ->
    ∑ v' : term, red Σ Γ u' v' × compare_term Σ Σ pb v v'.
  Proof using Type.
    destruct pb; cbn;
    apply red_eq_term_upto_univ_l; tc.
  Qed.

  Lemma red_compare_term_r {pb Γ} {u v u' : term} :
    compare_term Σ Σ pb u u' ->
    red Σ Γ u' v ->
    ∑ v' : term, red Σ Γ u v' × compare_term Σ Σ pb v' v.
  Proof using Type.
    destruct pb; cbn;
    apply red_eq_term_upto_univ_r; tc.
  Qed.

  Lemma closed_red_compare_term_l {pb Γ} {u v u' : term} :
    is_open_term Γ u' ->
    compare_term Σ Σ pb u u' ->
    Σ ;;; Γ ⊢ u ⇝ v ->
    ∑ v' : term, Σ ;;; Γ ⊢ u' ⇝ v' × compare_term Σ Σ pb v v'.
  Proof using Type.
    intros isop comp [clΓ clu red].
    destruct (red_compare_term_l comp red) as [nf [r eq]].
    exists nf; repeat (split; eauto with fvs).
  Qed.

  Lemma closed_red_compare_term_r {pb Γ} {u v u' : term} :
    is_open_term Γ u ->
    compare_term Σ Σ pb u u' ->
    Σ ;;; Γ ⊢ u' ⇝ v ->
    ∑ v' : term, Σ ;;; Γ ⊢ u ⇝ v' × compare_term Σ Σ pb v' v.
  Proof using Type.
    intros isop comp [clΓ clu red].
    destruct (red_compare_term_r comp red) as [nf [r eq]].
    exists nf; repeat (split; eauto with fvs).
  Qed.

  Lemma closed_red_red_ctx {Γ Γ'} {T U} :
    Σ ⊢ Γ ⇝ Γ' ->
    Σ ;;; Γ ⊢ T ⇝ U ->
    ∑ t, Σ ;;; Γ' ⊢ T ⇝ t × Σ ;;; Γ' ⊢ U ⇝ t.
  Proof using wfΣ.
    intros rctx [clΓ clT r].
    assert (is_open_term Γ U) by eauto with fvs.
    eapply (red_red_ctx Σ wfΣ (Γ := exist Γ clΓ) (T := exist T clT)) in r as [t [r r']].
    2:exact rctx.
    exists t. split. split; auto. eauto with fvs.
    rewrite -(length_of rctx); eauto with fvs.
    split; eauto with fvs.
    rewrite -(length_of rctx); eauto with fvs.
  Qed.

  Lemma ws_cumul_pb_red {pb} {Γ t u} :
    Σ ;;; Γ ⊢ t ≤[pb] u <~>
    ∑ v v', [× Σ ;;; Γ ⊢ t ⇝ v, Σ ;;; Γ ⊢ u ⇝ v' &
      compare_term Σ (global_ext_constraints Σ) pb v v'].
  Proof using wfΣ.
    split.
    - move/ws_cumul_pb_alt; intros (v & v' & [clΓ clt clu red red' leq]).
      exists v, v'; repeat split; eauto with fvs.
    - intros (v & v' & [red red' leq]).
      apply ws_cumul_pb_alt; exists v, v'.
      repeat split; eauto with fvs.
  Qed.

  Lemma closed_red_confluence {Γ} {t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ⇝ v ->
    ∑ v', Σ ;;; Γ ⊢ u ⇝ v' × Σ ;;; Γ ⊢ v ⇝ v'.
  Proof using wfΣ.
    intros [clΓ clT r] [clΓ' clT' r'].
    destruct (red_confluence (Γ := exist Γ clΓ) (t := exist t clT) r r') as [v' [redl redr]].
    cbn in *. exists v'; repeat split; eauto with fvs.
  Qed.

  Lemma ws_cumul_pb_red_ctx {pb} {Γ Γ'} {T U} :
    Σ ⊢ Γ ⇝ Γ' ->
    Σ ;;; Γ ⊢ T ≤[pb] U ->
    Σ ;;; Γ' ⊢ T ≤[pb] U.
  Proof using wfΣ.
    intros Hctx H.
    apply ws_cumul_pb_red in H as (v & v' & [redl redr leq]).
    destruct (closed_red_red_ctx Hctx redl) as [lnf [redl0 redr0]].
    eapply ws_cumul_pb_red.
    eapply closed_red_compare_term_l in leq as [? [? ?]]. 3:exact redr0.
    2:{ rewrite -(length_of Hctx). now eapply closed_red_open_right. }
    destruct (closed_red_red_ctx Hctx redr) as [rnf [redl1 redr1]].
    destruct (closed_red_confluence c redr1) as [nf [redl' redr']].
    unshelve epose proof (closed_red_compare_term_r _ c0 redl') as [lnf' [? ?]]. exact byfvs.
    exists lnf', nf. split; eauto with fvs.
    - now transitivity lnf.
    - now transitivity rnf.
  Qed.

  Lemma red_red_ctx_inv {Γ Δ : closed_context} {t : open_term Γ} {u} :
    red Σ Γ t u -> red_ctx Σ Δ Γ -> red Σ Δ t u.
  Proof using wfΣ.
    intros r rc.
    eapply red_ctx_red_context in rc.
    eapply PCUICContextReduction.red_red_ctx; tea; eauto with fvs.
  Qed.

  Lemma red_red_ctx_inv' {Γ Δ : context} {t u} :
    Σ ⊢ Δ ⇝ Γ ->
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Δ ⊢ t ⇝ u.
  Proof using wfΣ.
    intros rc [onΓ ont r].
    move: (red_ctx_closed_left rc) => onΔ.
    eapply closed_red_ctx_red_ctx in rc.
    eapply red_ctx_red_context in rc.
    eapply PCUICContextReduction.red_red_ctx in r.
    econstructor; tea. all:eauto with fvs.
    all:try now rewrite (All2_fold_length rc).
    all:eauto with fvs.
    rewrite -(All2_fold_length rc); eauto with fvs.
  Qed.

  Lemma cumul_red_ctx_inv {pb} {Γ Γ' : context} {T U : term} :
    Σ ;;; Γ ⊢ T ≤[pb] U ->
    Σ ⊢ Γ' ⇝ Γ ->
    Σ ;;; Γ' ⊢ T ≤[pb] U.
  Proof using wfΣ.
    intros H Hctx.
    apply ws_cumul_pb_red in H as (v & v' & [redl redr leq]).
    epose proof (red_red_ctx_inv' Hctx redl).
    epose proof (red_red_ctx_inv' Hctx redr).
    apply ws_cumul_pb_red.
    now exists v, v'.
  Qed.

  Lemma closed_red_eq_context_upto_l {pb Γ Δ} {u} {v} :
    is_closed_context Δ ->
    Σ ;;; Γ ⊢ u ⇝ v ->
    compare_context Σ pb Γ Δ ->
    ∑ v', Σ ;;; Δ ⊢ u ⇝ v' × eq_term Σ Σ v v'.
  Proof using Type.
    intros clΔ [onΓ onu r] c.
    destruct (red_eq_context_upto_l _ c r) as [nf [red eq]].
    exists nf. split; auto. split; eauto with fvs.
    now rewrite -(All2_fold_length c).
  Qed.

  Lemma closed_red_eq_context_upto_r {pb Γ Δ} {u} {v} :
    is_closed_context Γ ->
    Σ ;;; Δ ⊢ u ⇝ v ->
    compare_context Σ pb Γ Δ ->
    ∑ v', Σ ;;; Γ ⊢ u ⇝ v' × eq_term Σ Σ v v'.
  Proof using Type.
    intros clΔ [onΓ onu r] c.
    destruct (red_eq_context_upto_r _ c r) as [nf [red eq]].
    symmetry in eq.
    exists nf. split; auto. split; eauto with fvs.
    now rewrite (All2_fold_length c).
  Qed.

  Lemma cumul_trans_red_leqterm {Γ : closed_context} {t u v : open_term Γ} :
    Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
    ∑ l o r, red Σ Γ t l ×
             red Σ Γ u o ×
             red Σ Γ v r ×
             leq_term Σ.1 Σ l o × leq_term Σ.1 Σ o r.
  Proof using wfΣ.
    intros X X0.
    intros.
    eapply cumul_alt in X as [t0 [u0 (redl & redr & eq)]].
    eapply cumul_alt in X0 as [u1 [v0 (redl' & redr' & eq')]].
    destruct (red_confluence redr redl') as [unf [nfl nfr]].
    eapply red_eq_term_upto_univ_r in eq; try tc. 2:tea.
    destruct eq as [t1 [red'0 eq2]].
    eapply red_eq_term_upto_univ_l in eq'; try tc; tea.
    destruct eq' as [v1 [red'1 eq1]].
    exists t1, unf, v1.
    repeat split.
    transitivity t0; auto.
    transitivity u0; auto.
    transitivity v0; auto. eapply eq2. eapply eq1.
  Qed.

  Lemma cumul_pb_compare_context {pb pb' Γ Δ T U} :
    compare_context Σ pb Γ Δ ->
    Σ ;;; Δ |- T <=[pb'] U ->
    Σ ;;; Γ |- T <=[pb'] U.
  Proof using Type.
    intros eqctx cum.
    eapply cumul_alt in cum as (nf & nf' & redl & redr & ?).
    eapply red_eq_context_upto_r in redl; tea; tc.
    eapply red_eq_context_upto_r in redr; tea; tc.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply cumul_alt. exists v', v''; repeat split; auto.
    transitivity nf.
    eapply eq_term_upto_univ_leq; tc; auto.
    transitivity nf' => //.
    eapply eq_term_upto_univ_leq; tc; auto.
    now symmetry.
  Qed.

  (* Conversion is untyped so this currently holds as compare_context
    just allows cumulativity on types, which do not participate in reduction.
    However the useful lemma is the one above that shows we can lift a
    conversion from a large context to a smaller one (contravariance).
    *)
  Local Remark cumul_pb_compare_context_inv {pb pb' Γ Δ T U} :
    compare_context Σ pb Γ Δ ->
    Σ ;;; Γ |- T <=[pb'] U ->
    Σ ;;; Δ |- T <=[pb'] U.
  Proof using Type.
    intros eqctx cum.
    eapply cumul_alt in cum as (nf & nf' & redl & redr & ?).
    eapply red_eq_context_upto_l in redl; tea; tc.
    eapply red_eq_context_upto_l in redr; tea; tc.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply cumul_alt. exists v', v''; repeat split; auto.
    transitivity nf.
    eapply eq_term_upto_univ_leq; tc; auto.
    now symmetry.
    transitivity nf' => //.
    eapply eq_term_upto_univ_leq; tc; auto.
  Qed.

  Lemma conv_eq_context_upto {Γ} {Δ} {T U} :
    eq_context Σ Σ Γ Δ ->
    Σ ;;; Γ |- T = U ->
    Σ ;;; Δ |- T = U.
  Proof using Type.
    intro eqctx. symmetry in eqctx.
    now eapply cumul_pb_compare_context.
  Qed.

  Lemma conv_leq_context_upto {Γ Δ T U} :
    leq_context Σ Σ Γ Δ ->
    Σ ;;; Δ |- T = U ->
    Σ ;;; Γ |- T = U.
  Proof using Type.
    apply cumul_pb_compare_context.
  Qed.

  (* Conversion is untyped so this currently holds as context ws_cumul_pb
     just allows cumulativity on types, which do not participate in reduction.
     However the useful lemma is the one above that shows we can lift a
     conversion from a large context to a smaller one (contravariance).
     *)
  Local Remark conv_leq_context_upto_inv {Γ Δ T U} :
    leq_context Σ Σ Γ Δ ->
    Σ ;;; Γ |- T = U ->
    Σ ;;; Δ |- T = U.
  Proof using Type.
    apply cumul_pb_compare_context_inv.
  Qed.

  Lemma cumul_leq_context_upto {Γ Δ T U} :
    leq_context Σ Σ Δ Γ ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Δ |- T <= U.
  Proof using Type.
    apply cumul_pb_compare_context.
  Qed.

  Lemma ws_cumul_pb_compare_context {pb pb' Γ Δ T U} :
    compare_context Σ pb Δ Γ ->
    is_closed_context Δ ->
    Σ ;;; Γ ⊢ T ≤[pb'] U ->
    Σ ;;; Δ ⊢ T ≤[pb'] U.
  Proof using wfΣ.
    intros eqctx cl cum.
    eapply ws_cumul_pb_red in cum as [nf [nf' [redl redr ?]]].
    eapply closed_red_eq_context_upto_r in redl; tea; eauto with fvs.
    eapply closed_red_eq_context_upto_r in redr; tea; eauto with fvs.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply ws_cumul_pb_red. exists v', v''; split; auto.
    destruct pb'; cbn in *; transitivity nf.
    now symmetry.
    transitivity nf' => //.
    now apply eq_term_leq_term.
    transitivity nf'; auto.
    now apply eq_term_leq_term.
  Qed.

  Local Remark ws_cumul_pb_compare_context_inv {pb pb' Γ Δ T U} :
    compare_context Σ pb Γ Δ ->
    is_closed_context Δ ->
    Σ ;;; Γ ⊢ T ≤[pb'] U ->
    Σ ;;; Δ ⊢ T ≤[pb'] U.
  Proof using wfΣ.
    intros eqctx cl cum.
    eapply ws_cumul_pb_red in cum as [nf [nf' [redl redr ?]]].
    eapply closed_red_eq_context_upto_l in redl; tea; eauto with fvs.
    eapply closed_red_eq_context_upto_l in redr; tea; eauto with fvs.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply ws_cumul_pb_red. exists v', v''; split; auto.
    destruct pb'; cbn in *; transitivity nf.
    - now symmetry.
    - transitivity nf'; auto.
    - apply eq_term_leq_term. now symmetry.
    - transitivity nf' => //.
      now apply eq_term_leq_term.
  Qed.

  Lemma eq_leq_context_upto Γ Δ :
    eq_context Σ Σ Γ Δ ->
    leq_context Σ Σ Γ Δ.
  Proof using Type. apply eq_context_upto_impl. all: tc. Qed.

  Lemma cumul_eq_context_upto {Γ Δ T U} :
    eq_context Σ Σ Γ Δ ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Δ |- T <= U.
  Proof using Type.
    intro H. symmetry in H. revert H.
    apply cumul_pb_compare_context.
  Qed.

  Lemma ws_cumul_pb_eq_context_upto {pb Γ Δ T U} :
    eq_context Σ Σ Γ Δ ->
    is_closed_context Δ ->
    Σ ;;; Γ ⊢ T ≤[pb] U ->
    Σ ;;; Δ ⊢ T ≤[pb] U.
  Proof using wfΣ.
    intros eqctx cl. symmetry in eqctx.
    now eapply ws_cumul_pb_compare_context.
  Qed.

  Lemma cumul_pb_alt_red_ctx {Γ : closed_context} {Γ' pb} {T U : open_term Γ} :
    Σ ;;; Γ |- T <=[pb] U ->
    red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T <=[pb] U.
  Proof using wfΣ.
    intros H Hctx.
    eapply cumul_alt in H. apply cumul_alt.
    destruct H as (T' & U' & redv & redv' & leqvv').
    destruct (red_red_ctx _ _ redv Hctx) as [Tj [redTj redT'j]].
    destruct (red_red_ctx _ _ redv' Hctx) as [Uj [redUUj redU'j]].
    destruct (fill_pb (Γ := inj_closed Γ' byfvs) (t := inj_open T' byfvs) (u := inj_open U' byfvs) leqvv' redT'j redU'j) as [Tnf [Unf [[redTnf redUnf] eqnf]]].
    exists Tnf, Unf; intuition eauto.
    now transitivity Tj.
    now transitivity Uj.
  Qed.

  Lemma cumul_pb_alt_red_ctx_inv {Γ Γ' : closed_context} {pb} {T U : open_term Γ} :
    Σ ;;; Γ |- T <=[pb] U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T <=[pb] U.
  Proof using wfΣ.
    intros H Hctx.
    apply cumul_alt in H as (v & v' & redl & redr & leq).
    pose proof (red_red_ctx_inv redl Hctx).
    pose proof (red_red_ctx_inv redr Hctx).
    apply cumul_alt.
    exists v, v'.
    split. pcuic. auto.
  Qed.

  Lemma conv_alt_red_ctx {Γ : closed_context} {Γ'} {T U : open_term Γ} :
    Σ ;;; Γ |- T = U ->
    red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof using wfΣ.
    apply cumul_pb_alt_red_ctx.
  Qed.

  Lemma conv_alt_red_ctx_inv {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T = U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T = U.
  Proof using wfΣ.
    apply cumul_pb_alt_red_ctx_inv.
  Qed.

  Lemma cumul_alt_red_ctx {Γ : closed_context} {Γ'} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof using wfΣ.
    apply cumul_pb_alt_red_ctx.
  Qed.

  Lemma cumul_alt_red_ctx_inv {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof using wfΣ.
    apply cumul_pb_alt_red_ctx_inv.
  Qed.

  Lemma ws_cumul_pb_red_ctx_inv {pb Γ Γ'} {T U} :
    Σ ⊢ Γ' ⇝ Γ ->
    Σ ;;; Γ ⊢ T ≤[pb] U ->
    Σ ;;; Γ' ⊢ T ≤[pb] U.
  Proof using wfΣ.
    intros Hctx H.
    apply ws_cumul_pb_red in H as [v [v' [redl redr leq]]].
    epose proof (red_red_ctx_inv' Hctx redl).
    epose proof (red_red_ctx_inv' Hctx redr).
    apply ws_cumul_pb_red.
    now exists v, v'.
  Qed.

  Lemma closed_red_refl Γ t :
    is_closed_context Γ ->
    is_open_term Γ t ->
    Σ ;;; Γ ⊢ t ⇝ t.
  Proof using Type.
    now constructor.
  Qed.

  Lemma red_decl_refl Γ d :
    is_closed_context Γ ->
    ws_decl Γ d ->
    All_decls (closed_red Σ Γ) d d.
  Proof using Type.
    destruct d as [na [b|] ty] => [onΓ /andP[] /=|]; constructor.
    all:split; eauto with fvs.
  Qed.

  Lemma closed_red_ctx_refl Γ : is_closed_context Γ -> Σ ⊢ Γ ⇝ Γ.
  Proof using Type.
    move/on_free_vars_ctx_All_fold => a.
    apply: All_fold_All2_fold_impl; tea; clear => Γ d H IH; cbn.
    apply red_decl_refl.
    now apply on_free_vars_ctx_All_fold.
  Qed.

  Lemma ws_cumul_ctx_pb_red {pb} {Γ Γ' : context} :
    ws_cumul_ctx_pb pb Σ Γ Γ' ->
    ∑ Δ Δ', Σ ⊢ Γ ⇝ Δ × Σ ⊢ Γ' ⇝ Δ' ×
      compare_context Σ pb Δ Δ'.
  Proof using wfΣ.
    intros Hctx.
    induction Hctx.
    - exists [], []; intuition pcuic.
    - destruct IHHctx as (Δ & Δ' & redl & redr & eq).
      destruct p.
      { apply (ws_cumul_pb_red_ctx redl) in eqt.
        eapply ws_cumul_pb_red in eqt as (v & v' & [tv tv' com]).
        destruct (closed_red_eq_context_upto_l (pb:=pb) (Δ := Δ') byfvs tv' eq) as [t'' [redt'' eq']].
        exists (vass na v :: Δ), (vass na' t'' :: Δ').
        intuition auto. constructor; auto. constructor; auto.
        eapply red_red_ctx_inv'; tea.
        constructor; auto. econstructor.
        eapply red_red_ctx_inv'; tea.
        constructor => //. constructor; auto.
        destruct pb; cbn in *.
        * transitivity v' => //.
        * transitivity v' => //. now eapply eq_term_leq_term. }
      { apply (ws_cumul_pb_red_ctx redl) in eqb.
        eapply ws_cumul_pb_red in eqb as (v & v' & [tv tv' com]).
        destruct (closed_red_eq_context_upto_l (pb:=pb) (Δ := Δ') byfvs tv' eq) as [t'' [redt'' eq']].
        apply (ws_cumul_pb_red_ctx redl) in eqt.
        eapply ws_cumul_pb_red in eqt as (v0 & v0' & [tv0 tv0' com0]).
        destruct (closed_red_eq_context_upto_l (pb:=pb) (Δ := Δ') byfvs tv0' eq) as [t0'' [redt0'' eq0']].
        exists (vdef na v v0 :: Δ), (vdef na' t'' t0'' :: Δ').
        intuition auto. constructor; auto. constructor; auto.
        1-2:eapply red_red_ctx_inv'; tea.
        constructor; auto. econstructor; eapply red_red_ctx_inv'; tea.
        constructor => //. constructor; auto.
        cbn in *. transitivity v' => //.
        destruct pb; cbn in *.
        * transitivity v0' => //.
        * transitivity v0' => //. now eapply eq_term_leq_term. }
  Qed.

  Lemma ws_cumul_pb_ws_cumul_ctx {pb pb'} {Γ Γ'} {T U} :
    Σ ⊢ Γ' ≤[pb'] Γ ->
    Σ ;;; Γ ⊢ T ≤[pb] U ->
    Σ ;;; Γ' ⊢ T ≤[pb] U.
  Proof using wfΣ.
    intros Hctx H.
    apply ws_cumul_ctx_pb_red in Hctx => //.
    destruct Hctx as [Δ [Δ' [l [r elr]]]].
    eapply (ws_cumul_pb_red_ctx r) in H.
    destruct pb'; cbn in *.
    - eapply (ws_cumul_pb_eq_context_upto (symmetry elr)) in H. 2:eauto with fvs.
      now eapply (ws_cumul_pb_red_ctx_inv l) in H.
    - eapply (ws_cumul_pb_compare_context (pb:=Cumul) elr) in H. 2:eauto with fvs.
      now eapply (ws_cumul_pb_red_ctx_inv l) in H.
  Qed.

  #[global]
  Instance conv_context_sym : Symmetric (ws_cumul_ctx_pb Conv Σ).
  Proof using wfΣ.
    intros Γ Γ' conv.
    eapply All2_fold_sym; tea.
    clear Γ Γ' conv. intros Γ Γ' d d' H IH []; constructor; auto.
    now symmetry.
    eapply ws_cumul_pb_ws_cumul_ctx; tea. now symmetry.
    now symmetry.
    eapply ws_cumul_pb_ws_cumul_ctx; tea. now symmetry.
    eapply ws_cumul_pb_ws_cumul_ctx; tea. now symmetry.
  Qed.

  Lemma ws_cumul_pb_eq_le {Γ t u} :
    Σ ;;; Γ ⊢ t = u -> Σ ;;; Γ ⊢ t ≤ u.
  Proof using Type.
    induction 1.
    - constructor; eauto.
      now eapply eq_term_leq_term.
    - econstructor 2; eauto.
    - econstructor 3; eauto.
  Qed.
  Hint Resolve ws_cumul_pb_eq_le : pcuic.

  Lemma conv_cumul_context {Γ Δ} :
    Σ ⊢ Γ ≤[Conv] Δ -> Σ ⊢ Γ ≤[Cumul] Δ.
  Proof using wfΣ.
    induction 1; constructor; auto.
    eapply conv_context_sym in X.
    depelim p; constructor; auto.
    - now apply ws_cumul_pb_eq_le.
    - now apply ws_cumul_pb_eq_le.
  Qed.
  Hint Resolve conv_cumul_context : pcuic.

  (** This is provable as conversion is not relying on types of variables,
      and bodies of let-ins are convertible even for context cumulativity. *)

  Local Remark ws_cumul_pb_ws_cumul_ctx_inv {pb pb'} {Γ Γ'} {T U} :
    Σ ⊢ Γ ≤[pb'] Γ' ->
    Σ ;;; Γ ⊢ T ≤[pb] U ->
    Σ ;;; Γ' ⊢ T ≤[pb] U.
  Proof using wfΣ.
    intros Hctx H.
    apply ws_cumul_ctx_pb_red in Hctx => //.
    destruct Hctx as [Δ [Δ' [l [r elr]]]].
    eapply (ws_cumul_pb_red_ctx_inv r).
    destruct pb'; cbn in *.
    - eapply (ws_cumul_pb_red_ctx l) in H.
      eapply (ws_cumul_pb_compare_context_inv (pb:=Conv) elr) in H => //. eauto with fvs.
    - eapply (ws_cumul_pb_red_ctx l) in H.
      eapply (ws_cumul_pb_compare_context_inv (pb:=Cumul) elr) in H => //. eauto with fvs.
  Qed.

  Lemma ws_cumul_decls_ws_cumul_ctx {pb pb'} {Γ Γ'} {d d'} :
    Σ ⊢ Γ' ≤[pb'] Γ ->
    ws_cumul_decls pb Σ Γ d d' ->
    ws_cumul_decls pb Σ Γ' d d'.
  Proof using wfΣ.
    intros Hctx H.
    destruct H; constructor; auto; eapply ws_cumul_pb_ws_cumul_ctx; tea.
  Qed.

  #[global]
  Instance ws_cumul_ctx_pb_trans pb : Transitive (ws_cumul_ctx_pb pb Σ).
  Proof using wfΣ.
    eapply All2_fold_trans.
    intros.
    etransitivity; tea.
    now eapply (ws_cumul_decls_ws_cumul_ctx X).
  Qed.

End ContextConversion.

#[global] Hint Resolve isType_is_open_term isTypeRel_is_open_term PCUICClosedTyp.wf_local_closed_context : fvs.
#[global] Hint Resolve conv_ctx_refl' : pcuic.
#[global] Hint Constructors All_decls_alpha_pb : pcuic.

Lemma compare_context_cumul_pb_context {cf} Σ pb :
  subrelation (compare_context Σ pb) (cumul_pb_context cumulAlgo_gen pb Σ).
Proof.
  intros Γ Δ h. induction h.
  - constructor.
  - constructor; tas.
    destruct p; constructor; auto; constructor; tas.
Qed.

Lemma eq_context_upto_cumul_pb_context {cf:checker_flags} (Σ : global_env_ext) cmp_universe cmp_sort pb pb' :
  RelationClasses.subrelation (cmp_universe Conv) (eq_universe Σ) ->
  RelationClasses.subrelation (cmp_universe pb) (compare_universe Σ pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (eq_sort Σ) ->
  RelationClasses.subrelation (cmp_sort pb) (compare_sort Σ pb') ->
  subrelation (eq_context_upto Σ cmp_universe cmp_sort pb) (cumul_pb_context cumulAlgo_gen pb' Σ).
Proof.
  intros.
  etransitivity. 2: apply compare_context_cumul_pb_context.
  eapply eq_context_upto_impl; tc.
Qed.

Lemma eq_context_upto_conv_context {cf:checker_flags} (Σ : global_env_ext) cmp_universe cmp_sort :
  RelationClasses.subrelation (cmp_universe Conv) (eq_universe Σ) ->
  RelationClasses.subrelation (cmp_sort Conv) (eq_sort Σ) ->
  subrelation (eq_context_upto Σ cmp_universe cmp_sort Conv) (conv_context cumulAlgo_gen Σ).
Proof.
  intros.
  apply eq_context_upto_cumul_pb_context; tc.
Qed.

Lemma eq_context_upto_cumul_context {cf:checker_flags} (Σ : global_env_ext) cmp_universe cmp_sort :
  RelationClasses.subrelation (cmp_universe Conv) (eq_universe Σ) ->
  RelationClasses.subrelation (cmp_universe Cumul) (leq_universe Σ) ->
  RelationClasses.subrelation (cmp_sort Conv) (eq_sort Σ) ->
  RelationClasses.subrelation (cmp_sort Cumul) (leq_sort Σ) ->
  subrelation (eq_context_upto Σ cmp_universe cmp_sort Cumul) (fun Γ Γ' => cumul_context cumulAlgo_gen Σ Γ Γ').
Proof.
  intros.
  apply eq_context_upto_cumul_pb_context; tc.
Qed.

#[global]
Instance eq_subrel_eq_univ {cf:checker_flags} Σ : RelationClasses.subrelation eq (eq_universe Σ).
Proof. intros x y []. reflexivity. Qed.

#[global]
Instance eq_subrel_eq_sort {cf:checker_flags} Σ : RelationClasses.subrelation eq (eq_sort Σ).
Proof. intros x y []. reflexivity. Qed.

Lemma eq_context_upto_names_conv_context {cf:checker_flags} (Σ : global_env_ext) :
  subrelation eq_context_upto_names (fun Γ Γ' => conv_context cumulAlgo_gen Σ Γ Γ').
Proof.
  etransitivity.
  2: apply compare_context_cumul_pb_context.
  eapply eq_context_upto_names_eq_context_upto; tc.
Qed.

Lemma eq_context_upto_univ_conv_context {cf:checker_flags} {Σ : global_env_ext} Γ Δ :
  eq_context Σ.1 Σ Γ Δ ->
  conv_context cumulAlgo_gen Σ Γ Δ.
Proof.
  apply compare_context_cumul_pb_context.
Qed.

Lemma eq_context_upto_univ_cumul_context {cf:checker_flags} {Σ : global_env_ext} Γ Δ :
  leq_context Σ.1 Σ Γ Δ ->
  cumul_context cumulAlgo_gen Σ Γ Δ.
Proof.
  apply compare_context_cumul_pb_context.
Qed.

Lemma conv_context_app_same {cf:checker_flags} Σ Γ Γ' Δ :
  conv_context cumulAlgo_gen Σ Γ Γ' ->
  conv_context cumulAlgo_gen Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof.
  intros HΔ.
  induction Δ; auto.
  destruct a as [na [b|] ty]; constructor; auto;
    constructor; reflexivity.
Qed.

Lemma cumul_context_app_same {cf:checker_flags} Σ Γ Γ' Δ :
  cumul_context cumulAlgo_gen Σ Γ Γ' ->
  cumul_context cumulAlgo_gen Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof.
  intros HΔ.
  induction Δ; auto.
  destruct a as [na [b|] ty]; constructor; auto;
    constructor; reflexivity.
Qed.

#[global] Hint Extern 4 (eq_term_upto_univ _ _ _ _ _ _) => reflexivity : pcuic.

Lemma context_cumulativity_wf_app {cf:checker_flags} Σ Γ Γ' Δ :
  cumul_context cumulAlgo_gen Σ Γ' Γ ->
  wf_local Σ Γ' ->
  All_local_env (fun Γ j =>
    forall Γ' : context,
    cumul_context cumulAlgo_gen Σ Γ' Γ -> wf_local Σ Γ' ->
    (lift_typing0 (fun t T => Σ;;; Γ' |- t : T)) j)
    (Γ,,, Δ) ->
  wf_local Σ (Γ' ,,, Δ).
Proof.
  intros.
  eapply All_local_env_app => //.
  eapply All_local_env_app_inv in X1 as [].
  eapply All_local_env_impl_ind; tea => /=.
  intros Γ'' j H HT.
  eapply HT. eapply All2_fold_app => //.
  eapply All2_fold_refl. intros. eapply cumul_decls_refl.
  eapply All_local_env_app; auto.
Qed.

Lemma is_closed_context_cumul_app Γ Δ Γ' :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context Γ' ->
  #|Γ| = #|Γ'| ->
  is_closed_context (Γ' ,,, Δ).
Proof.
  rewrite !on_free_vars_ctx_app => /andP[] onΓ onΔ onΓ' <-.
  now rewrite onΓ' onΔ.
Qed.

Lemma on_free_vars_decl_eq n m d :
  on_free_vars_decl (shiftnP n xpred0) d ->
  n = m ->
  on_free_vars_decl (shiftnP m xpred0) d.
Proof.
  now intros o ->.
Qed.

#[global] Hint Extern 4 (is_true (on_free_vars_decl (shiftnP _ xpred0) _)) =>
  eapply on_free_vars_decl_eq; [eassumption|len; lia] : fvs.

Lemma ws_cumul_ctx_pb_false_forget {cf} {Σ} {wfΣ : wf Σ} {Γ Γ'} :
  ws_cumul_ctx_pb Conv Σ Γ Γ' -> conv_context cumulAlgo_gen Σ Γ Γ'.
Proof.
  apply: ws_cumul_ctx_pb_forget.
Qed.

Lemma ws_cumul_ctx_pb_true_forget {cf} {Σ} {wfΣ : wf Σ} {Γ Γ'} :
  ws_cumul_ctx_pb Cumul Σ Γ Γ' -> cumul_context cumulAlgo_gen Σ Γ Γ'.
Proof.
  apply: ws_cumul_ctx_pb_forget.
Qed.

Ltac exass H :=
  match goal with
  |- ∑ x : ?A, _ =>
    assert (H : A); [idtac|exists H]
  end.

Lemma into_ws_cumul_ctx_pb {cf:checker_flags} {pb : conv_pb} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ Γ' : context} :
  is_closed_context Γ ->
  is_closed_context Γ' ->
  cumul_pb_context cumulAlgo_gen pb Σ Γ Γ' ->
  ws_cumul_ctx_pb pb Σ Γ Γ'.
Proof.
  move/on_free_vars_ctx_All_fold => onΓ.
  move/on_free_vars_ctx_All_fold => onΓ'.
  destruct pb.
  { intros cum.
    eapply All2_fold_All_fold_mix in cum; tea.
    eapply All2_fold_impl_ind; tea. clear -wfΣ.
    cbn; intros. red.
    eapply All2_fold_All_fold_mix_inv in X as [cum [onΓ onΔ]].
    move/on_free_vars_ctx_All_fold: onΓ => onΓ.
    move/on_free_vars_ctx_All_fold: onΔ => onΓ'.
    destruct X1 as [wsd [wsd' cumd]].
    eapply into_ws_cumul_decls; cbn; tea.
    rewrite (All2_fold_length X0) //. }
  { intros cum.
    eapply All2_fold_All_fold_mix in cum; tea.
    eapply All2_fold_impl_ind; tea. clear -wfΣ.
    cbn; intros. red.
    eapply All2_fold_All_fold_mix_inv in X as [cum [onΓ onΔ]].
    move/on_free_vars_ctx_All_fold: onΓ => onΓ.
    move/on_free_vars_ctx_All_fold: onΔ => onΓ'.
    destruct X1 as [wsd [wsd' cumd]].
    eapply into_ws_cumul_decls; cbn; tea.
    rewrite (All2_fold_length X0) //. }
Qed.

Lemma ws_cumul_ctx_pb_refl {cf} {Σ} {wfΣ : wf Σ} {pb} {Γ : context} :
  is_closed_context Γ -> Σ ⊢ Γ ≤[pb] Γ.
Proof.
  move/on_free_vars_ctx_All_fold.
  induction 1; constructor; auto.
  eapply (into_ws_cumul_decls _ Γ); tea; eauto with fvs.
  destruct pb; cbn; reflexivity.
Qed.

Lemma ws_cumul_ctx_pb_app_same {cf} {Σ} {wfΣ : wf Σ} {pb} {Γ Γ' Δ : context} :
  is_closed_context (Γ ,,, Δ) ->
  Σ ⊢ Γ ≤[pb] Γ' -> Σ ⊢ Γ,,, Δ ≤[pb] Γ',,, Δ.
Proof.
  move=> iscl cum.
  eapply into_ws_cumul_ctx_pb => //.
  eapply is_closed_context_cumul_app; tea; eauto with fvs.
  now rewrite (All2_fold_length cum).
  destruct pb.
  - apply conv_context_app_same.
    now apply ws_cumul_ctx_pb_false_forget.
  - apply cumul_context_app_same.
    now apply ws_cumul_ctx_pb_true_forget.

Qed.

Lemma context_cumulativity_app {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {pb Γ Γ' Δ Δ'} :
  Σ ⊢ Γ' ≤ Γ ->
  Σ ⊢ Γ ,,, Δ ≤[pb] Γ ,,, Δ' ->
  Σ ⊢ Γ' ,,, Δ ≤[pb] Γ' ,,, Δ'.
Proof.
  intros cum conv.
  pose proof (length_of conv). len in H.
  eapply All2_fold_app; eauto.
  eapply ws_cumul_ctx_pb_refl; cbn; eauto with fvs.
  eapply All2_fold_app_inv in conv as []. 2:lia.
  eapply All2_fold_impl_ind; tea.
  intros. simpl in X1.
  pose proof (All2_fold_length cum).
  eapply ws_cumul_decls_ws_cumul_ctx; tea.
  eapply ws_cumul_ctx_pb_app_same.
  { pose proof (ws_cumul_ctx_pb_closed_left cum).
    eapply (ws_cumul_decls_inv _ (Γ':=Γ' ,,, Γ0)) in X1 as [isc _]; tea.
    eapply is_closed_context_cumul_app; tea; try lia. }
  exact cum.
Qed.

Abbreviation open_context Γ := (ws_context (shiftnP #|Γ| xpred0)).

Lemma weakening_cumul0 {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ : closed_context} {Γ'' : open_context Γ}
  {M N : open_term Γ} n :
  n = #|Γ''| ->
  Σ ;;; Γ |- M <= N ->
  Σ ;;; Γ ,,, Γ'' |- lift0 n M <= lift0 n N.
Proof. intros; subst. apply (weakening_cumul (Γ':= [])); tea; eauto with fvs. Qed.
