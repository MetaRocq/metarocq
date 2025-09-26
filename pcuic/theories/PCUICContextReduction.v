(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICInduction
     PCUICReduction PCUICCases PCUICWeakeningConv PCUICWeakeningTyp
     PCUICTyping PCUICOnFreeVars PCUICSubstitution
     PCUICRenameDef PCUICRenameConv PCUICInstDef PCUICInstConv.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Section CtxReduction.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext}.
  Context (wfΣ : wf Σ).

  Lemma red_prod_alt Γ na M M' N N' :
    red Σ Γ M M' -> red Σ (Γ ,, vass na M') N N' ->
    red Σ Γ (tProd na M N) (tProd na M' N').
  Proof using Type.
    intros. eapply (transitivity (y := tProd na M' N)).
    * now eapply (red_ctx_congr (tCtxProd_l _ tCtxHole _)).
    * now eapply (red_ctx_congr (tCtxProd_r _ _ tCtxHole)).
  Qed.

  Lemma red_decls_refl Γ Δ d : red_decls Σ Γ Δ d d.
  Proof using Type.
    destruct d as [na [b|] ty]; constructor; auto.
  Qed.

  Lemma red_context_refl Γ : red_context Σ Γ Γ.
  Proof using Type.
    apply All2_fold_refl => ? ?.
    apply red_decls_refl.
  Qed.

  Lemma red_context_app_same {Γ Δ Γ'} :
    red_context Σ Γ Δ ->
    red_context Σ (Γ ,,, Γ') (Δ ,,, Γ').
  Proof using Type.
    intros r.
    eapply All2_fold_app => //.
    apply All2_fold_refl.
    intros; apply red_decls_refl.
  Qed.
  Hint Rewrite inst_case_predicate_context_length : len.

  Lemma on_inst_case_context P Γ pars puinst ctx :
    on_ctx_free_vars P Γ ->
    test_context_k (fun k : nat => on_free_vars (closedP k xpredT))
       #|pars| ctx ->
    forallb (on_free_vars P) pars ->
    on_ctx_free_vars (shiftnP #|ctx| P) (Γ,,, PCUICCases.inst_case_context pars puinst ctx).
  Proof using Type.
    move=> onΓ onctx hpars.
    relativize #|ctx|; [erewrite on_ctx_free_vars_extend, onΓ|now len].
    eapply on_free_vars_ctx_inst_case_context; tea; auto.
  Qed.

  Ltac inv_on_free_vars ::=
    match goal with
    | [ H : is_true (on_free_vars ?P (tPrim ?p)) |- _ ] =>
      cbn in H; move/andP: H => [] /andP[]; intros ???
    | [ H : is_true (on_free_vars ?P ?t) |- _ ] =>
      progress cbn in H;
      (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] ||
        eapply forallb_All in H); intros
    end.

  Lemma red1_red_ctx P Γ Δ t u :
    on_ctx_free_vars P Γ ->
    on_ctx_free_vars P Δ ->
    on_free_vars P t ->
    red1 Σ Γ t u ->
    red_context Σ Δ Γ ->
    red Σ Δ t u.
  Proof using wfΣ.
    move=> onΓ onΔ ont r Hctx.
    revert P onΓ ont Δ onΔ Hctx.
    induction r using red1_ind_all; intros P onΓ ont Δ onΔ Hctx;
      try inv_on_free_vars;
      try solve [eapply red_step; repeat (constructor; eauto)].
    - red in Hctx.
      destruct nth_error eqn:hnth => //; simpl in H; noconf H.
      eapply All2_fold_nth_r in Hctx; eauto.
      destruct Hctx as [x' [? ?]].
      destruct p as [cr rd]. destruct c => //; simpl in *.
      depelim rd => //. noconf H.
      eapply red_step.
      * constructor. rewrite e => //.
      * rewrite -(firstn_skipn (S i) Δ).
        eapply weakening_red_0; auto.
        + rewrite firstn_length_le //.
          eapply nth_error_Some_length in e. lia.
        + move: onΔ.
          rewrite -{1}(firstn_skipn (S i) Δ) on_ctx_free_vars_app.
          move=> /andP [] _; apply.
        + pose proof (nth_error_Some_length e).
          rewrite firstn_length_le //.
          eapply (nth_error_on_free_vars_ctx _ 0) in onΔ; tea.
          now move/andP: onΔ=> [] /=.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - eapply red_abs_alt; eauto.
    - eapply red_abs_alt; eauto.
      unshelve eapply (IHr (shiftnP 1 P)); tea.
      3:repeat (constructor; auto).
      all:rewrite on_ctx_free_vars_snoc ?onΓ ?onΔ /= //; auto with fvs.
    - eapply red_letin; eauto.
    - eapply red_letin; eauto.
    - unshelve eapply red_letin_alt; eauto.
      eapply IHr; tea.
      3:repeat (constructor; auto).
      all:rewrite on_ctx_free_vars_snoc ?onΓ ?onΔ /= //; auto with fvs.
    - eapply red_case_pars; eauto; pcuic.
      solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_All2; tea => /=; intuition eauto.
    - eapply red_case_p. eapply IHr; tea.
      3:now apply red_context_app_same.
      all:apply on_inst_case_context; tea.
    - eapply red_case_c; eauto.
    - eapply red_case_brs.
      unfold on_Trel; pcuic.
      eapply forallb_All in p4.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_All2; eauto.
      simpl. intuition eauto. rtoProp.
      eapply b1; revgoals; tea.
      1:now apply red_context_app_same.
      all:eapply on_inst_case_context; tea.
    - eapply red_proj_c; eauto.
    - eapply red_app; eauto.
    - eapply red_app; eauto.
    - eapply red_prod_alt; eauto.
    - eapply red_prod_alt; eauto.
      eapply IHr; tea.
      * rewrite on_ctx_free_vars_snoc onΓ; auto with fvs.
      * rewrite on_ctx_free_vars_snoc onΔ; auto with fvs.
      * constructor; auto. now constructor.
    - eapply red_evar. simpl in ont.
      solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_All2; simpl; eauto. simpl. intuition eauto.
    - eapply red_fix_one_ty.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      intuition eauto. move/andP: H0 => [] /=. eauto.
    - eapply red_fix_one_body.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto. move/andP: H0 => /= []; intuition eauto.
      eapply b0; tea.
      * relativize #|mfix0|; [erewrite on_ctx_free_vars_extend, onΓ, on_free_vars_fix_context|now len] => //.
      * relativize #|mfix0|; [erewrite on_ctx_free_vars_extend, onΔ, on_free_vars_fix_context|now len] => //.
      * now eapply red_context_app_same.
    - eapply red_cofix_one_ty.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      move/andP: H0 => []; intuition eauto.
    - eapply red_cofix_one_body.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
      move/andP: H0 => []; intuition auto.
      eapply b0; tea.
      * relativize #|mfix0|; [erewrite on_ctx_free_vars_extend, onΓ, on_free_vars_fix_context|now len] => //.
      * relativize #|mfix0|; [erewrite on_ctx_free_vars_extend, onΔ, on_free_vars_fix_context|now len] => //.
      * now eapply red_context_app_same.
    - eapply red_primArray_one_value. toAll. eapply OnOne2_All_mix_left in X; tea. solve_all.
    - eapply red_primArray_default; eauto.
    - eapply red_primArray_type; eauto.
  Qed.

  Lemma red_red_ctx P Γ Δ t u :
    on_ctx_free_vars P Γ ->
    on_ctx_free_vars P Δ ->
    on_free_vars P t ->
    red Σ Γ t u ->
    red_context Σ Δ Γ ->
    red Σ Δ t u.
  Proof using wfΣ.
    intros onΓ onΔ ont.
    induction 1; eauto using red1_red_ctx.
    intros H.
    transitivity y; eauto.
    eapply IHX2; tea. eapply red_on_free_vars in X1; tea.
  Qed.

  Lemma red_context_app {Γ Γ' Δ Δ'} :
    red_context Σ Γ Δ ->
    red_context_rel Σ Γ Γ' Δ' ->
    red_context Σ (Γ ,,, Γ') (Δ ,,, Δ').
  Proof using Type.
    intros r r'.
    eapply All2_fold_app => //.
    eapply All2_fold_impl; tea => /= Γ0 Γ'0 d d'.
    intros h; depelim h; constructor; auto.
  Qed.

  Lemma red_context_app_same_left {Γ Γ' Δ'} :
    red_context_rel Σ Γ Γ' Δ' ->
    red_context Σ (Γ ,,, Γ') (Γ ,,, Δ').
  Proof using Type.
    intros h.
    eapply All2_fold_app => //.
    apply red_context_refl.
  Qed.

  Lemma on_ctx_free_vars_cons P d Γ :
    on_ctx_free_vars P (d :: Γ) =
    on_ctx_free_vars (addnP 1 P) Γ && (P 0 ==> on_free_vars_decl (addnP 1 P) d).
  Proof using Type.
    rewrite (on_ctx_free_vars_app _ _ [_]) on_ctx_free_vars_tip /=.
    bool_congr.
  Qed.

  Lemma red_context_on_ctx_free_vars {P Γ Δ} :
    on_ctx_free_vars P Γ ->
    red_context Σ Γ Δ ->
    on_ctx_free_vars P Δ.
  Proof using wfΣ.
    intros onΓ.
    induction 1 in P, onΓ |- *; auto.
    rewrite /= on_ctx_free_vars_cons in onΓ.
    rewrite on_ctx_free_vars_cons.
    move/andP: onΓ => [] onΓ ond.
    rewrite (IHX _ onΓ) /=.
    case: (P 0) ond => //=.
    rewrite /on_free_vars_decl /test_decl /=.
    case: p; intros; eauto using red_on_free_vars.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
      intros. apply /andP. eauto using red_on_free_vars.
  Qed.

  Lemma red_context_rel_on_ctx_free_vars {P Γ Δ Δ'} :
    on_ctx_free_vars (addnP #|Δ| P) Γ ->
    on_ctx_free_vars P Δ ->
    red_context_rel Σ Γ Δ Δ' ->
    on_ctx_free_vars P Δ'.
  Proof using wfΣ.
    intros onΓ onΔ.
    induction 1 in onΓ, P, onΔ |- *; auto.
    rewrite /= on_ctx_free_vars_cons in onΔ.
    rewrite on_ctx_free_vars_cons.
    move/andP: onΔ => [] onΔ ond.
    rewrite (IHX _ _ onΔ) /=.
    { rewrite addnP_add Nat.add_1_r //. }
    case: (P 0) ond => //=.
    rewrite /on_free_vars_decl /test_decl /=.
    case: p; intros; eauto using red_on_free_vars.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
      intros _ ond. eapply red_on_free_vars. 3:tea. 2:auto.
      now rewrite on_ctx_free_vars_app onΔ onΓ.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
      intros. apply /andP. split.
      * eapply red_on_free_vars;revgoals;tea.
        now rewrite on_ctx_free_vars_app onΔ onΓ.
      * eapply red_on_free_vars;revgoals;tea.
        now rewrite on_ctx_free_vars_app onΔ onΓ.
  Qed.

  Definition on_ctx_free_vars_fold P ctx :=
    All_fold (fun Γ d =>
      let k := Nat.pred #|ctx| - #|Γ| in
      P k ==> on_free_vars_decl (addnP (S k) P) d) ctx.

  Lemma addnP_closedP n P : addnP 1 (closedP (S n) P) ≐1 closedP n (addnP 1 P).
  Proof using Type.
    intros i. rewrite /addnP /closedP /shiftnP /=.
    repeat (PCUICSigmaCalculus.nat_compare_specs => //).
  Qed.

  Lemma red_context_trans Γ Δ Δ' :
    on_ctx_free_vars (closedP #|Γ| xpredT) Γ ->
    red_context Σ Γ Δ -> red_context Σ Δ Δ' -> red_context Σ Γ Δ'.
  Proof using wfΣ.
    intros onctx H; induction H in onctx, Δ' |- *; auto.
    intros H'; depelim H'.
    move: onctx; rewrite on_ctx_free_vars_cons => /andP[] /= onΓ ond.
    setoid_rewrite addnP_closedP in onΓ.
    setoid_rewrite addnP_closedP in ond.
    intros.
    constructor; eauto.
    - eapply IHAll2_fold; tea.
    - destruct p; depelim r; constructor.
      * eapply red_trans; tea.
        eapply red_red_ctx. 4,5:tea. all:tea.
        { eapply red_context_on_ctx_free_vars; tea. }
        { eapply red_on_free_vars; tea; auto with fvs. }
      * eapply red_trans; tea.
        eapply red_red_ctx. 4,5:tea. all:tea.
        { eapply red_context_on_ctx_free_vars; tea. }
        { eapply red_on_free_vars; tea; auto with fvs.
          move/andP: ond => [] /= //. }
      * eapply red_trans; tea.
        eapply red_red_ctx. 4,5:tea. all:tea.
        { eapply red_context_on_ctx_free_vars; tea. }
        { eapply red_on_free_vars; tea; auto with fvs.
          move/andP: ond => [] /= //. }
  Qed.

  Lemma red_context_app_right {Γ Γ' Δ Δ'} :
    on_ctx_free_vars (closedP #|Γ ,,, Γ'| xpredT) (Γ ,,, Γ') ->
    red_context Σ Γ Δ ->
    red_context_rel Σ Δ Γ' Δ' ->
    red_context Σ (Γ ,,, Γ') (Δ ,,, Δ').
  Proof using wfΣ.
    intros onf red red'.
    eapply red_context_trans; tea.
    - eapply red_context_app_same. tea.
    - eapply red_context_app; [apply red_context_refl|tas].
  Qed.

  Lemma red_context_rel_inv {Γ Γ' Δ'} :
    red_context Σ (Γ ,,, Γ') (Γ ,,, Δ') ->
    red_context_rel Σ Γ Γ' Δ'.
  Proof using Type.
    intros r.
    eapply All2_fold_app_inv => //.
    move: (All2_fold_length r). len.
  Qed.

  (*
    intros onΓ r r'.
    eapply All2_fold_app => //.
    * now rewrite (All2_fold_length r').
    * move: onΓ; rewrite on_ctx_free_vars_app => /andP [] onΓ' onΓ.
      have onΔ := red_context_on_ctx_free_vars onΓ r.
      have onΔ' := red_context_rel_on_ctx_free_vars onΔ onΓ' r'.
      induction r' in P, onΓ, onΔ, onΓ', onΔ' |- *; simpl; constructor; auto.
      - move: onΓ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ0 ond; tea.
        move: onΔ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ'' ond'; tea.
        eapply IHr'; tea.
      - destruct p.
        + constructor.
          move: onΓ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ0 ond; tea.
          move: onΔ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ'' ond'; tea.
          simpl in onΓ, onΔ.
          eapply red_red_ctx.
          5:now eapply red_context_app_same.
          4:tea.
          { rewrite on_ctx_free_vars_app. erewrite onΓ0. now rewrite addnP_add Nat.add_1_r onΔ. }
          { rewrite on_ctx_free_vars_app. erewrite onΓ0. now rewrite addnP_add Nat.add_1_r onΓ. }
  Abort. *)

  Lemma OnOne2_local_env_All2_fold {P Q Γ Δ} :
    OnOne2_local_env P Γ Δ ->
    (forall Γ d d', P Γ d d' -> Q Γ Γ d d') ->
    (forall Γ Δ d, Q Γ Δ d d) ->
    All2_fold Q Γ Δ.
  Proof using Type.
    intros onc HPQ HQ.
    induction onc; try constructor; auto.
    - apply All2_fold_refl => //.
    - apply All2_fold_refl => //.
  Qed.

  Lemma red_ctx_rel_red_context_rel Γ Δ Δ' :
    on_ctx_free_vars (closedP #|Γ,,, Δ| xpredT) (Γ,,, Δ) ->
    red_ctx_rel Σ Γ Δ Δ' <~> red_context_rel Σ Γ Δ Δ'.
  Proof using wfΣ.
    intros cl.
    split.
    - rewrite /red_ctx_rel /red_context_rel; induction 1.
      * eapply OnOne2_local_env_All2_fold; tea => ? d d'.
        2:{ eapply red_decls_refl. }
        destruct d as [na [b|] ty], d' as [na' [b'|] ty']; cbn; intuition auto;
          subst; constructor; auto.
      * eapply All2_fold_refl => Δ [na [b|] ty]; constructor; auto; constructor 2.
      * rewrite - !/(red_ctx_rel _ _ _ _) - !/(red_context_rel _ _ _ _) in X1 X2 IHX1 IHX2 *.
        eapply red_context_app_same_left in IHX1 => //.
        eapply red_context_app_same_left in IHX2 => //.
        2:{ eapply red_context_on_ctx_free_vars; tea.
            now rewrite -(All2_fold_length IHX1). }
        eapply red_context_rel_inv.
        eapply red_context_trans; tea.
    - induction 1; try solve [constructor].
      depelim p.
      * transitivity (vass na T' :: Γ0).
        { eapply red_one_decl_red_ctx_rel.
          do 2 constructor; auto. }
        rewrite /= on_ctx_free_vars_cons in cl.
        move/andP: cl=> [] ond cl. specialize (IHX ond).
        clear -IHX.
        induction IHX; try now do 2 constructor.
        econstructor 3; tea.
      * transitivity (vdef na b' T :: Γ0).
        + eapply red_one_decl_red_ctx_rel.
          do 2 constructor; auto.
        + transitivity (vdef na b' T' :: Γ0).
          ++ eapply red_one_decl_red_ctx_rel.
             do 2 constructor; auto.
          ++ rewrite /= on_ctx_free_vars_cons in cl;
              move/andP: cl=> [] ond cl. specialize (IHX ond). clear -IHX.
             induction IHX; try now do 2 constructor.
             econstructor 3; tea.
  Qed.

End CtxReduction.



