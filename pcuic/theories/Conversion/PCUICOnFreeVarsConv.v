(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICClosed
     PCUICOnFreeVars PCUICTyping PCUICReduction PCUICGlobalEnv PCUICWeakeningEnvConv PCUICClosedConv
     PCUICWeakeningEnvTyp PCUICInstDef PCUICRenameDef PCUICRenameConv.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Lemma on_free_vars_rename P f t :
  on_free_vars P (rename f t) = on_free_vars (P ∘ f) t.
Proof.
  induction t in P, f |- * using term_forall_list_ind.

  all: cbn => //.

  - erewrite forallb_map, All_forallb_eq_forallb ; tea.
    all: eauto.
  - by rw IHt1 IHt2 shiftnP_shiftn.
  - by rw IHt1 IHt2 shiftnP_shiftn.
  - by rw IHt1 IHt2 IHt3 shiftnP_shiftn.
  - by rw IHt1 IHt2.
  - destruct X as (IHpar&ctx&IHret).
    f_equal.
    1: erewrite forallb_map, All_forallb_eq_forallb ; tea ; eauto.
    f_equal.
    1: by rw IHret shiftnP_shiftn.
    f_equal.
    1: by rw length_map.
    f_equal.
    1: auto.
    erewrite forallb_map, All_forallb_eq_forallb ; tea.
    1: reflexivity.
    intros b [].
    f_equal.
    1: by rw length_map.
    by rw /PCUICSigmaCalculus.rename_branch /= e shiftnP_shiftn.
  - erewrite forallb_map, All_forallb_eq_forallb ; tea.
    1: reflexivity.
    intros ? [? ebod].
    rw /test_def /=.
    f_equal.
    1: auto.
    by rw length_map ebod shiftnP_shiftn.
  - erewrite forallb_map, All_forallb_eq_forallb ; tea.
    1: reflexivity.
    intros ? [? ebod].
    rw /test_def /=.
    f_equal.
    1: auto.
    by rw length_map ebod shiftnP_shiftn.
  - solve_all.
Qed.

Lemma shiftn_ext_cond (P : nat -> bool) f f' n :
  (forall i, P i -> f i = f' i) ->
  forall k,
  shiftnP n P k ->
  shiftn n f k = shiftn n f' k.
Proof.
  intros.
  unfold shiftn, shiftnP in H0 |- *.
  nat_compare_specs ; cbn in *.
  now f_equal.
Qed.

Lemma rename_ext_cond (P : nat -> bool) f f' t :
  ( forall i, P i -> f i = f' i ) ->
  on_free_vars P t ->
  rename f t = rename f' t.
Proof.
  intros H Ht.
  revert P f f' H Ht.
  elim t using term_forall_list_ind; cbn in |- *; intros; try easy.

  1-6,8,11:
    try rw H; try rw H0 ; try rw H1 ; try easy;
    solve [f_equal; solve_all; eauto using shiftn_ext_cond].

  - f_equal; solve_all.
    * eapply map_predicate_shift_eq_spec; solve_all; eauto using shiftn_ext_cond.
    * apply map_branch_shift_eq_spec; solve_all; eauto using shiftn_ext_cond.
  - f_equal.
    rw /test_def in Ht.
    solve_all ; eauto using shiftn_ext_cond.
  - f_equal.
    rw /test_def in Ht.
    solve_all ; eauto using shiftn_ext_cond.
Qed.

Lemma rename_on_free_vars n t f :
  on_free_vars (shiftnP n xpred0) t -> rename (shiftn n f) t = t.
Proof.
  intros.
  erewrite rename_ext_cond ; tea.
  1: now apply rename_ren_id.
  intros i.
  now rw /shiftnP /shiftn orb_false_r => -> //=.
Qed.


Lemma urename_on_free_vars_shift P Γ Δ f u (Ξ: context) :
   let sP := shiftnP #|Γ| P in
   urenaming sP Γ Δ f ->
   is_closed_context Γ ->
   is_closed_context Δ ->
   on_free_vars (shiftnP #|Ξ| (shiftnP #|Γ| xpred0)) u ->
   on_free_vars (shiftnP #|Ξ| (shiftnP #|Δ| xpred0))
                (rename (shiftn #|Ξ| f) u).
Proof.
  intros sP hf HΓ HΔ Hu. rw on_free_vars_rename.
  eapply on_free_vars_impl. 2: tea. clear Hu. intros n Hn.
  apply urenaming_context with (Ξ:=Ξ) in hf.
  unfold urenaming in hf.
  specialize (hf n). destruct (nth_error (Γ,,, Ξ) n) eqn : Hnth.
  - specialize (hf c); cbn in hf. forward hf.
    * unfold shiftnP in Hn. unfold sP , shiftnP.
      toProp. toProp Hn. destruct Hn.
      + intuition.
      + right. toProp. toProp H. destruct H; intuition auto with *.
    * destruct (hf eq_refl) as [decl' [Hfn _]].
      clear hf Hn. unfold sP , shiftnP. rw orb_false_r.
      assert (shiftn #|Ξ| f n < #|Δ,,, rename_context f Ξ|).
      { eapply nth_error_Some'. exists decl'. eauto. }
      rw app_context_length in H.
      rw rename_context_length in H.
      toProp. clear -H.
      repeat rw PeanoNat.Nat.ltb_lt. lia.
- rw nth_error_None in Hnth. rw app_context_length in Hnth. unfold shiftnP in *. toProp Hn. toProp. unfold shiftn.
  clear -Hn Hnth. destruct Hn.
  * toProp H. intuition auto with *.
  * toProp H. destruct H; [toProp H |]; intuition auto with *.
Defined.

Lemma urename_is_open_term P Γ Δ f u : let sP := shiftnP #|Γ| P in
   urenaming sP Γ Δ f -> is_closed_context Γ -> is_closed_context Δ -> is_open_term Γ u -> is_open_term Δ (rename f u).
Proof.
  intros sP hf HΓ HΔ Hu.
  unfold is_open_term.
  rewrite <- (shiftnP0 (shiftnP #|Δ| xpred0)).
  rewrite <- (shiftn0 f).
  eapply urename_on_free_vars_shift with (Ξ:=[]); eauto.
  rw shiftnP0; eauto.
Defined.




Lemma on_free_vars_ctx_inst_case_context
  P (Γ : list context_decl) (pars : list term)
  (puinst : Instance.t) (pctx : list context_decl) :
  forallb (on_free_vars (shiftnP #|Γ| P)) pars ->
  on_free_vars_ctx (closedP #|pars| xpredT) pctx ->
  on_free_vars_ctx P Γ ->
  on_free_vars_ctx P (Γ,,, inst_case_context pars puinst pctx).
Proof.
  intros. rw on_free_vars_ctx_app H1 /=.
  eapply on_free_vars_ctx_inst_case_context; trea; solve_all.
  rw test_context_k_closed_on_free_vars_ctx //.
Qed.


Lemma rename_context_on_free_vars f n l  :
on_free_vars_ctx (closedP n xpredT) l ->
rename_context (shiftn n f) l = l.
Proof.
  intro Hclosed.
  unfold on_free_vars_ctx in Hclosed.
  unfold rename_context, fold_context_k.
  induction l; eauto.
  cbn in *. rw alli_app in Hclosed. toProp Hclosed.
  destruct Hclosed as [H Hclosed].
  rw mapi_rec_app. rw List.distr_rev.
  rw IHl; eauto.
  cbn in *. f_equal.
  toProp Hclosed. destruct Hclosed as [Hclosed _].
  destruct a; unfold map_decl; cbn.
  unfold on_free_vars_decl in Hclosed.
  unfold test_decl in Hclosed.
  toProp Hclosed. cbn in Hclosed.
  destruct Hclosed as [Hbody Htype].
  f_equal.
  - destruct decl_body; eauto; cbn in *.
    f_equal. rw closedP_shiftnP in Hbody.
    rw shiftnP_add in Hbody. rw shiftn_add.
    apply rename_on_free_vars; eauto.
  - rw closedP_shiftnP in Htype.
    rw shiftnP_add in Htype. rw shiftn_add.
    apply rename_on_free_vars; eauto.
Defined.

Lemma inst_case_predicate_context_rename f p :
  on_free_vars_ctx (closedP #|pparams p| xpredT) (pcontext p) ->
  inst_case_predicate_context (rename_predicate f p) = rename_context f (inst_case_predicate_context p).
Proof.
  intro Hclosed. unfold inst_case_predicate_context.
  unfold pparams at 1. cbn.
  replace (pcontext p) with
  (rename_context (shiftn #|(pparams p)| f) (pcontext p)) at 1.
  - rewrite <- rename_inst_case_context. reflexivity.
  - apply rename_context_on_free_vars; eauto.
Defined.

Lemma inst_case_branch_context_rename f p x :
on_free_vars_ctx (closedP #|pparams p| xpredT) (bcontext x) ->
inst_case_branch_context (rename_predicate f p)
     (rename_branch f x) =
     rename_context f (inst_case_branch_context p x).
Proof.
  intro Hclosed. unfold inst_case_branch_context. cbn.
  replace (bcontext x) with
  (rename_context (shiftn #|(pparams p)| f) (bcontext x)) at 1.
  - rewrite <- rename_inst_case_context. reflexivity.
  - apply rename_context_on_free_vars; eauto.
Defined.
