From Stdlib Require Import Bool List Arith Lia.
From Stdlib Require String.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICGlobalEnv
  PCUICTactics PCUICCumulativity
  PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping PCUICSigmaCalculus PCUICOnFreeVars PCUICClosed PCUICConfluence PCUICSpine PCUICInductiveInversion PCUICParallelReductionConfluence PCUICWellScopedCumulativity PCUICClosed PCUICRenameDef PCUICInstConv PCUICClosedTyp PCUICWeakeningEnvTyp PCUICRenameTyp PCUICRenameConv PCUICGuardCondition PCUICWeakeningConv.

From MetaRocq.PCUIC Require Import BDTyping BDToPCUIC BDFromPCUIC.

From Stdlib Require Import ssreflect ssrbool.
From Stdlib.Program Require Import Equality.

Ltac case_inequalities :=
  match goal with
  | |- context [?x <=? ?y] =>
    destruct (Nat.leb_spec x y)
  | |- context [?x <? ?y] =>
    destruct (Nat.ltb_spec x y)
  end.

Lemma shiftnP_shiftn P f i : (shiftnP i P) ∘ (shiftn i f) ≐1 shiftnP i (P ∘ f).
Proof.
  intros k.
  rewrite !/shiftnP /shiftn.
  destruct (Nat.ltb_spec k i) => /=.
  all: case_inequalities => //=; lia_f_equal.
Qed.

Lemma on_free_vars_rename P f t :
  on_free_vars P (rename f t) = on_free_vars (P ∘ f) t.
Proof.
  induction t in P, f |- * using term_forall_list_ind.

  all: cbn => //.

  - erewrite forallb_map, All_forallb_eq_forallb ; tea.
    all: eauto.
  - by rewrite IHt1 IHt2 shiftnP_shiftn.
  - by rewrite IHt1 IHt2 shiftnP_shiftn.
  - by rewrite IHt1 IHt2 IHt3 shiftnP_shiftn.
  - by rewrite IHt1 IHt2.
  - destruct X as (IHpar&ctx&IHret).
    f_equal.
    1: erewrite forallb_map, All_forallb_eq_forallb ; tea ; eauto.
    f_equal.
    1: by rewrite IHret shiftnP_shiftn.
    f_equal.
    1: by rewrite length_map.
    f_equal.
    1: auto.
    erewrite forallb_map, All_forallb_eq_forallb ; tea.
    1: reflexivity.
    intros b [].
    f_equal.
    1: by rewrite length_map.
    by rewrite /PCUICSigmaCalculus.rename_branch /= e shiftnP_shiftn.
  - erewrite forallb_map, All_forallb_eq_forallb ; tea.
    1: reflexivity.
    intros ? [? ebod].
    rewrite /test_def /=.
    f_equal.
    1: auto.
    by rewrite length_map ebod shiftnP_shiftn.
  - erewrite forallb_map, All_forallb_eq_forallb ; tea.
    1: reflexivity.
    intros ? [? ebod].
    rewrite /test_def /=.
    f_equal.
    1: auto.
    by rewrite length_map ebod shiftnP_shiftn.
  - solve_all.
Qed.

Lemma Alli_impl_le {A P Q} {l : list A} {n} :
  Alli P n l ->
  (forall m x, m <= n + #|l| -> P m x -> Q m x) ->
  Alli Q n l.
Proof.
  induction 1.
  - intros _. constructor.
  - intros H.
    constructor.
    + apply H => //.
      1: lia.
    + apply IHX.
      intros.
      apply H => //.
      cbn. lia.
Qed.

Lemma addnP_strengthen_lift i k k' :
  i <= k' ->
  (addnP (S i) (strengthenP k' k xpredT)) ∘ (lift_renaming k (Nat.pred k' - i))
    ≐1 xpredT.
Proof.
  intros l ?.
  rewrite /addnP /strengthenP /lift_renaming.
  destruct (Nat.leb_spec (Nat.pred k' - i) a) => //.
  all: case_inequalities => //.
  all: case_inequalities => //.
  all: lia.
Qed.


Lemma on_ctx_free_vars_strengthenP Γ Γ' Γ'':
  on_ctx_free_vars xpredT Γ ->
  on_ctx_free_vars xpredT Γ'' ->
  on_ctx_free_vars (strengthenP #|Γ''| #|Γ'| xpredT) (Γ,,,Γ',,,lift_context #|Γ'| 0 Γ'').
Proof.
  intros hΓ hΓ''.
  rewrite !on_ctx_free_vars_app.
  repeat (apply /andP ; split).
  - rewrite /on_ctx_free_vars /lift_context /=.
    erewrite alli_fold_context_k_prop.
    apply alli_Alli in hΓ''.
    eapply alli_Alli, Alli_impl_le ; tea.
    move => i [? [?|] ?] /= ?.
    + rewrite /on_free_vars_decl /test_decl /= !addnP_xpredT => /andP [? ?].
      apply /implyP => _.
      apply /andP ; split.
      all: rewrite lift_rename on_free_vars_rename Nat.add_0_r addnP_strengthen_lift //.
    + rewrite /on_free_vars_decl /test_decl /= !addnP_xpredT => ?.
      apply /implyP => _.
      rewrite lift_rename on_free_vars_rename Nat.add_0_r addnP_strengthen_lift //.

  - rewrite lift_context_length.
    rewrite /on_ctx_free_vars.
    apply alli_Alli.
    eapply forall_nth_error_Alli.
    intros i ? ?.
    assert (i < #|Γ'|) by (apply nth_error_Some ; congruence).
    rewrite /addnP /strengthenP /=.
    repeat case_inequalities => //=.
    all: lia.
  - rewrite addnP_add lift_context_length.
    erewrite on_ctx_free_vars_proper.
    3: reflexivity.
    1: eassumption.
    intros ?.
    rewrite /addnP /strengthenP.
    case_inequalities => //.
    case_inequalities => //.
    lia.
Qed.

Lemma on_free_vars_ctx_tip P d : on_free_vars_ctx P [d] = on_free_vars_decl P d.
Proof. cbn; rewrite andb_true_r // shiftnP0 //. Qed.

Lemma on_free_vars_it_mkLambda_or_LetIn {P Δ t} :
  on_free_vars P (it_mkLambda_or_LetIn Δ t) =
    on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
Proof.
  move: P. induction Δ using rev_ind => P.
  - cbn. now rewrite shiftnP0.
  - destruct x as [na [b|] ty]; rewrite it_mkLambda_or_LetIn_app /= /mkLambda_or_LetIn /=.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
      /on_free_vars_decl /test_decl /=. ring.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
     /on_free_vars_decl /test_decl /=. ring.
Qed.

Lemma on_free_vars_case_predicate_context `{checker_flags} Σ ci mdecl idecl p P :
  wf Σ ->
  declared_inductive Σ ci mdecl idecl ->
  forallb (on_free_vars P) (pparams p) ->
  wf_predicate mdecl idecl p ->
  eq_context_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  on_free_vars_ctx P (case_predicate_context ci mdecl idecl p).
Proof.
  intros.
  rewrite /case_predicate_context /case_predicate_context_gen /pre_case_predicate_context_gen /inst_case_context.
  erewrite <- on_free_vars_map2_cstr_args.
  2: rewrite fold_context_k_length !length_map ; eapply All2_length ; tea.
  apply on_free_vars_ctx_subst_context0.
  2: by rewrite forallb_rev.
  rewrite on_free_vars_ctx_subst_instance List.length_rev.
  apply closedn_ctx_on_free_vars_shift.
  replace #|pparams p| with (context_assumptions (ind_params mdecl)).
  1: eapply closed_ind_predicate_context ; tea ; eapply declared_minductive_closed ; eauto.
  apply H0.
  erewrite wf_predicate_length_pars ; tea.
  eapply onNpars, on_declared_minductive ; eauto.
  apply H0.
Qed.

Lemma on_free_vars_case_branch_context `{checker_flags} {Σ : global_env_ext } {wfΣ : wf Σ} {P ci mdecl idecl p br cdecl} :
   let brctx := case_branch_context ci.1 mdecl p (forget_types (bcontext br)) cdecl in
   declared_constructor Σ ci mdecl idecl cdecl ->
   wf_predicate mdecl idecl p ->
   wf_branch cdecl br ->
   forallb (on_free_vars P) (pparams p) ->
   on_free_vars_ctx P brctx.
Proof.
  intros brctx decli wfp wfb havp.
  rewrite /brctx /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
  rewrite -on_free_vars_map2_cstr_args.
  { len. by apply wf_branch_length. }
  eapply on_free_vars_ctx_inst_case_context ; tea.
  1: reflexivity.
  rewrite test_context_k_closed_on_free_vars_ctx -closedn_ctx_on_free_vars.
  erewrite wf_predicate_length_pars ; eauto.
  erewrite <- onNpars.
  2: eapply PCUICInductives.oi.
  2: apply decli.
  eapply closedn_ctx_cstr_branch_context.
  eassumption.
Qed.

Lemma substP_shiftnP k n p :
  substP k n p (shiftnP (k+n) p) ≐1 (shiftnP k p).
Proof.
  intros i; rewrite /shiftnP /substP /= /strengthenP /=.
  do 2 case_inequalities => //=.
  1-2: exfalso ; lia.
  by rewrite /= (Nat.add_comm k n) Nat.sub_add_distr Nat.add_sub orb_diag.
Qed.

Lemma on_free_vars_subst (p : nat -> bool) k s t :
  forallb (on_free_vars p) s ->
  on_free_vars (shiftnP (k + #|s|) p) t ->
  on_free_vars (shiftnP k p) (subst s k t).
Proof.
  intros.
  rewrite -substP_shiftnP.
  by apply on_free_vars_subst_gen.
Qed.

Corollary on_free_vars_subst0 (p : nat -> bool) s t :
  forallb (on_free_vars p) s ->
  on_free_vars (shiftnP #|s| p) t ->
  on_free_vars p (subst s 0 t).
Proof.
  intros.
  rewrite -(shiftnP0 p).
  by apply on_free_vars_subst.
Qed.


Lemma on_free_vars_case_branch_type `{checker_flags} {Σ : global_env_ext } {wfΣ : wf Σ} {P} {ci : case_info} {mdecl idecl p br i cdecl} :
  let predctx := case_predicate_context ci mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx (preturn p) in
  let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
  declared_constructor Σ (ci.(ci_ind),i) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  eq_context_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  wf_branch cdecl br ->
  forallb (on_free_vars P) (pparams p) ->
  on_free_vars (shiftnP #|pcontext p| P) (preturn p) ->
  on_free_vars (shiftnP #|bcontext br| P) brctxty.2.
Proof.
  intros predctx ptm brctxty decli wfp allctx wfb havp havr.
  rewrite /brctxty /case_branch_type /case_branch_type_gen /=.
  rewrite on_free_vars_mkApps.
  apply /andP ; split.
  2: rewrite forallb_app ; apply /andP ; split.
  - erewrite wf_branch_length by eassumption.
    eapply on_free_vars_lift0.
    rewrite addnP_shiftnP /ptm on_free_vars_it_mkLambda_or_LetIn.
    apply /andP ; split.
    + rewrite /predctx.
      eapply on_free_vars_case_predicate_context.
      all: tea.
      apply decli.
    + rewrite /predctx.
      rewrite case_predicate_context_length.
      all: eassumption.

  - repeat rewrite !forallb_map.
    epose proof (declared_constructor_closed_indices decli).
    eapply forallb_impl ; tea.
    intros.
    rewrite (wf_branch_length wfb).
    apply on_free_vars_subst.
    1: by rewrite forallb_rev.
    rewrite List.length_rev /expand_lets_k -shiftnP_add.
    assert (#|pparams p| = (context_assumptions (subst_instance (puinst p) (ind_params mdecl)))) as ->.
    { erewrite context_assumptions_subst_instance, onNpars, wf_predicate_length_pars ; eauto.
      eapply PCUICInductives.oi ; eauto.
      exact decli.p1.
    }
    apply on_free_vars_subst.
    + eapply foron_free_vars_extended_subst.
      rewrite on_free_vars_ctx_subst_instance.
      eapply closed_ctx_on_free_vars, declared_inductive_closed_params.
      by eapply decli.
    + rewrite extended_subst_length subst_instance_length context_assumptions_subst_instance.
      rewrite shiftnP_add Nat.add_comm.
      apply on_free_vars_lift_impl.
      rewrite Nat.add_comm.
      apply on_free_vars_subst.
      1:{
        eapply forallb_impl ; [|eapply closed_inds].
        intros ; by apply closed_on_free_vars.
      }
      len.
      rewrite on_free_vars_subst_instance.
      apply closedn_on_free_vars.
      by rewrite Nat.add_comm Nat.add_assoc.

  - rewrite /= andb_true_r on_free_vars_mkApps.
    apply /andP ; split => //.
    rewrite forallb_app.
    apply /andP ; split.
    + rewrite forallb_map.
      eapply forallb_impl ; tea.
      intros.
      by rewrite on_free_vars_lift0 // (wf_branch_length wfb) addnP_shiftnP.
    + rewrite (wf_branch_length wfb).
      by apply on_free_vars_to_extended_list.

Qed.

Definition unlift_renaming n k i := if i <? k then i else i - n.
Definition unlift n k := rename (unlift_renaming n k).

Lemma lift_unlift n k : (unlift_renaming n k) ∘ (lift_renaming n k) ≐1 ren_id.
Proof.
  intros i.
  rewrite /unlift_renaming /lift_renaming /ren_id.
  repeat case_inequalities.
  all: lia.
Qed.

Corollary lift_unlift_term {n k} t : unlift n k (lift n k t) = t.
Proof.
  by rewrite lift_rename /unlift (rename_compose _ _ _) lift_unlift rename_ren_id.
Qed.

Corollary lift_unlift_context {n k} Γ :
  rename_context (unlift_renaming n k) (rename_context (lift_renaming n k) Γ) = Γ.
Proof.
  etransitivity.
  2: by apply fold_context_k_id.
  rewrite /rename_context fold_context_k_compose.
  apply fold_context_k_proper => //.
  intros ? ?.
  etransitivity.
  2: by apply rename_ren_id.
  rewrite rename_compose.
  apply rename_proper => //.
  intros ?.
  rewrite shiftn_lift_renaming.
  rewrite /shiftn /unlift_renaming /lift_renaming /ren_id.
  repeat case_inequalities => //.
  all: lia.
Qed.

Section OnFreeVars.

  Context `{cf : checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ).

  Let Pinfer Γ t T :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P T.

  Let Psort (Γ : context) (t : term) (u : sort) := True.

  Let Pprod Γ t (na : aname) A B :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.

  Let Pind Γ (ind : inductive) t (u : Instance.t) args :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    All (on_free_vars P) args.

  Let Pcheck (Γ : context) (t : term) (T : term) := True.

  Let Pj (Γ : context) (j : judgment) := True.

  Let PΓ (Γ : context) :=
    True.

  Let PΓ_rel (Γ Γ' : context) := True.

  Theorem bidirectional_on_free_vars : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind Pj PΓ PΓ_rel.
  Proof using wfΣ.
    apply bidir_ind_env.

    - constructor.

    - constructor.

    - constructor.

    - intros. red.
      intros P HΓ Hn.
      eapply alli_Alli, Alli_nth_error in HΓ ; tea.
      apply on_free_vars_lift0.
      by move: HΓ => /implyP /(_ Hn) /andP [].

    - easy.
    - easy.
    - intros until bty.
      move => _ _ _ Hbty ? ? /= /andP [] ? ?.
      apply /andP ; split ; tea.
      apply Hbty ; tea.
      rewrite on_ctx_free_vars_snoc.
      apply /andP ; split ; tea.

    - intros until A.
      move => _ _ _ Ht ? ? /= /andP [] ? /andP [] ? ?.
      repeat (apply /andP ; split ; tea).
      apply Ht ; tea.
      rewrite on_ctx_free_vars_snoc.
      repeat (apply /andP ; split ; tea).

    - intros until u.
      move => _ HAB _ _ ? ? /= /andP [] ? ?.
      edestruct HAB ; tea.
      apply on_free_vars_subst1 ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_constant_closed_type ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_inductive_closed_type ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      eapply declared_constructor_closed_type ; tea.

    - intros.
      move => ? ? /= /and5P [] ? ? Hctx ? ?.
      rewrite on_free_vars_mkApps.
      apply /andP ; split.
      + rewrite on_free_vars_it_mkLambda_or_LetIn.
        rewrite test_context_k_closed_on_free_vars_ctx -closedn_ctx_on_free_vars in Hctx.
        apply /andP ; split.
        2: by rewrite case_predicate_context_length.
        eapply on_free_vars_case_predicate_context ; eassumption.

      + rewrite forallb_app.
        apply /andP ; split.
        2: by rewrite /= andb_true_r.
        apply All_forallb, All_skipn.
        auto.

    - intros until args.
      move => ? _ ? largs ? ? ?.
      apply on_free_vars_subst0.
      + cbn ; apply /andP ; split ; auto.
        rewrite forallb_rev.
        apply All_forallb.
        auto.
      + eapply closedn_on_free_vars.
        rewrite closedn_subst_instance /= List.length_rev largs.
        eapply declared_projection_closed_type ; tea.

    - intros until decl.
      move => ? ndec ? ? ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].

    - intros until decl.
      move => ? ndec ? ? ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].

    - intros. red. intros. destruct X0; cbn => //.
      simp prim_type. cbn in *. solve_all.
    - easy.

    - intros ? ? ? ? ? ? _ HT Hred.
      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply red_on_free_vars in Hred ; tea.
      by move: Hred => /= /andP [].
    - intros ? ? ? ? ? ? _ HT Hred.
      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply red_on_free_vars in Hred ; tea.
      rewrite on_free_vars_mkApps in Hred.
      by move: Hred => /= /forallb_All.

    - easy.

  Qed.

  Lemma infering_on_free_vars P Γ t T :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |- t ▹ T ->
    on_free_vars P T.
  Proof using wfΣ.
    intros.
    edestruct bidirectional_on_free_vars as (_&_&_&_&p&_).
    eapply p ; eauto.
  Qed.

  Lemma infering_prod_on_free_vars P Γ t na A B :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |- t ▹Π (na,A,B) ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.
  Proof using wfΣ.
    intros.
    eapply bidirectional_on_free_vars ; eauto.
  Qed.

End OnFreeVars.

Lemma on_free_vars_type `{checker_flags} P Σ (wfΣ : wf Σ.1) Γ t T :
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Γ |- t : T ->
  ∑ T', on_free_vars P T' × Σ ;;; Γ |- t : T'.
Proof.
  intros oΓ ot ty.
  assert (wf_local Σ Γ) by (eapply typing_wf_local ; tea).
  apply typing_infering in ty as [T' []] ; tea.
  exists T' ; split.
  - edestruct bidirectional_on_free_vars as (_&_&_&_&?&_).
    all: eauto.
  - by apply infering_typing.
Qed.

Section BDRenaming.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wf Σ).

Let Pinfer Γ t T :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹ rename f T.

Let Psort Γ t u :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹□ u.

Let Pprod Γ t na A B :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹Π (na,rename f A,rename (shiftn 1 f) B).

Let Pind Γ ind t u args :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹{ind} (u, map (rename f) args).


Let Pcheck Γ t T :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  on_free_vars P T ->
  Σ ;;; Δ |- rename f t ◃ rename f T.

Let Pj Γ j :=
  forall P Δ f,
    urenaming P Γ Δ f ->
    on_ctx_free_vars P Γ ->
    lift_sorting
      (fun t T => on_free_vars P t -> on_free_vars P T -> Σ ;;; Δ |- rename f t ◃ rename f T)
      (fun T u => on_free_vars P T -> Σ ;;; Δ |- rename f T ▹□ u) j.

Let PΓ := All_local_env Pj.

Let PΓ_rel Γ Γ' :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars_ctx P Γ' ->
  wf_local_bd_rel Σ Δ (rename_context f Γ').

Lemma rename_telescope P f Γ Δ tel tys:
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  forallb (on_free_vars P) tys ->
  on_free_vars_ctx P (List.rev tel) ->
  PCUICTyping.ctx_inst Pcheck Γ tys tel ->
  PCUICTyping.ctx_inst (checking Σ) Δ (map (rename f) tys) (rename_telescope f tel).
Proof using Type.
  intros ur hΓ htys htel ins.
  induction ins in Δ, ur, hΓ, htys, htel |- *.
  - constructor.
  - rewrite rename_telescope_cons /=.
    move: htys => /= /andP [] ? ?.
    rewrite /= on_free_vars_ctx_app on_free_vars_ctx_tip /= in htel.
    move : htel => /andP [] ? ?.
    constructor.
    1: eauto.
    rewrite -(rename_subst_telescope _ [_]).
    apply IHins ; tea.
    rewrite -subst_context_subst_telescope.
    apply on_free_vars_ctx_subst_context0.
    1: assumption.
    by rewrite /= andb_true_r.
  - rewrite rename_telescope_cons /=.
    rewrite /= on_free_vars_ctx_app on_free_vars_ctx_tip /= in htel.
    move : htel => /andP [] /andP [] /= ? ? ?.
    constructor.
    rewrite -(rename_subst_telescope _ [_]).
    apply IHins ; tea.
    rewrite -subst_context_subst_telescope.
    apply on_free_vars_ctx_subst_context0.
    1: assumption.
    by rewrite /= andb_true_r.
Qed.

Theorem bidirectional_renaming : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind Pj PΓ PΓ_rel.
Proof using wfΣ.
  apply bidir_ind_env.

  - intros Γ j Hj P Δ f hf hΓ.
    apply lift_sorting_impl with (1 := Hj) => //; intros ?? [Ht IHt] **.
    all: eapply IHt; eauto.

  - intros Γ _ _ hΓ. red.
    apply All_local_env_impl with (1 := hΓ); clear Γ hΓ.
    intros Γ j Hj P Δ f hf hΓ'.
    apply lift_sorting_impl with (1 := Hj) => //; intros ?? IHt **.
    all: eapply IHt; eauto.

  - intros Γ Γ' _ _ HΓ P Δ f hf hΓ hΓ'.
    apply All_local_env_fold. change (fold_context_k _ ?Γ) with (rename_context f Γ).
    induction HΓ in hΓ' |- * using All_local_rel_ind1. 1: constructor.
    rewrite on_free_vars_ctx_snoc in hΓ'. move/andP: hΓ' => [hΓ'] /andP [onb ont].
    apply All_local_env_snoc; auto.
    eapply urenaming_context in hf ; tea.
    apply lift_sorting_f_it_impl with X => //.
    1: destruct decl_body => //; cbn in onb |- *.
    all: intros IHt; eapply IHt; eauto.
    all: rewrite on_ctx_free_vars_concat hΓ /= on_free_vars_ctx_on_ctx_free_vars //.

  - intros Γ n decl isdecl P Δ f hf hΓ ht.
    eapply hf in isdecl as h => //.
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto.

  - intros. red. intros. cbn in *.
    by constructor.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor.
    { specialize (X0 _ _ _ hf hΓ).
      eapply lift_sorting_f_it_impl with X0 => //= IH. now apply IH. }
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor ; eauto.
    { specialize (X0 _ _ _ hf hΓ).
      eapply lift_sorting_f_it_impl with X0 => //= IH. now apply IH. }
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? /andP [] ? ?.
    econstructor ; eauto.
    { specialize (X0 _ _ _ hf hΓ).
      eapply lift_sorting_f_it_impl with X0 => //= IH. all: now apply IH. }
    eapply X2 ; tea.
    1: by apply urenaming_vdef.
    rewrite on_ctx_free_vars_snoc.
    repeat (apply /andP ; split ; tea).

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    rewrite rename_subst0 ; cbn.
    econstructor ; eauto.
    eapply X2 ; tea.
    eapply infering_prod_on_free_vars.
    4: eassumption.
    all: assumption.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_constant_closed_type ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_inductive_closed_type ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= _.
    erewrite rename_closed.
    2: by eapply declared_constructor_closed_type ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] on_pars /andP [] ? /andP [] ? /andP [] ? /forallb_All on_brs.
    rewrite rename_mkApps rename_it_mkLambda_or_LetIn map_app map_skipn /=.
    rewrite rename_case_predicate_context // case_predicate_context_length // rename_predicate_preturn.
    econstructor ; eauto.
    + eapply X2 ; tea.
      * rewrite -rename_case_predicate_context //.
        erewrite <- case_predicate_context_length ; tea.
        apply urenaming_context ; assumption.
      * erewrite <- case_predicate_context_length ; tea.
        rewrite /predctx.
        erewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        rewrite on_free_vars_ctx_on_ctx_free_vars.
        eapply on_free_vars_case_predicate_context ; tea.
    + by eapply rename_wf_predicate.
    + rewrite -rename_case_predicate_context ; tea.
      eapply X5 ; tea.
      eapply on_free_vars_case_predicate_context ; tea.
    + rewrite -[subst_instance _ _](rename_closedn_ctx f 0).
      { pose proof (declared_inductive_closed_params H).
        now rewrite closedn_subst_instance_context. }
      rewrite rename_context_telescope rename_telescope_shiftn0 /=.
      eapply rename_telescope ; tea.
      rewrite rev_involutive.
      rewrite on_free_vars_ctx_subst_instance.
      eapply closed_ctx_on_free_vars, declared_inductive_closed_params.
      eassumption.

    + now rewrite length_map.

    + rewrite /= firstn_map.
      eapply bidirectional_on_free_vars, (All_firstn (n := ci.(ci_npar))) in X ; tea.
      solve_all.
      now eapply conv_renameP.
    + by apply rename_wf_branches.
    + eapply Forall2_All2 in H7.
      eapply All2i_All2_mix_left in X9; eauto.
      eapply All2i_All_mix_right in X9 ; eauto.
      eapply All2i_nth_hyp in X9.
      eapply All2i_map_right, (All2i_impl X9) => i cdecl br.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
      move=> [Hnth [ [wfbr [eqbctx [wfbctx [IHbctx [Hbod IHbod]]]]] /andP [on_ctx on_bod] ]].
      rewrite test_context_k_closed_on_free_vars_ctx in on_ctx.
      rewrite -(rename_closed_constructor_body mdecl cdecl f).
      { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
        split; eauto. }
      split; auto.
      { simpl. rewrite -rename_cstr_branch_context //.
        1:eapply (declared_inductive_closed_params H).
        rewrite rename_closedn_ctx //.
        eapply closed_cstr_branch_context.
        now split.
      }
      cbn -[case_branch_type case_predicate_context].
      rewrite case_branch_type_fst.
      rewrite -rename_case_branch_context_gen //.
      2-3:len.
      1:exact (declared_inductive_closed_params H).
      1:rewrite (wf_branch_length wfbr) //.
      1:rewrite (wf_predicate_length_pars H1).
      1:erewrite declared_minductive_ind_npars ; eauto; apply H.
      assert (on_free_vars_ctx P brctxty.1).
      { rewrite case_branch_type_fst.
        eapply (@on_free_vars_case_branch_context _ _ _ _ (ci.(ci_ind),i)).
        all: tea.
        split.
        all: eassumption.
      }
      set (brctx' := rename_context f _).
      split.
      1: eapply IHbctx ; eauto.
      rewrite rename_case_branch_type //.
      eapply IHbod.
      * rewrite case_branch_type_fst /=.
        relativize #|bcontext br| ; [eapply urenaming_context|] ; tea.
        by rewrite case_branch_context_length.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
        relativize (#|bcontext br|).
        1: erewrite on_ctx_free_vars_concat.
        2: rewrite case_branch_type_length //.
        2: erewrite wf_branch_length ; eauto.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
        eapply on_free_vars_case_branch_type.
        all: tea.
        split.
        all: assumption.

  - intros. red. move => P Δ f hf hΓ /= ?.
    rewrite rename_subst0 /= rename_subst_instance map_rev List.length_rev.
    erewrite rename_closedn.
    2: rewrite H0 ; eapply declared_projection_closed_type ; tea.
    econstructor ; eauto.
    by rewrite length_map.

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply fix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + apply All_mix with (1 := ht) in X0.
      apply All_map, All_impl with (1 := X0).
      move => d [] /andP [] hT hb p.
      specialize (p _ _ _ hf hΓ).
      eapply lift_sorting_it_impl_gen with p => // IHp.
      eapply IHp ; tea.
    + apply All_mix with (1 := ht) in X2.
      apply All_map, All_impl with (1 := X2).
      move => d [] /andP [] hT hb p.
      rewrite /on_def_body !rename_fix_context !rename_context_length -!(fix_context_length mfix) -!rename_shiftn in hb |- *.
      eapply urenaming_context in hf ; tea.
      eapply on_ctx_free_vars_fix_context in hΓ; tea. rewrite -(fix_context_length mfix) in hΓ.
      specialize (p _ _ _ hf hΓ).
      rewrite <-(shiftnP0 P) in hT. eapply on_free_vars_lift_impl in hT. rewrite Nat.add_0_r in hT.
      apply lift_sorting_f_it_impl with p => //= IHp.
      all: eapply IHp ; tea.
    + by apply rename_wf_fixpoint.

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply cofix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + apply All_mix with (1 := ht) in X0.
      apply All_map, All_impl with (1 := X0).
      move => d [] /andP [] hT hb p.
      specialize (p _ _ _ hf hΓ).
      eapply lift_sorting_it_impl_gen with p => // IHp.
      eapply IHp ; tea.
    + apply All_mix with (1 := ht) in X2.
      apply All_map, All_impl with (1 := X2).
      move => d [] /andP [] hT hb p.
      rewrite /on_def_body !rename_fix_context !rename_context_length -!(fix_context_length mfix) -!rename_shiftn in hb |- *.
      eapply urenaming_context in hf ; tea.
      eapply on_ctx_free_vars_fix_context in hΓ; tea. rewrite -(fix_context_length mfix) in hΓ.
      specialize (p _ _ _ hf hΓ).
      rewrite <-(shiftnP0 P) in hT. eapply on_free_vars_lift_impl in hT. rewrite Nat.add_0_r in hT.
      apply lift_sorting_f_it_impl with p => //= IHp.
      all: eapply IHp ; tea.
    + by apply rename_wf_cofixpoint.

  - intros. red. intros P Δ f hf ht.
    cbn. rewrite rename_prim_type. econstructor; tea; rewrite ?prim_val_tag_map //.
    destruct X0; cbn in *; constructor; cbn; eauto.
    * eapply hty; tea; solve_all.
    * eapply hdef; tea; solve_all.
    * solve_all.

  - intros. red. intros P Δ f hf ht.
    econstructor ; eauto.
    rewrite -/(rename f (tSort u)).
    eapply red_rename ; tea.
    now eapply infering_on_free_vars.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tProd na A B)).
    eapply red_rename ; tea.
    now eapply infering_on_free_vars.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tInd ind ui)) -rename_mkApps.
    eapply red_rename ; tea.
    now eapply infering_on_free_vars.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    eapply cumul_renameP ; tea.
    eapply infering_on_free_vars.
    4: eassumption.
    all: assumption.

Qed.

End BDRenaming.

Lemma closedn_ctx_lift_inv n k k' Γ :
  k <= k' -> closedn_ctx (k' + n) (lift_context n k Γ) ->
  closedn_ctx k' Γ.
Proof.
  intros le.
  induction Γ as [|d ?]; cbn; auto; rewrite lift_context_snoc !closedn_ctx_cons /=;
    move/andP=> [clΓ cld]; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld; rewrite /test_decl /=.
  replace (k' + n + #|Γ|) with (#|Γ| + k' + n) in * by lia.
  move/andP=> [clb clt]; apply andb_and; split.
  - destruct (decl_body d) => /= //. cbn in clb |- *.
    eapply closedn_lift_inv in clb => //.
    lia.
  - eapply closedn_lift_inv in clt => //.
    lia.
Qed.

Lemma urenaming_strengthen P Γ Γ' Γ'' :
  urenaming (strengthenP #|Γ''| #|Γ'| P) (Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'') (Γ,,,Γ'') (unlift_renaming #|Γ'| #|Γ''|).
Proof.
  rewrite <- rename_context_lift_context.
  intros i decl' pi nthi.
  rewrite /strengthenP in pi.
  destruct (Nat.ltb_spec0 i #|Γ''|) as [iΓ''|iΓ''].
  - rewrite nth_error_app_context_lt in nthi.
    1: by rewrite fold_context_k_length.
    rewrite nth_error_rename_context in nthi.
    apply option_map_Some in nthi as [decl'' []].
    subst.
    eexists ; split ; [idtac|split ; [idtac|split]].
    + rewrite /unlift_renaming.
      move: (iΓ'') => /Nat.ltb_spec0 ->.
      rewrite nth_error_app_context_lt //.
      eassumption.
    + reflexivity.
    + rewrite /= rename_compose.
      apply rename_proper ; auto.
      intros x.
      rewrite !rshiftk_S lift_renaming_spec -(shiftn_rshiftk _ _ _) !shiftn_add -lift_renaming_spec.
      rewrite Nat.add_0_r Nat.add_comm Nat.sub_add; try lia.
      rewrite (lift_unlift _ _ _) /ren_id /unlift_renaming.
      by move: (iΓ'') => /Nat.ltb_spec0 ->.
    + cbn ; destruct (decl_body decl'') ; rewrite //=.
      f_equal.
      rewrite rename_compose.
      apply rename_proper ; auto.
      intros x.
      change (S (i + _)) with
        (rshiftk (S i) (shiftn (#|Γ''| - S i) (lift_renaming #|Γ'| 0) x)).
      rewrite shiftn_lift_renaming lift_renaming_spec -(shiftn_rshiftk _ _ _) shiftn_add.
      rewrite -lift_renaming_spec Nat.add_0_r.
      rewrite Nat.add_comm Nat.sub_add //.
      rewrite (lift_unlift _ _ _) /ren_id /unlift_renaming.
      by move: (iΓ'') => /Nat.ltb_spec0 ->.
  - rewrite -app_context_assoc /= in nthi.
    destruct (Nat.ltb_spec0 i (#|Γ''| + #|Γ'|)) as [iΓ'|iΓ'] ; cbn in * ; [congruence|..].
    apply Nat.nlt_ge in iΓ'.
    rewrite nth_error_app_context_ge length_app /= rename_context_length // in nthi.
    eexists ; repeat split.
    + rewrite /unlift_renaming.
      case_inequalities.
      1: lia.
      rewrite nth_error_app_context_ge ; [lia|..].
      rewrite -nthi.
      f_equal.
      lia.
    + apply rename_proper ; auto.
      intros x.
      rewrite /unlift_renaming.
      case_inequalities.
      1: lia.
      case_inequalities.
      all: lia.
    + destruct (decl_body decl') ; rewrite //=.
      f_equal.
      apply rename_proper ; auto.
      intros x.
      rewrite /unlift_renaming.
      case_inequalities.
      1: lia.
      case_inequalities.
      all: lia.
Qed.


Theorem typing_renaming_cond_P `{checker_flags} {P f Σ Γ Δ t T} {wfΣ : wf Σ.1} :
  renaming P Σ Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Γ |- t : T ->
  ∑ T', [× (on_free_vars P T'), (Σ ;;; Γ |- t : T'), (Σ ;;; Γ |- T' <= T) &
  (Σ ;;; Δ |- rename f t : rename f T')].
Proof.
  move => [ur wfΔ] fvΓ fvt tyt.
  move: (tyt) => /typing_wf_local wfΓ.
  move: (tyt) => /typing_infering [T' [inf cum]].
  unshelve epose proof (infering_on_free_vars _ _ _ _ _ _ _ _ inf); eauto.
  pose proof (inf' := inf). apply infering_typing in inf; eauto.
  exists T'. split; eauto.
  eapply ws_cumul_pb_forget_cumul; eauto.
  eapply bidirectional_renaming in inf'; eauto.  eapply infering_typing; eauto.
Qed.

Lemma strengthening `{cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Γ' Γ'' t T :
  Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |- lift #|Γ'| #|Γ''| t : T ->
  ∑ T', [× on_free_vars (strengthenP #|Γ''| #|Γ'| xpredT) T',
        (Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |- lift #|Γ'| #|Γ''|  t : T') ,
        (Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |- T' <= T) &
        (Σ ;;;  Γ ,,, Γ'' |- t : unlift #|Γ'| #|Γ''| T')].
Proof.
  intros Hty.
  assert (wf_local Σ Γ) by
    move: Hty => /typing_wf_local /All_local_env_app_inv [] /All_local_env_app_inv [] //.

  assert (wfΓ'' : wf_local Σ (Γ ,,, Γ'')).
  { apply All_local_env_app => //.
    erewrite <- (lift_unlift_context Γ'').
    eapply bidirectional_to_pcuic ; tea.
    rewrite rename_context_lift_context.
    eapply bidirectional_renaming ; tea.
    - eapply All_local_app_rel, bidirectional_from_pcuic => //.
      eapply type_Prop_wf.
      apply typing_wf_local in Hty.
      eassumption.
    - eapply (urenaming_strengthen _ _ _ []).
    - apply (on_ctx_free_vars_strengthenP _ _ []) => //.
      eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
      by apply wf_local_closed_context.
    - rewrite -on_free_vars_ctx_lift_context.
      move: Hty => /typing_wf_local /closed_wf_local.
      rewrite closedn_ctx_app => /andP [_] /=.
      rewrite app_context_length Nat.add_comm => hΓ''.
      apply closedn_ctx_lift_inv in hΓ''.
      2: easy.
      eapply (@closedn_ctx_on_free_vars_shift _ _ xpredT) in hΓ''.
      rewrite <- shiftnP_xpredT.
      eassumption.
  }

  eapply typing_renaming_cond_P in Hty as [T' [? ?]]; eauto.
  exists T'. split; eauto.
  - erewrite <- (lift_unlift_term t); eauto.
  - split; eauto. eapply urenaming_strengthen.
  - move: wfΓ'' => /wf_local_closed_context.
    rewrite on_free_vars_ctx_app => /andP [? ?].
    apply on_ctx_free_vars_strengthenP.
    all: eapply on_free_vars_ctx_on_ctx_free_vars_xpredT ; eassumption.
  - rewrite on_free_vars_lift -shiftnP_xpredT.
    move: Hty => /subject_closed.
    len.
    rewrite -[X in _ + X]Nat.add_comm Nat.add_assoc => Ht.
    eapply closedn_lift_inv in Ht.
    2: lia.
    eapply closedn_on_free_vars.
    eassumption.
Qed.


Lemma strengthening_type `{cf: checker_flags} {Σ : global_env_ext} {wfΣ : PCUICTyping.wf Σ} Γ Γ' Γ'' t s :
  Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |- lift #|Γ'| #|Γ''| t : tSort s ->
  ∑ s', Σ ;;; Γ ,,, Γ'' |- t : tSort s' × leq_sort Σ s' s.
Proof.
  intros H; pose proof (H' := H); eapply strengthening in H. destruct H as [T' [? HT Hcumul HT']].
  pose proof (Hcumul' := Hcumul).
  pose proof (type_closed HT).
  eapply closedn_on_free_vars in H.
  pose proof (type_closed HT').
  eapply closedn_on_free_vars in H0.
  pose proof (wf_local_closed_context (typing_wf_local H')).
  eapply into_ws_cumul_pb in Hcumul; eauto.
  eapply PCUICConversion.ws_cumul_pb_Sort_r_inv in Hcumul as [s' [Hred Hcumul]].
  eapply closed_red_red in Hred. pose proof (HT'':=HT'). eapply PCUICValidity.validity in HT' as (_ & ? & ? & _).
  exists s'; split; eauto.
  assert (PCUICReduction.red Σ (Γ,,, Γ'') (unlift #|Γ'| #|Γ''| T') (tSort s')).
  { assert (tSort s' = unlift #|Γ'| #|Γ''| (tSort s')) by reflexivity. rewrite H2; clear H2.
    eapply red_rename. eauto. eapply (urenaming_strengthen _ _ _ _); eauto.
    2-3: eauto. eapply typing_wf_local in HT''.
    eapply wf_local_closed_context in HT''. revert HT''.
    rewrite on_free_vars_ctx_app => /andP [? ?].
    apply on_ctx_free_vars_strengthenP.
    all: eapply on_free_vars_ctx_on_ctx_free_vars_xpredT; eauto.
  }
  eapply type_Cumul; eauto. eapply PCUICSR.subject_reduction; eauto.
  assert (liftSort : unlift #|Γ'| #|Γ''| (tSort s') = tSort s') by reflexivity. rewrite <- liftSort; clear liftSort.
  eapply PCUICConversion.cumulAlgo_cumulSpec. eapply PCUICConversion.ws_cumul_pb_red_r_inv; eauto.
  eapply ws_cumul_pb_refl; eauto. eapply PCUICInversion.typing_closed_ctx; eauto.
Qed.
