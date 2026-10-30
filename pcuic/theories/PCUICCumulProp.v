(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICInductives PCUICGeneration PCUICSpine
     PCUICGlobalEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICSubstitution PCUICUnivSubst PCUICUnivSubstitutionConv
     PCUICUnivSubstitutionTyp PCUICClosedTyp
     PCUICConversion PCUICCumulativity PCUICConfluence PCUICContexts
     PCUICSR PCUICInversion PCUICValidity PCUICSafeLemmata PCUICContextConversion
     PCUICContextConversionTyp PCUICEquality PCUICReduction PCUICOnFreeVars
     PCUICWellScopedCumulativity
     PCUICInductiveInversion.

From Equations.Type Require Import Relation Relation_Properties.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect.

Implicit Types (Σ : global_env_ext).

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.

Lemma cumul_sort_confluence {Σ} {wfΣ : wf Σ} {Γ A u v} :
  Σ ;;; Γ ⊢ A ≤ tSort u ->
  Σ ;;; Γ ⊢ A ≤ tSort v ->
  ∑ v', (Σ ;;; Γ ⊢ A = tSort v') *
        (leq_sort (global_ext_constraints Σ) v' u /\
          leq_sort (global_ext_constraints Σ) v' v).
Proof using Type.
  move=> H H'.
  eapply ws_cumul_pb_Sort_r_inv in H as [u'u ?].
  eapply ws_cumul_pb_Sort_r_inv in H' as [vu ?].
  destruct p, p0.
  destruct (closed_red_confluence c c1) as [x [r1 r2]].
  eapply invert_red_sort in r1.
  eapply invert_red_sort in r2. subst. noconf r2.
  exists u'u. split; auto. now apply red_conv.
Qed.

Lemma cumul_ind_confluence {Σ : global_env_ext} {wfΣ : wf Σ} {Γ A ind u v l l'} :
  Σ ;;; Γ ⊢ A ≤ mkApps (tInd ind u) l  ->
  Σ ;;; Γ ⊢ A ≤ mkApps (tInd ind v) l' ->
  ∑ v' l'',
    [× Σ ;;; Γ ⊢ A ⇝ (mkApps (tInd ind v') l''),
       ws_cumul_pb_terms Σ Γ l l'',
       ws_cumul_pb_terms Σ Γ l' l'',
       cmp_ind_universes Σ ind #|l| v' u &
       cmp_ind_universes Σ ind #|l'| v' v].
Proof using Type.
  move=> H H'.
  eapply ws_cumul_pb_Ind_r_inv in H as [u'u [l'u [redl ru ?]]].
  eapply ws_cumul_pb_Ind_r_inv in H' as [vu [l''u [redr ru' ?]]].
  destruct (closed_red_confluence redl redr) as [nf [redl' redr']].
  eapply invert_red_mkApps_tInd in redl'  as [args' [eqnf clΓ conv]].
  eapply invert_red_mkApps_tInd in redr'  as [args'' [eqnf' _ conv']].
  rewrite eqnf in eqnf'. solve_discr. subst nf.
  all:auto. exists u'u, args'; split; auto.
  - transitivity (mkApps (tInd ind u'u) l'u).
    auto. eapply closed_red_mkApps => //.
  - eapply red_terms_ws_cumul_pb_terms in conv.
    transitivity l'u => //. now symmetry.
  - eapply red_terms_ws_cumul_pb_terms in conv'.
    transitivity l''u => //. now symmetry.
Qed.

Lemma ws_cumul_pb_LetIn_l_inv_alt {Σ Γ C na d ty b} {wfΣ : wf Σ.1} :
  wf_local Σ (Γ ,, vdef na d ty) ->
  Σ ;;; Γ ⊢ tLetIn na d ty b = C ->
  Σ ;;; Γ,, vdef na d ty ⊢ b = lift0 1 C.
Proof using Type.
  intros wf Hlet.
  epose proof (red_expand_let wf).
  etransitivity. eapply red_conv, X.
  eapply ws_cumul_pb_is_open_term_left in Hlet.
  { rewrite on_fvs_letin in Hlet. now move/and3P: Hlet => []. }
  eapply (@weakening_ws_cumul_pb _ _ _ _ Γ [] [vdef _ _ _]); auto.
  now eapply ws_cumul_pb_LetIn_l_inv in Hlet.
  now eapply wf_local_closed_context.
Qed.

Lemma is_propositional_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  Σ ;;; Γ ⊢ T ≤ tSort s ->
  Σ ;;; Γ ⊢ T ≤ tSort s' ->
  Sort.is_propositional s -> Sort.is_propositional s'.
Proof using Hcf.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluence hs hs') as [x' [conv [leq leq']]].
  move: leq leq'.
  destruct x', s, s' => //=.
  now rewrite Hcf.
Qed.

Lemma is_prop_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  Σ ;;; Γ ⊢ T ≤ tSort s ->
  Σ ;;; Γ ⊢ T ≤ tSort s' ->
  Sort.is_prop s -> Sort.is_prop s'.
Proof using Hcf.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluence hs hs') as [x' [conv [leq leq']]].
  move: leq leq'.
  destruct x', s, s' => //=.
  now rewrite Hcf.
Qed.

Lemma is_sprop_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  Σ ;;; Γ ⊢ T ≤ tSort s ->
  Σ ;;; Γ ⊢ T ≤ tSort s' ->
  Sort.is_sprop s -> Sort.is_sprop s'.
Proof using Type.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluence hs hs') as [x' [conv [leq leq']]].
  move: leq leq'.
  destruct x', s, s' => //=.
Qed.

Lemma prop_sort_eq {Σ Γ u u'} : Sort.is_prop u -> Sort.is_prop u' ->
  is_closed_context Γ ->
  Σ ;;; Γ ⊢ tSort u = tSort u'.
Proof using Type.
  destruct u, u';
  move=> //_ //_.
  constructor => //. constructor.
  red. red. constructor.
Qed.

Lemma sprop_sort_eq {Σ Γ u u'} : Sort.is_sprop u -> Sort.is_sprop u' ->
  is_closed_context Γ ->
  Σ ;;; Γ ⊢ tSort u = tSort u'.
Proof using Type.
  destruct u, u';
  move=> //_ //_.
  constructor => //. constructor.
  do 2 red. constructor.
Qed.

Lemma conv_sort_inv {Σ : global_env_ext} {wfΣ : wf Σ} Γ s s' :
  Σ ;;; Γ ⊢ tSort s = tSort s' ->
  eq_sort (global_ext_constraints Σ) s s'.
Proof using Type.
  intros H.
  eapply ws_cumul_pb_alt_closed in H as [v [v' [redv redv' eqvv']]].
  eapply invert_red_sort in redv.
  eapply invert_red_sort in redv'. subst.
  now depelim eqvv'.
Qed.

Lemma is_prop_superE {l} : Sort.is_prop (Sort.super l) -> False.
Proof using Type.
  destruct l => //.
Qed.

Lemma is_sprop_superE {l} : Sort.is_sprop (Sort.super l) -> False.
Proof using Type.
  destruct l => //.
Qed.

Lemma is_prop_prod {s s'} : Sort.is_prop s' -> Sort.is_prop (Sort.sort_of_product s s').
Proof using Type.
  destruct s' => //.
Qed.

Lemma is_sprop_prod {s s'} : Sort.is_sprop s' -> Sort.is_sprop (Sort.sort_of_product s s').
Proof using Type.
  destruct s' => //.
Qed.

Definition eq_univ_prop (u v : sort) :=
  match Sort.to_family u, Sort.to_family v with
  | Sort.fSProp, Sort.fSProp => true
  | Sort.fProp, Sort.fProp => true
  | Sort.fType, Sort.fType => true
  | Sort.fType, Sort.fProp | Sort.fProp, Sort.fType => prop_sub_type
  | _, _ => false
  end.

Definition eq_term_prop (Σ : global_env) napp :=
  PCUICEquality.eq_term_upto_univ_napp Σ (fun _ _ _ => True) (fun _ => eq_univ_prop) Conv napp.

Reserved Notation " Σ ;;; Γ |- t ~~ u " (at level 50, Γ, t, u at next level).

Inductive cumul_prop `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | cumul_refl t u :
    is_closed_context Γ ->
    is_open_term Γ t ->
    is_open_term Γ u ->
    eq_term_prop Σ.1 0 t u -> Σ ;;; Γ |- t ~~ u
  | cumul_red_l t u v :
    is_closed_context Γ ->
    is_open_term Γ t ->
    is_open_term Γ u ->
    is_open_term Γ v ->
    red1 Σ.1 Γ t v -> Σ ;;; Γ |- v ~~ u -> Σ ;;; Γ |- t ~~ u
  | cumul_red_r t u v :
    is_closed_context Γ ->
    is_open_term Γ t ->
    is_open_term Γ u ->
    is_open_term Γ v ->
    Σ ;;; Γ |- t ~~ v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t ~~ u

where " Σ ;;; Γ |- t ~~ u " := (cumul_prop Σ Γ t u) : type_scope.

Lemma eq_term_prop_impl Σ cmp_universe cmp_sort pb napp t u :
  RelationClasses.subrelation (cmp_sort Conv) eq_univ_prop ->
  RelationClasses.subrelation (cmp_sort pb) eq_univ_prop ->
  PCUICEquality.eq_term_upto_univ_napp Σ.1 cmp_universe cmp_sort pb napp t u ->
  eq_term_prop Σ napp t u.
Proof using Type.
  intros hsub_conv hsub_pb.
  eapply PCUICEquality.eq_term_upto_univ_impl.
  all:auto.
  all: now intros ??.
Qed.

#[global]
Instance subrelation_compare_sort_eq_prop φ pb :
  RelationClasses.subrelation (compare_sort φ pb) eq_univ_prop.
Proof using Type.
  intros s s'.
  destruct pb, s, s' => //=.
Qed.

Lemma eq_term_eq_term_prop_impl Σ φ pb napp t u :
  compare_term_napp Σ φ pb napp t u ->
  eq_term_prop Σ napp t u.
Proof using Type.
  eapply eq_term_prop_impl.
  all: apply subrelation_compare_sort_eq_prop.
Qed.

Lemma cumul_pb_cumul_prop Σ Γ pb A B :
  Σ ;;; Γ ⊢ A ≤[pb] B ->
  Σ ;;; Γ |- A ~~ B.
Proof using Type.
  induction 1.
  - constructor => //. now apply eq_term_eq_term_prop_impl in c.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma cumul_prop_alt {Σ : global_env_ext} {Γ T U} {wfΣ : wf Σ} :
  Σ ;;; Γ |- T ~~ U <~>
  ∑ nf nf', [× Σ ;;; Γ ⊢ T ⇝ nf, Σ ;;; Γ ⊢ U ⇝ nf' & eq_term_prop Σ 0 nf nf'].
Proof using Type.
  split.
  - induction 1.
    exists t, u. intuition pcuic.
    destruct IHX as [nf [nf' [redl redr eq]]].
    exists nf, nf'; split; pcuic.
    eapply into_closed_red; eauto.
    transitivity v; auto. apply redl.
    destruct IHX as [nf [nf' [redl redr eq]]].
    exists nf, nf'; split; pcuic.
    transitivity v; auto.
    apply into_closed_red; auto.
  - intros [nf [nf' [redv redv' eq]]].
    assert (clnf := closed_red_open_right redv).
    assert (clnf' := closed_red_open_right redv').
    destruct redv as [clsrc clT redv]. destruct redv' as [clsrc' clU redv'].
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** epose proof (red1_is_open_term _ _ r clsrc clU).
       econstructor 3; eauto.
    * epose proof (red1_is_open_term _ _ r clsrc clT).
      econstructor 2; eauto.
Qed.

Lemma cumul_prop_sort {Σ Γ s s'} {wfΣ : wf Σ} :
  Σ ;;; Γ |- tSort s ~~ tSort s' ->
  eq_univ_prop s s'.
Proof.
  intros equiv.
  eapply cumul_prop_alt in equiv as [nf [nf' [redl redr eq]]].
  eapply invert_red_sort in redl. apply invert_red_sort in redr.
  subst.
  now depelim eq.
Qed.

Lemma cumul_prop_props {Σ Γ u u'} {wfΣ : wf Σ}:
  Sort.is_prop u ->
  Σ ;;; Γ |- tSort u ~~ tSort u' ->
  Sort.is_prop u'.
Proof using Hcf.
  move => isp /cumul_prop_sort. move: isp.
  destruct u, u' => //=. cbn. rewrite Hcf //.
Qed.

Lemma cumul_sprop_props {Σ Γ u u'} {wfΣ : wf Σ} :
  Sort.is_sprop u ->
  Σ ;;; Γ |- tSort u ~~ tSort u' ->
  Sort.is_sprop u'.
Proof using Type.
  move => isp /cumul_prop_sort. move: isp.
  destruct u, u' => //.
Qed.

Instance refl_eq_univ_prop : RelationClasses.Reflexive eq_univ_prop.
Proof using Type.
  now intros [].
Qed.

Instance sym_eq_univ_prop : RelationClasses.Symmetric eq_univ_prop.
Proof using Type.
  now intros [] [].
Qed.

Instance trans_eq_univ_prop : RelationClasses.Transitive eq_univ_prop.
Proof using Type.
  now intros [] [] [].
Qed.

#[global]
Instance equiv_eq_univ_prop : RelationClasses.Equivalence eq_univ_prop.
Proof using Type.
  split; exact _.
Qed.

#[global]
Instance equiv_True {T} : @RelationClasses.Equivalence T (fun _ _ => True).
Proof using Type.
  split; auto.
Qed.

#[global]
Instance subrel_R_True {T} R : @RelationClasses.subrelation T R (fun _ _ => True).
Proof.
  now intros ??.
Qed.

#[global]
Instance substu_f_True {T} `{UnivSubst T} f : SubstUnivPreserving f (fun _ _ => True).
Proof using Type.
  now intros ???.
Qed.

#[global]
Instance substu_True_eq_univ_prop : SubstUnivPreserving (fun _ _ => True) eq_univ_prop.
Proof using Type.
  now intros []???.
Qed.

Lemma LevelExprSet_For_all (P : LevelExpr.t -> Prop) (u : Universe.t) :
  LevelExprSet.For_all P u <->
  Forall P (LevelExprSet.elements u).
Proof using Type.
  pose proof (Universe.to_nonempty_list_spec u).
  pose proof (Universe.to_nonempty_list_spec' u).
  rewrite (Universe.For_all_exprs P u).
  destruct (Universe.to_nonempty_list u). rewrite -H. simpl.
  split.
  - constructor; intuition.
  - intros H'; inv H'; intuition.
Qed.

Lemma univ_expr_set_in_elements e s :
  LevelExprSet.In e s <-> In e (LevelExprSet.elements s).
Proof using Type.
  rewrite -LevelExprSet.elements_spec1. generalize (LevelExprSet.elements s).
  now eapply InA_In_eq.
Qed.

Lemma univ_epxrs_elements_map g s :
  forall e, In e (LevelExprSet.elements (Universe.map g s)) <->
      In e (map g (LevelExprSet.elements s)).
Proof using Type.
  intros e.
  rewrite -Universe.In_elements Universe.map_spec in_map_iff; setoid_rewrite <- Universe.In_elements.
  firstorder.
Qed.

Lemma Forall_elements_in P s : Forall P (LevelExprSet.elements s) <->
  (forall x, LevelExprSet.In x s -> P x).
Proof using Type.
  setoid_rewrite univ_expr_set_in_elements.
  generalize (LevelExprSet.elements s).
  intros.
  split; intros.
  induction H; depelim H0; subst => //; auto.
  induction l; constructor; auto.
  apply H. repeat constructor.
  apply IHl. intros x inxl. apply H. right; auto.
Qed.

Lemma univ_exprs_map_all P g s :
  Forall P (LevelExprSet.elements (Universe.map g s)) <->
  Forall (fun x => P (g x)) (LevelExprSet.elements s).
Proof using Type.
  rewrite !Forall_elements_in.
  setoid_rewrite Universe.map_spec.
  intuition auto.
  eapply H. now exists x.
  destruct H0 as [e' [ins ->]]. apply H; auto.
Qed.

Lemma expr_set_forall_map f g s :
  LevelExprSet.for_all f (Universe.map g s) <->
  LevelExprSet.for_all (fun e => f (g e)) s.
Proof using Type.
  rewrite /is_true !LevelExprSet.for_all_spec !LevelExprSet_For_all.
  apply univ_exprs_map_all.
Qed.

(* Lemma is_prop_subst_level_expr u1 u2 s :
  Forall2 (fun x y : Level.t => eq_univ_prop (Universe.make x) (Universe.make y)) u1 u2  ->
  LevelExpr.is_prop (subst_instance_level_expr u1 s) = LevelExpr.is_prop (subst_instance_level_expr u2 s).
Proof.
  intros hu. destruct s; simpl; auto.
  destruct e as [[] ?]; simpl; auto.
  destruct (nth_error u1 n) eqn:E.
  eapply Forall2_nth_error_Some_l in hu; eauto.
  destruct hu as [t' [-> eq]].
  red in eq. rewrite !univ_is_prop_make in eq.
  eapply eq_iff_eq_true in eq.
  destruct t, t'; simpl in eq => //.
  eapply Forall2_nth_error_None_l in hu; eauto.
  now rewrite hu.
Qed. *)

Lemma cumul_prop_sym Σ Γ T U :
  wf Σ.1 ->
  Σ ;;; Γ |- T ~~ U ->
  Σ ;;; Γ |- U ~~ T.
Proof using Type.
  intros wfΣ Hl.
  eapply cumul_prop_alt in Hl as [t' [u' [tt' uu' eq]]].
  eapply cumul_prop_alt.
  exists u', t'; split; auto.
  now symmetry.
Qed.

Lemma cumul_prop_trans Σ Γ T U V :
  wf Σ ->
  Σ ;;; Γ |- T ~~ U ->
  Σ ;;; Γ |- U ~~ V ->
  Σ ;;; Γ |- T ~~ V.
Proof using Type.
  intros wfΣ Hl Hr.
  eapply cumul_prop_alt in Hl as [t' [u' [tt' uu' eq]]].
  eapply cumul_prop_alt in Hr as [u'' [v' [uu'' vv' eq']]].
  eapply cumul_prop_alt.
  destruct (closed_red_confluence uu' uu'') as [u'nf [ul ur]].
  destruct ul as [? ? ul]. destruct ur as [? ? ur].
  eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; tc.
  eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; tc.
  exists tnf, unf.
  split; auto.
  - transitivity t' => //. eapply into_closed_red; auto. fvs.
  - transitivity v' => //. eapply into_closed_red; auto; fvs.
  - now transitivity u'nf.
Qed.

Global Instance cumul_prop_transitive Σ Γ : wf Σ -> CRelationClasses.Transitive (cumul_prop Σ Γ).
Proof using Type. intros. red. intros. now eapply cumul_prop_trans. Qed.

Lemma cumul_prop_cumul_pb_l {Σ Γ pb A T B} {wfΣ : wf_ext Σ} :
  Σ ;;; Γ |- A ~~ T ->
  Σ ;;; Γ ⊢ A ≤[pb] B ->
  Σ ;;; Γ |- B ~~ T.
Proof using Type.
  intros HT cum.
  eapply cumul_pb_cumul_prop in cum; auto.
  etransitivity ; eauto.
  eapply cumul_prop_sym; eauto.
Qed.

Lemma cumul_prop_cum_pb_r {Σ Γ pb A T B} {wfΣ : wf_ext Σ} :
  Σ ;;; Γ |- A ~~ T ->
  Σ ;;; Γ ⊢ B ≤[pb] A ->
  Σ ;;; Γ |- B ~~ T.
Proof using Type.
  intros HT cum.
  eapply cumul_pb_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
Qed.

Definition conv_decls_prop (Σ : global_env_ext) (Γ Γ' : context) (c d : context_decl) :=
  match decl_body c, decl_body d with
  | None, None => True
  | Some b, Some b' => b = b'
  | _, _ => False
  end.

Notation conv_ctx_prop Σ := (All2_fold (conv_decls_prop Σ)).

Lemma conv_ctx_prop_refl Σ Γ :
  conv_ctx_prop Σ Γ Γ.
Proof using Type.
  induction Γ as [|[na [b|] ty]]; constructor; eauto => //.
Qed.

Lemma conv_ctx_prop_app Σ Γ Γ' Δ :
  conv_ctx_prop Σ Γ Γ' ->
  conv_ctx_prop Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof using Type.
  induction Δ; simpl; auto.
  destruct a as [na  [b|] ty]; intros; constructor => //.
  now eapply IHΔ.
  now eapply IHΔ.
Qed.

Lemma red1_upto_conv_ctx_prop Σ Γ Γ' t t' :
  red1 Σ.1 Γ t t' ->
  conv_ctx_prop Σ Γ Γ' ->
  red1 Σ.1 Γ' t t'.
Proof using Type.
  intros Hred; induction Hred using red1_ind_all in Γ' |- *;
    try solve [econstructor; eauto; try solve [solve_all]].
  - econstructor. destruct (nth_error Γ i) eqn:eq; simpl in H => //.
    noconf H; simpl in H; noconf H.
    eapply All2_fold_nth in X; eauto.
    destruct X as [d' [Hnth [ctxrel cp]]].
    red in cp. rewrite H in cp. rewrite Hnth /=.
    destruct (decl_body d'); subst => //.
  - econstructor. eapply IHHred. constructor; simpl; auto => //.
  - econstructor. eapply IHHred. constructor; simpl => //.
  - intros h. constructor.
    eapply IHHred. now apply conv_ctx_prop_app.
  - intros h; constructor.
    eapply OnOne2_impl; tea => /= br br'.
    intros [red IH].
    split=> //. now eapply red, conv_ctx_prop_app.
  - intros. constructor; eapply IHHred; constructor; simpl; auto => //.
  - intros. eapply fix_red_body. solve_all.
    eapply b0. now eapply conv_ctx_prop_app.
  - intros. eapply cofix_red_body. solve_all.
    eapply b0. now eapply conv_ctx_prop_app.
Qed.

Lemma closed_red1_upto_conv_ctx_prop Σ Γ Γ' t t' :
  is_closed_context Γ' ->
  Σ ;;; Γ ⊢ t ⇝1 t' ->
  conv_ctx_prop Σ Γ Γ' ->
  Σ ;;; Γ' ⊢ t ⇝1 t'.
Proof using Type.
  intros clΓ' [] conv.
  eapply red1_upto_conv_ctx_prop in clrel_rel; eauto.
  split; auto.
  now rewrite -(All2_fold_length conv).
Qed.

Lemma red_upto_conv_ctx_prop Σ Γ Γ' t t' :
  red Σ.1 Γ t t' ->
  conv_ctx_prop Σ Γ Γ' ->
  red Σ.1 Γ' t t'.
Proof using Type.
  intros Hred. intros convctx.
  induction Hred; eauto.
  constructor. now eapply red1_upto_conv_ctx_prop.
  eapply rt_trans; eauto.
Qed.

Lemma closed_red_upto_conv_ctx_prop Σ Γ Γ' t t' :
  is_closed_context Γ' ->
  Σ ;;; Γ ⊢ t ⇝ t' ->
  conv_ctx_prop Σ Γ Γ' ->
  Σ ;;; Γ' ⊢ t ⇝ t'.
Proof using Type.
  intros clΓ' [] conv.
  eapply red_upto_conv_ctx_prop in clrel_rel; eauto.
  split; auto.
  now rewrite -(All2_fold_length conv).
Qed.

Lemma cumul_prop_prod_inv {Σ Γ na A B na' A' B'} {wfΣ : wf Σ} :
  Σ ;;; Γ |- tProd na A B ~~ tProd na' A' B' ->
  Σ ;;; Γ ,, vass na A |- B ~~ B'.
Proof using Type.
  intros H; eapply cumul_prop_alt in H as [nf [nf' [redv redv' eq]]].
  eapply invert_red_prod in redv as (? & ? & [? ? ?]).
  eapply invert_red_prod in redv' as (? & ? & [? ? ?]).
  subst. all:auto.
  eapply cumul_prop_alt.
  exists x0, x2. split; auto.
  eapply closed_red_upto_conv_ctx_prop; eauto. fvs.
  constructor; auto => //. apply conv_ctx_prop_refl.
  depelim eq. apply eq2.
Qed.

Lemma substitution_untyped_cumul_prop {Σ Γ Δ Γ' s M N} {wfΣ : wf Σ} :
  forallb (is_open_term Γ) s ->
  untyped_subslet Γ s Δ ->
  Σ ;;; (Γ ,,, Δ ,,, Γ') |- M ~~ N ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~~ (subst s #|Γ'| N).
Proof using Type.
  intros cls subs Hcum.
  eapply cumul_prop_alt in Hcum as [nf [nf' [redl redr eq']]].
  eapply closed_red_untyped_substitution in redl; eauto.
  eapply closed_red_untyped_substitution in redr; eauto.
  eapply cumul_prop_alt.
  eexists _, _; split; eauto.
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  eapply All2_refl.
  intros x. eapply PCUICEquality.eq_term_upto_univ_refl; typeclasses eauto.
Qed.

Lemma substitution_cumul_prop {Σ Γ Δ Γ' s M N} {wfΣ : wf Σ} :
  subslet Σ Γ s Δ ->
  Σ ;;; (Γ ,,, Δ ,,, Γ') |- M ~~ N ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~~ (subst s #|Γ'| N).
Proof using Type.
  intros subs Hcum.
  eapply substitution_untyped_cumul_prop; tea.
  now eapply subslet_open in subs.
  now eapply subslet_untyped_subslet.
Qed.

Lemma substitution_untyped_cumul_prop_equiv {Σ Γ Δ Γ' s s' M} {wfΣ : wf Σ} :
  is_closed_context (Γ ,,, Δ ,,, Γ') ->
  forallb (is_open_term Γ) s ->
  forallb (is_open_term Γ) s' ->
  is_open_term (Γ ,,, Δ ,,, Γ') M ->
  #|s| = #|Δ| -> #|s'| = #|Δ| ->
  All2 (eq_term_prop Σ.1 0) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~~ (subst s' #|Γ'| M).
Proof using Type.
  intros clctx cls cls' clM lens_ lens' Heq.
  constructor.
  { eapply is_closed_subst_context; tea. }
  { eapply is_open_term_subst; tea. }
  { relativize #|Γ ,,, _|. eapply is_open_term_subst; tea. len. }
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  reflexivity.
Qed.

Lemma cumul_prop_args {Σ Γ args args'} {wfΣ : wf_ext Σ} :
  All2 (cumul_prop Σ Γ) args args' ->
  ∑ nf nf', [× All2 (closed_red Σ Γ) args nf, All2 (closed_red Σ Γ) args' nf' &
    All2 (eq_term_prop Σ 0) nf nf'].
Proof using Type.
  intros a.
  induction a. exists [], []; intuition auto.
  destruct IHa as (nfa & nfa' & [redl redr eq]).
  eapply cumul_prop_alt in r as (nf & nf' & [redl' redr' eq'']).
  exists (nf :: nfa), (nf' :: nfa'); intuition auto.
Qed.

Lemma is_closed_context_snoc_inv Γ d : is_closed_context (d :: Γ) ->
  is_closed_context Γ /\ closed_decl #|Γ| d.
Proof using Type.
  rewrite on_free_vars_ctx_snoc.
  move/andP => []; split; auto.
  unfold ws_decl in b. destruct d as [na [bod|] ty]; cbn in *; auto.
  move/andP: b => /= [] clb clt.
  unfold closed_decl. cbn.
  now rewrite !closedP_on_free_vars clb clt.
  now rewrite closedP_on_free_vars.
Qed.

Lemma red_conv_prop {Σ Γ T U} {wfΣ : wf_ext Σ} :
  Σ ;;; Γ ⊢ T ⇝ U ->
  Σ ;;; Γ |- T ~~ U.
Proof using Type.
  move/(red_ws_cumul_pb (pb:=Conv)).
  now apply cumul_pb_cumul_prop.
Qed.

Lemma substitution_red_terms_conv_prop {Σ Γ Δ Γ' s s' M} {wfΣ : wf_ext Σ} :
  is_closed_context (Γ ,,, Δ ,,, Γ') ->
  is_open_term (Γ ,,, Δ ,,, Γ') M ->
  untyped_subslet Γ s Δ ->
  red_terms Σ Γ s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~~ (subst s' #|Γ'| M).
Proof using Type.
  intros.
  apply red_conv_prop.
  eapply closed_red_red_subst; tea.
Qed.

Lemma context_conversion_cumul_prop {Σ Γ Δ M N} {wfΣ : wf_ext Σ} :
  Σ ;;; Γ |- M ~~ N ->
  Σ ⊢ Γ = Δ ->
  Σ ;;; Δ |- M ~~ N.
Proof using Type.
  induction 1; intros.
  - constructor => //. eauto with fvs. now rewrite -(All2_fold_length X).
    now rewrite -(All2_fold_length X).
  - specialize (IHX X0). transitivity v => //.
    eapply red1_red in r.
    assert (Σ ;;; Γ ⊢ t ⇝ v) by (now apply into_closed_red).
    symmetry in X0.
    eapply conv_red_conv in X1. 2:exact X0.
    3:{ eapply ws_cumul_pb_refl. fvs. now rewrite (All2_fold_length X0). }
    2:{ eapply closed_red_refl. fvs. now rewrite (All2_fold_length X0). }
    symmetry in X1. now eapply cumul_pb_cumul_prop.
  - specialize (IHX X0). transitivity v => //.
    eapply red1_red in r.
    assert (Σ ;;; Γ ⊢ u ⇝ v) by (now apply into_closed_red).
    symmetry in X0.
    eapply conv_red_conv in X1. 2:exact X0.
    3:{ eapply ws_cumul_pb_refl. fvs. now rewrite (All2_fold_length X0). }
    2:{ eapply closed_red_refl. fvs. now rewrite (All2_fold_length X0). }
    symmetry in X1. now eapply cumul_pb_cumul_prop.
Qed.

(** Note: a more general version involving substitution in an extended context Γ ,,, Δ would be
  harder as it requires a more involved proof about reduction being "preserved" when converting contexts using
  cumul_prop rather than standard conversion.
*)
Lemma substitution_untyped_cumul_prop_cumul {Σ Γ Δ Δ' s s' M} {wfΣ : wf_ext Σ} :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  is_open_term (Γ ,,, Δ) M ->
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ' ->
  All2 (cumul_prop Σ Γ) s s' ->
  Σ ;;; Γ |- subst0 s M ~~ subst0 s' M.
Proof using Type.
  intros clctx clctx' clM subs subs' Heq.
  assert (lens' := All2_length Heq).
  destruct (cumul_prop_args Heq) as (nf & nf' & [redl redr eq]) => //.
  transitivity (subst0 nf M).
  * eapply (substitution_red_terms_conv_prop (Γ':=[])). 3:tea. all:tea.
  * transitivity (subst0 nf' M).
    constructor.
    - rewrite on_free_vars_ctx_app in clctx. now move/andP: clctx.
    - eapply (is_open_term_subst (Γ' := [])). apply clctx.
      eapply closed_red_terms_open_right in redl. solve_all.
      now rewrite -(All2_length redl) -(untyped_subslet_length subs). apply clM.
    - eapply (is_open_term_subst (Γ' := [])). apply clctx.
      eapply closed_red_terms_open_right in redr. solve_all.
      now rewrite -(All2_length redr) -(untyped_subslet_length subs). apply clM.
    - eapply PCUICEquality.eq_term_upto_univ_substs => //. reflexivity.
    - eapply cumul_prop_sym; auto.
      eapply (substitution_red_terms_conv_prop (Γ':=[])). 3:tea. all:tea.
      len. len in clM. now rewrite -(untyped_subslet_length subs') -lens' (untyped_subslet_length subs).
Qed.

Lemma substitution1_untyped_cumul_prop {Σ Γ na t u M N} {wfΣ : wf Σ.1} :
  is_open_term Γ u ->
  Σ ;;; (Γ ,, vass na t) |- M ~~ N ->
  Σ ;;; Γ |- M {0 := u} ~~ N {0 := u}.
Proof using Type.
  intros clu Hcum.
  eapply (substitution_untyped_cumul_prop (Δ := [_]) (Γ' := [])) in Hcum; cbn; eauto.
  cbn; rewrite clu //.
  repeat constructor.
Qed.

Lemma cmp_True_subst_instance Σ univs u u' (i : Instance.t) :
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  cmp_universe_instance (fun _ _ => True) (subst_instance u i) (subst_instance u' i).
Proof using Type.
  intros wfΣ cu cu'. red.
  eapply All2_Forall2, All2_map, All2_refl => ui.
  unfold on_rel. auto.
Qed.

Lemma cumul_prop_subst_instance {Σ Γ univs u u' T} {wfΣ : wf Σ} :
  is_closed_context Γ ->
  is_open_term Γ T ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  Σ ;;; Γ |- subst_instance u T ~~ subst_instance u' T.
Proof using Type.
  intros clΓ clT cu cu'.
  eapply cumul_prop_alt.
  enough (∑ nf nf' : term,
    [× red Σ Γ T@[u] nf, red Σ Γ T@[u'] nf' & eq_term_prop Σ 0 nf nf']).
  { destruct X as [nf [nf' [r r' e]]]. exists nf, nf'. split; try constructor; auto; fvs. }
  eexists _, _; split; intuition auto. clear clΓ clT.
  induction T using PCUICInduction.term_forall_list_ind; cbn; intros;
    try solve [constructor; eauto; solve_all].
  - cbn. constructor.
    destruct s; split; reflexivity.
  - constructor. eapply PCUICEquality.eq_term_upto_univ_impl in IHT1; eauto.
    all:try typeclasses eauto.
    apply IHT2.
  - constructor. now eapply cmp_True_subst_instance.
  - constructor. now eapply cmp_instance_opt_variance, cmp_True_subst_instance.
  - constructor. now eapply cmp_instance_opt_variance, cmp_True_subst_instance.
  - cbn. constructor. splits; simpl; solve_all.
    eapply cmp_True_subst_instance; tea. reflexivity.
    apply IHT.
    eapply All2_map.
    eapply All_All2; tea. cbn. unfold eq_branch.
    intuition auto. rewrite /id. reflexivity.
  - constructor. unfold eq_mfixpoint.
    eapply All2_map. eapply All_All2; tea.
    cbn. intros d [].
    intuition eauto.
  - constructor. unfold eq_mfixpoint.
    eapply All2_map. eapply All_All2; tea.
    cbn. intros d [].
    intuition eauto.
  - cbn. constructor; splits; simpl.
    destruct p as [? []]; constructor; cbn in *; intuition eauto.
    solve_all.
Qed.

Lemma cmp_True_instance Σ univs u u' :
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  cmp_universe_instance (fun _ _ => True) u u'.
Proof using Type.
  intros wfΣ cu cu'.
  destruct univs; simpl in *.
  - destruct u, u' => //=.
  - apply Forall2_triv.
    destruct cu as (_ & ? & _).
    destruct cu' as (_ & ? & _).
    congruence.
Qed.

Lemma untyped_subslet_inds Γ ind u u' mdecl :
  untyped_subslet Γ (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance u' (arities_context (ind_bodies mdecl))).
Proof using Type Hcf cf.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4.
  unfold inds.
  induction l using rev_ind; simpl; first constructor.
  simpl. rewrite length_app /= => Hlen.
  unfold arities_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=.
  rewrite /= Nat.add_1_r /=.
  constructor.
  rewrite -rev_map_spec. apply IHl. lia.
Qed.

Hint Resolve conv_ctx_prop_refl : core.

Lemma cumul_prop_tProd {Σ : global_env_ext} {Γ na t ty na' t' ty'} {wfΣ : wf_ext Σ} :
  eq_binder_annot na na' ->
  eq_term Σ.1 Σ t t' ->
  Σ ;;; Γ ,, vass na t |- ty ~~ ty' ->
  Σ ;;; Γ |- tProd na t ty ~~ tProd na' t' ty'.
Proof using Type.
  intros eqann eq cum.
  eapply cumul_prop_alt in cum as (nf & nf' & [redl redr eq']).
  eapply cumul_prop_alt. eexists (tProd na t nf), (tProd na' t' nf'); split; eauto.
  - eapply closed_red_prod_codom; auto.
  - eapply clrel_ctx in redl.
    move: redl; rewrite on_free_vars_ctx_snoc /= => /andP[]; rewrite /on_free_vars_decl /test_decl /= => onΓ ont.
    have clt' : is_open_term Γ t'.
    eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars in eq; tea.
    eapply closed_red_prod; auto.
    now eapply closed_red_refl.
    eapply closed_red_upto_conv_ctx_prop; eauto.
    now rewrite on_free_vars_ctx_snoc /= onΓ.
    repeat (constructor; auto).
  - repeat (constructor; auto).
    eapply eq_term_eq_term_prop_impl; eauto.
Qed.

Lemma cumul_prop_tLetIn (Σ : global_env_ext) {Γ na t d ty na' t' d' ty'} {wfΣ : wf_ext Σ} :
  eq_binder_annot na na' ->
  eq_term Σ.1 Σ t t' ->
  eq_term Σ.1 Σ d d' ->
  Σ ;;; Γ ,, vdef na d t |- ty ~~ ty' ->
  Σ ;;; Γ |- tLetIn na d t ty ~~ tLetIn na' d' t' ty'.
Proof using Type.
  intros eqann eq eq' cum.
  eapply cumul_prop_alt in cum as (nf & nf' & [redl redr eq'']).
  eapply cumul_prop_alt.
  assert(eq_context Σ Σ (Γ ,, vdef na d t) (Γ ,, vdef na' d' t')).
  { repeat constructor; pcuic. eapply eq_context_upto_refl; typeclasses eauto. }
  eapply (closed_red_eq_context_upto_l (pb:=Conv)) in redr; eauto.
  2:{ eapply clrel_ctx in redl. rewrite !on_free_vars_ctx_snoc in redl |- *.
      move/andP: redl => [] -> /= /andP[] cld clt.
      eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars in cld; tea.
      eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars in clt; tea.
      rewrite /on_free_vars_decl /test_decl /=.
      now rewrite cld clt. }
  destruct redr as [v' [redv' eq''']].
  eexists (tLetIn na d t nf), (tLetIn na' d' t' v'); split.
  - now eapply closed_red_letin_body.
  - now eapply closed_red_letin_body.
  - constructor; eauto.
    eapply eq_term_eq_term_prop_impl; eauto.
    eapply eq_term_eq_term_prop_impl; eauto.
    transitivity nf'. auto. now eapply eq_term_eq_term_prop_impl.
Qed.

Lemma cumul_prop_mkApps {Σ Γ f args f' args'} {wfΣ : wf_ext Σ} :
  is_closed_context Γ ->
  is_open_term Γ f ->
  is_open_term Γ f' ->
  eq_term Σ.1 Σ f f' ->
  All2 (cumul_prop Σ Γ) args args' ->
  Σ ;;; Γ |- mkApps f args ~~ mkApps f' args'.
Proof using Type Hcf cf.
  intros clΓ clf clf' eq eq'.
  eapply cumul_prop_alt.
  eapply cumul_prop_args in eq' as (nf & nf' & [redl redr eq']).
  exists (mkApps f nf), (mkApps f' nf'); split.
  - eapply closed_red_mkApps; auto.
  - eapply closed_red_mkApps; auto.
  - eapply eq_term_upto_univ_mkApps.
    eapply eq_term_upto_univ_impl.
    6:eapply eq. 5: lia.
    all: tc.
    auto.
Qed.

Hint Resolve closed_red_open_right : fvs.

Lemma red_cumul_prop {Σ Γ} {wfΣ : wf Σ} :
  CRelationClasses.subrelation (closed_red Σ Γ) (cumul_prop Σ Γ).
Proof using Type.
  intros x y r. eapply cumul_prop_alt. exists y, y.
  split; fvs. eapply closed_red_refl; fvs. apply eq_term_upto_univ_refl; typeclasses eauto.
Qed.

Lemma eq_term_prop_mkApps_inv {Σ ind u args ind' u' args'} {wfΣ : wf_ext Σ} :
  forall n, eq_term_prop Σ n (mkApps (tInd ind u) args) (mkApps (tInd ind' u') args') ->
  All2 (eq_term_prop Σ 0) args args'.
Proof using Type.
  revert args'.
  induction args using rev_ind; intros args' n; simpl.
  intros H; destruct args' using rev_case.
  constructor.
  depelim H. solve_discr. eapply app_eq_nil in H1 as [_ H]. congruence.
  intros H.
  destruct args' using rev_case. depelim H. solve_discr.
  apply app_eq_nil in H1 as [_ H]; discriminate.
  rewrite !mkApps_app /= in H. depelim H.
  eapply All2_app => //.
  eapply IHargs; eauto. repeat constructor.
  red. apply H0.
Qed.

Lemma cumul_prop_mkApps_Ind_inv {Σ Γ ind u args ind' u' args'} {wfΣ : wf_ext Σ} :
  Σ ;;; Γ |- mkApps (tInd ind u) args ~~ mkApps (tInd ind' u') args' ->
  All2 (cumul_prop Σ Γ) args args'.
Proof using Type.
  intros eq.
  eapply cumul_prop_alt in eq as (nf & nf' & [redl redr eq']).
  eapply invert_red_mkApps_tInd in redl as [args'' [-> clΓ eqargs]].
  eapply invert_red_mkApps_tInd in redr as [args''' [-> _ eqargs']].
  eapply All2_trans. typeclasses eauto.
  eapply All2_impl; eauto. eapply red_cumul_prop.
  eapply All2_trans. typeclasses eauto.
  2:{ eapply All2_symP. intros x y H; now eapply cumul_prop_sym.
      eapply All2_impl; eauto. eapply red_cumul_prop. }
  eapply eq_term_prop_mkApps_inv in eq' => //.
  eapply closed_red_terms_open_right in eqargs.
  eapply closed_red_terms_open_right in eqargs'.
  solve_all. constructor; auto.
Qed.

Global Instance cumul_prop_sym' Σ Γ : wf Σ.1 -> CRelationClasses.Symmetric (cumul_prop Σ Γ).
Proof using Type.
  now intros wf x y; eapply cumul_prop_sym.
Qed.

Notation eq_term_napp Σ n x y :=
  (eq_term_upto_univ_napp Σ (eq_sort Σ) (eq_sort Σ) n x y).

Notation leq_term_napp Σ n x y :=
    (eq_term_upto_univ_napp Σ (eq_sort Σ) (leq_sort Σ) n x y).

Lemma cumul_prop_is_open {Σ Γ T U} :
  Σ ;;; Γ |- T ~~ U ->
  [× is_closed_context Γ, is_open_term Γ T & is_open_term Γ U].
Proof using Type.
  induction 1; split; auto.
Qed.

Lemma is_closed_context_weaken {Γ Δ} :
  is_closed_context Γ ->
  is_closed_context Δ ->
  is_closed_context (Γ ,,, Δ).
Proof using Type.
  rewrite on_free_vars_ctx_app => -> /=.
  eapply on_free_vars_ctx_impl. discriminate.
Qed.

(** Well-typed terms in the leq_term relation live in the same sort hierarchy. *)
Lemma typing_leq_term_prop_gen :
  env_prop
    (fun Σ Γ t T =>
      forall t' T' : term,
      on_udecl Σ.1 Σ.2 ->
      Σ ;;; Γ |- t' : T' ->
      forall pb n, compare_term_napp Σ Σ pb n t' t ->
      Σ ;;; Γ |- T ~~ T')%type
    (fun Σ Γ j => on_udecl Σ.1 Σ.2 ->
      lift_typing0 (fun t T =>
      forall t' T' : term,
      Σ ;;; Γ |- t' : T' ->
      forall pb n, compare_term_napp Σ Σ pb n t' t ->
      Σ ;;; Γ |- T ~~ T') j)
    (fun Σ Γ => wf_local Σ Γ).
Proof using Type Hcf cf.
  eapply typing_ind_env.
  { intros ???? H ?. apply lift_typing_impl with (1 := H) => ?? [] ?? ?? //. eauto. }
  1: now auto.

  all: intros Σ wfΣ Γ wfΓ; intros.

  1-13:match goal with
  [ H : compare_term_napp _ _ _ _ _ _ |- _ ] => depelim H
  end; assert (wf_ext Σ) by (split; assumption).

  15:{ assert (wf_ext Σ) by (split; assumption). specialize (X1 _ _ H X5 _ _ X6).
       eapply cumul_prop_cumul_pb_l; tea.
       eapply cumulSpec_cumulAlgo_curry in X4; tea; fvs. }

  6:{ eapply inversion_App in X6 as (na' & A' & B' & hf & ha & cum); auto.
      specialize (X3 _ _ H hf _ _ X7_1).
      specialize (X5 _ _ H ha _ _ X7_2).
      eapply cumul_pb_cumul_prop in cum; auto.
      transitivity (B' {0 := u0}) => //.
      eapply cumul_prop_prod_inv in X3 => //.
      transitivity (B' {0 := u}).
      eapply substitution1_untyped_cumul_prop in X3. eapply X3.
      now eapply subject_is_open_term.
      destruct (cumul_prop_is_open cum).
      constructor; auto. eapply on_free_vars_subst => /= //.
      eapply subject_is_open_term in X4. now rewrite X4.
      rewrite shiftnP_add. now eapply cumul_prop_is_open in X3 as [].
      eapply eq_term_eq_term_prop_impl => //.
      eapply PCUICEquality.eq_term_upto_univ_substs.
      all: try reflexivity.
      constructor. 2:constructor. now symmetry. }

  - eapply inversion_Rel in X0 as [decl' [wfΓ' [Hnth Hcum]]]; auto.
    rewrite Hnth in H; noconf H. now eapply cumul_pb_cumul_prop in Hcum.

  - eapply inversion_Sort in X0 as [wf [wfs Hs]]; auto.
    apply subrelation_compare_sort_eq_prop in c => //.
    apply cumul_pb_cumul_prop in Hs => //.
    eapply cumul_prop_trans; eauto.
    destruct (cumul_prop_is_open Hs) as [].
    constructor => //. constructor. rewrite /eq_univ_prop !Sort.sType_super //.

  - eapply inversion_Prod in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 H). apply unlift_TypUniv in X1, Ha.
    specialize (X1 _ _ Ha _ _ X5_1).
    eapply context_conversion in Hb.
    3:{ constructor. apply conv_ctx_refl. constructor. eassumption.
      constructor. eauto. }
    2:{ pcuic. }
    specialize (X3 _ _ H Hb _ _ X5_2).
    eapply cumul_pb_cumul_prop in Hs => //.
    eapply cumul_prop_trans; eauto.
    constructor; fvs. constructor.
    apply cumul_prop_sort in X1, X3. move: X1 X3. clear.
    unfold eq_univ_prop.
    destruct s2, s2' => //=.
    all: destruct s1, s1' => //=.

  - eapply inversion_Lambda in X4 as (B & dom & bod & cum); tas.
    specialize (X3 t0 B H).
    assert(conv_context cumulAlgo_gen Σ (Γ ,, vass na0 ty) (Γ ,, vass na t)).
    { repeat constructor; pcuic. }
    forward X3 by eapply context_conversion; eauto; pcuic.
    specialize (X3 _ _ X5_2). eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_tProd; eauto. now symmetry. now symmetry.

  - eapply inversion_LetIn in X4 as (A & dombod & codom & cum); auto.
    assert(conv_context cumulAlgo_gen Σ (Γ ,, vdef na0 t ty) (Γ ,, vdef na b b_ty)).
    { repeat constructor; pcuic. }
    specialize (X3 u A H).
    forward X3 by eapply context_conversion; eauto; pcuic.
    specialize (X3 _ _ X5_3).
    eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_tLetIn; auto; now symmetry.

  - eapply inversion_Const in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    unshelve eapply declared_constant_to_gen in H, declc; eauto.
    pose proof (declared_constant_inj _ _ H declc); subst decl'.
    eapply cumul_prop_subst_instance; eauto. fvs.
    destruct (cumul_prop_is_open cum) as [].
    now rewrite on_free_vars_subst_instance in i0.

  - eapply inversion_Ind in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    unshelve eapply declared_inductive_to_gen in isdecl, declc; eauto.
    pose proof (declared_inductive_inj isdecl declc) as [-> ->].
    eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_subst_instance; tea. fvs.
    destruct (cumul_prop_is_open cum) as [].
    now rewrite on_free_vars_subst_instance in i0.

  - eapply inversion_Construct in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    unshelve eapply declared_constructor_to_gen in declc; eauto.
    unshelve epose proof (isdecl' := declared_constructor_to_gen isdecl); eauto.
    pose proof (declared_constructor_inj isdecl' declc) as [-> [-> ->]].
    eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    unfold type_of_constructor.
    have clars : is_closed_context (arities_context (ind_bodies mdecl))@[u].
    { eapply wf_local_closed_context. eapply (wf_arities_context_inst isdecl H). }
    have clty : is_open_term (Γ,,, arities_context (ind_bodies mdecl)) (cstr_type cdecl').
    { eapply closedn_on_free_vars, closed_upwards.
      eapply PCUICClosedTyp.declared_constructor_closed_gen_type; tea. len. }
    rewrite on_free_vars_ctx_subst_instance in clars.
    etransitivity.
    eapply (@substitution_untyped_cumul_prop_equiv _ Γ (subst_instance u (arities_context mdecl.(ind_bodies))) []); auto.
    * simpl.
      apply is_closed_context_weaken. fvs.
      now rewrite on_free_vars_ctx_subst_instance.
    * eapply on_free_vars_terms_inds.
    * eapply on_free_vars_terms_inds.
    * simpl.
      rewrite on_free_vars_subst_instance /=.
      len. len in clty.
    * len.
    * len.
    * induction (ind_bodies mdecl) in |- *; simpl; constructor; auto.
      constructor. simpl. eapply cmp_instance_opt_variance.
      eapply cmp_True_instance; eauto.
    * simpl.
      eapply (@substitution_untyped_cumul_prop _ Γ (subst_instance u0 (arities_context mdecl.(ind_bodies))) []) => //.
      eapply on_free_vars_terms_inds.
      eapply untyped_subslet_inds. simpl.
      eapply cumul_prop_subst_instance => //; eauto.
      eapply is_closed_context_weaken; fvs.
      len in clty; len.

  - eapply inversion_Case in X9 as (mdecl' & idecl' & isdecl' & indices' & data & cum); auto.
    eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto. simpl.
    clear X8.
    unshelve eapply declared_inductive_to_gen in isdecl, isdecl'; eauto.
    destruct (declared_inductive_inj isdecl isdecl'). subst.
    destruct data.
    specialize (X7 _ _ H6 scrut_ty _ _ X10).
    eapply cumul_prop_sym => //.
    destruct e as [eqpars [eqinst [eqpctx eqpret]]].
    rewrite /ptm.
    eapply cumul_prop_mkApps => //. fvs.
    { eapply cumul_prop_is_open in cum as [].
      rewrite on_free_vars_mkApps in i0.
      move/andP: i0 => [] //. }
    { now eapply type_it_mkLambda_or_LetIn, subject_is_open_term in pret. }
    { eapply PCUICEquality.eq_term_upto_univ_it_mkLambda_or_LetIn => //. tc.
      rewrite /predctx.
      rewrite /case_predicate_context /case_predicate_context_gen.
      rewrite /pre_case_predicate_context_gen /inst_case_context.
      eapply eq_context_upto_names_map2_set_binder_name; tea.
      eapply eq_context_upto_subst_context; tea. 1,2: tc.
      eapply eq_context_upto_univ_subst_instance; try tc. tas.
      now eapply All2_rev. }
    eapply All2_app. 2:(repeat constructor; eauto using eq_term_eq_term_prop_impl).
    eapply cumul_prop_mkApps_Ind_inv in X7 => //.
    eapply All2_app_inv_l in X7 as (?&?&?&?&?).
    eapply All2_symP => //. typeclasses eauto.
    eapply app_inj in e as [eql ->] => //.
    move: (All2_length eqpars).
    move: (All2_length a). lia. fvs. now eapply subject_is_open_term in scrut_ty.
    now apply subject_is_open_term in X6.

  - eapply inversion_Proj in X3 as (u' & mdecl' & idecl' & cdecl' & pdecl' & args' & inv); auto.
    intuition auto.
    specialize (X2 _ _  H0 a0 _ _ X4).
    eapply cumul_pb_cumul_prop in b; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_mkApps_Ind_inv in X2 => //.
    unshelve epose proof (a' := declared_projection_to_gen a); eauto.
    unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
    destruct (declared_projection_inj a' isdecl') as [<- [<- [<- <-]]].
    destruct (isType_mkApps_Ind_inv _ isdecl X0 (validity X1)) as [ps [argss [_ cu]]]; eauto.
    destruct (isType_mkApps_Ind_inv _ isdecl X0 (validity a0)) as [? [? [_ cu']]]; eauto.
    epose proof (wf_projection_context _ _ isdecl c1).
    epose proof (wf_projection_context _ _ isdecl c2).
    transitivity (subst0 (c0 :: List.rev args') (subst_instance u pdecl'.(proj_type))).
    eapply (@substitution_untyped_cumul_prop_cumul Σ Γ (projection_context p.(proj_ind) mdecl' idecl' u)) => //.
    * cbn -[projection_context on_free_vars_ctx].
      eapply is_closed_context_weaken; tas. fvs. now eapply wf_local_closed_context in X3.
    * cbn -[projection_context on_free_vars_ctx].
      eapply is_closed_context_weaken; tas. fvs. now eapply wf_local_closed_context in X6.
    * epose proof (declared_projection_closed a).
      len. rewrite on_free_vars_subst_instance. simpl; len.
      rewrite (declared_minductive_ind_npars a) in H1.
      rewrite closedn_on_free_vars //. eapply closed_upwards; tea. lia.
    * epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ _ isdecl wfΣ X1 (validity X1)).
      now eapply subslet_untyped_subslet.
    * epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ _ a wfΣ a0 (validity a0)).
      now eapply subslet_untyped_subslet.
    * constructor => //. symmetry; constructor => //; fvs.
      { now eapply eq_term_eq_term_prop_impl. }
      { now eapply All2_rev. }
    * eapply (@substitution_cumul_prop Σ Γ (projection_context p.(proj_ind) mdecl' idecl' u') []) => //.
      { apply (projection_subslet Σ _ _ _ _ _ _ _ _ _ a wfΣ a0 (validity a0)). }
      eapply cumul_prop_subst_instance; eauto.
      cbn -[projection_context on_free_vars_ctx]; eapply is_closed_context_weaken => //; fvs.
      epose proof (declared_projection_closed a).
      simpl; len.
      rewrite (declared_minductive_ind_npars a) in H1.
      rewrite closedn_on_free_vars //. eapply closed_upwards; tea. lia.

  - eapply inversion_Fix in X4 as (decl' & fixguard' & Hnth & types' & bodies & wffix & cum); auto.
    eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply All2_nth_error in e; eauto.
    destruct e as (a & _).
    constructor; [fvs|..].
    { eapply nth_error_all in X0; tea.
      now apply isTypeRel_is_open_term in X0. }
    { now eapply cumul_prop_is_open in cum as []. }
    eapply eq_term_eq_term_prop_impl; eauto.
    now symmetry in a.

  - eapply inversion_CoFix in X4 as (decl' & fixguard' & Hnth & types' & bodies & wfcofix & cum); auto.
    eapply cumul_pb_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply All2_nth_error in e; eauto.
    destruct e as (a & _).
    constructor; [fvs|..].
    { eapply nth_error_all in X0; tea.
      now apply isTypeRel_is_open_term in X0. }
    { now eapply cumul_prop_is_open in cum as []. }
    eapply eq_term_eq_term_prop_impl; eauto.
    now symmetry in a.

  - depelim X3.
    eapply inversion_Prim in X2 as [prim_ty' [cdecl' []]]; tea. depelim o.
    1-3:rewrite H in e; noconf e; eapply cumul_pb_cumul_prop; eauto; pcuic.
    depelim X1.
    cbn in H, e2. rewrite H in e2. noconf e2. eapply cumul_pb_cumul_prop; eauto; pcuic.
    move: w; simp prim_type. intro. etransitivity; tea. constructor; fvs. cbn.
    depelim X0. fvs. eapply eq_term_leq_term. symmetry; repeat constructor; eauto.
Qed.

Lemma typing_leq_term_prop (Σ : global_env_ext) Γ t t' T T' :
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  on_udecl Σ.1 Σ.2 ->
  Σ ;;; Γ |- t' : T' ->
  forall pb n, compare_term_napp Σ Σ pb n t' t ->
  Σ ;;; Γ |- T ~~ T'.
Proof using Type Hcf cf.
  intros.
  now eapply (env_prop_typing typing_leq_term_prop_gen).
Qed.

Lemma typing_cumul_term_prop {Σ : global_env_ext} {wfΣ : wf_ext Σ} pb Γ t t' T T' :
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  Σ ;;; Γ |- t' <=[pb] t ->
  Σ ;;; Γ |- T ~~ T'.
Proof using Type Hcf cf.
  intros.
  apply cumul_alt in X1 as (v & v' & r & r' & leq).
  eapply typing_leq_term_prop. 5: eassumption. 1,3: apply wfΣ.
  all: eapply subject_reduction; [ auto | | eassumption]; assumption.
Qed.

End no_prop_leq_type.
