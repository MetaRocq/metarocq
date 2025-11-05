(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICCases PCUICCumulativity PCUICTyping
     PCUICReduction PCUICWeakeningEnv
     PCUICClosed PCUICPosition.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags).

(** * Universe Substitution lemmas for typing derivations. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".

Create HintDb univ_subst.

Local Ltac aa := rdest; eauto with univ_subst.

Import Universe.NES.
Import Universes.

Lemma subset_levels l s : LevelSet.Subset (levels l) s <-> (forall lk, LevelExprSet.In lk l -> LevelSet.In lk.1 s).
Proof. rewrite /LevelSet.Subset. setoid_rewrite levels_spec. firstorder.
  apply H. exists lk.2; destruct lk => //.
Qed.

Lemma subst_instance_level_expr_val {u l v} v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, val v (nth n u Universe.zero) = valuation_poly v' n)
  : val v (subst_instance_level_expr u l) = val v' l.
Proof.
  destruct l as [l k]; cbn. destruct l; cbn; try congruence.
  - cbn. lia.
  - rewrite H1. lia.
  - rewrite /subst_instance_level_expr //=.
    have hn := nth_nth_error n u Universe.zero.
    move: (H2 n); rewrite hn.
    destruct nth_error eqn:he => //.
    * intros <-. rewrite val_plus //. lia.
    * intros <-. cbn. lia.
Qed.

Lemma subst_instance_universe_val u l v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, val v (nth n u Universe.zero) = valuation_poly v' n)
  : val v (subst_instance_universe u l) = val v' l.
Proof.
  move: l; eapply Universe.NES.elim.
  - intros le; cbn. rewrite (subst_instance_level_expr_val v') //.
  - intros le x ih hin.
    rewrite /subst_instance_universe.
    rewrite val_add /Universe.concat_map.
    rewrite -ih.
    rewrite Universe.fold_union_add /Universe.sup.
    rewrite val_sup. f_equal.
    now apply subst_instance_level_expr_val.
Qed.

Lemma eq_valuation v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, valuation_poly v n = valuation_poly v' n)
  : forall u : sort, Sort.to_csort v u = Sort.to_csort v' u.
Proof.
  intros [| | u]; cbnr. f_equal.
  assert (He : forall e : LevelExpr.t, val v e = val v' e). {
    intros [[] b]; cbnr; rewrite ?H1 ?H2; reflexivity. }
  eapply val_eq_levels_alg. 2:{ reflexivity. }
  intros l _. specialize (He (l, 0)). now cbn in He.
  Unshelve. exact config.default_checker_flags.
Qed.
(*
Lemma is_prop_subst_instance_level u l
    : Level.is_prop (subst_instance_level u l) = Level.is_prop l.
Proof.
  destruct l; cbn; try reflexivity.
  destruct (le_lt_dec #|u| n) as [HH|HH].
  + now rewrite nth_overflow.
  + eapply (forallb_nth _ _ _ Level.lzero Hu) in HH.
    destruct HH as [l [HH1 HH2]]. rewrite HH1. now apply ssrbool.negbTE.
Qed. *)

Lemma subst_instance_sort_val u s v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, val v (nth n u Universe.zero) = valuation_poly v' n)
  : Sort.to_csort v (subst_instance_sort u s) = Sort.to_csort v' s.
Proof.
  destruct s as [ | | exprs]; cbnr.
  f_equal; now apply subst_instance_universe_val.
Qed.

Definition subst_instance_valuation (u : Instance.t) (v : valuation) :=
  {| valuation_mono := valuation_mono v ;
     valuation_poly := fun i => val v (nth i u Universe.zero) |}.

Lemma subst_instance_level_val' u l v
  : val v (subst_instance_level_expr u l) = val (subst_instance_valuation u v) l.
Proof.
  now apply subst_instance_level_expr_val.
Qed.

Lemma subst_instance_universe_val' u exprs v
  : val v (subst_instance_universe u exprs) = val (subst_instance_valuation u v) exprs.
Proof.
  now apply subst_instance_universe_val.
Qed.

Lemma subst_instance_sort_val' u l v
  : Sort.to_csort v (subst_instance_sort u l) = Sort.to_csort (subst_instance_valuation u v) l.
Proof.
  now apply subst_instance_sort_val.
Qed.

Lemma subst_instance_universe_make' (l : LevelExpr.t) u :
  subst_instance u (Universe.make l) = subst_instance_level_expr u l.
Proof. reflexivity. Qed.

(* Lemma subst_instance_universe_make l u :
  subst_instance_universe u (Universe.of_level l)
  = Universe.of_level (subst_instance u l).
Proof.
  destruct l; cbnr. rewrite nth_nth_error.
  destruct nth_error; cbnr.
Qed. *)


Class SubstUnivPreserving eq_universe {A} `{UnivSubst A} (eqA : A -> A -> Prop) := Build_SubstUnivPreserving :
  forall u u1 u2, cmp_universe_instance eq_universe u1 u2 ->
    eqA (subst_instance u1 u) (subst_instance u2 u).

Lemma subst_equal_inst_inst Re Re' :
  SubstUnivPreserving Re Re' ->
  forall u u1 u2, cmp_universe_instance Re u1 u2 ->
             cmp_universe_instance Re' (subst_instance u1 u)
                                    (subst_instance u2 u).
Proof.
  intros hRe u. induction u; cbnr; try now constructor.
  intros u1 u2; unfold cmp_universe_instance; cbn; constructor.
  - apply (hRe a u1 u2 H).
  - exact (IHu u1 u2 H).
Qed.

Lemma subst_equal_inst_global_inst Σ cmp_universe pb gr napp :
  SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv) ->
  forall u u1 u2, cmp_universe_instance (cmp_universe Conv) u1 u2 ->
             cmp_global_instance Σ cmp_universe pb gr napp (subst_instance u1 u)
                                    (subst_instance u2 u).
Proof.
  intros subst_conv u u1 u2 Ru1u2.
  unfold cmp_global_instance, cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen as [| |v].
  - now eapply subst_equal_inst_inst.
  - len.
  - left. now eapply subst_equal_inst_inst.
Qed.

Lemma eq_term_upto_univ_subst_instance Σ cmp_universe cmp_sort pb napp :
  SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort pb) ->
  forall t u1 u2,
    cmp_universe_instance (cmp_universe Conv) u1 u2 ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (subst_instance u1 t)
                            (subst_instance u2 t).
Proof.
  intros hsubst_conv hsubst_sort_conv hsubst_sort_pb t.
  induction t in napp, pb, hsubst_sort_pb |- * using term_forall_list_ind; intros u1 u2 hu.
  all: cbn; try constructor; eauto using subst_equal_inst_inst, subst_equal_inst_global_inst.
  all: solve_all; unfold eq_predicate, eq_branches, eq_branch, eq_mfixpoint in *.
  all: try eapply All2_map, All_All2; tea; cbn; intros; rdest; eauto using subst_equal_inst_inst.
  - solve_all.
  - reflexivity.
  - reflexivity.
  - destruct p as [? []]; try now constructor.
    destruct X as (hty & hdef & harr).
    constructor; cbn; eauto. solve_all.
Qed.

Lemma add_subst le u i : (add le u)@[i] = union (subst_instance_level_expr i le) u@[i].
Proof.
  apply equal_exprsets => l.
  rewrite [_@[i]]Universe.fold_union_add //=.
Qed.

(* Lemma interp_nes_union (val : valuation): Universe.interp_nes val () *)

#[global]
Instance eq_universe_SubstUnivPreserving {cf:checker_flags} φ :
  SubstUnivPreserving (eq_universe φ) (eq_universe φ).
Proof.
  intros exprs u1 u2 hu.
  unfold_univ_rel.
  assert (He : forall e, val v (subst_instance_level_expr u1 e)
                    = val v (subst_instance_level_expr u2 e)). {
    destruct e as [[] b]; cbnr.
    case_eq (nth_error u1 n).
    - intros l1 X. eapply Forall2_nth_error_Some_l in hu; tea.
      rewrite /subst_instance_level_expr //=.
      destruct hu as [l2 [-> H2]].
      specialize (H2 v Hv).
      cbn in *. rewrite !val_plus X. lia.
    - intros X. eapply Forall2_nth_error_None_l in hu; tea.
      rewrite /subst_instance_level_expr //= X.
      destruct (nth_error u2 n); [discriminate|reflexivity]. }
  simpl.
  move: exprs.
  apply: Universe.NES.elim.
  - intros le; cbn. apply He.
  - intros le x hv hnin.
    now rewrite -!interp_nes_val !add_subst !interp_nes_val !val_sup hv He.
Qed.

#[global]
Instance leq_universe_SubstUnivPreserving {cf:checker_flags} φ :
  SubstUnivPreserving (leq_universe φ) (leq_universe φ).
Proof.
  intros exprs u1 u2 hu.
  unfold_univ_rel.
  assert (He : forall e, val v (subst_instance_level_expr u1 e)
                    <= val v (subst_instance_level_expr u2 e)). {
    destruct e as [[] b]; cbnr.
    case_eq (nth_error u1 n).
    - intros l1 X. eapply Forall2_nth_error_Some_l in hu; tea.
      rewrite /subst_instance_level_expr //= X.
      destruct hu as [l2 [-> H2]].
      specialize (H2 v Hv).
      cbn in *. rewrite !val_plus; lia.
    - intros X. eapply Forall2_nth_error_None_l in hu; tea.
      rewrite /subst_instance_level_expr //= X.
      destruct (nth_error u2 n); [discriminate|reflexivity]. }
  simpl.
  move: exprs.
  apply: Universe.NES.elim.
  - intros le; cbn. apply He.
  - intros le x hv hnin.
    rewrite -!interp_nes_val !add_subst !interp_nes_val !val_sup.
    specialize (He le). lia.
Qed.

#[global]
Instance compare_universe_substu {cf} φ pb : SubstUnivPreserving (eq_universe φ) (compare_universe φ pb).
Proof.
  destruct pb; tc.
  intros u ui ui' H.
  apply leq_universe_SubstUnivPreserving.
  eapply cmp_universe_instance_impl'; tea. tc.
Qed.

#[global]
Instance compare_sort_substu {cf:checker_flags} φ pb :
  SubstUnivPreserving (eq_universe φ) (compare_sort φ pb).
Proof.
  intros s u1 u2 hu.
  destruct s as [| | u]; cbnr. rewrite compare_sort_type.
  now eapply Build_SubstUnivPreserving.
Qed.

Global Instance subst_instance_def {A} `(UnivSubst A) : UnivSubst (def A)
  := fun u => map_def (subst_instance u) (subst_instance u).

Global Instance subst_instance_prod {A B} `(UnivSubst A) `(UnivSubst B)
  : UnivSubst (A × B)
  := fun u => map_pair (subst_instance u) (subst_instance u).

Global Instance subst_instance_nat : UnivSubst nat
  := fun _ n => n.

Lemma subst_instance_level_expr_make u l :
  subst_instance_level_expr u l = Universe.plus l.2 (subst_instance_level u l.1).
Proof.
  destruct l; simpl; auto.
Qed.

Lemma plus_plus n m u : Universe.plus n (Universe.plus m u) = Universe.plus (n + m) u.
Proof.
  apply equal_exprsets => -[l k]. rewrite /Universe.plus.
  rewrite Universe.map_spec.
  setoid_rewrite Universe.map_spec.
  split.
  - move=> -[] e [] [] e1 [] hin -> ->.
    exists e1. split => //. rewrite /LevelExpr.add //=. lia_f_equal.
  - move=> -[] [l' k'] [] hin he. noconf he.
    exists (l', m + k').  rewrite /LevelExpr.add.
    split.
    * eexists; split; trea. lia_f_equal.
    * cbn. lia_f_equal.
Qed.

Lemma subst_instance_level_expr_add i n u :
  subst_instance_level_expr i (LevelExpr.add n u) = Universe.plus n (subst_instance_level_expr i u).
Proof.
  apply equal_exprsets => -[l k']; destruct u as [[] k].
  1-2:cbn; rewrite ?LevelExprSet.singleton_spec ?LevelExprSet.add_spec /LevelExpr.add //=.
  - firstorder; rewrite H; left; lia_f_equal.
  - firstorder; rewrite H; left; lia_f_equal.
  - rewrite /LevelExpr.add. cbn -[subst_instance_level_expr Universe.plus].
    rewrite !subst_instance_level_expr_make plus_plus. cbn. reflexivity.
Qed.

Lemma subst_instance_universe_plus i n u :
  subst_instance_universe i (Universe.plus n u) = Universe.plus n (subst_instance_universe i u).
Proof.
  apply equal_exprsets => -[l k]; rewrite /subst_instance_universe.
  rewrite /Universe.concat_map Universe.fold_union_spec.
  rewrite Universe.map_spec. setoid_rewrite Universe.map_spec.
  setoid_rewrite Universe.fold_union_spec. firstorder.
  - subst. destruct x0; noconf H1. destruct x1. cbn in H0. cbn.
    exists (t0, n1 + n0).
    split => //.
    * eexists; split; trea.
      apply Universe.map_spec. exists (t0, n0) => //.
    * rewrite /LevelExpr.add //=. lia_f_equal.
  - destruct x; noconf H0.
    destruct x0.
    rewrite subst_instance_level_expr_make in H1.
    apply Universe.map_spec in H1 as [? []].
    destruct x; noconf H1.
    exists (t1, n + n1). split.
    * eexists; split; trea. rewrite /LevelExpr.add. lia_f_equal.
    * cbn. eexists. split.
      + exact H0.
      + cbn. rewrite /LevelExpr.add. cbn. lia_f_equal.
Qed.

Lemma subst_instance_level_expr_two u1 u2 (l : LevelExpr.t) :
  subst_instance_universe u1 (subst_instance_level_expr u2 l)
  = subst_instance_level_expr (subst_instance u1 u2) l.
Proof.
  destruct l as [[] k]; cbn; try reflexivity.
  - rewrite !subst_instance_level_expr_make.
    cbn. now rewrite Nat.add_0_r.
  - rewrite !subst_instance_level_expr_make.
    cbn. now rewrite Nat.add_0_r.
  - rewrite !subst_instance_level_expr_make.
    cbn -[subst_instance_level].
    rewrite subst_instance_universe_plus. f_equal.
    cbn.
    rewrite nth_error_map.
    destruct nth_error => //=.
    apply equal_exprsets => l. rewrite Universe.fold_union_spec.
    rewrite !LevelExprSet.singleton_spec.
    setoid_rewrite Universe.map_spec.
    setoid_rewrite LevelExprSet.singleton_spec.
    split.
    * intros [le' [hin hs]]. subst le'.
      destruct hs as [e []]. subst l. cbn.
      apply LevelExprSet.singleton_spec in H.
      subst e. reflexivity.
    * move=> ->.
      exists (LevelExpr.make Level.lzero). split => //.
      exists (LevelExpr.make Level.lzero). split => //.
      apply LevelExprSet.singleton_spec. reflexivity.
Qed.

Lemma subst_instance_universe_sup i (u u' : Universe.t) :
  (u ∪ u')@[i]%nes = (u@[i] ∪ u'@[i])%nes.
Proof.
  apply equal_exprsets => l.
  rewrite Universe.fold_union_spec.
  cbn. rewrite LevelExprSet.union_spec.
  rewrite !Universe.fold_union_spec.
  setoid_rewrite Universe.map_spec.
  setoid_rewrite LevelExprSet.union_spec.
  firstorder.
Qed.

Lemma subst_instance_univ0_two u1 u2 (exprs : Universe.t) :
  exprs@[u2]@[u1] = exprs@[u2@[u1]].
Proof.
  move: exprs; apply elim.
  - intros le. cbn.
    apply subst_instance_level_expr_two.
  - intros le x eq hnin.
    rewrite [_@[u2]]add_subst //= [_@[u2@[u1]]]add_subst.
    rewrite -subst_instance_level_expr_two -[x@[u2@[u1]]]eq.
    rewrite -[union (subst_instance_universe u1 (subst_instance_level_expr u2 le)) _](subst_instance_universe_sup u1).
    reflexivity.
Qed.

Lemma subst_instance_univ_two u1 u2 s :
  subst_instance_sort u1 (subst_instance_sort u2 s)
  = subst_instance_sort (subst_instance u1 u2) s.
Proof.
  destruct s; cbnr. f_equal.
  apply subst_instance_univ0_two.
Qed.

Lemma subst_instance_two_instance u1 u2 (u : Instance.t) :
  subst_instance u1 (subst_instance u2 u)
  = subst_instance (subst_instance u1 u2) u.
Proof.
  rewrite /subst_instance /= /subst_instance_instance.
  rewrite List.map_map.
  apply map_ext, subst_instance_univ0_two.
Qed.

Import Lists.List (map_map).

Lemma subst_instance_two u1 u2 (t : term) :
  subst_instance u1 (subst_instance u2 t)
  = subst_instance (subst_instance u1 u2) t.
Proof.
  rewrite /subst_instance /=.
  induction t using term_forall_list_ind; cbn; f_equal;
    auto using subst_instance_two_instance.
  - rewrite map_map. now apply All_map_eq.
  - apply subst_instance_univ_two.
  - destruct X; red in X0. rewrite map_predicate_map_predicate.
    apply map_predicate_eq_spec; solve_all.
    now rewrite [subst_instance_instance _ _]subst_instance_two_instance.
  - rewrite map_map. apply All_map_eq. red in X0. solve_all.
  - rewrite map_map. apply All_map_eq. solve_all.
    rewrite map_def_map_def; solve_all.
  - rewrite map_map. apply All_map_eq. solve_all.
    rewrite map_def_map_def; solve_all.
  - rewrite !mapu_prim_compose_rew. solve_all.
    intro. eapply subst_instance_univ0_two.
Qed.

Lemma subst_instance_two_context u1 u2 (Γ : context) :
  subst_instance u1 (subst_instance u2 Γ)
  = subst_instance (subst_instance u1 u2) Γ.
Proof.
  rewrite /subst_instance /=.
  induction Γ; try reflexivity.
  simpl. rewrite IHΓ; f_equal.
  destruct a as [? [] ?]; unfold map_decl; cbn;
    now rewrite !subst_instance_two.
Qed.

Lemma subst_instance_univ_cstr_two u1 u2 c :
  subst_instance_univ_cstr u1 (subst_instance_univ_cstr u2 c)
  = subst_instance_univ_cstr (subst_instance u1 u2) c.
Proof.
  destruct c as [[? ?] ?]; unfold subst_instance_univ_cstr; cbn.
  now rewrite !subst_instance_univ0_two.
Qed.

Lemma In_subst_instance_cstrs u c ctrs :
  UCS.In c (subst_instance_cstrs u ctrs)
  <-> exists c', c = subst_instance_univ_cstr u c' /\ UCS.In c' ctrs.
Proof.
  unfold subst_instance_cstrs.
  rewrite UCS.fold_spec.
  transitivity (UCS.In c UCS.empty \/
                exists c', c = subst_instance_univ_cstr u c'
                      /\ In c' (UCS.elements ctrs)).
  - generalize (UCS.elements ctrs), UCS.empty.
    induction l; cbn.
    + pcuicfo. now destruct H0 as [? ?].
    + intros t. etransitivity. 1: eapply IHl.
      split; intros [HH|HH].
      * destruct a as [[l1 a] l2]. apply UCS.add_spec in HH.
        destruct HH as [HH|HH]. 2: now left.
        right; eexists. split; [|left; reflexivity]. assumption.
      * destruct HH as [c' ?]. right; exists c'; intuition.
      * left. destruct a as [[l1 a] l2]. apply UCS.add_spec.
        now right.
      * destruct HH as [c' [HH1 [?|?]]]; subst.
        -- left. destruct c' as [[l1 c'] l2];
           apply UCS.add_spec; now left.
        -- right. exists c'. intuition.
  - rewrite UnivConstraintSetFact.empty_iff.
    transitivity (exists c', c = subst_instance_univ_cstr u c'
                        /\ In c' (UCS.elements ctrs)).
    1: intuition.
    apply iff_ex; intro. apply and_iff_compat_l. symmetry.
    etransitivity. 1: symmetry; apply UCS.elements_spec1.
    etransitivity. 1: eapply SetoidList.InA_alt.
    split; intro; eauto.
    now destruct H as [? [[] ?]].
Qed.

Lemma In_subst_level_instance_cstrs u c ctrs :
  UCS.In c (subst_level_instance_cstrs u ctrs)
  <-> exists c', c = subst_level_instance_univ_cstr u c' /\ UCS.In c' ctrs.
Proof.
  unfold subst_level_instance_cstrs.
  rewrite UCS.fold_spec.
  transitivity (UCS.In c UCS.empty \/
                exists c', c = subst_level_instance_univ_cstr u c'
                      /\ In c' (UCS.elements ctrs)).
  - generalize (UCS.elements ctrs), UCS.empty.
    induction l; cbn.
    + pcuicfo. now destruct H0 as [? ?].
    + intros t. etransitivity. 1: eapply IHl.
      split; intros [HH|HH].
      * destruct a as [[l1 a] l2]. apply UCS.add_spec in HH.
        destruct HH as [HH|HH]. 2: now left.
        right; eexists. split; [|left; reflexivity]. assumption.
      * destruct HH as [c' ?]. right; exists c'; intuition.
      * left. destruct a as [[l1 a] l2]. apply UCS.add_spec.
        now right.
      * destruct HH as [c' [HH1 [?|?]]]; subst.
        -- left. destruct c' as [[l1 c'] l2];
           apply UCS.add_spec; now left.
        -- right. exists c'. intuition.
  - rewrite UnivConstraintSetFact.empty_iff.
    transitivity (exists c', c = subst_level_instance_univ_cstr u c'
                        /\ In c' (UCS.elements ctrs)).
    1: intuition.
    apply iff_ex; intro. apply and_iff_compat_l. symmetry.
    etransitivity. 1: symmetry; apply UCS.elements_spec1.
    etransitivity. 1: eapply SetoidList.InA_alt.
    split; intro; eauto.
    now destruct H as [? [[] ?]].
Qed.

Lemma In_subst_instance_cstrs' u c ctrs :
  UCS.In c ctrs ->
  UCS.In (subst_instance_univ_cstr u c) (subst_instance_cstrs u ctrs).
Proof.
  intro H. apply In_subst_instance_cstrs. now eexists.
Qed.

Lemma subst_instance_cstrs_two u1 u2 ctrs :
  UCS.Equal
    (subst_instance_cstrs u1 (subst_instance_cstrs u2 ctrs))
    (subst_instance_cstrs (subst_instance u1 u2) ctrs).
Proof.
  intro c; split; intro Hc; apply In_subst_instance_cstrs.
  - apply In_subst_instance_cstrs in Hc; destruct Hc as [c' [eq Hc']].
    apply In_subst_instance_cstrs in Hc'; destruct Hc' as [c'' [eq' Hc'']].
    exists c''. subst; now rewrite subst_instance_univ_cstr_two.
  - apply In_subst_instance_cstrs in Hc; destruct Hc as [c' [eq Hc']].
    exists (subst_instance_univ_cstr u2 c'). split.
    + now rewrite subst_instance_univ_cstr_two.
    + now apply In_subst_instance_cstrs'.
Qed.

Lemma is_propositional_subst_instance_univ u l
  : Sort.is_propositional (subst_instance_sort u l) = Sort.is_propositional l.
Proof.
  destruct l; cbnr.
Qed.

Lemma is_prop_subst_instance_univ u l
  : Sort.is_prop (subst_instance_sort u l) = Sort.is_prop l.
Proof.
  destruct l; cbnr.
Qed.

Lemma is_sprop_subst_instance_univ u l
  : Sort.is_sprop (subst_instance_sort u l) = Sort.is_sprop l.
Proof.
  destruct l; cbnr.
Qed.

Lemma is_prop_subst_instance u x0 :
  Sort.is_prop x0 -> Sort.is_prop (subst_instance_sort u x0).
Proof.
  now rewrite is_prop_subst_instance_univ.
Qed.

Lemma sup_subst_instance_univ0 ui u1 u2 :
  subst_instance ui (Universe.sup u1 u2)
  = Universe.sup (subst_instance ui u1) (subst_instance ui u2).
Proof.
  apply subst_instance_universe_sup.
Qed.

Lemma sup_subst_instance_univ u s1 s2 :
  subst_instance_sort u (Sort.sup s1 s2)
  = Sort.sup (subst_instance_sort u s1) (subst_instance_sort u s2).
Proof.
  destruct s1, s2; cbnr. f_equal.
  apply sup_subst_instance_univ0.
Qed.

Lemma consistent_instance_declared {cf: checker_flags} lvs φ uctx (u : Instance.t) :
  consistent_instance lvs φ uctx u ->
  forallb (fun l : Universe.t => LS.subset (Universe.levels l) lvs) u.
Proof.
  unfold consistent_instance. destruct uctx as [|ctx].
  1: destruct u; [reflexivity|discriminate].
  intuition auto.
Qed.

Lemma monomorphic_level_notin_AUContext s φ :
  ~ LS.In (Level.level s) (AUContext.levels φ).
Proof.
  destruct φ as [φ1 φ2].
  intro H. apply (proj1 (LevelSetProp.of_list_1 _ _)) in H. cbn in H.
  apply SetoidList.InA_alt in H.
  destruct H as [? [? H]]; subst. revert H.
  unfold mapi; generalize 0.
  induction φ1; cbn. 1: trivial.
  intros n [H|H].
  - discriminate.
  - eauto.
Qed.

Global Instance satisfies_equal_sets v :
  Morphisms.Proper (Morphisms.respectful UCS.Equal iff) (satisfies v).
Proof.
  intros φ1 φ2 H; split; intros HH c Hc; now apply HH, H.
Qed.

Global Instance satisfies_subsets v :
  Morphisms.Proper (Morphisms.respectful UCS.Subset (fun A B : Prop => B -> A))
                   (satisfies v).
Proof.
  intros φ1 φ2 H H2 c Hc; now apply H2, H.
Qed.

#[global] Hint Resolve subst_instance_cstrs_two
     satisfies_equal_sets satisfies_subsets : univ_subst.

Lemma satisfies0_subst_instance_ctr u v c
  : satisfies0 v (subst_instance_univ_cstr u c)
    <-> satisfies0 (subst_instance_valuation u v) c.
Proof.
  destruct c as [[l1 []] l2]; unfold subst_instance_univ_cstr; cbn;
    split; intro H; constructor; inv H.
  all: rewrite <- ?subst_instance_universe_val'; tea.
  all: rewrite ?subst_instance_universe_val'; tea.
Qed.

Lemma satisfies_subst_instance_ctr u v ctrs
  : satisfies v (subst_instance_cstrs u ctrs)
    <-> satisfies (subst_instance_valuation u v) ctrs.
Proof.
  split; intros Hv c Hc.
  - apply satisfies0_subst_instance_ctr; tas. apply Hv.
    apply In_subst_instance_cstrs. exists c; now split.
  - apply In_subst_instance_cstrs in Hc.
    destruct Hc as [c' [? Hc']]; subst.
    apply satisfies0_subst_instance_ctr; auto.
Qed.

(** global constraints are monomorphic *)

Lemma not_var_global_levels {cf : checker_flags} {Σ} (hΣ : wf Σ) :
  LS.For_all (negb ∘ Level.is_var) (global_levels Σ).
Proof.
  destruct hΣ as [onu ond]. apply onu.
Qed.

Definition wf_ext_wk {cf : checker_flags} (Σ : global_env_ext)
  := wf Σ.1 × on_udecl_prop Σ.1 Σ.2.

Lemma wf_ext_wk_wf {cf:checker_flags} Σ : wf_ext_wk Σ -> wf Σ.
Proof. intro H; apply H. Qed.

#[global]
Hint Resolve wf_ext_wk_wf : core.

Lemma not_var_global_ext_levels {cf : checker_flags} Σ (hΣ : wf_ext_wk (Σ, Monomorphic_ctx)) :
  LS.For_all (negb ∘ Level.is_var) (global_ext_levels (Σ, Monomorphic_ctx)).
Proof. apply hΣ. Qed.

Lemma levels_global_constraint {cf : checker_flags} Σ (hΣ : wf Σ) c :
  UCS.In c (global_constraints Σ)
  -> LS.Subset (levels c.1.1) (global_levels Σ)
    /\ LS.Subset (levels c.2) (global_levels Σ).
Proof.
  intros inc.
  destruct hΣ. destruct o. specialize (H c inc).
  destruct c as [[l eq] r]; apply H.
Qed.

Lemma levels_global_ext_constraint {cf : checker_flags} Σ φ (hΣ : wf_ext_wk (Σ, φ)) c :
  UCS.In c (global_ext_constraints (Σ, φ))
  -> LS.Subset (levels c.1.1) (global_ext_levels (Σ, φ))
    /\ LS.Subset (levels c.2) (global_ext_levels (Σ, φ)).
Proof.
  intro H. apply UCS.union_spec in H; simpl in H.
  destruct hΣ as [hΣ Hφ], H as [Hc|H]; simpl in *.
  - red in Hφ. unfold global_ext_levels. simpl.
    destruct c as [[l1 c] l2]; exact (Hφ _ Hc).
  - apply levels_global_constraint in H; tas.
    destruct H. split.
    * unfold global_ext_levels. rewrite H. cbn. lsets.
    * unfold global_ext_levels. rewrite H0. cbn. lsets.
Qed.

Definition monomorphic_univ (ls : Universe.t) :=
  LevelSet.for_all (fun b => negb (Level.is_var b)) (levels ls).

Definition is_monomorphic_cstr (c : UnivConstraint.t)
  := monomorphic_univ c.1.1 && monomorphic_univ c.2.

Lemma monomorphic_global_constraint {cf : checker_flags} Σ (hΣ : wf Σ) c :
  UCS.In c (global_constraints Σ)
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_constraint in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  - now apply LevelSet.for_all_spec; tc => l /H1 /not_var_global_levels.
  - now apply LevelSet.for_all_spec; tc => l /H2 /not_var_global_levels.
Qed.

Lemma monomorphic_global_constraint_ext {cf : checker_flags} Σ
      (hΣ : wf_ext_wk (Σ, Monomorphic_ctx)) c :
  UCS.In c (global_ext_constraints (Σ, Monomorphic_ctx))
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_ext_constraint in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  - now apply LevelSet.for_all_spec; tc => l /H1 /not_var_global_ext_levels.
  - now apply LevelSet.for_all_spec; tc => l /H2 /not_var_global_ext_levels.
Qed.

#[global] Hint Resolve monomorphic_global_constraint monomorphic_global_constraint_ext
  : univ_subst.

Lemma subst_instance_monom_cstr inst c :
  is_monomorphic_cstr c
  -> subst_instance_univ_cstr inst c = c.
Proof.
  intro H; apply andb_and in H. destruct H.
Admitted.
  (* destruct c as [[[] ?] []]; cbnr; discriminate. *)
(* Qed. *)

Lemma equal_subst_instance_cstrs_mono u cstrs :
  UCS.For_all is_monomorphic_cstr cstrs ->
  UCS.Equal (subst_instance_cstrs u cstrs) cstrs.
Proof.
  intros HH c. etransitivity.
  - eapply In_subst_instance_cstrs.
  - split; intro H.
    + destruct H as [c' [eq Hc']]. subst; rewrite subst_instance_monom_cstr; aa.
    + exists c. rewrite subst_instance_monom_cstr; aa.
Qed.

Lemma subst_instance_cstrs_union u φ φ' :
  UCS.Equal (subst_instance_cstrs u (UCS.union φ φ'))
           (UCS.union (subst_instance_cstrs u φ) (subst_instance_cstrs u φ')).
Proof.
  intro c; split; intro Hc.
  - apply In_subst_instance_cstrs in Hc.
    destruct Hc as [c' [eq Hc]]; subst.
    apply UCS.union_spec in Hc. apply UCS.union_spec.
    destruct Hc; [left|right]; now apply In_subst_instance_cstrs'.
  - apply In_subst_instance_cstrs.
    apply UCS.union_spec in Hc.
    destruct Hc as [Hc|Hc]; apply In_subst_instance_cstrs in Hc;
      destruct Hc as [c'[eq Hc]]; exists c'; aa; apply UCS.union_spec;
        [left|right]; aa.
Qed.

#[global] Hint Unfold UCS.For_all : univ_subst.

Definition sub_context_set (φ φ' : ContextSet.t)
  := LS.Subset φ.1 φ'.1 /\ UCS.Subset φ.2 φ'.2.

Definition global_ext_context_set Σ : ContextSet.t
  := (global_ext_levels Σ, global_ext_constraints Σ).

Global Instance sub_context_set_trans : RelationClasses.Transitive sub_context_set.
Proof.
  split; (etransitivity; [eapply H | eapply H0]).
Qed.

Lemma consistent_ext_trans_polymorphic_case_aux {cf : checker_flags} {Σ φ1 φ2 φ' udecl inst inst'} :
  wf_ext_wk (Σ, Polymorphic_ctx (φ1, φ2)) ->
  valid_constraints0 (global_ext_constraints (Σ, Polymorphic_ctx (φ1, φ2)))
                     (subst_instance_cstrs inst udecl) ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs inst' φ2) ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs
                        (subst_instance inst' inst) udecl).
Proof.
  intros [HΣ Hφ] H3 H2.
  intros v Hv. rewrite <- subst_instance_cstrs_two.
  apply satisfies_subst_instance_ctr; tas. apply H3.
  apply satisfies_union; simpl. split.
  - apply satisfies_subst_instance_ctr; auto.
  - apply satisfies_subst_instance_ctr; tas.
    rewrite equal_subst_instance_cstrs_mono; aa.
    apply satisfies_union in Hv. apply Hv.
Qed.

Lemma consistent_ext_trans_polymorphic_cases {cf : checker_flags} Σ φ φ' udecl inst inst' :
  wf_ext_wk (Σ, φ) ->
  consistent_instance_ext (Σ, φ) (Polymorphic_ctx udecl) inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') (Polymorphic_ctx udecl)
                          (subst_instance inst' inst).
Proof.
  intros HΣφ [H [H0 H1]] H2.
  repeat split.
  2: now rewrite subst_instance_instance_length.
  + rewrite forallb_map. apply forallb_forall.
    intros l Hl. (* unfold global_ext_levels in *; simpl in *. *)
    eapply forallb_forall in H; tea. clear -H H2 Hl.
Admitted.
(*
    apply LevelSet_mem_union in H. destruct H as [H|H].
    2: { destruct l; simpl; try (apply LevelSet_mem_union; right; assumption).
         apply consistent_instance_declared in H2.
         apply (forallb_nth' n Level.lzero) in H2.
         destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
         apply LS.mem_spec, global_ext_levels_InSet. }
    *  destruct l; simpl.
       -- apply LS.mem_spec, global_ext_levels_InSet.
       -- apply LS.mem_spec in H.
          destruct φ as [|[φ1 φ2]]; simpl in *.
          { now apply LevelSetFact.empty_iff in H. }
          now apply monomorphic_level_notin_AUContext in H.
       -- apply consistent_instance_declared in H2.
          apply (forallb_nth' n Level.lzero) in H2.
          destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
          apply LS.mem_spec, global_ext_levels_InSet.
  + unfold consistent_instance_ext, consistent_instance in H2.
    unfold valid_constraints in *; destruct check_univs; [|trivial].
    destruct φ as [|[φ1 φ2]]; simpl in *.
    * intros v Hv. rewrite <- subst_instance_cstrs_two.
      apply satisfies_subst_instance_ctr; tas.
      apply H1. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      apply satisfies_union; simpl; split.
      -- intros c Hc. now apply Hv.
      -- apply satisfies_union in Hv; apply Hv.
    * destruct H2 as [_ [_ H2]].
      eapply consistent_ext_trans_polymorphic_case_aux; try eassumption.
Qed.
*)

Lemma consistent_ext_trans {cf : checker_flags} Σ φ φ' udecl inst inst' :
  wf_ext_wk (Σ, φ) ->
  consistent_instance_ext (Σ, φ) udecl inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') udecl (subst_instance inst' inst).
Proof.
  intros HΣφ H1 H2. destruct udecl as [|udecl].
  - (* udecl monomorphic *)
    cbn; now len.
  - (* udecl polymorphic *)
    eapply consistent_ext_trans_polymorphic_cases; eassumption.
Qed.

#[global] Hint Resolve consistent_ext_trans : univ_subst.

Lemma consistent_instance_valid_constraints {cf : checker_flags} Σ φ u univs :
  wf_ext_wk (Σ, φ) ->
  consistent_instance_ext (Σ, univs) φ u ->
  valid_constraints (global_ext_constraints (Σ, univs))
                    (subst_instance_cstrs u (global_ext_constraints (Σ, φ))).
Proof.
  intros HΣ HH.
  unfold valid_constraints; case_eq check_univs; [intro Hcf|trivial].
  intros v Hv. apply satisfies_subst_instance_ctr; tas.
  apply satisfies_union; simpl; split.
  - destruct φ as [|[φ1 φ2]].
    + cbn. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      * intros x hin. ucsets.
      * intros x hin. ucsets.
    + destruct HH as [_ [_ H1]].
      unfold valid_constraints in H1; rewrite Hcf in H1.
      apply satisfies_subst_instance_ctr; aa.
  - apply satisfies_subst_instance_ctr; tas.
    apply satisfies_union in Hv. destruct HΣ.
    rewrite equal_subst_instance_cstrs_mono; aa.
Qed.

#[global] Hint Resolve consistent_instance_valid_constraints : univ_subst.

Class SubstUnivPreserved {cf : checker_flags} {A} `{UnivSubst A} (R : UnivConstraintSet.t -> crelation A)
  := Build_SubstUnivPreserved :
       forall φ φ' (u : Instance.t),
         valid_constraints φ' (subst_instance_cstrs u φ) ->
         subrelation (R φ)
                     (precompose (R φ') (subst_instance u)).

Lemma satisfies_subst_instance {cf : checker_flags} φ φ' u :
  check_univs ->
  valid_constraints φ' (subst_instance_cstrs u φ) ->
  forall v, satisfies v φ' ->
       satisfies (subst_instance_valuation u v) φ.
Proof.
  intros Hcf HH v Hv.
  unfold valid_constraints in HH; rewrite Hcf in HH.
  apply satisfies_subst_instance_ctr; aa.
Qed.

Global Instance leq_universe_subst_instance {cf : checker_flags} : SubstUnivPreserved leq_universe.
Proof.
  intros φ φ' u HH exprs exprs' Hle.
  unfold_univ_rel eqn:H.
  rewrite !subst_instance_universe_val'; tas.
  apply Hle.
  eapply satisfies_subst_instance_ctr; tea.
Qed.

Global Instance eq_universe_subst_instance {cf : checker_flags} : SubstUnivPreserved eq_universe.
Proof.
  intros φ φ' u HH exprs exprs' Hle; cbnr; trivial.
  unfold_univ_rel eqn:H.
  rewrite !subst_instance_universe_val'; tas.
  apply Hle.
  eapply satisfies_subst_instance_ctr; tea.
Qed.

Global Instance leq_sort_subst_instance {cf : checker_flags} : SubstUnivPreserved leq_sort.
Proof.
  intros φ φ' u HH [| | exprs] [| | exprs'] Hle; cbnr; trivial.
  eapply Build_SubstUnivPreserved; tea.
Qed.

Global Instance eq_sort_subst_instance {cf : checker_flags} : SubstUnivPreserved eq_sort.
Proof.
  intros φ φ' u HH [| | exprs] [| | exprs'] Hle; cbnr; trivial.
  eapply Build_SubstUnivPreserved; tea.
Qed.

Global Instance compare_universe_subst_instance {cf : checker_flags} pb : SubstUnivPreserved (fun φ => compare_universe φ pb).
Proof.
  destruct pb; tc.
Qed.

Global Instance compare_sort_subst_instance {cf : checker_flags} pb : SubstUnivPreserved (fun φ => compare_sort φ pb).
Proof.
  destruct pb; tc.
Qed.

Lemma precompose_subst_instance cmp_universe u i i' :
  precompose (cmp_universe_instance cmp_universe) (subst_instance u) i i'
  <~> cmp_universe_instance (precompose cmp_universe (subst_instance_universe u)) i i'.
Proof.
  unfold cmp_universe_instance, subst_instance, on_rel.
  split; intro H; [apply Forall2_map_inv in H | apply Forall2_map]; apply Forall2_impl with (1 := H); intros => //.
Qed.

Definition precompose_subst_instance__1 Rle u i i'
  := fst (precompose_subst_instance Rle u i i').

Definition precompose_subst_instance__2 Rle u i i'
  := snd (precompose_subst_instance Rle u i i').

Lemma plus_0 u : Universe.plus 0 u = u.
Proof. Admitted.

Lemma subst_instance_make'_make u l :
  subst_instance u (Universe.make (LevelExpr.make l)) =
  subst_instance_level u l.
Proof.
  rewrite subst_instance_universe_make' subst_instance_level_expr_make.
  cbn. rewrite plus_0 //.
Qed.

Lemma precompose_subst_instance_global Σ cmp_universe pb gr napp u i i' :
  precompose (cmp_global_instance Σ cmp_universe pb gr napp) (subst_instance u) i i'
  <~> cmp_global_instance Σ (fun pb => precompose (cmp_universe pb) (subst_instance_universe u))
    pb gr napp i i'.
Proof.
  unfold cmp_global_instance, cmp_global_instance_gen, cmp_opt_variance, subst_instance.
  destruct global_variance_gen as [| |v].
  - apply precompose_subst_instance.
  - len.
  - split. all: intros [H|H]; [left|right].
    1,3: now apply precompose_subst_instance.
    all: [> rewrite -(map_id v) in H; apply Forall3_map_inv in H | rewrite -(map_id v); apply Forall3_map];
      apply Forall3_impl with (1 := H); clear v i i' H; intros v ??.
    all: destruct v => //=; unfold on_rel in *.
    all: rewrite !subst_instance_universe_make //.
Qed.

Definition precompose_subst_instance_global__1 Σ cmp_universe pb gr napp u i i'
  := fst (precompose_subst_instance_global Σ cmp_universe pb gr napp u i i').

Definition precompose_subst_instance_global__2 Σ cmp_universe pb gr napp u i i'
  := snd (precompose_subst_instance_global Σ cmp_universe pb gr napp u i i').

Global Instance eq_term_upto_univ_subst_preserved {cf : checker_flags} Σ
  (cmp_universe : forall _ _ (_ _ : Universe.t), Prop) (cmp_sort : forall _ _ (_ _ : sort), Prop) pb napp
  {huniverse : SubstUnivPreserved (fun φ => cmp_universe φ Conv)} {huniverse2 : SubstUnivPreserved (fun φ => cmp_universe φ pb)}
  {hsort : SubstUnivPreserved (fun φ => cmp_sort φ Conv)} {hsort2 : SubstUnivPreserved (fun φ => cmp_sort φ pb)}
  : SubstUnivPreserved (fun φ => eq_term_upto_univ_napp Σ (cmp_universe φ) (cmp_sort φ) pb napp).
Proof.
  intros φ φ' u HH t t'.
  specialize (huniverse _ _ _ HH).
  specialize (huniverse2 _ _ _ HH).
  specialize (hsort _ _ _ HH).
  specialize (hsort2 _ _ _ HH).
  clear HH. cbn in huniverse, huniverse2, hsort, hsort2.
  induction t in napp, pb, huniverse2, hsort2, t' |- * using term_forall_list_ind;
    inversion 1; subst; cbn; constructor;
      eauto using precompose_subst_instance__2, cmp_universe_instance_impl'.
  all: unfold eq_predicate, eq_branches, eq_branch, eq_mfixpoint in *.
  all: try (apply All2_map; eapply All2_impl'; tea;
    eapply All_impl; eauto; cbn; intros; aa).
  - eapply precompose_subst_instance_global__2.
    eapply cmp_global_instance_impl_same_napp; eauto.
  - eapply precompose_subst_instance_global__2.
    eapply cmp_global_instance_impl_same_napp; eauto.
  - destruct X2 as [? [? [? ?]]].
    repeat split; simpl; eauto; solve_all.
    * eapply precompose_subst_instance.
      eapply cmp_universe_instance_impl; eauto.
  - destruct p as [? []]; depelim X1; try now constructor.
    destruct X as (hty & hdef & harr).
    constructor; cbn; eauto. solve_all.
Qed.

Lemma leq_term_subst_instance {cf : checker_flags} Σ : SubstUnivPreserved (fun φ => leq_term Σ φ).
Proof. apply eq_term_upto_univ_subst_preserved; cbn; apply _. Qed.

Lemma eq_term_subst_instance {cf : checker_flags} Σ : SubstUnivPreserved (fun φ => eq_term Σ φ).
Proof. apply eq_term_upto_univ_subst_preserved; cbn; exact _. Qed.

Lemma compare_term_subst_instance {cf : checker_flags} Σ pb : SubstUnivPreserved (fun φ => compare_term Σ φ pb).
Proof. destruct pb; [apply eq_term_subst_instance|apply leq_term_subst_instance]. Qed.

Global Instance compare_decls_subst_preserved {cf : checker_flags} Σ
  (cmp_universe : forall _ _ (_ _ : Universe.t), Prop) (cmp_sort : forall _ _ (_ _ : sort), Prop) pb
  {huniverse : SubstUnivPreserved (fun φ => cmp_universe φ Conv)} {huniverse2 : SubstUnivPreserved (fun φ => cmp_universe φ pb)}
  {hsort : SubstUnivPreserved (fun φ => cmp_sort φ Conv)} {hsort2 : SubstUnivPreserved (fun φ => cmp_sort φ pb)}
  : SubstUnivPreserved (fun φ => compare_decls (fun pb => eq_term_upto_univ Σ (cmp_universe φ) (cmp_sort φ) pb) pb).
Proof.
  intros φ φ' u HH d d' []; constructor; cbn; auto.
  all: now eapply eq_term_upto_univ_subst_preserved.
Qed.

Global Instance eq_context_upto_subst_preserved {cf : checker_flags} Σ
  (cmp_universe : forall _ _ (_ _ : Universe.t), Prop) (cmp_sort : forall _ _ (_ _ : sort), Prop) pb
  {huniverse : SubstUnivPreserved (fun φ => cmp_universe φ Conv)} {huniverse2 : SubstUnivPreserved (fun φ => cmp_universe φ pb)}
  {hsort : SubstUnivPreserved (fun φ => cmp_sort φ Conv)} {hsort2 : SubstUnivPreserved (fun φ => cmp_sort φ pb)}
  : SubstUnivPreserved (fun φ => eq_context_upto Σ (cmp_universe φ) (cmp_sort φ) pb).
Proof.
  intros φ φ' u HH Γ Δ.
  induction 1; cbn; constructor; auto.
  now eapply compare_decls_subst_preserved.
Qed.

(** Now routine lemmas ... *)

Lemma In_subst_instance x u (l : Universe.t) :
  LevelExprSet.In x (subst_instance u l) <->
  (exists x', LevelExprSet.In x' l /\
    LevelExprSet.In x (subst_instance_level_expr u x')).
Proof.
  unfold subst_instance; cbn.
  unfold subst_instance_universe.
Admitted.

Lemma subst_instance_univ_super l u
  : subst_instance_sort u (Sort.super l) = Sort.super (subst_instance u l).
Proof.
  destruct l; cbnr.
  - rewrite closedu_subst_instance_level_expr //=.
  - rewrite closedu_subst_instance_level_expr //=.
  - now rewrite [_@[u]](subst_instance_universe_plus _ 1).
Qed.

Lemma monomorphic_level_notin_levels_of_udecl s udecl :
  LevelSet.In (Level.level s) (levels_of_udecl udecl) -> False.
Proof.
  destruct udecl; cbn.
  - lsets.
  - apply monomorphic_level_notin_AUContext.
Qed.

Lemma levels_zero : levels Universe.zero =_lset LevelSet.singleton Level.lzero.
Proof.
  now intros l; rewrite levels_singleton.
Qed.

Lemma subset_singleton x s : LevelSet.Subset (LevelSet.singleton x) s <-> LevelSet.In x s.
Proof.
  rewrite /LevelSet.Subset. setoid_rewrite LevelSet.singleton_spec.
  now firstorder subst.
Qed.

Lemma LevelIn_subst_instance {cf : checker_flags} Σ l u univs :
  LS.In l (global_ext_levels Σ) ->
  forallb (fun l : Universe.t => LS.subset (Universe.levels l) (global_ext_levels (Σ.1, univs))) u ->
  LS.Subset (levels (subst_instance_level u l)) (global_ext_levels (Σ.1, univs)).
Proof.
  intros H H'. destruct l.
  - cbn -[levels]. rewrite levels_zero subset_singleton.
    apply global_ext_levels_InSet.
  - move=> l; rewrite levels_singleton LevelSet.singleton_spec => ->.
   apply LS.union_spec in H; destruct H as [H|H]; simpl in *.
    + now apply monomorphic_level_notin_levels_of_udecl in H.
    + apply LS.union_spec; now right.
  - cbn.
    destruct nth_error eqn:hnth.
    + solve_all. eapply nth_error_all in hnth; tea.
      now apply LevelSet.subset_spec in hnth.
    + rewrite levels_zero subset_singleton.
      apply global_ext_levels_InSet.
Qed.


Lemma product_subst_instance u s1 s2
 : subst_instance_sort u (Sort.sort_of_product s1 s2)
   = Sort.sort_of_product (subst_instance_sort u s1) (subst_instance_sort u s2).
Proof.
  destruct s2; cbn; try reflexivity.
  destruct s1; cbn; try reflexivity.
  f_equal.
  apply sup_subst_instance_univ0.
Qed.

Lemma subst_instance_extended_subst u Γ :
  subst_instance u (extended_subst Γ 0) =
  extended_subst (subst_instance u Γ) 0.
Proof.
  rewrite /subst_instance /= /subst_instance_list /subst_instance /=.
  induction Γ as [|[na [b|] ty] Γ]; auto; rewrite /=; len; f_equal; auto.
  - rewrite [subst_instance_constr _ _]subst_instance_subst -IHΓ. f_equal.
    now rewrite subst_instance_lift.
  - rewrite !(lift_extended_subst _ 1).
    rewrite map_map_compose.
    setoid_rewrite subst_instance_lift.
    now rewrite -map_map_compose IHΓ.
Qed.
#[global] Hint Rewrite subst_instance_extended_subst : substu.

Lemma expand_lets_subst_instance u Γ t :
  subst_instance u (expand_lets Γ t) =
  expand_lets (subst_instance u Γ) (subst_instance u t).
Proof.
  rewrite /expand_lets /expand_lets_k.
  rewrite subst_instance_subst subst_instance_lift.
  now rewrite subst_instance_extended_subst /=; len.
Qed.
#[global] Hint Rewrite expand_lets_subst_instance : substu.

Global Instance subst_instance_predicate : UnivSubst (predicate term)
  := fun u => map_predicate (subst_instance u) (subst_instance u) (subst_instance u) id.

Lemma fix_subst_instance_subst u mfix :
  subst_instance u (fix_subst mfix) = fix_subst (subst_instance u mfix).
Proof.
  rewrite /subst_instance /subst_instance_list.
  unfold fix_subst. rewrite length_map.
  generalize #|mfix|. induction n. 1: reflexivity.
  simpl. rewrite IHn; reflexivity.
Qed.

Lemma cofix_subst_instance_subst u mfix :
  subst_instance u (cofix_subst mfix) = cofix_subst (subst_instance u mfix).
Proof.
  rewrite /subst_instance /subst_instance_list.
  unfold cofix_subst. rewrite length_map.
  generalize #|mfix|. induction n. 1: reflexivity.
  simpl. rewrite IHn; reflexivity.
Qed.

Lemma isConstruct_app_subst_instance u t :
  isConstruct_app (subst_instance u t) = isConstruct_app t.
Proof.
  unfold isConstruct_app.
  assert (HH: (decompose_app (subst_instance u t)).1
              = subst_instance u (decompose_app t).1). {
    unfold decompose_app. generalize (@nil term) at 1. generalize (@nil term).
    induction t; cbn; try reflexivity.
    intros l l'. erewrite IHt1; reflexivity. }
  rewrite HH. destruct (decompose_app t).1; reflexivity.
Qed.

Lemma fix_context_subst_instance u mfix :
  subst_instance u (fix_context mfix)
  = fix_context (subst_instance u mfix).
Proof.
  rewrite /subst_instance /= /subst_instance /subst_instance_context /map_context /fix_context.
  rewrite map_rev. f_equal.
  rewrite map_mapi mapi_map. eapply mapi_ext.
  intros n x. unfold map_decl, vass; cbn. f_equal.
  apply subst_instance_lift.
Qed.

Lemma subst_instance_app {A} {au : UnivSubst A} u (L1 L2 : list A) :
  subst_instance u (L1 ++ L2)
  = subst_instance u L1 ++ subst_instance u L2.
Proof.
  rewrite /subst_instance /= /subst_instance_list /=.
  now rewrite map_app.
Qed.

Lemma subst_instance_app_ctx u (L1 L2 : context) :
  subst_instance u (L1 ,,, L2)
  = subst_instance u L1 ,,, subst_instance u L2.
Proof.
  rewrite /app_context. now apply subst_instance_app.
Qed.

Definition map_constructor_body' f c :=
  {| cstr_name := cstr_name c;
     cstr_args := map_context f (cstr_args c);
     cstr_indices := List.map f (cstr_indices c);
     cstr_type := f (cstr_type c);
     cstr_arity := cstr_arity c |}.

Global Instance subst_instance_constructor_body : UnivSubst constructor_body
  := fun u => map_constructor_body' (subst_instance u).

Definition map_one_inductive_body' fu f oib :=
	{|
    ind_name := oib.(ind_name);
    ind_indices := map_context f oib.(ind_indices);
    ind_sort := fu oib.(ind_sort);
    ind_type := f oib.(ind_type);
    ind_kelim := oib.(ind_kelim);
    ind_ctors := List.map (map_constructor_body' f) oib.(ind_ctors);
    ind_projs := List.map (map_projection_body 0 (fun _ => f)) oib.(ind_projs);
    ind_relevance := oib.(ind_relevance) |}.

Global Instance subst_instance_inductive_body : UnivSubst one_inductive_body
  := fun u => map_one_inductive_body' (subst_instance u) (subst_instance u).

Definition map_mutual_inductive_body' fu f mib :=
  {| ind_finite := mib.(ind_finite);
     ind_npars := mib.(ind_npars);
     ind_params := map_context f mib.(ind_params);
     ind_bodies := List.map (map_one_inductive_body' fu f) mib.(ind_bodies);
     ind_universes := mib.(ind_universes);
     ind_variance := mib.(ind_variance) |}.

Global Instance subst_instance_mutual_inductive_body : UnivSubst mutual_inductive_body
  := fun u => map_mutual_inductive_body' (subst_instance u) (subst_instance u).

Lemma subst_instance_cstr_args u cdecl :
  cstr_args (subst_instance u cdecl) =
  subst_instance u (cstr_args cdecl).
Proof. reflexivity. Qed.

Lemma map_fold_context_k {term term' term''} (f : term' -> term) (g : nat -> term'' -> term') (Γ : list (BasicAst.context_decl term'')) :
  map_context f (fold_context_k g Γ) = fold_context_k (fun i => f ∘ (g i)) Γ.
Proof.
  now rewrite /map_context map_fold_context_k.
Qed.

Lemma subst_instance_subst_context u s k ctx :
  subst_instance u (subst_context s k ctx) =
  subst_context (subst_instance u s) k (subst_instance u ctx).
Proof.
  rewrite /subst_instance /= /subst_instance /subst_instance_context map_fold_context_k.
  rewrite /subst_context fold_context_k_map.
  apply fold_context_k_ext => i t.
  now rewrite -subst_instance_subst.
Qed.

Lemma subst_instance_subst_telescope u s k ctx :
  subst_instance u (subst_telescope s k ctx) =
  subst_telescope (subst_instance u s) k (subst_instance u ctx).
Proof.
  rewrite /subst_instance /= /subst_instance /subst_instance_context /= /subst_telescope /=
    /map_context map_mapi mapi_map.
  apply mapi_ext => i t.
  rewrite !compose_map_decl; apply map_decl_ext => t'.
  now rewrite -subst_instance_subst.
Qed.

Lemma subst_instance_lift_context u n k ctx :
  subst_instance u (lift_context n k ctx) =
  lift_context n k (subst_instance u ctx).
Proof.
  rewrite /subst_instance /= /subst_instance_context map_fold_context_k.
  rewrite /lift_context fold_context_k_map.
  apply fold_context_k_ext => i t.
  now rewrite subst_instance_lift.
Qed.

Lemma subst_instance_inds u0 ind u bodies :
  subst_instance u0 (inds ind u bodies)
  = inds ind (subst_instance u0 u) bodies.
Proof.
  unfold inds.
  induction #|bodies|; cbnr.
  f_equal. apply IHn.
Qed.

#[global] Hint Rewrite subst_instance_subst_context subst_instance_lift_context
  subst_instance_lift subst_instance_mkApps
  subst_instance_subst
  subst_instance_it_mkProd_or_LetIn
  subst_instance_it_mkLambda_or_LetIn
  subst_instance_inds
  : substu.
Ltac substu := autorewrite with substu.

Lemma inst_case_context_subst_instance pars puinst ctx u :
  subst_instance u (inst_case_context pars puinst ctx) =
  inst_case_context (subst_instance u pars) (subst_instance u puinst) ctx.
Proof.
  rewrite /inst_case_context; substu.
  rewrite [subst_instance _ _]map_rev.
  now rewrite subst_instance_two_context.
Qed.

Lemma inst_case_predicate_context_subst_instance p u :
  subst_instance u (inst_case_predicate_context p) =
  inst_case_predicate_context (subst_instance u p).
Proof.
  now rewrite /inst_case_predicate_context inst_case_context_subst_instance; cbn.
Qed.

Lemma inst_case_branch_context_subst_instance p br u :
  subst_instance u (inst_case_branch_context p br) =
  inst_case_branch_context (subst_instance u p) (map_branch (subst_instance u) id br).
Proof.
  now rewrite /inst_case_branch_context inst_case_context_subst_instance.
Qed.

Lemma iota_red_subst_instance pars p args br u :
  subst_instance u (iota_red pars p args br)
  = iota_red pars (subst_instance u p) (List.map (subst_instance u) args) (map_branch (subst_instance u) id br).
Proof.
  unfold iota_red.
  rewrite subst_instance_subst -map_skipn -map_rev.
  f_equal. rewrite expand_lets_subst_instance. f_equal.
  now rewrite inst_case_branch_context_subst_instance.
Qed.

Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) (l : list C) (l' : list D) :
  List.map f (map2 g l l') =
  map2 (fun (x : C) (y : D) => f (g x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  * cbn. now f_equal.
Qed.

Lemma map2_map_r {A B C D} (f : B -> C) (g : A -> C -> D) (l : list A) (l' : list B) :
  map2 g l (List.map f l') =
  map2 (fun x y => g x (f y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  * cbn. now f_equal.
Qed.

Lemma map2_set_binder_name_map bctx f Γ :
  map2 set_binder_name bctx (map_context f Γ) =
  map_context f (map2 set_binder_name bctx Γ).
Proof.
  now rewrite /map_context map_map2 map2_map_r.
Qed.

Lemma subst_instance_case_branch_context ind mdecl u p bctx cdecl :
  subst_instance u (case_branch_context ind mdecl p bctx cdecl) =
  case_branch_context ind mdecl (subst_instance u p) bctx cdecl.
Proof.
  unfold case_branch_context, case_branch_context_gen.
  cbn -[fold_context_k].
  substu => /=; len.
  rewrite /pre_case_branch_context_gen -inst_case_context_subst_instance.
  now rewrite -[subst_instance _ _]map2_set_binder_name_map.
Qed.

Lemma subst_instance_case_predicate_context ind mdecl idecl p u :
  subst_instance u (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (subst_instance u p).
Proof.
  unfold case_predicate_context, case_predicate_context_gen.
  cbn -[fold_context_k].
  substu => /=; len.
  rewrite /pre_case_predicate_context_gen -inst_case_context_subst_instance.
  now rewrite -[subst_instance _ _]map2_set_binder_name_map.
Qed.

Lemma subst_instance_to_extended_list u l
  : List.map (subst_instance u) (to_extended_list l)
    = to_extended_list (subst_instance u l).
Proof.
  - unfold to_extended_list, to_extended_list_k.
    change [] with (List.map (subst_instance u) (@nil term)) at 2.
    unf_term. generalize (@nil term), 0. induction l as [|[aa [ab|] ac] bb].
    + reflexivity.
    + intros l n; cbn. now rewrite IHbb.
    + intros l n; cbn. now rewrite IHbb.
Qed.

Lemma to_extended_list_subst_instance u l
  : to_extended_list (subst_instance u l) = to_extended_list l.
Proof.
  - unfold to_extended_list, to_extended_list_k.
    unf_term. generalize (@nil term), 0. induction l as [|[aa [ab|] ac] bb].
    + reflexivity.
    + intros l n; cbn. now rewrite IHbb.
    + intros l n; cbn. now rewrite IHbb.
Qed.

Lemma subst_instance_expand_lets u Γ t :
  subst_instance u (expand_lets Γ t) =
  expand_lets (subst_instance u Γ) (subst_instance u t).
Proof.
  rewrite /expand_lets /expand_lets_k.
  rewrite subst_instance_subst.
  rewrite subst_instance_extended_subst.
  f_equal.
  rewrite subst_instance_lift. len; f_equal.
Qed.

#[global] Hint Rewrite subst_instance_expand_lets closedn_subst_instance : substu.

Lemma subst_instance_expand_lets_ctx u Γ Δ :
  subst_instance u (expand_lets_ctx Γ Δ) =
  (expand_lets_ctx (subst_instance u Γ) (subst_instance u Δ)).
Proof.
  now rewrite /expand_lets_ctx /expand_lets_k_ctx; substu; len.
Qed.
#[global] Hint Rewrite subst_instance_expand_lets_ctx : substu.

Lemma forget_types_subst_instance l ctx :
  forget_types (subst_instance l ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_map_compose /=.
Qed.

Lemma subst_instance_case_branch_type {cf : checker_flags} {Σ} {wfΣ : wf Σ} u (ci : case_info) mdecl idecl p predctx br i cdecl :
  let ptm :=
    it_mkLambda_or_LetIn predctx (preturn p)
  in
  let p' := subst_instance u p in
  let ptm' :=
    it_mkLambda_or_LetIn
      (subst_instance u predctx)
      (preturn p') in
  case_branch_type ci mdecl idecl
     (subst_instance u p)
     (map_branch (subst_instance u) id br)
     ptm' i cdecl =
  map_pair (subst_instance u) (subst_instance u)
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite subst_instance_case_branch_context //.
  f_equal; substu.
  f_equal.
  rewrite map_app. f_equal.
  + rewrite !map_map_compose. apply map_ext => x.
    substu.
    rewrite [subst_instance u (List.rev _)]map_rev. f_equal.
    rewrite /expand_lets_k. len.
    rewrite ?subst_instance_two ?subst_instance_two_context //.
  + simpl. f_equal.
    substu. rewrite map_app /= //.
    rewrite subst_instance_to_extended_list to_extended_list_subst_instance.
    do 2 f_equal.
    rewrite !map_map_compose. now setoid_rewrite <-subst_instance_lift.
Qed.

Lemma subst_instance_wf_predicate u mdecl idecl p :
  wf_predicate mdecl idecl p ->
  wf_predicate mdecl idecl (subst_instance u p).
Proof.
  intros []. split.
  - now len.
  - simpl. assumption.
Qed.

Lemma subst_instance_wf_branch u cdecl br :
  wf_branch cdecl br ->
  wf_branch cdecl (map_branch (subst_instance u) id br).
Proof.
  now unfold wf_branch, wf_branch_gen.
Qed.

Lemma subst_instance_wf_branches cdecl u brs :
  wf_branches cdecl brs ->
  wf_branches cdecl (List.map (map_branch (subst_instance u) id) brs).
Proof.
  unfold wf_branches, wf_branches_gen.
  intros h. solve_all.
Qed.
#[global] Hint Resolve subst_instance_wf_predicate
  subst_instance_wf_branch subst_instance_wf_branches : pcuic.

Lemma subst_instance_predicate_set_pparams u p params :
  subst_instance u (set_pparams p params) =
  set_pparams (subst_instance u p) (List.map (subst_instance u) params).
Proof. reflexivity. Qed.

(* Lemma subst_instance_predicate_set_pcontext u p pcontext :
  subst_instance u (set_pcontext p pcontext) =
  set_pcontext (subst_instance u p) (subst_instance u pcontext).
Proof. reflexivity. Qed. *)

Lemma subst_instance_predicate_set_preturn u p pret :
  subst_instance u (set_preturn p pret) =
  set_preturn (subst_instance u p) (subst_instance u pret).
Proof. reflexivity. Qed.

Lemma red1_subst_instance Σ Γ u s t :
  red1 Σ Γ s t ->
  red1 Σ (subst_instance u Γ)
       (subst_instance u s) (subst_instance u t).
Proof.
  intros X0. pose proof I as X.
  intros. induction X0 using red1_ind_all.
  all: try (cbn; econstructor; eauto; fail).
  - cbn. rewrite subst_instance_subst. econstructor.
  - cbn. rewrite subst_instance_subst. econstructor.
  - cbn. rewrite subst_instance_lift. econstructor.
    unfold subst_instance.
    unfold option_map in *. destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context. rewrite nth_error_map E. cbn.
    rewrite map_decl_body. destruct c. cbn in H1. subst.
    reflexivity.
  - cbn. rewrite subst_instance_mkApps. cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcotext (map_branch (subst_instance u) br)).
    eapply red_iota; eauto with pcuic.
    * rewrite nth_error_map H //.
    * simpl. now len.
  - cbn. rewrite !subst_instance_mkApps. cbn.
    econstructor.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * inversion H.
        rewrite nth_error_map E. cbn.
        destruct d. cbn in *. cbn in *; try congruence.
        f_equal. f_equal.
        now rewrite subst_instance_subst fix_subst_instance_subst.
      * inversion H.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; inversion H0; clear H0.
      rewrite nth_error_map E. cbn.
      eapply isConstruct_app_subst_instance.
  - cbn. rewrite !subst_instance_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E.
    + inversion H.
      econstructor. fold subst_instance_constr.
      unfold unfold_cofix.
      rewrite nth_error_map E. cbn.
      rewrite subst_instance_subst.
      now rewrite cofix_subst_instance_subst.
    + cbn.
      inversion H.
  - cbn. unfold unfold_cofix in *.
    destruct nth_error eqn:E; inversion H.
    rewrite !subst_instance_mkApps.
    econstructor. fold subst_instance.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
    1: rewrite subst_instance_subst cofix_subst_instance_subst.
    all: now inversion E.
  - cbn. rewrite subst_instance_two. econstructor; eauto.
  - cbn. rewrite !subst_instance_mkApps.
    econstructor. now rewrite nth_error_map H.
  - cbn.
    rewrite [map_predicate _ _ _ _ (set_pparams _ _)]subst_instance_predicate_set_pparams.
    econstructor; eauto.
    eapply OnOne2_map. eapply OnOne2_impl. 1: eassumption.
    (* Used to be pcuicfo *)
    simpl in *; intuition; simpl in *.
  - cbn.
    rewrite [map_predicate _ _ _ _ (set_preturn _ _)]subst_instance_predicate_set_preturn.
    eapply case_red_return; eauto with pcuic.
    rewrite subst_instance_app in IHX0.
    now rewrite -inst_case_predicate_context_subst_instance.
  - cbn. econstructor; eauto with pcuic.
    * eapply OnOne2_map. eapply OnOne2_impl; [eassumption | pcuicfo];
      unfold on_Trel; simpl; intuition eauto.
      rewrite /map_branch /id.
      now rewrite subst_instance_app inst_case_branch_context_subst_instance in b0.
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. now red.
  - cbn. eapply fix_red_ty.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply fix_red_body.
    eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red; split; cbn; eauto.
    rewrite subst_instance_app in r0.
    now rewrite -(fix_context_subst_instance u mfix0).
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply cofix_red_body.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
    rewrite subst_instance_app in r0.
    now rewrite <- (fix_context_subst_instance u mfix0).
  - cbn. eapply array_red_val. eapply OnOne2_map. cbn. solve_all.
Qed.

Lemma subst_instance_ws_cumul_pb {cf : checker_flags} (Σ : global_env_ext) Γ u A B univs :
valid_constraints (global_ext_constraints (Σ.1, univs))
                  (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A = B ->
  (Σ.1,univs) ;;; subst_instance u Γ |- subst_instance u A = subst_instance u B.
Proof.
  intros HH X0. induction X0.
  - econstructor.
    eapply eq_term_subst_instance; tea.
  - econstructor 2. 1: eapply red1_subst_instance; cbn; eauto. eauto.
  - econstructor 3. 1: eauto. eapply red1_subst_instance; cbn; eauto.
Qed.

Lemma cumul_subst_instance {cf : checker_flags} (Σ : global_env_ext) Γ u A B univs :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A <= B ->
  (Σ.1,univs) ;;; subst_instance u Γ
                   |- subst_instance u A <= subst_instance u B.
Proof.
  intros HH X0. induction X0.
  - econstructor.
    eapply leq_term_subst_instance; tea.
  - econstructor 2. 1: eapply red1_subst_instance; cbn; eauto. eauto.
  - econstructor 3. 1: eauto. eapply red1_subst_instance; cbn; eauto.
Qed.

Lemma is_allowed_elimination_subst_instance {cf : checker_flags} (Σ : global_env_ext) univs inst u al :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs inst Σ) ->
  is_allowed_elimination Σ al u ->
  is_allowed_elimination (global_ext_constraints (Σ.1, univs)) al (subst_instance_sort inst u).
Proof.
  destruct al, u as [| | u]; trivial.
  intros val [H|isal] => //; right. cbn in isal |- *.
  unfold_univ_rel eqn:H.
  eapply satisfies_subst_instance_ctr in val; eauto.
  specialize (isal _ val).
  rewrite subst_instance_universe_val'; auto.
Qed.

Global Instance compare_decl_subst_instance {cf : checker_flags} pb Σ : SubstUnivPreserved (fun φ => compare_decl Σ φ pb).
Proof.
  intros φ1 φ2 u HH ? ? [] => /=; constructor; auto;
   eapply compare_term_subst_instance; tea.
Qed.

Global Instance compare_context_subst_instance {cf : checker_flags} pb Σ : SubstUnivPreserved (fun φ => compare_context Σ φ pb).
Proof.
  intros φ φ' u HH Γ Γ' X. eapply All2_fold_map, All2_fold_impl; tea.
  intros. eapply compare_decl_subst_instance; eassumption.
Qed.

Lemma subst_instance_destArity Γ A u :
  destArity (subst_instance u Γ) (subst_instance u A)
  = match destArity Γ A with
    | Some (ctx, s) => Some (subst_instance u ctx, subst_instance_sort u s)
    | None => None
    end.
Proof.
  induction A in Γ |- *; simpl; try reflexivity.
  - change (subst_instance u Γ,, vass na (subst_instance_constr u A1))
      with (subst_instance u (Γ ,, vass na A1)).
    now rewrite IHA2.
  - change (subst_instance u Γ ,,
               vdef na (subst_instance_constr u A1) (subst_instance_constr u A2))
      with (subst_instance u (Γ ,, vdef na A1 A2)).
    now rewrite IHA3.
Qed.

Lemma subst_instance_decompose_prod_assum u Γ t :
  subst_instance u (decompose_prod_assum Γ t)
  = decompose_prod_assum (subst_instance u Γ) (subst_instance u t).
Proof.
  induction t in Γ |- *; cbnr.
  - apply IHt2.
  - apply IHt3.
Qed.

Lemma subst_instance_decompose_app_rec u Γ t
  : subst_instance u (decompose_app_rec t Γ)
    = decompose_app_rec (subst_instance u t) (subst_instance u Γ).
Proof.
  induction t in Γ |- *; cbnr.
  now rewrite IHt1.
Qed.

Lemma subst_instance_decompose_app u t
  : subst_instance u (decompose_app t) = decompose_app (subst_instance u t).
Proof.
  unfold decompose_app. now rewrite (subst_instance_decompose_app_rec u []).
Qed.

Lemma subst_instance_smash u Γ Δ :
  subst_instance u (smash_context Δ Γ) =
  smash_context (subst_instance u Δ) (subst_instance u Γ).
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto.
  - rewrite IHΓ. f_equal.
    now rewrite subst_instance_subst_context.
  - rewrite IHΓ subst_instance_app; trivial.
Qed.

Lemma destInd_subst_instance u t :
  destInd (subst_instance u t) = option_map (fun '(i, u') => (i, subst_instance u u')) (destInd t).
Proof.
  destruct t; simpl; try congruence.
  f_equal.
Qed.

Lemma subst_instance_check_one_fix u mfix :
  List.map
        (fun x : def term =>
        check_one_fix (map_def (subst_instance u) (subst_instance u) x)) mfix =
  List.map check_one_fix mfix.
Proof.
  apply map_ext. intros [na ty def rarg]; simpl.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  erewrite <-(subst_instance_decompose_prod_assum u []).
  destruct (decompose_prod_assum [] ty) eqn:decty.
  rewrite app_context_nil_l in decomp.
  injection decomp. intros -> ->. clear decomp.
  simpl. rewrite !app_context_nil_l -(subst_instance_smash u _ []).
  unfold subst_instance, map_context.
  rewrite <- map_rev. rewrite nth_error_map.
  destruct nth_error as [d|] eqn:Hnth; simpl; auto.
  rewrite <- subst_instance_decompose_app.
  destruct (decompose_app (decl_type d)) eqn:Happ.
  simpl.
  rewrite destInd_subst_instance.
  destruct destInd as [[i u']|]; simpl; auto.
Qed.

Lemma subst_instance_check_one_cofix u mfix :
  List.map
        (fun x : def term =>
        check_one_cofix (map_def (subst_instance u) (subst_instance u) x)) mfix =
  List.map check_one_cofix mfix.
Proof.
  apply map_ext. intros [na ty def rarg]; simpl.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  rewrite <- (subst_instance_decompose_prod_assum _ []).
  destruct (decompose_prod_assum [] ty) eqn:decty.
  rewrite app_context_nil_l in decomp.
  injection decomp; intros -> ->; clear decomp.
  simpl.
  destruct (decompose_app t0) eqn:Happ.
  rewrite <- subst_instance_decompose_app, Happ. simpl.
  rewrite destInd_subst_instance.
  destruct destInd as [[i u']|]; simpl; auto.
Qed.

Lemma All_local_env_over_subst_instance {cf : checker_flags} Σ Γ (wfΓ : wf_local Σ Γ) :
  All_local_env_over (typing Σ)
                     (fun Γ0 (_ : wf_local Σ Γ0) t T (_ : Σ;;; Γ0 |- t : T) =>
       forall u univs, wf_ext_wk Σ ->
                  consistent_instance_ext (Σ.1, univs) Σ.2 u ->
                  (Σ.1, univs) ;;; subst_instance u Γ0
                  |- subst_instance u t : subst_instance u T)
                     Γ wfΓ ->
  forall u univs,
    wf_ext_wk Σ ->
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    wf_local (Σ.1, univs) (subst_instance u Γ).
Proof.
  induction 1; simpl; rewrite /subst_instance /=; constructor; cbn in *; auto.
  all: eapply lift_sorting_fu_it_impl with (tu := tu); cbn in *; eauto using relevance_subst.
Qed.

#[global] Hint Resolve All_local_env_over_subst_instance : univ_subst.

Lemma in_var_global_ext {cf : checker_flags} n Σ :
  wf Σ.1 ->
  LevelSet.In (Level.lvar n) (global_ext_levels Σ) ->
  LevelSet.In (Level.lvar n) (levels_of_udecl Σ.2).
Proof.
  intros wfΣ Hin.
  eapply LevelSet.union_spec in Hin.
  destruct Hin; auto.
  eapply not_var_global_levels in wfΣ.
  specialize (wfΣ (Level.lvar n) H).
  now simpl in wfΣ.
Qed.

Lemma monomorphic_level_in_global_ext l Σ :
  LevelSet.In (Level.level l) (global_ext_levels Σ) ->
  LevelSet.In (Level.level l) (global_levels Σ).
Proof.
  unfold global_ext_levels.
  intros [hin|hin] % LevelSet.union_spec.
  - now eapply monomorphic_level_notin_levels_of_udecl in hin.
  - apply hin.
Qed.

Lemma add_make l n : LevelExpr.add n (LevelExpr.make l) = (l, n).
Proof.
  rewrite /LevelExpr.add //=; lia_f_equal.
Qed.

Lemma subst_instance_level_spec x i l :
  LevelExprSet.In x (subst_instance_level i l) <->
  (~ Level.is_var l /\ x = LevelExpr.make l) \/ exists n, l = Level.lvar n /\
  if nth_error i n is (Some u) then LevelExprSet.In x u
  else x = (Level.lzero, 0).
Proof.
  destruct l.
  - cbn. setoid_rewrite LevelExprSet.singleton_spec. firstorder.
    congruence.
  - cbn; rewrite LevelExprSet.singleton_spec. firstorder congruence.
  - cbn. destruct nth_error eqn:hnth => //.
    * firstorder subst; auto => //.
      + right. exists n; split => //. now rewrite hnth.
      + now noconf H; rewrite hnth in H0.
    * rewrite LevelExprSet.singleton_spec. firstorder subst.
      + right. exists n. split => //; rewrite hnth. reflexivity.
      + now elim H.
      + noconf H. rewrite hnth in H0. subst. reflexivity.
Qed.

Lemma subst_instance_level_expr_spec x i le :
  LevelExprSet.In x (subst_instance_level_expr i le) <->
  (~ Level.is_var le.1 /\ x = le) \/ exists n k, le = (Level.lvar n, k) /\
   if nth_error i n is (Some u) then LevelExprSet.In x (Universe.plus k u)
  else x = (Level.lzero, k).
Proof.
  destruct le as [l k].
  cbn -[subst_instance_level].
  rewrite Universe.map_spec.
  setoid_rewrite subst_instance_level_spec.
  split.
  - move=> -[] e.
    firstorder subst.
    * left. now rewrite add_make.
    * right. exists x0, k. split => //. destruct nth_error => //.
      + rewrite Universe.map_spec. exists e; split => //.
      + subst. now rewrite add_make.
  - move=> -[] h.
    * destruct h as []. subst x. exists (l, 0). rewrite add_make; split => //.
      left. split => //.
    * destruct h as [n [k' [heq hnth]]].
      destruct nth_error eqn:hnth'.
      + noconf heq.
        apply Universe.map_spec in hnth as [? []]. subst x.
        exists x0; split => //.
        right. exists n; split => //.
        now rewrite hnth'.
      + noconf heq. subst x. exists (LevelExpr.make Level.lzero).
        rewrite add_make. split => //. right. eexists; split; trea.
        now rewrite hnth'.
Qed.

Lemma wf_universe_subst_instance {cf : checker_flags} (Σ : global_env_ext) univs ui u :
   wf Σ ->
   wf_universe Σ u ->
   consistent_instance_ext (Σ.1, univs) Σ.2 ui ->
   wf_universe (Σ.1, univs) (subst_instance ui u).
Proof.
  intros wfΣ Hl Hu e [[l n] [inl eq]]%In_subst_instance.
  apply subst_instance_level_expr_spec in eq as [H|H].
  - cbn in H. destruct H as [nvar ->].
    specialize (Hl (l, n) inl).
    destruct l => //.
    + cbn. eapply global_ext_levels_InSet.
    + cbn. apply monomorphic_level_in_global_ext in Hl.
      now eapply LS.union_spec.
  - destruct H as [n' [k [heq hnth]]].
    noconf heq.
    destruct nth_error eqn:hnth'.
    * eapply Universe.map_spec in hnth as [? []]; subst e.
      cbn.
      specialize (Hl (Level.lvar n', n) inl).
      eapply LS.union_spec in Hl as [Hl|Hl].
      + red in Hu. unfold levels_of_udecl in Hl.
        destruct Σ.2.
        { simpl in Hu. apply nth_error_Some_length in hnth'.
          destruct ui; try discriminate. lsets. }
        { destruct Hu as [declu [us vc]].
          eapply forallb_Forall in declu.
          eapply nth_error_forall in declu; eauto.
          simpl in declu. now eapply LS.subset_spec, subset_levels in declu. }
      + now apply not_var_global_levels in Hl.
   * subst e.
    now apply global_ext_levels_InSet.
Qed.

Lemma wf_sort_subst_instance {cf : checker_flags} (Σ : global_env_ext) univs ui s :
   wf Σ ->
   wf_sort Σ s ->
   consistent_instance_ext (Σ.1, univs) Σ.2 ui ->
   wf_sort (Σ.1, univs) (subst_instance ui s).
Proof.
  destruct s as [| | u]; cbnr.
  apply wf_universe_subst_instance.
Qed.

Definition global_context_set Σ : ContextSet.t := universes Σ.

Lemma global_context_set_sub_ext Σ φ :
  sub_context_set (global_context_set Σ) (global_ext_context_set (Σ, φ)).
Proof.
  split.
  - cbn. unfold global_ext_levels. cbn.
    unfold global_levels.
    intros x hin. apply LevelSet.union_spec; right.
    now apply LevelSet.union_spec; left.
  - apply UnivConstraintSetProp.union_subset_2.
Qed.

Definition wf_global_ext {cf : checker_flags} Σ ext := wf_ext_wk (Σ, ext).

From Stdlib Require Import Morphisms.
From Stdlib Require Import ssreflect.
Set SimplIsCbn.

Infix "$" := Basics.compose (at level 20).
Infix "@@" := Basics.apply (at level 20).

Lemma unfold_eq {A} (f : nat -> A) n x :
  (#|x| = n /\ forall i, i < n -> nth_error x i = Some (f i)) ->
  unfold n f = x.
Proof.
  intros hf.
  induction n in x, hf |- *; cbn.
  - destruct hf as [hl hf]. destruct x => //.
  - destruct x using rev_ind; destruct hf as [hl hf] => //.
    have he : #|x0| = n.
    { rewrite length_app //= in hl. lia. }
    f_equal.
    + eapply IHn.
      split => //.
      move=> i hlt; rewrite -hf; try lia.
      rewrite nth_error_app.
      destruct (Nat.ltb_spec i #|x0|) => //. lia.
    + f_equal. move: (hf n) => /fwd //.
      rewrite nth_error_app.
      destruct (Nat.ltb_spec n #|x0|) => //.
      * lia.
      * subst n. rewrite Nat.sub_diag nth_error_0 //=.
        now intros [= ->].
Qed.

Section SubstIdentity.
  Context `{cf:checker_flags}.

  Lemma subst_instance_id_mdecl Σ u mdecl :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    subst_instance u (Instance.of_level_instance @@ abstract_instance (ind_universes mdecl)) = u.
  Proof using Type.
    intros cu.
    red in cu. red in cu.
    destruct (ind_universes mdecl) eqn:eqi.
    - destruct u; simpl in cu; try discriminate.
      reflexivity.
    - simpl. destruct cst as [univs csts]. simpl.
      rewrite map_map map_mapi. simpl. simpl in cu.
      destruct cu as [Hu [sizeu vu]].
      rewrite mapi_unfold.
      set (f := fun i : nat => _).
      apply unfold_eq. split => //.
      move=> i h.
      subst f. cbn.
      rewrite subst_instance_level_expr_make //=.
      rewrite plus_0. elim: nth_error_spec => //. lia.
  Qed.

  Lemma declared_inductive_wf_ext_wk Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    wf_ext_wk (Σ, ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli. eapply declared_minductive_to_gen in decli.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
    red. simpl. split; auto.
    Unshelve. all:eauto.
  Qed.

  Lemma declared_inductive_wf_global_ext Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    wf_global_ext Σ (ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli. eapply declared_minductive_to_gen in decli.
    split; auto.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
    Unshelve. all:eauto.
  Qed.

  Hint Resolve declared_inductive_wf_ext_wk declared_inductive_wf_global_ext : pcuic.

  Lemma subst_instance_level_abs l n Σ :
    wf Σ ->
    LevelSet.In l (LevelSet.union
     (fold_right LevelSet.add LevelSet.empty
        (unfold n Level.lvar)) (global_levels Σ)) ->
    subst_level_instance_level (unfold n Level.lvar) l = l.
  Proof using Type.
    intros wfΣ lin.
    eapply LevelSet.union_spec in lin.
    destruct lin.
    - apply LevelSet_In_fold_right_add in H.
      destruct l; simpl; auto.
      eapply In_unfold_inj in H; [|congruence].
      pose proof (proj1 (nth_error_unfold Level.lvar n n0) H).
      now rewrite (nth_error_nth _ _ _ H0).
    - eapply not_var_global_levels in wfΣ.
      specialize (wfΣ l H). simpl in wfΣ.
      destruct l => //.
  Qed.

  Lemma subst_instance_universe_abs (l : Universe.t) n Σ :
    wf Σ ->
    LevelSet.Subset (Universe.levels l) (LevelSet.union
     (fold_right LevelSet.add LevelSet.empty
        (unfold n Level.lvar)) (global_levels Σ)) ->
    l@@[unfold n Level.lvar] = l.
  Proof using Type.
    intros wfΣ lin.
    apply equal_exprsets => l'.
    rewrite /subst_level_instance_universe.
    rewrite Universe.map_spec.
    rewrite /subst_level_instance_level_expr.
    split.
    - move=> -[e [hin hs]]. subst l'. rewrite subst_instance_level_abs.
      * apply lin. apply levels_spec. exists e.2. now destruct e.
      * destruct e => //.
    - move=> hin. exists l'. split => //. rewrite subst_instance_level_abs.
      * apply lin, levels_spec. exists l'.2; now destruct l'.
      * destruct l' => //.
  Qed.

  Lemma map_singleton f le : Universe.map f (singleton le) = singleton (f le).
  Proof.
    apply equal_exprsets=> l; rewrite Universe.map_spec. firstorder subst.
    * apply LevelExprSet.singleton_spec. now apply LevelExprSet.singleton_spec in H; subst.
    * apply LevelExprSet.singleton_spec in H. subst l. exists le. split => //. now apply LevelExprSet.singleton_spec.
  Qed.

  Lemma map_add f le u : Universe.map f (add le u) = add (f le) (Universe.map f u).
  Proof using Type.
    clear cf.
    apply equal_exprsets=> l; rewrite Universe.map_spec. firstorder subst.
    * apply LevelExprSet.add_spec. apply LevelExprSet.add_spec in H as [H|H]; subst; auto.
      right. apply map_spec. now exists x.
    * setoid_rewrite LevelExprSet.add_spec. apply LevelExprSet.add_spec in H as [H|H].
      + subst l. now exists le; split.
      + apply map_spec in H as [e []]. exists e. split => //. now right.
  Qed.

  Lemma subst_level_instance_level_instance_level {i} {l : Level.t} :
    Universe.of_level (subst_level_instance_level i l) = subst_instance_level i l.
  Proof.
    destruct l => //=.
    rewrite (nth_nth_error n i).
    rewrite nth_error_map.
    destruct nth_error => //=.
  Qed.

  Lemma plus_of_level n l : Universe.plus n (Universe.of_level l) = Universe.make (l, n).
  Proof using Type.
    clear cf.
    apply equal_exprsets => lk.
    rewrite Universe.map_spec /Universe.make singleton_spec /Universe.of_level.
    setoid_rewrite singleton_spec. firstorder subst.
    - now rewrite add_make.
    - exists (l, 0). split => //; rewrite /LevelExpr.add //= Nat.add_0_r //.
  Qed.

  Lemma subst_level_instance_singleton {i le} :
    (singleton le)@@[i] = Universe.singleton (subst_level_instance_level_expr i le).
  Proof. rewrite /subst_level_instance /subst_instance_level_expr; cbn.
    rewrite /subst_level_instance_universe map_singleton.
    rewrite /subst_level_instance_level_expr. destruct le as [l k]; cbn.
    reflexivity.
  Qed.

  Lemma subst_level_instance_singleton_level_expr {i le} :
    (singleton le)@@[i] = subst_instance_level_expr i le.
  Proof. rewrite /subst_level_instance /subst_instance_level_expr; cbn.
    rewrite /subst_level_instance_universe map_singleton.
    rewrite /subst_level_instance_level_expr. destruct le as [l k]; cbn.
    now rewrite -subst_level_instance_level_instance_level plus_of_level.
  Qed.

  Lemma subst_level_instance_add {i le u} :
    (add le u)@@[i] = (subst_instance_level_expr i le ∪ u@@[i])%nes.
  Proof. rewrite /subst_level_instance; cbn.
    rewrite [subst_level_instance_universe _ _]map_add.
    rewrite -subst_level_instance_singleton_level_expr.
    rewrite -Universe.union_add_singleton union_comm.
    now rewrite subst_level_instance_singleton.
  Qed.

  Lemma subst_level_instance_subst_instance_univ {u : Universe.t} {i} :
    u@@[i] = u@[i].
  Proof.
    apply equal_exprsets => l.
    move: u; apply elim.
    - move=> le. now rewrite subst_level_instance_singleton_level_expr.
    - move=> le x ih hnin.
      now rewrite subst_level_instance_add add_subst !LevelExprSet.union_spec ih.
  Qed.

  Lemma subst_level_instance_subst_instance_instance {u i} :
    u@@[i] = u@[i].
  Proof.
    apply map_ext.
    intros x.
    apply subst_level_instance_subst_instance_univ.
  Qed.

  Lemma subst_level_instance_instance_cstr {u cstr} :
    subst_level_instance_univ_cstr u cstr = subst_instance_univ_cstr u cstr.
  Proof.
    destruct cstr as [[l d] r]; cbn.
    rewrite /subst_level_instance_univ_cstr /subst_instance_univ_cstr //=.
    now rewrite !subst_level_instance_subst_instance_univ.
  Qed.

  Lemma subst_level_instance_instance_cstrs {u cstrs} :
    subst_level_instance_cstrs u cstrs =_ucset subst_instance_cstrs u cstrs.
  Proof.
    intros c.
    rewrite In_subst_instance_cstrs In_subst_level_instance_cstrs.
    split => -[cstr [-> hin]]; exists cstr; now rewrite subst_level_instance_instance_cstr.
  Qed.

  Lemma consistent_instance_ext_abstract_instance Σ udecl :
    wf Σ ->
    wf_global_ext Σ udecl ->
    consistent_instance_ext (Σ, udecl) udecl (abstract_instance udecl).
  Proof using Type.
    intros wfΣ wf_glob_ext.
    red. red.
    destruct udecl as [|[univs cst]] eqn:indu.
    { simpl. reflexivity. }
    split; [|split].
    - simpl abstract_instance.
      rewrite forallb_map.
      eapply forallb_mapi => //.
      intros i Hi. unfold global_ext_levels.
      apply LevelSet.subset_spec. rewrite levels_singleton subset_singleton //=.
      apply LevelSet.union_spec. left.
      unfold levels_of_udecl. simpl.
      rewrite (mapi_unfold Level.lvar).
      eapply LevelSet_In_fold_right_add.
      induction #|univs| in i, Hi |- *; try lia.
      simpl. eapply in_or_app. destruct (eq_dec i n).
      * subst. right; simpl; auto.
      * left; apply IHn; lia.
    - now rewrite length_map mapi_length.
    - simpl. rewrite (mapi_unfold Level.lvar).
      assert(UCS.Equal (subst_level_instance_cstrs (unfold #|univs| Level.lvar) cst) cst).
      { unfold UCS.Equal; intros a.
        unfold subst_level_instance_cstrs.
        red in wf_glob_ext.
        destruct wf_glob_ext as [_ wfext].
        unfold on_udecl_prop in wfext.
        simpl constraints_of_udecl in wfext.
        simpl levels_of_udecl in wfext.
        rewrite (mapi_unfold Level.lvar) in wfext.
        clear indu.
        simpl fst in wfext.
        revert wfext.
        eapply UnivConstraintSetProp.fold_rec_weak; auto.
        2:reflexivity.
        * intros s s' a' eqs H.
          intros Hf.
          rewrite <- eqs in Hf. rewrite -eqs; auto.
        * intros x a0 s nin equiv.
          intros cadd.
          eapply CS_For_all_add in cadd as [cadd Ps].
          specialize (equiv Ps). clear Ps.
          destruct x as [[l c] r]. destruct cadd as [inl inr].
          unfold subst_level_instance_univ_cstr. simpl.
          eapply subst_instance_universe_abs in inl; auto.
          + eapply subst_instance_universe_abs in inr; auto.
            rewrite inl inr.
          rewrite !UCS.add_spec.
          intuition auto. }
      unfold valid_constraints. destruct check_univs; auto.
      unfold valid_constraints0. simpl.
      unfold satisfies.
      intros v.
      rewrite subst_level_instance_instance_cstrs in H.
      rewrite H.
      eapply CS_For_all_union.
  Qed.

  Lemma udecl_prop_in_var_poly {Σ n} : on_udecl_prop Σ.1 Σ.2 -> LevelSet.In (Level.lvar n) (levels_of_udecl Σ.2) ->
    ∑ ctx, Σ.2 = Polymorphic_ctx ctx.
  Proof using cf.
    intros onu lin.
    destruct (Σ.2); intuition eauto.
    simpl in lin, onu. lsets.
  Qed.

  Lemma subst_abs_level Σ u :
    wf_ext_wk Σ ->
    LevelSet.In u (global_ext_levels Σ) ->
    subst_instance_level (abstract_instance Σ.2) u = Universe.of_level u.
  Proof using Type.
    intros [wfΣ onu] decl'.
    destruct u; simpl; auto. cbn -[LevelSet.subset global_ext_levels] in decl'.
    eapply in_var_global_ext in decl'; auto.
    destruct (udecl_prop_in_var_poly onu decl') as [[univs csts] eq].
    rewrite eq in decl' |- *. simpl in *.
    rewrite mapi_unfold in decl' |- *.
    eapply LevelSet_In_fold_right_add in decl'.
    eapply In_unfold_inj in decl'; try congruence.
    eapply (nth_error_unfold Level.lvar) in decl'.
    rewrite nth_error_map decl' //=.
  Qed.

  Lemma subst_abs_level_expr Σ (u : LevelExpr.t) :
    wf_ext_wk Σ ->
    LevelSet.In u.1 (global_ext_levels Σ) ->
    subst_instance_level_expr (abstract_instance Σ.2) u = Universe.make u.
  Proof using Type.
    intros [wfΣ onu] decl'.
    destruct u; simpl; auto. cbn -[LevelSet.subset global_ext_levels] in decl'.
    rewrite /subst_instance_level_expr subst_abs_level //=.
    now rewrite plus_of_level.
  Qed.

  Lemma subst_abs_universe Σ u :
    wf_ext_wk Σ ->
    LevelSet.Subset (levels u) (global_ext_levels Σ) ->
    subst_instance (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros [wfΣ onu] decl'.
    apply equal_exprsets => l.
    rewrite In_subst_instance.
    split.
    + intros [x' [hin hin']].
      rewrite subst_abs_level_expr in hin' => //.
      * apply decl', levels_spec. exists x'.2; now destruct x'.
      * apply LevelExprSet.singleton_spec in hin'. now subst.
    + intros hin. exists l. split => //.
      rewrite subst_abs_level_expr //.
      * apply decl', levels_spec. now exists l.2; destruct l.
      * now apply LevelExprSet.singleton_spec.
  Qed.


  Lemma consistent_instance_ext_subst_abs Σ decl u :
    wf_ext_wk Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) u = u.
  Proof.
    intros [wfΣ onu] cu.
    destruct decl.
    - simpl in cu. destruct u; simpl in *; try discriminate; auto.
    - destruct cu as [decl' [sizeu vc]].
      clear sizeu vc.
      induction u; simpl; auto. cbn in decl'.
      move/andb_and: decl' => [ina au]. specialize (IHu au).
      rewrite [subst_instance_universe _ _]subst_abs_universe //.
      * now apply LevelSet.subset_spec in ina.
      * now rewrite [ListDef.map _ _]IHu.
  Qed.

  Lemma consistent_instance_ext_subst_abs_univ Σ u :
    wf_ext_wk Σ ->
    wf_sort Σ u ->
    subst_instance_sort (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros wf cu.
    destruct u; simpl; auto. f_equal.
    rewrite subst_abs_universe //. cbn in cu.
    move=> l /levels_spec -[] k; apply cu.
  Qed.

  Lemma consistent_instance_ext_subst_abs_inds Σ decl ind u bodies :
    wf_ext_wk Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) (inds ind u bodies) =
      (inds ind u bodies).
  Proof using Type.
    intros wf cu.
    unfold inds. generalize #|bodies|.
    induction n; simpl; auto. rewrite IHn; f_equal.
    f_equal.
    now rewrite [subst_instance_instance _ _](consistent_instance_ext_subst_abs _ _ _ wf cu).
  Qed.

  Lemma wf_sort_type1 Σ : wf_sort Σ Sort.type1.
  Proof using Type.
    simpl.
    intros l hin%LevelExprSet.singleton_spec.
    subst l. simpl.
    apply global_ext_levels_InSet.
  Qed.

  Lemma wf_sort_super {Σ u} : wf_sort Σ u -> wf_sort Σ (Sort.super u).
  Proof using Type.
    destruct u; cbn.
    1-2:intros _ l hin%LevelExprSet.singleton_spec; subst l; apply wf_sort_type1;
     now apply LevelExprSet.singleton_spec.
    intros Hl.
    intros l hin.
    eapply Universes.spec_map_succ in hin as [x' [int ->]].
    simpl. now specialize (Hl _ int).
  Qed.

  Lemma app_inj {A} (l l' l0 l0' : list A) :
    #|l| = #|l0| ->
    l ++ l' = l0 ++ l0' ->
    l = l0 /\ l' = l0'.
  Proof using Type.
    induction l in l', l0, l0' |- *; destruct l0; simpl in * => //; auto.
    intros [= eq] [= -> eql].
    now destruct (IHl _ _ _ eq eql).
  Qed.

  Lemma subst_abstract_instance_id :
    env_prop (fun Σ Γ t T =>
        wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u t = t × subst_instance u T = T)
        (fun Σ _ j => wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        lift_wfu_term (fun t => subst_instance u t = t) (fun t => subst_instance u t = t) j)
        (fun Σ Γ =>
        wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u Γ = Γ).
  Proof using Type.
    eapply typing_ind_env; intros; simpl in *; auto.
    { apply lift_typing_subjtyp with (1 := X). 2: intros s Hs; now depelim Hs.
      intros ?? []; auto. }

    { apply All_local_env_cst in X0. clear -X0 X1.
      eapply All2_eq, All2_map_left. apply All_All2 with (1 := X0) => decl IH.
      destruct IH as (? & ? & ?), decl as [na bo ty]; tas; unfold map_decl; cbn in *.
      f_equal; tas. destruct bo => //. cbn in *. now f_equal. }

    all: try ((subst u || subst u0); split; [f_equal|]; intuition eauto).

    1:{ rewrite subst_instance_lift. f_equal.
      generalize H. rewrite -H1 /subst_instance /= nth_error_map H /= => [=].
      intros Hdecl. now rewrite -{2}Hdecl. }

    all: try match goal with H : lift_wfu_term _ _ _ |- _ => destruct H as (Htm & Hty & Hs); cbn in Htm, Hty, Hs end.
    all:try (solve [f_equal; eauto; try congruence]).
    all:try (rewrite ?subst_instance_two; f_equal; eapply consistent_instance_ext_subst_abs; eauto).

    - now rewrite consistent_instance_ext_subst_abs_univ.

    - rewrite consistent_instance_ext_subst_abs_univ //.
      now apply wf_sort_super.

    - rewrite product_subst_instance. do 2 f_equal; tas.
      now noconf b0.

    - intuition auto. noconf a; noconf b; noconf b0.
      rewrite subst_instance_subst /= /subst1.
      repeat (f_equal; simpl; auto).

    - rewrite /type_of_constructor subst_instance_subst subst_instance_two.
      erewrite consistent_instance_ext_subst_abs; eauto. f_equal.
      eapply consistent_instance_ext_subst_abs_inds; eauto.

    - solve_all; simpl in *.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        now noconf Hi.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        rewrite -{2}(map_id (pparams p)) in Hpars.
        now apply map_eq_inj in Hpars.

    - solve_all.

    - rewrite subst_instance_mkApps. f_equal.
      * rewrite /ptm.
        rewrite subst_instance_it_mkLambda_or_LetIn.
        rewrite subst_instance_app in H.
        eapply app_inj in H as []; [|now len].
        rewrite H. now f_equal.
      * rewrite map_app.
        rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        now rewrite hinds /= a0.
    - rewrite subst_instance_subst /=.
      rewrite /subst_instance /=.
      rewrite subst_instance_mkApps in b.
      eapply mkApps_nApp_inj in b as [Hi Hpars] => //.
      f_equal.
      * rewrite a; f_equal.
        rewrite /subst_instance_list. now rewrite map_rev Hpars.
      * rewrite [subst_instance_constr _ _]subst_instance_two.
        noconf Hi. now rewrite [subst_instance _ u]H.
    - solve_all.
      + destruct a0 as (_ & X & _); tas.
      + destruct b as (X & _); tas.
    - eapply nth_error_all in X0 as (_ & X0 & _); tea.
    - solve_all.
      + destruct a0 as (_ & X & _); tas.
      + destruct b as (X & _); tas.
    - eapply nth_error_all in X0 as (_ & X0 & _); tea.
    - destruct p as [? []]; cbnr. do 2 f_equal.
      depelim X0. specialize (hty X1); specialize (hdef X1).
      unfold mapu_array_model; destruct a; cbn -[Universe.of_level] in *.
      f_equal; intuition eauto.
      * rewrite [subst_instance_universe _ _]subst_abs_universe //.
        eapply subset_levels, wfl.
      * solve_all.
    - depelim X0; cbn => //=. depelim X. simp prim_type. cbn. f_equal; intuition eauto.
      do 2 f_equal.
      cbn -[Universe.of_level] in b.
      rewrite [subst_instance_universe _ _]subst_abs_universe //.
      apply subset_levels, wfl.
  Qed.

  Lemma typed_subst_abstract_instance Σ Γ t T :
    wf_ext_wk Σ ->
    Σ ;;; Γ |- t : T ->
    let u := abstract_instance Σ.2 in
    subst_instance u t = t.
  Proof using Type.
    intros [wfΣ onu] H. eapply (env_prop_typing subst_abstract_instance_id) in H as [H H']; eauto.
    split; auto.
  Qed.

  Lemma subst_instance_id Σ Γ :
    wf_ext_wk Σ ->
    wf_local Σ Γ ->
    let u := abstract_instance Σ.2 in
    subst_instance u Γ = Γ.
  Proof using Type.
    intros. eapply (env_prop_wf_local subst_abstract_instance_id) in X0; eauto.
  Qed.

End SubstIdentity.
