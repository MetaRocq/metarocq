From Stdlib Require Import PArith NArith ZArith Lia ssreflect ssrbool ssrfun Morphisms.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import MRList MROption MRUtils.
From MetaRocq.Common Require Import uGraph.
From MetaRocq.Common Require Import Universes.
(* Import wGraph. *)
Import UnivLoopChecking.UnivLoopChecking.

Definition levels_of_cs (cs : UnivConstraintSet.t) : LevelSet.t :=
  LevelSet.remove Level.lzero (univ_constraints_levels cs).

Lemma levelset_add_remove {l s} : LevelSet.add l (LevelSet.remove l s) =_lset LevelSet.add l s.
Proof.
  intros l'. split. lsets.
  destruct (Classes.eq_dec l l'). subst.
  - move/LevelSet.add_spec => -[heq|hin] //; lsets.
  - move/LevelSet.add_spec => -[heq|hin] //; lsets.
Qed.

Lemma levelset_subset_add {ls ls' l} : LevelSet.Subset ls ls' -> LevelSet.Subset ls (LevelSet.add l ls').
Proof.
  intros l' hin. lsets.
Qed.

Lemma levels_of_cs_spec cstr (lvls := levels_of_cs cstr)
  : uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  subst lvls; cbv [levels_of_cs].
  red. cbn. split.
  - move=> /LevelSet.remove_spec => -[] //.
  - move=> cl; cbn => hin.
    apply declared_univ_cstr_levels_spec.
    rewrite levelset_add_remove; apply levelset_subset_add.
    move=> ls hin'. apply univ_constraints_levels_spec. exists cl. split => //.
Qed.

Definition consistent_dec ctrs : {@consistent ctrs} + {~@consistent ctrs}.
Proof.
  pose proof (@uGraph.is_consistent_spec config.default_checker_flags (levels_of_cs ctrs, ctrs) (levels_of_cs_spec ctrs)) as H.
  destruct uGraph.is_consistent; [ left; apply H | right; intro H'; apply H in H' ]; auto.
Defined.



(* Lemma global_uctx_invariants_subset {ls ls' cs} :
  LevelSet.Subset ls ls' ->
  global_uctx_invariants (ls', cs) ->
  global_uctx_invariants (ls, cs).
Proof.
  intros hs [hnz hu]; red in hu; cbn in hu;
  red; cbn. split => //. now rewrite hs.
  red; cbn. rewrite hs.
Qed. *)


Definition levels_of_cs2 (cs1 cs2 : UnivConstraintSet.t) : LevelSet.t
  := LevelSet.union (levels_of_cs cs1) (levels_of_cs cs2).
Lemma levels_of_cs2_spec cs1 cs2 (lvls := levels_of_cs2 cs1 cs2)
  : uGraph.global_uctx_invariants (lvls, cs1)
    /\ uGraph.global_uctx_invariants (lvls, cs2).
Proof.
  have [hnz hs] := levels_of_cs_spec cs1.
  have [hnz' hs'] := levels_of_cs_spec cs2.
  split.
  - split. move=> /LevelSet.union_spec -[] hz; contradiction.
    red; cbn. rewrite /lvls /levels_of_cs2 levelset_add_union.
    eapply declared_univ_cstrs_levels_subset. 3:{ apply hs. } lsets. ucsets.
  - split. move=> /LevelSet.union_spec -[] hz; contradiction.
    red; cbn. rewrite /lvls /levels_of_cs2 levelset_add_union.
    eapply declared_univ_cstrs_levels_subset. 3:{ apply hs'. } lsets. ucsets.
Qed.

Definition levels_of_cscs (cs : ContextSet.t) (cstr : UnivConstraintSet.t) : LevelSet.t
  := LevelSet.union (ContextSet.levels cs) (levels_of_cs2 cstr (ContextSet.constraints cs)).
Lemma levels_of_cscs_spec cs cstr (lvls := levels_of_cscs cs cstr)
  : ~ LevelSet.In Level.lzero (ContextSet.levels cs) ->
    uGraph.global_uctx_invariants (lvls, ContextSet.constraints cs)
    /\ uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  intros csnz.
  destruct (levels_of_cs2_spec cstr (ContextSet.constraints cs)) as [[hnz h] [hnz' h']].
  split.
  - split. subst lvls. rewrite /levels_of_cscs. cbn.
    move/LevelSet.union_spec. intuition.
    red. rewrite levelset_add_union. apply global_uctx_invariants_union_or.
    right. apply levels_of_cs2_spec.
  - split. subst lvls. rewrite /levels_of_cscs. cbn.
    move/LevelSet.union_spec. intuition.
    red. rewrite levelset_add_union. apply global_uctx_invariants_union_or.
    right. apply levels_of_cs2_spec.
Qed.

Definition levels_of_universe (u : Universe.t) : LevelSet.t := Universe.levels u.

Lemma levels_of_universe_spec u cstr (lvls := levels_of_universe u)
  : levels_declared (lvls, cstr) u.
Proof.
  subst lvls; cbv [levels_of_universe]; cbn [fst snd].
  red. intros le hin. red. cbn. apply LevelSet.add_spec. right.
  apply Universe.levels_spec. now exists le.2; destruct le.
Qed.

(* Lemma invalid_cstr cs c : ~ valid0_cstrs cs c <-> ~ (forall v, exists v,  *)

Definition consistent_extension_on_dec (cf := config.default_checker_flags) cs cstr : {@consistent_extension_on cs cstr} + {~@consistent_extension_on cs cstr}.
Proof.
  unfold consistent_extension_on.
  have hp := push_uctx_spec init_model cs.
  cbn in hp.
  destruct (push_uctx init_model cs).
  - destruct hp as [ul uc]. destruct (check_constraints u cstr) eqn:hc.
    unfold check_constraints, check_constraints_gen in hc. cbn in hc.
    left.
    intros v hsat.
    apply UnivConstraintSet.for_all_spec in hc.
    exists v. split. move=> c /hc.
    have hs := checkb_spec u cs.
    forward hs. red. admit. forward hs. red. admit.
    red in hs. specialize (hs c). forward hs. admit. rewrite [_ = true]hs.
    now move/(_ v hsat).
    intros hl. reflexivity. tc.
    right.
    intros hv.
    have [c [hin hc']] : exists c, UnivConstraintSet.In c cstr /\ @check_constraint_gen config.default_checker_flags (checkb u) c = false.
      admit.
    unfold check_constraint_gen in hc'. cbn in hc'.
    have hs := checkb_spec u cs.
    forward hs. red. admit. forward hs. red. admit.
    red in hs.
    specialize (hs c). forward hs. admit. rewrite hc' in hs.
    destruct hs => //. forward H0 => //.
    intros v' hs. specialize (hv v' hs).
    destruct hv as [v'0 [hsat heq]].
    admit.
  - admit.
Admitted.

Import Clauses.FLS.
Import UnivConstraintType.ConstraintType.

Lemma declared_univ_cstrs_levels_spec cstrs : declared_univ_cstrs_levels (univ_constraints_levels cstrs) cstrs.
Proof.
  intros cl hin. apply declared_univ_cstr_levels_spec.
  intros l; rewrite univ_constraints_levels_spec. exists cl; split => //.
Qed.

Definition leq0_universe_dec (cf := config.default_checker_flags) ϕ u u' : {@leq0_universe ϕ u u'} + {~@leq0_universe ϕ u u'}.
Proof.
  set (levels := Universe.levels u ∪ Universe.levels u' ∪ (univ_constraints_levels ϕ)).
  set (uctx := (LevelSet.remove Level.lzero levels, ϕ)).
  have hc : global_uctx_invariants uctx.
  { red. split.
    * intros hin.
      now apply LevelSet.remove_spec in hin.
    * red. cbn. subst levels.
      eapply (declared_univ_cstrs_levels_subset (univ_constraints_levels ϕ)).
      lsets. reflexivity. apply declared_univ_cstrs_levels_spec. }
  destruct (push_uctx init_model uctx) eqn:eqp.
  have := check_leqb_universe_spec u0 uctx hc => /fwd.
  { now apply push_uctx_init_model_sat. }
  move/(_ cf u u') => /fwd.
  { cbn. rewrite levelset_add_remove /levels. split; lsets. }
  move=> -[]. destruct (check_leqb_universe_gen).
  * left. red. specialize (a eq_refl). red in a. cbn in a. red in a.
    move=> v vsat; move: (a v vsat). intros sat. now depelim sat.
  * move=> _ hv; right => leq. forward hv => //.
    cbn. red. red in leq.
    move=> v /leq. now constructor.
  * apply push_uctx_init_model_unsat in eqp => //.
    left. intros v hv. elim eqp.
    exists v. eapply satisfies_union. split.
    2:{ apply satisfies_init. }
    exact hv.
Qed.

Definition leq_universe_dec cf ϕ u u' : {@leq_universe cf ϕ u u'} + {~@leq_universe cf ϕ u u'}.
Proof.
  cbv [leq_universe]; destruct (@leq0_universe_dec ϕ u u'); destruct ?; auto.
Defined.

Definition eq0_universe_dec ϕ u u' : {@eq0_universe ϕ u u'} + {~@eq0_universe ϕ u u'}.
Proof.
  pose proof (eq0_universe_leq0_universe ϕ u u') as H.
  destruct (@leq0_universe_dec ϕ u u'), (@leq0_universe_dec ϕ u' u); constructor; destruct H; split_and; now auto.
Defined.

Definition eq_universe_dec {cf ϕ} u u' : {@eq_universe cf ϕ u u'} + {~@eq_universe cf ϕ u u'}.
Proof.
  cbv [eq_universe]; destruct ?; auto using eq0_universe_dec.
Defined.

Definition eq_sort__dec {univ eq_universe}
           (eq_universe_dec : forall u u', {@eq_universe u u'} + {~@eq_universe u u'})
           s s'
  : {@eq_sort_ univ eq_universe s s'} + {~@eq_sort_ univ eq_universe s s'}.
Proof.
  cbv [eq_sort_]; repeat destruct ?; auto. all: destruct pst; auto.
Defined.

Definition eq_sort_dec {cf ϕ} s s' : {@eq_sort cf ϕ s s'} + {~@eq_sort cf ϕ s s'} := eq_sort__dec eq_universe_dec _ _.

Definition valid_constraints_dec cf ϕ cstrs : {@valid_constraints cf ϕ cstrs} + {~@valid_constraints cf ϕ cstrs}.
Proof.
  set (levels := (univ_constraints_levels ϕ) ∪ (univ_constraints_levels cstrs)).
  set (uctx := (LevelSet.remove Level.lzero levels, ϕ)).
  have hc : global_uctx_invariants uctx.
  { red. split.
    * intros hin.
      now apply LevelSet.remove_spec in hin.
    * red. cbn. subst levels.
      eapply (declared_univ_cstrs_levels_subset (univ_constraints_levels ϕ)).
      lsets. reflexivity.
      intros cl hin. apply declared_univ_cstr_levels_spec.
      intros l; rewrite univ_constraints_levels_spec. exists cl; split => //. }
  destruct (push_uctx init_model uctx) eqn:eqp.
  - have := check_constraints_spec u uctx hc => /fwd.
    { now apply push_uctx_init_model_sat. }
    move/(_ cf cstrs) => /fwd.
    { cbn. red. cbn. split. lsets. red. cbn. rewrite levelset_add_remove /levels.
      rewrite levelset_add_union. eapply (declared_univ_cstrs_levels_subset (univ_constraints_levels cstrs)). lsets.
      reflexivity. apply declared_univ_cstrs_levels_spec. }
    move=> -[]. destruct (check_constraints_gen).
    * left. red. specialize (a eq_refl). red in a. cbn in a.
      destruct config.check_univs => //.
    * move=> _ hv; right => leq. forward hv => //.
  - apply push_uctx_init_model_unsat in eqp => //.
    left. red. destruct config.check_univs => //.
    intros v sat. elim eqp.
    exists v. eapply satisfies_union. split.
    2:{ apply satisfies_init. }
    exact sat.
Qed.

Definition valid_constraints0_dec ϕ ctrs : {@valid_constraints0 ϕ ctrs} + {~@valid_constraints0 ϕ ctrs}
  := @valid_constraints_dec config.default_checker_flags ϕ ctrs.

Definition is_lSet_dec cf ϕ s : {@is_lSet cf ϕ s} + {~@is_lSet cf ϕ s}.
Proof.
  apply eq_sort_dec.
Defined.

Definition is_allowed_elimination_dec cf ϕ allowed u : {@is_allowed_elimination cf ϕ allowed u} + {~@is_allowed_elimination cf ϕ allowed u}.
Proof.
  cbv [is_allowed_elimination is_true]; destruct ?; auto;
    try solve [ repeat decide equality ].
  destruct (@is_lSet_dec cf ϕ u), Sort.is_propositional; intuition auto.
Defined.
