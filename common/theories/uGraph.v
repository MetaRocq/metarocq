(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun OrderedTypeAlt MSetAVL MSetFacts MSetProperties MSetDecide Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config UnivConstraintType Universes UnivLoopChecking.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Import ConstraintType.
Set Equations Transparent.

Definition universe_model := UnivLoopChecking.univ_model.
Definition init_model : universe_model := UnivLoopChecking.init_model.

Definition uctx_invariants (uctx : ContextSet.t)
  := UnivLoopChecking.declared_univ_cstrs_levels uctx.1 uctx.2.

Definition global_uctx_invariants (uctx : ContextSet.t)
  := ~ LevelSet.In Level.lzero uctx.1 /\ uctx_invariants uctx.

Section Push.
  Import UnivLoopChecking.

Equations push_uctx (g : universe_model) (uctx : ContextSet.t) : option universe_model :=
push_uctx g uctx with UnivLoopChecking.declare_levels g uctx.1 :=
  | Some g' => enforce_constraints g' uctx.2
  | None => None.

Instance declared_univ_cstrs_levels_proper : Proper (LevelSet.Equal ==> UnivConstraintSet.Equal ==> iff)
  declared_univ_cstrs_levels.
Proof.
  move=> ?? e ?? e'.
  rewrite /declared_univ_cstrs_levels.
  rewrite e'. rewrite /UnivConstraintSet.For_all /declared_univ_cstr_levels.
Admitted.

Definition push_uctx_precond g uctx :=
  let allcstrs := UnivConstraintSet.union uctx.2 (UnivConstraintSet.union (init_constraints_of_levels uctx.1) (constraints g)) in
  ~ (exists l, LevelSet.In l uctx.1 /\ LevelSet.In l (UnivLoopChecking.levels g)) /\
  declared_univ_cstrs_levels (LevelSet.union (levels g) uctx.1) uctx.2.

Lemma push_uctx_spec g uctx :
  let allcstrs := UnivConstraintSet.union uctx.2 (UnivConstraintSet.union (init_constraints_of_levels uctx.1) (constraints g)) in
  match push_uctx g uctx with
  | None =>
    (* Either a universe was already declared *)
    (exists l, LevelSet.In l uctx.1 /\ LevelSet.In l (UnivLoopChecking.levels g)) \/
    (* Or a universe from the constraints is unbound *)
    ~ (declared_univ_cstrs_levels (LevelSet.union (levels g) uctx.1) uctx.2) \/
    (* Or the constraints are not satisfiable *)
    (~ exists v, satisfies v allcstrs)
  | Some g' =>
    levels g' =_lset LevelSet.union uctx.1 (levels g) /\
    constraints g' =_ucset allcstrs
  end.
Proof.
  funelim (push_uctx g uctx).
  destruct enforce_constraints eqn:ec.
  - move/enforce_constraints_spec: ec => [] eql eqc.
    have hs := declare_levels_spec g uctx.1.
    rewrite Heq in hs. move: hs => [] hndecl hdecll hdeclc.
    rewrite -eql in hdecll. split => //.
    now rewrite eqc hdeclc.
  - move/enforce_constraints_None: ec.
    have := declare_levels_spec g uctx.1.
    rewrite Heq.
    move=> [] hfresh hunion hcstrs [].
    + move=> ndecl. right. left.
      rewrite [levels _]hunion in ndecl.
      now rewrite LevelSetProp.union_sym.
    + move=> incon. right. right => -[v he]. apply incon.
      exists v. now rewrite hcstrs.
  - left. have := declare_levels_spec g uctx.1.
    now rewrite Heq.
Qed.

End Push.

Import UnivLoopChecking.

Definition is_model_of_uctx m uctx :=
  levels m =_lset LevelSet.union uctx.1 (LevelSet.singleton Universes.Level.lzero) /\
  constraints m =_ucset UnivConstraintSet.union uctx.2 (init_constraints_of_levels uctx.1).

(** ** Check of consistency ** *)

Equations is_consistent (uctx : ContextSet.t) : bool :=
is_consistent uctx := isSome (push_uctx init_model uctx).

Lemma satisfies_init v ls : satisfies v (init_constraints_of_levels ls).
Proof.
  move=> c /init_constraints_of_levels_spec_inv [l [inz eq]].
  destruct l; noconf eq.
  constructor; cbn. lia.
  constructor; cbn. lia.
Qed.

Lemma is_consistent_spec `{checker_flags} uctx (Huctx : global_uctx_invariants uctx)
  : is_consistent uctx <-> consistent uctx.2.
Proof.
  rewrite /is_consistent.
  have he := push_uctx_spec init_model uctx.
  destruct push_uctx => //.
  - cbn. split => // _.
    have hs := model_satisfies u. exists (to_valuation (LoopCheck.valuation u)).
    destruct he as [hl hcs]. rewrite hcs in hs.
    now eapply satisfies_union in hs as [].
  - split => //= hc.
    destruct Huctx as [hs ho].
    destruct he as [[l [inctx init]] | [h | h ]].
    { cbn in init. apply LevelSet.singleton_spec in init. subst l. contradiction. }
    { elim h. red in ho. move=> c /ho.
      rewrite declared_univ_cstr_levels_spec. intros cdecl.
      rewrite declared_univ_cstr_levels_spec.
      lsets. }
    { elim h. destruct hc as [v hv].
      exists v. eapply satisfies_union. split => //.
      eapply satisfies_union; split => //.
      2:{ cbn. intros c. ucsets. }
      apply satisfies_init. }
Qed.

Section CheckLeqProcedure.

  Context {cf:checker_flags}.
  Context (check_cstr : UnivConstraint.t -> bool).

  Definition check_leqb_universe_gen (u1 u2 : Universe.t) :=
    ~~ check_univs
    || (u1 == u2)
    || check_cstr (u1, Le, u2).

  Definition check_eqb_universe_gen (u1 u2 : Universe.t) :=
    ~~ check_univs
    || (u1 == u2)
    || check_cstr (u1, Eq, u2).

  Definition check_constraint_gen (c : UnivConstraint.t) :=
    ~~ check_univs || check_cstr c.

  Definition check_constraints_gen (c : UnivConstraintSet.t) :=
    ~~ check_univs || UnivConstraintSet.for_all check_cstr c.

  Definition eqb_univ_instance_gen (u1 u2 : Instance.t) : bool :=
    forallb2 check_eqb_universe_gen u1 u2.

  Definition leqb_sort_gen (s1 s2 : Sort.t) :=
    leqb_sort_ (fun _ => check_leqb_universe_gen) false s1 s2.

  Definition check_leqb_sort_gen (s1 s2 : Sort.t) :=
    (s1 == s2)
    || leqb_sort_gen s1 s2.

  Definition check_eqb_sort_gen (s1 s2 : Sort.t) :=
    (s1 == s2)
    || (leqb_sort_gen s1 s2 && leqb_sort_gen s2 s1).

End CheckLeqProcedure.

Definition model_of_uctx (m : universe_model) uctx :=
  LevelSet.Equal (levels m) (LevelSet.add Level.lzero uctx.1) /\
  UnivConstraintSet.Equal (constraints m) (UnivConstraintSet.union (init_constraints_of_levels uctx.1) uctx.2).

Definition leq0_universe ctrs (u u' : Universe.t) :=
  forall v, satisfies v ctrs -> val v u <= val v u'.

Definition leq_universe {cf : checker_flags} ctrs (u u' : Universe.t) :=
  if check_univs then leq0_universe ctrs u u' else True.

Definition eq0_universe φ (u u' : Universe.t) :=
  forall v, satisfies v φ -> val v u = val v u'.

Definition eq_universe {cf : checker_flags} φ (u u' : Universe.t) :=
  if check_univs then eq0_universe φ u u' else True.

Definition valid0_cstr φ (c : UnivConstraint.t) :=
  forall v, satisfies v φ -> satisfies0 v c.

Definition valid_cstr {cf : checker_flags} φ (c : UnivConstraint.t) :=
  if check_univs then valid0_cstr φ c else True.

Definition valid0_cstrs φ (c : UnivConstraintSet.t) :=
  forall v, satisfies v φ -> satisfies v c.

Definition valid_cstrs {cf : checker_flags} φ (c : UnivConstraintSet.t) :=
  if check_univs then valid0_cstrs φ c else True.

(* This section: specif in term of gc_uctx *)
Section CheckLeq.
  Context {cf:checker_flags}.

  Context (m : universe_model)
          uctx (Huctx: global_uctx_invariants uctx)
          (HG : model_of_uctx m uctx).

  Definition on_inl {A B : Type} (P : A -> Prop) (x : A + B) :=
    match x with
    | inl x0 => P x0
    | inr _ => True
    end.

  Definition level_declared l := LevelSet.In l uctx.1.

  Lemma level_declared_model (l : Level.t) :
    level_declared l -> LevelSet.In l (levels m).
  Proof using HG.
    intros Hl;subst. apply HG. clear cf.
    red in Hl; lsets.
  Qed.

  Definition expr_declared (e : LevelExpr.t)
    := LevelSet.In e.1 uctx.1.

  Definition levels_declared (u : Universe.t)
    := LevelExprSet.For_all expr_declared u.

  Definition levels_declared_sort (s : Sort.t)
    := Sort.on_sort levels_declared True s.

  Definition leqb_universe u u' := check m (u, Le, u').
  Definition eqb_universe u u' := check m (u, Eq, u').

  Definition checkb := check m.

  Definition check_spec (check: UnivConstraint.t -> bool) :=
    forall c, declared_univ_cstr_levels uctx.1 c ->
    check c <-> valid0_cstr uctx.2 c.

  Import C (clauses_sem).

  Lemma declared_incl c :
    declared_univ_cstr_levels uctx.1 c ->
    declared_univ_cstr_levels (levels m) c.
  Proof.
    destruct c as [[l d] r].
    move=> [hl hr]; cbn; split.
    - setoid_rewrite hl.
      rewrite (proj1 HG). lsets.
    - setoid_rewrite hr.
      rewrite (proj1 HG); lsets.
  Qed.

  Lemma interp_cstrs_union (v : Level.t -> nat) cstrs cstrs' :
    interp_cstrs v (UnivConstraintSet.union cstrs cstrs') <->
    interp_cstrs v cstrs /\ interp_cstrs v cstrs'.
  Proof.
    rewrite /interp_cstrs /UnivConstraintSet.For_all.
    setoid_rewrite UnivConstraintSet.union_spec.
    firstorder.
  Qed.

  Lemma interp_nes_val (v : valuation) (u : Universe.t) :
    Universe.interp_nes (val v) u = Universes.val v u.
  Proof.
    move: u. refine (Universe.interp_nes_elim (val v) (fun u i => i = val v u) _ _ _).
    - intros [l k]; rewrite val_singleton //= /val; cbn in *.
    - move=>[l k] u k' ih hnin.
      cbn. rewrite val_add //=. cbn. subst k'. cbn.
      reflexivity.
  Qed.

  Lemma satisfies0_interp_cstr (v : valuation) c :
    satisfies0 v c <-> interp_nat_cstr (val v) c.
  Proof.
    destruct c as [[l []] r]; cbn -[SemiLattice.Semilattice.le].
    split.
    - intros sat. depelim sat.
      rewrite !interp_nes_val. cbn. lia.
    - rewrite !interp_nes_val. cbn. constructor. lia.
    - split.
      * intros sat. depelim sat.
        rewrite !interp_nes_val. cbn. lia.
      * rewrite !interp_nes_val. cbn. constructor. lia.
  Qed.

  Lemma satisfies0_interp_cstr_inv V (v : Level.t -> nat) c :
    wf_valuation V v ->
    LevelSet.Subset (univ_constraint_levels c) V ->
    satisfies0 (to_valuation v) c <-> interp_nat_cstr v c.
  Proof.
    intros hwf hs.
    destruct c as [[l []] r]; cbn -[SemiLattice.Semilattice.le].
    - split.
      * intros sat. depelim sat.
        rewrite -!(@UnivLoopChecking.interp_nes_val V) in H => //.
        1-2:cbn in hs; lsets.
        cbn. lia.
      * intros hle. constructor.
        rewrite -!(@UnivLoopChecking.interp_nes_val V) //.
        1-2:cbn in hs; lsets.
        cbn in hle. lia.
    - split.
      * intros sat. depelim sat.
        rewrite -!(@UnivLoopChecking.interp_nes_val V) in H => //.
        1-2:cbn in hs; lsets.
      * intros hle. constructor.
        rewrite -!(@UnivLoopChecking.interp_nes_val V) //.
        1-2:cbn in hs; lsets.
  Qed.

  Lemma satisfies_interp_cstr (v : valuation) c :
    satisfies v c <-> interp_cstrs (val v) c.
  Proof.
    now split; move=> hf cs /hf /satisfies0_interp_cstr.
  Qed.

  Lemma satisfies_interp_cstr_inv V (v : Level.t -> nat) c :
    wf_valuation V v ->
    LevelSet.Subset (univ_constraints_levels c) V ->
    satisfies (to_valuation v) c <-> interp_cstrs v c.
  Proof.
    intros wf hs; split; move=> hf cs /[dup] hin /hf; eapply satisfies0_interp_cstr_inv; tea.
    intros h hin'. apply (hs h).
    rewrite univ_constraints_levels_spec. exists cs. split => //.
    move=> l hin'; apply hs, univ_constraints_levels_spec.
    now exists cs; split => //.
  Qed.

  Definition wf_zero_valuation V v :=
    forall l, LevelSet.In l V ->
    let zero := LS.Level.zero in
    if l == zero then True
    else if LS.Level.is_global l then v l > v zero
    else v l >= v zero.

  Lemma wf_valuation_zero V v :
    wf_valuation V v ->
    v Level.lzero = 0 ->
    wf_zero_valuation V v.
  Proof.
    rewrite /wf_valuation /wf_zero_valuation.
    move=> hl l hz /hl. destruct eqb => //.
    now rewrite l.
  Qed.

  Lemma wf_zero_valuation_init v :
    interp_cstrs v (init_constraints_of_levels uctx.1) ->
    wf_zero_valuation uctx.1 v.
  Proof.
    intros hi l hin. unfold LS.Level.zero.
    change (l == Level.lzero) with (eqb l Level.lzero).
    destruct (eqb_spec l Level.lzero) => //.
    destruct LS.Level.is_global eqn:isg.
    - specialize (hi (U1, Le, Universe.singleton (l,0))).
      forward hi.
      eapply init_constraints_of_levels_spec. tea.
      rewrite /init_constraint_of_level. destruct l => //.
      destruct l as [|g|i]=> //.
      cbn -[Pos.to_nat] in hi.
      destruct (v (Level.level g)) eqn:hv => //. noconf hi. lia.
    - specialize (hi (U0, Le, Universe.singleton (l,0))).
      forward hi.
      eapply init_constraints_of_levels_spec. tea.
      rewrite /init_constraint_of_level. destruct l => //.
      destruct l as [|g|i]=> //.
      cbn -[Pos.to_nat] in hi. lia.
  Qed.

  Definition shift_valuation (v : Level.t -> nat) : Level.t -> nat :=
    fun l => v l - v Level.lzero.

  Lemma wf_shift_valuation V v :
    wf_zero_valuation V v ->
    wf_valuation V (shift_valuation v).
  Proof.
    move=> wfv l /wfv. cbn. unfold LS.Level.zero.
    change (l == Level.lzero) with (eqb l Level.lzero).
    have he : shift_valuation v Level.lzero = 0.
    rewrite /shift_valuation //. lia.
    destruct (eqb_spec l Level.lzero).
    - now subst l.
    - destruct LS.Level.is_global eqn:isg; unfold shift_valuation; lia.
  Qed.

  Lemma wf_valuation_neq V v :
    wf_zero_valuation V v ->
    forall l, LevelSet.In l V -> v l >= v LS.Level.zero.
  Proof.
    intros wfv l hin.
    move: (wfv l hin).
    unfold LS.Level.zero in *.
    change (l == Level.lzero) with (eqb l Level.lzero).
    destruct (eqb_spec l Level.lzero) => //=. subst. lia.
    destruct l; cbn; try congruence; lia.
  Qed.

  Lemma interp_nes_shift {V} {v : Level.t -> nat} {u : Universe.t} :
    wf_zero_valuation V v ->
    LevelSet.Subset (Universe.levels u) V ->
    Universe.interp_nes (shift_valuation v) u =
    Universe.interp_nes v u - v Level.lzero /\ Universe.interp_nes v u >= v Level.lzero.
  Proof.
    move: u. refine (Universe.interp_nes_elim v (fun u i => _ -> _ ->
      Universe.interp_nes (shift_valuation v) u = i - v Level.lzero /\ i >= v Level.lzero) _ _ _).
    - intros [l k] wf hsub. rewrite /Universe.interp_expr //=
        Universe.interp_nes_singleton /val; cbn in *.
      specialize (wf l). forward wf.
      { apply hsub. unfold flip; cbn. lsets. }
      rewrite /shift_valuation in wf |- *.
      move: wf. unfold LS.Level.zero.
      change (l == Level.lzero) with (eqb l Level.lzero).
      destruct (eqb_spec l Level.lzero) => //=. subst. lia.
      destruct l; cbn. congruence. lia.
      cbn. intros. lia.
    - move=>[l k] u k' ih hnin wfv hsub.
      specialize (ih wfv). cbn. erewrite Universe.interp_nes_add.
      forward ih. setoid_rewrite <- hsub.
      rewrite Universe.levels_add. lsets.
      destruct ih as [ih ih']. rewrite ih.
      move: (wf_valuation_neq _ _ wfv l) => /fwd.
      apply hsub. rewrite Universe.levels_add //=. lsets.
      rewrite /Universe.interp_expr //= /shift_valuation //=.
      unfold LS.Level.zero; split; [lia|]. lia.
  Qed.

  Lemma interp_cstr_shift {V v c} :
    wf_zero_valuation V v ->
    declared_univ_cstr_levels V c ->
    interp_nat_cstr v c <-> interp_nat_cstr (shift_valuation v) c.
  Proof.
    intros hfw hdecl.
    destruct c as [[l d] r]; cbn.
    move: (interp_nes_shift (u := l) hfw) => /fwd. apply hdecl.
    move=> [hl hle].
    move: (interp_nes_shift (u := r) hfw) => /fwd. apply hdecl.
    move=> [hr hre].
    destruct d; rewrite hl hr; split; lia.
  Qed.

  Lemma declared_univ_cstr_levels_incl V c cls :
    declared_univ_cstrs_levels V cls ->
    UnivConstraintSet.In c cls ->
    declared_univ_cstr_levels V c.
  Proof.
    now move=> hdecl /hdecl.
  Qed.

  Lemma interp_cstrs_shift V v c :
    wf_zero_valuation V v ->
    declared_univ_cstrs_levels V c ->
    interp_cstrs v c <-> interp_cstrs (shift_valuation v) c.
  Proof.
    intros hfw hdecl.
    split; move=> hv cl /[dup] hin /hv; rewrite (interp_cstr_shift hfw); tea => //.
    all:now eapply declared_univ_cstr_levels_incl.
  Qed.

  Lemma uctx_subset :
    LevelSet.Subset (univ_constraints_levels uctx.2) uctx.1.
  Proof.
    red in Huctx. destruct Huctx. red in H0. intros l hin. red in H0.
    apply univ_constraints_levels_spec in hin as [cl [hin hincl]].
    apply H0 in hin.
    apply declared_univ_cstr_levels_spec in hin. now apply hin.
  Qed.

  Lemma checkb_spec : check_spec checkb.
  Proof.
    intros c decl.
    rewrite /checkb.
    rewrite check_nat_completeness.
    now apply declared_incl.
    split; intros hv.
    - intros v sat.
      specialize (hv (val v)).
      destruct HG.
      rewrite H0 in hv.
      forward hv.
      { apply interp_cstrs_union.
        split; [apply satisfies_interp_cstr, satisfies_init|now apply satisfies_interp_cstr]. }
      now apply satisfies0_interp_cstr.
    - intros v.
      rewrite (proj2 HG) interp_cstrs_union.
      intros [ii iu].
      specialize (hv (to_valuation (shift_valuation v))).
      rewrite (satisfies_interp_cstr_inv uctx.1) in hv.
      { apply wf_shift_valuation. apply wf_zero_valuation_init. exact ii. }
      apply uctx_subset.
      forward hv.
      rewrite -interp_cstrs_shift. apply wf_zero_valuation_init. apply ii.
      apply Huctx. exact iu.
      rewrite satisfies0_interp_cstr_inv in hv.
      apply wf_shift_valuation.
      apply wf_zero_valuation_init => //.
      now apply declared_univ_cstr_levels_spec.
      erewrite interp_cstr_shift => //.
      apply wf_zero_valuation_init => //. exact decl.
  Qed.

  Lemma fold_right_xpred0 {A} (l : list A) : fold_right (fun _ => xpred0) false l = false.
  Proof using Type. induction l; simpl; auto. Qed.

  Definition check_leqb_universe := (check_leqb_universe_gen checkb).
  Definition check_eqb_universe := (check_eqb_universe_gen checkb).

  Lemma check_leqb_universe_spec_gen check
     (check_correct : check_spec check)
     (l l' : Universe.t)
     (Hu1  : declared_univ_cstr_levels uctx.1 (l, Le, l'))
    : check_leqb_universe_gen check l l' <-> valid_cstr uctx.2 (l, Le, l').
  Proof using HG Huctx.
    specialize (check_correct _ Hu1).
    rewrite /check_leqb_universe_gen /valid_cstr. destruct check_univs => //=.
    destruct (eqb_spec l l').
    - subst l' => //=. split => // _. red. intros. constructor. lia.
    - cbn. apply check_correct.
  Qed.

  Definition check_leqb_universe_spec := check_leqb_universe_spec_gen _ checkb_spec.

  Lemma check_eqb_universe_spec_gen check
     (check_correct : check_spec check)
     (l l' : Universe.t)
     (Hu1  : declared_univ_cstr_levels uctx.1 (l, Eq, l'))
    : check_eqb_universe_gen check l l' <-> valid_cstr uctx.2 (l, Eq, l').
  Proof using HG Huctx.
    specialize (check_correct _ Hu1).
    rewrite /check_eqb_universe_gen /valid_cstr. destruct check_univs => //=.
    destruct (eqb_spec l l').
    - subst l' => //=. split => // _. red. intros. constructor. lia.
    - cbn. apply check_correct.
  Qed.

  Definition check_eqb_universe_spec := check_eqb_universe_spec_gen _ checkb_spec.

  Lemma fold_left_false {A} l : fold_left (B:=A) (fun _ : bool => xpred0) l false = false.
  Proof using Type.
    induction l; simpl; eauto.
  Qed.

  Definition check_constraints := (check_constraints_gen checkb).
  Definition eqb_univ_instance := (eqb_univ_instance_gen checkb).

  Definition leqb_sort := (leqb_sort_gen checkb).

  Definition check_leqb_sort := (check_leqb_sort_gen checkb).

  Definition check_eqb_sort := (check_eqb_sort_gen checkb).

  Lemma check_eqb_sort_refl_gen check
    (leqb_correct : check_spec check) u :
    check_eqb_sort_gen check u u.
  Proof using Type.
    unfold check_eqb_sort_gen; toProp; left.
    apply eqb_refl.
  Qed.

  Definition check_eqb_sort_refl := check_eqb_sort_refl_gen _ checkb_spec.

  (* Let levels_declared_sort (s : Sort.t) :=
    Sort.on_sort gc_levels_declared True s. *)

  Lemma levels_declared_uctx u : levels_declared u -> LevelSet.Subset (Universe.levels u) uctx.1.
  Proof.
    move=> hu l. hnf in hu.
    rewrite Universe.levels_spec.
    move=> -[k /hu hin]. apply hin.
  Qed.

  Lemma check_eqb_sort_spec_gen check
      (leqb_correct : check_spec check)
      (u1 u2 : Sort.t)
      (Hu1 : levels_declared_sort u1)
      (Hu2 : levels_declared_sort u2)
    : check_eqb_sort_gen check u1 u2 <-> eq_sort uctx.2 u1 u2.
  Proof.
    unfold check_eqb_sort_gen, eq_sort.
    destruct u1, u2; cbnr; split; intuition auto.
    - now destruct prop_sub_type.
    - toProp. destruct H.
      apply (@elimP _ _ (eqb_spec _ _)) in H. noconf H.
      reflexivity.
      toProp. destruct H as [hle hle'].
      apply (check_leqb_universe_spec_gen _ leqb_correct) in hle'.
      apply (check_leqb_universe_spec_gen _ leqb_correct) in hle.
      unfold valid_cstr, valid0_cstr in hle, hle'.
      apply antisymmetry; unfold Universes.leq_universe, Universes.leq0_universe;
      destruct check_univs => //.
      now move=> v /hle; intros s; depelim s.
      now move=> v /hle'; intros s; depelim s.
      all:split; now apply levels_declared_uctx.
    - toProp; right.
      apply partial_order_equivalence in H as [H H'].
      toProp; apply/(check_leqb_universe_spec_gen _ leqb_correct).
      * split; now apply levels_declared_uctx.
      * move: H; rewrite /Universes.leq_universe /Universes.leq0_universe.
        unfold valid_cstr, valid0_cstr. destruct check_univs => //.
        move=> hv v /hv. now constructor.
      * split; now apply levels_declared_uctx.
      * move: H'; rewrite /Universes.leq_universe /Universes.leq0_universe.
        unfold valid_cstr, valid0_cstr. destruct check_univs => //.
        move=> hv v /hv. now constructor.
  Qed.

  Definition check_eqb_sort_spec := check_eqb_sort_spec_gen _ checkb_spec.

End CheckLeq.

(*
Lemma consistent_ext_on_full_ext0 `{cf: checker_flags} [uctx G uctx' G']
      `{wGraph.invariants G, wGraph.invariants G', wGraph.acyclic_no_loop G'} :
  wGraph.subgraph G G' ->
  global_uctx_invariants uctx ->
  global_uctx_invariants uctx' ->
  is_graph_of_uctx G uctx ->
  is_graph_of_uctx G' uctx' ->
  consistent_extension_on uctx uctx'.2 <->
    wGraph.IsFullSubgraph.is_full_extension G G'.
Proof.
  move=> sub Huctx Huctx' HG HG'.
  rewrite IsFullSubgraph.is_full_extension_spec //; split.
  - move=> hext; split=> //.
    pose proof (wGraph.subgraph_acyclic _ _ sub _).
    apply: labelling_ext_lsp.
    move=> l1 /[dup] hl1 /(correct_valuation_of_labelling_satisfies HG).
    move=> /hext[v' [+ v'val]].
    move=> /(correct_labelling_of_valuation_satisfies_iff HG').
    exists (labelling_of_valuation v'); split=> //.
    move=> z /[dup] hz /(is_graph_of_uctx_levels _ _ HG) ?.
    rewrite -(val_valuation_of_labelling2 HG) // v'val //.
  - move=> fsub v /(correct_labelling_of_valuation_satisfies_iff HG) hl.
    pose (l := labelling_of_valuation v).
    pose (Gl := relabel_on G G' l).
    pose (l' := to_label ∘ (lsp Gl (wGraph.s Gl))).
    pose proof (hl' := extends_correct_labelling _ _ l hl fsub _).
    exists (valuation_of_labelling l'); split.
    + apply: (correct_valuation_of_labelling_satisfies HG')=> //.
    + move=> ? /[dup] ? /(is_graph_of_uctx_levels _ _ HG) ?.
      rewrite (val_valuation_of_labelling2 HG') //.
      * apply/(is_graph_of_uctx_levels _ _ HG').
        by apply: (vertices_sub _ _ sub).
      * rewrite /l' extends_labelling //.
Qed.

Lemma consistent_ext_on_full_ext `{cf: checker_flags} [uctx G uctx' G'] :
  is_graph_of_uctx G uctx ->
  is_graph_of_uctx G' uctx' ->
  global_uctx_invariants uctx ->
  global_uctx_invariants uctx' ->
  wGraph.is_acyclic G' ->
  wGraph.subgraph G G' ->
  consistent_extension_on uctx uctx'.2 <->
    wGraph.IsFullSubgraph.is_full_extension G G'.
Proof.
  move=> HG HG' /[dup] ? /(global_uctx_graph_invariants HG) ?.
  move=> /[dup] ? /(global_uctx_graph_invariants HG') ? /wGraph.is_acyclic_spec ??.
  by apply: consistent_ext_on_full_ext0.
Qed.
*)

Lemma init_constraints_of_levels_union ls ls' :
  UnivConstraintSet.Equal (init_constraints_of_levels (LevelSet.union ls ls'))
    (UnivConstraintSet.union (init_constraints_of_levels ls) (init_constraints_of_levels ls')).
Proof. Admitted.

Lemma is_graph_of_uctx_add `{cf : checker_flags} [m uctx uctx' m'] :
  push_uctx m uctx' = Some m' ->
  is_model_of_uctx m uctx ->
  is_model_of_uctx m' (ContextSet.union uctx' uctx).
Proof.
  move=> he; have := push_uctx_spec m uctx'. rewrite he.
  move=> [hlev hcstrs]. unfold is_model_of_uctx.
  move=> [hl hr]. rewrite hlev hl.
  rewrite LevelSetProp.union_assoc. split. lsets.
  rewrite hcstrs hr.
  rewrite init_constraints_of_levels_union /ContextSet.levels.
  rewrite UnivConstraintSetProp.union_assoc /ContextSet.constraints.
  ucsets.
Qed.
