(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool OrderedTypeAlt MSetAVL MSetFacts MSetProperties MSetDecide Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config UnivConstraintType Universes UnivLoopChecking.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Import ConstraintType.

Definition universe_model := UnivLoopChecking.univ_model.
Definition init_graph : universe_model := UnivLoopChecking.init_model.

Definition uctx_invariants (uctx : ContextSet.t)
  := UnivConstraintSet.For_all (declared_univ_cstr_levels uctx.1) uctx.2.

Definition global_uctx_invariants (uctx : ContextSet.t)
  := LevelSet.In Level.lzero uctx.1 /\ uctx_invariants uctx.

Section Push.
  Import UnivLoopChecking.

Equations push_uctx (g : universe_model) (uctx : ContextSet.t) : option universe_model :=
push_uctx g uctx with UnivLoopChecking.declare_levels g uctx.1 :=
  | Some g' => enforce_constraints g' uctx.2
  | None => None.

Lemma push_uctx_spec g uctx :
  match push_uctx g uctx with
  | None =>
    (* Either a universe was already declared *)
    (exists l, LevelSet.In l uctx.1 /\ LevelSet.In l (UnivLoopChecking.levels g)) \/
    (* Or the constraints are not satisfiable *)
    (~ exists v, satisfies v uctx.2)
  | Some g' =>
    levels g' =_lset LevelSet.union uctx.1 (levels g) /\
    constraints g' =_ucset UnivConstraintSet.union uctx.2 (UnivConstraintSet.union (init_constraints_of_levels uctx.1) (constraints g))
  end.
Proof.
  funelim (push_uctx g uctx).
  destruct enforce_constraints eqn:ec.
  - move/enforce_constraints_spec: ec => [] eql eqc.
    have hs := declare_levels_spec g uctx.1.
    rewrite Heq in hs. move: hs => [] hndecl hdecll hdeclc.
    rewrite /levels in eql. rewrite -eql in hdecll. split => //.
    now rewrite eqc hdeclc.
  - move/enforce_constraints_None: ec.





Section MakeGraph.
  Context uctx (Huctx : global_uctx_invariants uctx).
  Let ctrs := uctx.2.
  Let G : universes_graph := make_graph uctx.

  Lemma valuation_labelling_eq l (Hl : correct_labelling G l)
    : forall x, VSet.In x uctx.1
           -> labelling_of_valuation (valuation_of_labelling l) x = l x.
  Proof using Type.
    destruct x as [|s|n]; cbnr.
    - intros _. now apply proj1 in Hl; cbn in Hl.
    - intro Hs. apply Nat2Pos.id.
      assert (HH: EdgeSet.In (lzero, Z.of_nat 1, vtn (VariableLevel.level  s)) (wGraph.E G)). {
        subst G. apply make_graph_E. left.
        exists (VariableLevel.level  s). intuition. }
      apply (proj2 Hl) in HH; cbn in HH. lia.
  Qed.

  Lemma make_graph_spec v :
    gc_satisfies v uctx.2 <-> correct_labelling G (labelling_of_valuation v).
  Proof using Type.
    unfold gc_satisfies, correct_labelling. split; intro H.
    - split. reflexivity.
      intros e He. cbn in He.
      apply make_graph_E in He.
      destruct He as [[l [Hl He]]|[ctr [Hc He]]]; cbn.
      + subst e; cbn. destruct l; cbn; lia.
      + subst e.
        apply GoodUnivConstraintSet.for_all_spec in H.
        2: intros x y []; reflexivity.
        specialize (H _ Hc). cbn in *.
        destruct ctr as [[] z []|[] []| |n|n]; cbn in *; toProp H; try lia.
        all:try destruct t0; cbn in *; try lia.
    - apply GoodUnivConstraintSet.for_all_spec.
      intros x y []; reflexivity.
      intros gc Hgc.
      pose proof (XX := proj2 (make_graph_E uctx (edge_of_constraint gc))).
      forward XX. { right. now exists gc. }
      specialize (H.p2 _ XX).
      destruct gc as [[] z []|k ?| |n|n]; intro HH; cbn in *; toProp; try lia.
  Qed.

  Corollary make_graph_spec' l :
    (* gc_satisfies (valuation_of_labelling l) uctx.2 <-> correct_labelling G l. *)
    correct_labelling G l -> gc_satisfies (valuation_of_labelling l) uctx.2.
  Proof using Huctx.
    intro H. apply (make_graph_spec (valuation_of_labelling l)).
    unfold correct_labelling. intuition.
    rewrite !valuation_labelling_eq; tas. 3:now apply H.
    all: now apply make_graph_invariants.
  Qed.

  Corollary make_graph_spec2 :
    gc_consistent uctx.2 <-> exists l, correct_labelling G l.
  Proof.
    split.
    - intros [v H]. exists (labelling_of_valuation v).
      apply make_graph_spec. assumption.
    - intros [l Hl]. exists (valuation_of_labelling l).
      apply make_graph_spec'. assumption.
  Defined.

  Global Instance consistent_no_loop : gc_consistent ctrs -> acyclic_no_loop G.
  Proof.
    intro. apply acyclic_caract1, make_graph_spec2.
    now apply make_graph_invariants. assumption.
  Defined.
End MakeGraph.

Existing Class gc_consistent.
Existing Class global_gc_uctx_invariants.
Existing Class global_uctx_invariants.
Global Existing Instance gc_of_uctx_invariants.

(** ** Check of consistency ** *)

Definition is_consistent `{checker_flags} uctx :=
  match gc_of_uctx uctx with
  | Some uctx => is_acyclic (make_graph uctx)
  | None => false
  end.

Lemma is_consistent_spec `{checker_flags} uctx (Huctx : global_uctx_invariants uctx)
  : is_consistent uctx <-> consistent uctx.2.
Proof.
  etransitivity. 2: symmetry; apply gc_consistent_iff.
  unfold is_consistent; cbn.
  case_eq (gc_of_constraints uctx.2); cbn.
  2: intro; split; [discriminate|inversion 1].
  intros ctrs Hctrs.
  pose proof (gc_of_uctx_invariants uctx (uctx.1, ctrs)) as XX.
  cbn in XX; rewrite Hctrs in XX; specialize (XX Logic.eq_refl Huctx).
  etransitivity. apply make_graph_invariants in XX.
  etransitivity. apply is_acyclic_spec; tas.
  apply acyclic_caract1; tas.
  symmetry; apply (make_graph_spec2 (uctx.1, ctrs)); tas.
Qed.

Definition Equal_graph :=
  fun G G' : universes_graph =>
  LevelSet.Equal G.1.1 G'.1.1 /\
  wGraph.EdgeSet.Equal G.1.2 G'.1.2 /\ Level.eq G.2 G'.2.

Notation "'(=_g)'" := Equal_graph (at level 30).
Infix "=_g" := Equal_graph (at level 30).

Global Instance: RelationClasses.RewriteRelation ((=_g)) := {}.

Global Instance equal_graph_equiv : RelationClasses.Equivalence ((=_g)).
Proof. split; unfold Equal_graph.
  - intros [[vs es] s]; cbn. intuition reflexivity.
  - intros [[vs es] s] [[vs' es'] s']; cbn.
    intuition now symmetry.
  - intros [[vs es] s] [[vs' es'] s'] [[vs'' es''] s'']; cbn.
    intuition etransitivity; eauto.
Qed.

Lemma PathOf_proper {g g' x y} : g =_g g' -> PathOf g x y -> PathOf g' x y.
Proof.
  intros eq; induction 1; econstructor; eauto.
  destruct e as [n ine]. apply eq in ine. now exists n.
Defined.

Lemma PathOf_proper_weight {g g' x y} (eq: g =_g g') (p : PathOf g x y) : weight (PathOf_proper eq p) = weight p.
Proof.
  induction p; cbn; auto. destruct e; cbn.
  now rewrite IHp.
Qed.

Global Instance invariants_proper : Proper ((=_g) ==> impl) invariants.
Proof.
  intros [[vs es] s] [[vs' es'] s']; cbn in *.
  intros eq [ev sv sp]; constructor; eauto; cbn in *; intros.
  - firstorder eauto.
  - destruct eq as [? []]; cbn in *. rewrite -H1. now apply H.
  - specialize (sp x). apply eq in H. specialize (sp H).
    destruct sp as [[p hp]].
    pose proof (hs := proj2 (proj2 eq)); cbn in hs.
    rewrite -{2 4 6}hs.
    split; exists (PathOf_proper eq p). cbn.
    sq. now rewrite (PathOf_proper_weight eq).
Qed.

Global Instance invariants_proper_iff : Proper ((=_g) ==> iff) invariants.
Proof.
  intros g g' eq. split. now rewrite eq.
  now rewrite eq.
Qed.

Global Instance acyclic_no_loop_proper : Proper ((=_g) ==> iff) acyclic_no_loop.
Proof.
  intros g g' eq. split.
  - intros ac x p.
    rewrite -(PathOf_proper_weight (symmetry eq) p).
    apply ac.
  - intros ac x p.
    rewrite -(PathOf_proper_weight eq p).
    apply ac.
Qed.

Section CheckLeqProcedure.

  Context {cf:checker_flags}.
  Context (leqb_level_n : Z -> Level.t -> Level.t -> bool).

  (* this is function [check_smaller_expr] of kernel/uGraph.ml *)
  Definition leqb_expr_n_gen lt (e1 e2 : LevelExpr.t) :=
    match e1, e2 with
    | (l1, k), (l2, k') =>
      (* l1 + k < n = l2 + k' <-> l1 < n + (k - k') = l2 *)
      leqb_level_n (lt + (Z.of_nat k - Z.of_nat k'))%Z l1 l2
    end.

  (* this is function [exists_bigger] of kernel/uGraph.ml *)
  Definition leqb_expr_univ_n_gen lt (e1 : LevelExpr.t) (u : Universe.t) :=
    (* CHECKME:SPROP: should we use [prop_sub_type] here somehow? *)
    (* if LevelExpr.is_prop e1 && (n =? 0) then *)
    (*   prop_sub_type || Sort.is_prop u *)
                                             (* else *)
    let '(e2, u) := Universe.exprs u in
    List.fold_left (fun b e2 => leqb_expr_n_gen lt e1 e2 || b)
      u (leqb_expr_n_gen lt e1 e2).

  (* this is function [real_check_leq] of kernel/uGraph.ml *)
  Definition leqb_universe_n_gen lt (l1 l2 : Universe.t) :=
      let '(e1, u1) := Universe.exprs l1 in
      List.fold_left (fun b e1 => leqb_expr_univ_n_gen ⎩ lt ⎭ e1 l2 && b)
                     u1 (leqb_expr_univ_n_gen ⎩ lt ⎭ e1 l2).

  Definition check_leqb_universe_gen (u1 u2 : Universe.t) :=
    ~~ check_univs
    || (u1 == u2)
    || leqb_universe_n_gen false u1 u2.

  Definition check_eqb_universe_gen (u1 u2 : Universe.t) :=
    ~~ check_univs
    || (u1 == u2)
    || (leqb_universe_n_gen false u1 u2 && leqb_universe_n_gen false u2 u1).

  Definition check_gc_constraint_gen (gc : GoodConstraint.t) :=
    ~~ check_univs ||
    match gc with
    | GoodConstraint.gc_le l z l' => leqb_level_n z l l'
    | GoodConstraint.gc_lt_set_level k l => leqb_level_n (Z.of_nat (S k)) lzero (Level.level  l)
    | GoodConstraint.gc_le_set_var k n => leqb_level_n (Z.of_nat k) lzero (Level.lvar n)
    | GoodConstraint.gc_le_level_set l k => leqb_level_n (- Z.of_nat k)%Z (Level.level  l) lzero
    | GoodConstraint.gc_le_var_set n k => leqb_level_n (- Z.of_nat k)%Z (Level.lvar n) lzero
    end.

  Definition check_gc_constraints_gen :=
    GoodUnivConstraintSet.for_all check_gc_constraint_gen.

  Definition check_constraints_gen ctrs :=
    match gc_of_constraints ctrs with
    | Some ctrs => check_gc_constraints_gen ctrs
    | None => false
    end.

  Definition eqb_univ_instance_gen (u1 u2 : Instance.t) : bool :=
    forallb2 (fun l1 l2 => check_eqb_universe_gen
        (Universe.make' l1) (Universe.make' l2)) u1 u2.

  Definition leqb_sort_gen (s1 s2 : Sort.t) :=
    leqb_sort_n_ (fun _ => check_leqb_universe_gen) false s1 s2.

  Definition check_leqb_sort_gen (s1 s2 : Sort.t) :=
    (s1 == s2)
    || leqb_sort_gen s1 s2.

  Definition check_eqb_sort_gen (s1 s2 : Sort.t) :=
    (s1 == s2)
    || (leqb_sort_gen s1 s2 && leqb_sort_gen s2 s1).

End CheckLeqProcedure.

(* This section: specif in term of gc_uctx *)
Section CheckLeq.
  Context {cf:checker_flags}.

  Context (G : universes_graph)
          uctx (Huctx: global_gc_uctx_invariants uctx) (HC : gc_consistent uctx.2)
          (HG : Equal_graph G (make_graph uctx)).

  Definition on_inl {A B : Type} (P : A -> Prop) (x : A + B) :=
    match x with
    | inl x0 => P x0
    | inr _ => True
    end.


  Definition gc_level_declared l
    := VSet.In l uctx.1.

  Lemma gc_level_declared_make_graph (l : Level.t) :
    gc_level_declared l -> VSet.In l (wGraph.V G).
  Proof using HG.
    intros Hl;subst. now apply HG.
  Qed.

  Definition gc_expr_declared e
    := on_Some_or_None (fun l => VSet.In l uctx.1) (LevelExpr.get_noprop e).

  Definition gc_levels_declared (u : Universe.t)
    := LevelExprSet.For_all gc_expr_declared u.

  Definition gc_levels_declared_sort (s : Sort.t)
    := Sort.on_sort gc_levels_declared True s.

  Lemma val_level_of_variable_level v (l : VariableLevel.t)
    : val v (l : Level.t) = val v l.
  Proof using Type.
    destruct l; cbn; lia.
  Qed.

  Local Open Scope univ_scope.

  Lemma val_labelling_of_valuation v (l : Level.t)
    : val v l = labelling_of_valuation v l.
  Proof using Type.
    destruct l; cbnr.
  Qed.

  Lemma val_labelling_of_valuation' v (l : Level.t) n :
    val v (Universe.make (l, n))
    = n + labelling_of_valuation v l.
  Proof using Type.
    reflexivity.
  Qed.

  Lemma val_valuation_of_labelling' L  (l : Level.t) n
        (e := (l, n)) :
    gc_level_declared l ->
    correct_labelling G L ->
    val (valuation_of_labelling L) e = (n + (L l))%nat.
  Proof using HG.
    intros Hl [HG1 HG2]. rewrite [wGraph.s _](proj2 (proj2 HG)) in HG1. simpl in HG1.
    destruct l as [|l|l]; rewrite ?HG1; cbnr.
    pose proof (make_graph_E uctx (edge_of_level (VariableLevel.level  l))).p2 as H.
    forward H. {
      left. eexists; split; try reflexivity; tas. }
    apply HG in H.
    specialize (HG2 _ H); cbn in HG2. rewrite HG1 in HG2; cbn in HG2.
    f_equal. clear -HG2. set (L (Level.level  l)) in *; clearbody n.
    destruct n; try lia.
  Qed.

  Lemma val_valuation_of_labelling L  (l : Level.t) :
    gc_level_declared l ->
    correct_labelling G L ->
    val (valuation_of_labelling L) l = (L l).
  Proof using HG.
    intros Hl HL.
    exact (val_valuation_of_labelling' L l 0 Hl HL).
  Qed.

  Instance correct_labelling_proper : Proper ((=_g) ==> Logic.eq ==> iff) correct_labelling.
  Proof using Type.
    intros g g' eq x ? ->.
    unfold correct_labelling.
    rewrite [wGraph.s _](proj2 (proj2 eq)).
    now setoid_rewrite (proj1 (proj2 eq)).
  Qed.

  (** ** Check of leq ** *)

  Ltac unfold_univ_rel0 :=
    unfold eq0_universe, leq0_universe_n, leq_vertices,
    gc_eq0_universe, gc_leq0_universe, gc_lt0_universe, gc_leq0_universe_n in *;
    intros v Hv; cbnr.

  Lemma leq_universe_vertices0 n (l l' : Level.t)
    : leq_vertices G n l l'
      -> gc_leq0_universe_n n uctx.2 (Universe.make' l) (Universe.make' l').
  Proof using HG.
    intros H. unfold_univ_rel0.
    apply make_graph_spec in Hv; tas.
    eapply correct_labelling_proper in Hv; tea. 2:reflexivity.
    red in Hv.
    specialize (H _ Hv).
    rewrite !val_labelling_of_valuation; lia.
  Qed.

  Lemma leq_universe_vertices1 n (l l' : Level.t)
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq0_universe_n n uctx.2 (Universe.make' l) (Universe.make' l')
      -> leq_vertices G n l l'.
  Proof using HG Huctx.
    intros H. unfold_univ_rel0.
    eapply correct_labelling_proper in Hv. 2:symmetry; tea. 2:reflexivity.
    specialize (H _ (make_graph_spec' _ Huctx _ Hv)) as HH.
    eapply HG in Hl, Hl'.
    rewrite !Universe.val_make' in HH.
    rewrite <- (valuation_labelling_eq _ _ Hv l Hl).
    rewrite <- (valuation_labelling_eq _ _ Hv l' Hl').
    pose proof (val_labelling_of_valuation (valuation_of_labelling v) l).
    pose proof (val_labelling_of_valuation (valuation_of_labelling v) l').
    rewrite H0 H1 in HH. lia.
  Qed.

  Lemma leq_universe_vertices n (l l' : Level.t)
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq0_universe_n n uctx.2 (Universe.make' l) (Universe.make' l')
      <-> leq_vertices G n l l'.
  Proof using HG Huctx.
    split.
    - intros H. unfold_univ_rel0. apply leq_universe_vertices1; tas.
    - apply leq_universe_vertices0.
  Qed.

  Definition leqb_level_n n (l l' : Level.t)
    := leqb_vertices G n l l'.

  Definition leqb_level_n_spec_gen (leqb_level_n : Z -> Level.t -> Level.t -> bool) :=
    forall n (l l' : Level.t)
      (Hl : VSet.In l uctx.1) (Hl' : VSet.In l' uctx.1), leqb_level_n n l l'
    <-> gc_leq0_universe_n n uctx.2 (Universe.make' l) (Universe.make' l').

  Lemma leqb_level_n_spec : leqb_level_n_spec_gen leqb_level_n.
  Proof using HC HG Huctx.
    unfold leqb_level_n_spec_gen; intros;
    symmetry. etransitivity. apply leq_universe_vertices; now apply HG.
    etransitivity. apply leqb_vertices_correct; try exact _. 1-2:now rewrite HG; exact _.
    now unfold leqb_level_n.
  Qed.

  Definition leqb_expr_n := (leqb_expr_n_gen leqb_level_n).

  Lemma leqb_expr_n_spec0_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
    lt e e'
    : gc_expr_declared e ->
      gc_expr_declared e' ->
      leqb_expr_n_gen leqb_level_n_gen lt e e' ->
      gc_leq0_universe_n lt uctx.2 (Universe.make e) (Universe.make e').
  Proof using Type.
    unfold leqb_expr_n.
    destruct e as [l k], e' as [l' k'];
    try (cbn in *; discriminate);
      intros He He' H v Hv; cbn;
        eapply leqb_correct in H; eauto;
        specialize (H v Hv); cbn in H;lia.
  Qed.

  Definition leqb_expr_n_spec0 := leqb_expr_n_spec0_gen _ leqb_level_n_spec.

  Lemma andb_is_true (b b' : bool) : b /\ b' -> b && b'.
  Proof using Type. destruct b, b'; cbnr; intuition 0. Qed.

  Lemma leqb_expr_n_spec_gen leqb_level_n_gen
      (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen) n e e'
      (HHl  : gc_expr_declared e)
      (HHl' : gc_expr_declared e')
    : leqb_expr_n_gen leqb_level_n_gen ⎩ n ⎭ e e'
      <-> gc_leq0_universe_n ⎩ n ⎭ uctx.2 (Universe.make e) (Universe.make e').
  Proof using HC.
    split; [apply (leqb_expr_n_spec0_gen _ leqb_correct)|]; try assumption.
    destruct e as [l k] eqn:eqe, e' as [l' k'] eqn:eqe'; cbn; intro H;
      destruct HC as [v0 Hv0]; pose proof (H v0 Hv0) as H0; cbn in H0.
     simpl in H0 |- *.
    apply leqb_correct; tas.
    unfold_univ_rel0.
    specialize (H v Hv). simpl in H. cbn in H.
    lia.
  Qed.

  Definition leqb_expr_n_spec := leqb_expr_n_spec_gen _ leqb_level_n_spec.

  Import NonEmptySetFacts.

  Definition leqb_expr_univ_n := (leqb_expr_univ_n_gen leqb_level_n).

  Lemma leqb_expr_univ_n_spec0_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
    n e1 u
    : gc_expr_declared e1 -> gc_levels_declared u -> leqb_expr_univ_n_gen leqb_level_n_gen n e1 u
      -> gc_leq0_universe_n n uctx.2 (Universe.make e1) u.
  Proof using Type.
    unfold leqb_expr_univ_n_gen; intros He1 Hu H.
    unfold_univ_rel0.
    rewrite val_fold_right.
    destruct (Universe.exprs u) as [e u'] eqn:ee;cbn in *.
    rewrite <- !fold_left_rev_right in H; cbn in *.
    red in Hu.
    assert (Hu': gc_expr_declared e /\ Forall gc_expr_declared u'). {
    split. apply Hu. apply In_to_nonempty_list. fold Universe.exprs. left. now rewrite ee.
    apply Forall_forall. intros e' He'. apply Hu.
    apply In_to_nonempty_list. fold Universe.exprs. right. now rewrite ee. }
    destruct Hu' as [He Hu'].
    apply Forall_rev in Hu'. revert Hu'.
    induction (List.rev u'); cbn in *; intros.
    - eapply leqb_expr_n_spec0_gen; eauto; tas.
    - apply orb_true_iff in H. destruct H as [H|H].
      + eapply leqb_expr_n_spec0_gen in H; eauto. specialize (H v Hv); cbn in *.
        lia. now inversion Hu'.
      + apply IHl in H; clear IHl. lia. now inversion Hu'.
  Qed.

  Definition leqb_expr_univ_n_spec0 := leqb_expr_univ_n_spec0_gen _ leqb_level_n_spec.

  Import Nbar Datatypes.

  Lemma val_le_caract' (u : Universe.t) v k :
    (exists e, LevelExprSet.In e u /\ Z.of_nat k <= Z.of_nat (val v e))%Z <-> (Z.of_nat k <= Z.of_nat (val v u))%Z.
  Proof using Type.
    epose proof (val_le_caract u v k).
    intuition auto.
    apply inj_le, H0.
    destruct H as [e [? ?]]. exists e; split; auto.
    lia.
    assert (k <= val v u)%nat. lia.
    destruct (H1 H2) as [e [? ?]]. exists e; split; auto.
    lia.
  Qed.

  Lemma val_ge_caract' (u : Universe.t) v k :
    (forall e, LevelExprSet.In e u -> (Z.of_nat (val v e) <= Z.of_nat k)%Z) <-> (Z.of_nat (val v u) <= Z.of_nat k)%Z.
  Proof using Type.
    epose proof (val_ge_caract u v k).
    intuition auto.
    apply inj_le, H0.
    intros e hin. specialize (H e hin). lia.
    assert (val v u <= k)%nat. lia.
    specialize (H1 H3 e H2). lia.
  Qed.

  Lemma Z_of_nat_bool_to_nat x b : (Z.of_nat x + ⎩ b ⎭)%Z = Z.of_nat (x + if b then 1%nat else 0%nat).
  Proof using Type. destruct b; simpl; lia. Qed.

  Lemma Z_of_nat_inj_bool (x : bool) : Z.of_nat (if x then 1%nat else 0%nat) = ⎩ x ⎭.
  Proof using Type. destruct x; simpl; auto. Qed.

  Definition neg_forall p u :=
    LevelExprSet.for_all p u = false.

  Lemma exists_neg_forall p u : neg_forall p u <-> LevelExprSet.exists_ (fun x => ~~ (p x)) u.
  Proof using Type.
    unfold neg_forall.
    split. intros nf.
    now apply LevelExprSet_for_all_false in nf.
    intros ex.
    apply not_true_iff_false; intro HH.
    eapply LevelExprSet.for_all_spec in HH. 2:proper.
    red in ex.
    eapply LevelExprSet.exists_spec in ex as [x [inx npx]]. 2:proper.
    specialize (HH _ inx). simpl in HH. rewrite HH in npx. simpl in npx. congruence.
  Qed.

  Definition lsp_expr G l (ei : LevelExpr.t) : Nbar.t :=
    let '(li, bi) := ei in (lsp G l li + Some (Z.of_nat bi))%nbar.

  Local Open Scope Z_scope.

  Definition is_lt (x y : Nbar.t) : bool :=
    ~~ le_lt_dec y x.

  Lemma is_lt_spec x y : is_lt x y -> (x < y)%nbar.
  Proof using Type.
    unfold is_lt. destruct le_lt_dec. simpl. discriminate. simpl.
    auto.
  Qed.

  (* Non trivial lemma *)
  (* l + n  <= max (l1, ... ln)  -> exists i, l+n <= li *)
  Lemma gc_leq0_universe_n_sup lt (l : Level.t) b (u : Universe.t)
        (e := (l, b)) :
      gc_level_declared l ->
      gc_levels_declared u ->
      gc_leq0_universe_n ⎩ lt ⎭ uctx.2 (Universe.make e) u ->
      exists (e' : LevelExpr.t), LevelExprSet.In e' u
            /\ gc_leq0_universe_n ⎩ lt ⎭ uctx.2 (Universe.make e) (Universe.make e').
  Proof using HC HG Huctx.
    intros Hl Hu H.
    assert (HG1 : invariants G) by (rewrite HG; exact _).
    assert (HG2 : acyclic_no_loop G) by (rewrite HG; exact _).
    assert (Hs : wGraph.s G = lzero) by apply (proj2 (proj2 HG)).
    assert (Vs : VSet.In lzero (wGraph.V G)).
    { rewrite <-Hs. now apply source_vertex. }
    case_eq (lsp G l lzero).
    (* case where there is a path from l to Set, so l <= Set+ (-m).
      This implies that -m + b <= val v u.
    *)
    - intros lset Hlset. red in H.
      (** Needs to strengthen the argument using a valuations of l with - m *)
      assert (Hinl : VSet.In l (wGraph.V G)). {
        red in Hl;  cbn in Hl. now apply HG. }
      epose proof (lsp_to_s G Hinl).
      rewrite Hs in H0. specialize (H0 Hlset).
      pose proof (lsp_s G _ Hinl) as [sl [lspsl slpos]].
      assert (Hl' : forall v, gc_satisfies v uctx.2 -> (val v l <= Z.to_nat (- lset))%nat). {
        intros v Hv. apply make_graph_spec in Hv.
        rewrite <- HG in Hv.
        eapply correct_labelling_lsp in Hlset; tea.
        cbn in Hlset.
        change (labelling_of_valuation v l) with (val v l) in Hlset. lia. }
      assert (Hl'' : forall v, gc_satisfies v uctx.2 -> (Z.to_nat sl <= val v l)%nat). {
          intros v Hv. apply make_graph_spec in Hv.
          rewrite <- HG in Hv. rewrite Hs in lspsl.
          eapply correct_labelling_lsp in lspsl; tea.
          cbn in lspsl.
          change (labelling_of_valuation v l) with (val v l) in lspsl. lia. }
      assert (LevelExprSet.for_all
        (fun ei => is_lt (lsp_expr G l ei - Some (Z.of_nat b))%nbar (Some ⎩ lt ⎭))%Z
        u = false) as HH. {
        apply not_true_iff_false; intro HH.
        apply LevelExprSet.for_all_spec in HH; proper.
        set (G' := wGraph.Subgraph1.G' G lzero l lset) in *.
        assert (HG'1 : invariants G'). {
          subst G'; apply Subgraph1.HI'; tas. }
        assert (HG'2 : acyclic_no_loop G'). {
          subst G'; apply Subgraph1.HG'; tas. }
        eapply (Subgraph1.correct_labelling_lsp_G' G) in Hlset as Hlab; tas.
        fold G' in Hlab; cbn in Hlab.
        set (lab := fun x => to_label (lsp G' (wGraph.s G) x)) in *.
        pose proof (make_graph_spec' _ Huctx lab) as Hv.
        forward Hv; [now rewrite <- HG|].
        specialize (H _ Hv). specialize (Hl' _ Hv).
        specialize (Hl'' _ Hv).
        rewrite Universe.val_make in H.
        rewrite (val_valuation_of_labelling' _ l b) in H; tas.
        apply switch_minus in H.
        subst e.
        rewrite Z_of_nat_bool_to_nat in H.
        eapply val_le_caract' in H.
        destruct H as [ei [Hei H]]. specialize (HH ei Hei); cbn in HH.
        specialize (Hu ei Hei).
        destruct ei as [li bi]; cbn in *.
        assert (Vli : VSet.In li (wGraph.V G)).
        { now apply HG. }

        simpl in H. unfold is_lt in HH.
        match goal with
        | H : ~~ is_left ?X = true |- _ =>
          destruct X as [HH'|Hlt]; [discriminate|]; clear H
        end.
        rewrite val_valuation_of_labelling in H; tas.
        rewrite !Nat2Z.inj_add in H.
        rewrite Z_of_nat_inj_bool in H.
        assert (Z.of_nat (lab l) = - lset).
        { unfold lab.
          epose proof (Subgraph1.lsp_G'_spec_left G _ _ Hinl Vs _ Hlset l).
          fold G' in H1. rewrite Hs H1. clear H1.
          rewrite lsp_xx.
          pose proof (lsp_sym _ Hlset).
          destruct (lsp_s G l Hinl) as [sl' [lspsl' w]].
          rewrite Hs in lspsl'. rewrite lspsl' in H1 |- *.
          simpl in H1. cbn -[to_label].
          rewrite Z_of_to_label_pos //; lia. }
        rewrite H1 in H.
        destruct (lsp_s G' li) as [ni [Hni nipos]].
        { cbn. now apply HG. }
        generalize (Subgraph1.lsp_G'_spec_left G lzero l Hinl Vs _ Hlset li).
        fold G'. simpl in Hni.
        rewrite <-Hs, Hni.
        destruct (lsp_s G li Vli) as [sli [lspsli wsli]].
        rewrite lspsli. rewrite Hs in Hni, lspsli, lspsl.
        assert (⎩ lt ⎭ <= - Z.of_nat b + lset + Z.of_nat bi + Z.of_nat (lab li)) by lia.
        destruct (lsp G l li) as [lli|] eqn:elli.
        2:{ exfalso.
          generalize (lsp_codistance G l lzero li).
          now rewrite elli Hlset lspsli. }
        simpl in Hlt.
        assert (lli + Z.of_nat bi - Z.of_nat b < - Z.of_nat b + lset + Z.of_nat bi + Z.of_nat (lab li)) by lia.
        assert (lli < lset + Z.of_nat (lab li)) by lia.
        unfold lab in H. rewrite Hs in H.
        rewrite Hni in H.
        rewrite Z_of_to_label_pos in H; try lia.
        intros hmax.
        symmetry in hmax.
        apply eq_max in hmax as [[= eq]|eq]. subst ni.
        unfold lab in H4. rewrite Hs Hni in H4.
        rewrite Z_of_to_label_pos in H4; try lia.
        pose proof (lsp_codistance G l lzero li). rewrite Hlset lspsli elli in H5.
        simpl in H5. lia.
        simpl in eq. noconf eq.
        lia. }
      apply LevelExprSet_for_all_false in HH.
      apply LevelExprSet.exists_spec in HH; proper.
      unfold LevelExprSet.Exists in *.
      destruct HH as [[li bi] [He' HH]]. unfold is_lt in HH.
      rewrite negb_involutive in HH.
      eexists; split; tea.
      match goal with
      | H : ssrbool.is_left ?X = true |- _ =>
        destruct X as [HH'|HH']; try discriminate; clear H
      end.
      cbn in HH'.
      rewrite Hs in lspsl.
      case_eq (lsp G l li).
      2: intros X; rewrite X in HH'; destruct bi, b; contradiction.
      intros nl Hnl v Hv; rewrite Hnl in HH'.
      simpl in HH'.
      rewrite (val_labelling_of_valuation' v li bi); cbn.
      specialize (Hl' _ Hv).
      specialize (Hl'' _ Hv).
      pose proof Hv as Hv'.
      apply make_graph_spec in Hv; tas. rewrite <- HG in Hv.
      apply (correct_labelling_lsp _ Hnl) in Hv. cbn in Hv.
      apply switch_minus.
      rewrite !Nat2Z.inj_add.
      enough (Z.of_nat b + Z.of_nat (val v l) + ⎩ lt ⎭ - Z.of_nat bi <= Z.of_nat (labelling_of_valuation v li)) by lia.
      etransitivity; [|eassumption].
      assert (Z.of_nat (val v l) = Z.of_nat (labelling_of_valuation v l)).
      reflexivity. rewrite H1. lia.

    (* case where there is no path from l to Set *)
    - intros HlSet. subst e.
      assert (Hl' : VSet.In l (wGraph.V G)). {
        red in Hl; cbn in Hl; now apply HG. }

      assert (LevelExprSet.for_all
                (fun ei => match ei with
                        | (li, bi) =>
                          le_lt_dec (Some (Z.of_nat bi)
                          + Some (match b with 0%nat => 1%Z | _ => (- (Z.pred (Z.of_nat b)))%Z end)
                          + lsp G l li)
                          (Some ⎩ lt ⎭)%Z
                        end)%nbar
                u = false) as HH. {
        apply not_true_iff_false; intro HH.
        destruct (lsp_s G _ Hl') as [nl [Hnl nlpos]]; cbn in Hnl.

        assert (exists K : Z, (nl <= K)%Z /\
                LevelExprSet.For_all
                  (fun ei => match ei with
                            | (li, bi) =>
                              match lsp G (wGraph.s G) li with
                              | None => True
                              | Some ni => ((Z.of_nat bi) + ni < K)%Z
                              end
                                 end) u) as XX. {
          exists (LevelExprSet.fold
               (fun ei K => match ei with
                         | (li, bi) =>
                           match lsp G (wGraph.s G) li with
                           | None => K
                           | Some ni => Z.max K (Z.succ (Z.of_nat bi) + ni)
                           end
                         end) u nl).
          clear -Hu HG HG1 HG2. split.
          - rewrite LevelExprSet.fold_spec. rewrite <- fold_left_rev_right.
            induction (List.rev (LevelExprSet.elements u)). reflexivity.
            cbn. destruct a as [li bi]; tas.
            destruct (lsp G (wGraph.s G) li); tas; lia.
          - intros [li bi] Hei; trivial.
            specialize (Hu _ Hei); cbn in Hu.
            destruct (lsp_s G li) as [ni' [Hni' ni'pos]].
            { now apply HG. }
            rewrite Hni'.
            rewrite LevelExprSet.fold_spec. rewrite <- fold_left_rev_right.
            apply LevelExprSetFact.elements_1, InA_In_eq, in_rev in Hei.
            change (In (li, bi)
                       (@List.rev LevelExprSet.elt (LevelExprSet.elements u))) in Hei.
            induction (List.rev (LevelExprSet.elements u)); inv Hei.
            + subst a; cbn. rewrite Hni'. lia.
            + specialize (IHl H). cbn. destruct a as [li' bi'].
              destruct (lsp G (wGraph.s G) li'); lia. }
        destruct XX as [K [HK1 HK2]].
        assert (Hs' : VSet.In lzero (wGraph.V G)). {
          rewrite <- Hs; apply HG1. }
        set (G' := wGraph.G' G lzero l K) in *.
        assert (lsG : l <> wGraph.s G). intros eq.
        { rewrite eq in HlSet, Hnl.
          congruence. }
        assert (HG'1 : invariants G'). {
          subst G'; apply HI'; tas. }
        assert (HG'2 : acyclic_no_loop G'). {
          subst G'; apply HG'; tas. }
        apply correct_labelling_lsp_G' with (K:=K) in HlSet as Hlab; tas.
        fold G' in Hlab; cbn in Hlab.
        set (lab := fun x => to_label (lsp G' (wGraph.s G) x)) in *.
        pose proof (make_graph_spec' _ Huctx lab) as Hv.
        forward Hv; [now rewrite <- HG|].
        specialize (H _ Hv); clear Hv.
        rewrite Universe.val_make in H.
        rewrite val_valuation_of_labelling' in H; tas.

        apply switch_minus in H.
        rewrite Z_of_nat_bool_to_nat in H.
        apply val_le_caract' in H.
        destruct H as [ei [Hei H]].
        apply LevelExprSet.for_all_spec in HH; proper.
        specialize (HH _ Hei); cbn in HH.
        specialize (Hu _ Hei).
        destruct ei as [li bi]; cbn in H.
        rewrite val_valuation_of_labelling in H; tas.
        match goal with
        | H : is_left ?X = true |- _ =>
          destruct X as [HH'|HH']; try discriminate; clear H
        end.
        assert (lab l = to_label (Some K)) as XX. {
          subst lab; cbn. subst G'. rewrite -> Hs in *.
          rewrite lsp_G'_spec_left; tas. rewrite Hnl.
          unfold lsp. rewrite acyclic_lsp0_xx; tas.
          simpl. assert (Z.max nl (K + 0) = K). lia. now rewrite H0. }
        rewrite XX in H.
        destruct (lsp_s G li) as [ni [Hni nipos]].
        { now apply HG. }
        specialize (HK2 _ Hei); cbn in HK2. rewrite Hni in HK2.

        case_eq (lsp G l li).
        - intros ki Hki. rewrite Hki in HH'; cbn in HH'.
          destruct (Z.leb_spec ni (K + ki)).
          assert (lab li = to_label (Some (K + ki)%Z)) as XX'. {
            subst lab; cbn. subst G'. rewrite -> Hs in *.
            rewrite lsp_G'_spec_left; tas. rewrite Hki.
            rewrite Hni; cbn.
            assert (Z.max ni (K + ki) = K + ki)%Z as ->. lia.
            reflexivity. }
          rewrite XX' in H.
          rewrite !Nat2Z.inj_add in H.
          rewrite !Z_of_to_label in H.
          destruct (Z.leb_spec 0 K); [|lia].
          destruct (Z.leb_spec 0 (K + ki)); [|].
          rewrite Z_of_nat_inj_bool in H.
          destruct b; cbn in *; lia.
          destruct b, lt; cbn in *; lia.
          assert (lab li = to_label (Some ni)) as XX'. {
            subst lab; cbn. subst G'. rewrite -> Hs in *.
            rewrite lsp_G'_spec_left; tas. rewrite Hki Hni; simpl.
            enough (Z.max ni (K + ki) = ni)%Z as ->; auto. lia. }
          rewrite XX' in H.
          rewrite !Nat2Z.inj_add !Z_of_to_label Z_of_nat_inj_bool in H.
          destruct (Z.leb_spec 0 K); [|lia].
          destruct (Z.leb_spec 0 ni); [|lia].
          destruct b, lt; cbn in *; lia.

        - intro Hki.
          assert (lab li = to_label (Some ni)) as XX'. {
            subst lab; cbn. subst G'. rewrite -> Hs in *.
            rewrite lsp_G'_spec_left; tas. now rewrite Hki Hni. }
          rewrite XX' in H.
          rewrite !Nat2Z.inj_add !Z_of_to_label Z_of_nat_inj_bool in H.
          destruct (Z.leb_spec 0 K); [|lia].
          destruct (Z.leb_spec 0 ni); [|lia].
          destruct b, lt; cbn in *; lia. }

    apply LevelExprSet_for_all_false in HH.
    apply LevelExprSet.exists_spec in HH; proper.
    destruct HH as [[li bi] [He' HH]].
    eexists; split; tea.
    match goal with
    | H : ~~ is_left ?X = true |- _ =>
      destruct X as [HH'|HH']; try discriminate; clear H
    end.
    cbn in HH'. case_eq (lsp G l li).
    2: intros X; rewrite X in HH'; destruct bi, b; contradiction.
    intros nl Hnl v Hv; rewrite Hnl in HH'.
    apply make_graph_spec in Hv; tas. rewrite <- HG in Hv.
    apply (correct_labelling_lsp _ Hnl) in Hv.
    rewrite !val_labelling_of_valuation'.
    destruct b, lt; cbn in *; lia.
  Qed.

  Lemma leqb_expr_univ_n_spec_gen leqb_level_n_gen
      (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
      lt e1 (u : Universe.t)
      (He1 : gc_expr_declared e1)
      (Hu  : gc_levels_declared u)
    : leqb_expr_univ_n_gen leqb_level_n_gen ⎩ lt ⎭ e1 u
      <-> gc_leq0_universe_n ⎩ lt ⎭ uctx.2 (Universe.make e1) u.
  Proof using HC HG Huctx.
    split; [eapply leqb_expr_univ_n_spec0_gen; eauto|].
    unfold leqb_expr_univ_n_gen; intro HH.
    case_eq (Universe.exprs u). intros e u' ee.
    assert (Hu': gc_expr_declared e /\ Forall gc_expr_declared u'). {
    split. apply Hu. apply In_to_nonempty_list. fold Universe.exprs. left. now rewrite ee.
    apply Forall_forall. intros e' He'. apply Hu.
    apply In_to_nonempty_list. fold Universe.exprs. right. now rewrite ee. }
    destruct e1 as [l1 b1].
    apply gc_leq0_universe_n_sup in HH; tas.
    destruct HH as [e' [He' HH]]. eapply leqb_expr_n_spec_gen in HH; eauto; tas.
    apply In_to_nonempty_list in He'. fold Universe.exprs in He'; rewrite ee in He'; cbn in He'.
    rewrite <- !fold_left_rev_right.
    clear -He' HH. destruct He' as [H|H]; [subst|].
    * induction (List.rev u'); tas;cbn -[leqb_expr_n].
      now rewrite IHl orb_true_r.
    * apply In_rev in H.
      induction (List.rev u'); cbn -[leqb_expr_n]; invs H.
      unfold leqb_expr_n_gen in HH. now rewrite HH. now rewrite IHl; auto; rewrite orb_true_r.
  Qed.

  Definition leqb_expr_univ_n_spec := leqb_expr_univ_n_spec_gen _ leqb_level_n_spec.

  Definition leqb_universe_n := (leqb_universe_n_gen leqb_level_n).

  Lemma fold_right_xpred0 {A} (l : list A) : fold_right (fun _ => xpred0) false l = false.
  Proof using Type. induction l; simpl; auto. Qed.

  Lemma leqb_universe_n_spec0_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
    lt (u1 u2 : Universe.t)
    (Hu1  : gc_levels_declared u1)
    (Hu2  : gc_levels_declared u2)
: leqb_universe_n_gen leqb_level_n_gen lt u1 u2 -> gc_leq0_universe_n ⎩ lt ⎭ uctx.2 u1 u2.
  Proof using Type.
    unfold leqb_universe_n_gen. intros H.
    unfold_univ_rel0.
    unfold val, Universe.Evaluable.
    destruct (Universe.exprs u1) as [e1 u1'] eqn:Hu1'.
    rewrite <- fold_left_rev_right in *; cbn in *.
    assert (Hu': gc_expr_declared e1 /\ Forall gc_expr_declared u1'). {
    split. apply Hu1. apply In_to_nonempty_list. fold Universe.exprs. left. now rewrite Hu1'.
    apply Forall_forall. intros e' He'. apply Hu1.
    apply In_to_nonempty_list. fold Universe.exprs. right. now rewrite Hu1'. }
    destruct Hu' as [? Hu']. apply Forall_rev in Hu'. revert Hu'.
    induction (List.rev u1'); cbn in *; intros.
    + eapply leqb_expr_univ_n_spec0_gen in H; eauto.
      specialize (H v Hv); cbn in H. assumption.
    + set (z := (fold_right (fun e x => Nat.max (val v e) x) (val v e1) l)) in *.
      toProp as [H HH].
      eapply leqb_expr_univ_n_spec0_gen in H; eauto. specialize (H v Hv). cbn in H.
      destruct (Nat.max_dec (val v a) z) as [ee|ee]; rewrite ee.
      * assumption.
      * apply IHl; tas. now inversion Hu'.
      * now inversion Hu'.
  Qed.

  Definition leqb_universe_n_spec0 := leqb_universe_n_spec0_gen _ leqb_level_n_spec.

  Lemma leqb_universe_n_spec_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
    lt (l1 l2 : Universe.t)
        (Hu1  : gc_levels_declared l1)
        (Hu2  : gc_levels_declared l2)
    : leqb_universe_n_gen leqb_level_n_gen lt l1 l2
      <-> gc_leq0_universe_n ⎩ lt ⎭ uctx.2 l1 l2.
  Proof using HC HG Huctx.
    split; [eapply leqb_universe_n_spec0_gen; eauto |].
    unfold leqb_universe_n_gen; intro HH.
    unfold Universe.exprs.
    case_eq (to_nonempty_list l1); intros e1 uu1 Huu1.
    rewrite (fold_left_andb_forallb (fun e => _)).
    pose proof (to_nonempty_list_spec' l1) as X; rewrite Huu1 in X; cbn in X.
    rewrite X. apply forallb_Forall. apply Forall_forall.
    intros ei Hei.
    apply InA_In_eq, LevelExprSetFact.elements_2 in Hei.
    specialize (Hu1 _ Hei).
    eapply leqb_expr_univ_n_spec_gen; eauto; tas.
    intros v Hv. specialize (HH v Hv).
    simpl in HH |- *.
    transitivity (Z.of_nat (val v l1)); eauto.
    eapply (val_ge_caract' l1 v (val v l1)).p2. lia. auto.
  Qed.

  Definition leqb_universe_n_spec := leqb_universe_n_spec_gen _ leqb_level_n_spec.

  Definition check_leqb_universe := (check_leqb_universe_gen leqb_level_n).

  Lemma check_leqb_universe_spec_gen leqb_level_n_gen
     (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
     (u1 u2 : Universe.t)
     (Hu1  : gc_levels_declared u1)
     (Hu2  : gc_levels_declared u2)
    : check_leqb_universe_gen leqb_level_n_gen u1 u2 <-> gc_leq_universe uctx.2 u1 u2.
  Proof using HC HG Huctx.
    unfold check_leqb_universe_gen,
          gc_leq_universe, gc_leq_universe_n,
          leqb_universe_n_gen, gc_leq0_universe_n.
    destruct check_univs; [|split; trivial].
    split; cbn.
    - move/orP => [|].
      + rewrite univ_expr_eqb_true_iff.
        intros <- v Hv. lia.
      + now eapply (leqb_universe_n_spec0_gen _ _ false).
    - intros H; eapply (leqb_universe_n_spec_gen _ _ false) in H; tas.
      unfold leqb_universe_n_gen in H. rewrite H.
      now rewrite orb_true_r.
    Unshelve. all:eauto.
  Qed.

  Definition check_leqb_universe_spec := check_leqb_universe_spec_gen _ leqb_level_n_spec.

  Definition check_eqb_universe := (check_eqb_universe_gen leqb_level_n).

  Lemma check_eqb_universe_spec_gen leqb_level_n_gen
      (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
      (l1 l2 : Universe.t)
      (Hu1  : gc_levels_declared l1)
      (Hu2  : gc_levels_declared l2)
    : check_eqb_universe_gen leqb_level_n_gen l1 l2 <-> gc_eq_universe uctx.2 l1 l2.
  Proof using HC HG Huctx.
    unfold check_eqb_universe_gen, gc_eq_universe.
    destruct check_univs; [|split; trivial].
    split; cbn.
    - move/orP => [ | /andP [Hle Hge]].
      + rewrite univ_expr_eqb_true_iff.
        now intros <- v Hv.
      + eapply leqb_universe_n_spec0_gen in Hle, Hge; eauto.
        unfold_univ_rel0. specialize (Hle v Hv); specialize (Hge v Hv).
        simpl in *. lia.
    - intros H. toProp; right.
      toProp; eapply leqb_universe_n_spec_gen; tas; intros v Hv; specialize (H v Hv).
      rewrite H. cbn; lia.
      rewrite H. cbn; lia.
  Qed.

  Definition check_eqb_universe_spec := check_eqb_universe_spec_gen _ leqb_level_n_spec.

  Lemma fold_left_false {A} l : fold_left (B:=A) (fun _ : bool => xpred0) l false = false.
  Proof using Type.
    induction l; simpl; eauto.
  Qed.

  Definition check_gc_constraint := (check_gc_constraint_gen leqb_level_n).

  Definition check_gc_constraints := (check_gc_constraints_gen leqb_level_n).

  Definition check_constraints := (check_constraints_gen leqb_level_n).


  Definition gc_levels_declared' (vset : VSet.t) gc :=
     match gc with
    | GoodConstraint.gc_le l _ l' => VSet.In (VariableLevel.to_noprop l) vset /\
      VSet.In (VariableLevel.to_noprop l') vset
    | GoodConstraint.gc_lt_set_level _ n | GoodConstraint.gc_le_level_set n _ =>
	     VSet.In (Level.level  n) vset
    | GoodConstraint.gc_le_set_var _ n | GoodConstraint.gc_le_var_set n _ => VSet.In (Level.lvar n) vset
     end.

  Definition gcs_levels_declared (vset : VSet.t) gcs :=
    GoodUnivConstraintSet.For_all (gc_levels_declared' vset) gcs.


  Lemma check_gc_constraint_spec_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
    gc
    (Hu1 : gc_levels_declared' uctx.1 gc)
    : check_gc_constraint_gen leqb_level_n_gen gc
      -> if check_univs then forall v, gc_satisfies v uctx.2 -> gc_satisfies0 v gc else True.
  Proof using Huctx.
    unfold check_gc_constraint_gen.
    destruct check_univs; [cbn|trivial].
    destruct gc as [l z l'|k l|k n|l k|n k].
    - intros HH v Hv; eapply leqb_correct in HH; eauto.
      specialize (HH v Hv). cbn in *. toProp.
      pose proof (val_level_of_variable_level v l).
      pose proof (val_level_of_variable_level v l').
      destruct l, l'; cbn in *; lia.
      all: now inversion Hu1.
    - intros HH v Hv; eapply leqb_correct in HH; eauto.
      specialize (HH v Hv). cbn -[Z.of_nat] in HH. unfold gc_satisfies0. toProp.
      cbn in *. lia.
      now inversion Huctx.
    - intros HH v Hv; apply leqb_correct in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lia. now inversion Huctx. now inversion Hu1.
    - intros HH v Hv; apply leqb_correct in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lia. now inversion Hu1. now inversion Huctx.
    - intros HH v Hv; apply leqb_correct in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lia. now inversion Hu1. now inversion Huctx.
  Qed.

  Definition check_gc_constraint_spec := check_gc_constraint_spec_gen _ leqb_level_n_spec.

  Lemma check_gc_constraints_spec_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
    ctrs (Hu1 : gcs_levels_declared uctx.1 ctrs)
    : check_gc_constraints_gen leqb_level_n_gen ctrs
      -> if check_univs then forall v, gc_satisfies v uctx.2 -> gc_satisfies v ctrs else True.
  Proof using Huctx.
    rewrite /gcs_levels_declared in Hu1. pose proof check_gc_constraint_spec_gen as XX.
    unfold check_gc_constraints_gen. destruct check_univs; [cbn|trivial].
    intros HH v Hv.
    apply GoodUnivConstraintSet.for_all_spec. now intros x y [].
    apply GoodUnivConstraintSet.for_all_spec in HH. 2: now intros x y [].
    intros gc Hgc. specialize (HH gc Hgc).
    eapply XX; try eassumption. now apply Hu1.
  Qed.

  Definition check_gc_constraints_spec := check_gc_constraints_spec_gen _ leqb_level_n_spec.

  Definition eqb_univ_instance := (eqb_univ_instance_gen leqb_level_n).

  Definition leqb_sort := (leqb_sort_gen leqb_level_n).

  Definition check_leqb_sort := (check_leqb_sort_gen leqb_level_n).

  Definition check_eqb_sort := (check_eqb_sort_gen leqb_level_n).

  Lemma check_eqb_sort_refl_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen) u :
    check_eqb_sort_gen leqb_level_n_gen u u.
  Proof using Type.
    unfold check_eqb_sort_gen; toProp; left.
    apply eqb_refl.
  Qed.

  Definition check_eqb_sort_refl := check_eqb_sort_refl_gen _ leqb_level_n_spec.

  Definition gc_leq_sort φ :=
    leq_sort_n_ (fun n u u' => if check_univs then gc_leq0_universe_n n φ u u' else True) 0.

  Definition gc_eq_sort φ :=
    eq_sort_ (fun u u' => if check_univs then gc_eq0_universe φ u u' else True).

  Let levels_declared_sort (s : Sort.t) :=
    Sort.on_sort gc_levels_declared True s.

  Lemma check_eqb_sort_spec_gen leqb_level_n_gen
      (leqb_correct : leqb_level_n_spec_gen leqb_level_n_gen)
      (u1 u2 : Sort.t)
      (Hu1 : levels_declared_sort u1)
      (Hu2 : levels_declared_sort u2)
    : check_eqb_sort_gen leqb_level_n_gen u1 u2 <-> gc_eq_sort uctx.2 u1 u2.
  Proof.
    unfold check_eqb_sort_gen, gc_eq_sort.
    destruct u1, u2; cbnr; split; intuition auto.
    - now destruct prop_sub_type.
    - eapply check_eqb_universe_spec_gen; eauto; tas.
      unfold check_eqb_sort_gen, check_eqb_universe_gen in *; cbn in *.
      unfold check_leqb_universe_gen in *.
      destruct check_univs; cbnr.
      unfold eqb at 1, Sort.reflect_eq_sort, Sort.eqb in H. cbn in H.
      move/orP : H => /= [-> //|] /andP[] /orP[-> //|] H1 /orP[e | H2].
      1: apply NonEmptySetFacts.univ_expr_eqb_true_iff in e as ->.
      1: toProp; left; now apply NonEmptySetFacts.univ_expr_eqb_true_iff.
      toProp; right; now toProp.
    - toProp; right.
      eapply check_eqb_universe_spec_gen in H; eauto; tas.
      unfold check_eqb_universe_gen in *; cbn in *.
      unfold check_leqb_universe_gen in *.
      destruct check_univs; [cbn in * | trivial].
      move/orP : H => [H | /andP [H1 H2]].
      + apply NonEmptySetFacts.univ_expr_eqb_true_iff in H as ->.
        toProp; toProp; left; now apply NonEmptySetFacts.univ_expr_eqb_true_iff.
      + toProp; toProp; right; assumption.
  Defined.

  Definition check_eqb_sort_spec := check_eqb_sort_spec_gen _ leqb_level_n_spec.

End CheckLeq.

(* This section: specif in term of raw uctx *)
Section CheckLeq2.
  Context {cf:checker_flags}.

  Definition is_graph_of_uctx G uctx
    := on_Some (fun uctx => Equal_graph (make_graph uctx) G) (gc_of_uctx uctx).

  Context (G : universes_graph)
          uctx (Huctx: global_uctx_invariants uctx) (HC : consistent uctx.2)
          (HG : is_graph_of_uctx G uctx).

  Definition uctx' : VSet.t × GoodUnivConstraintSet.t.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    exact (uctx.1, ctrs).
    contradiction HG.
  Defined.

  #[clearbody] Let Huctx' : global_gc_uctx_invariants uctx'.
    unfold uctx'; cbn.
    eapply gc_of_uctx_invariants; tea.
    unfold is_graph_of_uctx, gc_of_uctx in *. cbn.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    reflexivity. contradiction HG.
  Defined.

  #[clearbody]
  Let HC' : gc_consistent uctx'.2.
    unfold uctx'; cbn. clear Huctx'.
    apply gc_consistent_iff in HC.
    unfold is_graph_of_uctx, gc_of_uctx in *.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    exact HC. contradiction HG.
  Defined.

  #[clearbody]
  Let HG' : Equal_graph G (make_graph uctx').
    unfold uctx' in *; cbn. clear Huctx'.
    unfold is_graph_of_uctx, gc_of_uctx in *.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    symmetry; exact HG. contradiction HG.
  Defined.

  Let level_declared (l : Level.t) := LevelSet.In l uctx.1.

  Let expr_declared (e : LevelExpr.t)
    := on_Some_or_None (fun l : Level.t => level_declared l)
                       (LevelExpr.get_noprop e).

  Let levels_declared (u : Universe.t) :=
    LevelExprSet.For_all expr_declared u.

  Lemma level_gc_declared_declared l
    : level_declared l -> gc_level_declared uctx' l.
  Proof using HG.
    clear. unfold uctx'.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2); [|contradiction HG].
    cbn; clear HG. unfold level_declared, gc_level_declared; cbn.
    destruct l; cbn; trivial; intro.
  Qed.

  Lemma expr_gc_declared_declared e
    : expr_declared e -> gc_expr_declared uctx' e.
  Proof using HG level_declared.
    destruct e as [l b]; cbn; trivial.
    intro; now apply (level_gc_declared_declared l) in H.
  Qed.

  Lemma levels_gc_declared_declared (u : Universe.t)
    : levels_declared u -> gc_levels_declared uctx' u.
  Proof using HG expr_declared.
    unfold levels_declared, gc_levels_declared.
    intros HH e He; specialize (HH e He).
    now apply expr_gc_declared_declared.
  Qed.

  Lemma leqb_univ_expr_n_spec_gen' leqb_level_n_gen
        (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen)
        lt e1 u
        (He1 : expr_declared e1)
        (Hu : levels_declared u)
    : leqb_expr_univ_n_gen leqb_level_n_gen ⎩ lt ⎭ e1 u
      <-> leq0_universe_n ⎩ lt ⎭ uctx.2 (Universe.make e1) u.
  Proof using HG' Huctx'.
    etransitivity.
    eapply (leqb_expr_univ_n_spec_gen G uctx' Huctx' HC' HG'); eauto; tas.
    - apply expr_gc_declared_declared; tas.
    - apply levels_gc_declared_declared; tas.
    - symmetry. etransitivity. apply gc_leq0_universe_n_iff.
      unfold uctx'; cbn; clear -HG.
      unfold is_graph_of_uctx, gc_of_uctx in *.
      destruct (gc_of_constraints uctx.2) as [ctrs|].
      reflexivity. contradiction HG.
  Qed.

  Definition leqb_univ_expr_n_spec' :=
      leqb_univ_expr_n_spec_gen' _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_leqb_universe_spec_gen' leqb_level_n_gen
      (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen)
      u1 u2
    : levels_declared u1 ->
      levels_declared u2 ->
      check_leqb_universe_gen leqb_level_n_gen u1 u2 -> leq_universe uctx.2 u1 u2.
  Proof using HG' Huctx'.
    unfold check_leqb_universe_gen; intros Hu1 Hu2 H.
    unfold_univ_rel.
    cbn in H; toProp H; destruct H as [e | ].
    { apply NonEmptySetFacts.univ_expr_eqb_true_iff in e. destruct e; lia. }
    eapply leqb_universe_n_spec0_gen in H; eauto.
    eapply gc_leq0_universe_iff; tea.
    unfold uctx' in *.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2). cbn in *. exact H.
    exact I.
    Unshelve. all: try eapply levels_gc_declared_declared; eauto.
  Qed.

  Definition check_leqb_universe_spec' :=
    check_leqb_universe_spec_gen' _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_leqb_universe_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) u1 u2 :
    levels_declared u1 ->
    levels_declared u2 ->
    leq_universe uctx.2 u1 u2 ->
    check_leqb_universe_gen leqb_level_n_gen u1 u2.
  Proof using HG' Huctx'.
    intros decl1 decl2.
    apply levels_gc_declared_declared in decl1.
    apply levels_gc_declared_declared in decl2.
    rewrite gc_leq_universe_iff.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    unfold uctx' in *.
    destruct gc_of_constraints; [cbn in *|contradiction HG].
    intros eq.
    apply <- check_leqb_universe_spec_gen; eauto.
    exact eq.
  Qed.

  Definition check_leqb_universe_complete :=
    check_leqb_universe_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_eqb_universe_spec_gen' leqb_level_n_gen
      (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen)
      u1 u2
    : levels_declared u1 ->
      levels_declared u2 ->
      check_eqb_universe_gen leqb_level_n_gen u1 u2 -> eq_universe uctx.2 u1 u2.
  Proof using HG' Huctx'.
    unfold check_eqb_universe_gen; intros Hu1 Hu2 H.
    unfold_univ_rel.
    cbn in H; toProp H; destruct H as [e | ].
    { apply NonEmptySetFacts.univ_expr_eqb_true_iff in e. destruct e; lia. }
    apply andb_prop in H. destruct H as [H1 H2].
    unshelve eapply leqb_universe_n_spec0_gen in H1; eauto.
    unshelve eapply leqb_universe_n_spec0_gen in H2; eauto.
    unfold uctx' in *.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    apply <- eq0_leq0_universe; tea.
    split; eapply gc_leq0_universe_iff;
      (destruct (gc_of_constraints uctx.2); [cbn in *|contradiction HG]); tas.
    all: now eapply levels_gc_declared_declared.
  Qed.

  Definition check_eqb_universe_spec' :=
    check_eqb_universe_spec_gen' _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_eqb_universe_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) u1 u2 :
    levels_declared u1 ->
    levels_declared u2 ->
    eq_universe uctx.2 u1 u2 ->
    check_eqb_universe_gen leqb_level_n_gen u1 u2.
  Proof using HG' Huctx'.
    intros decl1 decl2.
    apply levels_gc_declared_declared in decl1.
    apply levels_gc_declared_declared in decl2.
    rewrite gc_eq_universe_iff.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    unfold uctx' in *.
    destruct gc_of_constraints; [cbn in *|contradiction HG].
    intros eq.
    apply <- check_eqb_universe_spec_gen; eauto.
    exact eq.
  Qed.

  Definition check_eqb_universe_complete :=
    check_eqb_universe_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Definition leq0_level_n z l l' :=
    leq0_universe_n z uctx.2 (Universe.make' l) (Universe.make' l').

  Definition valid_gc_constraint (gc : GoodConstraint.t) :=
    match gc with
    | GoodConstraint.gc_le l z l' => leq0_level_n z l l'
    | GoodConstraint.gc_lt_set_level k l => leq0_level_n (Z.of_nat (S k)) lzero (Level.level  l)
    | GoodConstraint.gc_le_set_var k n => leq0_level_n (Z.of_nat k) lzero (Level.lvar n)
    | GoodConstraint.gc_le_level_set l k => leq0_level_n (- Z.of_nat k)%Z (Level.level  l) lzero
    | GoodConstraint.gc_le_var_set n k => leq0_level_n (- Z.of_nat k)%Z (Level.lvar n) lzero
    end.

  Definition valid_gc_constraints (gcs : GoodUnivConstraintSet.t) :=
    GoodUnivConstraintSet.For_all valid_gc_constraint gcs.

  Lemma leq0_level_n_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) z l l' :
    level_declared l ->
    level_declared l' ->
    leq0_level_n z l l' ->
    leqb_level_n_gen z l l'.
  Proof using HG' Huctx'.
    intros decll decll'.
    unfold leq0_level_n.
    intros le; eapply gc_leq0_universe_n_iff in le.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    unfold uctx' in *.
    destruct gc_of_constraints; [cbn in *|contradiction HG].
    now eapply leqb_correct.
  Qed.

  Definition leq0_level_n_complete :=
    leq0_level_n_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_gc_constraint_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) cstr :
    gc_levels_declared' uctx.1 cstr ->
    valid_gc_constraint cstr ->
    check_gc_constraint_gen leqb_level_n_gen cstr.
  Proof using HG' Huctx'.
    rewrite /check_gc_constraint_gen.
    destruct check_univs eqn:cu => //=.
    destruct cstr; cbn; intros hin;
    eapply leq0_level_n_complete_gen; intuition auto.
    all:apply Huctx.
  Qed.

  Definition check_gc_constraint_complete :=
    check_gc_constraint_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_gc_constraints_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) cstrs :
    gcs_levels_declared uctx.1 cstrs ->
    valid_gc_constraints cstrs ->
    check_gc_constraints_gen leqb_level_n_gen cstrs.
  Proof using HG' Huctx'.
    rewrite /gcs_levels_declared /valid_gc_constraints /check_gc_constraints.
    intros hdecl hval.
    eapply GoodConstraintSetFact.for_all_iff. typeclasses eauto.
    intros cstr hcstr. specialize (hdecl cstr hcstr).
    specialize (hval cstr hcstr). eapply check_gc_constraint_complete_gen => //.
  Qed.

  Definition check_gc_constraints_complete :=
    check_gc_constraints_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Definition valid_gc_constraints_ext gc :=
    forall v, satisfies v uctx.2 -> gc_satisfies v gc.

  Lemma valid_gc_constraints_aux gc :
    valid_gc_constraints_ext gc ->
    valid_gc_constraints gc.
  Proof using Type.
    intros Hv v inv.
    unfold gc_satisfies in Hv.
    destruct v; cbn in *; red;
    intros v Hv'; specialize (Hv _ Hv');
    eapply GoodConstraintSetFact.for_all_iff in Hv; try typeclasses eauto;
    specialize (Hv _ inv); cbn in Hv; cbn;
    rewrite ?val_level_of_variable_level //.

    now eapply Z.leb_le in Hv.
    eapply Nat.leb_le in Hv. lia.
    apply Nat.leb_le in Hv. lia.
    apply Nat.leb_le in Hv. lia.
    apply Nat.leb_le in Hv. lia.
  Qed.

  Lemma valid_valid_gc cstrs gc :
    check_univs ->
    valid_constraints uctx.2 cstrs ->
    gc_of_constraints cstrs = Some gc ->
    valid_gc_constraints gc.
  Proof using Type.
    intros cu Hgc vgc. apply valid_gc_constraints_aux.
    intros v Hv.
    pose proof (gc_of_constraints_spec v cstrs).
    rewrite vgc /= in H. apply H.
    rewrite /valid_constraints cu in Hgc. apply Hgc. apply Hv.
  Qed.

  Lemma gc_of_constraints_declared cstrs levels gc :
    global_uctx_invariants (levels, cstrs) ->
    gc_of_constraints cstrs = Some gc ->
    gcs_levels_declared levels gc.
  Proof using Type.
    intros Hlev hc.
    pose proof (gc_of_uctx_invariants (levels, cstrs) (levels, gc)).
    cbn in H. rewrite hc in H. specialize (H eq_refl). now apply H.
  Qed.

  Lemma check_constraints_spec_gen  leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) ctrs
    : global_uctx_invariants (uctx.1, ctrs) ->
      check_constraints_gen leqb_level_n_gen ctrs -> valid_constraints uctx.2 ctrs.
  Proof using HG' Huctx'.
    unfold check_constraints_gen, valid_constraints.
    case_eq (gc_of_constraints ctrs); [|try discriminate].
    intros ctrs' Hctrs' Hdeclared HH.
    epose proof check_gc_constraints_spec_gen.
    destruct check_univs => //=.
    intros v Hv.
    apply gc_of_constraints_spec.
    apply gc_of_constraints_spec in Hv.
    rewrite Hctrs'; cbn. eapply H; eauto;
    clear -HG Hv Hdeclared Hctrs';
    unfold is_graph_of_uctx, gc_of_uctx in HG;
    unfold uctx' in *; destruct (gc_of_constraints uctx.2) => //; cbn in *.
    eapply gc_of_constraints_declared; eauto.
  Qed.

  Definition check_constraints_spec :=
    check_constraints_spec_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  (* Completeness holds only for well-formed constraints sets *)
  Lemma check_constraints_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) ctrs :
    check_univs ->
    global_uctx_invariants (uctx.1, ctrs) ->
    valid_constraints uctx.2 ctrs ->
    check_constraints_gen leqb_level_n_gen ctrs.
  Proof using HG' Huctx'.
    intros cu gu vc.
    unfold check_constraints_gen.
    case_eq (gc_of_constraints ctrs); [|try discriminate].
    2:{ destruct HC as [v Hv].
        pose proof (gc_of_constraints_spec v ctrs).
        intros.
        rewrite /valid_constraints cu in vc.
        specialize (vc v Hv).
        rewrite H0 in H. intuition. }
    intros cstr gc.
    eapply check_gc_constraints_complete_gen; eauto.
    { eapply gc_of_constraints_declared. 2:tea. cbn. red in gu.  unfold is_graph_of_uctx, gc_of_uctx in HG.
      unfold uctx' in *.
      destruct (gc_of_constraints uctx.2) => //; cbn in uctx', HG. }
    eapply valid_valid_gc; tea.
  Qed.

  Definition check_constraints_complete :=
    check_constraints_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Let levels_declared_sort (s : Sort.t)
    := Sort.on_sort levels_declared True s.

  Lemma levels_univ_gc_declared_declared (s : Sort.t)
    : levels_declared_sort s -> gc_levels_declared_sort uctx' s.
  Proof using HG levels_declared.
    destruct s; cbnr.
    apply levels_gc_declared_declared.
  Qed.

  Lemma check_leqb_sort_spec_gen' leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) s1 s2
    : levels_declared_sort s1 ->
      levels_declared_sort s2 ->
      check_leqb_sort_gen leqb_level_n_gen s1 s2 -> leq_sort uctx.2 s1 s2.
  Proof using HG' Huctx'.
    intros Hu1 Hu2. move => /orP [H | H].
    - apply eqb_true_iff in H as ->.
      reflexivity.
    - destruct s1, s2; cbn in *; trivial; try discriminate H.
      now eapply check_leqb_universe_spec_gen'.
  Qed.

  Definition check_leqb_sort_spec' :=
    check_leqb_sort_spec_gen' _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_leqb_sort_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) s1 s2 :
    levels_declared_sort s1 ->
    levels_declared_sort s2 ->
    leq_sort uctx.2 s1 s2 ->
    check_leqb_sort_gen leqb_level_n_gen s1 s2.
  Proof using HG' Huctx'.
    move : s1 s2 => [| | u1] [| | u2] //. cbn.
    intros decl1 decl2 Hle.
    unfold check_leqb_sort_gen.
    toProp; right.
    apply check_leqb_universe_complete_gen => //.
  Qed.

  Definition check_leqb_sort_complete :=
    check_leqb_sort_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_eqb_sort_spec_gen' leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) s1 s2
    : levels_declared_sort s1 ->
      levels_declared_sort s2 ->
      check_eqb_sort_gen leqb_level_n_gen s1 s2 -> eq_sort uctx.2 s1 s2.
  Proof using HG' Huctx'.
    move : s1 s2 => [| | u1] [| | u2] //; intros Hu1 Hu2.
    { move/andP => [H HH] //. }
    move/orP => [H | H].
    - apply eqb_true_iff in H as ->.
      reflexivity.
    - eapply check_eqb_universe_spec_gen'; eauto.
      cbn in H. unfold check_eqb_universe_gen in *.
      move/andP: H => [/orP [/orP [-> | ->] | ->] /orP [/orP [He | HH] | ->]] //.
      all: try now rewrite orb_true_r.
      now rewrite He.
      apply NonEmptySetFacts.univ_expr_eqb_true_iff in HH as ->.
      toProp; left; toProp; right; now apply NonEmptySetFacts.univ_expr_eqb_true_iff.
  Qed.

  Definition check_eqb_sort_spec' :=
    check_eqb_sort_spec_gen' _ (leqb_level_n_spec _ _ Huctx' HC' HG').

  Lemma check_eqb_sort_complete_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) u1 u2 :
    levels_declared_sort u1 ->
    levels_declared_sort u2 ->
    eq_sort uctx.2 u1 u2 ->
    check_eqb_sort_gen leqb_level_n_gen u1 u2.
  Proof using HG' Huctx'.
    move : u1 u2 => [| | u1] [| | u2] //. cbn.
    intros decl1 decl2 Hle.
    eapply check_eqb_universe_complete_gen in Hle => //; eauto.
    unfold check_eqb_sort_gen, leqb_sort_gen, check_leqb_universe_gen; cbn.
    unfold check_eqb_universe_gen in Hle.
    move/orP: Hle => [/orP [-> | e] | /andP [H1 H2]] //=.
    now rewrite orb_true_r.
    apply eqb_eq in e as ->; rewrite eqb_refl //.
    toProp; right; toProp; toProp; right; assumption.
  Qed.

  Definition check_eqb_sort_complete :=
    check_eqb_sort_complete_gen _ (leqb_level_n_spec _ _ Huctx' HC' HG').

End CheckLeq2.

Section AddLevelsCstrs.

  Definition add_uctx (uctx : VSet.t × GoodUnivConstraintSet.t)
             (G : universes_graph) : universes_graph
    := let levels := VSet.union uctx.1 G.1.1 in
       let edges := add_level_edges uctx.1 G.1.2 in
       let edges := add_cstrs uctx.2 edges in
       (levels, edges, G.2).

  Definition uctx_of_udecl u : ContextSet.t :=
    (levels_of_udecl u, constraints_of_udecl u).

  Lemma gcs_elements_union s s' : GoodUnivConstraintSet.Empty s' ->
    GoodUnivConstraintSet.Equal (GoodUnivConstraintSet.union s s') s.
  Proof. gcsets. Qed.

  Lemma add_level_edges_spec e x g :
    EdgeSet.In e (add_level_edges x g) <->
    (exists c, option_edge_of_level c = Some e /\ VSet.In c x) \/ EdgeSet.In e g.
  Proof.
    rewrite /add_level_edges VSet.fold_spec.
    setoid_rewrite (VSetFact.elements_iff x). setoid_rewrite InA_In_eq.
    induction (VSet.elements x) in g |- *; simpl.
    intuition auto. now destruct H0 as [c [_ F]].
    rewrite {}IHl.
    split.
    * intros [[c [eq inl]]|?]; firstorder auto.
      destruct a as [|s|n]; simpl in *; auto.
      rewrite -> EdgeSet.add_spec in H. intuition auto.
      subst e. left; exists (Level.level  s); intuition auto.
      rewrite -> EdgeSet.add_spec in H. intuition auto.
      subst e. left; eexists; intuition eauto. reflexivity.
    * intros [[[|s|n] [[= <-] [->|inl]]]|?]; simpl; auto;
      rewrite -> ?EdgeSet.add_spec; simpl; intuition auto.
      left. exists (Level.level  s); auto.
      left. exists (Level.lvar n); auto.
      destruct a; simpl; rewrite -> ?EdgeSet.add_spec; simpl; intuition auto.
  Qed.

  Lemma add_cstrs_union g ctrs1 ctrs2 :
    EdgeSet.Equal (add_cstrs (GoodUnivConstraintSet.union ctrs1 ctrs2) g) (add_cstrs ctrs1 (add_cstrs ctrs2 g)).
  Proof.
    intros e.
    rewrite !add_cstrs_spec.
    setoid_rewrite GoodUnivConstraintSet.union_spec.
    firstorder eauto.
  Qed.

  Lemma add_level_edges_union g l1 l2 :
    EdgeSet.Equal (add_level_edges (VSet.union l1 l2) g)
    (add_level_edges l1 (add_level_edges l2 g)).
  Proof.
    intros e.
    rewrite !add_level_edges_spec.
    setoid_rewrite VSet.union_spec.
    firstorder eauto.
  Qed.

  Lemma add_level_edges_add_cstrs_comm l c g :
    EdgeSet.Equal (add_level_edges l (add_cstrs c g))
      (add_cstrs c (add_level_edges l g)).
  Proof.
    intros e.
    rewrite !add_level_edges_spec !add_cstrs_spec add_level_edges_spec.
    firstorder auto.
  Qed.

  Lemma forallb_spec {A : Type} (p : A -> bool) (l : list A) :
    match forallb p l with
    | true => forall x : A, In x l -> p x
    | false => exists x : A, In x l × p x = false
    end.
  Proof.
    induction l; cbn.
    - now intros.
    - destruct (forallb p l) eqn:heq.
      rewrite andb_true_r.
      destruct (p a) eqn:he.
      intros x []. subst; auto. now apply IHl.
      exists a; auto.
      rewrite andb_false_r. destruct IHl as [x [inx hx]].
      exists x. intuition auto.
  Qed.

  Lemma forallb_in {A : Type} (p : A -> bool) (l l' : list A) :
    (forall x : A, In x l <-> In x l') ->
    forallb p l = forallb p l'.
  Proof.
    intros heq.
    generalize (forallb_spec p l).
    generalize (forallb_spec p l').
    do 2 destruct forallb; intuition auto.
    destruct H0 as [x [hin hp]].
    - specialize (H x (proj1 (heq x) hin)). red in H; congruence.
    - destruct H as [x [hin hp]].
      specialize (H0 x (proj2 (heq _) hin)). congruence.
  Qed.

  Lemma levelset_for_all_eq f f' l l' :
    (forall x, f x = f' x) -> LevelSet.Equal l l' ->
    LevelSet.for_all f l = LevelSet.for_all f' l'.
  Proof.
    intros Hf heq.
    rewrite !VSetFact.for_all_b.
    setoid_replace f with f'; auto.
    eapply forallb_in.
    intros x.
    red in heq.
    specialize (heq x).
    rewrite -!InA_In_eq.
    now rewrite -!LevelSetFact.elements_iff.
  Qed.

  Lemma Nbar_max_spec n m v :
    Nbar.max n m = v ->
    (Nbar.le n m /\ v = m) \/ (Nbar.le m n /\ v = n).
  Proof.
    destruct n, m; cbn; firstorder.
    destruct (Z.max_spec_le z z0); firstorder; try lia.
    left. split; auto. congruence.
    right. split; auto. congruence.
  Qed.

  Lemma Nbar_max_spec' n m :
    Nbar.le n m -> Nbar.max m n = m.
  Proof.
    destruct n, m; cbn; firstorder. f_equal. lia.
  Qed.

  Lemma Nbar_max_spec'' n m :
    Nbar.le n m -> Nbar.max n m = m.
  Proof.
    destruct n, m; cbn; firstorder. f_equal. lia.
  Qed.

  Lemma Nbar_max_le n m k : Nbar.le (Nbar.max n m) k ->
    Nbar.le n k /\ Nbar.le m k.
  Proof.
    intros hl.
    generalize (Nbar_max_spec n m _ eq_refl). intuition subst; try rewrite H1 in hl; auto.
    - now transitivity m.
    - now transitivity n.
  Qed.

  Lemma fold_left_max_spec (l : list Nbar.t) acc n :
    fold_left Nbar.max l acc = n ->
    (n = acc /\ (forall x, In x l -> Nbar.le x n)) \/
    (In n l /\ Nbar.le acc n /\ (forall x, In x l -> Nbar.le x n)).
  Proof.
    induction l in acc, n |- *.
    - cbn. intros ->; firstorder.
    - cbn. intros H. specialize (IHl _ _ H).
      destruct IHl. firstorder auto.
      symmetry in H0. apply Nbar_max_spec in H0.
      firstorder auto. right. firstorder auto. subst; auto. now rewrite H2. subst x n.
      rewrite H2. reflexivity.
      left. firstorder auto. subst x n. now rewrite H2.
      destruct H0.
      right. firstorder auto.
      now apply Nbar_max_le in H1.
      now apply Nbar_max_le in H1.
  Qed.


  Lemma fold_left_max_spec' (l : list Nbar.t) acc n :
    (n = acc /\ (forall x, In x l -> Nbar.le x n)) \/
    (In n l /\ Nbar.le acc n /\ (forall x, In x l -> Nbar.le x n)) ->
    fold_left Nbar.max l acc = n.
  Proof.
    induction l in acc, n |- *.
    - cbn. intuition.
    - cbn. intros H.
      apply IHl. intuition auto.
      subst acc.
      pose proof (H1 a). left. split. symmetry. eapply Nbar_max_spec'; auto.
      intuition auto.
      left. split; intuition auto. subst a.
      symmetry. now apply Nbar_max_spec''.
      right. intuition auto. specialize (H2 a).
      apply Nbar.max_lub; auto.
  Qed.

  Lemma fold_left_comm_ext (l l' : list Nbar.t) :
    (forall x, In x l <-> In x l') ->
    fold_left Nbar.max l ≐1 fold_left Nbar.max l'.
  Proof.
    intros eql acc.
    generalize (fold_left_max_spec l acc _ eq_refl).
    generalize (fold_left_max_spec l' acc _ eq_refl).
    intuition auto.
    - now rewrite H H0.
    - rewrite H. apply fold_left_max_spec'. left; intuition auto.
      specialize (H2 x (proj1 (eql _) H3)). congruence.
    - rewrite H0. symmetry.
      apply fold_left_max_spec'. left; intuition auto.
      specialize (H4 x (proj2 (eql _) H2)). congruence.
    - apply fold_left_max_spec'. right.
      intuition auto. now apply eql. now apply H3, eql.
  Qed.

  Lemma fold_left_comm_ext2 f f' (l l' : list (Z × Level.t)) : f ≐1 f' ->
    (forall x, In x l <-> In x l') ->
    fold_left Nbar.max (map f l) ≐1 fold_left Nbar.max (map f' l').
  Proof.
    intros eqf eqg.
    apply fold_left_comm_ext.
    intros.
    rewrite !in_map_iff. firstorder eauto.
    specialize (eqg x0). exists x0; intuition auto. now rewrite -eqf.
    exists x0. specialize (eqg x0). rewrite eqf; intuition auto.
  Qed.

  Lemma Equal_graph_edges {e e'} : Equal_graph e e' ->
    forall x, In x (EdgeSet.elements e.1.2) <-> In x (EdgeSet.elements e'.1.2).
  Proof.
    intros [vs [es ?]]. intros x. red in vs.
    now rewrite -!InA_In_eq -!EdgeSetFact.elements_iff.
  Qed.

  Lemma succs_proper x e e' v: Equal_graph e e' ->
    In x (succs e v) <-> In x (succs e' v).
  Proof.
    intros eq. unfold succs.
    rewrite !in_map_iff.
    setoid_rewrite filter_In.
    now setoid_rewrite (Equal_graph_edges eq).
  Qed.

  Lemma fold_left_comm_ext3 f f' e e' x : f ≐1 f' ->
    Equal_graph e e' ->
    fold_left Nbar.max (map f (succs e x)) ≐1
    fold_left Nbar.max (map f' (succs e' x)).
  Proof.
    intros eqf eqg.
    apply fold_left_comm_ext2; auto.
    intros. now apply succs_proper.
  Qed.

  #[global] Instance lsp_proper : Morphisms.Proper ((=_g) ==> Logic.eq ==> Logic.eq ==> Logic.eq)%signature lsp.
  Proof.
    intros e e' He x ? <- y ? <-.
    unfold lsp, lsp0.
    pose proof (proj1 He).
    change (wGraph.V e) with e.1.1.
    change (wGraph.V e') with e'.1.1.
    replace (LevelSet.cardinal e'.1.1) with (LevelSet.cardinal e.1.1).
    2:{ now rewrite H. }
    revert H.
    generalize e.1.1, e'.1.1. intros t0 t1.
    induction (LevelSet.cardinal t0) in t0, t1, e, e', He, x, y |- *. cbn; auto.
    cbn. intros eqt.
    replace (LevelSet.mem x t0) with (LevelSet.mem x t1).
    2:{ now rewrite eqt. }
    destruct LevelSet.mem; auto.
    apply fold_left_comm_ext3; auto.
    intros [n0 y0]. f_equal.
    apply (IHn e e' He).
    intros elt. rewrite !LevelSet.remove_spec.
    intuition auto. now apply eqt. now apply eqt.
  Qed.

  #[global] Instance is_acyclic_proper : Morphisms.Proper ((=_g) ==> Logic.eq)%signature is_acyclic.
  Proof.
    intros e e' eq.
    unfold is_acyclic.
    eapply levelset_for_all_eq; tea. cbn.
    intros x. now setoid_rewrite eq.
    apply eq.
  Qed.

  Lemma add_uctx_make_graph levels1 levels2 ctrs1 ctrs2 :
    Equal_graph (add_uctx (levels1, ctrs1) (make_graph (levels2, ctrs2)))
      (make_graph (VSet.union levels1 levels2,
                    GoodUnivConstraintSet.union ctrs1 ctrs2)).
  Proof.
    rewrite /make_graph /= /add_uctx /=.
    unfold Equal_graph. split => //. split => //.
    now rewrite add_cstrs_union /= add_level_edges_add_cstrs_comm add_level_edges_union.
  Qed.

  Lemma add_uctx_subgraph uctx G : subgraph G (add_uctx uctx G).
  Proof.
    constructor.
    - apply: VSetProp.union_subset_2.
    - move=> x hx.
      apply/add_cstrs_spec; right.
      apply/add_level_edges_spec; by right.
    - reflexivity.
  Qed.

  Lemma acyclic_no_loop_add_uctx G uctx :
    wGraph.acyclic_no_loop (add_uctx uctx G) -> wGraph.acyclic_no_loop G.
  Proof.
    apply: wGraph.subgraph_acyclic ; apply: add_uctx_subgraph.
  Qed.

  Definition gc_result_eq (x y : option GoodUnivConstraintSet.t) :=
    match x, y with
    | Some x, Some y => GoodUnivConstraintSet.eq x y
    | None, None => True
    | _, _ => False
    end.

  Lemma add_gc_of_constraint_spec {cf:checker_flags} gc t :
    match add_gc_of_constraint gc (Some t) with
    | Some t' =>
      exists gcs, gc_of_constraint gc = Some gcs /\
      GCS.Equal t' (GCS.union t gcs)
    | None => gc_of_constraint gc = None
    end.
  Proof.
    unfold add_gc_of_constraint.
    simpl.
    destruct gc_of_constraint; simpl; auto.
    eexists; split; eauto. reflexivity.
  Qed.

  Lemma fold_left_add_gc_None {cf:checker_flags} l : fold_left (fun a e => add_gc_of_constraint e a) l None = None.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma fold_left_add_gc_Some_subset {cf:checker_flags} l t t':
    fold_left (fun a e => add_gc_of_constraint e a) l (Some t) = Some t' ->
    GCS.Subset t t'.
  Proof.
    induction l in t |- *; simpl; auto. intros [= ->]. reflexivity.
    pose proof (add_gc_of_constraint_spec a t).
    destruct add_gc_of_constraint; simpl.
    intros. specialize (IHl _ H0).
    destruct H as [gcs [gca eq]].
    rewrite -> eq in IHl. gcsets.
    now rewrite fold_left_add_gc_None.
  Qed.

  Variant gc_of_constraints_view {cf:checker_flags} (s : UnivConstraintSet.t) : option GoodUnivConstraintSet.t -> Type :=
  | gc_of_constraints_ok l :
    (forall gc, GoodUnivConstraintSet.In gc l <->
    (exists c gcs, gc_of_constraint c = Some gcs /\ UnivConstraintSet.In c s /\ GoodUnivConstraintSet.In gc gcs)) ->
    (forall c, UnivConstraintSet.In c s ->
      exists gcs, gc_of_constraint c = Some gcs /\ GoodUnivConstraintSet.Subset gcs l) ->
    gc_of_constraints_view s (Some l)
  | gc_of_constraints_none :
    (exists c, UnivConstraintSet.In c s /\ gc_of_constraint c = None) ->
    gc_of_constraints_view s None.

  Lemma gc_of_constraintsP {cf:checker_flags} s : gc_of_constraints_view s (gc_of_constraints s).
  Proof.
    unfold gc_of_constraints.
    rewrite UnivConstraintSet.fold_spec.
    destruct fold_left eqn:eq.
    - constructor.
      + intros.
        setoid_rewrite ConstraintSetFact.elements_iff. setoid_rewrite InA_In_eq.
        transitivity ((exists (c : LevelConstraint.t) (gcs : GoodUnivConstraintSet.t),
          gc_of_constraint c = Some gcs /\
          In c (UnivConstraintSet.elements s) /\ GoodUnivConstraintSet.In gc gcs) \/ GCS.In gc GCS.empty).
        2:gcsets.
        revert eq.
        generalize (GCS.empty).
        induction (UnivConstraintSet.elements s) in t0 |- *; simpl in *.
        intros ? [= ->]. firstorder auto.
        intros t' Ht'.
        pose proof (add_gc_of_constraint_spec a t').
        destruct add_gc_of_constraint eqn:addgc.
        destruct H as [gcs [gceq cseq]].
        specialize (IHl _ _ Ht').
        rewrite {}IHl.
        rewrite cseq GCS.union_spec.
        split.
        * intros [[c [gcs' [gceq' [incl ingcgcs']]]]|[]]; auto.
          left. exists c, gcs'; intuition auto.
          left.
          exists a, gcs; intuition auto.
        * intros [[c [gcs' [gceq' [[->|incl] ingcgcs']]]]|?]; auto.
          ++ rewrite gceq in gceq'. noconf gceq'. auto.
          ++ left. exists c, gcs'. intuition auto.
        * rewrite fold_left_add_gc_None in Ht'. discriminate.
      + intros c.
        setoid_rewrite ConstraintSetFact.elements_iff; setoid_rewrite InA_In_eq at 1.
        revert eq.
        generalize (GCS.empty).
        induction (UnivConstraintSet.elements s) in t0 |- *; simpl in *.
        intros ? [= ->]. firstorder auto.
        intros t' Ht'.
        pose proof (add_gc_of_constraint_spec a t').
        destruct add_gc_of_constraint eqn:addgc.
        destruct H as [gcs [gceq cseq]].
        specialize (IHl _ _ Ht').
        intros [->|incl]. eexists; split; eauto.
        intros gc gcin.
        apply fold_left_add_gc_Some_subset in Ht'.
        rewrite -> cseq in Ht'. gcsets.
        now specialize (IHl incl).
        now rewrite fold_left_add_gc_None in Ht'.
    - constructor.
      setoid_rewrite ConstraintSetFact.elements_iff; setoid_rewrite InA_In_eq at 1.
      revert eq.
      generalize GCS.empty.
      induction (UnivConstraintSet.elements s); simpl in * => //.
      intros t' eq.
      pose proof (add_gc_of_constraint_spec a t').
      destruct add_gc_of_constraint eqn:addgc.
      destruct H as [gcs [gceq cseq]].
      specialize (IHl _ eq).
      destruct IHl as [c [incl gcn]].
      exists c; intuition auto.
      exists a; intuition auto.
  Qed.

  Lemma gc_of_constraints_union {cf:checker_flags} S S' :
    gc_result_eq (gc_of_constraints (UnivConstraintSet.union S S'))
      (S1 <- gc_of_constraints S ;;
      S2 <- gc_of_constraints S' ;;
      ret (GoodUnivConstraintSet.union S1 S2)).
  Proof.
    case: (gc_of_constraintsP S) => [GS HS HS0|[c [incs gcn]]]; simpl.
    case: (gc_of_constraintsP S') => [GS' HS' HS'0|GS']; simpl.
    case: (gc_of_constraintsP (UnivConstraintSet.union S S')) => [GSS' HSS' HSS'0|[c [inc gcn]]].
    simpl.
    - intros gc.
      rewrite HSS' GCS.union_spec HS HS'.
      setoid_rewrite UnivConstraintSet.union_spec.
      split. intros [c [gcs ?]]. intuition auto.
      left; firstorder auto.
      right; firstorder auto.
      intros [[c [gcs ?]]|[c [gcs ?]]]; exists c, gcs; intuition auto.
    - cbn. apply UnivConstraintSet.union_spec in inc.
      destruct inc.
      specialize (HS0 _ H). rewrite gcn in HS0. now destruct HS0.
      specialize (HS'0 _ H). rewrite gcn in HS'0. now destruct HS'0.
    - destruct GS' as [c [inc gcn]].
      case: (gc_of_constraintsP (UnivConstraintSet.union S S')) => [GSS' HSS' HSS'0|[c' [inc' gcn']]].
      cbn.
      specialize (HSS'0 c).
      rewrite -> UnivConstraintSet.union_spec in HSS'0.
      specialize (HSS'0 (or_intror inc)) as [gcs [eq _]].
      now congruence.
      split.
    - case: (gc_of_constraintsP (UnivConstraintSet.union S S')) => [GSS' HSS' HSS'0|[c' [inc' gcn']]].
      cbn.
      specialize (HSS'0 c).
      rewrite -> UnivConstraintSet.union_spec in HSS'0.
      specialize (HSS'0 (or_introl incs)) as [gcs [eq _]].
      now congruence.
      split.
  Qed.

  Lemma gc_of_uctx_union `{checker_flags} uctx1 uctx2 gc1 gc2 :
    gc_of_uctx uctx1 = Some gc1 -> gc_of_uctx uctx2 = Some gc2 ->
    ∑ gc, gc_of_uctx (ContextSet.union uctx1 uctx2) = Some (LevelSet.union gc1.1 gc2.1, gc ) /\ GCS.eq gc (GCS.union gc1.2 gc2.2).
  Proof.
    unfold gc_of_uctx.
    pose proof (H' := gc_of_constraints_union uctx1.2 uctx2.2).
    move=> eq1 eq2; move: eq1 eq2 H'.
    case: (gc_of_constraints _) => //?.
    case: (gc_of_constraints _) => //?.
    case: (gc_of_constraints _) => //=? [=] <- [=] <- /=.
    eexists; split; [reflexivity| eassumption].
  Qed.

End AddLevelsCstrs.

#[global] Instance proper_add_level_edges levels : Morphisms.Proper (wGraph.EdgeSet.Equal ==> wGraph.EdgeSet.Equal)%signature (add_level_edges levels).
Proof.
  intros e e' he.
  rewrite /add_level_edges.
  rewrite !VSet.fold_spec.
  induction (VSet.elements levels) in e, e', he |- *; cbn; auto.
  apply IHl. destruct variable_of_level => //.
  now rewrite he.
Qed.

#[global] Instance proper_add_uctx cstrs : Morphisms.Proper ((=_g) ==> Equal_graph)%signature (add_uctx cstrs).
Proof.
  intros g g' eq. rewrite /add_uctx; cbn.
  split. cbn. now rewrite (proj1 eq).
  cbn. split => //.
  rewrite /add_level_edges. now rewrite (proj1 (proj2 eq)).
  apply eq.
Qed.

#[global] Instance gc_of_constraints_proper {cf : checker_flags} : Proper ((=_ucset) ==> R_opt GoodUnivConstraintSet.Equal) gc_of_constraints.
Proof.
  intros c c' eqc; cbn.
  destruct (gc_of_constraintsP c);
  destruct (gc_of_constraintsP c'); cbn.
  - intros cs; rewrite i i0. firstorder eauto.
  - destruct e0 as [cs [incs gcn]].
    apply eqc in incs. destruct (e cs incs) as [? []]. congruence.
  - destruct e as [cs [incs gcn]].
    apply eqc in incs. destruct (e0 cs incs) as [? []]. congruence.
  - exact I.
Qed.

#[global] Instance proper_add_level_edges' : Morphisms.Proper ((=_lset) ==> wGraph.EdgeSet.Equal ==> wGraph.EdgeSet.Equal)%signature add_level_edges.
Proof.
  intros l l' hl e e' <-.
  intros x; rewrite !add_level_edges_spec. firstorder eauto.
Qed.

#[global] Instance make_graph_proper : Proper ((=_gcs) ==> (=_g)) make_graph.
Proof.
  intros [v c] [v' c'] [eqv eqc]; cbn.
  unfold make_graph; cbn in *.
  split; cbn; auto.
  split; cbn; try reflexivity.
  now rewrite eqc eqv.
Qed.


From Stdlib Require Import SetoidTactics.

#[global] Instance is_graph_of_uctx_proper {cf : checker_flags} G : Proper ((=_cs) ==> iff) (is_graph_of_uctx G).
Proof.
  intros [l c] [l' c'] [eql eqc]; cbn.
  unfold is_graph_of_uctx; cbn. cbn in *.
  pose proof (gc_of_constraints_proper _ _ eqc).
  destruct (gc_of_constraints c); cbn in *; destruct (gc_of_constraints c'); cbn.
  now setoid_replace (l, t0) with (l', t1) using relation gcs_equal. elim H. elim H.
  intuition.
Qed.


#[global] Instance subgraph_proper : Proper ((=_g) ==> (=_g) ==> iff) subgraph.
Proof.
  unshelve apply: proper_sym_impl_iff_2.
  move=> g1 g1' [eqv1 [eqe1 eqs1]]  g2 g2' [eqv2 [eqe2 eqs2]].
  move=> [*]; constructor.
  + by rewrite <- eqv1, <- eqv2.
  + by rewrite <- eqe1, <- eqe2.
  + by rewrite <- eqs1, <- eqs2.
Qed.

#[global] Instance full_subgraph_proper : Proper ((=_g) ==> (=_g) ==> iff) full_subgraph.
Proof.
  unshelve apply: proper_sym_impl_iff_2.
  move=> g1 g1' eq1 g2 g2' eq2.
  move=> [?] lsp_dom; constructor=> *; rewrite -eq1 -eq2 //.
  apply lsp_dom; rewrite /wGraph.V (proj1 eq1) //.
Qed.

Lemma add_uctx_make_graph2 uctx1 uctx2 :
  add_uctx uctx2 (make_graph uctx1) =_g make_graph (VSet.union uctx2.1 uctx1.1, GCS.union uctx2.2 uctx1.2).
Proof. destruct uctx1, uctx2; apply: add_uctx_make_graph. Qed.

Lemma gc_of_uctx_levels `{checker_flags} udecl uctx :
  gc_of_uctx udecl = Some uctx -> ContextSet.levels udecl = uctx.1.
Proof.
  rewrite /gc_of_uctx.
  case: (gc_of_constraints _)=> //= ? [=] <- //.
Qed.


Definition gctx_union gctx1 gctx2 :=
  (LS.union gctx1.1 gctx2.1, GCS.union gctx1.2 gctx2.2).


(* The other implication between invariants does not hold
   (take for example uctx = ({}, {lzero < Level "foo"}) *)
Lemma global_uctx_graph_invariants `{cf : checker_flags} [uctx gph] :
  is_graph_of_uctx gph uctx -> global_uctx_invariants uctx -> wGraph.invariants gph.
Proof.
  move=> /on_SomeP [? [Huctx <-]] H0.
  pose proof (gc_of_uctx_invariants _ _ Huctx H0).
  apply: make_graph_invariants.
Qed.

#[export] Existing Instance correct_labelling_proper.

Lemma correct_labelling_of_valuation_satisfies_iff `{checker_flags} [uctx G v] :
  is_graph_of_uctx G uctx ->
  global_uctx_invariants uctx ->
  correct_labelling G (labelling_of_valuation v) <-> satisfies v uctx.2.
Proof.
  move=> /on_SomeP [gctx [eqSome <-]] inv.
  rewrite -make_graph_spec gc_of_constraints_spec (gc_of_uctx_of_constraints _ _ eqSome) //.
Qed.

Lemma is_graph_of_uctx_levels `{cf:checker_flags} G uctx :
  is_graph_of_uctx G uctx ->
  forall x, VSet.In x (wGraph.V G) <-> LS.In x uctx.1.
Proof.
  move=> /on_SomeP [gctx [eqSome HG]] ?.
  rewrite /wGraph.V -(proj1 HG) /= -(gc_of_uctx_levels _ _ eqSome) //.
Qed.

Lemma val_valuation_of_labelling2 `{checker_flags} [uctx G l] :
  is_graph_of_uctx G uctx ->
  global_uctx_invariants uctx ->
  correct_labelling G l ->
  forall x, VSet.In x uctx.1 ->
  val (valuation_of_labelling l) x = l x.
Proof.
  move=> /on_SomeP [gctx [eqSome HG]] inv hl x hx.
  apply: val_valuation_of_labelling.
  1: symmetry; eassumption.
  2: done.
  red; rewrite -(gc_of_uctx_levels _ _ eqSome) //.
Qed.

Lemma correct_valuation_of_labelling_satisfies `{checker_flags} [uctx G l] :
  is_graph_of_uctx G uctx ->
  global_uctx_invariants uctx ->
  correct_labelling G l -> satisfies (valuation_of_labelling l) uctx.2.
Proof.
  move=> /on_SomeP [gctx [eqSome <-]] inv.
  rewrite gc_of_constraints_spec (gc_of_uctx_of_constraints _ _ eqSome) /=.
  apply: make_graph_spec'; by apply: gc_of_uctx_invariants.
Qed.

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

Lemma is_graph_of_uctx_add `{cf : checker_flags} [gph uctx uctx' gctx'] :
  gc_of_uctx uctx' = Some gctx' ->
  is_graph_of_uctx gph uctx ->
  is_graph_of_uctx (add_uctx gctx' gph) (ContextSet.union uctx' uctx).
Proof.
  move=> h' /on_SomeP [gctx [h eq]].
  red.
  move: (gc_of_uctx_union _ _ _ _ h' h) => [gc'' [-> /= ?]].
  have eq' : (gcs_equal (LS.union gctx'.1 gctx.1, gc'') (gctx_union gctx' gctx)) by split=> //=.
  rewrite <- eq, eq'; symmetry; apply: add_uctx_make_graph2.
Qed.

Lemma is_consistent_spec2 `{cf : checker_flags} [gph gctx] :
  is_graph_of_uctx gph gctx -> is_consistent gctx <-> wGraph.is_acyclic gph.
Proof.
  unfold is_consistent. by move=> /on_SomeP [? [-> <-]].
Qed.

From MetaRocq.Utils Require Import MRUtils.

Lemma global_uctx_invariants_union_or lvls1 lvls2 cs
  : global_uctx_invariants (lvls1, cs) \/ global_uctx_invariants (lvls2, cs)
    -> global_uctx_invariants (LevelSet.union lvls1 lvls2, cs).
Proof.
  cbv [global_uctx_invariants uctx_invariants UnivConstraintSet.For_all declared_univ_cstr_levels]; cbn [fst snd ContextSet.levels ContextSet.constraints].
  repeat first [ apply conj
               | progress intros
               | progress cbv beta iota in *
               | progress destruct ?
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress split_and
               | rewrite !LevelSet.union_spec
               | progress specialize_dep_under_binders_by eapply pair
               | solve [ eauto ] ].
Qed.

Lemma global_gc_uctx_invariants_union_or lvls1 lvls2 cs
  : global_gc_uctx_invariants (lvls1, cs) \/ global_gc_uctx_invariants (lvls2, cs)
    -> global_gc_uctx_invariants (VSet.union lvls1 lvls2, cs).
Proof.
  cbv [global_gc_uctx_invariants uctx_invariants GoodUnivConstraintSet.For_all declared_univ_cstr_levels]; cbn [fst snd ContextSet.levels ContextSet.constraints].
  repeat first [ apply conj
               | progress intros
               | progress cbv beta iota in *
               | progress subst
               | progress destruct ?
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress split_and
               | rewrite !VSet.union_spec
               | progress specialize_dep_under_binders_by eassumption
               | solve [ eauto ] ].
Qed.

Lemma gc_levels_declared_union_or lvls1 lvls2 cstr u
  : gc_levels_declared (lvls1, cstr) u \/ gc_levels_declared (lvls2, cstr) u
    -> gc_levels_declared (VSet.union lvls1 lvls2, cstr) u.
Proof.
  cbv [gc_levels_declared LevelExprSet.For_all gc_expr_declared on_Some_or_None LevelExpr.get_noprop]; cbn [fst].
  repeat first [ apply conj
               | progress intros
               | progress cbv beta iota in *
               | progress destruct ?
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress split_and
               | rewrite !VSet.union_spec
               | progress specialize_dep_under_binders_by eassumption
               | solve [ eauto ] ].
Qed.
