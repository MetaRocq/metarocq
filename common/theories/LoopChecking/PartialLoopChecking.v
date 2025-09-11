(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From Equations Require Import Equations.

From MetaRocq.Common.LoopChecking Require Import Common Interfaces HornClauses Model Models.

Set Equations Transparent.

Module LoopCheckingImpl (LS : LevelSets).
(* This module is actually independent of the Models, it only needs the
  lemmas in Model.v, but we do this to share the LevelSets representation. *)
Module Export Model := Models(LS).

Local Open Scope Z_scope.

Definition v_minus_w_bound (W : LevelSet.t) (m : model) :=
  LevelMap.fold (fun w v acc => Z.max (option_get 0 v) acc)
    (LevelMapFact.filter (fun l _ => ~~ LevelSet.mem l W) m) 0%Z.

(** The termination proof relies on the correctness of check_model:
  it does strictly increase a value but not above [max_gain cls].
*)

Lemma v_minus_w_bound_irrel {W} m m' :
  model_map_outside W m m' ->
  v_minus_w_bound W m = v_minus_w_bound W m'.
Proof.
  unfold v_minus_w_bound.
  intros out. eapply LevelMapFact.fold_Equal. tc. cbn.
  { intros x y eq. cbn. solve_proper. }
  { intros x y. cbn. intros e e' a neq. lia. }
  apply LevelMapFact.F.Equal_mapsto_iff.
  intros k e. rewrite -> LevelMapFact.filter_iff.
  2:{ intros x y eq. red in eq. subst; solve_proper. }
  rewrite -> LevelMapFact.filter_iff.
  2:{ move=> x y ->. solve_proper. }
  rewrite [_ = true]not_mem. intuition auto.
  - now apply out.
  - now apply out.
Qed.

Local Open Scope Z_scope.

Lemma v_minus_w_bound_spec W m :
  forall x, ~ LevelSet.In x W -> level_value m x ≤ Some (v_minus_w_bound W m).
Proof.
  intros x him.
  unfold v_minus_w_bound.
  set (fm := LevelMapFact.filter _ _).
  replace (level_value m x) with (level_value fm x).
  2:{ unfold level_value.
      destruct LevelMap.find eqn:hl => //.
      eapply LevelMap.find_2 in hl.
      subst fm. cbn in hl.
      eapply LevelMapFact.filter_iff in hl as []. 2:tc.
      rewrite (LevelMap.find_1 H) //.
      destruct (LevelMap.find _ m) eqn:hl' => //.
      eapply LevelMap.find_2 in hl'.
      assert (LevelMap.MapsTo x o fm).
      eapply LevelMapFact.filter_iff. tc.
      split => //. now rewrite [_ = true]not_mem.
      now rewrite (LevelMap.find_1 H)  in hl. }
  clearbody fm.
  eapply LevelMapFact.fold_rec.
  - intros m' em. unfold level_value.
    destruct LevelMap.find eqn:hl => //.
    eapply LevelMap.find_2 in hl.
    now apply em in hl. constructor.
  - intros k e a m' m'' map nin hadd.
    red in hadd.
    unfold level_value. cbn.
    rewrite hadd LevelMapFact.F.add_o.
    destruct LevelMap.OT.eq_dec. do 2 red in e0. subst x.
    destruct LevelMap.find eqn:heq.
    apply LevelMap.find_2 in heq. elim nin. now exists o.
    intros _. destruct e; constructor; cbn. lia.
    destruct LevelMap.find => hf; depelim hf; constructor; lia.
Qed.

Definition levelset_m_eq : list Level.t × model -> list Level.t × model -> Prop :=
  fun x y => x.1 = y.1 /\ LevelMap.Equal x.2 y.2.

#[local] Instance lmeq_eq : Equivalence levelset_m_eq.
Proof.
  split. intros x. split => //.
  intros x y []; split => //.
  intros x y z [] []; split => //.
  all:etransitivity; tea.
Qed.

Definition level_value_default m l :=
  match level_value m l with Some x => x | None => 0 end%Z.

Definition measure_w W cls m w :=
  let bound := v_minus_w_bound W m in
  let maxgain := max_gain (cls_diff cls W) in
  (bound + Z.of_nat maxgain - (level_value_default m w))%Z.

Lemma invalid_clause_measure W cls cl m :
  defined_model_of W m ->
  ~~ valid_clause m cl ->
  Clauses.In cl (cls_diff cls W) ->
  (0 < measure_w W cls m (concl cl))%Z.
Proof.
  intros hwv. unfold valid_clause.
  destruct cl as [prem [l k]]; cbn.
  destruct min_premise eqn:hmin => //.
  move/negbTE/level_value_not_above_spec => hlt hin.
  have hne := (non_W_atoms_ne _ _ _ hin).
  cbn. unfold measure_w. unfold gain.
  set (clsdiff := Clauses.diff _ _).
  set (bound := v_minus_w_bound W m).
  enough ((level_value_default m l) < bound + Z.of_nat (max_gain clsdiff))%Z. lia.
  set (prem' := non_W_atoms W prem).
  set (preml := {| t_set := prem'; t_ne := hne |}).
  assert (Z.to_nat (gain (preml, (l, k))) <= max_gain clsdiff)%nat.
  { transitivity (Z.to_nat (gain (prem, (l, k)))). 2:now apply max_gain_in.
    unfold gain. cbn.
    pose proof (premise_min_subset preml prem).
    forward H. eapply non_W_atoms_subset. lia. }
  eapply Z.lt_le_trans with (bound + Z.of_nat (Z.to_nat (gain (preml, (l, k)))))%Z; try lia.
  unfold gain; cbn.
  enough ((level_value_default m l) < (v_minus_w_bound W m) + (k - premise_min preml))%Z. lia.
  unfold level_value_default. destruct (level_value m l) as [vl|] eqn:hl; revgoals.
  { eapply defined_model_of_value_None in hl; tea => //.
    eapply Clauses.diff_spec in hin as [hin _].
    now apply in_clauses_with_concl in hin as [hin _]. }
  depelim hlt.
  enough (k + z <= (v_minus_w_bound W m) + k - premise_min preml)%Z. lia.
  assert (min_premise m prem ≤ min_premise m preml)%Z.
  { eapply min_premise_subset. eapply non_W_atoms_subset. }
  rewrite hmin in H1. depelim H1.
  transitivity (k + y)%Z. lia.
  pose proof (min_premise_spec m preml) as [amin [exmin [inminpre eqminpre]]].
  have [maxpreml eqmax] := min_premise_max_premise m preml _ H2.
  pose proof (max_premise_value_spec m preml _ eqmax) as [amax [exmax [inmaxpre eqmaxpre]]].
  pose proof (premise_min_spec preml) as [apmin [expmin [inpminpre eqpminpre]]].
  assert (premise_min prem <= premise_min preml).
  { eapply premise_min_subset. eapply non_W_atoms_subset. }
  assert (y <= maxpreml - (premise_min preml))%Z.
  { rewrite eqpminpre. rewrite H2 in eqminpre; symmetry in eqminpre.
    pose proof (min_atom_value_levelexpr_value m exmin).
    specialize (amax _ inminpre) as amax'. rewrite eqmaxpre in amax'.
    destruct amax' as [vexmin [eqexmin ltexmin]].
    assert (expmin.2 <= exmin.2). specialize (apmin _ inminpre). lia.
    specialize (H4 _ _ eqminpre eqexmin). depelim ltexmin. etransitivity; tea.
    rewrite -eqmaxpre in H6. noconf H6.
    lia. }
  transitivity (k + (maxpreml - (premise_min preml)))%Z. lia.
  assert (k + (maxpreml - (premise_min preml)) =
    (maxpreml + k - (premise_min preml)))%Z as ->. lia.
  enough (maxpreml <= (v_minus_w_bound W m))%Z. lia.
  { have vm := v_minus_w_bound_spec W m exmax. unfold levelexpr_value in eqmaxpre.
    rewrite -eqmaxpre in vm.
    have [hlevels _] := (@levels_exprs_non_W_atoms W prem (level exmax)).
    rewrite levelexprset_levels_spec in hlevels.
    forward hlevels.
    exists exmax.2. now destruct exmax.
    rewrite LevelSet.diff_spec in hlevels.
    destruct hlevels as [_ nw]. specialize (vm nw). depelim vm. lia. }
Qed.

Record valid_model_def (V W : LevelSet.t) (m : model) (cls : clauses) :=
  { model_model : model;
    model_of_V :> model_of V model_model;
    model_updates : is_update_of cls W m model_model;
    model_clauses_conclusions : clauses_conclusions cls ⊂_lset V;
    model_ok :> is_model cls model_model;
 }.
Arguments model_model {V W m cls}.
Arguments model_of_V {V W m cls}.
Arguments model_updates {V W m cls}.
Arguments model_clauses_conclusions {V W m cls}.
Arguments model_ok {V W m cls}.
Extraction Inline model_model.

Definition valid_model := valid_model_def.

Definition loop_on_univ cls u := cls ⊢a u → succ_prems u.

Lemma loop_on_subset {cls cls' u} : Clauses.Subset cls cls' -> loop_on_univ cls u -> loop_on_univ cls' u.
Proof.
  intros sub; rewrite /loop_on_univ => hyp.
  now eapply entails_all_clauses_subset.
Qed.

Inductive result (V U : LevelSet.t) (cls : clauses) (m : model) :=
  | Loop (v : premises) (islooping : loop_on_univ cls v)
  | Model (w : LevelSet.t) (m : valid_model V w m cls) (prf : U ⊂_lset w).
Arguments Loop {V U cls m}.
Arguments Model {V U cls m}.
Arguments lexprod {A B}.

Definition option_of_result {V U m cls} (r : result V U m cls) : option model :=
  match r with
  | Model w m _ => Some m.(model_model)
  | Loop v _ => None
  end.

Notation loop_measure V W := (#|V|, #|V| - #|W|)%nat.

Definition lexprod_rel := lexprod lt lt.

#[local] Instance lexprod_rel_wf : WellFounded lexprod_rel.
Proof.
  eapply (Acc_intro_generator 1000). unfold lexprod_rel. eapply wf_lexprod, lt_wf. eapply lt_wf.
Defined.

Lemma model_incl {V W m cls} : valid_model V W m cls -> W ⊂_lset V.
Proof.
  intros vm; have upd := model_updates vm.
  move/is_update_of_case: upd => [].
  - intros [ne eq]. lsets.
  - move/strictly_updates_incl. have hv := model_clauses_conclusions vm. lsets.
Qed.

Lemma valid_model_total W W' m cls :
  forall vm : valid_model W W' m cls, model_of W m -> model_of W (model_model vm).
Proof.
  intros []; cbn => htot.
  move/is_update_of_case: model_updates0 => [].
  - intros [ne eq] => //.
  - intros su. eapply strictly_updates_ext in su.
    eapply model_of_ext; tea.
Qed.

Section InnerLoop.
  Definition sum_W W (f : LevelSet.elt -> nat) : nat :=
    LevelSet.fold (fun w acc => acc + f w)%nat W 0%nat.

  Definition measure (W : LevelSet.t) (cls : clauses) (m : model) : nat :=
    sum_W W (fun w => Z.to_nat (measure_w W cls m w)).

  Lemma measure_model W cls m :
    defined_model_of W m ->
    let clsdiff := cls_diff cls W in
    measure W cls m = 0%nat -> is_model clsdiff m.
  Proof using.
    unfold measure, sum_W, measure_w, is_model.
    set (clsdiff := Clauses.diff _ _).
    intros hv hm.
    assert (LevelSet.For_all (fun w => Some (v_minus_w_bound W m + Z.of_nat (max_gain clsdiff)) ≤ level_value m w) W).
    { move: hm.
      generalize (v_minus_w_bound W m) => vbound.
      eapply LevelSetProp.fold_rec.
      intros. intros x hin. firstorder eauto.
      intros x a s' s'' inw nins' hadd ih heq.
      forward ih by lia.
      intros l hin.
      specialize (hv _ inw) as [k lv]. rewrite /level_value_default (level_value_MapsTo lv) in heq.
      apply hadd in hin as [].
      * subst x. rewrite (level_value_MapsTo lv).
        constructor. lia.
      * now apply ih. }
    clear hm.
    eapply ClausesFact.for_all_iff. tc.
    intros cl hl.
    unfold valid_clause.
    destruct min_premise as [k0|] eqn:hk0 => //.
    destruct cl as [prem [l k]] => /=. cbn in hk0.
    rewrite /clsdiff in hl.
    destruct (proj1 (Clauses.diff_spec _ _ _) hl) as [hlcls hl'].
    eapply in_clauses_with_concl in hlcls as [lW incls].
    specialize (H _ lW). cbn -[clsdiff] in H. cbn in lW.
    specialize (hv _ lW) as [vl hvl]. rewrite /level_value_above (level_value_MapsTo hvl).
    rewrite (level_value_MapsTo hvl) in H; depelim H.
    (* etransitivity; tea. *)
    set (prem' := non_W_atoms W prem).
    assert (ne : LevelExprSet.is_empty prem' = false).
    { now eapply (non_W_atoms_ne W (prem, (l, k)) cls). }
    set (preml := {| t_set := prem'; t_ne := ne |}).
    assert (min_premise m prem ≤ min_premise m preml).
    { eapply min_premise_subset. eapply non_W_atoms_subset. }
    (* min_i (f(x_i)-k_i) <= max_i(f(x_i)) - min(k_i) *)
    pose proof (min_premise_spec m preml) as [amin [exmin [inminpre eqminpre]]].
    rewrite hk0 in H0. depelim H0. rename y into minpreml.
    pose proof (min_premise_max_premise _ _ _ H1) as [maxpreml eqmaxp].
    pose proof (max_premise_value_spec m preml _ eqmaxp) as [amax [exmax [inmaxpre eqmaxpre]]].
    rewrite -eqmaxp in eqmaxpre.
    pose proof (premise_min_spec preml) as [apmin [expmin [inpminpre eqpminpre]]].
    assert (min_premise m preml ≤ Some (maxpreml - premise_min preml))%Z.
    { rewrite eqminpre in H1.
      specialize (amax _ inminpre). destruct amax as [k' [lk' hk']].
      depelim hk'.
      pose proof (min_atom_value_levelexpr_value m exmin _ _ H2 lk').
      rewrite eqminpre H2. constructor. etransitivity; tea.
      rewrite eqmaxpre in eqmaxp.
      assert (expmin.2 <= exmin.2). specialize (apmin _ inminpre). lia.
      lia. }
    apply Z.leb_le. rewrite H1 in H2. depelim H2.
    transitivity (k + (maxpreml - premise_min preml)). lia.
    assert (Z.to_nat (gain (preml, (l, k))) <= max_gain clsdiff)%nat.
    { transitivity (Z.to_nat (gain (prem, (l, k)))). 2:now apply max_gain_in.
      unfold gain. cbn.
      pose proof (premise_min_subset preml prem).
      enough (premise_min prem <= premise_min preml) by lia.
      forward H3. eapply non_W_atoms_subset. lia. }
    transitivity (v_minus_w_bound W m + (gain (preml, (l, k)))).
    2:lia.
    unfold gain. cbn -[max_premise_value premise_min].
    assert (k + (maxpreml - premise_min preml) =
      (maxpreml + k - premise_min preml)) as ->. lia.
    assert (maxpreml <= v_minus_w_bound W m).
    { pose proof (v_minus_w_bound_spec W m exmax).
      have [hlevels _] := (@levels_exprs_non_W_atoms W prem (level exmax)).
      rewrite levelexprset_levels_spec in hlevels.
      forward hlevels.
      exists exmax.2. now destruct exmax.
      rewrite LevelSet.diff_spec in hlevels.
      destruct hlevels.
      forward H4 by auto.
      rewrite eqmaxp in eqmaxpre. unfold levelexpr_value in eqmaxpre. rewrite -eqmaxpre in H4.
      now depelim H4.
      }
    lia.
  Qed.

  Lemma level_value_default_def {m x v} : level_value m x = Some v -> level_value_default m x = v.
  Proof. unfold level_value_default. now intros ->. Qed.

  Lemma level_values_in_W m m' W x :
    defined_model_of W m ->
    m ⩽ m' ->
    LevelSet.In x W -> level_value m x ≤ level_value m' x ->
    exists k k', level_value m x = Some k /\ level_value m' x = Some k' /\ (k <= k').
  Proof.
    intros hwv ext hin hleq.
    specialize (hwv _ hin) as x'. destruct x' as [k hl]. rewrite (level_value_MapsTo hl) in hleq.
    eapply defined_model_of_ext in ext; tea.
    specialize (ext _ hin) as [k' hl'].
    rewrite (level_value_MapsTo hl') in hleq. depelim hleq.
    do 2 eexists. intuition eauto.
    now rewrite (level_value_MapsTo hl).
    now rewrite (level_value_MapsTo hl').
  Qed.

  Lemma measure_le {W cls m m'} :
    defined_model_of W m ->
    model_map_outside W m m' ->
    m ⩽ m' ->
    (measure W cls m' <= measure W cls m)%nat.
  Proof.
    intros hwv hout hle.
    unfold measure, measure_w, sum_W.
    rewrite (v_minus_w_bound_irrel _ _ hout).
    rewrite !LevelSet.fold_spec. unfold flip.
    eapply fold_left_le; unfold flip. 2:lia.
    - intros. rewrite LevelSet_In_elements in H.
      have lexx' := (model_le_values x hle).
      eapply level_values_in_W in lexx' as [k [k' [hk [hk' leq]]]]; tea.
      erewrite !level_value_default_def; tea. lia.
  Qed.

  Lemma measure_lt {W cls m m'} :
    defined_model_of W m ->
    model_map_outside W m m' ->
    m ⩽ m' ->
    (exists l, [/\ LevelSet.In l W, (0 < measure_w W cls m l)%Z &
     opt_le Z.lt (level_value m l) (level_value m' l)])%Z ->
    (measure W cls m' < measure W cls m)%nat.
  Proof.
    intros hwv hout hle.
    unfold measure, measure_w, sum_W.
    rewrite (v_minus_w_bound_irrel _ _ hout).
    intros hlt.
    rewrite !LevelSet.fold_spec. unfold flip.
    eapply fold_left_ne_lt; unfold flip.
    - unfold flip. intros; lia.
    - unfold flip; intros; lia.
    - destruct hlt as [l [hin _]]. intros he. rewrite -LevelSetProp.elements_Empty in he. lsets.
    - intros. rewrite LevelSet_In_elements in H.
      have lexx' := (model_le_values x hle).
      eapply level_values_in_W in lexx' as [k [k' [hk [hk' leq]]]]; tea.
      erewrite !level_value_default_def; tea. lia.
    - intros. rewrite LevelSet_In_elements in H.
      have lexx' := (model_le_values x hle).
      eapply level_values_in_W in lexx' as [k [k' [hk [hk' leq]]]]; tea.
      erewrite !level_value_default_def; tea. lia.
    - destruct hlt as [l [hinl hbound hlev]].
      exists l. rewrite LevelSet_In_elements. split => //.
      intros acc acc' accle.
      eapply Nat.add_le_lt_mono => //.
      depelim hlev. rewrite /level_value_default ?H0 ?H1 in hbound |- *.
      lia. now eapply defined_model_of_value_None in H; tea.
  Qed.

  Lemma check_model_spec_diff {cls w m w' m' w''} :
    model_of w m ->
    model_of w'' m ->
    let cls := (cls_diff cls w) in
    check_model cls (w'', m) = Some (w', m') ->
    [/\ w'' ⊂_lset w', w' ⊂_lset (w'' ∪ w),
      exists cl : clause,
        let cll := level (concl cl) in
        [/\ Clauses.In cl cls, ~~ valid_clause m cl, LevelSet.In cll w'
          & (opt_le Z.lt (level_value m cll) (level_value m' cll))%Z]
      & model_extension w' m m'].
  Proof.
    cbn; intros mof tot cm.
    pose proof (clauses_conclusions_diff_left cls w (cls ⇂ w)).
    apply check_model_has_invariants in cm as [].
    split => //. lsets.
    eapply model_of_subset. exact mof. tea. exact tot.
  Qed.

  Lemma valid_model_only_model W W' m cls :
    forall vm : valid_model W W' m cls,
    only_model_of W m -> only_model_of W (model_model vm).
  Proof.
    intros vm.
    have incl := model_incl vm.
    destruct vm as [m' mof isupd clsincl ism]. cbn.
    move: isupd; rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:heq. now intros ->.
    intros su om.
    eapply strictly_updates_only_model_gen in su; tea.
    eapply only_model_of_eq; tea. intro. lsets.
  Qed.

  Lemma valid_model_is_update_of W W' m cls :
    model_of W m ->
    forall vm : valid_model W W' (restrict_model W m) (cls ⇂ W),
    is_update_of (cls ⇂ W) W' m (model_update m (model_model vm)).
  Proof.
    intros mofW vm.
    have incl := model_incl vm.
    destruct vm as [m' mof isupd clsincl ism]. cbn.
    move: isupd. rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:he.
    - intros <-. now rewrite model_update_restrict.
    - intros su. eapply strictly_updates_restrict_model in su; tea.
  Qed.

  Lemma valid_model_is_update_of_eq W W' m cls cls' :
    model_of W m ->
    forall vm : valid_model W W' (restrict_model W m) cls,
    cls =_clset (cls' ⇂ W) ->
    is_update_of cls W' m (model_update m (model_model vm)).
  Proof.
    intros mofW vm.
    have incl := model_incl vm.
    destruct vm as [m' mof isupd clsincl ism]. cbn.
    move: isupd. rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:he.
    - intros <-. now rewrite model_update_restrict.
    - intros su eq. rewrite eq in su. eapply strictly_updates_restrict_model in su; tea.
      now rewrite eq.
  Qed.

  Context (V : LevelSet.t) (U : LevelSet.t) (init_model : model)
    (loop : forall (V' U' : LevelSet.t) (cls' : clauses) (minit m : model)
    (prf : [/\ clauses_levels cls' ⊂_lset V', only_model_of V' minit &
      is_update_of cls' U' minit m]),
    lexprod_rel (loop_measure V' U') (loop_measure V U) -> result V' U' cls' minit).

  Section innerloop_partition.
    Context (W : LevelSet.t) (cls : clauses).
    Context (premconclW conclW : clauses).
    Context (prf : [/\ strict_subset W V, ~ LevelSet.Empty W, U ⊂_lset W, clauses_conclusions cls ⊂_lset W,
      Clauses.Equal premconclW (cls ⇂ W) & Clauses.Equal conclW (Clauses.diff (cls ↓ W) (cls ⇂ W))]).

    #[tactic="idtac"]
    Equations? inner_loop_partition (m : model) (upd : strictly_updates cls W init_model m) :
      result W LevelSet.empty cls m
      by wf (measure W cls m) lt :=
      inner_loop_partition m upd with loop W LevelSet.empty premconclW (restrict_model W m) (restrict_model W m) _ _ := {
        (* premconclW = cls ⇂ W , conclW = (Clauses.diff (cls ↓ W) (cls ⇂ W)) *)
        | Loop u isl => Loop u (loop_on_subset _ isl)
        (* We have a model for (cls ⇂ W), we try to extend it to a model of (csl ↓ W).
          By invariant Wr ⊂ W *)
        | Model Wr mr empWr with inspect (check_model conclW (Wr, model_update m (model_model mr))) := {
          | exist None eqm => Model Wr {| model_model := model_update m (model_model mr) |} _
          | exist (Some (Wconcl, mconcl)) eqm with inner_loop_partition mconcl _ := {
            (* Here Wr ⊂ Wconcl by invariant *)
              | Loop u isl => Loop u isl
              | Model Wr' mr' UWconcl => Model (LevelSet.union Wconcl Wr') {| model_model := model_model mr' |} _ }
              (* Here Wr' ⊂ W by invariant *)
        (* We check if the new model [mr] for (cls ⇂ W) extends to a model of (cls ↓ W). *)
        (* We're entitled to recursively compute a better model starting with mconcl,
          as we have made the measure decrease:
          some atom in W has been strictly updated in Wconcl. *)
            } }.
    Proof.
      all:try solve [try apply LevelSet.subset_spec; try reflexivity].
      all:cbn [model_model]; clear loop inner_loop_partition.
      all:try apply LevelSet.subset_spec in hsub.
      all:auto.
      all:try destruct prf as [WV neW UW clsW eqprem eqconcl].
      all:try solve [intuition auto].
      all:try rewrite eqconcl in eqm.
      - split => //.
        * rewrite eqprem. apply clauses_levels_restrict_clauses.
        * now eapply strictly_updates_restrict_only_model.
        * eapply is_update_of_empty.
      - left. now eapply strict_subset_cardinal.
      - rewrite eqprem. eapply restrict_clauses_subset.
      - have mu := model_updates mr.
        setoid_rewrite eqprem at 1 in mu.
        eapply strictly_updates_is_update_of_restrict in upd; tea.
        apply check_model_spec in eqm as [Wconcl' [sumr ->]].
        have tr := strictly_updates_trans upd sumr.
        eapply strictly_updates_clauses_W; tea.
        { intros ?. now rewrite ClausesProp.union_sym union_diff_cls. }
        { have incl := model_incl mr. apply strictly_updates_incl in sumr.
          have hdiff := clauses_conclusions_diff_left cls W (cls ⇂ W). lsets. }
      - have mW : model_of W m.
        { now eapply strictly_updates_model_of in upd. }
        have tmr : model_of W (model_model mr).
        { eapply valid_model_total. eapply strictly_updates_restrict_only_model in upd.
          intro. apply upd. }
        have tmr' : model_of W (model_update m (model_model mr)).
        { eapply update_total_model; tea. }
        eapply (check_model_spec_diff tmr') in eqm as [subwwconcl subwconcl hm hext] => //.
        pose proof (clauses_conclusions_diff_left cls W (cls ⇂ W)).
        destruct hm as [cll [hind nvalid inwconcl hl]].
        eapply Nat.lt_le_trans with (measure W cls (model_update m (model_model mr))).
        2:{ eapply measure_le; eauto; try eapply mr; tea.
            - eapply strictly_updates_defined_model; tea.
            - apply model_map_outside_update. eapply valid_model_only_model.
              now eapply strictly_updates_restrict_only_model.
            - eapply is_update_of_ext.
              have mof := strictly_updates_model_of upd.
              apply: valid_model_is_update_of_eq _ _ _ _ cls mof mr eqprem. }
        have isdef : defined_model_of W (model_update m (model_model mr)).
        {  eapply strictly_updates_defined_model in upd.
          eapply defined_model_of_restrict in upd.
          have hupd := model_updates mr.
          have hu := (defined_model_of_is_update_of upd hupd).
          apply defined_model_of_update; tea. }
        eapply measure_lt; tea.
        { eapply model_map_outside_weaken. eapply hext. have incl := model_incl mr. lsets. }
        { apply hext. }
        eapply invalid_clause_measure in nvalid; tea.
        exists (level (concl cll)).
        split => //.
        eapply clauses_conclusions_diff_left; tea.
        eapply clauses_conclusions_spec. exists cll; split => //. exact hind.
        have incl := model_incl mr. eapply model_of_subset; tea.
      - apply mr'.
      - have updm : is_update_of premconclW Wr m (model_update m (model_model mr)).
        { exact: valid_model_is_update_of_eq _ _ _ _ cls (strictly_updates_model_of upd) mr eqprem. }
        eapply check_model_is_update_of in eqm as [eqm incl]. 2:eapply updm.
        eapply strictly_updates_is_update_of in eqm. 2:eapply mr'.
        eapply is_update_of_strictly_updates in eqm.
        eapply is_update_of_weaken; tea.
        now rewrite eqprem (ClausesProp.union_sym (cls ⇂ W)) union_diff ClausesProp.union_sym union_with_concl.
      - apply mr'.
      - lsets.
      - have updm : is_update_of premconclW Wr m (model_update m (model_model mr)).
        { exact: valid_model_is_update_of_eq _ _ _ _ cls (strictly_updates_model_of upd) mr eqprem. }
        eapply update_total_model. now apply strictly_updates_model_of in upd.
      - have updm : is_update_of premconclW Wr m (model_update m (model_model mr)).
        { exact: valid_model_is_update_of_eq _ _ _ _ cls (strictly_updates_model_of upd) mr eqprem. }
        eapply is_update_of_weaken. 2:apply updm. rewrite eqprem. apply restrict_clauses_subset.
      - rewrite check_model_is_model in eqm.
        have okm := (model_ok mr).
        have okupdm : is_model premconclW (model_update m (model_model mr)).
        { setoid_rewrite eqprem at 1. apply is_model_update. apply strictly_updates_model_of in upd; tea.
           eapply valid_model_only_model. now eapply strictly_updates_restrict_only_model.
           now setoid_rewrite <- eqprem at 1. }
        have mu := is_model_union okupdm eqm.
        rewrite {1}eqprem in mu.
        rewrite union_diff_eq in mu.
        rewrite union_restrict_with_concl in mu.
        now rewrite (clauses_conclusions_eq _ _ clsW).
    Qed.
  End innerloop_partition.

  (* We first partition the clauses among those that mention only W and the ones that can mention other atoms.
     We then call the loop on these two sets of clauses, which not need to change during the recursive calls.
    *)
  #[tactic="idtac"]
  Equations? inner_loop (W : LevelSet.t) (cls : clauses) (m : model)
    (prf : [/\ strict_subset W V, ~ LevelSet.Empty W, U ⊂_lset W, clauses_conclusions cls ⊂_lset W &
      strictly_updates cls W init_model m]) : result W LevelSet.empty cls m :=
    inner_loop W cls m prf with inspect (Clauses.partition (premise_restricted_to W) cls) :=
      | exist (premconclW, conclW) eqp => inner_loop_partition W cls premconclW conclW _ m _.
  Proof.
    - destruct prf as [subWV neW UW clsW mW].
      eapply (clauses_partition_spec clsW) in eqp as [eqprem eqconcl].
      split => //. now rewrite -(clauses_conclusions_eq _ _ clsW).
    - apply prf.
  Qed.

End InnerLoop.

(* To help equations *)
Opaque lexprod_rel_wf.

Local Open Scope Z_scope.

#[tactic="idtac"]
Equations? loop (V : LevelSet.t) (U : LevelSet.t) (cls : clauses) (minit m : model)
  (prf : [/\ clauses_levels cls ⊂_lset V, only_model_of V minit & is_update_of cls U minit m]) : result V U cls minit
  by wf (loop_measure V U) lexprod_rel :=
  loop V U cls minit m prf with inspect (check_model cls (U, m)) :=
    | exist None eqm => Model U {| model_model := m |} _
    | exist (Some (W, m')) eqm with inspect (LevelSet.equal W V) := {
      | exist true eq := Loop (of_level_map minit (check_model_defined_init_map prf eqm)) _
      (* Loop on cls ↓ W, with |W| < |V| *)
      | exist false neq with inner_loop V U minit loop W (cls ↓ W) m' _ :=
        { | Loop u isloop := Loop u (loop_on_subset _ isloop)
          | Model Wc mwc _
          (* We get a model for (cls ↓ W), we check if it extends to all clauses.
              By invariant |Wc| cannot be larger than |W|. *)
            with inspect (check_model cls (Wc, mwc.(model_model))) :=
          { | exist None eqm' => Model (LevelSet.union W Wc) {| model_model := mwc.(model_model) |} _
            | exist (Some (Wcls, mcls)) eqm' with inspect (LevelSet.equal Wcls V) := {
              | exist true _ := Loop (of_level_map m' (check_model_defined_map eqm)) _
              | exist false neq' with loop V (LevelSet.union W Wcls) cls minit mcls _ := {
                (* Here Wcls < V, we've found a model for all of the clauses with conclusion
                  in W, which can now be fixed. We concentrate on the clauses whose
                  conclusion is different. Clearly |W| < |V|, but |Wcls| is not
                  necessarily < |V| *)
                  | Loop u isloop := Loop u isloop
                  | Model Wvw mcls' hsub := Model Wvw {| model_model := model_model mcls' |} _ } } }
          }
      }
    .
Proof.
  all:cbn -[cls_diff clauses_with_concl restrict_clauses]; clear loop.
  all:try solve [intuition auto].
  all:try eapply levelset_neq in neq.
  all:have cls_sub := clauses_conclusions_levels cls.
  all:destruct prf as [clsV mof isupd].
  - red. eapply LevelSet.equal_spec in eq.
    set (prf := check_model_defined_init_map _ _); clearbody prf.
    eapply check_model_is_update_of in eqm; tea. rewrite eq in eqm.
    destruct eqm as [eqm incl]. rewrite union_idem in eqm.
    unshelve eapply strictly_updates_entails_on_V in eqm; tea.
    eapply entails_all_clauses_subset; tea. apply clauses_with_concl_subset.
  - eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have hi := strictly_updates_incl eqm.
    rewrite union_idem in hi, eqm.
    split => //.
    * split => //. lsets.
    * now eapply strictly_updates_non_empty.
    * apply clauses_conclusions_clauses_with_concl.
    * eapply strictly_updates_strenghten. exact eqm.

  - now intros ?; rewrite in_clauses_with_concl.
  - set (ne := check_model_defined_map _). clearbody ne.
    have hu := model_updates mwc.
    eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have om : only_model_of V m'.
    { rewrite union_idem in eqm.
      have incl' := strictly_updates_incl eqm.
      have hcl := clauses_conclusions_levels cls.
      eapply strictly_updates_only_model_gen in eqm; tea. eapply only_model_of_eq; tea. intro; lsets. }
    eapply strictly_updates_is_update_of in eqm; tea.
    rewrite union_idem union_with_concl in eqm.
    eapply check_model_is_update_of in eqm' as [eqm' incl']; tea.
    rewrite ClausesProp.union_sym union_with_concl in eqm'.
    eapply (strictly_updates_entails_on_V _ _ _ ne) in eqm'. red.
    eapply entails_all_clauses_subset; tea.
    eapply clauses_with_concl_subset. apply LevelSet.equal_spec in e. rewrite e. exact om.
  - eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have hu := model_updates mwc.
    eapply strictly_updates_is_update_of in hu; tea.
    rewrite union_idem union_with_concl in hu.
    eapply check_model_update_of in eqm' as [wmcls [upd ->]].
    eapply is_update_of_strictly_updates in hu.
    have tr := is_update_of_trans_eq hu upd.
    split => //. apply tr. clsets. lsets.
  - right.
    eapply check_model_spec_V in eqm' as eqm''. 3:etransitivity; [apply clauses_conclusions_levels|exact clsV]. cbn in eqm''.
    2:{
      eapply check_model_is_update_of in eqm as [eqm incl]; tea. rewrite union_idem in eqm.
      eapply strictly_updates_is_update_of in eqm; tea. 2:apply mwc.
      eapply strictly_updates_model_of_gen in eqm; tea. 2:exact mof.
      eapply model_of_subset; tea. lsets. }
    2:{ eapply is_update_of_total_model. apply mwc. }
    destruct eqm'' as [Hwc Hwcls H1 mext tot].
    eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    rewrite union_idem in eqm.
    have hu := model_updates mwc.
    eapply check_model_is_update_of in eqm' as [eqm' incl']; tea.
    rewrite ClausesProp.union_sym union_with_concl in eqm'.
    have WcW := model_incl mwc.
    have w_incl := strictly_updates_incl eqm.
    have wcls_incl := strictly_updates_incl eqm'.
    assert (exists l, LevelSet.In l Wcls /\ ~ LevelSet.In l W).
    { destruct H1 as [cl [clcls nvalid hcll hv]].
      pose proof (model_ok mwc).
      eapply is_model_invalid_clause in H; tea.
      assert (~ LevelSet.In (level (concl cl)) W).
      { intros hin. rewrite in_clauses_with_concl in H. intuition auto. }
      exists (concl cl). split => //. }
    rewrite -!diff_cardinal //. clear -w_incl clsV incl wcls_incl. have hincl := clauses_conclusions_levels cls. lsets. lsets.
    assert (Wcls ⊂_lset V). lsets.
    eapply strict_subset_cardinal.
    eapply (strict_subset_leq_right _ (LevelSet.diff V W)). 2:lsets.
    apply strict_subset_diff_incl => //.
    { red. split => //. lsets. intros heq. destruct H as [l' [hin hnin]].
      rewrite heq in hnin. apply hnin. lsets. }
    lsets. lsets.
  - eapply mcls'.
  - apply mcls'.
  - apply mcls'.
  - apply mcls'.
  - eapply check_model_is_update_of in eqm as []; tea. lsets.
  - eapply check_model_is_update_of in eqm as [suinit incl]; tea. rewrite union_idem in suinit.
    have hupd := model_updates mwc.
    eapply (is_update_of_weaken (cls' := cls)) in hupd. 2:intros ? ; rewrite in_clauses_with_concl; clsets.
    eapply strictly_updates_is_update_of in suinit; tea. rewrite union_idem in suinit.
    eapply model_of_strictly_updates; tea. exact mof.
  - eapply check_model_is_update_of in eqm as [suinit incl]; tea. rewrite union_idem in suinit.
    have hupd := model_updates mwc.
    eapply (is_update_of_weaken (cls' := cls)) in hupd. 2:intros ? ; rewrite in_clauses_with_concl; clsets.
    eapply is_update_of_trans_eq. eapply is_update_of_strictly_updates. tea. tea. clsets. lsets.
  - eapply clauses_levels_conclusions; assumption.
  - now apply check_model_None in eqm'.
  - eapply check_model_is_update_of in eqm as [suinit incl]; tea. lsets.
  - move: isupd. rewrite /is_update_of.
    destruct LevelSet.is_empty.
    * intros <-. exact mof.
    * intros su.
      eapply model_of_strictly_updates; tea. exact mof.
  - exact isupd.
  - apply clauses_levels_conclusions. assumption.
  - now eapply check_model_None in eqm.
  - lsets.
Qed.

Transparent lexprod_rel_wf.

End LoopCheckingImpl.
