(* Distributed under the terms of the MIT license. *)
(**

  This module defines the main loop-checking algorithm on a partial model in 𝐙.
  This algorithm is based on two nested well-founded recursive functions with separate measures.

  The main arguments developed here concern the termination of the algorithms, defining
  the two measures and showing the termination lemmas. It relies on the theory developped in
  Model.v about the properties of the [check_model]. The functions are dependently-typed:
  we know by construction that they return either a loop or a valid model.
  This is necessary to avoid fuel, as the termination argument relies on semantic arguments
  on the shapes of the model and clauses involved.

  To allow for incremental update of models, the notion of valid model of a set of clauses [cls]
  returned by the algorithm is parameterized by an initial model [m].
  - The [V] parameter represents the levels in the model, defined or undefined.
  - The clauses must have conclusions in [V].
  - The valid model ([model_model]) returned by the algorithm always results from a
    (possibly empty) sequence of strict updates from the initial model.
  - It is provably a model of the clauses ([model_ok]).

  The algorithm works by first checking if the model [m] validates all clauses, or
  requires a sequence of updates to validate some of the clauses. We track the updated
  values in a set [U], initially [U ⊂ V].

  - If it is a model we return it.
  - Otherwise we have a set [W] with [U ⊂ W] of levels that required updates to validate some of the clauses.

    + If [W = V], then actually all levels required a strict update from [m] to [m']:
      as we have an entailment [cls ⊢ m → m'] and all atoms in [m'] are strictly greater than [m],
      we can turn it into an entailment [cls ⊢ of_level_map m → of_level_map m + 1], resulting in a loop.
      Note that [m] must have at least one defined element here, otherwise no strict update could have
      happened (all clauses would be vacuously true).
    + Otherwise, [#|W| < #|V|].
      We then launch the inner loop on the set of clauses [cls ↓ W] (i.e. clauses with conclusions in W only),
      which will call loop-checking again on the smaller set [W].
      This returns either a loop which we return directly or a model of [cls ↓ W].
      In case we have a model of [cls ↓ W], we check if the new model validates the rest of the clauses
      (i.e. [cls \ cls ↓ W]). As our [check_model] function can accumulate a sequence of updates,
      we actually relaunch it on the whole set of clauses to gather more potential updates.

      + Again, if we have a model we return it, and need to check again for a loop.
      + Otherwise some strict updates were necessary and the new working set [W'] is such that
        [#|W'| < #|V|].
        At least one of those updates must be on a level [l] not in W, so we are entitled to do
        a recursive call to loop checking, as the cardinal of the set [U ∪ {l}] increased strictly
        without equating [V], so [#|V| - #|U ∪ {l}] < #|V| - #|U|].

  The inner loop takes V, W, cls ↓ W and the current model [m].
  This model [m] is a defined model for all of W as their values were strictly updated.
  It then works as follows:
  - We start by partitionning the clauses (cls ↓ W) depending on the fact that all premises are in W or not.
    We get a set (cls ⇂ W) of clauses restricted to W and the rest.
    We launch the loop checking algorithm on the restricted clauses and the restriction of the
    model to W: this satisfies the preconditions of the main loop as all the levels in the clauses
    we give are in W and the model only gives potential values to levels in W.
    It returns either a loop that we return or a model [m'] of (cls ⇂ W).
    We then update the initial model [m] with [m'], returning to a model of all of V.
    By invariant, we have that [m'] is an extension of [m] on W and does not have values for l ∉ W,
    in which case we keep the values from [m].
    We now test if this new model [m ∪ m'] is a model of the rest of the clauses with conclusions in W.
    If it is we return it. Otherwise, a sequence of strict updates was necessary on some set W' ⊂ W.
    We are entitled to do a recursive call to the inner loop again. The justification here relies
    on the fact that the levels in W can only be strictly updated a finite number of times by the clauses
    in (cls ↓ W \ cls ⇂ W). Intuitively, this is because the levels in [V - W] stay unchanged during the
    inner loop as we focus on [cls ↓ W]. We can hence give a bound on the maximal values the
    levels in [W] can reach. The bound is the maximal value [max {v | l := v ∈ m, l ∉ W}] + the maximal
    gain of the clauses in (cls ↓ W \ cls ⇂ W), which corresponds to the maximal amount by which a
    conclusion (in W) can be increased by those clauses due to levels in V - W, seen as a natural number.
    For a given level l ∈ W, we define the measure of l to be: [bound - m[l]] (remember m[l]
    is necessarily defined). The measure of a level hence decreases strictly when the model
    gets a strict update of l. If a clause in (cls ↓ W \ cls ⇂ W) is invalid, then
    the measure of its conclusion is necessarily strictly positive.

    ** Gain

    The gain of a clause [prems -> concl + k] is defined as [Z.to_nat (k - min_premise prems)].
    For example, the gain of downward closure clauses like [l + 1 -> l] is [Z.to_nat (0 + -1) = 0]:
    they cannot incur an update.

    The gain of clauses that might lift the value of a level upward like
    [l + 1 -> l' + 2] is [Z.to_nat (2 - 1) = 1]: they can incur an update by 1.

    The gain of clauses with negative premises can also incur lifts, e.g:
    [gain(l - 1 -> k) = Z.to_nat (0 - (-1)) = 1]: they also incur an update by 1.

    Crucially, the gain of clauses is invariant by shifting upwards *or downwards*, i.e.
    gain (l + k -> l' + k') = gain (l + k + z -> l' + k' + z) (k, k', z ∈ Ƶ)

    If the bounds were ever reached for all levels in l, then the clauses would be valid,
    contradicting the fact that [m ∪ m'] is not a model of (cls ↓ W \ cls ⇂ W)
    (see lemma [measure_model], which is actually not necessary for the proof).

    The reasonning for invalid clauses to force a positive measure for their conclusion is
    subtle. It goes as follows: if the clause [prems = premsW, premsNW -> concl + k] (concl, premwW ∈ W, premsnW ∉ W) is invalid,
    then its minimal premise min { m[l] - k) | (l, k) ∈ prems} must be equal to [Some z] and we must have that the
    conclusion does not hold, so m[concl] < k + z (i). By definition of the maximal gain,
    gain(premsNW -> concl + k) <= max_gain. Note that we focus on the premises not mentionning W here.
    We can strenthen the inequality we need to show to:

    m[concl] < max { m[l] | l ∈ V / W } + (k - premise_min premsNW) (in 𝐙)

    by transitivity with (i) it suffices to show:
    k + z <= max { m[l] | l ∈ V / W } + (k - premise_min premsNW)

    by cancellation we get to

    min {m[l] - k | (l, k) ∈ prems} <= max { m[l] | l ∈ V / W } - premise_min premsNW

    we can again strengthen to consider only premises not mentioning W.

    min {m[l] - k | (l, k) ∈ premsNW} <= max { m[l] | l ∈ V / W } - premise_min premsNW

    which is equivalent to

    min {m[l] - k | (l, k) ∈ premsNW} <= max { m[l] | l ∈ V / W } - min {k | (l, k) ∈ premsNW}

    We have the lemma that:

    min {m[l] - k | (l, k) ∈ premsNW} <= max {m[l] | (l, k) ∈ premsNW} - min {k | (l, k) ∈ premsNW}

    I.e. instead of looking at the minimal premise value, we take the maximum of the levels minus
    the minimum of the increments. To see why this holds:
    Assume (minl, mink) is such that min {m[l] - k | (l, k) ∈ premsNW} = m[minl] - mink.
    We have both min {k | (l, k) ∈ premsNW} <= mink and m[minl] <= max {m[l] | (l, k) ∈ premsNW},
    so the inequality holds.

    We can hence strengthen again by looking at the maximal value of a level in the premises:

    max {m[l] | (l, k) ∈ premsNW} - min {k | (l, k) ∈ premsNW} <= max { m[l] | l ∈ V / W } - min {k | (l, k) ∈ premsNW}

    This simplifies now to

    max {m[l] | (l, k) ∈ premsNW} <= max { m[l] | l ∈ V / W }

    As the (l, k) range over atoms not mentionniong W, this is provable.

    Coming back to the inner_loop measure: the measure is defined by taking the sum of the bounds
    of all levels in W. So at the recursive call, it suffices to show that for at least
    one level in W, this sum strictly decreased. This is the case because we found an invalid
    clause in (cls ↓ W \ cls ⇂ W) that required an update, and hence for its conclusion, the
    term in the sum decreased, the other terms just need to be shown to decrease largely, which
    easily follows from the fact that the new model [m ∪ m'] is an extension of the previous one hence
    has greater or equal values.

    This completes the termination proofs.

*)

From Stdlib Require Import ssreflect ssrfun ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From Equations Require Import Equations.

From MetaRocq.Common.LoopChecking Require Import Common Interfaces HornClauses Model Models.

Set Equations Transparent.

Module LoopCheckingImpl (LS : LevelSets).
(* This module is actually independent of the Models, it only needs the
  lemmas in Model.v, but we do this to share the LevelSets representation. *)
Module Export Model := Models(LS).

Local Open Scope Z_scope.

Record valid_model_def (V W : LevelSet.t) (m : model) (cls : clauses) :=
  { model_model : model;
    model_of_V :> model_of V model_model;
    model_updates : is_update_of cls W m model_model;
    model_clauses_conclusions : clauses_conclusions cls ⊂_lset V;
    model_ok :> is_model model_model cls;
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

Definition declared_clause_levels V cl := LevelSet.Subset (clause_levels cl) V.

Lemma declared_clause_levels_mon {V V' cl} : LevelSet.Subset V V' -> declared_clause_levels V cl -> declared_clause_levels V' cl.
Proof.
  now move => sub h l /h.
Qed.

Definition invalid_clauses m cls := Clauses.For_all (fun cl => valid_clause m cl = false) cls.

Record LoopClauses {cls loop_cls m loop} := mkLoopClauses
  { loop_cls_incl : loop_cls ⊂_clset cls;
    loop_nmodel : ~ exists cl, Clauses.In cl loop_cls /\ valid_clause m cl;
    incl_loop : levels loop ⊂_lset clauses_levels loop_cls }.
Arguments LoopClauses : clear implicits.

Inductive result (V U : LevelSet.t) (cls : clauses) (m : model) :=
  | Loop (v : premises) (hincl : LevelSet.Subset (levels v) (clauses_levels cls)) (islooping : loop_on_univ cls v)
  | Model (w : LevelSet.t) (m : valid_model V w m cls) (prf : U ⊂_lset w).
Arguments Loop {V U cls m}.
Arguments Model {V U cls m}.
Arguments lexprod {A B}.

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
  (0 < measure_w W cls m (concl cl).1)%Z.
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
    have := premise_min_subset preml prem => /fwd.
    { eapply non_W_atoms_subset. }
    lia. }
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
    move: (min_atom_value_levelexpr_value m exmin). rewrite /levelexpr_value.
    specialize (amax _ inminpre) as amax'. rewrite eqmaxpre in amax'.
    destruct amax' as [vexmin [eqexmin ltexmin]].
    have hle : expmin.2 <= exmin.2 by move: (apmin _ inminpre); lia.
    move/(_ _ _ eqminpre eqexmin) => ->. depelim ltexmin.
    rewrite -eqmaxpre in H5. noconf H5.
    lia. }
  transitivity (k + (maxpreml - (premise_min preml)))%Z. lia.
  assert (k + (maxpreml - (premise_min preml)) =
    (maxpreml + k - (premise_min preml)))%Z as ->. lia.
  enough (maxpreml <= (v_minus_w_bound W m))%Z. lia.
  { have vm := v_minus_w_bound_spec W m exmax.1. unfold levelexpr_value in eqmaxpre.
    rewrite -eqmaxpre in vm.
    have := (@levels_exprs_non_W_atoms W prem (level exmax)).
    rewrite leset_levels_spec => -[] /fwd.
    { exists exmax.2. now destruct exmax. }
    rewrite LevelSet.diff_spec => [] [_ nw] _.
    specialize (vm nw). depelim vm. lia. }
Qed.

Definition option_of_result {V U m cls} (r : result V U m cls) : option model :=
  match r with
  | Model w m _ => Some m.(model_model)
  | Loop v _ _ => None
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

Definition sum_W W (f : LevelSet.elt -> nat) : nat :=
  LevelSet.fold (fun w acc => acc + f w)%nat W 0%nat.

Lemma sum_W_0 {W f} l : sum_W W f = 0%nat -> LevelSet.In l W -> f l = 0%nat.
Proof.
  rewrite /sum_W.
  eapply LevelSetProp.fold_rec.
  - intros x hin. firstorder eauto.
  - move=> x a s' s'' inw nins' hadd + afx.
    move/fwd; [lia|] => ih /hadd[] eq. now move: afx; rewrite eq.
    now apply ih.
Qed.

Definition measure (W : LevelSet.t) (cls : clauses) (m : model) : nat :=
  sum_W W (fun w => Z.to_nat (measure_w W cls m w)).

Lemma measure_model W cls m :
  defined_model_of W m ->
  let clsdiff := cls_diff cls W in
  measure W cls m = 0%nat -> is_model m clsdiff.
Proof using.
  intros dnf clsdiff hm.
  apply Clauses.for_all_spec. tc.
  intros cl hcl.
  destruct (valid_clause) eqn:vc => //.
  eapply invalid_clause_measure in dnf; tea.
  2:{ rewrite vc //. }
  enough (measure_w W cls m (concl cl).1 = 0). lia.
  rewrite /measure in hm.
  move/(sum_W_0 (concl cl).1): hm => /fwd; [|lia].
  apply Clauses.diff_spec in hcl as [clw clr].
  now eapply in_clauses_with_concl in clw as [clw incls].
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


Instance incl_preorder : PartialOrder LevelSet.Equal LevelSet.Subset.
Proof.
  red. intros x y. split.
  - unfold relation_conjunction; cbn. intros ->. split; auto. reflexivity.
    red. reflexivity.
  - cbn; unfold flip. lsets.
Qed.

Instance rew_sub : RewriteRelation LevelSet.Subset := {}.


Instance incl_cls_preorder : PartialOrder Clauses.Equal Clauses.Subset.
Proof.
  red. intros x y. split.
  - unfold relation_conjunction; cbn. intros ->. split; auto. reflexivity.
    red. reflexivity.
  - cbn; unfold flip. clsets.
Qed.

Instance rew_cls_sub : RewriteRelation Clauses.Subset := {}.

Lemma is_modelP {m cls} : is_model m cls <-> Clauses.For_all (valid_clause m) cls.
Proof.
  rewrite /is_model.
  now rewrite [is_true _]Clauses.for_all_spec.
Qed.

Lemma Some_leq x y : (Some x ≤ y)%opt -> exists y', y = Some y' /\ (x <= y')%Z.
Proof.
  intros h; depelim h. now eexists.
Qed.

Lemma is_model_subset {m cls cls'} : cls ⊂_clset cls' -> is_model m cls' -> is_model m cls.
Proof.
  move=> incl /is_modelP cl; now apply/is_modelP=> cl' /incl /cl.
Qed.

Lemma is_model_restrict {cls W m} : is_model m cls -> is_model (restrict_model W m) (cls ↓ W).
Proof.
  move/is_modelP => ha. apply is_modelP => cl.
  move/in_clauses_with_concl => -[] conclW /ha.
  destruct cl as [prems [concl k]].
  move/valid_clause_elim => hz. apply valid_clause_intro => z hmin.
  move/min_premise_restrict: hmin => /hz.
  intros hs. cbn in conclW.
  move: (@level_valueP m concl) hs; case. 2:{ intros hnin hleq; depelim hleq. }
  move=> k' hm /Some_leq => -[vconcl [heq hle]]. subst k'.
  have [_] := restrict_model_spec W m concl (Some vconcl) => /fwd.
  split => //.
  move/level_value_MapsTo => ->. now constructor.
Qed.

Lemma restrict_with_concl_subset {cls W} : cls ⇂ W ⊂_clset (cls ↓ W).
Proof.
  move=> cl /in_restrict_clauses => -[conclW premsW hin].
  rewrite in_clauses_with_concl. split => //.
Qed.

Lemma is_model_restrict_only_w {cls W m} : is_model m cls -> is_model (restrict_model W m) (cls ⇂ W).
Proof.
  move/(is_model_restrict (W:=W)).
  intros he.
  eapply is_model_subset; tea.
  apply restrict_with_concl_subset.
Qed.

(* Lemma not_model_valid {m cls cl} : ~~ is_model m cls -> valid_clause m cl -> Clauses.In cl cls  *)
Lemma invalid_clauses_restrict {cls cls' W m} : cls ⊂_clset (cls' ⇂ W) ->
  invalid_clauses (restrict_model W m) cls ->
  invalid_clauses m cls.
Proof.
  move=> hincl ha cl /[dup] hin /ha.
  destruct cl as [prems [concl k]].
  rewrite /valid_clause. cbn.
  destruct min_premise eqn:hmin => //.
  move/min_premise_restrict: hmin => ->.

Admitted.

Lemma is_model_restrict_valid_noop {cls cls' W m} : cls ⊂_clset (cls' ⇂ W) ->
  forall cl, Clauses.In cl cls -> valid_clause m cl -> valid_clause (restrict_model W m) cl.
Proof.
  move=> hincl cl hin.
  destruct cl as [prems [concl k]].
  move/valid_clause_elim => hz. apply valid_clause_intro => z hmin.
  move/min_premise_restrict: hmin => /hz.
  intros hs.
  move: (@level_valueP m concl) hs; case. 2:{ intros hnin hleq; depelim hleq. }
  move=> k' hm /Some_leq => -[vconcl [heq hle]]. subst k'.
  have [_] := restrict_model_spec W m concl (Some vconcl) => /fwd.
  split => //. eapply hincl in hin.
  move/in_restrict_clauses: hin => -[] //=.
  move/level_value_MapsTo => ->. now constructor.
Qed.

Lemma is_model_restrict_noop {cls cls' W m} : cls ⊂_clset (cls' ⇂ W) -> is_model m cls -> is_model (restrict_model W m) cls.
Proof.
  move=> hincl.
  move/is_modelP => ha. apply is_modelP => cl /[dup] hin /ha.
  intros; now eapply is_model_restrict_valid_noop.
Qed.

Lemma strictly_updates_not_model {cls W m m'} : strictly_updates cls W m m' -> ~ is_model m cls.
Proof.
  intros su hn.
  eapply strictly_updates_invalid in su => //.
  move/negbTE: su. congruence.
Qed.

Section InnerLoop.

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
        | Loop u incl isl => Loop u _ (loop_on_subset _ isl)
        (* We have a model for (cls ⇂ W), we try to extend it to a model of (csl ↓ W).
          By invariant Wr ⊂ W *)
        | Model Wr mr empWr with inspect (check_model conclW (Wr, model_update m (model_model mr))) := {
          | exist None eqm => Model Wr {| model_model := model_update m (model_model mr) |} _
          | exist (Some (Wconcl, mconcl)) eqm with inner_loop_partition mconcl _ := {
            (* Here Wr ⊂ Wconcl by invariant *)
              | Loop u incl isl => Loop u incl isl
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
      - transitivity (clauses_levels premconclW) => //.
        eapply clauses_levels_mon. rewrite eqprem. apply restrict_clauses_subset.
      - rewrite eqprem. eapply restrict_clauses_subset.
      - have mu := model_updates mr.
        setoid_rewrite eqprem at 1 in mu.
        eapply strictly_updates_is_update_of_restrict in upd; tea.
        apply check_model_spec in eqm as [Wconcl' [sumr eqw]].
        have tr := strictly_updates_trans upd sumr.
        eapply strictly_updates_clauses_W; tea.
        { intros ?. now rewrite ClausesProp.union_sym union_diff_cls. }
        { have incl := model_incl mr. apply strictly_updates_incl in sumr.
          have hdiff := clauses_conclusions_diff_left cls W (cls ⇂ W).
          clear -clsW hdiff incl sumr.
          lsets. }
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
        have okupdm : is_model (model_update m (model_model mr)) premconclW.
        { setoid_rewrite eqprem at 2. apply is_model_update. apply strictly_updates_model_of in upd; tea.
           eapply valid_model_only_model. now eapply strictly_updates_restrict_only_model.
           now setoid_rewrite <- eqprem at 1. }
        have mu := is_model_union okupdm eqm.
        rewrite {2}eqprem in mu.
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

Lemma is_update_of_incl {cls : clauses} {W : LevelSet.t} {m m' : model} :
  is_update_of cls W m m' -> W ⊂_lset clauses_conclusions cls.
Proof.
  move/is_update_of_case => [[he heq]|].
  - intros l; lsets.
  - now move/strictly_updates_incl.
Qed.

Lemma strictly_updates_update_of {cls W m m'} :
  strictly_updates cls W m m' ->
  is_update_of cls W m m'.
Proof.
  intros su.
  rewrite /is_update_of.
  destruct LevelSet.is_empty eqn:he => //.
  eapply LevelSet.is_empty_spec in he.
  eapply strictly_updates_non_empty in su => //.
Qed.

Lemma levels_of_level_map {m ne V}:
  only_model_of V m ->
  levels (of_level_map m ne) ⊂_lset V.
Proof.
  move=> om l; rewrite levels_spec => -[k] /of_level_map_spec hin. apply om.
  now eexists.
Qed.

Local Open Scope Z_scope.

#[tactic="idtac"]
Equations? loop (V : LevelSet.t) (U : LevelSet.t) (cls : clauses) (minit m : model)
  (prf : [/\ clauses_levels cls ⊂_lset V, only_model_of V minit & is_update_of cls U minit m]) : result V U cls minit
  by wf (loop_measure V U) lexprod_rel :=
  loop V U cls minit m prf with inspect (check_model cls (U, m)) :=
    | exist None eqm => Model U {| model_model := m |} _
    | exist (Some (W, m')) eqm with inspect (LevelSet.equal W V) := {
      | exist true eq := Loop (of_level_map minit (check_model_defined_init_map prf eqm)) _ _
      (* Loop on cls ↓ W, with |W| < |V| *)
      | exist false neq with inner_loop V U minit loop W (cls ↓ W) m' _ :=
        { | Loop u incl isloop := Loop u _ (loop_on_subset _ isloop)
          | Model Wc mwc _
          (* We get a model for (cls ↓ W), we check if it extends to all clauses.
              By invariant |Wc| cannot be larger than |W|. *)
            with inspect (check_model cls (W, mwc.(model_model))) :=
          { | exist None eqm' => Model (LevelSet.union W Wc) {| model_model := mwc.(model_model) |} _
            | exist (Some (Wcls, mcls)) eqm' with inspect (LevelSet.equal Wcls V) := {
              | exist true _ := Loop (of_level_map minit (check_model_defined_init_map prf eqm)) _ _
              | exist false neq' with loop V (LevelSet.union W Wcls) cls minit mcls _ := {
                (* Here Wcls < V, we've found a model for all of the clauses with conclusion
                  in W, which can now be fixed. We concentrate on the clauses whose
                  conclusion is different. Clearly |W| < |V|, but |Wcls| is not
                  necessarily < |V| *)
                  | Loop u incl isloop := Loop u incl isloop
                  | Model Wvw mcls' hsub := Model Wvw {| model_model := model_model mcls' |} _ } } }
          }
      }
    .
Proof.
  all:cbn -[of_level_map cls_diff clauses_with_concl restrict_clauses]; clear loop.
  all:try solve [intuition auto].
  all:try eapply levelset_neq in neq.
  all:have cls_sub := clauses_conclusions_levels cls.
  all:destruct prf as [clsV mof isupd].
  - red. eapply LevelSet.equal_spec in eq0.
    set (prf := check_model_defined_init_map _ _); clearbody prf.
    eapply check_model_is_update_of in eqm; tea. rewrite eq0 in eqm.
    destruct eqm. rewrite union_idem in H. eapply strictly_updates_incl in H.
    have heq : V =_lset clauses_levels cls.
    { intros l. split. move/H. apply clauses_conclusions_levels. apply clsV. }
    intros l. rewrite -heq.
    rewrite levels_spec => -[k].
    rewrite of_level_map_spec. specialize (mof l). rewrite mof. now eexists.
  - red. eapply LevelSet.equal_spec in eq0.
    set (prf := check_model_defined_init_map _ _); clearbody prf.
    eapply check_model_is_update_of in eqm; tea. rewrite eq0 in eqm.
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
  - intros l; move/incl. apply clauses_levels_mon. apply clauses_with_concl_subset.
  - now intros ?; rewrite in_clauses_with_concl.
  - apply LevelSet.equal_spec in e.
    set (ne := check_model_defined_init_map _ _). clearbody ne.
    have hu := model_updates mwc.
    eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    eapply strictly_updates_is_update_of in eqm; tea.
    rewrite union_idem union_with_concl in eqm.
    eapply check_model_update_of in eqm' as [wmcls [upd eq]].
    intros l. rewrite levels_spec => -[k hin].
    eapply of_level_map_spec in hin.
    specialize (mof l) as [_ incl'].
    forward incl'. now eexists. rewrite -e in incl'.
    eapply strictly_updates_incl in eqm.
    eapply is_update_of_incl in upd.
    apply cls_sub. move: incl'; rewrite eq LevelSet.union_spec => -[] incl'.
    apply eqm. lsets. now apply upd.
  - set (ne := check_model_defined_init_map _ _). clearbody ne.
    apply LevelSet.equal_spec in e.
    have hu := model_updates mwc.
    eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have inclW : W ⊂_lset V.
    { rewrite union_idem in eqm.
      have incl' := strictly_updates_incl eqm.
      etransitivity; tea. etransitivity; tea. }
    eapply strictly_updates_is_update_of in eqm; tea.
    rewrite union_idem union_with_concl in eqm.
    (* have isupd' : is_update_of cls (W ∪ Wc) minit (model_model mwc). *)
    have incl' := is_update_of_incl hu.
    rewrite clauses_conclusions_clauses_with_concl in incl'.
    have hwwc : W ∪ Wc =_lset W.
    { intros l; lsets. }
    rewrite hwwc in eqm.
    eapply strictly_updates_update_of in eqm.
    eapply check_model_is_update_of in eqm' as [eqm' incl2]; tea.
    rewrite union_idem in eqm'. rewrite e in eqm'.
    eapply (strictly_updates_entails_on_V _ _ _ ne) in eqm'. red.
    eapply entails_all_clauses_subset; tea.
    eapply clauses_with_concl_subset. exact mof.
  - eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    have hu := model_updates mwc.
    have incl' := is_update_of_incl hu.
    eapply strictly_updates_is_update_of in hu; tea.
    rewrite union_idem union_with_concl in hu.
    eapply check_model_update_of in eqm' as [wmcls [upd ->]].
    eapply is_update_of_strictly_updates in hu.
    have tr := is_update_of_trans_eq hu upd.
    rewrite clauses_conclusions_clauses_with_concl in incl'.
    have hwwc : W ∪ Wc =_lset W.
    { intros l. lsets. }
    split => //. apply tr. clsets. lsets.
  - right.
    eapply check_model_spec_V in eqm' as eqm''. 3:etransitivity; [apply clauses_conclusions_levels|exact clsV]. cbn in eqm''.
    2:{
      eapply check_model_is_update_of in eqm as [eqm incl]; tea. rewrite union_idem in eqm.
      eapply strictly_updates_is_update_of in eqm; tea. 2:apply mwc.
      eapply strictly_updates_model_of_gen in eqm; tea. 2:exact mof.
      eapply model_of_subset; tea. lsets. }
    2:{ apply mwc. }
    destruct eqm'' as [Hwc Hwcls H1 mext tot].
    eapply check_model_is_update_of in eqm as [eqm incl]; tea.
    rewrite union_idem in eqm.
    have hu := model_updates mwc.
    have incl' := is_update_of_incl hu.
    rewrite clauses_conclusions_clauses_with_concl in incl'.
    have hwwc : W ∪ Wc =_lset W.
    { intros l. lsets. }
    eapply strictly_updates_is_update_of in hu; tea.
    rewrite union_with_concl hwwc in hu.
    eapply check_model_is_update_of in eqm' as [eqm' incl2]; tea.
    2:{ now eapply strictly_updates_update_of. }
    have WcW := model_incl mwc.
    have w_incl := strictly_updates_incl eqm.
    have wcls_incl := strictly_updates_incl eqm'.
    assert (exists l, LevelSet.In l Wcls /\ ~ LevelSet.In l W).
    { destruct H1 as [cl [clcls nvalid hcll hv]].
      pose proof (model_ok mwc).
      eapply is_model_invalid_clause in H; tea.
      assert (~ LevelSet.In (level (concl cl)) W).
      { intros hin. rewrite in_clauses_with_concl in H. intuition auto. }
      exists (concl cl).1. split => //. }
    rewrite -!diff_cardinal //. rewrite union_idem in wcls_incl.
    clear -w_incl clsV incl wcls_incl.
    have hincl := clauses_conclusions_levels cls.
    { lsets. }
    { lsets. }
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
