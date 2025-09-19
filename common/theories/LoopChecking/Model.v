(* Distributed under the terms of the MIT license. *)
(* This module defines the notion of model as a partial function from levels to Z.

  [is_model cls m] states that all clauses [cls] are valid in [m].

  An atom [l + k] is satisfied in a model [m] when the value of [l] in [m] is defined to [v : Z] and
  [k ≤ v]. If the value is undefined the atom does not hold.

  A clause [prems -> concl + k] is valid in [m]:
  - if the atom [concl + (k + kprem)] is satisfied where [kprem] is the minimal value of
    its (non-empty) premises.
  - otherwise, if the premises contain an undefined atom (the clause is not "enabled"),
    its minimal value is undefined and the premise vacuously holds.

  We develops the theory of [check_model m cls], the function that checks a model [m]
  w.r.t. a set of clauses [cls] and potentially updates some values to make the clauses hold.
  The main invariant is that, if [check_model] modifies some values, then we have a sequence of
  strict updates ([strictly_updates]) from the initial model to the modified one. If [check_model] does not modify any
  value, then [m] is already a model of [cls]. Note that some clauses in [cls] might not be
  activated/enabled by the model [m] (they hence hold vacuously).

  Note that [strictly_updates] is indexed by clauses and a levelset which should not be compared
  by Leibniz equality, we rather use a set(oid)-specific equality for them, hence [strictly_updates]
  is defined by so-called "Fording" of the index. We provide an elimination principle and "smart"
  constructors that can be nicer to work with: [strictly_updates_elim], [one_update] and [trans_update],
  and show that [strictly_updates] is [Proper] for these notions of equality.

  We also show the relation of a model to entailment:
  - If an entailment [cls ⊢ prems → concl] holds then any valid model [m] of the clauses [cls]
    satisfies [prems → concl], i.e [ is_model cls m -> valid_clause m (prems, concl) ].
  - Conversely, if we have a sequence of strict updates from model [m] to model [m'] under clauses
    [cls] then we have an entailment: [ cls ⊢ of_model_map m → of_level_map m' ], where
    [of_level_map] turns assignments [m -> Some v] to atoms [m + v] and [m -> None] are discarded.
    The maps must be defined for at least one level, which follows from the fact we have
    a strict update.

  - From any model we can build a valuation (in 𝐍) by shifting it upwards and inverting it
    so that the "lowest" level is mapped to 0 ([valuation_of_model])

  - If a clause is valid and enabled (its premises are all defined),
    the interpretation of the clause (in 𝐍) using the derived valuation is provable.

  - If an entailment [cls ⊢ prems → concl] holds then any valuation [v] that satisfies the clauses
    [cls] also satisfies [prems → concl], i.e [ forall v, ⟦ cls ⟧_v -> ⟦ prems ⟧_v >= ⟦ concl ⟧_v ] (in 𝐍).

  The algorithm in [PartialLoopChecking] will either build a model of the clauses by a sequence
  of strict updates from which we can build a valuation that satisfies the clauses or it will detect
  a loop, i.e. a situation where [cls ⊢ a → a + 1] for some (non-empty) set of atoms [a] (i.e. a contradiction when seen
  through the valuations).

  Altogether, by choosing appropriate initial models (defined in [Models.v]), this allows to decide
  satisfiability and validity.

  For satisfiabiliy [cls, prems → concl + k|=] we try to find a model of [cls /\ prems → concl + k]
  starting from an initial model m that enables the premises of all the clauses [cls] and [prems]:
  atoms [l + k] are defined such that m[l] >= k, so that the minimal premise value of all
  clauses is actually defined and [>= 0].

  For validity [cls |= prems → concl + k] we try to find a model of [cls] starting
  from an initial model m that enables *only* the premises [prems]:
  atoms [l + k] in [prems] are defined such that m[l] >= k. We then check if, in
  the (minimal) model that is inferred from the clauses [cls], the atom [concl + k] is satisfied.
  If so, the clause is valid: any possible valid valuation [v] of the clauses implies that
  [ ⟦ prems ⟧_v >= ⟦ concl ⟧_v ]. It implies that in any extension of the clauses [cls], the
  clause will remain valid.

*)

From Stdlib Require Import ssreflect ssrbool ssrfun ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From MetaRocq.Common Require Import Common Interfaces HornClauses.
From Equations Require Import Equations.
Set Equations Transparent.

Module Model (LS : LevelSets).
  Module Export Clauses := Clauses(LS).
  Export NES.
  Import Init.Logic (eq).

  Definition model := LevelMap.t (option Z).
  Definition equal_model (m m' : model) := LevelMap.Equal m m'.
  Definition defined_map (m : LevelMap.t (option Z)) :=
    exists l k, LevelMap.MapsTo l (Some k) m.

  Local Open Scope Z_scope.

  Definition level_value (m : model) (level : Level.t) : option Z :=
    match LevelMap.find level m with
    | Some v => v
    | None => None
    end.

  Lemma level_value_MapsTo {l k} {m : model} :
    LevelMap.MapsTo l k m -> level_value m l = k.
  Proof.
    unfold level_value.
  move=> mapto; rewrite (LevelMap.find_1 mapto) //.
  Qed.

  Lemma level_value_MapsTo' {l k} {m : model} :
    level_value m l = Some k -> LevelMap.MapsTo l (Some k) m.
  Proof.
    unfold level_value. destruct LevelMap.find eqn:hfind => //.
    eapply LevelMap.find_2 in hfind. now intros [= ->].
  Qed.

  Equations check_atom_value (z : option Z) (l : option Z) : bool :=
    | Some _, None => false
    | Some z, Some v => z <=? v
    | None, _ => true.

  Lemma check_atom_value_spec z l : reflectProp (z ≤ l) (check_atom_value z l).
  Proof.
    funelim (check_atom_value z l).
    - destruct (Z.leb_spec z v); constructor.
      * now constructor.
      * intros h; depelim h. lia.
    - constructor. intros h; depelim h.
    - constructor. constructor.
  Qed.

  Inductive findSpec {A} l m : option A -> Prop :=
    | inm k : LevelMap.MapsTo l k m -> findSpec l m (Some k)
    | ninm : ~ LevelMap.In l m -> findSpec l m None.

  Lemma find_spec {A} l (m : LevelMap.t A) : findSpec l m (LevelMap.find l m).
  Proof.
    destruct (LevelMap.find l m) eqn:heq; constructor.
    now apply LevelMap.find_2.
    now apply LevelMapFact.F.not_find_in_iff in heq.
  Qed.

  Variant level_value_spec (m : model) (l : Level.t) : option Z -> Prop :=
  | level_value_in k : LevelMap.MapsTo l k m -> level_value_spec m l k
  | level_value_nin : ~ LevelMap.In l m -> level_value_spec m l None.

  Lemma level_valueP {m l} : level_value_spec m l (level_value m l).
  Proof.
    rewrite /level_value.
    case: find_spec.
    - now move=> k0 hm; apply level_value_in.
    - now move=> hnin; apply level_value_nin.
  Qed.

  Definition levelexpr_value (m : model) (atom : LevelExpr.t) :=
    level_value m (level atom).

  Extraction Inline levelexpr_value.

  Definition min_atom_value (m : model) (atom : LevelExpr.t) : option Z :=
    let '(l, k) := atom in
    match level_value m l with
    | None => None
    | Some val => Some (val - k)%Z
    end.

  Definition min_premise (m : model) (l : premises) : option Z :=
    let (hd, tl) := to_nonempty_list l in
    fold_left (fun min atom => option_map2 Z.min (min_atom_value m atom) min) tl (min_atom_value m hd).

  Definition satisfiable_atom (m : model) (atom : Level.t * Z) : bool :=
    let '(l, k) := atom in
    match level_value m l with
    | Some val => k <=? val
    | None => false
    end.

  Definition satisfiable_premise (m : model) (l : premises) :=
    LevelExprSet.for_all (satisfiable_atom m) l.

  (* Definition valid_clause (m : model) (cl : clause) := *)
    (* implb (satisfiable_premise m (premise cl)) (satisfiable_atom m (concl cl)). *)
  Definition level_value_above m l k :=
    match level_value m l with
    | Some val => k <=? val
    | None => false
    end.

  Definition valid_clause (m : model) (cl : clause) :=
    let k0 := min_premise m (premise cl) in
    match k0 with
    | None => true
    | Some k0 =>
      let (l, k) := concl cl in
      level_value_above m l (k + k0)
    end.

  Definition is_model (cls : clauses) (m : model) : bool :=
    Clauses.for_all (valid_clause m) cls.

  Inductive update_result :=
    | VacuouslyTrue
    | Holds
    | DoesntHold (wm : LevelSet.t × model).

  Definition update_model (m : model) l v : model := LevelMap.add l (Some v) m.

  Definition update_value (m : model) (cl : clause) : option model :=
    let k0 := min_premise m (premise cl) in
    match k0 with
    | None => None
    | Some k0 =>
      let (l, k) := concl cl in
      (* Does the conclusion also hold?
          We optimize a bit here, rather than adding k0 in a second stage,
          we do it already while checking the clause. In the paper, a second
          pass computes this.
        *)
      if level_value_above m l (k + k0) then None
      else Some (update_model m l (k + k0))
    end.

  Definition check_clause_model cl '(modified, m) :=
      match update_value m cl with
    | None => (modified, m)
    | Some m => (clause_conclusion cl :: modified, m)
    end.

  Definition check_model_aux (cls : clauses) (wm : list Level.t × model) : list Level.t × model :=
    Clauses.fold check_clause_model cls wm.

  (* If check_model = None then we have a model of all clauses,
    othewise, we return Some (W', m') where W ⊂ W' and the model has
    been updated for at least one atom l ∈ W'. *)
  Definition check_model (cls : clauses) (wm : LevelSet.t × model) : option (LevelSet.t × model) :=
    let '(modified, m) := check_model_aux cls ([], wm.2) in
    match modified return option (LevelSet.t × model) with
    | [] => None
    | l => Some ((LevelSet.union (LevelSetProp.of_list l) wm.1), m)
    end.

  Definition strict_update m '(prems, (concl, k)) m' :=
    exists v,
    [/\ min_premise m prems = Some v, ~~ level_value_above m concl (k + v) &
    m' =m (LevelMap.add concl (Some (k + v)) m)].

  Inductive strictly_updates cls (s : LevelSet.t) : model -> model -> Prop :=
  | update_one m cl m' : Clauses.In cl cls ->
    s =_lset (LevelSet.singleton (clause_conclusion cl)) ->
    strict_update m cl m' -> strictly_updates cls s m m'


  | update_trans {ls ls' m m' m''} :
    strictly_updates cls ls m m' ->
    strictly_updates cls ls' m' m'' ->
    s =_lset LevelSet.union ls ls' ->
    strictly_updates cls s m m''.

  Definition is_update_of cls upd minit m :=
    if LevelSet.is_empty upd then minit =m m
    else strictly_updates cls upd minit m.

  #[export] Instance level_value_proper : Proper (equal_model ==> Logic.eq ==> Logic.eq) level_value.
  Proof.
    intros x y eqm l ? <-. unfold level_value.
    unfold equal_model in eqm.
    destruct LevelMap.find eqn:hl.
    - eapply LevelMap.find_2 in hl.
      rewrite eqm in hl.
      eapply LevelMap.find_1 in hl. now rewrite hl.
    - eapply LevelMapFact.F.not_find_in_iff in hl.
      rewrite eqm in hl.
      eapply LevelMapFact.F.not_find_in_iff in hl.
      now rewrite hl.
  Qed.

  #[export] Instance min_atom_value_proper : Proper (LevelMap.Equal ==> Logic.eq ==> Logic.eq) min_atom_value.
  Proof.
    intros m m' eqm ? ? ->. unfold min_atom_value.
    destruct y => //.
    now rewrite eqm.
  Qed.

  #[export] Instance min_premise_proper : Proper (LevelMap.Equal ==> Logic.eq ==> Logic.eq) min_premise.
  Proof.
    intros m m' eq ? ? ->.
    unfold min_premise.
    destruct to_nonempty_list.
    now setoid_rewrite eq.
  Qed.

  #[export] Instance level_value_above_proper : Proper (LevelMap.Equal ==> Logic.eq ==> Logic.eq ==> Logic.eq) level_value_above.
  Proof.
    intros m m' hm ? ? -> ? ? ->.
    unfold level_value_above.
    now rewrite hm.
  Qed.

  Instance strictly_updates_proper : Proper (Clauses.Equal ==> LevelSet.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) strictly_updates.
  Proof.
    intros ? ? H ? ? H' ? ? H'' ? ? H'''.
    split.
    induction 1 in y0, H', y, H, y1, H'', y2, H'''|- *;
    [econstructor 1|econstructor 2]; eauto.
    now rewrite <- H. now rewrite -H'. move: H2; unfold strict_update.
    destruct cl as [premse []].
    intros [v []]; exists v; split;
    try setoid_rewrite <- H;
    try setoid_rewrite <- H'';
    try setoid_rewrite <- H'''; firstorder.
    3:{ rewrite -H'. exact H0. }
    eapply IHstrictly_updates1; try firstorder. eapply IHstrictly_updates2; tea. reflexivity. reflexivity.
    induction 1 in x, H, x0, H', x1, H'', x2, H'''|- * ; [econstructor 1|econstructor 2]; eauto.
    now rewrite H. now rewrite H' H1. move: H2; unfold strict_update. destruct cl as [premse []].
    intros [v []]; exists v; split;
    try setoid_rewrite H;
    try setoid_rewrite H'';
    try setoid_rewrite H'''; firstorder.
    3:{ now rewrite H' H0. }
    eapply IHstrictly_updates1; try firstorder.
    eapply IHstrictly_updates2; auto; reflexivity.
  Qed.

  Lemma trans_update {cls m ls ls' m' m''} :
    strictly_updates cls ls m m' ->
    strictly_updates cls ls' m' m'' ->
    strictly_updates cls (ls ∪ ls') m m''.
  Proof.
    intros hin su; econstructor 2; trea.
  Qed.

  Lemma one_update {cls m cl m'} :
    Clauses.In cl cls -> strict_update m cl m' ->
    strictly_updates cls (LevelSet.singleton (clause_conclusion cl)) m m'.
  Proof.
    intros hin su; econstructor; trea.
  Qed.

  (* We have a more confortable elimination principle
    now for compatible predicates *)
  Lemma strictly_updates_elim :
    forall (cls : Clauses.t) (P : LevelSet.t -> model -> model -> Prop)
    (HP : Proper (LevelSet.Equal ==> Logic.eq ==> Logic.eq ==> iff) P),
    (forall m cl m', Clauses.In cl cls ->
      strict_update m cl m' -> P (LevelSet.singleton (clause_conclusion cl)) m m') ->
    (forall (ls ls' : LevelSet.t) (m m' m'' : model),
      strictly_updates cls ls m m' ->
      P ls m m' ->
      strictly_updates cls ls' m' m'' ->
      P ls' m' m'' -> P (ls ∪ ls') m m'') ->
      forall (s : LevelSet.t) (m m0 : model),
      strictly_updates cls s m m0 -> P s m m0.
  Proof.
    intros cls P cP h0 h1.
    induction 1.
    - rewrite H0. now apply h0.
    - rewrite H1. now eapply h1.
  Qed.

  Lemma strictly_updates_step cls w m m' m'' :
    strictly_updates cls w m m' ->
    forall cl, Clauses.In cl cls -> strict_update m' cl m'' ->
    strictly_updates cls (LevelSet.add (clause_conclusion cl) w) m m''.
  Proof.
    revert w m m'.
    apply: strictly_updates_elim.
    { solve_proper. }
    - intros.
      eapply update_trans; tea. 2:{ econstructor 1; tea. reflexivity. }
      eapply update_one. 3:tea. auto. reflexivity. lsets.
    - intros.
      specialize (H2 _ H3 H4).
      eapply update_trans; tea. lsets.
  Qed.

  Lemma strictly_updates_weaken cls w cls' :
    Clauses.Subset cls cls' ->
    forall m m', strictly_updates cls w m m' -> strictly_updates cls' w m m'.
  Proof.
    intros hcls m m'.
    induction 1. econstructor => //. now eapply hcls.
    econstructor 2; tea.
  Qed.

  Lemma strictly_updates_W_trans cls m w m' cl m'' :
    strictly_updates cls w m m' ->
    strict_update m' cl m'' ->
    strictly_updates (Clauses.add cl cls) (LevelSet.add (clause_conclusion cl) w) m m''.
  Proof.
    intros updW su.
    destruct cl as [prems [concl k]].
    eapply strictly_updates_step; tea.
    - eapply strictly_updates_weaken; tea. clsets.
    - rewrite Clauses.add_spec. left; reflexivity.
  Qed.

  #[export] Instance clauses_with_concl_proper : Proper (Clauses.Equal ==> LevelSet.Equal ==> Clauses.Equal) clauses_with_concl.
  Proof.
    intros ? ? H ? ? H' l.
    rewrite !in_clauses_with_concl.
    now rewrite H H'.
  Qed.

  #[export] Instance restrict_clauses_proper : Proper (Clauses.Equal ==> LevelSet.Equal ==> Clauses.Equal) restrict_clauses.
  Proof.
    intros ? ? H ? ? H' l.
    rewrite !in_restrict_clauses.
    now rewrite H H'.
  Qed.

  Lemma strictly_updates_strenghten {cls W m m'} :
    strictly_updates cls W m m' ->
    strictly_updates (cls ↓ W) W m m'.
  Proof.
    induction 1.
    - setoid_rewrite H0 at 2. eapply one_update.
      rewrite in_clauses_with_concl. split => //.
      rewrite H0.
      eapply LevelSet.singleton_spec; reflexivity. exact H1.
    - setoid_rewrite H1. rewrite clauses_with_concl_union.
      eapply trans_update.
      eapply strictly_updates_weaken; tea. intros x; clsets.
      eapply strictly_updates_weaken; tea. intros x; clsets.
  Qed.

  #[export] Instance equal_model_equiv : Equivalence equal_model.
  Proof. unfold equal_model.
    split; try econstructor; eauto.
    red. intros. now symmetry.
    red; intros. now transitivity y.
  Qed.

  #[export] Instance is_model_proper : Proper (Clauses.Equal ==> eq ==> eq) is_model.
  Proof.
    intros cl cl' eqcl x y ->. unfold is_model. now rewrite eqcl.
  Qed.

  #[export] Instance update_model_proper : Proper (LevelMap.Equal ==> eq ==> eq ==> LevelMap.Equal) update_model.
  Proof.
    intros m m' hm ? ? -> ? ? ->.
    unfold update_model.
    now rewrite hm.
  Qed.

  Instance clauses_elements_proper : Proper (Clauses.Equal ==> eq) Clauses.elements.
  Proof.
    intros cl cl' eq.
    have sl := Clauses.elements_spec2 cl.
    (* have nl := Clauses.elements_spec2w cl. *)
    have sl' := Clauses.elements_spec2 cl'.
    (* have nl' := Clauses.elements_spec2w cl'. *)
    have heq := @SortA_equivlistA_eqlistA _ Logic.eq _ Clause.lt_.
    do 3 forward heq by tc.
    specialize (heq _ _ sl sl').
    forward heq.
    red. intros x.
    rewrite -! ClausesProp.Dec.F.elements_iff. apply eq.
    now apply eqlistA_eq.
  Qed.

  Definition eqwm (x y : LevelSet.t * LevelMap.t (option Z)) :=
    LevelSet.Equal x.1 y.1 /\ LevelMap.Equal x.2 y.2.

  Instance eqwm_equiv : Equivalence eqwm.
  Proof.
    unfold eqwm; split.
    - intros [] => //=.
    - intros [] [] [] => //=. cbn in *. split; now symmetry.
    - intros [] [] [] [] [] => //=; cbn in *. split.
      now transitivity t2. now transitivity t3.
  Qed.

  Definition eqwm_list (x y : list Level.t * LevelMap.t (option Z)) :=
    x.1 = y.1 /\ LevelMap.Equal x.2 y.2.

  Instance eqwm_list_equiv : Equivalence eqwm_list.
  Proof.
    unfold eqwm; split.
    - intros [] => //=.
    - intros [] [] [] => //=. cbn in *. split; now symmetry.
    - intros [] [] [] [] [] => //=; cbn in *. split.
      now transitivity l0. now transitivity t1.
  Qed.

  Lemma update_value_valid {m cl} :
    match update_value m cl with
    | None => valid_clause m cl
    | Some _ => ~~ valid_clause m cl
    end.
  Proof.
    unfold update_value, valid_clause.
    destruct cl as [prem [l k]]; cbn.
    destruct min_premise => //.
    unfold level_value_above;
    destruct level_value => //.
    destruct Z.leb => //.
  Qed.

  Lemma valid_clause_elim {m prems concl k} : valid_clause m (prems, (concl, k)) ->
    forall z, min_premise m prems = Some z ->
    Some (z + k) ≤ level_value m concl.
  Proof.
    rewrite /valid_clause => hcl z eqmin.
    rewrite eqmin in hcl. cbn in *.
    move: hcl. rewrite /level_value_above. destruct level_value eqn:hl => //.
    move/Z.leb_le. constructor. lia.
  Qed.

  Lemma valid_clause_intro {m prems concl k} :
    (forall z,
      min_premise m prems = Some z ->
      Some (z + k) ≤ level_value m concl) ->
    valid_clause m (prems, (concl, k)).
  Proof.
    rewrite /valid_clause //=.
    destruct min_premise => //.
    intros hz.
    specialize (hz _ eq_refl). depelim hz.
    rewrite /level_value_above H0.
    apply Z.leb_le. lia.
  Qed.

  Lemma check_clause_model_spec {cl w m w' m'} :
    check_clause_model cl (w, m) = (w', m') ->
    (w = w' -> m = m' /\ valid_clause m cl) /\
    (w <> w' -> w' = clause_conclusion cl :: w /\
      strictly_updates (Clauses.singleton cl) (LevelSet.singleton (clause_conclusion cl)) m m').
  Proof.
    unfold check_clause_model.
    destruct update_value eqn:upd; revgoals.
    * intros [= <- <-]. split => //. split => //.
      move: (@update_value_valid m cl). now rewrite upd.
    * intros [= <- <-]. split => //.
      + intros. eapply (f_equal (@List.length _)) in H. cbn in H; lia.
      + intros _. split => //. apply one_update. clsets. unfold strict_update.
        move: upd. unfold update_value.
        destruct cl as [prems [concl k]]. cbn.
        destruct min_premise => //.
        destruct level_value_above eqn:hl => //.
        intros [= <-].
        exists z. split => //. rewrite hl. split => //.
  Qed.

  Lemma check_model_aux_spec {cls w m w' m'} :
    check_model_aux cls (w, m) = (w', m') ->
    (w = w' -> m = m' /\ is_model cls m) /\
    (w <> w' -> exists pref, w' = pref ++ w /\ strictly_updates cls (LevelSetProp.of_list pref) m m').
  Proof.
    rewrite /check_model_aux /is_model.
    revert w' m'.
    eapply ClausesProp.fold_rec.
    - intros s' he w' m' [= <- <-]. split => //. split => //.
      eapply Clauses.for_all_spec. tc. intros x hin. now apply he in hin.
    - clear. intros x [w'' m''] s' s'' inx nins' hadd ih w' m' cl.
      specialize (ih _ _ eq_refl) as[].
      split; intros; subst.
      + eapply check_clause_model_spec in cl as [].
        destruct (eqb_spec w' w'').
        { subst w''. specialize (H eq_refl) as []. specialize (H1 eq_refl) as []. split => //. congruence.
          eapply Clauses.for_all_spec in H3. eapply Clauses.for_all_spec. all:tc.
          intros ? hin. eapply hadd in hin as []; subst; firstorder. }
        forward H0 by auto. forward H2 by auto.
        destruct H0 as [pref [-> su]].
        destruct pref; cbn in *; try congruence.
        destruct H2. eapply (f_equal (@List.length _)) in H0; cbn in H0. rewrite length_app in H0. lia.
      + eapply check_clause_model_spec in cl as [].
        destruct (eqb_spec w w'').
        { subst w''. specialize (H eq_refl) as []. subst m''.
          destruct (eqb_spec w w'); subst; try congruence.
          specialize (H3 H) as []. subst w'. exists [clause_conclusion x]. split => //.
          setoid_replace (LevelSetProp.of_list [clause_conclusion x]) with (LevelSet.singleton (clause_conclusion x)).
          eapply ClausesProp.Add_Equal in hadd. rewrite hadd. eapply strictly_updates_weaken; tea. clsets.
          intros ?. rewrite LevelSetProp.of_list_1 InA_In_eq. firstorder. subst a.
          now apply LevelSet.singleton_spec.
          apply LevelSet.singleton_spec in H3. now constructor. }
        specialize (H0 H4).
        destruct (eqb_spec w'' w'); subst.
        { specialize (H2 eq_refl) as []; subst m''.
          destruct H0 as [pref []]. subst w'. exists pref; split => //.
          eapply strictly_updates_weaken; tea. intros ? ?. eapply hadd. clsets. }
        forward H3 by auto. destruct H3 as [->].
        destruct H0 as [pref [-> su]]. eexists (clause_conclusion x :: pref); split => //.
        setoid_replace (LevelSetProp.of_list (clause_conclusion x :: pref)) with (LevelSet.union (LevelSetProp.of_list pref) (LevelSet.singleton (clause_conclusion x))).
        eapply (strictly_updates_weaken _ _ s'') in su; tea; try firstorder.
        eapply (strictly_updates_weaken _ _ s'') in H3; tea; try firstorder.
        2:{ intros ?; rewrite Clauses.singleton_spec. intros ->. now apply hadd. }
        exact: trans_update su H3.
        intros ?. cbn. lsets.
  Qed.

  Inductive lift_option_rel {A} (R : relation A) : relation (option A) :=
  | lift_none : lift_option_rel R None None
  | lift_some x y : R x y -> lift_option_rel R (Some x) (Some y).
  Derive Signature for lift_option_rel.
  Instance update_value_proper : Proper (LevelMap.Equal ==> eq ==> lift_option_rel LevelMap.Equal) update_value.
  Proof.
    intros x y eqm [prems [concl k]] ? <- => //=.
    rewrite /update_value.
    setoid_rewrite eqm at 1. destruct min_premise => //=.
    setoid_rewrite eqm at 1. destruct level_value_above => //=; constructor.
    now rewrite eqm.
    constructor.
  Qed.

  Instance check_clause_model_proper : Proper (eq ==> eqwm_list ==> eqwm_list) check_clause_model.
  Proof.
    intros [prems [concl k]] ? <- [] [] eq.
    set (cl := (prems, (concl, k))) in *.
    cbn. destruct eq as [eql eqm]. cbn in *. subst l0.
    have equpd := update_value_proper t0 t1 eqm cl cl eq_refl.
    depelim equpd. rewrite H H0. split => //.
    rewrite H0 H1. split => //.
  Qed.

  #[export] Instance check_model_aux_proper : Proper (Clauses.Equal ==> eqwm_list ==> eqwm_list) check_model_aux.
  Proof.
    intros ? ? eq [] [] []; cbn in *. subst l0.
    rewrite /check_model_aux.
    rewrite !ClausesProp.fold_spec_right.
    rewrite eq. induction (List.rev (Clauses.elements y)); cbn.
    red; split => //=. rewrite IHl0. reflexivity.
  Qed.

  #[export] Instance check_model_aux_proper_strict : Proper (Clauses.Equal ==> eq ==> eq) check_model_aux.
  Proof.
    intros ? ? eq [] [] []; cbn in *.
    rewrite /check_model_aux.
    rewrite !ClausesProp.fold_spec_right. now rewrite eq.
  Qed.

  #[export] Instance check_model_proper : Proper (Clauses.Equal ==> eqwm ==> lift_option_rel eqwm) check_model.
  Proof.
    intros cls cls' eq.
    intros wm wm' eqm.
    unfold check_model.
    have := (check_model_aux_proper cls cls' eq ([], wm.2) ([], wm'.2)) => /fwd.
    split => //=. apply eqm.
    move=> [].
    destruct (check_model_aux cls _) eqn:eqc.
    destruct (check_model_aux cls' _) eqn:eqc' => //= <-.
    destruct l => //. constructor. destruct eqm. constructor.
    split => //=. now rewrite H.
  Qed.

  #[export] Instance check_model_proper_strict : Proper (Clauses.Equal ==> eq ==> eq) check_model.
  Proof.
    intros cls cls' eq ? ? ->.
    unfold check_model. now rewrite eq.
  Qed.

  Lemma check_model_spec {cls w m w' m'} :
    check_model cls (w, m) = Some (w', m') ->
    exists w'', strictly_updates cls w'' m m' /\
      w' =_lset LevelSet.union w w''.
  Proof.
    unfold check_model.
    destruct check_model_aux eqn:cm.
    apply check_model_aux_spec in cm as [].
    destruct l => //. forward H0. auto with datatypes.
    intros [= <- <-]. destruct H0 as [pref [heq su]].
    rewrite app_nil_r in heq. subst pref.
    exists (LevelSetProp.of_list (t0 :: l)). split => //.
    intros ?. cbn. lsets.
  Qed.


  Lemma strict_update_invalid m cl m' : strict_update m cl m' -> ~~ valid_clause m cl.
  Proof.
    destruct cl as [prems [concl k]].
    cbn.
    intros [v [him hna heq]].
    rewrite /valid_clause. rewrite him //=.
  Qed.

  Lemma strictly_updates_invalid cls w m m' : strictly_updates cls w m m' -> ~~ is_model cls m.
  Proof.
    induction 1.
    - eapply strict_update_invalid in H1.
      apply/negbT. unfold is_model.
      destruct Clauses.for_all eqn:fa => //.
      eapply Clauses.for_all_spec in fa; tc. eapply fa in H.
      now rewrite H in H1.
    - auto.
  Qed.

  Lemma check_model_None {cls acc} :
    check_model cls acc = None <-> is_model cls acc.2.
  Proof.
    unfold check_model.
    destruct check_model_aux eqn:cm.
    apply check_model_aux_spec in cm as [ne ex].
    destruct l => //. split => // _. now specialize (ne eq_refl) as [].
    split => //. forward ex by auto with datatypes. destruct ex as [pref [eq su]].
    rewrite app_nil_r in eq; subst pref.
    intros ism. eapply strictly_updates_invalid in su.
    now rewrite ism in su.
  Qed.

  Lemma check_model_updates_spec {cls w init_model m w' m'} :
    check_model cls (w, m) = Some (w', m') ->
    forall cls', strictly_updates cls' w init_model m ->
    strictly_updates (Clauses.union cls cls') w' init_model m' /\ w ⊂_lset w'.
  Proof.
    move/check_model_spec => [w'' [su eq]]. rw eq.
    intros cls' su'. split. 2:lsets.
    eapply trans_update; eapply strictly_updates_weaken; tea; clsets.
  Qed.

  Lemma strictly_updates_non_empty {cls W m m'} :
    strictly_updates cls W m m' -> ~ LevelSet.Empty W.
  Proof.
    induction 1.
    - intros he. specialize (he (clause_conclusion cl)). lsets.
    - intros he. apply IHstrictly_updates2. lsets.
  Qed.

  Lemma strictly_updates_non_empty_map {cls W m m'} :
    strictly_updates cls W m m' -> ~ LevelMap.Empty m'.
  Proof.
    induction 1.
    - intros he. specialize (he (clause_conclusion cl)).
      destruct cl as [prems [concl k]].
      destruct H1 as [? [? ? heq]].
      setoid_rewrite heq in he. eapply (he (Some (k + x))); cbn.
      rewrite LevelMapFact.F.add_mapsto_iff. firstorder.
    - intros he. now apply IHstrictly_updates2.
  Qed.

  Lemma strictly_updates_incl {cls W m m'} :
    strictly_updates cls W m m' -> W ⊂_lset clauses_conclusions cls.
  Proof.
    induction 1.
    - intros x. rewrite clauses_conclusions_spec. firstorder. exists cl.
      move: H2. rewrite H0. move/LevelSet.singleton_spec => ->. split => //.
    - lsets.
  Qed.

  Lemma is_update_of_non_empty {cls V m m'} : ~ LevelMap.Empty m ->
    is_update_of cls V m m' ->
    ~ LevelMap.Empty m'.
  Proof.
    rewrite /is_update_of. destruct LevelSet.is_empty.
    - now intros he <-.
    - intros he su. now eapply strictly_updates_non_empty_map in su.
  Qed.

  Instance defined_map_proper : Proper (LevelMap.Equal ==> iff) defined_map.
  Proof.
    intros x y eq; rewrite /defined_map.
    now setoid_rewrite eq.
  Qed.

  Lemma strictly_updates_defined_map {cls W m m'} :
    strictly_updates cls W m m' -> defined_map m'.
  Proof.
    induction 1.
    - exists (clause_conclusion cl).
      destruct cl as [prems [concl k]].
      destruct H1 as [? [? ? heq]]. cbn.
      setoid_rewrite heq. exists (k + x)%Z; cbn.
      rewrite LevelMapFact.F.add_mapsto_iff. firstorder.
    - assumption.
  Qed.

  Lemma is_update_of_defined_map {cls V m m'} : defined_map m ->
    is_update_of cls V m m' ->
    defined_map m'.
  Proof.
    rewrite /is_update_of. destruct LevelSet.is_empty.
    - now intros he <-.
    - intros he su. now eapply strictly_updates_defined_map in su.
  Qed.

  Lemma check_model_subset {cls v} :
    forall w' v', check_model cls v = Some (w', v') -> ~ LevelSet.Empty w'.
  Proof.
    intros w' v'.
    move/check_model_spec => [w'' [su ->]].
    eapply strictly_updates_non_empty in su. intros em. apply su. lsets.
  Qed.

  Definition model_same_domain (m m' : model) :=
    forall l, LevelMap.In l m <-> LevelMap.In l m'.

  #[export] Instance model_same_domain_refl : Reflexive model_same_domain.
  Proof. intros m l. reflexivity. Qed.

  #[export] Instance model_same_domain_trans : Transitive model_same_domain.
  Proof. intros m m' m'' h h' l. rewrite (h l). apply h'. Qed.

  Definition model_map_outside V (m m' : model) :=
    forall l, ~ LevelSet.In l V ->
      forall k, LevelMap.MapsTo l k m <-> LevelMap.MapsTo l k m'.

  #[export] Instance model_map_outside_refl V : Reflexive (model_map_outside V).
  Proof. intros m l. reflexivity. Qed.

  #[export] Instance model_map_outside_trans V : Transitive (model_map_outside V).
  Proof.
    intros m m' m'' h h' l hnin k.
    rewrite (h l hnin k). now apply h'.
  Qed.

  Definition model_rel R (m m' : model) :=
    forall l k, LevelMap.MapsTo l k m -> exists k', LevelMap.MapsTo l k' m' /\ R k k'.

  Infix "⩽" := (model_rel (opt_le Z.le)) (at level 70). (* \leqslant *)

  #[export] Instance model_le_refl R (HR : Reflexive R) : Reflexive (model_rel R).
  Proof. intros x l k map. exists k; split => //. Qed.

  #[export] Instance model_le_trans R (HR : Transitive R) : Transitive (model_rel R).
  Proof. intros m m' m'' mm' m'm'' l k map.
    apply mm' in map as [k' [map ?]].
    apply m'm'' in map as [k'' [map ?]]. exists k''. split => //.
    now transitivity k'.
  Qed.

  Lemma levelmap_find_eq {A} x (m m' : LevelMap.t A) :
    (forall k, LevelMap.MapsTo x k m <-> LevelMap.MapsTo x k m') ->
    LevelMap.find x m = LevelMap.find x m'.
  Proof.
   intros hm.
   destruct (LevelMap.find x m) eqn:he;
   destruct (LevelMap.find x m') eqn:he'.
   all:try apply LevelMap.find_2 in he. all:try apply LevelMap.find_2 in he'.
   apply hm in he. eapply LevelMapFact.F.MapsTo_fun in he; tea. congruence.
   apply hm in he. apply LevelMapFact.F.not_find_in_iff in he'. firstorder.
   apply LevelMapFact.F.not_find_in_iff in he. firstorder. congruence.
  Qed.

  Lemma levelmap_level_value_eq x (m m' : model) :
    (forall k, LevelMap.MapsTo x k m <-> LevelMap.MapsTo x k m') ->
    level_value m x = level_value m' x.
  Proof.
    intros he.
    rewrite /level_value. rewrite (levelmap_find_eq x m m') //.
  Qed.

  Lemma levelmap_find_eq_inv {A} x (m m' : LevelMap.t A) :
    LevelMap.find x m = LevelMap.find x m' ->
    (forall k, LevelMap.MapsTo x k m <-> LevelMap.MapsTo x k m').
  Proof.
    intros hfind.
   destruct (LevelMap.find x m) eqn:he;
   destruct (LevelMap.find x m') eqn:he'.
   all:try apply LevelMap.find_2 in he. all:try apply LevelMap.find_2 in he'. all:try congruence.
   noconf hfind. intros k; split; intros.
   eapply LevelMapFact.F.MapsTo_fun in he; tea. now subst.
   eapply LevelMapFact.F.MapsTo_fun in he'; tea. now subst.
   intros k; split; intros.
   apply LevelMapFact.F.not_find_in_iff in he. firstorder.
   apply LevelMapFact.F.not_find_in_iff in he'. firstorder.
  Qed.

  Lemma maps_to_update {l k} {m : model} {k'} : LevelMap.MapsTo l k m -> LevelMap.MapsTo l k' m <-> k = k'.
  Proof.
    firstorder. now eapply LevelMapFact.F.MapsTo_fun in H; tea. now subst.
  Qed.

  Lemma valid_update_value {m cl} :
    valid_clause m cl ->
    match update_value m cl with
    | None => true
    | Some _ => false
    end.
  Proof.
    unfold update_value, valid_clause.
    destruct cl as [prem [l k]]; cbn.
    destruct min_premise => //.
    unfold level_value_above.
    destruct level_value => //.
    destruct Z.leb => //.
  Qed.

  Lemma update_model_monotone m l k : level_value m l ≤ Some k ->
    m ⩽ update_model m l k.
  Proof.
    intros hl.
    intros l' k' maps.
    unfold update_model. cbn.
    destruct (eqb_spec l l').
    - subst l'. exists (Some k). move: hl.
      unfold level_value.
      rewrite (LevelMap.find_1 maps).
      intros hle.
      split => //. eapply LevelMap.add_1. eapply LevelMap.OT.eq_refl.
    - exists k'. split => //. apply LevelMap.add_2 => //. reflexivity.
  Qed.

  Lemma update_model_not_above m l k : level_value_above m l k = false ->
    m ⩽ update_model m l k.
  Proof.
    unfold level_value_above.
    intros hlev.
    apply update_model_monotone.
    destruct level_value as [v|] eqn:hv; constructor; lia.
  Qed.


  Lemma level_value_not_above_spec m l k : level_value_above m l k = false -> opt_le Z.lt (level_value m l) (Some k).
  Proof.
    unfold level_value_above; destruct level_value => // hlt; constructor. lia.
  Qed.

  Lemma level_value_above_leq {m l k} :
    Some k ≤ level_value m l ->
    level_value_above m l k.
  Proof.
    intros h; rewrite /level_value_above.
    depelim h. rewrite H0. apply Z.leb_le. lia.
  Qed.

  Lemma strict_update_ext m cl m' : strict_update m cl m' -> m ⩽ m'.
  Proof.
    destruct cl as [prems [concl k]].
    unfold strict_update.
    intros [v [hm ha heq]].
    intros x k' hin. setoid_rewrite heq.
    setoid_rewrite LevelMapFact.F.add_mapsto_iff.
    destruct (Level.eq_dec concl x). subst.
    move: ha; rewrite /level_value_above.
    eapply level_value_MapsTo in hin. rewrite hin.
    intros hlt'.
    exists (Some (k + v)).
    split. left. split; reflexivity.
    move/negbTE: hlt'.
    destruct k' => //.
    elim: Z.leb_spec => //. intros; constructor; lia. constructor.
    exists k'. split => //. right; eauto. reflexivity.
  Qed.

  Lemma strictly_updates_ext cls w m m' : strictly_updates cls w m m' -> m ⩽ m'.
  Proof.
    induction 1.
    now eapply strict_update_ext in H1.
    now transitivity m'.
  Qed.

  Lemma check_model_le {cls acc acc'} :
    check_model cls acc = Some acc' -> acc.2 ⩽ acc'.2.
  Proof.
    destruct acc as [w m], acc' as [w' m'].
    move/check_model_spec => [w'' [su ->]].
    cbn. now eapply strictly_updates_ext.
  Qed.

  Lemma level_value_update_model m l k :
    level_value (update_model m l k) l = Some k.
  Proof.
    unfold level_value, update_model.
    cbn -[LevelMap.find LevelMap.add].
    rewrite LevelMapFact.F.add_o.
    destruct LevelMap.OT.eq_dec => //.
    exfalso. now apply n.
  Qed.

  Lemma model_map_outside_weaken {W W'} {m m' : model} :
    model_map_outside W m m' ->
    W ⊂_lset W' ->
    model_map_outside W' m m'.
  Proof.
    intros hm sub x hin k.
    apply hm. intros hin'. apply sub in hin'. now apply hin.
  Qed.

  Lemma is_model_union {cls cls' m} :
    is_model cls m -> is_model cls' m -> is_model (Clauses.union cls cls') m.
  Proof.
    rewrite /is_model. rewrite /is_true -!ClausesFact.for_all_iff.
    now move=> ism ism' x /Clauses.union_spec [].
  Qed.

  Lemma model_le_values {m m' : model} x : m ⩽ m' -> level_value m x ≤ level_value m' x.
  Proof.
    intros lem. specialize (lem x).
    unfold level_value.
    destruct LevelMap.find eqn:hl => //.
    - apply LevelMap.find_2 in hl. specialize (lem _ hl) as [k' [mapsto leq]].
      now rewrite (LevelMap.find_1 mapsto).
    - constructor.
  Qed.


  Lemma min_premise_spec_aux (m : model) s k :
    min_premise m s = k ->
    (forall x, LevelExprSet.In x s -> (k ≤ min_atom_value m x)) /\
    (exists x, LevelExprSet.In x s /\ k = min_atom_value m x).
  Proof.
    unfold min_premise.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    intros <-.
    induction l.
    - cbn.
      split. intros x [->|] => //. reflexivity.
      now exists p; split => //.
    - destruct IHl as [ha hex].
      split.
      * intros x hin.
        eapply (in_elt_inv x a [p]) in hin as [<-|inih].
        { cbn. rewrite fold_left_comm.
          { intros x' y z. rewrite assoc. now rewrite (comm (min_atom_value m y)) -assoc. }
          apply Zmin_opt_left. }
      specialize (ha _ inih).
      cbn. rewrite fold_left_comm.
      { intros x' y z. rewrite assoc. now rewrite (comm (min_atom_value m y)) -assoc. }
      etransitivity; [apply Zmin_opt_right|assumption].
      * destruct hex as [minval [inmin ih]].
        cbn. rewrite fold_left_comm.
        { intros x' y z. rewrite assoc. now rewrite (comm (min_atom_value m y)) -assoc. }
        rewrite ih.
        destruct (min_opt_spec (min_atom_value m a) (min_atom_value m minval) _ eq_refl).
        { rewrite H. exists minval. cbn in inmin. split; [intuition|reflexivity]. }
        { rewrite H. exists a. cbn in inmin. split; [intuition|reflexivity]. }
  Qed.

  Lemma min_premise_spec (m : model) (s : premises) :
    (forall x, LevelExprSet.In x s -> min_premise m s ≤ min_atom_value m x) /\
    (exists x, LevelExprSet.In x s /\ min_premise m s = min_atom_value m x).
  Proof.
    now apply min_premise_spec_aux.
  Qed.

  Lemma min_premise_subset (m : model) (s s' : premises) :
    LevelExprSet.Subset s s' ->
    min_premise m s' ≤ min_premise m s.
  Proof.
    intros sub.
    have [has [mins [ins eqs]]] := min_premise_spec m s.
    have [has' [mins' [ins' eqs']]] := min_premise_spec m s'.
    specialize (sub _ ins). specialize (has' _ sub).
    now rewrite eqs.
  Qed.


  Lemma min_premise_add_infers m prems le lev :
    level_value m le.1 = Some lev ->
    forall z, min_premise m prems = Some z ->
    exists z', min_premise m (add le prems) = Some z' /\
      ((z' = lev - le.2 /\ z' <= z) \/ z' = z).
  Proof.
    intros hlev z hmin.
    have [hle [min' [hin hm]]] := min_premise_spec m (add le prems).
    have [hle' [min'' [hin' hm']]] := min_premise_spec m prems.
    move/LevelExprSet.add_spec: hin => [heq|hin].
    - noconf heq. destruct le as [le k].
      rewrite /min_atom_value hlev in hm.
      eexists; split => //; trea. left.
      specialize (hle min''). forward hle.
      { rewrite LevelExprSet.add_spec. now right. }
      rewrite hm -hm' hmin in hle. now depelim hle.
    - exists z. split => //. 2:right; reflexivity. rewrite hm -hmin hm'.
      move: (hle' _ hin). rewrite hmin. intros h; depelim h.
      rewrite H0 in hm.
      specialize (hle min''). forward hle. eapply LevelExprSet.add_spec. now right.
      rewrite hm in hle. rewrite -hm' hmin in hle. depelim hle.
      rewrite H0 -hm' hmin. f_equal. lia.
  Qed.

  Lemma min_premise_add {m le prems} : min_premise m (add le prems) =
    option_map2 Z.min (min_atom_value m le) (min_premise m prems).
  Proof.
    rewrite {1}/min_premise.
    have hs' := to_nonempty_list_spec (add le prems).
    destruct to_nonempty_list.
    have eqf : (fold_left (fun (min : option Z) (atom : LevelExpr.t) => option_map2 Z.min (min_atom_value m atom) min) l (min_atom_value m p)) =
      (option_map2 Z.min (min_atom_value m le) (min_premise m prems)).
    2:{ now rewrite eqf. }
    rewrite -(to_nonempty_list_spec' (add le prems)) in hs'. noconf hs'.
    rewrite fold_left_map. rewrite fold_left_comm_f. intros [] []; cbn; auto. lia_f_equal. unfold flip.
    have l := fold_left_impl_eq (min_atom_value m (to_nonempty_list (add le prems)).1) (min_atom_value m le)
      (List.map (min_atom_value m) (to_nonempty_list (add le prems)).2) (List.map (min_atom_value m) (LevelExprSet.elements prems)).
    rewrite l.
    intros x.
    { rewrite -!map_cons to_nonempty_list_spec' !in_map_iff.
      split.
      - move=> [] lk [] <-.
        rewrite -InA_In_eq.
        move/LevelExprSet.elements_spec1.
        rewrite LevelExprSet.add_spec.
        intros [->|inp].
        * exists le. split => //. now left.
        * exists lk. split => //. right. now apply InA_In_eq, LevelExprSet.elements_spec1.
      - intros [x' [<- hin]].
        exists x'. split => //. rewrite -InA_In_eq.
        eapply LevelExprSet.elements_spec1. rewrite LevelExprSet.add_spec.
        apply InA_In_eq in hin. depelim hin. now left.
        eapply LevelExprSet.elements_spec1 in hin. now right. }
    rewrite option_map2_comm.
    rewrite /min_premise.
    destruct (to_nonempty_list prems) eqn:he.
    rewrite fold_left_map.
    rewrite (fold_left_comm_f _ _ (List.map _ l0)). intros. apply option_map2_comm.
    rewrite -(fold_left_comm (option_map2 Z.min)).
    { intros. now rewrite -option_map2_assoc (option_map2_comm x y) option_map2_assoc. }
    rewrite -(to_nonempty_list_spec' prems) he; cbn.
    now rewrite option_map2_comm.
  Qed.

  Lemma min_premise_elim m (P : premises -> option Z -> Prop):
    (forall le, P (singleton le) (min_atom_value m le)) ->
    (forall prems acc le, P prems acc -> ~ LevelExprSet.In le prems -> P (add le prems) (option_map2 Z.min (min_atom_value m le) acc)) ->
    forall prems, P prems (min_premise m prems).
  Proof.
    intros hs hadd.
    eapply elim.
    - intros le. rewrite /min_premise.
      rewrite singleton_to_nonempty_list. cbn. apply hs.
    - intros le prems hp. now rewrite min_premise_add.
  Qed.

  Lemma min_premise_add_down {m} {prems : premises} {l k} :
    LevelExprSet.In (l, k + 1) prems ->
    forall z, min_premise m prems = Some z ->
        min_premise m (add (l, k) prems) = Some z.
  Proof.
    intros ine z hmin.
    have [hle [min' [hin hm]]] := min_premise_spec m (add (l, k) prems).
    have [hle' [min'' [hin' hm']]] := min_premise_spec m prems.
    move/LevelExprSet.add_spec: hin => [heq|hin].
    - noconf heq.
      specialize (hle (l, k + 1)).
      forward hle. eapply LevelExprSet.add_spec. now right.
      rewrite hm in hle.
      depelim hle. destruct level_value eqn:hl. noconf H0; noconf H1. lia. congruence.
      destruct level_value eqn:hl' => //.
      specialize (hle' _ ine). rewrite hmin in hle'; depelim hle'.
      now rewrite hl' in H1.
    - rewrite hm. specialize (hle' min' hin). rewrite hmin in hle'.
      depelim hle'. rewrite H0. f_equal. rewrite H0 in hm.
      specialize (hle min''). forward hle. eapply LevelExprSet.add_spec. now right.
      rewrite hm in hle. rewrite -hm' hmin in hle. depelim hle. lia.
  Qed.


  Lemma min_premise_singleton m u : min_premise m (singleton u) = min_atom_value m u.
  Proof.
    now rewrite /min_premise singleton_to_nonempty_list; cbn.
  Qed.

  Lemma min_atom_value_add m e x n :
    min_atom_value m e = Some x ->
    min_atom_value m (add_expr n e) = Some (x - n)%Z.
  Proof.
    rewrite /min_atom_value. destruct e. cbn.
    destruct level_value => //. intros [= <-].
    f_equal. lia.
  Qed.


  Lemma min_atom_value_add_inv m e x n :
    min_atom_value m (add_expr n e) = Some x ->
    min_atom_value m e = Some (x + n)%Z.
  Proof.
    rewrite /min_atom_value. destruct e. cbn.
    destruct level_value => //. intros [= <-].
    f_equal. lia.
  Qed.

  Lemma min_premise_add_prems {m n prems z} : min_premise m prems = Some z -> min_premise m (add_prems n prems) = Some (z - n)%Z.
  Proof.
    revert z.
    eapply min_premise_elim.
    - intros le hm.
      destruct le as [concl k].
      rewrite add_prems_singleton min_premise_singleton.
      apply min_atom_value_add.
    - intros prems' acc le ih nle z hm.
      destruct acc; cbn in hm. 2:{ destruct (min_atom_value m le); cbn in hm; congruence. }
      specialize (ih _ eq_refl).
      rewrite add_prems_add min_premise_add.
      destruct (min_atom_value m le) eqn:hm'; cbn in hm => //. noconf hm.
      apply (min_atom_value_add _ _ _ n) in hm'.
      rewrite ih hm'. cbn. f_equal. lia.
  Qed.

  Lemma min_premise_add_prems_inv {m n prems z} : min_premise m (add_prems n prems) = Some z ->
    min_premise m prems = Some (z + n)%Z.
  Proof.
    revert z.
    pattern prems.
    set (P := (fun n0 hm =>
    forall z : Z,
      min_premise m (add_prems n n0) = Some z -> hm = Some (z + n)%Z)).
    apply (@min_premise_elim _ P); subst P; cbn.
    - intros le z hm.
      destruct le as [concl k].
      rewrite add_prems_singleton min_premise_singleton in hm.
      now apply min_atom_value_add_inv.
    - intros prems' acc le ih nle z.
      rewrite add_prems_add min_premise_add.
      destruct (min_premise m (add_prems n prems')) eqn:he => //=.
      * destruct (min_atom_value m (add_expr n le)) eqn:ha => //=.
        intros [= <-].
        eapply min_atom_value_add_inv in ha. rewrite ha.
        specialize (ih _ eq_refl). subst acc. cbn. lia_f_equal.
      *  destruct (min_atom_value m (add_expr n le)) eqn:ha => //=.
  Qed.

  Lemma premise_min_spec_aux s k :
    premise_min s = k ->
    (forall x, LevelExprSet.In x s -> (k <= x.2)%Z) /\
    (exists x, LevelExprSet.In x s /\ k = x.2).
  Proof.
    unfold premise_min.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    intros <-.
    induction l.
    - cbn.
      split. intros x [->|] => //. reflexivity.
      now exists p; split => //.
    - destruct IHl as [ha hex].
      split; intros.
      eapply (in_elt_inv x a [p]) in H as [<-|inih].
      cbn. rewrite fold_left_comm. lia. lia.
      specialize (ha _ inih).
      cbn. rewrite fold_left_comm. lia. lia.
      destruct hex as [minval [inmin ih]].
      cbn. rewrite fold_left_comm. lia.
      destruct (Z.leb_spec a.2 minval.2).
      exists a. split; [intuition|]. rewrite -ih in H. lia.
      exists minval.
      cbn in inmin; split; [intuition auto|]. lia.
  Qed.

  Lemma premise_min_spec (s : premises) :
    (forall x, LevelExprSet.In x s -> premise_min s <= x.2) /\
    (exists x, LevelExprSet.In x s /\ premise_min s = x.2).
  Proof.
    now apply premise_min_spec_aux.
  Qed.


  Definition to_positive (s : premises) : premises :=
    let z := premise_min s in
    add_prems (- z) s.

  Lemma to_positive_spec (s : premises) : forall l k, LevelExprSet.In (l, k) s <-> LevelExprSet.In (l, k - premise_min s) (to_positive s).
  Proof.
    intros l k; rewrite /to_positive.
    rewrite In_add_prems. split.
    - move=> hin; exists (l, k). split => //. rewrite /add_expr; lia_f_equal.
    - move=> [] [l' k'] [] hin heq. noconf heq.
      now have -> : k = k' by lia.
  Qed.

  Lemma to_positive_spec_2 (s : premises) : forall l k, LevelExprSet.In (l, k) (to_positive s) <-> LevelExprSet.In (l, k + premise_min s) s.
  Proof.
    intros l k; rewrite /to_positive.
    rewrite In_add_prems. split.
    - move=> [] [l' k'] [] hin heq. noconf heq.
      now have <- : k' = - premise_min s + k' + premise_min s by lia.
    - move=> hin; exists (l, k + premise_min s). split => //.
      cbn. lia_f_equal.
  Qed.

  Lemma to_positive_pos (s : premises) : forall l k, LevelExprSet.In (l, k) (to_positive s) -> k >= 0.
  Proof.
    move=> l k /to_positive_spec_2.
    move: (premise_min_spec s) => [] + hex hs; move /(_ _ hs). cbn. lia.
  Qed.

  Lemma premise_max_spec_aux s k :
    premise_max s = k ->
    (forall x, LevelExprSet.In x s -> x.2 <= k) /\
    (exists x, LevelExprSet.In x s /\ k = x.2).
  Proof.
    unfold premise_max.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    intros <-.
    induction l.
    - cbn.
      split. intros x [->|] => //. reflexivity.
      now exists p; split => //.
    - destruct IHl as [ha hex].
      split; intros.
      eapply (in_elt_inv x a [p]) in H as [<-|inih].
      cbn. rewrite fold_left_comm. lia. lia.
      specialize (ha _ inih).
      cbn. rewrite fold_left_comm. lia. lia.
      destruct hex as [maxval [inmin ih]].
      cbn. rewrite fold_left_comm. lia.
      destruct (Z.leb_spec a.2 maxval.2).
      exists maxval. cbn in inmin; split; [intuition auto|].
      lia.
      exists a. split; [intuition|]. rewrite -ih in H. cbn in inmin.
      lia.
  Qed.

  Lemma premise_max_spec (s : premises) :
    (forall x, LevelExprSet.In x s -> x.2 <= premise_max s) /\
    (exists x, LevelExprSet.In x s /\ premise_max s = x.2).
  Proof.
    now apply premise_max_spec_aux.
  Qed.

  Lemma premise_min_subset (s s' : premises) :
    LevelExprSet.Subset s s' ->
    (premise_min s' <= premise_min s).
  Proof.
    intros sub.
    have [has [mins [ins eqs]]] := premise_min_spec s.
    have [has' [mins' [ins' eqs']]] := premise_min_spec s'.
    specialize (sub _ ins). specialize (has' _ sub).
    lia.
  Qed.

  Import -(notations) LevelExprSet.

  Definition max_premise_value (m : model) (l : premises) : option Z :=
    let (hd, tl) := to_nonempty_list l in
    fold_left (fun min atom => option_map2 Z.max (levelexpr_value m atom) min) tl (levelexpr_value m hd).

  Lemma max_premise_value_spec_aux (m : model) s k :
    max_premise_value m s = Some k ->
    (forall x, LevelExprSet.In x s -> exists k', levelexpr_value m x = Some k' /\ Some k' ≤ Some k) /\
    (exists x, LevelExprSet.In x s /\ Some k = levelexpr_value m x).
  Proof.
    unfold max_premise_value.
    move: (to_nonempty_list_spec s).
    destruct (to_nonempty_list s). intros heq.
    setoid_rewrite In_elements. rewrite -heq. clear s heq.
    induction l in k |- *.
    - cbn.
      intros eq.
      split. intros x [->|] => //. exists k. split => //. reflexivity.
      now exists p; split => //.
    - cbn. rewrite fold_left_comm. intros; apply fold_comm_assoc.
      intros heq. apply max_opt_spec in heq as [y' [z' [eqa [eqf ->]]]].
      specialize (IHl _ eqf). destruct IHl as [ha hex].
      split; intros.
      eapply (in_elt_inv x a [p]) in H as [<-|inih].
      { exists y'; intuition eauto. constructor; lia. }
      { specialize (ha _ inih) as [k' []]. exists k'; intuition eauto. constructor. depelim H0; lia. }
      destruct hex as [maxval [inmax ih]].
      cbn.
      destruct (Z.leb_spec z' y').
      exists a. split; [intuition|]. rewrite eqa. f_equal. lia.
      exists maxval. cbn in inmax; split; [intuition auto|]. rewrite -ih. f_equal; lia.
  Qed.

  Lemma max_premise_value_spec (m : model) (s : premises) k :
    max_premise_value m s = Some k ->
    (forall x, LevelExprSet.In x s -> exists k', levelexpr_value m x = Some k' /\ Some k' ≤ Some k) /\
    (exists x, LevelExprSet.In x s /\ Some k = levelexpr_value m x).
  Proof.
    apply (max_premise_value_spec_aux m s).
  Qed.

  Lemma min_premise_pos_spec {m prem k} :
    min_premise m prem = Some k ->
    forall x, LevelExprSet.In x prem -> Some (x.2 + k)%Z ≤ levelexpr_value m x.
  Proof.
    pose proof (min_premise_spec m prem) as [amin [exmin [inminpre eqminpre]]].
    intros hprem x hin.
    specialize (amin _ hin).
    unfold min_atom_value in amin.
    destruct x as [l k']; cbn in *. unfold levelexpr_value; cbn.
    destruct (level_value m l) eqn:he.
    - depelim amin.
      rewrite H0 in hprem. depelim hprem. constructor. lia.
      constructor.
      rewrite H in hprem; depelim hprem.
    - depelim amin. rewrite H in hprem. depelim hprem.
  Qed.

  Record model_extension W m m' :=
    { model_ext_le : m ⩽ m';
      model_ext_same_domain : model_same_domain m m';
      model_ext_same_outside : model_map_outside W m m' }.

  #[local] Instance model_ext_reflexive W : Reflexive (model_extension W).
  Proof.
    intros m; split; reflexivity.
  Qed.

  #[local] Instance model_ext_transitive W : Transitive (model_extension W).
  Proof.
    intros m m' m'' h h'; split; (etransitivity; [apply h|apply h']).
  Qed.

  Lemma model_extension_weaken W W' m m' :
    W ⊂_lset W' ->
    model_extension W m m' ->
    model_extension W' m m'.
  Proof.
    intros leW []; split => //.
    eapply model_map_outside_weaken; tea.
  Qed.

  Lemma model_ext_trans_weaken W W' m m' m'' :
    W ⊂_lset W' ->
    model_extension W m m' ->
    model_extension W' m' m'' ->
    model_extension W' m m''.
  Proof.
    intros leW mext mext'. eapply model_extension_weaken in mext; tea.
    now etransitivity; tea.
  Qed.

  Definition model_of V (m : model) :=
    forall k, LevelSet.In k V -> LevelMap.In k m.

  Definition defined_model_of V (m : model) :=
    forall l, LevelSet.In l V -> exists k, LevelMap.MapsTo l (Some k) m.

  Definition only_model_of V (m : model) :=
    forall k, LevelSet.In k V <-> exists x, LevelMap.MapsTo k x m.

  Lemma only_model_of_model_of {V m} : only_model_of V m -> model_of V m.
  Proof.
    intros om l. move/om. intros [k hm]; now exists k.
  Qed.

  Coercion only_model_of_model_of : only_model_of >-> model_of.

  Lemma level_value_above_MapsTo m l k : level_value_above m l k -> exists k', LevelMap.MapsTo l k' m /\ (Some k ≤ k').
  Proof.
    unfold level_value_above.
    destruct level_value eqn:hl => //.
    move/Z.leb_le => hle; exists (Some z).
    eapply level_value_MapsTo' in hl. split => //. now constructor.
  Qed.

  Lemma level_value_above_MapsTo' m l k k' : LevelMap.MapsTo l k' m -> (Some k ≤ k') -> level_value_above m l k.
  Proof.
    unfold level_value_above.
    intros H; apply LevelMap.find_1 in H. rewrite /level_value H.
    destruct k'. intros h; depelim h.
    now apply Z.leb_le. intros h; depelim h.
  Qed.

  Lemma level_value_add m l k : level_value (LevelMap.add l (Some k) m) l = Some k.
  Proof.
    rewrite /level_value LevelMapFact.F.add_eq_o //.
  Qed.

  Definition declared_model_level (m : model) l := LevelMap.In l m.

  Definition update_model_same_domain {m l k} :
    declared_model_level m l ->
    model_same_domain m (update_model m l k).
  Proof.
    unfold update_model, declared_model_level.
    intros hin x.
    rewrite LevelMapFact.F.add_in_iff. intuition auto. now subst.
  Qed.

  Definition update_model_outside {m w l k} :
    model_map_outside (LevelSet.add l w) m (update_model m l k).
  Proof.
    unfold update_model, model_map_outside.
    intros l'. rewrite LevelSet.add_spec.
    intros hin k'.
    rewrite LevelMapFact.F.add_neq_mapsto_iff //.
    intros heq. red in heq; subst l'. apply hin. now left.
  Qed.

  Lemma min_atom_value_levelexpr_value m l a lv : min_atom_value m l = Some a -> levelexpr_value m l = Some lv ->
    (a = lv - l.2).
  Proof.
    destruct l as [l k]; cbn. unfold levelexpr_value. cbn. destruct level_value => //.
    intros [= <-] [= <-]. lia.
  Qed.

  Lemma model_of_update w m l k : model_of w m -> model_of (LevelSet.add l w) (update_model m l k).
  Proof.
    rewrite /model_of => hint l'. rewrite LevelSet.add_spec.
    intros [->|hadd].
    - exists (Some k). now apply LevelMap.add_1.
    - specialize (hint _ hadd). unfold update_model.
      destruct hint as [x hx].
      destruct (eqb_spec l l'). subst.
      now exists (Some k); apply LevelMap.add_1.
      now exists x; eapply LevelMap.add_2.
  Qed.

  #[export] Instance model_map_outside_proper : Proper (LevelSet.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) model_map_outside.
  Proof.
    intros ? ? eqcl ? ? eqm ? ? eqs.
    unfold model_map_outside.
    setoid_rewrite eqcl. now setoid_rewrite eqm; setoid_rewrite eqs.
  Qed.

  #[export] Instance proper_levelexprset_levels : Proper (LevelExprSet.Equal ==> LevelSet.Equal)
    levels.
  Proof.
    intros s s' eq l.
    rewrite !levels_spec.
    firstorder eauto.
  Qed.

  Lemma min_premise_spec' {m prems z} : min_premise m prems = Some z ->
    (forall l k, LevelExprSet.In (l, k) prems ->
    exists v, level_value m l = Some v /\ z <= (v - k))%Z.
  Proof.
    intros hmin.
    have [hall hhmin'] := min_premise_spec m prems.
    intros l k hin; specialize (hall _ hin). rewrite hmin in hall.
    depelim hall. destruct level_value => //. noconf H0. exists z0. split => //.
  Qed.

  Lemma min_premise_pres {m m'} prems : m ⩽ m' -> min_premise m prems ≤ min_premise m' prems.
  Proof.
    intros ext.
    destruct (min_premise m prems) eqn:hmin.
    have leq := min_premise_spec' hmin. 2:constructor.
    have [leq' e'] := min_premise_spec m' prems.
    destruct (min_premise_spec m prems) as [_ [minz [inminz eqminz]]].
    rewrite hmin in eqminz.
    rewrite eqminz. destruct e' as [min' []]. rewrite H0.
    transitivity (min_atom_value m min').
    2:{ unfold min_atom_value. destruct min'.
      unfold level_value. destruct (LevelMap.find t0 m) eqn:hfind. 2:constructor.
      apply LevelMap.find_2 in hfind. apply ext in hfind as [k' [hfind hle]].
      apply LevelMap.find_1 in hfind. rewrite hfind. depelim hle; constructor. lia.
      }
    destruct min'. specialize (leq _ _ H) as [? []].
    unfold min_atom_value at 2. rewrite H1. rewrite -eqminz. constructor. lia.
  Qed.

  Lemma level_value_above_mon m m' l k : m ⩽ m' -> level_value_above m l k -> level_value_above m' l k.
  Proof.
    intros ext; move/level_value_above_MapsTo => [v [hm hleq]].
    eapply ext in hm. destruct hm as [v' [hm' leq']].
    eapply level_value_above_MapsTo'; tea. transitivity v => //.
  Qed.

  Lemma model_of_subset V V' m :
    model_of V m -> V' ⊂_lset V -> model_of V' m.
  Proof.
    intros ih hv k. specialize (ih k).
    now move/hv.
  Qed.

  Instance only_model_of_proper : Proper (LevelSet.Equal ==> LevelMap.Equal ==> iff) only_model_of.
  Proof.
    intros ? ? eq ? ? eq'.
    rewrite /only_model_of. now setoid_rewrite eq; setoid_rewrite eq'.
  Qed.

  Lemma only_model_of_eq V V' m :
    only_model_of V m -> V' =_lset V -> only_model_of V' m.
  Proof.
    intros ih hv k. now rewrite hv.
  Qed.

  Lemma check_model_ext {cls w init_model m w' m'} :
    check_model cls (w, m) = Some (w', m') ->
    strictly_updates cls w init_model m ->
    strictly_updates cls w' init_model m' /\ w ⊂_lset w'.
  Proof.
    move/check_model_updates_spec.
    intros ih cls'. eapply ih in cls' as [su incl]. split => //.
    eapply strictly_updates_weaken; tea. clsets.
  Qed.

  Lemma check_model_updates_spec_empty {cls m w m'} :
    check_model cls (LevelSet.empty, m) = Some (w, m') ->
    strictly_updates cls w m m'.
  Proof.
    move/check_model_spec => [w' [su ->]].
    setoid_replace (LevelSet.union LevelSet.empty w') with w' => //.
    intros x; lsets.
  Qed.

  Lemma check_model_is_model {W cls m} :
    check_model cls (W, m) = None <-> is_model cls m.
  Proof.
    now rewrite check_model_None.
  Qed.

  Lemma check_model_update {W cls m wm'} :
    model_of (clauses_conclusions cls) m ->
    model_of W m ->
    check_model cls (W, m) = Some wm' -> ~~ is_model cls m /\ m ⩽ wm'.2.
  Proof.
    intros mof tot.
    destruct wm'.
    move/check_model_spec => [w'' [su ->]]. cbn. split.
    now eapply strictly_updates_invalid.
    now eapply strictly_updates_ext.
  Qed.

  Lemma min_premise_max_premise m prem k :
    min_premise m prem = Some k ->
    exists k', max_premise_value m prem = Some k'.
  Proof.
    unfold min_premise, max_premise_value.
    destruct to_nonempty_list.
    assert (forall l k, fold_left
    (fun (min : option Z) (atom : LevelExpr.t) =>
    option_map2 Z.min (let '(l0, k0) := atom in match level_value m l0 with
                                                | Some val => Some (val - k0)%Z
                                                | None => None
                                                end) min)
    l None =
      Some k -> False).
    { clear. induction l; cbn => //. cbn in *.
      destruct a, level_value; cbn; auto. }
    assert
      (forall x y, fold_left (fun (min : option Z) (atom : LevelExpr.t) => option_map2 Z.min (min_atom_value m atom) min) l (Some x) = Some k ->
  exists k',
    fold_left (fun (min : option Z) (atom : LevelExpr.t) => option_map2 Z.max (levelexpr_value m atom) min) l (Some y) = Some k').
    { induction l; cbn.
      - intros x y [= <-]. now eexists.
      - intros x y.
        unfold min_atom_value, levelexpr_value, level. destruct a; cbn.
        destruct level_value => //=. eapply IHl. cbn. intros H'. exfalso.
        eapply H; eauto. }
    - unfold min_atom_value, levelexpr_value, level. destruct p; cbn.
      destruct level_value => //=. apply H0.
      intros; exfalso. now eapply H.
  Qed.

  Lemma model_of_value_None W m l :
    model_of W m ->
    LevelSet.In l W ->
    LevelMap.find l m = None -> False.
  Proof.
    intros tm inw. specialize (tm l inw) as [v hm].
    rewrite /level_value.
    now rewrite (LevelMap.find_1 hm).
  Qed.

  Lemma defined_model_of_value_None W m l :
    defined_model_of W m ->
    LevelSet.In l W ->
    level_value m l = None -> False.
  Proof.
    intros tm inw. specialize (tm l inw) as [v hm].
    rewrite /level_value.
    now rewrite (LevelMap.find_1 hm).
  Qed.

  #[export] Instance check_model_aux_proper_eq : Proper (Clauses.Equal ==> Logic.eq ==> Logic.eq) check_model_aux.
  Proof.
    intros cls cls' eq.
    intros wm wm' eq'. subst wm'.
    unfold check_model_aux.
    now eapply ClausesOrd.fold_equal; tc.
  Qed.

  Lemma strictly_updates_trans {cls cls' W W' m m' m''} :
    strictly_updates cls W m m' ->
    strictly_updates cls' W' m' m'' ->
    strictly_updates (Clauses.union cls cls') (LevelSet.union W W') m m''.
  Proof.
    intros su su'.
    eapply trans_update; eapply strictly_updates_weaken; tea; clsets.
  Qed.

  Lemma check_model_is_update_of {cls cls' U W minit m m'} :
    is_update_of cls U minit m ->
    check_model cls' (U, m) = Some (W, m') ->
    strictly_updates (Clauses.union cls cls') W minit m' /\ U ⊂_lset W.
  Proof.
    rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:he.
    - intros ->. eapply LevelSetFact.is_empty_2 in he.
      eapply LevelSetProp.empty_is_empty_1 in he.
      have := check_model_proper cls' cls' (reflexivity cls') (U, m) (LevelSet.empty, m) => /fwd /fwd.
      split => //. intros h; depelim h. rewrite H => //.
      rewrite H0. intros [= ->]. destruct y as [W' m'']. destruct H as [eq eq']; cbn in *.
      move/check_model_updates_spec_empty: H1. rewrite eq -eq'. intros H; split => //. 2:lsets.
      eapply strictly_updates_weaken; tea. clsets.
    - intros hs. move/check_model_spec => [w'' [su ->]]. split; [|lsets].
      eapply strictly_updates_trans; tea.
  Qed.

  Lemma is_update_of_case cls W m m' :
    is_update_of cls W m m' ->
    (LevelSet.Empty W /\ m =m m') \/ strictly_updates cls W m m'.
  Proof.
    rewrite /is_update_of.
    destruct LevelSet.is_empty eqn:he.
    - intros ->. left => //. now eapply LevelSetFact.is_empty_2 in he.
    - intros H; now right.
  Qed.

  Lemma model_of_ext {W m m'} :
    model_of W m -> m ⩽ m' -> model_of W m'.
  Proof.
    intros mof ext.
    intros k hin. destruct (mof k hin). specialize (ext _ _ H) as [k' []]. now exists k'.
  Qed.

  Lemma defined_model_of_ext {W m m'} :
    defined_model_of W m -> m ⩽ m' -> defined_model_of W m'.
  Proof.
    intros mof ext.
    intros k hin. destruct (mof k hin). specialize (ext _ _ H) as [k' []].
    depelim H1. now exists y.
  Qed.

  Lemma is_update_of_ext {cls W m m'} : is_update_of cls W m m' -> m ⩽ m'.
  Proof.
    move/is_update_of_case => [].
    - intros [he%LevelSetProp.empty_is_empty_1]. red. setoid_rewrite H.
      move=> l k hm; exists k; split => //. reflexivity.
    - apply strictly_updates_ext.
  Qed.

  Lemma model_of_union {U V cls} : model_of U cls -> model_of V cls -> model_of (LevelSet.union U V) cls.
  Proof.
    intros hu hv x.
    rewrite LevelSet.union_spec; move => [] hin.
    now apply hu. now apply hv.
  Qed.

  Instance model_of_proper : Proper (LevelSet.Equal ==> LevelMap.Equal ==> iff) model_of.
  Proof.
    intros ? ? H ? ? H'. unfold model_of. setoid_rewrite H.
    now setoid_rewrite H'.
  Qed.

  Instance defined_model_of_proper : Proper (LevelSet.Equal ==> LevelMap.Equal ==> iff) defined_model_of.
  Proof.
    unfold defined_model_of; solve_proper.
  Qed.

  Lemma defined_model_of_union {U V cls} :
    defined_model_of U cls ->
    defined_model_of V cls ->
    defined_model_of (LevelSet.union U V) cls.
  Proof.
    intros hu hv x.
    rewrite LevelSet.union_spec; move => [] hin.
    now apply hu. now apply hv.
  Qed.

  Lemma model_of_union_inv U V cls : model_of (LevelSet.union U V) cls -> model_of U cls /\ model_of V cls.
  Proof.
    rewrite /model_of.
    setoid_rewrite LevelSet.union_spec. firstorder.
  Qed.

  Lemma defined_model_of_union_inv U V cls :
    defined_model_of (LevelSet.union U V) cls ->
    defined_model_of U cls /\ defined_model_of V cls.
  Proof.
    rewrite /defined_model_of.
    setoid_rewrite LevelSet.union_spec. firstorder.
  Qed.

  Lemma strictly_updates_model_of_gen cls W m m' :
    strictly_updates cls W m m' ->
    forall W', model_of W' m -> model_of (LevelSet.union W' W) m'.
  Proof.
    clear. move: W m m'.
    apply: strictly_updates_elim.
    { solve_proper. }
    - intros m cl m' incl su W' tot x.
      destruct cl as [prems [concl cl]].
      destruct su as [minv [hmin ? heq]]. setoid_rewrite heq.
      setoid_rewrite LevelMapFact.F.add_in_iff. cbn.
      destruct (Level.eq_dec concl x).
      { now left. }
      { rewrite LevelSet.union_spec; intros [hin|hin].
        { eapply tot in hin as [wit mt]. right; exists wit. assumption. }
        { eapply LevelSet.singleton_spec in hin. red in hin; subst. congruence. } }
    - intros ls ls' m m' m'' su ihsu su' ihsu' W' tot.
      eapply ihsu in tot. eapply ihsu' in tot.
      eapply model_of_subset; tea. intros x; lsets.
  Qed.

  Lemma model_of_empty m : model_of LevelSet.empty m.
  Proof. intros x; now move/LevelSet.empty_spec. Qed.

  Lemma strictly_updates_total_model {cls W m m'} :
    strictly_updates cls W m m' ->
    model_of W m'.
  Proof.
    move/strictly_updates_model_of_gen/(_ LevelSet.empty)/(_ (model_of_empty _)).
    rewrite LevelSetProp.empty_union_1 //. lsets.
  Qed.

  Lemma strictly_updates_only_model_gen cls W m m' :
    strictly_updates cls W m m' ->
    forall W', only_model_of W' m -> only_model_of (LevelSet.union W' W) m'.
  Proof.
    move: W m m'; apply: strictly_updates_elim.
    { solve_proper. }
    - intros m cl m' incl su W' tot x.
      destruct cl as [prems [concl cl]].
      destruct su as [minv [hmin ? heq]]. setoid_rewrite heq.
      setoid_rewrite LevelMapFact.F.add_mapsto_iff. cbn.
      case: (Level.eq_dec concl x).
      { move=> ->. rewrite LevelSet.union_spec LevelSet.singleton_spec.
        firstorder; exists (Some (cl + minv)); left; split => //. }
      { rewrite LevelSet.union_spec LevelSet.singleton_spec /LevelSet.E.eq.
        firstorder. congruence. }
    - intros ls ls' m m' m'' su ihsu su' ihsu' W' tot.
      eapply ihsu in tot. eapply ihsu' in tot.
      eapply only_model_of_eq; tea. intros x; lsets.
  Qed.

  Lemma is_update_of_total_model cls W m m' : is_update_of cls W m m' -> model_of W m'.
  Proof.
    move/is_update_of_case => [].
    - intros [he eq].
      rewrite /model_of. lsets.
    - eapply strictly_updates_total_model.
  Qed.

  Lemma strict_update_modify m cl m' : strict_update m cl m' ->
    exists k, LevelMap.Equal m' (LevelMap.add (clause_conclusion cl) k m).
  Proof.
    rewrite /strict_update.
    destruct cl as [prems [concl k]].
    intros [v [hmin hab eq]]. now exists (Some (k + v)).
  Qed.

  Lemma strictly_updates_model_of {cls W m m'} :
    strictly_updates cls W m m' -> model_of W m'.
  Proof.
    move/strictly_updates_model_of_gen/(_ LevelSet.empty).
    rewrite LevelSetProp.empty_union_1. lsets.
    intros H; apply H. apply model_of_empty.
  Qed.

  Lemma strictly_updates_modify {cls W m m'} :
    strictly_updates cls W m m' ->
    forall l k, LevelMap.MapsTo l k m' -> LevelSet.In l W \/ LevelMap.MapsTo l k m.
  Proof.
    induction 1.
    + eapply strict_update_modify in H1 as [k eq].
      intros l k'. rewrite H0. rewrite LevelSet.singleton_spec.
      rewrite eq.
      rewrite LevelMapFact.F.add_mapsto_iff.
      intros [[]|] => //. red in H0; subst.
      now left. now right.
    + intros. eapply IHstrictly_updates2 in H2 as [].
      left; lsets.
      eapply IHstrictly_updates1 in H2 as []. left; lsets.
      now right.
  Qed.

  Lemma strictly_updates_modify_inv {cls W m m'} :
    strictly_updates cls W m m' ->
    forall l k, LevelMap.MapsTo l k m -> LevelSet.In l W \/ LevelMap.MapsTo l k m'.
  Proof.
    induction 1.
    + eapply strict_update_modify in H1 as [k eq].
      intros l k'. rewrite H0 LevelSet.singleton_spec.
      rewrite eq.
      rewrite LevelMapFact.F.add_mapsto_iff.
      intros hm. unfold Level.eq.
      destruct (Level.eq_dec l (clause_conclusion cl)). subst. now left.
      right. right. auto.
    + intros. eapply IHstrictly_updates1 in H2 as [].
      left; lsets.
      eapply IHstrictly_updates2 in H2 as []. left; lsets.
      now right.
  Qed.

  Lemma strictly_updates_outside cls W m m' :
    strictly_updates cls W m m' -> model_map_outside W m m'.
  Proof.
    move=> su.
    have lr := strictly_updates_modify su.
    have rl := strictly_updates_modify_inv su.
    intros l nin k.
    split; intros.
    - apply rl in H as [] => //.
    - apply lr in H as [] => //.
  Qed.

  Definition check_model_invariants cls w m w' m' (modified : bool) :=
    if modified then
      [/\ w ⊂_lset w',
          w' ⊂_lset (LevelSet.union w (clauses_conclusions cls)),
          exists cl,
            let cll := (level (concl cl)) in
            [/\ Clauses.In cl cls, ~~ valid_clause m cl,
            LevelSet.In cll w' &
            opt_le Z.lt (level_value m cll) (level_value m' cll)],
            model_extension w' m m' &
            model_of w' m']
    else (w, m) = (w', m') /\ model_of w m.

  Import Corelib.Init.Logic.

  #[export] Instance check_model_invariants_proper :
    Proper (Clauses.Equal ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) check_model_invariants.
  Proof.
    intros cls cls' eqcls.
    repeat intro; subst.
    unfold check_model_invariants.
    destruct y3 => //.
    now setoid_rewrite <-eqcls.
  Qed.

  Lemma check_model_has_invariants {cls w m w' m'} :
    model_of (clauses_conclusions cls) m ->
    model_of w m ->
    check_model cls (w, m) = Some (w', m') ->
    check_model_invariants cls w m w' m' true.
  Proof.
    intros mof tot.
    move/check_model_spec => [w'' [su eq]].
    cbn. split.
    - lsets.
    - apply strictly_updates_incl in su. lsets.
    - clear -su eq.
      move: w'' m m' su w' eq; apply: strictly_updates_elim.
      { intros ? ? meq ? ? -> ? ? ->. rw meq. reflexivity. }
      * move=> m cl m' incl su w' eq. exists cl. split => //. now eapply strict_update_invalid.
        unfold clause_conclusion. rewrite eq. rewrite /clause_conclusion. lsets.
        destruct cl as [prems [concl k]].
        destruct su as [minp [hin hnabove habove]].
        move: hnabove habove. rewrite /level_value_above.
        cbn. destruct level_value eqn:hv => //; try constructor.
        intros hle. intros ->. rewrite level_value_add. constructor.
        move/negbTE: hle. lia.
      * move=> ls ls' > su ihsu su' ihsu' w' eq. specialize (ihsu _ (reflexivity _)) as [cl []].
        exists cl. split => //. lsets.
        apply strictly_updates_ext in su'.
        depelim H2; rewrite ?H3. 2:{ rewrite H2; constructor. }
        eapply level_value_MapsTo', su' in H4 as [k' [map le]].
        eapply level_value_MapsTo in map. rewrite map. depelim le. constructor; lia.
    - constructor. now eapply strictly_updates_ext.
      clear -mof su.
      induction su.
      * move: H1; unfold strict_update. destruct cl as [prems [concl k]].
        intros [v [hmi nabove eqm]]. intros l. rewrite eqm.
        rewrite LevelMapFact.F.add_in_iff. specialize (mof l).
        rewrite clauses_conclusions_spec in mof. firstorder.
      * specialize (IHsu1 mof). transitivity m' => //.
        apply IHsu2. intros l hin. specialize (mof _ hin). now apply IHsu1 in mof.
      * eapply model_map_outside_weaken. now eapply strictly_updates_outside. lsets.
    - eapply strictly_updates_model_of_gen in su; tea. now rewrite eq.
  Qed.

  Definition infers_atom (m : model) (l : Level.t) (k : Z) := Some k ≤ level_value m l.

  Lemma infer_atom_downward {m l k k'} :
    infers_atom m l k ->
    (k' <= k) ->
    infers_atom m l k'.
  Proof.
    rewrite /infers_atom.
    intros infa le.
    transitivity (Some k) => //. now constructor.
  Qed.

  Lemma infers_atom_le {m m' l k} :
    infers_atom m l k ->
    m ⩽ m' ->
    infers_atom m' l k.
  Proof.
    rewrite /infers_atom.
    intros infa le.
    depelim infa. eapply level_value_MapsTo' in H0.
    eapply le0 in H0 as [k' [hm hle]].
    rewrite (level_value_MapsTo hm). depelim hle; constructor; lia.
  Qed.

  Lemma infers_atom_mapsto m l k : infers_atom m l k <->
    exists k', LevelMap.MapsTo l k' m /\ (Some k ≤ k').
  Proof.
    rewrite /infers_atom; split.
    - intros hle; depelim hle.
      eapply level_value_MapsTo' in H0. exists (Some y). split => //.
      now constructor.
    - intros [k' [hm hle]].
      eapply level_value_MapsTo in hm. now rewrite hm.
  Qed.

Lemma is_update_of_empty cls m :
    is_update_of cls LevelSet.empty m m.
  Proof.
    unfold is_update_of.
    rewrite LevelSetFact.is_empty_1 //. lsets.
  Qed.

  Lemma strictly_updates_W_eq cls W init m W' :
    LevelSet.Equal W W' ->
    strictly_updates cls W init m ->
    strictly_updates cls W' init m.
  Proof. now intros ->. Qed.

  Lemma strictly_updates_clauses_W cls cls' W init m W' :
    Clauses.Subset cls cls' ->
    LevelSet.Equal W W' ->
    strictly_updates cls W init m ->
    strictly_updates cls' W' init m.
  Proof. intros hsub ->. now apply strictly_updates_weaken. Qed.

  Lemma strictly_updates_is_update_of cls W init m cls' W' m' :
    strictly_updates cls W init m ->
    is_update_of cls' W' m m' ->
    strictly_updates (Clauses.union cls cls') (LevelSet.union W W') init m'.
  Proof.
    move=> su /is_update_of_case; intros [[empw eq]|su'].
    rewrite <- eq. eapply (strictly_updates_weaken cls). clsets.
    eapply strictly_updates_W_eq; tea. lsets.
    eapply trans_update; tea; eapply strictly_updates_weaken; tea; clsets.
  Qed.

  Definition restrict_model W (m : model) :=
    LevelMapFact.filter (fun l k => LevelSet.mem l W) m.

  Lemma restrict_model_spec W m :
    forall l k, LevelMap.MapsTo l k (restrict_model W m) <-> LevelMap.MapsTo l k m /\ LevelSet.In l W.
  Proof.
    intros l k; rewrite /restrict_model.
    now rewrite LevelMapFact.filter_iff LevelSet.mem_spec.
  Qed.

  (* Updates the entries in m with the values in m' if any *)
  Definition model_update (m m' : model) : model :=
    LevelMap.mapi (fun l k =>
      match LevelMap.find l m' with
      | Some k' => k'
      | None => k
      end) m.

  Instance model_update_proper : Proper (LevelMap.Equal ==> LevelMap.Equal ==> LevelMap.Equal) model_update.
  Proof.
    intros ? ? eq ? ? eq'.
    rewrite /model_update.
    apply LevelMapFact.F.Equal_mapsto_iff.
    intros k e.
    rewrite LevelMapFact.F.mapi_mapsto_iff. now intros ? ? ? ->.
    rewrite LevelMapFact.F.mapi_mapsto_iff. now intros ? ? ? ->.
    firstorder. exists x1. rewrite H. now rewrite -eq eq'.
    rewrite H. exists x1. now rewrite eq -eq'.
  Qed.

  Lemma model_update_spec m m' :
    forall l k, LevelMap.MapsTo l k (model_update m m') <->
      (~ LevelMap.In l m' /\ LevelMap.MapsTo l k m) \/
      (LevelMap.MapsTo l k m' /\ LevelMap.In l m).
  Proof.
    intros l k; split.
    - unfold model_update => hl.
      eapply LevelMapFact.F.mapi_inv in hl as [a [k' [-> [eqk mt]]]].
      move: eqk; elim: (find_spec l m').
      + intros ? hm <-. right; split => //. now exists a.
      + intros nin ->. left. split => //.
    - intros [[nin hm]|[inm' inm]].
      * eapply LevelMapFact.F.mapi_mapsto_iff. now intros x y e ->.
        elim: (find_spec l m').
        + intros k0 hm'. elim nin. now exists k0.
        + intros _. exists k. split => //.
      * eapply LevelMapFact.F.mapi_mapsto_iff. now intros x y e ->.
        elim: (find_spec l m').
        + intros k0 hm'. destruct inm as [a inm]. exists a. split => //.
          now eapply LevelMapFact.F.MapsTo_fun in inm'; tea.
        + intros nin; elim nin. now exists k.
  Qed.

  Lemma model_update_restrict m W : model_update m (restrict_model W m) =m m.
  Proof.
    apply LevelMapFact.F.Equal_mapsto_iff. intros l k.
    rewrite model_update_spec.
    split => //.
    - intros [[nin hk]|[hr inm]] => //.
      now eapply restrict_model_spec in hr.
    - intros hm.
      destruct (find_spec l (restrict_model W m)).
      + right. apply restrict_model_spec in H as [hm' hw].
        split. eapply LevelMapFact.F.MapsTo_fun in hm; tea. subst. apply restrict_model_spec; split => //.
        now exists k.
      + left. split => //.
  Qed.


  Lemma min_premise_preserved {m m'} {prems : premises} :
    (forall x, LevelSet.In x (levels prems) -> level_value m x = level_value m' x) ->
    min_premise m prems = min_premise m' prems.
  Proof.
    intros hcl.
    unfold min_premise.
    funelim (to_nonempty_list prems). bang. clear H.
    rw_in levels_spec hcl.
    have -> : min_atom_value m e = min_atom_value m' e.
    { destruct e as [k l'].
      rewrite /min_atom_value. rewrite -hcl //.
      exists l'.
      apply LevelExprSet.elements_spec1. rewrite e0. now left. }
    have cl' : forall x, (exists k, InA eq (x, k) l) -> level_value m x = level_value m' x.
    { intros x [k ina]. apply hcl. exists k. apply LevelExprSet.elements_spec1. rewrite e0. now right. }
    clear hcl Heqcall e0.
    generalize (min_atom_value m' e).
    induction l; cbn; auto.
    have -> : min_atom_value m a = min_atom_value m' a.
    { destruct a as [k l'].
      rewrite /min_atom_value. rewrite cl' //.
      exists l'. now left. }
    intros o.
    apply IHl.
    intros x [k l']. apply cl'. exists k. now right.
  Qed.

  Lemma min_premise_restrict m W (prems : premises) v :
    (forall l k, LevelExprSet.In (l, k) prems -> LevelSet.In l W) ->
    min_premise (restrict_model W m) prems = Some v ->
    min_premise m prems = Some v.
  Proof.
    intros hin.
    rewrite (@min_premise_preserved _ m) //.
    move=> x. rewrite levels_spec => [] [k] /hin inW.
    apply levelmap_level_value_eq => k'.
    rewrite restrict_model_spec. firstorder.
  Qed.

  Lemma model_of_model_update W m m' :
    model_of W m ->
    model_of W (model_update m m').
  Proof.
    intros hm l hin.
    move/hm: hin => [k hin].
    red. rw model_update_spec.
    destruct (LevelMapFact.F.In_dec m' l).
    - destruct i as [k' hin']. exists k'. right; split => //. now exists k.
    - exists k; left; split => //.
  Qed.

  Lemma strictly_updates_restrict_only_model {cls W m m'} : strictly_updates cls W m m' ->
    only_model_of W (restrict_model W m').
  Proof.
    intros su. red. rw restrict_model_spec.
    split => //. 2:clear; firstorder.
    eapply strictly_updates_total_model in su. move/[dup]/su. clear; firstorder.
  Qed.

  Lemma only_model_of_restrict W m :
    model_of W m -> only_model_of W (restrict_model W m).
  Proof.
    intros mof x. rw restrict_model_spec. firstorder.
  Qed.

  Lemma strictly_updates_from_restrict {cls W W' m m'} :
    clauses_conclusions cls ⊂_lset W ->
    model_of W m ->
    strictly_updates cls W' (restrict_model W m) m' ->
    only_model_of W m'.
  Proof.
    intros hcls mof su.
    have om := strictly_updates_only_model_gen _ _ _ _ su W.
    apply strictly_updates_incl in su.
    have hu : ((W ∪ W') =_lset W). intros x; lsets.
    rewrite hu in om. apply om.
    now apply only_model_of_restrict.
  Qed.

  Lemma restrict_model_update W m m' :
    model_of W m' ->
    only_model_of W m ->
    restrict_model W (model_update m' m) =m m.
  Proof.
    intros mof om.
    intro l. apply levelmap_find_eq => k.
    rewrite restrict_model_spec model_update_spec. split.
    - move=> [] [[hnin hm] hin|hm hin].
     specialize (proj1 (om l) hin) as [x hm']. elim hnin. now exists x.
     apply hm.
    - move=> hm. split => //. 2:now apply om; exists k.
     right; firstorder.
  Qed.

  Lemma model_update_trans m upd upd' :
    (forall l, LevelMap.In l upd -> LevelMap.In l upd') ->
    model_update (model_update m upd) upd' =m model_update m upd'.
  Proof.
    intros hl l. apply levelmap_find_eq => k.
    rewrite !model_update_spec /LevelMap.In.
    rw model_update_spec. firstorder.
    right. split => //.
    destruct (LevelMapFact.F.In_dec upd l).
    - destruct i as [updv hk].
      exists updv. firstorder.
    - exists x; left; firstorder.
  Qed.

  (* If we can update starting from a restricted model with no values outside [W],
     this can be lifted to the unrestricted model, applying the same updates *)
  Lemma strictly_updates_restrict_model_gen cls W W' m' :
    forall cls' mr,
      strictly_updates cls' W' mr m' ->
      forall m, model_of W m ->
      cls' = (cls ⇂ W) ->
      mr =m (restrict_model W m) ->
      strictly_updates (cls ⇂ W) W' m (model_update m m').
  Proof.
    intros cls' mr.
    move: W' mr m'; apply: strictly_updates_elim.
    { solve_proper. }
    - move=> m cl m' incl su mi mofW eq hm. subst cls'.
      apply one_update. auto.
      destruct cl as [prems [concl k]].
      destruct su as [v [hmin above heq]].
      rewrite hm in hmin, above.
      exists v. split => //.
      eapply min_premise_restrict with W => //.
      { intros l k' hp. move/in_restrict_clauses: incl => [] //= _ hsub _. apply hsub.
        rewrite levels_spec. now exists k'. }
      move: above.
      rewrite /level_value_above /level_value.
      elim: find_spec => //.
      + intros kr hkr.
        apply restrict_model_spec in hkr as [hkr hcl].
        now rewrite (LevelMap.find_1 hkr).
      + move=> ncl _.
        elim: find_spec => // => k' inm.
        apply in_restrict_clauses in incl as [inconcl inprems incls]. cbn in *.
        elim ncl. exists k'. eapply restrict_model_spec. split => //.
      + apply in_restrict_clauses in incl as [inconcl inprems incls]. cbn in *.
        rewrite heq. intro. apply levelmap_find_eq => k'.
        rewrite hm.
        rewrite model_update_spec !LevelMapFact.F.add_mapsto_iff restrict_model_spec.
        rewrite LevelMapFact.F.add_in_iff /Level.eq. firstorder; subst.
        right. split => //. left => //. now apply mofW.
        destruct (inLevelSet W y).
        * right. split. right => //. now exists k'.
        * left. split => //. intros []. congruence.
          destruct H2 as [yrest hin]. eapply restrict_model_spec in hin as []. contradiction.
    - move=> ls ls' m m' m'' su ihsu su' ihsu' mtot mof eq hm. subst cls'.
      specialize (ihsu mtot mof eq_refl hm).
      have model_of : model_of W (model_update mtot m').
        by apply model_of_model_update.
      move: (ihsu' (model_update mtot m') model_of eq_refl) => /fwd h.
      { rewrite hm in su. eapply strictly_updates_from_restrict in su; tea.
        2:eapply clauses_conclusions_restrict_clauses.
        now rewrite restrict_model_update. }
      eapply trans_update; tea.
      have eqm : (model_update (model_update mtot m') m'') =m model_update mtot m''.
      { eapply model_update_trans. eapply strictly_updates_ext in su'.
        intros l [k hin]. apply su' in hin as [k' []]. now exists k'. }
      now rewrite eqm in h.
  Qed.

  Lemma strictly_updates_restrict_model cls W W' m' :
    forall m, model_of W m ->
    strictly_updates (cls ⇂ W) W' (restrict_model W m) m' ->
    strictly_updates (cls ⇂ W) W' m (model_update m m').
  Proof.
    intros m mof su.
    eapply strictly_updates_restrict_model_gen; tea; reflexivity.
  Qed.

  Lemma strictly_updates_is_update_of_restrict cls W init m W' m' :
    strictly_updates cls W init m ->
    is_update_of (cls ⇂ W) W' (restrict_model W m) m' ->
    strictly_updates cls (LevelSet.union W W') init (model_update m m').
  Proof.
    move=> su /is_update_of_case; intros [[empw eq]|su'].
    - rewrite <- eq. eapply (strictly_updates_weaken cls). clsets.
      rewrite model_update_restrict.
      eapply strictly_updates_W_eq; tea. lsets.
    - eapply strictly_updates_restrict_model in su'.
      eapply strictly_updates_weaken in su'. 2:eapply restrict_clauses_subset.
      eapply trans_update; tea; eapply strictly_updates_weaken; tea; clsets.
      now apply strictly_updates_total_model in su.
  Qed.

  Lemma union_with_concl cls W : Clauses.Equal (Clauses.union cls (cls ↓ W)) cls.
  Proof.
    intros x. rewrite Clauses.union_spec in_clauses_with_concl. firstorder.
  Qed.

  Instance is_update_of_proper : Proper (Clauses.Equal ==> LevelSet.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) is_update_of.
  Proof.
    intros ?? H ?? H' ?? H'' ?? H'''.
    unfold is_update_of. setoid_rewrite H'. destruct LevelSet.is_empty.
    rewrite H'' H'''. reflexivity.
    firstorder. now rewrite -H -H' -H'' -H'''.
    subst. now rewrite H H' H'' H'''.
  Qed.

  Lemma empty_union l : LevelSet.Equal (LevelSet.union LevelSet.empty l) l.
  Proof. intros ?. lsets. Qed.

  Lemma is_update_of_strictly_updates cls W m m' :
    strictly_updates cls W m m' ->
    is_update_of cls W m m'.
  Proof.
    intros su. have ne := strictly_updates_non_empty su.
    rewrite /is_update_of. now rewrite (proj2 (levelset_not_Empty_is_empty _) ne).
  Qed.

  Lemma is_update_of_weaken {cls cls' W m m'} :
    Clauses.Subset cls cls' ->
    is_update_of cls W m m' -> is_update_of cls' W m m'.
  Proof.
    intros hsub.
    move/is_update_of_case => [].
    - intros []. subst. rewrite /is_update_of.
      now rewrite (LevelSetFact.is_empty_1 H).
    - intros su. have ne := strictly_updates_non_empty su.
      unfold is_update_of. rewrite (proj2 (levelset_not_Empty_is_empty _) ne).
      eapply strictly_updates_weaken; tea.
  Qed.

  Lemma is_update_of_trans {cls cls' W W' m m' m''} :
    is_update_of cls W m m' -> is_update_of cls' W' m' m'' ->
    is_update_of (Clauses.union cls cls') (LevelSet.union W W') m m''.
  Proof.
    move/is_update_of_case => [].
    - move=> [he eq]. intro. rewrite eq. rewrite (LevelSetProp.empty_is_empty_1 he) empty_union.
      move: H. eapply is_update_of_weaken. clsets.
    - intros su isu.
      eapply strictly_updates_is_update_of in isu; tea.
      have ne := strictly_updates_non_empty isu.
      rewrite /is_update_of. now rewrite (proj2 (levelset_not_Empty_is_empty _) ne).
  Qed.

  Lemma is_update_of_trans_eq {cls cls' W W' cltr Wtr m m' m''} :
    is_update_of cls W m m' -> is_update_of cls' W' m' m'' ->
    Clauses.Subset (Clauses.union cls cls') cltr ->
    LevelSet.Equal Wtr (LevelSet.union W W') ->
    is_update_of cltr Wtr m m''.
  Proof.
    intros hi hi' hcl hw. rewrite hw.
    eapply is_update_of_weaken; tea.
    eapply is_update_of_trans; tea.
  Qed.

  Lemma union_idem cls : Clauses.Equal (Clauses.union cls cls) cls.
  Proof. intros ?; rewrite Clauses.union_spec. firstorder. Qed.

  Lemma update_total_model W m m' :
     model_of W m ->
     model_of W (model_update m m').
  Proof.
    intros mof k inW.
    apply mof in inW as [v inW].
    destruct (LevelMapFact.F.In_dec m' k).
    - destruct i as [v' inm']. exists v'.
      rewrite model_update_spec. right; firstorder.
    - exists v. rewrite model_update_spec. left. split => //.
  Qed.

  Lemma model_map_outside_update W m m' :
    only_model_of W m' ->
    model_map_outside W m (model_update m m').
  Proof.
    intros om l nin k.
    rewrite model_update_spec.
    firstorder.
  Qed.

    Lemma valid_clause_preserved {m m' cl} :
    (forall x, LevelSet.In x (clause_levels cl) -> level_value m x = level_value m' x) ->
    valid_clause m cl ->
    valid_clause m' cl.
  Proof.
    intros hcl. destruct cl as [prems [concl k]].
    rewrite /valid_clause //=.
    rewrite (@min_premise_preserved m m' prems).
    { intros x inp. apply hcl. rewrite clause_levels_spec. now left. }
    destruct (min_premise m' prems) => //.
    rewrite /level_value_above. rewrite hcl //.
    rewrite clause_levels_spec. now right.
  Qed.

  Lemma is_model_update W m m' cls :
    model_of W m ->
    only_model_of W m' ->
    is_model (cls ⇂ W) m' ->
    is_model (cls ⇂ W) (model_update m m').
  Proof.
    intros mW om.
    rewrite /is_model.
    move/Clauses.for_all_spec. intros h.
    apply Clauses.for_all_spec. tc.
    intros cl hin.
    specialize (h cl hin). cbn in h.
    eapply valid_clause_preserved; tea.
    move=>x; move: hin. rewrite in_restrict_clauses.
    intros [incl inprems incls].
    rewrite clause_levels_spec. move=> [] hin.
    - apply inprems in hin.
      apply levelmap_level_value_eq => k.
      rewrite model_update_spec. clear -mW om hin. firstorder.
    - subst x. apply levelmap_level_value_eq => k.
      rewrite model_update_spec. cbn in *. firstorder.
  Qed.

  Lemma strictly_updates_defined_model cls W m m' :
    strictly_updates cls W m m' ->
    defined_model_of W m'.
  Proof.
    induction 1.
    - cbn. destruct cl as [prems [concl k]]; cbn in H0.
      destruct H1 as [hz [hmin habov heq]]. rewrite H0.
      move=> l /LevelSet.singleton_spec => -> //=.
      setoid_rewrite heq. exists (k + hz)%Z.
      apply LevelMapFact.F.add_mapsto_iff.
      left; split => //.
    - rewrite H1. apply defined_model_of_union; auto.
      eapply defined_model_of_ext. exact IHstrictly_updates1.
      now apply strictly_updates_ext in H0.
  Qed.

  Lemma defined_model_of_restrict W m :
    defined_model_of W m -> defined_model_of W (restrict_model W m).
  Proof.
    intros def l hin. specialize (def _ hin) as [k hm].
    exists k. apply restrict_model_spec. split => //.
  Qed.

  Lemma defined_model_of_update W m m' :
    model_of W m' ->
    defined_model_of W m -> defined_model_of W (model_update m' m).
  Proof.
    intros mof def l hin. specialize (def _ hin) as [k hm].
    exists k. apply model_update_spec. right. split => //.
    now apply mof.
  Qed.

  Lemma defined_model_of_is_update_of {W W' W'' m m'} :
    defined_model_of W m ->
    is_update_of W' W'' m m' ->
    defined_model_of W m'.
  Proof.
    intros def isupd l hin. move: isupd; rewrite /is_update_of.
    destruct LevelSet.is_empty.
    - intros h; setoid_rewrite <- h. specialize (def _ hin) as [k hm].
      now exists k.
    - now move/strictly_updates_ext/defined_model_of_ext; move/(_ W).
  Qed.

  Lemma check_model_spec_V {V cls w m w' m'} :
    model_of V m -> clauses_conclusions cls ⊂_lset V ->
    model_of w m ->
    check_model cls (w, m) = Some (w', m') ->
    check_model_invariants cls w m w' m' true.
  Proof.
    cbn; intros mof incl tot cm.
    apply check_model_has_invariants in cm => //.
    eapply model_of_subset. exact mof. tea.
  Qed.

  Lemma is_modelP m cls : reflect (Clauses.For_all (valid_clause m) cls) (is_model cls m).
  Proof.
    case E: is_model; constructor.
    - now move: E; rewrite /is_model -ClausesFact.for_all_iff.
    - intros hf. apply ClausesFact.for_all_iff in hf; tc. unfold is_model in E; congruence.
  Qed.

  Lemma is_model_invalid_clause cl cls m : is_model cls m -> ~~ valid_clause m cl -> ~ Clauses.In cl cls.
  Proof.
    move/is_modelP => ism /negP valid hin.
    now specialize (ism _ hin).
  Qed.


  Definition model_min m :=
    LevelMap.fold (fun l k acc => Z.min acc (option_get 0 k)) m 0.

  Lemma model_min_spec m : forall l k, LevelMap.MapsTo l (Some k) m -> (model_min m <= k)%Z.
  Proof.
    intros l k hm.
    rewrite /model_min.
    move: hm; eapply LevelMapFact.fold_rec.
    - move=> m0 he hm. now apply he in hm.
    - intros k' e a m' m'' hm nin hadd hle hm''.
      specialize (hadd l).
      eapply levelmap_find_eq_inv in hadd. eapply hadd in hm''.
      rewrite LevelMapFact.F.add_mapsto_iff in hm''.
      move: hm''=> [] [h h'].
      * subst e. cbn. lia.
      * move/hle: h'. lia.
  Qed.

  Lemma model_min_spec2 m : (model_min m <= 0)%Z.
  Proof.
    rewrite /model_min.
    eapply LevelMapFact.fold_rec.
    - intros; reflexivity.
    - intros k' e a m' m'' hm nin hadd hle. lia.
  Qed.

  Definition model_max m :=
    LevelMap.fold (fun l k acc => Z.max acc (option_get 0 k)) m 0.

  Lemma model_max_spec m : forall l k, LevelMap.MapsTo l k m -> (k ≤ Some (model_max m)).
  Proof.
    intros l k hm.
    rewrite /model_max.
    move: hm; eapply LevelMapFact.fold_rec.
    - move=> m0 he hm. now apply he in hm.
    - intros k' e a m' m'' hm nin hadd hle hm''.
      specialize (hadd l).
      eapply levelmap_find_eq_inv in hadd. eapply hadd in hm''.
      rewrite LevelMapFact.F.add_mapsto_iff in hm''.
      move: hm''=> [] [h h'].
      * subst k. destruct e; constructor. cbn. lia.
      * move/hle: h'. intros h'; depelim h'; constructor; lia.
  Qed.

  Lemma model_max_spec2 m : (0 <= model_max m)%Z.
  Proof.
    rewrite /model_max.
    eapply LevelMapFact.fold_rec.
    - intros; reflexivity.
    - intros k' e a m' m'' hm nin hadd hle. lia.
  Qed.

  Definition valuation_of_model (m : model) : LevelMap.t nat :=
    let max := model_max m in
    let min := model_min m in
    LevelMap.fold (fun l k acc => LevelMap.add l (Z.to_nat (max - option_get 0 k - min)) acc) m (LevelMap.empty _).

  Lemma valuation_of_model_spec m :
    forall l k, LevelMap.MapsTo l (Some k) m ->
      let v := (model_max m - k - model_min m)%Z in
      LevelMap.MapsTo l (Z.to_nat v) (valuation_of_model m).
  Proof.
    intros l k hm v.
    unfold valuation_of_model. subst v.
    move: hm. generalize (model_max m) (model_min m) => n n'.
    eapply LevelMapFact.fold_rec.
    - intros v he hm.
      now eapply he in hm.
    - intros.
      specialize (H1 l). eapply levelmap_find_eq_inv in H1. eapply H1 in hm.
      rewrite LevelMapFact.F.add_mapsto_iff in hm. destruct hm as [[-> ->]|[neq hm]].
      * eapply LevelMapFact.F.add_mapsto_iff. left. split => //.
      * eapply LevelMapFact.F.add_mapsto_iff. right. split => //. now apply H2.
  Qed.

  Lemma strictly_updates_valid_model {W W' m m' cls} :
    is_model (cls ↓ W) m ->
    strictly_updates cls W' m m' ->
    exists l, LevelSet.In l W' /\ ~ LevelSet.In l W.
  Proof.
    intros vm su.
    move: W' m m' su vm; apply: strictly_updates_elim.
    { intros ? ? eq ? ? -> ? ? ->. now setoid_rewrite eq. }
    - move=> m cl m' incl su vm. exists (clause_conclusion cl). split => //. lsets. intros hin.
      eapply strict_update_invalid in su.
      eapply is_model_invalid_clause in vm; tea. apply vm.
      eapply in_clauses_with_concl. split => //.
    - move=> ls ls' m m' m'' su ihsu su' ihsu' vm.
      destruct (ihsu vm). exists x.
      rewrite LevelSet.union_spec. firstorder.
  Qed.

  Lemma model_of_strictly_updates cls W V m m' :
    strictly_updates cls W m m' -> model_of V m -> model_of V m'.
  Proof.
    intros su.
    induction su.
    - intros mv l hin. apply mv in hin.
      destruct cl as [prems [concl k]].
      destruct H1 as [minv [eqmin nabove eqm]]. rewrite eqm.
      rewrite LevelMapFact.F.add_in_iff. now right.
    - eauto.
  Qed.

  Lemma check_model_ne {cls U m W m'} : check_model cls (U, m) = Some (W, m') -> ~ LevelSet.Empty W.
  Proof.
    move/check_model_spec => [w'' [su ->]].
    apply strictly_updates_non_empty in su.
    intros he. apply su. lsets.
  Qed.

  Lemma check_model_update_of {cls U m W m'} : check_model cls (U, m) = Some (W, m') ->
    exists W', is_update_of cls W' m m' /\ W =_lset LevelSet.union U W'.
  Proof.
    move/check_model_spec => [w'' [su eq]]. rw eq. exists w''. split => //.
    now eapply is_update_of_strictly_updates.
  Qed.

  Lemma strictly_updates_all cls V minit m :
    strictly_updates cls V minit m ->
    (forall l k, LevelSet.In l V -> LevelMap.MapsTo l k minit ->
      exists k', LevelMap.MapsTo l (Some k') m /\ opt_le Z.lt k (Some k')).
  Proof.
    move: V minit m; apply: strictly_updates_elim.
    { intros ? ? eq ? ? -> ? ? ->. now setoid_rewrite eq. }
    - move=> m cl m' incl su l k hin hm.
      move: su; rewrite /strict_update.
      destruct cl as [prems [concl gain]].
      move=> [] v [] minp hlt. cbn in hin. eapply LevelSet.singleton_spec in hin. red in hin; subst l.
      move/negbTE: hlt; rewrite /level_value_above.
      intros hle eq. setoid_rewrite eq.
      eexists. setoid_rewrite LevelMapFact.F.add_mapsto_iff. split; [left;split;eauto|] => //.
      destruct level_value eqn:hl => //.
      * rewrite (level_value_MapsTo hm) in hl. noconf hl. constructor. lia.
      * rewrite (level_value_MapsTo hm) in hl. noconf hl. constructor.
    - move=> ls ls' m m' m'' su ihsu su' ihsu' l k; rewrite LevelSet.union_spec; move=> [] hin hm.
      apply ihsu in hm as [k' [hle hm']]; tea.
      eapply strictly_updates_ext in su'. apply su' in hle as [k'' [hm'' lek'']].
      depelim lek''.
      exists y. split => //. depelim hm'; constructor; lia.
      eapply strictly_updates_ext in su. eapply su in hm as [k' [hm' lek']].
      eapply ihsu' in hm' as [k'' [hm'' lek'']]; tea.
      exists k''. split => //. depelim lek'; depelim lek''; constructor; lia.
  Qed.

  Definition model_rel_partial R V (m m' : model) :=
  forall l,
    (LevelSet.In l V -> forall k, LevelMap.MapsTo l k m ->
       exists k', LevelMap.MapsTo l k' m' /\ opt_le R k k') /\
    (~ LevelSet.In l V -> forall k, LevelMap.MapsTo l k m <-> LevelMap.MapsTo l k m').

  Lemma model_of_sext {R W W' m m'} :
    model_of W m ->
    model_of W' m ->
    model_rel_partial R W m m' ->
    model_of W' m'.
  Proof.
    intros mof mof' ext.
    intros l hin.
    destruct (mof' l hin). specialize (ext l) as [lin lout].
    destruct (inLevelSet W l) as [hin'|hout].
    - specialize (lin hin' _ H). firstorder.
    - specialize (lout hout x).
      exists x. now apply lout.
  Qed.

  Lemma defined_model_of_sext {R W W' m m'} :
    defined_model_of W m ->
    defined_model_of W' m ->
    model_rel_partial R W m m' ->
    defined_model_of W' m'.
  Proof.
    intros mof mof' ext.
    intros l hin.
    destruct (mof' l hin). specialize (ext l) as [lin lout].
    destruct (inLevelSet W l) as [hin'|hout].
    - specialize (lin hin' _ H). firstorder. depelim H1. now exists y.
    - specialize (lout hout (Some x)).
      exists x. now apply lout.
  Qed.

  Lemma model_rel_partial_trans {R W W' m m' m''} (HR : Transitive R) :
    model_rel_partial R W m m' ->
    model_rel_partial R W' m' m'' ->
    model_rel_partial R (LevelSet.union W W') m m''.
  Proof.
    intros mr mr' l.
    specialize (mr l) as [inWmr outWmr].
    specialize (mr' l) as [inWmr' outWmr'].
    split.
    { rewrite LevelSet.union_spec. move=> [] hin k hm.
      - specialize (inWmr hin k hm) as [k' [hk' rk']].
        destruct (inLevelSet W' l).
        + specialize (inWmr' H k' hk') as [k'' [hk'' rk'']].
          exists k''. split => //. now transitivity k'.
        + specialize (outWmr' H k'). exists k'. split => //. now apply outWmr'.
      - destruct (inLevelSet W l).
        + specialize (inWmr H k hm) as [k'' [hk'' rk'']].
          specialize (inWmr' hin k'' hk'') as [km' [hkm' rkm']].
          exists km'. split => //. now transitivity k''.
        + specialize (outWmr H k) as eq.
          apply eq in hm.
          specialize (inWmr' hin k hm) as [m''k [hm'' rm'']].
          exists m''k. split => //. }
    { move/not_in_union_inv => [] ninW ninW' k.
      rewrite (outWmr ninW k).
      rewrite (outWmr' ninW' k). reflexivity. }
  Qed.

  Lemma strictly_updates_model_lt {cls V} {m m'} :
    strictly_updates cls V m m' ->
    model_of V m ->
    model_rel_partial Z.lt V m m'.
  Proof.
    move=> h mV l. split => //.
    - move/strictly_updates_all: h => h; move=> inv k /h; move/(_ inv) => [k' []].
      exists (Some k'); split => //.
    - now eapply strictly_updates_outside.
  Qed.

  #[program]
  Definition of_level_map (m : LevelMap.t (option Z)) (hne : defined_map m) : premises :=
    {| t_set := LevelMap.fold (fun l k acc =>
      if k is (Some k') return _ then LevelExprSet.add (l, k') acc else acc) m LevelExprSet.empty |}.
  Next Obligation. apply not_Empty_is_empty.
    move: hne. eapply LevelMapFact.fold_rec. firstorder.
    intros. rewrite /LevelExprSet.Empty.
    intros ha. destruct e eqn:he.
    - specialize (ha (k, z)). apply ha; apply LevelExprSet.add_spec. now left.
    - destruct hne as [witl [witk hin]].
      apply levelmap_add_spec in H1. rewrite H1 in hin.
      rewrite LevelMapFact.F.add_mapsto_iff in hin;
        destruct hin as [[? eq]|[new hm]]; try congruence.
      eapply H2. now exists witl, witk. exact ha.
  Qed.

  Lemma mapsto_some_add_none l k l' (m : model) :
    LevelMap.MapsTo l (Some k) (LevelMap.add l' None m) <->
    LevelMap.MapsTo l (Some k) m /\ l <> l'.
  Proof.
    rewrite LevelMapFact.F.add_mapsto_iff; firstorder; congruence.
  Qed.

  Lemma of_level_map_spec m hne :
    forall l k, LevelExprSet.In (l, k) (of_level_map m hne) <-> LevelMap.MapsTo l (Some k) m.
  Proof.
    intros l k; rewrite /of_level_map //=.
    clear hne.
    have : forall acc,
      LevelExprSet.In (l, k)
      (LevelMap.fold (fun (l0 : LevelMap.key) k0 (acc : LevelExprSet.t) =>
        if k0 is (Some k') then LevelExprSet.add (l0, k') acc else acc) m acc) <->
      LevelMap.MapsTo l (Some k) m \/ LevelExprSet.In (l, k) acc.
    move=> acc; eapply LevelMapFact.fold_rec.
    - firstorder.
    - intros.
      destruct e eqn:he.
      { rewrite LevelExprSet.add_spec H2.
        split.
        * intros [eq|hm].
          + noconf eq. specialize (H1 l). eapply levelmap_find_eq_inv in H1.
            erewrite H1. left. apply LevelMapFact.F.add_mapsto_iff. left => //.
          + specialize (H1 l). eapply levelmap_find_eq_inv in H1; erewrite H1.
            rewrite LevelMapFact.F.add_mapsto_iff.
            destruct (Level.eq_dec l k0); subst; firstorder. exact None.
        * intros hm'. destruct hm'.
          + specialize (H1 l). eapply levelmap_find_eq_inv in H1. eapply H1 in H3.
            apply LevelMapFact.F.add_mapsto_iff in H3. destruct H3. firstorder; subst. left. red. red in H3. subst.
            noconf H6; reflexivity.
            unfold LevelExprSet.E.eq. destruct H3. now right; left.
          + unfold LevelExprSet.E.eq. now right. }
      { rewrite H2. clear H2; apply levelmap_add_spec in H1; rewrite H1.
        rewrite mapsto_some_add_none. firstorder. cbn in H0.
        destruct (Level.eq_dec l k0).
        * subst. cbn in H0. firstorder.
        * left. auto. }
    - intros. rewrite H. firstorder. lesets.
  Qed.

  Lemma strictly_updates_defined_init_map {cls W m m'} :
    strictly_updates cls W m m' -> defined_map m.
  Proof.
    induction 1.
    - destruct cl as [prems [concl k]].
      destruct H1 as [? [? ? heq]].
      eapply min_premise_spec_aux in H1 as [_ [[] [inprems heq']]].
      unfold min_atom_value in heq'.
      destruct level_value eqn:hl => //. apply level_value_MapsTo' in hl.
      now exists t0, z0.
    - auto.
  Qed.

  Lemma defined_map_ne m : defined_map m -> ~ LevelMap.Empty m.
  Proof.
    move=> [] k [] v hm he. now eapply he.
  Qed.

  Lemma strictly_updates_non_empty_init_map {cls W m m'} :
    strictly_updates cls W m m' -> ~ LevelMap.Empty m.
  Proof.
    now move/strictly_updates_defined_init_map/defined_map_ne.
  Qed.

  Definition premise_values (prems : premises) m :=
    map (fun '(l, k) => (l, option_get 0 (level_value m l))) prems.

  Lemma premise_values_spec prems m :
    forall l k, LevelExprSet.In (l, k) (premise_values prems m) <->
      (exists k', LevelExprSet.In (l, k') prems /\ k = option_get 0 (level_value m l)).
  Proof.
    rewrite /premise_values.
    intros l k. rewrite map_spec.
    firstorder. destruct x. noconf H0.
    exists z. split => //. exists(l, x); split => //. now rewrite -H0.
  Qed.

  Definition hyps_map (hyps : premises) m :=
    (forall (l : Level.t) k, LevelExprSet.In (l, k) hyps <-> LevelMap.MapsTo l (Some k) m).

  Lemma model_hyps_entails cls m hyps (prems : premises) concl :
    Clauses.In (prems, concl) cls ->
    (forall l k, LevelExprSet.In (l,k) prems -> exists z, Some z ≤ level_value m l) ->
    hyps_map hyps m ->
    cls ⊢a hyps → premise_values prems m.
  Proof.
    intros incls hmx hm.
    intros [l k] hin.
    rewrite premise_values_spec in hin. destruct hin as [k' [inp ->]].
    red in hm.
    constructor. rewrite hm.
    specialize (hmx l _ inp).
    depelim hmx. depelim H. rewrite H0 //=.
    now eapply level_value_MapsTo'.
  Qed.

  Lemma hyps_entails (hyps : premises) m cls :
    hyps_map hyps m ->
    forall prems conclk, Clauses.In (prems, conclk) cls ->
    forall v, min_premise m prems = Some v ->
    cls ⊢a hyps → add_prems v prems.
  Proof.
    intros H prems conclk H0 v H1.
    have [minsleq mineq] := min_premise_spec m prems.
    destruct mineq as [[minprem minpremk] [inprems eqminp]]. cbn.
    have hmz' : forall l k, LevelExprSet.In (l, k) prems -> exists z, Some z ≤ level_value m l.
    { intros l k hin. specialize (minsleq _ hin). rewrite H1 in minsleq. cbn in minsleq. destruct level_value => //.
      depelim minsleq. exists (v + k)%Z. constructor. lia. depelim minsleq. }
    move: eqminp. rewrite /min_atom_value.
    destruct level_value eqn:hl. intros hminp.
    2:{ now rewrite H1. }
    rewrite H1 in hminp. noconf hminp.
    have entails_prems : cls ⊢a hyps → premise_values prems m.
      by eapply model_hyps_entails with conclk; auto.
    eapply entails_all_trans; tea.
    eapply entails_succ.
    intros l k. rewrite In_add_prems.
    intros [[prem premk] [inprem [= -> ->]]].
    rw premise_values_spec. eexists.
    split. exists premk. split => //.
    have hmz'' := hmz' prem _ inprem.
    depelim hmz''. depelim H2. rewrite H3 //=.
    specialize (minsleq _ inprem). cbn in minsleq. rewrite H3 in minsleq.
    rewrite H1 in minsleq. depelim minsleq. lia.
  Qed.

  Lemma strictly_updates_entails {cls V mzero m} (hne : defined_map mzero) (hne' : defined_map m) :
    strictly_updates cls V mzero m ->
    entails_all cls (of_level_map mzero hne) (of_level_map m hne').
  Proof.
    move=> su; move: V mzero m su hne hne'.
    apply: strictly_updates_elim; [|move=>m cl m' incl su|move=>ls ls' m m' m'' su ihsu su' ihsu'].
    { intros ? ? eq. solve_proper. }
    all:intros hne hne'.
    - destruct cl as [prems [concl k]].
      destruct su as [minp [hmin nabove eqm']].
      have [minsleq mineq] := min_premise_spec m prems.
      destruct mineq as [minprem [inprems eqminp]]. cbn.
      move: eqminp. rewrite /min_atom_value.
      move/negbTE/level_value_not_above_spec: nabove => nabove.
      destruct minprem as [minprem mink].
      destruct (level_value m minprem) eqn:hminprem; rewrite hmin //; intros [= ->].
      intros [l k'] hin.
      eapply of_level_map_spec in hin. rewrite eqm' in hin.
      rewrite LevelMapFact.F.add_mapsto_iff in hin.
      destruct hin as [[eq heq]|[neq hm]]. noconf heq.
      have hypss := of_level_map_spec m hne.
      set (hyps := of_level_map m hne) in *. clearbody hyps.
      have entailscl : entails cls (prems, (concl, k)) by exact: entails_in incl.
      move/(entails_shift (z - mink)): entailscl. cbn. move => entailscl.
      eapply (entails_all_one (concl := add_prems (z - mink) prems)) => //.
      eapply level_value_MapsTo' in hminprem.
      rewrite -hypss in hminprem.
      eapply hyps_entails; tea. red in eq; subst.
      have -> : (k + (z - mink) = z - mink + k)%Z by lia.
      exact entailscl.
      constructor. now rewrite of_level_map_spec.
    - have hnemid : defined_map m'. by exact: strictly_updates_defined_map su.
      specialize (ihsu hne hnemid).
      specialize (ihsu' hnemid hne').
      eapply entails_all_trans; tea.
  Qed.

  Lemma is_update_of_entails {cls V m m' hne hne'} : is_update_of cls V m m' ->
    cls ⊢a of_level_map m hne → of_level_map m' hne'.
  Proof.
    rewrite /is_update_of.
    destruct LevelSet.is_empty.
    - intros heq [].
      rewrite !of_level_map_spec. rewrite -heq.
      constructor. now apply of_level_map_spec.
    - eapply strictly_updates_entails.
  Qed.

  Local Open Scope Z_scope.

  Lemma infers_atom_of_level_map {cls m hne l k} :
    infers_atom m l k ->
    cls ⊢ of_level_map m hne → (l, k).
  Proof.
    rewrite /infers_atom. intros hle. depelim hle.
    have [y' eq] : exists y', y = (k + y'). exists (y - k). lia.
    eapply (entails_trans (concl := (l, k + y'))).
    - constructor. rewrite of_level_map_spec.
      eapply level_value_MapsTo'. rewrite H0. f_equal. lia.
    - eapply (entails_pred_closure_n (n := Z.to_nat y')).
      constructor. eapply LevelExprSet.singleton_spec.
      rewrite Z2Nat.id. lia. reflexivity.
  Qed.

  (* The criterion for loops:
    when a set of updates manages to strictly update all the levels it started with,
    then we can deduce a looping constraint `x, ..., z -> x + 1, ... z + 1`.
    *)

  Lemma entails_any_one V cls m nem m' nem' :
    model_of V m ->
    cls ⊢a of_level_map m nem → of_level_map m' nem' ->
    model_rel_partial Z.lt V m m' ->
    forall l k, LevelSet.In l V ->
    LevelMap.MapsTo l (Some k) m -> cls ⊢ of_level_map m nem → (l, k + 1).
  Proof.
    intros tot cla mp l k hin hm.
    eapply entails_all_one; tea.
    move: (proj1 (mp l) hin).
    move: (tot _ hin) => [x hm'].
    move/(_ _ hm) => [k'' [hm'' lt]].
    apply infers_atom_of_level_map. red. rewrite (level_value_MapsTo hm'').
    depelim lt. constructor. lia.
  Qed.

  Lemma entails_any V cls m nem m' nem' :
    only_model_of V m ->
    cls ⊢a of_level_map m nem → of_level_map m' nem' ->
    model_rel_partial Z.lt V m m' ->
    cls ⊢a of_level_map m nem → succ_prems (of_level_map m nem).
  Proof.
    intros tot cla mp [l k].
    rewrite In_add_prems => [] [[l' k']] [] /of_level_map_spec hm.
    rewrite /succ_expr => he. noconf he. rewrite Z.add_comm.
    eapply entails_any_one; tea. exact tot. apply tot. now exists (Some k').
  Qed.

  Lemma strictly_updates_entails_on_V cls V mzero hne m :
    only_model_of V mzero ->
    strictly_updates cls V mzero m ->
    entails_all (cls ↓ V) (of_level_map mzero hne) (succ_prems (of_level_map mzero hne)).
  Proof.
    move=> tot su.
    have mp := strictly_updates_model_lt su tot.
    have nem := strictly_updates_defined_map su.
    eapply strictly_updates_strenghten in su.
    eapply (strictly_updates_entails hne nem) in su; tea.
    eapply entails_any in su; tea.
  Qed.

  Lemma check_model_defined_init_map {cls V U minit m W m'} :
    [/\ clauses_levels cls ⊂_lset V, only_model_of V minit & is_update_of cls U minit m] ->
    check_model cls (U, m) = Some (W, m') ->
    defined_map minit.
  Proof.
    intros [_ _ isupd] check.
    eapply check_model_is_update_of in check as [su incl]; tea.
    rewrite union_idem in su.
    now eapply strictly_updates_defined_init_map in su.
  Qed.

  Lemma check_model_defined_map {cls U m W m'} :
    check_model cls (U, m) = Some (W, m') ->
    defined_map m'.
  Proof.
    intros check.
    eapply check_model_spec in check as [W' [su incl]]; tea.
    now eapply strictly_updates_defined_map in su.
  Qed.

  Section Semantics.
    Import Semilattice.
    Section Interpretation.
      Context {A : Type} {s : Semilattice A}.
      Context (V : Level.t -> A).

      Definition interp_expr '(l, k) := (add k (V l))%Z.
      Definition interp_prems prems :=
        let '(hd, tl) := to_nonempty_list prems in
        fold_right (fun lk acc => join (interp_expr lk) acc) (interp_expr hd) tl.

      Definition clause_sem (cl : clause) : Prop :=
        let '(prems, concl) := cl in
        le (interp_prems prems) (interp_expr concl).

      Definition clauses_sem (cls : clauses) : Prop :=
        Clauses.For_all clause_sem cls.
    End Interpretation.

    Section OfSL.
      Context {A} {SL : Semilattice A}.
      Declare Scope sl_scope.
      Infix "≤" := le : sl_scope.
      Infix "≡" := eq : sl_scope.
      Local Open Scope sl_scope.

      (* There exists a valuation making all clauses true in the natural numbers *)
      Definition satisfiable (cls : clauses) :=
        exists V, clauses_sem V cls.

      (* Any valuation making all clauses valid in the given semilattice also satisfies the clause cl *)
      Definition entails_sem (cls : clauses) (cl : clause) :=
        forall V, clauses_sem V cls -> clause_sem V cl.

      Lemma interp_add_expr V n e :
        interp_expr V (add_expr n e) ≡ add n (interp_expr V e).
      Proof.
        destruct e as [l k]; cbn. now rewrite add_distr.
      Qed.

      Lemma interp_prems_singleton V e :
        interp_prems V (NES.singleton e) = interp_expr V e.
      Proof.
        rewrite /interp_prems.
        now rewrite singleton_to_nonempty_list /=.
      Qed.

      Lemma interp_prems_ge v (prems : premises) :
        forall prem, LevelExprSet.In prem prems ->
        interp_expr v prem ≤ interp_prems v prems.
      Proof.
        intros.
        unfold interp_prems.
        have he := to_nonempty_list_spec prems.
        destruct to_nonempty_list.
        pose proof to_nonempty_list_spec'.
        rewrite In_elements in H. rewrite -he in H. clear H0 he. clear -H.
        destruct H. subst p.
        - induction l. cbn. auto.
          cbn. red. eapply join_idem. cbn.
          etransitivity; tea.
          apply join_le_right.
        - induction l in H |- *.
          now cbn in H.
          cbn in H. destruct H; subst; cbn.
          * cbn. apply join_le_left.
          * specialize (IHl H). etransitivity; tea. apply join_le_right.
      Qed.

      Lemma interp_prems_elements V u :
        interp_prems V u = fold_right join (interp_expr V (to_nonempty_list u).1) (List.map (interp_expr V) (to_nonempty_list u).2).
      Proof.
        rewrite /interp_prems.
        have he := to_nonempty_list_spec u.
        destruct to_nonempty_list.
        now rewrite Universes.fold_right_map.
      Qed.

      Lemma fold_right_interp {V : Level.t -> A} {x l x' l'} :
        equivlistA Logic.eq (x :: l) (x' :: l') ->
        fold_right join (interp_expr V x) (List.map (interp_expr V) l) = fold_right join (interp_expr V x') (List.map (interp_expr V) l').
      Proof.
        intros eq. apply fold_right_equivlist_all.
        intros a. rewrite !InA_In_eq.
        rewrite !(in_map_iff (interp_expr V) (_ :: _)).
        setoid_rewrite <-InA_In_eq.
        split.
        - move=> [b [<- ]].
          eexists; split; trea. now apply eq in b0.
        - move=> [b [<- ]].
          eexists; split; trea. now apply eq in b0.
      Qed.

      Lemma equivlistA_add le u : let l := to_nonempty_list (NES.add le u) in
        equivlistA eq (l.1 :: l.2) (le :: LevelExprSet.elements u).
      Proof.
        have he := to_nonempty_list_spec (NES.add le u).
        destruct to_nonempty_list. cbn.
        intros x. rewrite he.
        rewrite !LevelExprSet.elements_spec1.
        split.
        - move/LevelExprSet.add_spec => [->|hin].
          now constructor. constructor 2. now apply LevelExprSet.elements_spec1.
        - intros h; depelim h; subst. now apply LevelExprSet.add_spec; left.
          apply LevelExprSet.add_spec. now apply LevelExprSet.elements_spec1 in h.
      Qed.

      Lemma interp_prems_add V le (u : premises) :
        interp_prems V (NES.add le u) = Z.max (interp_expr V le) (interp_prems V u).
      Proof.
        rewrite 2!interp_prems_elements.
        erewrite fold_right_interp. 2:apply equivlistA_add.
        rewrite fold_right_comm.
        { apply map_nil, elements_not_empty. }
        f_equal. eapply fold_right_equivlist_all.
        have he := to_nonempty_list_spec u.
        destruct to_nonempty_list. rewrite -he //=.
      Qed.

      Lemma interp_prems_elim (P : premises -> Z -> Prop) V :
        (forall le, P (NES.singleton le) (interp_expr V le)) ->
        (forall le u k, P u k -> ~ LevelExprSet.In le u -> P (NES.add le u) (Z.max (interp_expr V le) k)) ->
        forall u, P u (interp_prems V u).
      Proof.
        intros hs hadd.
        eapply elim.
        - intros le. rewrite interp_prems_singleton. apply hs.
        - intros le prems ih hnin.
          rewrite interp_prems_add. now apply hadd.
      Qed.

      Local Open Scope Z_scope.
      Lemma interp_add_prems V n e : interp_prems V (add_prems n e) = n + interp_prems V e.
      Proof.
        revert e.
        refine (interp_prems_elim (fun u z => interp_prems V (add_prems n u) = n + z) _ _ _).
        - intros le.
          rewrite add_prems_singleton interp_prems_singleton //=.
          destruct le; cbn. lia.
        - intros le u k heq hnin.
          rewrite add_prems_add.
          rewrite interp_prems_add heq interp_add_expr. lia.
      Qed.


      Lemma interp_prems_in {V le} {u : premises} : LevelExprSet.In le u -> interp_prems V u >= interp_expr V le.
      Proof.
        revert u.
        refine (interp_prems_elim (fun u z => LevelExprSet.In le u -> z >= interp_expr V le) V _ _).
        - intros le' u'.
          apply LevelExprSet.singleton_spec in u'. red in u'; subst. lia.
        - move=> le' u z hz hnin /LevelExprSet.add_spec [->|hin]. lia.
          specialize (hz hin). lia.
      Qed.

      Lemma clauses_sem_subset {u u' : premises} : u ⊂_leset u' ->
        forall V, interp_prems V u' >= interp_prems V u.
      Proof.
        intros hsub V.
        revert u u' hsub.
        refine (interp_prems_elim (fun u z => forall u' : premises, u ⊂_leset u' -> interp_prems V u' >= z) V _ _).
        - intros le u' hsing.
          specialize (hsing le). forward hsing by now apply LevelExprSet.singleton_spec.
          now apply interp_prems_in.
        - intros le u k ih hin u' sub.
          have hle := sub le.
          specialize (ih u').
          forward ih. intros x hin'. apply sub. now apply LevelExprSet.add_spec; right.
          forward hle by now apply LevelExprSet.add_spec; left.
          have hi := interp_prems_in (V := V) hle. lia.
      Qed.


    End OfSL.
  End Semantics.

  Definition enabled_clause (m : model) (cl : clause) :=
    exists z, min_premise m (premise cl) = Some z.

  Definition enabled_clauses (m : model) (cls : clauses) :=
    Clauses.For_all (enabled_clause m) cls.


  Import Semilattice.

  Definition to_val (v : LevelMap.t nat) l :=
    match LevelMap.find l v with
    | Some n => n
    | None => 0%nat
    end.

  (* Interprest in a nat semilattice only *)
  Definition correct_model {SL : Semilattice nat} (cls : clauses) (m : model) :=
    enabled_clauses m cls /\ clauses_sem (to_val (valuation_of_model m)) cls.

  Lemma enabled_clause_ext {m m' cl} :
    m ⩽ m' -> enabled_clause m cl -> enabled_clause m' cl.
  Proof.
    intros hext; rewrite /enabled_clause.
    destruct cl as [prems [concl k]]; cbn; move=> [z hm].
    have pr := min_premise_pres prems hext.
    rewrite hm in pr. depelim pr. now exists y.
  Qed.


  Lemma enabled_clauses_ext m m' cls : m ⩽ m' -> enabled_clauses m cls -> enabled_clauses m' cls.
  Proof.
    intros hext.
    rewrite /enabled_clauses.
    intros ha cl; move/ha.
    now apply enabled_clause_ext.
  Qed.

  Lemma in_pred_closure_entails cls cl :
    in_pred_closure cls cl ->
    (forall V, clauses_sem V cls -> clause_sem V cl).
  Proof.
    induction 1.
    - intros V. rewrite /clauses_sem. intros ha.
      apply ha in H.
      move: H; rewrite /clause_sem.
      destruct cl as [prems concl].
      cbn. rewrite interp_add_prems.
      destruct concl as [concl conclk].
      rewrite /add_expr; cbn. lia.
    - intros V clsm. cbn.
      rewrite interp_prems_singleton.
      cbn. lia.
  Qed.

  (** Enabled and valid clauses are satisfied by valuation *)
  Lemma valid_clause_model model cl :
    enabled_clause model cl ->
    valid_clause model cl ->
    clause_sem (to_val (valuation_of_model model)) cl.
  Proof.
    unfold enabled_clause, valid_clause.
    destruct min_premise eqn:hmin => //= => //.
    2:{ intros [k' eq]. congruence. }
    intros [k' eq]. noconf eq.
    destruct cl as [prems [concl k]]; cbn.
    unfold level_value_above.
    destruct level_value eqn:hl => //.
    unfold level_value in hl. destruct LevelMap.find eqn:hfind => //. noconf hl.
    move/Z.leb_le => hrel.
    eapply LevelMap.find_2 in hfind.
    have conclm := valuation_of_model_spec _ _ _ hfind.
    set (v := (model_max _ - _)) in *.
    cbn in conclm.
    eapply LevelMap.find_1 in conclm.
    subst v.
    pose proof (@min_premise_spec model prems) as [premmin [prem [premin premeq]]].
    rewrite hmin in premeq.
    eapply Z.le_ge.
    eapply Z.le_trans. 2:{ eapply interp_prems_ge; tea. }
    unfold interp_expr. destruct prem as [prem k'].
    symmetry in premeq.
    move: premeq. unfold min_atom_value.
    unfold level_value. destruct (LevelMap.find prem) eqn:findp => //.
    destruct o => //.
    intros [= <-].
    eapply LevelMap.find_2 in findp.
    have premm := valuation_of_model_spec _ _ _ findp.
    eapply LevelMap.find_1 in premm.
    assert (z1 - k' <= z0 - k). lia.
    have hm : z0 <= model_max model.
    { eapply model_max_spec in hfind; tea. now depelim hfind. }
    have hm' : z1 <= model_max model.
    { eapply model_max_spec in findp; tea. now depelim findp. }
    have hmi : model_min model <= z0.
    { eapply model_min_spec; tea. }
    have hmi' : model_min model <= z1.
    { eapply model_min_spec; tea. }
    assert (0 <= model_max model)%Z by apply model_max_spec2.
    assert (model_min model <= 0)%Z by apply model_min_spec2.
    rewrite /to_val premm conclm.
    lia.
  Qed.

  Lemma valid_clauses_model model cls :
    enabled_clauses model cls ->
    is_model cls model ->
    clauses_sem (to_val (valuation_of_model model)) cls.
  Proof.
    move=> en ism cl hin.
    apply valid_clause_model.
    now apply en.
    now move/Clauses.for_all_spec: ism; apply.
  Qed.

  Lemma init_model_enabled cls : enabled_clauses (max_clause_premises cls) cls.
  Proof.
    unfold enabled_clauses.
    intros x hin. unfold enabled_clause.
    pose proof (@min_premise_spec (max_clause_premises cls) (premise x)) as [premmin [prem [premin premeq]]].
    have inV : LevelSet.In (level prem) (clauses_levels cls).
    { rewrite clauses_levels_spec. exists x; split => //. rewrite /clause_levels.
      eapply LevelSet.union_spec; left. rewrite levels_spec. exists prem.2.
      destruct prem. exact premin. }
    rewrite premeq. unfold min_atom_value.
    destruct prem as [l k].
    have hm := max_clause_premises_spec_inv cls l inV.
    rewrite (level_value_MapsTo hm).
    have hs := max_clause_premise_of_spec l k _ _ hin premin.
    depelim hs. rewrite H0.
    eexists => //.
  Qed.

  Definition valid_entailment cls cl := forall V, clauses_sem V cls -> clause_sem V cl.
  Definition invalid_entailment cls cl :=
    forall V, clauses_sem V cls -> clause_sem V cl -> False.

  Lemma clauses_sem_entails {cls cl} :
    entails cls cl ->
    valid_entailment cls cl.
  Proof.
    induction 1.
    - intros v clls. red.
      destruct concl0 as [concl k].
      have hge := interp_prems_ge v prems _ H.
      by lia.
    - move=> V Hcls.
      move: {IHentails} (IHentails _ Hcls).
      unfold clause_sem. unfold ge => hyp.
      etransitivity; tea. rewrite interp_prems_add.
      rewrite interp_prems_add in hyp.
      eapply in_pred_closure_entails in H; tea.
      move: H; rewrite /clause_sem. unfold ge.
      have ssub := clauses_sem_subset H1 V. lia.
  Qed.

  Lemma clauses_sem_entails_all {cls prems concl} :
    cls ⊢a prems → concl ->
    (forall V, clauses_sem V cls -> interp_prems V prems >= interp_prems V concl).
  Proof.
    intros ha V hcls.
    red in ha.
    move: ha.
    revert concl.
    refine (@interp_prems_elim (fun concl z => _ -> interp_prems V prems >= z) V _ _).
    - move=> le //=. move/(_ le).
      intros h; forward h by now apply LevelExprSet.singleton_spec.
      now have ent := (clauses_sem_entails h _ hcls).
    - intros le u k ih hnin.
      intros hf.
      forward ih. intros x hin; apply (hf x).
      rewrite LevelExprSet.add_spec; now right.
      specialize (hf le).
      forward hf by now apply LevelExprSet.add_spec; left.
      cbn in hf.
      have ent := (clauses_sem_entails hf _ hcls). cbn in ent.
      lia.
  Qed.

  Lemma valid_clause_shift m n cl :
    valid_clause m cl -> valid_clause m (add_clause n cl).
  Proof.
    destruct cl as [prems [concl k]].
    move/valid_clause_elim => hv.
    apply valid_clause_intro => z eqmin.
    eapply min_premise_add_prems_inv in eqmin.
    specialize (hv _ eqmin).
    etransitivity; tea. constructor; lia.
  Qed.

  Lemma entails_model_valid cls cl : entails cls cl ->
    forall m, is_model cls m -> valid_clause m cl.
  Proof.
    induction 1.
    - intros m ism.
      destruct concl0 as [concl k].
      apply valid_clause_intro => z hmin.
      eapply min_premise_spec_aux in hmin as [hle [x [hin heq]]].
      specialize (hle _ H). depelim hle.
      destruct level_value eqn:hl => //. noconf H1.
      constructor. lia.
    - intros.
      specialize (IHentails m H2).
      depelim H.
      * destruct cl as [premsc conclc].
        noconf H0.
        eapply Clauses.for_all_spec in H3.
        eapply H3 in H. 2:tc.
        destruct concl0 as [concl k].
        eapply valid_clause_intro => z eqmin.
        have mins := min_premise_subset m (add_prems n premsc) prems H2.
        rewrite eqmin in mins; depelim mins.
        destruct conclc as [conclc k'].
        have vshift : valid_clause m (add_prems n premsc, add_expr n (conclc, k')).
        { now eapply (valid_clause_shift _ n) in H. }
        have hv := valid_clause_elim vshift _ H4.
        depelim hv. rename y0 into vmconclc.
        eapply (min_premise_add_infers _ _ (add_expr n (conclc, k'))) in eqmin as [minadd [eqminadd disj]]; tea.
        move/valid_clause_elim: IHentails => //=.
        move/(_ _ eqminadd).
        destruct disj as [[eq le']| ->].
        + move=> h. cbn in le'. cbn in eq. subst minadd.
          depelim h. rewrite H8. constructor. lia.
        + intros h; depelim h. rewrite H8; constructor; lia.
      * destruct concl0 as [concl0 k'].
        apply valid_clause_intro => z hmin.
        have mins := min_premise_subset m _ _ H1.
        rewrite min_premise_singleton in mins.
        specialize (H1 (x, k+1)); forward H1 by now apply LevelExprSet.singleton_spec.
        have hadd := min_premise_add_down H1 _ hmin.
        exact: valid_clause_elim IHentails _ hadd.
  Qed.

End Model.