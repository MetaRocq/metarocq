(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From MetaRocq.Common Require Import Common Interfaces HornClauses.
From Equations Require Import Equations.
Set Equations Transparent.

Module Model (LS : LevelSets).
  Module Export Clauses := Clauses(LS).

  Definition model := LevelMap.t (option Z).
  Definition equal_model (m m' : model) := LevelMap.Equal m m'.

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
    let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
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

  Infix "=m" := LevelMap.Equal (at level 50).

  Definition strict_update m '(prems, (concl, k)) m' :=
    exists v,
    [/\ min_premise m prems = Some v, ~~ level_value_above m concl (k + v) &
    m' =m (LevelMap.add concl (Some (k + v)) m)].

  Inductive strictly_updates cls : LevelSet.t -> model -> model -> Prop :=
  | update_one m cl m' : Clauses.In cl cls ->
    strict_update m cl m' -> strictly_updates cls (LevelSet.singleton (clause_conclusion cl)) m m'
  | update_trans {ls ls' m m' m''} :
    strictly_updates cls ls m m' ->
    strictly_updates cls ls' m' m'' ->
    strictly_updates cls (LevelSet.union ls ls') m m''.

  Lemma strictly_updates_step cls w m m' m'' :
    strictly_updates cls w m m' ->
    forall cl, Clauses.In cl cls -> strict_update m' cl m'' ->
    strictly_updates cls (LevelSet.add (clause_conclusion cl) w) m m''.
  Proof.
    induction 1.
    - intros.
      replace (LevelSet.add (clause_conclusion cl0) (LevelSet.singleton (clause_conclusion cl)))
        with (LevelSet.union (LevelSet.singleton (clause_conclusion cl)) (LevelSet.singleton (clause_conclusion cl0))).
      eapply update_trans; eapply update_one; tea.
      eapply LevelSet.eq_leibniz. red. lsets.
    - intros.
      specialize (IHstrictly_updates2 _ H1 H2).
      replace (LevelSet.add (clause_conclusion cl) (LevelSet.union ls ls'))
        with (LevelSet.union ls (LevelSet.add (clause_conclusion cl) ls')).
      eapply update_trans; tea.
      eapply LevelSet.eq_leibniz. red. lsets.
  Qed.

  Lemma strictly_updates_weaken cls w cls' :
    Clauses.Subset cls cls' ->
    forall m m', strictly_updates cls w m m' -> strictly_updates cls' w m m'.
  Proof.
    intros hcls m m'.
    induction 1. constructor => //. now eapply hcls.
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

  #[export] Instance is_model_proper : Proper (Clauses.Equal ==> eq ==> eq) is_model.
  Proof.
    intros cl cl' eqcl x y ->. unfold is_model. now rewrite eqcl.
  Qed.

  #[export] Instance equal_model_equiv : Equivalence equal_model.
  Proof. unfold equal_model.
    split; try econstructor; eauto.
    red. intros. now symmetry.
    red; intros. now transitivity y.
  Qed.

  #[export] Instance level_value_proper : Proper (equal_model ==> eq ==> eq) level_value.
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

  #[export] Instance min_atom_value_proper : Proper (LevelMap.Equal ==> eq ==> eq) min_atom_value.
  Proof.
    intros m m' eqm ? ? ->. unfold min_atom_value.
    destruct y => //.
    now rewrite eqm.
  Qed.

  #[export] Instance min_premise_proper : Proper (LevelMap.Equal ==> eq ==> eq) min_premise.
  Proof.
    intros m m' eq ? ? ->.
    unfold min_premise.
    destruct to_nonempty_list.
    now setoid_rewrite eq.
  Qed.

  #[export] Instance update_model_proper : Proper (LevelMap.Equal ==> eq ==> eq ==> LevelMap.Equal) update_model.
  Proof.
    intros m m' hm ? ? -> ? ? ->.
    unfold update_model.
    now rewrite hm.
  Qed.

  #[export] Instance level_value_above_proper : Proper (LevelMap.Equal ==> eq ==> eq ==> eq) level_value_above.
  Proof.
    intros m m' hm ? ? -> ? ? ->.
    unfold level_value_above.
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

  #[export] Instance check_model_aux_proper : Proper (Clauses.Equal ==> eq ==> eq) check_model_aux.
  Proof.
    intros ? ? eq ? ? ->.
    rewrite /check_model_aux.
    rewrite !ClausesProp.fold_spec_right.
    now rewrite eq.
  Qed.

  #[export] Instance check_model_proper : Proper (Clauses.Equal ==> eq ==> eq) check_model.
  Proof.
    intros cls cls' eq.
    intros wm wm' ->.
    unfold check_model.
    destruct (check_model_aux cls _) eqn:eqc.
    destruct (check_model_aux cls' _) eqn:eqc' => //.
    pose proof (check_model_aux_proper cls cls' eq ([], wm'.2) _ eq_refl).
    rewrite eqc eqc' in H. noconf H.
    destruct l => //.
  Qed.

  Instance strictly_updates_proper : Proper (Clauses.Equal ==> LevelSet.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) strictly_updates.
  Proof.
    intros ? ? H ? ? H' ? ? H'' ? ? H'''.
    eapply LevelSet.eq_leibniz in H'. subst y0.
    split.
    induction 1 in y, H, y1, H'', y2, H'''|- * ; [econstructor 1|econstructor 2]; eauto.
    now rewrite <- H. move: H1; unfold strict_update. destruct cl as [premse []].
    intros [v []]; exists v; split;
    try setoid_rewrite <- H;
    try setoid_rewrite <- H'';
    try setoid_rewrite <- H'''; firstorder.
    eapply IHstrictly_updates1; firstorder. firstorder.
    induction 1 in x, H, x1, H'', x2, H'''|- * ; [econstructor 1|econstructor 2]; eauto.
    now rewrite H. move: H1; unfold strict_update. destruct cl as [premse []].
    intros [v []]; exists v; split;
    try setoid_rewrite H;
    try setoid_rewrite H'';
    try setoid_rewrite H'''; firstorder.
    eapply IHstrictly_updates1; firstorder. firstorder.
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
      + intros _. split => //. constructor. clsets. unfold strict_update.
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
          replace (LevelSetProp.of_list [clause_conclusion x]) with (LevelSet.singleton (clause_conclusion x)).
          eapply ClausesProp.Add_Equal in hadd. rewrite hadd. eapply strictly_updates_weaken; tea. clsets.
          eapply LevelSet.eq_leibniz. red. intros ?. rewrite LevelSetProp.of_list_1. firstorder. constructor.
          rewrite LevelSet.singleton_spec in H3. firstorder. depelim H3. subst. lsets. depelim H3. }
        specialize (H0 H4).
        destruct (eqb_spec w'' w'); subst.
        { specialize (H2 eq_refl) as []; subst m''.
          destruct H0 as [pref []]. subst w'. exists pref; split => //.
          eapply strictly_updates_weaken; tea. intros ? ?. eapply hadd. clsets. }
        forward H3 by auto. destruct H3 as [->].
        destruct H0 as [pref [-> su]]. eexists (clause_conclusion x :: pref); split => //.
        replace (LevelSetProp.of_list (clause_conclusion x :: pref)) with (LevelSet.union (LevelSetProp.of_list pref) (LevelSet.singleton (clause_conclusion x))).
        eapply (strictly_updates_weaken _ _ s'') in su; tea; try firstorder.
        eapply (strictly_updates_weaken _ _ s'') in H3; tea; try firstorder.
        2:{ intros ?; rewrite Clauses.singleton_spec. intros ->. now apply hadd. }
        exact: update_trans _ su H3.
        apply LevelSet.eq_leibniz. intros ?. cbn. lsets.
  Qed.

  Lemma check_model_spec {cls w m w' m'} :
    check_model cls (w, m) = Some (w', m') ->
    exists w'', strictly_updates cls w'' m m' /\ w' = LevelSet.union w w''.
  Proof.
    unfold check_model.
    destruct check_model_aux eqn:cm.
    apply check_model_aux_spec in cm as [].
    destruct l => //. forward H0. auto with datatypes.
    intros [= <- <-]. destruct H0 as [pref [heq su]].
    rewrite app_nil_r in heq. subst pref.
    exists (LevelSetProp.of_list (t :: l)). split => //.
    eapply LevelSet.eq_leibniz. intros ?. cbn. lsets.
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
    - eapply strict_update_invalid in H0.
      apply/negbT. unfold is_model.
      destruct Clauses.for_all eqn:fa => //.
      eapply Clauses.for_all_spec in fa; tc. eapply fa in H.
      now rewrite H in H0.
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
    move/check_model_spec => [w'' [su ->]].
    intros cls' su'. split.
    eapply update_trans; eapply strictly_updates_weaken; tea; clsets. lsets.
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
      destruct H0 as [? [? ? heq]].
      setoid_rewrite heq in he. eapply (he (Some (k + x))); cbn.
      rewrite LevelMapFact.F.add_mapsto_iff. firstorder.
    - intros he. now apply IHstrictly_updates2.
  Qed.

  Lemma strictly_updates_incl {cls W m m'} :
    strictly_updates cls W m m' -> W ⊂_lset clauses_conclusions cls.
  Proof.
    induction 1.
    - intros x. rewrite clauses_conclusions_spec. firstorder. exists cl.
      eapply LevelSet.singleton_spec in H1; red in H1; subst. split => //.
    - lsets.
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
    now eapply strict_update_ext in H0.
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

  Import LevelExprSet.
  Import NonEmptySetFacts.

  Definition max_premise_value (m : model) (l : premises) : option Z :=
    let (hd, tl) := NonEmptySetFacts.to_nonempty_list l in
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
    (a <= lv - l.2).
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
    rewrite !levelexprset_levels_spec.
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


End Model.