

Definition split_clauses m cls :=
  Clauses.partition (is_enabled_clause m) cls.

Definition enabled_clauses_of m cls := (split_clauses m cls).1.
Definition disabled_clauses_of m cls := (split_clauses m cls).2.

Lemma split_clauses_spec_1 m cls :
  cls =_clset Clauses.union (enabled_clauses_of m cls) (disabled_clauses_of m cls).
Proof. Admitted.

Lemma enabled_clauses_spec m cl cls : Clauses.In cl (enabled_clauses_of m cls) <-> Clauses.In cl cls /\ enabled_clause m cl.
Admitted.

Lemma disabled_clauses_spec m cl cls : Clauses.In cl (disabled_clauses_of m cls) <-> Clauses.In cl cls /\ ~ enabled_clause m cl.
Admitted.

Lemma nenabled_clause m cl : ~ enabled_clause m cl <-> min_premise m (premise cl) = None.
Proof.
  case: (reflect_enabled m cl) => //.
  split => //. red in p. firstorder. congruence.
  firstorder. cbn in H. destruct min_premise => //.
  destruct (H _ eq_refl).
Qed.

Lemma is_model_split m cls :
  is_model m cls <-> (is_total_model m (enabled_clauses_of m cls)).
Proof.
  split.
  - move/Clauses.for_all_spec => ism.
    split.
    intros cl. now rewrite enabled_clauses_spec. tc.
    apply Clauses.for_all_spec. tc.
    move=> cl /enabled_clauses_spec => -[] /ism //.
  - move=> -[]. intros en. red in en. red in en.
    intros ism. rewrite (split_clauses_spec_1 m cls).
    eapply is_model_union. auto.
    eapply Clauses.for_all_spec. tc.
    move=> [prems [concl k]] /disabled_clauses_spec -[] hin hen.
    Search enabled_clause.
    apply valid_clause_intro.
    now move/nenabled_clause: hen => ->.
Qed.

Lemma enabled_clause_defined {m cl} :
  enabled_clause m cl ->
  defined_model_of (NES.levels (premise cl)) m.
Proof.
  destruct cl as [prems [concl k]]; cbn.
  move=> -[] z //= /min_premise_spec' hl.
  move=> l /NES.levels_spec -[] k' /hl [v] [] hm _.
  eapply level_value_MapsTo' in hm. now eexists.
Qed.

Lemma check_clause_invalid_Z cls cl mcheck :
  check_gen cls cl = Invalid mcheck -> ~ valid_clause_Z (enabled_clauses_of mcheck cls) cl.
Proof.
  move/check_invalid => -[ism mof min en inv] nv.
  destruct cl as [prems [concl k]].
  destruct (level_value mcheck concl) eqn:he.
  * specialize (nv (Z_valuation_of_model mcheck)).
    forward nv. apply valuation_of_model_pos.
    forward nv. apply is_model_split in ism.
    apply valid_clauses_model. apply ism. apply ism.
    move: nv.
    rewrite def_clause_sem_valid.
    unfold defined_model_of.
    intros l; rewrite clause_levels_spec //=.
    intros [hin|eq].
    move/enabled_clause_defined: en.
    now move/(_ _ hin). subst.
    eapply level_value_MapsTo' in he. now eexists.
    contradiction.
  * apply is_model_split in ism.
    destruct en as [minp eqmin].
    remember (interp_nes (Z_valuation_of_model mcheck) prems) as iprems eqn:hprems.
    symmetry in hprems.
    set val := fun l =>
      if l == concl then iprems + 1 - k
      else Z_valuation_of_model mcheck l.
    specialize (nv val).
    forward nv. admit.
    forward nv. admit.
    move: nv; cbn.
    rewrite {1}/val eqb_refl.
    have eqi : interp_nes val prems = interp_nes (Z_valuation_of_model mcheck) prems.
    move/min_premise_spec': eqmin => //=.
    eapply interp_nes_elim. tc.
    intros [le lek] h. rewrite /interp_expr.
    rewrite interp_nes_singleton /interp_expr //=.
    specialize (h le lek). admit.
    intros. admit.
    rewrite !eqi hprems. lia.
Admitted.

Lemma contra A B : (A -> B) -> (~ B -> ~ A).
Proof. intros f nb a. exact (nb (f a)). Qed.

Lemma invalid_clause_Z_ex cls cl :
  (exists v : Level.t -> Z, positive_valuation v /\ clauses_sem v cls /\ ~ clause_sem v cl) ->
   ~ valid_clause_Z cls cl.
Proof.
  intros [v [vpos [cs ncsem]]].
  red. move/(_ v vpos cs). contradiction.
Qed.

(*
  Check for validity in Z: cls |= cl.

  Take an existing total model m of cls.
  Add clauses low: v -> Set forall v. Ensure m[Set] = model_max m.
  Add clauses high Set + 1 + (model_max - m[v]) -> v for every v, trivially
  satisfied: as min_premise m [Set + 1 + (model_max m - m[v])] =
    model_max m - (1 + (model_max m - model_min m)) = - 1 - model_min m <= m[v].

  So m is also a total model of cls + low + high.
  Launch checking for cls' ⊃ cls.
  If we find a loop we get cls' |- loop, but as m is a total model of cls', that implies false in Z.
  Otherwise we get a valid model [mcheck |= cls']
  and either valid_clause mcheck cl or ~ valid_clause mcheck cl.
  - If valid_clause mcheck cl, then
    mcheck |= cls as cls ⊂ cls'.
    So we have a valid clause in Zinf and Z, but not a proof
    for every valuation...

  E.g check x >= 0, y >= 0 -> x >= y.
  adds 0 >= x and 0 >= y, forcing x = y = 0!
  Add instead just 0 >= y, not better, it entails x >= y = 0.
  Add instead just ⊥ + 1 >= y: starting from { x = 0; y = None; ⊥ = None }.
  we get
  { x = 0; y = None; ⊥ = 0 },
  { x = 0; y = -1; ⊥ = 0 }. Good, does not entail x >= y
  But x + 1 >= y ?
  { x = 1; y = None; ⊥ = None } ->
  { x = 1; y = None; ⊥ = 1 } ->
  { x = 1; y = 0; ⊥ = 1 }.
  Ok as well.

  - If ~ valid_clause mcheck cl.
    Then we have clauses_sem (Z_valuation_of_model mcheck) cls',
    so clauses_sem (Z_valuation_of_model mcheck) cls, and
    ~ clause_sem (Z_valuation_of_model mcheck) cl.
*)

Definition bound_clauses (m : Model.model) :=
  LevelMap.fold (fun l k =>
    Clauses.add (singleton (Level.zero, model_max m + 1 - option_get 0 k), (l, 0))) m Clauses.empty.

Lemma bound_clauses_spec {cl m} :
  Clauses.In cl (bound_clauses m) ->
  exists l k, LevelMap.MapsTo l k m /\ cl = (singleton (Level.zero, model_max m + 1 - option_get 0 k), (l, 0)).
Proof.
  rewrite /bound_clauses.
  set (mmax := model_max m). clearbody mmax.
  eapply LevelMapFact.fold_rec.
  - intros s' he hin. clsets.
  - intros x a cls s' s'' hin hnin hadd ih.
    rsets. destruct H.
    * subst cl. exists x, a. split.
      eapply levelmap_add_spec in hadd. rewrite hadd.
      apply LevelMapFact.F.add_mapsto_iff. now left. reflexivity.
    * eapply levelmap_add_spec in hadd.
      specialize (ih H) as [l []]. exists l, x0. split => //.
      rewrite hadd.
      apply LevelMapFact.F.add_mapsto_iff. right; split => //.
      intros ->. destruct H0. subst cl.
      apply hnin; now eexists.
      apply H0. apply H0.
Qed.
(*
Lemma bound_clauses_spec_inv {l k V} :
  LevelSet.In l V ->
  Clauses.In (singleton (Level.zero, k), (l, 0)) (bound_clauses k V).
Proof.
  rewrite /bound_clauses.
  eapply LevelSetProp.fold_rec.
  - intros s' he hin. lsets.
  - intros x a s' s'' hin hnin hadd ih.
    rsets. apply hadd in H as [H|H].
    * subst l. now left.
    * specialize (ih H). now right.
Qed. *)

Lemma bound_clauses_prop m cls :
  is_model m cls -> is_model m (bound_clauses m).
Proof.
  intros ism.
  apply is_modelP => cl /bound_clauses_spec -[] l [k] [] hm heq.
  subst cl.
  apply valid_clause_intro => z.
  rewrite min_premise_singleton /min_atom_value.
  destruct level_value eqn:hl => //=.
  have hz : z0 = model_max m. todo "zero spec".
  subst z0.
  intros [=].
  have hzeq : z = - 1 + option_get 0 k. lia.
  rewrite hzeq.
  rewrite (level_value_MapsTo hm). destruct k. cbn in *; subst.
  constructor. lia.
  cbn in *. subst z.
  todo "defined level".
Qed.

Lemma bound_clauses_ext m m' :
  m' ⩽ m -> is_model m (bound_clauses m) -> is_model m' (bound_clauses m).
Proof.
  intros hext.
Abort.


Definition check_gen_Z (m : t) cl :=
  check_gen (Clauses.union (bound_clauses m) (clauses m)) cl.

Lemma enabled_clause_mcheck_zero_enabled mcheck cl cls :
  enabled_clause mcheck cl ->
  is_model mcheck cls ->
  Deciders.above_zero_declared (clauses_levels cls) cls ->
  exists k, LevelMap.MapsTo Level.zero (Some k) mcheck.
Proof.
Admitted.

Lemma enabled_clause_mcheck_all_enabled mcheck cl cls :
  enabled_clause mcheck cl ->
  is_model mcheck cls ->
  Deciders.above_zero_declared (clauses_levels cls) cls ->
  forall l, LevelMap.In l mcheck -> exists k, LevelMap.MapsTo l (Some k) mcheck.
Proof.
Admitted.

Lemma option_map_add_zero k : option_map (Z.add 0) k = k.
Proof. destruct k => //. Qed.

Lemma check_clause_invalid_Z_dis m cl :
  clause_levels cl ⊂_lset levels m ->
  check_gen_Z m cl = Valid -> valid_clause_Z (clauses m) cl.
Proof.
  intros hwf.
  unfold check_gen_Z.
  set (bcls := bound_clauses _).
  set (cls' := Clauses.union _ _).
  move/check_gen_entails.
  rewrite entails_completeness.
  intros hm. eapply valid_total_models_Z_models.
  intros m' tot def.
  specialize (hm (option Z) _ (opt_valuation_of_model m')).
  apply clause_sem_valid. apply hm.
  eapply clauses_sem_union.
  destruct tot as [en ism].
  split; revgoals.
  eapply clauses_sem_valid; exact ism. revgoals. eauto.
  have hmin : minimal_above (clauses m) (check_init_model (clauses m) cl) m.
  admit.
  red in hmin.
  specialize (hmin m'). forward hmin. admit.
  forward hmin. exact ism.
  intros cl' hin.
  eapply bound_clauses_spec in hin as [l [k [hm' heq]]].
  subst cl'. cbn -[Semilattice.eq]. rewrite interp_nes_singleton /interp_expr.
  rewrite /opt_valuation_of_model.
  case: (find_spec l m').
  intros k0 hml. destruct k0 => //. 2:{ todo "m' must have a value for l". }
  case: (find_spec Level.zero m').
  intros kz hmz. destruct kz. 2:{ todo "zero must have a value". }
  rewrite option_map_add_zero.
  destruct k.
  have hmax : z0 = model_max m'. admit.
  subst z0.
  have hv := valuation_of_value_pos hml.
  cbn -[Semilattice.le]. cbn.
  eapply hmin in hm' as [k' []].
  eapply LevelMapFact.F.MapsTo_fun in hml; tea. subst k'. depelim H0.
  rewrite /valuation_of_value.
  have hmleq : model_max m <= model_max m'. admit.
  unfold valuation_of_value in hv.
  have hv' := valuation_of_value_pos H0.
  unfold valuation_of_value in hv'.
  have hmeq : (model_max m' - model_max m' - model_min m') = - model_min m'. lia.
  rewrite hmeq. lia.
  cbn.
  todo "scope".
  todo "zero defined".
  todo "zero defined".
Qed.

Lemma check_clause_invalid_Z_dis m cl mcheck :
  clause_levels cl ⊂_lset levels m ->
  check_gen_Z m cl = Invalid mcheck -> ~ valid_clause_Z (clauses m) cl.
Proof.
  intros hwf.
  unfold check_gen_Z.
  set (bcls := bound_clauses _ _).
  set (cls' := Clauses.union _ _).
  move/check_invalid => -[ism mof hmin en inval].
  apply invalid_clause_Z_ex.
  exists (Z_valuation_of_model mcheck).
  split. apply valuation_of_model_pos.
  have hab := above_zero_declared m.
  have hdef0 : defined_model_of (clauses_levels cls') mcheck.
  { eapply enabled_clause_defined in en.
    specialize (hab (choose (premise cl)).1).
    forward hab. apply hwf.
    eapply clause_levels_spec. left.
    eapply NES.levels_spec. exists (choose (premise cl)).2.
    destruct (choose _) eqn:hc. cbn. rewrite -hc.
    eapply choose_spec.
    red in hab.
  }
  split.
  eapply valid_clauses_model. admit.
  eapply is_model_subset; tea. subst cls'; clsets.
  intros csem.
  eapply def_clause_sem_valid in csem. contradiction.
  eapply enabled_clause_defined in en. admit.
Qed.