#[program]
Definition of_level_map_n (m : LevelMap.t nat) V n (hne : ~ LevelMap.Empty m) : nonEmptyLevelExprSet :=
  {| t_set := LevelMap.fold (fun l k acc =>
    if LevelSet.mem l V then LevelExprSet.add (l, n + k) acc else
    LevelExprSet.add (l, k) acc) m LevelExprSet.empty |}.
Next Obligation. Admitted.

Lemma of_level_map_n_spec m V hne :
  forall l n k, LevelExprSet.In (l, k) (of_level_map_n m V n hne) ->
    (exists k', LevelMap.MapsTo l k' m /\
      (LevelSet.In l V -> k = n + k') /\
      (~ LevelSet.In l V -> k = k')).
Proof.
Admitted.

Lemma of_level_map_n_spec_inv m V hne :
  forall l n k, LevelMap.MapsTo l k m ->
    exists k', LevelExprSet.In (l, k') (of_level_map_n m V n hne) /\
      (LevelSet.In l V -> k' = n + k) /\
      (~ LevelSet.In l V -> k' = k).
Proof.
Admitted.


Lemma of_level_map_of_level_map_n m V ne :
  of_level_map m ne = of_level_map_n m V 0 ne.
Proof.
  apply eq_univ'.
  intros [l k].
  rewrite of_level_map_spec.
  firstorder.
  - unshelve eapply (of_level_map_n_spec_inv _ V ne _ 0) in H.
    destruct H as [k' [hin [inv ninv]]].
    destruct (inLevelSet V l) as [hvin|hnin].
    specialize (inv hvin). cbn in inv. now subst k'.
    specialize (ninv hnin). cbn in ninv. now subst.
  - eapply of_level_map_n_spec in H as [k' [hm [hin hnin]]].
    destruct (inLevelSet V l) as [hvin|hvnin].
    now rewrite (hin hvin).
    now rewrite (hnin hvnin).
Qed.

Lemma of_level_map_n_only_model m V n ne :

  only_model_of V m ->
  of_level_map_n m V n ne = add_prems n (of_level_map m ne).
Proof.
  intros om.
  apply eq_univ'.
  intros [l k].
  rewrite In_add_prems.
  split.
  - move/of_level_map_n_spec => [k' [hm [hin hnin]]].
    destruct (inLevelSet V l) as [hvin|hvnin].
    * rewrite (hin hvin). exists (l, k').
      rewrite of_level_map_spec. split => //. rewrite /add_expr. lia_f_equal.
    * elim hvnin. apply om. now exists k'.
  - intros [[? ?] [hin heq]]. unfold add_expr in heq; noconf heq.
    unshelve eapply of_level_map_spec in hin.
    have inv : LevelSet.In l V.
    { apply om. now exists n0. }
    eapply (of_level_map_n_spec_inv _ V ne _ n) in hin as [k' [hin [hinv hninv]]].
    specialize (hinv inv). subst k'. now rewrite Nat.add_comm.
Qed.


(* Lemma entails_any V cls m nem m' nem' :
  only_model_of V m ->
  cls ⊢a of_level_map m nem → of_level_map m' nem' ->
  model_rel_partial Nat.lt V m m' ->
  cls ⊢a of_level_map m nem → of_level_map_n m V 1 nem.
Proof.
  intros tot cla mp [l k].
  move/of_level_map_n_spec.
  intros [k' [hm [hin hnin]]].
  destruct (LevelSetDecide.MSetDecideAuxiliary.dec_In l V).
  rewrite (hin H).
  rewrite -[1 + _]Nat.add_1_r.
  eapply entails_any_one; tea.
  rewrite (hnin H).
  constructor. now rewrite of_level_map_spec.
Qed. *)

(* Lemma entails_any V cls m nem m' nem' :
  model_of V m ->
  model_rel_partial Z.lt V m m' ->
  cls ⊢a of_level_map_n m V 1 nem → of_level_map_n m V 2 nem.
Proof. *)


(* Lemma entails_concls cls V n m hne hne' :
  model_of V m ->
  entails_all cls (of_level_map_n m V n hne) (of_level_set V n hne').
Proof.
  move=> tot [l k].
  rewrite levelexprset_of_levels_spec => [] [] hin ->.
  specialize (tot _ hin) as [k' hm].
  move/of_level_map_n_spec_inv in hm.
  specialize (hm V hne n) as [k'' [hm [hin' hnin]]].
  specialize (hin' hin). subst k''. cbn in *.
  exists
  depind ent.
  - move: H.
    rewrite of_level_map_n_spec => [] [k' [mt [hin hnin]]].
    destruct (inLevelSet V l) as [H|H].
    * now left.
    * right. apply hnin in H. now subst k'.
  - specialize (IHent _ _ _ en l).

  intros [] *)

(*
Lemma strictly_updates_restrict cls V m m' :
  strictly_updates cls V m m' ->
  (forall cl, Clauses.In cl (cls_diff cls V) -> valid_clause m cl) ->
  strictly_updates (cls ⇂ V) V m m'.
Proof.
  induction 1.
  - intros hcl. constructor; auto.
    move: {hcl} (hcl cl).
    rewrite Clauses.diff_spec in_clauses_with_concl in_restrict_clauses.
    destruct cl as [prems [concl k]]; cbn.
    move=> h. split => //. eapply in_singleton.
    forward h.
    { split. split => //. apply in_singleton.
    intros [insing hle incl'].
    assert (~ LevelSet.Empty (levels prems)). admit.
    have eqc : (forall l, LevelSet.In l (levels prems) -> l = concl).
    { move=> l /hle. now rewrite LevelSet.singleton_spec. }
    move: H0; rewrite /valid_clause //=.
    intros [v [hmin hlt la eqm]].
    destruct min_premise eqn:hm => //.
    have [minple [minprem [inprems eqm]]] := min_premise_spec m prems.


    assert (LevelSet.Equal (levels prems) (LevelSet.singleton concl)). split => //. lsets.
    rewrite LevelSet.singleton_spec => ->. destruct (LevelSet.choose (levels prems)) eqn:hc.
    apply LevelSet.choose_spec1 in hc. apply hle in hc. apply LevelSet.singleton_spec in hc; red in hc; subst.

*)

(*
Lemma strictly_updates_entails_loop_relax cls V mzero hne m :
  let bound := v_minus_w_bound V m in
  let maxgain := max_gain cls in
  let n := Z.to_nat bound + maxgain in
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_map_n mzero V n hne) (of_level_map_n mzero V (n + 1) hne).
Proof.
  move=> bound maxgain n tot su.
  have mp := strictly_updates_model_lt su tot.
  have nem := strictly_updates_non_empty_map su.
  eapply (strictly_updates_entails hne nem) in su; tea.
  eapply entails_any in su; tea.
  eapply (entails_all_shift n) in su.
  rewrite -of_level_map_of_level_map_n.
Qed.
*)
(* Lemma of_level_map_n_split m V n hne : of_level_map_n m V n hne = of_level_set V n hne'  *)
Lemma max_premise_model_unique cls m : max_premise_model cls clauses_levels m -> m = max_premise_map cls.
Proof.
Admitted.


(*
Lemma strictly_updates_entails_loop_relax' ocls cls V (hne : ~ LevelSet.Empty V) mzero m :
  above_max_premise_model ocls mzero ->
  cls ⊂_clset ocls ->
  V =_lset clauses_levels cls ->
  model_of V mzero ->
  strictly_updates cls V mzero m ->
  entails_all cls (of_level_set V (max_clause_premise cls) hne)
    (of_level_set V (max_clause_premise cls + 1) hne).
Proof.
  move=> habove hincl hv tot su.
  eapply strictly_updates_entails_loop_relax; tea. *)



(*
Lemma above_max_premise_model_strengthen {cls cls' m} :
  cls ⊂_clset cls' ->
  above_max_premise_model cls m ->
  above_max_premise_model cls' m.
Proof.
  intros hincl [[V' su]|eq].
  left. 2:{ subst. red. } exists V'.
  eapply strictly_updates_weaken; tea. red in ha.
  move/(hmon _ _ hincl)/(ha l) => ha'.
  eapply infer_atom_downward; tea.
  apply max_clause_premise_mon in hincl. lia.
Qed. *)
Lemma model_max_max_premise_map cls : (model_max (max_premise_map cls)) = max_clause_premise cls.
Proof.
Admitted.



Definition new_model m V newk : model :=
  LevelMap.fold (fun l k acc =>
    let k' := if LevelSet.mem l V then newk else k in
    LevelMap.add l k' acc) m (LevelMap.empty _).

Lemma new_model_spec m V newk l k :
  LevelMap.MapsTo l k (new_model m V newk) ->
  (exists k', LevelMap.MapsTo l k' m /\
    if LevelSet.mem l V then k = newk else k = k').
Proof. Admitted.

Definition domain (l : LevelMap.t (option Z)) : LevelSet.t :=
  LevelSetProp.of_list (List.map fst (LevelMap.elements l)).


(* (forall cl', Clauses.In cl cls -> forall l k, LevelExprSet.In (l, k) (premise cl') -> k <= n) *)
Lemma strictly_updates_entails_loop_max cls V (hne : ~ LevelSet.Empty V) m :
  V =_lset clauses_levels cls ->
  strictly_updates cls V (max_premise_map cls) m ->
  entails_all cls (of_level_set V ((model_max (max_premise_map cls))) hne)
    (of_level_set V ((model_max (max_premise_map cls)) + 1) hne).
Proof.
  intros.
  rewrite !model_max_max_premise_map.
  eapply strictly_updates_entails_loop; tea.
  eapply max_premise_model_exists.
  apply todo.
Qed.


Definition find_max (ls : LevelExprSet.t) (l : Level.t) :=
  LevelExprSet.fold (fun '(l', k) acc => if eqb l l' then opt_max (Some k) acc else acc) ls None.

Inductive find_max_spec ls l : option nat -> Prop :=
| find_max_ex m : LevelExprSet.In (l, m) ls -> (forall k, LevelExprSet.In (l, k) ls -> k <= m) -> find_max_spec ls l (Some m)
| find_max_absent : ~ (exists k, LevelExprSet.In (l, k) ls) -> find_max_spec ls l None.

Lemma find_max_correct ls l : find_max_spec ls l (find_max ls l).
Proof.
  unfold find_max.
  apply: (LevelExprSetProp.fold_rec (P := fun ls a => find_max_spec ls l a)).
  - intros s' ise; constructor. intros [k hin]. now apply ise in hin.
  - intros x a s' s'' hin hnotin hadd hspec.
    destruct x as [l' k].
    destruct (eqb_spec l l'); subst.
    * depelim hspec.
      { constructor. destruct (Nat.max_spec k m) as [[hle hm]|[hle hm]].
        + rewrite hm. apply hadd; right; apply H.
        + rewrite hm. apply hadd; left; reflexivity.
        + intros k' hin'. apply hadd in hin' as [].
          { noconf H1. lia. }
          { specialize (H0 _ H1). lia. } }
      { constructor. apply hadd; now left.
        intros k0 hin'. apply hadd in hin' as [].
        { noconf H0; reflexivity. }
        { elim H. now exists k0. } }
    * depelim hspec; constructor; eauto.
      + apply hadd; now right.
      + intros k' hin'. apply hadd in hin' as [].
        { noconf H2. congruence. }
        now apply H0 in H2.
      + intros [k0 hk0]. apply hadd in hk0 as [].
        { noconf H1; congruence. }
        apply H. now exists k0.
Qed.


(* Lemma valuation_of_model_pos l k model : LevelMap.MapsTo l (Z.to_nat k) (valuation_of_model model) -> (k >= 0)%Z.
Proof.
  unfold valuation_of_model.
  revert l k.
  eapply LevelMapFact.fold_rec.
  - intros. now rewrite LevelMapFact.F.empty_mapsto_iff in H0.
  - intros l0 k0 e m' m'' me nk hadd hind l k.
    rewrite LevelMapFact.F.add_mapsto_iff.
    intros [].
    * destruct H. red in H; subst.
      destruct k0.
      { have hmax := (model_max_spec model l (Some z) me). depelim hmax.
        have hmin := (model_min_spec model l (Some z) me). depelim hmin.
        assert (0 <= model_max model)%Z. admit.
        assert (model_min model <= 0)%Z. admit.
        assert (model_max model - option_get 0%Z (Some z) - model_min model = k)%Z. admit.
        cbn in H4.
        lia. *)




Definition model_above cls m := forall l,
  LevelSet.In l (clauses_levels cls) ->
  exists k', LevelMap.MapsTo l k' m /\ max_clause_premise cls <= k'.

Lemma model_above_infers {cls m} :
  model_above cls m ->
  (forall l, LevelSet.In l (clauses_levels cls) -> infers_atom m l (max_clause_premise cls)).
Proof.
Admitted.

Lemma model_above_update {cls V' m m'} :
  model_above cls m ->
  strictly_updates cls V' m m' ->
  model_above cls m'.
Proof.
  move=> above /strictly_updates_ext.
  move=> le l /above => [] [] k' [] hm hle.
  apply le in hm as [k'' [hin' le']].
  exists k''. split => //. now transitivity k'.
Qed.

Lemma max_premise_model_above cls m : max_premise_model cls clauses_levels m -> model_above cls m.
Admitted.


(* Lemma max_premise_model_above cls sel sel' m :
  (sel' cls ⊂_lset sel cls) ->
  max_premise_model cls sel m ->
  above_max_premise_model cls m.
Proof.
  move=> incl mp l hl; move: (proj1 mp l (incl _ hl)); rewrite /infers_atom.
  move/level_value_MapsTo => ->. reflexivity.
Qed. *)

