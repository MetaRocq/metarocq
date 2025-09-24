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



Definition add_max l k m :=
  match LevelMap.find l m with
  | Some k' =>
    if (k' <? k)%nat then LevelMap.add l k m
    else m
  | _ => LevelMap.add l k m
 end.

Definition min_model_map (m : model) cls : model :=
  Clauses.fold (fun '(cl, concl) acc =>
    LevelExprSet.fold (fun '(l, k) acc =>
      add_max l k acc) cl (add_max (levelexpr_level concl) 0 acc)) cls m.

Lemma In_add_max l l' k acc :
  LevelMap.In (elt:=nat) l (add_max l' k acc) <->
  (l = l' \/ LevelMap.In l acc).
Proof.
  unfold add_max.
  destruct LevelMap.find eqn:hl.
  - case: Nat.ltb_spec.
    + rewrite LevelMapFact.F.add_in_iff /Level.eq.
      firstorder eauto.
    + intros. intuition auto. subst.
      now rewrite LevelMapFact.F.in_find_iff hl.
  - LevelMapFact.F.map_iff. rewrite /Level.eq. intuition auto.
Qed.

Definition is_max k' k l acc :=
  match LevelMap.find l acc with
  | Some k'' => k' = Nat.max k k''
  | _ => k' = k
  end.


Definition min_model_map (m : model) cls : model :=
  Clauses.fold (fun '(cl, concl) acc =>
    LevelExprSet.fold (fun '(l, k) acc =>
      add_max l k acc) cl (add_max (levelexpr_level concl) 0 acc)) cls m.

Lemma MapsTo_add_max l l' k k' acc :
  LevelMap.MapsTo (elt:=nat) l k' (add_max l' k acc) <->
  if eqb l l' then is_max k' k l acc else LevelMap.MapsTo l k' acc.
Proof.
  unfold add_max.
  destruct LevelMap.find eqn:hl.
  { case: Nat.ltb_spec.
  - rewrite LevelMapFact.F.add_mapsto_iff /Level.eq.
    destruct (eqb_spec l l').
    { unfold is_max.
      firstorder eauto. subst k' l'. rewrite hl. f_equal. lia. congruence. subst l'.
      rewrite hl in H0. subst k'.
      left. split; auto. f_equal; lia. }
    intros. firstorder eauto. congruence.
  - intros. unfold is_max.
    destruct (eqb_spec l l'); subst. rewrite hl. firstorder eauto. apply LevelMap.find_1 in H. rewrite hl in H. noconf H.
    f_equal; lia. subst k'. apply LevelMap.find_2. rewrite hl. f_equal. f_equal. lia. reflexivity.
  }
  - rewrite LevelMapFact.F.add_mapsto_iff. intuition auto; subst.
    destruct (eqb_spec l l'); subst. unfold is_max. now rewrite hl. congruence.
    destruct (eqb_spec l l'); subst. unfold is_max. now rewrite hl. congruence.
    destruct (eqb_spec l l'); subst. unfold is_max in H; rewrite hl in H. subst k'. left; intuition eauto. reflexivity.
    right. intuition eauto.
Qed.

Lemma In_fold_add_max k n a :
  LevelMap.In (elt:=nat) k
  (LevelExprSet.fold
      (fun '(l, k0) acc => add_max l k0 acc) n a) <->
  (LevelSet.In k (levels n)) \/ LevelMap.In k a.
Proof.
  eapply LevelExprSetProp.fold_rec.
  - intros s' he.
    rewrite (LevelExprSetProp.empty_is_empty_1 he).
    cbn. unfold levels. rewrite LevelExprSetProp.fold_empty. rewrite LevelSetFact.empty_iff. intuition auto.
  - intros.
    destruct x as [l k'].
    rewrite In_add_max.
    rewrite H2 !levelexprset_levels_spec.
    split.
    * intros []; subst.
      left. exists k'. apply H1. now left.
      destruct H3 as [[k'' ?]|?]. left; exists k''. apply H1. now right.
      now right.
    * red in H1. setoid_rewrite H1.
      intros [[k'' []]|]. noconf H3. now left.
      right. now left; exists k''. right; right. apply H3.
Qed.

Lemma MapsTo_fold_add_max l n a :
  let map := LevelExprSet.fold (fun '(l, k0) acc => add_max l k0 acc) n a in
  (forall k, LevelMap.MapsTo (elt:=nat) l k map ->
  ((exists kl, LevelExprSet.In (l, kl) n /\ kl = k /\
    (forall kl', LevelExprSet.In (l, kl') n -> kl' <= kl) /\
    (forall kl', LevelMap.MapsTo l kl' a -> kl' <= kl)) \/
    (LevelMap.MapsTo l k a /\ (forall kl', LevelExprSet.In (l, kl') n -> kl' <= k))))
  /\ (forall l, ~ LevelMap.In l map -> ~ (exists k, LevelExprSet.In (l, k) n) /\ ~ (LevelMap.In l a)).
Proof.
  eapply LevelExprSetProp.fold_rec.
  - intros s' he. cbn.
    setoid_rewrite (LevelExprSetProp.empty_is_empty_1 he).
    intuition auto. right. split; eauto.
    intros kl. now move/LevelExprSet.empty_spec.
    destruct H0. now apply LevelExprSet.empty_spec in H0.
     (* destruct H0 as [? [he' _]]. now rewrite LevelExprSetFact.empty_iff in he'. *)
  - cbn; intros.
    destruct x as [xl k']. split.
    2:{ intros l0 hnin. destruct H2 as [_ H2]. specialize (H2 l0). split.
      { intros [k hex]. eapply H1 in hex as [hin|hin]. noconf hin. apply hnin.
        eapply In_add_max. now left.
         unshelve eapply (proj1 (H2 _)).
        intros hin'. apply hnin. rewrite In_add_max. now right. now exists k. }
      { apply H2 => hin. elim hnin. rewrite In_add_max. now right. } }
    intros.
    rewrite MapsTo_add_max in H3.
    destruct (eqb_spec l xl); subst.
    * unfold is_max in H3 at 1.
      destruct LevelMap.find eqn:hfind.
      { subst k. pose proof (LevelMap.find_2 hfind). destruct H2 as [H2 Hnotin]. destruct (H2 _ H3).
          left. destruct H4 as [kl [hkl hleq]]. destruct hleq as [hleq hmax]. subst n0.
          destruct (Nat.max_spec k' kl) as [[]|[]].
          { exists kl. split. apply H1. now right. split. f_equal. lia. split. intros.
            apply H1 in H6 as []. noconf H6. lia. now apply (proj1 hmax). destruct hmax as [_ hmax].
            intros. now apply hmax. }
          { exists k'. split. apply H1. now left. split. f_equal; lia. destruct hmax as [hmax hmax']; split.
            intros kl' hin. apply H1 in hin as []; subst. noconf H6. lia. specialize (hmax _ H6). lia.
            intros. transitivity kl. now apply hmax'. lia. }
          destruct (H2 _ H3) as [[kl [hkl hleq]]|]. noconf hleq.
          destruct hleq as [hleq hmax]. subst n0.
          destruct (Nat.max_spec k' kl) as [[]|[]].
          { left. exists kl. split. apply H1. now right. destruct hmax as [hmax hmax']. split. f_equal. lia. split.
            intros. apply H1 in H7 as []. noconf H7. lia. now apply hmax. apply hmax'. }
          { left. exists k'. split. apply H1. now left. destruct hmax as [hmax hmax']. split. f_equal. lia. split.
            intros kl' hin. apply H1 in hin as []. noconf H7. lia. specialize (hmax _ H7). lia.
            intros. transitivity kl => //. now eapply hmax'. }
          destruct H4. clear H5.
          destruct (Nat.max_spec k' n0) as [[]|[]].
          { right. split. now rewrite H7.
            intros kl' hin. apply H1 in hin as [hin|hin]; noconf hin. lia.
            specialize (H6 _ hin). depelim H6; lia. }
          { left. exists k'. split. apply H1. now left. split. f_equal. lia. split.
            intros kl' hin. apply H1 in hin as []. noconf H8. lia.
            specialize (H6 _ H8). lia.
            intros. transitivity n0. 2: lia. eapply (LevelMapFact.F.MapsTo_fun H4) in H8. subst kl'. reflexivity. }
      }
      subst k. left. exists k'. split; eauto. firstorder. split. reflexivity.
      destruct H2 as [hl hnotin]. eapply LevelMapFact.F.not_find_in_iff in hfind.
      apply hnotin in hfind as hfind'.
      split.
      { intros. eapply H1 in H2 as [hin|hin]; noconf hin. reflexivity.
        destruct hfind' as [hfind' _].
        elim hfind'. now exists kl'. }
      { intros kl' hin. destruct hfind' as []. now elim H3; exists kl'. }
    * destruct H2 as [H2 hfind]. destruct (H2 _ H3) as [[lk [hkl hleq]]|].
      + left. depelim hleq. destruct H6 as [hinl hinacc]. exists lk. split; [firstorder|]. split => //.
        split => //.
        { intros kl' hin. apply H1 in hin as [hin|hin]. noconf hin. congruence. subst k. now apply hinl. }
      + right. intuition auto.
        eapply H1 in H5 as [hin|hin]; noconf hin. congruence.
        now eapply H7.
Qed.


Lemma min_model_map_levels m cls k :
  LevelMap.In k (min_model_map m cls) <->
    LevelSet.In k (clauses_levels cls) \/ LevelMap.In k m.
Proof.
  rewrite /min_model_map.
  rewrite clauses_levels_spec.
  eapply ClausesProp.fold_rec.
  - intros s' he. intuition auto.
    destruct H0 as [cl []].
    clsets.
  - intros x a s' s'' inx ninx hadd ih.
    destruct x as [cl k'].
    rewrite In_fold_add_max In_add_max. rewrite ih.
    intuition auto. left. exists (cl, k'); intuition auto.
    apply hadd. now left.
    rewrite clause_levels_spec. now left.
    subst. left. exists (cl, k'). split. apply hadd; now left.
    rewrite clause_levels_spec. now right.
    destruct H as [cl'' []]. left. exists cl''.
    intuition auto. apply hadd. now right.
    destruct H3 as [cl'' []].
    apply hadd in H0 as []; subst.
    rewrite clause_levels_spec in H3. destruct H3; subst.
    cbn in H0. now left. right. now left.
    right. right. left; exists cl''. split => //.
Qed.

Lemma premises_model_map_levels m cls k :
  LevelMap.In k (premises_model_map m cls) <->
    LevelSet.In k (clauses_premises_levels cls) \/ LevelMap.In k m.
Proof.
  rewrite /premises_model_map.
  rewrite clauses_premises_levels_spec.
  eapply ClausesProp.fold_rec.
  - intros s' he. intuition auto.
    destruct H0 as [cl []].
    clsets.
  - intros x a s' s'' inx ninx hadd ih.
    destruct x as [cl k'].
    rewrite In_fold_add_max ih.
    intuition auto.
    * left. exists (cl, k'); intuition auto.
      apply hadd. now left.
    * destruct H as [cl'' []]. left. exists cl''.
      intuition auto. apply hadd. now right.
    * destruct H3 as [cl'' []].
      apply hadd in H0 as []; subst.
      now left. right. now left.
Qed.



Section Completeness.
  Reserved Notation "x ≡ y" (at level 90).
  Record semilattice :=
    { carrier :> Type;
      eq : carrier -> carrier -> Prop where "x ≡ y" := (eq x y);
      succ : carrier -> carrier;
      join : carrier -> carrier -> carrier;
      join_assoc x y z : join x (join y z) ≡ join (join x y) z;
      join_comm x y : join x y ≡ join y x;
      join_idem x : join x x ≡ x;
      join_sub x : join x (succ x) ≡ succ x;
      succ_join : forall x y, succ (join x y) ≡ join (succ x) (succ y);
    }.

  Notation "x ≡ y" := (eq _ x y).

  Section Derived.
    Context (s : semilattice).
    Definition le (x y : s) := join s x y ≡ y.

    Fixpoint add (x : s) n : s :=
      match n with
      | 0 => x
      | S n => succ _ (add x n)
      end.

  End Derived.

  Definition term (V : Type) : Type := list (V * nat).
  Definition relation (V : Type) := term V -> term V -> Prop.

  Record presented (V : Type) := {
    terms : term V -> Prop;
    relations : relation V }.

  Definition valid (V : Type) (C : presented V) (t u : term V) := relations _ C t u.

  Section Terms.
    Context (V : Type) (pres : presented V).
    Definition succV (t : term V) := map (fun '(x, n) => (x, S n)) t.
    Definition maxV (t u : term V) := t ++ u.

    Definition presents : semilattice.
    Proof.
      unshelve refine {| carrier := term V; eq := relations _ pres; succ := succV; join := maxV |}.
      all:apply (todo "laws").
    Defined.

    (* Definition interp_exp (vn : V * nat) : presents := let '(v, n) := vn in add presents v n. *)
    Definition interp_term (t : term V) :=
      let '(hd, tl) := t in
      List.fold_left (fun x n => join _ n (interp_exp x)) tl (interp_exp hd).

    Lemma all_terms (x : s) : exists t : term,





  Section Completeness.

    Definition add_presentation eq p :=
      {| V := p.(V); C := eq :: p.(C) |}.

    Definition relation_levels (r : rel) := (NES.levels r.1 ∪ NES.levels r.2)%levels.

    Definition wf_presentation p :=
      forall r, List.In r p.(C) -> relation_levels r ⊂_lset p.(V).

    Definition levels_position (l : Level.t) (ls : LevelSet.t) i :=
      List.nth_error (LevelSet.elements ls) i = Some l.

    Equations level_position (l : Level.t) (ls : list Level.t) : option nat :=
    level_position l [] := None ;
    level_position l (x :: xs) with Level.eqb l x :=
      { | true => Some 0
        | false with level_position l xs :=
          | None => None
          | Some n => Some (S n) }.

    Definition levelexpr_pos (l : LevelExpr.t) (ls : LevelSet.t) :=
      match level_position l.1 (LevelSet.elements ls) with
      | None => 0
      | Some pos =>  LevelSet.cardinal ls * Z.to_nat l.2 + pos
      end.

    Section Enum.

    Inductive enumeration : premises × premises -> Type :=
    | enum_single le le' : enumeration (singleton le, singleton le')
    | enum_add_left le (u v : premises) : ~ LevelExprSet.In le u -> enumeration (u, v) -> enumeration (NES.add le u, v)
    | enum_add_right le (u v : premises) : ~ LevelExprSet.In le v -> enumeration (u, v) -> enumeration (u, NES.add le v).

    Lemma acc_enum : forall r, enumeration r.
    Proof.
      intros [l r].
      move: l r. apply: NES.elim.
      - intros le.
        apply: NES.elim.
        * intros le'. constructor.
        * intros le' x. now constructor.
      - intros le x ihr nin r. now constructor.
    Qed.
    End Enum.
  Definition strict_subset (s s' : LevelExprSet.t) :=
    LevelExprSet.Subset s s' /\ ~ LevelExprSet.Equal s s'.

(* Lemma strict_subset_incl (x y z : LevelSet.t) : LevelSet.Subset x y -> strict_subset y z -> strict_subset x z.
Proof.
  intros hs []. split => //. lsets.
  intros heq. apply H0. lsets.
Qed. *)

    Definition premises_strict_subset (x y : premises) := strict_subset x y.

    Definition ord := lexprod premises_strict_subset premises_strict_subset.
    Derive Signature for lexprod.

    Lemma premises_incl_singleton (u : premises) le :
      u ⊂_leset (singleton le) -> LevelExprSet.Equal u (singleton le).
    Proof.
      intros incl; split => //.
      - apply incl.
      - intros hin. eapply LevelExprSet.singleton_spec in hin. subst.
        move: u incl. apply: NES.elim.
        * intros le' hs. specialize (hs le'). forward hs. apply LevelExprSet.singleton_spec. lesets.
          apply LevelExprSet.singleton_spec in hs. subst le'.
          now apply LevelExprSet.singleton_spec.
        * intros le' x ih hnin hadd.
          rewrite LevelExprSet.add_spec. right; apply ih.
          intros ? hin. apply hadd. now rewrite LevelExprSet.add_spec; right.
    Qed.

    Lemma subset_add {a l x} :
      ~ LevelExprSet.In l a -> a ⊂_leset NES.add l x -> a ⊂_leset x.
    Proof.
      intros hnin; rewrite -union_add_singleton.
      move=> hsub lk /[dup]/hsub. rewrite union_spec.
      intros [] => //. apply LevelExprSet.singleton_spec in H. subst. contradiction.
    Qed.

    (* Lemma subset_add_2 {a l x} :
      LevelExprSet.In l a -> a ⊂_leset NES.add l x -> a ⊂_leset x.
    Proof.
      intros hnin; rewrite -union_add_singleton.
      move=> hsub lk /[dup]/hsub. rewrite union_spec.
      intros [] => //. apply LevelExprSet.singleton_spec in H. subst. contradiction.
    Qed. *)

    Section LevelExprSetCardinal.

    Import LevelExprSet.
    Import LevelExprSetProp.

    Lemma cardinal_1_is_singleton a : cardinal a = 1 <-> exists x, Equal a (singleton x).
    Proof. Admitted.

    Lemma premises_cardinal (p : premises) : cardinal p > 0.
    Proof. Admitted.

    Lemma not_Equal_exists_diff (p p' : premises) :
      p ⊂_leset p' -> ~ Equal p p' ->
      exists le, (In le p' /\ ~ In le p).
    Proof.
      intros hsub neq.
      pose c := choose (diff p' p).
      case hc : c => [elt|]. move/choose_spec1: hc.
      rewrite diff_spec => -[hin nin]. now exists elt.
      move/choose_spec2: hc => hc.
      have hsub' : p' ⊂_leset p. lesets. elim neq.
      lesets.
    Qed.

    Lemma premises_strict_subset_spec p p' : premises_strict_subset p p' <->
      (p ⊂_leset p') /\ exists le, In le p' /\ ~ In le p.
    Proof.
      split.
      - intros [hincl hneq]. split => //.
        now apply not_Equal_exists_diff.
      - intros [hincl [le [inp' ninp]]].
        split => // => he. rewrite -he in inp'. contradiction.
    Qed.

    Lemma premises_strict_subset_cardinal (p p' : premises) :
      premises_strict_subset p p' -> (cardinal p < cardinal p')%nat.
    Proof.
      rewrite premises_strict_subset_spec => -[incl [le [inp' ninp]]].
      eapply subset_cardinal_lt; tea.
    Qed.

    Lemma cardinal_add {le x} : ~ In le x -> cardinal (add le x) = 1 + cardinal x.
    Proof. lesets. Qed.

    Lemma premises_eq_singleton {a : premises} {x} : a = singleton x :> LevelExprSet.t -> a = NES.singleton x.
    Proof.
      intros he. rewrite -equal_exprsets. cbn. now rewrite he.
    Qed.

    Lemma premises_strict_subset_wf : well_founded premises_strict_subset.
    Proof.
      red. intros a.
      have hr : LevelExprSet.cardinal a <= LevelExprSet.cardinal a by lesets.
      revert hr. generalize a at 2 => a'. move: a' a.
      apply: NES.elim.
      - intros le a. rewrite NES.LevelExprSetProp.singleton_cardinal.
        have carda := premises_cardinal a => cardle.
        have : cardinal a = 1 by lia.
        rewrite cardinal_1_is_singleton => -[x heq].
        move/eq_leibniz/premises_eq_singleton: heq. intros ->.
        constructor. intros y hp.
        destruct hp. eapply premises_incl_singleton in H. contradiction.
      - intros le x accx hnin.
        intros a asub.
        constructor => y.
        move/premises_strict_subset_cardinal => hc.
        apply accx. rewrite cardinal_add // in asub. lia.
    Qed.
    End LevelExprSetCardinal.

    Lemma acc_ord r : Acc ord r.
    Proof.
      apply wf_lexprod; apply premises_strict_subset_wf.
    Qed.
    Instance ord_wf : WellFounded ord.
    Proof. red. exact acc_ord. Qed.

    Lemma premises_strict_subset_add {l} {u : premises} :
      ~ LevelExprSet.In l u -> premises_strict_subset u (NES.add l u).
    Proof.
      intros hnin; rewrite premises_strict_subset_spec.
      rewrite -union_add_singleton. setoid_rewrite union_spec. split.
      - intros l'. rewrite union_spec; lesets.
      - exists l; split => //. right; now apply LevelExprSet.singleton_spec.
    Qed.




(* Completeness try *)
(*


  Parameter ϕ : nat -> rel.
    Parameter ϕ_exists : forall r, exists n, ϕ n = r.
    Parameter ϕ_inj : forall n n', ϕ n = ϕ n' -> n = n'.

    Definition neg_r p e :=
      p ⊢ℒ add_prems 1 e.1 ≤ e.2 \/ p ⊢ℒ add_prems 1 e.2 ≤ e.1.

    (* Definition consistent (r : rels) :=
      ~ (exists e, r ⊢ℒ e /\ neg_r r e).

    Definition satisfiable (r : rels) :=
      exists v, interp_rels v r.

    Definition satisfiable_consistent {p} :
      satisfiable p -> consistent p.
    Proof.
      move=> [v it] [[l r] [hx [hnl|hnl]]];
      eapply presentation_entails_valid_eq in hx;
      eapply presentation_entails_valid_le in hnl;
      move: (hx _ it); move: (hnl _ it); cbn;
      rewrite !interp_add_prems; lia.
    Qed. *)

    (* Definition consistent' (Γ : rels) :=
      exists r, ~ (Γ ⊢ℒ r). *)

    Definition bottom (s : semilattice) :=
      exists x : s, add 1%Z x ≤ x.

    Notation "⟘" := (bottom _) : sl_scope.

    Definition consistent Γ :=
      ~ exists e, Γ ⊢ℒ e ≡ add_prems 1 e.

    Inductive 𝒮 (r : rels) : rels -> nat -> Prop :=
    | S_0 Γ : List.incl Γ r -> 𝒮 r Γ 0
    | S_incl Γ n : 𝒮 r Γ n ->
      (* ~ consistent (ϕ n :: Γ) ->  *)
      𝒮 r Γ (S n)
    | S_phi Γ n : 𝒮 r Γ n -> consistent (ϕ n :: Γ) -> 𝒮 r (ϕ n :: Γ) (S n).

    Definition 𝒮ω rs (Γ : rels) := exists (n: nat), 𝒮 rs Γ n.

    Definition in𝒮ω rs r := exists (n: nat) Γ, 𝒮 rs Γ n /\ Γ ⊢ℒ r.

    (* /\ Γ ⊢ℒ r *)

    Definition maximally_consistent (Γ : rels) :=
       consistent Γ /\ forall r, (~ consistent (r :: Γ) \/ Γ ⊢ℒ r).

    Definition satisfiable (s : semilattice) (r : rels) :=
      exists v, interp_rels (SL := sl s) v r.

    Lemma consistent_satisfiable Γ :
      satisfiable Z_semilattice Γ -> consistent Γ.
    Proof.
      move=> [v sat] [e].
      move/presentation_entails_valid_rel/(_ Z_semilattice v sat). cbn.
      rewrite interp_add_prems. change (add 1%Z (interp_prems v e)) with (Z.add 1 (interp_prems v e)).
      cbn -[Z.add]. lia.
    Qed.

    Section MaximallyConsistent.

      Lemma 𝒮ω_consistent_maximal Γ Γ' n : consistent Γ -> 𝒮 Γ Γ' n -> consistent Γ'.
       (* /\ (consistent' (ϕ n :: Γ') \/ Γ' ⊢ℒ ϕ n). *)
      Proof.
        move=> con sprf. induction sprf.
        - intros [e pe]. apply con. exists e.
          eapply entails_L_rels_subset; tea.
        - exact IHsprf.
        - intros [e neq].
          destruct H. now exists e.
      Qed.

      Definition 𝒮ω_exists rs (crs : consistent rs) n : exists Γ, 𝒮 rs Γ n.
      Proof.
        induction n.
        - exists rs. by constructor.
        - destruct IHn as [Γ' sn].
          destruct (check_pres_clause_spec Γ' (ϕ n)).
          * exists (ϕ n :: Γ'). apply S_phi => //.
            intros [e he]. apply 𝒮ω_consistent_maximal in sn => //.
            eapply entails_L_cut in H; tea.
            apply sn. now exists e.
          * exists Γ'. apply S_incl => //.
      Qed.

    Definition inSw rs r := exists n Γ, 𝒮 rs Γ n /\ Γ ⊢ℒ r.

    Import Semilattice.

    Lemma axiom_inSw {rs r} : rs ⊢ℒ r -> inSw rs r.
    Proof.
      intros hs. exists 0, rs; split. constructor. red; auto.
      exact: hs.
    Qed.

*)


  Class Decidable (A : Prop) := dec : A \/ ~ A.
  Arguments dec A {Decidable}.

  (* Definition check_pres_clause p r :=
    LoopCheck.Impl.check_clauses (clauses_of_relations p) (clauses_of_eq r.1 r.2).

  Lemma check_pres_clause_spec p r : p ⊢ℒ r \/ ~ (p ⊢ℒ r).
  Proof.
    destruct (check_pres_clause p r) eqn:eq.
    - move: eq.
      rewrite /check_pres_clause.
   Admitted.

  Instance dec_entails_L {p s t} : Decidable (p ⊢ℒ s ≡ t).
  Proof.
    red. eapply check_pres_clause_spec.
  Qed.

  Lemma contra_prop A B (decB : Decidable B) : (~ B -> ~ A) -> (A -> B).
  Proof. intros he a. destruct (dec B). exact H. specialize (he H). contradiction. Qed.

  Definition satisfiable (s : semilattice) (r : rels) :=
    exists v, interp_rels (SL := sl s) v r.
 *)
