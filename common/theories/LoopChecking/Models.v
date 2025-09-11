(* Distributed under the terms of the MIT license. *)
(* This module defines a handful of initial models that are used
  for defining satisfiability and validity checking.
*)

From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From MetaRocq.Common Require Import Common Interfaces HornClauses Model.
From Equations Require Import Equations.
Set Equations Transparent.

Module Models (LS : LevelSets).
  Module Export Model := Model(LS).
  Local Open Scope Z_scope.

  Definition premises_model_map (m : model) cls : model :=
    let levels := clauses_premises_levels cls in
    LevelSet.fold (fun l acc =>
      LevelMap.add l (max_clause_premise_of l cls) acc) levels m.

  Definition zero_model levels : model :=
    LevelSet.fold (fun l acc => LevelMap.add l None acc) levels (LevelMap.empty _).

  Definition premises_model V cl : LevelSet.t * model :=
    let levels := LevelSet.union (clause_levels cl) V in
    (levels, premises_model_map (zero_model levels) (Clauses.singleton cl)).

  Lemma premises_model_map_spec m cls :
    forall l k,
    LevelMap.MapsTo l k (premises_model_map m cls) <->
    ((LevelSet.In l (clauses_premises_levels cls) /\ k = max_clause_premise_of l cls /\ isSome k) \/
    (~ LevelSet.In l (clauses_premises_levels cls) /\ LevelMap.MapsTo l k m)).
  Proof.
    intros l k; rewrite /premises_model_map.
    eapply LevelSetProp.fold_rec.
    - intros s' he. split. intros hm. right. split => //.
      firstorder.
    - intros x a s' s'' hin hnin hadd ih.
      split.
      * rewrite LevelMapFact.F.add_mapsto_iff.
        firstorder. subst k. red in H; subst. firstorder.
        left; firstorder.
        apply clauses_premises_levels_spec in hin as [cl [incl inlev]].
        apply levelexprset_levels_spec in inlev as [k inprem].
        have hs := max_clause_premise_of_spec l k cls cl incl inprem.
        depelim hs. now rewrite H3.
      * intros [[hin' [-> iss]]|].
        rewrite LevelMapFact.F.add_mapsto_iff.
        destruct (Level.eq_dec x l); subst; firstorder.
        destruct (Level.eq_dec x l); subst; firstorder.
        rewrite LevelMapFact.F.add_mapsto_iff. right; split => //.
  Qed.

  Lemma zero_model_spec {l ls n} : LevelMap.MapsTo l n (zero_model ls) <-> LevelSet.In l ls /\ n = None.
  Proof.
    unfold zero_model.
    eapply LevelSetProp.fold_rec.
    - intros s' he. rewrite LevelMapFact.F.empty_mapsto_iff. firstorder.
    - intros x a s s' hin hnin hadd eq.
      rewrite LevelMapFact.F.add_mapsto_iff. firstorder.
      destruct (Level.eq_dec x l).
      * subst. now left.
      * right. split => //. apply hadd in H1. destruct H1; try congruence. now apply H0.
  Qed.


  Lemma premises_model_map_min_premise {levels cls prems z} :
    min_premise (premises_model_map (zero_model levels) cls) prems = Some z ->
    (exists minp mink, LevelExprSet.In (minp, mink) prems /\
      exists maxp, max_clause_premise_of minp cls = Some maxp /\
      z = maxp - mink) \/
    (exists minp mink, LevelExprSet.In (minp, mink) prems /\ z + mink <= 0)%Z.
  Proof.
    set (m := premises_model_map _ _).
    have [minple [[minp mink] [inminp mineq]]] := min_premise_spec m prems.
    rewrite mineq. rewrite /min_atom_value.
    destruct level_value eqn:hl => //. intros [= <-].
    eapply level_value_MapsTo' in hl.
    eapply premises_model_map_spec in hl as [[inpcls [hm _]]|[ninpcls h']]. left.
    2:{ apply zero_model_spec in h' as [h' [= ->]]. }
    exists minp, mink. split => //. noconf hm. rewrite -hm.
    eexists; split => //.
  Qed.

  Lemma premises_model_map_in m cls l :
    LevelMap.In l (premises_model_map m cls) <-> (LevelSet.In l (clauses_premises_levels cls) \/ LevelMap.In l m).
  Proof.
    rewrite /premises_model_map.
    eapply LevelSetProp.fold_rec.
    - intros s' he. firstorder.
    - intros x a s' s'' hin hnin hadd ih.
      rewrite LevelMapFact.F.add_in_iff.
      firstorder.
  Qed.

  Lemma premises_model_map_min_premise_inv {levels cls} :
    forall cl, Clauses.In cl cls ->
    exists z, min_premise (premises_model_map (zero_model levels) cls) (premise cl) = Some z /\ (0 <= z)%Z.
  Proof.
    set (m := premises_model_map _ _).
    move=> cl hin.
    have [minple [[minp mink] [inminp mineq]]] := min_premise_spec m (premise cl).
    rewrite mineq. rewrite /min_atom_value.
    destruct level_value eqn:hl => //.
    - eexists. split; trea.
      have ps := proj1 (premises_model_map_spec _ cls minp (Some z)) (level_value_MapsTo' hl).
      destruct ps as [[minpsl [eq _]]|].
      * symmetry in eq.
        have sp := (max_clause_premise_of_spec _ _ _ _ hin inminp).
        depelim sp. rewrite eq in H0. noconf H0. lia.
      * destruct H. elim H.
        eapply clauses_premises_levels_spec. exists cl. split => //.
        eapply levelexprset_levels_spec. now exists mink.
    - unfold level_value in hl.
      destruct LevelMap.find eqn:hl'. subst o.
      2:{ move/LevelMapFact.F.not_find_in_iff: hl'. elim.
        rewrite premises_model_map_in. left.
        eapply clauses_premises_levels_spec. exists cl. split => //.
        eapply levelexprset_levels_spec. now exists mink. }
      eapply LevelMap.find_2 in hl'.
      move/premises_model_map_spec: hl' => [[]|[nin hm]] => //.
      * now intros hnminp [_ hn].
      * move: nin; elim.
        eapply clauses_premises_levels_spec. exists cl. split => //.
        eapply levelexprset_levels_spec. now exists mink.
  Qed.

  Lemma in_premises_model V cl :
    forall l,
    LevelMap.In l (premises_model V cl).2 <->
    LevelSet.In l V \/ LevelSet.In l (clause_levels cl).
  Proof.
    intros l. rewrite premises_model_map_in.
    rewrite clauses_premises_levels_spec.
    firstorder.
    - right. apply Clauses.singleton_spec in H.
      apply clause_levels_spec. left. now subst.
    - apply zero_model_spec in H as [hin ->].
      apply LevelSet.union_spec in hin. firstorder.
    - right. exists None. apply zero_model_spec. split => //; lsets.
    - eapply clause_levels_spec in H as [H|H].
      * left. exists cl. split => //. now apply Clauses.singleton_spec.
      * subst. right. exists None. apply zero_model_spec. split => //.
        apply LevelSet.union_spec. left. apply clause_levels_spec. now right.
  Qed.

  Lemma of_level_map_premises_model_map cls cl V ne :
    cls ⊢a premise cl → of_level_map (premises_model_map (zero_model V) (Clauses.singleton cl)) ne.
  Proof.
    intros [l k].
    rewrite of_level_map_spec. move/premises_model_map_spec; cbn.
    intros [[hin' [[= heq] _]]|[hnin hm]].
    2:{ now apply zero_model_spec in hm as []. }
    move: hin'; cbn; rewrite LevelSet.union_spec. intros []; [|lsets].
    eapply max_premise_of_spec_in in H as [maxp' [eq hin']].
    rewrite eq in heq; noconf heq.
    now constructor.
  Qed.

  Lemma entails_all_satisfies {cls prems m hne l k} :
    cls ⊢a prems → of_level_map m hne ->
    infers_atom m l k ->
    cls ⊢ prems → (l, k).
  Proof.
    intros hl hi.
    eapply entails_all_one; tea. now apply infers_atom_of_level_map.
  Qed.

  Lemma premises_model_map_ne V cls :
    ~ LevelMap.Empty V ->
    ~ LevelMap.Empty (premises_model_map V cls).
  Proof.
    intros ne he. apply ne.
    have ne' := premises_model_map_in V cls.
    intros l k hin.
    specialize (ne' l). destruct ne'. forward H0. right. now exists k.
    destruct H0 as [k' hin'].
    now move/he: hin'.
  Qed.

  Lemma premises_model_map_defined V cls :
    ~ Clauses.Empty cls ->
    defined_map (premises_model_map V cls).
  Proof.
    move/clauses_ne_exist => [cl hin].
    destruct cl as [prems concl].
    pose proof (to_nonempty_list_spec' prems).
    set (l := (to_nonempty_list prems).1) in *.
    have hs := max_clause_premise_of_spec l l.2 cls (prems, concl) hin.
    forward hs. cbn. eapply LevelExprSet.elements_spec1; rewrite -H.
    constructor. destruct l; reflexivity. depelim hs.
    exists l, y. apply premises_model_map_spec. left.
    split => //.
    eapply clauses_premises_levels_spec. eexists; split; tea => //.
    rewrite //= levelexprset_levels_spec. exists l.2.
    setoid_rewrite <- LevelExprSet.elements_spec1. rewrite -H //=.
    constructor. destruct l; reflexivity.
  Qed.

  (* To infer an extension, we weaken a valid model for V to a model for [V ∪ clauses_levels cls] by
    setting a minimal value for the new atoms in [clauses_levels cls \ V]
    such that the new clauses [cls] do not hold vacuously.
  *)

  Equations add_max (l : Level.t) (k : option Z) (m : model) : model :=
  add_max l k m with level_value m l :=
    { | Some k' with check_atom_value k (Some k') :=
      { | true => m
        | false => LevelMap.add l k m }
    | None => LevelMap.add l k m }.

  Lemma add_max_spec l l' k k' (m : model) :
    LevelMap.MapsTo l k (add_max l' k' m) <->
    (l = l' /\ k = max_opt_of Z.max k' (level_value m l)) \/
    (l <> l' /\ LevelMap.MapsTo l k m).
  Proof.
    funelim (add_max l' k' m).
    - rewrite LevelMapFact.F.add_mapsto_iff /Level.eq. firstorder; subst.
      left. split => //. rewrite Heq. now rewrite max_opt_of_l.
      left. firstorder. now rewrite Heq max_opt_of_l.
    - clear Heqcall.
      destruct (Level.eq_dec l0 l).
      * subst l0. rewrite Heq0.
        move/check_atom_value_spec: Heq.
        rewrite (maps_to_update (level_value_MapsTo' Heq0)).
        firstorder; subst; try left; try split; auto; depelim Heq; cbn; lia_f_equal.
      * firstorder.
    - rewrite LevelMapFact.F.add_mapsto_iff /Level.eq.
      have := check_atom_value_spec k (Some k'). rewrite {}Heq.
      intros h; depelim h. apply nleq_optZ in H as [z [-> hlt]].
      firstorder; subst.
      * left; split => //. rewrite Heq0 //=. lia_f_equal.
      * left; split => //. rewrite Heq0 //=. lia_f_equal.
  Qed.

  Definition min_model_clause cl m :=
    LevelExprSet.fold (fun '(l, k) acc => add_max l (Some k) acc) (premise cl)
      (add_max (concl cl) None m).

  Definition min_model_map (m : model) cls : model :=
    Clauses.fold min_model_clause cls m.

  Lemma In_add_max l l' k acc :
    LevelMap.In l (add_max l' k acc) <-> (l = l' \/ LevelMap.In l acc).
  Proof.
    rewrite /LevelMap.In.
    rw add_max_spec. firstorder subst.
    eexists; left; eauto.
    destruct (Level.eq_dec l l'); subst; eexists; eauto.
  Qed.

  Definition max_of_premises l kl n :=
    (forall kl', LevelExprSet.In (l, kl') n -> Some kl' ≤ kl).

  Definition is_expr l (e : LevelExpr.t) :=
    let '(concl, k) := e in concl = l.

  Definition max_of_clause l kl cl :=
    max_of_premises l kl (premise cl).

  Definition max_of_map l kl m :=
    (forall kl', LevelMap.MapsTo l kl' m -> kl' ≤ kl).

  Definition is_max_of_clause_and_map l cl m k :=
    max_of_premises l k (premise cl) /\ max_of_map l k m.

  Definition is_in_premise l k (u : LevelExprSet.t) :=
    (exists kl, LevelExprSet.In (l, kl) u /\ k = Some kl).

  Definition is_in_clause l k (cl : clause) :=
    is_in_premise l k (premise cl) \/ (l = (clause_conclusion cl) /\ k = None).

  Definition is_max_of_clause_model l cl m k :=
    is_max_of_clause_and_map l cl m k /\
    (is_in_clause l k cl \/ LevelMap.MapsTo l k m).

  Definition is_higher l k m := exists k', LevelMap.MapsTo l k' m /\ k ≤ k'.

  Definition is_max_of_clause_map (map : model) l cl (m : model) : Prop :=
    (forall k, LevelMap.MapsTo l k map -> is_max_of_clause_model l cl m k)
    /\ (forall l k, LevelMap.MapsTo l k m \/ is_in_clause l k cl -> is_higher l k map).

  Lemma is_higher_le l k l' k' m : is_higher l k m -> is_higher l k (add_max l' k' m).
  Proof.
    rewrite /is_higher.
    rw add_max_spec.
    intros [k'0 [hm hle]].
    destruct (Level.eq_dec l l').
    - subst. eexists. split; eauto. rewrite (level_value_MapsTo hm).
      transitivity k'0 => //. apply max_opt_of_le_r.
    - exists k'0. split; eauto.
  Qed.

  Lemma is_higher_add l k m : is_higher l k (add_max l k m).
  Proof.
    rewrite /is_higher.
    rw add_max_spec. eexists. split; eauto.
    apply max_opt_of_le_l.
  Qed.

  Lemma is_higher_mon l k k' m : is_higher l k' m -> k ≤ k' -> is_higher l k m.
  Proof.
    intros [? []] le. exists x. split => //. now transitivity k'.
  Qed.

  Lemma MapsTo_fold_add_max l n a :
    let map := LevelExprSet.fold (fun '(l, k0) acc => add_max l (Some k0) acc) n a in
    (forall k, LevelMap.MapsTo l k map ->
    ((exists kl,
      [/\ LevelExprSet.In (l, kl) n, k = Some kl,
      (forall kl', LevelExprSet.In (l, kl') n -> kl' <= kl) &
      (forall kl', LevelMap.MapsTo l kl' a -> kl' ≤ Some kl)]) \/
      (LevelMap.MapsTo l k a /\ (forall kl', LevelExprSet.In (l, kl') n -> Some kl' ≤ k))))
    /\ (forall l k, LevelMap.MapsTo l k a \/ is_in_premise l k n -> is_higher l k map) /\
    a ⩽ map.
    (* ~ LevelMap.In l map -> ~ (exists k, LevelExprSet.In (l, k) n) /\ ~ (LevelMap.In l a)). *)
  Proof.
    eapply LevelExprSetProp.fold_rec.
    - intros s' he. cbn.
      rewrite /is_in_premise /is_higher.
      setoid_rewrite (LevelExprSetProp.empty_is_empty_1 he).
      intuition auto. right. split; eauto.
      intros kl. now move/LevelExprSet.empty_spec.
      exists k; split => //. reflexivity.
      destruct H0 as [x [hin ->]]. now apply LevelExprSet.empty_spec in hin.
      reflexivity.
    - cbn; intros.
      destruct x as [xl k']. split.
      2:{ split.
        { intros l0 hnin. destruct H2 as [hm [H2 _]]. specialize (H2 l0).
        intros [ina|ins''].
        { specialize (H2 hnin (or_introl ina)). eapply is_higher_le; tea. }
        { destruct ins'' as [x [ins'' ->]].
          apply H1 in ins'' as [[=]|ins'].
          * subst. apply is_higher_add.
          * apply is_higher_le, H2. right. eexists; eauto. } }
        { destruct H2 as [_ [_ H2]].
          intros l' hin. move/H2 => [k'0 [hm hle]].
          rw add_max_spec. destruct (Level.eq_dec l' xl).
          - eexists; split. left; eauto. subst l'.
            rewrite (level_value_MapsTo hm). transitivity (k'0) => //.
            apply max_opt_of_le_r.
          - eexists; split; eauto. } }
      intros.
      rewrite add_max_spec in H3; destruct H3 as [[<- hk]|[hdiff hm]].
      * destruct H2 as [hin hnin]. symmetry in hk.
        have [[leacc eqms]|[len eqms]] := max_opt_of_spec hk.
        { depelim leacc. specialize (hin _ (level_value_MapsTo' H3)) as [[kl [inkl [= <-] les' lea]]|].
          { left. exists y. split => //. apply H1; now right. congruence. intros.
            apply H1 in H4 as [[=]|ins']. 2:now apply les'. subst kl'. lia. }
          { destruct H4. right. split. now rewrite -H3 -eqms in H4. intros.
            apply H1 in H6 as [[=]|ins']; subst; trea. rewrite H3; cbn; constructor; lia_f_equal.
            rewrite H3; cbn; constructor. apply H5 in ins'. depelim ins'. lia. } }
        { left. exists k'. split => //.
          * apply H1. now left.
          * move=> kl' /H1 [[=]|ins']. lia. depelim len. transitivity x; tea. specialize (hin _ (level_value_MapsTo' H3)) as
          [[kl [inkl [= <-] les' lea]]|[]].
            { now eapply les'. }
            { specialize (H5 _ ins'). depelim H5. lia. }
            { move: H2 hk. rewrite /level_value. destruct (find_spec l a0).
              * intros ->. apply hin in H2 as [[kl []]|[hm hkl']] => //. apply hkl' in ins'. depelim ins'.
              * intros _; cbn; intros <-.
                destruct hnin as [hnin _].
                specialize (hnin l (Some kl')); forward hnin. right.
                red. exists kl'. split => //.
                destruct hnin as [ka [hma hge]]. elim H2. now exists ka. }
          * subst k. intros kl' mt. move: len. case: level_valueP => [k ma0 le|].
            specialize (hin _ ma0) as [[kl []]|[hm hkl']] => //.
            + subst k. eapply H5 in mt. now depelim le; depelim mt; constructor; lia.
            + transitivity k => //. eapply LevelMapFact.F.MapsTo_fun in mt; tea. subst. reflexivity.
            + intros hnin' _. destruct hnin as [hnin _]. specialize (hnin l kl').
              forward hnin. now left. destruct hnin as [? [hm ?]]. elim hnin'. now exists x. }
      * destruct H2. eapply H2 in hm as [[kl []]|[hm hkl']] => //.
        { left. exists kl. split => //. apply H1. now right. intros kl' h. subst k.
          apply H6. apply H1 in h. destruct h as [[=]|?] => //. subst. congruence. }
        { right. split => //. intros kl' hin. apply H1 in hin as [[=]|?] => //; subst; try congruence. eauto. }
  Qed.

  Lemma min_model_clause_spec l cl a :
    let map := min_model_clause cl a in
    is_max_of_clause_map map l cl a.
  Proof.
    intros m. rewrite /is_max_of_clause_map /is_max_of_clause_model.
    have h := MapsTo_fold_add_max l (premise cl) (add_max (concl cl) None a).
    change (LevelExprSet.fold (fun '(l, k0) (acc : model) => add_max l (Some k0) acc) (premise cl)
        (add_max (concl cl) None a)) with (min_model_clause cl a) in h.
    cbn in h. destruct h. split.
    - intros k hm. specialize (H k hm) as [[kl []]|[hm' hle]].
      * split => //. subst k. red. split. intros kl' hin. constructor. now apply H2.
        move=> kl' hm''. specialize (H3 kl').
        rewrite add_max_spec in H3. forward H3.
        destruct (Level.eq_dec l (concl cl)).
        { subst l. left. split => //. rewrite max_opt_of_r. apply level_value_MapsTo in hm''. now rewrite hm''. }
        { right. split => //. }
        exact H3. left.
        red. left. red. subst k. eauto.
      * rewrite add_max_spec in hm'.
        rewrite max_opt_of_r in hm'. destruct hm' as [[]|[]]; try subst l.
        { repeat split => //.
          { intros l hin'. subst k. rewrite (level_value_MapsTo hin'). reflexivity. }
          { destruct k. right. symmetry in H1. now apply level_value_MapsTo' in H1.
            left. red. right. split => //. } }
        { split => //. split => //.
          { intros l' hin'. eapply LevelMapFact.F.MapsTo_fun in H1; tea. subst. reflexivity. }
          firstorder. }
    - intros l' k. destruct H0 as [H0 hext]. specialize (H0 l' k).
      intros [hm|hinc].
      { forward H0. left. rewrite add_max_spec.
        destruct (Level.eq_dec l' (concl cl)); eauto.
        { left. split => //. rewrite max_opt_of_r.
          now rewrite (level_value_MapsTo hm). }
        destruct H0 as [? [hinm hle]].
        eapply is_higher_mon; tea. exists x. split; eauto. reflexivity. }
      { red in hinc. destruct hinc. apply H0. now right.
        destruct H1 as [-> ->].
        destruct (Level.eq_dec l (concl cl)).
        red.
        destruct (LevelMap.find (concl cl) a) eqn:hl.
        * apply LevelMap.find_2 in hl.
          specialize (hext (concl cl) o).
          forward hext. rewrite add_max_spec. left. split => //.
          rewrite max_opt_of_r. now rewrite (level_value_MapsTo hl).
          destruct hext as [k' []]. exists k'. split => //. constructor.
        * specialize (hext (concl cl) None).
          forward hext. rewrite add_max_spec. left. split => //.
          now rewrite /level_value hl.
          destruct cl; unfold clause_conclusion in *. exact hext.
        * specialize (hext (concl cl) (level_value a (concl cl))).
          forward hext. rewrite add_max_spec. left. split => //.
          destruct hext as [l' []]; exists l'; split => //. constructor. }
  Qed.

  Lemma min_model_map_acc l cls m :
    let map := min_model_map m cls in
    (forall k, LevelMap.MapsTo l k map -> max_of_map l k m) /\
    m ⩽ map.
  Proof.
    cbn. rewrite /min_model_map.
    eapply ClausesProp.fold_rec.
    2:{ intros. destruct H2 as [hf hin].
      have [hm hnin] := min_model_clause_spec l x a.
      split.
      intros k.
      move/hm. rewrite /is_max_of_clause_model. intros [[ism' ism] hasm].
      destruct hasm; eauto. intros kl'. move/hin => [k' [hmk' lek']].
      red in ism. specialize (ism _ hmk'). now transitivity k'.
      transitivity a => //.
      intros l' k ha. specialize (hnin l' k (or_introl ha)).
      exact hnin. }
    split; [|reflexivity].
    intros k hin k' hin'.
    eapply LevelMapFact.F.MapsTo_fun in hin; tea. subst; reflexivity.
  Qed.

  Lemma max_of_map_ext l k m m' : m ⩽ m' -> max_of_map l k m' -> max_of_map l k m.
  Proof.
    intros hext hm l'; move/hext => [k' [hm' le]].
    apply hm in hm'. now transitivity k'.
  Qed.

  Lemma mapsto_max_of_map l k m : LevelMap.MapsTo l k m -> max_of_map l k m.
  Proof.
    intros hm l' k'. eapply LevelMapFact.F.MapsTo_fun in hm; tea.
    subst; reflexivity.
  Qed.

  Lemma min_model_map_spec l cls m :
    let map := min_model_map m cls in
    (forall k, LevelMap.MapsTo l k map ->
    [/\ (exists cl, Clauses.In cl cls /\ is_in_clause l k cl) \/ LevelMap.MapsTo l k m,
      (forall cl, Clauses.In cl cls -> max_of_premises l k (premise cl)) & max_of_map l k m]) /\
      (forall cl, Clauses.In cl cls -> forall l, LevelSet.In l (clause_levels cl) -> LevelMap.In l map) /\
      m ⩽ map.
  Proof.
    cbn.
    rewrite /min_model_map.
    have hgen : forall cls m, (forall k, LevelMap.MapsTo l k (Clauses.fold min_model_clause cls m) ->
      [/\ (exists cl : Clauses.elt, Clauses.In cl cls /\ is_in_clause l k cl) \/
      LevelMap.MapsTo l k m,
        forall cl : Clauses.elt, Clauses.In cl cls -> max_of_premises l k (premise cl)
      & max_of_map l k (Clauses.fold min_model_clause cls m)]) /\
      (forall cl, Clauses.In cl cls -> forall l, LevelSet.In l (clause_levels cl) -> LevelMap.In l (Clauses.fold min_model_clause cls m)) /\
      m ⩽ Clauses.fold min_model_clause cls m.
    2:{ specialize (hgen cls m). destruct hgen as [hgen [hcls H]]; split; eauto.
        intros k hm. specialize (hgen k hm) as [] => //.
        split => //. eapply max_of_map_ext; tea. }
    clear.
    intros cls m.
    eapply ClausesProp.fold_rec.
    - intros s' he. split; [ | split; [|reflexivity]].
      * intros k hin. split => //. now right.
        intros cl hin'. clsets. now apply mapsto_max_of_map.
      * intros cl ins'; clsets.
    - intros x a s' s'' hin hnin hadd [ih [ihcls hext]]. split; [|split]; revgoals.
      { transitivity a => //. intros l' hin' hm.
        have := min_model_clause_spec l' x a. cbn.
        intros [_ hm']. specialize (hm' l' hin').
        now forward hm' by eauto. }
      { intros cl ins'' l' inlev.
        apply hadd in ins'' as [<-|].
        * have := min_model_clause_spec l' x a. cbn.
          intros [_ hm']. eapply clause_levels_spec in inlev as [].
          + eapply levelexprset_levels_spec in H as [k' incl].
            specialize (hm' l' (Some k')). forward hm'. right. left. rewrite /is_in_premise. exists k'; eauto.
            destruct hm' as [? []]; now eexists.
          + subst l'. specialize (hm' (concl x) None). forward hm'.
            right. right. split => //.
            destruct hm' as [? []]; now eexists.
        * specialize (ihcls _ H _ inlev) as [k' ina].
          have := min_model_clause_spec l' x a. cbn.
          move=> [] _ /(_ l' k' (or_introl ina)).
          clear. firstorder. }
      intros k.
      have := min_model_clause_spec l x a. cbn.
      intros [hm hm'] hmk. destruct (hm _ hmk).
      split => //.
      { destruct H0; eauto.
      { left; exists x. split => //. apply hadd. now left. }
      { specialize (ih _ H0) as []. destruct H1; eauto. left.
        move: H1 => [] w []; exists w; split; eauto. apply hadd. now right. } }
      { move=> cl /hadd => [] [<-|hin'].
        { now move: H => []. }
        { specialize (hm' l k). forward hm' by (destruct H0; eauto).
          intros k' h.
          specialize (ihcls _ hin' l).
          forward ihcls.
          { eapply clause_levels_spec. left. eapply levelexprset_levels_spec. now exists k'. }
          destruct ihcls as [ka ihcls].
          specialize (ih _ ihcls) as [ihm ihcls' maxm].
          specialize (ihcls' _ hin' _ h).
          transitivity ka => //.
          destruct H as [mp mmap].
          now apply mmap. } }
      { intros kl inma. eapply LevelMapFact.F.MapsTo_fun in hmk; tea. subst. reflexivity. }
  Qed.

  Lemma only_model_of_min_model_map cls V m :
    clauses_levels cls ⊂_lset V ->
    only_model_of V m -> only_model_of V (min_model_map m cls).
  Proof.
    intros incl om l.
    split.
    - move=> /om => [] [k inm].
      have [hmap [hcls hext]] := min_model_map_spec l cls m.
      specialize (hext l k inm). firstorder.
    - have [hmap [hcls hext]] := min_model_map_spec l cls m.
      move=> [] x /hmap => [] [excl allcl maxm].
      red in maxm.
      destruct excl as [[cl [incls incl']]|inm].
      * apply incl. apply clauses_levels_spec. exists cl. split => //.
        red in incl'.
        apply clause_levels_spec.
        clear -incl'. firstorder. subst. left. apply levelexprset_levels_spec.
        firstorder.
      * rewrite (om l). now exists x.
  Qed.

End Models.
