(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils NonEmptyLevelExprSet SemiLattice.

From MetaRocq.Common Require Universes.
From MetaRocq.Common.LoopChecking Require Import Common Interfaces HornClauses InitialSemilattice.
From Equations Require Import Equations.
Set Equations Transparent.

Module HornSemilattice (LS : LevelSets).
  Module Export Clauses := Clauses LS.
  Module Export SL := InitialSemilattice LS.
  Import NES.

  Local Open Scope sl_scope.

  Definition relations_of_clauses c :=
    Clauses.fold (fun '(prems, concl) acc => (NES.union (singleton concl) prems, prems) :: acc) c [].

  Definition clauses_of_relations r :=
    List.fold_right (fun '(l, r) acc => Clauses.union (clauses_of_eq l r) acc) Clauses.empty r.

  Lemma clauses_of_relations_spec {rels} :
    forall cl, Clauses.In cl (clauses_of_relations rels) ->
      exists r, In r rels /\ Clauses.In cl (clauses_of_eq r.1 r.2).
  Proof.
    rewrite /clauses_of_relations.
    induction rels; cbn.
    - clsets.
    - move=> cl. destruct a as [l r]; cbn in *.
      rewrite Clauses.union_spec => -[].
      * rewrite /clauses_of_eq Clauses.union_spec => -[inl|inr]; cbn;
        rw Clauses.union_spec; cbn.
        exists (l, r). split => //. now left. cbn. now left.
        exists (l, r). split => //. now left. cbn. now right.
      * move/IHrels => [[l' r'] [hin]]; cbn in *.
        rewrite /clauses_of_eq Clauses.union_spec => -[inl|inr]; cbn;
        rw Clauses.union_spec; now exists (l', r'); split => //.
  Qed.

  Lemma clauses_of_relations_spec_inv {rels} :
    forall r, In r rels ->
      Clauses.Subset (clauses_of_eq r.1 r.2) (clauses_of_relations rels).
  Proof.
    rewrite /clauses_of_relations.
    induction rels; cbn.
    - clsets.
    - move=> [l r] //= [].
      * move=> -> ?. rewrite Clauses.union_spec; now left.
      * move/IHrels => //= hin ?. destruct a as [l' r'].
        rewrite Clauses.union_spec; now right.
  Qed.

  Lemma relations_of_clauses_spec {cls} :
    forall eq, In eq (relations_of_clauses cls) ->
      exists prems concl, Clauses.In (prems, concl) cls /\
        eq = (singleton concl ∨ prems, prems).
  Proof.
    rewrite /relations_of_clauses.
    eapply ClausesProp.fold_rec.
    - move=> s'he eq => //=.
    - move=> x a s' s'' hin hnin hadd ih eq.
      destruct x as [prems concl]. cbn.
      intros [<-|ina].
      * do 2 eexists. split => //. apply hadd. now left.
      * move: (ih _ ina) => [? [? []]]. do 2 eexists; split => //.
        apply hadd. now right. assumption.
  Qed.

  Lemma relations_of_clauses_spec_inv {cls} :
    forall cl, Clauses.In cl cls ->
    In (singleton (concl cl) ∨ premise cl, premise cl) (relations_of_clauses cls).
  Proof.
    rewrite /relations_of_clauses.
    eapply ClausesProp.fold_rec.
    - move=> s'he eq => //=.
    - move=> x a s' s'' hin hnin hadd ih eq.
      destruct x as [prems concl]. cbn.
      rewrite hadd.
      intros [<-|ina].
      * cbn. now left.
      * move: (ih _ ina) => insing. now right.
  Qed.

  Definition entails_L_clause p cl :=
    p ⊢ℒ singleton (concl cl) ≤ premise cl.

  Definition entails_L_clauses cls cls' :=
    Clauses.For_all (entails_L_clause (relations_of_clauses cls)) cls'.

  Lemma entails_L_idem_gen {le} {prems : premises} {p} :
    LevelExprSet.In le prems ->
    p ⊢ℒ (singleton le) ∨ prems ≡ prems.
  Proof.
    move: prems; apply: NES.elim.
    - move=> le' /LevelExprSet.singleton_spec <-.
      apply entails_idem.
    - move=> le' x hin hnin /LevelExprSet.add_spec [].
      * unfold LevelExprSet.E.eq in *; intros eq; subst le'.
        rewrite union_comm union_add_singleton.
        rewrite add_idem. apply entails_refl.
      * move/hin => heq.
        rewrite -!union_add_singleton -union_assoc.
        now apply entails_join_congr.
  Qed.

  Lemma in_pred_closure_entails_L {cls} cl :
    in_pred_closure cls cl ->
    entails_L_clause (relations_of_clauses cls) cl.
  Proof.
    induction 1.
    - rewrite /entails_L_clause /rel_le.
      destruct cl as [prems concl]; cbn.
      rewrite -add_prems_singleton -add_prems_union.
      apply entails_add_congr.
      apply entails_c. now eapply (relations_of_clauses_spec_inv (prems, concl)).
    - replace (x, (k + 1)%Z) with (add_expr 1%Z (x, k)).
      rewrite -add_prems_singleton. red; cbn.
      eapply entails_sub.
      now rewrite /succ_expr Z.add_comm.
  Qed.

  Lemma entails_entails_L {cls} cl :
    entails cls cl ->
    entails_L_clause (relations_of_clauses cls) cl.
  Proof.
    intros h; induction h.
    - red.
      now apply entails_L_idem_gen.
    - move: IHh; rewrite -!union_add_singleton.
      eapply in_pred_closure_entails_L in H.
      rewrite /entails_L_clause in H |- *; cbn in *.
      have hsub:= entails_L_subset H H0.
      move=> h'.
      eapply entails_L_le_trans. tea.
      move/entails_L_eq_le_1: hsub. now rewrite union_comm.
  Qed.

  Theorem entails_ℋ_entails_L {cls} cls' :
    cls ⊢ℋ cls' ->
    entails_L_clauses cls cls'.
  Proof.
    move=> h cl /h. apply entails_entails_L.
  Qed.

  Lemma in_pred_closure_entails_clause {cls cl} :
    in_pred_closure cls cl ->
    entails cls cl.
  Proof.
    destruct cl as [prems concl]; intros inp.
    eapply clause_cut; trea.
    constructor. now apply NES.add_spec.
  Qed.

  Lemma in_clause_of_le {le} {l r : premises} :
    LevelExprSet.In le l <->
    Clauses.Clauses.In (r, le) (l ⋞ r).
  Proof.
    rewrite clauses_of_le_spec.
    split.
    - exists le. split => //.
    - intros [lk [hin [=]]]. now subst le.
  Qed.

  Lemma entails_ℋ_entails_L_eq_left {p l r} :
    In (l, r) p ->
    clauses_of_relations p ⊢a r → l.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    eapply clauses_of_relations_spec_inv. tea. cbn.
    rewrite /clauses_of_eq Clauses.union_spec. left.
    apply clauses_of_le_spec. now exists l'.
  Qed.

  Lemma entails_ℋ_entails_L_eq_right {p l r} :
    In (l, r) p ->
    clauses_of_relations p ⊢a l → r.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    eapply clauses_of_relations_spec_inv. tea. cbn.
    rewrite /clauses_of_eq Clauses.union_spec. right.
    apply clauses_of_le_spec. now exists l'.
  Qed.

  Lemma entails_clauses_eq_pres {p l r} :
    In (l, r) p ->
    clauses_of_relations p ⊢ℋ l ≡ r.
  Proof.
    intros hin.
    apply Theory.eq_antisym.
    split.
    - rewrite to_entails_all. now apply entails_ℋ_entails_L_eq_left.
    - rewrite to_entails_all. now apply entails_ℋ_entails_L_eq_right.
  Qed.

  Theorem entails_L_entails {p r} :
    p ⊢ℒ r ->
    clauses_of_relations p ⊢ℋ clauses_of_eq r.1 r.2.
  Proof.
    intros h; depind h; cbn.
    * now eapply entails_clauses_eq_pres.
    * eapply Theory.eq_refl.
    * now eapply Theory.eq_sym.
    * now eapply Theory.eq_trans.
    * now eapply Theory.succ_congr.
    * now eapply Theory.succ_inj in IHh.
    * now eapply Theory.join_congr_left.
    * eapply Theory.join_assoc.
    * eapply Theory.join_idem.
    * eapply Theory.join_comm.
    * eapply Theory.join_succ.
    * eapply Theory.succ_join.
  Qed.

  Lemma entails_L_split p (s t : premises) :
    (forall le, LevelExprSet.In le s -> p ⊢ℒ singleton le ≤ t) ->
    p ⊢ℒ s ≤ t.
  Proof.
    move: s; apply: NES.elim.
    - intros [l k] ih. eapply ih.
      now apply LevelExprSet.singleton_spec.
    - move=> le x h hnin ih.
      forward h.
      { move=> le' hin. move: (ih le') => /fwd //.
        eapply LevelExprSet.add_spec. now right. }
      specialize (ih le); forward ih.
      eapply LevelExprSet.add_spec; now left.
      rewrite -union_add_singleton.
      now eapply entails_L_le_join.
  Qed.

  Lemma entails_L_clauses_pres_all {p s t} :
    (relations_of_clauses (clauses_of_relations p)) ⊢ℒ s ≡ t ->
    p ⊢ℒ s ≡ t.
  Proof.
    induction 1; try solve [econstructor; eauto]. cbn in H.
    move/relations_of_clauses_spec: H => [prems [concl [hin heq]]].
    noconf heq.
    move/clauses_of_relations_spec: hin => [[l r]] [] hin //=.
    rewrite /clauses_of_eq Clauses.union_spec => -[] hin';
    eapply entails_L_le_eq;
    rewrite clauses_of_le_spec in hin'.
    - destruct hin' as [? [hin' heq]]. noconf heq.
      eapply entails_L_le_trans with l.
      * now eapply entails_L_in.
      * eapply entails_L_eq_le_1. now constructor.
    - destruct hin' as [? [hin' heq]]; noconf heq.
      eapply entails_L_le_trans with r.
      + now eapply entails_L_in.
      + eapply entails_L_eq_le_1. eapply entails_sym. now constructor.
  Qed.

  Lemma entails_L_clauses_pres_le {p s t} :
    entails_L_clauses (clauses_of_relations p) (s ⋞ t) ->
    p ⊢ℒ s ≤ t.
  Proof.
    intros hf. do 2 red in hf.
    rw_in clauses_of_le_spec hf.
    eapply entails_L_split.
    move=> le hin.
    move: (hf (t, le)) => /fwd.
    { exists le; split => //. }
    move=> h; red in h. cbn in h.
    now eapply entails_L_clauses_pres_all in h.
  Qed.

  Lemma entails_L_clauses_of_relations_eq {p s t} :
    entails_L_clauses (clauses_of_relations p) (s ≡ t) ->
    p ⊢ℒ s ≡ t.
  Proof.
    intros hf. do 2 red in hf.
    eapply entails_L_eq_antisym.
    all: apply entails_L_clauses_pres_le.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
  Qed.

  Lemma completeness_eq p s t :
    p ⊢ℒ s ≡ t <->
    clauses_of_relations p ⊢ℋ clauses_of_eq s t.
  Proof.
    split.
    - move/entails_L_entails => //=.
    - move/entails_ℋ_entails_L.
      by apply entails_L_clauses_of_relations_eq.
  Qed.
(*
  Lemma entails_L_clause_entails {cls cl} :
    entails_L_clause (relations_of_clauses cls) cl ->
    entails cls cl.
  Proof. *)

  Lemma clauses_of_relations_relations_of_clauses {cls} : cls ⊂_clset (clauses_of_relations (relations_of_clauses cls)).
  Proof.
    intros cl.
    move/relations_of_clauses_spec_inv/clauses_of_relations_spec_inv => //=; apply.
    rewrite /clauses_of_eq Clauses.union_spec. left.
    eapply clauses_of_le_spec. exists (concl cl). split => //. rewrite LevelExprSet.union_spec. left; now apply LevelExprSet.singleton_spec.
    now destruct cl.
  Qed.

  Lemma entails_all_singleton cls prems concl :
    cls ⊢a prems → singleton concl <-> cls ⊢ prems → concl.
  Proof.
    split.
    - move/(_ concl) => /fwd //. now apply LevelExprSet.singleton_spec.
    - move=> cl cl' /LevelExprSet.singleton_spec. intros e; red in e; now subst cl'.
  Qed.

  Lemma entails_ℋ_singleton cls prems concl :
    cls ⊢ℋ singleton concl ⋞ prems <-> cls ⊢ prems → concl.
  Proof.
    rewrite to_entails_all. apply entails_all_singleton.
  Qed.

  Lemma entails_ℋ_clauses_of_relations {cls cls'} :
    clauses_of_relations (relations_of_clauses cls) ⊢ℋ cls' ->
    cls ⊢ℋ cls'.
  Proof.
    move=> ha. eapply (entails_clauses_cut (cls0 := clauses_of_relations (relations_of_clauses cls))); revgoals.
    eapply entails_ℋ_clauses_subset; tea.
    { intros ?; rewrite Clauses.union_spec; now left. }
    intros cl.
    move/clauses_of_relations_spec => [] [l r] [] //= /relations_of_clauses_spec [] prems [] concl [] hin [=] -> ->.
    have eq : cls ⊢ℋ (singleton concl ∪ prems) ≡ prems.
    apply Theory.le_spec, to_entails_all, entails_all_singleton.
    now eapply entails_in.
    now move/eq.
  Qed.

    (* - move/clauses_of_relations_spec => [] [l r] [] /relations_of_clauses_spec [] prems [] [concl k] [] incls [=] -> -> //=.
      rewrite /clauses_of_eq Clauses.union_spec. !clauses_of_le_spec => -[[lk [hin heq]]|[lk [hin heq]]].
      * subst cl.
       exists (concl cl). split => //. rewrite LevelExprSet.union_spec. left; now apply LevelExprSet.singleton_spec.
 *)

  Lemma entails_L_entails_ℋ {cls} cls' :
    entails_L_clauses cls cls' ->
    cls ⊢ℋ cls'.
  Proof.
    move=> hcl cl /hcl.
    move/entails_L_entails => //=.
    move/entails_ℋ_clauses_of_relations/Theory.eq_antisym => -[] + _.
    move/Theory.join_le_left => -[] + _.
    move/entails_ℋ_singleton.
    now destruct cl.
  Qed.

  Lemma entails_L_clauses_eq {p s t} :
    entails_L_clauses p (s ≡ t) <->
    entails_L_clauses p (s ⋞ t) /\ entails_L_clauses p (t ⋞ s).
  Proof.
    rewrite /entails_L_clauses /clauses_of_eq.
    split.
    - intros ha; split => l; move:(ha l); rewrite Clauses.union_spec;
      intros he hle; apply he; now constructor.
    - intros [le le'] l.
      rewrite Clauses.union_spec; intros []; [apply le|apply le']; assumption.
  Qed.

  Theorem entails_L_entails_ℋ_equiv {cls cls'} :
    entails_L_clauses cls cls' <-> cls ⊢ℋ cls'.
  Proof.
    split.
    - apply entails_L_entails_ℋ.
    - apply entails_ℋ_entails_L.
  Qed.

End HornSemilattice.
