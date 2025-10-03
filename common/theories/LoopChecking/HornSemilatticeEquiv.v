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
  Module Import ISL := InitialSemilattice LS.
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

  Lemma relations_of_clauses_union {cls cls'} :
    equivlistA Logic.eq (relations_of_clauses (Clauses.union cls cls'))
      (relations_of_clauses cls ++ relations_of_clauses cls').
  Proof.
    intros eq. split; rewrite !InA_In_eq; rewrite in_app_iff.
    - move/relations_of_clauses_spec => -[] prems [] concl [] hin ->.
      eapply Clauses.union_spec in hin as [hin|hin]; [left|right];
      now apply (relations_of_clauses_spec_inv (_, _)).
    - move=> [] /relations_of_clauses_spec => -[] prems [] concl [] hin ->;
      apply (relations_of_clauses_spec_inv (_, _)); now apply Clauses.union_spec.
  Qed.

  Definition entails_L_pres_clause p cl :=
    p ⊢ℒ singleton (concl cl) ≤ premise cl.

  Definition entails_L_pres_clauses p cls :=
    Clauses.For_all (entails_L_pres_clause p) cls.

  Definition entails_L_clause cls cl :=
    entails_L_pres_clause (relations_of_clauses cls) cl.

  Definition entails_L_clauses cls cls' :=
    entails_L_pres_clauses (relations_of_clauses cls) cls'.

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
    entails_L_pres_clause (relations_of_clauses cls) cl.
  Proof.
    induction 1.
    - rewrite /entails_L_pres_clause /rel_le.
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
    entails_L_pres_clause (relations_of_clauses cls) cl.
  Proof.
    intros h; induction h.
    - red.
      now apply entails_L_idem_gen.
    - move: IHh; rewrite -!union_add_singleton.
      eapply in_pred_closure_entails_L in H.
      rewrite /entails_L_pres_clause in H |- *; cbn in *.
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

  Lemma entails_L_pres_clauses_of_le {p s t} :
    entails_L_pres_clauses p (s ⋞ t) <->
    p ⊢ℒ s ≤ t.
  Proof.
    split.
    - unfold entails_L_clauses.
      intros hf. do 2 red in hf.
      rw_in clauses_of_le_spec hf.
      eapply entails_L_split.
      move=> le hin.
      move: (hf (t, le)) => /fwd.
      { exists le; split => //. }
      now move=> h; red in h.
    - intros hf. rewrite /entails_L_pres_clauses.
      intros cl. rewrite clauses_of_le_spec => -[] le [hin ->].
      red. cbn. eapply entails_L_le_trans; tea. now eapply entails_L_in.
  Qed.

  Lemma entails_L_clauses_pres_le {p s t} :
    entails_L_clauses (clauses_of_relations p) (s ⋞ t) ->
    p ⊢ℒ s ≤ t.
  Proof.
    rewrite /entails_L_clauses entails_L_pres_clauses_of_le.
    now move/entails_L_clauses_pres_all.
  Qed.


  Lemma entails_L_pres_clauses_of_eq_split {p s t} :
    entails_L_pres_clauses p (s ≡ t) <->
    entails_L_pres_clauses p (s ⋞ t) /\
    entails_L_pres_clauses p (t ⋞ s).
  Proof.
    rewrite /entails_L_pres_clauses /clauses_of_eq /Clauses.For_all.
    setoid_rewrite Clauses.union_spec.
    split.
    - intros h; split.
      * intros h' hcl. apply h. now left.
      * intros h' hcl. apply h. now right.
    - intros [] x []; eauto.
  Qed.

  Lemma entails_L_pres_clauses_of_relations_eq {p s t} :
    entails_L_pres_clauses p (s ≡ t) <->
    p ⊢ℒ s ≡ t.
  Proof.
    rewrite entails_L_pres_clauses_of_eq_split.
    rewrite !entails_L_pres_clauses_of_le.
    eapply entails_L_eq_antisym.
  Qed.

  Lemma entails_L_clauses_of_relations_eq {p s t} :
    entails_L_clauses (clauses_of_relations p) (s ≡ t) ->
    p ⊢ℒ s ≡ t.
  Proof.
    rewrite /entails_L_clauses entails_L_pres_clauses_of_relations_eq.
    now move/entails_L_clauses_pres_all.
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
    entails_L_pres_clause (relations_of_clauses cls) cl ->
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

  Lemma entails_ℋ_clauses_of_relations_equiv {cls cls'} :
    cls ⊢ℋ cls' <->
    clauses_of_relations (relations_of_clauses cls) ⊢ℋ cls'.
  Proof.
    split.
    - move/entails_ℋ_clauses_subset; apply. apply clauses_of_relations_relations_of_clauses.
    - apply entails_ℋ_clauses_of_relations.
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

  Lemma entails_L_clauses_entails_L_relations cls r :
    relations_of_clauses cls ⊢ℒ r <->
    entails_L_clauses cls (clauses_of_eq r.1 r.2).
  Proof.
    rewrite entails_L_clauses_eq.
    destruct r as [l r]; cbn.
    rewrite -entails_L_eq_antisym.
    split; intros [le le']; split.
    all:by apply entails_L_pres_clauses_of_le.
  Qed.

  Lemma clauses_of_relations_cons {l r rels} :
    clauses_of_relations ((l, r) :: rels) =_clset
    Clauses.union (clauses_of_eq l r) (clauses_of_relations rels).
  Proof.
    cbn. reflexivity.
  Qed.

  Lemma entails_L_cut {Γ r r'} :
    Γ ⊢ℒ r ->
    r :: Γ ⊢ℒ r' ->
    Γ ⊢ℒ r'.
  Proof.
    destruct r as [l r], r' as [l' r'].
    move/completeness_eq => h1.
    move/completeness_eq => h2.
    apply completeness_eq.
    rewrite clauses_of_relations_cons in h2.
    eapply entails_clauses_cut; tea.
  Qed.

  Lemma entails_L_all_entails_cut {Γ r r'} :
    Γ ⊢ℒ r ->
    r :: Γ ⊩ℒ r' ->
    Γ ⊩ℒ r'.
  Proof.
    intros h; elim; constructor.
    now eapply entails_L_cut. exact H1.
  Qed.

  Lemma entails_L_all_cut {p q r} :
    p ⊩ℒ q -> q ++ p ⊢ℒ r -> p ⊢ℒ r.
  Proof.
    move=> hp. move: hp r. elim.
    - move=> r hr. eapply entails_L_rels_subset; tea. now red.
    - move=> x l px pl ih r hxl.
      move: (ih r) => /fwd //.
      cbn in hxl. eapply entails_L_cut; tea.
      eapply entails_L_rels_subset in px. tea. red => ?. now rewrite in_app_iff.
  Qed.

  Lemma entails_L_all_one_trans {p q r} :
    p ⊩ℒ q -> q ⊢ℒ r -> p ⊢ℒ r.
  Proof.
    intros hq hr. eapply entails_L_all_cut; tea.
    eapply entails_L_rels_subset; tea. red => ?; now rewrite in_app_iff.
  Qed.

  Lemma entails_L_all_trans {p q r} :
    p ⊩ℒ q -> q ⊩ℒ r -> p ⊩ℒ r.
  Proof.
    move=> hp. elim.
    - constructor.
    - move=> re res ent hres ih.
      constructor. eapply entails_L_all_one_trans. exact hp. exact ent. exact ih.
  Qed.


  Instance entails_L_all_preorder : PreOrder entails_L_rels.
  Proof.
    split.
    - red. apply entails_L_all_refl.
    - red. intros x y z. apply entails_L_all_trans.
  Qed.

  Instance equiv_L_rels_equiv : Equivalence equiv_L_rels.
  Proof.
    split.
    - intros r. split; eapply entails_L_all_refl.
    - intros r r' []; split; auto.
    - intros r r0 r1 [] []; split; eapply entails_L_all_trans; eauto.
  Qed.

  Instance entails_L_all_partial_order : PartialOrder equiv_L_rels entails_L_rels.
  Proof.
    split; tc; auto.
  Qed.

  Instance entails_L_proper_equiv : Proper (equiv_L_rels ==> Logic.eq ==> iff) entails_L.
  Proof.
    intros r r' h ?? ->. split.
    - intros h'. destruct h. eapply entails_L_all_one_trans; tea.
    - intros h'. destruct h. eapply entails_L_all_one_trans; tea.
  Qed.

  Lemma relations_of_clauses_mon {s s'}: s ⊂_clset s' -> incl (relations_of_clauses s) (relations_of_clauses s').
  Proof.
    intros hs.
    move=> x /relations_of_clauses_spec [] prems [] concl [hin heq]. subst x.
    apply hs in hin. eapply relations_of_clauses_spec_inv in hin. now cbn in *.
  Qed.

  Lemma relations_of_clauses_eq {s s' : clauses} :
    s =_clset s' ->
    equivlistA Logic.eq (relations_of_clauses s) (relations_of_clauses s').
  Proof.
    intros eq.
    red. intros []; rewrite !InA_In_eq.
    split.
    - apply relations_of_clauses_mon. clsets.
    - apply relations_of_clauses_mon. clsets.
  Qed.

  Instance relations_of_clauses_proper : Proper (Clauses.Equal ==> equivlistA Logic.eq) relations_of_clauses.
  Proof.
    intros cls cls' H. now apply relations_of_clauses_eq.
  Qed.

  Lemma entails_L_clauses_subset {cls cls' r} :
    entails_L_clauses cls r ->
    Clauses.Subset cls cls' ->
    entails_L_clauses cls' r.
  Proof.
    intros ent sub.
    red. red. do 2 red in ent.
    move=> cl /ent. unfold entails_L_clause.
    intros ent'.
    eapply entails_L_rels_subset; tea.
    now apply relations_of_clauses_mon.
  Qed.

  Lemma entails_L_all_relations_of_clauses {cls cls'} :
    cls =_clset cls' ->
    relations_of_clauses cls ⊩ℒ relations_of_clauses cls'.
  Proof.
    intros heq. rewrite (relations_of_clauses_eq heq).
    reflexivity.
  Qed.

  Lemma entails_L_clauses_subset_all {cls cls'} :
    cls ⊂_clset cls' ->
    relations_of_clauses cls' ⊩ℒ relations_of_clauses cls.
  Proof.
    intros heq.
    have hm := relations_of_clauses_mon heq.
    now eapply entails_L_clauses_incl.
  Qed.

  Lemma entails_clauses_tauto cls : cls ⊢ℋ cls.
  Proof.
    intros cl hin. now apply entails_in.
  Qed.

  Lemma entails_L_clauses_tauto cls : entails_L_clauses cls cls.
  Proof.
    intros cl hin. red. eapply entails_L_entails_ℋ_equiv; tea.
    apply entails_clauses_tauto.
  Qed.

  Lemma entails_L_relations_of_clauses_le_impl l r :
    relations_of_clauses (l ⋞ r) ⊢ℒ l ≤ r.
  Proof.
    eapply completeness_eq.
    rewrite -entails_ℋ_clauses_of_relations_equiv.
    apply Theory.eq_antisym. split.
    - apply Theory.join_le_left. split. apply entails_clauses_tauto.
      apply Theory.le_refl.
    - apply Theory.join_right.
  Qed.

  Lemma entails_L_relations_of_clauses_eq l r :
    relations_of_clauses (l ≡ r) ⊢ℒ l ≡ r.
  Proof.
    eapply completeness_eq.
    rewrite -entails_ℋ_clauses_of_relations_equiv.
    apply entails_clauses_tauto.
  Qed.

  Lemma entails_L_to_clauses_pres_all {p r} :
    p ⊢ℒ r ->
    (relations_of_clauses (clauses_of_relations p)) ⊢ℒ r.
  Proof.
    intros h; depind h.
    all:try solve [econstructor; eauto].
    apply clauses_of_relations_spec_inv in H. cbn in H.
    have hr := relations_of_clauses_spec_inv (cls := clauses_of_relations p).
    rewrite entails_L_clauses_entails_L_relations. cbn.
    eapply entails_L_clauses_subset; tea.
    eapply entails_L_clauses_tauto.
  Qed.

  Lemma entails_L_clause_rels {p cl} :
    entails_L_pres_clause p cl ->
    entails_L_pres_clause (relations_of_clauses (clauses_of_relations p)) cl.
  Proof.
    now move/entails_L_to_clauses_pres_all.
  Qed.

  Lemma entails_L_clauses_relations {p cls} :
    entails_L_pres_clauses p cls ->
    entails_L_pres_clauses (relations_of_clauses (clauses_of_relations p)) cls.
  Proof.
    now move=> hcls cl /hcls/entails_L_clause_rels.
  Qed.


  Lemma entails_L_in_cls {prems concl cls} :
    Clauses.In (prems, concl) cls -> relations_of_clauses cls ⊢ℒ singleton concl ≤ prems.
  Proof.
    intros hin. eapply entails_c.
    apply relations_of_clauses_spec_inv in hin. now cbn in hin.
  Qed.

  Lemma entails_L_relations_of_clauses_le l r :
    relations_of_clauses (l ⋞ r) ⊫ℒ [l ≤ r]%rel.
  Proof.
    split.
    - constructor. apply entails_L_relations_of_clauses_le_impl. constructor.
    - apply Forall_forall => rel.
      move/relations_of_clauses_spec => [] prems [] concl [] hin ->.
      unfold rel_le.
      eapply clauses_of_le_spec in hin as [k [hin heq]]. noconf heq.
      eapply entails_trans with (l ∨ r). 2:{ eapply entails_c. constructor. now constructor. }
      apply entails_L_eq_antisym. split.
      eapply entails_L_le_join_l. now eapply entails_L_in.
      eapply entails_L_le_trans with r.
      eapply entails_L_eq_le_1. eapply entails_c; now constructor.
      eapply entails_L_le_right.
  Qed.

End HornSemilattice.
