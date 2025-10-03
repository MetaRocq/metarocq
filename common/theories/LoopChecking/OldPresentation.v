  Record presentation :=
    { V : LevelSet.t; C : rels }.

  Definition presentation_of cstrs :=
    {| V := levels_of_z_constraints cstrs;
       C := relations_of_constraints cstrs |}.


  Definition presentation_of_clauses cls :=
    {| V := Clauses.clauses_levels cls;
       C := relations_of_clauses cls |}.


  Definition entails_cstr cstrs c :=
    entails_clauses (to_clauses cstrs) (LoopCheck.to_clauses (to_constraint c)).

  Definition entails_z_cstr cstrs c :=
    entails_clauses (of_z_constraints cstrs) (LoopCheck.to_clauses c).

  Definition entails_cstrs cstrs cstrs' :=
    entails_clauses (of_z_constraints cstrs) (of_z_constraints cstrs').


  Lemma check_valid m c :
    check m c <-> entails_cstr (constraints m) c.
  Proof.
    rewrite /check LoopCheck.check_spec.
    rewrite /entails_clauses.
    enough ((LoopCheck.clauses (model m)) =_clset (to_clauses (constraints m))).
    { split; intros ? ?.
      move/H0. now rewrite H.
      move/H0. now rewrite H. }
    intros cl.
    rewrite to_clauses_spec.
    split.
    - now move/(repr_constraints_inv m).
    - intros [cstr [hin incl]].
      eapply (repr_constraints m); tea.
  Qed.

  Lemma presentation_of_clauses_spec cls prems concl :
    Clauses.In (prems, concl) cls ->
    In (NES.singleton concl ∨ prems, prems) (C (presentation_of_clauses cls)).
  Proof.
    rewrite /presentation_of_clauses //=.
    move/relations_of_clauses_spec_inv => //=.
  Qed.

  (* Import LoopCheck.Impl.I.Model.Model.Clauses.FLS. *)

  Definition presentation_entails cstrs c :=
    let '(l, d, r) := to_constraint c in
    match d with
    | ConstraintType.Le => relations_of_constraints (to_z_cstrs cstrs) ⊢ℒ l ≤ r
    | ConstraintType.Eq => relations_of_constraints (to_z_cstrs cstrs) ⊢ℒ l ≡ r
    end.

  Lemma check_valid_pres m c :
    check m c <-> presentation_entails (constraints m) c.
  Proof.
    rewrite check_valid.
    destruct c as [[l []] r]; cbn.
    - rewrite completeness_le.
      rewrite /entails_cstr /entails_z_cstr.
      now rewrite to_clauses_of_z_constraints.
    - rewrite completeness_eq_cstrs.
      rewrite /entails_cstr /entails_z_cstr.
      now rewrite to_clauses_of_z_constraints.
  Qed.
  Lemma presentation_entails_valid_eq {p l r} :
    p ⊢ℒ l ≡ r -> valid_constraint p (l, ConstraintType.Eq, r).
  Proof.
    move/completeness.
    rewrite /valid_relation /valid_constraint /interp_z_cstr //=.
  Qed.

  Lemma presentation_entails_valid_le {p l r} :
    p ⊢ℒ l ≤ r -> valid_constraint p (l, ConstraintType.Le, r).
  Proof.
    rewrite /valid_constraint /interp_z_cstr //=.
    move/presentation_entails_valid_eq => vc v hc.
    specialize (vc v hc). cbn in vc.
    rewrite interp_nes_union in vc. apply vc.
  Qed.

  Lemma presentation_entails_valid {p c} :
    entails_L_cstr p c -> valid_constraint p c.
  Proof.
    destruct c as [[l []] r]; cbn.
    - apply presentation_entails_valid_le.
    - apply presentation_entails_valid_eq.
  Qed.

  Lemma presentation_entails_satisfies {p cstrs} :
    entails_L_cstrs p cstrs -> valid_cstrs p cstrs.
  Proof.
    intros ha c hin. specialize (ha c hin).
    now apply presentation_entails_valid.
  Qed.

  Lemma completeness_eq_cstrs cstrs s t :
    relations_of_constraints cstrs ⊢ℒ s ≡ t <->
    entails_z_cstr cstrs (s, ConstraintType.Eq, t).
  Proof.
    unfold entails_z_cstr.
    rewrite -entails_L_entails_ℋ_equiv.
    rewrite -LoopCheck.Impl.Abstract.entails_L_rels_entails_L_clauses.
    rewrite relation_of_constraint_of_clause //=.
    now rewrite rels_of_z_constraints_spec entails_L_all_tip.
  Qed.

  Lemma completeness_le cstrs s t :
    relations_of_constraints cstrs ⊢ℒ s ≤ t <->
    entails_z_cstr cstrs (s, ConstraintType.Le, t).
  Proof.
    unfold entails_z_cstr.
    split.
    - move/completeness_eq_cstrs. cbn.
      intros h; red in h. cbn in h.
      eapply Theory.le_spec. now rewrite /Clauses.le.
    - move/entails_ℋ_entails_L. apply entails_L_clauses_le.
  Qed.



  Lemma entails_clauses_le {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Le, r) cstrs ->
    of_z_constraints cstrs ⊢a r → l.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    rewrite of_z_constraints_spec. eexists; split; tea.
    now apply in_clause_of_le.
  Qed.

  Lemma entails_clauses_eq_left {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Eq, r) cstrs ->
    of_z_constraints cstrs ⊢a r → l.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    rewrite of_z_constraints_spec. eexists; split; tea.
    rewrite LoopCheck.to_clauses_spec. left. exists l'. split => //.
  Qed.

  Lemma entails_clauses_eq_right {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Eq, r) cstrs ->
    of_z_constraints cstrs ⊢a l → r.
  Proof.
    intros hin l' cl.
    eapply in_pred_closure_entails_clause, incls0.
    rewrite of_z_constraints_spec. eexists; split; tea.
    rewrite LoopCheck.to_clauses_spec. right. exists l'. split => //.
  Qed.

  Lemma entails_clauses_eq_cstr {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Eq, r) cstrs ->
    of_z_constraints cstrs ⊢ℋ l ≡ r.
  Proof.
    intros hin.
    apply Theory.eq_antisym.
    split.
    - rewrite to_entails_all. now apply entails_clauses_eq_left.
    - rewrite to_entails_all. now apply entails_clauses_eq_right.
  Qed.

  Lemma entails_clauses_le_cstr {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Le, r) cstrs ->
    of_z_constraints cstrs ⊢ℋ l ⋞ r.
  Proof.
    intros hin.
    rewrite to_entails_all. now apply entails_clauses_le.
  Qed.

  Lemma entails_L_clauses_eq_cstr {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Eq, r) cstrs ->
    relations_of_clauses (of_z_constraints cstrs) ⊢ℒ l ≡ r.
  Proof.
    move/entails_clauses_eq_cstr.
    rewrite -entails_L_entails_ℋ_equiv.
    now rewrite -(entails_L_clauses_entails_L_relations _ (l, r)).
  Qed.

  Lemma entails_L_clauses_le_cstr {cstrs l r} :
    ZUnivConstraintSet.In (l, ConstraintType.Le, r) cstrs ->
    relations_of_clauses (of_z_constraints cstrs) ⊢ℒ l ≤ r.
  Proof.
    move/entails_clauses_le_cstr.
    rewrite -entails_L_entails_ℋ_equiv.
    now rewrite /entails_L_clauses Clauses.entails_L_pres_clauses_of_le.
  Qed.

  Lemma entails_L_clauses_leq_def {p l r} :
    entails_L_clauses p (l ⋞ r) <-> entails_L_clauses p (l ∨ r ≡ r).
  Proof.
    rewrite /entails_L_clauses.
    rewrite entails_L_pres_clauses_of_relations_eq.
    now rewrite Clauses.entails_L_pres_clauses_of_le.
  Qed.

    Lemma entails_to_clauses {prems concl cstr} :
     Clauses.In (prems, concl) (LoopCheck.to_clauses cstr) ->
     [relation_of_constraint cstr] ⊢ℒ (singleton concl ≤ prems).
  Proof.
    destruct cstr as [[l []] r].
    - intros hin. cbn -[le].
      have en := entails_L_relations_of_clauses_le l r.
      setoid_rewrite <- en. cbn in hin.
      now eapply entails_L_in_cls.
    - intros hin; cbn in hin |- *.
      rewrite -entails_L_relations_of_clauses_eq.
      now eapply entails_L_in_cls.
  Qed.

  Lemma entails_L_clauses_all {cstrs s t} :
    (relations_of_clauses (of_z_constraints cstrs)) ⊢ℒ s ≡ t <->
    (relations_of_constraints cstrs) ⊢ℒ s ≡ t.
  Proof.
    now rewrite rels_of_z_constraints_spec.
  Qed.

  Lemma entails_L_clauses_le {cstrs s t} :
    entails_L_pres_clauses (relations_of_clauses (of_z_constraints cstrs)) (s ⋞ t) ->
    relations_of_constraints cstrs ⊢ℒ s ≤ t.
  Proof.
    intros hf. do 2 red in hf. rw_in clauses_of_le_spec hf.
    eapply entails_L_split.
    move=> le hin.
    move: (hf (t, le)) => /fwd.
    { exists le; split => //. }
    move=> h; red in h. cbn in h.
    now eapply entails_L_clauses_all in h.
  Qed.

  Lemma entails_L_clauses_of_eq {cstrs s t} :
    entails_L_pres_clauses (relations_of_clauses (of_z_constraints cstrs)) (s ≡ t) ->
    relations_of_constraints cstrs ⊢ℒ s ≡ t.
  Proof.
    intros hf. do 2 red in hf.
    eapply entails_L_eq_antisym. split.
    all: apply entails_L_clauses_le.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
    - intros cl hin; red. eapply hf.
      rewrite /clauses_of_eq. clsets.
  Qed.


  Definition entails_L_cstr p c :=
    let '(l, d, r) := c in
    match d with
    | ConstraintType.Le => p ⊢ℒ l ≤ r
    | ConstraintType.Eq => p ⊢ℒ l ≡ r
    end.

  Lemma entails_L_clauses_cstr {cstrs c} :
    entails_L_clauses (of_z_constraints cstrs) (LoopCheck.to_clauses c) ->
    entails_L_cstr (relations_of_constraints cstrs) c.
  Proof.
    destruct c as [[l []] r].
    - cbn. apply entails_L_clauses_le.
    - cbn. apply entails_L_clauses_of_eq.
  Qed.

  Definition entails_L_cstrs p cstrs :=
    ZUnivConstraintSet.For_all (entails_L_cstr p) cstrs.
