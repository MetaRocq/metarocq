  Record presentation :=
    { V : LevelSet.t; C : rels }.

  Definition presentation_of cstrs :=
    {| V := levels_of_z_constraints cstrs;
       C := relations_of_constraints cstrs |}.


  Definition presentation_of_clauses cls :=
    {| V := Clauses.clauses_levels cls;
       C := relations_of_clauses cls |}.


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
    rewrite interp_prems_union in vc. apply vc.
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
