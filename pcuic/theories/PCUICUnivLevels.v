
Definition fresh_levels global_levels levels :=
    LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels.

  Definition declared_constraints_levels levels cstrs :=
    UnivConstraintSet.For_all (declared_univ_cstr_levels levels) cstrs.

  Definition declared_constraints_levels_union levels cstrs cstrs' :
    declared_constraints_levels levels cstrs ->
    declared_constraints_levels levels cstrs' ->
    declared_constraints_levels levels (UnivConstraintSet.union cstrs cstrs').
  Proof.
    intros decl decl'.
    rewrite /declared_constraints_levels.
    intros x inx.
    eapply ConstraintSetProp.FM.union_1 in inx as [].
    now eapply decl. now eapply decl'.
  Qed.

  Definition declared_constraints_levels_union_left levels levels' cstrs :
    declared_constraints_levels levels cstrs ->
    declared_constraints_levels (LevelSet.union levels levels') cstrs.
  Proof.
    rewrite /declared_constraints_levels.
    intros hx x inx.
    specialize (hx x inx).
    destruct x as [[l d] r]. split.
    destruct hx. now eapply LevelSetFact.union_2.
    destruct hx.
    now eapply LevelSetFact.union_2.
  Qed.

  Definition declared_constraints_levels_union_right levels levels' cstrs :
    declared_constraints_levels levels' cstrs ->
    declared_constraints_levels (LevelSet.union levels levels') cstrs.
  Proof.
    rewrite /declared_constraints_levels.
    intros hx x inx.
    specialize (hx x inx).
    destruct x as [[l d] r].
    destruct hx; split. now eapply LevelSetFact.union_3.
    now eapply LevelSetFact.union_3.
  Qed.

  Definition declared_constraints_levels_subset levels levels' cstrs :
    declared_constraints_levels levels cstrs ->
    LevelSet.Subset levels levels' ->
    declared_constraints_levels levels' cstrs.
  Proof.
    rewrite /declared_constraints_levels.
    intros hx sub x inx.
    specialize (hx x inx). red in hx.
    destruct x as [[l d] r]; cbn in *.
    split.
    red in inx.
    now eapply sub.
    now eapply sub.
  Qed.

  Lemma on_udecl_spec `{checker_flags} Σ (udecl : universes_decl) :
    on_udecl Σ udecl =
    let levels := levels_of_udecl udecl in
    let global_levels := global_levels Σ in
    let all_levels := LevelSet.union levels global_levels in
    fresh_levels global_levels levels
    /\ declared_constraints_levels all_levels (constraints_of_udecl udecl)
    /\ satisfiable_udecl Σ udecl.
  Proof. unfold on_udecl. reflexivity. Qed.

  Lemma on_udecl_prop_spec `{checker_flags} Σ (udecl : universes_decl) :
    on_udecl_prop Σ udecl =
      let levels := levels_of_udecl udecl in
      let global_levels := global_levels Σ in
      let all_levels := LevelSet.union levels global_levels in
      declared_constraints_levels all_levels (constraints_of_udecl udecl).
  Proof. reflexivity. Qed.

  Notation levels_of_list := LevelSetProp.of_list.

  Lemma levels_of_list_app l l' :
    levels_of_list (l ++ l') =
    LevelSet.union (levels_of_list l)
      (levels_of_list l').
  Proof.
    rewrite /LevelSetProp.of_list fold_right_app.
    induction l; cbn.
    apply LevelSet.eq_leibniz. red.
    rewrite LevelSet_union_empty //.
    apply LevelSet.eq_leibniz. red.
    rewrite IHl. rewrite LevelSetProp.union_add //.
  Qed.

  Definition aulevels inst cstrs :
    AUContext.levels (inst, cstrs) =
    LevelSetProp.of_list (unfold #|inst| Level.Var).
  Proof.
    cbn.
    now rewrite mapi_unfold.
  Qed.

  #[global] Instance unfold_proper {A} : Proper (eq ==> `=1` ==> eq) (@unfold A).
  Proof.
    intros x y -> f g eqfg.
    induction y; cbn; auto. f_equal; auto. f_equal. apply eqfg.
  Qed.

  (* sLemma unfold_add {A} n k (f : nat -> A) : skipn k (unfold (k + n) f) = unfold k (fun x => f (x + n)). *)

  Lemma unfold_add {A} n k (f : nat -> A) : unfold (n + k) f = unfold k f ++ unfold n (fun x => f (x + k)).
  Proof.
    induction n in k |- *.
    cbn. now rewrite app_nil_r.
    cbn. rewrite IHn. now rewrite app_assoc.
  Qed.


  Definition unfold_levels_app n k :
    LevelSetProp.of_list (unfold (n + k) Level.Var) =
    LevelSet.union (LevelSetProp.of_list (unfold k Level.Var))
      (LevelSetProp.of_list (unfold n (fun i => Level.Var (k + i)))).
  Proof.
    rewrite unfold_add levels_of_list_app //.
    now setoid_rewrite Nat.add_comm at 1.
  Qed.

  Lemma levels_of_list_spec l ls :
    LevelSet.In l (levels_of_list ls) <-> In l ls.
  Proof.
    now rewrite LevelSetProp.of_list_1 InA_In_eq.
  Qed.

  Lemma In_unfold k l n :
    In l (unfold n (λ i : nat, Level.Var (k + i))) <-> ∃ k' : nat, l = Level.Var k' ∧ k <= k' < k + n.
  Proof.
    induction n; cbn => //. firstorder. lia.
    split. intros [] % in_app_or => //.
    eapply IHn in H as [k' [eq lt]]. subst l; exists k'. intuition lia.
    destruct H as []; subst => //.
    exists (k + n). intuition lia.
    intros [k' [-> lt]].
    apply/in_or_app.
    destruct (eq_dec k' (k + n)). subst k'.
    right => //. cbn; auto.
    left. eapply IHn. exists k'; intuition lia.
  Qed.

  Lemma In_levels_of_list k l n :
    LevelSet.In l (levels_of_list (unfold n (fun i => Level.Var (k + i)))) <->
    exists k', l = Level.Var k' /\ k <= k' < k + n.
  Proof.
    rewrite LevelSetProp.of_list_1 InA_In_eq. now apply In_unfold.
  Qed.

  Lemma In_lift_level k l n : LevelSet.In l (levels_of_list (unfold n (λ i : nat, Level.Var i))) <->
    LevelSet.In (lift_level k l) (levels_of_list (unfold n (λ i : nat, Level.Var (k + i)))).
  Proof.
    split.
    - move/(In_levels_of_list 0) => [k' [-> l'lt]].
      eapply In_levels_of_list. exists (k + k'); cbn; intuition lia.
    - move/(In_levels_of_list k) => [k' [eq l'lt]].
      eapply (In_levels_of_list 0).
      destruct l; noconf eq. exists n0; cbn; intuition lia.
  Qed.

  Lemma not_var_lift l k s :
    LS.For_all (λ x : LS.elt, ~~ Level.is_var x) s ->
    LevelSet.In l s ->
    LevelSet.In (lift_level k l) s.
  Proof.
    intros.
    specialize (H _ H0). cbn in H.
    destruct l; cbn => //.
  Qed.

  Lemma declared_constraints_levels_lift s n k cstrs :
    LS.For_all (λ x : LS.elt, (negb ∘ Level.is_var) x) s ->
    declared_constraints_levels
      (LevelSet.union (levels_of_list (unfold n (λ i : nat, Level.Var i))) s) cstrs ->
    declared_constraints_levels
      (LevelSet.union (levels_of_list (unfold n (λ i : nat, Level.Var (k + i)))) s)
      (lift_constraints k cstrs).
  Proof.
    rewrite /declared_constraints_levels.
    intros hs ha [[l d] r] inx.
    eapply In_lift_constraints in inx as [c' [eq incs]].
    specialize (ha _ incs). destruct c' as [[l' d'] r']; cbn in eq; noconf eq.
    destruct ha as [inl' inr'].
    apply LevelSetFact.union_1 in inl'. apply LevelSetFact.union_1 in inr'.
    split.
    - apply LevelSet.union_spec.
      destruct inl'.
      + left. now apply In_lift_level.
      + right. apply not_var_lift => //.
    - apply LevelSet.union_spec.
      destruct inr'.
      + left. now apply In_lift_level.
      + right. apply not_var_lift => //.
  Qed.

  Definition levels_of_cstr (c : UnivConstraintSet.elt) :=
    let '(l, d, r) := c in
    LevelSet.add l (LevelSet.add r LevelSet.empty).

  Definition levels_of_cstrs cstrs :=
    UnivConstraintSet.fold (fun c acc => LevelSet.union (levels_of_cstr c) acc) cstrs.

  Lemma levels_of_cstrs_acc l cstrs acc :
    LevelSet.In l acc \/ LevelSet.In l (levels_of_cstrs cstrs LevelSet.empty) <->
    LevelSet.In l (levels_of_cstrs cstrs acc).
  Proof.
    rewrite /levels_of_cstrs.
    rewrite !UnivConstraintSet.fold_spec.
    induction (UnivConstraintSet.elements cstrs) in acc |- * => /=.
    split. intros []; auto. inversion H. firstorder.
    split.
    intros []. apply IHl0. left. now eapply LevelSetFact.union_3.
    apply IHl0 in H as []. apply IHl0. left.
    eapply LevelSet.union_spec. left.
    eapply LevelSet.union_spec in H. destruct H => //. inversion H.
    apply IHl0. right => //.
    intros. apply IHl0 in H as [].
    eapply LevelSet.union_spec in H. destruct H => //.
    right. apply IHl0. left. apply LevelSet.union_spec. now left.
    now left. right.
    eapply IHl0. now right.
  Qed.

  Lemma levels_of_cstrs_spec l cstrs :
    LevelSet.In l (levels_of_cstrs cstrs LevelSet.empty) <->
    exists d r, UnivConstraintSet.In (l, d, r) cstrs \/ UnivConstraintSet.In (r, d, l) cstrs.
  Proof.
    rewrite -levels_of_cstrs_acc.
    split.
    - intros []. inversion H.
      move: H.
      rewrite /levels_of_cstrs.
      eapply ConstraintSetProp.fold_rec.
      + intros s' em inl. inversion inl.
      + intros x a s' s'' inx ninx na.
        intros.
        destruct x as [[l' d] r].
        eapply LevelSet.union_spec in H0 as [].
        eapply LevelSet.add_spec in H0 as []; subst.
        exists d, r. left. now apply na.
        eapply LevelSet.add_spec in H0 as []; subst.
        exists d, l'. right; now apply na. inversion H0.
        specialize (H H0) as [d' [r' h]].
        exists d', r'. red in na.
        destruct h. destruct (na (l, d', r')).
        firstorder. firstorder.

    - intros [d [r [indr|indr]]].
      rewrite /levels_of_cstrs. right.
      move: indr; eapply ConstraintSetProp.fold_rec.
      intros. now specialize (H _ indr).
      intros x a s' s'' inx inx' add inih ihih'.
      eapply LevelSet.union_spec.
      eapply add in ihih' as []; subst. left.
      eapply LevelSet.add_spec. now left. firstorder.
      right.
      rewrite /levels_of_cstrs.
      move: indr; eapply ConstraintSetProp.fold_rec.
      intros. now specialize (H _ indr).
      intros x a s' s'' inx inx' add inih ihih'.
      eapply LevelSet.union_spec.
      eapply add in ihih' as []; subst. left.
      eapply LevelSet.add_spec. right. eapply LevelSet.add_spec; now left. firstorder.
  Qed.

  Lemma declared_constraints_levels_in levels cstrs :
    LevelSet.Subset (levels_of_cstrs cstrs LevelSet.empty) levels ->
    declared_constraints_levels levels cstrs.
  Proof.
    rewrite /declared_constraints_levels.
    intros sub [[l d] r] inx. red in sub.
    split. apply (sub l). eapply levels_of_cstrs_spec. do 2 eexists; firstorder eauto.
    apply (sub r). eapply levels_of_cstrs_spec. do 2 eexists; firstorder eauto.
  Qed.

  Lemma In_variance_cstrs l d r v i i' :
    UnivConstraintSet.In (l, d, r) (variance_cstrs v i i') ->
      (In l i \/ In l i') /\ (In r i \/ In r i').
  Proof.
    induction v in i, i' |- *; destruct i, i'; intros; try solve [inversion H].
    cbn in H.
    destruct a. apply IHv in H. cbn. firstorder auto.
    eapply UnivConstraintSet.add_spec in H as []. noconf H. cbn; firstorder.
    eapply IHv in H; firstorder.
    eapply UnivConstraintSet.add_spec in H as []. noconf H. cbn; firstorder.
    eapply IHv in H; firstorder.
  Qed.

  Lemma In_lift l n k : In l (map (lift_level k) (unfold n Level.Var)) <->
    In l (unfold n (fun i => Level.Var (k + i))).
  Proof.
    induction n; cbn; auto. firstorder.
    firstorder.
    move: H1; rewrite map_app.
    intros [] % in_app_or.
    apply/in_or_app. firstorder.
    apply/in_or_app. firstorder.
    move: H1; intros [] % in_app_or.
    rewrite map_app. apply/in_or_app. firstorder.
    rewrite map_app. apply/in_or_app. firstorder.
  Qed.
