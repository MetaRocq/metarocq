
  Section Semantics.
    Import Semilattice.
    Section Interpretation.
      Context {A : Type} {s : Semilattice A Z}.
      Context (V : Level.t -> A).

      (* Definition interp_expr '(l, k) := add k (V l). *)

      Definition clause_sem (cl : clause) : Prop :=
        let '(prems, concl) := cl in
        le (interp_expr concl) (interp_prems prems).

      Definition clauses_sem (cls : clauses) : Prop :=
        Clauses.For_all clause_sem cls.
    End Interpretation.


  End Semantics.




  Definition to_val (v : LevelMap.t nat) l :=
    match LevelMap.find l v with
    | Some n => n
    | None => 0%nat
    end.

  Definition to_Z_val (v : Level.t -> nat) := fun l => Z.of_nat (v l).

  (* Interprest in a nat semilattice only *)
  Definition correct_model {SL : Semilattice Z Z} (cls : clauses) (m : model) :=
    enabled_clauses m cls /\ clauses_sem (to_Z_val (to_val (valuation_of_model m))) cls.


  Lemma in_pred_closure_entails {A} {SL : Semilattice A Z} cls cl :
    in_pred_closure cls cl ->
    (forall V, clauses_sem V cls -> clause_sem V cl).
  Proof.
    induction 1.
    - intros V. rewrite /clauses_sem. intros ha.
      apply ha in H.
      move: H; rewrite /clause_sem.
      destruct cl as [prems concl].
      cbn. rewrite interp_add_prems.
      destruct concl as [concl conclk].
      rewrite /add_expr; cbn.
      rewrite -add_distr => le. now apply (le_add (n:=n)) in le.
    - intros V clsm. cbn.
      rewrite interp_prems_singleton.
      cbn. red. rewrite -!add_distr. rewrite -add_join.
      now rewrite join_sub.
  Qed.

  (** Enabled and valid clauses are satisfied by valuation *)
  Lemma valid_clause_model model cl :
    enabled_clause model cl ->
    valid_clause model cl ->
    clause_sem (to_Z_val (to_val (valuation_of_model model))) cl.
  Proof.
    unfold enabled_clause, valid_clause.
    destruct min_premise eqn:hmin => //= => //.
    2:{ intros [k' eq]. congruence. }
    intros [k' eq]. noconf eq.
    destruct cl as [prems [concl k]]. cbn -[le].
    unfold level_value_above.
    destruct level_value eqn:hl => //.
    unfold level_value in hl. destruct LevelMap.find eqn:hfind => //. noconf hl.
    move/Z.leb_le => hrel.
    eapply LevelMap.find_2 in hfind.
    have conclm := valuation_of_model_spec _ _ _ hfind.
    set (v := (model_max _ - _)) in *.
    cbn in conclm.
    eapply LevelMap.find_1 in conclm.
    subst v.
    pose proof (@min_premise_spec model prems) as [premmin [prem [premin premeq]]].
    rewrite hmin in premeq.
    eapply transitivity. 2:{ eapply interp_prems_ge; tea. }
    unfold interp_expr. destruct prem as [prem k'].
    symmetry in premeq.
    move: premeq. unfold min_atom_value.
    unfold level_value. destruct (LevelMap.find prem) eqn:findp => //.
    destruct o => //.
    intros [= <-].
    eapply LevelMap.find_2 in findp.
    have premm := valuation_of_model_spec _ _ _ findp.
    eapply LevelMap.find_1 in premm.
    assert (z1 - k' <= z0 - k). lia.
    have hm : z0 <= model_max model.
    { eapply model_max_spec in hfind; tea. now depelim hfind. }
    have hm' : z1 <= model_max model.
    { eapply model_max_spec in findp; tea. now depelim findp. }
    have hmi : model_min model <= z0.
    { eapply model_min_spec; tea. }
    have hmi' : model_min model <= z1.
    { eapply model_min_spec; tea. }
    assert (0 <= model_max model)%Z by apply model_max_spec2.
    assert (model_min model <= 0)%Z by apply model_min_spec2.
    rewrite /to_Z_val /to_val premm conclm.
    cbn. lia.
  Qed.

  Lemma valid_clauses_model model cls :
    enabled_clauses model cls ->
    is_model cls model ->
    clauses_sem (to_Z_val (to_val (valuation_of_model model))) cls.
  Proof.
    move=> en ism cl hin.
    apply valid_clause_model.
    now apply en.
    now move/Clauses.for_all_spec: ism; apply.
  Qed.

  Definition valid_entailment cls cl := forall V, clauses_sem V cls -> clause_sem V cl.
  Definition invalid_entailment cls cl :=
    forall V, clauses_sem V cls -> clause_sem V cl -> False.

  Lemma clauses_sem_entails {cls cl} :
    entails cls cl ->
    valid_entailment cls cl.
  Proof.
    induction 1.
    - intros v clls. red.
      destruct concl0 as [concl k].
      have hge := interp_prems_ge (SL := Zsemilattice) v prems _ H.
      cbn in *. by lia.
    - move=> V Hcls.
      move: {IHentails} (IHentails _ Hcls).
      unfold clause_sem. unfold ge => hyp.
      etransitivity; tea. rewrite interp_prems_add.
      rewrite interp_prems_add in hyp.
      eapply in_pred_closure_entails in H; tea.
      move: H; rewrite /clause_sem. unfold ge.
      have ssub := clauses_sem_subset (SL := Zsemilattice) H1 V.
      cbn in *. lia.
  Qed.

  Lemma clauses_sem_entails_all {cls prems concl} :
    cls ⊢a prems → concl ->
    (forall V, clauses_sem V cls -> interp_prems V concl ≤ interp_prems V prems).
  Proof.
    intros ha V hcls.
    red in ha.
    move: ha.
    revert concl.
    refine (@interp_prems_elim _ _ (fun concl z => _ -> z ≤ interp_prems V prems) V _ _ _).
    - move=> le //=. move/(_ le).
      intros h; forward h by now apply LevelExprSet.singleton_spec.
      now have ent := (clauses_sem_entails h _ hcls).
    - intros le u k ih hnin.
      intros hf.
      forward ih. intros x hin; apply (hf x).
      rewrite LevelExprSet.add_spec; now right.
      specialize (hf le).
      forward hf by now apply LevelExprSet.add_spec; left.
      cbn in hf.
      have ent := (clauses_sem_entails hf _ hcls). cbn in ent.
      cbn in *. lia.
  Qed.

