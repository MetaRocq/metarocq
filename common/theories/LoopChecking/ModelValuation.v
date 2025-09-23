
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

