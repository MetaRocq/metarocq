
(** To ensure validity in Z, one must remove "latent" loops from the clauses.
  As we start validity checking from a set of satisfiable clauses, we know
  that there exists an equivalent set of clauses (for Z valuations) with
  no latent loop.
  It is basically computed by the inference algorithm.

  E.g. if we encountered a clause l ∨ x + 1 -> l+1 during inference and found
  a total model m of this clause, then necessarily the model also validates
  x + 1 -> l + 1 as:

    min_premise m (l ∨ x + 1) = (min m[l] m[x]-1)+1 <= m[l] <-> m[x] <= m[l]

  So, instead of checking d


*)

Class In T E := in_pred : E -> T -> Prop.
Instance Ines : In LevelExprSet.t LevelExpr.t := LevelExprSet.In.
Instance Inprems : In NES.t LevelExpr.t := fun x s => LevelExprSet.In x s.

Notation " x ∈ S " := (in_pred x S) (at level 20).

Equations remove_prem_opt (le : LevelExpr.t) (e : NES.t) : option NES.t :=
  remove_prem_opt le e with inspect (LevelExprSet.is_empty (LevelExprSet.remove le e)) :=
    | exist true _ => None
    | exist false he => Some {| t_set := LevelExprSet.remove le e; t_ne := he |}.

Lemma remove_prem_opt_Some le e e' le' :
  remove_prem_opt le e = Some e' ->
  LevelExprSet.In le' e' <->
  LevelExprSet.In le' e /\ le <> le'.
Proof.
  funelim (remove_prem_opt le e) => //.
  intros [= <-]; cbn.
  rewrite LevelExprSet.remove_spec /LevelExprSet.E.eq.
  intuition auto.
Qed.

Lemma remove_prem_opt_Some_eq le e e' :
  le ∈ e ->
  remove_prem_opt le e = Some e' ->
  e = union (singleton le) e' /\ ~ le ∈ e'.
Proof.
  intros hin.
  move/remove_prem_opt_Some => hl.
  split.
  - apply equal_exprsets => lk.
    rewrite LevelExprSet.union_spec LevelExprSet.singleton_spec.
    rewrite hl.
    destruct (Classes.eq_dec lk le).
    * subst. split => // _. now left.
    * split => //. intros hin'. now right.
      intros []. congruence. apply H.
  - intros hin'. specialize (hl le).
    apply hl in hin'. destruct hin'. congruence.
Qed.

Lemma remove_prem_opt_None le e :
  remove_prem_opt le e = None ->
  LevelExprSet.In le e <-> e = singleton le.
Proof.
  funelim (remove_prem_opt le e) => //.
  intros _. clear H. move: e0.
  rewrite LevelExprSet.is_empty_spec.
  intros he.
  split. intros.
  - red in he.
    apply equal_exprsets => l.
    rewrite LevelExprSet.singleton_spec /LevelExprSet.E.eq.
    split. intros hin.
    setoid_rewrite LevelExprSet.remove_spec in he.
    destruct (Classes.eq_dec l le0) => //.
    elim (he l). split => //.
    now intros ->.
  - intros ->. now eapply LevelExprSet.singleton_spec.
Qed.

Definition union_opt (e : NES.t) (e' : option NES.t) : NES.t :=
  match e' with
  | Some e' => union e e'
  | None => e
  end.

Lemma union_opt_union e e' e'' : union (union_opt e e') e'' = union e (union_opt e'' e').
Proof.
  destruct e'; cbn.
  now rewrite union_assoc (@union_comm t0).
  reflexivity.
Qed.

Lemma union_remove le prems :
  le ∈ prems ->
  union_opt (singleton le) (remove_prem_opt le prems) = prems.
Proof.
  intros hin.
  destruct (remove_prem_opt le prems) eqn:hr.
  - apply equal_exprsets => lk.
    cbn. rsets; rewrite /LevelExprSet.E.eq.
    eapply remove_prem_opt_Some in hr. erewrite hr.
    firstorder auto. subst. apply hin.
    destruct (Classes.eq_dec lk le). now left.
    right. firstorder.
  - apply remove_prem_opt_None in hr.
    apply hr in hin. subst prems. now cbn.
Qed.

Lemma entails_weak_union_opt cls prems prems' concl :
  entails cls (prems, concl) ->
  entails cls (union_opt prems prems', concl).
Proof.
  destruct prems'; cbn => //.
  now intros ent; rewrite union_comm; eapply entails_weak_union.
Qed.

Inductive max_chain cls : Clause.t -> Prop :=
| incl cl : entails cls cl -> max_chain cls cl
| chain {prems concl k k'} {prems' : NES.t} {concl'} :
  max_chain cls (prems, (concl, k)) ->
  max_chain cls (prems', concl') ->
  (concl, k') ∈ prems' ->
  max_chain cls (union_opt (add_prems (k' - k) prems) (remove_prem_opt (concl, k') prems'), concl').

Lemma max_chain_entails cls cl :
  max_chain cls cl <-> entails cls cl.
Proof.
  split.
  + induction 1.
    - exact H.
    - eapply (entails_cumul_one (prems' := singleton (concl0, k'))); revgoals.
      { rewrite union_opt_union union_remove //. now eapply entails_weak_union. }
      eapply (entails_shift (k' - k)) in IHmax_chain1.
      cbn in IHmax_chain1.
      have heq: k' - k + k = k' by lia.
      rewrite heq in IHmax_chain1.
      eapply entails_all_singleton.
      now eapply entails_weak_union_opt.
  + intros ent; now apply incl.
Qed.

Definition thin_clause m cl :=
  let prems := premise cl in
  let filter '(l, k) := if entails_dec m (prems, (l, k + 1)) then false else true in
  LevelExprSet.filter filter (premise cl).


Lemma thin_clause_spec m cl :
  let prems := thin_clause m cl in
  if LevelExprSet.is_empty prems then
    entails_all (clauses m) (premise cl) (succ (premise cl))
  else
    exists premsnl premsl,
    [/\ premise cl = (union_opt premsnl premsl)%nes,
      prems = premsnl,
      (forall l k, (l, k) ∈ premsnl -> ~ entails (clauses m) (premise cl, (l, k+1))) &
      on_Some_or_None (fun premsl => entails_all (clauses m) (premise cl) (succ premsl)) premsl].
Proof.
  intros prems.
  destruct (LevelExprSet.is_empty prems) eqn:ise.
  - have ha : forall l k, LevelExprSet.In (l, k) (premise cl) -> entails (clauses m) (premise cl, (l, k + 1)).
    intros l k hin.
    eapply (empty_filter _ _ ise) in hin.
    destruct entails_dec => //.
    move=> -[] l k /In_add_prems -[[l' k']] [] hin ->.
    eapply ha in hin. rewrite /succ_expr //=. now rewrite Z.add_comm.
  - subst prems; unfold thin_clause in *.
    set (fn := fun '(l, k) => _) in *.
    set (fil := LevelExprSet.filter _ _) in *.
    have hs := LevelExprSet.partition_spec2 (f:=fn) (premise cl). forward hs. tc.
    have hs' := LevelExprSet.partition_spec1 (f:=fn) (premise cl). forward hs'. tc.
    set (part := LevelExprSet.partition _ _) in *.
    exists {| t_set := fil; t_ne := ise |}.
    destruct (LevelExprSet.is_empty part.2) eqn:ise2.
    * exists None.
      cbn. split => //.
      { apply equal_exprsets; cbn.
        move=> lk. rewrite LevelExprSet.filter_spec.
        intuition auto.
        rewrite hs in ise2.
        have he := empty_filter _ _ ise2.
        specialize (he lk H).
        destruct (fn lk) => //. }
      { move=> l k /LevelExprSet.filter_spec -[] hin hf hent.
        unfold fn in hf. destruct entails_dec => //. }
    * exists (Some {| t_set := part.2; t_ne := ise2 |}).
      cbn. split => //.
      apply equal_exprsets => l. cbn.
      rewrite LevelExprSet.union_spec.
      rewrite -[fil]hs'.
      now rewrite -partition_in.
      { move=> l k /LevelExprSet.filter_spec -[] hin' hf hent.
        unfold fn in hf. destruct entails_dec => //. }
      { move=> l /In_add_prems -[[le' le'k]] [].
        cbn. rewrite hs => /LevelExprSet.filter_spec [] hin heq.
        intros ->. unfold fn in heq. destruct entails_dec => //.
        cbn in heq. now rewrite Z.add_comm. }
Qed.

Equations thin_clause_opt (m : t) (cl : clause) : option clause :=
  | m, cl with inspect (LevelExprSet.is_empty (thin_clause m cl)) :=
    | exist true _ => None
    | exist false ne => Some ({| t_set := thin_clause m cl; t_ne := ne |}, concl cl).


Lemma thin_clause_opt_spec m cl :
  match thin_clause_opt m cl with
  | None => False
  | Some cl' =>
    exists premsnl premsl,
    [/\ premise cl = union_opt premsnl premsl,
      cl' = (premsnl, concl cl),
      (forall l k, (l, k) ∈ premsnl -> ~ entails (clauses m) (premise cl, (l, k+1))) &
      on_Some_or_None (fun premsl => entails_all (clauses m) (premise cl) (succ premsl)) premsl]
  end.
Proof.
  funelim (thin_clause_opt m cl); clear H.
  - assert (h := thin_clause_spec m cl).
    cbn in h.
    rewrite e in h.
    now eapply model_entails_loop in h.
  - assert (h := thin_clause_spec m cl).
    cbn in h.
    clear Heqcall.
    rewrite ne in h.
    destruct h as [premsnl [premsl []]].
    exists premsnl, premsl; split => //.
    f_equal. apply equal_exprsets; cbn. now rewrite H0.
Qed.

Lemma interp_nes_thin_clause (v : Level.t -> Z) {m cl ne} {premsnl : NES.t} :
  thin_clause m cl = premsnl ->
  interp_nes v ({| t_set := thin_clause m cl; t_ne := ne |}) =
  interp_nes v premsnl.
Proof.
  intros eq.
  destruct premsnl.
  destruct cl as [prems concl]; cbn in eq.
  subst t_set0. f_equal.
  apply equal_exprsets. cbn. reflexivity.
Qed.

Lemma interp_nes_union_opt v e e' :
  interp_nes v (union_opt e e') =
  match e' with
  | Some e' => Z.max (interp_nes v e) (interp_nes v e')
  | None => interp_nes v e
  end.
Proof.
  destruct e' => //=.
  now rewrite interp_nes_union; cbn.
Qed.

Lemma thin_clause_opt_valid m cl :
  match thin_clause_opt m cl with
  | None => False
  | Some cl' => valid_clause_Z (clauses m) cl <-> valid_clause_Z (clauses m) cl'
  end.
Proof.
  (* intros hent. *)
  funelim (thin_clause_opt m cl).
  - clear H Heqcall.
    have hs := thin_clause_spec m cl.
    cbn in hs. rewrite e in hs.
    now eapply model_entails_loop in hs.
  - clear H Heqcall.
    have hs := thin_clause_spec m cl.
    cbn in hs. rewrite ne in hs.
    destruct cl as [prems [concl k]].
    rewrite /valid_clause_Z. cbn.
    cbn in hs. destruct hs as [premsl [premsnl [heq heq' hent' hentl]]].
    split.
    * move=> hv v vpos csem.
      have hi := interp_nes_thin_clause v (ne := ne) heq'.
      move: hv => /(_ v vpos csem).
      rewrite hi. subst prems.
      rewrite interp_nes_union_opt.
      destruct premsnl => //.
      destruct heq'.
      move/to_entails_all: hentl.
      move/entails_L_entails_ℋ_equiv/entails_L_rels_entails_L_clauses/completeness_all.
      move/(_ Z _ v).
      rewrite -interp_rels_clauses_sem.
      move/(_ csem).
      rewrite -interp_rels_clauses_sem.
      move/clauses_sem_clauses_of_le.
      rewrite interp_add_prems interp_nes_union.
      cbn in hent' |- *. lia.
    * move=> hv v vpos csem.
      have hi := interp_nes_thin_clause v (ne := ne) heq'.
      move: hv => /(_ v vpos csem).
      rewrite hi.
      subst prems.
      rewrite interp_nes_union_opt.
      destruct premsnl => //.
      destruct heq'.
      move/to_entails_all: hentl.
      move/entails_L_entails_ℋ_equiv/entails_L_rels_entails_L_clauses/completeness_all.
      move/(_ Z _ v).
      rewrite -interp_rels_clauses_sem.
      move/(_ csem).
      rewrite -interp_rels_clauses_sem.
      move/clauses_sem_clauses_of_le.
      rewrite interp_add_prems interp_nes_union.
      cbn in hent' |- *. lia.
Qed.

(*
Lemma thin_clause_opt_entails m cl :
  match thin_clause_opt m cl with
  | None => False
  | Some cl' => entails (clauses m) cl' -> entails (clauses m) cl
  end.
Proof. Admitted. *)

Definition thin_clauses m :=
  Clauses.fold (fun cl acc =>
    match thin_clause_opt m cl with
    | Some cl' => Clauses.add cl' acc
    | None => acc (* Impossible for consistent models *)
    end) (clauses m) Clauses.empty.

Lemma thin_clauses_spec m :
  forall cl, Clauses.In cl (clauses m) ->
    exists cl', thin_clause_opt m cl = Some cl' /\ Clauses.In cl' (thin_clauses m).
Proof. Admitted.

Lemma thin_clauses_spec_inv m :
  forall cl, Clauses.In cl (thin_clauses m) ->
    exists clo, thin_clause_opt m clo = Some cl /\ Clauses.In clo (clauses m).
Proof. Admitted.

(** The thinned clauses are stronger than the original clauses *)
Lemma thin_clauses_entails m : thin_clauses m ⊢ℋ clauses m.
Proof.
  intros cl hin.
  destruct (thin_clauses_spec m cl hin) as [cl' [heq hin']].
  have hs := thin_clause_opt_spec m cl.
  rewrite heq in hs. destruct hs as [premsnl [premsl [eq eq' ent ent']]].
  destruct cl as [prems concl]. cbn in eq, eq', ent.
  subst prems cl'.
  now eapply entails_weak_union_opt, entails_in.
Qed.
Lemma thin_clauses_model model m :
  is_model model (thin_clauses m) -> is_model model (clauses m).
Proof.
  move=> ism. eapply is_model_entails_H; tea.
  eapply thin_clauses_entails.
Qed.


Lemma is_total_model_thin m m' :
  is_total_model m' (clauses m) ->
  is_total_model m' (thin_clauses m).
Proof.
  move/is_total_model_altP => ism.
  apply/is_total_model_altP => cl /thin_clauses_spec_inv -[] cl' [] heq /ism.
  have := thin_clause_opt_spec m cl'.
  rewrite heq => -[premsnl] [premsl] [eq eq' ent nent].
  subst cl.
  move=> -[] minp [] value [] => hmin hl hle.
  exists minp, value. cbn. split => //.
  rewrite -hmin eq.
  apply antisymmetry; revgoals.
  { eapply min_premise_subset. destruct premsl; cbn; lesets. }
  destruct premsl as [premsl|]; cbn => //; revgoals. reflexivity.
  rewrite min_premise_union.
  cbn in nent.
  rewrite -to_entails_all in nent.
  eapply entails_all_model_valid in nent. 2:{ apply is_model_valid. eapply is_total_model_altP in ism. apply ism. }
  rewrite eq in nent. cbn in nent.
  rewrite eq min_premise_union in hmin.
  destruct (min_premise m' premsl) as [minl|] eqn:minle, (min_premise m' premsnl) as [minnl|] eqn:minnle; cbn in hmin |- * => //.
  noconf hmin. constructor.
  eapply valid_clauses_of_le in nent. 2:{ rewrite min_premise_union minle minnle //=. }
  2:{ rewrite (min_premise_add_prems minle); trea. } lia.
Qed.


Lemma total_model_thin m : is_total_model (model m) (thin_clauses m).
Proof.
  by eapply is_total_model_thin, total_model.
Qed.

Definition check_clauseZ m cl :=
  check_genb (thin_clauses m) cl.

Lemma clauses_levels_thin m : clauses_levels (thin_clauses m) ⊂_lset clauses_levels (clauses m).
Proof. Admitted.

Lemma check_gen_thin_model_looping m cl v vcls isl :
  check_gen (thin_clauses m) cl = IsLooping v vcls isl -> False.
Proof.
  intros.
  have hm := m.(model_valid).(model_ok).
  have hen := model_enabled m.
  have htot : is_total_model (model m) (clauses m).
  split => //.
  eapply is_total_model_thin in htot.
  eapply (check_valid_looping (cls := thin_clauses m)). apply htot. tea.
  eapply defined_model_of_ext. eapply defined_model_of_subset.
  2:{ eapply defined_model. }
  intros ? ?; eapply clauses_levels_declared.
  instantiate (1 := m). now eapply clauses_levels_thin, vcls.
  reflexivity.
Qed.

Lemma checkb_thin_entails m cl :
  check_genb (thin_clauses m) cl <-> entails (thin_clauses m) cl.
Proof.
  unfold check_genb.
  destruct (check_gen) eqn:ec.
  - now move/check_gen_thin_model_looping: ec.
  - split => //.
    now move/check_invalid_entails: ec.
  - now move/check_gen_entails: ec.
Qed.
