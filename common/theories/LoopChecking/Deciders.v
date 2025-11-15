(* Distributed under the terms of the MIT license. *)
From Ltac2 Require Ltac2.
From Stdlib Require Import ssreflect ssrfun ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils MRClasses SemiLattice.

From MetaRocq.Common Require UnivConstraintType.
From Equations Require Import Equations.

From MetaRocq.Common.LoopChecking Require Import Common Interfaces HornClauses Model Models PartialLoopChecking InitialSemilattice HornSemilatticeEquiv.

Set Equations Transparent.

Module Type LoopCheckingItf (LS : LevelSets).

  (* Type of consistent models of a set of universe constraints *)
  Parameter model : Type.
  Parameter univ : Type.

  Notation constraint := (univ * UnivConstraintType.ConstraintType.t * univ).

  (* Returns the valuation of the model: a minimal assignement from levels to constraints
    that make the enforced clauses valid. *)
  Parameter valuation : model -> LS.LevelMap.t nat.

  Parameter init_model : model.

  (* Returns None if already declared *)
  Parameter declare_level : LS.Level.t -> model -> option model.

  (* If the constraints mention undeclared universes, returns None,
     otherwise, returns either a model or a looping universe, i.e. such that u >= u + 1 is implied
     by the constraint *)
  Parameter enforce : constraint -> model -> option (model + univ).

  (* Definition valid_constraint m c :=
    let v := valuation m in
    clause_sem v c.

  Parameter enforce_spec : forall c m, enforce c m = Some (inl m') ->
    valid_constraint m c. *)

  (* Returns true is the clause is valid in the model and all its possible consistent extensions.
     Returns false if the constraint results in an inconsistent set of constraints or it simply
     is not valid. *)
  Parameter check : model -> constraint -> bool.

End LoopCheckingItf.

Module Deciders (LS : LevelSets).

Module Import I := LoopCheckingImpl LS.
Import LS.
Local Open Scope Z_scope.

Definition init_model cls := max_clause_premises cls.

Lemma init_model_levels cls k :
  LevelMap.In k (init_model cls) <-> LevelSet.In k (clauses_levels cls).
Proof.
  split.
  - now move=> [] k' /max_clause_premises_spec.
  - move/max_clause_premises_spec_inv. now eexists.
Qed.

Definition init_w (levels : LevelSet.t) : LevelSet.t := LevelSet.empty.
Definition infer_result V cls := result V LevelSet.empty cls (init_model cls).

Equations? infer (cls : clauses) : infer_result (clauses_levels cls) cls :=
  infer cls := loop (clauses_levels cls) LevelSet.empty cls (init_model cls) (init_model cls) (And3 _ _ _).
Proof.
  - now rewrite -init_model_levels.
  - apply is_update_of_empty.
Qed.

Local Open Scope string_scope2.

Definition print_level_Z_map (m : LevelMap.t (option Z)) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => Level.to_string l ^ " -> " ^ string_of_option string_of_Z w) nl list.

Definition print_result {V cls} (m : infer_result V cls) :=
  match m return string with
  | Loop _ _ _ => "looping on "
  | Model w m _ => "satisfiable with model: " ^ print_level_Z_map m.(model_model) ^ nl ^ " W = " ^
    print_lset w
    ^ nl ^ "valuation: " ^ print_level_nat_map (valuation_of_model m.(model_model))
  end.

Definition valuation_of_result {V cls} (m : infer_result V cls) :=
  match m with
  | Loop _ _ _  => "looping"
  | Model w m _ => print_level_nat_map (valuation_of_model m.(model_model))
  end.

Definition to_string_expr (e : LevelExpr.t) : string :=
  let '(l, n) := e in Level.to_string l ^ (if n is Z0 then "" else "+" ^ string_of_Z n).

Definition print_premise (l : premises) : string :=
  let (e, exprs) := to_nonempty_list l in
  to_string_expr e ^
  match exprs with
  | [] => ""
  | _ => ", " ^ print_list to_string_expr ", " exprs
  end.

Definition print_clauses (cls : clauses) :=
  let list := Clauses.elements cls in
  print_list (fun '(l, r) =>
    print_premise l ^ " → " ^ to_string_expr r) nl list.

Definition valuation := LevelMap.t nat.

Equations? infer_model (cls : clauses) : model + premises :=
infer_model cls with loop (clauses_levels cls) LevelSet.empty cls (init_model cls) (init_model cls) _ :=
  | Loop v _ _ => inr v
  | Model w vm heq => inl vm.(model_model).
Proof.
  split.
  - reflexivity.
  - apply infer_obligation_2.
  - apply is_update_of_empty.
Qed.

Definition correct_model (cls : clauses) (m : model) :=
  enabled_clauses m cls /\ is_model m cls.

(* Entailment *)

Import I.Model.Model.Clauses.ISL.

Lemma enabled_clauses_of_le m v u :
  (exists z, min_premise m u = Some z) ->
  enabled_clauses m (v ⋞ u)%cls.
Proof.
  intros hmin cl hcl.
  eapply clauses_of_le_spec in hcl.
  destruct hcl as [lk [hin eq]]. subst cl.
  hnf. now cbn.
Qed.

Lemma enabled_clauses_le {m} {v u : NES.t} : defined_model_of (levels u) m -> enabled_clauses m (v ⋞ u)%cls.
Proof.
  intros def. eapply enabled_clauses_of_le.
  move: u def; apply: NES.elim.
  - intros le. rewrite levels_singleton min_premise_singleton.
    intros h. specialize (h le.1). forward h by now rsets.
    destruct h as [k hm]; rewrite /min_atom_value.
    destruct le; cbn. rewrite (level_value_MapsTo hm). now eexists.
  - intros le r hd hnin hdef.
    rewrite levels_add in hdef.
    rewrite min_premise_add.
    eapply defined_model_of_union_inv in hdef as [].
    forward hd by auto.
    destruct hd as [z ->].
    specialize (H le.1); forward H by now rsets.
    destruct H as [k hm]; rewrite /min_atom_value.
    destruct le; cbn. rewrite (level_value_MapsTo hm). now eexists.
Qed.

Definition infer_correctness cls :=
  match infer_model cls with
  | inl m => correct_model cls m
  | inr u => ~ exists m, defined_model_of (levels u) m /\ is_model m cls
  end.

Definition valid_clauses m cls := Clauses.For_all (valid_clause m) cls.
Infix "⊨" := valid_clauses (at level 90).

Lemma is_model_valid {cls m} : is_model m cls <-> m ⊨ cls.
Proof.
  rewrite /is_model.
  rewrite [is_true _]Clauses.for_all_spec. reflexivity.
Qed.

Lemma entails_all_model_valid {cls cls' : clauses} {m : model} :
  m ⊨ cls -> cls ⊢ℋ cls' -> m ⊨ cls'.
Proof.
  intros ism ent cl incl.
  move/ent: incl => entcl.
  eapply entails_model_valid; tea.
  apply Clauses.for_all_spec. tc. apply ism.
Qed.

Lemma valid_enabled_clause_spec model cl :
  enabled_clause model cl ->
  valid_clause model cl ->
  exists hmin, min_premise model (premise cl) = Some hmin /\ (Some (hmin + (concl cl).2) ≤ level_value model (concl cl).1)%opt.
Proof.
  intros [hmin eq].
  destruct cl as [prems [concl k]]. move/valid_clause_elim/(_ hmin eq) => hle.
  exists hmin. split => //.
Qed.

Lemma valid_enabled_clauses_spec {model cls} :
  enabled_clauses model cls ->
  valid_clauses model cls ->
  forall cl, Clauses.In cl cls ->
  exists hmin, min_premise model (premise cl) = Some hmin /\ (Some (hmin + (concl cl).2) ≤ level_value model (concl cl).1)%opt.
Proof.
  intros en valid cl hin.
  specialize (en cl hin).
  specialize (valid cl hin).
  now apply valid_enabled_clause_spec.
Qed.


Lemma min_opt_None_right x z : min_opt x None = Some z -> False.
Proof.
  destruct x => //=.
Qed.

Lemma min_opt_None_left x z : min_opt None x = Some z -> False.
Proof.
  destruct x => //=.
Qed.

Lemma loop_invalid {m u} : enabled_clauses m (succ u ⋞ u)%cls -> m ⊨ succ u ⋞ u -> False.
Proof.
  intros en valid.
  have vm := valid_enabled_clauses_spec en valid.
  setoid_rewrite clauses_of_le_spec in vm.
  clear en valid.
  move: u vm. apply: NES.elim.
  - intros le hcl.
    move: (hcl (singleton le, succ_expr le)) => /fwd.
    { exists (succ_expr le). split => //.
      apply In_add_prems. exists le; split => //. now apply LevelExprSet.singleton_spec. }
    move=> [z [hmin hleq]]. cbn -[Z.add] in hleq.
    rewrite min_premise_singleton /min_atom_value in hmin.
    destruct le as [l k]. cbn -[Z.add] in *.
    destruct (level_value m l) eqn:hl => //. noconf hmin.
    apply opt_le_some_inv in hleq. lia.
  - intros le x en hnin h.
    apply en. intros cl [lk [hin eq]]. subst cl.
    eapply In_add_prems in hin as [? []]. subst lk. rewrite /concl. cbn.
    move: (h (add le x, succ_expr x0)) => /fwd.
    { exists (succ_expr x0). split => //.
      apply In_add_prems. exists x0. split => //.
      apply LevelExprSet.add_spec. now right. }
    intros [hmin [eqmin lv]].
    cbn in lv. cbn in eqmin.
    rewrite min_premise_add in eqmin.
    move: (h (add le x, succ_expr le)) => /fwd.
    { exists (succ_expr le). split => //.
      apply In_add_prems. exists le. split => //.
      apply LevelExprSet.add_spec; now left. }
    intros [hmin' [eqmin' lv']]. cbn in eqmin', lv'.
    rewrite min_premise_add in eqmin'.
    destruct (min_premise m x) eqn:mx.
    * exists z. split => //.
      destruct (min_atom_value m le) eqn:mina; cbn in * => //.
      noconf eqmin; noconf eqmin'.
      destruct le as [le lek]. destruct x0 as [x0 x0k]; cbn -[Z.add] in *.
      destruct (level_value m le) => //.
      Opaque Z.add. depelim lv'. depelim lv. rewrite H1. constructor.
      noconf mina. lia.
    * now apply min_opt_None_right in eqmin'.
Qed.

Import Semilattice.
Lemma infer_correct cls : infer_correctness cls.
Proof.
  unfold infer_correctness.
  destruct infer_model as [m|] eqn:hi.
  - (* Correct *) move: hi.
    funelim (infer_model cls) => //.
    intros [= <-].
    set (obl := infer_model_obligation_1 cls). clearbody obl.
    clear Heq Heqcall.
    have mincl := model_incl vm.
    destruct vm as [model ofV isupd clsconcl ism]; cbn in *.
    set (V := clauses_levels cls) in *.
    unfold correct_model.
    have encl : enabled_clauses model cls.
    { eapply enabled_clauses_ext. apply is_update_of_ext in isupd. exact isupd.
      apply init_model_enabled. }
    split => //.
  - intros [v [en clssem]].
    move: hi.
    funelim (infer_model cls) => //. intros [=]. subst t0.
    red in islooping. clear Heq Heqcall.
    apply to_entails_all in islooping.
    apply is_model_valid in clssem.
    have hv := entails_all_model_valid clssem islooping.
    eapply loop_invalid in hv; tea.
    now apply enabled_clauses_le.
Qed.

Definition min_clause_q cl :=
  Z.min (premise_min (premise cl)) (concl cl).2.

(* For checking we start from an a prems -> concl we
*)

Program Definition loop_check cls (cl : clause) : result (premises_model (clauses_levels cls) None cl).1 LevelSet.empty cls (premises_model (clauses_levels cls) None cl).2 :=
  let V := clauses_levels cls in
  let i := None in
  loop (premises_model V i cl).1 LevelSet.empty cls (premises_model V i cl).2 (premises_model V i cl).2 _.
Next Obligation.
  split => //.
  - lsets.
  - intros l. rewrite LevelSet.union_spec.
    rewrite -/(LevelMap.In l (premises_model (clauses_levels cls) None cl).2).
    rewrite in_premises_model. intuition auto.
  - apply is_update_of_empty.
Qed.

Variant check_result {cls} :=
  | IsLooping (v : premises) (hincl : NES.levels v ⊂_lset clauses_levels cls) (islooping : loop_on_univ cls v)
  | Invalid (m : model)
  | Valid.
Arguments check_result : clear implicits.

Lemma valid_model_find {V W cl cls} :
  forall v : valid_model (clause_levels cl ∪ V) W (premises_model_map (zero_model None (clause_levels cl ∪ V)) (Clauses.singleton cl)) cls,
  ~ LevelMap.find (concl cl).1 (model_model v) = None.
Proof.
  intros v hfind.
  destruct cl as [prems [concl k]]; cbn in *.
  have vmupd := model_of_V v.
  set (pm := premises_model_map _ _) in *.
  move/LevelMapFact.F.not_find_in_iff: hfind; apply.
  apply vmupd. rewrite LevelSet.union_spec; left.
  rewrite clause_levels_spec. now right.
Qed.

Equations check_entails (cls : clauses) (cl : clause) : check_result cls :=
check_entails cls cl with inspect (loop_check cls cl) :=
  { | exist (Loop v _ isl) he => IsLooping v _ isl
    | exist (Model W v _) he with inspect (LevelMap.find (concl cl).1 v.(model_model)) := {
      | exist (Some val) he' with check_atom_value (Some (concl cl).2) val :=
        { | true => Valid
          | false => Invalid v.(model_model) }
      | exist None he' with valid_model_find v he' := {}
    }
  }.

(* If a clause checks, then it is entailed (and will be valid in any extension of the model) *)
Theorem check_entails_entails {cls cl} :
  check_entails cls cl = Valid -> entails cls cl.
Proof.
  destruct cl as [prems [concl k]].
  funelim (check_entails cls _) => // _.
  set (V := (clause_levels _ ∪ clauses_levels cls)%levels) in *.
  clear Heqcall H H0. cbn [concl fst snd] in *.
  move/check_atom_value_spec: Heq; intros h; depelim h. rename H into hgt.
  have vmupd := model_updates v.
  have vmok := model_ok v.
  set (pm := premises_model_map _ _) in *.
  have nepm : defined_map pm.
  { apply premises_model_map_defined.
    set (cl := (prems, _)) in *.
    move/(_ cl). rewrite Clauses.singleton_spec. congruence. }
  have nev : defined_map (model_model v).
    by apply (is_update_of_defined_map nepm vmupd).
  move/(is_update_of_entails (hne := nepm) (hne' := nev)): vmupd => ent.
  set (cl := (prems, (concl0, k))) in V.
  have of_lset := of_level_map_premises_model_map cls cl V nepm.
  have tr := entails_all_trans of_lset ent.
  eapply (entails_all_satisfies (l := concl0) (k := k)) in tr.
  2:{ red. rewrite /level_value he'. now constructor. }
  exact tr.
Qed.


Lemma check_entails_entails_looping {cls cl v vcls isl} :
  check_entails cls cl = IsLooping v vcls isl -> cls ⊢a v → succ_prems v.
Proof.
  funelim (check_entails cls cl) => //.
Qed.

Lemma check_looping {cls cl v vcls isl} :
  check_entails cls cl = IsLooping v vcls isl ->
  ~ (exists m, defined_model_of (levels v) m /\ is_model m cls).
Proof.
  move/check_entails_entails_looping.
  intros loop [m' [en clssem]].
  apply to_entails_all in loop.
  apply is_model_valid in clssem.
  have hv := entails_all_model_valid clssem loop.
  eapply loop_invalid in hv; tea.
  now apply enabled_clauses_le.
Qed.

Lemma check_valid_looping {cls cl m v vcls isl} :
  is_model m cls ->
  check_entails cls cl = IsLooping v vcls isl ->
  defined_model_of (levels v) m -> False.
Proof.
  move=> ism.
  move/check_looping => ex hdef. apply ex.
  exists m. split => //.
Qed.

Definition consistent cls :=
  exists val : Level.t -> Z, positive_valuation val /\ clauses_sem val cls.

Lemma consistent_no_loop cls v :
  consistent cls ->
  cls ⊢a v → succ v -> False.
Proof.
  move=> [val [vpos vsem]].
  move/to_entails_all/entails_L_entails_ℋ_equiv.
  move/entails_L_rels_entails_L_clauses/completeness_all.
  move/(_ Z _ val).
  rewrite -!interp_rels_clauses_sem => /fwd //.
  move/clauses_sem_leq.
  rewrite interp_add_prems. cbn. lia.
Qed.

Lemma model_entails_succ cls m v :
  is_model m cls ->
  enabled_clauses m cls ->
  cls ⊢a v → succ v -> False.
Proof.
  move=> mok en.
  apply consistent_no_loop.
  exists (Z_valuation_of_model m).
  split. apply valuation_of_model_pos.
  eapply valid_clauses_model => //.
Qed.

Instance Z_le_partialorder : PreOrder Z.le.
Proof.
  split; tc.
Qed.

Instance opt_le_preorder {A} (R : relation A) {preo : PreOrder R}: PreOrder (opt_le R).
Proof.
  split; tc.
Qed.

Instance opt_le_partialorder : PartialOrder Logic.eq (opt_le Z.le).
Proof.
  red; split; cbn; unfold flip.
  * intros ->. split; reflexivity.
  * move=> [] le le'. destruct x, x0; cbn in *; depelim le; depelim le'; lia_f_equal.
Qed.

Instance model_rel_preorder {R : relation (option Z)} : PreOrder R -> PreOrder (model_rel R).
Proof.
  intros []. split; tc.
Qed.

Instance model_rel_partialorder {R : relation (option Z)} {preo : PreOrder R} :
  PartialOrder Logic.eq R -> PartialOrder LevelMap.Equal (model_rel R).
Proof.
  intros partialo.
  intros m m'.
  split.
  - intros hm. cbn. split.
    * hnf. setoid_rewrite hm. eexists; split; trea.
    * hnf. setoid_rewrite hm. eexists; split; trea.
  - cbn; unfold flip => -[] le le'.
    rewrite LevelMapFact.F.Equal_mapsto_iff => k v.
    red in le, le'. split.
    * move=> hm. move: (le _ _ hm) => [k' [hm' lek']].
      move: (le' _ _ hm') => [k1 [hk1 lek1]].
      eapply LevelMapFact.F.MapsTo_fun in hm; tea. subst k1.
      have eq : v = k'. now apply antisymmetry. now subst k'.
    * move=> hm. move: (le' _ _ hm) => [k' [hm' lek']].
      move: (le _ _ hm') => [k1 [hk1 lek1]].
      eapply LevelMapFact.F.MapsTo_fun in hm; tea. subst k1.
      have eq : v = k'. now apply antisymmetry. now subst k'.
Qed.

Definition updates cls m m' := exists W, is_update_of cls W m m'.

Lemma updates_ext {cls m m'} : updates cls m m' -> m ⩽ m'.
Proof.
  now move=> [W] /is_update_of_ext.
Qed.

Instance updates_proper : Proper (Clauses.Equal ==> LevelMap.Equal ==> LevelMap.Equal ==> iff) updates.
Proof.
  intros ? ? cls ? ? hm ?? hm'. unfold updates.
  setoid_rewrite cls. setoid_rewrite hm. now setoid_rewrite hm'.
Qed.

Definition minimal_above_updates cls minit m :=
  forall m', updates cls minit m' ->
    is_model m' cls ->
    updates cls m m'.

Lemma not_value_above m l k : ~~ level_value_above m l k <-> opt_le Z.lt (level_value m l) (Some k).
Proof.
  split.
  now move/negbTE/level_value_not_above_spec.
  intros h; depelim h; rewrite /level_value_above.
  - rewrite H0. apply/negP => /Z.leb_le. lia.
  - now rewrite H.
Qed.

Lemma levelset_is_empty_empty : LevelSet.is_empty LevelSet.empty.
Proof.
  eapply LevelSet.is_empty_spec. lsets.
Qed.

Lemma levelset_is_empty_singleton x : LevelSet.is_empty (LevelSet.singleton x) = false.
Proof.
  rewrite levelset_not_Empty_is_empty. intros he; specialize (he x). lsets.
Qed.


Definition check_init_model cls cl :=
  (premises_model (clauses_levels cls) None cl).2.

Definition minimal_above cls minit m :=
  forall m', minit ⩽ m' -> is_model m' cls -> m ⩽ m'.

Lemma minimal_above_refl cls m : minimal_above cls m m.
Proof.
  red.
  now intros m'.
Qed.

Lemma minimal_above_trans cls m m' m'' : minimal_above cls m m' -> minimal_above cls m' m'' ->
  minimal_above cls m m''.
Proof.
  red. intros min min' m0 ext hin.
  red in min. specialize (min _ ext hin).
  exact (min' m0 min hin).
Qed.

Lemma strictly_updates_minimal_above cls W m m' :
  strictly_updates cls W m m' ->
  minimal_above cls m m'.
Proof.
  move: W m m'.
  apply: (strictly_updates_elim cls).
  - intros l l' h ? ? x ? ? y. subst x0 x1.
    unfold minimal_above. reflexivity.
  - destruct cl as [prems [concl k]].
    move=> m' hin [minp [hmin habove]].
    rewrite /minimal_above. intros h. setoid_rewrite h.
    move=> mf ext ism.
    eapply is_model_valid in ism.
    specialize (ism _ hin). cbn in ism.
    move/valid_clause_elim: ism.
    intros hz.
    have := @min_premise_pres m mf prems ext.
    rewrite hmin. move/Some_leq => -[minmf] [] /hz /Some_leq [mfconcl] [] vmconcl leq' leq.
    move=> l k'. rsets. destruct H as [[<- <-]|[neq mt]].
    * exists (Some mfconcl). split => //. now eapply level_value_MapsTo'.
      constructor. lia.
    * now apply ext.
  - intros * su ma su' ma'.
    now eapply minimal_above_trans; tea.
Qed.

Lemma is_update_of_minimal_above {cls W m m'} :
  is_update_of cls W m m' ->
  minimal_above cls m m'.
Proof.
  move/is_update_of_case => [[emp eq]|su].
  - rewrite /minimal_above => m0. now rewrite eq.
  - now eapply strictly_updates_minimal_above.
Qed.

Theorem check_invalid {cls cl m} :
  check_entails cls cl = Invalid m ->
  [/\ is_model m cls,
     model_of (clauses_levels cls ∪ clause_levels cl) m,
     minimal_above cls (check_init_model cls cl) m,
     enabled_clause m cl & ~ valid_clause m cl].
Proof.
  funelim (check_entails cls cl) => //.
  clear H H0 he.
  set (V := (clause_levels cl ∪ clauses_levels cls)%levels) in *.
  destruct cl as [prems [concl k]].
  rename val into conclval_v => [=] eq. subst m.
  clear Heqcall prf.
  move: (check_atom_value_spec (Some k) conclval_v). rewrite Heq.
  intros r; depelim r. rename H into nent.
  have vmupd := model_updates v.
  have vmok := model_ok v.
  set (pm := premises_model_map _ _) in *.
  set (cl := (prems, _)) in V.
  have nepm : defined_map pm.
  { apply premises_model_map_defined.
    move/(_ cl). rewrite Clauses.singleton_spec /cl. congruence. }
  have nev : defined_map (model_model v).
    by apply (is_update_of_defined_map nepm vmupd).
  move/(is_update_of_entails (hne := nepm) (hne' := nev)): vmupd => ent.
  have en : enabled_clause (model_model v) cl.
  { apply (@enabled_clause_ext pm).
    exact: is_update_of_ext (model_updates v).
    red; cbn.
    have hcl : Clauses.In cl (Clauses.singleton cl).
    { now eapply Clauses.singleton_spec. }
    have hs:= @premises_model_map_min_premise_inv V _ None _ hcl. firstorder. }
  split => //.
  { have hv := model_of_V v. clear -hv.
    subst V. cbn. now rewrite LevelSetProp.union_sym.
   }
  { eapply (is_update_of_minimal_above (model_updates v)). }
  destruct en as [z minp].
  move/valid_clause_elim/(_ z minp).
  cbn in minp.
  cbn in he'.
  rewrite /level_value he' => h; depelim h. apply nent.
  constructor. cbn -[check_atom_value] in Heq.
  have posz : 0 <= z.
  { have hsu := model_updates v.
    eapply is_update_of_ext in hsu.
    have hs := min_premise_pres prems hsu.
    rewrite minp in hs.
    have hmin := @premises_model_map_min_premise_inv V (Clauses.singleton cl) None cl.
    forward hmin. now apply Clauses.singleton_spec.
    destruct hmin as [minp' [hmineq hpos]].
    rewrite hmineq in hs. depelim hs. lia. }
  lia.
Qed.

Lemma valid_clause_satisfies m prems concl : valid_clause m (prems, concl) <->
  min_premise m prems = None \/
  (exists z, min_premise m prems = Some z /\ satisfiable_atom m (add_expr z concl)).
Proof.
  destruct concl as [concl k].
  split.
  - move/valid_clause_elim. intros hz.
    destruct min_premise => //. right. specialize (hz _ eq_refl). depelim hz.
    eexists; split; trea. unfold satisfiable_atom. cbn. rewrite H0. apply Z.leb_le. lia.
    now left.
  - intros disj; apply valid_clause_intro.
    intros z hz.
    destruct disj. congruence. destruct H as [z0 [hmin hsat]].
    rewrite hmin in hz; noconf hz.
    cbn in hsat. destruct level_value => //. constructor. apply Z.leb_le in hsat. lia.
Qed.

Definition inverse_clauses (cl : clause) :=
  let (prems, concl) := cl in
  clauses_of_le (succ_prems prems) (singleton concl).

Definition normalize m k :=
  option_map (fun k => k - model_min m) k.

Definition le_inter m m' :=
  (forall l k k', LevelMap.MapsTo l k m -> LevelMap.MapsTo l k' m' -> (k ≤ k')%opt).

Lemma is_ext_le_inter m m' :
  (m ⩽ m') -> le_inter m m'.
Proof.
  move=> hext l k k' /hext [] x [] hm0 hle hm1.
  eapply LevelMapFact.F.MapsTo_fun in hm0; tea. now subst.
Qed.

Import LevelMap (MapsTo).

Lemma mapsto_shift_model {n m k l} : MapsTo l k (shift_model n m) -> MapsTo l (option_map (fun k => k - n) k) m.
Proof.
  rewrite /shift_model LevelMapFact.F.map_mapsto_iff.
  intros [a [-> hm]]. destruct a; cbn => //.
  now have -> : (z + n - n) = z by lia.
Qed.

Lemma mapsto_shift_model_inv {n m k l} : MapsTo l k m -> MapsTo l (option_map (fun k => k + n) k) (shift_model n m).
Proof.
  rewrite /shift_model LevelMapFact.F.map_mapsto_iff.
  intros hm; eexists; split; trea.
Qed.

Definition normalize_model m := shift_model (- model_min m) m.

Lemma min_premise_None m prems : min_premise m prems = None <->
  (exists le, LevelExprSet.In le prems /\ level_value m le.1 = None).
Proof.
  have [hf hex] := min_premise_spec m prems.
  destruct min_premise eqn:hmin.
  - split => //.
    move=> [[minp minpk] [hin' hl]].
    specialize (hf _ hin'). rewrite /min_atom_value hl in hf.
    depelim hf.
  - split => // _.
    destruct hex as [[minp mink] [hin heq]].
    exists (minp, mink). split => //. rewrite /min_atom_value in heq.
    destruct level_value; cbn in *; congruence.
Qed.


Lemma model_of_level_value {V m} l :
  model_of V m ->
  LevelSet.In l V ->
  exists k, LevelMap.MapsTo l k m /\ level_value m l = k.
Proof.
  intros mof hin.
  specialize (mof l hin).
  destruct mof as [k hin']. exists k. split => //.
  now rewrite (level_value_MapsTo hin').
Qed.


Hint Rewrite clause_levels_spec levels_spec : set_specs'.

Lemma nge_lt x y : (~ x <= y) -> y < x.
Proof. intros n. unfold lt; cbn. lia. Qed.
Definition pred_expr (le : LevelExpr.t) :=
  (le.1, le.2 - 1).

Definition checking_clause (cl : clause) :=
  let (prems, concl) := cl in
  (singleton (pred_expr concl) ∪ prems, concl).

  Definition clause_premises_levels cl := NES.levels (premise cl).

  Lemma checking_clause_premise_levels cl :
    clause_premises_levels (checking_clause cl) =_lset
    clause_levels (checking_clause cl).
  Proof.
    destruct cl as [prems [concl k]]; rewrite /clause_premises_levels /checking_clause //=.
    rewrite /clause_levels. cbn. unfold pred_expr; cbn.
    intros l; firstorder. lsets. rsets.
    rewrite NES.levels_spec //=. exists (k - 1). lsets.
  Qed.

  Lemma checking_clause_levels cl :
    clause_levels (checking_clause cl) =_lset clause_levels cl.
  Proof.
    destruct cl as [prems [concl k]]; rewrite /clause_premises_levels /checking_clause //=.
    rewrite /clause_levels. cbn. unfold pred_expr; cbn.
    intros l. rewrite LevelSet.union_spec NES.levels_spec //=.
    setoid_rewrite LevelExprSet.union_spec; rewrite LevelSet.union_spec.
    setoid_rewrite NES.levels_spec. firstorder rsets. noconf H.
    now right.
  Qed.

Definition is_total_model m cls :=
  Model.enabled_clauses m cls /\ is_model m cls.

Definition is_enabled_clause m cl :=
  isSome (min_premise m (premise cl)).

Lemma reflect_enabled m cl : reflect (enabled_clause m cl) (is_enabled_clause m cl).
Proof.
  rewrite /is_enabled_clause /enabled_clause.
  destruct min_premise => //=.
  constructor; now eexists.
  constructor. intros [z eq] => //.
Qed.

Definition levels_of_model (m : model) :=
  LevelMap.fold (fun l _ acc => LevelSet.add l acc) m LevelSet.empty.

Lemma to_SL cls x y :
  let SL := horn_semi cls in
  cls ⊢ℋ x ⋞ y <-> x ≤ y.
Proof.
  intros SL.
  now cbn; rewrite Theory.le_spec /Clauses.le.
Qed.

Lemma add_n_succ {cls} {n : nat} (x : premises) :
  let SL := horn_semi cls in
  (x ∨ add (- Z.of_nat n) x ≡ x)%sl.
Proof.
  intros SL.
  induction n.
  - cbn. rewrite add_prems_0. apply (join_idem (Semilattice := SL)).
  - rewrite Nat2Z.inj_succ.
    have ha := add_prems_add_prems (-1) (-Z.of_nat n) x.
    have eq : - Z.of_nat n = 1 + - Z.succ (Z.of_nat n). lia.
    cbn in ha.
    rewrite -{1}IHn join_assoc (join_comm (add _ x)).
    rewrite eq -add_distr join_sub add_distr.
    cbn. rewrite -eq. apply IHn.
Qed.

Lemma valid_enabled_inverse m cl :
  enabled_clause m (checking_clause cl) ->
  valid_clause m (checking_clause cl) = false ->
  valid_clauses m (inverse_clauses (checking_clause cl)).
Proof.
  destruct cl as [prems [concl kconcl]].
  intros en vcl cl hin.
  unfold inverse_clauses in hin.
  eapply clauses_of_le_spec in hin as [[l k] [hin heq]]. subst cl.
  apply valid_clause_intro.
  move=> z hmin. red in en. cbn in en.
  destruct en as [z' hz].
  eapply min_premise_spec_aux in hz as [hf hex].
  rewrite min_premise_singleton in hmin.
  rewrite /min_atom_value in hmin.
  rewrite add_prems_union in hin.
  rewrite add_prems_singleton in hin.
  rewrite LevelExprSet.union_spec /singleton //= in hin.
  destruct hin. rsets. noconf H.
  rewrite /min_atom_value in hmin.
  destruct (level_value m concl) eqn:hl => //. noconf hmin. constructor. lia.
  rewrite map_levelexprset_spec in H. destruct H as [[l' k'] [hin heq]].
  noconf heq.
  move: vcl.
  unfold valid_clause. cbn.
  destruct min_premise eqn:hmin'.
  rewrite /level_value_above. rewrite /min_atom_value in hmin.
  destruct level_value eqn:hl => //. noconf hmin.
  move: hmin'.
  rewrite union_comm NES.union_add_singleton min_premise_add.
  rewrite /min_atom_value //= hl.
  destruct (min_premise m prems) eqn:hmprems => //=.
  intros [= <-].
  apply min_premise_spec_aux in hmprems as [hfp exp].
  specialize (hfp _ hin). rewrite /min_atom_value in hfp.
  destruct (level_value m l) eqn:hl'. depelim hfp.
  move/Z.leb_gt => h. constructor. lia.
  depelim hfp.
  move=> //.
Qed.


Theorem check_invalid_inverse {cls cl mcheck} :
  check_entails cls (checking_clause cl) = Invalid mcheck ->
  is_model mcheck (inverse_clauses (checking_clause cl)).
Proof.
  move/check_invalid => [ism mofm minm encl invcl].
  move/negP/negPf: invcl.
  rewrite /is_model => neg. apply Clauses.for_all_spec; tc.
  now apply valid_enabled_inverse.
Qed.

Lemma check_invalid_entails {cls cl m} :
  check_entails cls cl = Invalid m -> ~ entails cls cl.
Proof.
  move/check_invalid => [ism mof mabove en nv].
  now move/entails_model_valid/(_ m ism).
Qed.

(* For checking to satisfy injectivity rules,
  we force the conclusion to be defined by adding it to the premises.
  In injective semilattices, we can then remove it.
 *)


  Import Semilattice.
  Import ISL.


Equations? infer_model_extension (V : LevelSet.t) (m : model) (cls cls' : clauses)
  (prf : clauses_levels cls ⊂_lset V /\ clauses_levels cls' ⊂_lset V /\ only_model_of V m) : result V LevelSet.empty (Clauses.union cls cls') m :=
  | V, m, cls, cls', prf := loop V LevelSet.empty (Clauses.union cls cls') m m _.
Proof.
  split.
  - intros x. rewrite clauses_levels_spec.
    move=> [] cl. rewrite Clauses.union_spec.
    intros [[] incls]. apply H. apply clauses_levels_spec. exists cl. split => //.
    apply H0. apply clauses_levels_spec. exists cl; split => //.
  - exact H1.
  - eapply is_update_of_empty.
Qed.

Lemma is_update_of_only_model_of {V cls W m m'} :
  only_model_of V m ->
  is_update_of cls W m m' ->
  clauses_conclusions cls ⊂_lset V ->
  only_model_of V m'.
Proof.
  intros om.
  move/is_update_of_case => -[].
  - move=> [] he heq. now rewrite -heq.
  - move/[dup]/strictly_updates_only_model_gen.
    move/(_ _ om) => om' /strictly_updates_incl incl incl'.
    have he : (LevelSet.union V W) =_lset V.
    { lsets. }
    now rewrite he in om'.
Qed.

Equations? infer_extension {V W init cls} (m : valid_model V W init cls)
  (hincl : only_model_of V init)
  (hs : clauses_levels cls ⊂_lset V)
  (cls' : clauses)
  (hs' : clauses_levels cls' ⊂_lset V) :
  result V LevelSet.empty (Clauses.union cls cls') m.(model_model) :=
  infer_extension m hincl hs cls' hs' :=
    infer_model_extension V m.(model_model) cls cls' _.
Proof.
  split; [|split].
  - lsets.
  - lsets.
  - eapply is_update_of_only_model_of. exact hincl.
    eapply m.
    now rewrite (clauses_conclusions_levels cls).
Qed.

Section InitModels.

Definition init_clause_of_level l :=
  (singleton (l, 0), (Level.zero, if Level.is_global l then 1 else 0)).

Definition declared_init_clause_of_level l cls :=
  if eqb l Level.zero then True
  else Clauses.In (init_clause_of_level l) cls.


  Definition zero_declared m :=
    exists k, LevelMap.MapsTo Level.zero (Some (Z.of_nat (S k))) m.

  Lemma zero_declared_ext {m m'} :
    zero_declared m ->
    m ⩽ m' ->
    zero_declared m'.
  Proof. rewrite /zero_declared.
    move=> [] k hm ext. red in ext.
    move/ext: hm => -[] k' [hm' hle].
    rewrite Nat2Z.inj_succ in hle. depelim hle.
    setoid_rewrite Nat2Z.inj_succ.
    exists (Z.to_nat (Z.pred y)).
    rewrite Z2Nat.id //. by lia.
    have -> : Z.succ (Z.pred y) = y. lia.
    exact hm'.
  Qed.

  Definition declared_pos V (m : model) :=
    forall l, LevelSet.In l V -> exists k, LevelMap.MapsTo l (Some (Z.of_nat k)) m.

  Lemma declared_pos_ext {V} {m m' : model} :
    declared_pos V m ->
    m ⩽ m' ->
    declared_pos V m'.
  Proof. rewrite /declared_pos.
    move=> hl ext l /hl [] k /ext [] k' [] hm' hle.
    depelim hle.
    exists (Z.to_nat y).
    rewrite Z2Nat.id //. by lia.
  Qed.

  Definition above_zero_declared V cls :=
    forall l, LevelSet.In l V -> declared_init_clause_of_level l cls.

  Lemma above_zero_declared_ext {V cls cls'} :
    above_zero_declared V cls ->
    cls ⊂_clset cls' ->
    above_zero_declared V cls'.
  Proof. rewrite /above_zero_declared. rsets.
    move: (H _ H1); unfold declared_init_clause_of_level.
    case: (eqb_spec l Level.zero) => //.
    intros nzero. clsets.
  Qed.

End InitModels.

Module CorrectModel.

  Record t {V cls} :=
  { initial_model : model;
    declared_zero : zero_declared initial_model;
    declared_positive : declared_pos V initial_model;
    declared_above_zero : above_zero_declared V cls;
    enabled_model : enabled_clauses initial_model cls;
    only_model_of_V : only_model_of V initial_model;
    model_updates : LevelSet.t;
    clauses_declared : clauses_levels cls ⊂_lset V;
    model_valid : valid_model V model_updates initial_model cls
     }.
  Arguments t : clear implicits.

  Definition model_of {V cls} (x : t V cls) := x.(model_valid).(model_model).
  Coercion model_of : t >-> model.

  Lemma is_model_of {V cls} (x : t V cls) : is_model (model_of x) cls.
  Proof. apply x.(model_valid). Qed.

  Lemma model_minimal {V cls} (x : t V cls) : minimal_above cls (initial_model x) (model_of x).
  Proof.
    have upd := I.model_updates x.(model_valid).
    now eapply is_update_of_minimal_above in upd.
  Qed.

  Lemma declared_zero_model_of {V cls} (x :t V cls) : zero_declared (model_of x).
  Proof.
    have h := declared_zero x.
    have hupd := I.model_updates x.(model_valid).
    eapply is_update_of_ext in hupd.
    eapply zero_declared_ext; tea.
  Qed.

  Lemma declared_pos_model_of {V cls} (x :t V cls) : declared_pos V (model_of x).
  Proof.
    have h := declared_positive x.
    have hupd := I.model_updates x.(model_valid).
    eapply is_update_of_ext in hupd.
    eapply declared_pos_ext; tea.
  Qed.

  Lemma clauses_For_all_union f cls cls' :
    Clauses.For_all f (Clauses.union cls cls') <->
    Clauses.For_all f cls /\ Clauses.For_all f cls'.
  Proof.
    split.
    - move=> hf. split.
      all:move=> cl hin; move: (hf cl) => /fwd //; clsets.
    - move=> -[] ha hb cl /Clauses.union_spec.
      firstorder.
  Qed.

  Lemma clauses_for_all_union f cls cls' :
    Clauses.for_all f (Clauses.union cls cls') <->
    Clauses.for_all f cls /\ Clauses.for_all f cls'.
  Proof.
    rewrite ![is_true _]Clauses.for_all_spec.
    apply clauses_For_all_union.
  Qed.

  Lemma enabled_clauses_union {m cls cls'} :
    enabled_clauses m (Clauses.union cls cls') <->
    enabled_clauses m cls /\ enabled_clauses m cls'.
  Proof.
    unfold enabled_clauses. now apply clauses_For_all_union.
  Qed.

  Lemma is_model_union m cls cls' :
    is_model m (Clauses.union cls cls') <-> is_model m cls /\ is_model m cls'.
  Proof.
    unfold is_model. now rewrite clauses_for_all_union.
  Qed.

  Lemma is_total_model_union m cls cls' :
    is_total_model m (Clauses.union cls cls') <->
    is_total_model m cls /\ is_total_model m cls'.
  Proof.
    unfold is_total_model.
    rewrite enabled_clauses_union is_model_union.
    firstorder.
  Qed.

  Lemma declared_pos_enabled {m V cls} :
    clauses_levels cls ⊂_lset V ->
    declared_pos V m ->
    enabled_clauses m cls.
  Proof.
    intros incl dp.
    intros [prems [concl k]] hin; cbn.
    red. cbn.
    destruct min_premise eqn:hmin. now eexists.
    have [le [hin' heq]] := proj1 (min_premise_None m prems) hmin.
    move: (dp le.1) => /fwd.
    apply incl. eapply clauses_levels_spec. eexists; split; tea.
    rewrite clause_levels_spec. left. cbn. apply levels_spec. exists le.2; destruct le => //.
    intros [k0 hm].
    eapply level_value_MapsTo in hm. congruence.
  Qed.

  Equations? init_model : t (LevelSet.singleton Level.zero) Clauses.empty :=
  init_model := {|
      initial_model := LevelMap.add Level.zero (Some 1) (LevelMap.empty _);
      only_model_of_V := _;
      model_updates := LevelSet.empty;
      model_valid := {| model_model := LevelMap.add Level.zero (Some 1) (LevelMap.empty _) |} |}.
  Proof.
    - exists 0%nat. rsets. left; auto.
    - exists 1%nat. rsets.
    - rsets. red. now rewrite eqb_refl.
    - clsets.
    - rsets. split.
      * intros ->. exists (Some 1). rsets. now left.
      * move=> [] k'. rsets. destruct p; intuition auto.
    - lsets.
    - red. rsets. exists (Some 1). rsets; firstorder.
    - red. now rsets.
    - cbn in H. lsets.
  Qed.

  Record loop {cls} :=
    { loop_univ : premises;
      loop_incl : NES.levels loop_univ ⊂_lset clauses_levels cls;
      loop_on_univ : cls ⊢a loop_univ → succ_prems loop_univ;
    }.
  Arguments loop : clear implicits.

  Definition result V cls := (t V cls + loop cls)%type.

  #[local] Obligation Tactic := program_simpl.
  Equations? infer_extension_correct {V W init cls} (m : valid_model V W init cls)
    (enabled : enabled_clauses init cls)
    (hincl : only_model_of V init)
    (hs : clauses_levels cls ⊂_lset V)
    (cls' : clauses)
    (hs' : clauses_levels cls' ⊂_lset V)
    (hdeclz : zero_declared init)
    (hdecla : above_zero_declared V (Clauses.union cls cls'))
    (declp : declared_pos V init)
    : result V (Clauses.union cls cls') :=
  infer_extension_correct m enabled hincl hs cls' hs' hdeclz hdecla hdeclp with infer_extension m hincl hs cls' hs' :=
    | Loop u vcls isl => inr {| loop_univ := u; loop_on_univ := isl |}
    | Model w m' _ =>
      inl {|
        initial_model := m.(model_model);
        only_model_of_V := _;
        model_updates := w; clauses_declared := _;
        model_valid := {| model_model := m'.(model_model) |} |}.
  Proof.
    - have mupd := I.model_updates m. eapply is_update_of_ext in mupd.
      eapply zero_declared_ext; tea.
    - move=> l inv.
      have mupd := I.model_updates m. eapply is_update_of_ext in mupd.
      eapply declared_pos_ext; tea.
    - eapply enabled_clauses_ext.
      have mupd := I.model_updates m. eapply is_update_of_ext in mupd. exact mupd.
      rewrite enabled_clauses_union; split => //.
      red in hdeclp.
      red in hdecla.
      eapply declared_pos_enabled; tea.
    - exact: (valid_model_only_model _ _ _ _ m hincl).
    - intros x; rewrite clauses_levels_spec; rw Clauses.union_spec.
      intros [cl [[hin|hin] incl]]. apply hs. apply clauses_levels_spec. clear -hin incl; firstorder.
      apply hs'. apply clauses_levels_spec. clear -hin incl; firstorder.
    - have vm := model_of_V m'. eapply model_of_subset; tea. lsets.
    - apply m'.
    - intros ?; rewrite clauses_conclusions_spec.
      intros [cl [H H']]. apply Clauses.union_spec in H as [H|H];
        [apply hs|apply hs']; subst a; apply clauses_levels_spec; exists cl; split => //;
        eapply clause_levels_spec; auto.
    - apply m'.
  Qed.

  Equations? infer_extension_valid {V cls} (m : t V cls) cls' : option (result V (Clauses.union cls cls')) :=
  infer_extension_valid m cls' with inspect (LevelSet.subset (clauses_levels cls') V) :=
    | exist false heq => None
    | exist true heq => Some (infer_extension_correct (model_valid m) _ _ _ cls' _ _ _ _).
  Proof.
    - apply enabled_model.
    - apply only_model_of_V.
    - now apply m.
    - now apply LevelSet.subset_spec in heq.
    - now apply m.
    - apply LevelSet.subset_spec in heq.
      eapply above_zero_declared_ext. now apply m. clsets.
    - now apply m.
  Qed.

  Lemma infer_extension_valid_None {V cls} (m : t V cls) cls' :
    infer_extension_valid m cls' = None <-> ~ LevelSet.Subset (clauses_levels cls') V.
  Proof.
    funelim (infer_extension_valid m cls') => //=.
    - split=> // eq. clear Heqcall H. exfalso.
      apply LevelSet.subset_spec in heq. contradiction.
    - split=> // _ hsub. clear H.
      move/negP: heq => /LevelSet.subset_spec. contradiction.
  Qed.

  Lemma initial_model_levels {V cls} (m : t V cls) : forall l, (exists k, LevelMap.MapsTo l (Some k) (initial_model m)) <-> LevelSet.In l V.
  Proof.
    intros l. split.
    - move=> [] k hm.
      have hv := (only_model_of_V m).
      apply hv. now exists (Some k).
    - intros hin.
      have := declared_above_zero m _ hin.
      rewrite /declared_init_clause_of_level.
      case: (eqb_spec l Level.zero).
      * move=> ->.
        have := CorrectModel.declared_zero m.
        unfold zero_declared.
        now move=> [] k hm; exists (Z.of_nat (S k)).
      * intros nzero.
        have he := enabled_model m.
        move/he. rewrite /enabled_clause /init_clause_of_level.
        move=> [] k hm. cbn in hm.
        rewrite min_premise_singleton /min_atom_value in hm.
        destruct level_value eqn:hl => //.
        exists z. apply (level_value_MapsTo' hl).
  Qed.

  Definition model_valuation {V cls} (m : t V cls) : clauses_sem (to_Z_val (Model.valuation (model_of m))) cls.
  Proof.
    destruct m as []; cbn.
    apply valid_clauses_model; tea; cbn.
    - eapply enabled_clauses_ext; tea.
      eapply is_update_of_ext, model_valid0.
    - apply model_valid.
  Qed.

  Lemma model_levels {V cls} (m : t V cls) :
    forall l, LevelSet.In l V <-> (exists k, LevelMap.MapsTo l (Some k) (model_valid m).(model_model)).
  Proof.
    intros l. rewrite -initial_model_levels. split.
    - move=> [] k hm.
      have hupd := (I.model_updates m.(model_valid)).
      apply is_update_of_ext in hupd.
      eapply hupd in hm as [k' [hm hle]].
      depelim hle. now exists y.
    - intros hin.
      rewrite initial_model_levels.
      have hv := only_model_of_V m.
      have hupd := (I.model_updates m.(model_valid)).
      eapply is_update_of_only_model_of in hupd; tea.
      destruct hin as [k hm]. apply hupd. now exists (Some k).
      apply (model_valid m).
  Qed.

  Lemma model_zero_level {V cls} (m : t V cls) :
    exists k, LevelMap.MapsTo Level.zero (Some k) (model_valid m).(model_model) /\ 0 < k.
  Proof.
    have [k hm] := declared_zero m.
    have hupd := I.model_updates m.(model_valid).
    move/is_update_of_ext: hupd.
    move/(_ _ _ hm) => [k' [hm' ha]]. rewrite Nat2Z.inj_succ in ha. depelim ha.
    exists y; split => //. rewrite -Nat2Z.inj_succ in H. clear - H. cbn in *. lia.
  Qed.

  Lemma initial_model_min {V cls} (m : t V cls) : model_min (initial_model m) = 0.
  Proof.
    have minlt := model_min_spec2 (initial_model m).
    apply antisymmetry => //.
    have mins := model_min_spec.
    have [?|[l [k [mapmin ismin]]]] := model_has_min (initial_model m); try lia.
    rewrite ismin.
    have := (declared_positive m l) => /fwd.
    { rewrite -initial_model_levels; now eexists. }
    move=> [] k' hm.
    eapply LevelMapFact.F.MapsTo_fun in mapmin; tea. noconf mapmin. lia.
  Qed.

  Lemma model_min_ext {V m m'} :
    defined_model_of V m ->
    only_model_of V m' ->
    m ⩽ m' ->
    model_min m <= model_min m'.
  Proof.
    move=> om om' hext.
    have ms := model_min_spec m.
    have ms' := model_min_spec m'.
    (* have [m0|mhas] := model_has_min m. *)
    have [m0'|[l [k [mhas' kle]]]] := model_has_min m'; try lia.
    have ms2 := (model_min_spec2 m). lia.
    specialize (om l).
    forward om. rewrite om'. now exists (Some k).
    destruct om as [lk hmk].
    move: hmk => /[dup]/ms hle /hext [k' [hm' hle']]. depelim hle'.
    eapply LevelMapFact.F.MapsTo_fun in mhas'; tea. noconf mhas'. rewrite kle. lia.
  Qed.

  Lemma model_min_0 {V cls} (m : t V cls) : model_min m = 0.
  Proof.
    have initm := initial_model_min m.
    have hupd := I.model_updates m.(model_valid).
    move/is_update_of_ext: hupd => ext.
    have := model_min_ext (V:=V) _ _ ext => /fwd.
    { intros l. now rewrite initial_model_levels. }
    move=> /fwd.
    { apply (valid_model_only_model _ _ _ _ (model_valid m)).
      eapply m. }
    move=> hle.
    have minupd := model_min_spec2 m.
    rewrite initm in hle. rewrite -/(model_of m) in ext hle. lia.
  Qed.

  Lemma model_max_0 {V cls} {m : t V cls}: forall l k, LevelMap.MapsTo l (Some k) (model_of m) ->
     (Some k ≤ level_value (model_of m) (Level.zero))%opt.
  Proof.
    intros l k hm.
    have hab := declared_above_zero m l.
    rewrite (model_levels m) in hab.
    forward hab by now eexists.
    red in hab.
    move: hab hm; case: (eqb_spec l Level.zero).
    * move=> -> _ hm.
      now rewrite (level_value_MapsTo hm).
    * move=> nz hin hm.
      have hv := model_valuation m.
      apply hv in hin.
      move: hin; rewrite /clause_sem /init_clause_of_level //=.
      rewrite interp_nes_singleton //=.
      rewrite /to_Z_val /to_val /Model.valuation /to_val.
      have vs:= valuation_of_model_spec _ _ _ hm.
      rewrite (LevelMap.find_1 vs).
      have [kz [hz hzpos]] := model_zero_level m.
      have vzs := valuation_of_model_spec _ _ _ hz.
      rewrite (LevelMap.find_1 vzs). cbn. rewrite -/(model_of m).
      rewrite (level_value_MapsTo hz).
      intros ineq; constructor.
      destruct (Level.is_global) eqn:isg.
      + lia.
      + cbn in ineq.
        have hk := valuation_range hm.
        have hk' := valuation_range hz.
        rewrite -/(model_of m) in hk'.
        have mmax := model_max_spec2 (model_of m).
        have mmin := model_min_spec2 (model_of m).
        lia.
  Qed.

  Lemma model_max_gen {V cls} {m : t V cls} {l k} : LevelMap.MapsTo l (Some k) (model_of m) ->
    (if Level.is_global l then
      (to_val (Model.valuation_of_model (model_of m)) Level.zero) < (to_val (Model.valuation_of_model (model_of m)) l)
    else
      (to_val (Model.valuation_of_model (model_of m)) Level.zero) <= (to_val (Model.valuation_of_model (model_of m)) l))%nat.
  Proof.
    intros hm.
    have hab := declared_above_zero m l.
    rewrite (model_levels m) in hab.
    forward hab by now eexists.
    red in hab.
    move: hab hm; case: (eqb_spec l Level.zero).
    * move=> -> _ hm.
      have := Level.is_global_zero.
      destruct Level.is_global => //.
    * move=> nz hin hm.
      have hv := model_valuation m.
      apply hv in hin.
      move: hin; rewrite /clause_sem /init_clause_of_level //=.
      rewrite interp_nes_singleton //=.
      rewrite /to_Z_val /to_val /Model.valuation /to_val.
      have vs:= valuation_of_model_spec _ _ _ hm.
      rewrite (LevelMap.find_1 vs).
      have [kz [hz hzpos]] := model_zero_level m.
      have vzs := valuation_of_model_spec _ _ _ hz.
      rewrite (LevelMap.find_1 vzs). cbn. rewrite -/(model_of m).
      intros ineq.
      destruct (Level.is_global) eqn:isg.
      + lia.
      + cbn in ineq.
        have hk := valuation_range hm.
        have hk' := valuation_range hz.
        rewrite -/(model_of m) in hk'.
        have mmax := model_max_spec2 (model_of m).
        have mmin := model_min_spec2 (model_of m).
        lia.
  Qed.

  Lemma valuation_0 {V cls} {m : t V cls}: to_val (Model.valuation_of_model (model_of m)) Level.zero = 0%nat.
  Proof.
    have mmax := model_max_spec2 m.
    have mmin := model_min_spec2 m.
    have mmax' := model_has_max m.
    have [kzero [hzero hpos]] := model_zero_level m.
    have zerom := model_max_spec m _ _ hzero. depelim zerom.
    destruct mmax'. rewrite H0 in H. cbn in *. lia.
    destruct H0 as [l' [k' [hm' eqmax]]].
    move/model_max_0: hm'. rewrite (level_value_MapsTo hzero) => hle; depelim hle.
    have mr := valuation_range hzero. subst k'.
    have hs := valuation_of_model_spec (model_of m) _ _ hzero.
    cbn in hs.
    rewrite /to_val. rewrite (LevelMap.find_1 hs).
    have min0 := model_min_0 m.
    lia.
  Qed.

  Lemma valuation_global {V cls} {m : t V cls} :
    forall l, LevelSet.In l V -> Level.is_global l -> (0 < to_val (Model.valuation_of_model (model_of m)) l)%nat.
  Proof.
    move=> l /(model_levels m) [] k inm isg.
    have hmax := model_max_gen inm.
    rewrite isg in hmax.
    rewrite valuation_0 in hmax. lia.
  Qed.

  Lemma valuation_not_global {V cls} {m : t V cls} :
    forall l, LevelSet.In l V -> ~~ Level.is_global l -> (0 <= to_val (Model.valuation_of_model (model_of m)) l)%nat.
  Proof.
    move=> l /(model_levels m) [] k inm isg.
    have hmax := model_max_gen inm.
    move/negbTE: isg hmax => ->.
    now rewrite valuation_0.
  Qed.

End CorrectModel.

Module Abstract.
  Import CorrectModel.
  Record t :=
    { levels : LevelSet.t;
      clauses : Clauses.t;
      correct_model :> CorrectModel.t levels clauses }.

  Program Definition init_model : t :=
    {| levels := LevelSet.singleton Level.zero;
       clauses := Clauses.empty;
       correct_model := CorrectModel.init_model |}.

  Lemma clauses_levels_declared m : clauses_levels (clauses m) ⊂_lset levels m.
  Proof.
    exact m.(correct_model).(CorrectModel.clauses_declared).
  Qed.

  Lemma init_model_levels :
    levels init_model = LevelSet.singleton Level.zero.
  Proof. reflexivity. Qed.

  Lemma zero_declared_in (m : model) : zero_declared m -> LevelMap.In Level.zero m.
  Proof. intros [k hm]. now eexists. Qed.

  Definition model (x : t) := model_of x.(correct_model).

  Lemma zero_declared m : zero_declared (model m).
  Proof. eapply declared_zero_model_of. Qed.

  Lemma above_zero_declared m : above_zero_declared (levels m) (clauses m).
  Proof. eapply (declared_above_zero m). Qed.

  Lemma model_levels m :
    forall l, LevelSet.In l (levels m) <-> (exists k, LevelMap.MapsTo l (Some k) (model m)).
  Proof. apply (model_levels m). Qed.

  Lemma init_model_clause :
    clauses init_model = Clauses.empty.
  Proof. reflexivity. Qed.

  Lemma levelmap_add_comm {A} l o l' o' (m : LevelMap.t A) : l <> l' ->
    LevelMap.add l o (LevelMap.add l' o' m) =m
    LevelMap.add l' o' (LevelMap.add l o m).
  Proof.
    intros neq.
    apply LevelMapFact.F.Equal_mapsto_iff => k' o''.
    rewrite !LevelMapFact.F.add_mapsto_iff /Level.eq.
    firstorder; subst. right. split => //. auto.
    left; firstorder.
    right; firstorder.
  Qed.

  Lemma strictly_updates_add clauses W m m' l k :
    ~ LevelSet.In l (clauses_levels clauses) ->
    strictly_updates clauses W m m' ->
    strictly_updates clauses W (LevelMap.add l k m) (LevelMap.add l k m').
  Proof.
    move=> hnin su; move: W m m' su;
    apply: strictly_updates_elim; [|move=>m [prems [concl k']] m' incl su|move=>ls ls' m m' m'' su ihsu su' ihsu'].
    { solve_proper. }
    - move: su => [] v [] hmin habov hm'. cbn.
      eapply update_one; tea => //.
      exists v. split => //.
      * erewrite min_premise_preserved; tea.
        intros.
        have neq : x <> l.
        { intros ->. apply hnin. apply clauses_levels_spec. exists (prems, (concl, k')).
          split => //. apply clause_levels_spec. now left. }
        rewrite /level_value.
        rewrite LevelMapFact.F.add_neq_o; auto.
      * have neq : concl <> l.
        { intros ->. apply hnin. apply clauses_levels_spec. exists (prems, (l, k')).
          split => //. apply clause_levels_spec. now right. }
        rewrite /level_value_above /level_value LevelMapFact.F.add_neq_o; auto.
      * have neq : concl <> l.
        { intros ->. apply hnin. apply clauses_levels_spec. exists (prems, (l, k')).
          split => //. apply clause_levels_spec. now right. }
        now rewrite levelmap_add_comm // hm'.
    - eapply trans_update; tea.
  Qed.

  Lemma is_model_add clauses l k m :
    ~ LevelSet.In l (clauses_levels clauses) ->
    is_model m clauses ->
    is_model (LevelMap.add l k m) clauses.
  Proof.
    move=> hnin ism.
    eapply Clauses.for_all_spec; tc => cl hin'.
    move/Clauses.for_all_spec: ism => /(_ _ hin').
    destruct cl as [prems [concl k']].
    move/valid_clause_elim => he.
    apply valid_clause_intro => z.
    erewrite (@min_premise_preserved _ m); tea.
    - move/he.
      have neq : concl <> l.
      { intros ->. apply hnin. apply clauses_levels_spec. exists (prems, (l, k')).
        split => //. apply clause_levels_spec. now right. }
      rewrite /level_value LevelMapFact.F.add_neq_o; auto.
    - intros x hin.
      have neq : x <> l.
      { intros ->. apply hnin. apply clauses_levels_spec. exists (prems, (concl, k')).
        split => //. apply clause_levels_spec. now left. }
      rewrite /level_value.
      rewrite LevelMapFact.F.add_neq_o; auto.
  Qed.

  Lemma clauses_For_all_add {cl cls} {P} : Clauses.For_all P (Clauses.add cl cls) <->
    P cl /\ Clauses.For_all P cls.
  Proof.
    rewrite /Clauses.For_all; split; rsets.
    * split; intros; apply H; now rsets.
    * destruct H0; subst; now rsets.
  Qed.
  Hint Rewrite @clauses_For_all_add : set_specs.

  Lemma enabled_clauses_add {m cl cls} :
    enabled_clauses m (Clauses.add cl cls) <->
    enabled_clause m cl /\ enabled_clauses m cls.
  Proof.
    rewrite /enabled_clauses. now rsets.
  Qed.
  Hint Rewrite @enabled_clauses_add : set_specs.

  Lemma enabled_clause_init {l m k} :
    enabled_clause (LevelMap.add l (Some k) (initial_model (correct_model m))) (init_clause_of_level l).
  Proof.
    red.
    rewrite /init_clause_of_level //=.
    setoid_rewrite min_premise_singleton.
    rewrite /min_atom_value. setoid_rewrite level_value_add.
    now eexists.
    (* have [k ld] := declared_zero m.(model).
    eexists. rewrite (level_value_MapsTo ld). reflexivity. *)
  Qed.

  Lemma level_value_None (l : Level.t) {m : LevelMap.t _} : ~ LevelMap.In l m -> level_value m l = None.
  Proof.
    rewrite /level_value. destruct (find_spec l m) => //.
    elim. now exists k.
  Qed.

  Lemma level_value_add_other (l l' : Level.t) {k} {m : LevelMap.t _} : l <> l' -> level_value (LevelMap.add l k m) l' = level_value m l'.
  Proof.
    rewrite /level_value => hl.
    destruct (find_spec l' m) => //.
    rewrite LevelMapFact.F.add_neq_o => //.
    erewrite LevelMap.find_1; tea. reflexivity.
    rewrite LevelMapFact.F.add_neq_o => //.
    rewrite LevelMapFact.F.not_find_in_iff in H.
    now rewrite H.
  Qed.

  Instance lsets_po : PartialOrder LevelSet.Equal LevelSet.Subset.
  Proof.
    red. split.
    - intros eq; split; try red; lsets.
    - intros []. unfold flip in *; lsets.
  Qed.

  Instance clsets_po : PartialOrder Clauses.Equal Clauses.Subset.
  Proof.
    red. split.
    - intros eq; split; try red; clsets.
    - intros []. unfold flip in *; clsets.
  Qed.

  Instance levels_subset : Proper (Logic.eq ==> LevelSet.Subset ==> impl) LevelSet.In.
  Proof.
    intros ??-> ?? s hin. firstorder.
  Qed.

  Lemma clauses_levels_add {cl cls} : clauses_levels (Clauses.add cl cls) =_lset LevelSet.union (clause_levels cl) (clauses_levels cls).
  Proof.
    intros ?; rewrite !clauses_levels_spec; rsets.
    split.
    - move=> [] cl'. rsets; subst. firstorder. now subst.
    - intros []; firstorder. exists cl; firstorder; now rsets.
      exists x. firstorder. now rsets.
  Qed.
  Hint Rewrite @clauses_levels_add : set_specs.
  Hint Rewrite @levelexprset_singleton : set_specs.
  Hint Rewrite levels_singleton : set_specs.

  Lemma clause_levels_init_constraint l : clause_levels (init_clause_of_level l)
    =_lset (LevelSet.singleton Level.zero ∪ LevelSet.singleton l)%levels.
  Proof.
    rewrite /init_clause_of_level //=.
    intros ?; rewrite clause_levels_spec; rsets; cbn; rsets; cbn. firstorder.
  Qed.

  #[tactic="program_simpl"]
  Equations? declare_valid_model {V W init cls}
    (m : valid_model V W init cls)
    (l : Level.t)
    (hl : LevelSet.mem l V = false)
    (hnin : ~ LevelSet.In l (clauses_levels cls))
    (hz : LevelSet.In Level.zero V)
    (hzd : Deciders.zero_declared init) :
    valid_model (LevelSet.add l V) W
      (LevelMap.add l (Some (if Level.is_global l then 0 else 1)) init)
      (Clauses.add (init_clause_of_level l) cls) :=
  @declare_valid_model V W init cls m l hl hnin hz zerod := {|
      model_model := LevelMap.add l (Some (if Level.is_global l then 0 else 1)) m.(model_model) |}.
  Proof.
    all:destruct m as [M mofV mupd mcls mok]. cbn in *.
    * intros k. rewrite LevelSet.add_spec LevelMapFact.F.add_in_iff. firstorder. now left.
    * move: mupd; rewrite /is_update_of //=.
      destruct (LevelSet.is_empty) eqn:hw.
      { now intros ->. }
      { eapply levelset_not_Empty_is_empty in hw.
        apply LevelSetFact.not_mem_iff in hl.
        intros s. eapply strictly_updates_weaken; revgoals.
        eapply strictly_updates_add; tea. now clsets. }
    * rewrite clauses_conclusions_add. cbn. rsets.
    * apply LevelSetFact.not_mem_iff in hl.
      rewrite ClausesProp.add_union_singleton is_model_union //.
      split => //.
      rewrite is_model_valid.
      intros cl; rsets. subst cl.
      rewrite /init_clause_of_level.
      rewrite /valid_clause. cbn. rewrite min_premise_singleton //=.
      rewrite level_value_add /level_value_above.
      set value := Some _.
      have hleq : (Some 1 ≤ level_value (LevelMap.add l value M) Level.zero)%opt.
      { rewrite level_value_add_other. intros ->. now apply hl.
        eapply is_update_of_ext in mupd.
        eapply zero_declared_ext in zerod; tea.
        destruct zerod as [k hzero]. rewrite (level_value_MapsTo hzero).
        subst value. constructor. lia. }
      depelim hleq. rewrite H0.
      apply Z.leb_le. cbn. destruct Level.is_global; lia.
      apply is_model_add => //.
  Qed.

  #[tactic="program_simpl"]
  Equations? declare_level (m : t) (l : Level.t) : option t :=
  declare_level m l with inspect (LevelSet.mem l m.(levels)) :=
    | exist true _ => None
    | exist false hneq =>
      Some {|
        levels := LevelSet.add l m.(levels);
        clauses := Clauses.add (init_clause_of_level l) m.(clauses);
        correct_model :=
          {| initial_model := LevelMap.add l (Some (if Level.is_global l then 0 else 1)) m.(initial_model);
             only_model_of_V := _;
             model_updates := m.(model_updates);
             model_valid := declare_valid_model m.(model_valid) l hneq _ _ _
          |}
      |}.
  Proof.
    - have hv := only_model_of_V m.
      eapply zero_declared_ext. apply m.(correct_model). eapply update_model_monotone.
      rsets; rewrite level_value_None.
      { move=> hin'. apply hneq.
        apply hv, hin'. }
      constructor.
    - have hd := declared_positive m.
      move=> l' /LevelSet.add_spec [] hin'.
      * red in hin'; subst l'. destruct Level.is_global; [exists 0%nat|exists 1%nat]; rsets.
      * eapply hd in hin' as [k' hm']. exists k'. rsets. right. split => //.
        intros ->. apply hneq. eapply initial_model_levels; now eexists.
    - intros l'. rsets. destruct H; subst.
      * red. destruct eqb => //. clsets.
      * have hv := declared_above_zero m.(correct_model).
        eapply above_zero_declared_ext in H; tea. clsets.
    - have hv := only_model_of_V m.(correct_model).
      rewrite enabled_clauses_add. split; revgoals.
      { eapply enabled_clauses_ext.
        eapply update_model_not_above. rsets.
        rewrite /level_value_above.
        now rewrite level_value_None // => /hv.
        apply m.(correct_model). }
      apply enabled_clause_init.
    - intros k. rewrite LevelSet.add_spec /LevelSet.E.eq.
      rw LevelMapFact.F.add_mapsto_iff.
      have hyp := m.(correct_model).(only_model_of_V) k.
      firstorder; subst. all:rewrite /Level.eq.
      * now eexists.
      * exists x. right; split => //. intros ->.
        apply LevelSetFact.not_mem_iff in hneq. contradiction.
    - have hyp := m.(correct_model).(clauses_declared).
      rsets. rewrite clause_levels_init_constraint in H.
      move: H => []; rsets. destruct a0; subst.
      * right.
        have hd := declared_zero m.(correct_model). apply m.(only_model_of_V).
        now apply zero_declared_in.
      * now left.
      * move: b => [] cl [] hin. right.
        apply (clauses_levels_declared m a). rsets. firstorder.
    - destruct m as [levels clauses vm]; cbn in *.
      apply LevelSetFact.not_mem_iff in hneq; lsets.
    - destruct m as [levels clauses vm]; cbn in *.
      destruct vm as [init zerod azerod dpos en omofV W incl vm].
      apply zero_declared_in in zerod.
      now apply omofV.
    - destruct m as [levels clauses vm]; cbn in *.
      apply (declared_zero vm).
  Qed.

  Lemma declare_level_clauses {m l m'} :
    declare_level m l = Some m' -> clauses m' = (Clauses.add (init_clause_of_level l) (clauses m)).
  Proof.
    funelim (declare_level m l) => //=.
    intros [= <-]. now cbn.
  Qed.

  Lemma declare_level_levels {m l m'} :
    declare_level m l = Some m' -> ~ LevelSet.In l (levels m) /\ levels m' =_lset LevelSet.add l (levels m).
  Proof.
    funelim (declare_level m l) => //=.
    intros [= <-]. split; cbn => //.
    move/LevelSet.mem_spec. rewrite hneq => //.
  Qed.

  Lemma declare_level_None {m l} :
    declare_level m l = None <-> LevelSet.In l (levels m).
  Proof.
    funelim (declare_level m l) => //=; clear H Heqcall.
    - apply LevelSet.mem_spec in e. firstorder.
    - split => //.
      move/LevelSet.mem_spec. rewrite hneq => //.
  Qed.

  Equations enforce_clauses (m : t) (cls : Clauses.t) : option (t + loop (Clauses.union (clauses m) cls)) :=
  enforce_clauses m cls with infer_extension_valid m.(correct_model) cls :=
    | None => None
    | Some (inl m') => Some (inl {| correct_model := m' |})
    | Some (inr u) => Some (inr u).

  Lemma enforce_clauses_None m cls :
    enforce_clauses m cls = None <->
    ~ LevelSet.Subset (clauses_levels cls) (levels m).
  Proof.
    simp enforce_clauses.
    have:= @infer_extension_valid_None _ _ (correct_model m) cls.
    destruct infer_extension_valid as [[]|]; simp enforce_clauses; split => //.
    1-2:move/H => //. intuition.
  Qed.

  Lemma enforce_clauses_not_None m cls :
    enforce_clauses m cls <> None <-> LevelSet.Subset (clauses_levels cls) (levels m).
  Proof.
    unfold not. rewrite enforce_clauses_None.
    destruct (LevelSet.subset (clauses_levels cls) (levels m)) eqn:he.
    apply LevelSet.subset_spec in he. firstorder.
    move/negP: he.
    intros ne. red in ne.
    split => //.
    intros ne'. destruct ne'. intros hs.
    apply LevelSet.subset_spec in hs. apply ne. now rewrite hs.
  Qed.

  Lemma enforce_clauses_levels m cls m' :
    enforce_clauses m cls = Some (inl m') ->
    levels m' = levels m.
  Proof.
    funelim (enforce_clauses m cls) => //=.
    intros [= <-]. now cbn.
  Qed.

  Lemma enforce_clauses_clauses m cls m' :
    enforce_clauses m cls = Some (inl m') ->
    clauses m' = Clauses.union (clauses m) cls.
  Proof.
    funelim (enforce_clauses m cls) => //=.
    intros [= <-]. now cbn.
  Qed.

  Import I.Model.Model.Clauses.ISL.


  Lemma premises_loop cls cl {prems : premises} conclk :
    premise cl ⊂_leset prems ->
    Clauses.add cl cls ⊢ prems → conclk ->
    exists n, cls ⊢ singleton (add_expr n (concl cl)) ∨ prems → conclk.
  Proof.
    intros hincl h.
    depind h.
    - exists 0. constructor. eapply LevelExprSet.union_spec. now right.
    - forward IHh. intros l. move/hincl. now rewrite add_spec.
      depelim H.
      eapply Clauses.add_spec in H. destruct H.
      * subst cl0. destruct cl; noconf H0. cbn in *.
        destruct IHh as [n0 ent].
        exists (Z.max n0 n).
        destruct (Z.max_spec n0 n) as [[hle heq]|[hlt heq]].
        { rewrite heq.
          have he := @entails_add cls (NES.add (add_expr n p) prems) (add_expr n0 p) concl0.
          forward he.
          { destruct p as [concl k].
            eapply entails_lower. exists (n + k). split.
            rewrite LevelExprSet.add_spec. now left. cbn. lia. }
          rewrite union_comm union_add_singleton. apply he.
          rewrite -union_add_singleton union_comm. exact ent. }
        { rewrite heq.
          have he := @entails_add cls (NES.add (add_expr n0 p) prems) (add_expr n p) concl0.
          forward he.
          { destruct p as [concl k].
            eapply entails_lower. exists (n0 + k). split.
            rewrite LevelExprSet.add_spec. now left. cbn. lia. }
          rewrite union_comm union_add_singleton. apply he.
          move: ent.
          now rewrite -!union_add_singleton -union_assoc (@union_comm _ prems). }
      * destruct IHh. exists x.
        destruct cl0 ; noconf H0.
        eapply (clause_cut _ (add_prems n t0) (add_expr n p)).
        apply (incls _ (t0, p)) => //.
        move: H2.
        now rewrite -!union_add_singleton union_assoc.
        move=> le /H1 hin. apply LevelExprSet.union_spec. now right.
      * destruct IHh as [n ent]. exists n.
        eapply (clause_cut _ (singleton (x, k+1)) (x, k)).
        constructor.
        move: ent. now rewrite -!union_add_singleton union_assoc.
        move=> le /H0 hin. apply LevelExprSet.union_spec. now right.
  Qed.




  Definition entails_loop m cls :=
    exists u : premises,
    NES.levels u ⊂_lset clauses_levels (Clauses.union (clauses m) cls) /\
    Clauses.union (clauses m) cls ⊢ℋ succ u ⋞ u.

  Lemma enforce_clauses_loop_simple m cls u :
    enforce_clauses m cls = Some (inr u) ->
    entails_loop m cls.
  Proof.
    funelim (enforce_clauses m cls) => //=.
    intros [= <-]. clear -u.
    destruct u as [u incl loop]. cbn [loop_univ].
    eapply to_entails_all in loop.
    now exists u; split.
  Qed.

  Lemma enforce_clauses_loop m cls u :
    enforce_clauses m cls = Some (inr u) ->
    entails_L_clauses (Clauses.union (clauses m) cls) (loop_univ u ≡ succ_prems (loop_univ u)).
  Proof.
    funelim (enforce_clauses m cls) => //=.
    intros [= <-]. clear -u.
    destruct u as [u incl loop]. cbn [loop_univ].
    eapply to_entails_all in loop.
    apply entails_L_clauses_eq; split; revgoals.
    - now eapply entails_ℋ_entails_L.
    - eapply entails_ℋ_entails_L.
      eapply to_entails_all.
      apply entails_all_succ.
  Qed.


  (* Returns the valuation of the model: a minimal assignement from levels to constraints
    that make the enforced clauses valid. *)
  Definition valuation m := to_val (Model.valuation_of_model (model m)).

  (** This is a valuation in Z, which defaults to 0 for undefined universes. It enables all clauses. *)
  Definition model_valuation m : clauses_sem (to_Z_val (valuation m)) (clauses m).
  Proof.
    destruct m as [levels clauses []]; cbn.
    apply valid_clauses_model; tea; cbn.
    - eapply enabled_clauses_ext; tea; cbn.
      eapply is_update_of_ext, model_valid0.
    - apply model_valid.
  Qed.

  Definition opt_valuation (m : t) := opt_valuation_of_model (model m).

  (** This is a valuation in Z⊥  *)
  Definition model_opt_Z_valuation m : clauses_sem (opt_valuation m) (clauses m).
  Proof.
    apply valid_clauses_model_opt; tea; cbn.
    apply model_valid.
  Qed.

  Definition enables_clause val cl :=
    exists k, interp_nes val (premise cl) = Some k.

  Definition enables_clauses val cls := Clauses.For_all (enables_clause val) cls.

  Definition consistent_opt_val (val : Level.t -> option Z) (cls : Clauses.t) :=

    clauses_sem val cls.

  Definition consistent_opt cls :=
    exists val : Level.t -> option Z, consistent_opt_val val cls.

  Lemma min_atom_value_mapsto {m le k} : min_atom_value m le = Some k ->
    LevelMap.MapsTo le.1 (Some (k + le.2)) m.
  Proof.
    rewrite /min_atom_value.
    destruct le. case: (@level_valueP m t0) => // -[k'|] // hm [=] <-.
    cbn. now have -> : k' - z + z = k' by lia.
  Qed.

  Lemma mapsto_opt_valuation_of_model {m l k} :
    LevelMap.MapsTo l (Some k) m ->
    opt_valuation_of_model m l = Some (valuation_of_value m k).
  Proof.
    rewrite /opt_valuation_of_model => hm; apply LevelMap.find_1 in hm.
    now rewrite hm.
  Qed.

  Lemma min_premise_interp_nes_ex {m u minp} :
    min_premise m u = Some minp ->
    exists z, interp_nes (opt_valuation_of_model m) u = Some z /\
    (exists maxx maxk, LevelExprSet.In maxx u /\ LevelMap.MapsTo maxx.1 (Some maxk) m /\ z = valuation_of_value m maxk + maxx.2) /\
    forall x, LevelExprSet.In x u -> exists k, LevelMap.MapsTo x.1 (Some k) m /\
    valuation_of_value m k + x.2 <= z /\ minp <= k - x.2.
  Proof.
    move: u minp.
    apply: NES.elim.
    { intros [l lk]. rewrite interp_nes_singleton min_premise_singleton //= => minp.
      case: (@level_valueP m l) => // -[] // vl hm [=] <-.
      rewrite (mapsto_opt_valuation_of_model hm) //=.
      eexists; split => //.
      setoid_rewrite LevelExprSet.singleton_spec. split.
      do 2 eexists; split; trea. split; tea. cbn. lia.
      intros x ->. eexists; split => //. exact hm. split => //. cbn. lia. cbn. lia. }
    { intros [l k] u.
      intros h nin minp.
      rewrite min_premise_add.
      destruct min_atom_value eqn:hmin => //.
      2:{ now move/min_opt_None_left. }
      destruct (min_premise m u) => //.
      specialize (h _ eq_refl) as [z1 [? [[maxx [maxk [inmax [mmax maxle]]]]]]].
      cbn. intros [= <-].
      have ha := (NES.interp_nes_add (SL := Zopt_semi) (opt_valuation_of_model m) (l, k) u).
      rewrite H in ha.
      have hminv := min_atom_value_mapsto hmin. cbn in hminv.
      cbn [interp_expr] in ha.
      rewrite (mapsto_opt_valuation_of_model hminv) in ha.
      cbn [eq Zopt_semi] in ha.
      destruct (interp_nes _ (NES.add _ _)); cbn in ha => //.
      subst z2. eexists; split; trea.
      split.
      destruct (Z.max_spec (k + valuation_of_value m (z + k)) z1) as [[hle heq]|[hle heq]].
      * do 2 eexists; split => //. eapply LevelExprSet.add_spec. now right.
        split; tea. now subst z1.
      * do 2 eexists; split => //. eapply LevelExprSet.add_spec. left; trea.
        split. exact hminv. cbn in *. lia.
      * intros x; rewrite LevelExprSet.add_spec => -[].
        + intros ->. eexists; split; tea. cbn. lia.
        + move/H0 => [k' [hm [hle hle']]]. eexists; split; tea. lia. }
  Qed.

  Lemma model_enabled m : enabled_clauses (model m) (clauses m).
  Proof.
    have hen := enabled_model m.
    have hupd := I.model_updates m.(model_valid).
    eapply is_update_of_ext in hupd.
    eapply enabled_clauses_ext in hen; tea.
  Qed.

  Lemma opt_valuation_enables m : enables_clauses (opt_valuation m) (clauses m).
  Proof.
    move: (model_enabled m).
    cbn. rewrite /opt_valuation /opt_valuation_of_model /model /model_of.
    generalize (model_model (model_valid m)).
    generalize (clauses m).
    clear; intros cls m en.
    move=> cl /en; clear.
    destruct cl as [prems concl]; rewrite /enabled_clause /enables_clause; cbn.
    intros [k hmin].
    move/min_premise_interp_nes_ex: hmin => [z [eq rest]]. now exists z.
  Qed.

  Lemma clauses_consistent_opt_val m : consistent_opt_val (opt_valuation m) (clauses m).
  Proof.
    (* split. *)
     (* apply opt_valuation_enables. *)
    apply model_opt_Z_valuation.
  Qed.

  Lemma clauses_consistent_opt m : consistent_opt (clauses m).
  Proof.
    eexists; eapply clauses_consistent_opt_val.
  Qed.

  Lemma clauses_consistent m : consistent (clauses m).
  Proof. exists (Z_valuation_of_model m); split.
    - apply valuation_of_model_pos.
    - apply model_valuation.
  Qed.

  Definition inconsistent_opt cls := ~ (consistent_opt cls).

  Definition inconsistent cls := ~ (consistent cls).

  Lemma model_entails_loop m v :
    clauses m ⊢a v → succ v -> False.
  Proof.
    eapply model_entails_succ; tea.
    exact: m.(correct_model).(model_valid).(model_ok).
    eapply enabled_clauses_ext, m.(correct_model).(enabled_model).
    now eapply (is_update_of_ext m.(correct_model).(model_valid).(I.model_updates)).
  Qed.

  Lemma enforce_clauses_inconsistent_semilattice {m cls u} :
    enforce_clauses m cls = Some (inr u) ->
    forall S (SL : Semilattice.Semilattice S Q.t) (V : Level.t -> S),
    clauses_sem V (Clauses.union (clauses m) cls) ->
    clauses_sem V (loop_univ u ≡ succ (loop_univ u)).
  Proof.
    move/enforce_clauses_loop.
    rewrite -entails_L_rels_entails_L_clauses.
    rewrite -ISL.completeness_all.
    move=> vr S SL V.
    specialize (vr S SL V).
    move: vr.
    rewrite !interp_rels_clauses_sem // => vr /vr.
  Qed.

  Lemma enforce_clauses_inconsistent_loop {m cls u} :
    enforce_clauses m cls = Some (inr u) ->
    entails_loop m cls.
  Proof.
    now move/enforce_clauses_loop_simple.
  Qed.

  Definition defined_valuation_of {A} V (v : Level.t -> option A) :=
    forall l, LevelSet.In l V -> exists x, v l = Some x.

  Instance proper_defined_valuation_of {A} :
    Proper (LevelSet.Equal ==> Logic.eq ==> iff) (@defined_valuation_of A).
  Proof.
    intros x y ? ?? ->.
    rewrite /defined_valuation_of.
    now setoid_rewrite H.
  Qed.

  Definition inconsistent_opt_ext m cls :=
    entails_loop m cls.
    (* forall v : Level.t -> option Z,
      defined_valuation_of (clauses_levels (Clauses.union (clauses m) cls)) v ->
      clauses_sem v (Clauses.union (clauses m) cls) -> False. *)


  Lemma interp_expr_inv {m le k} :
    interp_expr (opt_valuation_of_model m) le = Some k ->
    exists k', LevelMap.MapsTo le.1 (Some k') m /\ k = le.2 + valuation_of_value m k'.
  Proof.
    destruct le as [l k'].
    rewrite /interp_expr /opt_valuation_of_model.
    destruct (find_spec l m) => //.
    destruct k0 => //; intros [= <-].
    exists z. split => //.
  Qed.

  Lemma interp_expr_defined {model} le :
    defined_model_of (LevelSet.singleton le.1) model ->
    interp_expr (opt_valuation_of_model model) le = Some (interp_expr (Z_valuation_of_model model) le).
  Proof.
    destruct le as [l k]; cbn.
    move => /(_ l) => /fwd. lsets.
    move=> [v hm].
    have := (@opt_valuation_of_model_pos model l).
    rewrite /opt_valuation_of_model /Z_valuation_of_model /to_val /to_Z_val.
    rewrite (LevelMap.find_1 hm). cbn.
    eapply Model.valuation_of_model_spec in hm.
    rewrite (LevelMap.find_1 hm). cbn.
    rewrite /valuation_of_value. cbn.
    intros h; specialize (h _ eq_refl).
    f_equal. lia.
  Qed.

  Lemma interp_expr_defined_val (v : Level.t -> option Z) le :
    defined_valuation_of (LevelSet.singleton le.1) v ->
    exists k, interp_expr v le = Some k.
  Proof.
    destruct le as [l k]; cbn.
    move => /(_ l) => /fwd. lsets.
    move=> [x hm]. rewrite hm. now eexists.
  Qed.

  Lemma R_optP (x y : option Z) : reflectProp (R_opt eq x y) (eqb x y).
  Proof.
    destruct (eqb_spec x y); constructor.
    - destruct x, y; cbn; try congruence. now noconf H.
    - intros hr. destruct x, y; cbn; depelim hr; try congruence.
  Qed.

  Lemma interp_nes_add_opt_Z {v le u} : NES.interp_nes (SL := Zopt_semi) v (NES.add le u) =
    option_map2 Z.max (interp_expr v le) (interp_nes (SL := Zopt_semi) v u).
  Proof.
    have ha := interp_nes_add (SL := Zopt_semi) v le u.
    move/R_optP: ha. move/(eqb_eq _ _). auto.
  Qed.


  Lemma interp_nes_defined_val v (u : NES.t) :
    defined_valuation_of (NES.levels u) v ->
    exists u', interp_nes v u = Some u'.
  Proof.
    move: u.
    apply: elim.
    - intros [l k] => //= hin.
      rewrite !interp_nes_singleton.
      rewrite levels_singleton in hin.
      now apply interp_expr_defined_val.
    - move=> le x eq wf def.
      forward eq. move: def. rewrite /defined_model_of.
      move=> h l hin. apply h. rewrite levels_add. lsets.
      rewrite interp_nes_add_opt_Z.
      destruct eq as [? ->].
      have := @interp_expr_defined_val v le => /fwd.
      { intros l; move: (def l) => h hin; apply h. rewrite levels_add. rsets. now left. }
      intros [k ->]. now eexists.
  Qed.

  Lemma interp_nes_defined {m} (u : NES.t) :
    defined_model_of (NES.levels u) m ->
    interp_nes (opt_valuation_of_model m) u = Some (interp_nes (Z_valuation_of_model m) u).
  Proof.
    move: u.
    apply: elim.
    - intros [l k] => //= hin.
      rewrite !interp_nes_singleton.
      rewrite levels_singleton in hin.
      rewrite interp_expr_defined //.
    - move=> le x eq wf def.
      forward eq. move: def. rewrite /defined_model_of.
      move=> h l hin. apply h. rewrite levels_add. lsets.
      rewrite interp_nes_add_opt_Z eq interp_expr_defined.
      { intros l; move: (def l) => h hin; apply h. rewrite levels_add. rsets. now left. }
      cbn. now rewrite interp_nes_add.
  Qed.

  Lemma defined_model (m : t) : defined_model_of (levels m) (model_of m).
  Proof.
    intros l hin.
    have [k hm] := declared_pos_model_of m l hin.
    now exists (Z.of_nat k).
  Qed.

  Lemma enforce_clauses_inconsistent_opt {m cls u} :
    enforce_clauses m cls = Some (inr u) ->
    inconsistent_opt_ext m cls.
  Proof.
    intros ec. red.
    now move/enforce_clauses_inconsistent_loop: ec.
    (* unfold entails_loop.
    move/enforce_clauses_inconsistent_semilattice: ec => /(_ (option Z) _ v csem).
    rewrite clauses_sem_eq //= interp_add_prems //=.
    destruct u as [loop incl hl]. cbn.
    destruct interp_nes eqn:hi => //=. lia.
    red in def.
    have [l|hd] := interp_nes_defined_val v loop.
    { move/incl. apply def. }
    congruence. *)
  Qed.

  Lemma enforce_clauses_inconsistent {m cls u} :
    enforce_clauses m cls = Some (inr u) ->
    inconsistent (Clauses.union (clauses m) cls).
  Proof.
    move/enforce_clauses_inconsistent_semilattice => ec [v [posv cs]].
    move: (ec Z _ v cs).
    rewrite clauses_sem_eq //= interp_add_prems //=. lia.
  Qed.

  Definition inconsistent_ext_Z m cls :=
    forall v : Level.t -> Z, positive_valuation v -> clauses_sem v (clauses m) -> ~ clauses_sem v cls.

  Definition inconsistent_ext m cls :=
    forall v : Level.t -> option Z, positive_opt_valuation v -> clauses_sem v (clauses m) -> ~ clauses_sem v cls.

  Equations? enforce_dec m cls (wf : clauses_levels cls ⊂_lset levels m) :
    { consistent (Clauses.union (clauses m) cls) } +
    { inconsistent_opt_ext m cls } :=
    enforce_dec m cls wf with inspect (enforce_clauses m cls) :=
    | exist None ec => !%prg (* impossible by wf *)
    | exist (Some (inl model)) ec => in_left
    | exist (Some (inr loop)) ec => in_right.
  Proof.
    - move/enforce_clauses_clauses: ec.
      intros <-. apply clauses_consistent.
    - now move/enforce_clauses_inconsistent_opt: ec.
    - move/enforce_clauses_None: ec. contradiction.
  Qed.

  Definition valid_entailments cls cls' :=
    forall S (SL : Semilattice S Q.t) (V : Level.t -> S), clauses_sem V cls -> clauses_sem V cls'.

  Definition valid_semilattice_entailment {S} (SL : Semilattice S Q.t) cls cl :=
    (forall (v : Level.t -> S), clauses_sem v cls -> clause_sem v cl).

  Definition valid_semilattice_entailments {S} (SL : Semilattice S Q.t) cls cls' :=
    (forall (v : Level.t -> S), clauses_sem v cls -> clauses_sem v cls').

  Lemma opt_valuation_of_model_inv {m l k} :
    opt_valuation_of_model m l = Some k ->
    exists k', LevelMap.MapsTo l (Some k') m /\ k = valuation_of_value m k'.
  Proof.
    rewrite /opt_valuation_of_model.
    destruct (find_spec l m) => //.
    destruct k0 => //; intros [= <-].
    exists z. split => //.
  Qed.

  Lemma clause_sem_defined_premises_valid {model cl} :
    defined_model_of (NES.levels (premise cl)) model ->
    clause_sem (opt_valuation_of_model model) cl -> clause_sem (Z_valuation_of_model model) cl.
  Proof.
    intros def.
    destruct cl as [prems [concl k]].
    rewrite /clause_sem. rewrite interp_nes_defined //.
    unfold interp_expr.
    destruct (opt_valuation_of_model model concl) eqn:hconcl.
    * eapply opt_valuation_of_model_inv in hconcl as [k' [hm heq]]. subst z.
      cbn. rewrite {3}/Z_valuation_of_model /to_Z_val /to_val.
      have hv := valuation_of_value_pos hm.
      apply valuation_of_model_spec in hm.
      rewrite (LevelMap.find_1 hm). rewrite -/(valuation_of_value model k').
      lia.
    * now cbn.
  Qed.

  Lemma clause_sem_defined_valid_all {model cl} :
    defined_model_of (clause_levels cl) model ->
    clause_sem (Z_valuation_of_model model) cl <-> clause_sem (opt_valuation_of_model model) cl.
  Proof.
    intros def.
    destruct cl as [prems [concl k]].
    rewrite /clause_sem. rewrite interp_nes_defined.
    { intros l hin; apply def. rewrite /clause_levels //=. lsets. }
    rewrite interp_expr_defined.
    { intros l hin; apply def; rewrite /clause_levels //=. cbn in hin. lsets. }
    now cbn.
  Qed.

  Lemma clauses_sem_def_equiv {model cls} :
    defined_model_of (clauses_levels cls) model ->
    clauses_sem (Z_valuation_of_model model) cls <-> clauses_sem (opt_valuation_of_model model) cls.
  Proof.
    intros def.
    rewrite /clauses_sem. red in def.
    split; move=> ha cl /[dup]/ha cs hin.
    rewrite -clause_sem_defined_valid_all //.
    { intros l hin'; apply def. eapply clauses_levels_spec. now exists cl. }
    rewrite clause_sem_defined_valid_all //.
    { intros l hin'; apply def. eapply clauses_levels_spec. now exists cl. }
  Qed.


  Definition valuation_max V v :=
    LevelSet.fold (fun l acc => match v l with Some k => Z.max k acc | None => acc end) V 0%Z.

  Definition valuation_min V v :=
    LevelSet.fold (fun l acc => match v l with Some k => Z.min k acc | None => acc end) V 0%Z.

  Definition value_of_valuation V v k :=
    let max := valuation_max V v in
    let min := valuation_min V v in
    min + k - max.

  Definition levels_of_model (m : Model.model) :=
    LevelMap.fold (fun l _ => LevelSet.add l) m LevelSet.empty.

  Lemma clause_sem_valid {model cl} :
    clause_sem (opt_valuation_of_model model) cl -> valid_clause model cl.
  Proof.
    intros semcl.
    destruct cl as [prems [concl k]].
    cbn -[le] in semcl.
    apply valid_clause_intro => minp mineq.
    cbn -[le] in semcl.
    have [iprems [eqiprems [[maxl [maxk [inmax [hmax eqmax]]]] hleprems]]] := min_premise_interp_nes_ex mineq.
    rewrite eqiprems in semcl. subst iprems.
    apply le_spec in semcl. destruct semcl => //.
    destruct H as [y' [z' [eq [eq' le]]]]. noconf eq'.
    destruct opt_valuation_of_model eqn:evconcl; noconf eq.
    rename z into vconcl.
    move/opt_valuation_of_model_inv: evconcl => [mconcl [hmconcl eq]].
    subst vconcl.
    rewrite /level_value_above.
    rewrite (level_value_MapsTo hmconcl). constructor.
    have [exm [[minl mink] [hin fmin]]] := min_premise_spec_aux _ _ _ mineq.
    specialize (hleprems _ inmax). cbn in hleprems.
    destruct hleprems as [minv [hminv [lei ge]]].
    eapply LevelMapFact.F.MapsTo_fun in hmax; tea. noconf hmax.
    have exm' := (exm _ hin). depelim exm'.
    rewrite /min_atom_value in fmin. destruct (level_value model minl) eqn:hminl => //.
    noconf fmin. noconf H0.
    move: lei ge le0.
    rewrite /valuation_of_value. unfold le, eq; cbn. lia.
  Qed.

  Lemma clauses_sem_valid {model cls} :
    clauses_sem (opt_valuation_of_model model) cls <-> is_model model cls.
  Proof.
    rewrite is_model_valid. split.
    intros clssem. red. move=> cl /clssem. apply clause_sem_valid.
    move=> vm cl /vm. apply valid_clause_model_opt.
  Qed.

  Lemma def_clause_sem_valid {model cl} :
    defined_model_of (clause_levels cl) model ->
    clause_sem (Z_valuation_of_model model) cl <-> valid_clause model cl.
  Proof.
    intros def.
    split.
    - intros cs. apply clause_sem_valid. rewrite -clause_sem_defined_valid_all //.
    - intros v. rewrite clause_sem_defined_valid_all //. now apply valid_clause_model_opt.
  Qed.

  Lemma def_clauses_sem_valid {model cls} :
    defined_model_of (clauses_levels cls) model ->
    clauses_sem (Z_valuation_of_model model) cls <-> is_model model cls.
  Proof.
    intros def. rewrite clauses_sem_def_equiv //.
    apply clauses_sem_valid.
  Qed.

  Theorem check_invalid_valuation {cls cl m} :
    check_entails cls cl = Invalid m ->
    let v := opt_valuation_of_model m in
    [/\ positive_opt_valuation v, clauses_sem v cls,
      defined_valuation_of (clause_premises_levels cl) v & ~ clause_sem v cl].
  Proof.
    move/check_invalid=> [ism _ _ en inval].
    have hpos := opt_valuation_of_model_pos.
    have semcls := valid_clauses_model_opt _ _ ism.
    split => //.
    { intros l.
      move: en; rewrite /enabled_clause => -[z hmin].
      eapply min_premise_spec_aux in hmin as [hf _].
      rewrite /clause_premises_levels NES.levels_spec.
      move=> [] k /hf. intros le; depelim le. move: H0.
      rewrite /opt_valuation_of_model /level_value.
      case: (find_spec l m) => //; destruct k0 => //.
      move=> hmf [= eq]. subst y. now eexists. }
    { move/clause_sem_valid. contradiction. }
  Qed.

    Definition opt_val_of_Z_val (v : Level.t -> Z) : Level.t -> option Z := fun l => Some (v l).

    Definition Z_val_of_opt_val (v : Level.t -> option Z) : Level.t -> Z := fun l => option_get 0 (v l).

    Lemma interp_expr_opt {v e} :
      interp_expr (opt_val_of_Z_val v) e = Some (interp_expr (SL := Zsemilattice) v e).
    Proof.
      destruct e; cbn; congruence.
    Qed.

    Lemma interp_expr_opt_inv {v e z} :
      interp_expr (SL := Zopt_semi) v e = Some z ->
      interp_expr (Z_val_of_opt_val v) e = z.
    Proof.
      destruct e; cbn. rewrite /Z_val_of_opt_val. destruct (v t0) eqn:vt0 => //=. congruence.
    Qed.

    Lemma interp_nes_add_Z {v le u} : NES.interp_nes (SL := Zsemilattice) v (NES.add le u) =
      Z.max (interp_expr v le) (interp_nes v u).
    Proof.
      now rewrite interp_nes_add.
    Qed.

    Lemma interp_nes_opt {v e} :
      interp_nes (opt_val_of_Z_val v) e = Some (interp_nes v e).
    Proof.
      move: e; apply elim.
      - intros []. now rewrite !interp_nes_singleton interp_expr_opt.
      - intros le x h nin.
        rewrite interp_nes_add_opt_Z interp_expr_opt h //=.
        f_equal. now rewrite interp_nes_add.
    Qed.

    Lemma interp_nes_opt_inv {v} {e z} :
      interp_nes v e = Some z ->
      interp_nes (Z_val_of_opt_val v) e = z.
    Proof.
      move: e z; apply: NES.elim.
      - intros le z. rewrite !interp_nes_singleton.
        now move/interp_expr_opt_inv.
      - intros le x h nin z.
        rewrite interp_nes_add_opt_Z interp_nes_add.
        case he : interp_expr => //. 2:{ cbn. destruct interp_nes => //. }
        move/interp_expr_opt_inv: he => ->.
        case he' : interp_nes => //=.
        move/h: he'. intros ->. congruence.
    Qed.

    Lemma clause_sem_opt {v cl} :
      clause_sem (opt_val_of_Z_val v) cl <-> clause_sem v cl.
    Proof.
      destruct cl as [prems concl]; rewrite /clause_sem interp_expr_opt interp_nes_opt.
      now cbn.
    Qed.

    Lemma clauses_sem_opt {v cls} :
      clauses_sem (opt_val_of_Z_val v) cls <-> clauses_sem v cls.
    Proof.
      now split; move => h cl /h; rewrite clause_sem_opt.
    Qed.

  Definition declared_clauses_levels V cls := LevelSet.Subset (clauses_levels cls) V.

  Lemma defined_model_of_subset {V V' m} : LevelSet.Subset V V' -> defined_model_of V' m -> defined_model_of V m.
  Proof.
    now move=> sub def l /sub /def.
  Qed.

  Lemma entails_dec (m : t) cl :
    { entails (clauses m) cl } + { ~ entails (clauses m) cl }.
  Proof.
    destruct (check_entails (clauses m) cl) eqn:ch.
    - move/check_looping: ch; elim.
      exists (model_of m). split.
      { have dm := defined_model m.
        eapply defined_model_of_subset; tea.
        eapply defined_model_of_subset; tea.
        apply clauses_levels_declared. }
      exact: is_model_of m.
    - move/check_invalid_entails: ch. intros ne. now right.
    - move/check_entails_entails: ch. now left.
  Qed.

  Definition valid_clause_opt cls cl :=
    forall v : Level.t -> option Z,
      positive_opt_valuation v ->
      clauses_sem v cls -> clause_sem v cl.

  Definition valid_clauses_Z cls cls' :=
    forall v : Level.t -> Z,
      positive_valuation v ->
      clauses_sem v cls -> clauses_sem v cls'.

  Definition model_of_valuation V v :=
    LevelSet.fold (fun l => LevelMap.add l (option_map (value_of_valuation V v) (v l))) V (LevelMap.empty _).

  Lemma contraP P Q : (P -> Q) -> (~ Q -> ~ P).
  Proof. intros f hp q. apply (hp (f q)). Qed.

  Lemma clauses_sem_subset {S} {SL : Semilattice.Semilattice S Q.t} {v : Level.t -> S} {cls cls'} : clauses_sem v cls -> cls' ⊂_clset cls -> clauses_sem v cls'.
  Proof.
    now move=> hall hsub cl /hsub.
  Qed.

  Import Semilattice.

  Lemma clauses_sem_clauses_of_le {S} {SL : Semilattice S Q.t} (V : Level.t -> S) l r :
    clauses_sem V (clauses_of_le l r) ->
    (interp_nes V l ≤ interp_nes V r)%sl.
  Proof.
    rewrite /clauses_sem.
    intros hl. red in hl.
    setoid_rewrite clauses_of_le_spec in hl.
    move: l hl. apply: elim.
    - move => le he.
      rewrite interp_nes_singleton.
      move: (he (r, le)) => /fwd.
      exists le. split => //. now apply LevelExprSet.singleton_spec.
      now cbn.
    - intros le x ih hnin ih'.
      rewrite interp_nes_add.
      forward ih. intros x0 [x1 [hin ->]].
      move: (ih' (r, x1)) => /fwd. exists x1. split => //. apply LevelExprSet.add_spec. now right.
      auto.
      move: (ih' (r, le)) => /fwd. exists le. split => //.  apply LevelExprSet.add_spec. now left.
      cbn. cbn in ih. rewrite /Semilattice.le.
      move: ih. rewrite /Semilattice.le.
      now rewrite join_assoc; intros ->.
  Qed.

  Lemma clauses_sem_tot_inverse_false (v : Level.t -> Z) (cl : clause) :
    clauses_sem v (inverse_clauses cl) ->
    clause_sem v cl ->
    False.
  Proof.
    destruct cl as [prems concl].
    cbn [clause_sem]. move/clauses_sem_clauses_of_le.
    rewrite interp_add_prems interp_nes_singleton. cbn; lia.
  Qed.

  Lemma neg_inverse_Z (v : Level.t -> Z) (cl : clause) :
    ~ clause_sem v cl <-> clauses_sem v (inverse_clauses cl).
  Proof.
    destruct cl as [prems [concl k]].
    cbn [clause_sem]. rewrite clauses_sem_leq.
    rewrite interp_add_prems interp_nes_singleton. cbn.
    split; lia.
  Qed.

  Lemma neg_inverse_Z_inv (v : Level.t -> Z) (cl : clause) :
    clause_sem v cl <-> ~ clauses_sem v (inverse_clauses cl).
  Proof.
    destruct cl as [prems [concl k]].
    cbn [clause_sem]. rewrite clauses_sem_leq.
    rewrite interp_add_prems interp_nes_singleton. cbn.
    split; lia.
  Qed.

  Lemma neg_inverse (v : Level.t -> option Z) (cl : clause) :
    defined_valuation_of (clause_levels cl) v ->
    ~ clause_sem v cl <-> clauses_sem v (inverse_clauses cl).
  Proof.
    destruct cl as [prems [concl k]].
    cbn [clause_sem]. rewrite clauses_sem_leq.
    rewrite interp_add_prems interp_nes_singleton. cbn.
    intros def.
    have [l|vc hc] := interp_expr_defined_val v (concl, k).
    { intros hin; apply def. cbn in *. rsets. apply clause_levels_spec. cbn.
      now right. }
    have [l|vp hp] := interp_nes_defined_val v prems.
    { intros hin; apply def. cbn in *. rsets. apply clause_levels_spec. cbn.
      now left. }
    cbn in hc. rewrite hc hp //=. lia.
  Qed.

  Definition enforce_inverse m cl :=
    enforce_clauses m (inverse_clauses cl).

  Lemma clause_levels_inverse cl :
    clauses_levels (inverse_clauses cl) =_lset clause_levels cl.
  Proof.
    intros l. destruct cl as [prems concl].
    rewrite clauses_levels_spec.
    rewrite /inverse_clauses.
    rewrite clause_levels_spec => //=.
    split; firstorder.
    - eapply clauses_of_le_spec in H.
      destruct H as [lk [hin eq]]. subst x.
      apply clause_levels_spec in H0.
      destruct H0; cbn in *; firstorder.
      right. apply NES.levels_spec in H as []; cbn in H.
      rsets. subst. left.
      apply In_add_prems in hin as [le' []]. subst lk.
      cbn. apply levels_spec. exists le'.2. destruct le' => //.
    - apply levels_spec in H as [k hin].
      exists ((singleton concl), (l, add 1 k)). split.
      apply clauses_of_le_spec. exists (l, add 1 k); split => //.
      apply In_add_prems. eexists; split; trea. reflexivity.
      apply clause_levels_spec. now right; cbn.
    - subst. exists (singleton concl, choose (succ prems)).
      split. apply clauses_of_le_spec.
      exists (choose (succ prems)). split => //. apply choose_spec.
      apply clause_levels_spec. left; cbn.
      apply levels_spec; exists concl.2. destruct concl; cbn. now rsets.
  Qed.

  Lemma clause_sem_Z_dec (v : Level.t -> Z) cl :
    Decidable.decidable (clause_sem v cl).
  Proof.
    destruct cl; cbn.
    red. lia.
  Qed.

  Lemma clause_sem_dec (v : Level.t -> option Z) cl :
    Decidable.decidable (clause_sem v cl).
  Proof.
    destruct cl; cbn.
    destruct interp_expr eqn:ie; cbn;
    destruct interp_nes eqn:ine; cbn.
    red.
    destruct (Z.eq_dec (Z.max z z0) z0). now left.
    now right. now left. now right. now left.
  Qed.

  Instance total_opt : Total (option Z).
  Proof.
    red. intros [] []; cbn. lia. now left. now right. now left.
  Qed.

  Instance con_Z : Consistent Z.
  Proof.
    intros x; cbn. lia.
  Qed.

  Instance con_nat : Consistent nat.
  Proof.
    intros x; cbn. lia.
  Qed.

Definition check_entailsb cls cl :=
  match check_entails cls cl with
  | IsLooping _ _ _ => false
  | Valid => true
  | Invalid _ => false
  end.

Lemma check_entails_model_looping m cl v vcls isl :
  check_entails (clauses m) cl = IsLooping v vcls isl -> False.
Proof.
  intros. eapply check_valid_looping; tea.
  apply m.(model_valid).(model_ok).
  eapply defined_model_of_ext. eapply defined_model_of_subset.
  2:{ eapply defined_model. }
  now intros ? ?; eapply clauses_levels_declared, vcls.
  have hupd := m.(model_valid).(I.model_updates).
  now eapply is_update_of_ext in hupd.
Qed.

Lemma checkb_entails m cl :
  check_entailsb (clauses m) cl <-> entails (clauses m) cl.
Proof.
  unfold check_entailsb.
  destruct (check_entails) eqn:ec.
  - now move/check_entails_model_looping: ec.
  - split => //.
    now move/check_invalid_entails: ec.
  - now move/check_entails_entails: ec.
Qed.

Lemma check_entails_model m cl :
  check_entailsb (clauses m) cl <->
  (forall m', is_model m' (clauses m) -> enabled_clause m' cl -> valid_clause m' cl).
Proof.
  unfold check_entailsb.
  destruct (check_entails) eqn:ec.
  - now move/check_entails_model_looping: ec.
  - split => //.
    move/check_invalid: ec.
    intros [ism mof hmin en inval]. move/(_ m0 ism en). contradiction.
  - split => // _.
    intros m' ism.
    move/check_entails_entails: ec => ent.
    intros _.
    eapply entails_model_valid; tea.
Qed.

Definition valid_model_clause m cl :=
  (forall m', is_model m' (clauses m) -> enabled_clause m' cl -> valid_clause m' cl).

Lemma entails_models m cl : entails (clauses m) cl <-> valid_model_clause m cl.
Proof.
  now rewrite -checkb_entails check_entails_model.
Qed.

Definition valid_all_model_clauses m cls :=
  (forall m', is_model m' (clauses m) -> enabled_clauses m' cls -> valid_clauses m' cls).

Definition valid_model_clauses m cls :=
  (forall m', is_model m' (clauses m) ->
    forall cl, Clauses.In cl cls -> enabled_clause m' cl -> valid_clause m' cl).

Lemma entails_all_models m cls : clauses m ⊢ℋ cls -> valid_all_model_clauses m cls.
Proof.
  rewrite /entails_clauses.
  intros ha m' ism en.
  move=> cl hin. specialize (ha _ hin).
  specialize (en _ hin).
  now move/entails_models/(_ _ ism): ha.
Qed.

Lemma entails_all_models_inv m cls : valid_model_clauses m cls <-> clauses m ⊢ℋ cls.
Proof.
  split.
  - rewrite /entails_clauses.
    move=> ha cl /ha hall.
    now rewrite entails_models.
  - rewrite /entails_clauses.
    intros ha m' ism cl. move=> /ha.
    move/entails_models=> vm. now apply vm.
Qed.

Lemma check_entails_neg_exists_model m cl :
  check_entailsb (clauses m) cl = false <->
  exists m', [/\ is_model m' (clauses m), enabled_clause m' cl & ~ valid_clause m' cl].
Proof.
  unfold check_entailsb.
  funelim (check_entails (clauses m) cl) => //.
  - clear H. symmetry in Heqcall.
    now move/check_entails_model_looping: Heqcall.
  - clear H H0. symmetry in Heqcall. split => //.
    move/check_entails_entails: Heqcall => ent.
    intros [m' []]; exfalso.
    eapply entails_model_valid in ent; tea. contradiction.
  - clear H H0. symmetry in Heqcall. split => //.
    move/check_invalid: Heqcall => -[]. now eexists; split => //.
Qed.

Lemma negb_iff (b : bool) : ~ b <-> ~~ b.
Proof. destruct b; intuition. Qed.

Lemma nentails_model m cl :
  ~ entails (clauses m) cl <->
  exists m', [/\ is_model m' (clauses m), enabled_clause m' cl & ~ valid_clause m' cl].
Proof.
  rewrite -checkb_entails.
  rewrite negb_iff /is_true negb_true_iff.
  apply check_entails_neg_exists_model.
Qed.

Definition consistent_clauses cls :=
  exists val : Level.t -> Z, positive_valuation val /\ clauses_sem val cls.

(* The valution here is in 𝐙 + ∞:
  - clauses max (∞, ...) >= x are trivially valid.
  - clauses max ... >= ∞ are invalid.

  This corresponds  the fact that validity checking does compute
  all the "downward" consequences of its premises (say [x, y]),
  but will not consider unrelated max(v, x) expressions if [v] is
  not entailed by [x] or [y].
  I.e. such expressions can live arbitrarily high.
 *)
Definition valid_clause_Zinf cls cl :=
  forall v : Level.t -> option Z,
  positive_opt_valuation v ->
  clauses_sem v cls ->
  clause_sem v cl.

Definition valid_clauses_Zinf cls cls' :=
  forall v : Level.t -> option Z,
  positive_opt_valuation v ->
  clauses_sem v cls ->
  clauses_sem v cls'.

Definition valid_clause_Z cls cl :=
  forall v : Level.t -> Z,
  positive_valuation v ->
  clauses_sem v cls ->
  clause_sem v cl.

Lemma valid_clause_Z_Zinf cls cl : valid_clause_Zinf cls cl -> valid_clause_Z cls cl.
Proof.
  move=> vzinf v pos csem.
  move: (vzinf (opt_val_of_Z_val v)) => /fwd.
  { rewrite /opt_val_of_Z_val => l k hopt. noconf hopt.
    apply pos. }
  rewrite clauses_sem_opt clause_sem_opt; apply => //.
Qed.

Definition valid_clause_Z_mon cls cls' cl :
  Clauses.Subset cls cls' -> valid_clause_Zinf cls cl -> valid_clause_Zinf cls' cl.
Proof.
  intros hsub vz v vpos clsem.
  eapply vz => //.  eapply clauses_sem_subset; tea.
Qed.

Definition valid_clause_Z_mon_neg cls cls' cl :
  Clauses.Subset cls cls' -> ~ valid_clause_Zinf cls' cl -> ~ valid_clause_Zinf cls cl.
Proof.
  intros hsub vz vz'. eapply valid_clause_Z_mon in vz'; tea. contradiction.
Qed.

Lemma check_clause_invalid_Zinf m mcheck cl :
  check_entails (clauses m) cl = Invalid mcheck -> ~ valid_clause_Zinf (clauses m) cl.
Proof.
  move/check_invalid_valuation => [vpos csem hdef clsem].
  now move=> /(_ (opt_valuation_of_model mcheck) vpos csem).
Qed.

Lemma incon_forall cls : ~ consistent cls -> (forall v : Level.t -> Z, positive_valuation v -> clauses_sem v cls -> False).
Proof.
  intros incon v hpos csem. apply incon. exists v. split => //.
Qed.

Lemma consistent_dec (m : t) cl :
  clauses_levels (Clauses.singleton cl) ⊂_lset levels m ->
  { consistent (Clauses.union (clauses m) (Clauses.singleton cl)) } +
  { ~ consistent (Clauses.union (clauses m) (Clauses.singleton cl)) }.
Proof.
  intros hwf. destruct (enforce_dec m (Clauses.singleton cl)) => //.
  - now left.
  - right. destruct i as [loop [incl ent]].
    intros [v [csem c]].
    eapply entails_L_entails_ℋ_equiv in ent.
    eapply entails_L_rels_entails_L_clauses in ent.
    eapply completeness_all in ent.
    red in ent.
    specialize (ent Z _ v).
    rewrite -!interp_rels_clauses_sem in ent.
    specialize (ent c).
    eapply clauses_sem_clauses_of_le in ent.
    rewrite interp_add_prems in ent. cbn in ent. lia.
Qed.

Lemma curry {A B C : Prop} : (A /\ B -> C) <-> (A -> B -> C).
Proof. intuition. Qed.

Lemma incon_con m cl :
  ~ consistent (Clauses.union (clauses m) (Clauses.singleton cl)) ->
  consistent (Clauses.union (clauses m) (inverse_clauses cl)).
Proof.
  intros n.
  have hf := incon_forall _ n.
  setoid_rewrite clauses_sem_union in hf.
  specialize (hf (Z_valuation_of_model m)).
  forward hf. apply valuation_of_model_pos.
  rewrite (@curry _ _ _) in hf.
  forward hf. eapply model_valuation.
  exists (Z_valuation_of_model m). split.
  apply valuation_of_model_pos.
  eapply clauses_sem_union. split.
  apply model_valuation.
  rewrite clauses_sem_singleton in hf. cbn in hf.
  now eapply neg_inverse_Z in hf.
Qed.

Lemma consistent_clause_dec (m : t) cl :
  clauses_levels (Clauses.singleton cl) ⊂_lset levels m ->
  { consistent (Clauses.union (clauses m) (Clauses.singleton cl)) } +
  { consistent (Clauses.union (clauses m) (inverse_clauses cl)) }.
Proof.
  intros hwf; destruct (consistent_dec m cl) => //.
  - now left.
  - right. now apply incon_con.
Qed.

Instance proper_clauses_sem {S} {SL : Semilattice S Q.t} (v : Level.t -> S) : Proper (Clauses.Equal ==> iff) (clauses_sem v).
Proof.
  intros cls cls' h.
  rewrite /clauses_sem. now rewrite h.
Qed.

Lemma consistent_clauses_dec (m : t) cls :
  clauses_levels cls ⊂_lset levels m ->
  { m' | clauses m' =_clset Clauses.union (clauses m) cls } + (* consistent *)
  { ~ exists m', clauses m' =_clset (Clauses.union (clauses m) cls) }.
Proof.
  intros hwf.
  destruct (enforce_clauses m cls) eqn:hl.
  destruct s as [m'|loop].
  - move/enforce_clauses_clauses: hl.
    left; exists m'. rewrite hl. reflexivity.
  - move/enforce_clauses_inconsistent: hl.
    intros hincon. right. intros [m' hcls].
    elim hincon. red. exists (Z_valuation_of_model m'). split.
    eapply valuation_of_model_pos. have hm := model_valuation m'.
    now rewrite hcls in hm.
  - now move/enforce_clauses_None: hl.
Qed.

Definition check_entails_clauses (cls : Clauses.t) (cls' : Clauses.t) : bool :=
  Clauses.for_all (check_entailsb cls) cls'.

Lemma check_entails_clauses_spec m cls' :
  check_entails_clauses (clauses m) cls' <-> clauses m ⊢ℋ cls'.
Proof.
  rewrite /check_entails_clauses.
  rewrite [is_true _]Clauses.for_all_spec.
  split.
  move=> ha cl /ha.
  rewrite -/(is_true (check_entailsb (clauses m) cl)).
  now rewrite checkb_entails.
  move=> hent cl /hent.
  now rewrite -checkb_entails.
Qed.

Definition valid_total_models cls cl :=
  forall m : Model.model, is_total_model m cls ->
  defined_model_of (clause_levels cl) m -> valid_clause m cl.

Lemma valid_total_models_Z_models cls cl : valid_clause_Z cls cl -> valid_total_models cls cl.
Proof.
  intros H m istot encl.
  move: (H (Z_valuation_of_model m)) => /fwd.
  eapply valuation_of_model_pos.
  move=> /fwd. destruct istot. move/is_modelP: H1 => H1.
  move=> cl' /[dup] /H0 en /H1.
  now eapply valid_clause_model.
  intros cs.
  rewrite -def_clause_sem_valid //.
Qed.

Instance incl_leset_preorder : PartialOrder LevelExprSet.Equal LevelExprSet.Subset.
Proof.
  red. intros x y. split.
  - unfold relation_conjunction; cbn. intros ->. split; auto. reflexivity.
    red. reflexivity.
  - cbn; unfold flip. lesets.
Qed.

Instance rew_lesub : RewriteRelation LevelExprSet.Subset := {}.

Lemma subset_singleton (prems : premises) x : prems ⊂_leset singleton x -> prems = singleton x.
Proof.
  move: prems; apply: elim.
  - move=> le /(_ le) => /fwd.
    now apply LevelExprSet.singleton_spec.
    now rewrite LevelExprSet.singleton_spec => ->.
  - intros le x' hincl hnin hadd.
    destruct (Classes.eq_dec x le).
    * subst. specialize (hadd (choose x')).
      forward hadd. apply add_spec; right. apply choose_spec.
      eapply singleton_spec in hadd. subst.
      elim hnin. apply choose_spec.
    * specialize (hadd le). forward hadd.
      now apply add_spec.
      apply LevelExprSet.singleton_spec in hadd. red in hadd. congruence.
Qed.

(** Due to the possible models of entailments in arbitrary semilattices
  with an inflationary and injective endomorphism, one cannot rule out
  models where + is the identity, hence the following counterexamples:
  a clause can be declared invalid by checking while it is valid
  when considering only models in (Z, max, +).
*)
Module CounterExample1.
(* x ∨ y -> y + 1 *)
Definition valid_Z_counterexample_cls (x y : Level.t) : clause :=
  ((singleton (x, 0) ∨ singleton (y, 0)), (y, 1))%nes.

(* x -> y + 1 *)
Definition valid_Z_counterexample_cl (x y : Level.t) : clause :=
  (singleton (x, 0), (y, 1))%nes.

Example check_clause_invalid_Z_counterexample (x y : Level.t) :
  x <> y ->
  let cls := Clauses.singleton (valid_Z_counterexample_cls x y) in
  let cl := valid_Z_counterexample_cl x y in
  exists mcheck, check_entails cls cl = Invalid mcheck /\ valid_clause_Z cls cl.
Proof.
  move=> hdiff cls cl.
  set (v := (fun l : Level.t => if eqb l x then 1 else 0)%Z).
  have vx : v x = 1. now rewrite /v eqb_refl.
  have vy : v y = 0. rewrite /v. case: eqb_spec => //. subst; congruence.
  have hcls : clauses_sem v cls.
  { eapply clauses_sem_singleton. cbn.
    rewrite interp_nes_union !interp_nes_singleton //=.
    rewrite vx vy. cbn. lia. }
  have hcon : consistent cls.
  { exists v. split => //.
    intros l. unfold v. case: eqb_spec => //. }
  destruct check_entails eqn:ec.
  - move/check_entails_entails_looping: ec.
    move/consistent_no_loop. contradiction.
  - exists m. split => //.
    intros v' vpos csem.
    unfold cl; cbn.
    rewrite interp_nes_singleton //=.
    move: (csem (valid_Z_counterexample_cls x y)) => /fwd. now eapply Clauses.singleton_spec.
    cbn. rewrite !interp_nes_union !interp_nes_singleton //=. lia.
  - exfalso. move/check_entails_entails: ec.
    rewrite entails_completeness.
    intros ent.
    set (vopt := (fun l : Level.t => if eqb l x then Some 0 else None)%Z).
    have voptx : vopt x = Some 0. now rewrite /vopt eqb_refl.
    have vopty : vopt y = None. rewrite /vopt. case: eqb_spec => //. subst; congruence.
    specialize (ent (option Z) _ vopt).
    have hcls' : clauses_sem vopt cls.
    { eapply clauses_sem_singleton. cbn.
      rewrite interp_nes_union !interp_nes_singleton //=.
      rewrite voptx vopty. now cbn. }
    move: (ent hcls'); cbn.
    rewrite !interp_nes_singleton //=.
    now rewrite voptx vopty; cbn.
Qed.

Example check_clause_checking_invalid_Z_example (x y : Level.t) :
  x <> y ->
  let cls := Clauses.singleton (valid_Z_counterexample_cls x y) in
  let cl := valid_Z_counterexample_cl x y in
  check_entails cls (checking_clause cl) = Valid.
Proof.
  move=> hdiff cls cl.
  set (v := (fun l : Level.t => if eqb l x then 1 else 0)%Z).
  have vx : v x = 1. now rewrite /v eqb_refl.
  have vy : v y = 0. rewrite /v. case: eqb_spec => //. subst; congruence.
  have hcls : clauses_sem v cls.
  { eapply clauses_sem_singleton. cbn.
    rewrite interp_nes_union !interp_nes_singleton //=.
    rewrite vx vy. cbn. lia. }
  have hcon : consistent cls.
  { exists v. split => //.
    intros l. unfold v. case: eqb_spec => //. }
  destruct check_entails eqn:ec.
  - move/check_entails_entails_looping: ec.
    move/consistent_no_loop. contradiction.
  - exfalso. move/check_invalid_entails: ec.
    apply. apply entails_completeness.
    red. intros.
    move: (H (valid_Z_counterexample_cls x y)) => /fwd.
    now apply Clauses.singleton_spec.
    cbn. rewrite !interp_nes_union !interp_nes_singleton //=.
    rewrite !add_neutral. intros hle.
    now rewrite join_comm.
  - reflexivity.
Qed.

End CounterExample1.

Module CounterExample2.
(* x + 1 ∨ y -> y + 1 *)
Definition valid_Z_counterexample_cls (x y : Level.t) : clause :=
  ((singleton (x, 1) ∨ singleton (y, 0)), (y, 1))%nes.

(* x -> y *)
Definition valid_Z_counterexample_cl (x y : Level.t) : clause :=
  (singleton (x, 0), (y, 0))%nes.

Example check_clause_invalid_Z_counterexample (x y : Level.t) :
  x <> y ->
  let cls := Clauses.singleton (valid_Z_counterexample_cls x y) in
  let cl := valid_Z_counterexample_cl x y in
  exists mcheck, check_entails cls cl = Invalid mcheck /\ valid_clause_Z cls cl.
Proof.
  move=> hdiff cls cl.
  set (v := (fun l : Level.t => if eqb l x then 1 else 0)%Z).
  have vx : v x = 1. now rewrite /v eqb_refl.
  have vy : v y = 0. rewrite /v. case: eqb_spec => //. subst; congruence.
  have hcls : clauses_sem v cls.
  { eapply clauses_sem_singleton. cbn.
    rewrite interp_nes_union !interp_nes_singleton //=.
    rewrite vx vy. cbn. lia. }
  have hcon : consistent cls.
  { exists v. split => //.
    intros l. unfold v. case: eqb_spec => //. }
  destruct check_entails eqn:ec.
  - move/check_entails_entails_looping: ec.
    move/consistent_no_loop. contradiction.
  - exists m. split => //.
    intros v' vpos csem.
    unfold cl; cbn.
    rewrite interp_nes_singleton //=.
    move: (csem (valid_Z_counterexample_cls x y)) => /fwd. now eapply Clauses.singleton_spec.
    cbn. rewrite !interp_nes_union !interp_nes_singleton //=. lia.
  - exfalso. move/check_entails_entails: ec.
    rewrite entails_completeness.
    intros ent.
    set (vopt := (fun l : Level.t => if eqb l x then Some 0 else None)%Z).
    have voptx : vopt x = Some 0. now rewrite /vopt eqb_refl.
    have vopty : vopt y = None. rewrite /vopt. case: eqb_spec => //. subst; congruence.
    specialize (ent (option Z) _ vopt).
    have hcls' : clauses_sem vopt cls.
    { eapply clauses_sem_singleton. cbn.
      rewrite interp_nes_union !interp_nes_singleton //=.
      rewrite voptx vopty. now cbn. }
    move: (ent hcls'); cbn.
    rewrite !interp_nes_singleton //=.
    now rewrite voptx vopty; cbn.
Qed.

Example check_clause_checking_invalid_Z_example (x y : Level.t) :
  x <> y ->
  let cls := Clauses.singleton (valid_Z_counterexample_cls x y) in
  let cl := valid_Z_counterexample_cl x y in
  check_entails cls (checking_clause cl) = Valid.
Proof.
  move=> hdiff cls cl.
  set (v := (fun l : Level.t => if eqb l x then 1 else 0)%Z).
  have vx : v x = 1. now rewrite /v eqb_refl.
  have vy : v y = 0. rewrite /v. case: eqb_spec => //. subst; congruence.
  have hcls : clauses_sem v cls.
  { eapply clauses_sem_singleton. cbn.
    rewrite interp_nes_union !interp_nes_singleton //=.
    rewrite vx vy. cbn. lia. }
  have hcon : consistent cls.
  { exists v. split => //.
    intros l. unfold v. case: eqb_spec => //. }
  destruct check_entails eqn:ec.
  - move/check_entails_entails_looping: ec.
    move/consistent_no_loop. contradiction.
  - exfalso. move/check_invalid_entails: ec.
    apply. apply entails_completeness.
    red. intros.
    move: (H (valid_Z_counterexample_cls x y)) => /fwd.
    now apply Clauses.singleton_spec.
    cbn. rewrite !interp_nes_union !interp_nes_singleton //=.
    rewrite !add_neutral. intros hle.
    eapply (le_add (n := 1)).
    rewrite !add_join !add_distr add_neutral join_comm.
    exact hle.
  - reflexivity.
Qed.

End CounterExample2.

Lemma empty_filter f les :
  LevelExprSet.is_empty (LevelExprSet.filter f les) ->
  forall l, LevelExprSet.In l les -> f l = false.
Proof.
  move/LevelExprSet.is_empty_spec.
  have hs := LevelExprSet.partition_spec2 (f:=f) les. forward hs. tc.
  have hs' := LevelExprSet.partition_spec1 (f:=f) les. forward hs'. tc.
  rewrite -hs'.
  intros he l.
  specialize (hs' l). specialize (hs l).
  destruct (f l) eqn:hl.
  rewrite LevelExprSet.filter_spec in hs'.
  specialize (he l). rewrite hs' in he. intros hin; elim he; split => //.
  auto.
Qed.

Lemma partition_in f les :
  forall lk, LevelExprSet.In lk les <->
    LevelExprSet.In lk (LevelExprSet.partition f les).1 \/
    LevelExprSet.In lk (LevelExprSet.partition f les).2.
Proof.
  intros lk.
  rewrite LevelExprSet.partition_spec1 LevelExprSet.partition_spec2.
  rewrite !LevelExprSet.filter_spec.
  firstorder auto.
  destruct (f lk); firstorder.
Qed.

Lemma is_model_entails_H m cls cls' :
  is_model m cls ->
  cls ⊢ℋ cls' ->
  is_model m cls'.
Proof.
  move=> /[dup] ism. rewrite !is_modelP.
  move=> ha hent cl /hent ent.
  specialize (ha cl).
  eapply entails_model_valid; tea.
Qed.

Lemma is_model_singleton m cl : is_model m (Clauses.singleton cl) <-> valid_clause m cl.
Proof.
  rewrite is_modelP. split.
  * move/(_ cl) => /fwd //. clsets.
  * now move=> hv cl' /Clauses.singleton_spec ->.
Qed.

Definition valid_non_vacuous m cl :=
  exists minp value,
    [/\ min_premise m (premise cl) = Some minp,
       level_value m (concl cl).1 = Some value &
       minp + (concl cl).2 <= value].

Definition is_total_model_alt m cls :=
  forall cl, Clauses.In cl cls -> valid_non_vacuous m cl.

Lemma is_total_model_altP m cls :
  is_total_model m cls <-> is_total_model_alt m cls.
Proof.
  split.
  - move=> -[] en /is_modelP ism.
    move=> [prems [concl k]] /[dup] /en [minp hmin] /ism.
    move/valid_clause_elim/(_ _ hmin).
    move/Some_leq => -[] z' [] hl hleq.
    exists minp, z'. split => //.
  - move=> ism; split.
    * now move=> cl /ism -[] minp [] value [] => //; exists minp.
    * apply/is_modelP => cl /ism -[] minp [] value [] => // hmin hl hle.
      destruct cl as [prems [concl k]].
      apply valid_clause_intro => z hz.
      rewrite hmin in hz. noconf hz.
      rewrite hl; constructor. exact hle.
Qed.

Lemma min_premise_union m prems prems' :
  min_premise m (prems ∨ prems') = min_opt (min_premise m prems) (min_premise m prems').
Proof.
  pattern prems, (min_premise m prems).
  set (P := fun t0 => _).
  revert prems.
  apply: (@min_premise_elim m _ _ _); subst P; cbn.
  - intros le. now rewrite union_comm union_add_singleton min_premise_add.
  - intros prems acc le he hnin.
    rewrite -union_add_singleton (@union_comm prems) union_assoc union_comm union_add_singleton.
    rewrite min_premise_add he.
    now rewrite assoc.
Qed.

Lemma valid_clauses_of_le m prems prems' :
  m ⊨ prems ⋞ prems' ->
  forall min min', min_premise m prems' = Some min ->
    min_premise m prems = Some min' ->
    min <= min'.
Proof.
  revert prems'.
  eapply min_premise_elim.
  - intros [l k] prems'.
    intros hl. specialize (hl (prems', (l, k))).
    forward hl. rewrite clauses_of_le_spec. exists (l, k). split => //.
    now apply singleton_spec. cbn in hl.
    move/valid_clause_elim: hl => hz.
    move=> min min' /hz /Some_leq -[y'] [] /level_value_MapsTo' hl leq hat.
    rewrite (Model.min_atom_value_mapsto hl) in hat. cbn in hat. noconf hat. lia.
  - intros prems' acc le ih hnin prems0 hadd min min' minp minp'.
    move: (ih prems0) => /fwd.
    { move=> cl. rewrite clauses_of_le_spec => -[lk [hin heq]].
      move: (hadd cl) => /fwd //. subst cl. rewrite clauses_of_le_spec.
      exists lk. split => //. eapply LevelExprSet.add_spec; now right. }
    move=>/(_ _ _ minp).
    destruct (min_atom_value m le) eqn:hat => //. destruct acc; noconf minp'.
    2:{ cbn in minp'. destruct acc => //. }
    move/(_ _ eq_refl).
    move: (hadd (prems0, le)) => /fwd.
    { rewrite clauses_of_le_spec. exists le. split => //.
      eapply LevelExprSet.add_spec; now left. }
    destruct le as [le lek]; move/valid_clause_elim/(_ _ minp) => /Some_leq.
    apply min_atom_value_mapsto in hat. rewrite (level_value_MapsTo hat).
    move=> -[y'] [] [=] <-. lia.
Qed.

Lemma total_model m : is_total_model (model m) (clauses m).
Proof.
  split. apply model_enabled. apply model_ok.
Qed.

Lemma entails_clauses_completeness cls cls' :
  cls ⊢ℋ cls' ->
  valid_clauses_Z cls cls'.
Proof.
  rewrite -entails_L_entails_ℋ_equiv.
  rewrite -entails_L_rels_entails_L_clauses.
  rewrite -completeness_all.
  intros vr v vpos csem.
  specialize (vr Z _ v).
  rewrite -!interp_rels_clauses_sem in vr.
  eauto.
Qed.

Lemma total_model_sem {m cls} :
  is_total_model m cls ->
  clauses_sem (Z_valuation_of_model m) cls.
Proof.
  intros [en ism].
  now eapply valid_clauses_model.
Qed.

Lemma inverse_clauses_levels {m cl} :
  clause_levels cl ⊂_lset levels m ->
  clauses_levels (inverse_clauses cl) ⊂_lset levels m.
Proof.
  intros hs. now rewrite clause_levels_inverse.
Qed.

Lemma check_entails_valid_Z m cl :
  check_entailsb (clauses m) cl -> valid_clause_Z (clauses m) cl.
Proof.
  rewrite checkb_entails.
  move=> ent v posv csem.
  apply entails_completeness in ent.
  red in ent.
  now move: {ent}(ent Z _ v csem).
Qed.

Definition consistent_clauses_model cls :=
  exists m, Model.enabled_clauses m cls /\ is_model m cls.

Lemma consistent_model m : consistent_clauses_model (clauses m).
Proof.
  exists (model m). split.
  eapply model_enabled.
  apply model_ok.
Qed.

Lemma check_entails_clauses_gen_spec cls cls' :
  consistent_clauses_model cls ->
  check_entails_clauses cls cls' <-> entails_clauses cls cls'.
Proof.
  intros hcon.
  split.
  - rewrite /check_entails_clauses.
    move/Clauses.for_all_spec => ha cl /ha.
    unfold check_entailsb; destruct check_entails eqn:hc => //.
    now move/check_entails_entails: hc.
  - intros hv.
    rewrite /check_entails_clauses /check_entailsb.
    eapply Clauses.for_all_spec; tc => cl hin.
    destruct check_entails eqn:hc => //.
    * exfalso. destruct hcon as [m [en ism]].
      eapply check_entails_entails_looping in hc; tea.
      eapply model_entails_succ in hc; tea.
    * move/check_invalid_entails: hc => he.
      exfalso. elim he. now apply hv.
Qed.


Equations check_clause_wf m cl (wf : clause_levels cl ⊂_lset levels m) : bool :=
  check_clause_wf m cl wf with enforce_dec m (inverse_clauses cl) (inverse_clauses_levels wf) :=
  | left con => false
  | right incon => true.

Equations? check_clause (m : t) (cl : clause) : option bool :=
  check_clause m cl with inspect (LevelSet.subset (clause_levels cl) (levels m)) :=
    | exist true hl => Some (check_clause_wf m cl _)
    | exist false _ => None.
Proof. apply LevelSet.subset_spec in hl; now apply hl. Qed.

Definition check_clauses m (cls : Clauses.t) : option bool :=
  Clauses.fold (fun cl acc =>
    match acc with
    | None => None
    | Some false => acc
    | Some true => check_clause m cl
    end) cls (Some true).

Lemma check_clause_invalid m cl wf :
  check_clause_wf m cl wf = false -> ~ valid_clause_Z (clauses m) cl.
Proof.
  unfold check_clause_wf.
  destruct (enforce_dec m (inverse_clauses cl)) => //= _.
  intros inv. destruct c as [v [vpos csem]].
  specialize (inv v vpos).
  apply clauses_sem_union in csem as [csem clsem].
  apply inv in csem.
  apply neg_inverse_Z in clsem. contradiction.
Qed.

Lemma check_clause_valid m cl wf :
  check_clause_wf m cl wf -> valid_clause_Z (clauses m) cl.
Proof.
  unfold check_clause_wf.
  destruct (enforce_dec m (inverse_clauses cl)) => //= _ v vpos csem.
  red in i. destruct i as [loop [hincl hloop]].
  have nev : ~ exists v, positive_valuation v /\ clauses_sem v (Clauses.union (clauses m) (inverse_clauses cl)).
  { intros [vz [hpos hv]].
    eapply entails_clauses_completeness in hloop.
    move: (hloop vz) => /fwd //.
    move/(_ hv).
    move/clauses_sem_clauses_of_le; rewrite interp_add_prems. cbn. lia. }
  destruct (clause_sem_Z_dec v cl) => //.
  apply neg_inverse_Z in H.
  elim nev. exists v. split => //.
  apply clauses_sem_union. split => //.
Qed.

Lemma check_clause_wf_spec m cl wf :
  check_clause_wf m cl wf <-> valid_clause_Z (clauses m) cl.
Proof.
  destruct (check_clause_wf m cl) eqn:ec.
  - split => // _.
    now apply check_clause_valid in ec.
  - split => // hv.
    apply check_clause_invalid in ec.
    contradiction.
Qed.

Lemma check_clause_undeclared m cl :
  check_clause m cl = None <-> ~ clause_levels cl ⊂_lset (levels m).
Proof.
  funelim (check_clause m cl) => //.
  - split => //. intros ne; exfalso. clear H Heqcall.
    apply LevelSet.subset_spec in hl. contradiction.
  - split => // _ hincl.
    apply LevelSet.subset_spec in hincl. congruence.
Qed.

Lemma check_clause_spec m cl :
  forall b, check_clause m cl = Some b ->
  b <-> valid_clause_Z (clauses m) cl.
Proof.
  funelim (check_clause m cl) => //.
  clear H Heqcall. intros b [= <-].
   apply check_clause_wf_spec.
Qed.

Inductive reflect_opt (PN PS : Prop) : option bool -> Prop :=
  | ReflectNone : PN -> reflect_opt PN PS None
  | ReflectSomeT : PS -> reflect_opt PN PS (Some true)
  | ReflectSomeF : ~ PS -> reflect_opt PN PS (Some false).
Derive Signature for reflect_opt.

Lemma check_clauseP {m cl} : reflect_opt
  (~ clause_levels cl ⊂_lset (levels m))
  (valid_clause_Z (clauses m) cl)
  (check_clause m cl).
Proof.
  destruct (check_clause m cl) as [b|] eqn:ec.
  - apply check_clause_spec in ec.
    destruct b; constructor; try apply ec => //.
    destruct ec. now move/H0.
  - constructor. now apply check_clause_undeclared.
Qed.

Definition valid_clauses cls cls' :=
  forall v : Level.t -> Z,
    positive_valuation v ->
    clauses_sem v cls -> clauses_sem v cls'.

Lemma check_clausesP {m cls} : reflect_opt
  (~ clauses_levels cls ⊂_lset (levels m))
  (valid_clauses (clauses m) cls)
  (check_clauses m cls).
Proof.
  unfold check_clauses.
  eapply ClausesProp.fold_rec.
  - intros s' he. constructor.
    now move=> v vpos csem cl /he.
  - intros x a s' s'' hin hnin hadd ih.
    destruct a => //.
    depelim ih.
    * elim: (@check_clauseP m x).
      { move=> hdecl. constructor => hincl.
        apply hdecl. rewrite -hincl.
        red in hadd.
        have hcl := clauses_levels_mon (Clauses.singleton x) s''.
        rewrite -hcl => l. rewrite hadd.
        rewrite Clauses.singleton_spec. intros; now left.
        rewrite clauses_levels_spec => hin'. exists x; split => //. clsets. }
      { move=> hv. constructor. intros v vpos csem.
        specialize (H v vpos csem).
        specialize (hv v vpos csem).
        move=> cl /hadd -[].
        now intros ->. apply H. }
      { move=> hv. constructor. intros inv.
        apply hv => v vpos csem. apply (inv v vpos csem x).
        apply hadd. now left. }
    * constructor. intros inv.
      apply H => v vpos csem. specialize (inv v vpos csem).
      move=> cl hin'. specialize (hadd cl).
      destruct hadd. forward H1. now right.
      now apply inv.
    * constructor. depelim ih.
      move=> hincl. apply H.
      rewrite -hincl.
      eapply clauses_levels_mon.
      intros cl; rewrite (hadd cl).
      now right.
Qed.

Definition check_entails_model_clauses m cls :=
  check_entails_clauses (clauses m) cls.

Lemma check_entails_model_clauses_entails m cls :
  check_entails_model_clauses m cls <-> entails_clauses (clauses m) cls.
Proof.
  rewrite check_entails_clauses_gen_spec //.
  apply consistent_model.
Qed.


Equations? check_clauses_wf m cls (wf : clauses_levels cls ⊂_lset levels m) : bool :=
  check_clauses_wf m cls wf with inspect (check_clauses m cls) :=
    | exist None heq := False_rect _ _
    | exist (Some b) heq => b.
Proof.
  move: heq; elim: check_clausesP => //.
Qed.

Lemma check_clauses_spec m cls (wf : clauses_levels cls ⊂_lset (levels m)) :
  check_clauses_wf m cls wf <-> valid_clauses_Z (clauses m) cls.
Proof.
  funelim (check_clauses_wf m cls wf) => //.
  clear H Heqcall.
  move: heq; elim: check_clausesP => //.
  - intros vc [= <-]. split => //.
  - intros inv [= <-]. split => //.
  - bang.
Qed.

Theorem check_entailsb_spec m cl :
  check_entailsb (clauses m) cl -> valid_clause_Z (clauses m) cl.
Proof.
  apply check_entails_valid_Z.
Qed.

Definition valid_clauses_inf cls cls' :=
  forall v : Level.t -> option Z,
    positive_opt_valuation v ->
    clauses_sem v cls -> clauses_sem v cls'.

Lemma check_entails_clauses_complete m cls :
  check_entails_model_clauses m cls <-> valid_entailments (clauses m) cls.
Proof.
  rewrite check_entails_model_clauses_entails.
  rewrite -entails_L_entails_ℋ_equiv.
  rewrite -entails_L_rels_entails_L_clauses.
  rewrite -completeness_all.
  split.
  - move=> vr s sl v.
    move: (vr _ sl v).
    rewrite !interp_rels_clauses_sem //.
  - intros ve S s v.
    move: (ve S s v).
    now rewrite //= !interp_rels_clauses_sem.
Qed.

Lemma check_entails_clauses_Z_positive_complete m cls :
  check_entails_model_clauses m cls <-> valid_clauses_inf (clauses m) cls.
Proof.
  split.
  - rewrite check_entails_model_clauses_entails.
    rewrite -entails_L_entails_ℋ_equiv.
    rewrite -entails_L_rels_entails_L_clauses.
    rewrite -completeness_all.
    move=> vr v.
    red in vr.
    move: (vr (option Z) Zopt_semi v).
    rewrite !interp_rels_clauses_sem //.
  - intros sem. unfold check_entails_model_clauses.
    eapply Clauses.for_all_spec. tc.
    move=> cl /sem => semcl.
    unfold check_entailsb.
    destruct check_entails eqn:hc => //.
    * move/check_entails_entails_looping : hc.
      rewrite -to_entails_all.
      rewrite -entails_L_entails_ℋ_equiv.
      rewrite -entails_L_rels_entails_L_clauses.
      rewrite -ISL.completeness_all.
      move/(_ Z _ (Z_valuation_of_model m)).
      rewrite -interp_rels_clauses_sem.
      move/(_ (model_valuation m)).
      rewrite -interp_rels_clauses_sem.
      rewrite clauses_sem_leq. cbn.
      rewrite interp_add_prems //=. lia.
    * move/check_invalid_valuation: hc.
      move=> [hpos semcls def ncl]. specialize (semcl _ hpos semcls).
      now elim ncl.
Qed.

Lemma check_entails_clauses_Z_complete m cls :
  check_entails_model_clauses m cls <-> valid_semilattice_entailments Zopt_semi (clauses m) cls.
Proof.
  split.
  - rewrite check_entails_model_clauses_entails.
    rewrite -entails_L_entails_ℋ_equiv.
    rewrite -entails_L_rels_entails_L_clauses.
    rewrite -completeness_all.
    move=> vr v.
    red in vr.
    move: (vr (option Z) Zopt_semi v).
    rewrite !interp_rels_clauses_sem //.
  - intros sem. unfold check_entails_model_clauses, check_entails_clauses.
    eapply Clauses.for_all_spec. tc.
    move=> cl /sem => semcl.
    unfold check_entailsb; destruct check_entails eqn:hc => //.
    * move/check_entails_entails_looping : hc.
      rewrite -to_entails_all.
      rewrite -entails_L_entails_ℋ_equiv.
      rewrite -entails_L_rels_entails_L_clauses.
      rewrite -ISL.completeness_all.
      move/(_ Z _ (Z_valuation_of_model m)).
      rewrite -interp_rels_clauses_sem.
      move/(_ (model_valuation m)).
      rewrite -interp_rels_clauses_sem.
      rewrite clauses_sem_leq. cbn.
      rewrite interp_add_prems //=. lia.
    * move/check_invalid_valuation: hc.
      move=> [_ semcls def ncl]. specialize (semcl (opt_valuation_of_model m0)). elim ncl; now apply semcl.
Qed.

Definition pred (le : LevelExpr.t) := (le.1, le.2 - 1).

Lemma nRopt {A} (x y : A) : ~ R_opt Logic.eq (Some x) (Some y) -> x <> y.
Proof.
  intros hr heq. apply hr. now cbn.
Qed.

End Abstract.
End Deciders.

Module LoopChecking (LS : LevelSets).
  Module Impl := Deciders(LS).
  Import Impl.CorrectModel.
  Import Impl.I.
  Import Impl.Abstract.

  Definition t := t.

  Definition model (x : t) : Model.model := model x.

  Definition levels (x : t) := levels x.
  Definition clauses (x : t) := clauses x.
  Definition valuation (x : t) := valuation x.

  Lemma clauses_levels_declared m : clauses_levels (clauses m) ⊂_lset levels m.
  Proof.
    apply clauses_levels_declared.
  Qed.

  Notation univ := NES.t.

  Import UnivConstraintType.ConstraintType (Le, Eq).

  Definition constraint := (univ * UnivConstraintType.ConstraintType.t * univ).

  Local Definition to_clauses (cstr : constraint) : Clauses.t :=
    let '(l, d, r) := cstr in
    match d with
    | Le => clauses_of_le l r
    | Eq => clauses_of_eq l r
    end.

  Lemma to_clauses_spec l d r :
    forall cl, Clauses.In cl (to_clauses (l, d, r)) <->
    match d with
    | Le => LevelExprSet.Exists (fun lk => cl = (r, lk)) l
    | Eq => LevelExprSet.Exists (fun lk => cl = (r, lk)) l \/ LevelExprSet.Exists (fun rk => cl = (l, rk)) r
    end.
  Proof.
    intros cl. destruct d => //=.
    - apply clauses_of_le_spec.
    - rewrite /clauses_of_eq Clauses.union_spec.
      have := clauses_of_le_spec l r cl.
      have := clauses_of_le_spec r l cl.
      firstorder.
  Qed.

  Lemma zero_declared_in_levels m : LevelSet.In Level.zero (levels m).
  Proof.
    have [k hm] := zero_declared m.
    apply model_levels. eexists; tea.
  Qed.

  Lemma declared_init_clauses {m} : forall l,
    LevelSet.In l (levels m) <->
    l = Level.zero \/ Clauses.In (Impl.init_clause_of_level l) (clauses m).
  Proof.
    move=> l.
    move: (above_zero_declared m l).
    rewrite /Impl.declared_init_clause_of_level /Impl.init_clause_of_level => ab.
    split.
    - move: ab; case: (eqb_spec l Level.zero) => //.
      * now left.
      * move=> eq hin.
        right. destruct Level.is_global eqn:isg => //.
        apply (hin H).
        apply (hin H).
    - move=> [h|h].
      * subst l. apply zero_declared_in_levels.
      * apply (clauses_levels_declared m).
        apply clauses_levels_spec. eexists; split; tea. cbn.
        apply clause_levels_spec. left. cbn.
        apply levels_spec. exists 0%Z. now apply LevelExprSet.singleton_spec.
  Qed.

  Definition init_model := Impl.Abstract.init_model.

  (* Returns None if already declared *)
  Definition declare_level := Impl.Abstract.declare_level.

  Lemma declare_level_levels {m l m'} :
    declare_level m l = Some m' -> ~ LevelSet.In l (levels m) /\ levels m' =_lset LevelSet.add l (levels m).
  Proof. apply declare_level_levels. Qed.

  Lemma declare_level_None {m l} :
    declare_level m l = None <-> LevelSet.In l (levels m).
  Proof. apply declare_level_None. Qed.

  Lemma declare_level_clauses l m m' : declare_level m l = Some m' ->
    Impl.Abstract.clauses m' = Clauses.add (Impl.init_clause_of_level l) (Impl.Abstract.clauses m).
  Proof. apply declare_level_clauses. Qed.

  Definition loop (m : t) c := Impl.CorrectModel.loop (Clauses.union (clauses m) (to_clauses c)).

  (* Returns either a model or a looping universe, i.e. such that u >= u + 1 is implied
     by the constraint *)
  Definition enforce (m : t) c : option (t + loop m c) :=
    enforce_clauses m (to_clauses c).

  Lemma enforce_None {m cls} :
    enforce m cls = None <-> ~ LevelSet.Subset (clauses_levels (to_clauses cls)) (levels m).
  Proof.
    apply enforce_clauses_None.
  Qed.

  Lemma enforce_not_None {m cls} :
    enforce m cls <> None <-> LevelSet.Subset (clauses_levels (to_clauses cls)) (levels m).
  Proof.
    apply enforce_clauses_not_None.
  Qed.

  Import Semilattice.
  Lemma enforce_inconsistent_semilattice {m cls u} :
    enforce m cls = Some (inr u) ->
    forall S (SL : Semilattice.Semilattice S Q.t) (V : Level.t -> S), clauses_sem V (Clauses.union (clauses m) (to_clauses cls)) ->
       clauses_sem V (Impl.CorrectModel.loop_univ u ≡ succ (Impl.CorrectModel.loop_univ u)).
  Proof.
    rewrite /enforce.
    now move/enforce_clauses_inconsistent_semilattice.
  Qed.

  Lemma enforce_inconsistent {m cls u} :
    enforce m cls = Some (inr u) ->
    inconsistent_ext_Z m (to_clauses cls).
  Proof.
    move/enforce_clauses_inconsistent.
    intros incon v vpos clssem csem.
    apply incon. red. exists v. split => //.
    apply clauses_sem_union. split => //.
  Qed.

  Lemma enforce_clauses {m cls m'} :
    enforce m cls = Some (inl m') ->
    clauses m' = Clauses.union (clauses m) (to_clauses cls).
  Proof.
    apply enforce_clauses_clauses.
  Qed.

  Lemma enforce_levels m cls m' :
    enforce m cls = Some (inl m') ->
    levels m' = levels m.
  Proof. apply enforce_clauses_levels. Qed.

  Definition valid_entailments cls cls' :=
    forall S (SL : Semilattice.Semilattice S Q.t) (V : Level.t -> S), clauses_sem V cls -> clauses_sem V cls'.

  Definition check_wf m cls (wf : clauses_levels cls ⊂_lset levels m) :=
    check_clauses_wf m cls wf.

  Lemma check_wfP m c wf : check_wf m c wf <-> valid_clauses_Z (clauses m) c.
  Proof.
    apply check_clauses_spec.
  Qed.

  Definition check m cls :=
    match check_clauses m cls with
    | None => false
    | Some b => b
    end.

  Lemma check_spec m cls :
    clauses_levels cls ⊂_lset levels m ->
    check m cls <-> valid_clauses_Z (clauses m) cls.
  Proof.
    intros hwf.
    rewrite /check.
    elim: check_clausesP; intuition.
  Qed.

  Definition check_constraint m c := check m (to_clauses c).

  Lemma check_constraintS m c :
    clauses_levels (to_clauses c) ⊂_lset levels m ->
    check_constraint m c <-> valid_clauses_Z (clauses m) (to_clauses c).
  Proof.
    apply check_spec.
  Qed.

  (** Entailment is weaker than validity in Z: it is equivalent to validity in Z^∞ *)

  (* Returns true is the constraint is valid in the model and all its possible consistent extensions.
     Returns false if the constraint results in an inconsistent set of constraints or it simply
     is not valid. *)
  Definition check_entails m c :=
    check_entails_model_clauses m (to_clauses c).

  (* Checking corresponds to entailment in the free semilattice *)
  Lemma check_entails_spec {m c} :
    check_entails m c <-> entails_clauses (clauses m) (to_clauses c).
  Proof. apply check_entails_model_clauses_entails. Qed.

  (* Checking corresponds to validity in *all* semilattices, including degenerate ones. *)
  Lemma check_entails_complete m c :
    check_entails m c <-> valid_entailments (clauses m) (to_clauses c).
  Proof. apply check_entails_clauses_complete. Qed.

  (* Checking corresponds to validity in the Z^∞ semilattice. *)
  Lemma check_entails_Z_complete m c :
    check_entails m c <-> valid_semilattice_entailments Zopt_semi (clauses m) (to_clauses c).
  Proof. apply check_entails_clauses_Z_complete. Qed.

  Lemma check_Z_complete_positive m c :
    check_entails m c <-> valid_clauses_inf (clauses m) (to_clauses c).
  Proof. apply check_entails_clauses_Z_positive_complete. Qed.

  Lemma zero_declared m : Impl.zero_declared (model m).
  Proof. eapply zero_declared. Qed.

  Lemma above_zero_declared m : Impl.above_zero_declared (levels m) (clauses m).
  Proof. eapply above_zero_declared. Qed.

  Definition model_valuation m : clauses_sem (to_Z_val (valuation m)) (clauses m).
  Proof.
    apply model_valuation.
  Qed.

  Lemma model_valuation_zero m : valuation m Level.zero = 0%nat.
  Proof. apply valuation_0. Qed.

  Lemma model_valuation_global {m l} : LevelSet.In l (levels m) -> Level.is_global l -> (valuation m l > 0)%nat.
  Proof. apply valuation_global. Qed.

  Lemma model_valuation_not_global {m l} : LevelSet.In l (levels m) -> ~~ Level.is_global l -> (valuation m l >= 0)%nat.
  Proof. apply valuation_not_global. Qed.

End LoopChecking.
