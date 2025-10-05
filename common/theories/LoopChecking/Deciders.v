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
  enabled_clauses m cls /\ is_model cls m.


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
  | inr u => ~ exists m, defined_model_of (levels u) m /\ is_model cls m
  end.

Definition valid_clauses m cls := Clauses.For_all (valid_clause m) cls.
Infix "⊨" := valid_clauses (at level 90).

Lemma is_model_valid {cls m} : is_model cls m <-> m ⊨ cls.
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

Program Definition loop_check cls (cl : clause) : result (premises_model (clauses_levels cls) cl).1 LevelSet.empty cls (premises_model (clauses_levels cls) cl).2 :=
  let V := clauses_levels cls in
  loop (premises_model V cl).1 LevelSet.empty cls (premises_model V cl).2 (premises_model V cl).2 _.
Next Obligation.
  split => //.
  - lsets.
  - intros l. rewrite LevelSet.union_spec.
    rewrite -/(LevelMap.In l (premises_model (clauses_levels cls) cl).2).
    rewrite in_premises_model. intuition auto.
  - apply is_update_of_empty.
Qed.

Variant check_result {cls} :=
  | IsLooping (v : premises) (hincl : NES.levels v ⊂_lset clauses_levels cls) (islooping : loop_on_univ cls v)
  | Invalid
  | Valid.
Arguments check_result : clear implicits.

Lemma valid_model_find {V W cl cls} :
  forall v : valid_model (clause_levels cl ∪ V) W (premises_model_map (zero_model (clause_levels cl ∪ V)) (Clauses.singleton cl)) cls,
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

Equations check_gen (cls : clauses) (cl : clause) : check_result cls :=
check_gen cls cl with inspect (loop_check cls cl) :=
  { | exist (Loop v _ isl) he => IsLooping v _ isl
    | exist (Model W v _) he with inspect (LevelMap.find (concl cl).1 v.(model_model)) := {
      | exist (Some val) he' with check_atom_value (Some (concl cl).2) val :=
        { | true => Valid
          | false => Invalid }
      | exist None he' with valid_model_find v he' := {}
    }
  }.

(* If a clause checks, then it is entailed (and will be valid in any extension of the model) *)
Theorem check_gen_entails {cls cl} :
  check_gen cls cl = Valid -> entails cls cl.
Proof.
  destruct cl as [prems [concl k]].
  funelim (check_gen cls _) => // _.
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


Lemma check_gen_entails_looping {cls cl v vcls isl} :
  check_gen cls cl = IsLooping v vcls isl -> cls ⊢a v → succ_prems v.
Proof.
  funelim (check_gen cls cl) => //.
Qed.

Lemma check_looping {cls cl v vcls isl} :
  check_gen cls cl = IsLooping v vcls isl ->
  ~ (exists m, defined_model_of (levels v) m /\ is_model cls m).
Proof.
  move/check_gen_entails_looping.
  intros loop [m' [en clssem]].
  apply to_entails_all in loop.
  apply is_model_valid in clssem.
  have hv := entails_all_model_valid clssem loop.
  eapply loop_invalid in hv; tea.
  now apply enabled_clauses_le.
Qed.

Lemma check_valid_looping {cls cl m v vcls isl} :
  is_model cls m ->
  check_gen cls cl = IsLooping v vcls isl ->
  defined_model_of (levels v) m -> False.
Proof.
  move=> ism.
  move/check_looping => ex hdef. apply ex.
  exists m. split => //.
Qed.

Lemma model_entails_succ cls m v :
  is_model cls m ->
  enabled_clauses m cls ->
  cls ⊢a v → succ v -> False.
Proof.
  move=> mok en.
  move/to_entails_all/entails_L_entails_ℋ_equiv.
  move/entails_L_rels_entails_L_clauses/completeness_all.
  move/(_ Z _ (Z_valuation_of_model m)).
  rewrite -!interp_rels_clauses_sem => /fwd.
  cbn in *.
  eapply valid_clauses_model => //.
  move/clauses_sem_leq.
  rewrite interp_add_prems. cbn. lia.
Qed.

Theorem check_invalid {cls cl} :
  check_gen cls cl = Invalid -> exists m, [/\ is_model cls m, enabled_clause m cl & ~ valid_clause m cl].
Proof.
  funelim (check_gen cls cl) => //.
  clear H H0 he.
  set (V := (clause_levels cl ∪ clauses_levels cls)%levels) in *.
  destruct cl as [prems [concl k]].
  rename val into conclval_v => _.
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
  exists (model_model v).
  have en : enabled_clause (model_model v) cl.
  { apply (@enabled_clause_ext pm).
    exact: is_update_of_ext (model_updates v).
    red; cbn.
    have hcl : Clauses.In cl (Clauses.singleton cl).
    { now eapply Clauses.singleton_spec. }
    have hs:= @premises_model_map_min_premise_inv V _ _ hcl. firstorder. }
  split => //.
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
    have hmin := @premises_model_map_min_premise_inv V (Clauses.singleton cl) cl.
    forward hmin. now apply Clauses.singleton_spec.
    destruct hmin as [minp' [hmineq hpos]].
    rewrite hmineq in hs. depelim hs. lia. }
  lia.
Qed.

Lemma check_invalid_entails {cls cl} :
  check_gen cls cl = Invalid -> ~ entails cls cl.
Proof.
  move/check_invalid => [m [ism en nv]].
  now move/entails_model_valid/(_ m ism).
Qed.

(* For checking to satisfy injectivity rules,
  we force the conclusion to be defined by adding it to the premises.
  In injective semilattices, we can then remove it.
 *)

Definition pred_expr (le : LevelExpr.t) :=
  (le.1, le.2 - 1).

Definition checking_clause (cl : clause) :=
  let (prems, concl) := cl in
  (singleton (pred_expr concl) ∪ prems, concl).

Definition check_clause cls cl :=
  check_gen cls (checking_clause cl).

Definition valid_clause_Z cls cl :=
  forall v : Level.t -> Z,
  positive_valuation v ->
  clauses_sem v cls -> clause_sem v cl.

Lemma check_clause_valid_Z cls cl :
  check_clause cls cl = Valid -> valid_clause_Z cls cl.
Proof.
  unfold check_clause.
  move/check_gen_entails.
  move=> ent v posv csem.
  apply entails_completeness in ent.
  move: {ent}(ent Z _ v csem).
  destruct cl as [prems [concl k]].
  rewrite //= !interp_nes_union interp_nes_singleton //= /interp_expr //=.
  lia.
Qed.

  Import Semilattice.
  Import ISL.

(* Lemma elim_pred {cls prems concl} :
  entails cls (union prems (singleton (pred concl)), concl) ->
  entails cls (prems, concl) \/ entails cls (singleton (pred concl), concl).
Proof.
  Search entails.
  set (SL := init_model (relations_of_clauses cls)).
  rewrite -!entails_all_singleton.
  rewrite -!to_entails_all.
  rewrite -!entails_L_entails_ℋ_equiv.
  rewrite -!entails_L_rels_entails_L_clauses.
  rewrite !entails_L_relations_of_clauses_le.
  rewrite !entails_L_all_tip.
  change (le (singleton concl) (prems ∨ singleton (pred concl)) ->
    (le (singleton concl) (prems) \/
     le (singleton concl) (singleton (pred concl)))). *)

(*
Lemma check_complete {cls cl} :
  checkb cls cl <-> valid_semilattice_entailment cls cl.
Proof.
  unfold checkb.
  destruct check eqn:ec.
  - split => //.
    intros vs. red in vs.
    move/check_entails_looping: ec.
    rewrite -to_entails_all.
    move/entails_ℋ_entails_L.
    move/entails_L_rels_entails_L_clauses.
    rewrite -completeness_all.
    intros vr. red in vr.
    red in islooping. specialize (vr Z _ (valuation_of_model m)) *)



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


Equations? infer_extension {V W init cls} (m : valid_model V W init cls)
  (hincl : only_model_of V init)
  (hs : clauses_levels cls ⊂_lset V)
  (cls' : clauses) :
  result (LevelSet.union (clauses_levels cls') V) LevelSet.empty (Clauses.union cls cls') (min_model_map m.(model_model) cls') :=
  infer_extension m hincl hs cls' :=
    infer_model_extension (LevelSet.union (clauses_levels cls') V) (min_model_map m.(model_model) cls') cls cls' _.
Proof.
  repeat split.
  - lsets.
  - lsets.
  - have ms := min_model_map_spec cls' (model_model m).
    set (map := min_model_map _ _) in *.
    destruct ms as [hm [hcls hext]].
    rewrite LevelSet.union_spec => [] [].
    * move/clauses_levels_spec.
      intros [cl [hin ink]].
      now move: hcls => /(_ _ hin _ ink).
    * move/(model_of_V m k).
      move=> [] x /hext. firstorder.
  - have ms := min_model_map_spec cls' (model_model m).
    set (map := min_model_map _ _) in *.
    destruct ms as [hm [hcls hext]].
    rewrite LevelSet.union_spec.
    move=> [] v /hm [] [[cl [incl inclv]]|hm'] ihcls mmap.
    * left.
      red in inclv. eapply clauses_levels_spec.
      exists cl. split => //. eapply clause_levels_spec.
      destruct inclv as [[? []]|].
      + left. eapply levels_spec. now eexists.
      + right. intuition.
    * have [_ ho] := valid_model_only_model _ _ _ _ m hincl k.
      forward ho by now exists v. now right.
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
    model_valid : valid_model V model_updates initial_model cls }.
  Arguments t : clear implicits.

  Definition model_of {V cls} (x : t V cls) := x.(model_valid).(model_model).
  Coercion model_of : t >-> model.

  Lemma is_model_of {V cls} (x : t V cls) : is_model cls (model_of x).
  Proof. apply x.(model_valid). Qed.

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

  (* Lemma zero_is_max {V cls} (x : t V cls) :
    level_value (model_of x) Level.zero = Some (model_max (model_of x)).
  Proof.
    intros hl.
    have ha : forall l, (level_value (model_of x) l ≤ level_value (model_of x) Level.zero)%opt.
    { todo "semi". }
    have hmax := model_max_spec.
    have hmax' := model_max_spec2.
    Print model_max.

 *)


  Equations? init_model : t (LevelSet.singleton Level.zero) Clauses.empty :=
  init_model := {|
      initial_model := LevelMap.add Level.zero (Some 1) (LevelMap.empty _);
      only_model_of_V := _;
      model_updates := LevelSet.empty; |}.
  Proof.
    - exists 0%nat. rsets. left; auto.
    - exists 1%nat. rsets.
    - rsets. red. now rewrite eqb_refl.
    - clsets.
    - rsets. split.
      * intros ->. exists (Some 1). rsets. now left.
      * move=> [] k'. rsets. destruct p; intuition auto.
    - lsets.
    - refine {| model_model := LevelMap.add Level.zero (Some 1) (LevelMap.empty _) |}.
      * red. rsets. exists (Some 1). rsets; firstorder.
      * red. now rsets.
      * now rsets.
      * rewrite /is_model. eapply Clauses.for_all_spec. tc. now rsets.
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
  infer_extension_correct m enabled hincl hs cls' hs' hdeclz hdecla hdeclp with infer_extension m hincl hs cls' :=
    | Loop u vcls isl => inr {| loop_univ := u; loop_on_univ := isl |}
    | Model w m' _ =>
      inl {|
        initial_model := min_model_map m.(model_model) cls';
        only_model_of_V := _;
        model_updates := w; clauses_declared := _;
        model_valid := {| model_model := m'.(model_model) |} |}.
  Proof.
    - have [_ [_ hm]] := min_model_map_spec cls' (model_model m).
      have mupd := I.model_updates m. eapply is_update_of_ext in mupd.
      assert (hr := transitivity mupd hm).
      eapply zero_declared_ext; tea.
    - move=> l inv.
      have [_ [_ hm]] := min_model_map_spec cls' (model_model m).
      have mupd := I.model_updates m. eapply is_update_of_ext in mupd.
      assert (hr := transitivity mupd hm).
      eapply declared_pos_ext; tea.
    - eapply min_model_map_enabled.
      eapply enabled_clauses_ext.
      have mupd := I.model_updates m. eapply is_update_of_ext in mupd. exact mupd.
      exact enabled.
    - have := valid_model_only_model _ _ _ _ m hincl.
      now apply only_model_of_min_model_map.
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

  Lemma model_max {V cls} {m : t V cls}: forall l k, LevelMap.MapsTo l (Some k) (model_of m) ->
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
    move/model_max: hm'. rewrite (level_value_MapsTo hzero) => hle; depelim hle.
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
    is_model clauses m ->
    is_model clauses (LevelMap.add l k m).
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

  Equations? declare_level (m : t) (l : Level.t) : option t :=
  declare_level m l with inspect (LevelSet.mem l m.(levels)) :=
    | exist true _ => None
    | exist false hneq => Some {| levels := LevelSet.add l m.(levels); clauses := Clauses.add (init_clause_of_level l) m.(clauses) |}.
  Proof.
    refine {| initial_model := LevelMap.add l (Some (if Level.is_global l then 0 else 1)) m.(initial_model);
      only_model_of_V := _;
      model_updates := m.(model_updates); |}.
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
      destruct vm as [init zerod azerod dpos en omofV W incl vm].
      destruct vm as [M mofV mupd mcls mok]. cbn in *.
      refine {| model_model := LevelMap.add l (Some (if Level.is_global l then 0 else 1)) M |}.
      * intros k. rewrite LevelSet.add_spec LevelMapFact.F.add_in_iff. firstorder. now left.
      * move: mupd; rewrite /is_update_of.
        destruct (LevelSet.is_empty) eqn:hw.
        { now intros ->. }
        { eapply levelset_not_Empty_is_empty in hw.
          apply LevelSetFact.not_mem_iff in hneq.
          intros s. eapply strictly_updates_weaken; revgoals.
          now eapply strictly_updates_add. now clsets. }
      * rewrite clauses_conclusions_add. cbn. rsets. destruct H; subst.
        + right. apply omofV. now apply zero_declared_in.
        + right; lsets.
      * apply LevelSetFact.not_mem_iff in hneq.
        rewrite ClausesProp.add_union_singleton is_model_union //.
        rewrite is_model_valid.
        intros cl; rsets. subst cl.
        rewrite /init_clause_of_level.
        rewrite /valid_clause. cbn. rewrite min_premise_singleton //=.
        rewrite level_value_add /level_value_above.
        set value := Some _.
        have hl : (Some 1 ≤ level_value (LevelMap.add l value M) Level.zero)%opt.
        { rewrite level_value_add_other. intros ->. apply hneq.
          { now apply omofV, zero_declared_in. }
          eapply is_update_of_ext in mupd.
          eapply zero_declared_ext in zerod; tea.
          destruct zerod as [k hzero]. rewrite (level_value_MapsTo hzero).
          subst value. constructor. lia. }
        depelim hl. rewrite H0.
        apply Z.leb_le. cbn. destruct Level.is_global; lia.
        apply is_model_add => //. lsets => //.
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
    (* enables_clauses val cls /\  *)
    clauses_sem val cls.

  Definition consistent_opt cls :=
    exists val : Level.t -> option Z, consistent_opt_val val cls.

  Definition consistent cls :=
    exists val : Level.t -> Z, positive_valuation val /\ clauses_sem val cls.

  (*
Lemma opt_valuation_of_model_equiv m l :
    option_get 0%Z (opt_valuation_of_model m l) = valuation_of_model m l.
  Proof.
    rewrite /opt_valuation_of_model /to_Z_val /to_val.
    case: find_spec.
    * move=> k hm.
      destruct k => //.
      have he := valuation_of_model_spec m l _ hm.
      apply LevelMap.find_1 in he. rewrite he. todo "bounds".
      apply LevelMap.find_1 in hm. cbn. todo "zero".
    * move=> hnin. cbn. todo "zero".
  Qed. *)

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

  Lemma opt_valuation_enables m : enables_clauses (opt_valuation m) (clauses m).
  Proof.
    have hen := enabled_model m.
    have hupd := I.model_updates m.(model_valid).
    eapply is_update_of_ext in hupd.
    eapply enabled_clauses_ext in hen; tea.
    move: hen.
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
    forall v : Level.t -> option Z,
      defined_valuation_of (clauses_levels cls) v ->
      clauses_sem v (Clauses.union (clauses m) cls) -> False.


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

  Lemma enforce_clauses_inconsistent_opt {m cls u} :
    enforce_clauses m cls = Some (inr u) ->
    inconsistent_opt_ext m cls.
  Proof.
    intros ec. red. intros v def csem.
    move/enforce_clauses_inconsistent_semilattice: ec => /(_ (option Z) _ v csem).
    rewrite clauses_sem_eq //= interp_add_prems //=.
    destruct u as [loop incl hl]. cbn.
    destruct interp_nes eqn:hi => //=. lia.
    red in def.
    todo "scoping".
  Qed.

  Lemma enforce_clauses_inconsistent {m cls u} :
    enforce_clauses m cls = Some (inr u) ->
    inconsistent (Clauses.union (clauses m) cls).
  Proof.
    move/enforce_clauses_inconsistent_semilattice => ec [v [posv cs]].
    move: (ec Z _ v cs).
    rewrite clauses_sem_eq //= interp_add_prems //=. lia.
  Qed.

  Definition inconsistent_clause_ext m cl :=
    forall v : Level.t -> Z, positive_valuation v -> clauses_sem v (clauses m) -> ~ clause_sem v cl.

  Definition inconsistent_ext m cls :=
    forall v : Level.t -> option Z, positive_opt_valuation v -> clauses_sem v (clauses m) -> ~ clauses_sem v cls.

  Lemma enforce_dec m cls :
    clauses_levels cls ⊂_lset levels m ->
    { consistent (Clauses.union (clauses m) cls) } +
    { inconsistent_opt_ext m cls }.
  Proof.
    intros hm.
    destruct (enforce_clauses m cls) eqn:ec.
    destruct s as [model|loop].
    - left. move/enforce_clauses_clauses: ec.
      intros <-. apply clauses_consistent.
    - right. now move/enforce_clauses_inconsistent_opt: ec.
      (* intros he v semcs semc. red in he.
      specialize (he )
       apply he. red. exists v. split => //.
      apply clauses_sem_union. split => //. *)
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
    clauses_sem (opt_valuation_of_model model) cls <-> is_model cls model.
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
    clauses_sem (Z_valuation_of_model model) cls <-> is_model cls model.
  Proof.
    intros def. rewrite clauses_sem_def_equiv //.
    apply clauses_sem_valid.
  Qed.

  Definition clause_premises_levels cl := NES.levels (premise cl).

  Theorem check_invalid_valuation {cls cl} :
    check_gen cls cl = Invalid ->
    exists v : Level.t -> option Z,
    [/\ positive_opt_valuation v, clauses_sem v cls,
      defined_valuation_of (clause_premises_levels cl) v & ~ clause_sem v cl].
  Proof.
    move/check_invalid=> [m' [ism en inval]].
    have hpos := opt_valuation_of_model_pos.
    have semcls := valid_clauses_model_opt _ _ ism.
    exists (opt_valuation_of_model m'). split => //.
    { intros l.
      move: en; rewrite /enabled_clause => -[z hmin].
      eapply min_premise_spec_aux in hmin as [hf _].
      rewrite /clause_premises_levels NES.levels_spec.
      move=> [] k /hf. intros le; depelim le. move: H0.
      rewrite /opt_valuation_of_model /level_value.
      case: (find_spec l m') => //; destruct k0 => //.
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


  Lemma defined_model (m : t) : defined_model_of (levels m) (model_of m).
  Proof.
    intros l hin.
    have [k hm] := declared_pos_model_of m l hin.
    now exists (Z.of_nat k).
  Qed.

  Definition declared_clauses_levels V cls := LevelSet.Subset (clauses_levels cls) V.

  Lemma defined_model_of_subset {V V' m} : LevelSet.Subset V V' -> defined_model_of V' m -> defined_model_of V m.
  Proof.
    now move=> sub def l /sub /def.
  Qed.

  Lemma entails_dec (m : t) cl :
    { entails (clauses m) cl } + { ~ entails (clauses m) cl /\
      exists v : Level.t -> option Z,
      [/\ positive_opt_valuation v, clauses_sem v (clauses m), defined_valuation_of (clause_premises_levels cl) v & ~ clause_sem v cl] }.
  Proof.
    destruct (check_gen (clauses m) cl) eqn:ch.
    - move/check_looping: ch; elim.
      exists (model_of m). split.
      { have dm := defined_model m.
        eapply defined_model_of_subset; tea.
        eapply defined_model_of_subset; tea.
        apply clauses_levels_declared. }
      exact: is_model_of m.
    - have ci := check_invalid_valuation ch.
      move/check_invalid_entails: ch. intros ne. right. split => //.
    - move/check_gen_entails: ch. now left.
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

  Definition inverse_clauses (cl : clause) :=
    let (prems, concl) := cl in
    clauses_of_le (succ_prems prems) (singleton concl).

  Lemma clauses_sem_subset {S} {SL : Semilattice.Semilattice S Q.t} {v : Level.t -> S} {cls cls'} : clauses_sem v cls -> cls' ⊂_clset cls -> clauses_sem v cls'.
  Proof.
    now move=> hall hsub cl /hsub.
  Qed.

  Import Semilattice.

  Lemma clauses_sem_clauses_of_le (V : Level.t -> Z) l r :
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
      cbn. lia.
    - intros le x ih hnin ih'.
      rewrite interp_nes_add.
      forward ih. intros x0 [x1 [hin ->]].
      move: (ih' (r, x1)) => /fwd. exists x1. split => //. apply LevelExprSet.add_spec. now right.
      auto.
      move: (ih' (r, le)) => /fwd. exists le. split => //.  apply LevelExprSet.add_spec. now left.
      cbn. cbn in ih. lia.
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
      right. apply NES.levels_spec in H as [].
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

  Search consistent.

  Lemma consistent_dec m cl :
    clause_levels cl ⊂_lset levels m ->
    { consistent (Clauses.union (clauses m) (Clauses.singleton cl)) } +
    { consistent (Clauses.union (clauses m) (inverse_clauses cl)) }.
  Proof.
    intros hcl.
    destruct (enforce_dec m (Clauses.singleton cl)).
    admit.
    - now left.
    - destruct (enforce_dec m (inverse_clauses cl)).
      admit.
      + now right.
      + admit.
        (* red in i, i0.
        setoid_rewrite neg_inverse in i0.
        specialize (i (valuation_of_model m) valuation_of_model_pos (model_valuation m)).
        specialize (i0 (valuation_of_model m) valuation_of_model_pos (model_valuation m)).
        elim i. now apply clauses_sem_singleton. *)
  Admitted.

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

  Lemma clauses_sem_dec (v : Level.t -> option Z) cl :
    Decidable.decidable (clauses_sem v cl).
  Proof.
    unfold clauses_sem.
    move: cl.
  Admitted.

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

  Lemma checking_clause_premise_levels cl :
    clause_premises_levels (checking_clause cl) =_lset
    clause_levels (checking_clause cl).
  Proof.
    destruct cl as [prems [concl k]]; rewrite /clause_premises_levels /checking_clause //=.
    rewrite /clause_levels. cbn. unfold pred_expr; cbn.
    intros l; firstorder. lsets. rsets.
    rewrite NES.levels_spec. exists (k - 1). lsets.
  Qed.

  Lemma checking_clause_levels cl :
    clause_levels (checking_clause cl) =_lset clause_levels cl.
  Proof.
    destruct cl as [prems [concl k]]; rewrite /clause_premises_levels /checking_clause //=.
    rewrite /clause_levels. cbn. unfold pred_expr; cbn.
    intros l. rewrite LevelSet.union_spec NES.levels_spec.
    setoid_rewrite LevelExprSet.union_spec; rewrite LevelSet.union_spec.
    setoid_rewrite NES.levels_spec. firstorder rsets. noconf H.
    now right.
  Qed.

Lemma check_clause_invalid_valid_Z m cl :
  clause_levels cl ⊂_lset (levels m) ->
  check_clause (clauses m) cl = Invalid -> ~ valid_clause_Z (clauses m) cl.
Proof.
  move=> hwf.
  unfold check_clause.
  move/[dup]/check_invalid_entails => nent /check_invalid_valuation [v [posv csem def ncheck]].
  intros vcl. red in vcl.
  destruct (enforce_dec m (inverse_clauses (checking_clause cl))) => //.
  * setoid_rewrite <- hwf.
    rewrite clause_levels_inverse.
    now rewrite checking_clause_levels.
  * destruct c as [tot [totpos csem']].
    apply clauses_sem_union in csem' as [cls cinv].
    move: (vcl tot) => /fwd. exact: totpos.
    move=>/(_ cls) => hcl.
    eapply clauses_sem_tot_inverse_false; tea.
    destruct cl as [prems [concl k]].
    move: hcl; cbn -[Semilattice.le].
    rewrite interp_nes_union interp_nes_singleton /interp_expr. cbn -[Semilattice.le]. cbn; lia.
  * clear vcl. apply (i v).
    rewrite clause_levels_inverse.
    now rewrite checking_clause_premise_levels in def.
    apply clauses_sem_union. split => //.
    rewrite neg_inverse in ncheck.
    { now rewrite checking_clause_premise_levels in def. }
    exact ncheck.
Qed.

Lemma check_clause_looping m cl v vcls isl :
  check_clause (clauses m) cl = IsLooping v vcls isl -> False.
Proof.
  rewrite /check_clause.
  intros. eapply check_valid_looping; tea.
  apply m.(model_valid).(model_ok).
  eapply defined_model_of_ext. eapply defined_model_of_subset.
  2:{ eapply defined_model. }
  now intros ? ?; eapply clauses_levels_declared, vcls.
  have hupd := m.(model_valid).(I.model_updates).
  now eapply is_update_of_ext in hupd.
Qed.

Definition check cls cl :=
  match check_clause cls cl with
  | IsLooping _ _ _ => false
  | Valid => true
  | Invalid => false
  end.

Theorem check_spec m cl :
  clause_levels cl ⊂_lset levels m ->
  check (clauses m) cl <-> valid_clause_Z (clauses m) cl.
Proof.
  unfold check.
  destruct check_clause eqn:he; split => //.
  - now move/check_clause_looping: he.
  - now move/check_clause_invalid_valid_Z: he => /(_ H).
  - now move/check_clause_valid_Z: he.
Qed.

Lemma check_neg_spec m cl :
  clause_levels cl ⊂_lset levels m ->
  check (clauses m) cl = false <-> ~ valid_clause_Z (clauses m) cl.
Proof.
  unfold check.
  destruct check_clause eqn:he; split => //.
  - now move/check_clause_looping: he.
  - now move/check_clause_invalid_valid_Z: he => /(_ H).
  - now move/check_clause_valid_Z: he.
Qed.

Definition check_clauses (cls : clauses) (cls' : clauses) : bool :=
  Clauses.for_all (checkb cls) cls'.


  Definition valid_clauses cls cls' :=
    forall v : Level.t -> option Z,
      positive_opt_valuation v ->
      clauses_sem v cls -> clauses_sem v cls'.


  Definition check_clauses m cls :=
    check_clauses (clauses m) cls.


  Lemma check_clauses_spec m cls :
    check_clauses m cls <-> entails_clauses (clauses m) cls.
  Proof.
    split.
    - rewrite /check_clauses /Deciders.check_clauses.
      move/Clauses.for_all_spec => ha cl /ha. unfold checkb.
      destruct check_clause eqn:ch => // _.
      eapply check_gen_entails in ch. now apply ch.
    - intros hv.
      rewrite /check_clauses /Deciders.check_clauses.
      eapply Clauses.for_all_spec; tc => cl hin.
      unfold checkb; destruct check eqn:hc => //.
      * exfalso; eapply check_entails_looping in hc; tea.
        now apply model_entails_succ in hc.
      * move/check_invalid_entails: hc => he.
        exfalso. elim he. now apply hv.
  Qed.

  Lemma check_clauses_complete m cls :
    check_clauses m cls <-> valid_entailments (clauses m) cls.
  Proof.
    rewrite check_clauses_spec.
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

  Lemma check_clauses_Z_positive_complete m cls :
    check_clauses m cls <-> valid_clauses (clauses m) cls.
  Proof.
    split.
    - rewrite check_clauses_spec.
      rewrite -entails_L_entails_ℋ_equiv.
      rewrite -entails_L_rels_entails_L_clauses.
      rewrite -completeness_all.
      move=> vr v.
      red in vr.
      move: (vr (option Z) Zopt_semi v).
      rewrite !interp_rels_clauses_sem //.
    - intros sem. unfold check_clauses, Deciders.check_clauses.
      eapply Clauses.for_all_spec. tc.
      move=> cl /sem => semcl.
      unfold checkb; destruct check eqn:hc => //.
      * move/check_entails_looping : hc.
        rewrite -to_entails_all.
        rewrite -entails_L_entails_ℋ_equiv.
        rewrite -entails_L_rels_entails_L_clauses.
        rewrite -ISL.completeness_all.
        move/(_ Z _ (valuation_of_model m)).
        rewrite -interp_rels_clauses_sem.
        move/(_ (model_valuation m)).
        rewrite -interp_rels_clauses_sem.
        rewrite clauses_sem_leq. cbn.
        rewrite interp_add_prems //=. lia.
      * move/check_invalid_valuation: hc.
        move=> [v [hpos semcls def ncl]]. specialize (semcl v hpos semcls).
        now elim ncl.
  Qed.

  Lemma check_clauses_Z_complete m cls :
    check_clauses m cls <-> valid_semilattice_entailments Zopt_semi (clauses m) cls.
  Proof.
    split.
    - rewrite check_clauses_spec.
      rewrite -entails_L_entails_ℋ_equiv.
      rewrite -entails_L_rels_entails_L_clauses.
      rewrite -completeness_all.
      move=> vr v.
      red in vr.
      move: (vr (option Z) Zopt_semi v).
      rewrite !interp_rels_clauses_sem //.
    - intros sem. unfold check_clauses, Deciders.check_clauses.
      eapply Clauses.for_all_spec. tc.
      move=> cl /sem => semcl.
      unfold checkb; destruct check eqn:hc => //.
      * move/check_entails_looping : hc.
        rewrite -to_entails_all.
        rewrite -entails_L_entails_ℋ_equiv.
        rewrite -entails_L_rels_entails_L_clauses.
        rewrite -ISL.completeness_all.
        move/(_ Z _ (valuation_of_model m)).
        rewrite -interp_rels_clauses_sem.
        move/(_ (model_valuation m)).
        rewrite -interp_rels_clauses_sem.
        rewrite clauses_sem_leq. cbn.
        rewrite interp_add_prems //=. lia.
      * move/check_invalid_valuation: hc.
        move=> [v [_ semcls def ncl]]. specialize (semcl v). elim ncl; now apply semcl.
    Qed.

Definition pred (le : LevelExpr.t) := (le.1, le.2 - 1).

(* Theorem check_entails_all {cls prems concl} :
  check cls (prems, concl) = Valid ->
  entails cls (union prems (singleton (pred concl)), concl).
Proof.
Admitted. *)


  Lemma nRopt {A} (x y : A) : ~ R_opt Logic.eq (Some x) (Some y) -> x <> y.
  Proof.
    intros hr heq. apply hr. now cbn.
  Qed.
(*
  Lemma extend_val m cl :
    (exists v : Level.t -> option Z,
      [/\ positive_opt_valuation v, clauses_sem v (clauses m), enables_clause v cl & ~ clause_sem v cl]) ->
    exists v : Level.t -> option Z,
      [/\ positive_opt_valuation v, enables_clauses v (clauses m), clauses_sem v (clauses m), enables_clause v cl & ~ clause_sem v cl].
  Proof.
    intros [v [vpos csem en nsem]].
    destruct cl as [prems concl]. cbn in nsem.
    red in en. destruct en as [k he].
    rewrite he in nsem. cbn in nsem.
    destruct (interp_expr v concl) eqn:hiconcl.
    - (* Conclusion is defined but not high enough *)
      apply nRopt in nsem.
      have hmax : Z.max z k = z /\ k < z.
      { destruct (Z.max_spec k z) as [[]|[]]; try lia. split => //. lia.
        cbn. lia. }
      cbn in he.
       exact H.
      move/(iffP): nsem. *)




  Lemma check' m cl :
    clause_levels cl ⊂_lset levels m ->
    { valid_clause_Z (clauses m) cl } + { ~ valid_clause_Z (clauses m) cl }.
  Proof.
    intros hwf.
    (* Check *)
    destruct (entails_dec m cl).
    - left. intros h hpov hsem.
      rewrite -entails_completeness in e.
      now apply e.
    - destruct (consistent_dec m cl) => //.
      * right; intros vc. red in vc. red in c. destruct a.
        admit.
            (* * setoid_rewrite <- hwf.
        now rewrite clause_levels_inverse. *)
      * right. intros vc.
        destruct c as [tot [totpos csem]].
        apply clauses_sem_union in csem as [cls cinv].
        red in vc. move: (vc tot) => /fwd. exact: totpos.
        move=>/(_ cls) => hcl.
        now eapply clauses_sem_tot_inverse_false.
  Qed.

  (* Definition check_clauses m cls (decl : clauses_levels cl ⊂_lset levels m) :=
    { valid_clause_Z (clauses m) cl } + { ~ valid_clause_Z (clauses m) cl }.
  Proof. *)


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
    inconsistent_ext m (to_clauses cls).
  Proof.
    move/enforce_clauses_inconsistent.
    intros incon v vpos clssem csem.
    apply incon. exists v. split => //.
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

  (* Definition check m c :
    clause_levels (to_clauses c) ⊂_lset levels m ->
    { valid_clauses_Z (clauses m) (to_clauses c) } + { ~ valid_clauses_Z (clauses m) (to_clauses c) } :=
    Impl.check m.(Impl.Abstract.clauses) (to_clauses c). *)



  (* Returns true is the constraint is valid in the model and all its possible consistent extensions.
     Returns false if the constraint results in an inconsistent set of constraints or it simply
     is not valid. *)
  Definition check m c :=
    Impl.check_clauses m.(Impl.Abstract.clauses) (to_clauses c).

  (* Checking corresponds to entailment in the free semilattice *)
  Lemma check_spec {m c} :
    check m c <-> entails_clauses (clauses m) (to_clauses c).
  Proof. apply check_clauses_spec. Qed.

  (* Checking corresponds to validity in *all* semilattices, including degenerate ones. *)
  Lemma check_complete m c :
    check m c <-> valid_entailments (clauses m) (to_clauses c).
  Proof. apply check_clauses_complete. Qed.

  (* Checking corresponds to validity in the lifted Z semilattice. *)
  Lemma check_Z_complete m c :
    check m c <-> valid_semilattice_entailments Zopt_semi (clauses m) (to_clauses c).
  Proof. apply check_clauses_Z_complete. Qed.

  Lemma check_Z_complete_positive m c :
    check m c <-> valid_clauses (clauses m) (to_clauses c).
  Proof. apply check_clauses_Z_positive_complete. Qed.

  Lemma zero_declared m : Impl.CorrectModel.zero_declared (model m).
  Proof. eapply zero_declared. Qed.

  Lemma above_zero_declared m : Impl.CorrectModel.above_zero_declared (levels m) (clauses m).
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
