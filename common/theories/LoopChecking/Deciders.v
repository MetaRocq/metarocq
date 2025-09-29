(* Distributed under the terms of the MIT license. *)
From Ltac2 Require Ltac2.
From Stdlib Require Import ssreflect ssrfun ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils MRClasses SemiLattice.

From MetaRocq.Common Require UnivConstraintType Universes.
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

(* Import I.Model.ISL. *)
(* Import Equiv *)

Definition init_model cls := max_clause_premises cls.

Lemma init_model_levels cls k :
  LevelMap.In k (init_model cls) <-> LevelSet.In k (clauses_levels cls).
Proof.
  split.
  - now move=> [] k' /max_clause_premises_spec.
  - move/max_clause_premises_spec_inv. now eexists.
Qed.

Definition init_w (levels : LevelSet.t) : LevelSet.t := LevelSet.empty.

(* We don't need predecessor clauses as they are trivially satisfied *)
(* Definition add_predecessors (V : LevelSet.t) cls :=
  LevelSet.fold (fun l acc =>
    Clauses.add (NonEmptySetFacts.singleton (l, 1), (l, 0)) acc) V cls. *)

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
  | Loop _ _ => "looping on "
  | Model w m _ => "satisfiable with model: " ^ print_level_Z_map m.(model_model) ^ nl ^ " W = " ^
    print_lset w
    ^ nl ^ "valuation: " ^ print_level_nat_map (valuation_of_model m.(model_model))
  end.

Definition valuation_of_result {V cls} (m : infer_result V cls) :=
  match m with
  | Loop _ _  => "looping"
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
  | Loop v _ => inr v
  | Model w vm heq => inl vm.(model_model).
Proof.
  split.
  - reflexivity.
  - apply infer_obligation_2.
  - apply is_update_of_empty.
Qed.

Definition correct_model (cls : clauses) (m : model) :=
  enabled_clauses m cls /\ is_model cls m.



Lemma clauses_of_le_singleton le r :
  (singleton le ⋞ r)%cls =_clset Clauses.singleton (r, le).
Proof.
  intros l.
  rewrite Clauses.singleton_spec clauses_of_le_spec.
  firstorder.
  - subst l. apply LevelExprSet.singleton_spec in H.
    now red in H; subst x.
  - subst l. exists le. split => //. now apply LevelExprSet.singleton_spec.
Qed.

Lemma clauses_of_le_add le l r :
  (NES.add le l ⋞ r)%cls =_clset Clauses.add (r, le) (l ⋞ r).
Proof.
  intros cl.
  rewrite Clauses.add_spec clauses_of_le_spec.
  split.
  - move=> [] x [] /LevelExprSet.add_spec; rewrite /LevelExprSet.E.eq.
    move=> [->|hin]. now left.
    intros ->. right. rewrite clauses_of_le_spec. now exists x.
  - move=> [->|]. exists le. split => //.
    * now apply LevelExprSet.add_spec; left.
    * rewrite clauses_of_le_spec => -[] k [] hin ->.
      exists k. split => //. now apply LevelExprSet.add_spec.
Qed.

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
    move=> [z [hmin hleq]]. cbn in hleq.
    depelim hleq. cbn in H0.
    rewrite min_premise_singleton /min_atom_value in hmin.
    destruct le as [l k]. cbn -[Z.add] in *. rewrite H0 in hmin. noconf hmin. lia.
  - intros le x en hnin h.
    apply en. intros cl [lk [hin eq]]. subst cl.
    eapply In_add_prems in hin as [? []]. subst lk. cbn.
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
  | IsLooping (v : premises) (islooping : loop_on_univ cls v)
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

Equations check (cls : clauses) (cl : clause) : check_result cls :=
  check cls cl with loop_check cls cl :=
    | Loop v isl => IsLooping v isl
    | Model W v _ with inspect (LevelMap.find (concl cl).1 v.(model_model)) := {
      | exist (Some val) he with check_atom_value (Some (concl cl).2) val :=
        { | true => Valid
          | false => Invalid }
      | exist None he with valid_model_find v he := {}
    }.

Definition check_clauses (cls : clauses) (cls' : clauses) : bool :=
  let check_one cl :=
    match check cls cl with
    | IsLooping _ _ => false
    | Valid => true
    | Invalid => false
    end
  in
  Clauses.for_all check_one cls'.

(* If a clause checks, then it is entailed (and will be valid in any extension of the model) *)
Theorem check_entails {cls cl} :
  check cls cl = Valid -> entails cls cl.
Proof.
  destruct cl as [prems [concl k]].
  funelim (check cls _) => // _.
  set (V := (clause_levels _ ∪ clauses_levels cls)%levels) in *.
  clear Heqcall H. cbn [concl fst snd] in *. clear Heq0.
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
  2:{ red. rewrite /level_value he. now constructor. }
  exact tr.
Qed.

Lemma check_entails_looping {cls cl v isl} :
  check cls cl = IsLooping v isl -> cls ⊢a v → succ_prems v.
Proof.
  funelim (check cls cl) => //.
Qed.

Lemma check_looping {cls cl v isl} :
  check cls cl = IsLooping v isl ->
  ~ (exists m, defined_model_of (levels v) m /\ is_model cls m).
Proof.
  move/check_entails_looping.
  intros loop [m' [en clssem]].
  apply to_entails_all in loop.
  apply is_model_valid in clssem.
  have hv := entails_all_model_valid clssem loop.
  eapply loop_invalid in hv; tea.
  now apply enabled_clauses_le.
Qed.

(* Lemma check_valid_looping {cls cl m v isl} :
  enabled_clauses m cls ->
  is_model cls m ->
  check cls cl = IsLooping v isl -> False.
Proof.
  move=> en ism.
  rewrite /check /loop_check.
  destruct loop.

   /check_looping; apply.
  destruct def as [def isupd].
  exists m'. split => //.
  move: isupd; move/is_update_of_case => [].
  * move=> [] empw eq. rewrite -eq.
  exists m.
Qed. *)

Theorem check_invalid {cls cl} :
  check cls cl = Invalid -> ~ entails cls cl.
Proof.
  funelim (check cls cl) => //.
  set (V := (clause_levels cl ∪ clauses_levels cls)%levels) in *.
  destruct cl as [prems [concl k]].
  rename val into conclval_v => _. clear H Heq0 Heqcall prf. cbn in he.
  move: (check_atom_value_spec (Some k) conclval_v). rewrite Heq.
  intros r; depelim r. rename H into nent. intros H.
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
  move/entails_model_valid/(_ _ vmok): H.
  have [z minp] : enabled_clause (model_model v) cl.
  { apply (@enabled_clause_ext pm).
    exact: is_update_of_ext (model_updates v).
    red; cbn.
    have hcl : Clauses.In cl (Clauses.singleton cl).
    { now eapply Clauses.singleton_spec. }
    have hs:= @premises_model_map_min_premise_inv V _ _ hcl. firstorder. }
  move/valid_clause_elim/(_ z minp).
  cbn in minp.
  rewrite /level_value he => h; depelim h. apply nent.
  constructor.
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

Lemma min_model_map_enabled m cls cls' :
  enabled_clauses m cls ->
  enabled_clauses (min_model_map m cls') (Clauses.union cls cls').
Proof.
  intros en cl.
  rewrite Clauses.union_spec => -[].
  - move/en; rewrite /enabled_clause => -[z hmin].
    have := @min_premise_pres m (min_model_map m cls') (premise cl) => /fwd.
    apply min_model_map_acc.
    rewrite hmin => h; depelim h. now exists y.
  - intros hin; rewrite /enabled_clause.
    have [hm [incl hext]] := min_model_map_spec cls' m.
    have [hle [minp [inp ->]]] := min_premise_spec (min_model_map m cls') (premise cl).
    move: (incl _ hin). move/(_ minp.1) => /fwd.
    { apply clause_levels_spec. left. now apply in_levels. }
    move=> [k hmap].
    specialize (hm minp.1 k hmap) as [_ hm _].
    destruct minp.
    move: hm => /(_ _ hin)/(_ _ inp). intros le; depelim le.
    exists (y - z). now rewrite /min_atom_value (level_value_MapsTo hmap).
Qed.


Definition init_clause_of_level l :=
  (singleton (l, 0), (Level.zero, if Level.is_global l then 1 else 0)).

Definition declared_init_clause_of_level l cls :=
  if eqb l Level.zero then True
  else Clauses.In (init_clause_of_level l) cls.

Module CorrectModel.

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
    { admit. }
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
    | Loop u isl => inr {| loop_univ := u; loop_on_univ := isl |}
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
        unfold CorrectModel.zero_declared.
        now move=> [] k hm; exists (Z.of_nat (S k)).
      * intros nzero.
        have he := enabled_model m.
        move/he. rewrite /enabled_clause /init_clause_of_level.
        move=> [] k hm. cbn in hm.
        rewrite min_premise_singleton /min_atom_value in hm.
        destruct level_value eqn:hl => //.
        exists z. apply (level_value_MapsTo' hl).
  Qed.


  Definition clause_sem {S} {SL : Semilattice S Q.t} (V : Level.t -> S) (cl : clause) : Prop :=
    let '(prems, concl) := cl in
    le (interp_expr V concl) (interp_prems V prems).

  Definition clauses_sem {S} {SL : Semilattice S Q.t} (V : Level.t -> S) (cls : Clauses.t) : Prop :=
    Clauses.For_all (clause_sem V) cls.

  Instance clauses_sem_proper {S} {SL : Semilattice S Q.t} :
    Proper (Logic.eq ==> Clauses.Equal ==> iff) clauses_sem.
  Proof.
    move=> ?? -> ?? h.
    rewrite /clauses_sem.
    now rewrite h.
  Qed.

  Lemma clauses_sem_singleton {S} {SL : Semilattice S Q.t} {V cl} :
    clauses_sem V (Clauses.singleton cl) <-> clause_sem V cl.
  Proof.
    rewrite /clauses_sem /Clauses.For_all.
    split; firstorder. apply H. clsets.
    apply Clauses.singleton_spec in H0. now subst.
  Qed.

  Lemma clauses_sem_add {S} {SL : Semilattice S Q.t} {V cl cls} :
    clauses_sem V (Clauses.add cl cls) <-> clause_sem V cl /\ clauses_sem V cls.
  Proof.
    rewrite /clauses_sem /Clauses.For_all.
    split.
    - intros hcl. split.
      * apply hcl, Clauses.add_spec; now left.
      * move=> x hin; apply hcl, Clauses.add_spec; now right.
    - move=> [] hcl hcls x /Clauses.add_spec -[]. now subst.
      apply hcls.
  Qed.

  Lemma clauses_sem_union {S} {SL : Semilattice S Q.t} {V cls cls'} :
    clauses_sem V (Clauses.union cls cls') <-> clauses_sem V cls /\ clauses_sem V cls'.
  Proof.
    rewrite /clauses_sem /Clauses.For_all.
    setoid_rewrite Clauses.union_spec. firstorder.
  Qed.


  Definition to_val (v : LevelMap.t nat) l :=
    match LevelMap.find l v with
    | Some n => n
    | None => 0%nat
    end.

  Definition to_Z_val (v : Level.t -> nat) := fun l => Z.of_nat (v l).

  Definition valuation m := to_val (Model.valuation_of_model m).

  Lemma valuation_range {m l k} :
    LevelMap.MapsTo l (Some k) m ->
    model_min m <= k <= model_max m.
  Proof.
    move=> hm.
    have mins := model_min_spec m _ _ hm.
    have maxs := model_max_spec m _ _ hm.
    depelim maxs. lia.
  Qed.

  (** Enabled and valid clauses are satisfied by valuation.
     *)
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
    have [z0min z0max] := valuation_range hfind.
    have [z1min z1max] := valuation_range findp.
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

  Definition model_valuation {V cls} (m : t V cls) : clauses_sem (to_Z_val (valuation (model_of m))) cls.
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
      have he : (V ∪ W) =_lset V.
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
      rewrite interp_prems_singleton //=.
      rewrite /to_Z_val /to_val /valuation /to_val.
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
      (to_val (valuation_of_model (model_of m)) Level.zero) < (to_val (valuation_of_model (model_of m)) l)
    else
      (to_val (valuation_of_model (model_of m)) Level.zero) <= (to_val (valuation_of_model (model_of m)) l))%nat.
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
      rewrite interp_prems_singleton //=.
      rewrite /to_Z_val /to_val /valuation /to_val.
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

  Lemma valuation_0 {V cls} {m : t V cls}: to_val (valuation_of_model (model_of m)) Level.zero = 0%nat.
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
    forall l, LevelSet.In l V -> Level.is_global l -> (0 < to_val (valuation_of_model (model_of m)) l)%nat.
  Proof.
    move=> l /(model_levels m) [] k inm isg.
    have hmax := model_max_gen inm.
    rewrite isg in hmax.
    rewrite valuation_0 in hmax. lia.
  Qed.

  Lemma valuation_not_global {V cls} {m : t V cls} :
    forall l, LevelSet.In l V -> ~~ Level.is_global l -> (0 <= to_val (valuation_of_model (model_of m)) l)%nat.
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
    =_lset (LevelSet.singleton Level.zero ∪ LevelSet.singleton l).
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

  Lemma enforce_clauses_inconsistent m cls u :
    enforce_clauses m cls = Some (inr u) ->
    entails_L_clauses (Clauses.union (clauses m) cls) (loop_univ u ≡ succ_prems (loop_univ u)).
  Proof.
    funelim (enforce_clauses m cls) => //=.
    intros [= <-]. clear -u.
    destruct u as [u loop]. cbn [loop_univ].
    eapply to_entails_all in loop.
    apply entails_L_clauses_eq; split; revgoals.
    - now eapply entails_ℋ_entails_L.
    - eapply entails_ℋ_entails_L.
      eapply to_entails_all.
      apply entails_all_succ.
  Qed.

  Definition check_clauses m cls :=
    check_clauses (clauses m) cls.

  Instance entails_L_pres_clauses_proper : Proper (Logic.eq ==> Clauses.Equal ==> iff) entails_L_pres_clauses.
  Proof.
    intros ?? -> ? ? h.
    rewrite /entails_L_pres_clauses. now rewrite h.
  Qed.

  Lemma entails_L_pres_clauses_union {p cls cls'} : entails_L_pres_clauses p (Clauses.union cls cls') <->
    entails_L_pres_clauses p cls /\
    entails_L_pres_clauses p cls'.
  Proof.
    rewrite /entails_L_pres_clauses /Clauses.For_all.
    setoid_rewrite Clauses.union_spec. by firstorder.
  Qed.

  Lemma entails_L_rels_entails_rels p rs :
    entails_L_rels p rs <-> entails_L_clauses (clauses_of_relations p) (clauses_of_relations rs).
  Proof.
    induction rs.
    - split => //.
      * intros ent cl hin. cbn in hin. clsets.
      * cbn. constructor.
    - split.
      * intros ent; depelim ent.
        unfold entails_L_clauses.
        destruct a as [l r]. rewrite clauses_of_relations_cons entails_L_pres_clauses_union. split.
        now eapply entails_L_clauses_relations, entails_L_pres_clauses_of_relations_eq.
        apply IHrs, ent.
      * unfold entails_L_clauses.
        destruct a as [l r]. rewrite clauses_of_relations_cons entails_L_pres_clauses_union.
        move=> [] lr ih. constructor.
        apply (proj1 entails_L_pres_clauses_of_relations_eq) in lr.
        now apply entails_L_clauses_pres_all in lr.
        apply IHrs, ih.
  Qed.

  Lemma entails_clauses_of_relations cls : entails_clauses cls (clauses_of_relations (relations_of_clauses cls)).
  Proof.
    apply entails_ℋ_clauses_of_relations_equiv. apply entails_clauses_tauto.
  Qed.

  Lemma entails_clauses_trans {cls cls' cls''} : cls ⊢ℋ cls' -> cls' ⊢ℋ cls'' -> cls ⊢ℋ cls''.
  Proof.
    intros ent ent'.
    eapply entails_clauses_cut; tea.
    eapply entails_ℋ_clauses_subset; tea. clsets.
  Qed.

  Lemma entails_L_rels_entails_L_clauses cls cls' :
    entails_L_rels (relations_of_clauses cls) (relations_of_clauses cls') <-> entails_L_clauses cls cls'.
  Proof.
    rewrite entails_L_rels_entails_rels.
    rewrite !entails_L_entails_ℋ_equiv.
    split.
    - intros cl. eapply entails_clauses_cut. eapply entails_ℋ_clauses_of_relations. tea.
      eapply entails_ℋ_clauses_subset. eapply entails_clauses_tauto. intros cl' hin.
      apply clauses_of_relations_relations_of_clauses in hin.
      rewrite Clauses.union_spec. now left.
    - intros hent. eapply (proj1 entails_ℋ_clauses_of_relations_equiv).
      eapply entails_clauses_trans; tea. eapply entails_clauses_of_relations.
  Qed.

  Lemma clauses_sem_leq {S} {SL : Semilattice S Q.t} (V : Level.t -> S) l r :
    clauses_sem V (l ⋞ r) <->
    (interp_prems V l ≤ interp_prems V r)%sl.
  Proof.
    move: l.
    apply: elim.
    - intros le; cbn.
      rewrite clauses_of_le_singleton clauses_sem_singleton.
      cbn. now rewrite interp_prems_singleton.
    - move=> le x xr hnin.
      rewrite clauses_of_le_add clauses_sem_add xr.
      cbn. rewrite interp_prems_add.
      symmetry; apply join_le_left_eq.
  Qed.

  Lemma clauses_sem_eq {S} {SL : Semilattice S Q.t} (V : Level.t -> S) l r :
    clauses_sem V (l ≡ r) <->
    (interp_prems V l ≡ interp_prems V r)%sl.
  Proof.
    rewrite /clauses_of_eq clauses_sem_union !clauses_sem_leq.
    symmetry; apply eq_antisym.
  Qed.

  Definition relation_of_clause cl := (singleton (concl cl) ≤ premise cl).

  Lemma interp_rels_of_clauses {S} {SL : Semilattice S Q.t} {V cls} :
    interp_rels V (relations_of_clauses cls) <->
    forall cl, Clauses.In cl cls -> interp_rel V (relation_of_clause cl).
  Proof.
    rewrite /interp_rels Forall_forall.
    split.
    - move=> hx cl /relations_of_clauses_spec_inv.
      now move/hx.
    - move=> hcl x /relations_of_clauses_spec => -[] prems [] concl.
      now move=> [] /hcl hin ->.
  Qed.

  Lemma interp_rels_clauses_sem {S} {SL : Semilattice S Q.t} {V cls} :
    clauses_sem V cls <-> interp_rels V (relations_of_clauses cls).
  Proof.
    rewrite interp_rels_of_clauses.
    split.
    - move=> sem [prems concl] /sem //=.
      now rewrite /le interp_prems_union interp_prems_singleton.
    - move=> hcl [prems concl] /hcl /=.
      now rewrite /le interp_prems_union interp_prems_singleton.
  Qed.

  Definition Z_valuation_of_model m :=
    to_Z_val (to_val (valuation_of_model (model m))).

  Lemma model_entails_succ m v : clauses m ⊢a v → succ v -> False.
  Proof.
    move/to_entails_all/entails_L_entails_ℋ_equiv.
    move/entails_L_rels_entails_L_clauses/completeness_all.
    move/(_ Z _ (Z_valuation_of_model m)).
    rewrite -!interp_rels_clauses_sem => /fwd.
    cbn in *.
    have mok := m.(correct_model).(model_valid).(model_ok).
    eapply valid_clauses_model.
    eapply enabled_clauses_ext, m.(correct_model).(enabled_model).
    now eapply (is_update_of_ext m.(correct_model).(model_valid).(I.model_updates)).
    exact mok.
    move/clauses_sem_leq.
    rewrite interp_add_prems. cbn. lia.
  Qed.

  Lemma check_clauses_spec m cls :
    check_clauses m cls <-> entails_clauses (clauses m) cls.
  Proof.
    split.
    - rewrite /check_clauses /Deciders.check_clauses.
      move/Clauses.for_all_spec => ha cl /ha.
      destruct check eqn:ch => // _.
      eapply check_entails in ch. now apply ch.
    - intros hv.
      rewrite /check_clauses /Deciders.check_clauses.
      eapply Clauses.for_all_spec; tc => cl hin.
      destruct check eqn:hc => //.
      * exfalso; eapply check_entails_looping in hc; tea.
        now apply model_entails_succ in hc.
      * move/check_invalid: hc => he.
        exfalso. elim he. now apply hv.
  Qed.

  Definition valid_entailments cls cls' :=
    forall S (SL : Semilattice S Q.t) (V : Level.t -> S), clauses_sem V cls -> clauses_sem V cls'.

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
  Lemma enforce_inconsistent {m cls u} :
    enforce m cls = Some (inr u) ->
    forall S (SL : Semilattice.Semilattice S Q.t) V, clauses_sem V (Clauses.union (clauses m) (to_clauses cls)) ->
       clauses_sem V (Impl.CorrectModel.loop_univ u ≡ succ (Impl.CorrectModel.loop_univ u)).
  Proof.
    rewrite /enforce.
    move/enforce_clauses_inconsistent.
    rewrite -entails_L_rels_entails_L_clauses.
    rewrite -ISL.completeness_all.
    move=> vr S SL V.
    specialize (vr S SL V).
    move: vr.
    rewrite !interp_rels_clauses_sem // => vr /vr.
    (* rewrite -interp_rels_clauses_sem.
    rewrite clauses_sem_eq.
    setoid_rewrite interp_add_prems; cbn -[Z.add].
    lia. *)
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

  (* Returns true is the constraint is valid in the model and all its possible consistent extensions.
     Returns false if the constraint results in an inconsistent set of constraints or it simply
     is not valid. *)
  Definition check m c :=
    Impl.check_clauses m.(Impl.Abstract.clauses) (to_clauses c).

  Lemma check_spec {m c} :
    check m c <-> entails_clauses (clauses m) (to_clauses c).
  Proof. apply check_clauses_spec. Qed.

  Lemma check_complete m c :
    check m c <-> valid_entailments (clauses m) (to_clauses c).
  Proof. apply check_clauses_complete. Qed.


  (* Returns the valuation of the model: a minimal assignement from levels to constraints
    that make the enforced clauses valid. *)
  Definition valuation m := to_val (Model.valuation_of_model (model m)).

  Definition model_valuation m : clauses_sem (to_Z_val (valuation m)) (clauses m).
  Proof.
    destruct m as [levels clauses []]; cbn.
    apply valid_clauses_model; tea; cbn.
    - eapply enabled_clauses_ext; tea; cbn.
      eapply is_update_of_ext, model_valid0.
    - apply model_valid.
  Qed.

  Lemma zero_declared m : Impl.CorrectModel.zero_declared (model m).
  Proof. eapply zero_declared. Qed.

  Lemma above_zero_declared m : Impl.CorrectModel.above_zero_declared (levels m) (clauses m).
  Proof. eapply above_zero_declared. Qed.

  Lemma model_valuation_zero m : valuation m Level.zero = 0%nat.
  Proof. apply valuation_0. Qed.

  Lemma model_valuation_global {m l} : LevelSet.In l (levels m) -> Level.is_global l -> (valuation m l > 0)%nat.
  Proof. apply valuation_global. Qed.

  Lemma model_valuation_not_global {m l} : LevelSet.In l (levels m) -> ~~ Level.is_global l -> (valuation m l >= 0)%nat.
  Proof. apply valuation_not_global. Qed.

End LoopChecking.
