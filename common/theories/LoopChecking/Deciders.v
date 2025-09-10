(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ZArith.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.

From MetaRocq.Common Require Universes.
From Equations Require Import Equations.

From MetaRocq.Common.LoopChecking Require Import Common Interfaces HornClauses Model PartialLoopChecking.

Set Equations Transparent.

Module Type LoopCheckingItf (LS : LevelSets).

  (* Type of consistent models of a set of universe constraints *)
  Parameter model : Type.
  Notation univ := LS.LevelExprSet.nonEmptyLevelExprSet.

  Inductive constraint_type := UnivEq | UnivLe.
  Notation constraint := (univ * constraint_type * univ).

  Parameter init_model : model.

  (* Returns None if already declared *)
  Parameter declare_level : LS.Level.t -> model -> option model.

  (* If the constraints mention undeclared universes, returns None,
     otherwise, returns either a model or a looping universe, i.e. such that u >= u + 1 is implied
     by the constraint *)
  Parameter enforce : constraint -> model -> option (model + univ).

  (* Returns true is the clause is valid in the model and all its possible consistent extensions.
     Returns false if the constraint results in an inconsistent set of constraints or it simply
     is not valid. *)
  Parameter check : model -> constraint -> bool.

  (* Returns the valuation of the model: a minimal assignement from levels to constraints
    that make the enforced clauses valid. *)
  Parameter valuation : model -> LS.LevelMap.t nat.
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
  - now move => [] k' /max_clause_premises_spec.
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
  let (e, exprs) := NonEmptySetFacts.to_nonempty_list l in
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

Equations? infer_model (cls : clauses) : option model :=
infer_model cls with loop (clauses_levels cls) LevelSet.empty cls (init_model cls) (init_model cls) _ :=
  | Loop _ _ => None
  | Model w vm heq => Some vm.(model_model).
Proof.
  split.
  - reflexivity.
  - apply infer_obligation_2.
  - apply is_update_of_empty.
Qed.

Definition enabled_clause (m : model) (cl : clause) :=
  exists z, min_premise m (premise cl) = Some z.

Definition enabled_clauses (m : model) (cls : clauses) :=
  Clauses.For_all (enabled_clause m) cls.

Definition correct_model (cls : clauses) (m : model) :=
  enabled_clauses m cls /\ clauses_sem (valuation_of_model m) cls.

Definition infer_correctness cls :=
  match infer_model cls with
  | Some m => correct_model cls m
  | None => ~ exists v, clauses_sem v cls
  end.

Lemma enabled_clauses_ext m m' cls : m ⩽ m' -> enabled_clauses m cls -> enabled_clauses m' cls.
Proof.
  intros hext.
  rewrite /enabled_clauses.
  intros ha cl; move/ha.
  unfold enabled_clause.
  intros [minp heq].
  have hp := min_premise_pres (premise cl) hext.
  rewrite heq in hp. depelim hp. now exists y.
Qed.

Lemma interp_prems_ge v (prems : premises) :
  forall prem, LevelExprSet.In prem prems ->
  interp_expr v prem <= interp_prems v prems.
Proof.
  intros.
  unfold interp_prems.
  have he := to_nonempty_list_spec prems.
  destruct to_nonempty_list.
  pose proof to_nonempty_list_spec'.
  rewrite In_elements in H. rewrite -he in H. clear H0 he. clear -H.
  destruct H. subst p.
  - induction l. cbn. auto.
    cbn. lia. cbn. lia.
  - induction l in H |- *.
    now cbn in H.
    cbn in H. destruct H; subst; cbn.
    * cbn. lia.
    * specialize (IHl H). lia.
Qed.

(** Enabled and valid clauses are satisfied by valuation *)
Lemma valid_clause_model model cl :
  enabled_clause model cl ->
  valid_clause model cl ->
  clause_sem (valuation_of_model model) cl.
Proof.
  unfold enabled_clause, valid_clause.
  destruct min_premise eqn:hmin => //= => //.
  2:{ intros [k' eq]. congruence. }
  intros [k' eq]. noconf eq.
  destruct cl as [prems [concl k]]; cbn.
  unfold level_value_above.
  destruct level_value eqn:hl => //.
  unfold interp_level. unfold level_value in hl. destruct LevelMap.find eqn:hfind => //. noconf hl.
  move/Z.leb_le => hrel.
  eapply LevelMap.find_2 in hfind.
  have conclm := valuation_of_model_spec _ _ _ hfind.
  set (v := (model_max _ - _)) in *.
  cbn in conclm.
  eapply LevelMap.find_1 in conclm. rewrite conclm.
  subst v.
  pose proof (@min_premise_spec model prems) as [premmin [prem [premin premeq]]].
  rewrite hmin in premeq.
  eapply Z.le_ge.
  eapply Z.le_trans. 2:{ eapply interp_prems_ge; tea. }
  unfold interp_expr. destruct prem as [prem k'].
  symmetry in premeq.
  move: premeq. unfold min_atom_value.
  unfold level_value. destruct (LevelMap.find prem) eqn:findp => //.
  destruct o => //.
  intros [= <-].
  eapply LevelMap.find_2 in findp.
  have premm := valuation_of_model_spec _ _ _ findp.
  unfold interp_level.
  eapply LevelMap.find_1 in premm. rewrite premm.
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
  lia.
Qed.

Lemma init_model_enabled cls : enabled_clauses (init_model cls) cls.
Proof.
  unfold enabled_clauses.
  intros x hin. unfold enabled_clause.
  pose proof (@min_premise_spec (init_model cls) (premise x)) as [premmin [prem [premin premeq]]].
  have inV : LevelSet.In prem (clauses_levels cls).
  { rewrite clauses_levels_spec. exists x; split => //. rewrite /clause_levels.
    eapply LevelSet.union_spec; left. rewrite levelexprset_levels_spec. exists prem.2.
    destruct prem. exact premin. }
  unfold init_model. rewrite premeq. unfold min_atom_value.
  destruct prem as [l k].
  have hm := max_clause_premises_spec_inv cls l inV.
  rewrite (level_value_MapsTo hm).
  have hs := max_clause_premise_of_spec l k _ _ hin premin.
  depelim hs. rewrite H0.
  eexists => //.
Qed.

Lemma interp_add_expr V n e : interp_expr V (add_expr n e) = n + interp_expr V e.
Proof.
  destruct e as [l k]; cbn. lia.
Qed.

Lemma interp_prems_singleton V e :
  interp_prems V (singleton e) = interp_expr V e.
Proof.
  rewrite /interp_prems.
  now rewrite singleton_to_nonempty_list /=.
Qed.

Lemma fold_right_max_in {a l} n : In a l -> a <= fold_right Z.max n l.
Proof.
  induction l.
  - now cbn.
  - intros [eq|inl]. subst a0. cbn. lia.
    cbn. specialize (IHl inl). lia.
Qed.

Lemma fold_right_max_acc {n l} : n <= fold_right Z.max n l.
Proof.
  induction l.
  - now cbn.
  - cbn. lia.
Qed.

Lemma fold_right_impl n l l' :
  (forall x, In x l -> In x l') -> fold_right Z.max n l <= fold_right Z.max n l'.
Proof.
  induction l in l' |- *.
  - cbn. destruct l'; cbn. lia.
    intros. have := @fold_right_max_acc n l'. lia.
  - cbn; intros h.
    have inal' := (h a (or_introl eq_refl)).
    have := fold_right_max_in n inal'.
    specialize (IHl l').
    forward IHl.
    intros. apply h. now right.
    lia.
Qed.

Lemma fold_right_equivlist n l l' :
  equivlistA eq l l' -> fold_right Z.max n l = fold_right Z.max n l'.
Proof.
  intros eq.
  have h := fold_right_impl n l l'.
  forward h. intros x; rewrite -!InA_In_eq. apply eq.
  have h' := fold_right_impl n l' l.
  forward h'. intros x; rewrite -!InA_In_eq. apply eq.
  lia.
Qed.

Fixpoint max_list (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: xs => match max_list xs with
    | Some m => Some (Z.max x m)
    | None => Some x end
  end.

Lemma max_list_fold_right n l : max_list (n :: l) = Some (fold_right Z.max n l).
Proof.
  induction l; cbn.
  - reflexivity.
  - cbn in IHl. destruct max_list. f_equal. noconf IHl. lia.
    f_equal; noconf IHl. lia.
Qed.

Lemma fold_right_max_spec n l :
  let fn := fold_right Z.max in
  (forall x, In x (n :: l) -> x <= fn n l) /\
  (exists x, In x (n :: l) /\ fn n l = x).
Proof.
  induction l; cbn.
  - split. intros x [] => //. now subst.
    exists n. firstorder.
  - cbn in IHl. destruct IHl as [h h'].
    split.
    intros x [|[]]; subst.
    * specialize (h x). forward h by auto. lia.
    * lia.
    * specialize (h x). forward h by auto. lia.
    * destruct h' as [x []]. exists (Z.max a x). rewrite -{4}H0. split => //.
      destruct H; subst.
      destruct (Z.max_spec a x) as [[]|[]]; firstorder; subst.
      destruct (Z.max_spec a (fold_right Z.max n l)) as [[]|[]]; firstorder; subst. rewrite H1.
      auto.
Qed.

Lemma fold_right_equivlist_all n n' l l' :
  equivlistA eq (n :: l) (n' :: l') -> fold_right Z.max n l = fold_right Z.max n' l'.
Proof.
  intros eq.
  have [hla [maxl [inmaxl eqmaxl]]] := fold_right_max_spec n l.
  have [hra [maxr [inmaxr eqmaxr]]] := fold_right_max_spec n' l'.
  rewrite eqmaxl eqmaxr.
  red in eq; setoid_rewrite InA_In_eq in eq.
  apply (eq _) in inmaxl. apply hra in inmaxl.
  apply eq in inmaxr. apply hla in inmaxr. lia.
Qed.

Lemma interp_prems_elements V u :
  interp_prems V u = fold_right Z.max (interp_expr V (to_nonempty_list u).1) (List.map (interp_expr V) (to_nonempty_list u).2).
Proof.
  rewrite /interp_prems.
  have he := to_nonempty_list_spec u.
  destruct to_nonempty_list.
  now rewrite Universes.fold_right_map.
Qed.

Lemma fold_right_interp {V x l x' l'} :
  equivlistA eq (x :: l) (x' :: l') ->
  fold_right Z.max (interp_expr V x) (List.map (interp_expr V) l) = fold_right Z.max (interp_expr V x') (List.map (interp_expr V) l').
Proof.
  intros eq. apply fold_right_equivlist_all.
  intros a. rewrite !InA_In_eq.
  rewrite !(in_map_iff (interp_expr V) (_ :: _)).
  setoid_rewrite <-InA_In_eq.
  split.
  - move=> [b [<- ]].
    eexists; split; trea. now apply eq in b0.
  - move=> [b [<- ]].
    eexists; split; trea. now apply eq in b0.
Qed.

Lemma equivlistA_add le u : let l := to_nonempty_list (add le u) in
 equivlistA eq (l.1 :: l.2) (le :: LevelExprSet.elements u).
Proof.
  have he := to_nonempty_list_spec (add le u).
  destruct to_nonempty_list. cbn.
  intros x. rewrite he.
  rewrite !LevelExprSet.elements_spec1.
  split.
  - move/LevelExprSet.add_spec => [->|hin].
    now constructor. constructor 2. now apply LevelExprSet.elements_spec1.
  - intros h; depelim h; subst. now apply LevelExprSet.add_spec; left.
    apply LevelExprSet.add_spec. now apply LevelExprSet.elements_spec1 in h.
Qed.

Lemma fold_right_comm acc l : l <> [] -> fold_right Z.max acc l = Z.max acc (fold_right Z.max (List.hd acc l) (List.tl l)).
Proof.
  induction l in acc |- *.
  - intros; congruence.
  - intros _. cbn. destruct l; cbn. lia.
    cbn in IHl. rewrite (IHl acc). congruence.
    rewrite (IHl a). congruence. lia.
Qed.

Lemma interp_prems_add V le (u : premises) :
  interp_prems V (add le u) = Z.max (interp_expr V le) (interp_prems V u).
Proof.
  rewrite 2!interp_prems_elements.
  erewrite fold_right_interp. 2:apply equivlistA_add.
  rewrite fold_right_comm.
  { apply map_nil, elements_not_empty. }
  f_equal. eapply fold_right_equivlist_all.
  have he := to_nonempty_list_spec u.
  destruct to_nonempty_list. rewrite -he //=.
Qed.

Lemma interp_prems_eq (P : premises -> Z -> Prop) V :
  (forall le, P (singleton le) (interp_expr V le)) ->
  (forall le u k, P u k -> ~ LevelExprSet.In le u -> P (add le u) (Z.max (interp_expr V le) k)) ->
  forall u, P u (interp_prems V u).
Proof.
  intros hs hadd.
  eapply premises_elim.
  - intros le. rewrite interp_prems_singleton. apply hs.
  - intros le prems ih hnin.
    rewrite interp_prems_add. now apply hadd.
Qed.

Lemma add_prems_singleton n cl : add_prems n (singleton cl) = singleton (add_expr n cl).
Proof.
  apply eq_univ_equal => [] [l k].
  rewrite In_add_prems LevelExprSet.singleton_spec.
  firstorder.
  - destruct x; noconf H0.
    eapply LevelExprSet.singleton_spec in H.
    now red in H; noconf H.
  - destruct cl. exists (t, z). split => //.
    red in H; noconf H. now apply LevelExprSet.singleton_spec.
Qed.

Lemma interp_add_prems V n e : interp_prems V (add_prems n e) = n + interp_prems V e.
Proof.
  revert e.
  refine (interp_prems_eq (fun u z => interp_prems V (add_prems n u) = n + z) _ _ _).
  - intros le.
    rewrite add_prems_singleton interp_prems_singleton //=.
    destruct le; cbn. lia.
  - intros le u k heq hnin.
    rewrite add_prems_add.
    rewrite interp_prems_add heq interp_add_expr. lia.
Qed.

Lemma in_pred_closure_entails cls cl :
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
    rewrite /add_expr; cbn. lia.
  - intros V clsm. cbn.
    rewrite interp_prems_singleton.
    cbn. lia.
Qed.

Lemma interp_prems_in {V le} {u : premises} : LevelExprSet.In le u -> interp_prems V u >= interp_expr V le.
Proof.
  revert u.
  refine (interp_prems_eq (fun u z => LevelExprSet.In le u -> z >= interp_expr V le) V _ _).
  - intros le' u'.
    apply LevelExprSet.singleton_spec in u'. red in u'; subst. lia.
  - move=> le' u z hz hnin /LevelExprSet.add_spec [->|hin]. lia.
    specialize (hz hin). lia.
Qed.

Lemma clauses_sem_subset {u u' : premises} : u ⊂_leset u' ->
  forall V, interp_prems V u' >= interp_prems V u.
Proof.
  intros hsub V.
  revert u u' hsub.
  refine (interp_prems_eq (fun u z => forall u' : premises, u ⊂_leset u' -> interp_prems V u' >= z) V _ _).
  - intros le u' hsing.
    specialize (hsing le). forward hsing by now apply LevelExprSet.singleton_spec.
    now apply interp_prems_in.
  - intros le u k ih hin u' sub.
    have hle := sub le.
    specialize (ih u').
    forward ih. intros x hin'. apply sub. now apply LevelExprSet.add_spec; right.
    forward hle by now apply LevelExprSet.add_spec; left.
    have hi := interp_prems_in (V := V) hle. lia.
Qed.

#[refine] Instance ge_refl : Reflexive Z.ge := _.
Proof. red. lia. Qed.

#[refine] Instance ge_trans : Transitive Z.ge := _.
Proof. red. lia. Qed.

Lemma clauses_sem_entails {cls cl} :
  entails cls cl ->
  (forall V, clauses_sem V cls -> clause_sem V cl).
Proof.
  induction 1.
  - intros v clls. red.
    destruct concl0 as [concl k].
    have hge := interp_prems_ge v prems _ H.
    by lia.
  - move=> V Hcls.
    move: {IHentails} (IHentails _ Hcls).
    unfold clause_sem. unfold ge => hyp.
    etransitivity; tea. rewrite interp_prems_add.
    rewrite interp_prems_add in hyp.
    eapply in_pred_closure_entails in H; tea.
    move: H; rewrite /clause_sem. unfold ge.
    have ssub := clauses_sem_subset H1 V. lia.
Qed.

Lemma clauses_sem_entails_all {cls prems concl} :
  cls ⊢a prems → concl ->
  (forall V, clauses_sem V cls -> interp_prems V prems >= interp_prems V concl).
Proof.
  intros ha V hcls.
  red in ha.
  move: ha.
  revert concl.
  refine (@interp_prems_eq (fun concl z => _ -> interp_prems V prems >= z) V _ _).
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
    lia.
Qed.

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
    unfold clauses_sem.
    intros cl hin.
    eapply valid_clause_model. now eapply encl in hin.
    eapply Clauses.for_all_spec in ism; tc. now specialize (ism _ hin).
  - intros [v clssem].
    move: hi.
    funelim (infer_model cls) => //. intros _.
    red in islooping.
    have sem := clauses_sem_entails_all islooping v0.
    specialize (sem clssem).
    rewrite interp_add_prems in sem. lia.
Qed.

Definition valid_entailment cls cl := forall V, clauses_sem V cls -> clause_sem V cl.

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

Definition premises_of_level_set (l : LevelSet.t) :=
  LevelSet.fold (fun l acc => (l, 0) :: acc) l [].

Definition extendV V (cl : clause) :=
  let '(prems, concl) := cl in
  (add_list (premises_of_level_set V) prems, concl).

Lemma premises_model_map_min_premise {levels cls prems z} :
  min_premise (premises_model_map (zero_model levels) cls) prems = Some z ->
  (exists minp mink, LevelExprSet.In (minp, mink) prems /\
    exists maxp, max_clause_premise_of minp cls = Some maxp /\
    z = maxp - mink) \/
  (exists minp mink, LevelExprSet.In (minp, mink) prems /\ z + mink <= 0)%Z.
Proof.
  set (m := premises_model_map _ _).
  have [minple [[minp mink] [inminp mineq]]] := min_premise_spec m prems.
  rewrite mineq. rewrite /min_atom_value.
  destruct level_value eqn:hl => //. intros [= <-].
  eapply level_value_MapsTo' in hl.
  eapply premises_model_map_spec in hl as [[inpcls [hm _]]|[ninpcls h']]. left.
  2:{ apply zero_model_spec in h' as [h' [= ->]]. }
  exists minp, mink. split => //. noconf hm. rewrite -hm.
  eexists; split => //.
Qed.

Lemma premises_model_map_min_premise_inv {levels cls} :
  forall cl, Clauses.In cl cls ->
  exists z, min_premise (premises_model_map (zero_model levels) cls) (premise cl) = Some z /\ (0 <= z)%Z.
Proof.
  set (m := premises_model_map _ _).
  move=> cl hin.
  have [minple [[minp mink] [inminp mineq]]] := min_premise_spec m (premise cl).
  rewrite mineq. rewrite /min_atom_value.
  destruct level_value eqn:hl => //.
  - eexists. split; trea.
    have ps := proj1 (premises_model_map_spec _ cls minp (Some z)) (level_value_MapsTo' hl).
    destruct ps as [[minpsl [eq _]]|].
    * symmetry in eq.
      have sp := (max_clause_premise_of_spec _ _ _ _ hin inminp).
      depelim sp. rewrite eq in H0. noconf H0. lia.
    * destruct H. elim H.
      eapply clauses_premises_levels_spec. exists cl. split => //.
      eapply levelexprset_levels_spec. now exists mink.
  - unfold level_value in hl.
    destruct LevelMap.find eqn:hl'. subst o.
    2:{ move/LevelMapFact.F.not_find_in_iff: hl'. elim.
      rewrite premises_model_map_in. left.
      eapply clauses_premises_levels_spec. exists cl. split => //.
      eapply levelexprset_levels_spec. now exists mink. }
    eapply LevelMap.find_2 in hl'.
    move/premises_model_map_spec: hl' => [[]|[nin hm]] => //.
    * now intros hnminp [_ hn].
    * move: nin; elim.
      eapply clauses_premises_levels_spec. exists cl. split => //.
      eapply levelexprset_levels_spec. now exists mink.
Qed.

Lemma is_update_of_entails {cls V m m' hne hne'} : is_update_of cls V m m' ->
  cls ⊢a of_level_map m hne → of_level_map m' hne'.
Proof.
  rewrite /is_update_of.
  destruct LevelSet.is_empty.
  - intros heq [].
    rewrite !of_level_map_spec. rewrite -heq.
    constructor. now apply of_level_map_spec.
  - eapply strictly_updates_entails.
Qed.

Lemma is_update_of_non_empty {cls V m m'} : ~ LevelMap.Empty m ->
  is_update_of cls V m m' ->
  ~ LevelMap.Empty m'.
Proof.
  rewrite /is_update_of. destruct LevelSet.is_empty.
  - now intros he <-.
  - intros he su. now eapply strictly_updates_non_empty_map in su.
Qed.

Instance defined_map_proper : Proper (LevelMap.Equal ==> iff) defined_map.
Proof.
  intros x y eq; rewrite /defined_map.
  now setoid_rewrite eq.
Qed.

Lemma is_update_of_defined_map {cls V m m'} : defined_map m ->
  is_update_of cls V m m' ->
  defined_map m'.
Proof.
  rewrite /is_update_of. destruct LevelSet.is_empty.
  - now intros he <-.
  - intros he su. now eapply strictly_updates_defined_map in su.
Qed.

Lemma inj_add_prems_sub {n u u'} : add_prems n u ⊂_leset add_prems n u' -> u ⊂_leset u'.
Proof.
  rewrite /add_prems.
  intros hm [l k]. specialize (hm (l, k + n)).
  rewrite !map_spec in hm.
  intros hin.
  forward hm. exists (l, k); split => //.
  destruct hm as [[] [hin' eq]].
  apply (@add_expr_inj n (l, k)) in eq. now noconf eq.
Qed.

Lemma premises_of_level_set_spec l k V : LevelSet.In l V /\ k = 0 <-> In (l, k) (premises_of_level_set V).
Proof.
  rewrite /premises_of_level_set.
  eapply LevelSetProp.fold_rec.
  - intros s' he. firstorder.
  - intros x a s' s'' hin hnin hadd ih.
    red in hadd. rewrite {}hadd.
    cbn. firstorder. subst. now left. noconf H1. now left. now noconf H1.
Qed.

Lemma in_succ_add_premises {V u x k} : LevelExprSet.In (x, Z.of_nat (k + 1)) (add_list (premises_of_level_set V) u) -> LevelExprSet.In (x, Z.of_nat (k + 1)) u.
Proof.
  rewrite add_list_spec. intros [hn|hn] => //.
  eapply premises_of_level_set_spec in hn as []. lia.
Qed.

(* Lemma inj_succ_prems {V u u'} : succ_prems u ⊂_leset add_list (premises_of_level_set V) u' -> succ_prems u ⊂_leset u'.
Proof.
  intros sub x. rewrite In_add_prems => [] [[l k] [hin ->]].
  specialize (sub (l, Z.of_nat (k + 1))).
  forward sub.
  apply In_add_prems. exists (l, k). split => //.
  now apply in_succ_add_premises in sub.
Qed. *)

Lemma succ_clauses_equiv cls prems concl :
  succ_clauses cls ⊢ succ_prems prems → succ_expr concl ->
  cls ⊢ prems → concl.
Proof.
  intros ha; depind ha.
  - constructor.
    move: H.
    rewrite In_add_prems => [] [le [hin heq]].
    move/add_expr_inj: heq. now intros ->.
  - depelim H.
    + destruct cl as [prems concl]. noconf H0.
      eapply in_add_clauses in H as [[prems' concl'] [hin heq]].
      noconf heq.
      eapply (clause_cut _ (add_prems n prems') (add_expr n concl')). 2:eapply IHha.
      2:{ f_equal. rewrite !add_expr_add_expr. now rewrite add_prems_add add_expr_add_expr Z.add_comm. }
      exact: (incls cls (prems', concl') n hin).
      rewrite add_prems_add_prems in H1. rewrite Z.add_comm in H1.
      rewrite -(add_prems_add_prems 1 n prems') in H1.
      now move/inj_add_prems_sub: H1.
    + specialize (H0 (x, k + 1)). forward H0. now apply LevelExprSet.singleton_spec.
      eapply In_add_prems in H0 as [[l' k'] [hin heq]]. noconf heq.
      have eq: k' = k by lia. subst k'. clear H.
      eapply clause_cut. 2:eapply IHha. eapply (predcl _ x (k - 1)).
      2:{ intros x'. move/LevelExprSet.singleton_spec => ->. now have -> : k - 1 + 1 = k by lia. }
      f_equal. rewrite add_prems_add. f_equal.
      rewrite /succ_expr //=. lia_f_equal.
Qed.

Lemma entails_weak_list {cls prem concl concl'} :
  cls ⊢ prem → concl ->
  cls ⊢ add_list concl' prem → concl.
Proof.
  intros hcl.
  induction concl' in prem, hcl |- *.
  - exact hcl.
  - cbn. eapply IHconcl'. now eapply entails_weak.
Qed.

Lemma entails_all_weak_list {cls prem concl concl'} :
  entails_all cls prem concl ->
  entails_all cls (add_list concl' prem) concl.
Proof.
  intros hcl x hin.
  specialize (hcl _ hin). cbn in hcl.
  now eapply entails_weak_list.
Qed.

Lemma premises_of_level_set_empty : premises_of_level_set LevelSet.empty = [].
Proof.
  now rewrite /premises_of_level_set LevelSetProp.fold_empty.
Qed.

(* Lemma succ_clauses_equiv_weak cls prems concl :
  succ_clauses cls ⊢ succ_prems prems → succ_expr concl ->
  cls ⊢ prems → concl.
Proof.
  move/(entails_weak_list (concl' := [])) => he.
  eapply (succ_clauses_equiv _ LevelSet.empty).
  cbn. now rewrite premises_of_level_set_empty.
Qed. *)

Lemma entails_all_succ_clauses cls prems concl :
  succ_clauses cls ⊢a succ_prems prems → succ_prems concl ->
  cls ⊢a prems → concl.
Proof.
  intros ha l hin. specialize (ha (succ_expr l)). forward ha.
  eapply In_add_prems. exists l. split => //. cbn in ha.
  now eapply succ_clauses_equiv in ha.
Qed.

Definition entails_equiv cls u u' :=
  cls ⊢a u → u' /\ cls ⊢a u' → u.

Notation "cls '⊢a' u ↔ u'" := (entails_equiv cls u u') (at level 90).

Lemma max_premise_of_spec_aux s l k :
  max_premise_of l s = k ->
  (forall k', LevelExprSet.In (l, k') s -> (Some k' ≤ k)) /\
  ((exists k', LevelExprSet.In (l, k') s /\ k = Some k') \/
    ((~ exists k', LevelExprSet.In (l, k') s) /\ k = None)).
Proof.
  unfold max_premise_of.
  revert k.
  eapply LevelExprSetProp.fold_rec.
  - intros s' he k <-. cbn. split => //.
    * now move=> k' /he.
    * right; split => //. now move=> [] k' /he.
  - intros [l' k'] a s' s'' hin hnin hadd ih k.
    specialize (ih _ eq_refl) as [hle hex].
    intros hmax.
    split. move=> k'0 /hadd => [] [].
    { move=> [=] eq eq'. subst l' k'. rewrite eqb_refl in hmax.
      destruct a; cbn in hmax; subst; constructor; lia. }
    { move/hle. move: hmax. destruct (eqb_spec l l'); subst.
      intros <-. intros h; depelim h; cbn. constructor; lia.
      intros -> h; depelim h; constructor; lia. }
    destruct hex as [[k'' [hin' heq]]|nex]. subst a.
    { left. destruct (eqb_spec l l'). subst. exists (Z.max k' k''); split; trea.
      2:{ subst k. eexists; split => //. apply hadd. now right. }
      eapply hadd.
      destruct (Z.max_spec k' k'') as [[hlt ->]|[hle' ->]] => //. now right. now left. }
    destruct nex as [nex ->].
    destruct (eqb_spec l l'). subst. left. exists k'. split => //. apply hadd; now left.
    subst k. right. split => //.
    intros [k'' hin']. apply hadd in hin' as []. noconf H0. congruence.
    apply nex. now exists k''.
Qed.

Lemma max_premise_of_prems_max {l prems k} :
  max_premise_of l prems = Some k -> LevelExprSet.In (l, k) prems.
Proof.
  destruct max_premise_of eqn:maxp => //. intros [= ->].
  apply max_premise_of_spec_aux in maxp as [hle hex].
  destruct hex as [[k' [hin [= ->]]]|hne] => //.
  destruct hne; congruence.
Qed.

Lemma max_premise_of_singleton l k : max_premise_of l (singleton (l, k)) = Some k.
Proof.
  remember (max_premise_of l (singleton (l, k))) as mp. symmetry in Heqmp.
  apply max_premise_of_spec_aux in Heqmp as [hle hex].
  destruct hex as [[k' [hin heq]]|hne] => //.
  eapply LevelExprSet.singleton_spec in hin. now noconf hin.
  destruct hne as [nein ->]. elim nein.
  exists k. now eapply LevelExprSet.singleton_spec.
Qed.

Lemma max_premise_of_spec2 l k (u : premises) : LevelExprSet.In (l, k) u ->
  exists k', LevelExprSet.In (l, k') u /\ max_premise_of l u = Some k'.
Proof.
  remember (max_premise_of l u) as mp. symmetry in Heqmp.
  apply max_premise_of_spec_aux in Heqmp as [hle hex].
  intros hin. destruct hex. firstorder.
  destruct H as [nein ->]. elim nein. now exists k.
Qed.

Lemma max_premise_of_spec_in l (u : premises) : LevelSet.In l (levels u) ->
  exists k, max_premise_of l u = Some k /\ LevelExprSet.In (l, k) u.
Proof.
  intros hexi.
  remember (max_premise_of l u) as mp. symmetry in Heqmp.
  apply max_premise_of_spec_aux in Heqmp as [hle hex].
  destruct hex. destruct H as [l' [hin heq]]. subst mp.
  - eexists; split => //.
  - destruct H as [nein ->]. elim nein.
    now eapply levelexprset_levels_spec in hexi.
Qed.

(* Lemma of_level_map_premises_model_map cls cl V ne :
  (forall l, LevelSet.In l (clause_levels cl) -> LevelSet.In l V) ->
  cls ⊢a add_list (premises_of_level_set V) (premise cl) → of_level_map (premises_model_map (zero_model V) (Clauses.singleton cl)) ne.
Proof.
  intros hin [l k].
  rewrite of_level_map_spec. move/premises_model_map_spec; cbn.
  rewrite max_opt_of_l.
  cbn; rewrite LevelSet.union_spec. firstorder try lsets.
  cbn in H1.
  - rewrite Z.max_comm.
    destruct (Z.max_spec 0 (max_premise_of l (premise cl))) as [[hle ->]|[hge ->]].
    * constructor. rewrite add_list_spec; right.
      now eapply max_premise_of_spec_in.
    * constructor. rewrite add_list_spec. left.
      apply premises_of_level_set_spec. split => //.
      apply hin. apply clause_levels_spec. now left.
  - eapply zero_model_spec in H1 as [hin' [= ->]].
Qed. *)

(* Lemma max_premise_of_pos l prems : max_premise_of l prems >= 0.
Proof.
  have hs := max_premise_of_spec_aux prems l.
  destruct max_premise_of. lia. lia.
  specialize (hs _ eq_refl) as [_ [[k' []]|[_ hne]]]; lia.
Qed.
 *)

Lemma of_level_map_premises_model_map cls cl V ne :
  cls ⊢a premise cl → of_level_map (premises_model_map (zero_model V) (Clauses.singleton cl)) ne.
Proof.
  intros [l k].
  rewrite of_level_map_spec. move/premises_model_map_spec; cbn.
  intros [[hin' [[= heq] _]]|[hnin hm]].
  2:{ now apply zero_model_spec in hm as []. }
  move: hin'; cbn; rewrite LevelSet.union_spec. intros []; [|lsets].
  eapply max_premise_of_spec_in in H as [maxp' [eq hin']].
  rewrite eq in heq; noconf heq.
  now constructor.
Qed.

Lemma entails_all_satisfies {cls prems m hne l k} :
  cls ⊢a prems → of_level_map m hne ->
  infers_atom m l k ->
  cls ⊢ prems → (l, k).
Proof.
  intros hl hi.
  eapply entails_all_one; tea. now apply infers_atom_of_level_map.
Qed.

Lemma premises_model_map_ne V cls :
  ~ LevelMap.Empty V ->
  ~ LevelMap.Empty (premises_model_map V cls).
Proof.
  intros ne he. apply ne.
  have ne' := premises_model_map_in V cls.
  intros l k hin.
  specialize (ne' l). destruct ne'. forward H0. right. now exists k.
  destruct H0 as [k' hin'].
  now move/he: hin'.
Qed.

Lemma clauses_ne_exist cls : ~ Clauses.Empty cls -> exists cl, Clauses.In cl cls.
Proof.
  intros ne.
  destruct (Clauses.choose cls) eqn:hc.
  - exists e. now apply Clauses.choose_spec1 in hc.
  - now apply Clauses.choose_spec2 in hc.
Qed.

Lemma premises_model_map_defined V cls :
  ~ Clauses.Empty cls ->
  defined_map (premises_model_map V cls).
Proof.
  move/clauses_ne_exist => [cl hin].
  destruct cl as [prems concl].
  pose proof (to_nonempty_list_spec' prems).
  set (l := (to_nonempty_list prems).1) in *.
  have hs := max_clause_premise_of_spec l l.2 cls (prems, concl) hin.
  forward hs. cbn. eapply LevelExprSet.elements_spec1; rewrite -H.
  constructor. destruct l; reflexivity. depelim hs.
  exists l, y. apply premises_model_map_spec. left.
  split => //.
  eapply clauses_premises_levels_spec. eexists; split; tea => //.
  rewrite //= levelexprset_levels_spec. exists l.2.
  setoid_rewrite <- LevelExprSet.elements_spec1. rewrite -H //=.
  constructor. destruct l; reflexivity.
Qed.

Variant check_result {cls} :=
  | IsLooping (v : premises) (islooping : loop_on_univ cls v)
  | Invalid
  | Valid.
Arguments check_result : clear implicits.

Equations check_atom_value (z : option Z) (l : option Z) : bool :=
  | Some _, None => false
  | Some z, Some v => z <=? v
  | None, _ => true.

Lemma check_atom_value_spec z l : reflectProp (z ≤ l) (check_atom_value z l).
Proof.
  funelim (check_atom_value z l).
  - destruct (Z.leb_spec z v); constructor.
    * now constructor.
    * intros h; depelim h. lia.
  - constructor. intros h; depelim h.
  - constructor. constructor.
Qed.

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
    | IsLooping v isl => false
    | Valid => true
    | Invalid => false
    end
  in
  Clauses.for_all check_one cls'.

(* If a clause checks, then it should be valid in any extension of the model *)
Lemma check_entails {cls cl} :
  check cls cl = Valid -> valid_entailment cls cl.
Proof.
  destruct cl as [prems [concl k]].
  funelim (check cls _) => // _.
  set (V := clause_levels _ ∪ clauses_levels cls) in *.
  clear Heqcall H. cbn [concl fst snd] in *. clear Heq0.
  unfold valid_entailment, valid_clause, level_value_above.
  move/check_atom_value_spec: Heq; intros h; depelim h. rename H into hgt.
  intros valuation ext.
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
  eapply clauses_sem_entails in tr ; tea.
Qed.

Definition invalid_entailment cls cl :=
  forall V, clauses_sem V cls -> clause_sem V cl -> False.

Definition infers_univ (m : model) (u : premises) :=
  exists z, min_premise m u = Some z /\ (0 <= z)%Z.

Definition infers_expr (m : model) (le : LevelExpr.t) :=
  let '(l, k) := le in infers_atom m l k.

Lemma valid_clause_elim {m prems concl k} : valid_clause m (prems, (concl, k)) ->
  forall z, min_premise m prems = Some z ->
  Some (z + k) ≤ level_value m concl.
Proof.
  rewrite /valid_clause => hcl z eqmin.
  rewrite eqmin in hcl. cbn in *.
  move: hcl. rewrite /level_value_above. destruct level_value eqn:hl => //.
  move/Z.leb_le. constructor. lia.
Qed.

Lemma valid_clause_intro {m prems concl k} :
  (forall z,
    min_premise m prems = Some z ->
    Some (z + k) ≤ level_value m concl) ->
  valid_clause m (prems, (concl, k)).
Proof.
  rewrite /valid_clause //=.
  destruct min_premise => //.
  intros hz.
  specialize (hz _ eq_refl). depelim hz.
  rewrite /level_value_above H0.
  apply Z.leb_le. lia.
Qed.

Lemma infers_expr_min_atom_value m le : infers_expr m le -> exists k, min_atom_value m le = Some k /\ (0 <= k)%Z.
Proof.
  destruct le as [l k]; rewrite /infers_expr //=.
  rewrite /infers_atom. destruct level_value => // hle; depelim hle.
  eexists; split; trea. lia.
Qed.

Lemma min_premise_add_infers m prems le lev :
  level_value m le.1 = Some lev ->
  forall z, min_premise m prems = Some z ->
  exists z', min_premise m (add le prems) = Some z' /\
    ((z' = lev - le.2 /\ z' <= z) \/ z' = z).
Proof.
  intros hlev z hmin.
  have [hle [min' [hin hm]]] := min_premise_spec m (add le prems).
  have [hle' [min'' [hin' hm']]] := min_premise_spec m prems.
  move/LevelExprSet.add_spec: hin => [heq|hin].
  - noconf heq. destruct le as [le k].
    rewrite /min_atom_value hlev in hm.
    eexists; split => //; trea. left.
    specialize (hle min''). forward hle.
    { rewrite LevelExprSet.add_spec. now right. }
    rewrite hm -hm' hmin in hle. now depelim hle.
  - exists z. split => //. 2:right; reflexivity. rewrite hm -hmin hm'.
    move: (hle' _ hin). rewrite hmin. intros h; depelim h.
    rewrite H0 in hm.
    specialize (hle min''). forward hle. eapply LevelExprSet.add_spec. now right.
    rewrite hm in hle. rewrite -hm' hmin in hle. depelim hle.
    rewrite H0 -hm' hmin. f_equal. lia.
Qed.

Lemma fold_left_map {A B C} (f : B -> A -> A) (g : C -> B) l acc :
  fold_left (fun acc l => f (g l) acc) l acc =
  fold_left (fun acc l => f l acc) (List.map g l) acc.
Proof.
  induction l in acc |- *; cbn; auto.
Qed.

Lemma fold_left_max_acc {n l} : (forall x, In x l -> x = n) -> n = fold_left (option_map2 Z.min) l n.
Proof.
  induction l in n |- *.
  - now cbn.
  - cbn. intros he. transitivity (option_map2 Z.min n a). 2:apply IHl.
    specialize (he a). forward he. now left. subst. destruct n => //= //. lia_f_equal.
    intros. have h := (he x). forward h by now right.
    have h' := (he a). forward h' by now left. subst.
    destruct n => //=; lia_f_equal.
Qed.

Lemma option_map2_comm x y : option_map2 Z.min x y = option_map2 Z.min y x.
Proof.
  destruct x, y; cbn; lia_f_equal.
Qed.

Lemma option_map2_assoc x y z :
  option_map2 Z.min x (option_map2 Z.min y z) =
  option_map2 Z.min (option_map2 Z.min x y) z.
Proof.
  destruct x, y, z; cbn; lia_f_equal.
Qed.

Local Notation fn := (fold_left (option_map2 Z.min)).

Lemma fold_left_impl n l :
  (forall x, In x (n :: l) -> fn l n ≤ x) /\
  (exists x, In x (n :: l) /\ fn l n = x).
Proof.
  induction l in n |- *.
  - cbn. split; intros.
    destruct H => //. subst. reflexivity.
    exists n. split => //. now left.
  - cbn. split; intros.
    { destruct (IHl n) as [hle [min [hin heq]]].
    rewrite fold_left_comm.
    { now intros; rewrite -option_map2_assoc (option_map2_comm x0 y) option_map2_assoc. }
    repeat destruct H; subst.
    * specialize (hle n). forward hle. now left.
      transitivity (fn l n); auto. eapply Zmin_opt_left.
    * eapply Zmin_opt_right.
    * transitivity (fn l n); auto. apply Zmin_opt_left.
      apply hle. now right. }
    * specialize (IHl (option_map2 Z.min n a)).
      destruct IHl as [hle [min [hin heq]]]. subst min. eexists. split; trea.
      destruct hin.
      rewrite -H.
      destruct n, a; cbn; firstorder.
      destruct (Z.min_spec z z0) as [[? heq]|[? heq]].
      rewrite -{1}heq. now left. right; left. f_equal. lia.
      now right.
Qed.

Lemma fold_left_impl_eq n n' l l' :
  (forall x, In x (n :: l) <-> In x (n' :: l' )) ->
  fn l n = fn l' n'.
Proof.
  intros heq.
  destruct (fold_left_impl n l) as [hle [minl [hin heq']]].
  destruct (fold_left_impl n' l') as [hle' [minl' [hin' heq'']]].
  rewrite heq' heq''.
  specialize (hle minl'). forward hle. now apply heq.
  specialize (hle' minl). forward hle'. now apply heq.
  rewrite heq'' in hle'. rewrite heq' in hle. depelim hle'. depelim hle. f_equal; lia.
  now depelim hle.
Qed.

Lemma fold_left_comm_f {A} (f : A -> A -> A) n l :
  (forall x y, f x y = f y x) ->
  fold_left f l n = fold_left (flip f) l n.
Proof.
  induction l in n |- *; cbn; auto.
  intros hf. rewrite IHl //.
  unfold flip. now rewrite hf.
Qed.

Lemma min_premise_add {m le prems} : min_premise m (add le prems) =
  option_map2 Z.min (min_atom_value m le) (min_premise m prems).
Proof.
  rewrite {1}/min_premise.
  have hs' := to_nonempty_list_spec (add le prems).
  destruct to_nonempty_list.
  have eqf : (fold_left (fun (min : option Z) (atom : LevelExpr.t) => option_map2 Z.min (min_atom_value m atom) min) l (min_atom_value m p)) =
    (option_map2 Z.min (min_atom_value m le) (min_premise m prems)).
  2:{ now rewrite eqf. }
  rewrite -(to_nonempty_list_spec' (add le prems)) in hs'. noconf hs'.
  rewrite fold_left_map. rewrite fold_left_comm_f. intros [] []; cbn; auto. lia_f_equal. unfold flip.
  have l := fold_left_impl_eq (min_atom_value m (to_nonempty_list (add le prems)).1) (min_atom_value m le)
    (List.map (min_atom_value m) (to_nonempty_list (add le prems)).2) (List.map (min_atom_value m) (LevelExprSet.elements prems)).
  rewrite l.
  intros x.
  { rewrite -!map_cons to_nonempty_list_spec' !in_map_iff.
    split.
    - move=> [] lk [] <-.
      rewrite -InA_In_eq.
      move/LevelExprSet.elements_spec1.
      rewrite LevelExprSet.add_spec.
      intros [->|inp].
      * exists le. split => //. now left.
      * exists lk. split => //. right. now apply InA_In_eq, LevelExprSet.elements_spec1.
    - intros [x' [<- hin]].
      exists x'. split => //. rewrite -InA_In_eq.
      eapply LevelExprSet.elements_spec1. rewrite LevelExprSet.add_spec.
      apply InA_In_eq in hin. depelim hin. now left.
      eapply LevelExprSet.elements_spec1 in hin. now right. }
  rewrite option_map2_comm.
  rewrite /min_premise.
  destruct (to_nonempty_list prems) eqn:he.
  rewrite fold_left_map.
  rewrite (fold_left_comm_f _ _ (List.map _ l0)). intros. apply option_map2_comm.
  rewrite -(fold_left_comm (option_map2 Z.min)).
  { intros. now rewrite -option_map2_assoc (option_map2_comm x y) option_map2_assoc. }
  rewrite -(to_nonempty_list_spec' prems) he; cbn.
  now rewrite option_map2_comm.
Qed.

Lemma min_premise_elim m (P : premises -> option Z -> Prop):
  (forall le, P (singleton le) (min_atom_value m le)) ->
  (forall prems acc le, P prems acc -> ~ LevelExprSet.In le prems -> P (add le prems) (option_map2 Z.min (min_atom_value m le) acc)) ->
  forall prems, P prems (min_premise m prems).
Proof.
  intros hs hadd.
  eapply premises_elim.
  - intros le. rewrite /min_premise.
    rewrite singleton_to_nonempty_list. cbn. apply hs.
  - intros le prems hp. now rewrite min_premise_add.
Qed.

Lemma min_premise_add_down {m} {prems : premises} {l k} :
  LevelExprSet.In (l, k + 1) prems ->
  forall z, min_premise m prems = Some z ->
       min_premise m (add (l, k) prems) = Some z.
Proof.
  intros ine z hmin.
  have [hle [min' [hin hm]]] := min_premise_spec m (add (l, k) prems).
  have [hle' [min'' [hin' hm']]] := min_premise_spec m prems.
  move/LevelExprSet.add_spec: hin => [heq|hin].
  - noconf heq.
    specialize (hle (l, k + 1)).
    forward hle. eapply LevelExprSet.add_spec. now right.
    rewrite hm in hle.
    depelim hle. destruct level_value eqn:hl. noconf H0; noconf H1. lia. congruence.
    destruct level_value eqn:hl' => //.
    specialize (hle' _ ine). rewrite hmin in hle'; depelim hle'.
    now rewrite hl' in H1.
  - rewrite hm. specialize (hle' min' hin). rewrite hmin in hle'.
    depelim hle'. rewrite H0. f_equal. rewrite H0 in hm.
    specialize (hle min''). forward hle. eapply LevelExprSet.add_spec. now right.
    rewrite hm in hle. rewrite -hm' hmin in hle. depelim hle. lia.
Qed.


Lemma min_premise_singleton m u : min_premise m (singleton u) = min_atom_value m u.
Proof.
  now rewrite /min_premise singleton_to_nonempty_list; cbn.
Qed.

Lemma min_atom_value_add m e x n :
  min_atom_value m e = Some x ->
  min_atom_value m (add_expr n e) = Some (x - n)%Z.
Proof.
  rewrite /min_atom_value. destruct e. cbn.
  destruct level_value => //. intros [= <-].
  f_equal. lia.
Qed.


Lemma min_atom_value_add_inv m e x n :
  min_atom_value m (add_expr n e) = Some x ->
  min_atom_value m e = Some (x + n)%Z.
Proof.
  rewrite /min_atom_value. destruct e. cbn.
  destruct level_value => //. intros [= <-].
  f_equal. lia.
Qed.

Lemma min_premise_add_prems {m n prems z} : min_premise m prems = Some z -> min_premise m (add_prems n prems) = Some (z - n)%Z.
Proof.
  revert z.
  eapply min_premise_elim.
  - intros le hm.
    destruct le as [concl k].
    rewrite add_prems_singleton min_premise_singleton.
    apply min_atom_value_add.
  - intros prems' acc le ih nle z hm.
    destruct acc; cbn in hm. 2:{ destruct (min_atom_value m le); cbn in hm; congruence. }
    specialize (ih _ eq_refl).
    rewrite add_prems_add min_premise_add.
    destruct (min_atom_value m le) eqn:hm'; cbn in hm => //. noconf hm.
    apply (min_atom_value_add _ _ _ n) in hm'.
    rewrite ih hm'. cbn. f_equal. lia.
Qed.

Lemma min_premise_add_prems_inv {m n prems z} : min_premise m (add_prems n prems) = Some z ->
  min_premise m prems = Some (z + n)%Z.
Proof.
  revert z.
  pattern prems.
  set (P := (fun n0 hm =>
  forall z : Z,
    min_premise m (add_prems n n0) = Some z -> hm = Some (z + n)%Z)).
  apply (@min_premise_elim _ P); subst P; cbn.
  - intros le z hm.
    destruct le as [concl k].
    rewrite add_prems_singleton min_premise_singleton in hm.
    now apply min_atom_value_add_inv.
  - intros prems' acc le ih nle z.
    rewrite add_prems_add min_premise_add.
    destruct (min_premise m (add_prems n prems')) eqn:he => //=.
    * destruct (min_atom_value m (add_expr n le)) eqn:ha => //=.
      intros [= <-].
      eapply min_atom_value_add_inv in ha. rewrite ha.
      specialize (ih _ eq_refl). subst acc. cbn. lia_f_equal.
    *  destruct (min_atom_value m (add_expr n le)) eqn:ha => //=.
Qed.

Lemma level_value_above_leq {m l k} :
  Some k ≤ level_value m l ->
  level_value_above m l k.
Proof.
  intros h; rewrite /level_value_above.
  depelim h. rewrite H0. apply Z.leb_le. lia.
Qed.

Lemma valid_clause_shift m n cl :
  valid_clause m cl -> valid_clause m (add_clause n cl).
Proof.
  destruct cl as [prems [concl k]].
  move/valid_clause_elim => hv.
  apply valid_clause_intro => z eqmin.
  eapply min_premise_add_prems_inv in eqmin.
  specialize (hv _ eqmin).
  etransitivity; tea. constructor; lia.
Qed.

Lemma entails_model_valid cls cl : entails cls cl ->
  forall m, is_model cls m -> valid_clause m cl.
Proof.
  induction 1.
  - intros m ism.
    destruct concl0 as [concl k].
    apply valid_clause_intro => z hmin.
    eapply min_premise_spec_aux in hmin as [hle [x [hin heq]]].
    specialize (hle _ H). depelim hle.
    destruct level_value eqn:hl => //. noconf H1.
    constructor. lia.
  - intros.
    specialize (IHentails m H2).
    depelim H.
    * destruct cl as [premsc conclc].
      noconf H0.
      eapply Clauses.for_all_spec in H3.
      eapply H3 in H. 2:tc.
      destruct concl0 as [concl k].
      eapply valid_clause_intro => z eqmin.
      have mins := min_premise_subset m (add_prems n premsc) prems H2.
      rewrite eqmin in mins; depelim mins.
      destruct conclc as [conclc k'].
      have vshift : valid_clause m (add_prems n premsc, add_expr n (conclc, k')).
      { now eapply (valid_clause_shift _ n) in H. }
      have hv := valid_clause_elim vshift _ H4.
      depelim hv. rename y0 into vmconclc.
      eapply (min_premise_add_infers _ _ (add_expr n (conclc, k'))) in eqmin as [minadd [eqminadd disj]]; tea.
      move/valid_clause_elim: IHentails => //=.
      move/(_ _ eqminadd).
      destruct disj as [[eq le']| ->].
      + move=> h. cbn in le'. cbn in eq. subst minadd.
        depelim h. rewrite H8. constructor. lia.
      + intros h; depelim h. rewrite H8; constructor; lia.
    * destruct concl0 as [concl0 k'].
      apply valid_clause_intro => z hmin.
      have mins := min_premise_subset m _ _ H1.
      rewrite min_premise_singleton in mins.
      specialize (H1 (x, k+1)); forward H1 by now apply LevelExprSet.singleton_spec.
      have hadd := min_premise_add_down H1 _ hmin.
      exact: valid_clause_elim IHentails _ hadd.
Qed.

Lemma check_entails_looping {cls cl v isl} :
  check cls cl = IsLooping v isl -> cls ⊢a v → succ_prems v.
Proof.
  funelim (check cls cl) => //.
Qed.

Lemma enabled_clause_ext {m m' cl} :
  m ⩽ m' -> enabled_clause m cl -> enabled_clause m' cl.
Proof.
  intros hext; rewrite /enabled_clause.
  destruct cl as [prems [concl k]]; cbn; move=> [z hm].
  have pr := min_premise_pres prems hext.
  rewrite hm in pr. depelim pr. now exists y.
Qed.

Lemma check_entails_false {cls cl} :
  check cls cl = Invalid -> ~ entails cls cl.
Proof.
  funelim (check cls cl) => //.
  set (V := clause_levels cl ∪ clauses_levels cls) in *.
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


(* To infer an extension, we weaken a valid model for V to a model for [V ∪ clauses_levels cls] by
   setting a minimal value for the new atoms in [clauses_levels cls \ V]
   such that the new clauses [cls] do not hold vacuously.
*)

Equations add_max (l : Level.t) (k : option Z) (m : model) : model :=
add_max l k m with level_value m l :=
  { | Some k' with check_atom_value k (Some k') :=
    { | true => m
      | false => LevelMap.add l k m }
  | None => LevelMap.add l k m }.

Lemma nleq_optZ k k' : ~ k ≤ Some k' -> exists z, k = Some z /\ k' < z.
Proof.
  destruct k.
  - exists z. split => //. eapply Znot_ge_lt => hl; apply H. constructor. lia.
  - elim. constructor.
Qed.

Lemma add_max_spec l l' k k' (m : model) :
  LevelMap.MapsTo l k (add_max l' k' m) <->
  (l = l' /\ k = max_opt_of Z.max k' (level_value m l)) \/
  (l <> l' /\ LevelMap.MapsTo l k m).
Proof.
  funelim (add_max l' k' m).
  - rewrite LevelMapFact.F.add_mapsto_iff /Level.eq. firstorder; subst.
    left. split => //. rewrite Heq. now rewrite max_opt_of_l.
    left. firstorder. now rewrite Heq max_opt_of_l.
  - clear Heqcall.
    destruct (eq_dec l0 l).
    * subst l0. rewrite Heq0.
      move/check_atom_value_spec: Heq.
      rewrite (maps_to_update (level_value_MapsTo' Heq0)).
      firstorder; subst; try left; try split; auto; depelim Heq; cbn; lia_f_equal.
    * firstorder.
  - rewrite LevelMapFact.F.add_mapsto_iff /Level.eq.
    have := check_atom_value_spec k (Some k'). rewrite {}Heq.
    intros h; depelim h. apply nleq_optZ in H as [z [-> hlt]].
    firstorder; subst.
    * left; split => //. rewrite Heq0 //=. lia_f_equal.
    * left; split => //. rewrite Heq0 //=. lia_f_equal.
Qed.

Definition min_model_clause cl m :=
  LevelExprSet.fold (fun '(l, k) acc => add_max l (Some k) acc) (premise cl)
    (add_max (concl cl) None m).

Definition min_model_map (m : model) cls : model :=
  Clauses.fold min_model_clause cls m.

Lemma In_add_max l l' k acc :
  LevelMap.In l (add_max l' k acc) <-> (l = l' \/ LevelMap.In l acc).
Proof.
  rewrite /LevelMap.In.
  rw add_max_spec. firstorder subst.
  eexists; left; eauto.
  destruct (eq_dec l l'); subst; eexists; eauto.
Qed.

Definition is_max k' k l acc :=
  match LevelMap.find l acc with
  | Some k'' => k' = Nat.max k k''
  | _ => k' = k
  end.

Lemma max_opt_of_spec {x y k'} : max_opt_of Z.max x y = k' ->
  (x ≤ y /\ k' = y) \/ (y ≤ x /\ k' = x).
Proof.
  destruct x, y; cbn; firstorder subst.
  - destruct (Z.max_spec z z0) as [[]|[]];
    [left|right]; split; try constructor; lia_f_equal.
  - right. split; constructor.
  - left. split; constructor.
  - left; split; constructor.
Qed.

Definition max_of_premises l kl n :=
  (forall kl', LevelExprSet.In (l, kl') n -> Some kl' ≤ kl).

Definition is_expr l (e : LevelExpr.t) :=
  let '(concl, k) := e in concl = l.

Definition max_of_clause l kl cl :=
  max_of_premises l kl (premise cl).

Definition max_of_map l kl m :=
  (forall kl', LevelMap.MapsTo l kl' m -> kl' ≤ kl).

Definition is_max_of_clause_and_map l cl m k :=
  max_of_premises l k (premise cl) /\ max_of_map l k m.

Definition is_in_premise l k (u : LevelExprSet.t) :=
  (exists kl, LevelExprSet.In (l, kl) u /\ k = Some kl).

Definition is_in_clause l k (cl : clause) :=
  is_in_premise l k (premise cl) \/ (l = (clause_conclusion cl) /\ k = None).

Definition is_max_of_clause_model l cl m k :=
  is_max_of_clause_and_map l cl m k /\
  (is_in_clause l k cl \/ LevelMap.MapsTo l k m).

Definition is_higher l k m := exists k', LevelMap.MapsTo l k' m /\ k ≤ k'.

Definition is_max_of_clause_map (map : model) l cl (m : model) : Prop :=
  (forall k, LevelMap.MapsTo l k map -> is_max_of_clause_model l cl m k)
  /\ (forall l k, LevelMap.MapsTo l k m \/ is_in_clause l k cl -> is_higher l k map).


Lemma max_opt_of_le_l z z' : z ≤ max_opt_of Z.max z z'.
Proof.
  destruct z, z'; cbn; constructor; lia.
Qed.

Lemma max_opt_of_le_r z z' : z' ≤ max_opt_of Z.max z z'.
Proof.
  destruct z, z'; cbn; constructor; lia.
Qed.

Lemma is_higher_le l k l' k' m : is_higher l k m -> is_higher l k (add_max l' k' m).
Proof.
  rewrite /is_higher.
  rw add_max_spec.
  intros [k'0 [hm hle]].
  destruct (eq_dec l l').
  - subst. eexists. split; eauto. rewrite (level_value_MapsTo hm).
    transitivity k'0 => //. apply max_opt_of_le_r.
  - exists k'0. split; eauto.
Qed.

Lemma is_higher_add l k m : is_higher l k (add_max l k m).
Proof.
  rewrite /is_higher.
  rw add_max_spec. eexists. split; eauto.
  apply max_opt_of_le_l.
Qed.

Lemma is_higher_mon l k k' m : is_higher l k' m -> k ≤ k' -> is_higher l k m.
Proof.
  intros [? []] le. exists x. split => //. now transitivity k'.
Qed.

Lemma MapsTo_fold_add_max l n a :
  let map := LevelExprSet.fold (fun '(l, k0) acc => add_max l (Some k0) acc) n a in
  (forall k, LevelMap.MapsTo l k map ->
  ((exists kl,
    [/\ LevelExprSet.In (l, kl) n, k = Some kl,
    (forall kl', LevelExprSet.In (l, kl') n -> kl' <= kl) &
    (forall kl', LevelMap.MapsTo l kl' a -> kl' ≤ Some kl)]) \/
    (LevelMap.MapsTo l k a /\ (forall kl', LevelExprSet.In (l, kl') n -> Some kl' ≤ k))))
  /\ (forall l k, LevelMap.MapsTo l k a \/ is_in_premise l k n -> is_higher l k map) /\
  a ⩽ map.
   (* ~ LevelMap.In l map -> ~ (exists k, LevelExprSet.In (l, k) n) /\ ~ (LevelMap.In l a)). *)
Proof.
  eapply LevelExprSetProp.fold_rec.
  - intros s' he. cbn.
    rewrite /is_in_premise /is_higher.
    setoid_rewrite (LevelExprSetProp.empty_is_empty_1 he).
    intuition auto. right. split; eauto.
    intros kl. now move/LevelExprSet.empty_spec.
    exists k; split => //. reflexivity.
    destruct H0 as [x [hin ->]]. now apply LevelExprSet.empty_spec in hin.
    reflexivity.
  - cbn; intros.
    destruct x as [xl k']. split.
    2:{ split.
      { intros l0 hnin. destruct H2 as [hm [H2 _]]. specialize (H2 l0).
      intros [ina|ins''].
      { specialize (H2 hnin (or_introl ina)). eapply is_higher_le; tea. }
      { destruct ins'' as [x [ins'' ->]].
        apply H1 in ins'' as [[=]|ins'].
        * subst. apply is_higher_add.
        * apply is_higher_le, H2. right. eexists; eauto. } }
      { destruct H2 as [_ [_ H2]].
        intros l' hin. move/H2 => [k'0 [hm hle]].
        rw add_max_spec. destruct (eq_dec l' xl).
        - eexists; split. left; eauto. subst l'.
          rewrite (level_value_MapsTo hm). transitivity (k'0) => //.
          apply max_opt_of_le_r.
        - eexists; split; eauto. } }
    intros.
    rewrite add_max_spec in H3; destruct H3 as [[<- hk]|[hdiff hm]].
    * destruct H2 as [hin hnin]. symmetry in hk.
      have [[leacc eqms]|[len eqms]] := max_opt_of_spec hk.
      { depelim leacc. specialize (hin _ (level_value_MapsTo' H3)) as [[kl [inkl [= <-] les' lea]]|].
        { left. exists y. split => //. apply H1; now right. congruence. intros.
          apply H1 in H4 as [[=]|ins']. 2:now apply les'. subst kl'. lia. }
        { destruct H4. right. split. now rewrite -H3 -eqms in H4. intros.
          apply H1 in H6 as [[=]|ins']; subst; trea. rewrite H3; cbn; constructor; lia_f_equal.
          rewrite H3; cbn; constructor. apply H5 in ins'. depelim ins'. lia. } }
      { left. exists k'. split => //.
        * apply H1. now left.
        * move=> kl' /H1 [[=]|ins']. lia. depelim len. transitivity x; tea. specialize (hin _ (level_value_MapsTo' H3)) as
         [[kl [inkl [= <-] les' lea]]|[]].
          { now eapply les'. }
          { specialize (H5 _ ins'). depelim H5. lia. }
          { move: H2 hk. rewrite /level_value. destruct (find_spec l a0).
            * intros ->. apply hin in H2 as [[kl []]|[hm hkl']] => //. apply hkl' in ins'. depelim ins'.
            * intros _; cbn; intros <-.
              destruct hnin as [hnin _].
              specialize (hnin l (Some kl')); forward hnin. right.
              red. exists kl'. split => //.
              destruct hnin as [ka [hma hge]]. elim H2. now exists ka. }
        * subst k. intros kl' mt. move: len. case: level_valueP => [k ma0 le|].
          specialize (hin _ ma0) as [[kl []]|[hm hkl']] => //.
          + subst k. eapply H5 in mt. now depelim le; depelim mt; constructor; lia.
          + transitivity k => //. eapply LevelMapFact.F.MapsTo_fun in mt; tea. subst. reflexivity.
          + intros hnin' _. destruct hnin as [hnin _]. specialize (hnin l kl').
            forward hnin. now left. destruct hnin as [? [hm ?]]. elim hnin'. now exists x. }
    * destruct H2. eapply H2 in hm as [[kl []]|[hm hkl']] => //.
      { left. exists kl. split => //. apply H1. now right. intros kl' h. subst k.
        apply H6. apply H1 in h. destruct h as [[=]|?] => //. subst. congruence. }
      { right. split => //. intros kl' hin. apply H1 in hin as [[=]|?] => //; subst; try congruence. eauto. }
Qed.

Lemma min_model_clause_spec l cl a :
  let map := min_model_clause cl a in
  is_max_of_clause_map map l cl a.
Proof.
  intros m. rewrite /is_max_of_clause_map /is_max_of_clause_model.
  have h := MapsTo_fold_add_max l (premise cl) (add_max (concl cl) None a).
  change (LevelExprSet.fold (fun '(l, k0) (acc : model) => add_max l (Some k0) acc) (premise cl)
      (add_max (concl cl) None a)) with (min_model_clause cl a) in h.
  cbn in h. destruct h. split.
  - intros k hm. specialize (H k hm) as [[kl []]|[hm' hle]].
    * split => //. subst k. red. split. intros kl' hin. constructor. now apply H2.
      move=> kl' hm''. specialize (H3 kl').
      rewrite add_max_spec in H3. forward H3.
      destruct (eq_dec l (concl cl)).
      { subst l. left. split => //. rewrite max_opt_of_r. apply level_value_MapsTo in hm''. now rewrite hm''. }
      { right. split => //. }
      exact H3. left.
      red. left. red. subst k. eauto.
    * rewrite add_max_spec in hm'.
      rewrite max_opt_of_r in hm'. destruct hm' as [[]|[]]; try subst l.
      { repeat split => //.
        { intros l hin'. subst k. rewrite (level_value_MapsTo hin'). reflexivity. }
        { destruct k. right. symmetry in H1. now apply level_value_MapsTo' in H1.
          left. red. right. split => //. } }
      { split => //. split => //.
        { intros l' hin'. eapply LevelMapFact.F.MapsTo_fun in H1; tea. subst. reflexivity. }
        firstorder. }
  - intros l' k. destruct H0 as [H0 hext]. specialize (H0 l' k).
    intros [hm|hinc].
    { forward H0. left. rewrite add_max_spec.
      destruct (eq_dec l' (concl cl)); eauto.
      { left. split => //. rewrite max_opt_of_r.
        now rewrite (level_value_MapsTo hm). }
      destruct H0 as [? [hinm hle]].
      eapply is_higher_mon; tea. exists x. split; eauto. reflexivity. }
    { red in hinc. destruct hinc. apply H0. now right.
      destruct H1 as [-> ->].
      destruct (eq_dec l (concl cl)).
      red.
      destruct (LevelMap.find (concl cl) a) eqn:hl.
      * apply LevelMap.find_2 in hl.
        specialize (hext (concl cl) o).
        forward hext. rewrite add_max_spec. left. split => //.
        rewrite max_opt_of_r. now rewrite (level_value_MapsTo hl).
        destruct hext as [k' []]. exists k'. split => //. constructor.
      * specialize (hext (concl cl) None).
        forward hext. rewrite add_max_spec. left. split => //.
        now rewrite /level_value hl.
        destruct cl; unfold clause_conclusion in *. exact hext.
      * specialize (hext (concl cl) (level_value a (concl cl))).
        forward hext. rewrite add_max_spec. left. split => //.
        destruct hext as [l' []]; exists l'; split => //. constructor. }
Qed.

Lemma min_model_map_acc l cls m :
  let map := min_model_map m cls in
  (forall k, LevelMap.MapsTo l k map -> max_of_map l k m) /\
  m ⩽ map.
Proof.
  cbn. rewrite /min_model_map.
  eapply ClausesProp.fold_rec.
  2:{ intros. destruct H2 as [hf hin].
    have [hm hnin] := min_model_clause_spec l x a.
    split.
    intros k.
    move/hm. rewrite /is_max_of_clause_model. intros [[ism' ism] hasm].
    destruct hasm; eauto. intros kl'. move/hin => [k' [hmk' lek']].
    red in ism. specialize (ism _ hmk'). now transitivity k'.
    transitivity a => //.
    intros l' k ha. specialize (hnin l' k (or_introl ha)).
    exact hnin. }
  split; [|reflexivity].
  intros k hin k' hin'.
  eapply LevelMapFact.F.MapsTo_fun in hin; tea. subst; reflexivity.
Qed.

Lemma max_of_map_ext l k m m' : m ⩽ m' -> max_of_map l k m' -> max_of_map l k m.
Proof.
  intros hext hm l'; move/hext => [k' [hm' le]].
  apply hm in hm'. now transitivity k'.
Qed.

Lemma mapsto_max_of_map l k m : LevelMap.MapsTo l k m -> max_of_map l k m.
Proof.
  intros hm l' k'. eapply LevelMapFact.F.MapsTo_fun in hm; tea.
  subst; reflexivity.
Qed.

Lemma min_model_map_spec l cls m :
  let map := min_model_map m cls in
  (forall k, LevelMap.MapsTo l k map ->
   [/\ (exists cl, Clauses.In cl cls /\ is_in_clause l k cl) \/ LevelMap.MapsTo l k m,
    (forall cl, Clauses.In cl cls -> max_of_premises l k (premise cl)) & max_of_map l k m]) /\
    (forall cl, Clauses.In cl cls -> forall l, LevelSet.In l (clause_levels cl) -> LevelMap.In l map) /\
    m ⩽ map.
Proof.
  cbn.
  rewrite /min_model_map.
  have hgen : forall cls m, (forall k, LevelMap.MapsTo l k (Clauses.fold min_model_clause cls m) ->
    [/\ (exists cl : Clauses.elt, Clauses.In cl cls /\ is_in_clause l k cl) \/
    LevelMap.MapsTo l k m,
      forall cl : Clauses.elt, Clauses.In cl cls -> max_of_premises l k (premise cl)
    & max_of_map l k (Clauses.fold min_model_clause cls m)]) /\
    (forall cl, Clauses.In cl cls -> forall l, LevelSet.In l (clause_levels cl) -> LevelMap.In l (Clauses.fold min_model_clause cls m)) /\
    m ⩽ Clauses.fold min_model_clause cls m.
  2:{ specialize (hgen cls m). destruct hgen as [hgen [hcls H]]; split; eauto.
      intros k hm. specialize (hgen k hm) as [] => //.
      split => //. eapply max_of_map_ext; tea. }
  clear.
  intros cls m.
  eapply ClausesProp.fold_rec.
  - intros s' he. split; [ | split; [|reflexivity]].
    * intros k hin. split => //. now right.
      intros cl hin'. clsets. now apply mapsto_max_of_map.
    * intros cl ins'; clsets.
  - intros x a s' s'' hin hnin hadd [ih [ihcls hext]]. split; [|split]; revgoals.
    { transitivity a => //. intros l' hin' hm.
      have := min_model_clause_spec l' x a. cbn.
      intros [_ hm']. specialize (hm' l' hin').
      now forward hm' by eauto. }
    { intros cl ins'' l' inlev.
      apply hadd in ins'' as [<-|].
      * have := min_model_clause_spec l' x a. cbn.
        intros [_ hm']. eapply clause_levels_spec in inlev as [].
        + eapply levelexprset_levels_spec in H as [k' incl].
          specialize (hm' l' (Some k')). forward hm'. right. left. rewrite /is_in_premise. exists k'; eauto.
          destruct hm' as [? []]; now eexists.
        + subst l'. specialize (hm' (concl x) None). forward hm'.
          right. right. split => //.
          destruct hm' as [? []]; now eexists.
      * specialize (ihcls _ H _ inlev) as [k' ina].
        have := min_model_clause_spec l' x a. cbn.
        move=> [] _ /(_ l' k' (or_introl ina)).
        clear. firstorder. }
    intros k.
    have := min_model_clause_spec l x a. cbn.
    intros [hm hm'] hmk. destruct (hm _ hmk).
    split => //.
    { destruct H0; eauto.
    { left; exists x. split => //. apply hadd. now left. }
    { specialize (ih _ H0) as []. destruct H1; eauto. left.
      move: H1 => [] w []; exists w; split; eauto. apply hadd. now right. } }
    { move=> cl /hadd => [] [<-|hin'].
      { now move: H => []. }
      { specialize (hm' l k). forward hm' by (destruct H0; eauto).
        intros k' h.
        specialize (ihcls _ hin' l).
        forward ihcls.
        { eapply clause_levels_spec. left. eapply levelexprset_levels_spec. now exists k'. }
        destruct ihcls as [ka ihcls].
        specialize (ih _ ihcls) as [ihm ihcls' maxm].
        specialize (ihcls' _ hin' _ h).
        transitivity ka => //.
        destruct H as [mp mmap].
        now apply mmap. } }
    { intros kl inma. eapply LevelMapFact.F.MapsTo_fun in hmk; tea. subst. reflexivity. }
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
  - have ms := min_model_map_spec k cls' (model_model m).
    set (map := min_model_map _ _) in *.
    destruct ms as [hm [hcls hext]].
    rewrite LevelSet.union_spec => [] [].
    * move/clauses_levels_spec.
      intros [cl [hin ink]].
      now move: hcls => /(_ _ hin _ ink).
    * move/(model_of_V m k).
      move=> [] x /hext. firstorder.
  - have ms := min_model_map_spec k cls' (model_model m).
    set (map := min_model_map _ _) in *.
    destruct ms as [hm [hcls hext]].
    rewrite LevelSet.union_spec.
    move=> [] v /hm [] [[cl [incl inclv]]|hm'] ihcls mmap.
    * left.
      red in inclv. eapply clauses_levels_spec.
      exists cl. split => //. eapply clause_levels_spec.
      destruct inclv as [[? []]|].
      + left. eapply levelexprset_levels_spec. now eexists.
      + right. intuition.
    * have [_ ho] := valid_model_only_model _ _ _ _ m hincl k.
      forward ho by now exists v. now right.
Qed.

Lemma only_model_of_min_model_map cls V m :
  clauses_levels cls ⊂_lset V ->
  only_model_of V m -> only_model_of V (min_model_map m cls).
Proof.
  intros incl om l.
  split.
  - move=> /om => [] [k inm].
    have [hmap [hcls hext]] := min_model_map_spec l cls m.
    specialize (hext l k inm). firstorder.
  - have [hmap [hcls hext]] := min_model_map_spec l cls m.
    move=> [] x /hmap => [] [excl allcl maxm].
    red in maxm.
    destruct excl as [[cl [incls incl']]|inm].
    * apply incl. apply clauses_levels_spec. exists cl. split => //.
      red in incl'.
      apply clause_levels_spec.
      clear -incl'. firstorder. subst. left. apply levelexprset_levels_spec.
      firstorder.
    * rewrite (om l). now exists x.
Qed.

Module CorrectModel.
  Record t {V cls} :=
  { the_model : model;
    only_model_of_V : only_model_of V the_model;
    model_updates : LevelSet.t;
    clauses_declared : clauses_levels cls ⊂_lset V;
    model_valid : valid_model V model_updates the_model cls }.
  Arguments t : clear implicits.

  #[local] Obligation Tactic := program_simpl.
  Equations? infer_extension_correct {V W init cls} (m : valid_model V W init cls)
    (hincl : only_model_of V init)
    (hs : clauses_levels cls ⊂_lset V)
    (cls' : clauses)
    (hs' : clauses_levels cls' ⊂_lset V) : (t V (Clauses.union cls cls')) + premises :=
  infer_extension_correct m hincl hs cls' hs' with infer_extension m hincl hs cls' :=
    | Loop u _ => inr u
    | Model w m' _ =>
      inl {|
        the_model := min_model_map m.(model_model) cls';
        only_model_of_V := _;
        model_updates := w; clauses_declared := _;
        model_valid := {| model_model := m'.(model_model) |} |}.
  Proof.
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

  Equations? infer_extension_valid {V cls} (m : t V cls) cls' : option (t V (Clauses.union cls cls') + premises) :=
  infer_extension_valid m cls' with inspect (LevelSet.subset (clauses_levels cls') V) :=
    | exist false heq => None
    | exist true heq := Some (infer_extension_correct (model_valid m) _ _ cls' _).
  Proof.
    - apply only_model_of_V.
    - now apply m.
    - now apply LevelSet.subset_spec in heq.
  Qed.
End CorrectModel.

Module Abstract.
  Import CorrectModel.
  Record t :=
    { levels : LevelSet.t;
      clauses : Clauses.t;
      model : CorrectModel.t levels clauses }.

  Program Definition init_model : t :=
    {| levels := LevelSet.empty;
       clauses := Clauses.empty;
       model := _ |}.
  Next Obligation.
    refine {| the_model := LevelMap.empty _;
      only_model_of_V := _;
      model_updates := LevelSet.empty; |}.
    - intros l. split. lsets.
      intros [x hm]. now eapply LevelMapFact.F.empty_mapsto_iff in hm.
    - now intros l; rewrite clauses_levels_spec.
    - refine {| model_model := LevelMap.empty _ |}.
      * red. lsets.
      * red. rewrite (proj2 (LevelSet.is_empty_spec _)). lsets.
        reflexivity.
      * now intros l; rewrite clauses_conclusions_spec.
      * rewrite /is_model. eapply Clauses.for_all_spec. tc.
        intros x hin. now apply Clauses.empty_spec in hin.
  Qed.

  Equations? declare_level (m : t) (l : Level.t) : option t :=
  declare_level m l with inspect (LevelSet.mem l m.(levels)) :=
    | exist true _ => None
    | exist false hneq => Some {| levels := LevelSet.add l m.(levels); clauses := m.(clauses) |}.
  Proof.
    refine {| the_model := LevelMap.add l None m.(model).(the_model);
      only_model_of_V := _;
      model_updates := m.(model).(model_updates); |}.
    - intros k. rewrite LevelSet.add_spec /LevelSet.E.eq.
      rw LevelMapFact.F.add_mapsto_iff.
      have hyp := m.(model).(only_model_of_V) k.
      firstorder; subst. all:rewrite /Level.eq.
      * now exists None.
      * exists x. right; split => //. intros ->.
        apply LevelSetFact.not_mem_iff in hneq. contradiction.
    - have hyp := m.(model).(clauses_declared). lsets.
    - destruct m as [levels clauses vm]; cbn in *.
      destruct vm as [init omofV W incl vm].
      destruct vm as [M mofV mupd mcls mok]. cbn in *.
      refine {| model_model := LevelMap.add l None M |}.
      * intros k. rewrite LevelSet.add_spec LevelMapFact.F.add_in_iff. firstorder. now left.
      * move: mupd.
        rewrite /is_update_of.
        destruct (LevelSet.is_empty) eqn:hw.
        now intros ->.
        { apply (todo "strict update weakening"). }
      * lsets.
      * apply (todo "cannot activate more clauses").
  Qed.

  Equations enforce_clauses (m : t) (cls : Clauses.t) : option (t + premises) :=
  enforce_clauses m cls with infer_extension_valid m.(model) cls :=
    | None => None
    | Some (inl m') => Some (inl {| model := m' |})
    | Some (inr u) => Some (inr u).

End Abstract.
End Deciders.

Module LoopChecking (LS : LevelSets).
  Module Impl := Deciders(LS).
  Import Impl.I.

  Definition model := Impl.Abstract.t.

  Notation univ := LS.LevelExprSet.nonEmptyLevelExprSet.

  Inductive constraint_type := UnivEq | UnivLe.
  Notation constraint := (univ * constraint_type * univ).

  Definition enforce_constraint (cstr : constraint) (cls : Clauses.t) : Clauses.t :=
    let '(l, d, r) := cstr in
    match d with
    | UnivLe =>
      LevelExprSet.fold (fun lk acc => Clauses.add (r, lk) acc) (LevelExprSet.t_set l) cls
    | UnivEq =>
      let cls :=
        LevelExprSet.fold (fun lk acc => Clauses.add (r, lk) acc) (LevelExprSet.t_set l) cls
      in
      let cls' :=
        LevelExprSet.fold (fun rk acc => Clauses.add (l, rk) acc) (LevelExprSet.t_set r) cls
      in cls'
    end.

  Definition init_model := Impl.Abstract.init_model.

  (* Returns None if already declared *)
  Definition declare_level l m := Impl.Abstract.declare_level m l.

  (* Returns either a model or a looping universe, i.e. such that u >= u + 1 is implied
     by the constraint *)
  Definition enforce c (m : model) : option (model + univ) :=
    Impl.Abstract.enforce_clauses m (enforce_constraint c Clauses.empty).

  (* Returns true is the clause is valid in the model and all its possible consistent extensions.
     Returns false if the constraint results in an inconsistent set of constraints or it simply
     is not valid. *)
  Definition check m c :=
    Impl.check_clauses m.(Impl.Abstract.clauses) (enforce_constraint c Clauses.empty).

  (* Returns the valuation of the model: a minimal assignement from levels to constraints
    that make the enforced clauses valid. *)
  Definition valuation m := Model.valuation_of_model m.(Impl.Abstract.model).(Impl.CorrectModel.the_model).

End LoopChecking.