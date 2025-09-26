From MetaCoq.Template Require Import utils Universes TemplateLoopChecking.

Import UnivLoopChecking.

(* bytestring scope *)
Open Scope bs.
(* Tests using Coq's evaluation (does not scale to large examples as the loop function is producing proofs) *)

Definition mk_level x := LevelExpr.make (Level.Level x).
Definition levela := mk_level "a".
Definition levelb := mk_level "b".
Definition levelc := mk_level "c".
Definition leveld := mk_level "d".
Definition levele := mk_level "e".

Definition ex_levels : LevelSet.t :=
  LevelSetProp.of_list (List.map (LevelExpr.get_level) [levela; levelb; levelc; leveld; levele]).

Definition mk_clause (hd : LevelExpr.t) (premise : list LevelExpr.t) (e : LevelExpr.t) : clause :=
  (NonEmptySetFacts.add_list premise (NonEmptySetFacts.singleton hd), e).

(* Example from the paper *)
Definition clause1 : clause := mk_clause levela [levelb] (LevelExpr.succ levelb).
Definition clause2 : clause := mk_clause levelb [] (LevelExpr.add 3 levelc).
Definition clause3 := mk_clause (LevelExpr.add 1 levelc) [] leveld.
Definition clause4 := mk_clause levelb [LevelExpr.add 2 leveld] levele.
Definition clause5 := mk_clause levele [] levela.

Definition ex_clauses :=
  clauses_of_list [clause1; clause2; clause3; clause4].

Definition ex_loop_clauses :=
  clauses_of_list [clause1; clause2; clause3; clause4; clause5].


Example test := infer ex_clauses.
Example test_loop := infer ex_loop_clauses.

Eval compute in print_result test.
Eval compute in print_result test_loop.

(* Testing the unfolding of the loop function "by hand" *)
Definition hasFiniteModel {V U cls m} (m : result V U cls m) :=
  match m with
  | Loop => false
  | Model _ _ _ => true
  end.

Ltac hnf_eq_left :=
  match goal with
  | |- ?x = ?y => let x' := eval hnf in x in change (x' = y)
  end.

(* Goal hasFiniteModel test.
  hnf. hnf_eq_left. exact eq_refl.
  unfold test.
  unfold infer.
  rewrite /check.
  simp loop.
  set (f := check_model _ _).
  hnf in f. simpl in f.
  unfold f. unfold inspect.
  simp loop.
  set (eq := LevelSet.equal _ _).
  hnf in eq. unfold eq, inspect.
  simp loop.
  set (f' := check_model _ _).
  hnf in f'. unfold f', inspect.
  simp loop.
  set (f'' := check_model _ _).
  hnf in f''. simpl in f''.
  unfold inspect, f''. simp loop.
  set (eq' := LevelSet.equal _ _).
  hnf in eq'. unfold eq', inspect.
  simp loop.
  set (cm := check_model _ _).
  hnf in cm. simpl in cm.
  unfold inspect, cm. simp loop.
  exact eq_refl.
Qed. *)

Eval lazy in print_result test.
Eval compute in print_result test_loop.

Definition add_cstr (x : Universe.t) d (y : Universe.t) cstrs :=
  UnivConstraintSet.add (x, d, y) cstrs.

Coercion Universe.make : LevelExpr.t >-> Universe.t.
Import ConstraintType.
Definition test_cstrs :=
  (add_cstr levela Eq (LevelExpr.add 1 levelb)
  (add_cstr (Universe.sup levela levelc) Eq (LevelExpr.add 1 levelb)
  (add_cstr levelb (ConstraintType.Le 0) levela
  (add_cstr levelc (ConstraintType.Le 0) levelb
    UnivConstraintSet.empty)))).

Definition test_clauses := enforce_constraints test_cstrs.

Definition test_levels : LevelSet.t :=
  LevelSetProp.of_list (List.map (LevelExpr.get_level) [levela; levelb; levelc]).

Eval compute in print_clauses test_clauses.

Definition test' := infer test_clauses.
Eval compute in print_result test'.
Import Universe (sup).

Definition test_levels' : LevelSet.t :=
  LevelSetProp.of_list (List.map (LevelExpr.get_level)
    [levela; levelb;
      levelc; leveld]).

Notation " x + n " := (LevelExpr.add n x).

Fixpoint chain (l : list LevelExpr.t) :=
  match l with
  | [] => UnivConstraintSet.empty
  | hd :: [] => UnivConstraintSet.empty
  | hd :: (hd' :: _) as tl =>
    add_cstr hd (Le 10) (LevelExpr.add 1 hd') (chain tl)
  end.

Definition levels_to_n n :=
  unfold n (fun i => (Level.Level (string_of_nat i), 0)).

Definition test_chain := chain (levels_to_n 2).

Eval compute in print_clauses (enforce_constraints test_chain).
Eval compute in init_model (enforce_constraints test_chain).
(** These constraints do have a finite model that makes all implications true (not vacuously) *)
Time Eval vm_compute in print_result (infer (enforce_constraints test_chain)).

(* Eval compute in print_result test''. *)
(* Definition chainres :=  (infer (enforce_constraints test_chain)). *)

(*Goal hasFiniteModel chainres.
  hnf.
  unfold chainres.
  unfold infer.
  simp loop.
  set (f := check_model _ _).
  compute in f.
  hnf in f. simpl in f.
  unfold f. unfold inspect.
  simp loop.
  set (eq := LevelSet.equal _ _). simpl in eq.
  hnf in eq. unfold eq, inspect.
  rewrite loop_clause_1_clause_2_equation_2.
  set (l := loop _ _ _ _ _).
  assert (l = Loop).
  subst l.
  simp loop.
  set (f' := check_model _ _).
  hnf in f'. cbn in f'. unfold update_model in f'. simpl in f'. unfold f', inspect.
  cbn.
  simp loop.
  set (f'' := check_model _ _).
  hnf in f''. simpl in f''.
  unfold inspect, f''. simp loop.
  set (eq' := LevelSet.equal _ _).
  hnf in eq'. unfold eq', inspect.
  simp loop.
  set (cm := check_model _ _).
  hnf in cm. simpl in cm.
  unfold inspect, cm. simp loop.
  exact eq_refl.
Qed. *)

(*Goal chainres = Loop.
  unfold chainres.
  unfold infer.
  set (levels := Clauses.fold _ _ _).
  rewrite /check.
  simp loop.
  set (f := check_model _ _).
  hnf in f. cbn in f.
  unfold f. unfold inspect.
  simp loop.
  set (eq := LevelSet.equal _ _).
  hnf in eq. unfold eq, inspect.
  simp loop.
  set (f' := check_model _ _).
  hnf in f'. cbn in f'. unfold flip in f'. cbn in f'.

set (f := check_model _ _).
hnf in f. cbn in f.
unfold f. cbn -[forward]. unfold flip.
unfold init_w.
rewrite unfold_forward.
set (f' := check_model _ _).
cbn in f'. unfold flip in f'.
hnf in f'. cbn in f'.
cbn.

unfold check_model. cbn -[forward]. unfold flip.
set (f := update_value _ _). cbn in f.
unfold Nat.leb in f. hnf in f.

Eval compute in print_result (infer ex_levels test_clauses).

*)

Definition test_above0 :=
  (add_cstr (levelc + 1) (ConstraintType.Le 0) levelc UnivConstraintSet.empty).

Eval compute in print_clauses (enforce_constraints test_above0).
Definition testabove0 := infer (enforce_constraints test_above0).

(** Loop c + 1 <= c *)
Eval vm_compute in print_result testabove0.

(** Verify that no clause holds vacuously for the model *)

Definition premise_holds (m : model) (cl : clause) :=
  satisfiable_premise m (premise cl).

Definition premises_hold (cls : clauses) (m : model) : bool :=
  Clauses.for_all (premise_holds m) cls.

Definition print_model_premises_hold cls (m : model) :=
  if premises_hold cls m then "all premises hold"
  else "some premise doesn't hold".

Definition print_premises_hold {V U cls m} (r : result V U cls m) :=
  match r with
  | Loop => "looping"
  | Model w m _ => print_model_premises_hold cls m.(model_model)
  end.

(* Is clause [c] non-vacuous and satisfied by the model? *)
Definition check_clause (m : model) (cl : clause) : bool :=
  satisfiable_premise m (premise cl) && satisfiable_atom m (concl cl).

Definition check_clauses (m : model) cls : bool :=
  Clauses.for_all (check_clause m) cls.

Definition check_cstr (m : model) (c : UnivConstraint.t) :=
  let cls := enforce_constraint (to_constraint c) (clauses_of_list []) in
  check_clauses m cls.

Definition check_cstrs (m : model) (c : UnivConstraintSet.t) :=
  let cls := enforce_constraints c in
  check_clauses m cls.

  (* as [cl []].
  eapply Clauses.union_spec in H as [].
  apply m.(model_clauses_conclusions).
  rewrite clauses_conclusions_spec. now exists cl.
  eapply prf. rewrite clauses_conclusions_spec.
  now exists cl.
Qed. *)

(*Equations? weaken_model (m : model) (cls : clauses) : valid_model (LevelSet.union (clauses_levels cls) V m cls) :=
  weaken_model m cls :=
    {| model_clauses := m.(model_clauses);
       model_model :=  |}.
Proof.
  rewrite LevelSet.union_spec. right. now apply m.
Qed. *)

Definition model_variables (m : model) : LevelSet.t :=
  LevelMap.fold (fun l _ acc => LevelSet.add l acc) m LevelSet.empty.

Variant enforce_result :=
  | Looping
  | ModelExt (m : model).

Definition enforce_cstr {V init cls} (m : valid_model V init cls) (c : UnivConstraint.t) :=
  let cls := enforce_constraint (to_constraint c) (clauses_of_list []) in
  enforce_clauses m cls.

Definition enforce_cstrs {V init cls} (m : valid_model V init cls) (c : UnivConstraintSet.t) :=
  let cls := enforce_constraints c in
  enforce_clauses m cls.

Definition initial_cstrs :=
  (add_cstr (sup levela levelb) Eq (levelc + 1)
  (add_cstr levelc (Le 0) (sup levela levelb)
  (add_cstr levelc (Le 0) levelb
    UnivConstraintSet.empty))).

Definition enforced_cstrs :=
  (* (add_cstr (sup levela levelb) Eq (sup (levelc + 1) leveld) *)
  (add_cstr (levelb + 10) (Le 0) levele
  (* (add_cstr levelc (Le 0) levelb *)
  UnivConstraintSet.empty).

Definition initial_cls := enforce_constraints initial_cstrs.
Definition enforced_cls := enforce_constraints enforced_cstrs.

Eval vm_compute in init_model initial_cls.

Definition abeqcS :=
  enforce_constraints
    (add_cstr (sup levela levelb) Eq (levelc + 1) UnivConstraintSet.empty).

Eval compute in print_clauses initial_cls.
Eval compute in print_clauses abeqcS.

Definition test'' := infer initial_cls.
Definition testabeqS := infer abeqcS.

Eval vm_compute in print_result test''.
Eval vm_compute in print_result testabeqS.

Eval vm_compute in print_model_premises_hold initial_cls (init_model initial_cls).

Ltac get_result c :=
  let c' := eval vm_compute in c in
  match c' with
  | Loop => fail "looping"
  | Model ?w ?m _ => exact m
  end.

Definition model_cstrs' := ltac:(get_result test'').

Notation "x ≡ y" := (eq_refl : x = y) (at level 70).

Eval vm_compute in check_cstrs model_cstrs'.(model_model) initial_cstrs ≡ true.
(* Here c <= b, in the model b = 0 is minimal, and b's valuation gives 1 *)
Eval vm_compute in print_result (infer initial_cls).

(* Here it is still the case, we started with b = 0 but move it to 10
  due to the b + 10 -> e clause, and reconsider the b -> c clause to move
  c up *)
Eval vm_compute in
  option_map valuation_of_model
  (enforce_cstrs model_cstrs' enforced_cstrs).

(* The whole set of constraints has a finite model with c <= b *)

Definition all_clauses := Clauses.union initial_cls enforced_cls.

Eval vm_compute in valuation_of_result (infer all_clauses).
Eval vm_compute in
  option_map (is_model all_clauses) (option_of_result (infer all_clauses)).

(* This is a model? *)
Eval vm_compute in enforce_cstrs model_cstrs' enforced_cstrs.
Eval vm_compute in print_clauses initial_cls.

(** This is also a model of (the closure of) the initial clauses *)
Check (option_map (is_model initial_cls) (enforce_cstrs model_cstrs' enforced_cstrs)
  ≡ Some true).

(* And a model of the new constraints *)
Check (option_map (is_model enforced_cls) (enforce_cstrs model_cstrs' enforced_cstrs)
   ≡ Some true).

(* All premises hold *)
Eval vm_compute in
  option_map (print_model_premises_hold enforced_cls)
    (enforce_cstrs model_cstrs' enforced_cstrs).
