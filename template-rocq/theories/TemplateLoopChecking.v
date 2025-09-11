(* Distributed under the terms of the MIT license. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Universes.
From MetaRocq.Common.LoopChecking Require Import Common Interfaces Deciders.
From Equations Require Import Equations.
Set Equations Transparent.

Import Universes.

Module MoreLevel.
  Import Universes.
  Include Level.

  Definition to_string := string_of_level.
End MoreLevel.

Module LevelMap.
  Module OT := FMapOrderedType_from_UsualOrderedType Level.
  Include FMapAVL.Make OT.
End LevelMap.

Module LevelExprZ.
  Definition t := (Level.t * Z)%type.
  Local Open Scope Z_scope.

  Definition succ (l : t) : t := (fst l, Z.succ (snd l)).

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltLevelExpr1 l n n' : (n < n') -> lt_ (l, n) (l, n')
  | ltLevelExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').
  Derive Signature for lt_.
  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X. subst. lia. subst.
      eapply Level.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2; now rewrite H1 H2.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match Level.compare l1 l2 with
      | Eq => Z.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [? ?] [? ?]; cbn; repeat constructor.
    destruct (Level.compare_spec t0 t1); repeat constructor; tas.
    subst.
    destruct (Z.compare_spec z z0); repeat constructor; tas. congruence.
  Qed.

  Global Instance reflect_t : ReflectEq t := reflect_prod _ _ .

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2} := Classes.eq_dec.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End LevelExprZ.

Module LevelExprZSet.
  Include MSetList.MakeWithLeibniz LevelExprZ.

  Definition levels (e : t) :=
    fold (fun le => LevelSet.add (fst le)) e LevelSet.empty.

  Record nonEmptyLevelExprSet
    := { t_set : t ;
         t_ne  : is_empty t_set = false }.
End LevelExprZSet.
Module LevelExprZSetFacts := WFactsOn LevelExprZ LevelExprZSet.
Module LevelExprZSetProp := MSetProperties.OrdProperties LevelExprZSet.

Module LevelSet.
  Include MakeWithLeibniz Level.
End LevelSet.
Module LS <: LevelSets.
  Module Level := MoreLevel .
  Module LevelSet := LevelSet.
  Module LevelExpr := LevelExprZ.
  Module LevelExprSet := LevelExprZSet.
  Module LevelMap := LevelMap.
End LS.

Module UnivLoopChecking.
  Module LoopCheck := LoopChecking LS.
  Include LoopCheck.
End UnivLoopChecking.

Import UnivLoopChecking.

Definition to_levelexprzset (u : LevelExprSet.t) : LS.LevelExprSet.t :=
  LevelExprSet.fold (fun '(l, k) => LS.LevelExprSet.add (l, Z.of_nat k)) u LS.LevelExprSet.empty.

Lemma to_levelexprzset_spec u :
  forall l k, LevelExprSet.In (l, k) u -> LevelExprZSet.In (l, Z.of_nat k) (to_levelexprzset u).
Proof.
  intros l k.
  rewrite /to_levelexprzset.
  apply LevelExprSetProp.fold_rec.
  - now move=> s' hs' /hs'.
  - move=> x a s' s'' hin hnin hadd ih /hadd [].
    * intros ->. apply LevelExprZSet.add_spec. now left.
    * intros hin'. destruct x. apply LevelExprZSet.add_spec. now right.
Qed.

Program Definition to_atoms (u : Universe.t) : LevelExprZSet.nonEmptyLevelExprSet :=
  {| LevelExprZSet.t_set := to_levelexprzset u |}.
Next Obligation.
  destruct u. cbn.
  destruct (LevelExprZSet.is_empty _) eqn:he => //.
  apply LevelExprZSet.is_empty_spec in he.
  assert (LevelExprSet.is_empty t_set).
  apply LevelExprSet.is_empty_spec. intros x hin.
  destruct x. eapply (he (t, Z.of_nat n)).
  now apply to_levelexprzset_spec.
  congruence.
Qed.

Definition from_levelexprzset (u : LS.LevelExprSet.t) : LevelExprSet.t :=
  LS.LevelExprSet.fold (fun '(l, k) =>LevelExprSet.add (l, Z.to_nat k)) u LevelExprSet.empty.

Lemma from_levelexprzset_spec u :
  forall l k, LevelExprZSet.In (l, k) u -> LevelExprSet.In (l, Z.to_nat k) (from_levelexprzset u).
Proof.
  intros l k.
  rewrite /from_levelexprzset.
  apply LevelExprZSetProp.P.fold_rec.
  - now move=> s' hs' /hs'.
  - move=> x a s' s'' hin hnin hadd ih /hadd [].
    * intros ->. apply LevelExprSet.add_spec. now left.
    * intros hin'. destruct x. apply LevelExprSet.add_spec. now right.
Qed.

Program Definition from_atoms (u : univ) : Universe.t :=
  {| LevelExprSet.t_set := from_levelexprzset (LS.LevelExprSet.t_set u) |}.
Next Obligation.
  destruct u. cbn.
  destruct (LevelExprSet.is_empty _) eqn:he => //.
  apply LevelExprSet.is_empty_spec in he.
  assert (LevelExprZSet.is_empty t_set).
  apply LevelExprZSet.is_empty_spec. intros x hin.
  destruct x. eapply (he (t, Z.to_nat z)).
  now apply from_levelexprzset_spec.
  congruence.
Qed.

Definition to_constraint (x : UnivConstraint.t) : constraint :=
  let '(l, d, r) := x in
  let '(l, d, r) := match d with
  | ConstraintType.Eq => (l, UnivEq, r)
  | ConstraintType.Le k =>
    if (k <? 0)%Z then (l, UnivLe, Universe.add (Z.to_nat (- k)) r)
    else (Universe.add (Z.to_nat k) l, UnivLe, r)
  end
  in (to_atoms l, d, to_atoms r).

Module Clauses := Impl.I.Model.Model.Clauses.Clauses.

Definition level_constraint_to_constraint (x : LevelConstraint.t) : constraint :=
  let '(l, d, r) := x in
  let '(l, d, r) := match d with
  | ConstraintType.Eq => (Universe.make' l, UnivEq, Universe.make' r)
  | ConstraintType.Le k =>
    if (k <? 0)%Z then (Universe.make' l, UnivLe, Universe.make (r, Z.to_nat (-k)))
    else (Universe.make (l, Z.to_nat k), UnivLe, Universe.make' r)
  end
  in (to_atoms l, d, to_atoms r).

Declare Scope levelnat_scope.
Delimit Scope levelnat_scope with levelnat.
Module LevelNatMapNotation.
  Import LevelMap.Raw.
  Notation levelmap := (tree nat) (only parsing).
  Definition parse_levelnat_map (l : list Byte.byte) : option levelmap :=
    None.
  Definition print_levelnat_map (m : levelmap) :=
    let list := LevelMap.Raw.elements m in
    print_list (fun '(l, w) => MoreLevel.to_string l ^ " -> " ^ string_of_nat w) nl list.

  Definition print_levelmap (l : levelmap) : list Byte.byte :=
    to_bytes (print_levelnat_map l).

  String Notation levelmap parse_levelnat_map print_levelmap
      : levelnat_scope.
End LevelNatMapNotation.
Import LevelNatMapNotation.
Arguments LevelMap.Bst {elt} this%levelnat {is_bst}.

From MetaRocq.Template Require Import All Core.
Definition time : forall {A} {B : A -> Type}, string -> (forall x : A, B x) -> forall x : A, B x :=
  fun A B s f x => f x.

Global Instance TemplateMonad_Monad@{t u} : Monad@{t u} TemplateMonad@{t u} :=
  {| ret := @tmReturn ; bind := @tmBind |}.
Import MRMonadNotation.
Local Open Scope monad_scope.
Open Scope bs_scope.
Import TemplateLoopChecking.UnivLoopChecking.

Universes u v.
#[universes(polymorphic)]
Definition check_le@{u v} : unit := tt.

Definition univ_model := Impl.Abstract.t.

(* We ignore errors here, which can happen only if the levels are already declared *)
Definition declare_levels (m : univ_model) (l : LevelSet.t) :=
  LevelSet.fold (fun l m => match declare_level l m with None => m | Some m => m end) l m.

Definition enforce_level_constraints (m : univ_model) (l : ConstraintSet.t) :=
  ConstraintSet.fold (fun c m =>
    match m with
    | inl m =>
      let c := (level_constraint_to_constraint c) in
      match enforce c m with
      | None => (inr (c, None))
      | Some (inl m) => (inl m)
      | Some (inr u) => (inr (c, Some u))
      end
    | inr err => inr err
    end) l (inl m).

Import Impl.I.Model.Model.Clauses.FLS.

Definition of_constraint (c : constraint) : UnivConstraint.t :=
  let '(l, d, r) := c in
  let d' := match d with
    | UnivLe => ConstraintType.Le 0
    | UnivEq => ConstraintType.Eq
    end
  in
  (from_atoms l, d', from_atoms r).

Definition print_result (r : model + (constraint × option univ)) : string :=
  match r with
  | inl m => "Model: \n" ++ print_level_nat_map (valuation m)
  | inr (c, None) => "Constraint uses undeclared levels: " ++
    Universes.print_univ_constraint (of_constraint c)
  | inr (c, Some u) => "Constraint " ++
    Universes.print_univ_constraint (of_constraint c) ++ " entails a loop on " ++
    string_of_universe (from_atoms u)
  end.

Definition test : TemplateMonad unit :=
  tmQuoteUniverses >>= fun ctx =>
  let m := time "declaring levels" (declare_levels init_model) (fst ctx) in
  let m' := time "enforcing clauses" (enforce_level_constraints m) (snd ctx) in
  tmMsg (print_result m') ;;
  (* tmMsg (print_clauses clauses) ;; *)
  (* tmMsg (string_of_nat (LevelSet.cardinal (fst ctx)));; *)
   (* ++ " universes and " ++ string_of_nat (ConstraintSet.cardinal (snd ctx)) ++ " constraints") ;; *)
  tmMsg "done".

(* MetaRocq Run test. *)

  (* let result := time "loop-checking" TemplateLoopChecking.UnivLoopChecking.infer clauses in *)
  (* tmMsg (TemplateLoopChecking.UnivLoopChecking.print_result result). *)
From MetaRocq.Template Require Import Pretty.

Definition env_from_context (c : ContextSet.t) : global_env_ext :=
  (empty_ext {| universes := c; declarations := []; retroknowledge := Retroknowledge.empty |}).

MetaRocq Run (ctx <- tmQuoteUniverses ;;
  t <- tmQuote (Type@{u}) ;;
  tmMsg (print_term (env_from_context ctx) [] true t)).

Definition make_level (n : ident) : Level.t := Level.level n.

