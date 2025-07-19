(* Distributed under the terms of the MIT license. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Universes.
From MetaRocq.Template Require Import LoopChecking.
From Equations Require Import Equations.
Set Equations Transparent.

Import Universes.

Module MoreLevel.
  Import Universes.
  Include Level.

  Definition reflect_eq : ReflectEq t := reflect_level.
  Definition to_string := string_of_level.

End MoreLevel.

Module LevelMap.
  Module OT := FMapOrderedType_from_UsualOrderedType Level.
  Include FMapAVL.Make OT.
End LevelMap.

Module UnivLoopChecking.
  Module LoopCheck := LoopChecking MoreLevel LevelSet LevelExpr LevelExprSet LevelMap.
  Include LoopCheck.
End UnivLoopChecking.

Import UnivLoopChecking.

Definition to_constraint (x : UnivConstraint.t) : constraint :=
  let '(l, d, r) := x in
  let '(l, d, r) := match d with
  | ConstraintType.Eq => (l, UnivEq, r)
  | ConstraintType.Le k =>
    if (k <? 0)%Z then (l, UnivLe, Universe.add (Z.to_nat (- k)) r)
    else (Universe.add (Z.to_nat k) l, UnivLe, r)
  end
  in (l, d, r).

Definition level_constraint_to_constraint (x : LevelConstraint.t) : constraint :=
  let '(l, d, r) := x in
  let '(l, d, r) := match d with
  | ConstraintType.Eq => (Universe.make' l, UnivEq, Universe.make' r)
  | ConstraintType.Le k =>
    if (k <? 0)%Z then (Universe.make' l, UnivLe, Universe.make (r, Z.to_nat (-k)))
    else (Universe.make (l, Z.to_nat k), UnivLe, Universe.make' r)
  end
  in (l, d, r).

Definition enforce_constraints (cstrs : UnivConstraintSet.t) : clauses :=
  UnivConstraintSet.fold (fun cstr acc => enforce_constraint (to_constraint cstr) acc) cstrs (clauses_of_list []).

Definition enforce_level_constraints (cstrs : ConstraintSet.t) : clauses :=
  ConstraintSet.fold (fun cstr acc => enforce_constraint (level_constraint_to_constraint cstr) acc) cstrs (clauses_of_list []).

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
(*
Definition valuation_of_model (m : model) : LevelMap.t nat :=
  let max := LevelMap.fold (fun l k acc => Nat.max k acc) m 0%Z in
  LevelMap.fold (fun l k acc => LevelMap.add l (max - k)%nat acc) m (LevelMap.empty _).

Definition print_level_nat_map (m : LevelMap.t nat) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => string_of_level l ^ " -> " ^ string_of_nat w) nl list.

Definition print_lset (l : LevelSet.t) :=
  let list := LevelSet.elements l in
  print_list string_of_level " " list.

Arguments model_model {V m cls}.

Definition print_result {V cls} (m : infer_result V cls) :=
  match m with
  | Loop => "looping"
  | Model w m _ => "satisfiable with model: " ^ print_level_nat_map (model_model m) ^ nl ^ " W = " ^
    print_lset w
    ^ nl ^ "valuation: " ^ print_level_nat_map (valuation_of_model (model_model m))
  end. *)

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

Definition test : TemplateMonad unit :=
  tmQuoteUniverses >>= fun ctx =>
  let clauses := time "building clauses" enforce_level_constraints (snd ctx) in
  tmMsg (print_clauses clauses) ;;
  (* tmMsg (string_of_nat (LevelSet.cardinal (fst ctx)));; *)
   (* ++ " universes and " ++ string_of_nat (ConstraintSet.cardinal (snd ctx)) ++ " constraints") ;; *)
  tmMsg "done".

  (* let result := time "loop-checking" TemplateLoopChecking.UnivLoopChecking.infer clauses in *)
  (* tmMsg (TemplateLoopChecking.UnivLoopChecking.print_result result). *)
From MetaRocq.Template Require Import Pretty.

Definition env_from_context (c : ContextSet.t) : global_env_ext :=
  (empty_ext {| universes := c; declarations := []; retroknowledge := Retroknowledge.empty |}).

MetaRocq Run (ctx <- tmQuoteUniverses ;;
  t <- tmQuote (Type@{u}) ;;
  tmMsg (print_term (env_from_context ctx) [] true t)).

Definition make_level (n : ident) : Level.t := Level.level n.

Definition check_constraint (cls : clauses) c :=



