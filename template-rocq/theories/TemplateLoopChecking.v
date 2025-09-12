(* Distributed under the terms of the MIT license. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import Program RelationClasses Morphisms.
From Stdlib Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Universes.
From MetaRocq.Common.LoopChecking Require Import Common Interfaces Deciders.
From Equations Require Import Equations.
Set Equations Transparent.


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

