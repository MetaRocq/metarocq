Require Import Stdlib.Lists.List.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.Common Require Import Universes uGraph.
From MetaRocq.Common.LoopChecking Require Import UnivLoopChecking.
From MetaRocq.Template Require Import
     Ast
     Loader
     TemplateMonad.Extractable.
Import TemplateMonad.Extractable.

Definition time : forall {A} {B : A -> Type}, string -> (forall x : A, B x) -> forall x : A, B x :=
  fun A B s f x => f x.

Extract Constant time =>
  "(fun c f x -> let s = Caml_bytestring.caml_string_of_bytestring c in Tm_util.time (Pp.str s) f x)".

Open Scope bs_scope.

Definition print_model (levels : LevelSet.t) (m : universe_model) : string :=
  print_list (fun l => string_of_level l ++ " -> " ++ string_of_nat (UnivLoopChecking.model_val m l))
    nl (LevelSet.elements levels).

(** Check the universe constraints of the current environment with the loop-checking
    algorithm, building a model of them, or fail if they are inconsistent. *)
Definition check_universes : TM unit :=
  tmBind tmQuoteUniverses (fun ctx =>
  let levels := LevelSet.remove Level.lzero (fst ctx) in
  let cstrs := snd ctx in
  tmBind (tmMsg (string_of_nat (LevelSet.cardinal levels) ++ " universes and " ++
    string_of_nat (UnivConstraintSet.cardinal cstrs) ++ " constraints")) (fun _ =>
  match time "loop-checking" (push_uctx init_model) (levels, cstrs) with
  | Some m => tmMsg ("Model:" ++ nl ++ print_model levels m)
  | None => tmFail "The universe constraints are inconsistent"
  end)).
