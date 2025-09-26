Require Import Stdlib.Lists.List.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.Template Require Import
     Ast
     Loader
     TemplateMonad.Extractable.
Import TemplateMonad.Extractable.
From MetaRocq Require Import Common.BasicAst Template.AstUtils Template.Ast TemplateLoopChecking.

Definition time : forall {A} {B : A -> Type}, string -> (forall x : A, B x) -> forall x : A, B x :=
  fun A B s f x => f x.

Extract Constant time =>
  "(fun c f x -> let s = Caml_bytestring.caml_string_of_bytestring c in Tm_util.time (Pp.str s) f x)".

Open Scope bs_scope.

Import MRMonadNotation.
Local Open Scope monad_scope.

Global Instance TemplateMonad_Monad@{t u} : Monad@{t u} TM@{t} :=
  {| ret := @tmReturn ; bind := @tmBind |}.

Definition check_universes : TM unit :=
  tmQuoteUniverses >>= fun ctx =>
  let clauses := time "building clauses" enforce_level_constraints (snd ctx) in
  tmMsg (string_of_nat (LevelSet.cardinal (fst ctx)) ++ " universes and " ++ string_of_nat (UnivConstraintSet.cardinal (snd ctx)) ++ " constraints") ;;
  let result := time "loop-checking" TemplateLoopChecking.UnivLoopChecking.infer clauses in
  tmMsg (TemplateLoopChecking.UnivLoopChecking.print_result result).
