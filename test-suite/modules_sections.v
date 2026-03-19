From MetaRocq.Template Require Import All.
From MetaRocq.Utils Require Import utils.
Import MonadNotation.


Module Type A.
  Parameter x : nat.
End A.

Module B (X : A) (Y : A).

  MetaRocq Test Quote Y.x.
  MetaRocq Unquote Definition uuu :=
          (tConst (MPbound ["modules_sections"; "TestSuite"; "MetaRocq"] "Y" 1, "x") []).


  MetaRocq Run (bc <- tmQuote X.x ;;
               tmPrint bc ;;
               bc <- tmUnquote bc ;;
               tmPrint bc).

End B.


Module Type C (X : A) (Y : A).
  MetaRocq Run (bc <- tmQuote X.x ;;
               tmPrint bc ;;
               bc <- tmUnquote bc ;;
               tmPrint bc).
End C.


Section S.

  Definition b := forall X, X.
  Definition c := Set.
  (* Set Printing All. Set Printing Universes. *)
  MetaRocq Run (bc <- tmQuote b ;;
                    tmPrint bc ;;
                    tmMkDefinition "bb" bc ;;
                    tmPrint "lol").
  Check bb.

  Variable x : nat.
  MetaRocq Run (bc <- tmQuote x ;;
                    tmPrint bc ;;
                    tmMkDefinition "bx" bc ;;
                    tmPrint "lol").

  Check bx.

End S.

MetaRocq Run (bc <- tmQuote b ;;
                tmPrint bc ;;
                bc <- tmUnquote bc ;;
                tmPrint bc).

From MetaRocq Require Import Template.Pretty.
Check (eq_refl : print_term (empty_ext empty_global_env) [] true
                      (tConst (MPfile ["test"; "Examples"; "MetaRocq"], "b") [])
                 = "MetaRocq.Examples.test.b").

Module S.

  Definition b := forall X, X.
  MetaRocq Run (bc <- tmQuote b ;;
               tmPrint bc ;;
               bc <- tmUnquote bc ;;
               tmPrint bc).
End S.

MetaRocq Run (bc <- tmQuote S.b ;;
             tmPrint bc ;;
             bc <- tmUnquote bc ;;
             tmPrint bc).



MetaRocq Test Quote my_projT2.
MetaRocq Test Unquote
     (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Corelib"], "nat") 0) 0 []).
MetaRocq Unquote Definition zero_from_syntax
  := (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Corelib"], "nat") 0) 0 []).

Existing Class nat.

Module Type X.
  Definition t : nat := 0.
  Parameter t' : nat.
  Parameter t'' : nat.
  Print Instances nat.
  MetaRocq Run (tmLocate1 "t" >>= tmExistingInstance global).
  MetaRocq Run (tmLocate1 "t'" >>= tmExistingInstance global).
  Print Instances nat.
End X.

Section XX.
  Variable u : nat.
  Fail MetaRocq Run (tmLocate1 "u" >>= tmExistingInstance global).
  Print Instances nat.
End XX.

Module Y (A : X).
  Print Instances nat.
  MetaRocq Run (tmLocate1 "t''" >>= tmExistingInstance global).
  Print Instances nat.
End Y.

MetaRocq Run (tmLocateModule1 "B" >>= tmPrint).
MetaRocq Run (tmLocateModule1 "S" >>= tmPrint).
MetaRocq Run (tmLocateModType1 "X" >>= tmPrint).
Fail MetaRocq Run (tmLocateModType1 "B" >>= tmPrint).
Fail MetaRocq Run (tmLocateModType1 "modules_sections.S" >>= tmPrint). (* finds (MPdot (MPfile ["FMapInterface"; "FSets"; "Stdlib"]) "S") if unqualified *)
Fail MetaRocq Run (tmLocateModule1 "X" >>= tmPrint).
