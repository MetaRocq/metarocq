From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import MonadNotation.

Section test.

  MetaRocq Run (tmVariable "bla" nat).
  Check (bla : nat).
  MetaRocq Run (tmDefinition "test" bla).
  MetaRocq Run (tmDefinition "test2" 0).

  MetaRocq Run (tmVariable "toto" nat ;;
              gr <- tmLocate1 "toto" ;;
              match gr with
              | VarRef id => let term := tVar id in
                            tmPrint "Here we can get the term"
              | _ => tmFail "Something bad happened"
              end).

End test.

Check (test : nat -> nat).
Check (test2 : nat).
