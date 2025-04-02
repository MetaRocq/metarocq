From MetaCoq Require Import Template.All.
Import MCMonadNotation.

Fixpoint tm_double n : TemplateMonad nat :=
  match n with
  | 0 => ret 0
  | S n =>
      n' <- tm_double n;;
      ret (S (S n'))
  end.

(* these should all run in under 0.2s; previously the final one took ~30s *)
Timeout 3 Time MetaCoq Run (tmPrint =<< tm_double 1000).
Timeout 3 Time MetaCoq Run (tmPrint =<< tm_double 2000).
Timeout 3 Time MetaCoq Run (tmPrint =<< tm_double 3000).
Timeout 3 Time MetaCoq Run (tmPrint =<< tm_double 4000).
Timeout 3 Time MetaCoq Run (tmPrint =<< tm_double 5000).
