From Stdlib Require Import String.
From MetaRocq.Template Require Import monad_utils All.
From Stdlib.Numbers.Cyclic Require Import PrimInt63 Sint63.

Local Open Scope string_scope.
Local Open Scope sint63_scope.
Import MonadNotation.

Definition bigint : PrimInt63.int := 542985047%int63.

Abbreviation eval_hnf := (tmEval hnf).
Abbreviation eval := (tmEval all).

MetaRocq Run (eval_hnf bigint >>=
            (fun x => tmQuote (x + 1)%int63) >>=
            tmMkDefinition "foo").

Print foo.

MetaRocq Run (eval_hnf bigint >>=
            (fun x => tmQuote (x + 1)%int63 >>= fun q =>
            tmUnquoteTyped int q >>= fun unq =>
            tmPrint unq >>= fun _ =>
            tmLemma "foo'" (bigint + 1 = unq)%int63 >>=
            fun x => tmPrint x)).

From Stdlib Require Import PrimFloat.

Definition f := (- (of_uint63 bigint / 3))%float.
Eval lazy in f.
MetaRocq Run (tmEval lazy f >>=
            (fun x => tmQuote (x + 1)%float) >>=
            tmMkDefinition "fplus1").

MetaRocq Run (tmUnquoteTyped float (tFloat f) >>=
  (fun x : float => tmPrint x >>=
   fun _ => tmQuote x >>= tmMkDefinition "somefloat")).
Print somefloat.
