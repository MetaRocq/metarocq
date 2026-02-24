From MetaRocq.Utils Require Import monad_utils.

Inductive result T E :=
| Ok (t : T)
| Err (e : E).

Arguments Ok {_ _}.
Arguments Err {_ _}.

Global Instance Monad_result {E} : Monad (fun T => result T E) :=
  {| ret _ t := Ok t;
     bind _ _ mt f :=
     match mt with
     | Ok t => f t
     | Err e => Err e
     end |}.

Definition map_error {T E1 E2} (f : E1 -> E2) (r : result T E1) : result T E2 :=
  match r with
  | Ok t => Ok t
  | Err e => Err (f e)
  end.
