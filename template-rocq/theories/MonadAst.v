(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Template Require Import Ast.

Import MonadNotation.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Section with_monad.
  Context {T} {M : Monad T}.

  Section map_predicate.
    Context {term term' : Type}.
    Context (uf : Instance.t -> T Instance.t).
    Context (paramf preturnf : term -> T term').

    Definition monad_map_predicate (p : predicate term) :=
      let '{| pparams := pparams;
             puinst := puinst;
             pcontext := pcontext;
             preturn := preturn |} := p in
      pparams <- monad_map paramf pparams;;
      puinst <- uf puinst;;
      preturn <- preturnf preturn;;
      ret {| pparams := pparams;
            puinst := puinst;
            pcontext := pcontext;
            preturn := preturn |}.
  End map_predicate.

  Section map_predicate_k.
    Context {term : Type}.
    Context (uf : Instance.t -> T Instance.t).
    Context (f : nat -> term -> T term).

    Definition monad_map_predicate_k k (p : predicate term) :=
      let '{| pparams := pparams;
             puinst := puinst;
             pcontext := pcontext;
             preturn := preturn |} := p in
      pparams <- monad_map (f k) pparams;;
      puinst <- uf puinst;;
      preturn <- f (#|pcontext| + k) preturn;;
      ret {| pparams := pparams;
            puinst := puinst;
            pcontext := pcontext;
            preturn := preturn |}.

  End map_predicate_k.

  Section map_branch.
    Context {term term' : Type}.
    Context (bbodyf : term -> T term').

    Definition monad_map_branch (b : branch term) :=
      let '{| bcontext := bcontext;
             bbody := bbody |} := b in
      bbody <- bbodyf bbody;;
      ret {| bcontext := bcontext;
            bbody := bbody |}.
  End map_branch.

  Definition monad_map_branches {term B} (f : term -> T B) l := monad_map (monad_map_branch f) l.

  Definition monad_map_branches_k {term term'} f k brs :=
    (monad_map (fun b => @monad_map_branch term term' (f (#|b.(bcontext)| + k)) b) brs).
End with_monad.
