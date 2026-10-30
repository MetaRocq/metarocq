(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.PCUIC Require Import PCUICAst.

Import MonadNotation.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Section with_monad.
  Context {T} {M : Monad T}.

  Section map_predicate.
    Context {term term' : Type}.
    Context (uf : Instance.t -> T Instance.t).
    Context (paramf preturnf : term -> T term').
    Context (pcontextf : list (BasicAst.context_decl term) -> T (list (BasicAst.context_decl term'))).

    Definition monad_map_predicate (p : predicate term) :=
      pparams <- monad_map paramf p.(pparams);;
      puinst <- uf p.(puinst);;
      preturn <- preturnf p.(preturn);;
      pcontext <- pcontextf p.(pcontext);;
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
      pparams <- monad_map (f k) p.(pparams);;
      puinst <- uf p.(puinst);;
      preturn <- f (#|p.(pcontext)| + k) p.(preturn);;
      ret {| pparams := pparams;
            puinst := puinst;
            pcontext := p.(pcontext);
            preturn := preturn |}.

  End map_predicate_k.

  Section map_branch.
    Context {term term' : Type}.
    Context (bbodyf : term -> T term').
    Context (bcontextf : list (BasicAst.context_decl term) -> T (list (BasicAst.context_decl term'))).

    Definition monad_map_branch (b : branch term) :=
      bbody <- bbodyf b.(bbody);;
      bcontext <- bcontextf b.(bcontext);;
      ret {| bcontext := bcontext;
            bbody := bbody |}.
  End map_branch.

  Definition monad_map_branches {term B} (f : term -> T B) (g : list (BasicAst.context_decl term) -> T (list (BasicAst.context_decl B))) l := monad_map (monad_map_branch f g) l.

  Definition monad_map_branch_k {term term'} (f : nat -> term -> T term') g k b
    := @monad_map_branch term term' (f (#|bcontext b| + k)) g b.

  Definition monad_map_branches_k {term term'} f h k brs :=
    (monad_map (@monad_map_branch_k term term' f h k) brs).
End with_monad.
