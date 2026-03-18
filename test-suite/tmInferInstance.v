From MetaRocq Require Import Template.All.
From Stdlib Require Export String List.

Import MonadNotation.

Existing Class True.
Global Existing Instance I.

MetaRocq Run (tmInferInstance None True >>= tmPrint).
MetaRocq Run (tmInferInstance None False >>= tmPrint).

Section noFixUniverse.
  Set Printing Universes.

  Universes u__opt u1 u2.
  Let set_u__opt :=  (option : Type@{u__opt} -> Type).
  Constraint u__opt < u1.

  Check ( tmInferInstance@{u1 u2}).
End noFixUniverse.
