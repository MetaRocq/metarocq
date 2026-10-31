From MetaRocq.Template Require Import Extraction.
From MetaRocq.LoopChecking Require Import LoopCheckingPlugin.

(** Same setup as the erasure and safechecker plugins: the extracted modules already
    provided by the template plugin are not part of this plugin (see ../src/dune). *)
Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int Init
           UnivSubst Typing Checker Retyping OrderedType Logic Common Common0 Equality Classes
           Uint63 Induction Monad.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.
