(* Distributed under the terms of the MIT license. *)
From Coq Require Import Ascii FSets ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63.
From MetaCoq.Utils Require Import utils.
From PPrint Require Import Utils.

(** * Extraction setup for the erasure phase of template-coq.

    Any extracted code planning to link with the plugin
    should use these same directives for consistency.
*)

Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common ws_cumul_pb Classes Numeral
           Uint63 Induction.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

From MetaCoq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst EGlobalEnv Extract ErasureFunction.
From MetaCoq.ErasurePlugin Require Import Erasure.

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

(* Extract Constant PCUICWfEnvImpl.guard_impl => "(fun _ _ _ _ -> true)".
Extract Constant PCUICTyping.guard_checking => "(fun _ _ _ _ -> true)". *)

Set Extraction Output Directory "src".

Separate Extraction ErasureFunction.erase Erasure
         (* The following directives ensure separate extraction does not produce name clashes *)
         PPrint.Utils Coq.Strings.String utils Template.UnivSubst ELiftSubst EGlobalEnv.

