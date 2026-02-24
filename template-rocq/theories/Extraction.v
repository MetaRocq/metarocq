(* Distributed under the terms of the MIT license. *)
(** * Extraction setup for template-rocq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

From Stdlib Require Ascii Extraction ZArith NArith.

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Reflect config.
From MetaRocq.Template Require Import Ast Induction.
From Stdlib Require Import FSets ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63 ExtrOCamlPString.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.

Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality UnivSubst Numeral
           Uint63 Induction Monad.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

From MetaRocq.Template Require Import TemplateMonad.Extractable Induction
     LiftSubst UnivSubst Pretty TemplateProgram.
Import Init.Nat.

Extract Inductive Common.hint_locality => "Hints.hint_locality" ["Hints.Local" "Hints.Export" "Hints.SuperGlobal"].
Extract Constant Typing.guard_checking => "{ fix_guard = (fun _ _ _ -> true); cofix_guard = (fun _ _ _ -> true) }".

Set Extraction Output Directory "gen-src".

(* Silence the warnings for specifications axioms of int63 *)
Set Warnings "-extraction-logical-axiom".
(* Floats *)
Separate Extraction FloatOps.Prim2SF.

Recursive Extraction Library Extractable.
Extraction Library MRPrelude.
Extraction Library MROption.
Extraction Library MRUtils.
Extraction Library MRList.
Extraction Library EqDecInstances.
Extraction Library Induction.
Extraction Library LiftSubst.
Extraction Library UnivSubst.
Extraction Library BasicAst.

Extraction Library Reflect.
Extraction Library Pretty.
Extraction Library config.

Recursive Extraction Library TemplateProgram.
