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

(* Qualify the constructors that ExtrOCamlFloats maps to Float64's, so that the
   extracted modules do not need to open Float64. *)
Extract Inductive FloatClass.float_class =>
  "Float64.float_class"
  [ "Float64.PNormal" "Float64.NNormal" "Float64.PSubn" "Float64.NSubn"
    "Float64.PZero" "Float64.NZero" "Float64.PInf" "Float64.NInf" "Float64.NaN" ].
Extract Inductive PrimFloat.float_comparison =>
  "Float64.float_comparison"
  [ "Float64.FEq" "Float64.FLt" "Float64.FGt" "Float64.FNotComparable" ].

(* Extracted as is, eq_equivalence is a record of applications, whose type cannot
   be generalized to match its interface. *)
Extract Constant CRelationClasses.eq_equivalence =>
  "{ rocq_Equivalence_Reflexive = (fun _ -> __);
     rocq_Equivalence_Symmetric = (fun _ _ _ -> __);
     rocq_Equivalence_Transitive = (fun _ _ _ _ _ -> __) }".

Extract Constant Typing.guard_checking => "{ fix_guard = (fun _ _ _ -> true); cofix_guard = (fun _ _ _ -> true) }".

(* The constant constructors of byte are represented as the integers 0..255 in declaration
   order, so they can be compared natively instead of going through binary naturals. *)
Extract Inlined Constant MetaRocq.Utils.ByteCompare.compare =>
  "(fun x y -> let c = Stdlib.compare (Obj.magic x : int) (Obj.magic y : int) in
               if c < 0 then Datatypes.Lt else if c = 0 then Datatypes.Eq else Datatypes.Gt)".
