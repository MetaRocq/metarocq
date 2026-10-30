(* Distributed under the terms of the MIT license. *)
(** * Extraction of the extractable template-rocq plugin.

    The extraction directives are in [MetaRocq.Template.Extraction]; this file
    only performs the extraction, as a dune [rocq.extraction] prelude. *)

From MetaRocq.Template Require Import Extraction.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".
(* dune expects the extracted files in the current directory *)
Set Warnings "-extraction-default-directory".

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
