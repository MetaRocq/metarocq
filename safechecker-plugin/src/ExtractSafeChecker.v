(* Distributed under the terms of the MIT license. *)
(** * Extraction of the safechecker plugin.

    The extraction directives are in [MetaRocq.SafeCheckerPlugin.Extraction]; this file
    only performs the extraction, as a dune [rocq.extraction] prelude. *)

From Stdlib Require Import OrdersTac Ascii ExtrOcamlBasic ExtrOCamlInt63 ExtrOCamlFloats.
From MetaRocq.Utils Require Import utils.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl PCUICSafeChecker PCUICSafeConversion.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateChecker.
From MetaRocq.SafeCheckerPlugin Require Import Extraction.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".
(* dune expects the extracted files in the current directory *)
Set Warnings "-extraction-default-directory".

Separate Extraction Wf.Fix_sub MakeOrderTac PCUICSafeChecker.typecheck_program
         infer_and_print_template_program_with_guard
         (* The following directives ensure separate extraction does not produce name clashes *)
         Stdlib.Strings.String UnivSubst PCUICPretty.
