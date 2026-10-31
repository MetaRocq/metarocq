(* Distributed under the terms of the MIT license. *)
(** * Extraction of the erasure plugin.

    The extraction directives are in [MetaRocq.ErasurePlugin.Extraction]; this file
    only performs the extraction, as a dune [rocq.extraction] prelude. *)

From Stdlib Require Import Ascii FSets ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63 ExtrOCamlPString.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst EGlobalEnv Extract ErasureFunction.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.ErasurePlugin Require Import Extraction.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".
(* The plugin relies on the axioms assumed in [MetaRocq.ErasurePlugin.Erasure]
   (normalization, well-typedness of the erased programs, ...). *)
Set Warnings "-extraction-logical-axiom".
(* dune expects the extracted files in the current directory *)
Set Warnings "-extraction-default-directory".

Separate Extraction ErasureFunction.erase Erasure
         (* The following directives ensure separate extraction does not produce name clashes *)
         Stdlib.Strings.String utils Template.UnivSubst ELiftSubst EGlobalEnv.
