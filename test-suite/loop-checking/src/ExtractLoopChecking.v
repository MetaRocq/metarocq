From MetaRocq.Template Require Import Extraction.
From MetaRocq.LoopChecking Require Import LoopCheckingPlugin Extraction.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".
(* dune expects the extracted files in the current directory *)
Set Warnings "-extraction-default-directory".

Separate Extraction LoopCheckingPlugin.check_universes
         (* The following directives ensure separate extraction does not produce name clashes *)
         Stdlib.Strings.String utils.
