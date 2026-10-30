From MetaRocq.Template Require Import Extraction.
From MetaRocq.ExtractedPluginDemo Require Import Lens MyPlugin.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".
(* dune expects the extracted files in the current directory *)
Set Warnings "-extraction-default-directory".

Extraction Library Lens.
Extraction Library MyPlugin.

