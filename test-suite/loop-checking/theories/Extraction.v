Require Import Template.Extraction.
From MetaCoq.LoopChecking Require Import LoopCheckingPlugin.

Extract Constant BinInt.Z.of_nat => "(fun x -> x)".
Extract Constant BinInt.Z.to_nat => "(fun x -> x)".

Cd "gen-src".

Extraction Library LoopChecking.
Extraction Library TemplateLoopChecking.
Extraction Library LoopCheckingPlugin.

Cd "..".
