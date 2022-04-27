From Equations Require Import Equations.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
From MetaCoq.Template Require Import LoopChecking.

Extract Constant BinInt.Z.of_nat => "(fun x -> x)".
Extract Constant BinInt.Z.to_nat => "(fun x -> x)".
Extract Constant pr1 => "fst".
Extract Constant pr2 => "snd".

Extraction Inline inspect.
Extraction Inline ReflectEq.eqb ReflectEq.reflect_prod ReflectEq.eq_prod.

Cd "extraction_clauses".

Extraction "loop_checking.ml" LoopChecking.

Cd "..".