From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import MonadNotation.

MetaRocq Run (tmLocate1 "I" >>= tmDefinition "qI").

Fail MetaRocq Run (tmExistingInstance global qI).

Existing Class True.

MetaRocq Run (tmExistingInstance global qI).
Print Instances True.
