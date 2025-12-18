Require Import MetaRocq.Template.All.
From MetaRocq Require Import TemplateToPCUIC PCUICTemplateMonad PCUICPretty.
Require Import MetaRocq.ErasurePlugin.Loader.

Fixpoint even n := match n with O => true | S n => odd n end
with odd n := match n with O => false | S n => even n end.

MetaRocq Erase even.

MetaRocq Quote Recursively Definition evenq := even.
Definition evenqpcuic := let '(Σext, t) := trans_template_program evenq in (PCUICProgram.trans_env_env Σext.1, t).
Definition pp := show evenqpcuic.

Eval compute in pp.
