From MetaRocq Require Import Template.Loader.
Import bytestring.

Definition I (t:Type) (x:t) : t := x.
Definition II := I (forall t:Type, t -> t) I.
MetaRocq Quote Definition qII := Eval compute in II.
