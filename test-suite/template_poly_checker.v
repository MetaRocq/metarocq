(** The safe checker on definitions using template polymorphic inductive
    types, which are quoted as universe polymorphic inductive types over their
    template universes (see template_poly.v). *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

(** The sort of a template polymorphic inductive type depends on the sorts
    of its arguments. *)
Definition list_nat_set : Set := list nat.
MetaRocq SafeCheck list_nat_set.

Definition prod_set : Set := (nat * bool)%type.
MetaRocq SafeCheck prod_set.

Universe big.

(** Arguments that do not fit the default universes. *)
Definition list_big := list Type@{big}.
MetaRocq SafeCheck list_big.

Definition nil_big : list Type@{big} := nil.
MetaRocq SafeCheck nil_big.

Universe small.
Constraint small < big.
Definition cons_big : list Type@{big} := cons Type@{small} nil.
MetaRocq SafeCheck cons_big.

Definition length_big (x : list Type@{big}) : nat :=
  match x with nil => 0 | cons _ _ => 1 end.
MetaRocq SafeCheck length_big.

(** Partial applications and unapplied inductive types use the default
    universes. *)
Definition list_fun := @List.map nat bool.
MetaRocq SafeCheck list_fun.

Definition bool_list := List.map negb (cons true (cons false nil)).
MetaRocq SafeCheck bool_list.

Definition list_arg (f : Type -> Type) := f nat.
Definition list_arg_list := list_arg list.
MetaRocq SafeCheck list_arg_list.

(** Arguments in Prop: MetaRocq has no sort qualities and counts them as
    Set, so applications of template polymorphic inductive types to
    propositions live in Set, while Rocq can put them in Prop. This is
    enough as long as they are not used as propositions. *)
Definition prod_prop_set : Set := (True * True)%type.
MetaRocq SafeCheck prod_prop_set.

Definition list_prop : Set := list True.
MetaRocq SafeCheck list_prop.

Definition sum_prop : Set := (True + False)%type.
MetaRocq SafeCheck sum_prop.

Definition pair_prop (A : Prop) (x : A) : A * A := (x, x).
MetaRocq SafeCheck pair_prop.

Definition pair_I := pair_prop True I.
MetaRocq SafeCheck pair_I.

(* Rocq types [True * True] in Prop, MetaRocq only in Set. *)
Definition prod_prop : Prop := (True * True)%type.
Fail MetaRocq SafeCheck prod_prop.

Definition prod_prop_fun (A : Prop) : Prop := (A * A)%type.
Fail MetaRocq SafeCheck prod_prop_fun.

(** A template polymorphic record with primitive projections. *)
Set Primitive Projections.
Inductive R (A : Type) : Type := mkR { fld : A }.
Unset Primitive Projections.

(* [fld x] elaborates through the projection constant [fld], whose parameter
   is at the default universe: a pattern matching elaborates to the primitive
   projection itself. *)
Definition fld_big (x : R Type@{big}) := match x with mkR y => y end.
MetaRocq SafeCheck fld_big.

Definition mkR_set : R nat := mkR _ 0.
MetaRocq SafeCheck mkR_set.
