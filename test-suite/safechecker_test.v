From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From MetaRocq Require Import SafeCheckerPlugin.SafeTemplateChecker.

Local Open Scope string_scope.

MetaRocq SafeCheck nat.
(*
Environment is well-formed and Ind(Stdlib.Init.Datatypes.nat,0,[]) has type: Sort([Set])
*)

MetaRocq SafeCheck (3 + 1).

Definition bool_list := List.map negb (cons true (cons false nil)).
MetaRocq SafeCheck bool_list.
MetaRocq RocqCheck bool_list.

Record template_list_record := { template_list_field : list nat }.
MetaRocq SafeCheck template_list_record.
MetaRocq SafeCheck (list nat).

(* The command must retain universes minted while elaborating its input. *)
MetaRocq SafeCheck (fun (A : Type) (B : Type) => prod A B).

Definition template_list_to_nat : list nat -> nat := fun _ => 0.
MetaRocq SafeCheck template_list_to_nat.

Definition template_list_match (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | cons x _ => x
  end.
MetaRocq SafeCheck template_list_match.

From Stdlib Require Import Ring_theory.
MetaRocq SafeCheck (prod nat nat).
MetaRocq SafeCheck (prod True True).
MetaRocq SafeCheck @Stdlib.setoid_ring.Ring_theory.div_theory.
From Stdlib Require Import CRelationClasses.

(* [iffT] applies template [prod] at [max(i,j)] inside a polymorphic
   declaration.  It therefore covers scoped algebraic instances, their
   explicit sort annotations, and the extended universe instance at use. *)
Definition template_iffT_nat := iffT nat nat.
MetaRocq SafeCheck template_iffT_nat.

(* [sigT]'s second template parameter is a family [A -> Type@{u}], not a sort;
   the kernel binds [u] from the arity's conclusion (make_param_univs). *)
Definition template_sigT_nat := {n : nat & nat}.
MetaRocq SafeCheck template_sigT_nat.

(* Issue #16: nested [sigT] instances at independent universes. *)
Definition template_issue16 := {A : Type & {B : Type & A}}.
MetaRocq SafeCheck template_issue16.

(* One kernel match on template [prod] reached in two contexts.  The kernel
   stores no instance on it, so the translated case instance must not depend
   on the context.  Typing [f h] converts [template_case_eq nat p] with
   [template_case_eq_nat p]; both unfold to the stuck match on [p], quoted
   once with [C : Type@{template_case_u}] and once with [nat : Set]
   (seen in the wild on a [cdiv] match in [Ring_polynom], at [Ring_polynom.22]
   and [Ring_theory.98]).  The conversion is placed inside the body because
   that is where the two occurrences meet: the quoter quotes a constant's
   declared type as the kernel stores it, so the type alone would not bring
   them together.  A named universe keeps minimization from turning
   [template_case_u] into [Set]. *)
Universe template_case_u.
Definition template_case_eq (C : Type@{template_case_u}) (p : C * C) : Prop :=
  match p with pair a b => a = b end.
Definition template_case_eq_nat (p : nat * nat) : Prop :=
  match p with pair a b => a = b end.
Definition template_case_instance (p : nat * nat)
  (f : template_case_eq_nat p -> nat) (h : template_case_eq nat p) : nat :=
  f h.
MetaRocq SafeCheck @template_case_instance.

(* A partially applied template inductive is compared with exact instances
   in PCUIC.  Typing [g _ h] converts [template_partial_rel nat], which
   unfolds to [@eq A] quoted at [A : Type@{template_case_u}], with [@eq nat]
   (Z.eq_equiv: [eq@{RelationClasses.21} Z] against [eq@{Set} Z]). *)
Definition template_partial_rel (A : Type@{template_case_u}) : A -> A -> Prop :=
  @eq A.
Definition template_partial_instance (P : (nat -> nat -> Prop) -> Prop)
  (g : forall R, P R -> nat) (h : P (@eq nat)) : nat :=
  g (template_partial_rel nat) h.
MetaRocq SafeCheck @template_partial_instance.

(* A record whose field has an algebraic sort below the record's algebraic
   sort.  Each algebraic sort is quoted as a fresh level; the inductive-sort
   check needs [template_alg_inner]'s level below [template_alg_outer]'s,
   which the kernel derives from [max(a+1, b+1) <= max(a+1, b+1, c+1)]
   (seen in the wild on a record whose field sort is a strict sub-maximum of
   the record's own sort). *)
Universes template_alg_a template_alg_b template_alg_c.
Record template_alg_inner := {
  template_alg_ia : Type@{template_alg_a};
  template_alg_ib : Type@{template_alg_b} }.
Record template_alg_outer := {
  template_alg_oi : template_alg_inner;
  template_alg_oc : Type@{template_alg_c} }.
MetaRocq SafeCheck @template_alg_outer.

(* A template class with two [Type] parameters whose field [T -> Prop] lives
   in [max(u1, Set+1)], since [Prop : Type@{Set+1}].  Its sort is
   [max(Set+1, u0, u1)], and the template levels may be [Set].  The quoter must
   keep the [Set+1] component of that sort: without it the declared sort's
   representative is only above [u0] and [u1], and the inductive-sort check
   fails (seen on Stdlib's [ZifyClasses.InjTyp]). *)
#[universes(template)]
Class template_injtyp (S : Type) (T : Type) := {
  template_injtyp_inj : S -> T;
  template_injtyp_pred : T -> Prop;
  template_injtyp_cstr : forall x, template_injtyp_pred (template_injtyp_inj x) }.
MetaRocq SafeCheck @template_injtyp.

(* SafeCheck uses default checker flags even when quotation runs while Rocq
   universe checking is disabled.  The upper-bound pass must still ask a
   checking graph what follows from the source graph. *)
Unset Universe Checking.
MetaRocq SafeCheck @template_alg_outer.
Set Universe Checking.

Set Universe Polymorphism.
(* This nested use gives [list] the algebraic template instance [max(i,j)].
   It exercises the shared representative in both the list instance and the
   explicit result-sort annotation. *)
Polymorphic Definition template_list_prod@{i j}
  (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
  list (prod A B).
Definition template_list_prod_nat := template_list_prod nat nat.
MetaRocq SafeCheck template_list_prod_nat.

(* Rocq rejects this: [list Type@{i}] lives in [Type@{i+1}], not in
   [Type@{i}].  No SafeCheck runs here; MetaRocq Test SafeCheck Rejects in
   test-plugin/test/template_translation.v checks that the checker rejects
   the same comparison. *)
Fail Polymorphic Definition template_successor_too_low@{i} : Type@{i} :=
  list Type@{i}.

Unset Universe Polymorphism.

(* The level for [max(i, j)] minted inside a polymorphic declaration gets the
   upper bounds that the declaration's constraints prove: typing the body at
   [Type@{k}] needs [max(i, j) <= k], which follows from [i <= k] and
   [j <= k].  (These SafeCheck commands are monomorphic: the universes of the
   elaborated input go to the global graph, where the upper-bound pass sees
   them.  test-plugin/test/template_translation.v pins the polymorphic
   command, where it does not.) *)
Polymorphic Definition template_local_upper@{i j k | i <= k, j <= k}
  (X : Type@{i}) (Y : Type@{j}) : Type@{k} := list (prod X Y).
MetaRocq SafeCheck @template_local_upper.

(* A use of it inside another polymorphic declaration, at a global upper
   level: the use's own level for [max(a, b)] must be below that global
   level, which the use's constraints prove. *)
Universe template_local_g.
Polymorphic Definition template_local_upper_use@{a b | a <= template_local_g, b <= template_local_g}
  (X : Type@{a}) (Y : Type@{b}) : Type@{template_local_g} :=
  template_local_upper@{a b template_local_g} X Y.
MetaRocq SafeCheck @template_local_upper_use.

(* A cumulative polymorphic inductive whose constructor uses list at
   [Type@{i}]: the translation adds a level to its context for list's
   instance [i+1], and its variance needs an entry for that level too.  It is
   used at two instances, and once through cumulativity on [j]. *)
Polymorphic Cumulative Inductive template_cum@{i j | i < j} : Type@{j} :=
  template_cum_C : list Type@{i} -> template_cum.
MetaRocq SafeCheck template_cum.
Universes template_cum_a template_cum_b template_cum_c.
Constraint template_cum_a < template_cum_b.
Constraint template_cum_b < template_cum_c.
Definition template_cum_two :=
  (template_cum@{template_cum_a template_cum_c},
   template_cum@{template_cum_b template_cum_c}).
MetaRocq SafeCheck template_cum_two.
Definition template_cum_up (x : template_cum@{template_cum_a template_cum_b})
  : template_cum@{template_cum_a template_cum_c} := x.
MetaRocq SafeCheck template_cum_up.

(* Why the level that the translation adds gets Irrelevant variance: here
   [i] is covariant, and the added level is list's instance [max(i, k)].  The
   use below compares two instances whose original levels are related by the
   declaration's own variance, and whose added levels differ.  Rocq accepts
   it, and so must SafeCheck: an added level with Invariant variance would
   reject it. *)
Polymorphic Cumulative Inductive pdt_pos@{i k j | i < j, k <= j}
  (A : Type@{i}) (B : Type@{k}) : Type@{j} :=
  pdt_pos_C : (A -> Type@{i}) -> list (A * B) -> pdt_pos A B.
MetaRocq SafeCheck pdt_pos.
Universes pdt_pos_w1 pdt_pos_w2 pdt_pos_v1 pdt_pos_v2 pdt_pos_z.
Constraint pdt_pos_w1 < pdt_pos_w2.
Constraint pdt_pos_v1 < pdt_pos_v2.
Constraint pdt_pos_w2 < pdt_pos_z.
Constraint pdt_pos_v2 < pdt_pos_z.
Definition pdt_pos_up (A : Type@{pdt_pos_w1}) (B : Type@{pdt_pos_v1})
  (v : pdt_pos@{pdt_pos_w1 pdt_pos_v1 pdt_pos_z} A B)
  : pdt_pos@{pdt_pos_w2 pdt_pos_v2 pdt_pos_z} A B := v.
MetaRocq SafeCheck pdt_pos_up.

(* A known limit.  Rocq types [prod True True] in [Prop]: the template
   quality of [prod] follows its arguments.  The translation drops template
   qualities and gives the instance [Type@{Set}], so SafeCheck rejects a
   declaration that needs [Prop]. *)
Definition template_prod_prop : Prop := prod True True.
Fail MetaRocq SafeCheck template_prod_prop.

(* Time MetaRocq SafeCheck @infer_and_print_template_program. *)
(* Fails after about 30 seconds on Rocq 9.2.0, before the checker runs:
Error: Quoting sort polymorphic abstract universe context not yet supported.
*)

(* Unset Universe Minimization ToSet. *)

(* From Stdlib Require Import Decimal. *)
From Stdlib Require Import Decimal.
Definition bignat : nat := Nat.of_num_uint 10000%uint.
MetaRocq SafeCheck bignat.
MetaRocq RocqCheck bignat.

Set Warnings "-notation-overriden".
From MetaRocq.TestSuite Require Import hott_example.

MetaRocq SafeCheck @issect'.

MetaRocq SafeCheck @ap_pp.
MetaRocq RocqCheck ap_pp.

Set MetaRocq Timing.

From MetaRocq.TestSuite Require Import hott_example.

(* FIXME TODO Private polymorphic universes *)
MetaRocq SafeCheck @isequiv_adjointify.
MetaRocq RocqCheck isequiv_adjointify.

MetaRocq SafeCheck @IsEquiv.
MetaRocq RocqCheck IsEquiv.
