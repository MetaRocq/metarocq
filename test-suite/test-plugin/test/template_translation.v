From MetaRocq.TestPlugin Require Import Loader.

(* Regressions for the translation of template-polymorphic inductives that
   SafeCheck runs before checking (see safechecker_test.v). *)

(* Changing impredicative Set changes the sort retyping assigns to this shared
   template argument.  The test command uses one quotation cache across both
   environments and compares the second result with a fresh quotation. *)
Universe template_cache_flags_u.
MetaRocq Test Cache Typing Flags
  (list (forall X : Type@{template_cache_flags_u}, nat)).

(* The application [list A] is one physical kernel term in both lambdas, but
   retyping [A] sees a different Rel declaration in each body.  The command
   compares the second body with both the first and a fresh quotation. *)
Universes template_cache_rel_i template_cache_rel_j.
MetaRocq Test Quoter Rel Context Cache
  (fun A : Type@{template_cache_rel_i} => list A)
  Type@{template_cache_rel_j}.

(* Initially neither global level is below the other, so quoting their maximum
   mints a representative.  The command then uses [push_context_set] to add
   [template_cache_graph_i < template_cache_graph_j]; the maximum quotes as
   [template_cache_graph_j] under that graph and must not reuse the first
   cache entry. *)
Universes template_cache_graph_i template_cache_graph_j.
MetaRocq Test Quoter Graph Cache
  Type@{template_cache_graph_i} Type@{template_cache_graph_j}.

(* The first quotation retypes an argument constant in an environment extended
   with that constant.  The same physical application is then quoted under the
   original environment, where a fresh quotation rejects the missing global;
   a cache hit must not hide that rejection. *)
MetaRocq Test Quoter Global Environment Cache list.

(* The compound product has a scope-dependent child.  The test confirms a hit
   in the same scope, a miss in another scope, and rejection outside a scope. *)
MetaRocq Test Quoter Scope Cache.

(* The quoter refuses a bound universe at offset two inside a polymorphic
   declaration.  The command confirms that the refusal restores the
   translation's name, scope, dependency-root and in-progress state, and that
   the translation then still rejects a bound level outside a declaration. *)
MetaRocq Test Quoter Restores State.

Set Universe Polymorphism.

(* The upper-bound pass must let [Control.Timeout] leave its graph query. *)
MetaRocq Test Quoter Propagates Timeout.

(* Inside a polymorphic declaration, the level minted for [max(i, j)] gets the
   upper bound [<= k] only when the declaration's constraints prove
   [max(i, j) <= k]: with [i <= k] and [j <= k], not with [i <= k] alone. *)
MetaRocq Test Quoter Local Upper Bounds.

(* Template sort qualities are not translated.  Rocq assigns [prod True True]
   to [Prop], while the translated template instance is in [Set].  Pin the
   known completeness refusal to that comparison rather than to any error. *)
Definition template_prod_prop : Prop := prod True True.
MetaRocq Test SafeCheck Rejects Source
  "Types are not convertible:
Type([Set])
and:
Prop"
  "template_prod_prop" template_prod_prop.

(* This calls the extracted SafeCheck entrypoint after trusted quotation, then
   adds a quoted declaration whose [Type@{Set}] body is claimed at
   [Type@{Set}], the successor-too-low condition that Rocq rejects for
   [template_successor_too_low] in safechecker_test.v. *)
MetaRocq Test SafeCheck Rejects
  "Terms
Type([Set+1])
and
Type([Set])
do not have the same head when comparing for cumulativity"
  "while checking Regression.MetaRocq.successor_too_low" nat.

(* Input-side negative fixtures: the obligation each one breaks exists in the
   environment before quotation, and each goes through the production
   SafeCheck path.  Each asserts the part of the checker's message that names
   the failing check and its two sorts, and the subject of the rejection. *)

(* [Set : Type@{Set+1}], so this declaration's claimed type is wrong.  The
   quoter must hand the checker this declared type, not a type inferred from
   the body, which would be the type of a repaired declaration. *)
Unset Universe Checking.
Definition template_declared_type_is_checked : Set := Set.
Set Universe Checking.
MetaRocq Test SafeCheck Rejects Source
  "Terms
Type([Set+1])
and
Type([Set])
do not have the same head when comparing for cumulativity"
  "template_declared_type_is_checked"
  template_declared_type_is_checked.

(* A bound universe [u] has no lower bound, so a cast from
   [Type@{max(Set+1,u)}] to [Type@{u}] is not justified.  Dropping the [Set+1]
   component would make that cast reflexive and erase the obligation.  Rocq
   cannot write an algebraic sort in a binder, so the command builds the
   declaration in the kernel environment the quoter reads.  The checker sees
   [max(Set+1,u)] as the fresh bound level [lvar1] and [u] as [lvar0]. *)
MetaRocq Test Quoter Set Successor Cast
  "Terms
Type([lvar1])
and
Type([lvar0])
do not have the same head when comparing for cumulativity"
  "while checking Regression.MetaRocq.set_successor_cast".

(* [bad : Type@{d} := list Type@{d}], where [d] is [list]'s own template
   default universe.  [Type@{d} : Type@{d+1}], so the declaration needs
   [d+1 <= d] and must be rejected.  Its body is headed by a template
   inductive, so it reaches the path where a substitution keyed on the body's
   instance could replace the declared [d] by the body's larger
   representative and repair the declaration.  The default is read from the
   inductive's metadata, not named here: the command puts its name where the
   expected message says [<default>].  The body's sort is the level the quoter
   mints for [d+1], [Template.MetaRocq.algebraic.1]. *)
MetaRocq Test Quoter Declared Default
  "Terms
Type([Template.MetaRocq.algebraic.1])
and
Type([<default>])
do not have the same head when comparing for cumulativity"
  "while checking Regression.MetaRocq.declared_type_successor" list.

Unset Universe Polymorphism.

(* Controls for the inductive-sort check that [template_injtyp] in
   safechecker_test.v relies on: a constructor argument in a larger universe
   than the declared sort.  Universe checking is off only while Rocq accepts
   the declarations.  [neg_sort_poly] has the shape the template translation
   produces: a declared sort that is a bound level [u], which an instance may
   set to [Set], below a field in [max(u, Set+1)].  The empty constraint list
   [@{u|}] keeps Rocq from adding [Set < u].  (A named global universe would
   not do: Rocq's graph holds [Set < u] for it.) *)
Unset Universe Checking.
Record neg_sort_mono : Set := { neg_sort_mono_f : Prop }.
Polymorphic Record neg_sort_poly@{u|} (T : Type@{u}) : Type@{u} :=
  { neg_sort_poly_f : T -> Prop }.
Set Universe Checking.
MetaRocq Test SafeCheck Rejects Source
  "Incorrect inductive sort: The constructor arguments universes are not smaller than the declared inductive sort"
  "neg_sort_mono" @neg_sort_mono.
MetaRocq Test SafeCheck Rejects Source
  "Incorrect inductive sort: The constructor arguments universes are not smaller than the declared inductive sort"
  "neg_sort_poly" @neg_sort_poly.

(* A known limit.  A polymorphic SafeCheck keeps the universes of its
   elaborated input, and their constraints, in the context of the toplevel
   term, not in the global graph.  The upper-bound pass queries the global
   graph, so the level minted at this use for [max(i, j)] of the instance
   gets no upper bound [<= k], and the instance does not satisfy the
   constraint of [template_local_upper2] that bounds that level by [k].  The
   monomorphic SafeCheck of the same declaration is accepted
   (safechecker_test.v). *)
Polymorphic Definition template_local_upper2@{i j k | i <= k, j <= k}
  (X : Type@{i}) (Y : Type@{j}) : Type@{k} := list (prod X Y).
#[universes(polymorphic)]
MetaRocq Test SafeCheck Rejects Source
  "ctrs not satisfiable" "while checking toplevel term" @template_local_upper2.

(* Control for the variance of a level that the translation adds to a
   cumulative inductive: that level gets Irrelevant variance, and the check
   of the declaration's own levels must stay.  [i] is invariant, and the
   definition below needs [template_cum_inv@{a c} <= template_cum_inv@{b c}]
   with [a < b], which Rocq refuses.  Unset Universe Checking lets it in, and
   SafeCheck must still refuse it for that comparison. *)
Polymorphic Cumulative Inductive template_cum_inv@{=i j | i < j} : Type@{j} :=
  template_cum_inv_C : list Type@{i} -> template_cum_inv.
Universes template_cum_inv_a template_cum_inv_b template_cum_inv_c.
Constraint template_cum_inv_a < template_cum_inv_b.
Constraint template_cum_inv_b < template_cum_inv_c.
Fail Definition template_cum_inv_rocq
  (x : template_cum_inv@{template_cum_inv_a template_cum_inv_c})
  : template_cum_inv@{template_cum_inv_b template_cum_inv_c} := x.
Unset Universe Checking.
Definition template_cum_inv_bad
  (x : template_cum_inv@{template_cum_inv_a template_cum_inv_c})
  : template_cum_inv@{template_cum_inv_b template_cum_inv_c} := x.
Set Universe Checking.
MetaRocq Test SafeCheck Rejects Source
  "do not have the same head when comparing for cumulativity"
  "template_cum_inv_bad"
  template_cum_inv_bad.

(* The same control where the added levels differ and the declaration's own
   variance decides: [i] is covariant (the accepted direction is
   [pdt_pos_up] in safechecker_test.v), and this definition needs the
   reverse, [pdt_pos_w2 <= pdt_pos_w1], which Rocq refuses.  SafeCheck must
   refuse it for that comparison. *)
Polymorphic Cumulative Inductive pdt_pos@{i k j | i < j, k <= j}
  (A : Type@{i}) (B : Type@{k}) : Type@{j} :=
  pdt_pos_C : (A -> Type@{i}) -> list (A * B) -> pdt_pos A B.
Universes pdt_pos_w1 pdt_pos_w2 pdt_pos_v1 pdt_pos_v2 pdt_pos_z.
Constraint pdt_pos_w1 < pdt_pos_w2.
Constraint pdt_pos_v1 < pdt_pos_v2.
Constraint pdt_pos_w2 < pdt_pos_z.
Constraint pdt_pos_v2 < pdt_pos_z.
Fail Definition pdt_pos_bad_rocq (A : Type@{pdt_pos_w1}) (B : Type@{pdt_pos_v1})
  (v : pdt_pos@{pdt_pos_w2 pdt_pos_v2 pdt_pos_z} A B)
  : pdt_pos@{pdt_pos_w1 pdt_pos_v1 pdt_pos_z} A B := v.
Unset Universe Checking.
Definition pdt_pos_bad (A : Type@{pdt_pos_w1}) (B : Type@{pdt_pos_v1})
  (v : pdt_pos@{pdt_pos_w2 pdt_pos_v2 pdt_pos_z} A B)
  : pdt_pos@{pdt_pos_w1 pdt_pos_v1 pdt_pos_z} A B := v.
Set Universe Checking.
MetaRocq Test SafeCheck Rejects Source
  "do not have the same head when comparing for cumulativity"
  "pdt_pos_bad"
  pdt_pos_bad.
