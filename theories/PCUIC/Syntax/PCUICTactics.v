
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICLiftSubst
  PCUICSigmaCalculus.

#[global] Hint Extern 20 (#|?X| = #|?Y|) =>
  match goal with
  [ H : All2_fold _ ?X ?Y |- _ ] => apply (All2_fold_length H)
  | [ H : All2_fold _ ?Y ?X |- _ ] => symmetry; apply (All2_fold_length H)
  | [ H : on_contexts_over _ _ _ ?X ?Y |- _ ] => apply (All2_fold_length H)
  | [ H : on_contexts_over _ _ _ ?Y ?X |- _ ] => symmetry; apply (All2_fold_length H)
   end : pcuic.

Ltac pcuic_core :=
  try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

Ltac pcuic :=
  pcuic_core || ltac:(try (red; repeat red; cbn in *; pcuic_core)).

Definition lengths :=
  (@context_assumptions_expand_lets_ctx,
   @context_assumptions_subst_context,
   context_assumptions_fold,
   @context_assumptions_app,
   @context_assumptions_map,
   @context_assumptions_mapi,
   @context_assumptions_mapi_context,
   @context_assumptions_smash_context,
   @context_assumptions_subst_instance,
   @context_assumptions_lift_context,
   @inst_case_context_assumptions,
    @expand_lets_ctx_length, @subst_context_length,
    @subst_instance_length, @expand_lets_k_ctx_length, @inds_length, @lift_context_length,
    @length_app, @repeat_length, @List.length_rev, @extended_subst_length, @reln_length,
    Nat.add_0_r, @app_nil_r, @length_rev_map, @length_rev, @unfold_length,
    @length_map, @mapi_length, @mapi_rec_length, @map_InP_length,
    @fold_context_length,
    @fold_context_k_length, @cofix_subst_length, @fix_subst_length,
    fix_context_length,
    @smash_context_length,
    @arities_context_length,
    @forget_types_length,
    @PCUICCases.ind_predicate_context_length,
    @PCUICCases.cstr_branch_context_length,
    @PCUICCases.inst_case_branch_context_length,
    @PCUICCases.inst_case_predicate_context_length,
    @inst_case_context_length,
    @ind_predicate_context_length,
    @map_context_length, @length_skipn_map,
    @mapi_context_length, idsn_length,
    @projs_length, ren_ids_length).

Ltac len ::=
  repeat (rw !lengths /= //); try solve [lia_f_equal].

Tactic Notation "len" "in" hyp(id) :=
  repeat (rw !lengths /= // in id);
  try solve [lia_f_equal].

(* Can be used after [move] by ssr tactics, e.g. [rewrite foo => /lens] *)
Notation "'lens'" := ltac:(len) (only parsing).

