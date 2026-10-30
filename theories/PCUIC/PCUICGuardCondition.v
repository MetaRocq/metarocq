(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICEquality PCUICTyping PCUICReduction PCUICSigmaCalculus
     PCUICNamelessDef PCUICRenameDef PCUICInstDef.

(* AXIOM postulate correctness of the guard condition checker *)

Definition tFixCoFix (b:FixCoFix) := if b then tFix else tCoFix.

Definition nl_mfix mfix := map (map_def_anon nl nl) mfix.

Definition subst_instance_mfix (mfix : list (def term)) u := map (map_def (subst_instance u) (subst_instance u)) mfix.

Definition inst_mfix mfix σ := map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix.

Definition rename_mfix mfix f := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix.

Class GuardCheckerCorrect :=
{
  guard_red1 b Σ Γ mfix mfix' idx :
    Σ.1 ;;; Γ |- tFixCoFix b mfix idx ⇝ tFixCoFix b mfix' idx ->
    guard b Σ Γ mfix ->
    guard b Σ Γ mfix' ;

  guard_eq_term b Σ Γ mfix mfix' idx :
    upto_names (tFixCoFix b mfix idx) (tFixCoFix b mfix' idx) ->
    guard b Σ Γ mfix ->
    guard b Σ Γ mfix' ;

  guard_extends b (Σ Σ':global_env_ext) Γ mfix :
    extends Σ Σ' ->
    guard b Σ Γ mfix ->
    guard b Σ' Γ mfix ;

  guard_context_cumulativity `{checker_flags} b Σ Γ Γ' mfix :
    All2_fold (cumul_decls cumulSpec0 Σ) Γ' Γ ->
    guard b Σ Γ mfix ->
    guard b Σ Γ' mfix ;

  guard_subst_instance `{checker_flags} b Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    guard b Σ Γ mfix ->
    guard b (Σ.1, univs) (subst_instance u Γ) (subst_instance_mfix mfix u) ;

  guard_inst `{checker_flags} b Σ Γ Δ mfix σ :
    Σ ;;; Γ ⊢ σ : Δ ->
    guard b Σ Δ mfix ->
    guard b Σ Γ (inst_mfix mfix σ) ;

  guard_rename `{checker_flags} b P Σ Γ Δ mfix f :
    urenaming P Γ Δ f ->
    guard b Σ Γ mfix ->
    guard b Σ Δ (rename_mfix mfix f) ;

}.

Axiom guard_checking_correct : GuardCheckerCorrect.
#[global] Existing Instance guard_checking_correct.

Definition fix_guard_red1 := guard_red1 Fix.
Definition fix_guard_eq_term := guard_eq_term Fix.
Definition fix_guard_subst_instance `{checker_flags} := guard_subst_instance Fix.
Definition fix_guard_extends := guard_extends Fix.
Definition fix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity Fix.
Definition fix_guard_inst `{checker_flags} := guard_inst Fix.
Definition fix_guard_rename `{checker_flags} := guard_rename Fix.

Definition cofix_guard_red1 := guard_red1 CoFix.
Definition cofix_guard_eq_term := guard_eq_term CoFix.
Definition cofix_guard_subst_instance `{checker_flags} := guard_subst_instance CoFix.
Definition cofix_guard_extends := guard_extends CoFix.
Definition cofix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity CoFix.
Definition cofix_guard_inst `{checker_flags} := guard_inst CoFix.
Definition cofix_guard_rename `{checker_flags} := guard_rename CoFix.
