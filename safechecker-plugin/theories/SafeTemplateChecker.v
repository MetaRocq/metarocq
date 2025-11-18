(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import AstUtils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
    PCUICSN BDToPCUIC PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICSafeChecker PCUICWfEnv PCUICWfEnvImpl.

Import MRMonadNotation.

From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.

Definition trans_program (p : Ast.Env.program) : program :=
  let Σ' := trans_global_env p.1 in
  (Σ', trans Σ' p.2).

Definition EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} := EnvCheck wf_env_ext.

Local Instance Monad_EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} : Monad EnvCheck_wf_env_ext := _.

Definition clean_global_env (p : Ast.Env.global_env) : Ast.Env.global_env :=
  {| Ast.Env.universes := PCUICGlobalEnv.clean_uctx p.(Ast.Env.universes);
     Ast.Env.retroknowledge := p.(Ast.Env.retroknowledge);
     Ast.Env.declarations := p.(Ast.Env.declarations)
    |}.

Definition clean_program (p : Ast.Env.program) : Ast.Env.program :=
  (clean_global_env p.1, p.2).

Program Definition infer_template_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  (p : Ast.Env.program) φ
  (* this is the hypothesis we need, idk how to simplify it or appropriately generalize it, maybe use check_wf_env_ext_prop to simplify Σ0 ∼_ext X' into _ ∼ X so that we get an equality? *)
  {normalization_in
    : forall (g : global_decl) (Hdecls' : nat) (X : X_env_type optimized_abstract_env_impl),
      (forall Σ0 : global_env,
          Σ0 ∼ X ->
          Σ0 =
            {|
              universes := (trans_program (clean_program p)).1;
              declarations := skipn Hdecls' (declarations (trans_program (clean_program p)).1);
              retroknowledge := retroknowledge (trans_program (clean_program p)).1
            |}) ->
      forall X' : X_env_ext_type optimized_abstract_env_impl,
        check_wf_env_ext_prop optimized_abstract_env_impl X X' (universes_decl_of_decl g) ->
        forall Σ0 : global_env_ext, wf_ext Σ0 -> Σ0 ∼_ext X' -> NormalizationIn Σ0}
  {normalization_in'
    : forall x : X_env_ext_type optimized_abstract_env_impl,
      ((trans_program (clean_program p)).1, φ) ∼_ext x ->
      forall Σ : global_env_ext, wf_ext Σ -> Σ ∼_ext x -> NormalizationIn Σ}
  : EnvCheck_wf_env_ext (let p' := trans_program (clean_program p) in ∑ A, { X : wf_env_ext |
    ∥ (p'.1, φ) = X.(wf_env_ext_reference).(reference_impl_env_ext) × wf_ext (p'.1, φ) ×  (p'.1, φ) ;;; [] |- p'.2 : A ∥ }) :=
  pp <- typecheck_program (cf := cf) (nor:=nor) optimized_abstract_env_impl (trans_program (clean_program p)) φ ;;
  ret (pp.π1 ; (exist (proj1_sig pp.π2) _)).
Next Obligation.
  sq. destruct H; split; eauto. destruct p0; split; eauto.  eapply infering_typing; tea. eapply w. constructor.
Qed.

Program Definition infer_and_print_template_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  (p : Ast.Env.program) φ
(* this is the hypothesis we need, idk how to simplify it or appropriately generalize it, maybe use check_wf_env_ext_prop to simplify Σ0 ∼_ext X' into _ ∼ X so that we get an equality? *)
  {normalization_in
    : forall (g : global_decl) (Hdecls' : nat) (X : X_env_type optimized_abstract_env_impl),
      (forall Σ0 : global_env,
          Σ0 ∼ X ->
          Σ0 =
            {|
              universes := (trans_program (clean_program p)).1;
              declarations := skipn Hdecls' (declarations (trans_program (clean_program p)).1);
              retroknowledge := retroknowledge (trans_program (clean_program p)).1
            |}) ->
      forall X' : X_env_ext_type optimized_abstract_env_impl,
        check_wf_env_ext_prop optimized_abstract_env_impl X X' (universes_decl_of_decl g) ->
        forall Σ0 : global_env_ext, wf_ext Σ0 -> Σ0 ∼_ext X' -> NormalizationIn Σ0}
  {normalization_in'
    : forall x : X_env_ext_type optimized_abstract_env_impl,
      ((trans_program (clean_program p)).1, φ) ∼_ext x ->
      forall Σ : global_env_ext, wf_ext Σ -> Σ ∼_ext x -> NormalizationIn Σ}  : string + string :=
  match infer_template_program (cf:=cf) p φ return string + string with
  | CorrectDecl t =>
    let Σ' := trans_global_env p.1 in
    inl ("Environment is well-formed and " ^ string_of_term (trans Σ' p.2) ^
         " has type: " ^ string_of_term t.π1)
  | EnvError Σ (AlreadyDeclared id) =>
    inr ("Already declared: " ^ id)
  | EnvError Σ (IllFormedDecl id e) =>
    inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
  end.

(* Program Definition check_template_program {cf : checker_flags} (p : Ast.Env.program) (ty : Ast.Env.term) *)
(*   : EnvCheck (∥ trans_global (AstUtils.empty_ext (List.rev p.1)) ;;; [] |- trans p.2 : trans ty ∥) := *)
(*   p <- typecheck_program (cf:=cf) ((trans_global (AstUtils.empty_ext p.1)).1, trans p.2) ;; *)
(*   wrap_error "During checking of type constraints" (check p.1 _ _ _ (trans ty));; *)
(*   ret (Monad:=envcheck_monad) _. *)

(* Next Obligation. *)
(*   unfold trans_global. *)
(*   simpl. unfold empty_ext in X. *)
(*   unfold trans_global_decls in X. *)
(*   rewrite <-map_rev in X. *)
(* Qed. *)

(* Program Definition typecheck_template_program' {cf : checker_flags} (p : Ast.Env.program) *)
(*   : EnvCheck (∑ A, ∥ Typing.typing (AstUtils.empty_ext (List.rev p.1)) [] p.2 A ∥) := *)
(*   p <- typecheck_template_program (cf:=cf) p ;; *)
(*   ret (Monad:=envcheck_monad) (p.π1 ; _). *)
