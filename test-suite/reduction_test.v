From Stdlib Require Import Recdef.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Template Require Import TemplateMonad Loader.
(* From MetaRocq.SafeChecker Require Import SafeTemplateChecker. *)
From MetaRocq.PCUIC Require Import PCUICEquality PCUICAst PCUICReflect PCUICSafeLemmata PCUICTyping PCUICNormal PCUICAstUtils PCUICSN.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC PCUICToTemplate.
From Stdlib Require Import String.
Local Open Scope string_scope.

From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Common Require Import config.

Import MRMonadNotation.
Unset MetaRocq Debug.
(* We're doing erasure assuming no Prop <= Type rule and lets can appear in constructor types. *)
#[local] Existing Instance extraction_checker_flags.

From MetaRocq.TestSuite Require hott_example.

(* MetaRocq Quote Recursively Definition qequiv_adjointify := @isequiv_adjointify. *)

From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfReduction PCUICErrors PCUICSafeReduce PCUICTypeChecker PCUICSafeChecker PCUICWfEnv PCUICWfEnvImpl PCUICSafeConversion.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateChecker.

#[local,program] Instance fake_abstract_guard_impl : PCUICWfEnvImpl.abstract_guard_impl :=
  {
    guard_impl := PCUICWfEnvImpl.fake_guard_impl
  }.
Next Obligation. todo "this axiom is inconsitent, only used to make infer compute". Qed.
#[local,program] Instance assume_normalization {nor} : @PCUICSN.Normalization default_checker_flags nor.
Next Obligation. todo "we should write a Template Monad program to prove normalization for the particular program being inferred, rather than axiomatizing it". Qed.
#[local] Existing Instance PCUICSN.normalization.

Definition typecheck_template (cf := default_checker_flags)
  {nor : normalizing_flags} (p : Ast.Env.program)
   :=
  let p' := trans_program p in
    match
      infer_template_program (cf:=cf) p Monomorphic_ctx
    with CorrectDecl X =>
      X.π1
      (* PCUICPretty.print_env true 10 X.π2.π1.(wf_env_ext_reference).(reference_impl_env_ext) *)
    | _ => todo "should not happen"
  end.

Definition aa := Set.

Inductive Empty (A:Set) : Set := .

Definition dummy (n : nat) : nat := match n with 0 => 1 | S n => n end.

Set Primitive Projections.

MetaRocq Quote Recursively Definition foo :=
  @hott_example.isequiv_adjointify.
(* plus. *)
(* (fun n m => n + m). *)
(* (forall (n:nat), nat).  *)
(* (fix f (n : nat) : nat := 0). *)
(* (fun t:nat => fun u : unit => t = t). *)
(* (match 100 with 0 => 1 | S n => n end). *)
(* (fun t => match t with tt => 0 end). *)
(* (match todo "foo" with 0 => 1 | S n => n end). *)
(* Set.  *)
(* ((fun x => x + 1) 4). *)

Definition default_normal : @normalizing_flags default_checker_flags.
now econstructor.
Defined.
Unset MetaRocq Strict Unquote Universe Mode.

(* Time Definition bar := Eval lazy in @typecheck_template default_normal foo. *)

(* MetaRocq Unquote Definition unbar := (PCUICToTemplate.trans bar). *)

Program Definition eval_compute (cf := default_checker_flags)
(nor : normalizing_flags)
(p : Ast.Env.program) φ  : Ast.term + string
:= match infer_template_program (cf:=cf) p φ return Ast.term + string with
| CorrectDecl A =>
  let p' := trans_program (clean_program p) in
  let Σ' := TemplateToPCUIC.trans_global_env (clean_program p).1 in
  let redtm := reduce_term RedFlags.default
    optimized_abstract_env_impl (proj1_sig A.π2)
    [] p'.2 _ in
  inl (PCUICToTemplate.trans redtm)
| EnvError Σ (AlreadyDeclared id) =>
  inr ("Already declared: " ^ id)
| EnvError Σ (IllFormedDecl id e) =>
  inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
end.
Next Obligation.
  sq. destruct H0 as [? [? H0]]. pose (typing_wf_local H0).
  econstructor. rewrite <- e. eauto.
Qed.

Program Definition eval_compute_cheat (cf := default_checker_flags)
(nor : normalizing_flags)
(p : Ast.Env.program) φ  : Ast.term
:= let p' := trans_program (clean_program p) in
  let tm := reduce_term RedFlags.default
     canonical_abstract_env_impl
    {| reference_impl_env_ext := (p'.1 , φ);
       reference_impl_ext_wf := (todo "wf") |}
    [] p'.2 (todo "welltyped") in
    PCUICToTemplate.trans tm.

Time Definition bar'' := Eval lazy in eval_compute default_normal foo Monomorphic_ctx.
MetaRocq Unquote Definition bar''' := (match bar'' with inl x => x | inr  _ => todo "" end).
