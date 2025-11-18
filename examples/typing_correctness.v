(*From MetaRocq.Template Require Import config All.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICLiftSubst TemplateToPCUIC.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl PCUICTypeChecker PCUICSafeChecker.
From Equations Require Import Equations.




Polymorphic Inductive list@{u} (A : Type@{u}) : Type@{u} :=
(* | nil : list A *)
(* | cons : A -> list A -> list A *)
.

Polymorphic Inductive rtree@{u} : Type@{u} :=
| node : list rtree -> rtree.

Universe u.

Polymorphic Inductive empty@{u} : Type@{u} :=.

Polymorphic Inductive unit@{u} : Type@{u} := tt.

MetaRocq Quote Recursively Definition empty_sig_full_template := (fun (A : Type@{u}) (x : A) => x).
Definition empty_sig_full := trans_template_program empty_sig_full_template.

MetaRocq Quote Recursively Definition empty_full_template := empty@{u}.
Definition empty_full := trans_template_program empty_full_template.

MetaRocq Quote Recursively Definition unit_full_template := tt@{u}.
Definition unit_full := trans_template_program unit_full_template.

MetaRocq Quote Recursively Definition list_full_template := list@{u}.
Definition list_full := trans_template_program list_full_template.

MetaRocq Quote Recursively Definition rtree_full_template := rtree@{u}.
Definition rtree_full := trans_template_program rtree_full_template.

Definition extract_gctx : PCUICProgram.pcuic_program -> global_env_ext :=
  fun p => (p.1.1.(PCUICProgram.trans_env_env), p.1.2).

Definition gctx := Eval cbv in extract_gctx empty_full. (* Change here *)

Global Program Instance fake_guard_impl : abstract_guard_impl :=
{| guard_impl := fake_guard_impl |}.
Next Obligation. Admitted.

Local Existing Instance PCUICSN.default_normalizing.
Import MRMonadNotation.

Definition make_wf_env_ext (Σ : global_env_ext) : EnvCheck wf_env_ext wf_env_ext :=
  '(exist Σ' pf) <- check_wf_ext optimized_abstract_env_impl Σ ;;
  ret Σ'.

Local Existing Instance default_checker_flags.

Definition gctx_wf_env : wf_env_ext.
Proof.
  let wf_proof := eval hnf in (make_wf_env_ext gctx) in
  match wf_proof with
  | CorrectDecl _ ?x => exact x
  | ?z => set (error := z)
   (* idtac z ; fail "Couldn't prove the global environment is well-formed" *)
  end.
Defined.
*)
(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes.
From MetaRocq.Template Require Import Loader.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICLiftSubst.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl PCUICTypeChecker PCUICSafeChecker.
From Equations Require Import Equations.

Local Existing Instance default_checker_flags.
Local Existing Instance PCUICSN.default_normalizing.
Local Existing Instance PCUICSN.normalization.
Import MRMonadNotation.

(* ********************************************************* *)
(* In this file we define a small plugin which proves        *)
(* the identity theorem for any sort using the safe checker. *)
(* ********************************************************* *)

Definition bAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition bNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Definition tImpl X Y := tProd bAnon X (lift0 1 Y).

Definition univ := Level.level "s".

(* TODO move to SafeChecker *)

Definition gctx : global_env_ext :=
  ({| universes := (LevelSet.singleton univ, UnivConstraintSet.empty); declarations := []
    ; retroknowledge := Retroknowledge.empty |}, Monomorphic_ctx).

(** We use the environment checker to produce the proof that gctx, which is a singleton with only
    universe "s" declared  is well-formed. *)

Definition kername_of_string (s : string) : kername :=
  (MPfile [], s).

Global Program Instance fake_guard_impl : abstract_guard_impl :=
{| guard_impl := fake_guard_impl |}.
Next Obligation. Admitted.
Global Instance assume_normalization : PCUICSN.Normalization.
Admitted.

Definition make_wf_env_ext (Σ : global_env_ext) : EnvCheck wf_env_ext wf_env_ext :=
  '(exist Σ' pf) <- check_wf_ext optimized_abstract_env_impl Σ ;;
  ret Σ'.

Definition gctx_wf_env : wf_env_ext.
Proof.
  let wf_proof := eval hnf in (make_wf_env_ext gctx) in
  match wf_proof with
  | CorrectDecl _ ?x => exact x
  | _ => fail "Couldn't prove the global environment is well-formed"
  end.
Defined.



(** There is always a proof of `forall x : Sort s, x -> x` *)

Definition inh {cf:checker_flags} (Σ : wf_env_ext) Γ T := ∑ t, forall Σ0 : global_env_ext, abstract_env_ext_rel Σ Σ0 -> ∥ typing Σ0 Γ t T ∥.

Definition check_inh (Σ : wf_env_ext) Γ (wfΓ : forall Σ0 : global_env_ext, abstract_env_ext_rel Σ Σ0 -> ∥ wf_local Σ0 Γ ∥) t {T} : typing_result (inh Σ Γ T) :=
  prf <- check_type_wf_env_fast optimized_abstract_env_impl Σ Γ wfΓ t (T := T) ;;
  ret (t; prf).

Ltac fill_inh t :=
  lazymatch goal with
  [ wfΓ : forall _ _, ∥ wf_local _ ?Γ ∥ |- inh ?Σ ?Γ ?T ] =>
    let t := uconstr:(check_inh Σ Γ wfΓ t (T:=T)) in
    let proof := eval cbn in t in
    match proof with
    | Checked ?d => exact_no_check d
    | TypeError ?e =>
        let str := eval cbn in (string_of_type_error Σ e) in
        fail "Failed to inhabit " T " : " str
    | _ => set (blocked := proof)
    (* fail "Anomaly: unexpected return value: " proof *)
    end
  | [ |- inh _ ?Γ _ ] => fail "Missing local wellformedness assumption for" Γ
  end.

(* Lemma identity_typing (s := sType (Universe.of_level univ)): inh gctx_wf_env [] (tImpl (tSort s) (tSort s)).
Proof.
  set (impl := tLambda (bNamed "s") (tSort s) (tRel 0)).
  assert (wfΓ : forall Σ0 : global_env_ext,
  abstract_env_ext_rel gctx_wf_env Σ0 -> ∥ wf_local Σ0 [] ∥) by do 2 constructor.

  Time fill_inh impl.

Time Qed. *)


Lemma identity_typing (s := sType (Universe.of_level univ)):
     (∑ t : term,
        forall Σ0 : global_env_ext,
        Σ0 = gctx_wf_env ->
        ∥ Σ0;;; [] |- t
          : tProd (bNamed "s") (tSort s) (tImpl (tRel 0) (tRel 0)) ∥).
(* inh gctx_wf_env [] (tProd (bNamed "s") (tSort u) (tImpl (tRel 0) (tRel 0))). *)
Proof.
  set (impl := tLambda (bNamed "s") (tSort s) (tLambda bAnon (tRel 0) (tRel 0))).
  assert (wfΓ : forall Σ0 : global_env_ext,
  abstract_env_ext_rel gctx_wf_env Σ0 -> ∥ wf_local Σ0 [] ∥) by do 2 constructor.
  pose (T := tProd (bNamed "s") (tSort s) (tImpl (tRel 0) (tRel 0))).
  pose (Σ := gctx_wf_env).
  let t := uconstr:(check_inh Σ [] wfΓ impl (T:=T)) in
  let proof := eval hnf in t in
  match proof with
  | Checked ?d => exact_no_check d
  | TypeError ?e =>
      let str := eval cbn in (string_of_type_error Σ e) in
      fail "Failed to inhabit " T " : " str
  | _ => set (blocked := proof)
  (* fail "Anomaly: unexpected return value: " proof *)
  end.
Defined.

(* Print Opaque Dependencies identity_typing. *)
