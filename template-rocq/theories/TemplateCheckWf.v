From Stdlib Require Import List.
From MetaRocq.Common Require Import config Transform.
From MetaRocq.Template Require Import TemplateProgram Pretty EtaExpand All Loader.
Import ListNotations.
Import MonadNotation.
Import bytestring.
Open Scope bs_scope.

#[local] Existing Instance config.default_checker_flags.

Definition eta_expand p :=
  EtaExpand.eta_expand_program p.

Definition check_def (d : kername × global_decl) : TemplateMonad unit :=
  match d.2 with
  | ConstantDecl cb =>
    match cb.(cst_body) with
    | Some body =>
      tmMsg ("Unquoting eta-expanded " ++ string_of_kername d.1)%bs ;;
      tmUnquote body ;;
      tmMsg ("Succeeded")
    | None => ret tt
    end
  | InductiveDecl idecl => ret tt
  end.

Definition is_nil {A} (l : list A) :=
  match l with
  | [] => true
  | _ :: _ => false
  end.

Fixpoint wfterm (t : term) : bool :=
  match t with
  | tRel i => true
  | tEvar ev args => List.forallb (wfterm) args
  | tLambda _ T M | tProd _ T M => wfterm T && wfterm M
  | tApp u v => wfterm u && List.forallb (wfterm) v && negb (isApp u) && negb (is_nil v)
  | tCast c kind t => wfterm c && wfterm t
  | tLetIn na b t b' => wfterm b && wfterm t && wfterm b'
  | tCase ind p c brs =>
    let p' := test_predicate (fun _ => true) (wfterm) (wfterm) p in
    let brs' := forallb (wfterm ∘ bbody) brs in
    p' && wfterm c && brs'
  | tProj p c => wfterm c
  | tFix mfix idx =>
    List.forallb (test_def wfterm wfterm) mfix
  | tCoFix mfix idx =>
    List.forallb (test_def wfterm wfterm) mfix
  | _ => true
  end.

From Stdlib Require Import ssrbool.

Definition wf_global_decl d :=
  match d with
  | ConstantDecl cb => wfterm cb.(cst_type) && option_default wfterm cb.(cst_body) true
  | InductiveDecl idecl => true
  end.
Definition wf_global_declarations : global_declarations -> bool := forallb (wf_global_decl ∘ snd).
Definition wf_global_env (g : global_env) := wf_global_declarations g.(declarations).
Definition wf_program p := wf_global_env p.1 && wfterm p.2.

Definition check_wf (g : Ast.Env.program) : TemplateMonad unit :=
  monad_map check_def g.1.(declarations) ;;
  tmMsg "Wellformed global environment" ;; ret tt.

Axiom assume_wt_template_program : forall p : Ast.Env.program, ∥ wt_template_program p ∥.

Definition check_wf_eta (p : Ast.Env.program) : TemplateMonad unit :=
  monad_map check_def (eta_expand (make_template_program_env p (assume_wt_template_program p))).1.(declarations) ;;
  tmMsg "Wellformed eta-expanded global environment" ;; ret tt.

(* To test that a program's eta-expansion is indeed well-typed according to Rocq's kernel use:

  MetaRocq Run (tmQuoteRec wf_program >>= check_wf_eta). *)
