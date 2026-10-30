From Stdlib Require Import List.
From Stdlib Require Import String.
From MetaRocq.Erasure.Typed Require Import Transform.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Erasure.Typed Require Import Certifying.
From MetaRocq.Template Require Import All.
From MetaRocq.Common Require Import Kernames.

Import MonadNotation.

Section betared.
  Context (Σ : global_env).

  Fixpoint decompose_lam (t : term) {struct t} :
  (list aname × list term) × term :=
    match t with
    | tLambda na A B =>
      let (nAs, B0) := decompose_lam B in
      let (ns, As) := nAs in (na :: ns, A :: As, B0)
    | _ => ([], [], t)
    end.

  Fixpoint betared_aux (args : list term) (t : term) : term :=
      match t with
      | tApp hd args0 => betared_aux (map (betared_aux []) args0 ++ args) hd
      | tCast t0 _ _ => betared_aux args t0
      | tLambda na ty body =>
        let b := betared_aux [] body in
        beta_body (tLambda na ty b) args
      | t => mkApps (map_subterms (betared_aux []) t) args
      end.

  Definition betared : term -> term := betared_aux [].

  Definition betared_in_constant_body cst :=
    {| cst_type := cst_type cst;
       cst_universes := cst_universes cst;
       cst_body := option_map betared (cst_body cst);
       cst_relevance := cst.(cst_relevance) |}.

  Definition betared_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (betared_in_constant_body cst)
    | _ => d
    end.

End betared.

Definition betared_globals (Σ : global_declarations) : global_declarations :=
  fold_right (fun '(kn, decl) decls => (kn, betared_in_decl decl) :: decls) [] Σ.

Definition betared_globals_template
           (mpath : modpath)
           (Σ : global_declarations)
           (seeds : KernameSet.t)
  : TemplateMonad global_declarations :=
  let suffix := "_after_betared" in
  Σbeta <- tmEval lazy (betared_globals Σ);;
  gen_defs_and_proofs Σ Σbeta mpath suffix seeds;;
  ret Σbeta.

(** Mainly for testing purposes *)
(* Needs to set universe to Set otherwise make vos without Universe Checking fails *)
Definition extract_def_name {A : Type} (a : A) : TemplateMonad@{_ Set} KernameSet.elt :=
  extract_def_name a.

Definition betared_def {A}
           (def : A) : TemplateMonad global_declarations :=
  mpath <- tmCurrentModPath tt;;
  p <- tmQuoteRecTransp def false ;;
  kn <- (extract_def_name def : TemplateMonad KernameSet.elt) ;;
  betared_globals_template mpath (declarations p.1) (KernameSet.singleton kn).

Definition template_betared : TemplateTransform :=
  fun Σ => Ok (timed "Inlining" (fun _ => mk_global_env (universes Σ) (betared_globals (declarations Σ)) (retroknowledge Σ))).
(*
Module Ex1.

  Definition foo (n : nat) := (fun x => x) n.

  MetaRocq Run (betared_def foo).

  (* FIXME: it's a bit fragile to refer to unquoted definitions, because their names depend on a module/path they are in *)
  MetaRocq Quote Recursively Definition foo_after :=
    MetaRocq_Erasure_Typed_CertifyingBeta_Ex1_foo_after_betared.

  MetaRocq Quote Recursively Definition foo_before := foo.

  Lemma after_not_before :
    lookup_env foo_after.1 <%% MetaRocq_Erasure_Typed_CertifyingBeta_Ex1_foo_after_betared %%> =
    lookup_env foo_before.1 <%% foo %%> -> False.
  Proof. easy. Qed.
End Ex1.
*)
