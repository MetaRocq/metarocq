From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import Loader.
From MetaRocq.Template Require Import TemplateMonad.
From MetaRocq.PCUIC Require Import PCUICAst PCUICReduction PCUICCumulativity PCUICTyping PCUICSafeLemmata.

Import MRMonadNotation.
Local Open Scope bs_scope.

(** MetaRocq is:

  - The "template-rocq" monad, dealing with reification of terms
    and environments.
  - The PCUIC development of the syntactic metatheory of Rocq.
  - The SafeChecker package implementing reduction, conversion
    and typechecking in a sound and complete way.
  - The Erasure package implementing verified extraction to
    untyped lambda-calculus
*)

(* The Template monad *)

Print Ast.term.


MetaRocq Quote Definition reifx := (fun x : nat => x).
Definition foo := (fun x : nat => fun x : nat => x).
MetaRocq Quote Definition reifx' := Eval compute in (fun x : nat => let y := x in fun x : nat => y).
Print reifx'.
MetaRocq Unquote Definition x :=
  (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Corelib"], "nat") 0) 0 []).

MetaRocq Run (tmBind (tmQuote (3 + 3)) tmPrint).

MetaRocq Run (t <- tmLemma "foo44" nat ;;
             qt <- tmQuote t ;;
             t <- tmEval all t ;;
             tmPrint qt ;; tmPrint t).
Next Obligation.
  exact (3+2).
Defined.

(* PCUIC:

    + Universes (with full algebraic universes supported everywhere)
    + Universe polymorphism
    + Standard type theory with dependent products and let-ins
    + Inductive types and coinductive types
    + Constant and axiom declarations in a global environment *)

Print typing.

Check type_Sort.
Check type_LetIn.
Check type_Const.

From MetaRocq.PCUIC Require PCUICSR.

Check PCUICSR.subject_reduction.

(** Verified conversion and type-checking *)

From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl PCUICTypeChecker PCUICSafeChecker PCUICSafeRetyping.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
Check PCUICSafeConversion.isconv_term_sound.
Check PCUICSafeConversion.isconv_term_complete.

Check PCUICSafeChecker.infer_wf_env.
(** Proof of completeness is near completion. *)

(** Verified retyping: from a term that is known to be well-typeable,
  compute its principal type. Very common in tactics to avoid retypechecking
  the whole term. *)
Check type_of.
Check type_of_subtype.

(* Running the safe checker inside Rocq *)
From MetaRocq.Examples Require Import metarocq_tour_prelude.

Check check_inh.

Ltac set_head_match c :=
  let c := eval cbn delta [c] in c in
  match c with
    | match ?d with _ => _ end =>
      set_head_match d || (let head := fresh in set (head := d))
  end.

Arguments infer_type {cf nor X_type X normalization_in infer}.
About Checked_comp.

(** We construct a proof of typing entirely within Rocq, calling the typechecker to produce the derivation *)
Lemma identity_typing (u := Universe.of_level univ):
  inh gctx_wf_env [] (tProd (bNamed "s") (tSort (sType u)) (tImpl (tRel 0) (tRel 0))).
Proof.
  (* We construct a term *)
  set (impl := tLambda (bNamed "s") (tSort (sType u)) (tLambda bAnon (tRel 0) (tRel 0))).
  (* Show that the empty context is well-formed  *)
  assert (wfΓ : forall Σ0 : global_env_ext, abstract_env_ext_rel gctx_wf_env Σ0 -> ∥ wf_local Σ0 [] ∥) by do 2 constructor.
  (** And build the typing derivation reflexively using the type checker *)
  fill_inh impl.
Qed.

(** The extracted typechecker also runs in OCaml *)
MetaRocq SafeCheck (fun x : nat => x + 1).
MetaRocq SafeCheck (forall x : Set, x -> x).

(** Erasure *)
From MetaRocq.ErasurePlugin Require Import Erasure Loader.

(** Running erasure live in Rocq *)
Definition test (p : Ast.Env.program) : string :=
  erase_and_print_template_program default_erasure_config [] p.

MetaRocq Quote Recursively Definition zero := 0.

Definition zerocst := Eval lazy in test zero.

Definition singleton_elim :=
  ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

MetaRocq Run (tmEval lazy singleton_elim >>= tmQuoteRec >>=
  fun p => tmEval lazy (test p) >>= tmPrint). (* Optimized to remove match on Props *)

MetaRocq Erase singleton_elim.

(** Conclusion: Status of MetaRocq

  - Correctness and complete typechecker for (a large fragment of) Rocq.

  - All metatheory proofs are finished. Compared to Rocq's implementation:

    - full (max (i + k, j + l)) universe support including an efficient loop checker.

    - partial support for SProp (in programs but not yet formalized typing rules)

    - approximate cumulative inductive types checking (not yet up to reduction)

    - missing eta-conversion: the plan is to use contravariant subtyping and eta-reduction,
      as in Rocq CEP #47

    - missing template-polymorphism: we're studying a sort polymorphism extension
      (with G. Gilbert, K. Maillard and N. Tabareau) to subsume it completely.

    - missing modules and fast conversion machines.

  - Much work to come on the template-rocq side to ease meta-programming.

  - Relation to CertiRocq: fast and verified correct erasure, not depending on type-checking
    (only retyping).

    + Eta-expansion and let-expansion proofs are part of MetaRocq

    + Future work: handling of primitive types (ints, floats, arrays, ...)
    at the level of the specification

*)



