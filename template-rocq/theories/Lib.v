(* Distributed under the terms of the MIT license. *)
From MetaRocq.Common Require Import uGraph.
From MetaRocq.Template Require Import Ast TemplateMonad Loader Checker.
From MetaRocq.Utils Require Import utils.

#[local] Set Universe Polymorphism.

(** * Commands. *)

(** Quote a term. *)
Notation "'$quote' x" :=
  ltac:((let p y := exact y in quote_term x p))
  (at level 0, only parsing).

(** Run a template program. *)
Notation "'$run' f" :=
  ltac:(
    let p y := exact y in
    run_template_program f p
  ) (at level 0, only parsing).

(** Quote and term and its environment. *)
Notation "'$quote_rec' x" :=
  ($run (tmQuoteRec x))
  (at level 0, only parsing).

(** Unquote a term (using [tmUnquote]). *)
Notation "'$unquote' x" :=
  ltac:(
    let p y :=
      match y with
      | existT_typed_term ?T ?b => exact b
      end
    in
    run_template_program (tmUnquote x) p
  ) (at level 0, only parsing).

(** Unquote a term (using [tmUnquoteTyped]). *)
Notation "'$unquote' x : T" :=
  ($run (tmUnquoteTyped T x))
  (at level 0, T at level 100, x at next level, only parsing).

(** [unfold_toplevel x] replaces the constant [x] by its definition.
    Fails if [x] is not a constant. *)
Definition unfold_toplevel {A} (x : A) : TemplateMonad A :=
  tmBind (tmQuote x) (fun y =>
    match y with
    | tConst na _ => tmEval (Common.unfold na) x
    | _ => tmFail "unfold_toplevel: not a constant"%bs
    end).

(** Quote the _definition_ of a constant. *)
Notation "'$quote_def' x" :=
  ($run (tmBind (unfold_toplevel x) tmQuote))
  (at level 0, only parsing).

(** [get_kername t] returns the kernel name of [t].
    Fails if [t] is not of the form [tConst _ _]. *)
Definition get_kername (t : term) : TemplateMonad kername :=
  match t with
  | tConst c u => tmReturn c
  | _ => tmFail "get_kername: not a constant"%bs
  end.

(** Get the kernel name of a constant. *)
Notation "'$name' x" :=
  ($run (get_kername ($quote x)))
  (at level 0, only parsing).

(** Recursively quote the _definition_ of a constant. *)
Notation "'$quote_def_rec' x" :=
  ($run (tmBind (unfold_toplevel x) tmQuoteRec))
  (at level 0, only parsing).

(** * Useful shortcuts. *)

(** [term_eqb t1 t2] checks if [t1] and [t2] are equal modulo alpha equivalence.
  No universe constraints are taken into account. *)
Definition term_eqb (t1 t2 : term) :=
  @eq_term config.default_checker_flags init_model t1 t2.

(** Short-form notation for [tLambda]. *)
Notation tLam x A b :=
  (tLambda {| binder_name := nNamed x; binder_relevance := Relevant |} A b).

(** Short-form notation for [tProd]. *)
Notation tPro x A b :=
  (tProd {| binder_name := nNamed x; binder_relevance := Relevant |} A b).

(** Short-form notation for [tLetIn]. *)
Notation tLet x A t b :=
  (tLetIn {| binder_name := nNamed x; binder_relevance := Relevant |} t A b).

Notation "'__'" := (hole) (no associativity, at level 0).

(** * Monadic notations. *)

(** These notations replace the default ones from Utils.monad_utils
    by equivalent ones which are specialized to the TemplateMonad.
    This helps avoid typeclass errors. *)
Module TemplateMonadNotations.

Declare Scope tm_scope.
Delimit Scope tm_scope with tm.

Notation "c >>= f" :=
  (tmBind c f)
  (at level 50, left associativity) : tm_scope.

Notation "f =<< c" :=
  (c >>= f)%tm
  (at level 51, right associativity) : tm_scope.

Notation "'mlet' x <- c1 ;; c2" :=
  (c1 >>= (fun x => c2))%tm
  (at level 100, c1 at next level, right associativity, x pattern) : tm_scope.

Notation "'mlet' ' pat <- c1 ;; c2" :=
  (c1 >>= (fun x => match x with pat => c2 end))%tm
  (at level 100, pat pattern, c1 at next level, right associativity) : tm_scope.

Notation "x <- c1 ;; c2" :=
  (c1 >>= (fun x => c2))%tm
  (at level 100, c1 at next level, right associativity) : tm_scope.

Notation "' pat <- c1 ;; c2" :=
  (c1 >>= (fun x => match x with pat => c2 end))%tm
  (at level 100, pat pattern, c1 at next level, right associativity) : tm_scope.

Notation "e1 ;; e2" :=
  (_ <- e1%tm ;; e2%tm)%tm
  (at level 100, right associativity) : tm_scope.

End TemplateMonadNotations.

(** * Packed inductives and constructors. *)

(** In MetaRocq.Template the information related to an inductive type is spread accross
    three different datatypes : [inductive], [one_inductive_body] and [mutual_inductive_body].
    One often needs access to all three : [packed_inductive] packages them in a single datatype. *)
Record packed_inductive :=
  { pi_ind : inductive
  ; pi_body : one_inductive_body
  ; pi_mbody : mutual_inductive_body }.

(** Same as [packed_inductive] but for constructors. *)
Record packed_constructor :=
  { (** The inductive this constructor belongs to. *)
    pc_pi : packed_inductive
  ; (** The index of this constructor. *)
    pc_idx : nat
  ; (** The body of this constructor. *)
    pc_body : constructor_body }.

(** [pi_ctors pi] returns the list of [packed_constructors] of the
    packed inductive [pi]. *)
Definition pi_ctors (pi : packed_inductive) : list packed_constructor :=
  mapi (fun i ctor => {| pc_pi := pi ; pc_idx := i ; pc_body := ctor |}) pi.(pi_body).(ind_ctors).

(** [pi_block pi] returns the list of packed inductives in the same block
    as [pi], including [pi] itself, ordered from first to last. *)
Definition pi_block (pi : packed_inductive) : list packed_inductive :=
  mapi
    (fun i body =>
      {| pi_ind := {| inductive_mind := pi.(pi_ind).(inductive_mind) ; inductive_ind := i |}
      ;  pi_body := body
      ;  pi_mbody := pi.(pi_mbody) |})
    pi.(pi_mbody).(ind_bodies).