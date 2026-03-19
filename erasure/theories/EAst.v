(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Universes.
From MetaRocq.Erasure Require Import EPrimitive.
(** * Extracted terms

  These are the terms produced by extraction: compared to kernel terms,
  all proofs and types are translated to [tBox] or erased (type annotations
  at lambda and let-ins, types of fix/cofixpoints), applications
  are in binary form and casts are removed.  *)

Declare Scope erasure.
Local Open Scope erasure.

Record def (term : Set) := { dname : name; dbody : term; rarg : nat }.
Derive NoConfusion for def.
Arguments dname {term} d.
Arguments dbody {term} d.
Arguments rarg {term} d.

Definition map_def {term : Set} (f : term -> term) (d : def term) :=
  {| dname := d.(dname); dbody := f d.(dbody); rarg := d.(rarg) |}.

Definition test_def {term : Set} (f : term -> bool) (d : def term) :=
  f d.(dbody).

Definition mfixpoint (term : Set) := list (def term).

Inductive term : Set :=
| tBox (* Represents all proofs *)
| tRel (n : nat)
| tVar (i : ident) (* For free variables (e.g. in a goal) *)
| tEvar (n : nat) (l : list term)
| tLambda (na : name) (t : term)
| tLetIn (na : name) (b t : term) (* let na := b : B in t *)
| tApp (u v : term)
| tConst (k : kername)
| tConstruct (ind : inductive) (n : nat) (args : list term)
| tCase (indn : inductive * nat (* # of parameters *)) (c : term  (* discriminee *)) (brs : list (list name * term) (* branches *))
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term)
| tLazy (t : term)
| tForce (t : term).

Derive NoConfusion for term.

Bind Scope erasure with term.

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | a :: args => mkApps (tApp t a) args
  end.

Definition mkApp t u := Eval cbn in mkApps t [u].

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ => true
  | _ => false
  end.

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := { (* parameter_entry_type : term *) }.

Record definition_entry := {
  (* definition_entry_type      : term; *)
  definition_entry_body      : term;
  definition_entry_opaque    : bool }.


Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

(** *** Inductive entries *)

(** This is the representation of mutual inductives.
    nearly copied from [kernel/entries.mli]

  Assume the following definition in concrete syntax:

[[
  Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
  ...
  with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1  ... | cpnp : Tpnp.
]]

  then, in [i]th block, [mind_entry_params] is [xn:Xn;...;x1:X1];
  [mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
  [mind_entry_lc] is [Ti1;...;Tini], defined in context
  [A'1;...;A'p;x1:X1;...;xn:Xn] where [A'i] is [Ai] generalized over
  [x1:X1;...;xn:Xn].
*)

Inductive local_entry : Set :=
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.

Record one_inductive_entry : Set := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term (* constructor list *) }.

Record mutual_inductive_entry := {
  mind_entry_record    : option (option ident);
  (* Is this mutual inductive defined as a record?
     If so, is it primitive, using binder name [ident]
     for the record in primitive projections ? *)
  mind_entry_finite    : recursivity_kind;
  mind_entry_params    : list (ident * local_entry);
  mind_entry_inds      : list one_inductive_entry;
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by Template Rocq yet. *) }.



(** ** Declarations *)

(** *** The context of De Bruijn indices *)

Record context_decl := {
  decl_name : name ;
  decl_body : option term }.

(** Local (de Bruijn) variable binding *)

Definition vass x := {| decl_name := x; decl_body := None |}.

(** Local (de Bruijn) let-binding *)

Definition vdef x t := {| decl_name := x; decl_body := Some t |}.

(** Local (de Bruijn) context *)

Definition context := list context_decl.

Bind Scope erasure with context.

(** Mapping over a declaration and context. *)

Definition map_decl f (d : context_decl) :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body) |}.

Definition map_context f c :=
  List.map (map_decl f) c.

(** Last declaration first *)

Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level) : erasure.

(** *** Environments *)

Record constructor_body :=
  mkConstructor {
    cstr_name : ident;
    cstr_nargs : nat (* arity, w/o lets, w/o parameters *)
  }.
Derive NoConfusion for constructor_body.

Record projection_body :=
  mkProjection {
    proj_name : ident;
  }.
Derive NoConfusion for projection_body.

(** See [one_inductive_body] from [declarations.ml]. *)
Record one_inductive_body : Set := {
  ind_name : ident;
  ind_propositional : bool; (* True iff the inductive lives in Prop *)
  ind_kelim : allowed_eliminations; (* Allowed eliminations *)
  ind_ctors : list constructor_body;
  ind_projs : list projection_body (* names of projections, if any. *) }.
Derive NoConfusion for one_inductive_body.

(** See [mutual_inductive_body] from [declarations.ml]. *)
Record mutual_inductive_body := {
  ind_finite : recursivity_kind;
  ind_npars : nat;
  ind_bodies : list one_inductive_body }.
Derive NoConfusion for mutual_inductive_body.

Definition cstr_arity (mdecl : mutual_inductive_body) (cdecl : constructor_body) :=
  (mdecl.(ind_npars) + cdecl.(cstr_nargs))%nat.

(** See [constant_body] from [declarations.ml] *)
Record constant_body := { cst_body : option term }.

Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : mutual_inductive_body -> global_decl.
Derive NoConfusion for global_decl.


(** A context of global declarations *)

Definition global_declarations := list (kername * global_decl).

Abbreviation global_context := global_declarations.

(** *** Programs

  A set of declarations and a term, as produced by extraction from
  template-rocq programs. *)

Definition program : Type := global_declarations * term.
