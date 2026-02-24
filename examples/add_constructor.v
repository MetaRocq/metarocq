(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

Import MonadNotation.

(* **************************************************** *)
(* In this file we define a small plugin which allow to *)
(* add a constructor to an inductive without rewriting  *)
(* the whole inductive.                                 *)
(* **************************************************** *)


(** ** Auxiliary functions *)


Class TslIdent := { tsl_ident : ident -> ident }.

Local Instance prime_tsl_ident : TslIdent
  := {| tsl_ident := fun id => id ^ "'" |}.

Fixpoint try_remove_n_lambdas (n : nat) (t : term) {struct n} : term :=
  match n, t with
  | 0, _ => t
  | S n, tLambda _ _ t => try_remove_n_lambdas n t
  | S _, _ => t
  end.


(** * Plugin *)

(* [add_ctor] add a constructor to a [mutual_inductive_body]
 (that is a reified declaration of an inductive). *)

Definition tsl_constructor_body (c : constructor_body) : constructor_body :=
  {| cstr_name := tsl_ident c.(cstr_name);
     cstr_args := cstr_args c;
     cstr_indices := cstr_indices c;
     cstr_type := cstr_type c;
     cstr_arity := cstr_arity c |}.

Definition remove_last_n {A} (l : list A) (n : nat) : list A :=
  firstn (#|l| - n) l.

Definition new_cstr mdecl (idc : ident) (ctor : term) : constructor_body :=
  let '(args, concl) := decompose_prod_assum [] ctor in
  let (hd, indices) := decompose_app concl in
  {| cstr_name := idc;
    cstr_args := remove_last_n args #|mdecl.(ind_params)|;
    cstr_indices := skipn mdecl.(ind_npars) indices;
    cstr_type := ctor;
    cstr_arity := context_assumptions args |}.

Polymorphic Definition add_ctor (mind : mutual_inductive_body) (ind0 : inductive) (idc : ident) (ctor : term)
  : mutual_inductive_body
  := let i0 := inductive_ind ind0 in
     {| ind_finite := mind.(ind_finite);
        ind_npars := mind.(ind_npars) ;
        ind_universes := mind.(ind_universes) ;
        ind_variance := mind.(ind_variance);
        ind_params := mind.(ind_params);
        ind_bodies := mapi (fun (i : nat) (ind : one_inductive_body) =>
          {| ind_name := tsl_ident ind.(ind_name) ;
            ind_indices := ind.(ind_indices);
            ind_sort := ind.(ind_sort);
            ind_type  := ind.(ind_type) ;
            ind_kelim := ind.(ind_kelim) ;
            ind_ctors := let ctors := map tsl_constructor_body ind.(ind_ctors) in
                          if Nat.eqb i i0 then
                            let n := #|ind_bodies mind| in
                            let typ := try_remove_n_lambdas n ctor in
                            ctors ++ [new_cstr mind idc typ]
                          else ctors;
            ind_projs := ind.(ind_projs);
            ind_relevance := ind.(ind_relevance) |})
            mind.(ind_bodies) |}.


(* [add_constructor] is a new command (in Template Rocq style) *)
(* which do what we want *)

Polymorphic Definition add_constructor (tm : Ast.term)
            (idc : ident) (type : Ast.term)
  : TemplateMonad unit
  := match tm with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       let ind' := add_ctor decl ind0 idc type in
       tmMkInductive' ind'
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.


(** * Examples *)
Local Open Scope bs_scope.
(** Here we add a silly constructor to bool. *)
MetaRocq Run (
    add_constructor <% bool %> "foo" <% (fun x : Type => nat -> x -> bool -> x) %>).
(* Inductive bool' : Set := *)
(*     true' : bool' *)
(*   | false' : bool' *)
(*   | foo : nat -> bool' -> bool -> bool' *)
Definition test := bool'.
Definition test' : nat -> bool' -> bool -> bool' := foo.

(** Here is a useful usecase: add a case to a syntax. *)
Inductive tm :=
| var : nat -> tm
| lam : tm -> tm
| app : tm -> tm -> tm.

MetaRocq Run (add_constructor <%tm%> "letin" <% (fun tm' => tm' -> tm' -> tm') %>).

Definition test2 := letin.
(* Inductive tm' : Type := *)
(*     var' : nat -> tm' *)
(*   | lam' : tm' -> tm' *)
(*   | app' : tm' -> tm' -> tm' *)
(*   | letin : tm' -> tm' -> tm' *)


MetaRocq Run (add_constructor <%@eq%> "foo'"
                    <% (fun (eq':forall A, A -> A -> Type) => forall A x y, nat -> eq' A x x -> bool -> eq' A x y) %>).
Definition test3 := foo'.
MetaRocq Run (add_constructor <%@Nat.Odd_alt%> "foo''"
                    <%(fun (even' odd':nat -> Prop) => odd' 0)%>).
Definition test4 := foo''.
Module A.
MetaRocq Run (add_constructor <%@Nat.Even_alt%> "foo'"
                    <%(fun (even' odd':nat -> Prop) => even' 0)%>).
End A.
