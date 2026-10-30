From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Export EAst.
From MetaRocq.Erasure Require EPretty.

Import ListNotations.

Inductive box_type :=
| TBox
| TAny
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TVar (_ : nat) (* Level of type variable *)
| TInd (_ : inductive)
| TConst (_ : kername).

Fixpoint decompose_arr (bt : box_type) : list box_type * box_type :=
  match bt with
  | TArr dom cod => let (args, res) := decompose_arr cod in
                    (dom :: args, res)
  | _ => ([], bt)
  end.

Definition can_have_args (bt : box_type) : bool :=
  match bt with
  | TInd _
  | TConst _ => true
  | _ => false
  end.

Fixpoint mkTApps (hd : box_type) (args : list box_type) : box_type :=
  match args with
  | [] => hd
  | a :: args => mkTApps (TApp hd a) args
  end.

Record constant_body :=
  { cst_type : list name * box_type;
    cst_body : option term; }.

(** The arity of an inductive and type alias is an iterated product that we will
    decompose into type vars. Each type var has information about its
    type associated with it. Here are a couple of examples:

    - [sig : forall (A : Type), (A -> Prop) -> Type] returns [[a; b]] where

        tvar_is_logical a = false,
        tvar_is_arity a = true,
        tvar_is_sort a = true,

        tvar_is_logical b = true,
        tvar_is_arity b = true,
        tvar_is_sort b = false,

    - [Vector.t : Type -> nat -> Type] returns [[a; b]] where

        tvar_is_logical a = false,
        tvar_is_arity a = true,
        tvar_is_sort a = true,

        tvar_is_logical b = false,
        tvar_is_arity b = false,
        tvar_is_sort b = false *)
Record type_var_info :=
  { tvar_name : name;
    tvar_is_logical : bool;
    tvar_is_arity : bool;
    tvar_is_sort : bool; }.

Record one_inductive_body :=
  { ind_name : ident;
    ind_propositional : bool;
    ind_kelim : Universes.allowed_eliminations;
    ind_type_vars : list type_var_info;
    ind_ctors : list (ident *
                      list (name * box_type) *
                      nat (* original arities, unfortunately needed for erases_one_inductive_body *)
                     );
    ind_projs : list (ident * box_type); }.

Record mutual_inductive_body :=
  { ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_bodies : list one_inductive_body }.

Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : mutual_inductive_body -> global_decl
| TypeAliasDecl : option (list type_var_info * box_type) -> global_decl.

(** has_deps specified whether the environment includes dependencies of this global *)
Definition global_env := list (kername * bool (* has_deps *) * global_decl).

Definition lookup_env (Σ : global_env) (id : kername) : option global_decl :=
  option_map snd (find (fun '(name, _, _) => eq_kername id name) Σ).

Definition lookup_constant (Σ : global_env) (kn : kername) : option constant_body :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cst) => Some cst
  | _ => None
  end.

Definition lookup_minductive (Σ : global_env) (kn : kername) : option mutual_inductive_body :=
  match lookup_env Σ kn with
  | Some (InductiveDecl mib) => Some mib
  | _ => None
  end.

Definition lookup_inductive (Σ : global_env) (ind : inductive) : option one_inductive_body :=
  match lookup_minductive Σ (inductive_mind ind) with
  | Some mib => nth_error (ind_bodies mib) (inductive_ind ind)
  | None => None
  end.

Definition lookup_constructor
           (Σ : global_env)
           (ind : inductive) (c : nat) : option (ident * list (name * box_type) * nat) :=
  match lookup_inductive Σ ind with
  | Some oib => nth_error (ind_ctors oib) c
  | None => None
  end.

Definition lookup_constructor_full (Σ : global_env)
           (ind : inductive) (c : nat) :
  option (mutual_inductive_body * one_inductive_body * (ident * list (name * box_type) * nat)) :=
  match lookup_minductive Σ (inductive_mind ind) with
  | Some mib => match nth_error (ind_bodies mib) (inductive_ind ind) with
               | Some oib => match nth_error (ind_ctors oib) c with
                            | Some c => Some (mib, oib, c)
                            | None => None
                            end
               | None => None
               end
  | None => None
  end.

Definition trans_cst (cst : constant_body) : EAst.constant_body :=
  {| EAst.cst_body := cst_body cst |}.

Definition trans_ctors (ctors : list (ident * list (name * box_type) * nat)) :=
  map (fun '(nm, _, nargs) => mkConstructor nm nargs) ctors.

Definition trans_oib (oib : one_inductive_body) : EAst.one_inductive_body :=
  {| EAst.ind_name := oib.(ind_name);
     EAst.ind_kelim := oib.(ind_kelim);
     EAst.ind_propositional := oib.(ind_propositional);
     EAst.ind_ctors := trans_ctors oib.(ind_ctors);
     EAst.ind_projs := map (Basics.compose mkProjection fst) oib.(ind_projs) |}.

Definition trans_mib
           (mib : mutual_inductive_body) : EAst.mutual_inductive_body :=
  {| EAst.ind_finite := mib.(ind_finite);
     EAst.ind_npars := mib.(ind_npars);
     EAst.ind_bodies := map trans_oib mib.(ind_bodies) |}.

Definition trans_global_decl (decl : global_decl) : EAst.global_decl :=
  match decl with
  | ConstantDecl cst => EAst.ConstantDecl (trans_cst cst)
  | InductiveDecl mib => EAst.InductiveDecl (trans_mib mib)
  | TypeAliasDecl o =>
    EAst.ConstantDecl {| EAst.cst_body := option_map (fun _ => tBox) o |}
  end.

Definition fresh_global (s : kername) (g : global_env) :=
  Forall (fun '(kn,_,decl) => kn <> s) g.


Inductive fresh_globals : global_env -> Prop :=
    fresh_globals_empty : fresh_globals []
  | fresh_globals_cons : forall kn b d g,
                         fresh_globals g ->
                         fresh_global kn g ->
                         fresh_globals ((kn,b,d) :: g).

Definition trans_env (Σ : global_env) : EAst.global_context :=
  map (fun d => (d.1.1, trans_global_decl d.2)) Σ.

Definition print_term (Σ : global_env) (t : term) : bytestring.String.t :=
  EPretty.print_program (trans_env Σ,t).
