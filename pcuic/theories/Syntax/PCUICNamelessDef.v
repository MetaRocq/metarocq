(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import RelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICTyping PCUICPosition PCUICUnivSubst
     PCUICSigmaCalculus (* for context manipulations *).
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect.

Implicit Types cf : checker_flags.

(** Typing / conversion does not rely on name annotations of binders.

  We prove this by constructing a type-preserving translation to
  terms where all binders are anonymous. An alternative would be to
  be parametrically polymorphic everywhere on the binder name type.
  This would allow to add implicit information too. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".

Definition anon (na : name) : bool :=
  match na with
  | nAnon => true
  | nNamed s => false
  end.

Definition banon (na : binder_annot name) : bool := anon na.(binder_name).

Definition nameless_decl nameless (d : context_decl) :=
  banon (decl_name d) && option_default nameless d.(decl_body) true && nameless d.(decl_type).

Fixpoint nameless (t : term) : bool :=
  match t with
  | tRel n => true
  | tVar n => true
  | tEvar n l => forallb nameless l
  | tSort s => true
  | tProd na A B => banon na && nameless A && nameless B
  | tLambda na A b => banon na && nameless A && nameless b
  | tLetIn na b B t => banon na && nameless b && nameless B && nameless t
  | tApp u v => nameless u && nameless v
  | tConst c u => true
  | tInd i u => true
  | tConstruct i n u => true
  | tCase ci p c brs =>
    forallb nameless p.(pparams) &&
    forallb (nameless_decl nameless) p.(pcontext) &&
    nameless p.(preturn) && nameless c &&
    forallb (fun b => forallb (nameless_decl nameless) b.(bcontext) && nameless b.(bbody)) brs
  | tProj p c => nameless c
  | tFix mfix idx =>
    forallb (fun d => banon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  | tCoFix mfix idx =>
    forallb (fun d => banon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  | tPrim p => test_prim nameless p
  end.

Abbreviation nameless_ctx := (forallb (nameless_decl nameless)).

Definition anonymize (b : binder_annot name) : binder_annot name :=
  map_binder_annot (fun _ => nAnon) b.

Definition map_def_anon {A B} (tyf bodyf : A -> B) (d : def A) := {|
  dname := anonymize d.(dname) ;
  dtype := tyf d.(dtype) ;
  dbody := bodyf d.(dbody) ;
  rarg  := d.(rarg)
|}.

Definition map_decl_anon (f : term -> term) (d : context_decl) := {|
  decl_name := anonymize d.(decl_name) ;
  decl_body := option_map f d.(decl_body) ;
  decl_type := f d.(decl_type)
|}.

Definition nl_predicate (nl : term -> term) (p : predicate term) : predicate term :=
  {| pparams := map nl p.(pparams);
     puinst := p.(puinst);
     pcontext := map (map_decl_anon nl) p.(pcontext);
     preturn := nl p.(preturn); |}.

Definition nl_branch (nl : term -> term) (b : branch term) : branch term :=
  {| bcontext := map (map_decl_anon nl) b.(bcontext);
     bbody := nl b.(bbody); |}.

Fixpoint nl (t : term) : term :=
  match t with
  | tRel n => tRel n
  | tVar n => tVar n
  | tEvar n l => tEvar n (map nl l)
  | tSort s => tSort s
  | tProd na A B => tProd (anonymize na) (nl A) (nl B)
  | tLambda na A b => tLambda (anonymize na) (nl A) (nl b)
  | tLetIn na b B t => tLetIn (anonymize na) (nl b) (nl B) (nl t)
  | tApp u v => tApp (nl u) (nl v)
  | tConst c u => tConst c u
  | tInd i u => tInd i u
  | tConstruct i n u => tConstruct i n u
  | tCase ci p c brs => tCase ci (nl_predicate nl p) (nl c) (map (nl_branch nl) brs)
  | tProj p c => tProj p (nl c)
  | tFix mfix idx => tFix (map (map_def_anon nl nl) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def_anon nl nl) mfix) idx
  | tPrim p => tPrim (map_prim nl p)
  end.

Definition nlctx (Γ : context) : context :=
  map (map_decl_anon nl) Γ.

Definition nl_constant_body c :=
  Build_constant_body
    (nl c.(cst_type)) (option_map nl c.(cst_body)) c.(cst_universes)
    c.(cst_relevance).

Definition nl_constructor_body c :=
  {| cstr_name := c.(cstr_name) ;
     cstr_args := nlctx c.(cstr_args);
     cstr_indices := map nl c.(cstr_indices);
     cstr_type := nl c.(cstr_type);
     cstr_arity := c.(cstr_arity) |}.

Definition nl_projection_body p :=
  {| proj_name := p.(proj_name) ;
     proj_type := nl p.(proj_type);
     proj_relevance := p.(proj_relevance) |}.

Definition nl_one_inductive_body o :=
  Build_one_inductive_body
    o.(ind_name)
    (nlctx o.(ind_indices))
    o.(ind_sort)
    (nl o.(ind_type))
    o.(ind_kelim)
    (map nl_constructor_body o.(ind_ctors))
    (map nl_projection_body o.(ind_projs))
    o.(ind_relevance).

Definition nl_mutual_inductive_body m :=
  Build_mutual_inductive_body
    m.(ind_finite)
    m.(ind_npars)
    (nlctx m.(ind_params))
    (map nl_one_inductive_body m.(ind_bodies))
    m.(ind_universes) m.(ind_variance).

Definition nl_global_decl (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cb => ConstantDecl (nl_constant_body cb)
  | InductiveDecl mib => InductiveDecl (nl_mutual_inductive_body mib)
  end.

Definition nl_global_declarations (Σ : global_declarations) : global_declarations :=
  (map (on_snd nl_global_decl) Σ).

Definition nl_global_env (Σ : global_env) : global_env :=
  {| universes := Σ.(universes);
     declarations := nl_global_declarations Σ.(declarations);
     retroknowledge := Σ.(retroknowledge) |}.

Definition nlg (Σ : global_env_ext) : global_env_ext :=
  let '(Σ, φ) := Σ in
  (nl_global_env Σ, φ).
