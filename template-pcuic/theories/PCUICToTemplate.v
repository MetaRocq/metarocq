(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Uint63 FloatOps FloatAxioms.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases.
Set Warnings "-notation-overridden".
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Template Require Import  AstUtils Ast.
Set Warnings "+notation-overridden".

Definition uint63_from_model (i : uint63_model) : Uint63.int :=
  Uint63.of_Z (proj1_sig i).

Definition float64_from_model (f : float64_model) : PrimFloat.float :=
  FloatOps.SF2Prim (proj1_sig f).

Definition trans_prim (trans : PCUICAst.term -> Ast.term) (t : prim_val) : Ast.term :=
  match t.π2 with
  | primIntModel i => Ast.tInt i
  | primFloatModel f => Ast.tFloat f
  | primStringModel s => Ast.tString s
  | primArrayModel a => Ast.tArray (array_universe a) (map trans (array_value a)) (trans (array_default a)) (trans (array_type a))
  end.

Definition trans_predicate (t : PCUICAst.predicate Ast.term) : predicate Ast.term :=
  {| pparams := t.(PCUICAst.pparams);
     puinst := t.(PCUICAst.puinst);
     pcontext := forget_types t.(PCUICAst.pcontext);
     preturn := t.(PCUICAst.preturn) |}.

Definition trans_branch (t : PCUICAst.branch Ast.term) : branch Ast.term :=
  {| bcontext := forget_types t.(PCUICAst.bcontext);
     bbody := t.(PCUICAst.bbody) |}.

Fixpoint trans (t : PCUICAst.term) : Ast.term :=
  match t with
  | PCUICAst.tRel n => tRel n
  | PCUICAst.tVar n => tVar n
  | PCUICAst.tEvar ev args => tEvar ev (List.map trans args)
  | PCUICAst.tSort u => tSort u
  | PCUICAst.tConst c u => tConst c u
  | PCUICAst.tInd c u => tInd c u
  | PCUICAst.tConstruct c k u => tConstruct c k u
  | PCUICAst.tLambda na T M => tLambda na (trans T) (trans M)
  | PCUICAst.tApp u v => mkApp (trans u) (trans v)
  | PCUICAst.tProd na A B => tProd na (trans A) (trans B)
  | PCUICAst.tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | PCUICAst.tCase ind p c brs =>
    let p' := PCUICAst.map_predicate id trans trans (map_context trans) p in
    let brs' := List.map (PCUICAst.map_branch trans (map_context trans)) brs in
    tCase ind (trans_predicate p') (trans c) (map trans_branch brs')
  | PCUICAst.tProj p c => tProj p (trans c)
  | PCUICAst.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | PCUICAst.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  | PCUICAst.tPrim i => trans_prim trans i
  end.

Notation trans_decl := (map_decl trans).

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_constructor_body (d : PCUICEnvironment.constructor_body) :=
  {| cstr_name := d.(PCUICEnvironment.cstr_name);
     cstr_args := trans_local d.(PCUICEnvironment.cstr_args);
     cstr_indices := map trans d.(PCUICEnvironment.cstr_indices);
     cstr_type := trans d.(PCUICEnvironment.cstr_type);
     cstr_arity := d.(PCUICEnvironment.cstr_arity) |}.

Definition trans_projection_body (d : PCUICEnvironment.projection_body) :=
 {| proj_name := d.(PCUICEnvironment.proj_name);
    proj_type := trans d.(PCUICEnvironment.proj_type);
    proj_relevance := d.(PCUICEnvironment.proj_relevance) |}.

Definition trans_one_ind_body (d : PCUICEnvironment.one_inductive_body) :=
  {| ind_name := d.(PCUICEnvironment.ind_name);
     ind_relevance := d.(PCUICEnvironment.ind_relevance);
     ind_indices := trans_local d.(PCUICEnvironment.ind_indices);
     ind_type := trans d.(PCUICEnvironment.ind_type);
     ind_sort := d.(PCUICEnvironment.ind_sort);
     ind_kelim := d.(PCUICEnvironment.ind_kelim);
     ind_ctors := List.map trans_constructor_body d.(PCUICEnvironment.ind_ctors);
     ind_projs := List.map trans_projection_body d.(PCUICEnvironment.ind_projs) |}.

Definition trans_constant_body bd :=
  {| cst_type := trans bd.(PCUICEnvironment.cst_type); cst_body := option_map trans bd.(PCUICEnvironment.cst_body);
     cst_universes := bd.(PCUICEnvironment.cst_universes);
     cst_relevance := bd.(PCUICEnvironment.cst_relevance) |}.


Definition trans_minductive_body md :=
  {| ind_finite := md.(PCUICEnvironment.ind_finite);
     ind_npars := md.(PCUICEnvironment.ind_npars);
     ind_params := trans_local md.(PCUICEnvironment.ind_params);
     ind_bodies := map trans_one_ind_body md.(PCUICEnvironment.ind_bodies);
     ind_universes := md.(PCUICEnvironment.ind_universes);
     ind_variance := md.(PCUICEnvironment.ind_variance)
  |}.

Definition trans_global_decl (d : PCUICEnvironment.global_decl) :=
  match d with
  | PCUICEnvironment.ConstantDecl bd => ConstantDecl (trans_constant_body bd)
  | PCUICEnvironment.InductiveDecl bd => InductiveDecl (trans_minductive_body bd)
  end.

Definition trans_global_decls (d : PCUICEnvironment.global_declarations) : global_declarations :=
  List.map (on_snd trans_global_decl) d.

Definition trans_global_env (d : PCUICEnvironment.global_env) : global_env :=
  {| universes := d.(PCUICEnvironment.universes);
     declarations := trans_global_decls d.(PCUICEnvironment.declarations);
     retroknowledge := d.(PCUICEnvironment.retroknowledge) |}.

Definition trans_global (Σ : PCUICEnvironment.global_env_ext) : global_env_ext :=
  (trans_global_env (fst Σ), snd Σ).

Definition trans_one_inductive_entry (oie : PCUICAst.one_inductive_entry) : one_inductive_entry
  := {| mind_entry_typename := oie.(PCUICAst.mind_entry_typename);
       mind_entry_arity := trans oie.(PCUICAst.mind_entry_arity);
       mind_entry_consnames := oie.(PCUICAst.mind_entry_consnames);
       mind_entry_lc := List.map trans oie.(PCUICAst.mind_entry_lc); |}.

Definition trans_mutual_inductive_entry (mie : PCUICAst.mutual_inductive_entry) : mutual_inductive_entry
  := {| mind_entry_record := mie.(PCUICAst.mind_entry_record);
       mind_entry_finite := mie.(PCUICAst.mind_entry_finite);
       mind_entry_private := mie.(PCUICAst.mind_entry_private);
       mind_entry_universes := universes_entry_of_decl mie.(PCUICAst.mind_entry_universes);
       mind_entry_inds := List.map trans_one_inductive_entry mie.(PCUICAst.mind_entry_inds);
       mind_entry_params := trans_local mie.(PCUICAst.mind_entry_params);
       mind_entry_variance := None (* TODO: support universe variance in PCUIC *);
       mind_entry_template := false (* TODO: support template polymorphism in PCUIC? *) |}.
