(* Distributed under the terms of the MIT license. *)
(* From Stdlib Require Import Uint63 FloatOps FloatAxioms. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICTyping PCUICProgram.

(** This translation expands lets in constructor arguments, so that
  iota reduction reduces to a simple substitution operation with no
  let expansion involved.
*)

Definition trans_branch p (br : branch term) :=
  if is_assumption_context br.(bcontext) then br
  else
    {| bcontext := smash_context [] br.(bcontext);
       bbody :=
        expand_lets
          (subst_context (List.rev p.(pparams)) 0 br.(bcontext)@[p.(puinst)])
          br.(bbody) |}.

Fixpoint trans (t : term) : term :=
  match t with
  | tRel n => tRel n
  | tVar n => tVar n
  | tEvar ev args => tEvar ev (List.map trans args)
  | tSort u => tSort u
  | tConst c u => tConst c u
  | tInd c u => tInd c u
  | tConstruct c k u => tConstruct c k u
  | tLambda na T M => tLambda na (trans T) (trans M)
  | tApp u v => tApp (trans u) (trans v)
  | tProd na A B => tProd na (trans A) (trans B)
  | tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | tCase ind p c brs =>
    let p' := map_predicate id trans trans (map_context trans) p in
    let brs' := List.map (map_branch trans (map_context trans)) brs in
    tCase ind p' (trans c) (map (trans_branch p') brs')
  | tProj p c => tProj p (trans c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  | tPrim i => tPrim (map_prim trans i)
  end.

Abbreviation trans_decl := (map_decl trans).

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_cstr_concl_head mdecl i (args : context) :=
  tRel (#|mdecl.(ind_bodies)| - S i + #|mdecl.(ind_params)| + #|args|).

Definition trans_cstr_concl mdecl i args indices :=
  (mkApps (trans_cstr_concl_head mdecl i args)
    (to_extended_list_k (trans_local mdecl.(ind_params)) #|args| ++ indices)).

Definition trans_constructor_body i (mdecl : mutual_inductive_body) (d : PCUICEnvironment.constructor_body) :=
  let args' := trans_local d.(cstr_args) in
  let args := smash_context [] args' in
  let indices := map (expand_lets args') (map trans d.(cstr_indices)) in
  {| cstr_name := d.(PCUICEnvironment.cstr_name);
     cstr_args := args;
     cstr_indices := indices;
     cstr_type :=
      it_mkProd_or_LetIn (trans_local mdecl.(ind_params))
        (it_mkProd_or_LetIn args
          (trans_cstr_concl mdecl i args indices));
     cstr_arity := d.(PCUICEnvironment.cstr_arity) |}.

Definition trans_projection_body (d : PCUICEnvironment.projection_body) :=
 {| proj_name := d.(PCUICEnvironment.proj_name);
    proj_type := trans d.(PCUICEnvironment.proj_type);
    proj_relevance := d.(PCUICEnvironment.proj_relevance) |}.

Definition trans_one_ind_body mdecl i (d : PCUICEnvironment.one_inductive_body) :=
  {| ind_name := d.(PCUICEnvironment.ind_name);
     ind_relevance := d.(PCUICEnvironment.ind_relevance);
     ind_indices := trans_local d.(PCUICEnvironment.ind_indices);
     ind_type := trans d.(PCUICEnvironment.ind_type);
     ind_sort := d.(PCUICEnvironment.ind_sort);
     ind_kelim := d.(PCUICEnvironment.ind_kelim);
     ind_ctors := List.map (trans_constructor_body i mdecl) d.(PCUICEnvironment.ind_ctors);
     ind_projs := List.map trans_projection_body d.(PCUICEnvironment.ind_projs) |}.

Definition trans_minductive_body md :=
  {| ind_finite := md.(PCUICEnvironment.ind_finite);
     ind_npars := md.(PCUICEnvironment.ind_npars);
     ind_params := trans_local md.(PCUICEnvironment.ind_params);
     ind_bodies := mapi (trans_one_ind_body md) md.(PCUICEnvironment.ind_bodies);
     ind_universes := md.(PCUICEnvironment.ind_universes);
     ind_variance := md.(PCUICEnvironment.ind_variance)
  |}.

Definition trans_constant_body bd :=
  {| cst_type := trans bd.(PCUICEnvironment.cst_type);
     cst_body := option_map trans bd.(PCUICEnvironment.cst_body);
     cst_universes := bd.(PCUICEnvironment.cst_universes);
     cst_relevance := bd.(PCUICEnvironment.cst_relevance) |}.

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

Definition expand_lets_program (p : pcuic_program) : pcuic_program :=
  let Σ' := PCUICExpandLets.trans_global p.1 in
  ((build_global_env_map Σ', p.1.2), PCUICExpandLets.trans p.2).
