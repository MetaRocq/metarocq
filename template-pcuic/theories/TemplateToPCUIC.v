(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Uint63 FloatOps FloatAxioms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive EnvMap.
From MetaRocq.Template Require AstUtils TemplateProgram.
From MetaRocq.PCUIC Require Import PCUICAst PCUICPrimitive PCUICCases PCUICProgram.

Lemma to_Z_bounded_bool (i : Uint63.int) :
  ((0 <=? Uint63.to_Z i) && (Uint63.to_Z i <? wB))%Z.
Proof.
  generalize (Uint63.to_Z_bounded i).
  now intros [->%Z.leb_le ->%Z.ltb_lt].
Qed.

Definition uint63_to_model (i : Uint63.int) : uint63_model :=
  exist (Uint63.to_Z i) (to_Z_bounded_bool i).

Definition float64_to_model (f : PrimFloat.float) : float64_model :=
  exist (FloatOps.Prim2SF f) (FloatAxioms.Prim2SF_valid f).

Section Map2Bias.
  Context {A B C} (f : A -> B -> C) (default : B).

  Fixpoint map2_bias_left (l : list A) (l' : list B) : list C :=
    match l, l' with
    | [], [] => []
    | a :: as_, b :: bs => (f a b) :: map2_bias_left as_ bs
    | a :: as_, [] => (f a default) :: map2_bias_left as_ []
    | _, _ => []
    end.

  Lemma map2_bias_left_length l l' : #|map2_bias_left l l'| = #|l|.
  Proof using Type.
    induction l in l' |- *; destruct l'; simpl; auto; now rewrite IHl.
  Qed.

  Lemma map2_map2_bias_left l l' : #|l| = #|l'| -> map2_bias_left l l' = map2 f l l'.
  Proof using Type.
    induction l in l' |- *; destruct l'; simpl; auto.
    - discriminate.
    - intros [= hlen]. rewrite IHl; tas. reflexivity.
  Qed.
End Map2Bias.

Section Trans.
  Context (Σ : global_env_map).

  Definition dummy_decl : context_decl :=
    vass {| binder_name := nAnon; binder_relevance := Relevant |} (tSort Sort.type0).

  Definition trans_predicate ind mdecl idecl pparams puinst pcontext preturn :=
    let pctx := map2_bias_left set_binder_name dummy_decl pcontext (ind_predicate_context ind mdecl idecl) in
    {| pparams := pparams;
       puinst := puinst;
       pcontext := pctx;
       preturn := preturn |}.

  Definition trans_branch ind mdecl cdecl bcontext bbody :=
    let bctx := map2_bias_left set_binder_name dummy_decl bcontext (cstr_branch_context ind mdecl cdecl) in
    {| bcontext := bctx;
       bbody := bbody |}.

  Fixpoint trans (t : Ast.term) : term :=
  match t with
  | Ast.tRel n => tRel n
  | Ast.tVar n => tVar n
  | Ast.tEvar ev args => tEvar ev (List.map trans args)
  | Ast.tSort u => tSort u
  | Ast.tConst c u => tConst c u
  | Ast.tInd c u => tInd c u
  | Ast.tConstruct c k u => tConstruct c k u
  | Ast.tLambda na T M => tLambda na (trans T) (trans M)
  | Ast.tApp u v => mkApps (trans u) (List.map trans v)
  | Ast.tProd na A B => tProd na (trans A) (trans B)
  | Ast.tCast c kind t => tApp (tLambda (mkBindAnn nAnon rel_of_Type) (trans t) (tRel 0)) (trans c)
  | Ast.tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | Ast.tCase ci p c brs =>
    let p' := Ast.map_predicate id trans trans p in
    let brs' := List.map (Ast.map_branch trans) brs in
    match TransLookup.lookup_inductive Σ ci.(ci_ind) with
    | Some (mdecl, idecl) =>
      let tp := trans_predicate ci.(ci_ind) mdecl idecl p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
      let tbrs :=
        map2 (fun cdecl br => trans_branch ci.(ci_ind) mdecl cdecl br.(Ast.bcontext) br.(Ast.bbody))
                  idecl.(ind_ctors) brs' in
      tCase ci tp (trans c) tbrs
    | None =>
      (** We build an ill-formed case if the term + environment are not well-formed.
          But we still give the right length to the context so that all syntactic operations
          still work. *)
      tCase ci {| pparams := p'.(Ast.pparams);
                  puinst := p'.(Ast.puinst);
                  pcontext := map (fun na => vass na (tSort Sort.type0)) p'.(Ast.pcontext);
                  preturn := p'.(Ast.preturn) |}
          (trans c) []
    end
  | Ast.tProj p c => tProj p (trans c)
  | Ast.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | Ast.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  | Ast.tInt n => tPrim (primInt; primIntModel n)
  | Ast.tFloat n => tPrim (primFloat; primFloatModel n)
  | Ast.tString n => tPrim (primString; primStringModel n)
  | Ast.tArray l v d ty => tPrim (primArray; primArrayModel
    {| array_universe := l;
       array_value := List.map trans v;
       array_default := trans d;
       array_type := trans ty |})
  end.

  Definition trans_decl (d : Ast.Env.context_decl) :=
    {| decl_name := d.(decl_name);
      decl_body := option_map trans d.(decl_body);
      decl_type := trans d.(decl_type) |}.

  Definition trans_local Γ := List.map trans_decl Γ.

  Definition trans_constructor_body (d : Ast.Env.constructor_body) :=
    {| cstr_name := d.(Ast.Env.cstr_name);
      cstr_args := trans_local d.(Ast.Env.cstr_args);
      cstr_indices := map trans d.(Ast.Env.cstr_indices);
      cstr_type := trans d.(Ast.Env.cstr_type);
      cstr_arity := d.(Ast.Env.cstr_arity) |}.
  Definition trans_projection_body (d : Ast.Env.projection_body) :=
    {| proj_name := d.(Ast.Env.proj_name);
        proj_type := trans d.(Ast.Env.proj_type);
        proj_relevance := d.(Ast.Env.proj_relevance) |}.

  Definition trans_one_ind_body (d : Ast.Env.one_inductive_body) :=
    {| ind_name := d.(Ast.Env.ind_name);
      ind_relevance := d.(Ast.Env.ind_relevance);
      ind_indices := trans_local d.(Ast.Env.ind_indices);
      ind_sort := d.(Ast.Env.ind_sort);
      ind_type := trans d.(Ast.Env.ind_type);
      ind_kelim := d.(Ast.Env.ind_kelim);
      ind_ctors := List.map trans_constructor_body d.(Ast.Env.ind_ctors);
      ind_projs := List.map trans_projection_body d.(Ast.Env.ind_projs) |}.

  Definition trans_constant_body bd :=
    {| cst_type := trans bd.(Ast.Env.cst_type);
       cst_body := option_map trans bd.(Ast.Env.cst_body);
       cst_universes := bd.(Ast.Env.cst_universes);
       cst_relevance := bd.(Ast.Env.cst_relevance) |}.

  Definition trans_minductive_body md :=
    {| ind_finite := md.(Ast.Env.ind_finite);
      ind_npars := md.(Ast.Env.ind_npars);
      ind_params := trans_local md.(Ast.Env.ind_params);
      ind_bodies := map trans_one_ind_body md.(Ast.Env.ind_bodies);
      ind_universes := md.(Ast.Env.ind_universes);
      ind_variance := md.(Ast.Env.ind_variance) |}.

  Definition trans_global_decl (d : Ast.Env.global_decl) :=
    match d with
    | Ast.Env.ConstantDecl bd => ConstantDecl (trans_constant_body bd)
    | Ast.Env.InductiveDecl bd => InductiveDecl (trans_minductive_body bd)
    end.
End Trans.

Program Definition add_global_decl (env : global_env_map) (d : kername × global_decl) :=
  {| trans_env_env := add_global_decl env.(trans_env_env) d;
     trans_env_map := EnvMap.add d.1 d.2 env.(trans_env_map) |}.
Next Obligation.
  pose proof env.(trans_env_repr).
  red in H. rewrite H. reflexivity.
Qed.

Definition trans_global_decls env (d : Ast.Env.global_declarations) : global_env_map :=
  fold_right (fun decl Σ' =>
    let decl' := on_snd (trans_global_decl Σ') decl in
    add_global_decl Σ' decl') env d.

Definition empty_trans_env univs retro :=
  let init_global_env := {| universes := univs; declarations := []; retroknowledge := retro |} in
    {| trans_env_env := init_global_env;
       trans_env_map := EnvMap.empty;
       trans_env_repr := fun y => eq_refl |}.

Definition trans_global_env (d : Ast.Env.global_env) : global_env_map :=
  let init := empty_trans_env d.(Ast.Env.universes) d.(Ast.Env.retroknowledge) in
  trans_global_decls init d.(Ast.Env.declarations).

Definition trans_global (Σ : Ast.Env.global_env_ext) : global_env_ext_map :=
  (trans_global_env (fst Σ), snd Σ).

Definition trans_template_program (p :TemplateProgram.template_program) : pcuic_program :=
  let Σ' := trans_global (Ast.Env.empty_ext p.1) in
  (Σ', trans Σ' p.2).

