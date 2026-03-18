From Stdlib Require Import ssreflect ssrbool Morphisms Setoid ProofIrrelevance.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames EnvMap BasicAst.
From MetaRocq.Erasure Require Import EAst EGlobalEnv EAstUtils EGlobalEnv EAstUtils.
Import MonadNotation.

Lemma fresh_globals_cons_inv {Σ : global_context} {d} : EnvMap.fresh_globals (d :: Σ) -> EnvMap.fresh_globals Σ.
Proof. intros H; now depelim H. Qed.

Module GlobalContextMap.
  Record t :=
  { global_decls :> global_declarations;
    map : EnvMap.t global_decl;
    repr : EnvMap.repr global_decls map;
    wf : EnvMap.fresh_globals global_decls }.

  Program Definition empty : t :=
    {| global_decls := [];
       map := EnvMap.empty |}.
    Next Obligation.
      constructor.
    Qed.

  Program Definition add (Σ : GlobalContextMap.t) kn d (hpre : fresh_global kn Σ) : GlobalContextMap.t :=
    {| global_decls := (kn,d) :: Σ.(global_decls);
        map := EnvMap.add kn d Σ.(map) |}.
    Next Obligation.
      simpl. unfold KernameMapFact.uncurry.
      pose proof (Σ.(repr)). unfold EnvMap.repr in H.
      now rewrite H.
    Qed.
    Next Obligation.
      constructor => //. apply Σ.(wf).
    Qed.

  Definition global_context_map_equal Σ Σ' :=
    Σ.(global_decls) = Σ'.(global_decls).

  #[global] Instance gceq : DefaultRelation global_context_map_equal := {}.

  Lemma global_context_map_ind (P : GlobalContextMap.t -> Prop)
    (proper : Morphisms.Proper (global_context_map_equal ==> iff) P)
    (Pnil : P empty)
    (Pcons :
      forall Σ kn d fr,
        P Σ ->
        P (add Σ kn d fr))
      Σ : P Σ.
  Proof.
    destruct Σ as [Σ ? ? ?].
    induction Σ in map0, repr0, wf0 |- *; set (Σ':= {| global_decls := _ |}).
    - setoid_replace Σ' with empty => //.
    - set (Σg := {| global_decls := Σ; map := EnvMap.of_global_env Σ; repr := EnvMap.repr_global_env _;
           wf := fresh_globals_cons_inv wf0 |}).
      destruct a as [kn d].
      assert (fresh_global kn Σ). now depelim wf0.
      setoid_replace Σ' with (add Σg kn d H).
      apply Pcons. apply IHΣ.
      red. unfold Σ', add.
      cbn. reflexivity.
  Qed.

  Definition lookup_env Σ kn := EnvMap.lookup kn Σ.(map).

  Lemma lookup_env_spec (Σ : t) kn : lookup_env Σ kn = EGlobalEnv.lookup_env Σ kn.
  Proof.
    rewrite /lookup_env.
    rewrite (EnvMap.lookup_spec Σ.(global_decls)) //; apply Σ.
  Qed.

  Definition lookup_constant Σ kn : option constant_body :=
    decl <- lookup_env Σ kn;;
    match decl with
    | ConstantDecl cb => ret cb
    | InductiveDecl _ => None
    end.

  Lemma lookup_constant_spec Σ kn : lookup_constant Σ kn = EGlobalEnv.lookup_constant Σ kn.
  Proof.
    rewrite /lookup_constant /EGlobalEnv.lookup_constant.
    rewrite lookup_env_spec //.
  Qed.

  Definition lookup_minductive Σ kn : option mutual_inductive_body :=
    decl <- lookup_env Σ kn;;
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Lemma lookup_minductive_spec Σ kn : lookup_minductive Σ kn = EGlobalEnv.lookup_minductive Σ kn.
  Proof.
    rewrite /lookup_minductive /EGlobalEnv.lookup_minductive.
    rewrite lookup_env_spec //.
  Qed.

  Definition lookup_inductive Σ kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive Σ (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).

  Lemma lookup_inductive_spec Σ kn : lookup_inductive Σ kn = EGlobalEnv.lookup_inductive Σ kn.
  Proof.
    rewrite /lookup_inductive /EGlobalEnv.lookup_inductive.
    rewrite lookup_minductive_spec //.
  Qed.

  Definition lookup_constructor Σ kn c : option (mutual_inductive_body * one_inductive_body * constructor_body) :=
    '(mdecl, idecl) <- lookup_inductive Σ kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl, idecl, cdecl).

  Lemma lookup_constructor_spec Σ kn : lookup_constructor Σ kn = EGlobalEnv.lookup_constructor Σ kn.
  Proof.
    rewrite /lookup_constructor /EGlobalEnv.lookup_constructor.
    rewrite lookup_inductive_spec //.
  Qed.

  Definition lookup_projection Σ (p : projection) :
    option (mutual_inductive_body * one_inductive_body * constructor_body * projection_body) :=
    '(mdecl, idecl, cdecl) <- lookup_constructor Σ p.(proj_ind) 0 ;;
    pdecl <- nth_error idecl.(ind_projs) p.(proj_arg) ;;
    ret (mdecl, idecl, cdecl, pdecl).

  Lemma lookup_projection_spec Σ kn : lookup_projection Σ kn = EGlobalEnv.lookup_projection Σ kn.
  Proof.
    rewrite /lookup_projection /EGlobalEnv.lookup_projection.
    rewrite lookup_constructor_spec //.
  Qed.

  Definition lookup_inductive_pars Σ kn : option nat :=
    mdecl <- lookup_minductive Σ kn ;;
    ret mdecl.(ind_npars).

  Lemma lookup_inductive_pars_spec Σ kn : lookup_inductive_pars Σ kn = EGlobalEnv.lookup_inductive_pars Σ kn.
  Proof.
    rewrite /lookup_inductive_pars /EGlobalEnv.lookup_inductive_pars.
    now rewrite lookup_minductive_spec.
  Qed.

  Definition lookup_inductive_kind Σ kn : option recursivity_kind :=
    mdecl <- lookup_minductive Σ kn ;;
    ret mdecl.(ind_finite).

  Lemma lookup_inductive_kind_spec Σ kn : lookup_inductive_kind Σ kn = EGlobalEnv.lookup_inductive_kind Σ kn.
  Proof.
    rewrite /lookup_inductive_kind /EGlobalEnv.lookup_inductive_kind.
    now rewrite lookup_minductive_spec.
  Qed.

  Definition inductive_isprop_and_pars Σ (ind : inductive) :=
    '(mdecl, idecl) <- lookup_inductive Σ ind ;;
    ret (ind_propositional idecl, ind_npars mdecl).

  Lemma inductive_isprop_and_pars_spec Σ kn :
    inductive_isprop_and_pars Σ kn = EGlobalEnv.inductive_isprop_and_pars Σ kn.
  Proof.
    rewrite /inductive_isprop_and_pars /EGlobalEnv.inductive_isprop_and_pars.
    now rewrite lookup_inductive_spec.
  Qed.

  Definition constructor_isprop_pars_decl Σ (ind : inductive) (c : nat) :=
    '(mdecl, idecl, cdecl) <- lookup_constructor Σ ind c ;;
    ret (ind_propositional idecl, ind_npars mdecl, cdecl).

  Lemma constructor_isprop_pars_decl_spec Σ kn :
    constructor_isprop_pars_decl Σ kn = EGlobalEnv.constructor_isprop_pars_decl Σ kn.
  Proof.
    rewrite /constructor_isprop_pars_decl /EGlobalEnv.constructor_isprop_pars_decl.
    rewrite lookup_constructor_spec //.
  Qed.

  Definition lookup_constructor_pars_args Σ (ind : inductive) (c : nat) :=
    '(mdecl, idecl, cdecl) <- lookup_constructor Σ ind c ;;
    ret (ind_npars mdecl, cstr_nargs cdecl).

  Lemma lookup_constructor_pars_args_spec Σ kn :
    lookup_constructor_pars_args Σ kn = EGlobalEnv.lookup_constructor_pars_args Σ kn.
  Proof.
    rewrite /lookup_constructor_pars_args /EGlobalEnv.lookup_constructor_pars_args.
    rewrite lookup_constructor_spec //.
  Qed.

  Program Definition make (g : global_declarations) (Hg : EnvMap.fresh_globals g): t :=
    {| global_decls := g;
       map := EnvMap.of_global_env g |}.

  Lemma make_irrel Σ fr fr' : EEnvMap.GlobalContextMap.make Σ fr = EEnvMap.GlobalContextMap.make Σ fr'.
  Proof.
    unfold make. f_equal.
    apply proof_irrelevance.
  Qed.

End GlobalContextMap.

Coercion GlobalContextMap.global_decls : GlobalContextMap.t >-> global_declarations.
