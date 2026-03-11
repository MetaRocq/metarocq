From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames EnvMap.
From MetaRocq.Template Require Import Ast Typing.
Import MonadNotation.

Lemma fresh_globals_cons_inv {Σ : global_declarations} {d} : EnvMap.fresh_globals (d :: Σ) -> EnvMap.fresh_globals Σ.
Proof. intros H; now depelim H. Qed.

Lemma wf_fresh_globals {cf : checker_flags} (Σ : global_env) : wf Σ -> EnvMap.fresh_globals Σ.(declarations).
Proof.
  destruct Σ as [univs Σ]; cbn.
  move=> [] onu; cbn. induction 1; try destruct o; constructor; auto; constructor; eauto.
Qed.

Local Coercion declarations : global_env >-> global_declarations.

Module GlobalEnvMap.
  Record t :=
  { env :> global_env;
    map : EnvMap.t global_decl;
    repr : EnvMap.repr env.(declarations) map;
    wf : EnvMap.fresh_globals env.(declarations) }.

  Definition lookup_env Σ kn := EnvMap.lookup kn Σ.(map).

  Lemma lookup_env_spec (Σ : t) kn : lookup_env Σ kn = Env.lookup_env Σ kn.
  Proof.
    rewrite /lookup_env /Env.lookup_env.
    apply (EnvMap.lookup_spec Σ.(env).(declarations)); apply Σ.
  Qed.

  Definition lookup_minductive Σ kn : option mutual_inductive_body :=
    decl <- lookup_env Σ kn;;
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Lemma lookup_minductive_spec Σ kn : lookup_minductive Σ kn = Ast.lookup_minductive Σ kn.
  Proof.
    rewrite /lookup_minductive /Ast.lookup_minductive.
    rewrite lookup_env_spec //.
  Qed.

  Definition lookup_inductive Σ kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive Σ (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).

  Lemma lookup_inductive_spec Σ kn : lookup_inductive Σ kn = Ast.lookup_inductive Σ kn.
  Proof.
    rewrite /lookup_inductive /Ast.lookup_inductive.
    rewrite lookup_minductive_spec //.
  Qed.

  Definition lookup_constructor Σ kn c : option (mutual_inductive_body * one_inductive_body * constructor_body) :=
    '(mdecl, idecl) <- lookup_inductive Σ kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl, idecl, cdecl).

  Lemma lookup_constructor_spec Σ kn : lookup_constructor Σ kn = Ast.lookup_constructor Σ kn.
  Proof.
    rewrite /lookup_constructor /Ast.lookup_constructor.
    rewrite lookup_inductive_spec //.
  Qed.

  Definition lookup_projection Σ (p : projection) :
    option (mutual_inductive_body * one_inductive_body * constructor_body * projection_body) :=
    '(mdecl, idecl, cdecl) <- lookup_constructor Σ p.(proj_ind) 0 ;;
    pdecl <- nth_error idecl.(ind_projs) p.(proj_arg) ;;
    ret (mdecl, idecl, cdecl, pdecl).

  Lemma lookup_projection_spec Σ kn : lookup_projection Σ kn = Ast.lookup_projection Σ kn.
  Proof.
    rewrite /lookup_projection /Ast.lookup_projection.
    rewrite lookup_constructor_spec //.
  Qed.

  Program Definition make (g : global_env) (Hg : EnvMap.fresh_globals g.(declarations)): t :=
    {| env := g;
       map := EnvMap.of_global_env g.(declarations) |}.

End GlobalEnvMap.

Coercion GlobalEnvMap.env : GlobalEnvMap.t >-> global_env.
