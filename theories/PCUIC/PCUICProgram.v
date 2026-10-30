(** * Definition of programs in template-rocq, well-typed terms and provided transformations **)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config EnvMap.
From MetaRocq.PCUIC Require Import PCUICAstUtils PCUICAst PCUICGlobalEnv PCUICTyping.

(** Global environment with a map for efficient lookups *)

Record global_env_map :=
  { trans_env_env :> global_env;
    trans_env_map : EnvMap.t global_decl;
    trans_env_repr : EnvMap.repr trans_env_env.(declarations) trans_env_map }.

Program Definition build_global_env_map (g : global_env) : global_env_map :=
  {| trans_env_env := g;
     trans_env_map := EnvMap.EnvMap.of_global_env g.(declarations) |}.

Definition global_env_ext_map := global_env_map * universes_decl.

Definition pcuic_program : Type := global_env_ext_map * term.

Definition global_env_ext_map_global_env_ext (g : global_env_ext_map) : global_env_ext :=
  (trans_env_env (fst g), g.2).
Coercion global_env_ext_map_global_env_ext : global_env_ext_map >-> global_env_ext.

Definition global_env_ext_map_global_env_map : global_env_ext_map -> global_env_map := fst.
Coercion global_env_ext_map_global_env_map : global_env_ext_map >-> global_env_map.

(* A well-typed PCUIC program consists of a well-formed environment and term *)

Definition wt_pcuic_program {cf : checker_flags} (p : pcuic_program) :=
  wf_ext p.1 × ∑ T, typing p.1 [] p.2 T.

Module TransLookup.
  Definition lookup_minductive (Σ : global_env_map) mind :=
    match EnvMap.lookup mind Σ.(trans_env_map) with
    | Some (InductiveDecl decl) => Some decl
    | _ => None
    end.

  Definition lookup_inductive Σ ind :=
    match lookup_minductive Σ (inductive_mind ind) with
    | Some mdecl =>
      match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
      | Some idecl => Some (mdecl, idecl)
      | None => None
      end
    | None => None
    end.
End TransLookup.
