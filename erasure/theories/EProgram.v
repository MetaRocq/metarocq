(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform config BasicAst.
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
(* From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl. *)
From MetaRocq.Erasure Require EAstUtils EWellformed EEnvMap EGlobalEnv EWcbvEval.
Import EEnvMap.

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

Import Transform.

Local Obligation Tactic := program_simpl.

Import EGlobalEnv EWellformed.

Definition inductive_mapping : Set := Kernames.inductive * (bytestring.string * list nat).
Definition inductives_mapping := list inductive_mapping.

Record extract_inductive :=
  { cstrs : list kername; (* One constant for each constructor *)
    elim : kername } (* The new eliminator *).

Definition extract_inductives := list (inductive * extract_inductive).

Definition eprogram := (EAst.global_context * EAst.term).
Definition eprogram_env := (EEnvMap.GlobalContextMap.t * EAst.term).

Import EEnvMap.GlobalContextMap (make, global_decls).

Global Arguments EWcbvEval.eval {wfl} _ _ _.

Definition wf_eprogram (efl : EEnvFlags) (p : eprogram) :=
  @wf_glob efl p.1 /\ @wellformed efl p.1 0 p.2.

Definition wf_eprogram_env (efl : EEnvFlags) (p : eprogram_env) :=
  @wf_glob efl p.1.(global_decls) /\ @wellformed efl p.1.(global_decls) 0 p.2.

Definition eval_eprogram (wfl : EWcbvEval.WcbvFlags) (p : eprogram) (t : EAst.term) :=
  ∥ EWcbvEval.eval (wfl:=wfl) p.1 p.2 t ∥.

Definition closed_eprogram (p : eprogram) :=
  closed_env p.1 && ELiftSubst.closedn 0 p.2.

Definition closed_eprogram_env (p : eprogram_env) :=
  let Σ := p.1.(global_decls) in
  closed_env Σ && ELiftSubst.closedn 0 p.2.

Definition eval_eprogram_env (wfl : EWcbvEval.WcbvFlags) (p : eprogram_env) (t : EAst.term) :=
  ∥ EWcbvEval.eval (wfl:=wfl) p.1.(global_decls) p.2 t ∥.

Import EWellformed.

Lemma wf_glob_fresh {efl : EEnvFlags} Σ : wf_glob Σ -> EnvMap.EnvMap.fresh_globals Σ.
Proof.
  induction Σ. constructor; auto.
  intros wf; depelim wf. constructor; auto.
Qed.

Module TransformExt.
  Section Opt.
    Context {env env' env'' : Type}.
    Context {term term' term'' : Type}.
    Context {value value' value'' : Type}.
    Context {eval : program env term -> value -> Prop}.
    Context {eval' : program env' term' -> value' -> Prop}.
    Context {eval'' : program env'' term'' -> value'' -> Prop}.
    Context (o : Transform.t env env' term term' value value' eval eval').
    Context (extends : program env term -> program env term -> Prop).
    Context (extends' : program env' term' -> program env' term' -> Prop).

    Class t := preserves_obs : forall p p' (pr : o.(pre) p) (pr' : o.(pre) p'),
        extends p p' -> extends' (o.(transform) p pr) (o.(transform) p' pr').

  End Opt.

  Section Comp.
    Context {env env' env'' : Type}.
    Context {term term' term'' : Type}.
    Context {value value' value'' : Type}.
    Context {eval : program env term -> value -> Prop}.
    Context {eval' : program env' term' -> value' -> Prop}.
    Context {eval'' : program env'' term'' -> value'' -> Prop}.
    Context {extends : program env term -> program env term -> Prop}.
    Context {extends' : program env' term' -> program env' term' -> Prop}.
    Context {extends'' : program env'' term'' -> program env'' term'' -> Prop}.

    Local Obligation Tactic := idtac.
    #[global]
    Instance compose (o : Transform.t env env' term term' value value' eval eval')
      (o' : Transform.t env' env'' term' term'' value' value'' eval' eval'')
      (oext : t o extends extends')
      (o'ext : t o' extends' extends'')
      (hpp : (forall p, o.(post) p -> o'.(pre) p))
      : t (Transform.compose o o' hpp) extends extends''.
    Proof. red.
      intros p p' pr pr' ext.
      eapply o'ext. now apply oext.
    Qed.

  End Comp.

End TransformExt.

Definition extends_eprogram (p p' : eprogram) :=
  extends p.1 p'.1 /\ p.2 = p'.2.

Definition extends_eprogram_env (p p' : eprogram_env) :=
  extends p.1 p'.1 /\ p.2 = p'.2.
