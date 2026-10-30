From Stdlib Require Import List.
From Stdlib Require Import String.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst EProgram.

Definition map_subterms (f : term -> term) (t : term) : term :=
  match t with
  | tEvar n ts => tEvar n (map f ts)
  | tLambda na body => tLambda na (f body)
  | tLetIn na val body => tLetIn na (f val) (f body)
  | tApp hd arg => tApp (f hd) (f arg)
  | tCase p disc brs =>
    tCase p (f disc) (map (on_snd f) brs)
  | tProj p t => tProj p (f t)
  | tFix def i => tFix (map (map_def f) def) i
  | tCoFix def i => tCoFix (map (map_def f) def) i
  | tPrim p => tPrim (map_prim f p)
  | tLazy t => tLazy (f t)
  | tForce t => tForce (f t)
  | tConstruct ind n args => tConstruct ind n (map f args)
  | tRel n => tRel n
  | tVar na => tVar na
  | tConst kn => tConst kn
  | tBox => tBox
  end.

Section betared.

  Fixpoint beta_body (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
        match body with
        | tLambda na body => beta_body (body{0 := a}) args
        | _ => mkApps body (a :: args)
        end
    end.

  Fixpoint betared_aux (args : list term) (t : term) : term :=
    match t with
    | tApp hd arg => betared_aux (betared_aux [] arg :: args) hd
    | tLambda na body =>
      let b := betared_aux [] body in
      beta_body (tLambda na b) args
    | t => mkApps (map_subterms (betared_aux []) t) args
    end.

  Definition betared : term -> term := betared_aux [].

  Definition betared_in_constant_body cst :=
    {| cst_body := option_map betared (cst_body cst); |}.

  Definition betared_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (betared_in_constant_body cst)
    | _ => d
    end.

End betared.

Definition betared_env (Σ : global_declarations) : global_declarations :=
  map (fun '(kn, decl) => (kn, betared_in_decl decl)) Σ.

Definition betared_program (p : program) : program :=
  (betared_env p.1, betared p.2).

From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.

Axiom trust_betared_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall (input : Transform.program _ term),
  wf_eprogram efl input -> wf_eprogram efl (betared_program input).
Axiom trust_betared_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ term)
  (v : term),
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  eval_eprogram wfl (betared_program p) v' /\ v' = betared v.

Import Transform.

Program Definition betared_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "betared ";
    transform p _ := betared_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram efl p ;
    obseq p hp p' v v' := v' = betared v |}.

Next Obligation.
  now apply trust_betared_wf.
Qed.
Next Obligation.
  now eapply trust_betared_pres.
Qed.

Import EProgram EGlobalEnv.

#[global]
Axiom betared_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (betared_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).

#[global]
Axiom betared_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (betared_transformation efl wfl)
    extends_eprogram extends_eprogram.


