From Stdlib Require Import List String Arith Lia ssreflect ssrbool Morphisms.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring utils monad_utils.
From MetaRocq.Erasure Require Import EProgram EPrimitive EAst ESpineView EEtaExpanded EInduction EGlobalEnv
  EAstUtils ELiftSubst EWellformed ECSubst EWcbvEval.

Import Kernames.
Import MRMonadNotation.

Lemma lookup_declared_constructor {Σ id mdecl idecl cdecl} :
  lookup_constructor Σ id.1 id.2 = Some (mdecl, idecl, cdecl) ->
  declared_constructor Σ id mdecl idecl cdecl.
Proof.
  rewrite /lookup_constructor /declared_constructor.
  rewrite /declared_inductive /lookup_inductive.
  rewrite /declared_minductive /lookup_minductive.
  destruct lookup_env => //=. destruct g => //=.
  destruct nth_error eqn:hn => //. destruct (nth_error _ id.2) eqn:hn' => //.
  intros [= <- <- <-]. intuition auto.
Qed.

Fixpoint lookup_inductive_assoc {A} (Σ : list (inductive × A)) (kn : inductive) {struct Σ} : option A :=
    match Σ with
    | [] => None
    | d :: tl => if kn == d.1 then Some d.2 else lookup_inductive_assoc tl kn
    end.

Equations filter_map {A B} (f : A -> option B) (l : list A) : list B :=
  | f, [] := []
  | f, x :: xs with f x := {
    | None => filter_map f xs
    | Some x' => x' :: filter_map f xs }.

Section Remap.
  Context (Σ : global_declarations).
  Context (mapping : extract_inductives).

  Definition lookup_constructor_mapping i c : option kername :=
    trs <- lookup_inductive_assoc mapping i ;;
    nth_error trs.(cstrs) c.

  Definition lookup_constructor_remapping i c args :=
    match lookup_constructor_mapping i c with
    | None => tConstruct i c args
    | Some c' => mkApps (tConst c') args
    end.

  Fixpoint it_mkLambda nas t :=
    match nas with
    | [] => t
    | na :: nas => tLambda na (it_mkLambda nas t)
    end.

  Definition make_branch '(ctx, br) :=
    match #|ctx| with
    | 0 => tLambda BasicAst.nAnon (lift 1 0 br)
    | _ => it_mkLambda ctx br
    end.

  Definition remap_case i c brs :=
    match lookup_inductive_assoc mapping (fst i) with
    | None => tCase i c brs
    | Some tr =>
        mkApps (tConst tr.(elim)) (map make_branch brs)
    end.

  Equations remap (t : term) : term :=
    | tVar na => tVar na
    | tLambda nm bod => tLambda nm (remap bod)
    | tLetIn nm dfn bod => tLetIn nm (remap dfn) (remap bod)
    | tApp fn arg => tApp (remap fn) (remap arg)
    | tConst nm => tConst nm
    | tConstruct i m args => lookup_constructor_remapping i m (map remap args)
    | tCase i mch brs =>
        let brs := map (on_snd remap) brs in
        let mch := remap mch in
        remap_case i mch brs
    | tFix mfix idx => tFix (map (map_def remap) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def remap) mfix) idx
    | tProj p bod =>
      tProj p (remap bod)
    | tPrim p => tPrim (map_prim remap p)
    | tLazy t => tLazy (remap t)
    | tForce t => tForce (remap t)
    | tRel n => tRel n
    | tBox => tBox
    | tEvar ev args => tEvar ev (map remap args).

    Definition remap_constant_decl cb :=
      {| cst_body := option_map remap cb.(cst_body) |}.

    Definition remaped_one_ind kn i (oib : one_inductive_body) : bool :=
      match lookup_inductive_assoc mapping {| inductive_mind := kn; inductive_ind := i |} with
      | None => false
      | Some trs => true
      end.

    Definition remap_inductive_decl kn idecl :=
      let remapings := mapi (remaped_one_ind kn) idecl.(ind_bodies) in
      List.forallb (fun b => b) remapings.

    Definition remap_decl d :=
      match d.2 with
      | ConstantDecl cb => Some (d.1, ConstantDecl (remap_constant_decl cb))
      | InductiveDecl idecl => if remap_inductive_decl d.1 idecl then None else Some d
      end.

    Definition remap_env Σ :=
      filter_map (remap_decl) Σ.

End Remap.

Definition remap_program mapping (p : program) : program :=
  (remap_env mapping p.1, remap mapping p.2).

From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.

Definition inductives_extraction_program :=
  (global_context × extract_inductives) × term.

Definition inductives_extraction_program_inlinings (pr : inductives_extraction_program) : extract_inductives :=
  pr.1.2.

Coercion inductives_extraction_program_inlinings : inductives_extraction_program >-> extract_inductives.

Definition extract_inductive_program mapping (p : program) : inductives_extraction_program :=
  let Σ' := remap_env mapping p.1 in
  (Σ', mapping, remap mapping p.2).

Definition forget_inductive_extraction_info (pr : inductives_extraction_program) : eprogram :=
  let '((Σ', inls), p) := pr in
  (Σ', p).

Coercion forget_inductive_extraction_info : inductives_extraction_program >-> eprogram.

Definition eval_inductives_extraction_program wfl (pr : inductives_extraction_program) := eval_eprogram wfl pr.

Axiom trust_inductive_extraction_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall inductive_extraction : extract_inductives,
  forall (input : Transform.program _ term),
  wf_eprogram efl input -> wf_eprogram efl (extract_inductive_program inductive_extraction input).
Axiom trust_inductive_extraction_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inductive_extraction (p : Transform.program _ term)
  (v : term),
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  let ip := extract_inductive_program inductive_extraction p in
  eval_eprogram wfl ip v' /\ v' = remap ip v.

Import Transform.

Program Definition extract_inductive_transformation (efl : EEnvFlags) (wfl : WcbvFlags) inductive_extraction :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_inductives_extraction_program wfl) :=
  {| name := "inductive_extraction ";
    transform p _ := extract_inductive_program inductive_extraction p ;
    pre p := wf_eprogram efl p ;
    post (p : inductives_extraction_program) := wf_eprogram efl p ;
    obseq p hp (p' : inductives_extraction_program) v v' := v' = remap p' v |}.

Next Obligation.
  now apply trust_inductive_extraction_wf.
Qed.
Next Obligation.
  now eapply trust_inductive_extraction_pres.
Qed.

#[global]
Axiom trust_inline_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inductive_extraction,
  TransformExt.t (extract_inductive_transformation efl wfl inductive_extraction)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1.1 p'.1.1).

Definition extends_inductives_extraction_eprogram (p q : inductives_extraction_program) :=
  extends p.1.1 q.1.1 /\ p.2 = q.2.

#[global]
Axiom trust_inline_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inductive_extraction,
  TransformExt.t (extract_inductive_transformation efl wfl inductive_extraction)
    extends_eprogram extends_inductives_extraction_eprogram.


Program Definition forget_inductive_extraction_info_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
      (eval_inductives_extraction_program wfl) (eval_eprogram wfl) :=
    {| name := "forgetting about inductive_extraction info";
      transform p _ := (p.1.1, p.2) ;
      pre (p : inductives_extraction_program) := wf_eprogram efl p ;
      post (p : eprogram) := wf_eprogram efl p ;
      obseq p hp p' v v' := v' = v |}.

  Next Obligation.
    destruct input as [[Σ inls] t].
    exact p.
  Qed.
  Next Obligation.
    exists v; split => //. subst p'.
    now destruct p as [[Σ inls] t].
  Qed.

#[global]
Lemma forget_inductive_extraction_info_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (forget_inductive_extraction_info_transformation efl wfl)
    (fun p p' => extends p.1.1 p'.1.1) (fun p p' => extends p.1 p'.1).
Proof.
  intros.
  red. now intros [[] ?] [[] ?]; cbn.
Qed.

#[global]
Lemma forget_inductive_extraction_info_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (forget_inductive_extraction_info_transformation efl wfl)
    extends_inductives_extraction_eprogram extends_eprogram.
Proof.
  intros ? ? [[] ?] [[] ?]; cbn.
  now rewrite /extends_inductives_extraction_eprogram /extends_eprogram /=.
Qed.
