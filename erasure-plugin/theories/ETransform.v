(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Environment Transform config BasicAst uGraph.
From MetaRocq.Template Require Pretty Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICWeakeningEnvSN.
Set Warnings "+notation-overridden".
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureCorrectness Extract EOptimizePropDiscr
  ERemoveParams EProgram EConstructorsAsBlocks ECoInductiveToInductive.
From MetaRocq.Erasure Require Import ErasureFunction ErasureFunctionProperties.
From MetaRocq.TemplatePCUIC Require Import PCUICTransform.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform ERemoveParams.
Import EEnvMap EGlobalEnv EWellformed.

(** * Transformations of erased programs

  An [ETransform.t] is a transformation between λ□ programs, bundled with
  the properties used to compose correctness proofs of pipelines:
  - preservation of the extension of environments, and of terms under such
    extensions;
  - preservation of first-order values, with an exact [readback] of the
    first-order values of the target in the source;
  - commutation with applications, and preservation of function values.

  The predicates on programs used by these properties (environment
  extension [ext], first-order values [fo], eta-expansion [eta]) are
  indices of the record, so composition only requires them to agree. *)

Definition isFunction (t : EAst.term) :=
  EAst.isLambda t || EAstUtils.isFixApp t ||
  EAstUtils.isCoFix (EAstUtils.head t).

(** An applied cofixpoint is a function only when it lacks arguments. *)
Definition cofix_unsaturated (t : EAst.term) :=
  match EAstUtils.decompose_app t with
  | (EAst.tCoFix mfix idx, args) =>
    match nth_error mfix idx with
    | Some d => #|args| <? EAst.rarg d
    | None => false
    end
  | _ => true
  end.

Definition isFunctionS (t : EAst.term) :=
  isFunction t && cofix_unsaturated t.

Module ETransform.
Section Def.
  Context {env env' : Type}
    {eval : program env EAst.term -> EAst.term -> Prop}
    {eval' : program env' EAst.term -> EAst.term -> Prop}.
  Context {ext : program env EAst.term -> program env EAst.term -> Prop}
    {ext' : program env' EAst.term -> program env' EAst.term -> Prop}.
  Context {fo : program env EAst.term -> Prop}
    {fo' : program env' EAst.term -> Prop}.
  Context {eta : program env EAst.term -> Prop}
    {eta' : program env' EAst.term -> Prop}.

  Record t := {
    tr :> Transform.t env env' EAst.term EAst.term EAst.term EAst.term
      eval eval';
    (** Extension of environments *)
    transform_ext : forall p p' pr pr', ext p p' ->
      ext' (transform tr p pr) (transform tr p' pr');
    transform_ext_term : forall p p' pr pr', ext p p' -> p.2 = p'.2 ->
      (transform tr p pr).2 = (transform tr p' pr').2;
    (** First-order values *)
    compile_fo : forall p, pre tr p -> fo p -> program env' EAst.term;
    preserves_fo : forall p pr h, fo' (compile_fo p pr h);
    transform_fo : forall p pr h, transform tr p pr = compile_fo p pr h;
    (** Readback of first-order values *)
    readback : EAst.term -> option EAst.term;
    obseq_fo : forall p pr v v',
      fo (p.1, v) -> obseq tr p pr (transform tr p pr) v v' ->
      fo' ((transform tr p pr).1, v');
    readback_obseq : forall p pr p' v v',
      fo (p.1, v) -> obseq tr p pr p' v v' -> readback v' = Some v;
    readback_inj : forall v1 v2 x,
      readback v1 = Some x -> readback v2 = Some x -> v1 = v2;
    readback_fo : forall p pr h, readback (compile_fo p pr h).2 = Some p.2;
    (** Applications and functions *)
    transform_pre_irrel : forall p pr pr',
      transform tr p pr = transform tr p pr';
    transform_env_irrel : forall p p' pr pr', p.1 = p'.1 ->
      (transform tr p pr).1 = (transform tr p' pr').1;
    transform_etaexp : forall Σ t pr, eta (Σ, t) ->
      eta' (transform tr (Σ, t) pr);
    transform_app : forall Σ t u (pr : pre tr (Σ, EAst.tApp t u)),
      eta (Σ, t) ->
      exists prt pru,
        transform tr (Σ, EAst.tApp t u) pr =
        ((transform tr (Σ, EAst.tApp t u) pr).1,
         EAst.tApp (transform tr (Σ, t) prt).2 (transform tr (Σ, u) pru).2);
    transform_lam : forall p pr, isFunction p.2 ->
      isFunction (transform tr p pr).2;
    obseq_function : forall p pr p' v v',
      obseq tr p pr p' v v' -> isFunctionS v -> isFunctionS v' }.
End Def.
Arguments t {env env' eval eval'} ext ext' fo fo' eta eta'.

Section Ext.
  Context {env env' : Type}
    {eval : program env EAst.term -> EAst.term -> Prop}
    {eval' : program env' EAst.term -> EAst.term -> Prop}
    {ext : program env EAst.term -> program env EAst.term -> Prop}
    {ext' : program env' EAst.term -> program env' EAst.term -> Prop}
    {fo eta : program env EAst.term -> Prop}
    {fo' eta' : program env' EAst.term -> Prop}.
  Context (o : @t env env' eval eval' ext ext' fo fo' eta eta').

  (** The extension properties as [TransformExt] instances. *)
  Lemma transform_ext_inst : TransformExt.t o ext ext'.
  Proof. red. apply transform_ext. Qed.

  Lemma transform_ext_term_inst :
    TransformExt.t o (fun p p' => ext p p' /\ p.2 = p'.2)
      (fun p p' => ext' p p' /\ p.2 = p'.2).
  Proof.
    red. intros p p' pr pr' [e e2]. split.
    - now apply transform_ext.
    - now apply transform_ext_term.
  Qed.
End Ext.

Section Comp.
  Context {env env' env'' : Type}
    {eval : program env EAst.term -> EAst.term -> Prop}
    {eval' : program env' EAst.term -> EAst.term -> Prop}
    {eval'' : program env'' EAst.term -> EAst.term -> Prop}.
  Context {ext : program env EAst.term -> program env EAst.term -> Prop}
    {ext' : program env' EAst.term -> program env' EAst.term -> Prop}
    {ext'' : program env'' EAst.term -> program env'' EAst.term -> Prop}
    {fo eta : program env EAst.term -> Prop}
    {fo' eta' : program env' EAst.term -> Prop}
    {fo'' eta'' : program env'' EAst.term -> Prop}.
  Context (o : @t env env' eval eval' ext ext' fo fo' eta eta')
    (o' : @t env' env'' eval' eval'' ext' ext'' fo' fo'' eta' eta'')
    (hpp : forall p, post o p -> pre o' p).

  Definition compose_compile_fo p (pr : pre o p) (h : fo p) :=
    compile_fo o' (compile_fo o p pr h)
      (eq_rect_r (pre o') (hpp _ (correctness o p pr))
        (eq_sym (transform_fo o p pr h)))
      (preserves_fo o p pr h).

  Definition compose_readback v :=
    match readback o' v with
    | Some v' => readback o v'
    | None => None
    end.

  Local Obligation Tactic := idtac.

  Program Definition compose : t ext ext'' fo fo'' eta eta'' :=
    {| tr := Transform.compose o o' hpp;
       compile_fo := compose_compile_fo;
       readback := compose_readback |}.
  Next Obligation.
    intros p p' pr pr' e. cbn. unfold run, time.
    now apply (transform_ext o'), (transform_ext o).
  Qed.
  Next Obligation.
    intros p p' pr pr' e e2. cbn. unfold run, time.
    apply (transform_ext_term o').
    - now apply (transform_ext o).
    - now apply (transform_ext_term o).
  Qed.
  Next Obligation.
    intros p pr h. apply (preserves_fo o').
  Qed.
  Next Obligation.
    intros p pr h. cbn. unfold run, time, compose_compile_fo.
    set (cor := correctness o p pr). clearbody cor. move: cor.
    set (e := eq_sym (transform_fo o p pr h)). clearbody e.
    destruct e. cbn. intros cor.
    apply (transform_fo o').
  Qed.
  Next Obligation.
    intros p pr v v' h [v1 [obs obs']].
    eapply (obseq_fo o'); [|exact obs'].
    eapply (obseq_fo o); [exact h|exact obs].
  Qed.
  Next Obligation.
    intros p pr p' v v' h [v1 [obs obs']]. unfold compose_readback.
    rewrite (readback_obseq o' _ _ _ v1 v' _ obs').
    - eapply (obseq_fo o); [exact h|exact obs].
    - eapply (readback_obseq o); [exact h|exact obs].
  Qed.
  Next Obligation.
    intros v1 v2 x. unfold compose_readback.
    destruct (readback o' v1) as [y1|] eqn:e1 => //.
    destruct (readback o' v2) as [y2|] eqn:e2 => //.
    intros h1 h2.
    have ey := readback_inj o _ _ _ h1 h2. subst y2.
    exact (readback_inj o' _ _ _ e1 e2).
  Qed.
  Next Obligation.
    intros p pr h. unfold compose_readback, compose_compile_fo.
    rewrite (readback_fo o'). cbn.
    set (e := eq_sym (transform_fo o p pr h)). clearbody e.
    destruct e. cbn. apply (readback_fo o).
  Qed.
  Next Obligation.
    intros p pr pr'; cbn; unfold run, time.
    generalize (correctness o p pr).
    rewrite (transform_pre_irrel o p pr pr'). intros c.
    apply (transform_pre_irrel o').
  Qed.
  Next Obligation.
    intros p p' pr pr' heq; cbn; unfold run, time.
    apply (transform_env_irrel o').
    now apply (transform_env_irrel o).
  Qed.
  Next Obligation.
    intros Σ t0 pr h. cbn. unfold run, time.
    set (cr := correctness _ _ _).
    set (tro := transform o _ _) in *.
    clearbody cr. move: cr.
    assert (heq : tro = (tro.1, tro.2)) by (destruct tro; reflexivity).
    rewrite heq. intros cr.
    apply (transform_etaexp o').
    rewrite -heq. now apply (transform_etaexp o).
  Qed.
  Next Obligation.
    intros Σ t0 u pr iseta.
    destruct (transform_app o _ _ _ pr iseta) as [pr' [pr'' heq]].
    exists pr', pr''. cbn. unfold run, time.
    generalize (correctness o (Σ, EAst.tApp t0 u) pr).
    rewrite heq. intros pro'.
    cbn [fst snd].
    have irr : forall p q (e : p = q) (prp : pre o' p) (prq : pre o' q),
      transform o' p prp = transform o' q prq.
    { intros p q -> prp prq. apply (transform_pre_irrel o'). }
    have et : (transform o (Σ, EAst.tApp t0 u) pr).1 =
      (transform o (Σ, t0) pr').1 by now apply (transform_env_irrel o).
    have eu : (transform o (Σ, EAst.tApp t0 u) pr).1 =
      (transform o (Σ, u) pr'').1 by now apply (transform_env_irrel o).
    destruct (transform_app o' _ _ _ (hpp _ pro')) as [prt [pru heq']].
    { rewrite et -surjective_pairing. now apply (transform_etaexp o). }
    rewrite heq'. do 3 f_equal.
    - apply irr. now rewrite et -surjective_pairing.
    - apply irr. now rewrite eu -surjective_pairing.
  Qed.
  Next Obligation.
    intros p pr h. cbn. unfold run, time.
    now apply (transform_lam o'), (transform_lam o).
  Qed.
  Next Obligation.
    intros p pr p' v v' [v1 [obs obs']] h.
    eapply (obseq_function o'); [exact obs'|].
    eapply (obseq_function o); [exact obs|exact h].
  Qed.
End Comp.
End ETransform.

Declare Scope etransform_scope.
Bind Scope etransform_scope with ETransform.t.
Notation " o ⊳ o' " := (ETransform.compose o o' _)
  (at level 50, left associativity) : etransform_scope.
Open Scope etransform_scope.

(** Predicates used as indices of the [ETransform.t] of the passes.

  First-order values are built from constructors of inductive types which
  are not coinductive. This is stated with
  [EFirstorder.firstorder_ind_value], on blocks; before the
  constructors-as-blocks pass, on the block representation of the value. *)

Definition extends_map
  (p p' : Transform.program GlobalContextMap.t EAst.term) :=
  extends p.1 p'.1.
Definition extends_env (p p' : Transform.program E.global_context EAst.term) :=
  extends p.1 p'.1.

Definition fo_evalue
  (p : Transform.program E.global_context EAst.term) : Prop :=
  firstorder_evalue p.1 p.2 /\
  ∥ EFirstorder.firstorder_ind_value p.1
      (EConstructorsAsBlocks.compile_evalue_box p.2 []) ∥.
Definition fo_evalue_map
  (p : Transform.program GlobalContextMap.t EAst.term) : Prop :=
  firstorder_evalue p.1 p.2 /\
  ∥ EFirstorder.firstorder_ind_value p.1
      (EConstructorsAsBlocks.compile_evalue_box p.2 []) ∥.
Definition fo_evalue_block
  (p : Transform.program E.global_context EAst.term) : Prop :=
  firstorder_evalue_block p.1 p.2 /\
  ∥ EFirstorder.firstorder_ind_value p.1 p.2 ∥.

Definition is_eta_app
  (p : Transform.program E.global_context EAst.term) : Prop :=
  EEtaExpanded.isEtaExp p.1 p.2.
Definition is_eta_app_map
  (p : Transform.program GlobalContextMap.t EAst.term) : Prop :=
  EEtaExpanded.isEtaExp p.1 p.2.

Definition is_eta_fix_app
  (p : Transform.program E.global_context EAst.term) : Prop :=
  EEtaExpandedFix.isEtaExp p.1 [] p.2.
Definition is_eta_fix_app_map
  (p : Transform.program GlobalContextMap.t EAst.term) :
  Prop := EEtaExpandedFix.isEtaExp p.1 [] p.2.

(** A predicate on programs, on programs with a lookup table. *)
Definition on_map (P : Transform.program E.global_context EAst.term -> Prop)
  (p : Transform.program GlobalContextMap.t EAst.term) : Prop :=
  P (GlobalContextMap.global_decls p.1, p.2).

Lemma isLambda_mkApps_eq hd args :
  EAst.isLambda (EAst.mkApps hd args) = EAst.isLambda hd && (#|args| =? 0).
Proof.
  destruct args using rev_ind => /=.
  - now rewrite andb_true_r.
  - rewrite EAstUtils.mkApps_app length_app /= Nat.add_comm /=.
    now rewrite andb_false_r.
Qed.

(** Function values are preserved by the transformations commuting with
    applications, that keep the arity of cofixpoints. *)
Lemma isFunctionS_hom (f : EAst.term -> EAst.term) :
  (forall hd args, ~~ EAst.isApp hd ->
    EAst.isLambda hd || EAstUtils.isFix hd || EAstUtils.isCoFix hd ->
    f (EAst.mkApps hd args) = EAst.mkApps (f hd) (List.map f args)) ->
  (forall na b, EAst.isLambda (f (EAst.tLambda na b))) ->
  (forall mfix idx, EAstUtils.isFix (f (EAst.tFix mfix idx))) ->
  (forall mfix idx, f (EAst.tCoFix mfix idx) =
    EAst.tCoFix (List.map (EAst.map_def f) mfix) idx) ->
  forall t, isFunctionS t -> isFunctionS (f t).
Proof.
  intros hmk hlam hfix hcofix t.
  have napp := EAstUtils.decompose_app_notApp _ _ _
    (EAstUtils.decompose_app_head_spine t).
  rewrite -(EAstUtils.mkApps_head_spine t). move: napp.
  generalize (EAstUtils.head t) (EAstUtils.spine t) => hd l napp.
  rewrite /isFunctionS /cofix_unsaturated /isFunction /EAstUtils.isFixApp
    !EAstUtils.head_mkApps.
  rewrite !isLambda_mkApps_eq.
  rewrite EAstUtils.decompose_app_mkApps //.
  destruct hd => //=; rewrite ?andb_false_r //.
  - destruct l => //= _.
    have := hlam na hd. now destruct (f (EAst.tLambda na hd)).
  - intros _. rewrite hmk //.
    have := hfix mfix idx. destruct (f (EAst.tFix mfix idx)) => // _.
    now rewrite EAstUtils.head_mkApps EAstUtils.decompose_app_mkApps //=
      orb_true_r.
  - rewrite hmk // hcofix EAstUtils.head_mkApps
      EAstUtils.decompose_app_mkApps //=.
    rewrite nth_error_map. destruct nth_error => //=.
    now rewrite length_map orb_true_r.
Qed.


(** The same for [isFunction], for transformations that do not unfold
    cofixpoints. *)
Lemma isFunction_hom (f : EAst.term -> EAst.term) :
  (forall hd args, ~~ EAst.isApp hd ->
    EAst.isLambda hd || EAstUtils.isFix hd || EAstUtils.isCoFix hd ->
    f (EAst.mkApps hd args) = EAst.mkApps (f hd) (List.map f args)) ->
  (forall na b, EAst.isLambda (f (EAst.tLambda na b))) ->
  (forall mfix idx, EAstUtils.isFix (f (EAst.tFix mfix idx))) ->
  (forall mfix idx, EAstUtils.isCoFix (f (EAst.tCoFix mfix idx))) ->
  forall t, isFunction t -> isFunction (f t).
Proof.
  intros hmk hlam hfix hcofix t.
  have napp := EAstUtils.decompose_app_notApp _ _ _
    (EAstUtils.decompose_app_head_spine t).
  rewrite -(EAstUtils.mkApps_head_spine t). move: napp.
  generalize (EAstUtils.head t) (EAstUtils.spine t) => hd l napp.
  rewrite /isFunction /EAstUtils.isFixApp !EAstUtils.head_mkApps
    !isLambda_mkApps_eq.
  destruct hd => //=; rewrite ?andb_false_r //.
  - destruct l => //= _.
    have := hlam na hd. now destruct (f (EAst.tLambda na hd)).
  - intros _. rewrite hmk // EAstUtils.head_mkApps.
    have := hfix mfix idx. destruct (f (EAst.tFix mfix idx)) => // _.
    now rewrite /= orb_true_r.
  - intros _. rewrite hmk // EAstUtils.head_mkApps.
    have := hcofix mfix idx. destruct (f (EAst.tCoFix mfix idx)) => // _.
    now rewrite /= !orb_true_r.
Qed.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env :=
  {| wf_env_reference := {| reference_impl_env := Σ.(trans_env_env); reference_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.

Notation NormalizationIn_erase_pcuic_program_1 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p -> PCUICSN.NormalizationIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p)
       (only parsing).

Notation NormalizationIn_erase_pcuic_program_2 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p)
       (only parsing).

(* TODO: Where should this go? *)
#[local]
Lemma reference_impl_env_iter_pop_eq'
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  (wfe' := ErasureFunction.iter reference_pop (S n) (reference_impl_env wfe))
  : reference_impl_env X' = wfe'.
Proof.
  subst X' wfe'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local]
Lemma reference_impl_env_iter_pop_eq
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  : reference_impl_env X'
    = {| PCUICAst.PCUICEnvironment.universes := PCUICAst.PCUICEnvironment.universes (reference_impl_env wfe)
      ; PCUICAst.PCUICEnvironment.declarations := skipn (S n) (PCUICAst.PCUICEnvironment.declarations (reference_impl_env wfe))
      ; PCUICAst.PCUICEnvironment.retroknowledge := PCUICAst.PCUICEnvironment.retroknowledge (reference_impl_env wfe) |}.
Proof.
  subst X'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local] Lemma erase_pcuic_program_normalization_helper
  (cf := config.extraction_checker_flags) (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl} (p : global_env_ext_map)
  {normalization_in : NormalizationIn_erase_pcuic_program_1 p}
  {normalization_in_adjust_universes : NormalizationIn_erase_pcuic_program_2 p}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p ∥)
  : (let wfe := build_wf_env_from_env p.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p ∥)) in
     forall n : nat,
       n < #|PCUICAst.PCUICEnvironment.declarations p.1|
      -> forall kn cb pf,
        hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
          Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
        forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
          PCUICTyping.wf_ext Σ ->
          Σ
            ∼_ext @abstract_make_wf_env_ext extraction_checker_flags
            (@optimized_abstract_env_impl extraction_checker_flags _) wfe
            (PCUICAst.PCUICEnvironment.cst_universes cb) pf -> PCUICSN.NormalizationIn Σ)
    /\
      (let wfe := build_wf_env_from_env p.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p ∥)) in
       forall n : nat,
         n < #|PCUICAst.PCUICEnvironment.declarations p.1|
        -> let X' :=
             ErasureFunction.iter abstract_pop_decls (S n) wfe in
           forall kn cb pf,
             hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
               Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
             let Xext :=
               @abstract_make_wf_env_ext extraction_checker_flags
                 (@optimized_abstract_env_impl extraction_checker_flags _) X'
                 (PCUICAst.PCUICEnvironment.cst_universes cb) pf in
             forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
               PCUICTyping.wf_ext Σ -> Σ ∼_ext Xext -> PCUICSN.NormalizationIn Σ).
Proof.
  match goal with |- ?A /\ ?B => cut (A /\ (A -> B)); [ tauto | ] end.
  cbv beta zeta; split.
  all: cbn; intros; subst;
    repeat match goal with
      | [ H : forall x, x = _ -> _ |- _ ] => specialize (H _ eq_refl)
      | [ H : squash _ |- _ ] => destruct H
      | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
      end.
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalizationIn _ |- _ => revert H end.
    eapply normalization_in_adjust_universes; try assumption.
    cbv [PCUICSN.NormalizationIn]; cbn.
    let H := match goal with H : PCUICTyping.wf_ext _ |- _ => H end in
    rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
    [ eapply PCUICAst.NoDup_on_global_decls, H
    | eexists; eassumption ]. }
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalizationIn _ |- _ => revert H end.
    move => normalization_in.
    rewrite reference_impl_env_iter_pop_eq.
    repeat match goal with H : _ |- _ => rewrite reference_impl_env_iter_pop_eq in H end.
    eapply normalization_in_adjust_universes in normalization_in; eauto; revgoals.
    { repeat match goal with H : PCUICTyping.wf_ext _ |- _ => destruct H end;
        split; eassumption. }
    { let H := multimatch goal with H : PCUICTyping.wf_ext _ |- _ => H end in
      rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
      [ eapply PCUICAst.NoDup_on_global_decls, H
      | eexists; eassumption ]. }
    revert normalization_in.
    apply PCUICWeakeningEnvSN.weakening_env_normalization_in; eauto;
      try match goal with H : PCUICTyping.wf_ext _ |- _ => refine (@PCUICTyping.wf_ext_wf _ _ H) end.
    apply PCUICAst.PCUICEnvironment.extends_decls_extends, PCUICAst.PCUICEnvironment.strictly_extends_decls_extends_decls; split; cbn; try reflexivity.
    eauto using firstn_skipn. }
Qed.

(* Freshness of the erased environment does not depend on its
   well-formedness. *)
Lemma erase_global_deps_fresh_globals X_type deps X decls normalization_in heq :
  EnvMap.EnvMap.fresh_globals decls ->
  EnvMap.EnvMap.fresh_globals
    (@erase_global_deps X_type deps X decls normalization_in heq).1.
Proof.
  revert deps X normalization_in heq.
  induction decls; [cbn; auto|].
  - intros. constructor.
  - destruct a as [kn' d]. intros deps X nin heq H. depelim H.
    destruct d as []; simpl; destruct Kernames.KernameSet.mem.
    + cbn. constructor; [eapply IHdecls => //|].
      eapply erase_global_deps_fresh => //.
    + eapply IHdecls => //.
    + cbn. constructor; [eapply IHdecls => //|].
      eapply erase_global_deps_fresh => //.
    + eapply IHdecls => //.
Qed.

Local Obligation Tactic := program_simpl.

Program Definition erase_pcuic_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalization_in : NormalizationIn_erase_pcuic_program_1 p.1}
  {normalization_in_adjust_universes : NormalizationIn_erase_pcuic_program_2 p.1}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) wfΣ) in
  let wfext := @abstract_make_wf_env_ext _ optimized_abstract_env_impl wfe p.1.2 _ in
  let t := ErasureFunction.erase (normalization_in:=_) optimized_abstract_env_impl wfext nil p.2
    (fun Σ wfΣ => let '(sq (T; ty)) := wt in PCUICTyping.iswelltyped ty) in
  let Σ' := ErasureFunctionProperties.erase_global_fast (normalization_in:=_) optimized_abstract_env_impl
    (EAstUtils.term_global_deps t) wfe (p.1.(PCUICAst.PCUICEnvironment.declarations)) _ in
    (EEnvMap.GlobalContextMap.make Σ'.1 _, t).

Next Obligation. unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto. Defined.
Next Obligation.
  unfold erase_global_fast. erewrite erase_global_deps_fast_spec.
  eapply erase_global_deps_fresh_globals.
  Unshelve.
  - destruct wfΣ as [w]. eapply wf_fresh_globals, w.
  - unshelve edestruct erase_pcuic_program_normalization_helper;
      cbn in *; eauto.
  - cbn. now intros ? ->.
Defined.

Local Obligation Tactic := idtac.

Import Extract.

Definition erase_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalization_in normalization_in_adjust_universes}
  (wtp : ∥ wt_pcuic_program (cf:=config.extraction_checker_flags) p ∥)
  : eprogram_env :=
  @erase_pcuic_program guard p normalization_in normalization_in_adjust_universes (map_squash fst wtp) (map_squash snd wtp).

Lemma expanded_erase_program {guard : abstract_guard_impl} p {normalization_in normalization_in_adjust_universes} (wtp : ∥ wt_pcuic_program p ∥) :
  PCUICEtaExpand.expanded_pcuic_program p ->
  EEtaExpandedFix.expanded_eprogram_env (@erase_program guard p normalization_in normalization_in_adjust_universes wtp).
Proof.
  intros [etaenv etat]. split;
  unfold erase_program, erase_pcuic_program.
  eapply ErasureFunctionProperties.expanded_erase_global_fast, etaenv; try reflexivity; eauto.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  apply: (ErasureFunctionProperties.expanded_erase_fast (X_type:=optimized_abstract_env_impl)).
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  reflexivity. exact etaenv. exact etat.
Qed.

Lemma expanded_eprogram_env_expanded_eprogram_cstrs p :
  EEtaExpandedFix.expanded_eprogram_env p ->
  EEtaExpanded.expanded_eprogram_env_cstrs p.
Proof.
  move=> [] etaenv etat.
  apply /andP.
  split.
  - eapply EEtaExpanded.isEtaExpFix_env_isEtaExp_env. now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  - eapply EEtaExpanded.isEtaExpFix_isEtaExp. now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

Local Obligation Tactic := try solve [ eauto ].

Program Definition erase_transform {guard : abstract_guard_impl} : Transform.t _ _ PCUICAst.term EAst.term PCUICAst.term EAst.term
  eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=
     ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
     /\ PCUICEtaExpand.expanded_pcuic_program p
     /\ NormalizationIn_erase_pcuic_program_1 p.1
     /\ NormalizationIn_erase_pcuic_program_2 p.1 ;
   transform p hp := let nhs := proj2 (proj2 hp) in
                     @erase_program guard p (proj1 nhs) (proj2 nhs) (proj1 hp) ;
   post p := [/\ wf_eprogram_env all_env_flags p & EEtaExpandedFix.expanded_eprogram_env p];
   obseq p hp p' v v' := let Σ := p.1 in Σ ;;; [] |- v ⇝ℇ v' |}.

Next Obligation.
  cbn -[erase_program].
  intros ? p (wtp&etap&?&?).
  destruct erase_program eqn:e.
  split.
  - unfold erase_program, erase_pcuic_program in e.
    set (egf := erase_global_fast _ _ _ _ _) in e.
    set (ef := erase _ _ _ _ _) in e.
    cbn -[egf ef] in e. injection e. intros <- <-.
    have hcld := expanded_global_env_cofix_lambdas _ (proj1 etap).
    have hclt := expanded_cofix_lambdas _ _ _ (proj2 etap).
    split.
    eapply erase_global_fast_wf_glob; eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
    apply: (erase_wellformed_fast (X_type:=optimized_abstract_env_impl)); eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  - rewrite -e. cbn.
    now eapply expanded_erase_program.
Qed.

Next Obligation.
  red. move=> guard p v [[wf [T [HT1 HT2]]]]. unfold eval_pcuic_program, eval_eprogram.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; try now destruct wf; eauto.
  destruct p as [Σ t].
  intros [ev].
  destruct erase_program eqn:e.
  unfold erase_program, erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  destruct wf; cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  assert (ev' :forall Σ0 : PCUICAst.PCUICEnvironment.global_env, Σ0 = Σ' -> PCUICWcbvEval.eval Σ0 t v).
  { intros; now subst. }
  eapply (erase_correct optimized_abstract_env_impl Σ' Σ.2 _ _ _ _ _ (EAstUtils.term_global_deps _)) in ev'.
  6:{ erewrite <- erase_global_deps_fast_spec. reflexivity. }
  2:{ exact (expanded_global_env_cofix_lambdas _ (proj1 T)). }
  2:{ exact (expanded_cofix_lambdas _ _ _ (proj2 T)). }
  all:trea.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev' as [v' [he [hev]]]. exists v'; split => //.
  red. cbn.
  sq. exact hev. Unshelve.
  { intros; cbn in *.
    subst Σ'.
    multimatch goal with
    | [ H : _ |- _ ] => eapply H
    end; try eassumption;
    rewrite reference_impl_env_iter_pop_eq;
    repeat match goal with H : _ |- _ => rewrite reference_impl_env_iter_pop_eq in H end;
    assumption. }
  cbn; intros. sq. now subst.
Qed.

(** Typed erasure variant, using erasure but also keeping type information useful for later optimizations,
    e.g., de-arging. *)

Definition typed_erasure_pre (p : pcuic_program) :=
  ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
  /\ PCUICEtaExpand.expanded_pcuic_program p
  /\ NormalizationIn_erase_pcuic_program_1 p.1
  /\ NormalizationIn_erase_pcuic_program_2 p.1.

From MetaRocq.Erasure.Typed Require Import Erasure ExAst Optimize ExtractionCorrectness OptimizeCorrectness.
From MetaRocq.Erasure Require Import EWellformed.
From MetaRocq.PCUIC Require Import PCUICTyping.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
Set Equations Transparent.
Equations? erase_program_typed guard (p : pcuic_program) (pre : typed_erasure_pre p) : ExAst.global_env * EAst.term :=
 erase_program_typed guard p pre :=
  let wfΣ : ∥ wf_ext p.1 ∥ := _ in
  let X := PCUICWfEnvImpl.build_wf_env_from_env p.1 (map_squash fst wfΣ) in
  let t' := erase_term wfΣ p.2 _ in
  (erase_global_decls_deps_recursive
    (X_type := PCUICWfEnvImpl.optimized_abstract_env_impl (guard := guard))
    (X := X) (PEnv.declarations p.1) (PEnv.universes p.1) (PEnv.retroknowledge p.1)
    (fun Σ' eq => _)
    (EAstUtils.term_global_deps t') (fun _ => false), t').
Proof.
  - destruct pre0. destruct H. destruct X. now sq.
  - destruct pre0 as [[[wf []]] _]. now eexists.
  - cbn in eq. rewrite eq. clear; destruct p.1; cbn in *.
    set(x := eval_eprogram_env).
    destruct g; cbn in *.
    now destruct trans_env_env; cbn.
Qed.

Definition trans_ex_prog (p : ExAst.global_env * EAst.term) : EAst.global_context * EAst.term :=
  (ExAst.trans_env p.1, p.2).

Definition eval_typed_eprogram fl :=
  (fun p v => ∥ @EWcbvEval.eval fl (ExAst.trans_env p.1) p.2 v ∥).

Program Definition typed_erase_transform (guard := fake_guard_impl_instance) :
  Transform.t _ _ PCUICAst.term EAst.term PCUICAst.term EAst.term
  eval_pcuic_program (eval_typed_eprogram EWcbvEval.default_wcbv_flags) :=
 {| name := "typed erasure";
    pre p :=
     ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
     /\ PCUICEtaExpand.expanded_pcuic_program p
     /\ NormalizationIn_erase_pcuic_program_1 p.1
     /\ NormalizationIn_erase_pcuic_program_2 p.1 ;
   transform p hp := erase_program_typed guard p hp ;
   post p := [/\ wf_eprogram all_env_flags (trans_ex_prog p) &
     EEtaExpandedFix.expanded_eprogram (trans_ex_prog p)];
   obseq p hp p' v v' := let Σ := p.1 in Σ ;;; [] |- v ⇝ℇ v' |}.

Next Obligation.
  cbn -[erase_program].
  intros p (wtp&etap&?&?).
  have hcld := expanded_global_env_cofix_lambdas _ (proj1 etap).
  have hclt := expanded_cofix_lambdas _ _ _ (proj2 etap).
  unfold cofix_lambdas_env in hcld.
  destruct erase_program_typed eqn:e.
  split.
  - unfold erase_program_typed, erase_pcuic_program in e.
    set (egf := erase_global_decls_deps_recursive _ _ _ _ _ _) in e.
    unfold erase_term in e.
    set (ef := erase _ _ _ _ _) in e.
    cbn -[egf ef] in e. injection e. intros <- <-. clear e.
    unfold trans_ex_prog in *.
    split.
    now eapply wf_erase_global_decls_recursive.
    cbn [fst snd].
    eapply extends_wellformed.
    now eapply wf_erase_global_decls_recursive.
    2:unshelve eapply (erase_wellformed_weaken (PEnv.declarations p.1) _ _ _ (Γ:=[])); tea.
    4:exact KernameSet.empty.
    2:{ intros. now eapply Erasure.fake_normalization. }
    2:{ abstract (cbn; destruct p; destruct g; cbn; congruence). }
    rewrite erase_global_deps_erase_global.
    eapply trans_env_erase_global_decls; eauto.
    intros kn hin. rewrite KernameSet.union_spec in hin. destruct hin; [knset|].
    unfold erase_term.
    match goal with
    | [ H : context [@erase ?X_type ?X ?nin ?G ?t ?wt ] |- context [ @erase ?X_type' ?X' ?nin' ?G' ?t' ?wt' ] ] =>
      rewrite -(@erase_irrel_global_env X_type X nin X_type' X' nin' G t wt wt'); eauto
    end.
    red. cbn. intros; subst; intuition eauto.
    destruct wtp. eapply wf_fresh_globals, w.
  - move: e. rewrite /erase_program_typed.
    intros [= <- <-]. unfold trans_ex_prog; cbn -[trans_env].
    red. split; cbn -[trans_env].
    eapply expanded_erase_global_decls_recursive; eauto. eapply etap.
    eapply expanded_erase => //; eauto. eapply etap. eapply etap.
Qed.

Next Obligation.
  intros guard.
  set (cf := extraction_checker_flags).
  cbn. red.
  move=> p v [[wf [T [HT1 HT2]]]]. unfold eval_pcuic_program, eval_typed_eprogram.
  have hcld := expanded_global_env_cofix_lambdas _ (proj1 T).
  have hclt := expanded_cofix_lambdas _ _ _ (proj2 T).
  unfold cofix_lambdas_env in hcld.
  unfold erase_program_typed.
  set (er := erase_global_decls_deps_recursive _ _ _ _ _ _).
  set (et := erase_term _ _ _).
  unshelve edestruct (erase_pcuic_program_normalization_helper); cbn in *; try now destruct wf; eauto.
  destruct p as [Σ t].
  intros [ev].
  cbn in ev. clear H0.
  unfold erase_term, make_env in et.
  set (e := abstract_make_wf_env_ext _ _ _) in *.
  cbn [fst snd] in et.
  pose proof (abstract_env_ext_exists e) as [[Σe he]].
  match goal with
  [H := context [ @erase ?X_type ?X ?nin ?Γ t ?wt ] |- _ ] =>
   pose proof (@erases_erase X_type X nin Γ t wt _ he hclt)
  end.
  cbn in he. subst Σe. destruct Σ as [Σ univs]; cbn [fst snd] in *.
  assert (wv : welltyped (Σ, univs) [] v).
  { destruct wf. destruct s. eexists. eapply PCUICClassification.subject_reduction_eval; tea. }
  eapply ErasureCorrectness.erases_correct with (Σ := (trans_env_env Σ, univs)) (Σ' := trans_env er) in ev as (erv&erase_to&[erev]);eauto.
  - apply wf.
  - destruct wf. destruct s; now eexists.
  - destruct wf as [wf []]. eapply erase_global_erases_deps; tea.
    subst er.
    set (obl := fun Σ' => _).
    set (obl' := fun Σ' => _).
    destruct Σ. destruct trans_env_env. cbn -[build_wf_env_from_env e] in *.
    eapply (ErasureCorrectness.erase_global_decls_deps_recursive_correct _ _ _ _); eauto.
    intros k hin.
    eapply term_global_deps_spec in hin; tea. red in hin. destruct hin as [[decl eq]].
    cbn in eq. cbn. now rewrite eq. cbn. eapply wf.
Qed.

(** De-arging requires first the removal of match-on-box which allows getting rid of all
  dependencies on propositional inductive types. *)
Import EOptimizePropDiscr OptimizePropDiscr EWcbvEval.

Definition remove_match_on_box_typed_env m (Σ : global_env) :=
  map (on_snd (remove_match_on_box_decl m)) Σ.

Definition map_of_typed_global_env (p : global_env) (fr : fresh_globals p) :=
  GlobalContextMap.make (trans_env p) (OptimizePropDiscr.remove_match_on_box_env_obligation_1 p fr).

Definition pre_remove_match_on_box_typed efl (p : global_env * term) : Prop :=
  wf_eprogram efl (trans_ex_prog p) /\ EEtaExpandedFix.expanded_eprogram (trans_ex_prog p).

Lemma fresh_global_trans kn g : EnvMap.EnvMap.fresh_global kn (trans_env g) -> fresh_global kn g.
Proof.
  induction g as [ | [[kn' b] d] tl]; cbn; auto; constructor; eauto.
  - now depelim H.
  - depelim H. eapply Forall_map_inv in H0. ELiftSubst.solve_all.
Qed.

Lemma pre_remove_match_on_box_typed_fresh efl p : pre_remove_match_on_box_typed efl p -> fresh_globals p.1.
Proof.
  intros []. destruct H. eapply wf_glob_fresh in H.
  revert H. clear.
   destruct p; cbn. clear.
  intros h; depind h.
  - destruct g; noconf H. constructor.
  - destruct g0; noconf H0. destruct p as [[kn' b] d'].
    constructor; eauto. now eapply fresh_global_trans.
Qed.

Lemma map_trans_env Σ m : map (on_snd (EOptimizePropDiscr.remove_match_on_box_decl m)) (trans_env Σ) = trans_env (map (on_snd (OptimizePropDiscr.remove_match_on_box_decl m)) Σ).
Proof.
  induction Σ; cbn => //=.
  destruct a as [[kn b] d]; cbn. f_equal.
  unfold on_snd. cbn. f_equal. destruct d => //. destruct o => //.
  now apply IHΣ.
Qed.

Definition remove_match_on_box_program_typed efl (p : global_env * term) (pre : pre_remove_match_on_box_typed efl p) : global_env * term :=
  let m := map_of_typed_global_env p.1 (pre_remove_match_on_box_typed_fresh efl p pre) in
  (remove_match_on_box_typed_env m p.1, EOptimizePropDiscr.remove_match_on_box m p.2).
Import EOptimizePropDiscr.

Program Definition remove_match_on_box_typed_transform {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _  EAst.term EAst.term _ _ (eval_typed_eprogram fl) (eval_typed_eprogram (disable_prop_cases fl)) :=
  {| name := "optimize_prop_discr";
    transform p pr := remove_match_on_box_program_typed efl p pr ;
    pre p := pre_remove_match_on_box_typed efl p;
    post p := pre_remove_match_on_box_typed efl p;
    obseq p hp p' v v' := v' = EOptimizePropDiscr.remove_match_on_box (map_of_typed_global_env p.1 (pre_remove_match_on_box_typed_fresh efl p hp)) v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - cbn in *. unfold trans_ex_prog in *. cbn [fst snd] in *.
    unfold remove_match_on_box_program_typed; cbn [fst snd].
    cbn.
    rewrite trans_env_remove_match_on_box_env.
    split.
    + eapply remove_match_on_box_env_wf => //.
      cbn. eapply wfp.
    + cbn -[remove_match_on_box_env].
      rewrite /map_of_typed_global_env.
      set (obl := trans_env_fresh_globals _ _).
      set (obl' := OptimizePropDiscr.remove_match_on_box_env_obligation_1 _ _).
      assert (obl = obl') by apply proof_irrelevance. clearbody obl obl'; subst obl'.
      eapply remove_match_on_box_wellformed_irrel. cbn. eapply wfp.
      eapply remove_match_on_box_wellformed => //=. apply wfp. apply wfp.
  - rewrite /trans_ex_prog /= /remove_match_on_box_typed_env. cbn.
    rewrite -map_trans_env. unfold trans_ex_prog in *. cbn -[trans_env] in *.
    set (e' := map_of_typed_global_env _ _).
    eapply (remove_match_on_box_program_expanded_fix (e', t) wfp).
    unfold e'. unfold map_of_typed_global_env. red. cbn. eapply etap.
Qed.

Next Obligation.
  red. move=> fl wcon efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  cbn -[trans_env] in ev.
  unfold eval_typed_eprogram, remove_match_on_box_program_typed. cbn -[trans_env].
  set (obl := pre_remove_match_on_box_typed_fresh _ _ _).
  eapply (EOptimizePropDiscr.remove_match_on_box_correct (Σ := map_of_typed_global_env _ obl) t v) in ev; cbn -[trans_env]; eauto.
  eexists; split => //. rewrite -map_trans_env. now sq.
  apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
  Unshelve. eauto.
Qed.

Record dearging_config :=
  { overridden_masks : kername -> option bitmask;
    do_trim_const_masks : bool;
    do_trim_ctor_masks : bool }.

Definition check_dearging_precond (cf : dearging_config) Σ t :=
  if closed_env (trans_env Σ) then
    match ExtractionCorrectness.compute_program_masks cf.(overridden_masks)
      cf.(do_trim_const_masks) cf.(do_trim_ctor_masks) Σ t with
    | ResultMonad.Ok masks =>
      if valid_cases (ind_masks masks) t && is_expanded (ind_masks masks) (const_masks masks) t then Some masks else None
    | _ => None
    end
  else None.

Lemma check_dearging_precond_spec cf env t d :
  check_dearging_precond cf env t = Some d ->
  closed_env (trans_env env) /\
  valid_masks_env (ind_masks d) (const_masks d) env /\
  is_expanded_env (ind_masks d) (const_masks d) env /\
  valid_cases (ind_masks d) t
  /\ is_expanded (ind_masks d) (const_masks d) t.
Proof.
  unfold check_dearging_precond.
  destruct closed_env => //.
  unfold ExtractionCorrectness.compute_program_masks, Utils.timed.
  destruct analyze_program eqn:eqm => //.
  destruct is_expanded_env eqn:isex => //.
  destruct valid_masks_env eqn:vm => //=.
  destruct valid_cases eqn:vc => //=.
  destruct is_expanded eqn:ise => //=.
  intros [= <-]; cbn; intuition.
Qed.

Definition check_dearging_trans cf p :=
  ((check_dearging_precond cf p.1 p.2, p.1), p.2).

Definition eval_typed_eprogram_masks fl :=
  (fun (p : (option dearg_set * global_env) * term) v => ∥ @EWcbvEval.eval fl (ExAst.trans_env p.1.2) p.2 v ∥).

Definition post_dearging_checks efl cf (p : (option dearg_set × global_env) × term) :=
  (p.1.1 = check_dearging_precond cf p.1.2 p.2) /\
  wf_eprogram efl (trans_env p.1.2, p.2) /\ EEtaExpandedFix.expanded_eprogram (trans_env p.1.2, p.2).

Program Definition dearging_checks_transform {efl : EEnvFlags} cf {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_typed_eprogram opt_wcbv_flags) (eval_typed_eprogram_masks opt_wcbv_flags) :=
  {| name := "dearging";
    transform p _ := check_dearging_trans cf p ;
    pre p := pre_remove_match_on_box_typed efl p;
    post := post_dearging_checks efl cf;
    obseq p hp p' v v' := v' = v |}.
Next Obligation.
  cbn. intros. split => //.
Qed.
Next Obligation.
  cbn. intros. red. cbn. intros. exists v; split => //.
Qed.

Section Dearging.
  Import Optimize OptimizeCorrectness.

  Definition dearg (p : (option dearg_set × global_env) * term) : global_context * term :=
    match p.1.1 with
    | Some masks => (trans_env (dearg_env masks p.1.2), dearg_term masks p.2)
    | None => (trans_env p.1.2, p.2)
    end.

  Program Definition dearging_transform (efl := all_env_flags) cf :
    Transform.t _ _  EAst.term EAst.term _ _ (eval_typed_eprogram_masks opt_wcbv_flags) (eval_eprogram opt_wcbv_flags) :=
    {| name := "dearging";
      transform p _ := dearg p ;
      pre p := post_dearging_checks efl cf p;
      post p := wf_eprogram efl p /\ EEtaExpandedFix.expanded_eprogram p ;
      obseq p hp p' v v' := v' = (dearg (p.1, v)).2 |}.

  Next Obligation.
  Proof.
    cbn. intros.
    unfold dearg.
    destruct p. rewrite H.
    destruct check_dearging_precond eqn:eqp; cbn => //.
    destruct input as [[masks env] t]. cbn -[trans_env Optimize.dearg_env] in *.
    subst masks. destruct H0 as [wf exp].
    eapply check_dearging_precond_spec in eqp. intuition.
    - split; cbn.
      unfold dearg_env.
      eapply wf_glob_debox.
      eapply wf_glob_dearg; eauto.
      eapply wf.
      rewrite /dearg_env. rewrite -trans_env_debox.
      eapply wellformed_dearg; eauto.
      eapply wf.
    - rewrite /dearg_env -trans_env_debox. split; cbn.
      eapply expanded_dearg_env; tea. apply exp.
      eapply EEtaExpandedFix.isEtaExp_expanded, expanded_dearg; eauto.
      apply EEtaExpandedFix.expanded_isEtaExp, exp.
  Qed.

  Next Obligation.
    cbn. intros. red.
    intros p v [he [wfe exp]]. unfold eval_typed_eprogram_masks.
    intros [ev].
    unfold dearg. rewrite he.
    destruct (check_dearging_precond) as [masks|] eqn:cpre.
    * have hspec := check_dearging_precond_spec _ _ _ _ cpre.
      eapply (extract_program_correct _ _ _ masks cf.(overridden_masks)
        cf.(do_trim_const_masks) cf.(do_trim_ctor_masks)) in ev as ev'.
      destruct ev' as [ev'].
      eexists. split. red. sq. cbn. exact ev'. auto.
      - destruct wfe. now eapply wellformed_closed_env.
      - destruct wfe. now eapply wellformed_closed.
      - move: cpre. unfold check_dearging_precond. destruct closed_env => //.
        destruct ExtractionCorrectness.compute_program_masks => //.
        destruct (_ && _) => //. congruence.
      - apply hspec.
      - apply hspec.
    * exists v. cbn. split => //.
  Qed.

End Dearging.


Section PCUICEnv. (* Locally reuse the short names for PCUIC environment handling *)
Import PCUICAst.PCUICEnvironment.

Lemma build_wf_env_from_env_eq {cf : checker_flags} (guard : abstract_guard_impl) (Σ : global_env_ext_map) (wfΣ : ∥ PCUICTyping.wf_ext Σ ∥) :
  let wfe := build_wf_env_from_env Σ (map_squash (PCUICTyping.wf_ext_wf Σ) wfΣ) in
  forall Σ' : global_env, Σ' ∼ wfe -> declarations Σ' = declarations Σ.
Proof.
  cbn; intros. rewrite H. reflexivity.
Qed.

Definition extends_global_env (Σ Σ' : global_env_ext_map) :=
  [/\ (forall kn decl, lookup_env Σ kn = Some decl ->lookup_env Σ' kn = Some decl),
      Σ.(universes) = Σ'.(universes), Σ.2 = Σ'.2 & Σ.(retroknowledge) = Σ'.(retroknowledge)].

Definition extends_pcuic_program (p p' : pcuic_program) :=
  extends_global_env p.1 p'.1 /\ p.2 = p'.2.
Import ErasureFunction.
Import PCUICAst.

Lemma strictly_extends_lookups {cf:checker_flags} (X X' : wf_env) (Σ Σ' : global_env) :
  (forall (kn : kername) (decl decl' : global_decl), lookup_env Σ' kn = Some decl -> lookup_env Σ kn = Some decl' -> decl = decl') ->
  retroknowledge Σ = retroknowledge Σ' ->
  strictly_extends_decls X Σ -> strictly_extends_decls X' Σ' ->
  PCUICTyping.wf Σ -> PCUICTyping.wf Σ' ->
  equiv_env_inter X' X.
Proof.
  intros hl hr [] [] wf wf'.
  split.
  - intros kn d.
    unfold lookup_env in *.
    destruct s as [? eq], s0 as [? eq'].
    rewrite eq' eq in hl.
    intros decl' hl' hl''.
    specialize (hl kn d decl').
    eapply wf_fresh_globals in wf.
    eapply wf_fresh_globals in wf'.
    rewrite eq in wf; rewrite eq' in wf'.
    eapply lookup_global_app_wf in hl'; tea.
    eapply lookup_global_app_wf in hl''; tea.
    eauto.
  - rewrite /primitive_constant. now rewrite e0 e2 hr.
Qed.


Lemma lookup_env_In_map_fst Σ kn decl : EGlobalEnv.lookup_env Σ kn = Some decl -> In kn (map fst Σ).
Proof.
  induction Σ; cbn => //.
  case: eqb_spec.
  + intros -> [= <-]. now left.
  + intros _ hl. eauto.
Qed.

End PCUICEnv.

#[local] Obligation Tactic := idtac.

(** Optional transformations *)

Program Definition optional_transform {env env' term term' value value' eval eval'} (activate : bool)
  (tr : Transform.t env env' term term' value value' eval eval') :
  if activate then Transform.t env env' term term' value value' eval eval'
  else Transform.t env env term term value value eval eval :=
  if activate return if activate then Transform.t env env' term term' value value' eval eval'
  else Transform.t env env term term value value eval eval
  then tr
  else
  {| name := ("skipped " ^ tr.(name));
     transform p pr := p;
     pre := tr.(pre) ;
     post := tr.(pre) ;
     obseq p hp p' v v' := v' = v |}.
Next Obligation.
  intros. cbn. exact p.
Defined.
Next Obligation.
 cbn. intros. red. intros. exists v. split => //.
Defined.

Program Definition optional_self_transform {env term eval} (activate : bool)
  (tr : Transform.self_transform env term eval eval) :
  Transform.self_transform env term eval eval :=
  if activate return Transform.self_transform env term eval eval
  then tr
  else
  {| name := ("skipped " ^ tr.(name));
     transform p pr := p;
     pre := tr.(pre) ;
     post := tr.(pre) ;
     obseq p hp p' v v' := v' = v |}.
Next Obligation.
  intros. cbn. exact p.
Defined.
Next Obligation.
 cbn. intros. red. intros. exists v. split => //.
Defined.

#[global]
Instance optional_self_transformation_ext {env term eval} activate tr extends :
  TransformExt.t tr extends extends ->
  TransformExt.t (@optional_self_transform env term eval activate tr) extends extends.
Proof.
  red; intros. destruct activate; cbn in * => //. now apply H.
Qed.

Section OptionalETransform.
Local Obligation Tactic := idtac.
Context {env : Type}
  {eval : Transform.program env EAst.term -> EAst.term -> Prop}
  {ext : Transform.program env EAst.term -> Transform.program env EAst.term ->
    Prop}
  {fo eta : Transform.program env EAst.term -> Prop}.

(** An optional pass; when it is not activated, the readback is the
    identity. *)
Program Definition optional_etransform (b : bool)
  (o : @ETransform.t env env eval eval ext ext fo fo eta eta) :
  ETransform.t ext ext fo fo eta eta :=
  {| ETransform.tr := optional_self_transform b (ETransform.tr o);
     ETransform.compile_fo p :=
       match b return pre (optional_self_transform b (ETransform.tr o)) p ->
         fo p -> _ with
       | true => ETransform.compile_fo o p
       | false => fun _ _ => p
       end;
     ETransform.readback := if b then ETransform.readback o else Some |}.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_ext|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_ext_term|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.preserves_fo|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_fo|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.obseq_fo|].
  intros p pr v v' h e. now subst v'.
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.readback_obseq|].
  intros p pr p' v v' h e. now subst v'.
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.readback_inj|]. congruence.
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.readback_fo|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_pre_irrel|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_env_irrel|].
  now intros [] [] pr pr' ->.
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_etaexp|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_app|].
  intros Σ t u pr h.
  destruct (ETransform.transform_app o Σ t u pr h) as [prt [pru _]].
  now exists prt, pru.
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.transform_lam|now intros].
Qed.
Next Obligation.
  intros [] o; cbn; [apply ETransform.obseq_function|].
  intros p pr p' v v' e. now subst v'.
Qed.
End OptionalETransform.
