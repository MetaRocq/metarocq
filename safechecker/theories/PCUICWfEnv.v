(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph EnvMap.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec.

Definition level_mem : global_env_ext -> Level.t -> bool
  := fun X l => LevelSet.mem l (global_ext_levels X).

Definition on_global_decls {cf:checker_flags} Σ :=
  on_global_decls_data cumulSpec0 (lift_typing typing) (cf:=cf) Σ.(universes) Σ.(retroknowledge) Σ.(declarations).

Class abstract_env_struct {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl : Type) := {
  (* This part of the structure is here to state the correctness properties *)

  abstract_env_rel : abstract_env_impl -> global_env -> Prop;
  abstract_env_ext_rel : abstract_env_ext_impl -> global_env_ext -> Prop;

  (* Operations on the environment *)

  abstract_env_init (cs:ContextSet.t) (retro : Retroknowledge.t) : on_global_univs cs -> abstract_env_impl;
  abstract_env_add_decl X (kn:kername) (d:global_decl) :
   (forall Σ, abstract_env_rel X Σ -> ∥ on_global_decls Σ kn d ∥)
   -> abstract_env_impl;
  abstract_env_add_udecl X udecl :
    (forall Σ, abstract_env_rel X Σ -> ∥ on_udecl Σ.(universes) udecl ∥) ->
    abstract_env_ext_impl ;
  abstract_pop_decls : abstract_env_impl -> abstract_env_impl ;

  (* Queries on the environment *)

  abstract_env_lookup : abstract_env_ext_impl -> kername -> option global_decl;
  abstract_primitive_constant : abstract_env_ext_impl -> Primitive.prim_tag -> option kername;

  (* Primitive decision procedures *)
  abstract_env_level_mem : abstract_env_ext_impl -> Level.t -> bool;
  abstract_env_check : abstract_env_ext_impl -> UnivConstraint.t -> bool;
  abstract_env_guard : abstract_env_ext_impl -> FixCoFix -> context -> mfixpoint term -> bool;
  abstract_env_is_consistent : abstract_env_impl -> LevelSet.t * UnivConstraintSet.t -> bool ;

}.

Definition abstract_env_fixguard  {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) := abstract_env_guard X Fix.

Definition abstract_env_cofixguard  {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) := abstract_env_guard X CoFix.

Definition abstract_env_compare_universe {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : conv_pb -> Universe.t -> Universe.t -> bool :=
  check_cmpb_universe_gen (abstract_env_check X).

Definition abstract_env_compare_sort {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) : conv_pb -> sort -> sort -> bool :=
    check_cmpb_sort_gen (abstract_env_check X).

Definition abstract_env_check_constraints {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) : UnivConstraintSet.t -> bool :=
    check_constraints_gen (abstract_env_check X).

Definition abstract_env_ext_wf_universeb {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : Universe.t -> bool :=
    fun (u : Universe.t) => LevelExprSet.for_all (fun l => abstract_env_level_mem X (LevelExpr.get_level l)) u.

Definition abstract_env_ext_wf_sortb {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : sort -> bool :=
    Sort.on_sort (abstract_env_ext_wf_universeb X) true.

Definition abstract_env_level_mem' {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : LevelSet.t -> Level.t -> bool :=
    fun levels l => LevelSet.mem l levels || abstract_env_level_mem X l.

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl: Type)
  `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl} : Prop := {

  abstract_env_ext_exists X : ∥ ∑ Σ , abstract_env_ext_rel X Σ ∥;
  abstract_env_ext_wf X {Σ} : abstract_env_ext_rel X Σ -> ∥ wf_ext Σ ∥ ;
  abstract_env_ext_irr X {Σ Σ'} :
      abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ' ->  Σ = Σ';

  abstract_env_exists X : ∥ ∑ Σ , abstract_env_rel X Σ ∥;
  abstract_env_wf X {Σ} : abstract_env_rel X Σ -> ∥ wf Σ ∥;
  abstract_env_irr X {Σ Σ'} :
    abstract_env_rel X Σ -> abstract_env_rel X Σ' ->  Σ = Σ';

  abstract_env_init_correct univs retro cuniv :
    abstract_env_rel (abstract_env_init univs retro cuniv)
    {| universes := univs; declarations := []; retroknowledge := retro |} ;
  abstract_env_add_decl_correct X Σ kn d H : abstract_env_rel X Σ ->
    abstract_env_rel (abstract_env_add_decl X kn d H) (add_global_decl Σ (kn,d));
  abstract_env_add_udecl_rel X {Σ} udecl H :
    (abstract_env_rel X Σ.1 /\ Σ.2 = udecl) <->
    abstract_env_ext_rel (abstract_env_add_udecl X udecl H) Σ;
  abstract_pop_decls_correct X decls (prf : forall Σ : global_env, abstract_env_rel X Σ ->
            exists d, Σ.(declarations) = d :: decls) :
    let X' := abstract_pop_decls X in
    forall Σ Σ', abstract_env_rel X Σ -> abstract_env_rel X' Σ' ->
                      Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\
                      Σ.(retroknowledge) = Σ'.(retroknowledge);

  abstract_env_lookup_correct X {Σ} kn decl : abstract_env_ext_rel X Σ ->
      In (kn, decl) (declarations Σ) <-> abstract_env_lookup X kn = Some decl ;

  abstract_env_check_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ):
    check_spec (global_ext_uctx Σ) (abstract_env_check X);
  abstract_env_level_mem_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) l:
    LevelSet.In l (global_ext_levels Σ) <-> abstract_env_level_mem X l;
  abstract_env_is_consistent_correct X Σ udecl :
    abstract_env_rel X Σ ->
    UnivConstraintSet.For_all (declared_univ_cstr_levels (LevelSet.union udecl.1 (global_levels Σ))) udecl.2 ->
    consistent_extension_on (global_uctx Σ) udecl.2 <-> abstract_env_is_consistent X udecl;

  abstract_env_guard_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) fix_cofix Γ mfix :
      guard fix_cofix Σ Γ mfix <-> abstract_env_guard X fix_cofix Γ mfix;
  abstract_primitive_constant_correct X tag Σ :
    abstract_env_ext_rel X Σ -> abstract_primitive_constant X tag = PCUICEnvironment.primitive_constant Σ tag
  }.

Definition abstract_env_impl {cf:checker_flags} := ∑ X Y Z, @abstract_env_prop _ X Y Z.

Global Instance abstract_env_impl_abstract_env_struct {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_struct Σ.π1 Σ.π2.π1.
  exact (Σ.π2.π2.π1).
Defined.

Global Instance abstract_env_impl_abstract_env_prop {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_prop Σ.π1 Σ.π2.π1.
  exact (Σ.π2.π2.π2).
Defined.

Definition abstract_env_cored {cf:checker_flags} (_X : abstract_env_impl) (X : _X.π2.π1) {Σ Σ' Γ u v} : abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ'
-> cored Σ Γ u v -> cored Σ' Γ u v.
Proof.
  intros HΣ HΣ' Hred. erewrite (abstract_env_ext_irr _ HΣ'); eauto.
Defined.

Definition abstract_env_ext_sq_wf {cf:checker_flags} (X : abstract_env_impl) (x : X.π2.π1)
  Σ (wfΣ : abstract_env_ext_rel x Σ) : ∥ wf Σ∥.
  destruct (abstract_env_ext_wf _ wfΣ).
  sq. auto.
Qed.

Notation "Σ '∼' X" := (abstract_env_rel X Σ) (at level 40).
Notation "Σ '∼_ext' X" := (abstract_env_ext_rel X Σ) (at level 40).


Program Definition abstract_make_wf_env_ext {cf:checker_flags} {X_type : abstract_env_impl} (X : X_type.π1)
  univs (prf : forall Σ : global_env, abstract_env_rel X Σ -> ∥ wf_ext (Σ, univs) ∥) : X_type.π2.π1
  := abstract_env_add_udecl X univs _.
Next Obligation.
  specialize (prf _ H). sq. now destruct prf.
Defined.

Definition abstract_make_wf_env_ext_correct {cf:checker_flags} {X_type : abstract_env_impl} (X : X_type.π1)  univs prf :
let X' := abstract_make_wf_env_ext X univs prf in
forall Σ Σ', abstract_env_rel X Σ -> abstract_env_ext_rel X' Σ' -> Σ' = (Σ, univs).
Proof.
  unfold abstract_make_wf_env_ext. intros.
  rewrite <- abstract_env_add_udecl_rel in H0. destruct Σ' , H0; cbn in *.
  now rewrite (abstract_env_irr X H H0).
Defined.

From Stdlib Require Import MSetFacts.

From Stdlib Require Import Morphisms.

Global Instance consistent_proper : Proper (UCS.Equal ==> iff) consistent.
Proof.
  intros c c' eq. rewrite /consistent.
  now setoid_rewrite eq.
Qed.

Lemma on_udecl_mono {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} : on_udecl Σ Monomorphic_ctx.
Proof.
  repeat split; cbn.
  - intros i; rewrite LevelSetFact.empty_iff //.
  - intros i; rewrite UnivConstraintSetFact.empty_iff //.
  - red. rewrite /univs_ext_constraints /=.
    rewrite CS_union_empty.
    apply wfΣ.
  - apply consistent_extension_on_empty.
Qed.

Program Definition abstract_env_empty_ext {cf:checker_flags} {X_type : abstract_env_impl}
  (X : X_type.π1) : X_type.π2.π1
  := abstract_env_add_udecl X Monomorphic_ctx _.
Next Obligation.
  pose proof (abstract_env_wf _ H).
  sq. now apply on_udecl_mono.
Defined.

Definition abstract_env_empty_ext_rel {cf:checker_flags} {X_type : abstract_env_impl}
   (X : X_type.π1) {Σ} :
  (abstract_env_rel X Σ.1 /\ Σ.2 = Monomorphic_ctx)  <->
  abstract_env_ext_rel (abstract_env_empty_ext X) Σ.
Proof.
  unfold abstract_env_empty_ext. now rewrite <- abstract_env_add_udecl_rel.
Defined.

Program Definition abstract_env_empty {cf:checker_flags} {X_type : abstract_env_impl} : X_type.π1
  := abstract_env_init (LS.singleton Level.lzero , UCS.empty) Retroknowledge.empty _.
Next Obligation.
  repeat split.
  - intros x Hx; cbn in *. inversion Hx.
  - intros x Hx; cbn in *. destruct x; eauto. now inversion Hx.
  - red. unshelve eexists.
    + econstructor; eauto. intros; exact 1%positive.
    + red. intros ? ?. cbn in *. inversion H.
Defined.

Definition abstract_env_is_consistent_empty {cf:checker_flags} {X_type : abstract_env_impl}
  : ContextSet.t -> bool :=
  fun uctx => abstract_env_is_consistent (@abstract_env_empty cf X_type) uctx.

Lemma abstract_env_compare_universe_correct {cf:checker_flags} {X_type : abstract_env_impl}
  (X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) conv_pb u u' :
        wf_universe Σ u -> wf_universe Σ u' ->
        compare_universe Σ conv_pb u u' <->
        abstract_env_compare_universe X conv_pb u u'.
Proof.
  intros wfu wfu'. pose proof (abstract_env_ext_wf X wfΣ). sq.
  pose (Hleq := abstract_env_check_correct X wfΣ).
  eapply compare_universeP_gen with (pb := conv_pb) in Hleq.
  apply reflect_reflectT in Hleq.
  split.
  1: now eapply introT.
  1: now eapply elimT.
  all: tea. now constructor.
Qed.

Lemma abstract_env_compare_sort_correct {cf:checker_flags} {X_type : abstract_env_impl}
  (X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) conv_pb s s' :
        wf_sort Σ s -> wf_sort Σ s' ->
        compare_sort Σ conv_pb s s' <->
        abstract_env_compare_sort X conv_pb s s'.
Proof.
  intros wfu wfu'. pose proof (abstract_env_ext_wf X wfΣ). sq.
  pose (Hleq := abstract_env_check_correct X wfΣ).
  eapply compare_sortP_gen with (pb := conv_pb) in Hleq.
  apply reflect_reflectT in Hleq.
  split.
  1: now eapply introT.
  1: now eapply elimT.
  all: tea. now constructor.
Qed.

Lemma check_constraints_spec {cf:checker_flags} {X_type : abstract_env_impl}
     (X:X_type.π2.π1)  {Σ} (wfΣ : abstract_env_ext_rel X Σ) ctrs :
     uctx_invariants ((clean_uctx (global_ext_uctx Σ)).1, ctrs) ->
     abstract_env_check_constraints X ctrs -> valid_constraints (global_ext_constraints Σ) ctrs.
Proof.
    intros Huctx HH. pose proof (abstract_env_ext_wf X wfΣ). sq.
    pose (Hleq := abstract_env_check_correct X wfΣ).
    eapply (check_constraints_spec_gen (clean_uctx (global_ext_uctx Σ))); eauto.
    - apply check_spec_clean, Hleq.
    - split. rewrite /clean_uctx //=. lsets. exact Huctx.
Defined.

Lemma check_constraints_complete {cf:checker_flags} {X_type : abstract_env_impl}
    (X:X_type.π2.π1)  {Σ} (wfΣ : abstract_env_ext_rel X Σ) ctrs (H : check_univs) :
    uctx_invariants ((clean_uctx (global_ext_uctx Σ)).1, ctrs) ->
    valid_constraints (global_ext_constraints Σ) ctrs -> abstract_env_check_constraints X ctrs.
Proof.
    intros Huctx HH. pose proof (abstract_env_ext_wf X wfΣ). sq.
    pose (Hleq := abstract_env_check_correct X wfΣ).
    eapply (check_constraints_spec_gen (clean_uctx (global_ext_uctx Σ))); eauto.
    - apply check_spec_clean, Hleq.
    - split. rewrite /clean_uctx //=. lsets. exact Huctx.
Qed.

Lemma abstract_env_check_constraints_correct {cf:checker_flags} {X_type : abstract_env_impl}
    (X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) ctrs :
    check_univs -> uctx_invariants ((clean_uctx (global_ext_uctx Σ)).1, ctrs) ->
    valid_constraints Σ ctrs <-> abstract_env_check_constraints X ctrs.
Proof.
  split; intros.
  - eapply check_constraints_complete; eauto.
  - eapply check_constraints_spec; eauto.
Qed.

Lemma abstract_env_ext_wf_universeb_correct {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) u :
  wf_universeb Σ u = abstract_env_ext_wf_universeb X u.
Proof.
  destruct u as [ [] ?]; cbn. clear is_ok t_ne.
  induction this => //; cbn. set (b := LevelSet.Raw.mem _ _). set (b' := abstract_env_level_mem _ _).
  assert (Hbb' : b = b').
  { unfold b'. apply eq_true_iff_eq. rewrite <- (abstract_env_level_mem_correct X wfΣ (LevelExpr.get_level a)).
    now erewrite <- (LevelSet.Raw.mem_spec (LevelSet.this (global_ext_levels Σ)) (LevelExpr.get_level a)). }
  destruct Hbb', b => //.
Qed.

Lemma abstract_env_ext_wf_sortb_correct {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) s :
  wf_sortb Σ s = abstract_env_ext_wf_sortb X s.
Proof.
  destruct s as [| |u]; cbnr.
  now apply abstract_env_ext_wf_universeb_correct.
Qed.

Lemma abstract_env_level_mem_correct' {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) levels u :
  LevelSet.mem u (LevelSet.union levels (global_ext_levels Σ)) = abstract_env_level_mem' X levels u.
Proof.
  unfold abstract_env_level_mem'. rewrite LevelSetProp.Dec.F.union_b. f_equal.
  have h := (abstract_env_level_mem_correct X wfΣ u).
  apply eqb_iff. rewrite -[abstract_env_level_mem _ _ = true]h.
  now rewrite LevelSet.mem_spec.
Qed.

Lemma wf_consistent_extension_on_consistent {cf:checker_flags} {Σ} udecl :
  wf Σ -> consistent_extension_on (global_uctx Σ) udecl ->
  consistent (UnivConstraintSet.union udecl (global_constraints Σ)).
Proof.
  intros s Hext. pose proof (wf_consistent _ s).
  destruct H as [val Hval].
  destruct (Hext val Hval) as [val' [Hval' Hval'']]. exists val'.
  intros [[l ct] l'] [Hl|Hl]%UCS.union_spec; eauto.
  destruct (Hval _ Hl); cbn; econstructor.
Admitted.
  (* - erewrite <- (Hval'' l0). erewrite <- (Hval'' l'0) => //.
    + destruct s as [[Hs _] _]. now destruct (Hs _ Hl).
      + destruct s as [[Hs _] _]. now destruct (Hs _ Hl).
    - erewrite <- (Hval'' l0). erewrite <- (Hval'' l'0) => //.
      + destruct s as [[Hs _] _]. now destruct (Hs _ Hl).
      + destruct s as [[Hs _] _]. now destruct (Hs _ Hl). *)
(* Qed. *)

Lemma abstract_env_lookup_correct' {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} kn : abstract_env_ext_rel X Σ ->
  lookup_env Σ kn = abstract_env_lookup X kn.
Proof.
  intro wfΣ; pose proof (HΣ := abstract_env_ext_wf X wfΣ); sq.
  set (odecl := lookup_env _ _). case_eq odecl => [decl Hdecl| Hnotin].
  - intros. destruct (abstract_env_lookup_correct X kn decl wfΣ) as [H _].
    rewrite H; eauto. apply lookup_global_Some_iff_In_NoDup => //.
    destruct HΣ as [[] _]. now eapply NoDup_on_global_decls.
  - apply lookup_global_None in Hnotin. case_eq (abstract_env_lookup X kn) => //.
    intros decl Hdecl. eapply abstract_env_lookup_correct in Hdecl; eauto.
    destruct Hnotin. apply in_map_iff. now exists (kn,decl).
Qed.

