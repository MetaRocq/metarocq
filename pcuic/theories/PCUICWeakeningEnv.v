(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import LibHypsNaming.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma global_ext_constraints_app Σ Σ' φ
  : UnivConstraintSet.Subset (universes Σ).2 (universes Σ').2 ->
    UnivConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ', φ)).
Proof.
  unfold global_ext_constraints; simpl.
  intros sub ctr Hc. apply UnivConstraintSet.union_spec in Hc.
  apply UnivConstraintSet.union_spec.
  destruct Hc as [Hc|Hc]; [now left|right]. clear φ.
  unfold global_constraints in Hc.
  apply (sub _ Hc).
Qed.


Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | (extends ?t.1 _) => fresh "ext" t
  | (extends _ _) => fresh "ext"
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

(** * Weakening lemmas w.r.t. the global environment *)

(** ** Constraints *)

Lemma weakening_env_global_ext_level Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.In l (global_ext_levels (Σ, φ))
    -> LevelSet.In l (global_ext_levels (Σ', φ)).
Proof.
  unfold global_ext_levels; simpl.
  intros Hl. apply LevelSet.union_spec in Hl.
  apply LevelSet.union_spec.
  destruct Hl as [Hl|Hl]; [now left|right]. clear φ.
  destruct H as [[lsub csub] _].
  apply LevelSet.union_spec in Hl.
  apply LevelSet.union_spec; intuition auto.
Qed.
#[global] Hint Resolve weakening_env_global_ext_level : extends.

Lemma weakening_env_global_ext_levels Σ Σ' φ (H : extends Σ Σ') ls
  : LevelSet.Subset ls (global_ext_levels (Σ, φ))
    -> LevelSet.Subset ls (global_ext_levels (Σ', φ)).
Proof.
  move=> hs l /hs. now apply weakening_env_global_ext_level.
Qed.
#[global] Hint Resolve weakening_env_global_ext_levels : extends.

Lemma weakening_env_global_ext_level_mem Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.mem l (global_ext_levels (Σ, φ))
    -> LevelSet.mem l (global_ext_levels (Σ', φ)).
Proof.
  intro HH. apply LevelSet.mem_spec in HH.
  now eapply LevelSet.mem_spec, weakening_env_global_ext_levels.
Qed.

Lemma weakening_env_global_ext_levels_subset Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.subset l (global_ext_levels (Σ, φ))
    -> LevelSet.subset l (global_ext_levels (Σ', φ)).
Proof.
  rewrite ![is_true _]LevelSet.subset_spec. now apply weakening_env_global_ext_levels.
Qed.

Lemma weakening_env_global_ext_constraints Σ Σ' φ (H : extends Σ Σ')
  : UnivConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ', φ)).
Proof.
  destruct H as [sub _].
  apply global_ext_constraints_app, sub.
Qed.

#[global] Instance subrel_extends_cmp_universe {cf} pb (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (compare_universe (global_ext_constraints (Σ, ϕ)) pb)
    (compare_universe (global_ext_constraints (Σ', ϕ)) pb).
Proof.
  intros ext u u'.
  apply cmp_universe_subset.
  apply weakening_env_global_ext_constraints, ext.
Qed.

#[global] Instance subrel_extends_cmp {cf} pb (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (compare_sort (global_ext_constraints (Σ, ϕ)) pb)
    (compare_sort (global_ext_constraints (Σ', ϕ)) pb).
Proof.
  intros ext u u'.
  apply cmp_sort_subset.
  apply weakening_env_global_ext_constraints, ext.
Qed.

#[global] Instance subrel_extends_eq_pb {cf} pb (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_sort (global_ext_constraints (Σ, ϕ)))
    (compare_sort (global_ext_constraints (Σ', ϕ)) pb).
Proof.
  change (eq_sort ?φ) with (compare_sort φ Conv).
  intros ext.
  destruct pb.
  - tc.
  - transitivity (compare_sort (global_ext_constraints (Σ', ϕ)) Conv); tc.
Qed.

#[global] Instance subrel_extends_eq {cf} (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_sort (global_ext_constraints (Σ, ϕ)))
    (eq_sort (global_ext_constraints (Σ', ϕ))).
Proof. change (eq_sort ?φ) with (compare_sort φ Conv). tc. Qed.

#[global] Instance subrel_extends_le {cf} (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (leq_sort (global_ext_constraints (Σ, ϕ)))
    (leq_sort (global_ext_constraints (Σ', ϕ))).
Proof. change (leq_sort ?φ) with (compare_sort φ Cumul). tc. Qed.

#[global] Instance subrel_extends_eq_le {cf} (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_sort (global_ext_constraints (Σ, ϕ)))
    (leq_sort (global_ext_constraints (Σ', ϕ))).
Proof. change (leq_sort ?φ) with (compare_sort φ Cumul). tc. Qed.

Lemma subrelations_extends {cf} Σ Σ' φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_sort (global_ext_constraints (Σ,φ))) (eq_sort (global_ext_constraints (Σ',φ))).
Proof. typeclasses eauto. Qed.

Lemma subrelations_leq_extends {cf} Σ Σ' φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (leq_sort (global_ext_constraints (Σ,φ))) (leq_sort (global_ext_constraints (Σ',φ))).
Proof. typeclasses eauto. Qed.

Lemma subrelations_compare_extends {cf} Σ Σ' pb φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (compare_sort (global_ext_constraints (Σ,φ)) pb)
    (compare_sort (global_ext_constraints (Σ',φ)) pb).
Proof. destruct pb; typeclasses eauto. Qed.

Lemma subrelations_eq_compare_extends {cf} Σ Σ' pb φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_sort (global_ext_constraints (Σ,φ)))
    (compare_sort (global_ext_constraints (Σ',φ)) pb).
Proof. destruct pb; typeclasses eauto. Qed.


Lemma weakening_env_is_allowed_elimination {cf} Σ Σ' φ u allowed :
  extends Σ Σ' ->
  is_allowed_elimination (global_ext_constraints (Σ, φ)) allowed u ->
  is_allowed_elimination (global_ext_constraints (Σ', φ)) allowed u.
Proof.
  destruct allowed; cbnr; trivial.
  intros ext [ | al]; auto.
  destruct u; cbn in *; try now right.
  right.
  unfold_univ_rel.
  apply al.
  eapply satisfies_subset; eauto.
  apply weakening_env_global_ext_constraints, ext.
Qed.
#[global] Hint Resolve weakening_env_is_allowed_elimination : extends.

Lemma weakening_env_consistent_instance {cf} Σ Σ' φ ctrs u (H : extends Σ Σ')
  : consistent_instance_ext (Σ, φ) ctrs u
    -> consistent_instance_ext (Σ', φ) ctrs u.
Proof.
    unfold consistent_instance_ext, consistent_instance.
    intros X.
    destruct ctrs; tas.
    destruct X as (H0 & H1 & H2); repeat split; tas.
    - eapply forallb_Forall in H0; eapply forallb_Forall, Forall_impl; tea.
      intros x ?; now eapply weakening_env_global_ext_levels_subset.
    - eapply valid_subset; tea;
      now eapply weakening_env_global_ext_constraints.
Qed.
#[global] Hint Resolve weakening_env_consistent_instance : extends.

Lemma global_levels_union_set Σ :
  LevelSet.Equal (LevelSet.union (LevelSet.singleton Level.lzero) (global_levels Σ))
  (global_levels Σ).
Proof.
  apply LevelSetProp.union_subset_equal.
  intros x hin. eapply LevelSet.singleton_spec in hin; subst x.
  apply global_levels_InSet.
Qed.

Lemma global_levels_sub {univs univs'} : univs ⊂_cs univs' ->
  LevelSet.Subset (global_levels univs) (global_levels univs').
Proof.
  unfold global_levels => sub.
  intros x hin % LevelSet.union_spec.
  apply LevelSet.union_spec.
  intuition auto. left. now apply sub.
Qed.

Lemma extends_wf_universe {Σ : global_env_ext} Σ' u : extends Σ Σ' ->
  wf_universe Σ u -> wf_universe (Σ', Σ.2) u.
Proof.
  destruct Σ as [Σ univ]; cbn.
  intros [sub _].
  intros Hl.
  intros l inl; specialize (Hl l inl).
  cbn.
  unfold global_ext_levels.
  eapply LevelSet.union_spec; simpl.
  apply LevelSet.union_spec in Hl as [Hl|Hl]; cbn in Hl.
  - simpl. simpl in Hl. now left.
  - right. eapply global_levels_sub; tea.
Qed.

Lemma extends_wf_sort {Σ : global_env_ext} Σ' s : extends Σ Σ' ->
  wf_sort Σ s -> wf_sort (Σ', Σ.2) s.
Proof.
  destruct s => //=.
  apply extends_wf_universe.
Qed.


Definition on_udecl_prop (Σ : global_env) (udecl : universes_decl)
  := let levels := levels_of_udecl udecl in
     let global_levels := global_levels Σ.(universes) in
     let all_levels := LevelSet.union levels global_levels in
     UnivConstraintSet.For_all (declared_univ_cstr_levels all_levels) (constraints_of_udecl udecl).
     (* /\ match udecl with
       | Monomorphic_ctx ctx => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                               /\ LevelSet.Subset ctx.1 global_levels
                               /\ UnivConstraintSet.Subset ctx.2 (global_constraints Σ)
                               /\ satisfiable_udecl Σ.(universes) udecl
       | _ => True
       end. *)

Lemma in_global_levels l u :
  LevelSet.In l (ContextSet.levels u) ->
  LevelSet.In l (global_levels u).
Proof.
  intros hin; now apply LevelSet.union_spec.
Qed.

Lemma declared_cstr_levels_sub l l' c :
  LevelSet.Subset l l' ->
  declared_univ_cstr_levels l c -> declared_univ_cstr_levels l' c.
Proof.
  intros sub; unfold declared_univ_cstr_levels.
  destruct c as [[l1 eq] l2]. firstorder.
Qed.

Lemma on_udecl_on_udecl_prop (Σ : global_env) ctx :
  on_udecl Σ.(universes) (Polymorphic_ctx ctx) -> on_udecl_prop Σ (Polymorphic_ctx ctx).
Proof.
  intros [? [? ?]]. red.
  intros x hin. specialize (H0 x hin).
  eapply declared_cstr_levels_sub; tea.
  intros x' hin'.
  eapply LevelSet.union_spec. apply LevelSet.union_spec in hin'.
  intuition auto.
Qed.



(** ** Lookup *)

Lemma lookup_global_Some_fresh Σ c decl :
  lookup_global Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  destruct (eqb_spec c a.1); subst.
  - intros [= <-] H2. inv H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.

Lemma lookup_env_Some_fresh Σ c decl :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ.(declarations)).
Proof.
  apply lookup_global_Some_fresh.
Qed.

Section ExtendsWf.
  Context {cf : checker_flags}.
  Context {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P: global_env_ext -> context -> judgment -> Type}.

  Let wf := on_global_env Pcmp P.

  Lemma extends_lookup Σ Σ' c decl :
  wf Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof using P Pcmp cf.
  cbv [wf on_global_env].
  intros; eapply lookup_env_extends_NoDup; tea.
  repeat match goal with H : _ × _ |- _ => destruct H end.
  eapply NoDup_on_global_decls; tea.
Qed.
Hint Resolve extends_lookup : extends.

Lemma weakening_env_declared_constant :
  forall (Σ : global_env) cst (decl : constant_body),
    declared_constant Σ cst decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_constant Σ' cst decl.
Proof using P Pcmp cf.
  intros Σ cst decl H0 Σ' X2 H2.
  unfold declared_constant in *.
  eapply lookup_globals_In in H0.
  eapply lookup_globals_In.
  destruct H2 as [? H2 _].
  specialize (H2 cst). destruct H2 as [decls Hdecls].
  rewrite /lookup_envs in Hdecls. rewrite Hdecls.
  apply in_or_app. now right.
Qed.

Hint Resolve weakening_env_declared_constant : extends.

Lemma weakening_env_declared_minductive `{CF:checker_flags}:
  forall (Σ : global_env) ind decl,
    declared_minductive Σ ind decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_minductive Σ' ind decl.
Proof using P Pcmp cf.
  intros Σ cst decl H0 Σ' X2 H2.
  unfold declared_minductive in *.
  eapply lookup_globals_In in H0.
  eapply lookup_globals_In.
  destruct H2 as [? H2 _].
  specialize (H2 cst). destruct H2 as [decls Hdecls].
  rewrite /lookup_envs in Hdecls. rewrite Hdecls.
  apply in_or_app. now right.
Qed.

Hint Extern 0 => eapply weakening_env_declared_minductive : extends.

Lemma weakening_env_declared_inductive:
  forall (H : checker_flags) (Σ : global_env) ind mdecl decl,
    declared_inductive Σ mdecl ind decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_inductive Σ' mdecl ind decl.
Proof using P Pcmp cf.
  intros H Σ cst decl H0 [Hmdecl Hidecl] Σ' X2 H2. split; eauto with extends.
Qed.

Hint Extern 0 => eapply weakening_env_declared_inductive : extends.

Lemma weakening_env_declared_constructor :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl decl,
    declared_constructor Σ idecl ind mdecl decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_constructor Σ' idecl ind mdecl decl.
Proof using P Pcmp cf.
  intros H Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Extern 0 => eapply weakening_env_declared_constructor : extends.

Lemma weakening_env_declared_projection :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl cdecl pdecl,
    declared_projection Σ idecl ind mdecl cdecl pdecl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_projection Σ' idecl ind mdecl cdecl pdecl.
Proof using P Pcmp cf.
  intros H Σ cst mdecl idecl cdecl pdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Extern 0 => eapply weakening_env_declared_projection : extends.

(* Lemma wf_extends {Σ Σ'} : wf Σ' -> extends Σ Σ' -> wf Σ.
Proof.
  intros HΣ' [univs H]. simpl in *.
  split => //.
  - red.
  induction Σ''; auto.
  inv HΣ'. auto.
Qed. *)

(** ** Back to universes *)

Instance hr : RelationClasses.RewriteRelation LevelSet.Subset := {}.

Lemma weaken_lookup_on_global_env' Σ c decl :
  wf Σ ->
  lookup_env Σ c = Some decl ->
  on_udecl_prop Σ (universes_decl_of_decl decl).
Proof using P Pcmp cf.
  intros [onu wfΣ] HH.
  destruct Σ as [univs Σ]; cbn in *.
  induction wfΣ; simpl. 1: discriminate.
  destruct o as [? udecl o ?].
  cbn in HH. subst udecl.
  destruct (eqb_spec c kn); subst.
  - apply some_inj in HH; destruct HH. subst.
    clear -o. unfold on_udecl, on_udecl_prop in *.
    destruct o as [H1 [H2 [H3 H4]]]. repeat split.
    clear -H2. intros [[? ?] ?] Hc. specialize (H2 _ Hc).
    destruct H2 as [H H']. simpl. split.
    * rewrite H. lsets.
    * rewrite H'. lsets.
  - specialize (IHwfΣ HH). revert IHwfΣ o; clear.
    generalize (universes_decl_of_decl decl); intros d' HH Hd.
    unfold on_udecl_prop in *.
    intros [[? ?] ?] Hc. specialize (HH _ Hc).
    destruct HH as [H' H'']. simpl. split.
    * rewrite H'. lsets.
    * rewrite H''; lsets.
Qed.

Definition weaken_env_prop_full_gen
             (R : global_env_ext -> global_env_ext -> Type)
             (P : global_env_ext -> context -> term -> term -> Type) :=
  forall (Σ : global_env_ext) (Σ' : global_env),
    wf Σ -> wf Σ' -> R Σ (Σ', Σ.2) ->
    forall Γ t T, P Σ Γ t T -> P (Σ', Σ.2) Γ t T.

Definition weaken_env_prop_gen
           (R : global_env_ext -> global_env_ext -> Type)
           (P : global_env_ext -> context -> judgment -> Type) :=
  forall Σ Σ' φ, wf Σ -> wf Σ' -> R (Σ, φ) (Σ', φ) -> forall Γ j, P (Σ, φ) Γ j -> P (Σ', φ) Γ j.

Definition weaken_env_prop_full := weaken_env_prop_full_gen extends.
Definition weaken_env_decls_prop_full := weaken_env_prop_full_gen extends_decls.
Definition weaken_env_strictly_decls_prop_full := weaken_env_prop_full_gen strictly_extends_decls.
Definition weaken_env_strictly_on_decls_prop_full := weaken_env_prop_full_gen extends_strictly_on_decls.

Definition weaken_env_prop := weaken_env_prop_gen extends.
Definition weaken_env_decls_prop := weaken_env_prop_gen extends_decls.
Definition weaken_env_strictly_decls_prop := weaken_env_prop_gen strictly_extends_decls.
Definition weaken_env_strictly_on_decls_prop := weaken_env_prop_gen extends_strictly_on_decls.

Import CMorphisms CRelationClasses.
#[global] Instance weaken_env_prop_gen_impl
  : Proper (flip subrelation ==> (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ iffT))) ==> arrow)%signatureT weaken_env_prop_gen | 10.
Proof using Type.
  cbv -[weaken_env_prop_gen iffT]; cbv [weaken_env_prop_gen]; intros * H1 * H2 H3.
  unshelve
    (repeat (let x := fresh in
             intro x;
             first [ specialize (H3 x)
                   | let x := open_constr:(_) in specialize (H3 x) ]));
    eauto.
  all: rewrite -> H2 in *; assumption.
Qed.

#[global] Instance Proper_weaken_env_prop_gen_respectful
  : Proper (flip subrelation ==> (eq ==> eq ==> eq ==> iffT) ==> arrow)%signatureT weaken_env_prop_gen | 10.
Proof using Type.
  generalize weaken_env_prop_gen_impl; cbv -[weaken_env_prop_gen]; eauto.
Qed.

#[global] Instance weaken_env_prop_full_gen_impl
  : Proper (flip subrelation ==> (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ iffT)))) ==> arrow)%signatureT weaken_env_prop_full_gen | 10.
Proof using Type.
  cbv -[weaken_env_prop_full_gen iffT]; cbv [weaken_env_prop_full_gen]; intros * H1 * H2 H3.
  unshelve
    (repeat (let x := fresh in
             intro x;
             first [ specialize (H3 x)
                   | let x := open_constr:(_) in specialize (H3 x) ]));
    eauto.
  all: rewrite -> H2 in *; assumption.
Qed.

#[global] Instance Proper_weaken_env_prop_full_gen_respectful
  : Proper (flip subrelation ==> (eq ==> eq ==> eq ==> eq ==> iffT) ==> arrow)%signatureT weaken_env_prop_full_gen | 10.
Proof using Type.
  generalize weaken_env_prop_full_gen_impl; cbv -[weaken_env_prop_full_gen]; eauto.
Qed.

Lemma strictly_extends_decls_wf Σ Σ' :
  wf Σ' -> strictly_extends_decls Σ Σ' -> wf Σ.
Proof using P Pcmp cf.
  intros [onu ond] [eq [Σ'' eq']].
  split => //.
  - red. rewrite eq. apply onu.
  - rewrite eq. rewrite eq' in ond.
    rewrite -e in ond.
    revert ond; clear.
    induction Σ''; cbn; auto.
    intros H; depelim H.
    apply IHΣ''. apply H.
Qed.

End ExtendsWf.

Arguments weaken_env_prop_full_gen {cf} (Pcmp P R)%_function_scope _%_function_scope.
Arguments weaken_env_prop_gen {cf} (Pcmp P R)%_function_scope _%_function_scope.
Arguments weaken_env_prop_full {cf} (Pcmp P)%_function_scope _%_function_scope.
Arguments weaken_env_decls_prop_full {cf} (Pcmp P)%_function_scope _%_function_scope.
Arguments weaken_env_strictly_on_decls_prop_full {cf} (Pcmp P)%_function_scope _%_function_scope.
Arguments weaken_env_strictly_decls_prop_full {cf} (Pcmp P)%_function_scope _%_function_scope.
Arguments weaken_env_prop {cf} (Pcmp P)%_function_scope _%_function_scope.
Arguments weaken_env_decls_prop {cf} (Pcmp P)%_function_scope _%_function_scope.
Arguments weaken_env_strictly_on_decls_prop {cf} (Pcmp P)%_function_scope _%_function_scope.
Arguments weaken_env_strictly_decls_prop {cf} (Pcmp P)%_function_scope _%_function_scope.

#[global] Hint Resolve extends_lookup : extends.
#[global] Hint Resolve weakening_env_declared_constant : extends.
#[global] Hint Resolve weakening_env_declared_minductive : extends.
#[global] Hint Resolve weakening_env_declared_inductive : extends.
#[global] Hint Resolve weakening_env_declared_constructor : extends.
#[global] Hint Resolve weakening_env_declared_projection : extends.

(* diamond dependency, but the proofs should never matter *)
(* we export disabling this warning here so these coercions don't result in warnings, and then we re-enable it later to not suppress other warnings *)
Import CMorphisms CRelationClasses.
#[export] Set Warnings "-ambiguous-paths".
#[warning="-ambiguous-paths"]
Global Coercion weaken_env_prop_full_to_decls {cf Pcmp P P0} : @weaken_env_prop_full cf Pcmp P P0 -> @weaken_env_decls_prop_full cf Pcmp P P0.
Proof. eapply weaken_env_prop_full_gen_impl; repeat intro; tc; reflexivity. Qed.
#[warnings="-ambiguous-paths"]
Global Coercion weaken_env_prop_full_to_strictly_on_decls {cf Pcmp P P0} : @weaken_env_prop_full cf Pcmp P P0 -> @weaken_env_strictly_on_decls_prop_full cf Pcmp P P0.
Proof. eapply weaken_env_prop_full_gen_impl; repeat intro; tc; reflexivity. Qed.
#[warnings="-ambiguous-paths"]
Global Coercion weaken_env_prop_full_decls_to_strictly_decls {cf Pcmp P P0} : @weaken_env_decls_prop_full cf Pcmp P P0 -> @weaken_env_strictly_decls_prop_full cf Pcmp P P0.
Proof. eapply weaken_env_prop_full_gen_impl; repeat intro; tc; reflexivity. Qed.
#[warnings="-ambiguous-paths"]
Global Coercion weaken_env_prop_full_strictly_on_decls_to_strictly_decls {cf Pcmp P P0} : @weaken_env_strictly_on_decls_prop_full cf Pcmp P P0 -> @weaken_env_strictly_decls_prop_full cf Pcmp P P0.
Proof. eapply weaken_env_prop_full_gen_impl; repeat intro; tc; reflexivity. Qed.

#[warnings="-ambiguous-paths"]
Global Coercion weaken_env_prop_to_decls {cf Pcmp P P0} : @weaken_env_prop cf Pcmp P P0 -> @weaken_env_decls_prop cf Pcmp P P0.
Proof. eapply weaken_env_prop_gen_impl; repeat intro; tc; reflexivity. Qed.
#[warnings="-ambiguous-paths"]
Global Coercion weaken_env_prop_to_strictly_on_decls {cf Pcmp P P0} : @weaken_env_prop cf Pcmp P P0 -> @weaken_env_strictly_on_decls_prop cf Pcmp P P0.
Proof. eapply weaken_env_prop_gen_impl; repeat intro; tc; reflexivity. Qed.
#[warnings="-ambiguous-paths"]
Global Coercion weaken_env_prop_decls_to_strictly_decls {cf Pcmp P P0} : @weaken_env_decls_prop cf Pcmp P P0 -> @weaken_env_strictly_decls_prop cf Pcmp P P0.
Proof. eapply weaken_env_prop_gen_impl; repeat intro; tc; reflexivity. Qed.
#[warnings="-ambiguous-paths"]
Global Coercion weaken_env_prop_strictly_on_decls_to_strictly_decls {cf Pcmp P P0} : @weaken_env_strictly_on_decls_prop cf Pcmp P P0 -> @weaken_env_strictly_decls_prop cf Pcmp P P0.
Proof. eapply weaken_env_prop_gen_impl; repeat intro; tc; reflexivity. Qed.
#[export] Set Warnings Append "ambiguous-paths".

#[global] Hint Resolve weaken_env_prop_full_to_decls : extends.
#[global] Hint Resolve weaken_env_prop_full_to_strictly_on_decls : extends.
#[global] Hint Resolve weaken_env_prop_full_decls_to_strictly_decls : extends.
#[global] Hint Resolve weaken_env_prop_full_strictly_on_decls_to_strictly_decls : extends.

#[global] Hint Resolve weaken_env_prop_to_decls : extends.
#[global] Hint Resolve weaken_env_prop_to_strictly_on_decls : extends.
#[global] Hint Resolve weaken_env_prop_decls_to_strictly_decls : extends.
#[global] Hint Resolve weaken_env_prop_strictly_on_decls_to_strictly_decls : extends.
