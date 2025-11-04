(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ProofIrrelevance.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICTyping.

(** Injectivity of declared_*, inversion lemmas on declared global references and
    universe consistency of the global environment.
*)

Lemma declared_constant_inj {Σ c} decl1 decl2 :
  declared_constant_gen Σ c decl1 -> declared_constant_gen Σ c decl2 -> decl1 = decl2.
Proof.
  intros. unfold declared_constant_gen in *. rewrite H in H0.
  now inv H0.
Qed.

Lemma declared_inductive_inj {Σ mdecl mdecl' ind idecl idecl'} :
  declared_inductive_gen Σ ind mdecl' idecl' ->
  declared_inductive_gen Σ ind mdecl idecl ->
  mdecl = mdecl' /\ idecl = idecl'.
Proof.
  intros [] []. unfold declared_minductive_gen in *.
  rewrite H in H1. inversion H1. subst. rewrite H2 in H0. inversion H0. eauto.
Qed.

Lemma declared_constructor_inj {Σ mdecl mdecl' idecl idecl' cdecl cdecl' c} :
  declared_constructor_gen Σ c mdecl' idecl' cdecl ->
  declared_constructor_gen Σ c mdecl idecl cdecl' ->
  mdecl = mdecl' /\ idecl = idecl'  /\ cdecl = cdecl'.
Proof.
  intros [] [].
  destruct (declared_inductive_inj H H1); subst.
  rewrite H0 in H2. intuition congruence.
Qed.

Lemma declared_projection_inj {Σ mdecl mdecl' idecl idecl' cdecl cdecl' pdecl pdecl' p} :
  declared_projection_gen Σ p mdecl idecl cdecl pdecl ->
  declared_projection_gen Σ p mdecl' idecl' cdecl' pdecl' ->
  mdecl = mdecl' /\ idecl = idecl'  /\ cdecl = cdecl' /\ pdecl = pdecl'.
Proof.
  intros [] [].
  destruct (declared_constructor_inj H H1) as [? []]; subst.
  destruct H0, H2.
  rewrite H0 in H2. intuition congruence.
Qed.

Lemma declared_inductive_minductive {Σ ind mdecl idecl} :
  declared_inductive_gen Σ ind mdecl idecl -> declared_minductive_gen Σ (inductive_mind ind) mdecl.
Proof. now intros []. Qed.

Lemma declared_inductive_minductive' {Σ ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl -> declared_minductive Σ (inductive_mind ind) mdecl.
Proof. now intros []. Qed.

#[global]
Hint Extern 0 => eapply declared_inductive_minductive : pcuic core.

Coercion declared_inductive_minductive : declared_inductive_gen >-> declared_minductive_gen.
Coercion declared_inductive_minductive' : declared_inductive >-> declared_minductive.

Lemma declared_constructor_inductive {Σ ind mdecl idecl cdecl} :
  declared_constructor_gen Σ ind mdecl idecl cdecl ->
  declared_inductive_gen Σ ind.1 mdecl idecl.
Proof. now intros []. Qed.

Definition declared_constructor_inductive' {Σ ind mdecl idecl cdecl} :
  declared_constructor Σ ind mdecl idecl cdecl ->
  declared_inductive Σ ind.1 mdecl idecl.
Proof. now intros []. Qed.

Coercion declared_constructor_inductive : declared_constructor_gen >-> declared_inductive_gen.
Coercion declared_constructor_inductive' : declared_constructor >-> declared_inductive.

Lemma declared_projection_constructor {Σ ind mdecl idecl cdecl pdecl} :
  declared_projection_gen Σ ind mdecl idecl cdecl pdecl ->
  declared_constructor_gen Σ (ind.(proj_ind), 0) mdecl idecl cdecl.
Proof. now intros []. Qed.

Definition declared_projection_constructor' {Σ ind mdecl idecl cdecl pdecl} :
  declared_projection Σ ind mdecl idecl cdecl pdecl ->
  declared_constructor Σ (ind.(proj_ind), 0) mdecl idecl cdecl.
Proof. now intros []. Qed.

Coercion declared_projection_constructor : declared_projection_gen >-> declared_constructor_gen.
Coercion declared_projection_constructor' : declared_projection >-> declared_constructor.

Section DeclaredInv.
  Context {cf:checker_flags} {Σ} {wfΣ : wf Σ}.

  Lemma declared_minductive_ind_npars  {mdecl ind} :
    declared_minductive Σ ind mdecl ->
    ind_npars mdecl = context_assumptions mdecl.(ind_params).
  Proof using wfΣ.
    intros h.
    unshelve eapply declared_minductive_to_gen in h; tea.
    unfold declared_minductive in h.
    eapply lookup_on_global_env in h; tea.
    destruct h as (Σ' & ext & wfΣ' & decl').
    red in decl'. destruct decl' as [h ? ? ?].
    now rewrite onNpars.
  Qed.

End DeclaredInv.

From MetaRocq.Common Require Import UniversesDec.

Definition clean_uctx (uctx : ContextSet.t) :=
  (LevelSet.remove Level.lzero uctx.1, uctx.2).

Definition wf_global_uctx_invariants {cf:checker_flags} {P} Σ :
  on_global_env cumulSpec0 P Σ ->
  global_uctx_invariants (clean_uctx (global_uctx Σ)).
Proof.
 intros HΣ. split.
 - cbn. lsets.
 - unfold global_uctx.
   simpl. intros [[l ct] l'] Hctr. simpl in *.
   rewrite levelset_add_remove.
   induction Σ in HΣ, l, ct, l', Hctr |- *.
   destruct HΣ. cbn in *.
   destruct o as [decls cu].
   specialize (decls _ Hctr).
   split; apply levelset_subset_add, decls.
Qed.

Lemma LevelSet_in_union_global Σ l ls :
  LevelSet.In l (LevelSet.union ls (universes Σ).1) ->
  LevelSet.In l (LevelSet.union ls (global_levels (universes Σ))).
Proof.
  intros H % LevelSet.union_spec.
  apply LevelSet.union_spec. intuition auto.
  right. now apply LevelSet.union_spec.
Qed.

Definition wf_ext_global_uctx_invariants {cf:checker_flags} {P} Σ :
  on_global_env_ext cumulSpec0 P Σ ->
  global_uctx_invariants (clean_uctx (global_ext_uctx Σ)).
Proof.
 intros HΣ. split.
 - cbn. lsets.
 - destruct Σ as [Σ φ]. destruct HΣ as [HΣ Hφ].
   destruct (wf_global_uctx_invariants _ HΣ) as [_ XX].
   unfold global_ext_uctx, global_ext_levels, global_ext_constraints.
   simpl. intros [[l ct] l'] Hctr. simpl in *. apply UnivConstraintSet.union_spec in Hctr.
   destruct Hctr as [Hctr|Hctr].
   + destruct Hφ as [_ [HH _]]. specialize (HH _ Hctr). cbn in HH.
     intuition auto using LevelSet_in_union_global.
     rewrite levelset_add_remove. lsets.
     rewrite levelset_add_remove. lsets.
   + specialize (XX _ Hctr). cbn in XX.
     rewrite !levelset_add_remove in XX. destruct XX as [Xl Xr].
     rewrite !levelset_add_remove.
     rewrite levelset_add_union.
     split; lsets.
Qed.

Lemma wf_consistent {cf:checker_flags} Σ {P} :
  on_global_env cumulSpec0 P Σ -> consistent (global_constraints Σ).
Proof.
  destruct Σ.
  intros [cu ong]. apply cu.
Qed.

Definition global_ext_uctx_consistent {cf:checker_flags} {P} Σ
 : on_global_env_ext cumulSpec0 P Σ -> consistent (global_ext_uctx Σ).2.
Proof.
  intros HΣ. cbn. unfold global_ext_constraints.
  unfold wf_ext, on_global_env_ext in HΣ.
  destruct HΣ as (_ & _ & _ & HH & _). apply HH.
Qed.


