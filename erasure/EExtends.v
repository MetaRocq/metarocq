From Stdlib Require Import ssreflect.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.Erasure Require Import EGlobalEnv EAst EWellformed.

Section EEnvFlags.
  Context (efl : EEnvFlags).

  Lemma weakening_env_declared_constant :
    forall Σ cst decl,
      declared_constant Σ cst decl ->
      forall Σ', wf_glob Σ' -> extends Σ Σ' -> declared_constant Σ' cst decl.
  Proof using Type.
    intros Σ cst decl H0 Σ' X2 H2.
    eapply extends_lookup; eauto.
  Qed.

  Lemma weakening_env_declared_minductive :
    forall Σ ind decl,
      declared_minductive Σ ind decl ->
      forall Σ', wf_glob Σ' -> extends Σ Σ' -> declared_minductive Σ' ind decl.
  Proof using Type.
    intros Σ cst decl H0 Σ' X2 H2.
    eapply extends_lookup; eauto.
  Qed.

  Lemma weakening_env_declared_inductive:
    forall Σ ind mdecl decl,
      declared_inductive Σ mdecl ind decl ->
      forall Σ', wf_glob Σ' -> extends Σ Σ' -> declared_inductive Σ' mdecl ind decl.
  Proof using Type.
    intros Σ cst decl H0 [Hmdecl Hidecl] Σ' X2 H2. split.
    eapply weakening_env_declared_minductive; eauto.
    eauto.
  Qed.

  Lemma weakening_env_declared_constructor :
    forall Σ ind mdecl idecl decl,
      declared_constructor Σ idecl ind mdecl decl ->
      forall Σ', wf_glob Σ' -> extends Σ Σ' ->
      declared_constructor Σ' idecl ind mdecl decl.
  Proof using Type.
    intros Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
    split; eauto. eapply weakening_env_declared_inductive; eauto.
  Qed.

  Lemma extends_wf_glob {Σ Σ'} : extends_prefix Σ Σ' -> wf_glob Σ' -> wf_glob Σ.
  Proof using Type.
    intros [? ->].
    induction x; cbn; auto.
    intros wf; depelim wf. eauto.
  Qed.

  Lemma extends_prefix_extends Σ Σ' :
    extends_prefix Σ Σ' -> wf_glob Σ' ->
    extends Σ Σ'.
  Proof.
    intros [Σ'' ->].
    induction Σ''; cbn; auto.
    - unfold extends; tauto.
    - intros wf; depelim wf.
      specialize (IHΣ'' wf).
      red in IHΣ''. intros ? ? H'; specialize (IHΣ'' _ _ H').
      cbn.
      case: (eqb_spec kn0 kn).
      + intros <-. now eapply lookup_env_Some_fresh in IHΣ''.
      + now intros _.
  Qed.

  Definition global_subset (Σ Σ' : global_declarations) :=
    forall kn d, lookup_env Σ kn = Some d -> lookup_env Σ' kn = Some d.

  Lemma lookup_env_In d Σ :
    wf_glob Σ ->
    lookup_env Σ d.1 = Some d.2 <-> In d Σ.
  Proof using Type.
    intros wf.
    split.
    - induction Σ; cbn => //.
      destruct (eqb_spec d.1 a.1). intros [=]. destruct a, d; cbn in *; intuition auto.
      left; subst; auto. depelim wf.
      intros hl; specialize (IHΣ wf hl); intuition auto.
    - induction wf => /= //.
      intros [eq|hin]; eauto. subst d.
      now rw eqb_refl.
      specialize (IHwf hin).
      destruct (eqb_spec d.1 kn). subst kn.
      eapply lookup_env_Some_fresh in IHwf. contradiction.
      exact IHwf.
  Qed.

  Lemma global_subset_In Σ Σ' :
    wf_glob Σ -> wf_glob Σ' ->
    global_subset Σ Σ' <-> forall d, In d Σ -> In d Σ'.
  Proof using Type.
    split.
    - intros g d hin.
      specialize (g d.1 d.2).
      eapply lookup_env_In => //.
      apply g. apply lookup_env_In => //.
    - intros hd kn d hl.
      eapply (lookup_env_In (kn, d)) in hl => //.
      eapply (lookup_env_In (kn, d)) => //. eauto.
  Qed.

  Lemma global_subset_cons d Σ Σ' :
    global_subset Σ Σ' ->
    global_subset (d :: Σ) (d :: Σ').
  Proof using Type.
    intros sub kn d'.
    cbn. case: eqb_spec => [eq|neq] => //.
    eapply sub.
  Qed.

  Lemma fresh_global_subset Σ Σ' kn :
    wf_glob Σ -> wf_glob Σ' ->
    global_subset Σ Σ' ->
    fresh_global kn Σ' -> fresh_global kn Σ.
  Proof using Type.
    intros wfΣ wfΣ' sub fr.
    unfold fresh_global in *.
    eapply All_Forall, In_All.
    intros [kn' d] hin. cbn.
    intros eq; subst.
    eapply global_subset_In in hin; tea.
    eapply Forall_All in fr. eapply All_In in fr; tea.
    destruct fr. cbn in H. congruence.
  Qed.

  Lemma global_subset_cons_right d Σ Σ' :
    wf_glob Σ -> wf_glob (d :: Σ') ->
    global_subset Σ Σ' ->
    global_subset Σ (d :: Σ').
  Proof using Type.
    intros wf wf' gs.
    assert (wf_glob Σ'). now depelim wf'.
    rw (global_subset_In _ _ wf H) in gs.
    rw global_subset_In //.
    intros decl. specialize (gs decl).
    intros hin; specialize (gs hin). cbn. now right.
  Qed.

End EEnvFlags.
