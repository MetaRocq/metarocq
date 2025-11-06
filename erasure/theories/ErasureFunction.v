(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
Set Equations Transparent.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction PCUICReflect PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp PCUICContextConversionTyp PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion PCUICUnivSubstitutionTyp PCUICCumulativity PCUICSR PCUICSafeLemmata PCUICNormalization
  PCUICValidity PCUICPrincipality PCUICElimination PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICEtaExpand.

From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICSafeReduce PCUICSafeRetyping PCUICRetypingEnvIrrelevance.
From MetaRocq.Erasure Require Import EPrimitive EAstUtils ELiftSubst EArities Extract Prelim EDeps ErasureProperties ErasureCorrectness.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Local Set Keyed Unification.
Set Default Proof Using "Type*".
Import MRMonadNotation.

Implicit Types (cf : checker_flags).

#[local] Existing Instance extraction_normalizing.

Notation alpha_eq := PCUICEquality.eq_context_upto_names.

Ltac sq :=
  repeat match goal with
        | H : ∥ _ ∥ |- _ => destruct H as [H]
        end; try eapply sq.

Lemma wf_local_rel_alpha_eq_end {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ'} :
  wf_local Σ Γ ->
  alpha_eq Δ Δ' ->
  wf_local_rel Σ Γ Δ -> wf_local_rel Σ Γ Δ'.
Proof.
  intros wfΓ eqctx wf.
  apply All_local_env_app_inv.
  eapply All_local_env_app in wf => //.
  eapply PCUICSpine.wf_local_alpha; tea.
  eapply All2_app => //. reflexivity.
Qed.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma on_minductive_wf_params_weaken {ind mdecl Γ} {u} :
    declared_minductive Σ.1 ind mdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ Γ ->
    wf_local Σ (Γ ,,, (ind_params mdecl)@[u]).
  Proof using wfΣ.
    intros.
    eapply weaken_wf_local; tea.
    eapply PCUICArities.on_minductive_wf_params; tea.
  Qed.

  Context {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).

  Lemma on_minductive_wf_params_indices_inst_weaken {Γ} (u : Instance.t) :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ Γ ->
    wf_local Σ (Γ ,,, (ind_params mdecl ,,, ind_indices idecl)@[u]).
  Proof using decli wfΣ.
    intros. eapply weaken_wf_local; tea.
    eapply PCUICInductives.on_minductive_wf_params_indices_inst; tea.
  Qed.

End OnInductives.

Infix "=kn" := KernameSet.Equal (at level 90).
Ltac knset := KernameSetDecide.fsetdec.

Lemma term_global_deps_csubst a k b :
  KernameSet.Subset (term_global_deps (ECSubst.csubst a k b))
    (KernameSet.union (term_global_deps a) (term_global_deps b)).
Proof.
  induction b in k |- * using EInduction.term_forall_list_ind; cbn; try knset; eauto.
  - destruct Nat.compare; knset.
  - specialize (IHb1 k); specialize (IHb2 (S k)); knset.
  - specialize (IHb1 k); specialize (IHb2 k); knset.
  - destruct i. intros kn. rewrite knset_in_fold_left.
    rewrite KernameSet.union_spec knset_in_fold_left.
    intuition auto. destruct H0 as [a' [hin hin']].
    eapply in_map_iff in hin as [cs [<- hin]].
    eapply All_In in X as [X]; tea. specialize (X k).
    specialize (X _ hin').
    eapply KernameSet.union_spec in X as []. knset.
    right; right. now exists cs.
  - destruct p. intros kn.
    rewrite !KernameSet.union_spec !knset_in_fold_left.
    specialize (IHb k kn). intuition auto. knset.
    destruct H as [? []].
    eapply in_map_iff in H as [cs [<- hin]].
    eapply All_In in X as [X]; tea. specialize (X _ _ H0). intuition auto; try knset.
    cbn in H0. apply KernameSet.union_spec in X as []; [knset|].
    right; right; right. now exists cs.
  - specialize (IHb k). knset.
  - intros kn; rewrite knset_in_fold_left !KernameSet.union_spec knset_in_fold_left.
    intuition auto.
    destruct H0 as [? []].
    eapply in_map_iff in H as [cs [<- hin]].
    eapply All_In in X as [X]; tea. specialize (X _ _ H0). intuition auto; try knset.
    cbn in H0. apply KernameSet.union_spec in X as []; [knset|].
    right; right. now exists cs.
  - intros kn; rewrite knset_in_fold_left !KernameSet.union_spec knset_in_fold_left.
    intuition auto.
    destruct H0 as [? []].
    eapply in_map_iff in H as [cs [<- hin]].
    eapply All_In in X as [X]; tea. specialize (X _ _ H0). intuition auto; try knset.
    cbn in H0. apply KernameSet.union_spec in X as []; [knset|].
    right; right. now exists cs.
  - intros kn.
    funelim (prim_global_deps term_global_deps p); cbn; simp prim_global_deps; try knset.
    rewrite !knset_in_fold_left !KernameSet.union_spec; cbn.
    dependent elimination X as [EPrimitive.primPropArray (pair s al)].
    rewrite knset_in_fold_left.
    intuition eauto.
    * eapply s in H0. rewrite KernameSet.union_spec in H0. intuition eauto.
    * destruct H0 as [a [ha hkn]].
      eapply in_map_iff in ha as [x [heq hx]]. subst a.
      eapply All_In in al as [al]; tea.
      eapply al in hkn.
      rewrite KernameSet.union_spec in hkn. destruct hkn; eauto.
Qed.


Arguments KernameSet.mem : simpl never.

Lemma lookup_env_In Σ kn d : EGlobalEnv.lookup_env Σ kn = Some d -> In kn (map fst Σ).
Proof.
  induction Σ; cbn; auto.
  - easy.
  - destruct (eqb_spec kn a.1).
    intros [= <-]. left; auto.
    intros hl; right; auto.
Qed.


Notation terms_global_deps l :=
  (fold_left (fun (acc : KernameSet.t) (x : EAst.term) =>
   KernameSet.union (term_global_deps x) acc) l
    KernameSet.empty).

Lemma term_global_deps_fresh {efl : EWellformed.EEnvFlags} Σ k t :
  EWellformed.wellformed Σ k t ->
  forall kn, KernameSet.In kn (term_global_deps t) -> In kn (map fst Σ).
Proof.
  induction t in k |- * using EInduction.term_forall_list_ind; intros; try (cbn in *; try knset;
    rtoProp; intuition eauto).
  all:try eapply KernameSet.union_spec in H0; intuition eauto.
  - apply KernameSet.singleton_spec in H0. subst s.
    destruct (EGlobalEnv.lookup_env Σ kn) eqn:E.
    destruct g => //. destruct c => //. cbn in H1.
    now eapply lookup_env_In in E. easy.
  - destruct i. rewrite knset_in_fold_left in H0.
    destruct H0.
    apply KernameSet.singleton_spec in H0. subst kn.
    destruct (EGlobalEnv.lookup_env Σ _) eqn:E.
    destruct g => //. cbn in E.
    now eapply lookup_env_In in E. easy.
    destruct H0 as [a []].
    eapply All_In in X as [X]; tea. specialize (X k).
    destruct EWellformed.cstr_as_blocks. move/andP: H1 => [_ wf].
    solve_all. eapply All_In in wf as [wf]; tea. now specialize (X wf kn).
    destruct args => //.
  - destruct p. rewrite KernameSet.union_spec knset_in_fold_left in H0.
    destruct H0.
    apply KernameSet.singleton_spec in H0. subst kn. cbn in *.
    move: H1; rewrite /EWellformed.wf_brs; cbn.
    destruct (EGlobalEnv.lookup_env Σ _) eqn:E.
    destruct g => //.
    now eapply lookup_env_In in E. easy. clear H1.
    destruct H0. now apply (IHt k H3).
    destruct H0 as [a []].
    eapply All_In in X as [X]; tea.
    solve_all. eapply All_In in H2 as [wf]; tea. now specialize (X _ wf kn).
  - apply KernameSet.singleton_spec in H3. subst kn. cbn in *.
    destruct (EGlobalEnv.lookup_env Σ _) eqn:E.
    destruct g => //.
    now eapply lookup_env_In in E. easy.
  - rewrite knset_in_fold_left in H0; destruct H0; [knset|].
    destruct H0 as [a []].
    unfold EWellformed.wf_fix_gen in H1. move/andP: H1 => [_ hm]. solve_all.
    eapply All_In in hm as [hm]; tea. intuition auto.
    eapply (a0 (#|m| + k)) => //.
  - rewrite knset_in_fold_left in H0; destruct H0; [knset|].
    destruct H0 as [a []].
    unfold EWellformed.wf_fix_gen in H1. move/andP: H1 => [_ hm]. solve_all.
    eapply All_In in hm as [hm]; tea. intuition auto.
    eapply (a0 (#|m| + k)) => //.
  - primProp.
    move: H0; funelim (prim_global_deps term_global_deps p); try knset.
    rewrite knset_in_fold_left. depelim H2. intuition eauto.
    destruct H1 as [ar []]. eapply All_In in b as [[]]; tea. eauto.
Qed.

Lemma knset_mem_spec kn s : reflect (KernameSet.In kn s) (KernameSet.mem kn s).
Proof.
  destruct (KernameSet.mem_spec s kn).
  destruct (KernameSet.mem kn s).
  - now constructor.
  - constructor. intros hin. now apply H0 in hin.
Qed.

Definition constant_decls_deps decl :=
  match decl with
  | {| EAst.cst_body := Some b |} => term_global_deps b
  | _ => KernameSet.empty
  end.

Definition global_decl_deps decl :=
  match decl with
  | EAst.ConstantDecl cst => constant_decls_deps cst
  | _ => KernameSet.empty
  end.

Fixpoint global_deps (Σ : EAst.global_declarations) deps :=
  match Σ with
  | [] => deps
  | (kn, decl) :: decls =>
    if KernameSet.mem kn deps then
      global_deps decls
        (KernameSet.union deps (global_decl_deps decl))
    else global_deps decls deps
  end.

Lemma global_deps_union Σ deps deps' :
  global_deps Σ (KernameSet.union deps deps') =kn
  KernameSet.union (global_deps Σ deps) (global_deps Σ deps').
Proof.
  induction Σ in deps, deps' |- *; auto.
  - reflexivity.
  - destruct a. cbn -[KernameSet.mem].
    destruct (knset_mem_spec k deps').
    * case: (knset_mem_spec k _).
      move/KernameSet.union_spec => hin.
      destruct hin.
      eapply KernameSet.mem_spec in H. rewrite H.
      rewrite !IHΣ. knset.
      ** case: (knset_mem_spec k _); intros hin';
        rewrite !IHΣ; knset.
      ** intros hin'.
         case: (knset_mem_spec k _); intros hin'';
        rewrite !IHΣ; knset.
    * case: (knset_mem_spec k _); intros hin''.
      case: (knset_mem_spec k _); intros hin'''.
      rewrite !IHΣ. knset.
      rewrite !IHΣ. knset.
      case: (knset_mem_spec k _); intros hin'''.
      rewrite !IHΣ. knset.
      rewrite !IHΣ. knset.
Qed.

Lemma in_global_deps deps Σ :
  KernameSet.Subset deps (global_deps Σ deps).
Proof.
  induction Σ => //.
  destruct a as [kn [[[]]|]]; cbn; eauto;
  case: (knset_mem_spec kn _); intros hin''';
  rewrite ?global_deps_union;
   intros h hin; rewrite ?KernameSet.union_spec; try left; knset.
Qed.

Lemma global_deps_subset Σ deps deps' :
  KernameSet.Subset deps deps' ->
  KernameSet.Subset (global_deps Σ deps) (global_deps Σ deps').
Proof.
  induction Σ in deps, deps' |- *.
  - cbn. auto.
  - destruct a; cbn.
    intros sub.
    case: (knset_mem_spec k deps) => hin.
    eapply sub in hin. eapply KernameSet.mem_spec in hin. rewrite hin.
    rewrite !global_deps_union.
    specialize (IHΣ _ _ sub). knset.
    case: (knset_mem_spec k deps') => hin'.
    rewrite !global_deps_union.
    specialize (IHΣ _ _ sub). knset.
    now eapply IHΣ.
Qed.

Lemma wf_global_decl_deps {efl : EWellformed.EEnvFlags} Σ d :
  EWellformed.wf_global_decl Σ d ->
  forall kn, KernameSet.In kn (global_decl_deps d) -> In kn (map fst Σ).
Proof.
  intros wf kn hin.
  destruct d as [[[]]|] => //; cbn in hin.
    * eapply term_global_deps_fresh in hin. exact hin. cbn in wf; tea.
    * knset.
    * knset.
Qed.

Lemma lookup_global_deps {efl : EWellformed.EEnvFlags} Σ kn decl :
  EWellformed.wf_glob Σ ->
  EGlobalEnv.lookup_env Σ kn = Some decl ->
  forall kn, KernameSet.In kn (global_decl_deps decl) -> In kn (map fst Σ).
Proof.
  induction 1 in kn, decl |- *.
  - cbn => //.
  - cbn.
    case: (eqb_spec kn kn0) => heq.
    subst kn0; intros [= <-].
    intros kn' hkn'.
    * eapply wf_global_decl_deps in H0; tea. now right.
    * intros hl kn' kin.
      eapply IHwf_glob in hl; tea. now right.
Qed.

Lemma fresh_global_In kn Σ : EGlobalEnv.fresh_global kn Σ <-> ~ In kn (map fst Σ).
Proof.
  split.
  - intros fr.
    eapply (Forall_map (fun x => x <> kn) fst) in fr.
    intros hin.
    now eapply PCUICWfUniverses.Forall_In in fr; tea.
  - intros nin.
    red. eapply In_Forall. intros kn' hin <-.
    eapply nin. now eapply (in_map fst).
Qed.

Lemma global_deps_kn {fl :EWellformed.EEnvFlags} Σ kn decl :
  EWellformed.wf_glob Σ ->
  EGlobalEnv.declared_constant Σ kn decl ->
  KernameSet.Subset (global_deps Σ (constant_decls_deps decl)) (global_deps Σ (KernameSet.singleton kn)).
Proof.
  induction 1 in kn, decl |- *.
  - cbn. unfold EGlobalEnv.declared_constant. cbn => //.
  - cbn. unfold EGlobalEnv.declared_constant. cbn => //.
    destruct (eqb_spec kn kn0). subst kn0. cbn. intros [= ->].
    + case: (knset_mem_spec kn _) => hin.
      * eapply wf_global_decl_deps in H0; tea.
        now eapply fresh_global_In in H1.
      * case: (knset_mem_spec kn _) => hin'.
        rewrite !global_deps_union. cbn. knset.
        knset.

    + intros hl.
      case: (knset_mem_spec kn0 _) => hin.
      * exfalso.
        eapply lookup_global_deps in hl; tea.
        now eapply fresh_global_In in H1.
      * case: (knset_mem_spec kn0 _).
       ** move/KernameSet.singleton_spec. intros <-. congruence.
      ** intros hnin. now eapply IHwf_glob.
Qed.

Lemma term_global_deps_mkApps f args :
  term_global_deps (EAst.mkApps f args) =kn
  KernameSet.union (term_global_deps f) (terms_global_deps args).
Proof.
  induction args in f |- *.
  - cbn; knset.
  - cbn. rewrite IHargs. cbn.
    intros kn.
    rewrite !KernameSet.union_spec !knset_in_fold_left KernameSet.union_spec.
    intuition auto.
Qed.

From Stdlib Require Import Morphisms.

#[export] Instance global_deps_proper : Proper (eq ==> KernameSet.Equal ==> KernameSet.Equal) global_deps.
Proof.
  intros ? ? -> kns kns' eq.
  induction y in kns, kns', eq |- *; cbn; auto; try knset.
  destruct a. setoid_rewrite eq. destruct KernameSet.mem. rewrite IHy; [|reflexivity].
  now rewrite eq. now apply IHy.
Qed.

#[export] Instance global_deps_proper_subset : Proper (eq ==> KernameSet.Subset ==> KernameSet.Subset) global_deps.
Proof.
  intros ? ? -> kns kns' eq.
  induction y in kns, kns', eq |- *; cbn; auto; try knset.
  destruct a. destruct (knset_mem_spec k kns). eapply eq in i.
  eapply KernameSet.mem_spec in i. rewrite i. eapply IHy. knset.
  destruct (knset_mem_spec k kns'). specialize (IHy _ _ eq).
  rewrite global_deps_union. knset.
  eauto.
Qed.

Lemma term_global_deps_substl defs body :
  KernameSet.Subset (term_global_deps (ECSubst.substl defs body))
    (KernameSet.union (terms_global_deps defs) (term_global_deps body)).
Proof.
  intros kn. rewrite KernameSet.union_spec.
  unfold ECSubst.substl.
  induction defs in body |- *; cbn; auto.
  - intros hin. eapply IHdefs in hin as []; eauto. left.
    rewrite knset_in_fold_left. right.
    rewrite knset_in_fold_left in H.
    intuition. knset.
    rewrite knset_in_fold_left.
    eapply term_global_deps_csubst in H.
    intuition knset.
Qed.

Lemma terms_global_deps_rev l : terms_global_deps (List.rev l) =kn terms_global_deps l.
Proof.
  intros kn.
  rewrite !knset_in_fold_left. intuition auto; try knset.
  - destruct H0 as [x []]; right. exists x. now eapply In_rev in H.
  - destruct H0 as [x []]; right. exists x. now eapply In_rev in H.
Qed.

Lemma In_skipn {A} n (l : list A) : forall x, In x (skipn n l) -> In x l.
Proof.
  induction l in n |- *; destruct n => //.
  rewrite skipn_S. intros x hin; right; eauto.
Qed.

Lemma terms_global_deps_skipn n l : KernameSet.Subset (terms_global_deps (List.skipn n l)) (terms_global_deps l).
Proof.
  intros kn.
  rewrite !knset_in_fold_left. intuition auto; try knset.
  destruct H0 as [x []]; right. eapply In_skipn in H. now exists x.
Qed.


Lemma term_global_deps_iota_red pars args br :
  KernameSet.Subset (term_global_deps (EGlobalEnv.iota_red pars args br))
    (KernameSet.union (terms_global_deps args) (term_global_deps br.2)).
Proof.
  intros kn hin.
  eapply term_global_deps_substl in hin.
  rewrite !KernameSet.union_spec in hin *. intuition auto. left.
  rewrite terms_global_deps_rev in H.
  now apply terms_global_deps_skipn in H.
Qed.

Lemma fold_left_eq {A} f acc l :
  fold_left (fun acc (x : A) => KernameSet.union (f x) acc) l acc =kn
  KernameSet.union (fold_left (fun acc x => KernameSet.union (f x) acc) l KernameSet.empty) acc.
Proof.
  induction l in acc |- *; cbn. knset.
  rewrite IHl. rewrite (IHl (KernameSet.union _ _)). knset.
Qed.

Lemma term_global_deps_repeat t n : KernameSet.Subset (terms_global_deps (repeat t n)) (term_global_deps t).
Proof.
  induction n; cbn; auto; try knset.
  intros kn hin.
  rewrite fold_left_eq in hin.
  rewrite KernameSet.union_spec in hin. intuition auto.
  rewrite KernameSet.union_spec in H; intuition auto.
  knset.
Qed.

Notation terms_global_deps_gen f l :=
  (fold_left
    (fun (acc : KernameSet.t) (x : _) =>
    KernameSet.union (term_global_deps (f x)) acc) l KernameSet.empty).

Lemma term_global_deps_fix_subst mfix :
  KernameSet.Subset (terms_global_deps (EGlobalEnv.fix_subst mfix)) (terms_global_deps_gen EAst.dbody mfix).
Proof.
  unfold EGlobalEnv.fix_subst.
  induction #|mfix|; cbn.
  - knset.
  - rewrite fold_left_eq.
    intros kn. rewrite KernameSet.union_spec.
    intros [].
    + now eapply IHn in H.
    + knset.
Qed.

Lemma term_global_deps_cunfold_fix mfix idx n f :
  EGlobalEnv.cunfold_fix mfix idx = Some (n, f) ->
  KernameSet.Subset (term_global_deps f) (terms_global_deps_gen EAst.dbody mfix).
Proof.
  unfold EGlobalEnv.cunfold_fix.
  destruct nth_error eqn:E => //.
  intros [= <- <-].
  intros kn hin.
  eapply term_global_deps_substl in hin.
  rewrite KernameSet.union_spec in hin.
  destruct hin.
  now eapply term_global_deps_fix_subst in H.
  eapply nth_error_In in E.
  rewrite knset_in_fold_left. right. now exists d.
Qed.

Lemma term_global_deps_cofix_subst mfix :
  KernameSet.Subset (terms_global_deps (EGlobalEnv.cofix_subst mfix)) (terms_global_deps_gen EAst.dbody mfix).
Proof.
  unfold EGlobalEnv.cofix_subst.
  induction #|mfix|; cbn.
  - knset.
  - rewrite fold_left_eq.
    intros kn. rewrite KernameSet.union_spec.
    intros [].
    + now eapply IHn in H.
    + knset.
Qed.

Lemma term_global_deps_cunfold_cofix mfix idx n f :
  EGlobalEnv.cunfold_cofix mfix idx = Some (n, f) ->
  KernameSet.Subset (term_global_deps f) (terms_global_deps_gen EAst.dbody mfix).
Proof.
  unfold EGlobalEnv.cunfold_cofix.
  destruct nth_error eqn:E => //.
  intros [= <- <-].
  intros kn hin.
  eapply term_global_deps_substl in hin.
  rewrite KernameSet.union_spec in hin.
  destruct hin.
  now eapply term_global_deps_cofix_subst in H.
  eapply nth_error_In in E.
  rewrite knset_in_fold_left. right. now exists d.
Qed.

Lemma global_deps_empty Σ : global_deps Σ KernameSet.empty = KernameSet.empty.
Proof.
  induction Σ; cbn; auto.
  destruct a as [kn d].
  destruct (knset_mem_spec kn KernameSet.empty).
  knset. auto.
Qed.

Lemma eval_global_deps {fl : EWcbvEval.WcbvFlags} {efl : EWellformed.EEnvFlags} Σ t t' :
  EWellformed.wf_glob Σ ->
  Σ ⊢ t ⇓ t' -> KernameSet.Subset (global_deps Σ (term_global_deps t')) (global_deps Σ (term_global_deps t)).
Proof.
  intros wf.
  induction 1 using EWcbvEval.eval_ind; cbn; rewrite ?global_deps_union; try knset.
  - cbn in IHeval1.
    epose proof (term_global_deps_csubst a' 0 b).
    eapply (global_deps_subset Σ) in H2.
    rewrite global_deps_union in H2.
    knset.
  - epose proof (term_global_deps_csubst b0' 0 b1).
    eapply (global_deps_subset Σ) in H1.
    rewrite global_deps_union in H1.
    knset.
  - rewrite term_global_deps_mkApps in IHeval1.
    rewrite global_deps_union /= in IHeval1. destruct ind; cbn in *.
    intros kn hr.
    eapply IHeval2 in hr.
    eapply global_deps_proper_subset in hr.
    3:eapply (term_global_deps_iota_red pars args br). 2:reflexivity.
    rewrite global_deps_union KernameSet.union_spec in hr.
    specialize (IHeval1 kn); rewrite !KernameSet.union_spec in IHeval1 *.
    right.
    destruct hr.
    eapply global_deps_proper_subset. reflexivity.
    intros kn'. rewrite knset_in_fold_left. intros; left; eauto.
    now eapply IHeval1.
    rewrite fold_left_eq global_deps_union KernameSet.union_spec. left.
    eapply global_deps_proper_subset. reflexivity.
    intros kn'. rewrite knset_in_fold_left. intros; right.
    eapply nth_error_In in e2. exists br; split. auto. exact H2.
    exact H1.
  - intros kn hr.
    eapply IHeval2 in hr.
    eapply global_deps_proper_subset in hr; [|reflexivity|].
    2:eapply term_global_deps_iota_red.
    rewrite global_deps_union KernameSet.union_spec in hr.
    rewrite KernameSet.union_spec.
    right.
    eapply global_deps_proper_subset. reflexivity.
    intros kn'. rewrite fold_left_eq. intros h; exact h.
    rewrite global_deps_union KernameSet.union_spec.
    destruct hr. right. eapply IHeval1. cbn. destruct ind.
    now rewrite fold_left_eq global_deps_union KernameSet.union_spec.
    left.
    eapply global_deps_proper_subset. reflexivity.
    intros kn'. rewrite knset_in_fold_left. intros; right.
    eapply nth_error_In in e2. exists br; split. auto. exact H2.
    exact H1.
  - intros kn hr. eapply IHeval2 in hr.
    rewrite KernameSet.union_spec.
    eapply global_deps_proper_subset in hr; [|reflexivity|].
    2:eapply term_global_deps_substl.
    right. rewrite fold_left_eq global_deps_union KernameSet.union_spec.
    subst brs. cbn. left.
    rewrite global_deps_union KernameSet.union_spec in hr. destruct hr.
    eapply global_deps_proper_subset. reflexivity. 2:exact H1.
    setoid_rewrite term_global_deps_repeat. cbn. knset.
    now rewrite global_deps_union KernameSet.union_spec.
  - intros kn hin. eapply IHeval3 in hin.
    cbn in hin. rewrite global_deps_union KernameSet.union_spec in hin.
    rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec in hin.
    rewrite KernameSet.union_spec. intuition auto.
    + left. eapply IHeval1.
      rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec. left.
      cbn. eapply term_global_deps_cunfold_fix in e1.
      now setoid_rewrite e1 in H3.
    + left. eapply IHeval1.
      rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec. now right.
  - intros kn hin. eapply IHeval3 in hin.
    cbn in hin. rewrite global_deps_union KernameSet.union_spec in hin.
    rewrite KernameSet.union_spec. intuition auto.
    left. eapply IHeval1. cbn.
    eapply term_global_deps_cunfold_fix in e0.
    now setoid_rewrite e0 in H2.
  - intros kn hin. eapply IHeval2 in hin.
    cbn in hin. destruct ip.
    rewrite global_deps_union KernameSet.union_spec in hin.
    rewrite global_deps_union KernameSet.union_spec. intuition auto. right.
    rewrite fold_left_eq. rewrite fold_left_eq in H1.
    rewrite global_deps_union KernameSet.union_spec in H1.
    rewrite global_deps_union KernameSet.union_spec. intuition auto.
    rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec in H2.
    right. eapply IHeval1.
    rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec. intuition auto.
    left. cbn.
    eapply term_global_deps_cunfold_cofix in e0.
    now setoid_rewrite e0 in H1.
  - intros kn hin. eapply IHeval2 in hin.
    cbn in hin. rewrite global_deps_union KernameSet.union_spec in hin.
    rewrite KernameSet.union_spec. intuition auto. right.
    eapply IHeval1. cbn.
    rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec in H1.
    rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec.
    intuition auto. left.
    eapply term_global_deps_cunfold_cofix in e0.
    now setoid_rewrite e0 in H2.
  - cbn.
    epose proof (global_deps_kn Σ c decl wf isdecl).
    unfold constant_decls_deps in H0. destruct decl => //.
    cbn in e. subst cst_body0. knset.
  - move=> kn /IHeval2 hin.
    rewrite KernameSet.union_spec; right. eapply IHeval1.
    rewrite term_global_deps_mkApps global_deps_union KernameSet.union_spec.
    right. eapply nth_error_In in e3.
    eapply global_deps_proper_subset. reflexivity. 2:exact hin.
    intros k h. rewrite knset_in_fold_left. right. now exists a.
  - eapply nth_error_In in e3.
    move=> kn /IHeval2 hin.
    rewrite KernameSet.union_spec. right; apply IHeval1; cbn.
    destruct proj_ind. rewrite fold_left_eq.
    rewrite global_deps_union KernameSet.union_spec. left.
    eapply global_deps_proper_subset. reflexivity.
    intros kn'. rewrite knset_in_fold_left. intros; right. 2:tea.
    now exists a.
  - destruct ind.
    rewrite fold_left_eq. rewrite (fold_left_eq _ (KernameSet.singleton _)).
    intros kn. rewrite !global_deps_union !KernameSet.union_spec. intuition auto.
    left. clear -a iha H0.
    induction a; auto.
    move: H0. cbn.
    rewrite fold_left_eq (fold_left_eq _ (KernameSet.union _ _)).
    rewrite !global_deps_union !KernameSet.union_spec.
    destruct iha as [sub ih]. specialize (IHa ih). intuition eauto.
  - depelim X; cbn; simp prim_global_deps; try knset.
    eapply All2_over_undep in a.
    eapply All2_Set_All2 in ev. cbn. solve_all.
    rewrite fold_left_eq.
    intros hin h.
    rewrite fold_left_eq.
    rewrite !global_deps_union !KernameSet.union_spec in h *. intuition eauto. left.
    clear -H a. induction a. cbn; knset. cbn in H |- *.
    rewrite fold_left_eq global_deps_union !KernameSet.union_spec in H.
    rewrite fold_left_eq !global_deps_union !KernameSet.union_spec. intuition eauto.
    rewrite global_deps_union !KernameSet.union_spec in H0. intuition auto; try knset.
Qed.

Lemma in_global_deps_fresh {efl : EWellformed.EEnvFlags} kn Σ deps :
  EWellformed.wf_glob Σ ->
  KernameSet.In kn (global_deps Σ deps) ->
  EGlobalEnv.fresh_global kn Σ ->
  KernameSet.In kn deps.
Proof.
  induction Σ in deps |- *.
  - now cbn.
  - intros wf. destruct a as [kn' d]; cbn. depelim wf.
    case: (knset_mem_spec kn' deps) => hin.
    * rewrite global_deps_union KernameSet.union_spec.
      intros [] fr.
    ** depelim fr. now eapply IHΣ.
    ** depelim fr. exfalso. eapply IHΣ in H1; eauto.
      destruct d as [[[]]|] eqn:eqd; cbn in H.
      + cbn in H1. eapply (term_global_deps_fresh Σ) in H1; tea. cbn in H2.
        eapply (Forall_map (fun x => x <> kn) fst) in fr.
        now eapply PCUICWfUniverses.Forall_In in fr.
      + cbn in H1; knset.
      + cbn in H1; knset.
    * intros hin' fr. depelim fr. now eapply IHΣ.
Qed.

Local Existing Instance extraction_checker_flags.
(* Definition wf_ext_wf Σ : wf_ext Σ -> wf Σ := fst.
#[global]
Hint Resolve wf_ext_wf : core. *)

Ltac specialize_Σ wfΣ :=
  repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end.

Section fix_sigma.

  Context {cf : checker_flags} {nor : normalizing_flags}.
  Context (X_type : abstract_env_impl).
  Context (X : X_type.π2.π1).
  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.
  Local Definition HΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Definition term_rel : Relation_Definitions.relation
    (∑ Γ t, forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :=
    fun '(Γ2; B; H) '(Γ1; t1; H2) =>
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
    ∥∑ na A, red Σ Γ1 t1 (tProd na A B) × (Γ1,, vass na A) = Γ2∥.

  Definition cod B t := match t with tProd _ _ B' => B = B' | _ => False end.

  Lemma wf_cod : WellFounded cod.
  Proof using Type.
    sq. intros ?. induction a; econstructor; cbn in *; intros; try tauto; subst. eauto.
  Defined.

  Lemma wf_cod' : WellFounded (Relation_Operators.clos_trans _ cod).
  Proof using Type.
    eapply Subterm.WellFounded_trans_clos. exact wf_cod.
  Defined.

  Lemma Acc_no_loop A (R : A -> A -> Prop) t : Acc R t -> R t t -> False.
  Proof using Type.
    induction 1. intros. eapply H0; eauto.
  Qed.

  Ltac sq' :=
    repeat match goal with
          | H : ∥ _ ∥ |- _ => destruct H; try clear H
          end; try eapply sq.

  Definition wf_reduction_aux : WellFounded term_rel.
  Proof using normalization_in.
    intros (Γ & s & H). sq'.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ']].
    pose proof (abstract_env_ext_wf _ wfΣ') as wf. sq.
    set (H' := H _ wfΣ').
    induction (normalization_in Σ wf wfΣ' Γ s H') as [s _ IH]. cbn in IH.
    induction (wf_cod' s) as [s _ IH_sub] in Γ, H , H', IH |- *.
    econstructor.
    eintros (Γ' & B & ?) [(na & A & ? & ?)]; eauto. subst.
    eapply Relation_Properties.clos_rt_rtn1 in r. inversion r.
      + subst. eapply IH_sub. econstructor. cbn. reflexivity.
        intros. eapply IH.
        inversion H0.
        * subst. econstructor. eapply prod_red_r.  eassumption.
        * subst. eapply cored_red in H2 as [].
          eapply cored_red_trans. 2: eapply prod_red_r. 2:eassumption.
          eapply PCUICReduction.red_prod_r. eauto.
        * constructor. do 2 eexists. now split.
      + subst. eapply IH.
        * eapply red_neq_cored.
          eapply Relation_Properties.clos_rtn1_rt. exact r.
          intros ?. subst.
          eapply Relation_Properties.clos_rtn1_rt in X1.
          eapply cored_red_trans in X0; [| exact X1 ].
          eapply Acc_no_loop in X0. eauto.
          eapply @normalization_in; eauto.
        * constructor. do 2 eexists. now split.
  Unshelve.
  - intros. destruct H' as [].
    rewrite <- (abstract_env_ext_irr _ H2) in X0; eauto.
    rewrite <- (abstract_env_ext_irr _ H2) in wf; eauto.
    eapply inversion_Prod in X0 as (? & ? & h1 & ? & ?) ; auto.
    eapply cored_red in H0 as [].
    econstructor. econstructor; tea.
    rewrite <- (abstract_env_ext_irr _ H2) in X0; eauto.
    eapply subject_reduction; eauto.
  - intros. rewrite <- (abstract_env_ext_irr _ H0) in wf; eauto.
    rewrite <- (abstract_env_ext_irr _ H0) in X0; eauto.
    rewrite <- (abstract_env_ext_irr _ H0) in r; eauto.
    eapply red_welltyped; sq.
    3:eapply Relation_Properties.clos_rtn1_rt in r; eassumption.
    all:eauto.
  Defined.

  Instance wf_reduction : WellFounded term_rel.
  Proof using normalization_in.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_reduction_aux.
  Defined.

  Opaque wf_reduction.

  #[tactic="idtac"]
  Equations? is_arity Γ (HΓ : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥wf_local Σ Γ∥) T
    (HT : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ T) : bool
    by wf ((Γ;T;HT) : (∑ Γ t, forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)) term_rel :=
      {
        is_arity Γ HΓ T HT with inspect (@reduce_to_sort _ _ X_type X _ Γ T HT) => {
        | exist (Checked_comp H) rsort => true ;
        | exist (TypeError_comp _) rsort with
            inspect (@reduce_to_prod _ _ X_type X _ Γ T HT) => {
          | exist (Checked_comp (na; A; B; H)) rprod := is_arity (Γ,, vass na A) _ B _
          | exist (TypeError_comp e) rprod => false } }
      }.
  Proof using Type.
    - clear rprod is_arity rsort a0.
      intros Σ' wfΣ'; specialize (H Σ' wfΣ').
      repeat specialize_Σ wfΣ'.
      destruct HT as [s HT].
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      sq.
      eapply subject_reduction_closed in HT; tea.
      eapply inversion_Prod in HT as [? [? [? [t0 ?]]]].
      now eapply typing_wf_local in t0. pcuic. pcuic.
    - clear rprod is_arity rsort a0.
      intros Σ' wfΣ'; specialize (H Σ' wfΣ').
      repeat specialize_Σ wfΣ'.
      destruct HT as [s HT].
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      sq.
      eapply subject_reduction_closed in HT; tea.
      eapply inversion_Prod in HT as [? [? [? []]]].
      now eexists. all:pcuic.
    - cbn. clear rsort is_arity rprod.
      intros Σ' wfΣ'; specialize (H Σ' wfΣ').
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      repeat specialize_Σ wfΣ'.
      destruct HT as [s HT].
      sq.
      eapply subject_reduction_closed in HT; tea. 2:pcuic.
      eapply inversion_Prod in HT as [? [? [? []]]]. 2:pcuic.
      exists na, A. split => //.
      eapply H.
  Defined.

  Lemma is_arityP Γ (HΓ : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥wf_local Σ Γ∥) T
    (HT : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ T) :
    reflect (forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
              Is_conv_to_Arity Σ Γ T) (is_arity Γ HΓ T HT).
  Proof using Type.
    funelim (is_arity Γ HΓ T HT).
    - constructor.
      destruct H as [s Hs]. clear H0 rsort.
      pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (Hs _ wfΣ) as [Hs].
      intros. rewrite (abstract_env_ext_irr _ H wfΣ).
      exists (tSort s); split => //.
    - clear H0 H1.
      destruct X0; constructor; clear rprod rsort.
      * red.
        pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
        specialize_Σ wfΣ. sq.
        intros. rewrite (abstract_env_ext_irr _ H0 wfΣ).
        destruct i as [T' [[HT'] isa]].
        exists (tProd na A T'); split => //. split.
        etransitivity; tea. now eapply closed_red_prod_codom.
      * pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
        pose proof (abstract_env_ext_wf X wfΣ) as [wfΣ'].
        specialize_Σ wfΣ. sq.
        eintros [T' [[HT'] isa]]; eauto.
        destruct (PCUICContextConversion.closed_red_confluence H HT') as (? & ? & ?); eauto.
        eapply invert_red_prod in c as (? & ? & []); eauto. subst.
        apply n. intros. rewrite (abstract_env_ext_irr _ H0 wfΣ).
        red. exists x1.
        split => //.
        eapply isArity_red in isa. 2:exact c0.
        now cbn in isa.
    - constructor.
      clear H H0. pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      pose proof (abstract_env_ext_wf X wfΣ) as [wfΣ'].
      symmetry in rprod. symmetry in rsort.
      intros isc. specialize_Σ wfΣ.
      eapply Is_conv_to_Arity_inv in isc as [].
      * destruct H as [na [A [B [Hr]]]].
        apply e. exists na, A, B.
        intros ? H. now rewrite (abstract_env_ext_irr _ H wfΣ).
      * destruct H as [u [Hu]].
        apply a0. exists u.
        intros ? H. now rewrite (abstract_env_ext_irr _ H wfΣ).
  Qed.

End fix_sigma.

Opaque wf_reduction_aux.
Transparent wf_reduction.

(** Deciding if a term is erasable or not as a total function on well-typed terms.
  A term is erasable if:
  - it represents a type, i.e., its type is an arity
  - it represents a proof: its sort is Prop.
*)

Derive NoConfusion for typing_result_comp.

Opaque is_arity type_of_typing.

Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

Equations inspect_bool (b : bool) : { b } + { ~~ b } :=
  inspect_bool true := left eq_refl;
  inspect_bool false := right eq_refl.

#[tactic="idtac"]
Equations? is_erasableb X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} (Γ : context) (T : PCUICAst.term)
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ T) : bool :=
  is_erasableb X_type X Γ t wt with @type_of_typing extraction_checker_flags _ X_type X _ Γ t wt :=
    { | T with is_arity X_type X Γ _ T.π1 _ :=
      { | true => true
        | false => let s := @sort_of_type extraction_checker_flags _ X_type X _ Γ T.π1 _ in
          Sort.is_propositional s.π1 } }.
  Proof.
    - intros. specialize_Σ H. destruct wt; sq.
      pcuic.
    - intros. specialize_Σ H. destruct T as [T Ht].
      cbn. destruct (Ht Σ H) as [[tT Hp]].
      pose proof (abstract_env_ext_wf X H) as [wf].
      eapply validity in tT. pcuic.
    - intros. destruct T as [T Ht].
      cbn in *. specialize (Ht Σ H) as [[tT Hp]].
      pose proof (abstract_env_ext_wf X H) as [wf].
      eapply validity in tT. now sq.
  Qed.
Transparent is_arity type_of_typing.

Lemma is_erasableP {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {Γ : context} {t : PCUICAst.term}
  {wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t} :
  reflect (forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
           ∥ isErasable Σ Γ t ∥) (is_erasableb X_type X Γ t wt).
Proof.
  funelim (is_erasableb X_type X Γ t wt).
  - constructor. intros. pose proof (abstract_env_ext_wf _ H) as [wf].
    destruct type_of_typing as [x Hx]. cbn -[is_arity sort_of_type] in *.
    destruct (Hx _ H) as [[HT ?]].
    move/is_arityP: Heq => / (_ _ H) [T' [redT' isar]]. specialize_Σ H.
    sq. red. exists T'. eapply type_reduction_closed in HT.
    2: eassumption. eauto.
  - destruct type_of_typing as [x Hx]. cbn -[sort_of_type is_arity] in *.
    destruct (sort_of_type _ _ _ _). cbn.
    destruct (Sort.is_propositional x0) eqn:isp; constructor.
    * clear Heq; try clear Heqcall. intros.
      pose proof (abstract_env_ext_wf _ H) as [wf].
      specialize_Σ H.
      destruct Hx as [[HT ?]].
      destruct s as [Hs]. sq.
      exists x; split => //. right.
      exists x0. now split.
    * try clear Heqcall; pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      move => / (_ _ wfΣ) [[T' [HT' er]]].
      pose proof (abstract_env_ext_wf _ wfΣ) as [wf].
      move/is_arityP: Heq => nisa.
      specialize_Σ wfΣ.
      destruct Hx as [[HT ?]].
      specialize (p _ HT').
      destruct er as [isa|[u' [Hu' isp']]].
      { apply nisa. intros. rewrite (abstract_env_ext_irr _ H wfΣ).
        eapply invert_cumul_arity_r; tea. }
      { destruct s as [Hs].
        unshelve epose proof (H := unique_sorting_equality_propositional _ wf Hs Hu' p) => //. congruence. }
  Qed.

Equations? is_erasable {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} (Γ : context) (t : PCUICAst.term)
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
    { ∥ isErasable Σ Γ t ∥ } + { ∥ isErasable Σ Γ t -> False ∥ } :=
  is_erasable Γ T wt Σ wfΣ with inspect_bool (is_erasableb X_type X Γ T wt) :=
    { | left ise => left _
      | right nise => right _ }.
Proof.
  pose proof (abstract_env_ext_wf _ wfΣ) as [wf].
  now move/is_erasableP: ise => //.
  move/(elimN is_erasableP): nise.
  intros; sq => ise. apply nise.
  intros. now rewrite (abstract_env_ext_irr _ H wfΣ).
Qed.

Section Erase.
  Context (X_type : abstract_env_impl (cf := extraction_checker_flags)).
  Context (X : X_type.π2.π1).
  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  (* Ltac sq' :=
             repeat match goal with
                    | H : ∥ _ ∥ |- _ => destruct H; try clear H
                    end; try eapply sq. *)

  (* Bug in equationa: it produces huge goals leading to stack overflow if we
    don't try reflexivity here. *)
  Ltac Equations.Prop.DepElim.solve_equation c ::=
    intros; try reflexivity; try Equations.Prop.DepElim.simplify_equation c;
     try
	  match goal with
    | |- ImpossibleCall _ => DepElim.find_empty
    | _ => try red; try reflexivity || discriminates
    end.

  Opaque is_erasableb.

  #[tactic="idtac"]
  Equations? erase (Γ : context) (t : term)
    (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) : E.term
      by struct t :=
  { erase Γ t Ht with inspect_bool (is_erasableb X_type X Γ t Ht) :=
  { | left he := E.tBox;
    | right he with t := {
      | tRel i := E.tRel i
      | tVar n := E.tVar n
      | tEvar m l := E.tEvar m (erase_terms Γ l _)
      | tSort u := !%prg
      | tConst kn u := E.tConst kn
      | tInd kn u := !%prg
      | tConstruct kn k u := E.tConstruct kn k []
      | tProd _ _ _ := !%prg
      | tLambda na b b' := let t' := erase (vass na b :: Γ) b' _ in
        E.tLambda na.(binder_name) t'
      | tLetIn na b t0 t1 :=
        let b' := erase Γ b _ in
        let t1' := erase (vdef na b t0 :: Γ) t1 _ in
        E.tLetIn na.(binder_name) b' t1'
      | tApp f u :=
        let f' := erase Γ f _ in
        let l' := erase Γ u _ in
        E.tApp f' l'
      | tCase ci p c brs :=
        let c' := erase Γ c _ in
        let brs' := erase_brs Γ p brs _ in
        E.tCase (ci.(ci_ind), ci.(ci_npar)) c' brs'
      | tProj p c :=
        let c' := erase Γ c _ in
        E.tProj p c'
      | tFix mfix n :=
        let Γ' := (fix_context mfix ++ Γ)%list in
        let mfix' := erase_fix Γ' mfix _ in
        E.tFix mfix' n
      | tCoFix mfix n :=
        let Γ' := (fix_context mfix ++ Γ)%list in
        let mfix' := erase_cofix Γ' mfix _ in
        E.tCoFix mfix' n
      | tPrim (primInt; PCUICPrimitive.primIntModel i) := E.tPrim (primInt; EPrimitive.primIntModel i) ;
      | tPrim (primFloat; PCUICPrimitive.primFloatModel f) := E.tPrim (primFloat; EPrimitive.primFloatModel f) ;
      | tPrim (primString; PCUICPrimitive.primStringModel s) := E.tPrim (primString; EPrimitive.primStringModel s) ;
      | tPrim (primArray; PCUICPrimitive.primArrayModel a) :=
        E.tPrim (primArray; EPrimitive.primArrayModel
          {| EPrimitive.array_default := erase Γ a.(PCUICPrimitive.array_default) _;
             EPrimitive.array_value := erase_terms Γ a.(PCUICPrimitive.array_value) _ |})
    }
    } }

  where erase_terms (Γ : context) (l : list term) (Hl : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ All (welltyped Σ Γ) l ∥) : list E.term :=
  { erase_terms Γ [] _ := [];
    erase_terms Γ (t :: ts) _ :=
      let t' := erase Γ t _ in
      let ts' := erase_terms Γ ts _ in
      t' :: ts' }
(** We assume that there are no lets in contexts, so nothing has to be expanded.
  In particular, note that #|br.(bcontext)| = context_assumptions br.(bcontext) when no lets are present.
  *)
  where erase_brs (Γ : context) p (brs : list (branch term))
    (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
          ∥ All (fun br => welltyped Σ (Γ ,,, inst_case_branch_context p br) (bbody br)) brs ∥) :
    list (list name × E.term) :=
  { erase_brs Γ p [] Ht := [];
    erase_brs Γ p (br :: brs) Hbrs :=
      let br' := erase (Γ ,,, inst_case_branch_context p br) (bbody br) _ in
      let brs' := erase_brs Γ p brs _ in
      (erase_context br.(bcontext), br') :: brs' }

  where erase_fix (Γ : context) (mfix : mfixpoint term)
    (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
          ∥ All (fun d => isLambda d.(dbody) /\ welltyped Σ Γ d.(dbody)) mfix ∥) : E.mfixpoint E.term :=
  { erase_fix Γ [] _ := [];
    erase_fix Γ (d :: mfix) Hmfix :=
      let dbody' := erase Γ d.(dbody) _ in
      let dbody' := if isBox dbody' then
        match d.(dbody) with
        (* We ensure that all fixpoint members start with a lambda, even a dummy one if the
           recursive definition is erased. *)
        | tLambda na _ _ => E.tLambda (binder_name na) E.tBox
        | _ => dbody'
        end else dbody' in
      let d' := {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |} in
      d' :: erase_fix Γ mfix _ }

  where erase_cofix (Γ : context) (mfix : mfixpoint term)
      (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
            ∥ All (fun d => welltyped Σ Γ d.(dbody)) mfix ∥) : E.mfixpoint E.term :=
    { erase_cofix Γ [] _ := [];
      erase_cofix Γ (d :: mfix) Hmfix :=
        let dbody' := erase Γ d.(dbody) _ in
        let d' := {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |} in
        d' :: erase_cofix Γ mfix _ }
    .
  Proof using Type.
    all: try clear b'; try clear f';
      try clear t';
      try clear brs'; try clear c'; try clear br';
      try clear d' dbody'; try clear erase; try clear erase_terms; try clear erase_brs; try clear erase_mfix.
    all: cbn; intros; subst; lazymatch goal with [ |- False ] => idtac | _ => try clear he end.
    all: try pose proof (abstract_env_ext_wf _ H) as [wf];
         specialize_Σ H.
    all: try destruct Ht as [ty Ht]; try destruct s0; simpl in *.
    - now eapply inversion_Evar in Ht.
    - discriminate.
    - discriminate.
    - eapply inversion_Lambda in Ht as (? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_LetIn in Ht as (? & h1 & ? & ?); auto.
      apply unlift_TermTyp in h1.
      eexists; eauto.
    - simpl in *.
      eapply inversion_LetIn in Ht as (? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - move/is_erasableP: he. intro. apply he. intros.
      pose proof (abstract_env_ext_wf _ H) as [wf].
      specialize_Σ H. destruct Ht as [ty Ht]. sq.
      eapply inversion_Ind in Ht as (? & ? & ? & ? & ? & ?) ; auto.
      red. eexists. split. econstructor; eauto. left.
      eapply isArity_subst_instance.
      eapply isArity_ind_type; eauto.
    - eapply inversion_Case in Ht as (? & ? & ? & ? & [] & ?); auto.
      eexists; eauto.
    - now eapply welltyped_brs in Ht as []; tea.
    - eapply inversion_Proj in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_Fix in Ht as (? & ? & ? & ? & ? & ?); auto.
      sq. destruct p. move/andP: i => [wffix _].
      solve_all. destruct a0 as (Hb & _). cbn in Hb. now eexists.
    - eapply inversion_CoFix in Ht as (? & ? & ? & ? & ? & ?); auto.
      sq. eapply All_impl; tea. cbn. intros d (Hb & _); cbn in Hb; now eexists.
    - eapply inversion_Prim in Ht as [prim_ty [decl []]]; eauto.
      depelim p0. now eexists.
    - eapply inversion_Prim in Ht as [prim_ty [decl []]]; eauto.
      depelim p0. sq. solve_all. now eexists.
    - sq. now depelim Hl.
    - sq. now depelim Hl.
    - sq. now depelim Hbrs.
    - sq. now depelim Hbrs.
    - sq. now depelim Hmfix.
    - clear dbody'0. specialize_Σ H. sq. now depelim Hmfix.
    - sq. now depelim Hmfix.
    - sq. now depelim Hmfix.
  Qed.

End Erase.

Lemma is_erasableb_irrel {X_type X} {normalization_in normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {Γ t} wt wt' : is_erasableb X_type X Γ t wt (normalization_in:=normalization_in) = is_erasableb X_type X Γ t wt' (normalization_in:=normalization_in').
Proof.
  destruct (@is_erasableP X_type X normalization_in Γ t wt);
  destruct (@is_erasableP X_type X normalization_in' Γ t wt') => //.
Qed.

Ltac iserasableb_irrel :=
  match goal with
  [ H : context [@is_erasableb ?X_type ?X ?normalization_in ?Γ ?t ?wt], Heq : inspect_bool _ = _ |- context [ @is_erasableb _ _ ?normalization_in' _ _ ?wt'] ] =>
    generalize dependent H; rewrite (@is_erasableb_irrel X_type X normalization_in normalization_in' Γ t wt wt'); intros; rewrite Heq
  end.

Ltac simp_erase := simp erase; rewrite -?erase_equation_1.

Lemma erase_irrel X_type X {normalization_in} :
  (forall Γ t wt, forall normalization_in' wt', erase X_type X Γ t wt (normalization_in:=normalization_in) = erase X_type X Γ t wt' (normalization_in:=normalization_in')) ×
  (forall Γ l wt, forall normalization_in' wt', erase_terms X_type X Γ l wt (normalization_in:=normalization_in) = erase_terms X_type X Γ l wt' (normalization_in:=normalization_in')) ×
  (forall Γ p l wt, forall normalization_in' wt', erase_brs X_type X Γ p l wt (normalization_in:=normalization_in) = erase_brs X_type X Γ p l wt' (normalization_in:=normalization_in')) ×
  (forall Γ l wt, forall normalization_in' wt', erase_fix X_type X Γ l wt (normalization_in:=normalization_in) = erase_fix X_type X Γ l wt' (normalization_in:=normalization_in')) ×
  (forall Γ l wt, forall normalization_in' wt', erase_cofix X_type X Γ l wt (normalization_in:=normalization_in) = erase_cofix X_type X Γ l wt' (normalization_in:=normalization_in')).
Proof.
  apply: (erase_elim X_type X
    (fun Γ t wt e =>
      forall normalization_in' (wt' : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->  welltyped Σ Γ t), e = erase X_type X Γ t wt' (normalization_in:=normalization_in'))
    (fun Γ l awt e => forall normalization_in' wt', e = erase_terms X_type X Γ l wt' (normalization_in:=normalization_in'))
    (fun Γ p l awt e => forall normalization_in' wt', e = erase_brs X_type X Γ p l wt' (normalization_in:=normalization_in'))
    (fun Γ l awt e => forall normalization_in' wt', e = erase_fix X_type X Γ l wt' (normalization_in:=normalization_in'))
    (fun Γ l awt e => forall normalization_in' wt', e = erase_cofix X_type X Γ l wt' (normalization_in:=normalization_in'))); clear.
  all:intros *; intros; simp_erase.
  all:try simp erase; try iserasableb_irrel; simp_erase.
  all: try solve [ cbv beta zeta;
                   repeat match goal with
                     | [ H : context[_ -> _ = _] |- _ ]
                       => erewrite H; try reflexivity
                     end;
                   reflexivity ].
  all: try move => //.
  all: try bang.
Qed.

Lemma erase_terms_eq X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} Γ ts wt :
  erase_terms X_type X Γ ts wt = All_Forall.map_All (erase X_type X Γ) ts wt.
Proof.
  funelim (All_Forall.map_All (erase X_type X Γ) ts wt); cbn; auto.
  f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Opaque wf_reduction.

#[global]
Hint Constructors typing erases : core.

Lemma erase_to_box {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {Γ t} (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
  let et := erase X_type X Γ t wt in
  if is_box et then ∥ isErasable Σ Γ t ∥
  else ~ ∥ isErasable Σ Γ t ∥.
Proof.
  cbn. intros.
  revert Γ t wt.
  apply (erase_elim X_type X
    (fun Γ t wt e =>
      if is_box e then ∥ isErasable Σ Γ t ∥ else ∥ isErasable Σ Γ t ∥ -> False)
    (fun Γ l awt e => True)
    (fun Γ p l awt e => True)
    (fun Γ l awt e => True)
    (fun Γ l awt e => True)); intros.

  all:try discriminate; auto.
  all:cbn -[isErasable].
  all:try solve [  match goal with
  [ H : context [ @is_erasableb ?X_type ?X ?normalization_in ?Γ ?t ?Ht ] |- _ ] =>
    destruct (@is_erasableP X_type X normalization_in Γ t Ht)  => //
  end; intro;
    match goal with n : ~ _ |- _  => apply n end; intros ? HH; now rewrite (abstract_env_ext_irr _ HH H) ].
  all:try bang.
  - destruct (@is_erasableP X_type X normalization_in Γ t Ht) => //. apply s; eauto.
  - cbn in *. rewrite is_box_tApp.
    destruct (@is_erasableP X_type X normalization_in Γ (tApp f u) Ht) => //.
    destruct is_box.
    * cbn in *. clear H1.
      pose proof (abstract_env_ext_wf _ H) as [wf]. cbn in *.
      specialize_Σ H. destruct Ht, H0.
      eapply (EArities.Is_type_app _ _ _ [_]); eauto.
      eauto using typing_wf_local.
    * intro; apply n; intros. now rewrite (abstract_env_ext_irr _ H3 H).
Defined.

Lemma erases_erase {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {Γ t}
(wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :
forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> erases Σ Γ t (erase X_type X Γ t wt).
Proof.
  intros. revert Γ t wt.
  apply (erase_elim X_type X
    (fun Γ t wt e => Σ;;; Γ |- t ⇝ℇ e)
    (fun Γ l awt e => All2 (erases Σ Γ) l e)
    (fun Γ p l awt e =>
      All2 (fun (x : branch term) (x' : list name × E.term) =>
                       (Σ;;; Γ,,, inst_case_branch_context p x |-
                        bbody x ⇝ℇ x'.2) *
                       (erase_context (bcontext x) = x'.1)) l e)
    (fun Γ l awt e => All2
    (fun (d : def term) (d' : E.def E.term) =>
     [× binder_name (dname d) = E.dname d',
        rarg d = E.rarg d',
        isLambda (dbody d), E.isLambda (E.dbody d') &
        Σ;;; Γ |- dbody d ⇝ℇ E.dbody d']) l e)
    (fun Γ l awt e => All2
      (fun (d : def term) (d' : E.def E.term) =>
        (binder_name (dname d) = E.dname d') *
        (rarg d = E.rarg d'
         × Σ;;; Γ |- dbody d ⇝ℇ E.dbody d')) l e)) ; intros.
    all:try discriminate.
    all:try bang.
    all:try match goal with
      [ H : context [@is_erasableb ?X_type ?X ?normalization_in ?Γ ?t ?Ht ] |- _ ] =>
        edestruct (@is_erasableP X_type X normalization_in Γ t Ht) as [[H']|H'] => //; eauto ;
        try now eapply erases_box
    end.
    all: try solve [constructor; eauto].
  all:try destruct (abstract_env_ext_wf X H) as [wfΣ].
  all: cbn in *; try constructor; auto;
  specialize_Σ H.

  - clear Heq.
    eapply nisErasable_Propositional in Ht; auto.
    intro; eapply H'; intros. now rewrite (abstract_env_ext_irr _ H0 H).
  - cbn.
    destruct (Ht _ H).
    destruct (inversion_Case _ _ X1) as [mdecl [idecl []]]; eauto.
    eapply elim_restriction_works; eauto.
    intros isp. eapply isErasable_Proof in isp.
    eapply H'; intros. now rewrite (abstract_env_ext_irr _ H1 H).

  - clear Heq.
    destruct (Ht _ H) as [? Ht'].
    clear H0. eapply inversion_Proj in Ht' as (?&?&?&?&?&?&?&?&?&?); auto.
    eapply elim_restriction_works_proj; eauto. exact d.
    intros isp. eapply isErasable_Proof in isp.
    eapply H'; intros. now rewrite (abstract_env_ext_irr _ H0 H).

  - repeat constructor.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor; eauto.
  - cbn. pose proof (abstract_env_ext_wf _ H) as [wf].
    pose proof Hmfix as Hmfix'.
    specialize (Hmfix' _ H). destruct Hmfix'.
    depelim X1. destruct a.
    assert (exists na ty bod, dbody d = tLambda na ty bod).
    { clear -H1. destruct (dbody d) => //. now do 3 eexists. }
    destruct H3 as [na [ty [bod eq]]]. rewrite {1 3}eq /= //.
    move: H0. rewrite {1}eq.
    set (et := erase _ _ _ _ _). clearbody et.
    intros He. depelim He. cbn.
    split => //. cbn. rewrite eq. now constructor.
    split => //. cbn. rewrite eq.
    destruct H2.
    eapply Is_type_lambda in X2; tea. 2:pcuic. destruct X2.
    now constructor.
Qed.

Transparent wf_reduction.

(** We perform erasure up-to the minimal global environment dependencies of the term: i.e.
  we don't need to erase entries of the global environment that will not be used by the erased
  term.
*)

Program Definition erase_constant_body X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}
  (cb : constant_body)
  (Hcb : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ on_constant_decl (lift_typing typing) Σ cb ∥) : E.constant_body * KernameSet.t :=
  let '(body, deps) := match cb.(cst_body) with
          | Some b =>
            let b' := erase X_type X [] b _ in
            (Some b', term_global_deps b')
          | None => (None, KernameSet.empty)
          end in
  ({| E.cst_body := body; |}, deps).
Next Obligation.
Proof.
  specialize_Σ H. sq. red in Hcb.
  rewrite <-Heq_anonymous in Hcb. apply unlift_TermTyp in Hcb. now eexists.
Qed.

Definition erase_one_inductive_body (oib : one_inductive_body) : E.one_inductive_body :=
  (* Projection and constructor types are types, hence always erased *)
  let ctors := map (fun cdecl => EAst.mkConstructor cdecl.(cstr_name) cdecl.(cstr_arity)) oib.(ind_ctors) in
  let projs := map (fun pdecl => EAst.mkProjection pdecl.(proj_name)) oib.(ind_projs) in
  let is_propositional :=
    match destArity [] oib.(ind_type) with
    | Some (_, u) => Sort.is_propositional u
    | None => false (* dummy, impossible case *)
    end
  in
  {| E.ind_name := oib.(ind_name);
     E.ind_kelim := oib.(ind_kelim);
     E.ind_propositional := is_propositional;
     E.ind_ctors := ctors;
     E.ind_projs := projs |}.

Definition erase_mutual_inductive_body (mib : mutual_inductive_body) : E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  let bodies := map erase_one_inductive_body bds in
  {| E.ind_finite := mib.(ind_finite);
     E.ind_npars := mib.(ind_npars);
     E.ind_bodies := bodies; |}.

Lemma is_arity_irrel {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}
  {X_type' : abstract_env_impl} {X' : X_type'.π2.π1} {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ} {Γ h h' t wt wt'} :
  Hlookup X_type X X_type' X' ->
  is_arity X_type X Γ h t wt = is_arity X_type' X' Γ h' t wt'.
Proof.
  intros hl.
  funelim (is_arity X_type X _ _ _ _).
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H1.
    simp is_arity.
    epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    destruct (PCUICSafeReduce.inspect) eqn:hi.
    rewrite -e in H1.
    destruct x => //.
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H3.
    rewrite [is_arity X_type' X' _ _ _ _]is_arity_equation_1.
    epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    destruct (PCUICSafeReduce.inspect) eqn:hi.
    rewrite -rsort -e in H4.
    destruct x => //.
    rewrite is_arity_clause_1_equation_2.
    destruct (PCUICSafeReduce.inspect (reduce_to_prod _ _ _)) eqn:hi'.
    epose proof (reduce_to_prod_irrel hl HT wt').
    rewrite -rprod -e0 in H5 => //.
    destruct x => //.
    destruct a1 as [na' [A' [B' ?]]]. cbn in H5. noconf H5.
    rewrite is_arity_clause_1_clause_2_equation_1.
    now apply H0.
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H1.
    simp is_arity.
    destruct (PCUICSafeReduce.inspect) eqn:hi.
    rewrite -e0 in H1.
    destruct x => //.
    simp is_arity.
    destruct (PCUICSafeReduce.inspect (reduce_to_prod _ _ _)) eqn:hi'.
    epose proof (reduce_to_prod_irrel hl HT wt').
    rewrite -rprod -e1 in H2 => //.
    destruct x => //.
Qed.

Definition extends_global_env (Σ Σ' : PCUICAst.PCUICEnvironment.global_env) :=
  (forall kn decl, PCUICAst.PCUICEnvironment.lookup_env Σ kn = Some decl ->
    PCUICAst.PCUICEnvironment.lookup_env Σ' kn = Some decl) /\
  (forall tag, primitive_constant Σ tag = primitive_constant Σ' tag).

Lemma is_erasableb_irrel_global_env {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {X_type' X'} {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ} {Γ t wt wt'} :
  forall (hl : Hlookup X_type X X_type' X'),
  is_erasableb X_type X Γ t wt = is_erasableb X_type' X' Γ t wt'.
Proof.
  intros hl.
  simp is_erasableb.
  set (obl := is_erasableb_obligation_2 _ _ _ _). clearbody obl.
  set(ty := (type_of_typing X_type' _ _ _ wt')) in *.
  set(ty' := (type_of_typing X_type _ _ _ wt)) in *.
  assert (ty.π1 = ty'.π1).
  { subst ty ty'. unfold type_of_typing. symmetry.
    eapply infer_irrel => //. }
  clearbody ty. clearbody ty'.
  destruct ty, ty'. cbn in H. subst x0.
  cbn -[is_arity] in obl |- *.
  set (obl' := is_erasableb_obligation_1 X_type' X' Γ t wt').
  set (obl'' := is_erasableb_obligation_2 X_type' X' Γ t _).
  clearbody obl'. clearbody obl''.
  rewrite (is_arity_irrel (X:=X) (X' := X') (wt' := obl'' (x; s))) => //.
  destruct is_arity  => //. simp is_erasableb.
  set (obl2 := is_erasableb_obligation_3 _ _ _ _ _).
  set (obl2' := is_erasableb_obligation_3 _ _ _ _ _).
  simpl. f_equal. now apply sort_of_type_irrel.
Qed.

Ltac iserasableb_irrel_env :=
  match goal with
  [ H : context [@is_erasableb ?X_type ?X ?normalization_in ?Γ ?t ?wt], Heq : inspect_bool _ = _ |- context [ @is_erasableb _ _ _ _ _ ?wt'] ] =>
    generalize dependent H; rewrite (@is_erasableb_irrel_global_env _ _ _ _ _ _ _ _ wt wt') //; intros; rewrite Heq
  end.

Lemma erase_irrel_global_env {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {X_type' X'} {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ} {Γ t wt wt'} :
  forall (hl : Hlookup X_type X X_type' X'),
  erase X_type X Γ t wt = erase X_type' X' Γ t wt'.
Proof.
  intros hl.
  move: wt'.
  eapply (erase_elim X_type X
  (fun Γ t wt e =>
    forall (wt' : forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' ->  welltyped Σ' Γ t),
    e = erase X_type' X' Γ t wt')
  (fun Γ l awt e => forall wt',
    e = erase_terms X_type' X' Γ l wt')
  (fun Γ p l awt e => forall wt',
    e = erase_brs X_type' X'  Γ p l wt')
  (fun Γ l awt e => forall wt',
    e = erase_fix X_type' X'  Γ l wt')
  (fun Γ l awt e => forall wt',
    e = erase_cofix X_type' X'  Γ l wt')).
  all:intros *; intros; simp_erase.
  simp erase.
  all:try simp erase; try iserasableb_irrel_env; simp_erase.
  all:try solve [ cbv beta zeta;
                  repeat match goal with
                    | [ H : context[_ -> _ = _] |- _ ]
                      => erewrite H; try reflexivity
                    end;
                  reflexivity ].
  all:bang.
Qed.

Lemma erase_constant_body_irrel {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {X_type' X'} {normalization_in' : forall Σ, wf_ext Σ -> Σ ∼_ext X' -> NormalizationIn Σ} {cb ondecl ondecl'} :
  forall (hl : Hlookup X_type X X_type' X'),
  erase_constant_body X_type X cb ondecl = erase_constant_body X_type' X' cb ondecl'.
Proof.
  intros ext.
  destruct cb => //=.
  destruct cst_body0 => //=.
  unfold erase_constant_body; simpl => /=.
  f_equal. f_equal. f_equal.
  eapply erase_irrel_global_env; tea.
  f_equal.
  eapply erase_irrel_global_env; tea.
Qed.

From Stdlib Require Import Morphisms.

(* Global Instance proper_pair_levels_gcs : Proper ((=_lset) ==> GoodUnivConstraintSet.Equal ==> (=_gcs)) (@pair LevelSet.t GoodUnivConstraintSet.t).
Proof.
  intros l l' eq gcs gcs' eq'.
  split; cbn; auto.
Qed. *)

(* TODO: Should this live elsewhere? *)
Definition iter {A} (f : A -> A) : nat -> (A -> A)
  := fix iter (n : nat) : A -> A
    := match n with
       | O => fun x => x
       | S n => fun x => iter n (f x)
       end.

(* we use the [match] trick to get typeclass resolution to pick up the right instances without leaving any evidence in the resulting term, and without having to pass them manually everywhere *)
Notation NormalizationIn_erase_global_deps X decls
  := (match extraction_checker_flags, extraction_normalizing return _ with
      | cf, no
        => forall n,
          n < List.length decls ->
          let X' := iter abstract_pop_decls (S n) X in
          forall kn cb pf,
            List.hd_error (List.skipn n decls) = Some (kn, ConstantDecl cb) ->
            let Xext := abstract_make_wf_env_ext X' (cst_universes cb) pf in
            forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ
      end)
       (only parsing).

Lemma normalization_in_inv {X_type : abstract_env_impl} (X : X_type.π1)
  (decls : global_declarations) kn cb
  (normalization_in : NormalizationIn_erase_global_deps X ((kn, ConstantDecl cb) :: decls)) :
  NormalizationIn_erase_global_deps (abstract_pop_decls X) decls.
Proof.
  cbv [id]. intros.
  unshelve eapply (normalization_in (S n)); cbn; tea. lia.
Defined.

Program Definition erase_constant_decl {X_type : abstract_env_impl} (X : X_type.π1)
  (cb : constant_body)
  (normalization_in : forall pf,
    let Xext := abstract_make_wf_env_ext X (cst_universes cb) pf in
    forall Σ, wf_ext Σ -> Σ ∼_ext Xext -> NormalizationIn Σ)
  (oncb : forall Σ : global_env, Σ ∼ X -> ∥ wf_ext (Σ, cst_universes cb) * on_constant_decl (lift_typing typing) (Σ, cst_universes cb) cb ∥) :=
  let Xext := abstract_make_wf_env_ext X (cst_universes cb) _ in
  let normalization_in' : @id Prop _ := _ in (* hack to avoid program erroring out on unresolved tc *)
  @erase_constant_body X_type Xext normalization_in' cb _.
Next Obligation.
pose proof (abstract_env_wf _ H) as [wf].
specialize (oncb _ H). destruct oncb. sq. intuition auto.
Qed.

Next Obligation.
  unfold id. intros.
  unshelve eapply normalization_in; eauto.
Defined.

Next Obligation.
  destruct Σ as [Σ ext].
  pose proof (abstract_env_exists X) as [[? HX]].
  pose proof (abstract_env_wf _ HX) as [wfX].
  pose proof (abstract_make_wf_env_ext_correct X (cst_universes cb) _ _ _ HX H).
  noconf H0.
  clear H; specialize (oncb _ HX). destruct oncb as [[]]; sq; auto.
Qed.

(* When two environments agree on the intersection of their declarations *)
Definition equiv_decls_inter Σ Σ' :=
  (forall kn decl decl', EGlobalEnv.lookup_env Σ kn = Some decl -> EGlobalEnv.lookup_env Σ' kn = Some decl' -> decl = decl').

Definition equiv_env_inter Σ Σ' :=
  (forall kn decl decl', lookup_env Σ kn = Some decl -> lookup_env Σ' kn = Some decl' -> decl = decl') /\
  (forall tag : Primitive.prim_tag, primitive_constant Σ tag = primitive_constant Σ' tag).

Lemma equiv_env_inter_sym Σ Σ' :
  equiv_env_inter Σ Σ' <-> equiv_env_inter Σ' Σ.
Proof.
  unfold equiv_env_inter.
  intuition auto; symmetry; eauto.
Qed.

(* When  two environments agree on the intersection of their declarations *)
Lemma equiv_env_inter_hlookup {cf:checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
  (X_type' : abstract_env_impl) (X' : X_type'.π2.π1) :
  (forall Σ Σ', Σ ∼_ext X -> Σ' ∼_ext X' -> equiv_env_inter Σ Σ') -> Hlookup X_type X X_type' X'.
Proof.
  intros hl Σ HX Σ' HX'.
  specialize (hl _ _ HX HX') as [hl hr].
  split.
  - intros kn decl decl'.
    specialize (hl kn decl decl').
    rewrite <-(abstract_env_lookup_correct' _ _ HX).
    rewrite <-(abstract_env_lookup_correct' _ _ HX').
    intros Hl Hl'.
    rewrite Hl Hl'. f_equal. eauto.
  - intros tag; rewrite (abstract_primitive_constant_correct _ _ _ HX) (abstract_primitive_constant_correct _ _ _ HX').
    apply hr.
Qed.


Definition Hlookup_env {cf:checker_flags} (X_type : abstract_env_impl) (X : X_type.π1) (X_type' : abstract_env_impl)
  (X' : X_type'.π1) :=
  forall Σ : global_env, abstract_env_rel X Σ ->
  forall Σ' : global_env, abstract_env_rel X' Σ' ->
  equiv_env_inter Σ Σ'.

Lemma erase_constant_decl_irrel {X_type : abstract_env_impl} (X : X_type.π1) (cb : constant_body) normalization_in oncb
  (X' : X_type.π1) normalization_in' oncb' :
  Hlookup_env X_type X X_type X' ->
  erase_constant_decl X cb normalization_in oncb = erase_constant_decl X' cb normalization_in' oncb'.
Proof.
  unfold erase_constant_decl.
  intros hl.
  apply erase_constant_body_irrel.
  pose proof (abstract_env_exists X) as [[env wf]].
  pose proof (abstract_env_exists X') as [[env' wf']].
  red. intros.
  specialize (hl _ wf _ wf') as [hl hp].
  pose proof (abstract_make_wf_env_ext_correct X (cst_universes cb) _ _ _ wf H).
  pose proof (abstract_make_wf_env_ext_correct X' (cst_universes cb) _ _ _ wf' H0).
  split => //.
  { intros.
    rewrite -(abstract_env_lookup_correct' _ _ H).
    rewrite -(abstract_env_lookup_correct' _ _ H0). rewrite H3 H4. subst Σ Σ'.
    now specialize (hl _ _ _ H3 H4). }
  intros.
  { rewrite (abstract_primitive_constant_correct _ _ _ H).
    rewrite (abstract_primitive_constant_correct _ _ _ H0).
    now rewrite H1 H2. }
Qed.

Program Fixpoint erase_global_deps
  {X_type : abstract_env_impl} (deps : KernameSet.t) (X : X_type.π1) (decls : global_declarations)
  {normalization_in : NormalizationIn_erase_global_deps X decls}
  (prop : forall Σ : global_env, abstract_env_rel X Σ -> Σ.(declarations) = decls)
  : E.global_declarations * KernameSet.t :=
  match decls with
  | [] => ([], deps)
  | (kn, ConstantDecl cb) :: decls =>
    let X' := abstract_pop_decls X in
    if KernameSet.mem kn deps then
      let cb' := @erase_constant_decl X_type X' cb _ _ in
      let deps := KernameSet.union deps (snd cb') in
      let X'' := erase_global_deps deps X' decls _ in
      (((kn, E.ConstantDecl (fst cb')) :: fst X''), snd X'')
    else
      erase_global_deps deps X' decls _

  | (kn, InductiveDecl mib) :: decls =>
    let X' := abstract_pop_decls X in
    if KernameSet.mem kn deps then
      let mib' := erase_mutual_inductive_body mib in
      let X'':= erase_global_deps deps X' decls _ in
      (((kn, E.InductiveDecl mib') :: fst X''), snd X'')
    else erase_global_deps deps X' decls _
  end.
Next Obligation.
  cbv [id].
  unshelve eapply (normalization_in 0); tea; cbn; try reflexivity; try lia.
Defined.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]].
  pose proof (abstract_env_wf _ HX) as [wfX].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
  destruct x, Σ as [[] u], H0; cbn in *.
  subst. sq. inversion H1. subst. destruct wfX. cbn in *.
  specialize (prop _ HX).
  cbn in prop.
  rewrite prop in o0. depelim o0. destruct o1.
  split. 2:exact on_global_decl_d. split => //.
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
pose proof (abstract_env_exists X) as [[? HX]].
assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
{ now eexists. }
now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
pose proof (abstract_env_exists X) as [[? HX]].
assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
{ now eexists. }
now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.

Program Fixpoint erase_global {X_type : abstract_env_impl} (X : X_type.π1) (decls : global_declarations)
  {normalization_in : NormalizationIn_erase_global_deps X decls}
  (prop : forall Σ : global_env, abstract_env_rel X Σ -> Σ.(declarations) = decls)
  : E.global_declarations :=
  match decls with
  | [] => []
  | (kn, ConstantDecl cb) :: decls =>
    let X' := abstract_pop_decls X in
    let cb' := @erase_constant_decl X_type X' cb _ _ in
    let X'' := erase_global X' decls _ in
    ((kn, E.ConstantDecl (fst cb')) :: X'')

  | (kn, InductiveDecl mib) :: decls =>
    let X' := abstract_pop_decls X in
    let mib' := erase_mutual_inductive_body mib in
    let X'':= erase_global X' decls _ in
    ((kn, E.InductiveDecl mib') :: X'')
  end.
Next Obligation.
  cbv [id].
  unshelve eapply (normalization_in 0); tea; cbn; try reflexivity; try lia.
Defined.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]].
  pose proof (abstract_env_wf _ HX) as [wfX].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
  destruct x, Σ as [[] u], H0; cbn in *.
  subst. sq. inversion H1. subst. destruct wfX. cbn in *.
  specialize (prop _ HX).
  cbn in prop.
  rewrite prop in o0. depelim o0. destruct o1.
  split. 2:exact on_global_decl_d. split => //.
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.
Next Obligation.
  unshelve eapply (normalization_in (S _)); cbn in *; revgoals; try eassumption; lia.
Defined.
Next Obligation.
pose proof (abstract_env_exists X) as [[? HX]].
assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
{ now eexists. }
now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.

Lemma erase_global_deps_irr
  X_type deps (X X':X_type.π1) decls
  {normalization_in normalization_in'}
  prf prf' :
  (forall Σ Σ', Σ ∼ X -> Σ' ∼ X' -> forall tag, primitive_constant Σ tag = primitive_constant Σ' tag) ->
  erase_global_deps deps X decls (normalization_in:=normalization_in) prf =
  erase_global_deps deps X' decls (normalization_in:=normalization_in') prf'.
Proof.
  revert X X' deps normalization_in normalization_in' prf prf'.
  induction decls; eauto. intros. destruct a as [kn []].
  - cbn.
    set (ec := erase_constant_decl _ _ _ _).
    set (ec' := erase_constant_decl _ _ _ _).
    pose proof (abstract_env_exists X) as [[envX wfX]].
    pose proof (abstract_env_exists X') as [[envX' wfX']].
    pose proof (abstract_env_exists (abstract_pop_decls X)) as [[env wf]].
    pose proof (abstract_env_exists (abstract_pop_decls X')) as [[env' wf']].
    unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX wf) as [Hd [Hu Hr]]. shelve.
    { intros ? h. rewrite (prf _ h). now eexists. }
    unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX' wf') as [Hd' [Hu' Hr']]. shelve.
    { intros ? h. rewrite (prf' _ h). now eexists. }
    assert (ec = ec') as <-.
    { subst ec ec'.
      unfold erase_constant_decl.
      erewrite erase_constant_body_irrel. reflexivity.
      red. intros.
      pose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X) (cst_universes c) _ _ _ wf H0).
      pose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X') (cst_universes c) _ _ _ wf' H1).
      split => //.
      { intros.
        rewrite -(abstract_env_lookup_correct' _ _ H0).
        rewrite -(abstract_env_lookup_correct' _ _ H1).
        move: H4 H5. rewrite /lookup_env H2 H3 /= Hd Hd'. congruence. }
      intros.
      { rewrite (abstract_primitive_constant_correct _ _ _ H0).
        rewrite (abstract_primitive_constant_correct _ _ _ H1).
        specialize (H _ _ wfX wfX').
        rewrite H2 H3 /primitive_constant /= -Hr -Hr'. apply H. } }
    assert ((forall Σ Σ' : global_env,
      Σ ∼ abstract_pop_decls X -> Σ' ∼ abstract_pop_decls X' ->
      forall tag : Primitive.prim_tag, primitive_constant Σ tag = primitive_constant Σ' tag))        .
    { intros Σ Σ' h h' tag.
      pose proof (abstract_env_irr _ wf h). subst env.
      pose proof (abstract_env_irr _ wf' h'). subst env'.
      specialize (H _ _ wfX wfX').
      rewrite /primitive_constant -Hr -Hr'. apply H. }
    specialize (IHdecls (abstract_pop_decls X) (abstract_pop_decls X')).
    destruct KernameSet.mem; cbn.
    f_equal; f_equal. f_equal; now eapply IHdecls.
    now apply IHdecls. now apply IHdecls.
  - cbn.
    pose proof (abstract_env_exists X) as [[envX wfX]].
    pose proof (abstract_env_exists X') as [[envX' wfX']].
    pose proof (abstract_env_exists (abstract_pop_decls X)) as [[env wf]].
    pose proof (abstract_env_exists (abstract_pop_decls X')) as [[env' wf']].
    unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX wf) as [Hd [Hu Hr]]. shelve.
    { intros ? h. rewrite (prf _ h). now eexists. }
    unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX' wf') as [Hd' [Hu' Hr']]. shelve.
    { intros ? h. rewrite (prf' _ h). now eexists. }
    assert ((forall Σ Σ' : global_env,
    Σ ∼ abstract_pop_decls X -> Σ' ∼ abstract_pop_decls X' ->
    forall tag : Primitive.prim_tag, primitive_constant Σ tag = primitive_constant Σ' tag))        .
    { intros Σ Σ' h h' tag.
      pose proof (abstract_env_irr _ wf h). subst env.
      pose proof (abstract_env_irr _ wf' h'). subst env'.
      specialize (H _ _ wfX wfX').
      rewrite /primitive_constant -Hr -Hr'. apply H. }
    destruct KernameSet.mem; cbn. f_equal. f_equal. 1-2:f_equal. all:now eapply IHdecls.
Qed.


Lemma erase_global_irr X_type (X X':X_type.π1) decls {normalization_in normalization_in'}
prf prf' :
(forall Σ Σ', Σ ∼ X -> Σ' ∼ X' -> forall tag, primitive_constant Σ tag = primitive_constant Σ' tag) ->
erase_global X decls (normalization_in:=normalization_in) prf =
erase_global X' decls (normalization_in:=normalization_in') prf'.
Proof.
revert X X' normalization_in normalization_in' prf prf'.
induction decls; eauto. intros. destruct a as [kn []].
- cbn.
  set (ec := erase_constant_decl _ _ _ _).
  set (ec' := erase_constant_decl _ _ _ _).
  pose proof (abstract_env_exists X) as [[envX wfX]].
  pose proof (abstract_env_exists X') as [[envX' wfX']].
  pose proof (abstract_env_exists (abstract_pop_decls X)) as [[env wf]].
  pose proof (abstract_env_exists (abstract_pop_decls X')) as [[env' wf']].
  unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX wf) as [Hd [Hu Hr]]. shelve.
  { intros ? h. rewrite (prf _ h). now eexists. }
  unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX' wf') as [Hd' [Hu' Hr']]. shelve.
  { intros ? h. rewrite (prf' _ h). now eexists. }
  assert (ec = ec') as <-.
  { subst ec ec'.
    unfold erase_constant_decl.
    erewrite erase_constant_body_irrel. reflexivity.
    red. intros.
    pose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X) (cst_universes c) _ _ _ wf H0).
    pose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X') (cst_universes c) _ _ _ wf' H1).
    split => //.
    { intros.
      rewrite -(abstract_env_lookup_correct' _ _ H0).
      rewrite -(abstract_env_lookup_correct' _ _ H1).
      move: H4 H5. rewrite /lookup_env H2 H3 /= Hd Hd'. congruence. }
    intros.
    { rewrite (abstract_primitive_constant_correct _ _ _ H0).
      rewrite (abstract_primitive_constant_correct _ _ _ H1).
      specialize (H _ _ wfX wfX').
      rewrite H2 H3 /primitive_constant /= -Hr -Hr'. apply H. } }
  assert ((forall Σ Σ' : global_env,
    Σ ∼ abstract_pop_decls X -> Σ' ∼ abstract_pop_decls X' ->
    forall tag : Primitive.prim_tag, primitive_constant Σ tag = primitive_constant Σ' tag))        .
  { intros Σ Σ' h h' tag.
    pose proof (abstract_env_irr _ wf h). subst env.
    pose proof (abstract_env_irr _ wf' h'). subst env'.
    specialize (H _ _ wfX wfX').
    rewrite /primitive_constant -Hr -Hr'. apply H. }
  specialize (IHdecls (abstract_pop_decls X) (abstract_pop_decls X')).
  f_equal; f_equal. f_equal; now eapply IHdecls.
- cbn.
  pose proof (abstract_env_exists X) as [[envX wfX]].
  pose proof (abstract_env_exists X') as [[envX' wfX']].
  pose proof (abstract_env_exists (abstract_pop_decls X)) as [[env wf]].
  pose proof (abstract_env_exists (abstract_pop_decls X')) as [[env' wf']].
  unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX wf) as [Hd [Hu Hr]]. shelve.
  { intros ? h. rewrite (prf _ h). now eexists. }
  unshelve epose proof (abstract_pop_decls_correct _ _ _ _ _ wfX' wf') as [Hd' [Hu' Hr']]. shelve.
  { intros ? h. rewrite (prf' _ h). now eexists. }
  assert ((forall Σ Σ' : global_env,
  Σ ∼ abstract_pop_decls X -> Σ' ∼ abstract_pop_decls X' ->
  forall tag : Primitive.prim_tag, primitive_constant Σ tag = primitive_constant Σ' tag))        .
  { intros Σ Σ' h h' tag.
    pose proof (abstract_env_irr _ wf h). subst env.
    pose proof (abstract_env_irr _ wf' h'). subst env'.
    specialize (H _ _ wfX wfX').
    rewrite /primitive_constant -Hr -Hr'. apply H. }
  f_equal. f_equal. all:now eapply IHdecls.
Qed.

(* TODO: Figure out if this (and [erases]) should use [strictly_extends_decls] or [extends] -Jason Gross *)
Lemma erases_weakening_env {Σ Σ' : global_env_ext} {Γ t t' T} :
  wf Σ -> wf Σ' -> strictly_extends_decls Σ Σ' ->
  Σ ;;; Γ |- t : T ->
  erases Σ Γ t t' -> erases (Σ'.1, Σ.2) Γ t t'.
Proof.
  intros wfΣ wfΣ' ext Hty.
  eapply (env_prop_typing ESubstitution.erases_extends); tea.
Qed.

(* TODO: Figure out if this (and [erases]) should use [strictly_extends_decls] or [extends] -Jason Gross *)
Lemma erase_constant_body_correct X_type X {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} cb
  (onc : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ on_constant_decl (lift_typing typing) Σ cb ∥) :
  forall Σ Σ', abstract_env_ext_rel X Σ ->
  wf Σ -> wf Σ' -> strictly_extends_decls Σ Σ' ->
  erases_constant_body (Σ', Σ.2) cb (fst (erase_constant_body X_type X cb onc)).
Proof.
  red. destruct cb as [name [bod|] univs]; simpl; eauto. intros.
  set (ecbo := erase_constant_body_obligation_1 X_type X _ _ _ _). clearbody ecbo.
  cbn in *. specialize_Σ H. sq. apply unlift_TermTyp in onc.
  eapply (erases_weakening_env (Σ := Σ) (Σ' := (Σ', univs))); simpl; eauto.
  now eapply erases_erase.
Qed.

Lemma erase_constant_body_correct' {X_type X} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ} {cb}
  {onc : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ on_constant_decl (lift_typing typing) Σ cb ∥}
  {body} :
  EAst.cst_body (fst (erase_constant_body X_type X cb onc)) = Some body ->
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
  ∥ ∑ t T, (Σ ;;; [] |- t : T) * (Σ ;;; [] |- t ⇝ℇ body) *
    (term_global_deps body = snd (erase_constant_body X_type X cb onc)) ∥.
Proof.
  intros. destruct cb as [name [bod|] univs]; simpl; [| now simpl in H].
  simpl in H. noconf H.
  set (obl :=(erase_constant_body_obligation_1 X_type X
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := univs |} onc bod eq_refl)). clearbody obl. cbn in *.
  specialize_Σ H0. destruct (obl _ H0). sq.
  exists bod, A; intuition auto. now eapply erases_erase.
Qed.

Lemma erases_mutual {Σ mdecl m} :
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes m) mdecl m ->
  erases_mutual_inductive_body m (erase_mutual_inductive_body m).
Proof.
  intros oni.
  destruct m; constructor; simpl; auto.
  eapply onInductives in oni; simpl in *.
  assert (Alli (fun i oib =>
    match destArity [] oib.(ind_type) with Some _ => True | None => False end) 0 ind_bodies0).
  { eapply Alli_impl; eauto.
    simpl. intros n x []. simpl in *. rewrite ind_arity_eq.
    rewrite !destArity_it_mkProd_or_LetIn /= //. } clear oni.
  induction X; constructor; auto.
  destruct hd; constructor; simpl; auto.
  clear.
  induction ind_ctors0; constructor; auto.
  cbn in *.
  intuition auto.
  induction ind_projs0; constructor; auto.
Qed.
