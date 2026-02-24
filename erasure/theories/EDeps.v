From Stdlib Require Import Arith List.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import
     PCUICPrimitive PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICWeakeningEnv PCUICWeakeningEnvTyp.
Set Warnings "-notation-overridden".
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ECSubst EInduction
  ELiftSubst EGlobalEnv EWcbvEval Extract ESubstitution.
From MetaRocq.Erasure Require EExtends.
Set Warnings "+notation-overridden".
From MetaRocq.Common Require Import config.

Derive NoConfusion for term.
Derive Signature for erases_deps.
Derive Signature for Forall.

Lemma erases_deps_mkApps Σ Σ' hd args :
  erases_deps Σ Σ' hd ->
  Forall (erases_deps Σ Σ') args ->
  erases_deps Σ Σ' (mkApps hd args).
Proof.
  intros er erall.
  induction args using rev_ind; [easy|].
  rewrite !mkApps_app.
  cbn in *.
  apply Forall_app in erall as (? & ?).
  depelim H0.
  now constructor.
Qed.

Lemma erases_deps_mkApps_inv Σ Σ' hd args :
  erases_deps Σ Σ' (mkApps hd args) ->
  erases_deps Σ Σ' hd /\ Forall (erases_deps Σ Σ') args.
Proof.
  intros er.
  induction args using rev_ind; [easy|].
  rewrite mkApps_app in *.
  cbn in *.
  depelim er.
  intuition auto.
  now apply app_Forall.
Qed.

Lemma erases_deps_lift Σ Σ' n k t :
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (lift n k t).
Proof.
  intros er.
  induction t in k, t, er |- * using EInduction.term_forall_list_ind; cbn in *; auto.
  - now destruct (_ <=? _); constructor.
  - depelim er.
    constructor.
    induction H; cbn in *; [easy|].
    now depelim X.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    econstructor; eauto.
  - depelim er.
    econstructor; eauto. now len.
    clear H3.
    induction X; [easy|].
    depelim H4.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now econstructor.
  - depelim er.
    constructor.
    induction H in k, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim X; depelim er; constructor; cbn. solve_all.
    destruct p. solve_all.
  - depelim er.
  - depelim er.
Qed.

Lemma erases_deps_subst Σ Σ' s k t :
  All (erases_deps Σ Σ') s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (subst s k t).
Proof.
  intros aller er.
  induction t in k, aller, er |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _); [|now constructor].
    destruct nth_error eqn:nth; [|now constructor].
    eapply All_nth_error in nth; [|now eauto].
    now apply erases_deps_lift.
  - depelim er.
    constructor.
    induction H; [simpl; easy|].
    depelim X.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    econstructor; eauto.
  - depelim er.
    econstructor; eauto. now len. clear H3.
    induction X; [easy|].
    depelim H4.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now econstructor.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim X; depelim er; constructor; cbn; intuition auto; solve_all.
  - depelim er.
  - depelim er.
Qed.

Lemma erases_deps_subst1 Σ Σ' t k u :
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' u ->
  erases_deps Σ Σ' (subst1 t k u).
Proof.
  intros.
  apply erases_deps_subst; [|easy].
  now constructor.
Qed.

Lemma erases_deps_csubst Σ Σ' s k t :
  erases_deps Σ Σ' s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (csubst s k t).
Proof.
  intros aller er.
  induction t in k, aller, er |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ ?= _); try constructor; easy.
  - depelim er.
    constructor.
    induction H; [simpl; easy|].
    depelim X.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    cbn. econstructor; eauto.
  - depelim er.
    econstructor; [easy|easy|easy|easy|easy| | ].
    now len. clear H3.
    induction X; [easy|].
    depelim H4.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now econstructor.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl;easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim X; depelim er; constructor; cbn; intuition auto; solve_all.
  - depelim er.
  - depelim er.
Qed.

Lemma erases_deps_substl Σ Σ' s t :
  Forall (fun s => erases_deps Σ Σ' s) s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (substl s t).
Proof.
  intros all exp.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_app in all as (? & erx).
  depelim erx.
  now apply erases_deps_csubst.
Qed.

Lemma Forall_erases_deps_fix_subst Σ Σ' defs :
  Forall (erases_deps Σ Σ' ∘ dbody) defs ->
  Forall (erases_deps Σ Σ') (fix_subst defs).
Proof.
  intros all.
  unfold EGlobalEnv.fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now constructor.
  - now apply IHl.
Qed.

Lemma Forall_erases_deps_cofix_subst Σ Σ' defs :
  Forall (erases_deps Σ Σ' ∘ dbody) defs ->
  Forall (erases_deps Σ Σ') (EGlobalEnv.cofix_subst defs).
Proof.
  intros all.
  unfold EGlobalEnv.cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now constructor.
  - now apply IHl.
Qed.

Lemma erases_deps_cunfold_fix Σ Σ' defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
  erases_deps Σ Σ' f.
Proof.
  intros cuf all.
  unfold cunfold_fix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply erases_deps_substl; [|easy].
  now apply Forall_erases_deps_fix_subst.
Qed.

Lemma erases_deps_cunfold_cofix Σ Σ' defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
  erases_deps Σ Σ' f.
Proof.
  intros cuf all.
  unfold cunfold_cofix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply erases_deps_substl; [|easy].
  now apply Forall_erases_deps_cofix_subst.
Qed.

Notation "Σ ⊢ s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma erases_deps_eval {wfl:WcbvFlags} {hcon : with_constructor_as_block = false} Σ t v Σ' :
  Σ' ⊢ t ⇓ v ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' v.
Proof.
  intros ev er.
  induction ev in t, v, ev, er |- *; cbn in *.
  - now constructor.
  - depelim er.
    apply IHev3.
    apply erases_deps_csubst; [easy|].
    intuition auto.
    now depelim H.
  - depelim er.
    now apply IHev2, erases_deps_csubst.
  - depelim er.
    apply IHev2.
    unfold EGlobalEnv.iota_red.
    apply erases_deps_substl.
    + intuition auto.
      apply erases_deps_mkApps_inv in H5.
      now apply Forall_rev, Forall_skipn.
    + eapply nth_error_forall in e2; [|now eauto].
      assumption.
  - congruence.
  - depelim er.
    subst brs; cbn in *.
    depelim H4.
    cbn in *.
    apply IHev2.
    apply erases_deps_substl; [|easy].
    apply All_Forall, All_repeat.
    now constructor.
  - depelim er.
    intuition auto.
    eapply erases_deps_mkApps_inv in H as (? & ?).
    depelim H.
    apply IHev3.
    constructor; [|easy].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_fix.
  - depelim er.
    intuition auto.
    apply erases_deps_mkApps_inv in H as (? & ?).
    constructor; [|easy].
    now apply erases_deps_mkApps.
  - depelim er.
    specialize (IHev1 er1).
    specialize (IHev2 er2).
    eapply IHev3. econstructor; eauto.
    eapply erases_deps_cunfold_fix; eauto.
    now depelim IHev1.
  - depelim er.
    specialize (IHev1 er).
    apply erases_deps_mkApps_inv in IHev1 as (? & ?).
    depelim H5.
    apply IHev2.
    econstructor; [easy|easy|easy|easy| |easy|easy ].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix; eauto.
  - depelim er.
    specialize (IHev1 er).
    apply erases_deps_mkApps_inv in IHev1 as (? & ?).
    depelim H3.
    apply IHev2.
    econstructor; eauto.
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix.
  - depelim er.
    now apply IHev, H2.
  - depelim er.
    intuition auto.
    apply erases_deps_mkApps_inv in H3 as (? & ?).
    apply IHev2.
    now eapply nth_error_forall in e3.
  - congruence.
  - constructor.
  - depelim er.
    now constructor.
  - congruence.
  - depelim er. now constructor.
  - depelim er; depelim X; constructor; eauto.
    eapply All2_over_undep in a0. solve_all.
  - easy.
  - easy.
Qed.

#[global]
Hint Resolve erases_deps_eval erases_deps_subst erases_deps_subst1 : core.

Local Existing Instance config.extraction_checker_flags.

Lemma erases_deps_forall_ind Σ Σ'
  (P : Extract.E.term -> Prop)
  (Hbox : P Extract.E.tBox)
  (Hrel : forall i : nat, P (Extract.E.tRel i))
  (Hvar : forall n : ident, P (Extract.E.tVar n))
  (Hevar :
     forall (m : nat) (l : list Extract.E.term),
       Forall P l ->
       Forall (erases_deps Σ Σ') l -> P (Extract.E.tEvar m l))
  (Hlam : forall (na : name) (body : Extract.E.term),
        erases_deps Σ Σ' body -> P body -> P (Extract.E.tLambda na body))
  (Hletin : forall (na : name) (val body : Extract.E.term),
        erases_deps Σ Σ' val ->
        P val -> erases_deps Σ Σ' body -> P body -> P (Extract.E.tLetIn na val body))
  (Happ : forall hd arg : Extract.E.term,
        erases_deps Σ Σ' hd -> P hd -> erases_deps Σ Σ' arg -> P arg -> P (Extract.E.tApp hd arg))
  (Hconst : forall (kn : kername) (cb : PCUICAst.PCUICEnvironment.constant_body) (cb' : EAst.constant_body),
      PCUICAst.declared_constant Σ kn cb ->
      EGlobalEnv.declared_constant Σ' kn cb' ->
      erases_constant_body (Σ, cst_universes cb) cb cb' ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> erases_deps Σ Σ' body) ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> P body) ->
        P (Extract.E.tConst kn))
  (Hconstruct : forall (ind : inductive) (c : nat) mdecl idecl cdecl mdecl' idecl' cdecl',
      PCUICAst.declared_constructor Σ (ind, c) mdecl idecl cdecl ->
      declared_constructor Σ' (ind, c) mdecl' idecl' cdecl' ->
      erases_one_inductive_body idecl idecl' ->
      erases_mutual_inductive_body mdecl mdecl' ->
      P (Extract.E.tConstruct ind c []))
  (Hcase : forall (p : inductive × nat) mdecl idecl mdecl' idecl' (discr : Extract.E.term) (brs : list (list name × Extract.E.term)),
        PCUICAst.declared_inductive Σ (fst p) mdecl idecl ->
        EGlobalEnv.declared_inductive Σ' (fst p) mdecl' idecl' ->
        erases_mutual_inductive_body mdecl mdecl' ->
        erases_one_inductive_body idecl idecl' ->
        erases_deps Σ Σ' discr ->
        P discr ->
        #|idecl'.(ind_ctors)| = #|brs| ->
        Forall (fun br : _ × Extract.E.term => erases_deps Σ Σ' br.2) brs ->
        Forall (fun br => P br.2) brs ->
        P (Extract.E.tCase p discr brs))
  (Hproj : forall (p : projection) mdecl idecl cdecl pdecl mdecl' idecl' cdecl' pdecl' (t : Extract.E.term),
        PCUICAst.declared_projection Σ p mdecl idecl cdecl pdecl ->
        EGlobalEnv.declared_projection Σ' p mdecl' idecl' cdecl' pdecl' ->
        erases_mutual_inductive_body mdecl mdecl' ->
        erases_one_inductive_body idecl idecl' ->
        erases_deps Σ Σ' t -> P t -> P (Extract.E.tProj p t))
  (Hfix : forall (defs : list (Extract.E.def Extract.E.term)) (i : nat),
         Forall (fun d : Extract.E.def Extract.E.term => erases_deps Σ Σ' (Extract.E.dbody d)) defs ->
         Forall (fun d => P (E.dbody d)) defs ->
         P (Extract.E.tFix defs i))
  (Hcofix : forall (defs : list (Extract.E.def Extract.E.term)) (i : nat),
         Forall (fun d : Extract.E.def Extract.E.term => erases_deps Σ Σ' (Extract.E.dbody d)) defs ->
         Forall (fun d => P (E.dbody d)) defs ->
         P (Extract.E.tCoFix defs i))
  (Hprim : forall p, primProp (erases_deps Σ Σ') p -> primProp P p -> P (Extract.E.tPrim p)):
  forall t, erases_deps Σ Σ' t -> P t.
Proof.
  fix f 2.
  intros t ed.
  move f at top.
  destruct ed;
    try solve [match goal with
    | [H: _ |- _] => apply H
    end; auto].
  - apply Hevar; [|assumption].
    revert l H.
    fix f' 2.
    intros l [].
    + now constructor.
    + constructor; [now apply f|now apply f'].
  - eapply Hconst; try eassumption.
    intros.
    apply f.
    now apply H2.
  - eauto.
  - eapply Hcase; try eassumption.
    + now apply f.
    + clear H3; revert brs H4.
      fix f' 2.
      intros brs []; [now constructor|].
      constructor; [now apply f|now apply f'].
  - eapply Hproj; try eassumption.
    now apply f.
  - eapply Hfix; try assumption.
    revert defs H.
    fix f' 2.
    intros defs []; [now constructor|].
    constructor; [now apply f|now apply f'].
  - apply Hcofix; try assumption.
    revert defs H.
    fix f' 2.
    intros defs []; [now constructor|].
    constructor; [now apply f|now apply f'].
  - eapply Hprim; tea; constructor.
  - eapply Hprim; tea; constructor.
  - eapply Hprim; tea; constructor.
  - eapply Hprim; tea; constructor.
    intuition auto; solve_all.
    split. auto. destruct a as [d v]. cbn in *.
    eapply Forall_All.
    revert v H.
    fix aux 2.
    intros ? [];constructor; auto.
Defined.

(* Lemma fresh_global_erase {cf : checker_flags} Σ Σ' kn :
fresh_global kn Σ  -> erases_global Σ Σ' -> EExtends.fresh_global kn Σ'.
Proof.
  induction 2.
  - econstructor.
  - invs H. econstructor; eauto. eapply IHerases_global_decls; eauto.
  - invs H. econstructor; eauto. eapply IHerases_global_decls; eauto.
Qed.

Lemma wf_global_erase {cf : checker_flags} Σ Σ' :
  ∥ wf Σ ∥ -> erases_global Σ Σ' -> ∥ EExtends.wf_glob Σ' ∥.
Proof.
  intros Hwf H. induction H.
  - sq. econstructor.
  - forward IHerases_global_decls; sq; invs Hwf; eauto.
    econstructor. eauto. eapply fresh_global_erase; eauto.
  - forward IHerases_global_decls; sq; invs Hwf; eauto.
    econstructor. eauto. eapply fresh_global_erase; eauto.
Qed. *)

Lemma erases_deps_cons Σ Σ' kn decl decl' t :
  on_global_univs Σ.(universes) ->
  on_global_decls cumulSpec0 (lift_typing typing) Σ.(universes) Σ.(retroknowledge) ((kn, decl) :: Σ.(declarations)) ->
  erases_deps Σ Σ' t ->
  erases_deps (add_global_decl Σ (kn, decl)) ((kn, decl') :: Σ') t.
Proof.
  intros wfu wfΣ er.
  induction er using erases_deps_forall_ind; try solve [now constructor].
  inversion wfΣ.
  unshelve epose proof (H_ := declared_constant_to_gen H); eauto.
  3: econstructor; eauto.
  apply PCUICWeakeningEnv.lookup_env_Some_fresh in H_ as not_fresh.
  econstructor.
  - unfold PCUICAst.declared_constant, PCUICAst.declared_constant_gen in *; cbn.
    inversion wfΣ; subst. destruct X0.
    destruct (eqb_spec kn0 kn) as [<-|]; [congruence|].
    right. eassumption.
  - unfold EGlobalEnv.declared_constant in *. cbn -[ReflectEq.eqb].
    inversion wfΣ; subst. destruct X0.
    destruct (ReflectEq.eqb_spec kn0 kn); [congruence|].
    eassumption.
  - unfold erases_constant_body in *.
    destruct PCUICAst.PCUICEnvironment.cst_body eqn:body.
    + destruct E.cst_body eqn:ebody; [|easy].
      assert (PCUICAst.declared_constant (add_global_decl Σ (kn, decl)) kn0 cb).
      { unfold PCUICAst.declared_constant, declared_constant_gen.
        cbn.
        inversion wfΣ; subst. destruct X0.
        destruct (eqb_spec kn0 kn) as [<-|]; [congruence|].
        easy. }
      inversion wfΣ; subst. destruct X0.
      eapply declared_constant_inv in H4; eauto.
      2:exact weaken_env_prop_typing.
      red in H4.
      rewrite body in *.
      cbn in *.
      eapply (erases_extends (_, cst_universes cb)); cbn. 5:tea.
      1,3,5,6:constructor; auto.
      2:{ split; auto. eexists [_]; reflexivity. }
      eapply declared_constant_inv in H.
      2:exact weaken_env_prop_typing.
      2: easy.
      2: easy.
      unfold on_constant_decl in H.
      rewrite body in *.
      apply H.
    + now destruct E.cst_body.
  - easy.
  - econstructor; eauto. eapply weakening_env_declared_constructor; eauto with pcuic; tc.
    { eapply extends_decls_extends, strictly_extends_decls_extends_decls. econstructor; try reflexivity. eexists [(_, _)]; reflexivity. }
    invs wfΣ.
    destruct H0. split. 2: eauto.
    destruct d. split; eauto.
    red. cbn. cbn in *. destruct X0.
    destruct (eqb_spec (inductive_mind ind) kn). cbn in *.
    unshelve eapply declared_constructor_to_gen in H; eauto.
    3: econstructor; eauto. destruct H as [[]]. cbn in *.
    eapply PCUICWeakeningEnv.lookup_env_Some_fresh in kn_fresh. eauto.
    rewrite H4 in H. eapply H. exact H0.
  - destruct H as [H H'].
    inv wfΣ. destruct X0.
    unshelve eapply declared_minductive_to_gen in H; eauto.
    3: econstructor; eauto.
    econstructor; eauto.
    split; eauto. eapply declared_minductive_from_gen.
    red in H |- *.
    unfold PCUICEnvironment.lookup_env.
    simpl. destruct (eqb_spec (inductive_mind p.1) kn); auto. subst.
    eapply PCUICWeakeningEnv.lookup_env_Some_fresh in H; eauto. contradiction.
    destruct H0 as [H0 H0'].
    split; eauto. red in H0 |- *. cbn.
    change (eq_kername (inductive_mind p.1) kn) with (ReflectEq.eqb (inductive_mind p.1) kn).
    destruct (ReflectEq.eqb_spec (inductive_mind p.1) kn); auto. subst.
    eapply PCUICWeakeningEnv.lookup_env_Some_fresh in H. eauto.
    contradiction.
  - destruct H as [[[declm decli] declc] [declp hp]].
    inv wfΣ. destruct X0.
    unshelve eapply declared_minductive_to_gen in declm; eauto.
    3: econstructor; eauto.
    econstructor; eauto.
    apply declared_projection_from_gen.
    repeat split; eauto.
    unfold PCUICAst.declared_minductive, declared_minductive_gen in *.
    unfold PCUICEnvironment.lookup_env.
    simpl in *.
    destruct (ReflectEq.eqb_spec (inductive_mind p.(proj_ind)) kn). subst.
    eapply PCUICWeakeningEnv.lookup_env_Some_fresh in declm; eauto. contradiction.
    apply declm.
    destruct H0 as [[[]]]. destruct a.
    repeat split; eauto.
    simpl. unfold declared_minductive. cbn.
    destruct (ReflectEq.eqb_spec (inductive_mind p.(proj_ind)) kn); auto.
    unfold declared_minductive_gen in declm. cbn in *.
    rewrite H in declm.
    eapply PCUICWeakeningEnv.lookup_env_Some_fresh in kn_fresh.
    eauto. eauto.
  - depelim X0; intuition auto; constructor; auto.
Qed.

Derive Signature for erases_global_decls.
Derive Signature for Forall2.

Definition globals_erased_with_deps Σ Σ' :=
  (forall k cst,
    PCUICAst.declared_constant Σ k cst ->
    exists cst',
      EGlobalEnv.declared_constant Σ' k cst' /\
      erases_constant_body (Σ, cst_universes cst) cst cst' /\
      (forall body, cst_body cst' = Some body -> erases_deps Σ Σ' body)) /\
  (forall k mdecl idecl,
      PCUICAst.declared_inductive Σ k mdecl idecl ->
      exists mdecl' idecl',
        EGlobalEnv.declared_inductive Σ' k mdecl' idecl' /\
        erases_mutual_inductive_body mdecl mdecl').

Lemma erases_declared_constructor {Σ : global_env_ext} Σ' kn k mind idecl cdecl :
  PCUICAst.declared_constructor Σ.1 (kn, k) mind idecl cdecl ->
  globals_erased_with_deps Σ Σ' ->
  exists mind' idecl', (* declared_inductive Σ' (kn, k).1 mind' idecl' ->
  erases_one_inductive_body idecl idecl' -> *)
  declared_constructor Σ' (kn, k) mind' idecl' (mkConstructor (PCUICEnvironment.cstr_name cdecl) (PCUICEnvironment.cstr_arity cdecl)) /\
  erases_one_inductive_body idecl idecl' /\
  erases_mutual_inductive_body mind mind'.
Proof.
  intros [Hcon1 Hcon2] H.
  eapply H in Hcon1 as Hcon3. destruct Hcon3 as (mdecl' & idecl' & H1 & H2).
  pose proof H2 as H2'.
  destruct H1. destruct H2. cbn in *.
  destruct Hcon1 as [Hcon1 Hcon3]. red in Hcon1.
  eapply Forall2_nth_error_Some_l in H2 as (? & ? & ?); eauto.
  rewrite H2 in H1. invs H1. pose proof H4 as H4'.
  destruct H4 as (? & ? & ? & ? & ?).
  eapply Forall2_nth_error_Some_l in H1 as ([] & ? & ? & ?); subst; eauto.
  eexists. eexists. split; [ | split]; eauto.
  repeat eapply conj; try eassumption. cbn in *. now rewrite H8, H9.
Qed.

Lemma Forall2_nth_error_left {A B} {P} {l : list A} {l' : list B} : Forall2 P l l' ->
  forall n x, nth_error l n = Some x ->
  exists x', nth_error l' n = Some x' /\ P x x'.
Proof.
  induction 1; destruct n; simpl; auto; try discriminate.
  intros x' [= ->]. eexists; eauto.
Qed.

Lemma erases_deps_single Σ Σ' Γ t T et :
  wf_ext Σ ->
  Σ;;; Γ |- t : T ->
  Σ;;; Γ |- t ⇝ℇ et ->
  globals_erased_with_deps Σ Σ' ->
  erases_deps Σ Σ' et.
Proof.
  intros wf wt er Σer.
  induction er in er, t, T, wf, wt |- * using erases_forall_list_ind;
    cbn in *; try solve [constructor].
  - now apply inversion_Evar in wt.
  - constructor.
    now apply inversion_Lambda in wt as (? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & h1 & ? & ?); eauto.
    apply unlift_TermTyp in h1.
    now constructor; eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
    now constructor; eauto.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    apply Σer in d as d'; destruct d' as (? & ? & ? & ?).
    now econstructor; eauto.
  - eapply inversion_Construct in wt as (? & ? & ? & ? & ? & ? & ?); eauto.
    pose proof d as d'. destruct d'.
    destruct (proj2 Σer _ _ _ H0) as (? & ? & ? & ? & ?).
    edestruct @erases_declared_constructor as (? & ? & ? & ? & ?); eauto.
    econstructor; eauto.
  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    destruct (proj2 Σer _ _ _ x1) as (? & ? & ? & ?).
    econstructor; eauto.
    destruct H2. destruct x1; eauto. destruct H1.
    eapply Forall2_All2 in H2. eapply All2_nth_error in H2; eauto.
    { eapply Forall2_length in H0. eapply All2i_length in brs_ty.
      eapply All2_length in X. rewrite <- H0.
      depelim H2. destruct H1 as [].
      destruct x1 as []. eapply Forall2_nth_error_left in H2 as [x' []]; tea.
      rewrite H4 in H2; noconf H2. depelim H7. eapply Forall2_length in H2. lia. }
    clear -wf brs_ty X H0 Σer.
    subst predctx ptm.
    clear X.
    revert brs_ty brs' H0 Σer.
    generalize (PCUICEnvironment.ind_ctors x0).
    induction 1; intros er deps.
    { now depelim er. }
    depelim deps.
    destruct r0 as (? & ? & ? & ?).
    intros er.
    constructor; eauto. eapply H; auto.
    now rewrite <-(PCUICCasesContexts.inst_case_branch_context_eq a).

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?&?); eauto.
    destruct (proj2 Σer _ _ _ (proj1 (proj1 d))) as (? & ? & ? & ?).
    destruct d as [[[declm decli] declc] [declp hp]].
    set (H1' := H1). destruct H1'.
    eapply Forall2_All2 in H2. eapply All2_nth_error_Some in H2 as [bod' [hnth' ebod']]; eauto.
    set (H1' := ebod'). destruct H1' as [Hctors [Hprojs _]].
    eapply Forall2_All2 in Hctors. eapply All2_nth_error_Some in Hctors as [ctor' [hnth'' [Hctor' Hctor'']]]; eauto.
    eapply Forall2_All2 in Hprojs. eapply All2_nth_error_Some in Hprojs as [proj' [hnthp ?]]; eauto.
    econstructor; eauto. repeat split; eauto.
    repeat split; eauto. cbn. apply H0. now rewrite <- H3, hp.

  - constructor.
    apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H Σer.
    revert a0 X H Σer.
    generalize mfix at 1 3 5.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct a0 as [? ? ? ?].
    apply unlift_TermTyp in o.
    now constructor; eauto.
  - constructor.
    apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H Σer.
    revert a0 X H Σer.
    generalize mfix at 1 3 5.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct p as (?&?&?).
    apply unlift_TermTyp in o.
    now constructor; eauto.
  - eapply inversion_Prim in wt as [prim_ty [decl []]]; eauto.
    depelim H0; depelim p1; depelim X; cbn in *; try constructor; cbn; intuition eauto. solve_all.
Qed.

Lemma erases_global_all_deps Σ Σ' :
  wf Σ ->
  erases_global Σ Σ' ->
  globals_erased_with_deps Σ Σ'.
Proof.
  intros wf erg.
  set (Σg := Σ). destruct Σ as [univs Σ retro]; cbn in *.
  induction Σ as [|(kn, decl) Σ IH] in Σ', Σg, wf, erg |- *; cbn in *.
  - depelim erg.
    split; [intros ? ? decl|intros ? ? ? [decl ?]].
    unshelve eapply declared_constant_to_gen in decl; eauto.
    discriminate decl.
    unshelve eapply declared_minductive_to_gen in decl; eauto.
    discriminate decl.
  - split.
    intros kn' cst' decl'.
    destruct (eq_dec kn kn') as [<-|].
    + unshelve eapply declared_constant_to_gen in decl'; eauto.
      unfold declared_constant_gen, EGlobalEnv.declared_constant in *; cbn in *.
      rewrite eq_kername_refl in *.
      noconf decl'.
      depelim erg.
      exists cb'.
      cbn. rewrite eq_kername_refl.
      split; [easy|].
      inversion wf; subst.
      cbn in *.
      split.
      * unfold erases_constant_body, on_constant_decl in *.
        destruct ?; [|easy].
        destruct ?; [|easy].
        depelim wf. depelim o0. destruct o1. cbn in *.
        eapply (erases_extends ({| universes := univs; declarations := Σ |}, cst_universes cst')); eauto.
        cbn. 4:{ split; eauto; cbn; try reflexivity. eexists [_]; cbn; reflexivity. }
        constructor; auto. cbn. red in on_global_decl_d. rewrite E in on_global_decl_d. apply unlift_TermTyp in on_global_decl_d. exact on_global_decl_d.
        split; auto.
      * intros.
        eapply (erases_deps_cons {| universes := univs; declarations := Σ |} _ kn (PCUICEnvironment.ConstantDecl cst')); auto.
        unfold erases_constant_body in *.
        rewrite H1 in *.
        destruct ?; [|easy].
        unfold on_constant_decl in *.
        cbn in *.
        eapply (erases_deps_single (_, _)). 3:eauto.
        depelim wf. depelim o0. destruct o1.
        now split; cbn; eauto.
        depelim wf. depelim o0. destruct o1. do 2 red in on_global_decl_d. rewrite E in on_global_decl_d.
        now apply unlift_TermTyp in on_global_decl_d.
        apply IH; eauto. depelim wf. now depelim o0.
    + set (Σu := {| universes := univs; declarations := Σ; retroknowledge := retro |}).
      assert (wfΣu : PCUICTyping.wf Σu).
      { depelim wf. now depelim o0. }
      assert (exists decl' Σ'', Σ' = (kn, decl') :: Σ'' /\ erases_global Σu Σ'')
        as (erdecl & ? & -> & erg')
          by now depelim erg; eexists _, _.
      apply IH in erg'. 2:{ depelim wf. now depelim o0. }
      assert (decl_ext: PCUICAst.declared_constant Σu kn' cst').
      { unshelve eapply declared_constant_to_gen in decl'; eauto.
        eapply declared_constant_from_gen.
        unfold declared_constant_gen in *; cbn in *.
        destruct (eqb_spec kn' kn); [|eauto]. subst. contradiction. }
      specialize (proj1 erg' kn' cst' decl_ext) as (cst & decl'' & ? & ?).
      exists cst.
      split; [|split].
      * unfold declared_constant in *; cbn. rewrite decl''.
        change (eq_kername kn' kn) with (ReflectEq.eqb kn' kn).
        destruct (ReflectEq.eqb_spec kn' kn); auto. congruence.
      * inversion wf; subst.
        eapply declared_constant_inv in decl_ext; eauto.
        2: exact weaken_env_prop_typing.
        unfold on_constant_decl, erases_constant_body in *.
        destruct ?; [|easy].
        destruct ?; [|easy].
        apply unlift_TermTyp in decl_ext.
        eapply (erases_extends (Σu, cst_universes cst')).
        4:{ split; cbn; auto. eexists [_]; cbn; reflexivity. }
        all: cbn; eauto.
      * intros.
        apply H0 in H1.
        eapply (erases_deps_cons Σu); eauto. apply wfΣu. apply wf.
  + pose proof (wf' := wf). intros k mdecl idecl decli.
    depelim erg.
    * inv wf. inv X.
      specialize (IH _ (H0, X0) erg).
      apply proj2 in IH. specialize (IH k mdecl idecl).
      forward IH.
      assert (wf Σg).
      { econstructor; eauto. unfold Σg; cbn. econstructor;
        eauto. }
      destruct decli as [decli ?]. split; auto. cbn in X0, X1.
      unshelve eapply declared_minductive_to_gen in decli; eauto.
      eapply declared_minductive_from_gen.
      red in decli |- *. simpl in decli |- *.
      unfold PCUICEnvironment.lookup_env in decli |- *. simpl in *.
      destruct (eqb_spec (inductive_mind k) kn).  subst. discriminate. auto.
      destruct IH as [mdecl' [idecl' [decli' er]]].
      exists mdecl', idecl'. split; auto.
      red. destruct decli'; split; auto.
      assert (wf Σg).
      { econstructor; eauto. unfold Σg; cbn. econstructor;
        eauto. }
      destruct decli as [decli ?].
      unshelve eapply declared_minductive_to_gen in decli; eauto.
      unfold declared_minductive in *.
      simpl. destruct (eqb_spec (inductive_mind k) kn); subst; auto.
      unfold declared_inductive_gen, declared_minductive_gen in decli.
      unfold PCUICEnvironment.lookup_env in decli.
      simpl in decli. rewrite eq_kername_refl in decli. intuition discriminate.
    * inv wf. inv X. destruct X1.
      specialize (IH _ (H0, X0) erg).
      destruct decli as [decli ?].
      unshelve eapply declared_minductive_to_gen in decli; eauto.
      simpl in decli |- *.
      unfold declared_minductive_gen, PCUICEnvironment.lookup_env in decli.
      simpl in decli.
      destruct (eqb_specT (inductive_mind k) kn). simpl in *. subst. noconf decli.
      destruct (Forall2_nth_error_left (proj1 H) _ _ H1); eauto.
      eexists _, _; intuition eauto. split; eauto. red.
      simpl. rewrite eqb_refl. congruence.
      unshelve refine (let Σ_ : global_env := _ in _).
      { econstructor. exact univs. exact Σ. eauto. }
      change (declared_minductive_gen (PCUICEnvironment.lookup_env Σ_) (inductive_mind k) mdecl) in decli.
      eapply declared_minductive_from_gen in decli.
      destruct (proj2 IH _ _ _ (conj decli H1)) as [m' [i' [decli' ei]]].
      eexists _, _; intuition eauto.
      destruct decli'; red; split; eauto.
      red in d |- *. simpl.
      apply neqb in n. destruct eqb; cbn in n; try congruence.
Qed.

Lemma erases_global_erases_deps Σ Γ t T et Σ' :
  wf_ext Σ ->
  Σ;;; Γ |- t : T ->
  Σ;;; Γ |- t ⇝ℇ et ->
  erases_global Σ Σ' ->
  erases_deps Σ Σ' et.
Proof.
  intros.
  eapply erases_deps_single; eauto.
  now eapply erases_global_all_deps.
Qed.
