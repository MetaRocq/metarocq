(* Distributed under the terms of the MIT license. *)

(* Eta expanded constructors only, see EEtaExpandedFix for the more involved definition where fixpoints are also eta-expanded. *)

From Stdlib Require Import Utf8 Program btauto.Algebra.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames EnvMap BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction EGlobalEnv EExtends EWellformed ELiftSubst ESpineView ECSubst EWcbvEval EWcbvEvalInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

(** We assume [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors eval : core.

Import MRList (map_InP, map_InP_elim, map_InP_spec).

Equations discr_construct (t : term) : Prop :=
discr_construct (tConstruct ind n block_args) := False ;
discr_construct _ := True.

Inductive construct_view : term -> Type :=
| view_construct : forall ind n block_args, construct_view (tConstruct ind n block_args)
| view_other : forall t, discr_construct t -> construct_view t.

Equations construct_viewc t : construct_view t :=
construct_viewc (tConstruct ind n block_args) := view_construct ind n block_args ;
construct_viewc t := view_other t I.

Ltac toAll :=
    repeat match goal with
      | [ H : forall x, In x ?l -> _ |- _ ] => eapply In_All in H
    end.

Import ECSubst.

Section isEtaExp.
  Context (Σ : global_declarations).

  Definition isEtaExp_app ind c k :=
    match EGlobalEnv.lookup_constructor_pars_args Σ ind c with
    | Some (npars, nargs) => leb (npars + nargs) k
    | None => false
    end.

  Import TermSpineView.

  Definition is_nil {A} (l : list A) := match l with [] => true | _ => false end.

  Equations? isEtaExp (e : EAst.term) : bool
    by wf e (fun x y : EAst.term => size x < size y) :=
  | e with TermSpineView.view e := {
    | tRel i => true
    | tEvar ev args => forallb_InP args (fun x H => isEtaExp x)
    | tLambda na M => isEtaExp M
    | tApp u v napp nnil with construct_viewc u :=
      { | view_construct ind i block_args => isEtaExp_app ind i (List.length v) && forallb_InP v (fun x H => isEtaExp x) && is_nil block_args
        | view_other _ _ => isEtaExp u && forallb_InP v (fun x H => isEtaExp x) }
    | tLetIn na b b' => isEtaExp b && isEtaExp b'
    | tCase ind c brs => isEtaExp c && forallb_InP brs (fun x H => isEtaExp x.2)
    | tProj p c => isEtaExp c
    | tFix mfix idx => forallb_InP mfix (fun x H => isLambda x.(dbody) && isEtaExp x.(dbody))
    | tCoFix mfix idx => forallb_InP mfix (fun x H => isEtaExp x.(dbody))
    | tBox => true
    | tVar _ => true
    | tConst _ => true
    | tPrim p => test_primIn p (fun x H => isEtaExp x)
    | tLazy t => isEtaExp t
    | tForce t => isEtaExp t
    | tConstruct ind i block_args => isEtaExp_app ind i 0 && is_nil block_args }.
  Proof.
    all:try lia.
    3:now eapply size_mkApps_f.
    3:{ pose proof (size_mkApps_l napp nnil).
        setoid_rewrite <- (In_size id size H) in H0. unfold id in H0. lia. }
    all:try rewrite size_mkApps.
    all:try setoid_rewrite <- (In_size id size H); unfold id.
    all: try (cbn; lia).
    - eapply (In_size snd size) in H. cbn in H; lia.
    - eapply (In_size dbody size) in H. cbn in H; lia.
    - eapply (In_size dbody size) in H. cbn in H; lia.
    - destruct p as [? []]; cbn in *; intuition eauto.
      subst. lia.
      setoid_rewrite <- (In_size id size H0); unfold id. lia.
  Qed.

End isEtaExp.

#[universes(polymorphic)]
Global Hint Rewrite @test_primIn_spec @forallb_InP_spec : isEtaExp.
Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.

Section isEtaExp.
  Context (Σ : global_context).
  Abbreviation isEtaExp := (isEtaExp Σ).

  Lemma isEtaExp_mkApps_nonnil f v :
    ~~ isApp f -> v <> [] ->
    isEtaExp (mkApps f v) = match construct_viewc f with
      | view_construct ind i block_args => isEtaExp_app Σ ind i #|v| && forallb isEtaExp v && is_nil block_args
      | view_other t discr => isEtaExp f && forallb isEtaExp v
    end.
  Proof using Type.
    rewrite isEtaExp_equation_1.
    intros napp hv.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    cbn. destruct (construct_viewc f); cbn; simp isEtaExp => //.
  Qed.

  Lemma isEtaExp_mkApps_napp f v : ~~ isApp f ->
    isEtaExp (mkApps f v) = match construct_viewc f with
      | view_construct ind i block_args => isEtaExp_app Σ ind i #|v| && forallb isEtaExp v && is_nil block_args
      | view_other t discr => isEtaExp f && forallb isEtaExp v
    end.
  Proof using Type.
    intros napp.
    destruct v using rev_case; simp_eta.
    - destruct construct_viewc; rewrite andb_true_r //.
    - rewrite isEtaExp_mkApps_nonnil //.
  Qed.

  Lemma isEtaExp_Constructor ind i v block_args :
    isEtaExp (mkApps (EAst.tConstruct ind i block_args) v) = isEtaExp_app Σ ind i #|v| && forallb isEtaExp v && is_nil block_args.
  Proof using Type.
    rewrite isEtaExp_mkApps_napp //.
  Qed.


  Lemma isEtaExp_mkApps f u : isEtaExp (mkApps f u) ->
    let (hd, args) := decompose_app (mkApps f u) in
    match construct_viewc hd with
    | view_construct kn c block_args => isEtaExp_app Σ kn c #|args| && forallb isEtaExp args && is_nil block_args
    | view_other u discr => isEtaExp hd && forallb isEtaExp args
    end.
  Proof using Type.
    destruct decompose_app eqn:da.
    rewrite (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l. cbn -[isEtaExp].
    intros eq; rewrite eq.
    destruct (construct_viewc t) => //. simp isEtaExp in eq. rtoProp. solve_all.
    assert (t0 :: l <> []) by congruence.
    revert da H0. generalize (t0 :: l). clear t0 l; intros l.
    intros da nnil.
    rewrite isEtaExp_mkApps_napp //.
  Qed.

  Arguments EEtaExpanded.isEtaExp : simpl never.

  Lemma isEtaExp_mkApps_intro_notConstruct t l : ~~ isConstruct (head t) ->
     isEtaExp t -> All isEtaExp l -> isEtaExp (mkApps t l).
  Proof using Type.
    revert t; induction l using rev_ind; auto.
    intros t isc et a; eapply All_app in a as [].
    depelim a0. clear a0.
    destruct (decompose_app t) eqn:da.
    rewrite (decompose_app_inv da) in et isc *.
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l0. simp_eta.
    - rewrite isEtaExp_mkApps_napp //.
      destruct construct_viewc eqn:vc => //. cbn.
      rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
    - rewrite isEtaExp_mkApps_napp in et => //.
      destruct construct_viewc.
      rewrite head_mkApps in isc => //.
      rewrite -mkApps_app. rewrite isEtaExp_mkApps_napp //.
      destruct (construct_viewc t0) => //.
      move/andP: et => [] -> /=. rtoProp; solve_all.
      rewrite forallb_app. rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
  Qed.

  Lemma isEtaExp_tApp {f u} : isEtaExp (EAst.tApp f u) ->
    let (hd, args) := decompose_app (EAst.tApp f u) in
    match construct_viewc hd with
    | view_construct kn c block_args =>
      args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\
      isEtaExp_app Σ kn c #|args| && forallb isEtaExp args && is_nil block_args
    | view_other _ discr =>
      [&& isEtaExp hd, forallb isEtaExp args, isEtaExp f & isEtaExp u]
    end.
  Proof using Type.
    move/(isEtaExp_mkApps f [u]).
    cbn -[decompose_app]. destruct decompose_app eqn:da.
    destruct construct_viewc eqn:cv => //.
    intros ->.
    pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H.
    rewrite mkApps_app in H. noconf H.
    rewrite remove_last_app last_last. intuition auto.
    destruct l; cbn in *; congruence.
    pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. destruct t => //.
    rewrite mkApps_app in H. noconf H.
    move=> /andP[] etat. rewrite forallb_app => /andP[] etal /=.
    rewrite andb_true_r => etaa. rewrite etaa andb_true_r.
    rewrite etat etal. cbn. rewrite andb_true_r.
    eapply isEtaExp_mkApps_intro_notConstruct; auto; solve_all.
    destruct t => //.
  Qed.

End isEtaExp.

Section WeakEtaExp.
  Context (Σ : global_context).
  Abbreviation isEtaExp := (isEtaExp Σ).

  Lemma isEtaExp_app_mon ind c i i' : i <= i' -> isEtaExp_app Σ ind c i -> isEtaExp_app Σ ind c i'.
  Proof using Type.
    intros le.
    unfold isEtaExp_app.
    destruct lookup_constructor_pars_args as [[pars args]|]=> //.
    cbn.
    do 2 elim: Nat.leb_spec => //. lia.
  Qed.

  Lemma isEtaExp_mkApps_intro t l : isEtaExp t -> All isEtaExp l -> isEtaExp (mkApps t l).
  Proof using Type.
    revert t; induction l using rev_ind; auto.
    intros t et a; eapply All_app in a as [].
    depelim a0. clear a0.
    destruct (decompose_app t) eqn:da.
    rewrite (decompose_app_inv da) in et *.
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l0. simp_eta.
    - rewrite isEtaExp_mkApps_napp //.
      destruct construct_viewc.  cbn. len.
      rtoProp; repeat solve_all. cbn in et. rtoProp. rename H0 into et. simp isEtaExp in et.
      eapply isEtaExp_app_mon; tea; lia.
      eapply All_app_inv; eauto.
      cbn in et. rtoProp. rename H0 into et. simp isEtaExp in et.
      rewrite et forallb_app /=.
      rtoProp; repeat solve_all.
    - rewrite isEtaExp_mkApps_napp in et => //.
      destruct construct_viewc.
      rewrite -mkApps_app. rewrite isEtaExp_Constructor.
      rtoProp; solve_all.
      eapply isEtaExp_app_mon; tea. cbn. len. solve_all. depelim H2.
      solve_all. eapply All_app_inv => //. econstructor; eauto.
      eapply All_app_inv => //. eauto.
      rewrite -mkApps_app. rewrite isEtaExp_mkApps_napp //.
      destruct (construct_viewc t0) => //.
      move/andP: et => [] -> /=. rtoProp; solve_all.
      rewrite forallb_app. rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
  Qed.

  Lemma etaExp_csubst a k b :
    isEtaExp a -> isEtaExp b -> isEtaExp (ECSubst.csubst a k b).
  Proof using Type.
    intros etaa. move b at bottom.
    funelim (isEtaExp b); cbn -[isEtaExp]; try simp_eta; eauto;
      try toAll; repeat solve_all.
    - intros. simp isEtaExp ; cbn. destruct Nat.compare => //. simp_eta in etaa.
    - move/andP: H1 => [] etab etab'.
      apply/andP. split; eauto.
    - rtoProp. intuition eauto. now destruct block_args.
    - rtoProp. intuition eauto.
      solve_all.
    - move/andP: b => [] etaexp h.
      apply/andP; split.
      now eapply isLambda_csubst.
      eapply a0 => //.
    - move/andP: H0 => [] etaexp h.
      rewrite csubst_mkApps /=.
      rewrite isEtaExp_Constructor; solve_all.
      rtoProp; solve_all. solve_all.
      now destruct block_args.
    - rewrite csubst_mkApps /=.
      move/andP: H1 => [] eu ev.
      specialize (H _ k etaa eu).
      eapply isEtaExp_mkApps_intro => //. solve_all.
  Qed.

  Lemma isEtaExp_substl s t :
    forallb isEtaExp s -> isEtaExp t ->
    isEtaExp (substl s t).
  Proof using Type.
    induction s in t |- *; simpl; auto. rtoProp; intuition eauto using etaExp_csubst.
  Qed.

  Lemma isEtaExp_iota_red pars args br :
    forallb isEtaExp args ->
    isEtaExp br.2 ->
    isEtaExp (EGlobalEnv.iota_red pars args br).
  Proof using Type.
    intros etaargs etabr.
    unfold EGlobalEnv.iota_red.
    rewrite isEtaExp_substl // forallb_rev forallb_skipn //.
  Qed.

  Lemma isEtaExp_fix_subst mfix :
    forallb (fun d => isLambda (dbody d) && isEtaExp (dbody d)) mfix ->
    forallb isEtaExp (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; simp_eta; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.

  Lemma isEtaExp_cofix_subst mfix :
    forallb (isEtaExp ∘ dbody) mfix ->
    forallb isEtaExp (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; simp_eta; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.

  Lemma isEtaExp_cunfold_fix mfix idx n f :
    forallb (fun d => isLambda (dbody d) && isEtaExp (dbody d)) mfix ->
    EGlobalEnv.cunfold_fix mfix idx = Some (n, f) ->
    isEtaExp f.
  Proof using Type.
    intros heta.
    unfold EGlobalEnv.cunfold_fix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_fix_subst.
    eapply forallb_nth_error in heta; tea.
    erewrite heq in heta. now move/andP: heta.
  Qed.

  Lemma isEtaExp_cunfold_cofix mfix idx n f :
    forallb (isEtaExp ∘ dbody) mfix ->
    EGlobalEnv.cunfold_cofix mfix idx = Some (n, f) ->
    isEtaExp f.
  Proof using Type.
    intros heta.
    unfold EGlobalEnv.cunfold_cofix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_cofix_subst.
    eapply forallb_nth_error in heta; tea.
    now erewrite heq in heta.
  Qed.

End WeakEtaExp.

Definition isEtaExp_constant_decl Σ cb :=
  option_default (isEtaExp Σ) cb.(cst_body) true.

Definition isEtaExp_decl Σ d :=
  match d with
  | ConstantDecl cb => isEtaExp_constant_decl Σ cb
  | InductiveDecl idecl => true
  end.

Fixpoint isEtaExp_env (Σ : global_declarations) :=
  match Σ with
  | [] => true
  | decl :: Σ => isEtaExp_decl Σ decl.2 && isEtaExp_env Σ
  end.

Lemma isEtaExp_lookup_ext {Σ} {kn d}:
  isEtaExp_env Σ ->
  lookup_env Σ kn = Some d ->
  ∑ Σ', extends_prefix Σ' Σ × isEtaExp_decl Σ' d.
Proof.
  induction Σ; cbn.
  - move=> _; rewrite /declared_constant /lookup_env /= //.
  - move=> /andP[] etaa etaΣ.
    destruct a as [kn' d']; cbn in *.
    rewrite /declared_constant /=.
    case:eqb_specT => //.
    * intros e; subst kn'. move=> [=]. intros ->.
      exists Σ. split => //. now exists [(kn, d)].
    * intros ne. move=> Hl. destruct (IHΣ etaΣ Hl) as [Σ' [ext eta]].
      exists Σ'; split => //.
      destruct ext as [Σ'' ->].
      now exists ((kn', d')::Σ'').
Qed.

Lemma isEtaExp_app_extends {efl : EEnvFlags} Σ Σ' ind k n :
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp_app Σ ind k n ->
  isEtaExp_app Σ' ind k n.
Proof.
  rewrite /isEtaExp_app.
  rewrite /lookup_constructor_pars_args /lookup_constructor /lookup_inductive /lookup_minductive.
  move=> ext wf.
  destruct (lookup_env Σ _) eqn:hl => //.
  rewrite (extends_lookup wf ext hl) /= //.
Qed.

From MetaRocq.Erasure Require Import ELiftSubst.

Lemma isEtaExp_extends {efl : EEnvFlags} Σ Σ' t :
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp Σ t ->
  isEtaExp Σ' t.
Proof.
  intros ext wf.
  funelim (isEtaExp Σ t); simp_eta => //; rtoProp; intuition eauto; rtoProp; intuition auto.
  - eapply In_All in H; solve_all.
  - eapply isEtaExp_app_extends; tea.
  - eapply In_All in H0. solve_all.
  - eapply In_All in H; solve_all.
    move/andP: b => [] -> /=. eauto.
  - eapply In_All in H; solve_all.
  - solve_all.
  - eapply In_All in H; solve_all.
    rewrite isEtaExp_Constructor //. rtoProp; intuition auto.
    eapply isEtaExp_app_extends; tea.
    solve_all.
  - eapply In_All in H0. apply isEtaExp_mkApps_intro; eauto. solve_all.
Qed.

Lemma isEtaExp_extends_decl {efl : EEnvFlags} {Σ Σ' t} :
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp_decl Σ t ->
  isEtaExp_decl Σ' t.
Proof.
  intros ext wf; destruct t; cbn => //.
  rewrite /isEtaExp_constant_decl; destruct (cst_body c) => /= //.
  now eapply isEtaExp_extends.
Qed.

Lemma isEtaExp_lookup {efl : EEnvFlags} {Σ kn d}:
  isEtaExp_env Σ -> wf_glob Σ ->
  lookup_env Σ kn = Some d ->
  isEtaExp_decl Σ d.
Proof.
  move=> etaΣ wfΣ.
  move/(isEtaExp_lookup_ext etaΣ) => [Σ' []] ext hd.
  eapply isEtaExp_extends_decl; eauto.
  now eapply extends_prefix_extends.
Qed.

Section expanded.

Variable Σ : global_declarations.

Local Unset Elimination Schemes.

#[universes(template=no)]
Inductive expanded : term -> Prop :=
| expanded_tRel (n : nat) : expanded (tRel n)
| expanded_tVar (id : ident) : expanded (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall expanded args -> expanded (tEvar ev args)
| expanded_tLambda (na : name) (body : term) : expanded body -> expanded (tLambda na body)
| expanded_tLetIn (na : name) (def : term)(body : term) : expanded def -> expanded body -> expanded (tLetIn na def body)
| expanded_mkApps (f : term) (args : list term) : ~ isConstruct f -> args <> [] -> expanded f -> Forall expanded args -> expanded (mkApps f args)
| expanded_tConst (c : kername) : expanded (tConst c)
| expanded_tCase (ind : inductive) (pars : nat) (discr : term) (branches : list (list name × term)) :
    expanded discr -> Forall (fun br => expanded br.2) branches -> expanded (tCase (ind, pars) discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded t -> expanded (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) :
  Forall (fun d => isLambda d.(dbody) /\ expanded d.(dbody)) mfix -> expanded (tFix mfix idx)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) : Forall (fun d => expanded d.(dbody)) mfix -> expanded (tCoFix mfix idx)
| expanded_tConstruct_app ind idx mind idecl cdecl args :
    declared_constructor Σ (ind, idx) mind idecl cdecl ->
    #|args| >= cstr_arity mind cdecl ->
    Forall expanded args ->
    expanded (mkApps (tConstruct ind idx []) args)
| expanded_tPrim p : primProp@{Set Set} expanded p -> expanded (tPrim p)
| expanded_tLazy t : expanded t -> expanded (tLazy t)
| expanded_tForce t : expanded t -> expanded (tForce t)
| expanded_tBox : expanded tBox.

End expanded.
Derive Signature for expanded.

Lemma expanded_ind :
forall (Σ : global_declarations) (P : term -> Prop),
(forall n : nat, P (tRel n)) ->
(forall id : ident, P (tVar id)) ->
(forall (ev : nat) (args : list term), Forall (expanded Σ) args -> Forall P args -> P (tEvar ev args)) ->
(forall (na : name) (body : term),
 expanded Σ body -> P body -> P (tLambda na body)) ->
(forall (na : name) (def body : term),
 expanded Σ def ->
 P def -> expanded Σ body -> P body -> P (tLetIn na def body)) ->
(forall (f4 : term) (args : list term),
 ~ isConstruct f4 ->
 expanded Σ f4 -> P f4 -> args <> [] -> Forall (expanded Σ) args -> Forall P args -> P (mkApps f4 args)) ->
(forall c : kername, P (tConst c)) ->
(forall (ind : inductive) (pars : nat) (discr : term)
   (branches : list (list name × term)),
 expanded Σ discr ->
 P discr ->
 Forall (fun br : list name × term => expanded Σ br.2) branches ->
 Forall (fun br : list name × term => P br.2) branches ->
 P (tCase (ind, pars) discr branches)) ->
(forall (proj : projection) (t : term),
 expanded Σ t -> P t -> P (tProj proj t)) ->
(forall (mfix : mfixpoint term) (idx : nat),
 Forall (fun d : def term => isLambda (dbody d) /\ expanded Σ (dbody d)) mfix ->  Forall (fun d : def term => P (dbody d)) mfix  -> P (tFix mfix idx)) ->
(forall (mfix : mfixpoint term) (idx : nat),
 Forall (fun d : def term => expanded Σ (dbody d)) mfix ->  Forall (fun d : def term => P (dbody d)) mfix ->
 P (tCoFix mfix idx)) ->
(forall (ind : inductive) (idx : nat) (mind : mutual_inductive_body)
   (idecl : one_inductive_body) cdecl
   (args : list term),
 declared_constructor Σ (ind, idx) mind idecl cdecl ->
 #|args| >= cstr_arity mind cdecl -> Forall (expanded Σ) args -> Forall P args -> P (mkApps (tConstruct ind idx []) args)) ->
(forall p, primProp (expanded Σ) p -> primProp P p -> P (tPrim p)) ->
(forall t, expanded Σ t -> P t -> P (tLazy t)) ->
(forall t, expanded Σ t -> P t -> P (tForce t)) ->
(P tBox) ->
forall t : term, expanded Σ t -> P t.
Proof.
  intros Σ P. intros hrel hvar hevar hlam hletin happ hconst hcase hproj hfix hcofix hcapp hprim hlazy hforce hbox.
  fix f 2.
  intros t Hexp. destruct Hexp; eauto.
  - eapply hevar; eauto. induction H; econstructor; cbn in *; eauto.
  - eapply happ; eauto. clear H0. induction H1; econstructor; cbn in *; eauto.
  - eapply hcase; eauto. induction H; econstructor; cbn in *; eauto.
  - eapply hfix; eauto. induction H; econstructor; cbn in *; intuition eauto.
  - eapply hcofix; eauto. induction H; econstructor; cbn in *; eauto.
  - eapply hcapp; eauto. clear - H1 f. induction H1; econstructor; cbn in *; eauto.
  - eapply hprim; eauto.
    depelim X; constructor. destruct p; split; eauto.
    eapply (make_All_All f a0).
Qed.

Local Hint Constructors expanded : core.

Definition expanded_constant_decl Σ (cb : constant_body) : Prop :=
  on_Some_or_None (expanded Σ) cb.(cst_body).

Definition expanded_decl Σ d :=
  match d with
  | ConstantDecl cb => expanded_constant_decl Σ cb
  | InductiveDecl idecl => True
  end.

Inductive expanded_global_declarations : forall (Σ : global_declarations), Prop :=
| expanded_global_nil : expanded_global_declarations []
| expanded_global_cons decl Σ : expanded_global_declarations Σ ->
  expanded_decl Σ decl.2 -> expanded_global_declarations (decl :: Σ).

Definition expanded_global_env := expanded_global_declarations.

Definition expanded_eprogram_cstrs (p : eprogram) :=
  EEtaExpanded.isEtaExp_env p.1 && EEtaExpanded.isEtaExp p.1 p.2.

Definition expanded_eprogram_env_cstrs (p : eprogram_env) :=
  let decls := p.1.(EEnvMap.GlobalContextMap.global_decls) in
  EEtaExpanded.isEtaExp_env decls && EEtaExpanded.isEtaExp decls p.2.


Lemma isEtaExp_app_expanded Σ ind idx n :
   isEtaExp_app Σ ind idx n = true <->
   exists mind idecl cdecl,
   declared_constructor Σ (ind, idx) mind idecl cdecl /\ n ≥ cstr_arity mind cdecl.
Proof.
  unfold isEtaExp_app, lookup_constructor_pars_args, lookup_constructor, lookup_inductive, lookup_minductive.
  split.
  - intros H.
    destruct lookup_env as [[| mind] | ] eqn:E; cbn in H; try congruence.
    destruct nth_error as [ idecl | ] eqn:E2; cbn in H; try congruence.
    destruct (nth_error (ind_ctors idecl) idx) as [ [cname ?] | ] eqn:E3; cbn in H; try congruence.
    repeat esplit.
    red. all: eauto. unfold cstr_arity; cbn. eapply leb_iff in H. lia.
  - intros (? & ? & ? & [[]] & Hle).
    rewrite H. cbn. rewrite H0. cbn. rewrite H1. cbn.
    eapply leb_iff. eauto.
Qed.

Lemma expanded_isEtaExp_app_ Σ ind idx n mind idecl cdecl :
   declared_constructor Σ (ind, idx) mind idecl cdecl -> n ≥ cstr_arity mind cdecl ->
   isEtaExp_app Σ ind idx n = true.
Proof.
  intros. eapply isEtaExp_app_expanded. eauto 8.
Qed.

Lemma isEtaExp_expanded Σ t :
  isEtaExp Σ t -> expanded Σ t.
Proof.
  funelim (isEtaExp Σ t); intros; solve_all; eauto.
  - rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. eapply In_All in H.
    econstructor. solve_all.
  - eapply andb_true_iff in H1 as []; eauto.
  - rtoProp. eapply isEtaExp_app_expanded in H as (? & ? & ? & ? & ?).
    destruct block_args; inv H0.
    eapply expanded_tConstruct_app with (args := []); eauto.
  - eapply andb_true_iff in H1 as []. destruct ind. econstructor; eauto.
    rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2.
    eapply In_All in H0. solve_all.
  - econstructor. rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0.
    eapply In_All in H. rtoProp; intuition auto; solve_all.
    all: move/andP: b. 2:{ now intros []. }
    intuition auto.
  - econstructor. rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0.
    eapply In_All in H. solve_all.
  - econstructor. rewrite test_primIn_spec in H0. solve_all.
  - rtoProp. eapply In_All in H.
    rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2.
    eapply isEtaExp_app_expanded in H0 as (? & ? & ? & ? & ?).
    destruct block_args; inv H1.
    eapply expanded_tConstruct_app; eauto. solve_all.
  - eapply andb_true_iff in H1 as []. rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2.
    econstructor.
    + destruct u; inv Heq; eauto.
    + eauto.
    + eauto.
    + eapply In_All in H0. solve_all.
Qed.

Lemma expanded_isEtaExp Σ t :
  expanded Σ t -> isEtaExp Σ t.
Proof.
  induction 1; simp_eta; eauto.
  all: try now (
    (try (eapply andb_true_iff; split; eauto));
    (try eapply forallb_Forall);
    eauto).
  - eapply isEtaExp_mkApps_intro; eauto. solve_all.
  - solve_all.
  - rewrite isEtaExp_Constructor. rtoProp; repeat split.
    2: eapply forallb_Forall.
    2: solve_all. eapply expanded_isEtaExp_app_; eauto.
  - solve_all.
Qed.

Lemma expanded_global_env_isEtaExp_env {Σ} : expanded_global_env Σ -> isEtaExp_env Σ.
Proof.
  intros e; induction e; cbn => //.
  rewrite IHe andb_true_r.
  red in H; red. destruct decl as [kn []] => /= //.
  cbn in H. red in H. unfold isEtaExp_constant_decl.
  destruct (cst_body c); cbn in * => //.
  now eapply expanded_isEtaExp.
Qed.

Lemma isEtaExp_env_expanded_global_env {Σ} : isEtaExp_env Σ -> expanded_global_env Σ.
Proof.
  induction Σ; cbn => /= //.
  - constructor.
  - move/andP=> [] etad etae; constructor; eauto. now apply IHΣ.
    move: etad. destruct a.2; cbn in * => //. unfold isEtaExp_constant_decl, expanded_constant_decl.
    destruct (cst_body c) => /= //. apply isEtaExp_expanded.
Qed.

Lemma solve_discr_args {t f args} : ~~ isApp t -> t = mkApps f args -> args = [] /\ f = t.
Proof.
  intros napp ->.
  induction args using rev_ind; cbn in *; auto.
  rewrite mkApps_app in napp. now cbn in napp.
Qed.

Ltac solve_discr_args :=
  match goal with [ H : ?t = mkApps ?f ?args |- _ ] =>
    destruct (@solve_discr_args t f args eq_refl H) as [-> ->] ||
    destruct (@solve_discr_args t f args eq_refl H) as [-> ?]
  end.

Lemma expanded_mkApps_expanded {Σ f args} :
  expanded Σ f -> All (expanded Σ) args ->
  expanded Σ (mkApps f args).
Proof.
  intros.
  destruct (isConstruct f) eqn:eqc.
  destruct f => //.
  - depelim H; try solve_discr_args => //.
    let H3 := match goal with H : tConstruct _ _ _ = tConstruct _ _ _ |- _ => H end in
    noconf H3.
    eapply expanded_tConstruct_app; tea. cbn in H0. lia. solve_all.
  - destruct args using rev_ind; cbn => //.
    eapply expanded_mkApps => //. now rewrite eqc. solve_all.
Qed.

Lemma isEtaExp_tApp_arg Σ t u : isEtaExp Σ (tApp t u) -> isEtaExp Σ u.
Proof.
  move/isEtaExp_tApp. destruct decompose_app eqn:da.
  eapply decompose_app_inv in da. destruct l using rev_case.
  - cbn in da. subst t0. cbn. now move/and3P => [].
  - rewrite mkApps_app in da. noconf da.
    destruct construct_viewc.
    * intros [_ [_ [_ H]]]. move/andP: H => [] /andP[] _. rewrite forallb_app.
      move=> /andP[] //=. now rewrite andb_true_r.
    * now move/and4P => [].
Qed.

From MetaRocq.Erasure Require Import EEtaExpandedFix.

Local Ltac simp_eta ::= simp isEtaExp; rewrite -?isEtaExp_equation_1 -?EEtaExpanded.isEtaExp_equation_1.

Lemma isEtaExpFix_isEtaExp Σ Γ t : EEtaExpandedFix.isEtaExp Σ Γ t -> EEtaExpanded.isEtaExp Σ t.
Proof.
  funelim (isEtaExp Σ Γ t); try solve [simp_eta => //].
  - simp_eta.
    intros Ha. eapply In_All in H. solve_all.
  - simp_eta. rtoProp; intuition auto.
  - simp_eta. rtoProp; intuition auto.
    eapply In_All in H0; solve_all.
  - eapply In_All in H. simp_eta; rtoProp; intuition auto. solve_all.
  - simp_eta. solve_all_k 7. primProp. solve_all.
  - eapply In_All in H. simp_eta; rtoProp; intuition auto.
    rewrite EEtaExpanded.isEtaExp_Constructor. rtoProp; repeat split. eauto.
    solve_all. destruct block_args; cbn in *; eauto.
  - eapply In_All in H, H0. simp_eta.
    move => /andP[] /andP[] etafix etamfix etav.
    eapply EEtaExpanded.isEtaExp_mkApps_intro. simp_eta.
    clear -H etamfix. solve_all. rtoProp; intuition eauto.
    solve_all.
  - eapply In_All in H. simp_eta.
    move=> /andP[] etarel etav.
    eapply EEtaExpanded.isEtaExp_mkApps_intro. now simp_eta. solve_all.
  - eapply In_All in H0. simp_eta.
    move=> /andP[] etau etav.
    eapply EEtaExpanded.isEtaExp_mkApps_intro; auto. solve_all.
Qed.

Lemma isEtaExpFix_env_isEtaExp_env Σ : isEtaExp_env Σ -> EEtaExpanded.isEtaExp_env Σ.
Proof.
  induction Σ; cbn; auto.
  move/andP => [] etaa etaΣ.
  rewrite IHΣ // andb_true_r.
  move: etaa. rewrite /isEtaExp_decl /EEtaExpanded.isEtaExp_decl.
  destruct a.2 => //.
  rewrite /isEtaExp_constant_decl /EEtaExpanded.isEtaExp_constant_decl.
  destruct (cst_body c) => // /=.
  eapply isEtaExpFix_isEtaExp.
Qed.
