(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion
     PCUICSafeLemmata. (* for welltyped *)
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EDeps EExtends
    ELiftSubst ECSubst EGlobalEnv EWellformed EWcbvEval Extract Prelim
    EEnvMap EArities EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

(** We assumes [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors eval : core.

Section remove_match_on_box.
  Context (Σ : GlobalContextMap.t).

  Definition isprop_ind Σ (ind:inductive × nat)
    := match GlobalContextMap.inductive_isprop_and_pars Σ (fst ind) with
        | Some (true, _) => true
        | _ => false
    end.

  Fixpoint remove_match_on_box (t : term) : term :=
    match t with
    | tRel i => tRel i
    | tEvar ev args => tEvar ev (List.map remove_match_on_box args)
    | tLambda na M => tLambda na (remove_match_on_box M)
    | tApp u v => tApp (remove_match_on_box u) (remove_match_on_box v)
    | tLetIn na b b' => tLetIn na (remove_match_on_box b) (remove_match_on_box b')
    | tCase ind c brs =>
      let brs' := List.map (on_snd remove_match_on_box) brs in
      if isprop_ind Σ ind
      then
        match brs' with
        | [(a, b)] => ECSubst.substl (repeat tBox #|a|) b
        | _ => tCase ind (remove_match_on_box c) brs'
        end
      else tCase ind (remove_match_on_box c) brs'
    | tProj p c =>
      match GlobalContextMap.inductive_isprop_and_pars Σ p.(proj_ind) with
      | Some (true, _) => tBox
      | _ => tProj p (remove_match_on_box c)
      end
    | tFix mfix idx =>
      let mfix' := List.map (map_def remove_match_on_box) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := List.map (map_def remove_match_on_box) mfix in
      tCoFix mfix' idx
    | tBox => t
    | tVar _ => t
    | tConst _ => t
    | tConstruct ind i args => tConstruct ind i (map remove_match_on_box args)
    | tPrim p => tPrim (map_prim remove_match_on_box p)
    | tLazy t => tLazy (remove_match_on_box t)
    | tForce t => tForce (remove_match_on_box t)
    end.

  Lemma remove_match_on_box_mkApps f l : remove_match_on_box (mkApps f l) = mkApps (remove_match_on_box f) (map remove_match_on_box l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_repeat {A B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
  Proof using Type.
    now induction n; simpl; auto; rewrite IHn.
  Qed.

  Lemma map_remove_match_on_box_repeat_box n : map remove_match_on_box (repeat tBox n) = repeat tBox n.
  Proof using Type. by rewrite map_repeat. Qed.

  Import ECSubst.

  Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    rewrite mkApps_app /= IHl.
    now rewrite -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
  Qed.

  Lemma csubst_closed t k x : closedn k x -> csubst t k x = x.
  Proof using Type.
    induction x in k |- * using EInduction.term_forall_list_ind; simpl; auto.
    all:try solve [intros; f_equal; solve_all; eauto].
    intros Hn. eapply Nat.ltb_lt in Hn.
    - destruct (Nat.compare_spec k n); try lia. reflexivity.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
  Qed.

  Lemma closed_remove_match_on_box t k : closedn k t -> closedn k (remove_match_on_box t).
  Proof using Type.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - move/andP: H => [] clt cll. unfold isprop_ind.
      destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      rewrite IHt //.
      depelim X. cbn in *.
      rewrite andb_true_r in cll.
      specialize (i _ cll).
      eapply closed_substl. solve_all. eapply All_repeat => //.
      now rewrite repeat_length.
      rtoProp; solve_all. depelim cll. solve_all.
      depelim cll. depelim cll. solve_all.
      depelim cll. depelim cll. solve_all.
      rtoProp; solve_all. solve_all.
      rtoProp; solve_all. solve_all.
    - destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|]; cbn; auto.
    - solve_all_k 6.
  Qed.

  Lemma subst_csubst_comm l t k b :
    forallb (closedn 0) l -> closed t ->
    subst l 0 (csubst t (#|l| + k) b) =
    csubst t k (subst l 0 b).
  Proof using Type.
    intros hl cl.
    rewrite !closed_subst //.
    rewrite distr_subst. f_equal.
    symmetry. solve_all.
    rewrite subst_closed //.
    eapply closed_upwards; tea. lia.
  Qed.

  Lemma substl_subst s t :
    forallb (closedn 0) s ->
    substl s t = subst s 0 t.
  Proof using Type.
    induction s in t |- *; cbn; auto.
    intros _. now rewrite subst_empty.
    move/andP=> []cla cls.
    rewrite (subst_app_decomp [_]).
    cbn. rewrite lift_closed //.
    rewrite closed_subst //. now eapply IHs.
  Qed.

  Lemma substl_csubst_comm l t k b :
    forallb (closedn 0) l -> closed t ->
    substl l (csubst t (#|l| + k) b) =
    csubst t k (substl l b).
  Proof using Type.
    intros hl cl.
    rewrite substl_subst //.
    rewrite substl_subst //.
    apply subst_csubst_comm => //.
  Qed.

  Lemma remove_match_on_box_csubst a k b :
    closed a ->
    remove_match_on_box (ECSubst.csubst a k b) = ECSubst.csubst (remove_match_on_box a) k (remove_match_on_box b).
  Proof using Type.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros cl; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def,isprop_ind in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n)%nat; auto.
    - destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      all:unfold on_snd; cbn.
      * f_equal; auto.
      * depelim X. simpl in *.
        rewrite e //.
        assert (#|br| = #|repeat tBox #|br| |). now rewrite repeat_length.
        rewrite {2}H.
        rewrite substl_csubst_comm //.
        solve_all. eapply All_repeat => //.
        now eapply closed_remove_match_on_box.
      * depelim X. depelim X.
        f_equal; eauto.
        unfold on_snd; cbn. f_equal; eauto.
        f_equal; eauto.
        f_equal; eauto. f_equal; eauto.
        rewrite map_map_compose; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
    - destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|]=> //;
      now rewrite IHb.
  Qed.

  Lemma remove_match_on_box_substl s t :
    forallb (closedn 0) s ->
    remove_match_on_box (substl s t) = substl (map remove_match_on_box s) (remove_match_on_box t).
  Proof using Type.
    induction s in t |- *; simpl; auto.
    move/andP => [] cla cls.
    rewrite IHs //. f_equal.
    now rewrite remove_match_on_box_csubst.
  Qed.

  Lemma remove_match_on_box_iota_red pars args br :
    forallb (closedn 0) args ->
    remove_match_on_box (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map remove_match_on_box args) (on_snd remove_match_on_box br).
  Proof using Type.
    intros cl.
    unfold EGlobalEnv.iota_red.
    rewrite remove_match_on_box_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma remove_match_on_box_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def remove_match_on_box) mfix) = map remove_match_on_box (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma remove_match_on_box_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def remove_match_on_box) mfix) = map remove_match_on_box (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma remove_match_on_box_cunfold_fix mfix idx n f :
    forallb (closedn 0) (EGlobalEnv.fix_subst mfix) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def remove_match_on_box) mfix) idx = Some (n, remove_match_on_box f).
  Proof using Type.
    intros hfix.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite remove_match_on_box_substl // remove_match_on_box_fix_subst.
    discriminate.
  Qed.

  Lemma remove_match_on_box_cunfold_cofix mfix idx n f :
    forallb (closedn 0) (EGlobalEnv.cofix_subst mfix) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def remove_match_on_box) mfix) idx = Some (n, remove_match_on_box f).
  Proof using Type.
    intros hcofix.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite remove_match_on_box_substl // remove_match_on_box_cofix_subst.
    discriminate.
  Qed.

  Lemma remove_match_on_box_nth {n l d} :
    remove_match_on_box (nth n l d) = nth n (map remove_match_on_box l) (remove_match_on_box d).
  Proof using Type.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End remove_match_on_box.

Lemma is_box_inv b : is_box b -> ∑ args, b = mkApps tBox args.
Proof.
  unfold is_box, EAstUtils.head.
  destruct decompose_app eqn:da.
  simpl. destruct t => //.
  eapply decompose_app_inv in da. subst.
  eexists; eauto.
Qed.

Lemma eval_is_box {wfl:WcbvFlags} Σ t u : Σ ⊢ t ⇓ u -> is_box t -> u = EAst.tBox.
Proof.
  intros ev; induction ev => //.
  - rewrite is_box_tApp.
    intros isb. intuition congruence.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?. subst => //.
  - rewrite is_box_tApp. move/IHev1 => ?. subst. solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?. subst. cbn in i.
    destruct EWcbvEval.with_guarded_fix => //.
  - destruct t => //.
Qed.

Lemma isType_tSort {cf:checker_flags} {Σ : global_env_ext} {Γ s A} {wfΣ : wf Σ} : Σ ;;; Γ |- tSort s : A -> isType Σ Γ (tSort s).
Proof.
  intros HT.
  eapply inversion_Sort in HT as [l' [wfΓ Hs]]; auto.
  eapply has_sort_isType. econstructor; eauto.
Qed.

Lemma isType_it_mkProd {cf:checker_flags} {Σ : global_env_ext} {Γ na dom codom A} {wfΣ : wf Σ} :
  Σ ;;; Γ |- tProd na dom codom : A ->
  isType Σ Γ (tProd na dom codom).
Proof.
  intros HT.
  eapply inversion_Prod in HT as (? & ? & ? & ? & ?); auto.
  eapply has_sort_isType. econstructor; eauto.
Qed.

Definition remove_match_on_box_constant_decl Σ cb :=
  {| cst_body := option_map (remove_match_on_box Σ) cb.(cst_body) |}.

Definition remove_match_on_box_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (remove_match_on_box_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl idecl
  end.

Definition remove_match_on_box_env Σ :=
  map (on_snd (remove_match_on_box_decl Σ)) Σ.(GlobalContextMap.global_decls).

Import EnvMap.

Program Fixpoint remove_match_on_box_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
    on_snd (remove_match_on_box_decl Σg) hd :: remove_match_on_box_env' tl (fresh_globals_cons_inv HΣ)
  end.

Import EGlobalEnv EExtends.

(* Lemma extends_is_propositional {Σ Σ'} :
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind,
  match inductive_isprop_and_pars Σ ind with
  | Some b => inductive_isprop_and_pars Σ' ind = Some b
  | None => inductive_isprop_and_pars Σ' ind = None
  end.
Proof.
  intros wf ex ind.
  rewrite /inductive_isprop_and_pars.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).

Qed. *)

Lemma extends_inductive_isprop_and_pars {efl : EEnvFlags} {Σ Σ' ind} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_inductive Σ ind) ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars Σ' ind.
Proof.
  intros ext wf; cbn.
  unfold inductive_isprop_and_pars. cbn.
  destruct lookup_env as [[]|] eqn:hl => //.
  rewrite (extends_lookup wf ext hl).
  destruct nth_error => //.
Qed.

Lemma wellformed_remove_match_on_box_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  forall n, EWellformed.wellformed Σ n t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  remove_match_on_box Σ t = remove_match_on_box Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive
    lookup_projection
    GlobalContextMap.inductive_isprop_and_pars]; intros => //.
  all:unfold wf_fix_gen, isprop_ind in *; rtoProp; intuition auto.
  all:try now f_equal; eauto; solve_all.
  - destruct cstr_as_blocks; rtoProp; eauto. f_equal. solve_all. destruct args; inv H2. reflexivity.
  - rewrite !GlobalContextMap.inductive_isprop_and_pars_spec.
    assert (map (on_snd (remove_match_on_box Σ)) l = map (on_snd (remove_match_on_box Σ')) l) as -> by solve_all.
    assert (iss : isSome (lookup_inductive Σ p.1)).
    { move: H2; rewrite /wf_brs; destruct lookup_inductive => //. }
    rewrite (extends_inductive_isprop_and_pars H0 H1 iss).
    destruct inductive_isprop_and_pars as [[[]]|].
    destruct map => //. f_equal; eauto.
    destruct l0 => //. destruct p0 => //. f_equal; eauto.
    all:f_equal; eauto; solve_all.
  - rewrite !GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (extends_inductive_isprop_and_pars H0 H1).
    destruct (lookup_projection) as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => //.
    eapply lookup_projection_lookup_constructor in hl.
    eapply lookup_constructor_lookup_inductive in hl. now rewrite hl.
    destruct inductive_isprop_and_pars as [[[]]|] => //.
    all:f_equal; eauto.
Qed.

Lemma wellformed_remove_match_on_box_decl_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_global_decl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  remove_match_on_box_decl Σ t = remove_match_on_box_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold remove_match_on_box_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_remove_match_on_box_extends.
Qed.

Lemma lookup_env_remove_match_on_box_env_Some {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn d :
  wf_glob Σ ->
  GlobalContextMap.lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t,
    [× extends_prefix Σ' Σ, wf_global_decl Σ' d &
      lookup_env (remove_match_on_box_env Σ) kn = Some (remove_match_on_box_decl Σ' d)].
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  induction Σ in map, repr, wf |- *; simpl; auto => //.
  intros wfg.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-].
    exists (GlobalContextMap.make Σ (fresh_globals_cons_inv wf)). split.
    now eexists [_].
    cbn. now depelim wfg.
    f_equal. symmetry. eapply wellformed_remove_match_on_box_decl_extends. cbn. now depelim wfg.
    eapply extends_prefix_extends.
    cbn. now exists [a]. now cbn. now cbn.
  - intros _.
    set (Σ' := GlobalContextMap.make Σ (fresh_globals_cons_inv wf)).
    specialize (IHΣ (GlobalContextMap.map Σ') (GlobalContextMap.repr Σ') (GlobalContextMap.wf Σ')).
    cbn in IHΣ. forward IHΣ. now depelim wfg.
    intros hl. specialize (IHΣ hl) as [Σ'' [ext wfgd hl']].
    exists Σ''. split => //.
    * destruct ext as [? ->].
      now exists (a :: x).
    * rewrite -hl'. f_equal.
      clear -wfg.
      eapply map_ext_in => kn hin. unfold on_snd. f_equal.
      symmetry. eapply wellformed_remove_match_on_box_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      cbn. eapply extends_prefix_extends => //. now exists [a].
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_env_remove_match_on_box_env_None {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  GlobalContextMap.lookup_env Σ kn = None ->
  lookup_env (remove_match_on_box_env Σ) kn = None.
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_remove_match_on_box {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  wf_glob Σ ->
  lookup_env (remove_match_on_box_env Σ) kn = option_map (remove_match_on_box_decl Σ) (lookup_env Σ kn).
Proof.
  intros wf.
  rewrite -GlobalContextMap.lookup_env_spec.
  destruct (GlobalContextMap.lookup_env Σ kn) eqn:hl.
  - eapply lookup_env_remove_match_on_box_env_Some in hl as [Σ' [ext wf' hl']] => /=.
    rewrite hl'. f_equal.
    eapply wellformed_remove_match_on_box_decl_extends; eauto.
    now eapply extends_prefix_extends. auto.

  - cbn. now eapply lookup_env_remove_match_on_box_env_None in hl.
Qed.

Lemma is_propositional_remove_match_on_box {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (remove_match_on_box_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_remove_match_on_box (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma is_propositional_cstr_remove_match_on_box {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind c :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (remove_match_on_box_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_remove_match_on_box (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma lookup_inductive_pars_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  EGlobalEnv.lookup_inductive_pars Σ ind = EGlobalEnv.lookup_inductive_pars (remove_match_on_box_env Σ) ind.
Proof.
  rewrite /lookup_inductive_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_remove_match_on_box ind wf).
  rewrite /GlobalContextMap.lookup_inductive /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma closed_iota_red pars c args brs br :
  forallb (closedn 0) args ->
  nth_error brs c = Some br ->
  #|skipn pars args| = #|br.1| ->
  closedn #|br.1| br.2 ->
  closed (iota_red pars args br).
Proof.
  intros clargs hnth hskip clbr.
  rewrite /iota_red.
  eapply ECSubst.closed_substl => //.
  now rewrite forallb_rev forallb_skipn.
  now rewrite List.length_rev hskip Nat.add_0_r.
Qed.

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma lookup_constructor_remove_match_on_box {efl : EEnvFlags} {Σ : GlobalContextMap.t} {ind c} :
  wf_glob Σ ->
  lookup_constructor Σ ind c = lookup_constructor (remove_match_on_box_env Σ) ind c.
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_remove_match_on_box // /=. destruct lookup_env => // /=.
  destruct g => //.
Qed.

Lemma constructor_isprop_pars_decl_inductive {Σ ind c} {prop pars cdecl} :
  constructor_isprop_pars_decl Σ ind c = Some (prop, pars, cdecl)  ->
  inductive_isprop_and_pars Σ ind = Some (prop, pars).
Proof.
  rewrite /constructor_isprop_pars_decl /inductive_isprop_and_pars /lookup_constructor.
  destruct lookup_inductive as [[mdecl idecl]|]=> /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma remove_match_on_box_correct {efl : EEnvFlags} {fl}{wcon : with_constructor_as_block = false} {Σ : GlobalContextMap.t} t v :
  wf_glob Σ ->
  closed_env Σ ->
  @EWcbvEval.eval fl Σ t v ->
  closed t ->
  @EWcbvEval.eval (disable_prop_cases fl) (remove_match_on_box_env Σ) (remove_match_on_box Σ t) (remove_match_on_box Σ v).
Proof.
  intros wfΣ clΣ ev.
  induction ev; simpl in *.

  - move/andP => [] cla clt. econstructor; eauto.
  - move/andP => [] clf cla.
    eapply eval_closed in ev2; tea.
    eapply eval_closed in ev1; tea.
    econstructor; eauto.
    rewrite remove_match_on_box_csubst // in IHev3.
    apply IHev3. eapply closed_csubst => //.

  - move/andP => [] clb0 clb1. rewrite remove_match_on_box_csubst in IHev2.
    now eapply eval_closed in ev1.
    econstructor; eauto. eapply IHev2, closed_csubst => //.
    now eapply eval_closed in ev1.

  - move/andP => [] cld clbrs. rewrite remove_match_on_box_mkApps in IHev1.
    have := (eval_closed _ clΣ _ _ cld ev1); rewrite closedn_mkApps => /andP[] _ clargs.
    rewrite remove_match_on_box_iota_red in IHev2.
    eapply eval_closed in ev1 => //.
    unfold isprop_ind.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (constructor_isprop_pars_decl_inductive e1).
    eapply eval_iota; eauto.
    now rewrite -is_propositional_cstr_remove_match_on_box.
    rewrite nth_error_map e2 //. now len. cbn.
    rewrite -e4. rewrite !length_skipn length_map //.
    eapply IHev2.
    eapply closed_iota_red => //; tea.
    eapply nth_error_forallb in clbrs; tea. cbn in clbrs.
    now rewrite Nat.add_0_r in clbrs.

  - congruence.

  - move/andP => [] cld clbrs. unfold isprop_ind.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite e0 e1 /=.
    subst brs. cbn in clbrs. rewrite Nat.add_0_r andb_true_r in clbrs.
    rewrite remove_match_on_box_substl in IHev2.
    eapply All_forallb, All_repeat => //.
    rewrite map_remove_match_on_box_repeat_box in IHev2.
    apply IHev2.
    eapply closed_substl.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length Nat.add_0_r.

  - move/andP => [] clf cla. rewrite remove_match_on_box_mkApps in IHev1.
    simpl in *.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply EWcbvEval.eval_fix; eauto.
    rewrite length_map.
    eapply remove_match_on_box_cunfold_fix; tea.
    eapply closed_fix_subst. tea.
    rewrite remove_match_on_box_mkApps in IHev3. apply IHev3.
    rewrite closedn_mkApps clargs.
    eapply eval_closed in ev2; tas. rewrite ev2 /= !andb_true_r.
    eapply closed_cunfold_fix; tea.

  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply eval_closed in ev2; tas.
    rewrite remove_match_on_box_mkApps in IHev1 |- *.
    simpl in *. eapply EWcbvEval.eval_fix_value. auto. auto. auto.
    eapply remove_match_on_box_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    now rewrite length_map.

  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    eapply eval_closed in ev2; tas.
    simpl in *. eapply EWcbvEval.eval_fix'. auto. auto.
    eapply remove_match_on_box_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    eapply IHev2; tea. eapply IHev3.
    apply/andP; split => //.
    eapply closed_cunfold_fix; tea.

  - move/andP => [] cd clbrs. specialize (IHev1 cd).
    rewrite closedn_mkApps in IHev2.
    move: (eval_closed _ clΣ _ _ cd ev1).
    rewrite closedn_mkApps.
    move/andP => [] clfix clargs.
    forward IHev2.
    { rewrite clargs clbrs !andb_true_r.
      eapply closed_cunfold_cofix; tea. }
    rewrite -> remove_match_on_box_mkApps in IHev1, IHev2. simpl. unfold isprop_ind in *.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec in IHev2 |- *.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp => //.
    destruct brs as [|[a b] []]; simpl in *; auto.
    simpl in IHev1.
    eapply EWcbvEval.eval_cofix_case. tea.
    apply remove_match_on_box_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    apply IHev2.
    eapply EWcbvEval.eval_cofix_case; tea.
    apply remove_match_on_box_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    simpl in *.
    eapply EWcbvEval.eval_cofix_case; tea.
    apply remove_match_on_box_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    eapply EWcbvEval.eval_cofix_case; tea.
    apply remove_match_on_box_cunfold_cofix; tea. eapply closed_cofix_subst; tea.

  - intros cd. specialize (IHev1 cd).
    move: (eval_closed _ clΣ _ _ cd ev1).
    rewrite closedn_mkApps; move/andP => [] clfix clargs. forward IHev2.
    { rewrite closedn_mkApps clargs andb_true_r. eapply closed_cunfold_cofix; tea. }
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec in IHev2 |- *.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp; auto.
    rewrite -> remove_match_on_box_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply remove_match_on_box_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> remove_match_on_box_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply remove_match_on_box_cunfold_cofix; tea. eapply closed_cofix_subst; tea.

  - rewrite /declared_constant in isdecl.
    move: (lookup_env_remove_match_on_box c wfΣ).
    rewrite isdecl /= //.
    intros hl.
    econstructor; tea. cbn. rewrite e //.
    apply IHev.
    eapply lookup_env_closed in clΣ; tea.
    move: clΣ. rewrite /closed_decl e //.

  - move=> cld.
    eapply eval_closed in ev1; tea.
    move: ev1; rewrite closedn_mkApps /= => clargs.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (constructor_isprop_pars_decl_inductive e1).
    rewrite remove_match_on_box_mkApps in IHev1.
    specialize (IHev1 cld).
    eapply EWcbvEval.eval_proj; tea.
    now rewrite -is_propositional_cstr_remove_match_on_box.
    now len. rewrite nth_error_map e3 //.
    eapply IHev2.
    eapply nth_error_forallb in e3; tea.

  - congruence.

  - rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    now rewrite e0.

  - move/andP=> [] clf cla.
    rewrite remove_match_on_box_mkApps.
    eapply eval_construct; tea.
    rewrite -lookup_constructor_remove_match_on_box //. exact e0.
    rewrite remove_match_on_box_mkApps in IHev1. now eapply IHev1.
    now len.
    now eapply IHev2.

  - congruence.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply EWcbvEval.eval_app_cong; eauto.
    eapply EWcbvEval.eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * depelim a0. destruct t => //; rewrite ?remove_match_on_box_mkApps /=.
      cbn in i. now rewrite !orb_false_r orb_true_r in i.
    * destruct with_guarded_fix.
      + move: i.
        rewrite !negb_or.
        rewrite remove_match_on_box_mkApps !isFixApp_mkApps !isConstructApp_mkApps !isPrimApp_mkApps !isLazyApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        rewrite !andb_true_r.
        rtoProp; intuition auto.
        destruct v => /= //.
        destruct v => /= //.
        destruct v => /= //.
        destruct v => /= //.
      + move: i.
        rewrite !negb_or.
        rewrite remove_match_on_box_mkApps !isConstructApp_mkApps !isPrimApp_mkApps !isLazyApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        destruct v => /= //.
  - depelim X; repeat constructor.
    eapply All2_over_undep in a. eapply All2_All2_Set. eapply All2_Set_All2 in ev. subst a0 a'; cbn in *.
    rewrite /test_array_model /= in H. rtoProp; intuition auto; solve_all. eapply e.
    cbn in H. rewrite /test_array_model /= in H. now move/andP: H => [].
  - intros. econstructor; eauto. eapply IHev2. eapply eval_closed in ev1; tea.
  - destruct t => //.
    all:constructor; eauto. cbn [atom remove_match_on_box] in i |- *.
    rewrite -lookup_constructor_remove_match_on_box //. destruct args => //.
Qed.

From MetaRocq.Erasure Require Import EEtaExpanded.

Lemma isLambda_remove_match_on_box Σ t : isLambda t -> isLambda (remove_match_on_box Σ t).
Proof. destruct t => //. Qed.
Lemma isBox_remove_match_on_box Σ t : isBox t -> isBox (remove_match_on_box Σ t).
Proof. destruct t => //. Qed.

Lemma remove_match_on_box_expanded {Σ : GlobalContextMap.t} t : expanded Σ t -> expanded Σ (remove_match_on_box Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?remove_match_on_box_mkApps.
  - eapply expanded_mkApps_expanded => //. solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars]. unfold isprop_ind.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
    2-3:constructor; eauto; solve_all.
    destruct branches eqn:heq.
    constructor; eauto; solve_all. cbn.
    destruct l => /=.
    eapply isEtaExp_expanded.
    eapply isEtaExp_substl. eapply forallb_repeat => //.
    destruct branches as [|[]]; cbn in heq; noconf heq.
    cbn -[isEtaExp] in *. depelim H1. cbn in H1.
    now eapply expanded_isEtaExp.
    constructor; eauto; solve_all.
    depelim H1. depelim H1. do 2 (constructor; intuition auto).
    solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars].
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
    constructor. all:constructor; auto.
  - cbn. eapply expanded_tFix. solve_all.
    rewrite isLambda_remove_match_on_box //.
  - eapply expanded_tConstruct_app; tea.
    now len. solve_all.
Qed.

Lemma remove_match_on_box_expanded_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded Σ t -> expanded (remove_match_on_box_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rewrite lookup_env_remove_match_on_box // /= H //. 1-2:eauto. auto. solve_all.
Qed.

Lemma remove_match_on_box_expanded_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl Σ (remove_match_on_box_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply remove_match_on_box_expanded.
Qed.

Lemma remove_match_on_box_expanded_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded_decl Σ t -> expanded_decl (remove_match_on_box_env Σ) t.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply remove_match_on_box_expanded_irrel.
Qed.

Lemma remove_match_on_box_wellformed {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t -> EWellformed.wellformed Σ n (remove_match_on_box Σ t).
Proof.
  intros wfΣ hbox hrel.
  induction t in n |- * using EInduction.term_forall_list_ind => //.
  all:try solve [cbn; rtoProp; intuition auto; solve_all].
  - cbn -[lookup_constructor]. intros. destruct cstr_as_blocks; rtoProp; repeat split; eauto. 2:solve_all.
    2: now destruct args; inv H0. len.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars lookup_inductive]. move/and3P => [] hasc /andP[]hs ht hbrs.
    unfold isprop_ind.
    destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
    destruct l as [|[br n'] [|l']] eqn:eql; simpl.
    all:rewrite ?hasc ?hs /= ?andb_true_r.
    rewrite IHt //.
    depelim X. cbn in hbrs.
    rewrite andb_true_r in hbrs.
    specialize (i _ hbrs).
    eapply wellformed_substl => //. solve_all. eapply All_repeat => //.
    now rewrite repeat_length.
    cbn in hbrs; rtoProp; solve_all. depelim X; depelim X. solve_all.
    do 2 depelim X. solve_all.
    do 2 depelim X. solve_all.
    rtoProp; solve_all. solve_all.
    rtoProp; solve_all. solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars lookup_inductive]. move/andP => [] /andP[]hasc hs ht.
    destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
    all:rewrite hasc hs /=; eauto.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all. now eapply isLambda_remove_match_on_box.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all.
  - cbn. rtoProp; intuition auto; solve_all_k 6.
Qed.

Import EWellformed.

Lemma remove_match_on_box_wellformed_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_glob Σ ->
  forall n, wellformed Σ n t -> wellformed (remove_match_on_box_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_remove_match_on_box //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct (cst_body c) => //.
  - rewrite lookup_env_remove_match_on_box //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    repeat split; eauto. destruct cstr_as_blocks; rtoProp; repeat split; len; eauto. 1: solve_all.
  - rewrite /wf_brs; cbn. rewrite lookup_env_remove_match_on_box //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_remove_match_on_box //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    rewrite andb_false_r => //.
    destruct nth_error => /= //.
    all:intros; rtoProp; intuition auto; solve_all.
Qed.

From MetaRocq.Erasure Require Import EGenericGlobalMap.

#[local]
Instance GT : GenTransform := { gen_transform := remove_match_on_box; gen_transform_inductive_decl := id }.
#[local]
Instance GTID : GenTransformId GT.
Proof.
  red. reflexivity.
Qed.
#[local]
Instance GTExt efl : GenTransformExtends efl efl GT.
Proof.
  intros Σ t n wfΣ Σ' ext wf wf'.
  unfold gen_transform, GT.
  eapply wellformed_remove_match_on_box_extends; tea.
Qed.
#[local]
Instance GTWf efl : GenTransformWf efl efl GT.
Proof.
  refine {| gen_transform_pre := fun _ _ => has_tBox /\ has_tRel |}; auto.
  intros Σ n t [] wfΣ wft.
  eapply remove_match_on_box_wellformed_irrel => //.
  now eapply remove_match_on_box_wellformed.
Defined.

Lemma remove_match_on_box_env_extends' {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  List.map (on_snd (remove_match_on_box_decl Σ)) Σ.(GlobalContextMap.global_decls) =
  List.map (on_snd (remove_match_on_box_decl Σ')) Σ.(GlobalContextMap.global_decls).
Proof.
  intros ext wf.
  eapply (gen_transform_env_extends' (gt := GTExt efl)) => //.
Qed.

Lemma remove_match_on_box_extends_env {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (remove_match_on_box_env Σ) (remove_match_on_box_env Σ').
Proof.
  intros ext wf.
  now apply (gen_transform_extends (gt := GTExt efl) ext).
Qed.

Lemma remove_match_on_box_env_eq {efl : EEnvFlags} (Σ : GlobalContextMap.t) :
  wf_glob Σ ->
  remove_match_on_box_env Σ = remove_match_on_box_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  eapply (gen_transform_env_eq (gt := GTExt efl)) => //.
Qed.

Lemma remove_match_on_box_env_expanded {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (remove_match_on_box_env Σ).
Proof.
  unfold expanded_global_env; move=> wfg.
  rewrite remove_match_on_box_env_eq //.
  destruct Σ as [Σ map repr wf]. cbn in *.
  clear map repr.
  induction 1; cbn; constructor; auto.
  cbn in IHexpanded_global_declarations.
  unshelve eapply IHexpanded_global_declarations. now depelim wfg. cbn.
  set (Σ' := GlobalContextMap.make _ _).
  rewrite -(remove_match_on_box_env_eq Σ'). cbn. now depelim wfg.
  eapply (remove_match_on_box_expanded_decl_irrel (Σ := Σ')). now depelim wfg.
  now unshelve eapply (remove_match_on_box_expanded_decl (Σ:=Σ')).
Qed.


Lemma remove_match_on_box_wellformed_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} d :
  wf_glob Σ ->
  wf_global_decl Σ d -> wf_global_decl (remove_match_on_box_env Σ) d.
Proof.
  intros wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply remove_match_on_box_wellformed_irrel.
Qed.

Lemma remove_match_on_box_decl_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel -> wf_glob Σ ->
  forall d, wf_global_decl Σ d -> wf_global_decl (remove_match_on_box_env Σ) (remove_match_on_box_decl Σ d).
Proof.
  intros hasb hasr wf d.
  intros hd.
  eapply remove_match_on_box_wellformed_decl_irrel; tea.
  move: hd.
  destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply remove_match_on_box_wellformed => //.
Qed.

Lemma fresh_global_remove_match_on_box_env {Σ : GlobalContextMap.t} kn :
  fresh_global kn Σ ->
  fresh_global kn (remove_match_on_box_env Σ).
Proof.
  destruct Σ as [Σ map repr wf]; cbn in *.
  induction 1; cbn; constructor; auto.
  now eapply Forall_map; cbn.
Qed.


Lemma Pre_glob efl Σ wf :
  has_tBox -> has_tRel ->
  Pre_glob (GTWF:=GTWf efl) Σ wf.
Proof.
  intros hasb hasr. induction Σ => //. destruct a as [kn d]; cbn.
  split => //. destruct d as [[[|]]|] => //=.
Qed.

Lemma remove_match_on_box_env_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel ->
  wf_glob Σ -> wf_glob (remove_match_on_box_env Σ).
Proof.
  intros hasb hasrel wfg.
  eapply (gen_transform_env_wf (gt := GTExt efl)) => //.
  now apply Pre_glob.
Qed.

Definition remove_match_on_box_program (p : eprogram_env) :=
  (remove_match_on_box_env p.1, remove_match_on_box p.1 p.2).

Definition remove_match_on_box_program_wf {efl} (p : eprogram_env) {hastbox : has_tBox} {hastrel : has_tRel} :
  wf_eprogram_env efl p -> wf_eprogram efl (remove_match_on_box_program p).
Proof.
  intros []; split.
  now eapply remove_match_on_box_env_wf.
  cbn. eapply remove_match_on_box_wellformed_irrel => //. now eapply remove_match_on_box_wellformed.
Qed.

Definition remove_match_on_box_program_expanded {efl} (p : eprogram_env) :
  wf_eprogram_env efl p ->
  expanded_eprogram_env_cstrs p -> expanded_eprogram_cstrs (remove_match_on_box_program p).
Proof.
  unfold expanded_eprogram_env_cstrs.
  move=> [wfe wft] /andP[] etae etat.
  apply/andP; split.
  cbn. eapply expanded_global_env_isEtaExp_env, remove_match_on_box_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  eapply expanded_isEtaExp.
  eapply remove_match_on_box_expanded_irrel => //.
  now apply remove_match_on_box_expanded, isEtaExp_expanded.
Qed.


Section ExpandedFix.
  Import EEtaExpandedFix.

  Lemma expanded_mkApps_expanded Σ Γ t l : expanded Σ Γ t -> All (expanded Σ Γ) l -> expanded Σ Γ (mkApps t l).
  Proof.
    move/expanded_isEtaExp => ht ha. apply isEtaExp_expanded.
    eapply isEtaExp_mkApps_intro; eauto; solve_all. now eapply expanded_isEtaExp.
  Qed.

  Lemma remove_match_on_box_expanded_fix {Σ : GlobalContextMap.t} t : expanded Σ [] t -> expanded Σ [] (remove_match_on_box Σ t).
  Proof.
    induction 1 using expanded_ind.
    all:try solve[constructor; eauto; solve_all].
    all:rewrite ?remove_match_on_box_mkApps.
    - cbn. eapply expanded_tRel_app; tea. now len. solve_all.
    - eapply expanded_mkApps_expanded; eauto; solve_all.
    - cbn -[GlobalContextMap.inductive_isprop_and_pars]. unfold isprop_ind.
      rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
      destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
      2-3:constructor; eauto; solve_all.
      destruct branches eqn:heq.
      constructor; eauto; solve_all. cbn.
      destruct l => /=.
      depelim H0. depelim H2. subst branches.
      eapply isEtaExp_expanded.
      eapply expanded_isEtaExp in H2.
      eapply isEtaExp_substl; tea. len. eapply forallb_repeat => //.
      destruct branches as [|[]]; cbn in heq; noconf heq.
      cbn -[isEtaExp] in *. depelim H1. cbn in H1.
      constructor; eauto; solve_all.
      depelim H0. depelim H0. depelim H2. do 2 (constructor; intuition auto).
      solve_all.
    - cbn -[GlobalContextMap.inductive_isprop_and_pars].
      rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
      destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
      constructor. all:constructor; auto.
    - cbn. eapply expanded_tFix. 4:{ rewrite nth_error_map H4 //. }
      all:eauto; solve_all.
      rewrite isLambda_remove_match_on_box //.
      rewrite !rev_map_spec in b *; rewrite map_map /= //.
    - eapply expanded_tConstruct_app; tea.
      now len. solve_all.
  Qed.

  Lemma remove_match_on_box_expanded_fix_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} Γ t : wf_glob Σ -> expanded Σ Γ t -> expanded (remove_match_on_box_env Σ) Γ t.
  Proof.
    intros wf; induction 1 using expanded_ind.
    all:try solve[constructor; eauto; solve_all].
    eapply expanded_tRel_app; tea.
    eapply expanded_tFix; eauto. solve_all.
    eapply expanded_tConstruct_app.
    destruct H as [[H ?] ?].
    split => //. split => //. red.
    red in H. rewrite lookup_env_remove_match_on_box // /= H //. 1-2:eauto. auto. solve_all.
  Qed.

  Lemma remove_match_on_box_expanded_fix_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl Σ (remove_match_on_box_decl Σ t).
  Proof.
    destruct t as [[[]]|] => /= //.
    unfold expanded_constant_decl => /=.
    apply remove_match_on_box_expanded_fix.
  Qed.

  Lemma remove_match_on_box_expanded_fix_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded_decl Σ t -> expanded_decl (remove_match_on_box_env Σ) t.
  Proof.
    destruct t as [[[]]|] => /= //.
    unfold expanded_constant_decl => /=.
    apply remove_match_on_box_expanded_fix_irrel.
  Qed.

  Lemma remove_match_on_box_env_expanded_fix {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
    wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (remove_match_on_box_env Σ).
  Proof.
    unfold expanded_global_env; move=> wfg.
    rewrite remove_match_on_box_env_eq //.
    destruct Σ as [Σ map repr wf]. cbn in *.
    clear map repr.
    induction 1; cbn; constructor; auto.
    cbn in IHexpanded_global_declarations.
    unshelve eapply IHexpanded_global_declarations. now depelim wfg. cbn.
    set (Σ' := GlobalContextMap.make _ _).
    rewrite -(remove_match_on_box_env_eq Σ'). cbn. now depelim wfg.
    eapply (remove_match_on_box_expanded_fix_decl_irrel (Σ := Σ')). now depelim wfg.
    now unshelve eapply (remove_match_on_box_expanded_fix_decl (Σ:=Σ')).
  Qed.

  Definition remove_match_on_box_program_expanded_fix {efl} (p : eprogram_env) :
    wf_eprogram_env efl p ->
    expanded_eprogram_env p -> expanded_eprogram (remove_match_on_box_program p).
  Proof.
    unfold expanded_eprogram_env.
    move=> [wfe wft] [etae etat]. split.
    cbn. eapply remove_match_on_box_env_expanded_fix => //.
    eapply remove_match_on_box_expanded_fix_irrel => //.
    now apply remove_match_on_box_expanded_fix.
  Qed.

End ExpandedFix.
