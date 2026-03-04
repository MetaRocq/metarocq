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
    EEtaExpanded
    ELiftSubst ECSubst ESpineView EGlobalEnv EInduction EWellformed EWcbvEval Extract Prelim
    EEnvMap EArities EProgram.

Import MRList (map_InP, map_InP_elim, map_InP_spec).

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

(** We assumes [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

Axiom trust_cofix : forall {A}, A.

#[global]
Hint Constructors eval : core.

Section trans.
  Context (Σ : GlobalContextMap.t).

  Fixpoint trans (t : term) : term :=
    match t with
    | tRel i => tRel i
    | tEvar ev args => tEvar ev (List.map trans args)
    | tLambda na M => tLambda na (trans M)
    | tApp u v => tApp (trans u) (trans v)
    | tLetIn na b b' => tLetIn na (trans b) (trans b')
    | tCase ind c brs =>
      let brs' := List.map (on_snd trans) brs in
      match GlobalContextMap.lookup_inductive_kind Σ (fst ind).(inductive_mind) with
      | Some CoFinite =>
        tCase ind (tForce (trans c)) brs'
      | _ => tCase ind (trans c) brs'
      end
    | tProj p c =>
      match GlobalContextMap.lookup_inductive_kind Σ p.(proj_ind).(inductive_mind) with
      | Some CoFinite => tProj p (tForce (trans c))
      | _ => tProj p (trans c)
      end
    | tFix mfix idx =>
      let mfix' := List.map (map_def trans) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := List.map (map_def trans) mfix in
      tFix mfix' idx
    | tBox => t
    | tVar _ => t
    | tConst _ => t
    | tConstruct ind i args =>
      match GlobalContextMap.lookup_inductive_kind Σ ind.(inductive_mind) with
      | Some CoFinite => tLazy (tConstruct ind i (map trans args))
      | _ => tConstruct ind i (map trans args)
      end
    | tPrim p => tPrim (map_prim trans p)
    | tLazy t => tLazy (trans t)
    | tForce t => tForce (trans t)
    end.

  (* cofix succ x := match x with Stream x xs => Stream (x + 1) (succ xs) ->

    fix succ x := match x () with Stream x xs => fun () => Stream (x + 1) (succ xs)

    cofix ones := Stream 1 ones ->
    fix ones := fun () => Stream 1 ones
  *)

  Lemma trans_mkApps f l : trans (mkApps f l) = mkApps (trans f) (map trans l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_repeat {A B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
  Proof using Type.
    now induction n; simpl; auto; rewrite IHn.
  Qed.

  Lemma map_trans_repeat_box n : map trans (repeat tBox n) = repeat tBox n.
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

  Lemma closed_trans t k : closedn k t -> closedn k (trans t).
  Proof using Type.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct GlobalContextMap.lookup_inductive_kind as [[]|] => /= //; solve_all.
    - move/andP: H => [] clt clargs.
      destruct GlobalContextMap.lookup_inductive_kind as [[]|] => /= //; rtoProp; solve_all; solve_all.
    - destruct GlobalContextMap.lookup_inductive_kind as [[]|] => /= //; rtoProp; solve_all; solve_all.
    - primProp. solve_all_k 6.
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

  Lemma trans_csubst a k b :
    closed a ->
    trans (ECSubst.csubst a k b) = ECSubst.csubst (trans a) k (trans b).
  Proof using Type.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros cl; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n)%nat; auto.
    - destruct GlobalContextMap.lookup_inductive_kind as [[]|] => /= //.
      1,3,4:f_equal; rewrite map_map_compose; solve_all.
      do 2 f_equal; solve_all.
    - destruct GlobalContextMap.lookup_inductive_kind as [[]|] => /= //.
      all:f_equal; eauto; try (rewrite /on_snd map_map_compose; solve_all).
      f_equal. eauto.
    - destruct GlobalContextMap.lookup_inductive_kind as [[]|] => /= //.
      all:f_equal; eauto; try (rewrite /on_snd map_map_compose; solve_all).
      f_equal; eauto.
  Qed.

  Lemma trans_substl s t :
    forallb (closedn 0) s ->
    trans (substl s t) = substl (map trans s) (trans t).
  Proof using Type.
    induction s in t |- *; simpl; auto.
    move/andP => [] cla cls.
    rewrite IHs //. f_equal.
    now rewrite trans_csubst.
  Qed.

  Lemma trans_iota_red pars args br :
    forallb (closedn 0) args ->
    trans (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map trans args) (on_snd trans br).
  Proof using Type.
    intros cl.
    unfold EGlobalEnv.iota_red.
    rewrite trans_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma trans_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def trans) mfix) = map trans (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma trans_cunfold_fix mfix idx n f :
    forallb (closedn 0) (EGlobalEnv.fix_subst mfix) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def trans) mfix) idx = Some (n, trans f).
  Proof using Type.
    intros hfix.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite trans_substl // trans_fix_subst.
    discriminate.
  Qed.

  (* Lemma trans_cunfold_cofix mfix idx n f :
    forallb (closedn 0) (EGlobalEnv.cofix_subst mfix) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    exists d, nth_error mfix idx = Some d /\
      cunfold_fix mfix idx = Some (n, substl (fix_subst mfix) (dbody d)).
  Proof using Type.
    intros hcofix.
    unfold cunfold_cofix, cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal. exists d. split => //.
    discriminate.
  Qed. *)

  Lemma trans_nth {n l d} :
    trans (nth n l d) = nth n (map trans l) (trans d).
  Proof using Type.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End trans.

Lemma is_box_inv b : is_box b -> ∑ args, b = mkApps tBox args.
Proof.
  unfold is_box, EAstUtils.head.
  destruct decompose_app eqn:da.
  simpl. destruct t => //.
  eapply decompose_app_inv in da. subst.
  eexists; eauto.
Qed.

Import EWcbvEval.

Notation "Σ ⊢ s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

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

Lemma isType_tSort {cf:checker_flags} {Σ : global_env_ext} {Γ l A} {wfΣ : wf Σ} :
  Σ ;;; Γ |- tSort (sType (Universe.make l)) : A -> isType Σ Γ (tSort (sType (Universe.make l))).
Proof.
  intros HT.
  eapply inversion_Sort in HT as [l' [wfΓ Hs]]; auto.
  eexists; econstructor; eauto. cbn. split; eauto. econstructor; eauto.
Qed.

Lemma isType_it_mkProd {cf:checker_flags} {Σ : global_env_ext} {Γ na dom codom A} {wfΣ : wf Σ} :
  Σ ;;; Γ |- tProd na dom codom : A ->
  isType Σ Γ (tProd na dom codom).
Proof.
  intros HT.
  eapply inversion_Prod in HT as (? & ? & ? & ? & ?); auto.
  eexists; cbn; econstructor; split; eauto. econstructor; eauto.
Qed.

Definition trans_constant_decl Σ cb :=
  {| cst_body := option_map (trans Σ) cb.(cst_body) |}.

Definition trans_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (trans_constant_decl Σ cb)
  | InductiveDecl idecl => d
  end.

Definition trans_env Σ :=
  map (on_snd (trans_decl Σ)) Σ.(GlobalContextMap.global_decls).

Import EnvMap.

Program Fixpoint trans_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
    on_snd (trans_decl Σg) hd :: trans_env' tl (fresh_globals_cons_inv HΣ)
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

Lemma extends_lookup_inductive_kind {efl : EEnvFlags} {Σ Σ' ind} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_minductive Σ ind) ->
  lookup_inductive_kind Σ ind = lookup_inductive_kind Σ' ind.
Proof.
  intros ext wf.
  unfold lookup_inductive_kind. cbn.
  destruct lookup_env as [[]|] eqn:hl => //.
  now rewrite (extends_lookup wf ext hl).
Qed.

Lemma wellformed_trans_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  forall n, EWellformed.wellformed Σ n t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  trans Σ t = trans Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive
    lookup_projection
    lookup_constructor
    GlobalContextMap.lookup_inductive_kind]; intros => //.
  all:unfold wf_fix_gen in *; rtoProp; intuition auto.
  all:try now f_equal; eauto; solve_all.
  - rewrite !GlobalContextMap.lookup_inductive_kind_spec.
    destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
    destruct cstr_as_blocks.
    { move/andP: H2 => [] hpars hargs.
      assert (map (trans Σ) args = map (trans Σ') args) as -> by solve_all.
      rewrite (extends_lookup_inductive_kind H0 H1) //.
      apply lookup_constructor_lookup_inductive in hl.
      unfold lookup_inductive in hl.
      destruct lookup_minductive => //. }
    { destruct args => // /=.
      rewrite (extends_lookup_inductive_kind H0 H1) //.
      apply lookup_constructor_lookup_inductive in hl.
      unfold lookup_inductive in hl.
      destruct lookup_minductive => //. }
  - rewrite !GlobalContextMap.lookup_inductive_kind_spec.
    move: H2; rewrite /wf_brs.
    destruct lookup_inductive as [[mdecl idecl]|] eqn:hl => //.
    assert (map (on_snd (trans Σ)) l = map (on_snd (trans Σ')) l) as -> by solve_all.
    rewrite (extends_lookup_inductive_kind H0 H1) //.
    unfold lookup_inductive in hl.
    destruct lookup_minductive => //.
    rewrite (IHt _ H4 _ H0 H1) //.
  - rewrite !GlobalContextMap.lookup_inductive_kind_spec.
    destruct (lookup_projection) as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => //.
    eapply lookup_projection_lookup_constructor in hl.
    eapply lookup_constructor_lookup_inductive in hl.
    rewrite (extends_lookup_inductive_kind H0 H1) //.
    unfold lookup_inductive in hl.
    destruct lookup_minductive => //.
    rewrite (IHt _ H2 _ H0 H1) //.
Qed.

Lemma wellformed_trans_decl_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_global_decl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  trans_decl Σ t = trans_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold trans_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_trans_extends.
Qed.

Lemma lookup_env_trans_env_Some {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn d :
  wf_glob Σ ->
  GlobalContextMap.lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t,
    [× extends_prefix Σ' Σ, wf_global_decl Σ' d &
      lookup_env (trans_env Σ) kn = Some (trans_decl Σ' d)].
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  induction Σ in map, repr, wf |- *; simpl; auto => //.
  intros wfg.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-].
    exists (GlobalContextMap.make Σ (fresh_globals_cons_inv wf)). split.
    cbn. now exists [a]. now depelim wfg.
    depelim wfg; eauto.
    f_equal. symmetry. eapply wellformed_trans_decl_extends. cbn; auto. cbn.
    now eapply extends_fresh. cbn. now constructor.
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
      symmetry. eapply wellformed_trans_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      cbn. destruct a. eapply extends_fresh. now depelim wfg.
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_env_trans_env_None {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  GlobalContextMap.lookup_env Σ kn = None ->
  lookup_env (trans_env Σ) kn = None.
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_trans {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  wf_glob Σ ->
  lookup_env (trans_env Σ) kn = option_map (trans_decl Σ) (lookup_env Σ kn).
Proof.
  intros wf.
  rewrite -GlobalContextMap.lookup_env_spec.
  destruct (GlobalContextMap.lookup_env Σ kn) eqn:hl.
  - eapply lookup_env_trans_env_Some in hl as [Σ' [ext wf' hl']] => /= //.
    rewrite hl'. f_equal.
    eapply wellformed_trans_decl_extends; eauto.
    now eapply extends_prefix_extends.
  - cbn. now eapply lookup_env_trans_env_None in hl.
Qed.

Lemma is_propositional_trans {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (trans_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_trans (inductive_mind ind) wf) //.
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma is_propositional_cstr_trans {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind c :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (trans_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_trans (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
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

Lemma lookup_constructor_trans {efl : EEnvFlags} {Σ : GlobalContextMap.t} {ind c} :
  wf_glob Σ ->
  lookup_constructor Σ ind c = lookup_constructor (trans_env Σ) ind c.
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_trans // /=. destruct lookup_env => // /=.
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

Lemma value_constructor_as_block {wfl : WcbvFlags} {Σ ind c args} : value Σ (tConstruct ind c args) ->
  All (value Σ) args.
Proof.
  intros h; depelim h.
  - depelim a. cbn in i. destruct args => //.
  - eauto.
  - depelim v; solve_discr.
Qed.

Lemma constructor_isprop_pars_decl_constructor {Σ ind c prop npars cdecl}  :
  constructor_isprop_pars_decl Σ ind c = Some (prop, npars, cdecl) ->
  ∑ mdecl idecl, lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) /\ npars = ind_npars mdecl.
Proof.
  rewrite /constructor_isprop_pars_decl.
  destruct lookup_constructor as [[[mdecl idecl] cdecl']|] eqn:hl => //=.
  intros [= <- <- <-].
  exists mdecl, idecl; split => //.
Qed.

Lemma value_trans {efl : EEnvFlags} {fl : WcbvFlags} {hasc : cstr_as_blocks = true} {wcon : with_constructor_as_block = true} {Σ : GlobalContextMap.t} {c} :
  has_tApp -> wf_glob Σ ->
  wellformed Σ 0 c ->
  value Σ c ->
  value (trans_env Σ) (trans Σ c).
Proof.
  intros hasapp wfg wf h.
  revert c h wf. apply: EWcbvEval.value_values_ind.
  - intros t; destruct t => //; cbn -[lookup_constructor GlobalContextMap.lookup_inductive_kind].
    all:try solve [intros; repeat constructor => //].
    destruct args => //.
    move=> /andP[] wc. now rewrite wcon in wc.
  - intros p pv IH wf. cbn. constructor. constructor 2.
    cbn in wf. move/andP: wf => [hasp tp].
    primProp. depelim tp; depelim pv; depelim IH; constructor; cbn in *; rtoProp; intuition auto; solve_all.
  - intros ind c mdecl idecl cdecl args wc hl harglen hargs ihargs.
    simpl. rewrite hasc. move/andP => [] /andP[] hascstr _ /andP[] hpargs wfargs.
    cbn -[GlobalContextMap.lookup_inductive_kind].
    destruct GlobalContextMap.lookup_inductive_kind as [[]|] eqn:hl' => //.
    1,3,4:eapply value_constructor; tea; [erewrite <-lookup_constructor_trans; tea|now len|solve_all].
    apply trust_cofix.
    (* now do 2 constructor. *)
  - intros f args vh harglen hargs ihargs.
    rewrite wellformed_mkApps // => /andP[] wff wfargs.
    rewrite trans_mkApps.
    depelim vh. congruence.
    cbn.
    simpl in wff; move/andP: wff => [] hascof /andP[] /Nat.ltb_lt wfidx wffix.
    apply nth_error_Some in wfidx.
    destruct nth_error eqn:heq => //.
    all: apply trust_cofix.
Qed.

Ltac destruct_times :=
  match goal with
  | [ H : pair _ _ |- _ ] => destruct H
  | [ H : MRProd.and3 _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and4 _ _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and5 _ _ _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and6 _ _ _ _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and7 _ _ _ _ _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and8 _ _ _ _ _ _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and9 _ _ _ _ _ _ _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and10 _ _ _ _ _ _ _ _ _ _ |- _ ] => destruct H
  end.

From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksInd.
Lemma trans_correct {efl : EEnvFlags} {fl} {wcon : with_constructor_as_block = true}
  {wcb : cstr_as_blocks = true}
  {wpc : with_prop_case = false} (* Avoid tLazy tBox values *)
  {Σ : GlobalContextMap.t} t v :
  has_tApp ->
  wf_glob Σ ->
  closed_env Σ ->
  @EWcbvEval.eval fl Σ t v ->
  wellformed Σ 0 t ->
  @EWcbvEval.eval fl (trans_env Σ) (trans Σ t) (trans Σ v).
Proof.
  intros hasapp wfΣ clΣ ev wf.
  revert t v wf ev.
  eapply
  (eval_preserve_mkApps_ind fl wcon (efl := efl) Σ _
    (wellformed Σ) (Qpres := Qpreserves_wellformed efl _ wfΣ)) => //; eauto;
    intros; repeat destruct_times; try solve [econstructor; eauto 3].

  - intros. eapply eval_wellformed in H; tea.

  - econstructor; eauto.
    rewrite trans_csubst // in e. now eapply wellformed_closed.

  - rewrite trans_csubst // in e. now eapply wellformed_closed.
    cbn. econstructor; eauto.

  - assert (forallb (wellformed Σ 0) args).
    cbn -[lookup_constructor lookup_constructor_pars_args] in i2.
    rewrite wcb in i2. move/and3P: i2 => [] _ _ hargs.
    solve_all.
    rewrite trans_iota_red // in e.
    { solve_all. now eapply wellformed_closed. }
    cbn -[lookup_constructor lookup_constructor_pars_args
    GlobalContextMap.lookup_inductive_kind] in e0 |- *.
    eapply eval_closed in H as evc => //.
    2:{ now eapply wellformed_closed. }
    rewrite GlobalContextMap.lookup_inductive_kind_spec in e0 *.
    destruct lookup_inductive_kind as [[]|] eqn:hl => //.
    1,3,4:eapply eval_iota_block; eauto;
      [now rewrite -is_propositional_cstr_trans|
        rewrite nth_error_map H2 //|now len|
        try (cbn; rewrite -H4 !length_skipn length_map //)].
    eapply eval_iota_block.
    1,3,4: eauto.
    + now rewrite -is_propositional_cstr_trans.
    + rewrite nth_error_map H2 //.
    + eapply trust_cofix.
      (* eapply eval_beta. eapply e0; eauto.
      constructor; eauto.
      rewrite closed_subst // simpl_subst_k //.
      eapply EWcbvEval.eval_to_value in H.
      eapply value_constructor_as_block in H.
      eapply constructor_isprop_pars_decl_constructor in H1 as [mdecl [idecl [hl' hp]]].
      econstructor; eauto.
      now erewrite <-lookup_constructor_trans. len.
      now rewrite /cstr_arity.
      instantiate (1 := map (trans Σ) args).
      eapply All2_All2_Set.
      eapply values_final. solve_all.
      unshelve eapply value_trans; tea.*)
    + now len.
    + now len.
    + apply trust_cofix.

  - now rewrite H in wpc.

  - apply trust_cofix.
    (*rewrite trans_mkApps /= in e1.
    cbn; eapply eval_fix => //; tea.
    len. apply trust_cofix*)


  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
  - apply trust_cofix.
Qed.
(*
  - rewrite trans_mkApps in e1.
    simpl in *.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply EWcbvEval.eval_fix; eauto.
    rewrite length_map.
    eapply trans_cunfold_fix; tea.
    eapply closed_fix_subst. tea.
    rewrite trans_mkApps in IHev3. apply IHev3.
    rewrite closedn_mkApps clargs.
    eapply eval_closed in ev2; tas. rewrite ev2 /= !andb_true_r.
    eapply closed_cunfold_fix; tea.

  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply eval_closed in ev2; tas.
    rewrite trans_mkApps in IHev1 |- *.
    simpl in *. eapply EWcbvEval.eval_fix_value. auto. auto. auto.
    eapply trans_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    now rewrite length_map.

  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    eapply eval_closed in ev2; tas.
    simpl in *. eapply EWcbvEval.eval_fix'. auto. auto.
    eapply trans_cunfold_fix; eauto.
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
    rewrite -> trans_mkApps in IHev1, IHev2. simpl.
    rewrite GlobalContextMap.lookup_inductive_kind_spec in IHev2 |- *.
    destruct EGlobalEnv.lookup_inductive_kind as [[]|] eqn:isp => //.
    simpl in IHev1.
    eapply EWcbvEval.eval_cofix_case. tea.
    apply trans_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    apply IHev2.
    eapply EWcbvEval.eval_cofix_case; tea.
    apply trans_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    simpl in *.
    eapply EWcbvEval.eval_cofix_case; tea.
    apply trans_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    eapply EWcbvEval.eval_cofix_case; tea.
    apply trans_cunfold_cofix; tea. eapply closed_cofix_subst; tea.

  - intros cd. specialize (IHev1 cd).
    move: (eval_closed _ clΣ _ _ cd ev1).
    rewrite closedn_mkApps; move/andP => [] clfix clargs. forward IHev2.
    { rewrite closedn_mkApps clargs andb_true_r. eapply closed_cunfold_cofix; tea. }
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec in IHev2 |- *.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp; auto.
    rewrite -> trans_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply trans_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> trans_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply trans_cunfold_cofix; tea. eapply closed_cofix_subst; tea.

  - rewrite /declared_constant in isdecl.
    move: (lookup_env_trans c wfΣ).
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
    rewrite trans_mkApps in IHev1.
    specialize (IHev1 cld).
    eapply EWcbvEval.eval_proj; tea.
    now rewrite -is_propositional_cstr_trans.
    now len. rewrite nth_error_map e3 //.
    eapply IHev2.
    eapply nth_error_forallb in e3; tea.

  - congruence.

  - rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    now rewrite e0.

  - move/andP=> [] clf cla.
    rewrite trans_mkApps.
    eapply eval_construct; tea.
    rewrite -lookup_constructor_trans //. exact e0.
    rewrite trans_mkApps in IHev1. now eapply IHev1.
    now len.
    now eapply IHev2.

  - congruence.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply EWcbvEval.eval_app_cong; eauto.
    eapply EWcbvEval.eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * destruct t => //; rewrite trans_mkApps /=.
    * destruct with_guarded_fix.
      + move: i.
        rewrite !negb_or.
        rewrite trans_mkApps !isFixApp_mkApps !isConstructApp_mkApps !isPrimApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        rewrite !andb_true_r.
        rtoProp; intuition auto.
        destruct v => /= //.
        destruct v => /= //.
        destruct v => /= //.
      + move: i.
        rewrite !negb_or.
        rewrite trans_mkApps !isConstructApp_mkApps !isPrimApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        destruct v => /= //.
  - destruct t => //.
    all:constructor; eauto. cbn [atom trans] in i |- *.
    rewrite -lookup_constructor_trans //. destruct l => //.
Qed.
*)
From MetaRocq.Erasure Require Import EEtaExpanded.

Lemma isLambda_trans Σ t : isLambda t -> isLambda (trans Σ t).
Proof. destruct t => //. Qed.
Lemma isBox_trans Σ t : isBox t -> isBox (trans Σ t).
Proof. destruct t => //. Qed.

Lemma trans_expanded {Σ : GlobalContextMap.t} t : expanded Σ t -> expanded Σ (trans Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?trans_mkApps.
  - eapply expanded_mkApps_expanded => //. solve_all.
  - cbn -[GlobalContextMap.lookup_inductive_kind].
    rewrite GlobalContextMap.lookup_inductive_kind_spec.
    destruct lookup_inductive_kind as [[]|] => /= //.
    2-3:constructor; eauto; solve_all.
    constructor; eauto; solve_all. cbn.
    now constructor.
    constructor; eauto; solve_all.
  - cbn -[GlobalContextMap.lookup_inductive_kind].
    rewrite GlobalContextMap.lookup_inductive_kind_spec.
    destruct lookup_inductive_kind as [[]|] => /= //.
    2-3:constructor; eauto; solve_all.
    constructor; eauto; solve_all. cbn.
    now constructor.
    constructor; eauto; solve_all.
  - cbn. econstructor; eauto. solve_all. now eapply isLambda_trans.
  - cbn. econstructor; eauto; solve_all. apply trust_cofix.
  - cbn -[GlobalContextMap.lookup_inductive_kind].
    rewrite GlobalContextMap.lookup_inductive_kind_spec.
    destruct lookup_inductive_kind as [[]|] => /= //.
    1,3,4:eapply expanded_tConstruct_app; eauto; solve_all.
    apply trust_cofix. (* Needs constructor_as_blocks = true invariant *)
Qed.
    (*cbn.
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
    rewrite isLambda_trans //.
  - eapply expanded_tConstruct_app; tea.
    now len. solve_all.
Qed.
*)
Lemma trans_expanded_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded Σ t -> expanded (trans_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rewrite lookup_env_trans // /= H //. 1-2:eauto. auto. solve_all.
Qed.

Lemma trans_expanded_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl Σ (trans_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply trans_expanded.
Qed.

Lemma trans_expanded_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded_decl Σ t -> expanded_decl (trans_env Σ) t.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply trans_expanded_irrel.
Qed.

Lemma trans_env_extends' {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  extends_prefix Σ Σ' ->
  wf_glob Σ' ->
  List.map (on_snd (trans_decl Σ)) Σ.(GlobalContextMap.global_decls) =
  List.map (on_snd (trans_decl Σ')) Σ.(GlobalContextMap.global_decls).
Proof.
  intros ext.
  destruct Σ as [Σ map repr wf]; cbn in *.
  move=> wfΣ.
  assert (extends_prefix Σ Σ); auto. now exists [].
  assert (wf_glob Σ).
  { eapply extends_wf_glob. exact ext. tea. }
  revert H H0.
  generalize Σ at 1 3 5 6. intros Σ''.
  induction Σ'' => //. cbn.
  intros hin wfg. depelim wfg.
  f_equal.
  2:{ eapply IHΣ'' => //. destruct hin. exists (x ++ [(kn, d)]). rewrite -app_assoc /= //. }
  unfold on_snd. cbn. f_equal.
  eapply wellformed_trans_decl_extends => //. cbn.
  eapply extends_wf_global_decl. 3:tea.
  eapply extends_wf_glob; tea. eapply extends_prefix_extends; tea.
  2:{ eapply extends_wf_glob; tea. }
  destruct hin. exists (x ++ [(kn, d)]). rewrite -app_assoc /= //.
  cbn. eapply extends_prefix_extends; tea.
Qed.

Lemma trans_env_eq {efl : EEnvFlags} (Σ : GlobalContextMap.t) :
  wf_glob Σ -> trans_env Σ = trans_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  unfold trans_env.
  destruct Σ; cbn. cbn in wf.
  induction global_decls in map, repr, wf0, wf |- * => //.
  cbn. f_equal.
  destruct a as [kn d]; unfold on_snd; cbn. f_equal. symmetry.
  eapply wellformed_trans_decl_extends => //. cbn. now depelim wf. cbn.
  eapply extends_prefix_extends; tea. now exists [(kn, d)]. cbn.
  set (Σg' := GlobalContextMap.make global_decls (fresh_globals_cons_inv wf0)).
  erewrite <- (IHglobal_decls (GlobalContextMap.map Σg') (GlobalContextMap.repr Σg')).
  2:now depelim wf.
  set (Σg := {| GlobalContextMap.global_decls := _ :: _ |}).
  symmetry. eapply (trans_env_extends' (Σ := Σg') (Σ' := Σg)) => //.
  cbn. now exists [a].
Qed.

Lemma trans_env_expanded {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (trans_env Σ).
Proof.
  unfold expanded_global_env; move=> wfg.
  rewrite trans_env_eq //.
  destruct Σ as [Σ map repr wf]. cbn in *.
  clear map repr.
  induction 1; cbn; constructor; auto.
  cbn in IHexpanded_global_declarations.
  unshelve eapply IHexpanded_global_declarations. now depelim wfg. cbn.
  set (Σ' := GlobalContextMap.make _ _).
  rewrite -(trans_env_eq Σ'). cbn. now depelim wfg.
  eapply (trans_expanded_decl_irrel (Σ := Σ')). now depelim wfg.
  now unshelve eapply (trans_expanded_decl (Σ:=Σ')).
Qed.

Lemma trans_wellformed {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t -> EWellformed.wellformed Σ n (trans Σ t).
Proof.
  intros wfΣ hbox hrel.
  induction t in n |- * using EInduction.term_forall_list_ind => //.
  all:try solve [cbn; rtoProp; intuition auto; solve_all].
  all:apply trust_cofix.
  (*-
    cbn -[lookup_constructor]. intros. destruct cstr_as_blocks; rtoProp; repeat split; eauto. 2:solve_all.
    2: now destruct args; inv H0. len. eauto.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars lookup_inductive]. move/and3P => [] hasc /andP[]hs ht hbrs.
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
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all. now eapply isLambda_trans. now len.
    unfold test_def in *. len. eauto.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all. now len.
    unfold test_def in *. len. eauto. *)
Qed.

Import EWellformed.

Lemma trans_wellformed_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_glob Σ ->
  forall n, wellformed Σ n t -> wellformed (trans_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_trans //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct (cst_body c) => //.
  - rewrite lookup_env_trans //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    repeat split; eauto. destruct cstr_as_blocks; rtoProp; repeat split; len; eauto. 1: solve_all.
  - rewrite /wf_brs; cbn; rewrite lookup_env_trans //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_trans //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    rewrite andb_false_r => //.
    destruct nth_error => /= //.
    all:intros; rtoProp; intuition auto; solve_all.
Qed.

Lemma trans_wellformed_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} d :
  wf_glob Σ ->
  wf_global_decl Σ d -> wf_global_decl (trans_env Σ) d.
Proof.
  intros wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply trans_wellformed_irrel.
Qed.

Lemma trans_decl_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel -> wf_glob Σ ->
  forall d, wf_global_decl Σ d -> wf_global_decl (trans_env Σ) (trans_decl Σ d).
Proof.
  intros hasb hasr wf d.
  intros hd.
  eapply trans_wellformed_decl_irrel; tea.
  move: hd.
  destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply trans_wellformed => //.
Qed.

Lemma fresh_global_trans_env {Σ : GlobalContextMap.t} kn :
  fresh_global kn Σ ->
  fresh_global kn (trans_env Σ).
Proof.
  destruct Σ as [Σ map repr wf]; cbn in *.
  induction 1; cbn; constructor; auto.
  now eapply Forall_map; cbn.
Qed.

Lemma trans_env_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel ->
  wf_glob Σ -> wf_glob (trans_env Σ).
Proof.
  intros hasb hasrel.
  intros wfg. rewrite trans_env_eq //.
  destruct Σ as [Σ map repr wf]; cbn in *.
  clear map repr.
  induction wfg; cbn; constructor; auto.
  - rewrite /= -(trans_env_eq (GlobalContextMap.make Σ (fresh_globals_cons_inv wf))) //.
    eapply trans_decl_wf => //.
  - rewrite /= -(trans_env_eq (GlobalContextMap.make Σ (fresh_globals_cons_inv wf))) //.
    now eapply fresh_global_trans_env.
Qed.

Definition trans_program (p : eprogram_env) :=
  (trans_env p.1, trans p.1 p.2).

Definition trans_program_wf {efl} (p : eprogram_env) {hastbox : has_tBox} {hastrel : has_tRel} :
  wf_eprogram_env efl p -> wf_eprogram efl (trans_program p).
Proof.
  intros []; split.
  now eapply trans_env_wf.
  cbn. eapply trans_wellformed_irrel => //. now eapply trans_wellformed.
Qed.

Definition trans_program_expanded {efl} (p : eprogram_env) :
  wf_eprogram_env efl p ->
  expanded_eprogram_env_cstrs p -> expanded_eprogram_cstrs (trans_program p).
Proof.
  unfold expanded_eprogram_env_cstrs.
  move=> [wfe wft] /andP[] etae etat.
  apply/andP; split.
  cbn. eapply expanded_global_env_isEtaExp_env, trans_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  eapply expanded_isEtaExp.
  eapply trans_expanded_irrel => //.
  now apply trans_expanded, isEtaExp_expanded.
Qed.
