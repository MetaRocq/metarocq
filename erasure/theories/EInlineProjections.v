(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EExtends
    ELiftSubst ECSubst EGlobalEnv EWellformed EWcbvEval Extract
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

(** Allow everything in terms *)

Definition switch_no_params (efl : EEnvFlags) :=
  {| has_axioms := has_axioms;
     has_cstr_params := false;
     term_switches := term_switches ;
     cstr_as_blocks := false
     |}.
Definition flags_after_projs := (switch_no_params all_env_flags).
Local Existing Instance flags_after_projs.

Definition disable_projections_term_flags (et : ETermFlags) :=
  {| has_tBox := has_tBox
    ; has_tRel := has_tRel
    ; has_tVar := has_tVar
    ; has_tEvar := has_tEvar
    ; has_tLambda := has_tLambda
    ; has_tLetIn := has_tLetIn
    ; has_tApp := has_tApp
    ; has_tConst := has_tConst
    ; has_tConstruct := has_tConstruct
    ; has_tCase := true
    ; has_tProj := false
    ; has_tFix := has_tFix
    ; has_tCoFix := has_tCoFix
    ; has_tPrim := has_tPrim
    ; has_tLazy_Force := has_tLazy_Force
  |}.

Definition disable_projections_env_flag (efl : EEnvFlags) :=
  {| has_axioms := efl.(@has_axioms);
     term_switches := disable_projections_term_flags term_switches;
     has_cstr_params := efl.(@has_cstr_params) ;
     cstr_as_blocks := efl.(@cstr_as_blocks) |}.

Arguments lookup_projection : simpl never.
Arguments GlobalContextMap.lookup_projection : simpl never.

Lemma lookup_inductive_wellformed {efl : EEnvFlags} Σ (kn : kername)
  (decl : mutual_inductive_body) :
  wf_glob Σ → lookup_minductive Σ kn = Some decl → wf_minductive decl.
Proof.
  intros wfΣ.
  rewrite /lookup_minductive.
  destruct lookup_env as [[]|] eqn:hl => //=.
  intros [= <-]. now eapply lookup_env_wellformed in hl.
Qed.

Lemma wellformed_projection_args {efl : EEnvFlags} {Σ p mdecl idecl cdecl pdecl} :
  wf_glob Σ ->
  lookup_projection Σ p = Some (mdecl, idecl, cdecl, pdecl) ->
  #|idecl.(ind_ctors)| = 1 /\ p.(proj_arg) < cdecl.(cstr_nargs).
Proof.
  intros wfΣ.
  rewrite /lookup_projection /lookup_constructor /lookup_inductive.
  destruct lookup_minductive eqn:hl => //=.
  eapply lookup_inductive_wellformed in hl; eauto.
  move: hl. unfold wf_minductive.
  destruct nth_error eqn:hnth => //.
  destruct ind_ctors as [|? []] eqn:hnth' => //.
  destruct (nth_error (ind_projs _) _) eqn:hnth'' => //.
  intros wf [= <- <- <- <-].
  move: wf => /andP[] _.
  move/(nth_error_forallb hnth). rewrite /wf_inductive /wf_projections.
  destruct ind_projs => //. now rewrite nth_error_nil in hnth''.
  rewrite hnth'. cbn. move/(@eqb_eq nat). intros <-.
  eapply nth_error_Some_length in hnth''. now cbn in hnth''.
  destruct (nth_error (ind_projs _) _) eqn:hnth'' => //.
  move=> /andP[] _.
  move/(nth_error_forallb hnth). rewrite /wf_inductive /wf_projections.
  destruct ind_projs => //. now rewrite nth_error_nil in hnth''.
  rewrite hnth' //.
Qed.

Section optimize.
  Context (Σ : GlobalContextMap.t).

  Fixpoint optimize (t : term) : term :=
    match t with
    | tRel i => tRel i
    | tEvar ev args => tEvar ev (List.map optimize args)
    | tLambda na M => tLambda na (optimize M)
    | tApp u v => tApp (optimize u) (optimize v)
    | tLetIn na b b' => tLetIn na (optimize b) (optimize b')
    | tCase ind c brs => tCase ind (optimize c) (map (on_snd optimize) brs)
    | tProj p c =>
      match GlobalContextMap.lookup_projection Σ p with
      | Some (mdecl, idecl, cdecl, pdecl) =>
        tCase (p.(proj_ind), p.(proj_npars)) (optimize c) [(unfold cdecl.(cstr_nargs) (fun n => nAnon), tRel (cdecl.(cstr_nargs) - S p.(proj_arg)))]
      | _ => tProj p (optimize c)
      end
    | tFix mfix idx =>
      let mfix' := List.map (map_def optimize) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := List.map (map_def optimize) mfix in
      tCoFix mfix' idx
    | tBox => t
    | tVar _ => t
    | tConst _ => t
    | tConstruct ind n args => tConstruct ind n (map optimize args)
    | tPrim p => tPrim (map_prim optimize p)
    | tLazy t => tLazy (optimize t)
    | tForce t => tForce (optimize t)
    end.

  Lemma optimize_mkApps f l : optimize (mkApps f l) = mkApps (optimize f) (map optimize l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_optimize_repeat_box n : map optimize (repeat tBox n) = repeat tBox n.
  Proof using Type. by rewrite map_repeat. Qed.

  (* move to globalenv *)

  Lemma isLambda_optimize t : isLambda t -> isLambda (optimize t).
  Proof. destruct t => //. Qed.
  Lemma isBox_optimize t : isBox t -> isBox (optimize t).
  Proof. destruct t => //. Qed.

  Lemma wf_optimize t k :
    wf_glob Σ ->
    wellformed Σ k t -> wellformed Σ k (optimize t).
  Proof using Type.
    intros wfΣ.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold wf_fix_gen, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - rtoProp. split; eauto. destruct args; eauto.
    - move/andP: H => [] /andP[] -> clt cll /=.
      rewrite IHt //=. solve_all.
    - rewrite GlobalContextMap.lookup_projection_spec.
      destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl; auto => //.
      simpl.
      have [ncstrs arglen] := wellformed_projection_args wfΣ hl.
      apply lookup_projection_lookup_constructor, lookup_constructor_lookup_inductive in hl.
      rewrite /wf_brs hl /= andb_true_r.
      rewrite IHt //=; len. rewrite ncstrs. apply Nat.ltb_lt.
      lia.
    - len. rtoProp; solve_all. solve_all.
      now eapply isLambda_optimize. solve_all.
    - len. rtoProp; repeat solve_all.
    - rewrite test_prim_map. rtoProp; intuition eauto; solve_all.
  Qed.

  Lemma optimize_csubst {a k b} n :
    wf_glob Σ ->
    wellformed Σ (k + n) b ->
    optimize (ECSubst.csubst a k b) = ECSubst.csubst (optimize a) k (optimize b).
  Proof using Type.
    intros wfΣ.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros wft; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold wf_fix, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n0)%nat; auto.
    - f_equal. rtoProp. now destruct args; inv H0.
    - move/andP: wft => [] /andP[] hi hb hl. rewrite IHb. f_equal. unfold on_snd; solve_all.
      repeat toAll. f_equal. solve_all. unfold on_snd; cbn. f_equal.
      rewrite a0 //. now rewrite -Nat.add_assoc.
    - move/andP: wft => [] hp hb.
      rewrite GlobalContextMap.lookup_projection_spec.
      destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => /= //.
      f_equal; eauto. f_equal. len. f_equal.
      have arglen := wellformed_projection_args wfΣ hl.
      case: Nat.compare_spec. lia. lia.
      auto.
    - f_equal. move/andP: wft => [hlam /andP[] hidx hb].
      solve_all. unfold map_def. f_equal.
      eapply a0. now rewrite -Nat.add_assoc.
    - f_equal. move/andP: wft => [hidx hb].
      solve_all. unfold map_def. f_equal.
      eapply a0. now rewrite -Nat.add_assoc.
  Qed.

  Lemma optimize_substl s t :
    wf_glob Σ ->
    forallb (wellformed Σ 0) s ->
    wellformed Σ #|s| t ->
    optimize (substl s t) = substl (map optimize s) (optimize t).
  Proof using Type.
    intros wfΣ. induction s in t |- *; simpl; auto.
    move/andP => [] cla cls wft.
    rewrite IHs //. eapply wellformed_csubst => //.
    f_equal. rewrite (optimize_csubst (S #|s|)) //.
  Qed.

  Lemma optimize_iota_red pars args br :
    wf_glob Σ ->
    forallb (wellformed Σ 0) args ->
    wellformed Σ #|skipn pars args| br.2 ->
    optimize (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map optimize args) (on_snd optimize br).
  Proof using Type.
    intros wfΣ wfa wfbr.
    unfold EGlobalEnv.iota_red.
    rewrite optimize_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite List.length_rev.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma optimize_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cunfold_fix mfix idx n f :
    wf_glob Σ ->
    wellformed Σ 0 (tFix mfix idx) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof using Type.
    intros wfΣ hfix.
    unfold cunfold_fix.
    rewrite nth_error_map.
    cbn in hfix. move/andP: hfix => [] hlam /andP[] hidx hfix.
    destruct nth_error eqn:hnth => //.
    intros [= <- <-] => /=. f_equal.
    rewrite optimize_substl //. eapply wellformed_fix_subst => //.
    rewrite fix_subst_length.
    eapply nth_error_forallb in hfix; tea. now rewrite Nat.add_0_r in hfix.
    now rewrite optimize_fix_subst.
  Qed.

  Lemma optimize_cunfold_cofix mfix idx n f :
    wf_glob Σ ->
    wellformed Σ 0 (tCoFix mfix idx) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof using Type.
    intros wfΣ hfix.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    cbn in hfix. move/andP: hfix => [] hidx hfix.
    destruct nth_error eqn:hnth => //.
    intros [= <- <-] => /=. f_equal.
    rewrite optimize_substl //. eapply wellformed_cofix_subst => //.
    rewrite cofix_subst_length.
    eapply nth_error_forallb in hfix; tea. now rewrite Nat.add_0_r in hfix.
    now rewrite optimize_cofix_subst.
  Qed.

End optimize.

Definition optimize_constant_decl Σ cb :=
  {| cst_body := option_map (optimize Σ) cb.(cst_body) |}.

Definition optimize_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (optimize_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl idecl
  end.

Definition optimize_env Σ :=
  map (on_snd (optimize_decl Σ)) Σ.(GlobalContextMap.global_decls).

Import EnvMap.

Program Fixpoint optimize_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
    on_snd (optimize_decl Σg) hd :: optimize_env' tl (fresh_globals_cons_inv HΣ)
  end.

Import EGlobalEnv EExtends.

Lemma extends_lookup_projection {efl : EEnvFlags} {Σ Σ' p} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_projection Σ p) ->
  lookup_projection Σ p = lookup_projection Σ' p.
Proof.
  intros ext wf; cbn.
  unfold lookup_projection.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  simpl.
  rewrite (extends_lookup_constructor wf ext _ _ _ hl) //.
Qed.

Lemma wellformed_optimize_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  forall n, EWellformed.wellformed Σ n t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  optimize Σ t = optimize Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive
    GlobalContextMap.lookup_projection]; intros => //.
  all:unfold wf_fix_gen in *; rtoProp; intuition auto.
  5:{ destruct cstr_as_blocks; rtoProp. f_equal; eauto; solve_all. destruct args; cbn in *; eauto. }
  all:f_equal; eauto; solve_all.
  - rewrite !GlobalContextMap.lookup_projection_spec.
    rewrite -(extends_lookup_projection H0 H1 H3).
    destruct lookup_projection as [[[[]]]|]. f_equal; eauto.
    now cbn in H3.
Qed.

Lemma wellformed_optimize_decl_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_global_decl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  optimize_decl Σ t = optimize_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold optimize_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_optimize_extends.
Qed.

Lemma lookup_env_optimize_env_Some {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn d :
  wf_glob Σ ->
  GlobalContextMap.lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t,
    [× extends_prefix Σ' Σ, wf_global_decl Σ' d &
      lookup_env (optimize_env Σ) kn = Some (optimize_decl Σ' d)].
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
    f_equal. symmetry. eapply wellformed_optimize_decl_extends. cbn. now depelim wfg.
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
      symmetry. eapply wellformed_optimize_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      eapply extends_prefix_extends.
      cbn. now exists [a]. now cbn.
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_env_optimize_env_None {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  GlobalContextMap.lookup_env Σ kn = None ->
  lookup_env (optimize_env Σ) kn = None.
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  wf_glob Σ ->
  lookup_env (optimize_env Σ) kn = option_map (optimize_decl Σ) (lookup_env Σ kn).
Proof.
  intros wf.
  rewrite -GlobalContextMap.lookup_env_spec.
  destruct (GlobalContextMap.lookup_env Σ kn) eqn:hl.
  - eapply lookup_env_optimize_env_Some in hl as [Σ' [ext wf' hl']] => /=.
    rewrite hl'. f_equal.
    eapply wellformed_optimize_decl_extends; eauto.
    now eapply extends_prefix_extends. auto.

  - cbn. now eapply lookup_env_optimize_env_None in hl.
Qed.

Lemma is_propositional_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (optimize_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_optimize (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma lookup_inductive_pars_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  EGlobalEnv.lookup_inductive_pars Σ ind = EGlobalEnv.lookup_inductive_pars (optimize_env Σ) ind.
Proof.
  rewrite /lookup_inductive_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_optimize ind wf).
  rewrite /GlobalContextMap.lookup_inductive /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma is_propositional_cstr_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind c :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (optimize_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_optimize (inductive_mind ind) wf).
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

Definition disable_prop_cases fl := {| with_prop_case := false; with_guarded_fix := fl.(@with_guarded_fix) ; with_constructor_as_block := false |}.

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma lookup_constructor_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} {ind c} :
  wf_glob Σ ->
  lookup_constructor Σ ind c = lookup_constructor (optimize_env Σ) ind c.
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_optimize // /=. destruct lookup_env => // /=.
  destruct g => //.
Qed.

Lemma lookup_projection_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} {p} :
  wf_glob Σ ->
  lookup_projection Σ p = lookup_projection (optimize_env Σ) p.
Proof.
  intros wfΣ. rewrite /lookup_projection.
  rewrite -lookup_constructor_optimize //.
Qed.

Lemma constructor_isprop_pars_decl_inductive {Σ ind c} {prop pars cdecl} :
  constructor_isprop_pars_decl Σ ind c = Some (prop, pars, cdecl)  ->
  inductive_isprop_and_pars Σ ind = Some (prop, pars).
Proof.
  rewrite /constructor_isprop_pars_decl /inductive_isprop_and_pars /lookup_constructor.
  destruct lookup_inductive as [[mdecl idecl]|]=> /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_constructor {Σ ind c} {mdecl idecl cdecl} :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  constructor_isprop_pars_decl Σ ind c = Some (ind_propositional idecl, ind_npars mdecl, cdecl).
Proof.
  rewrite /constructor_isprop_pars_decl. intros -> => /= //.
Qed.

Lemma wf_mkApps Σ k f args : reflect (wellformed Σ k f /\ forallb (wellformed Σ k) args) (wellformed Σ k (mkApps f args)).
Proof.
  rewrite wellformed_mkApps //. eapply andP.
Qed.

Lemma substl_closed s t : closed t -> substl s t = t.
Proof.
  induction s in t |- *; cbn => //.
  intros clt. rewrite csubst_closed //. now apply IHs.
Qed.

Lemma substl_rel s k a :
  closed a ->
  nth_error s k = Some a ->
  substl s (tRel k) = a.
Proof.
  intros cla.
  induction s in k |- *.
  - rewrite nth_error_nil //.
  - destruct k => //=.
    * intros [= ->]. rewrite substl_closed //.
    * intros hnth. now apply IHs.
Qed.


Lemma optimize_correct {fl} {wcon : with_constructor_as_block = false} { Σ : GlobalContextMap.t} t v :
  wf_glob Σ ->
  @eval fl Σ t v ->
  wellformed Σ 0 t ->
  @eval fl (optimize_env Σ) (optimize Σ t) (optimize Σ v).
Proof.
  intros wfΣ ev.
  induction ev; simpl in *.

  - move/andP => [] cla clt. econstructor; eauto.
  - move/andP => [] clf cla.
    eapply eval_wellformed in ev2; tea => //.
    eapply eval_wellformed in ev1; tea => //.
    econstructor; eauto.
    rewrite -(optimize_csubst _ 1) //.
    apply IHev3. eapply wellformed_csubst => //.

  - move/andP => [] clb0 clb1.
    intuition auto.
    eapply eval_wellformed in ev1; tea => //.
    forward IHev2 by eapply wellformed_csubst => //.
    econstructor; eauto. rewrite -(optimize_csubst _ 1) //.

  - move/andP => [] /andP[] hl wfd wfbrs. rewrite optimize_mkApps in IHev1.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] wfc' wfargs.
    eapply nth_error_forallb in wfbrs; tea.
    rewrite Nat.add_0_r in wfbrs.
    forward IHev2. eapply wellformed_iota_red; tea => //.
    rewrite optimize_iota_red in IHev2 => //. now rewrite e4.
    econstructor; eauto.
    rewrite -is_propositional_cstr_optimize //. tea.
    rewrite nth_error_map e2 //. len. len.

  - congruence.

  - move/andP => [] /andP[] hl wfd wfbrs.
    forward IHev2. eapply wellformed_substl; tea => //.
    rewrite forallb_repeat //. len.
    rewrite e1 /= Nat.add_0_r in wfbrs. now move/andP: wfbrs.
    rewrite optimize_substl in IHev2 => //.
    rewrite forallb_repeat //. len.
    rewrite e1 /= Nat.add_0_r in wfbrs. now move/andP: wfbrs.
    eapply eval_iota_sing => //; eauto.
    rewrite -is_propositional_optimize //.
    rewrite e1 //. simpl.
    rewrite map_repeat in IHev2 => //.

  - move/andP => [] clf cla. rewrite optimize_mkApps in IHev1.
    simpl in *.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] wff wfargs.
    eapply eval_fix; eauto.
    rewrite length_map.
    eapply optimize_cunfold_fix; tea.
    rewrite optimize_mkApps in IHev3. apply IHev3.
    rewrite wellformed_mkApps // wfargs.
    eapply eval_wellformed in ev2; tas => //. rewrite ev2 /= !andb_true_r.
    eapply wellformed_cunfold_fix; tea.

  - move/andP => [] clf cla.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] clfix clargs.
    eapply eval_wellformed in ev2; tas => //.
    rewrite optimize_mkApps in IHev1 |- *.
    simpl in *. eapply eval_fix_value. auto. auto. auto.
    eapply optimize_cunfold_fix; eauto.
    now rewrite length_map.

  - move/andP => [] clf cla.
    eapply eval_wellformed in ev1 => //.
    eapply eval_wellformed in ev2; tas => //.
    simpl in *. eapply eval_fix'. auto. auto.
    eapply optimize_cunfold_fix; eauto.
    eapply IHev2; tea. eapply IHev3.
    apply/andP; split => //.
    eapply wellformed_cunfold_fix; tea. now cbn.

  - move/andP => [] /andP[] hl cd clbrs. specialize (IHev1 cd).
    eapply eval_wellformed in ev1; tea => //.
    move/wf_mkApps: ev1 => [] wfcof wfargs.
    forward IHev2.
    rewrite hl wellformed_mkApps // /= wfargs clbrs !andb_true_r.
    eapply wellformed_cunfold_cofix; tea => //.
    rewrite !optimize_mkApps /= in IHev1, IHev2.
    eapply eval_cofix_case. tea.
    eapply optimize_cunfold_cofix; tea.
    exact IHev2.

  - move/andP => [] hl hd.
    rewrite GlobalContextMap.lookup_projection_spec in IHev2 |- *.
    destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl' => //.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] wfcof wfargs.
    forward IHev2.
    { rewrite /= wellformed_mkApps // wfargs andb_true_r.
      eapply wellformed_cunfold_cofix; tea. }
    rewrite optimize_mkApps /= in IHev1.
    eapply eval_cofix_case. eauto.
    eapply optimize_cunfold_cofix; tea.
    rewrite optimize_mkApps in IHev2 => //.

  - rewrite /declared_constant in isdecl.
    move: (lookup_env_optimize c wfΣ).
    rewrite isdecl /= //.
    intros hl.
    econstructor; tea. cbn. rewrite e //.
    apply IHev.
    eapply lookup_env_wellformed in wfΣ; tea.
    move: wfΣ. rewrite /wf_global_decl /= e //.

  - move=> /andP[] iss cld.
    rewrite GlobalContextMap.lookup_projection_spec.
    eapply eval_wellformed in ev1; tea => //.
    move/wf_mkApps: ev1 => [] wfc wfargs.
    destruct lookup_projection as [[[[mdecl idecl] cdecl'] pdecl]|] eqn:hl' => //.
    pose proof (lookup_projection_lookup_constructor hl').
    rewrite (constructor_isprop_pars_decl_constructor H) in e1. noconf e1.
    forward IHev1 by auto.
    forward IHev2. eapply nth_error_forallb in wfargs; tea.
    rewrite optimize_mkApps /= in IHev1.
    eapply eval_iota; tea.
    rewrite /constructor_isprop_pars_decl -lookup_constructor_optimize // H //= //.
    rewrite H0 H1; reflexivity. cbn. reflexivity. len. len.
    rewrite length_skipn. lia.
    unfold iota_red. cbn.
    rewrite (substl_rel _ _ (optimize Σ a)) => //.
    { eapply nth_error_forallb in wfargs; tea.
      eapply wf_optimize in wfargs => //.
      now eapply wellformed_closed in wfargs. }
    pose proof (wellformed_projection_args wfΣ hl'). cbn in H1.
    rewrite nth_error_rev. len. rewrite length_skipn. lia.
    rewrite List.rev_involutive. len. rewrite length_skipn.
    rewrite nth_error_skipn nth_error_map.
    rewrite e2 -H1.
    assert((ind_npars mdecl + cstr_nargs cdecl - ind_npars mdecl) = cstr_nargs cdecl) by lia.
    rewrite H3.
    eapply (f_equal (option_map (optimize Σ))) in e3.
    cbn in e3. rewrite -e3. f_equal. f_equal. lia.

  - congruence.

  - move=> /andP[] iss cld.
    rewrite GlobalContextMap.lookup_projection_spec.
    destruct lookup_projection as [[[[mdecl idecl] cdecl'] pdecl]|] eqn:hl' => //.
    pose proof (lookup_projection_lookup_constructor hl').
    simpl in H.
    move: e0. rewrite /inductive_isprop_and_pars.
    rewrite (lookup_constructor_lookup_inductive H) /=.
    intros [= eq <-].
    eapply eval_iota_sing => //; eauto.
    rewrite -is_propositional_optimize // /inductive_isprop_and_pars
      (lookup_constructor_lookup_inductive H) //=. congruence.
    have lenarg := wellformed_projection_args wfΣ hl'.
    rewrite (substl_rel _ _ tBox) => //.
    { rewrite nth_error_repeat //. len. }
    now constructor.

  - move/andP=> [] clf cla.
    rewrite optimize_mkApps.
    eapply eval_construct; tea.
    rewrite -lookup_constructor_optimize //. exact e0.
    rewrite optimize_mkApps in IHev1. now eapply IHev1.
    now len.
    now eapply IHev2.

  - congruence.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply eval_app_cong; eauto.
    eapply eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * depelim a0.
      + destruct t => //; rewrite optimize_mkApps /=.
      + now rewrite /= !orb_false_r orb_true_r in i.
    * destruct with_guarded_fix.
      + move: i.
        rewrite !negb_or.
        rewrite optimize_mkApps !isFixApp_mkApps !isConstructApp_mkApps !isPrimApp_mkApps
          !isLazyApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        rewrite !andb_true_r.
        rtoProp; intuition auto;  destruct v => /= //.
      + move: i.
        rewrite !negb_or.
        rewrite optimize_mkApps !isConstructApp_mkApps !isPrimApp_mkApps !isLazyApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        destruct v => /= //.
  - intros; rtoProp; intuition eauto.
    depelim X; repeat constructor.
    eapply All2_over_undep in a.
    eapply All2_Set_All2 in ev. eapply All2_All2_Set. primProp.
    subst a0 a'; cbn in *. depelim H0; cbn in *. intuition auto; solve_all.
    primProp; depelim H0; intuition eauto.
  - intros wf; econstructor; eauto. eapply IHev2.
    eapply eval_wellformed in ev1; tea => //.
  - destruct t => //.
    all:constructor; eauto.
    cbn [atom optimize] in i |- *.
    rewrite -lookup_constructor_optimize //.
    destruct args; cbn in *; eauto.
Qed.

From MetaRocq.Erasure Require Import EEtaExpanded.

Lemma optimize_expanded {Σ : GlobalContextMap.t} t : expanded Σ t -> expanded Σ (optimize Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?optimize_mkApps.
  - eapply expanded_mkApps_expanded => //. solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars].
    rewrite GlobalContextMap.lookup_projection_spec.
    destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] => /= //.
    2:constructor; eauto; solve_all.
    destruct proj as [[ind npars] arg].
    econstructor; eauto. repeat constructor.
  - cbn. eapply expanded_tFix. solve_all.
    rewrite isLambda_optimize //.
  - eapply expanded_tConstruct_app; tea.
    now len. solve_all.
Qed.

Lemma optimize_expanded_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded Σ t -> expanded (optimize_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rewrite lookup_env_optimize // /= H //. 1-2:eauto. auto. solve_all.
Qed.

Lemma optimize_expanded_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl Σ (optimize_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply optimize_expanded.
Qed.

Lemma optimize_expanded_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded_decl Σ t -> expanded_decl (optimize_env Σ) t.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply optimize_expanded_irrel.
Qed.

Lemma optimize_wellformed_term {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t ->
  EWellformed.wellformed (efl := disable_projections_env_flag efl) Σ n (optimize Σ t).
Proof.
  intros hbox hrel wfΣ.
  induction t in n |- * using EInduction.term_forall_list_ind => //.
  all:try solve [cbn; rtoProp; intuition auto; solve_all].
  - cbn -[lookup_constructor_pars_args]. intros. rtoProp. repeat split; eauto.
    destruct cstr_as_blocks; rtoProp; eauto.
    destruct lookup_constructor_pars_args as [ [] | ]; eauto. split; len.  solve_all. split; eauto.
    solve_all. now destruct args; invs H0.
  - cbn. move/andP => [] /andP[] hast hl wft.
    rewrite GlobalContextMap.lookup_projection_spec.
    destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl'; auto => //.
    simpl.
    rewrite /wf_brs.
    rewrite (lookup_constructor_lookup_inductive (lookup_projection_lookup_constructor hl')) /=.
    rewrite hrel IHt //= andb_true_r.
    have [-> hargs'] := wellformed_projection_args wfΣ hl'.
    rtoProp; intuition auto.
    apply Nat.ltb_lt. len.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all. now eapply isLambda_optimize.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all.
  - cbn. rtoProp; intuition eauto; solve_all_k 6.
Qed.

Import EWellformed.

Lemma optimize_wellformed_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_glob Σ ->
  forall n, wellformed (efl := disable_projections_env_flag efl) Σ n t ->
  wellformed (efl := disable_projections_env_flag efl) (optimize_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    repeat (rtoProp; intuition auto).
    destruct has_axioms => //. cbn in *.
    destruct (cst_body c) => //.
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    repeat split; eauto. destruct cstr_as_blocks; rtoProp; repeat split; eauto. solve_all.
  - rewrite /wf_brs; cbn; rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
Qed.

Lemma optimize_wellformed {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t ->
  EWellformed.wellformed (efl := disable_projections_env_flag efl) (optimize_env Σ) n (optimize Σ t).
Proof.
  intros. apply optimize_wellformed_irrel => //.
  now apply optimize_wellformed_term.
Qed.

From MetaRocq.Erasure Require Import EGenericGlobalMap.

#[local]
Instance GT : GenTransform := { gen_transform := optimize; gen_transform_inductive_decl := id }.
#[local]
Instance GTID : GenTransformId GT.
Proof.
  red. reflexivity.
Qed.
#[local]
Instance GTExt efl : GenTransformExtends efl (disable_projections_env_flag efl) GT.
Proof.
  intros Σ t n wfΣ Σ' ext wf wf'.
  unfold gen_transform, GT.
  eapply wellformed_optimize_extends; tea.
Qed.
#[local]
Instance GTWf efl : GenTransformWf efl (disable_projections_env_flag efl) GT.
Proof.
  refine {| gen_transform_pre := fun _ _ => has_tBox /\ has_tRel |}; auto.
  intros Σ n t [] wfΣ wft.
  now apply optimize_wellformed.
Defined.

Lemma optimize_extends_env {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (optimize_env Σ) (optimize_env Σ').
Proof.
  intros hast ext wf.
  now apply (gen_transform_extends (gt := GTExt efl) ext).
Qed.

Lemma optimize_env_eq {efl : EEnvFlags} (Σ : GlobalContextMap.t) : wf_glob Σ -> optimize_env Σ = optimize_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  now apply (gen_transform_env_eq (gt := GTExt efl)).
Qed.

Lemma optimize_env_expanded {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (optimize_env Σ).
Proof.
  unfold expanded_global_env; move=> wfg.
  rewrite optimize_env_eq //.
  destruct Σ as [Σ map repr wf]. cbn in *.
  clear map repr.
  induction 1; cbn; constructor; auto.
  cbn in IHexpanded_global_declarations.
  unshelve eapply IHexpanded_global_declarations. now depelim wfg. cbn.
  set (Σ' := GlobalContextMap.make _ _).
  rewrite -(optimize_env_eq Σ'). cbn. now depelim wfg.
  eapply (optimize_expanded_decl_irrel (Σ := Σ')). now depelim wfg.
  now unshelve eapply (optimize_expanded_decl (Σ:=Σ')).
Qed.

Lemma Pre_glob efl Σ wf :
  has_tBox -> has_tRel -> Pre_glob (GTWF:=GTWf efl) Σ wf.
Proof.
  intros hasb hasr.
  induction Σ => //. destruct a as [kn d]; cbn.
  split => //. destruct d as [[[|]]|] => //=.
Qed.

Lemma optimize_env_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel ->
  wf_glob Σ -> wf_glob (efl := disable_projections_env_flag efl) (optimize_env Σ).
Proof.
  intros hasb hasre wfg.
  eapply (gen_transform_env_wf (gt := GTExt efl)) => //.
  now apply Pre_glob.
Qed.

Definition optimize_program (p : eprogram_env) :=
  (optimize_env p.1, optimize p.1 p.2).

Definition optimize_program_wf {efl : EEnvFlags} (p : eprogram_env) {hastbox : has_tBox} {hastrel : has_tRel} :
  wf_eprogram_env efl p -> wf_eprogram (disable_projections_env_flag efl) (optimize_program p).
Proof.
  intros []; split.
  now eapply optimize_env_wf.
  cbn. now eapply optimize_wellformed.
Qed.

Definition optimize_program_expanded {efl} (p : eprogram_env) :
  wf_eprogram_env efl p ->
  expanded_eprogram_env_cstrs p -> expanded_eprogram_cstrs (optimize_program p).
Proof.
  unfold expanded_eprogram_env_cstrs.
  move=> [wfe wft] /andP[] etae etat.
  apply/andP; split.
  cbn. eapply expanded_global_env_isEtaExp_env, optimize_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  eapply expanded_isEtaExp.
  eapply optimize_expanded_irrel => //.
  now apply optimize_expanded, isEtaExp_expanded.
Qed.
