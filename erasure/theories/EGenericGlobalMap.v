(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst EnvMap.
From MetaRocq.Erasure Require Import EAst EAstUtils EInduction EArities
    ELiftSubst ESpineView EGlobalEnv EWellformed EEnvMap
    EWcbvEval EEtaExpanded ECSubst EWcbvEvalEtaInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

Class GenTransform :=
  { gen_transform : GlobalContextMap.t -> term -> term;
    gen_transform_inductive_decl : mutual_inductive_body -> mutual_inductive_body }.

Class GenTransformId (G : GenTransform) :=
  gen_transform_inductive_decl_id : forall idecl, gen_transform_inductive_decl idecl = idecl.

Section GenTransformEnv.
  Context {GT : GenTransform}.

  Definition gen_transform_constant_decl Σ cb :=
    {| cst_body := option_map (gen_transform Σ) cb.(cst_body) |}.

  Definition gen_transform_decl Σ d :=
    match d with
    | ConstantDecl cb => ConstantDecl (gen_transform_constant_decl Σ cb)
    | InductiveDecl idecl => InductiveDecl (gen_transform_inductive_decl idecl)
    end.

  Definition gen_transform_env Σ :=
    map (on_snd (gen_transform_decl Σ)) Σ.(GlobalContextMap.global_decls).

  Program Fixpoint gen_transform_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
    match Σ with
    | [] => fun _ => []
    | hd :: tl => fun HΣ =>
      let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
      on_snd (gen_transform_decl Σg) hd :: gen_transform_env' tl (fresh_globals_cons_inv HΣ)
    end.
End GenTransformEnv.

Class GenTransformExtends (efl efl' : EEnvFlags) (GT : GenTransform) :=
  wellformed_gen_transform_extends : forall {Σ : GlobalContextMap.t} t,
    forall n, @EWellformed.wellformed efl Σ n t ->
    forall {Σ' : GlobalContextMap.t}, extends Σ Σ' ->
    @wf_glob efl Σ -> @wf_glob efl Σ' ->
    gen_transform Σ t = gen_transform Σ' t.

Class GenTransformWf (efl efl' : EEnvFlags) (GT : GenTransform) :=
{ gen_transform_pre : GlobalContextMap.t -> term -> Prop;
  gtwf_axioms_efl : forall _ : is_true (@has_axioms efl), is_true (@has_axioms efl');
  gen_transform_inductive_decl_wf :
    forall idecl, @wf_minductive efl idecl -> @wf_minductive efl' (gen_transform_inductive_decl idecl);

  gen_transform_wellformed : forall {Σ : GlobalContextMap.t} n t,
    gen_transform_pre Σ t ->
    @wf_glob efl Σ -> @EWellformed.wellformed efl Σ n t ->
    EWellformed.wellformed (efl := efl') (gen_transform_env Σ) n (gen_transform Σ t) }.

Section sec.
  Context {efl efl' gen_transform} {gt : GenTransformExtends efl efl' gen_transform}.

Import EGlobalEnv EExtends.


Lemma wellformed_gen_transform_decl_extends {Σ : GlobalContextMap.t} t :
  @wf_global_decl efl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> @wf_glob efl Σ -> @wf_glob efl Σ' ->
  gen_transform_decl Σ t = gen_transform_decl Σ' t.
Proof.
destruct t => /= //.
intros wf Σ' ext wfΣ wf'. f_equal. unfold gen_transform_constant_decl. f_equal.
destruct (cst_body c) => /= //. f_equal.
now eapply wellformed_gen_transform_extends.
Qed.

Lemma lookup_env_gen_transform_env_Some {Σ : GlobalContextMap.t} kn d :
  @wf_glob efl Σ ->
  lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t,
    [× extends_prefix Σ' Σ, @wf_global_decl efl Σ' d &
      lookup_env (gen_transform_env Σ) kn = Some (gen_transform_decl Σ' d)].
Proof.
  destruct Σ as [Σ ? ? ?]. cbn.
  revert map repr wf.
  induction Σ in |- *; simpl; auto => //.
  intros map repr fr wfg.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-].
    exists (GlobalContextMap.make Σ (fresh_globals_cons_inv fr)). split.
    now eexists [_].
    cbn. now depelim wfg.
    f_equal. symmetry. eapply wellformed_gen_transform_decl_extends. cbn. now depelim wfg.
    eapply (@extends_prefix_extends efl) => //.
    cbn. now exists [a]. now depelim wfg. auto.
  - intros _.
    cbn in IHΣ.
    specialize (IHΣ (EnvMap.of_global_env Σ) (EnvMap.repr_global_env _) (fresh_globals_cons_inv fr)).
    forward IHΣ. now depelim wfg.
    intros hl. specialize (IHΣ hl) as [Σ'' [ext wfgd hl']].
    exists Σ''. split => //.
    * destruct ext as [? ->].
      now exists (a :: x).
    * rewrite -hl'. f_equal.
      clear -wfg gt.
      eapply map_ext_in => kn hin. unfold on_snd. f_equal.
      symmetry. eapply wellformed_gen_transform_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      eapply (@extends_prefix_extends efl) => //.
      cbn. now exists [a]. now depelim wfg.
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
induction Σ; cbn; auto.
case: eqb_spec => //.
Qed.

Lemma lookup_env_gen_transform_env_None {Σ : GlobalContextMap.t} kn :
lookup_env Σ kn = None ->
lookup_env (gen_transform_env Σ) kn = None.
Proof.
cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_gen_transform {Σ : GlobalContextMap.t} kn :
@wf_glob efl Σ ->
lookup_env (gen_transform_env Σ) kn = option_map (gen_transform_decl Σ) (lookup_env Σ kn).
Proof.
intros wf.
destruct (lookup_env Σ kn) eqn:hl.
- eapply lookup_env_gen_transform_env_Some in hl as [Σ' [ext wf' hl']] => /=.
  rewrite hl'. f_equal.
  eapply wellformed_gen_transform_decl_extends; eauto.
  eapply (@extends_prefix_extends efl); auto.
  eapply extends_wf_glob; eauto.
  auto.

- cbn. now eapply lookup_env_gen_transform_env_None in hl.
Qed.


Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Section GenTransformId.

  Context {gid : GenTransformId gen_transform}.

Lemma is_propositional_gen_transform {Σ : GlobalContextMap.t} ind :
  @wf_glob efl Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (gen_transform_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_gen_transform (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //. cbn.
  now rewrite gen_transform_inductive_decl_id.
Qed.

Lemma is_propositional_cstr_gen_transform {Σ : GlobalContextMap.t} ind c :
  @wf_glob efl Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (gen_transform_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_gen_transform (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //=.
  now rewrite gen_transform_inductive_decl_id.
Qed.


Lemma lookup_constructor_gen_transform {Σ : GlobalContextMap.t} {ind c} :
  @wf_glob efl Σ ->
  lookup_constructor Σ ind c = lookup_constructor (gen_transform_env Σ) ind c.
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_gen_transform // /=. destruct lookup_env => // /=.
  destruct g => //=. now rewrite gen_transform_inductive_decl_id.
Qed.

Lemma lookup_projection_gen_transform {Σ : GlobalContextMap.t} {p} :
  @wf_glob efl Σ ->
  lookup_projection Σ p = lookup_projection (gen_transform_env Σ) p.
Proof.
  intros wfΣ. rewrite /lookup_projection.
  rewrite -lookup_constructor_gen_transform //.
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

End GenTransformId.

Lemma wf_mkApps (ha : has_tApp) Σ k f args : reflect (wellformed Σ k f /\ forallb (wellformed Σ k) args) (wellformed Σ k (mkApps f args)).
Proof.
  rewrite wellformed_mkApps //. eapply andP.
Qed.

Lemma extends_cons_inv Σ kn d Σ' :
  extends ((kn, d) :: Σ) Σ' ->
  fresh_global kn Σ ->
  extends Σ Σ'.
Proof.
  intros ext fr kn' d' hl.
  apply ext. rewrite elookup_env_cons_fresh => //.
  intros <-. now apply lookup_env_Some_fresh in hl.
Qed.

Lemma extends_cons_wf Σ a :
  @wf_glob efl (a :: Σ) ->
  extends Σ (a :: Σ).
Proof.
  intros hwf; depelim hwf.
  now apply extends_fresh.
Qed.

Lemma gen_transform_env_extends' {Σ Σ' : GlobalContextMap.t} :
  extends Σ Σ' ->
  @wf_glob efl Σ ->
  @wf_glob efl Σ' ->
  List.map (on_snd (gen_transform_decl Σ)) Σ.(GlobalContextMap.global_decls) =
  List.map (on_snd (gen_transform_decl Σ')) Σ.(GlobalContextMap.global_decls).
Proof.
  intros ext.
  move=> wfΣ wfΣ'.
  assert (Hext : extends Σ Σ); auto. red; tauto.
  generalize wfΣ.
  revert Hext.
  generalize Σ at 1 3 5 6.
  intros [Σ'' ? ? ?]. revert map repr wf.
  induction Σ'' => //; intros map repr wf. cbn.
  intros hin wfg. depelim wfg.
  f_equal.
  2:{ eapply (IHΣ'' (EnvMap.of_global_env Σ'') (EnvMap.repr_global_env _) (fresh_globals_cons_inv wf)).
      now apply extends_cons_inv in hin. now cbn. }
  unfold on_snd. cbn. f_equal.
  eapply wellformed_gen_transform_decl_extends => //. cbn.
  eapply extends_wf_global_decl => //. 2:tea.
  now apply extends_cons_inv in hin.
Qed.

Lemma gen_transform_env_eq (Σ : GlobalContextMap.t) : @wf_glob efl Σ ->
  gen_transform_env Σ = gen_transform_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  unfold gen_transform_env.
  destruct Σ as [Σ ? ? ?]; cbn in *.
  induction Σ in map, repr, wf0, wf |- * => //.
  cbn. f_equal.
  destruct a as [kn d]; unfold on_snd; cbn. f_equal. symmetry.
  eapply wellformed_gen_transform_decl_extends => //. cbn. now depelim wf.
  now apply extends_cons_wf. now depelim wf.
  erewrite <- (IHΣ (EnvMap.of_global_env _) (EnvMap.repr_global_env _) (fresh_globals_cons_inv wf0)).
  set (nΣ := {| GlobalContextMap.global_decls := Σ|}).
  2:now depelim wf.
  symmetry. cbn.
  change Σ with nΣ.(GlobalContextMap.global_decls).
  eapply gen_transform_env_extends'; eauto.
  now apply extends_cons_wf. now depelim wf.
Qed.

Lemma gen_transform_extends {Σ Σ' : GlobalContextMap.t} :
  extends Σ Σ' ->
  @wf_glob efl Σ ->
  @wf_glob efl Σ' ->
  extends (gen_transform_env Σ) (gen_transform_env Σ').
Proof.
  intros ext.
  unfold gen_transform_env.
  intros wf wf'.
  rewrite (gen_transform_env_extends' ext wf wf').
  intros kn d. specialize (ext kn).
  rewrite lookup_env_map_snd.
  destruct (lookup_env) eqn:E; cbn => //.
  intros [= <-].
  specialize (ext _ eq_refl).
  now rewrite lookup_env_map_snd ext /=.
Qed.

Import EWellformed.

Lemma gen_transform_wellformed_irrel {genid : GenTransformId gen_transform} {Σ : GlobalContextMap.t} t :
  @wf_glob efl Σ ->
  forall n, wellformed (efl := efl) Σ n t ->
  wellformed (efl := efl) (gen_transform_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. destruct (cst_body c); cbn; eauto.
  - rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    rewrite gen_transform_inductive_decl_id.
    repeat split; eauto. destruct cstr_as_blocks; rtoProp; repeat split; eauto. solve_all.
  - rewrite /wf_brs. cbn. rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    rewrite gen_transform_inductive_decl_id.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; repeat split; eauto.
    destruct g eqn:hg => /= //.
    now rewrite gen_transform_inductive_decl_id.
Qed.

Lemma gen_transform_wellformed_decl_irrel {genid : GenTransformId gen_transform} {Σ : GlobalContextMap.t} d :
  @wf_glob efl Σ ->
  wf_global_decl (efl:= efl) Σ d ->
  wf_global_decl (efl := efl) (gen_transform_env Σ) d.
Proof.
  intros wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply gen_transform_wellformed_irrel.
Qed.

Context {GTWF : GenTransformWf efl efl' gen_transform}.

Definition Pre_decl Σ d := match d with ConstantDecl cb => match cb.(cst_body) with
  | Some b =>  gen_transform_pre Σ b | _ => True end | _ => True end.

Lemma gen_transform_decl_wf {Σ : GlobalContextMap.t} :
  @wf_glob efl Σ ->
  forall d, @wf_global_decl efl Σ d -> Pre_decl Σ d ->
  wf_global_decl (efl := efl') (gen_transform_env Σ) (gen_transform_decl Σ d).
Proof.
  intros wf d.
  intros hd. intros pre.
  move: hd.
  destruct d => /= //. cbn in pre.
  destruct (cst_body c) => /= //.
  intros hwf. eapply gen_transform_wellformed => //. apply gtwf_axioms_efl. auto.
  destruct m => //. cbn.
  eapply gen_transform_inductive_decl_wf.
Qed.

Lemma fresh_global_gen_transform_env {Σ : GlobalContextMap.t} kn :
  fresh_global kn Σ ->
  fresh_global kn (gen_transform_env Σ).
Proof.
  destruct Σ as [Σ ? ? ?].
  induction Σ in map, repr, wf |- *; auto.
  intros fr; depelim fr. red.
  now eapply Forall_map; cbn.
Qed.

Fixpoint Pre_glob Σ : EnvMap.fresh_globals Σ -> Prop :=
  match Σ with
  | nil => fun _ => True
  | (kn, d) :: Σ => fun HΣ =>
    let Σg := GlobalContextMap.make Σ (fresh_globals_cons_inv HΣ) in
    Pre_decl Σg d /\ Pre_glob Σ (fresh_globals_cons_inv HΣ)
  end.

Import GlobalContextMap (repr, map, global_decls, wf).
Lemma gen_transform_env_wf {Σ : GlobalContextMap.t} :
  @wf_glob efl Σ -> Pre_glob Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf) -> wf_glob (efl := efl') (gen_transform_env Σ).
Proof.
  intros wfg pre.
  rewrite gen_transform_env_eq //.
  destruct Σ as [Σ ? ? ?]. cbn in *. revert pre.
  induction Σ in map0, repr0, wf0, wfg |- *; auto; cbn; constructor; auto.
  - eapply IHΣ. eapply EnvMap.repr_global_env. now depelim wfg.
    destruct a. apply pre.
  - cbn.
    set (Σp := GlobalContextMap.make Σ _).
    specialize (IHΣ (GlobalContextMap.map Σp) (GlobalContextMap.repr Σp) (fresh_globals_cons_inv wf0)).
    rewrite /= -(gen_transform_env_eq Σp) => //. now depelim wfg.
    eapply gen_transform_decl_wf => //. now depelim wfg. cbn. now depelim wfg.
    destruct a. apply pre.
  - cbn.
    set (Σp := {| global_decls := Σ;  map := EnvMap.of_global_env Σ; repr := EnvMap.repr_global_env _;
       wf := (fresh_globals_cons_inv wf0) |}).
    rewrite /= -(gen_transform_env_eq Σp) => //. now depelim wfg.
    eapply fresh_global_gen_transform_env. cbn. now depelim wf0.
Qed.

(* Definition gen_transform_program (p : eprogram_env) :=
  (gen_transform_env p.1, gen_transform p.1 p.2).

Definition gen_transform_program_wf (p : eprogram_env) {hastbox : has_tBox} {hastrel : has_tRel} :
  wf_eprogram_env efl p -> wf_eprogram (efl') (gen_transform_program p).
Proof.
  intros []; split.
  now eapply gen_transform_env_wf.
  cbn. eapply gen_transform_wellformed_irrel => //. now eapply gen_transform_wellformed.
Qed. *)

End sec.
