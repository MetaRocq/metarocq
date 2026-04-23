(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst EnvMap.
From MetaRocq.Erasure Require Import EAst EAstUtils EInduction EArities
    ELiftSubst ESpineView EGlobalEnv EWellformed EEnvMap
    EWcbvEval EEtaExpanded ECSubst EWcbvEvalEtaInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

Section sec.

Variable gen_transform : global_context -> term -> term.

Definition gen_transform_constant_decl Σ cb :=
    {| cst_body := option_map (gen_transform Σ) cb.(cst_body) |}.

Definition gen_transform_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (gen_transform_constant_decl Σ cb)
  | InductiveDecl idecl => d
  end.

Definition gen_transform_env Σ :=
  map (on_snd (gen_transform_decl Σ)) Σ.

Program Fixpoint gen_transform_env' Σ : global_context :=
match Σ with
| [] => []
| hd :: tl =>  on_snd (gen_transform_decl tl) hd :: gen_transform_env' tl
end.

Import EGlobalEnv EExtends.

Lemma extends_lookup_projection {efl : EEnvFlags} {Σ Σ' p} : extends Σ Σ' -> wf_glob Σ' ->
isSome (lookup_projection Σ p) ->
lookup_projection Σ p = lookup_projection Σ' p.
Proof.
intros ext wf; cbn -[lookup_projection].
unfold lookup_projection.
destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
simpl.
rewrite (extends_lookup_constructor wf ext _ _ _ hl) //.
Qed.

Variable efl' : EEnvFlags.
Variable efl : EEnvFlags.

Hypothesis wellformed_gen_transform_extends : forall {Σ : global_context} t,
forall n, EWellformed.wellformed Σ n t ->
forall {Σ' : global_context}, extends Σ Σ' -> wf_glob Σ -> wf_glob Σ' ->
gen_transform Σ t = gen_transform Σ' t.

Lemma wellformed_gen_transform_decl_extends {Σ : global_context} t :
wf_global_decl Σ t ->
forall {Σ' : global_context}, extends Σ Σ' -> wf_glob Σ -> wf_glob Σ' ->
gen_transform_decl Σ t = gen_transform_decl Σ' t.
Proof.
destruct t => /= //.
intros wf Σ' ext wfΣ wf'. f_equal. unfold gen_transform_constant_decl. f_equal.
destruct (cst_body c) => /= //. f_equal.
now eapply wellformed_gen_transform_extends.
Qed.

Lemma lookup_env_gen_transform_env_Some {Σ : global_context} kn d :
wf_glob Σ ->
lookup_env Σ kn = Some d ->
∑ Σ' : global_context,
  [× extends_prefix Σ' Σ, wf_global_decl Σ' d &
    lookup_env (gen_transform_env Σ) kn = Some (gen_transform_decl Σ' d)].
Proof.
induction Σ in |- *; simpl; auto => //.
intros wfg.
case: eqb_specT => //.
- intros ->. cbn. intros [= <-]. exists Σ. split.
  now eexists [_].
  cbn. now depelim wfg.
  f_equal. symmetry. eapply wellformed_gen_transform_decl_extends. cbn. now depelim wfg.
  eapply extends_prefix_extends => //.
  cbn. now exists [a]. now depelim wfg. auto.
- intros _.
  cbn in IHΣ. forward IHΣ. now depelim wfg.
  intros hl. specialize (IHΣ hl) as [Σ'' [ext wfgd hl']].
  exists Σ''. split => //.
  * destruct ext as [? ->].
    now exists (a :: x).
  * rewrite -hl'. f_equal.
    clear -wfg wellformed_gen_transform_extends.
    eapply map_ext_in => kn hin. unfold on_snd. f_equal.
    symmetry. eapply wellformed_gen_transform_decl_extends => //. cbn.
    eapply lookup_env_In in hin. 2:now depelim wfg.
    depelim wfg. eapply lookup_env_wellformed; tea.
    eapply extends_prefix_extends => //.
    cbn. now exists [a]. now depelim wfg.
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
induction Σ; cbn; auto.
case: eqb_spec => //.
Qed.

Lemma lookup_env_gen_transform_env_None {Σ : global_context} kn :
lookup_env Σ kn = None ->
lookup_env (gen_transform_env Σ) kn = None.
Proof.
cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_gen_transform {Σ : global_context} kn :
wf_glob Σ ->
lookup_env (gen_transform_env Σ) kn = option_map (gen_transform_decl Σ) (lookup_env Σ kn).
Proof.
intros wf.
destruct (lookup_env Σ kn) eqn:hl.
- eapply lookup_env_gen_transform_env_Some in hl as [Σ' [ext wf' hl']] => /=.
  rewrite hl'. f_equal.
  eapply wellformed_gen_transform_decl_extends; eauto.
  eapply extends_prefix_extends; auto.
  eapply extends_wf_glob; eauto.
  auto.

- cbn. now eapply lookup_env_gen_transform_env_None in hl.
Qed.


Lemma is_propositional_gen_transform {Σ : global_context} ind :
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (gen_transform_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_gen_transform (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma is_propositional_cstr_gen_transform {Σ : global_context} ind c :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (gen_transform_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_gen_transform (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma lookup_constructor_gen_transform {Σ : global_context} {ind c} :
  wf_glob Σ ->
  lookup_constructor Σ ind c = lookup_constructor (gen_transform_env Σ) ind c.
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_gen_transform // /=. destruct lookup_env => // /=.
  destruct g => //.
Qed.

Lemma lookup_projection_gen_transform {Σ : global_context} {p} :
  wf_glob Σ ->
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
  wf_glob (a :: Σ) ->
  extends Σ (a :: Σ).
Proof.
  intros hwf; depelim hwf.
  now apply extends_fresh.
Qed.

Lemma gen_transform_env_extends' {Σ Σ' : global_context} :
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  List.map (on_snd (gen_transform_decl Σ)) Σ =
  List.map (on_snd (gen_transform_decl Σ')) Σ.
Proof.
  intros ext.
  move=> wfΣ wfΣ'.
  assert (Hext : extends Σ Σ); auto. red; tauto.
  generalize wfΣ.
  revert Hext.
  generalize Σ at 1 3 5 6. intros Σ''.
  induction Σ'' => //. cbn.
  intros hin wfg. depelim wfg.
  f_equal.
  2:{ eapply IHΣ'' => //. now apply extends_cons_inv in hin. }
  unfold on_snd. cbn. f_equal.
  eapply wellformed_gen_transform_decl_extends => //. cbn.
  eapply extends_wf_global_decl => //. 2:tea.
  now apply extends_cons_inv in hin.
Qed.

Lemma gen_transform_env_eq (Σ : global_context) : wf_glob Σ -> gen_transform_env Σ = gen_transform_env' Σ.
Proof.
  intros wf.
  unfold gen_transform_env.
  induction Σ => //.
  cbn. f_equal.
  destruct a as [kn d]; unfold on_snd; cbn. f_equal. symmetry.
  eapply wellformed_gen_transform_decl_extends => //. cbn. now depelim wf.
  now apply extends_cons_wf. now depelim wf.
  erewrite <- IHΣ.
  2:now depelim wf.
  symmetry. eapply gen_transform_env_extends'; eauto.
  now apply extends_cons_wf. now depelim wf.
Qed.

Variable Pre : global_context -> term -> Prop.

Hypothesis gen_transform_wellformed : forall {Σ : global_context} n t,
  has_tBox -> has_tRel -> Pre Σ t ->
  @wf_glob efl Σ -> @EWellformed.wellformed efl Σ n t ->
  EWellformed.wellformed (efl := efl') Σ n (gen_transform Σ t).

Import EWellformed.

Lemma gen_transform_wellformed_irrel {Σ : global_context} t :
  wf_glob Σ ->
  forall n, wellformed (efl := efl') Σ n t ->
  wellformed (efl := efl') (gen_transform_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. destruct (cst_body c); cbn; eauto.
  - rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    repeat split; eauto. destruct cstr_as_blocks; rtoProp; repeat split; eauto. solve_all.
  - rewrite /wf_brs; cbn. rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_gen_transform //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; repeat split; eauto.
    destruct g eqn:hg => /= //.
Qed.

Lemma gen_transform_wellformed_decl_irrel {Σ : global_context} d :
  wf_glob Σ ->
  wf_global_decl (efl:= efl') Σ d ->
  wf_global_decl (efl := efl') (gen_transform_env Σ) d.
Proof.
  intros wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply gen_transform_wellformed_irrel.
Qed.

Hypothesis axioms_efl : forall _ : is_true (@has_axioms efl), is_true (@has_axioms efl').
Hypothesis cstrs_efl : forall _ : is_true (@has_cstr_params efl), is_true (@has_cstr_params efl').

Definition Pre_decl Σ d := match d with ConstantDecl cb => match cb.(cst_body) with Some b => Pre Σ b | _ => True end | _ => True end.

Lemma gen_transform_decl_wf {Σ : global_context} :
  has_tBox -> has_tRel -> wf_glob Σ ->
  forall d, wf_global_decl Σ d -> Pre_decl Σ d ->
  wf_global_decl (efl := efl') (gen_transform_env Σ) (gen_transform_decl Σ d).
Proof.
  intros hasb hasr wf d.
  intros hd. intros pre.
  eapply gen_transform_wellformed_decl_irrel; tea; eauto.
  move: hd.
  destruct d => /= //. cbn in pre.
  destruct (cst_body c) => /= //.
  intros hwf. eapply gen_transform_wellformed => //. auto.
  destruct efl => //; eauto. destruct m => //. cbn. unfold wf_minductive.
  cbn. move/andP => [] hp //. rtoProp. solve_all.
   eapply orb_true_iff. eapply orb_true_iff in hp as []; eauto.
   left. eapply cstrs_efl. now rewrite H.
Qed.

Lemma fresh_global_gen_transform_env {Σ : global_context} kn :
  fresh_global kn Σ ->
  fresh_global kn (gen_transform_env Σ).
Proof.
  induction 1; cbn; constructor; auto.
  now eapply Forall_map; cbn.
Qed.

Fixpoint Pre_glob Σ :=
  match Σ with
  | nil => True
  | (kn, d) :: Σ => Pre_decl Σ d /\ Pre_glob Σ
  end.

Lemma gen_transform_env_wf {Σ : global_context} :
  has_tBox -> has_tRel -> Pre_glob Σ ->
  wf_glob Σ -> wf_glob (efl := efl') (gen_transform_env Σ).
Proof.
  intros hasb hasrel pre.
  intros wfg. rewrite gen_transform_env_eq //.
  induction wfg; cbn; constructor; invs pre; auto.
  - rewrite /= -(gen_transform_env_eq Σ) => //. eauto.
    eapply gen_transform_decl_wf => //.
  - rewrite /= -(gen_transform_env_eq Σ) //.
    now eapply fresh_global_gen_transform_env.
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
