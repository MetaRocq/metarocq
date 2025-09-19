(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool Utf8 CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Set Warnings "-notation-overridden".
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnOne PCUICCases PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICCasesContexts PCUICTactics
     PCUICSigmaCalculus PCUICClosed PCUICClosedTyp PCUICContexts PCUICSubstitution
     PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICEquality
     PCUICWeakeningConv PCUICWeakeningTyp PCUICCumulativity
     PCUICUnivSubst PCUICUnivSubstitutionTyp PCUICGlobalEnv PCUICTyping PCUICGeneration
     PCUICConversion PCUICOnFreeVars
     PCUICValidity PCUICArities PCUICInversion
     PCUICCases PCUICWellScopedCumulativity PCUICSpine PCUICSR
     PCUICSafeLemmata PCUICInductives PCUICInductiveInversion.
From MetaRocq.PCUIC Require Import PCUICExpandLets.
Set Warnings "+notation-overridden".

Import MRMonadNotation.

Implicit Types (cf : checker_flags) (Σ : global_env_ext). (* Use {cf} to parameterize by checker_flags where needed *)

Set Default Proof Using "Type*".

(** Translation which expands the lets in constructor arguments contexts and the correspomding
  branches of pattern-matchings, so that let-expansion becomes unnecessary on the resulting terms.

  The proof of correctness is complicated by the fact that the translation is valid only on well-scoped
  terms, at the lowest level, so we carry around `on_free_vars` hypotheses everywhere. Reduction is
  only preserved when we are translating well-typed terms, as it relies on even stronger invariants on the
  representation of cases. Finally, the let-expansion of constructor's argument contexts is shown to
  preserve positivity and the cumulativity relation for cumulative inductive types, which is not entirely
  trivial. *)

(** Source = PCUIC, Target = Rocq *)
Module S := PCUICAst.
Module SE := PCUICEnvironment.
Module ST := PCUICTyping.
Module T := S.
Module TT := ST.

Module SL := PCUICLiftSubst.
Module TL := SL.


Ltac solve_list :=
  rewrite !map_map_compose ?compose_on_snd ?compose_map_def;
  try rewrite !length_map;
  try solve_all; try typeclasses eauto with core.

Lemma mapOne {X Y} (f:X->Y) x:
  map f [x] = [f x].
Proof.
  reflexivity.
Qed.

Lemma trans_local_app Γ Δ : trans_local (Γ ,,, Δ) = trans_local Γ ,,, trans_local Δ.
Proof.
  now rewrite /trans_local map_app.
Qed.

Lemma forget_types_map_context {term term'} (f : term' -> term) ctx :
  forget_types (map_context f ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_map_context.
Qed.

Lemma All_fold_map_context (P : context -> context_decl -> Type) (f : term -> term) ctx :
  All_fold P (map_context f ctx) <~> All_fold (fun Γ d => P (map_context f Γ) (map_decl f d)) ctx.
Proof.
  induction ctx.
  - split; constructor.
  - cbn. split; intros H; depelim H; constructor; auto; now apply IHctx.
Qed.

Lemma on_decl_trans_on_free_vars_decl (Γ : context) n (d : context_decl) :
  ondecl
    (λ t : term,
     on_free_vars (closedP (#|Γ| + n) xpredT) (trans t)) d ->
  on_free_vars_decl
    (shiftnP #|map_context trans Γ| (closedP n xpredT)) (trans_decl d).
Proof.
  intros []. unfold on_free_vars_decl, test_decl.
  destruct d as [na [b|] ty]; cbn in * => //;
     rewrite map_context_length shiftnP_closedP shiftnP_xpredT //.
  apply/andP. split; auto.
Qed.

Lemma All_fold_closed_on_free_vars_ctx n ctx :
  All_fold (λ Γ : context, ondecl (λ t : term,
        on_free_vars (closedP (#|Γ| + n) xpredT)
      (trans t))) ctx ->
  on_free_vars_ctx (closedP n xpredT) (map_context trans ctx).
Proof.
  intros af.
  eapply on_free_vars_ctx_All_fold.
  eapply All_fold_map_context, All_fold_impl; tea => ctx' d; cbn.
  now intros; eapply on_decl_trans_on_free_vars_decl.
Qed.

Definition plengths :=
    (@context_assumptions_subst_context,
    @context_assumptions_app,
    @context_assumptions_subst_instance, @context_assumptions_lift_context,
     @expand_lets_ctx_length, @subst_context_length,
    @subst_instance_length, @expand_lets_k_ctx_length, @inds_length, @lift_context_length,
    @length_app, @List.length_rev, @extended_subst_length, @reln_length,
    Nat.add_0_r, @app_nil_r,
    @length_map, @mapi_length, @mapi_rec_length,
    @fold_context_k_length, @cofix_subst_length, @fix_subst_length,
    @smash_context_length, @arities_context_length, @context_assumptions_map).

(* duplicated *)
Lemma is_assumption_context_spec Γ :
  reflect (PCUICLiftSubst.assumption_context Γ) (is_assumption_context Γ).
Proof.
 induction Γ; cbn.
 - econstructor. constructor.
 - destruct a as [na [b|] ty]; cbn.
   + constructor. intros ass; depelim ass.
   + elim: IHΓ; constructor; pcuic. now constructor.
     apply n; now depelim H.
Qed.

(*duplicated *)
Lemma assumption_context_assumptions Γ :
  assumption_context Γ ->
  context_assumptions Γ = #|Γ|.
Proof.
  induction 1; cbn; auto. congruence.
Qed.

Lemma bcontext_trans_length p br : #|bcontext (trans_branch p br)| = context_assumptions (bcontext br).
Proof.
  rewrite /trans_branch.
  elim: is_assumption_context_spec => ass.
  rewrite assumption_context_assumptions //.
  cbn. rewrite smash_context_length //.
Qed.

Lemma trans_on_free_vars P t :
  on_free_vars P t -> on_free_vars P (trans t).
Proof.
  revert P t. eapply term_on_free_vars_ind; cbn; auto;
    lazymatch goal with |- context [case_info] => idtac | _ => solve_all end.
  - intros; rtoProp; intuition auto.
    * solve_all.
    * now rewrite map_context_length.
    * rewrite length_map.
      rewrite test_context_k_closed_on_free_vars_ctx.
      now eapply All_fold_closed_on_free_vars_ctx.
    * eapply All_forallb, All_map, All_map, All_impl; tea; cbv beta.
      intros br [hctx ihctx hb ihb]. len.
      rewrite test_context_k_closed_on_free_vars_ctx.
      rewrite /trans_branch.
      elim: is_assumption_context_spec => isass.
      { cbn [map_branch bcontext]. apply/andP; split.
        now eapply All_fold_closed_on_free_vars_ctx.
        cbn. len. }
      cbn -[on_free_vars_ctx].
      rewrite on_free_vars_ctx_smash //.
      now eapply All_fold_closed_on_free_vars_ctx.
      rewrite /=.
      eapply on_free_vars_expand_lets_k. now len.
      eapply on_free_vars_ctx_subst_context0.
      rewrite !plengths.
      eapply All_fold_closed_on_free_vars_ctx in ihctx.
      rewrite -> closedP_shiftnP in ihctx.
      rewrite /id. rewrite on_free_vars_ctx_subst_instance.
      eapply on_free_vars_ctx_impl; tea.
      { unfold shiftnP. intros i. rewrite orb_false_r.
        move/Nat.ltb_lt => hlt. now apply/orP; left; eapply Nat.ltb_lt. }
      solve_all.
      rewrite !plengths. now apply ihb.
  - unfold test_def. solve_all. cbn. now len in b1.
  - unfold test_def. solve_all. cbn. now len in b1.
Qed.

Lemma on_free_vars_ctx_trans k ctx :
  on_free_vars_ctx (closedP k xpredT) ctx ->
  on_free_vars_ctx (closedP k xpredT) (map_context trans ctx).
Proof.
  intros H; apply on_free_vars_ctx_All_fold in H.
  eapply All_fold_closed_on_free_vars_ctx.
  eapply All_fold_impl; tea; cbn.
  intros ? ? h.
  destruct x as [na [b|] ty]; cbn in *;
  constructor; cbn; (move/andP: h => /= // || move: h) ;
  rewrite ?shiftnP_closedP ?shiftnP_xpredT //;
  intros; try now eapply trans_on_free_vars.
Qed.

Lemma trans_on_free_vars_ctx k ctx :
  on_free_vars_ctx (shiftnP k xpred0) ctx ->
  on_free_vars_ctx (shiftnP k xpred0) (map_context trans ctx).
Proof.
  intros hctx.
  rewrite -closedP_shiftnP. eapply on_free_vars_ctx_trans.
  rewrite closedP_shiftnP //.
Qed.

Lemma closedP_mon n n' P i : n <= n' -> closedP n P i -> closedP n' P i.
Proof.
  intros hn; rewrite /closedP.
  repeat nat_compare_specs => //.
Qed.

Ltac len := rewrite !plengths.

Lemma trans_lift (t : S.term) P n k :
  on_free_vars P t ->
  trans (S.lift n k t) = T.lift n k (trans t).
Proof.
  intros onfvs.
  revert P t onfvs k.
  apply: term_on_free_vars_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - f_equal; auto.
    rewrite /T.map_predicate_k /id /PCUICAst.map_predicate /= /=.
    f_equal. autorewrite with map; solve_all.
    rewrite map_context_length. solve_all.
    rewrite !map_map_compose.
    eapply All_map_eq, All_impl; tea; cbv beta => [br [hbctx ihbctx hb ihb]].
    rewrite /trans_branch /T.map_branch_k.
    elim: is_assumption_context_spec => isass.
    { cbn. rewrite /map_branch /=. f_equal. len. eapply ihb. }
    cbn -[expand_lets].
    len. rewrite (Nat.add_comm (context_assumptions _) k).
    f_equal. rewrite ihb.
    relativize (context_assumptions _).
    erewrite <- expand_lets_lift. 2:len. 2:reflexivity.
    rewrite !plengths.
    rewrite /id. f_equal.
    rewrite distr_lift_subst_context.
    rewrite !plengths. f_equal.
    rewrite map_rev. f_equal. solve_all.
    rewrite PCUICClosed.closed_ctx_lift //.
    rewrite closedn_ctx_on_free_vars.
    rewrite on_free_vars_ctx_subst_instance.
    eapply on_free_vars_ctx_trans. eapply on_free_vars_ctx_impl; tea.
    intros i. eapply closedP_mon. lia.
  - f_equal. solve_all.
  - f_equal; red in X, X0; solve_all.
  - f_equal; solve_all.
Qed.

Definition on_fst {A B C} (f:A->C) (p:A×B) := (f p.1, p.2).

Definition trans_def (decl:def PCUICAst.term) : def term.
Proof.
  destruct decl.
  constructor.
  - exact dname.
  - exact (trans dtype).
  - exact (trans dbody).
  - exact rarg.
Defined.

Lemma trans_global_ext_levels Σ:
  S.global_ext_levels Σ = T.global_ext_levels (trans_global Σ).
Proof. reflexivity. Qed.

Lemma trans_global_ext_constraints Σ :
  S.global_ext_constraints Σ = T.global_ext_constraints (trans_global Σ).
Proof. reflexivity. Qed.

Lemma trans_mem_level_set l Σ:
  LevelSet.mem l (S.global_ext_levels Σ) ->
  LevelSet.mem l (T.global_ext_levels (trans_global Σ)).
Proof. auto. Qed.

Lemma trans_in_level_set l Σ :
  LevelSet.In l (S.global_ext_levels Σ) ->
  LevelSet.In l (T.global_ext_levels (trans_global Σ)).
Proof. auto. Qed.

Lemma trans_lookup (Σ : global_env) cst :
  lookup_env (trans_global_env Σ) cst = option_map trans_global_decl (SE.lookup_env Σ cst).
Proof.
  cbn in *.
  destruct Σ as [univs Σ].
  induction Σ.
  - reflexivity.
  - cbn. case: eqb_spec; intros e; subst.
    + destruct a; auto.
    + now rewrite IHΣ.
Qed.

Lemma trans_declared_constant {cf} (Σ:global_env) {wfΣ : wf Σ} cst decl:
  S.declared_constant Σ cst decl ->
  T.declared_constant (trans_global_env Σ) cst (trans_constant_body decl).
Proof.
  intro H. unshelve eapply declared_constant_to_gen in H; eauto.
  unshelve eapply declared_constant_from_gen.
  move:H. unfold T.declared_constant, T.declared_constant_gen.
  rewrite trans_lookup.
  unfold S.declared_constant.
  intros ->.
  reflexivity.
Qed.

Lemma trans_constraintSet_in x Σ:
  UnivConstraintSet.In x (S.global_ext_constraints Σ) ->
  UnivConstraintSet.In x (T.global_ext_constraints (trans_global Σ)).
Proof.
  rewrite trans_global_ext_constraints.
  trivial.
Qed.

Lemma trans_consistent_instance_ext {cf} Σ decl u:
  S.consistent_instance_ext Σ decl u ->
  T.consistent_instance_ext (trans_global Σ) decl u.
Proof. auto. Qed.

Lemma trans_declared_inductive {cf} (Σ:global_env) {wfΣ : wf Σ} ind mdecl idecl:
  S.declared_inductive Σ ind mdecl idecl ->
  T.declared_inductive (trans_global_env Σ) ind (trans_minductive_body mdecl)
   (trans_one_ind_body mdecl (inductive_ind ind) idecl).
Proof.
  intro H. unshelve eapply declared_inductive_to_gen in H; eauto.
  unshelve eapply declared_inductive_from_gen.
  move:H. intros [].
  split.
  - unfold T.declared_minductive, T.declared_minductive_gen, S.declared_minductive in *.
    now rewrite trans_lookup H.
  - cbn. now rewrite nth_error_mapi H0 /=.
Qed.

Lemma trans_declared_constructor {cf} (Σ:global_env) {wfΣ : wf Σ} c mdecl idecl cdecl :
  let ind := (inductive_ind (fst c)) in
  S.declared_constructor Σ c mdecl idecl cdecl ->
  T.declared_constructor (trans_global_env Σ) c (trans_minductive_body mdecl) (trans_one_ind_body mdecl ind idecl)
    (trans_constructor_body ind mdecl cdecl).
Proof.
  intros ind [].
  split.
  - now apply trans_declared_inductive.
  - now apply map_nth_error.
Qed.

Lemma trans_mkApps t args:
  trans (PCUICAst.mkApps t args) =
  mkApps (trans t) (map trans args).
Proof.
  induction args in t |- *.
  - reflexivity.
  - cbn [map].
    cbn.
    rewrite IHargs.
    reflexivity.
Qed.

Lemma trans_decl_type decl:
  trans (decl_type decl) =
  decl_type (trans_decl decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma expand_lets_subst_comm Γ k s :
  expand_lets (subst_context s k Γ) ∘ subst s (#|Γ| + k) =1
  subst s (context_assumptions Γ + k) ∘ expand_lets Γ.
Proof.
  unfold expand_lets, expand_lets_k; simpl; intros x. len.
  rewrite !PCUICSigmaCalculus.subst_extended_subst.
  rewrite distr_subst. rewrite Nat.add_comm; f_equal; len.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma subst_context_subst_context s k s' Γ :
  subst_context s k (subst_context s' 0 Γ) =
  subst_context (map (subst s k) s') 0 (subst_context s (k + #|s'|) Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto;
    rewrite !subst_context_snoc /= /subst_decl /map_decl /=; f_equal;
    auto; f_equal; len;
  rewrite distr_subst_rec; lia_f_equal.
Qed.

Lemma trans_subst p q xs k t :
  on_free_vars p t ->
  forallb (on_free_vars q) xs ->
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  intros onfvs; revert p t onfvs k.
  apply: term_on_free_vars_ind; intros; cbn.
  all: cbn;try congruence.
  - destruct Nat.leb;trivial.
    rewrite nth_error_map.
    destruct nth_error eqn:hnth;cbn.
    2:now rewrite length_map.
    rewrite (trans_lift _ q) //.
    eapply nth_error_forallb in H0; tea.
  - f_equal.
    do 2 rewrite map_map.
    apply All_map_eq.
    solve_all. rewrite b //. solve_all.
  - rewrite H0 // H2 //.
  - rewrite H0 // H2 //.
  - rewrite H0 // H2 // H4 //.
  - rewrite H0 // H2 //.
  - f_equal; trivial.
    rewrite /= /id /T.map_predicate_k /map_predicate_k /map_predicate /=.
    f_equal; solve_all.
    * rewrite b //. solve_all.
    * rewrite H1 //. solve_all. now rewrite map_context_length.
    * rewrite H3 //.
    * rewrite /trans_branch; rewrite !map_map_compose.
      eapply All_map_eq, All_impl; tea; cbv beta; intros.
      destruct X3 as [hctx ihctx hb ihb].
      rewrite /T.map_branch_k /=.
      elim: is_assumption_context_spec => isass.
      { rewrite /map_branch /= ihb //. f_equal.
        now len. }
      f_equal; auto.
      len => /=.
      rewrite ihb // /id.
      replace (context_assumptions (map_context trans (bcontext x))) with
        (context_assumptions ((subst_context (List.rev (map trans (pparams pred))) 0
        (map_context trans (bcontext x))@[puinst pred]))). 2:now len.
      cbn.
      relativize (context_assumptions (bcontext x)).
      erewrite <- expand_lets_subst_comm. f_equal. 2:now len.
      2:now len.
      rewrite subst_context_subst_context. f_equal.
      rewrite map_rev; f_equal. solve_all. rewrite b //. solve_all. len.
      rewrite PCUICSpine.closed_ctx_subst //.
      eapply on_free_vars_ctx_trans in hctx.
      rewrite closedn_ctx_on_free_vars.
      rewrite on_free_vars_ctx_subst_instance.
      eapply on_free_vars_ctx_impl; tea.
      intros. eapply closedP_mon; tea. lia.
  - f_equal. rewrite H0 //.
  - f_equal. rewrite !map_map_compose. red in X, X0.
    repeat toAll. eapply All_map_eq, All_impl; tea.
    cbn. rtoProp; intuition auto.
    unfold map_def; cbn. f_equal. rewrite a //. solve_all.
    rewrite b1 //. solve_all. cbn. now len.
  - f_equal. rewrite !map_map_compose.
    repeat toAll. eapply All_map_eq, All_impl; tea.
    cbn. rtoProp; intuition auto.
    unfold map_def; cbn. f_equal. rewrite a //. solve_all.
    rewrite b //. solve_all. now len.
  - f_equal. solve_all. eapply b. solve_all.
Qed.

Lemma trans_subst_ctx (Γ : context) xs k t :
  on_free_vars (shiftnP (#|xs| + #|Γ|) xpred0) t ->
  forallb (on_free_vars (shiftnP #|Γ| xpred0)) xs ->
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  intros ont onxs.
  now erewrite trans_subst; tea.
Qed.

Lemma trans_subst10 u p q B :
  on_free_vars p B ->
  on_free_vars q u ->
  trans (S.subst1 u 0 B) =
  T.subst10 (trans u) (trans B).
Proof.
  unfold S.subst1. intros onB onu.
  rewrite (trans_subst p q) //. cbn. now rewrite onu.
Qed.

Lemma trans_subst_instance u t:
  trans (subst_instance u t) =
  subst_instance u (trans t).
Proof.
  induction t in u |- * using PCUICInduction.term_forall_list_ind;cbn;auto;try congruence.
  - do 2 rewrite map_map.
    f_equal.
    apply All_map_eq. solve_all.
  - red in X, X0.
    f_equal.
    + rewrite /map_predicate /=. f_equal. solve_all. solve_all.
    + solve_all.
    + rewrite !map_map_compose. eapply All_map_eq, All_impl; tea; cbv beta.
      intros ? []. rewrite /trans_branch /= /map_branch /= /id.
      elim: is_assumption_context_spec => isass.
      { f_equal. cbn. now rewrite e. }
      f_equal.
      rewrite PCUICUnivSubstitutionConv.subst_instance_expand_lets e.
      rewrite PCUICUnivSubstitutionConv.subst_instance_subst_context. f_equal.
      f_equal. rewrite [_@[u]]map_rev. f_equal. solve_all.
      solve_all. rewrite [_@[u]] map_map_compose.
      setoid_rewrite compose_map_decl.
      setoid_rewrite PCUICUnivSubstitutionConv.subst_instance_two.
      clear -a. rewrite [_@[_]]map_map_compose.
      rewrite map_map_compose. solve_all.
  - f_equal.
    unfold tFixProp in X. rewrite !map_map_compose. solve_all.
  - f_equal.
    unfold tFixProp in X.
    rewrite !map_map_compose. autorewrite with map. solve_all_one.
  - f_equal. solve_all.
Qed.

Lemma trans_subst_instance_ctx Γ u :
  trans_local Γ@[u] = (trans_local Γ)@[u].
Proof.
  rewrite /subst_instance /= /trans_local /SE.subst_instance_context /subst_instance_context
    /map_context.
  rewrite !map_map_compose. apply map_ext.
  move => [na [b|] ty]; cbn;
  rewrite /trans_decl /map_decl /=; f_equal; cbn;
  now rewrite trans_subst_instance.
Qed.

Lemma trans_cst_type decl:
  trans (SE.cst_type decl) =
  cst_type (trans_constant_body decl).
Proof.
  reflexivity.
Qed.

Lemma trans_ind_type mdecl i idecl:
  trans (SE.ind_type idecl) =
  ind_type (trans_one_ind_body mdecl i idecl).
Proof.
  reflexivity.
Qed.

Lemma trans_dtype decl:
  trans (dtype decl) =
  dtype (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_dbody decl:
  trans (dbody decl) =
  dbody (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_inds ind u mdecl :
  map trans (PCUICAst.inds (inductive_mind ind) u (SE.ind_bodies mdecl)) =
  inds (inductive_mind ind) u (ind_bodies (trans_minductive_body mdecl)).
Proof.
  rewrite PCUICCases.inds_spec inds_spec.
  rewrite map_rev map_mapi. simpl.
  f_equal. rewrite mapi_mapi. apply mapi_ext => n //.
Qed.

Lemma trans_declared_projection {cf} Σ {wfΣ : wf Σ} p mdecl idecl cdecl pdecl :
  let ind := (inductive_ind p.(proj_ind)) in
  S.declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  T.declared_projection (trans_global Σ).1 p (trans_minductive_body mdecl) (trans_one_ind_body mdecl ind idecl)
    (trans_constructor_body ind mdecl cdecl) (trans_projection_body pdecl).
Proof.
  intros ind []. split; [|split].
  - now apply trans_declared_constructor.
  - unfold on_snd.
    destruct H0.
    destruct pdecl, p.
    cbn in *.
    now apply map_nth_error.
  - now destruct mdecl;cbn in *.
Qed.

Lemma inv_opt_monad {X Y Z} (f:option X) (g:X->option Y) (h:X->Y->option Z) c:
  (x <- f;;
  y <- g x;;
  h x y) = Some c ->
  exists a b, f = Some a /\
  g a = Some b /\ h a b = Some c.
Proof.
  intros H.
  destruct f eqn: ?;cbn in *;try congruence.
  destruct (g x) eqn: ?;cbn in *;try congruence.
  do 2 eexists.
  repeat split;eassumption.
Qed.

Lemma trans_destr_arity x:
  destArity [] (trans x) =
  option_map (fun '(xs,u) => (map trans_decl xs,u)) (destArity [] x).
Proof.
  set xs := (@nil context_decl). unfold xs at 1.
  replace (@nil context_decl) with (map trans_decl xs) at 1 by (now subst). clearbody xs.
  induction x in xs |- *;cbn;trivial;unfold snoc.
  - rewrite <- IHx2.
    reflexivity.
  - rewrite <- IHx3.
    reflexivity.
Qed.

Lemma trans_mkProd_or_LetIn a t:
  trans (SE.mkProd_or_LetIn a t) =
  mkProd_or_LetIn (trans_decl a) (trans t).
Proof.
  destruct a as [? [] ?];cbn;trivial.
Qed.

Lemma trans_it_mkProd_or_LetIn xs t:
  trans (SE.it_mkProd_or_LetIn xs t) =
  it_mkProd_or_LetIn (map trans_decl xs) (trans t).
Proof.
  induction xs in t |- *;simpl;trivial.
  rewrite IHxs.
  f_equal.
  apply trans_mkProd_or_LetIn.
Qed.


Lemma trans_nth n l x : trans (nth n l x) = nth n (List.map trans l) (trans x).
Proof.
  induction l in n |- *; destruct n; trivial.
  simpl in *. congruence.
Qed.

Lemma trans_isLambda t :
  T.isLambda (trans t) = S.isLambda t.
Proof.
  destruct t; cbnr.
Qed.

Lemma trans_unfold_fix p mfix idx narg fn :
  on_free_vars p (tFix mfix idx) ->
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros onfvs [= <- <-]. simpl.
  repeat f_equal.
  rewrite (trans_subst (shiftnP #|mfix| p) p).
  unshelve eapply nth_error_forallb in onfvs; tea. now move/andP: onfvs => //.
  eapply (on_free_vars_fix_subst _ _ idx). tea.
  f_equal. clear Hdef. simpl.
  unfold fix_subst. rewrite length_map.
  revert onfvs.
  generalize mfix at 1 2 3 5.
  induction mfix; trivial.
  simpl; intros mfix' hfvs. f_equal.
  now eapply IHmfix.
Qed.

Lemma trans_unfold_cofix p mfix idx narg fn :
  on_free_vars p (tCoFix mfix idx) ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros onfvs [= <- <-]. simpl.
  repeat f_equal.
  rewrite (trans_subst (shiftnP #|mfix| p) p).
  unshelve eapply nth_error_forallb in onfvs; tea. now move/andP: onfvs => //.
  eapply (on_free_vars_cofix_subst _ _ idx). tea.
  f_equal. clear Hdef. simpl.
  unfold cofix_subst. rewrite length_map.
  revert onfvs.
  generalize mfix at 1 2 3 5.
  induction mfix; trivial.
  simpl; intros mfix' hfvs. f_equal.
  now eapply IHmfix.
Qed.

Lemma trans_is_constructor:
  forall (args : list S.term) (narg : nat),
    is_constructor narg args = true -> is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold is_constructor.
  rewrite nth_error_map //. destruct nth_error => //. simpl. intros.
  unfold isConstruct_app, decompose_app in *.
  destruct (decompose_app_rec t []) eqn:da. simpl in H.
  destruct t0 => //.
  apply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps /=.
  rewrite decompose_app_rec_mkApps //.
Qed.

Lemma refine_red1_r Σ Γ t u u' : u = u' -> red1 Σ Γ t u -> red1 Σ Γ t u'.
Proof.
  intros ->. trivial.
Qed.

Lemma refine_red1_Γ Σ Γ Γ' t u : Γ = Γ' -> red1 Σ Γ t u -> red1 Σ Γ' t u.
Proof.
  intros ->. trivial.
Qed.

Lemma forallb_mapi_ext {A B} (p : A -> bool) (l : list A) {f g : nat -> A -> B} :
  forallb p l ->
  (forall i x, p x -> f i x = g i x) ->
  mapi f l = mapi g l.
Proof.
  unfold mapi; generalize 0. induction l; cbn; auto.
  move=> n /andP[] pa pl hf.
  rewrite hf //. f_equal. apply IHl => //.
Qed.

Lemma trans_fix_context p mfix idx :
  on_free_vars p (tFix mfix idx) ->
  map trans_decl (SE.fix_context mfix) =
  fix_context (map (map_def trans trans) mfix).
Proof.
  unfold trans_local.
  unfold fix_context.
  rewrite map_rev map_mapi.
  cbn. move=> onfvs. f_equal.
  rewrite mapi_map. eapply forallb_mapi_ext; tea => i x hx.
  cbn. rewrite /trans_decl /= /vass. f_equal.
  rewrite (trans_lift _ p) //.
  now move/andP: hx.
Qed.

Lemma trans_subst_decl p q s k d :
  on_free_vars_terms p s ->
  on_free_vars_decl q d ->
  trans_decl (SE.subst_decl s k d) = subst_decl (map trans s) k (trans_decl d).
Proof.
  destruct d as [na [b|] ty]; cbn; rewrite /trans_decl /= /subst_decl /= /map_decl /=.
  intros ons ond.
  f_equal. f_equal.
  rewrite (trans_subst q p) //.
  now move/andP: ond => /=.
  rewrite (trans_subst q p) //.
  now move/andP: ond => /=.
  intros ons ond.
  f_equal. f_equal.
  rewrite (trans_subst q p) //.
Qed.

Lemma trans_subst_context p q s k Γ :
  on_free_vars_ctx p Γ ->
  on_free_vars_terms q s ->
  trans_local (SE.subst_context s k Γ) = subst_context (map trans s) k (trans_local Γ).
Proof.
  induction Γ as [|d Γ]; simpl; auto.
  rewrite !subst_context_snoc /= on_free_vars_ctx_snoc.
  move=> /andP[] onΓ ond ons.
  erewrite trans_subst_decl; tea. rewrite /app_context /snoc. len. f_equal.
  now apply IHΓ.
Qed.

Lemma trans_lift_decl p n k d :
  on_free_vars_decl p d ->
  trans_decl (SE.lift_decl n k d) = lift_decl n k (trans_decl d).
Proof.
  destruct d as [na [b|] ty]; cbn; rewrite /trans_decl /= /lift_decl /= /map_decl /=.
  intros ond.
  f_equal. f_equal.
  rewrite (trans_lift _ p) //.
  now move/andP: ond => /=.
  rewrite (trans_lift _ p) //.
  now move/andP: ond => /=.
  intros ond.
  f_equal. f_equal.
  rewrite (trans_lift _ p) //.
Qed.

Lemma trans_lift_context p n k Γ :
  on_free_vars_ctx p Γ ->
  trans_local (SE.lift_context n k Γ) = lift_context n k (trans_local Γ).
Proof.
  induction Γ as [|d]; auto.
  rewrite /= !lift_context_snoc /= on_free_vars_ctx_snoc.
  move/andP => [] onΓ ond.
  rewrite (trans_lift_decl (shiftnP #|Γ| p)) //. len. unfold snoc. f_equal.
  now apply IHΓ.
Qed.

Lemma trans_smash_context p Γ Δ :
  on_free_vars_ctx (shiftnP #|Δ| p) Γ ->
  on_free_vars_ctx p Δ ->
  trans_local (SE.smash_context Γ Δ) = smash_context (trans_local Γ) (trans_local Δ).
Proof.
  induction Δ in p, Γ |- *; simpl; auto.
  rewrite on_free_vars_ctx_snoc.
  move=> onΓ /andP [] onΔ ona.
  destruct a as [na [b|] ty] => /=.
  rewrite (IHΔ p) //.
  eapply on_free_vars_ctx_subst_context0.
  now rewrite shiftnP_add. cbn.
  move/andP: ona => [] /= -> //.
  f_equal.
  rewrite (trans_subst_context (shiftnP (S #|Δ|) p) (shiftnP #|Δ| p)) //.
  move/andP: ona => [] /= -> //; cbn; auto.
  rewrite (IHΔ p) //.
  rewrite on_free_vars_ctx_app /=.
  cbn. rewrite shiftnP0. move/andP: ona => [] _ ->.
  now rewrite shiftnP_add. f_equal. rewrite trans_local_app //.
Qed.

Lemma context_assumptions_map ctx : context_assumptions (map trans_decl ctx) = SE.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; lia.
Qed.

Lemma on_free_vars_ctx_k_eq p n Γ :
  on_free_vars_ctx_k p n Γ = on_free_vars_ctx (shiftnP n p) Γ.
Proof.
  rewrite /on_free_vars_ctx_k.
  rewrite alli_shift //.
  rewrite /on_free_vars_ctx.
  eapply alli_ext. intros i x.
  now rewrite shiftnP_add Nat.add_comm.
Qed.

Lemma trans_extended_subst p Γ n :
  on_free_vars_ctx p Γ ->
  map trans (extended_subst Γ n) = extended_subst (trans_local Γ) n.
Proof.
  induction Γ in n, p |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto.
  rewrite on_free_vars_ctx_snoc. move/andP => [] onΓ /andP[] onb onty.
  erewrite (trans_subst _ _); revgoals.
  eapply on_free_vars_extended_subst.
  erewrite on_free_vars_ctx_k_eq => //.
  eapply on_free_vars_ctx_impl; tea. intros i pi. rewrite /shiftnP.
  nat_compare_specs; cbn. auto. now instantiate (1 := xpredT).
  erewrite on_free_vars_lift. eapply onb.
  erewrite (trans_lift _ _); revgoals. eapply onb.
  rewrite (IHΓ p) //. f_equal. f_equal. now len.
  rewrite on_free_vars_ctx_snoc => /andP[] onΓ ont.
  f_equal; eauto.
Qed.

Lemma trans_expand_lets_k p Γ k T :
  on_free_vars_ctx p Γ ->
  on_free_vars (shiftnP #|Γ| p) T ->
  trans (SE.expand_lets_k Γ k T) = expand_lets_k (trans_local Γ) k (trans T).
Proof.
  rewrite /SE.expand_lets_k => onΓ onT.
  erewrite (trans_subst _ _); revgoals.
  eapply on_free_vars_extended_subst. rewrite on_free_vars_ctx_k_eq shiftnP0. exact onΓ.
  erewrite on_free_vars_lift. exact onT.
  erewrite (trans_lift _) => //. 2:exact onT.
  erewrite trans_extended_subst; tea.
  rewrite /expand_lets /expand_lets_k.
  now len.
Qed.

Lemma trans_expand_lets p Γ T :
  on_free_vars_ctx p Γ ->
  on_free_vars (shiftnP #|Γ| p) T ->
  trans (expand_lets Γ T) = expand_lets (trans_local Γ) (trans T).
Proof.
  move=> onΓ onT.
  rewrite /SE.expand_lets /SE.expand_lets_k.
  rewrite (trans_expand_lets_k p) //.
Qed.

Lemma trans_expand_lets_map p Γ T :
  on_free_vars_ctx p Γ ->
  on_free_vars_terms (shiftnP #|Γ| p) T ->
  map trans (map (expand_lets Γ) T) = map (expand_lets (trans_local Γ)) (map trans T).
Proof.
  move=> onΓ onT.
  eapply forallb_All in onT. solve_all.
  rewrite (trans_expand_lets p) //.
Qed.

Lemma alpha_eq_trans {Γ Δ} :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (trans_local Γ) (trans_local Δ).
Proof.
  intros.
  eapply All2_map, All2_impl; tea.
  intros x y []; constructor; subst; auto.
Qed.

Definition wt {cf} Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma isType_wt {cf} {Σ Γ T} : isType Σ Γ T -> wt Σ Γ T.
Proof.
  intros (_ & s & hs & _); now exists (PCUICAst.tSort s).
Qed.
Coercion isType_wt : isType >-> wt.

Lemma wt_wf_local {cf} {Σ} {Γ t} : wt Σ Γ t -> wf_local Σ Γ.
Proof.
  intros [s hs]. now eapply typing_wf_local.
Qed.

Coercion wt_wf_local : wt >-> All_local_env.

Lemma wt_red {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t u} : wt Σ Γ t -> red1 Σ Γ t u -> wt Σ Γ u.
Proof.
  intros [s hs] r. exists s.
  eapply subject_reduction; tea. now apply red1_red.
Qed.

Section wtsub.
  Context {cf} {Σ : PCUICEnvironment.global_env_ext} {wfΣ : PCUICTyping.wf Σ}.
  Import PCUICAst.
  Definition wt_subterm Γ (t : term) : Type :=
    let wt := wt Σ in
    match t with
    | tLambda na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tProd na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tLetIn na b ty b' => [× wt Γ b, wt Γ ty & wt (Γ ,, vdef na b ty) b']
    | tApp f a => wt Γ f × wt Γ a
    | tCase ci p c brs =>
      All (wt Γ) p.(pparams) ×
      ∑ mdecl idecl,
      [× declared_inductive Σ ci mdecl idecl,
         consistent_instance_ext Σ (PCUICEnvironment.ind_universes mdecl) (PCUICAst.puinst p),
         wf_predicate mdecl idecl p,
         eq_context_upto_names (PCUICCases.ind_predicate_context ci mdecl idecl) (PCUICAst.pcontext p),
         wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) p.(pcontext)@[p.(puinst)],
         PCUICSpine.spine_subst Σ Γ (PCUICAst.pparams p) (List.rev (PCUICAst.pparams p))
          (PCUICEnvironment.smash_context [] (PCUICEnvironment.ind_params mdecl)@[PCUICAst.puinst p]),
          wt (Γ ,,, PCUICCases.case_predicate_context ci mdecl idecl p) p.(preturn),
          wt Γ c &
          All2i (fun i cdecl br =>
            [× wf_branch cdecl br,
              eq_context_upto_names (bcontext br) (PCUICCases.cstr_branch_context ci mdecl cdecl),
               wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) br.(bcontext)@[p.(puinst)],
               eq_context_upto_names
                (Γ ,,, PCUICCases.case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl)
                (Γ ,,, inst_case_branch_context p br) &
              wt (Γ ,,, PCUICCases.case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl) br.(bbody)]) 0 idecl.(ind_ctors) brs]
    | tProj p c => wt Γ c
    | tFix mfix idx | tCoFix mfix idx =>
      All (fun d => wt Γ d.(dtype) × wt (Γ ,,, fix_context mfix) d.(dbody)) mfix
    | tEvar _ l => False
    | tRel i => wf_local Σ Γ
    | tPrim p => primitive_typing_hyps (fun Σ Γ t T => wt Γ t) Σ Γ p
    | _ => unit
    end.
  Import PCUICGeneration PCUICInversion.

  Lemma spine_subst_wt Γ args inst Δ : PCUICSpine.spine_subst Σ Γ args inst Δ ->
    All (wt Σ Γ) inst.
  Proof.
    intros []. clear -inst_subslet wfΣ.
    induction inst_subslet; constructor; auto.
    eexists; tea. eexists; tea.
  Qed.

  Lemma lift_wt_inv {Γ j} : lift_typing typing Σ Γ j -> lift_wf_term (wt Σ Γ) j.
  Proof.
    intros (? & ? & ? & _).
    split. 1: destruct j_term => //.
    all: eexists; eassumption.
  Qed.

  Lemma wt_inv {Γ t} : wt Σ Γ t -> wt_subterm Γ t.
  Proof.
    destruct t; simpl; intros [T h]; try exact tt.
    - now eapply typing_wf_local in h.
    - now eapply inversion_Evar in h.
    - eapply inversion_Prod in h as (?&?&h1&?&?); tea.
      apply lift_wt_inv in h1 as [].
      split; tas; eexists; eauto.
    - eapply inversion_Lambda in h as (?&h1&?&?); tea.
      apply lift_wt_inv in h1 as [].
      split; tas; eexists; eauto.
    - eapply inversion_LetIn in h as (?&h1&?&?); tea.
      apply lift_wt_inv in h1 as [].
      repeat split; tas; eexists; eauto.
    - eapply inversion_App in h as (?&?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_Case in h as (mdecl&idecl&decli&indices&[]&?); tea.
      assert (tty := PCUICValidity.validity scrut_ty).
      eapply PCUICInductiveInversion.isType_mkApps_Ind_smash in tty as []; tea.
      2:eapply (wf_predicate_length_pars wf_pred).
      split.
      eapply spine_subst_wt in s. now eapply All_rev_inv in s.
      exists mdecl, idecl. split; auto. now symmetry.
      * eapply All_local_env_app_inv. eapply wf_local_alpha.
        eapply All2_app; [|reflexivity].
        eapply alpha_eq_subst_instance. symmetry; tea.
        eapply wf_ind_predicate; tea. pcuic.
      * eexists; tea.
      * eexists; tea.
      * eapply Forall2_All2 in wf_brs.
        eapply All2i_All2_mix_left in brs_ty; tea.
        eapply All2i_nth_hyp in brs_ty.
        solve_all. split; auto.
        { eapply All_local_env_app_inv. eapply wf_local_alpha.
          eapply All2_app; [|reflexivity].
          eapply alpha_eq_subst_instance in a2.
          symmetry; tea.
          eapply validity in scrut_ty.
          epose proof (wf_case_branch_type ps _ decli scrut_ty wf_pred pret_ty conv_pctx i x y).
          forward X. { split; eauto. }
          specialize (X a1) as [].
          eapply wf_local_expand_lets in a5.
          rewrite /PCUICCases.cstr_branch_context.
          rewrite PCUICUnivSubstitutionConv.subst_instance_expand_lets_ctx.
          rewrite PCUICUnivSubstitutionConv.subst_instance_subst_context.
          rewrite PCUICUnivSubstitutionConv.subst_instance_inds.
          erewrite PCUICUnivSubstitutionConv.subst_instance_id_mdecl; tea. }
        erewrite PCUICCasesContexts.inst_case_branch_context_eq; tea. reflexivity.
        eexists; tea.
    - eapply inversion_Proj in h as (?&?&?&?&?&?&?&?&?); tea.
      eexists; eauto.
    - eapply inversion_Fix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? (_ & ? & ? & _); now eexists.
      eapply (All_impl a0). intros ? (h & _); cbn in h; eexists; tea.
    - eapply inversion_CoFix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? (_ & ? & ? & _); now eexists.
      eapply (All_impl a0). intros ? (h & _); cbn in h; eexists; tea.
    - eapply inversion_Prim in h as (?&?&[]).
      depelim p0; constructor; eauto. 1-2:now eexists. solve_all. now eexists. eauto.
  Qed.
End wtsub.

Ltac outtimes :=
  match goal with
  | ih : _ × _ |- _ =>
    destruct ih as [? ?]
  end.

Lemma red1_cumul {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> cumulAlgo Σ Γ T U.
Proof.
  intros r.
  econstructor 2; tea. constructor. reflexivity.
Qed.

Lemma red1_cumul_inv {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> cumulAlgo Σ Γ U T.
Proof.
  intros r.
  econstructor 3; tea. constructor. reflexivity.
Qed.

Definition TTconv {cf} (Σ : global_env_ext) Γ : relation term :=
  clos_refl_sym_trans (relation_disjunction (red1 Σ Γ) (eq_term Σ (T.global_ext_constraints Σ))).

Lemma red1_conv {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> TTconv Σ Γ T U.
Proof.
  intros r.
  now repeat constructor.
Qed.

Lemma trans_expand_lets_ctx p q Γ Δ :
  on_free_vars_ctx p Γ ->
  on_free_vars_ctx q Δ ->
  trans_local (SE.expand_lets_ctx Γ Δ) = expand_lets_ctx (trans_local Γ) (trans_local Δ).
Proof.
  move=> onΓ onΔ.
  rewrite /SE.expand_lets_ctx /SE.expand_lets_k_ctx /expand_lets_ctx /expand_lets_k_ctx.
  erewrite trans_subst_context.
  erewrite trans_extended_subst; tea.
  erewrite trans_lift_context; tea.
  rewrite context_assumptions_map length_map //.
  erewrite <- on_free_vars_ctx_lift_context; tea.
  eapply on_free_vars_extended_subst. rewrite on_free_vars_ctx_k_eq shiftnP0; tea.
Qed.

Lemma trans_cstr_branch_context p i ci mdecl cdecl :
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0) (cstr_args cdecl) ->
  smash_context [] (trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl)) =
  cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body i mdecl cdecl).
Proof.
  move=> onpars onargs.
  rewrite /PCUICCases.cstr_branch_context /cstr_branch_context.
  erewrite trans_expand_lets_ctx; tea.
  erewrite trans_subst_context; tea.
  erewrite trans_inds.
  rewrite -(PCUICContexts.expand_lets_smash_context _ []).
  f_equal.
  rewrite PCUICContexts.smash_context_subst_empty.
  f_equal => //. now cbn; rewrite length_map.
  eapply (inds_is_open_terms []).
  eapply on_free_vars_ctx_subst_context. len. exact onargs.
  eapply (inds_is_open_terms []).
Qed.

Lemma trans_cstr_branch_context_inst p i ci mdecl cdecl u :
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0) (cstr_args cdecl) ->
  smash_context [] (trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl)@[u]) =
  (cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body i mdecl cdecl))@[u].
Proof.
  move=> onps onargs.
  rewrite trans_subst_instance_ctx -(PCUICUnivSubstitutionConv.subst_instance_smash _ _ []).
  rewrite (trans_cstr_branch_context p i) //.
Qed.

From MetaRocq.PCUIC Require Import PCUICContexts.

Lemma eq_names_smash_context Γ :
  All2 (fun x y => decl_name x = decl_name y) (smash_context [] (trans_local Γ)) (smash_context [] Γ).
Proof.
  induction Γ.
  * constructor.
  * destruct a as [na [b|] ty]; cbn; auto.
    rewrite smash_context_acc (smash_context_acc _ [_]). constructor; auto.
Qed.

Lemma trans_assumption_context Γ : assumption_context Γ <-> assumption_context (trans_local Γ).
Proof.
  induction Γ; cbn; auto. reflexivity.
  split.
  - intros ass; depelim ass; constructor; auto.
    now apply IHΓ.
  - intros ass; destruct a as [na [b|] ty]; depelim ass; constructor.
    now apply IHΓ.
Qed.

Lemma trans_inst_case_branch_context_gen p q pred i br ci mdecl cdecl :
  let pred' := PCUICAst.map_predicate id trans trans (map_context trans) pred in
  wf_branch cdecl br ->
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
    (cstr_args cdecl) ->
  on_free_vars_terms q pred.(pparams) ->
  on_free_vars_ctx (shiftnP #|pred.(pparams)| xpred0) br.(bcontext) ->
  (* on_free_vars_ctx p cdecl.(cstr_args) -> *)
  eq_context_upto_names br.(PCUICAst.bcontext) (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  let br' := trans_branch pred' (map_branch trans (map_context trans) br) in
  (case_branch_context ci
    (trans_minductive_body mdecl) pred' (forget_types br'.(bcontext)) (trans_constructor_body i mdecl cdecl)) =
    (trans_local (smash_context [] (inst_case_branch_context pred br))).
Proof.
  intros p' wfbr onindpars onargs onpars onbctx.
  rewrite /inst_case_branch_context.
  rewrite /inst_case_context.
  rewrite /case_branch_context /case_branch_context_gen.
  rewrite (trans_smash_context q) //.
  { eapply on_free_vars_ctx_impl. 2:eapply on_free_vars_ctx_subst_context.
    3:rewrite forallb_rev //; tea.
    intros i'; rewrite shiftnP0 //.
    len. rewrite on_free_vars_ctx_subst_instance //.
    eapply on_free_vars_ctx_impl; tea.
    intros o. rewrite /shiftnP /=. rewrite orb_false_r.
    repeat nat_compare_specs; auto => //. }
  rewrite (trans_subst_context (shiftnP #|pred.(pparams)| xpred0) q).
  { rewrite on_free_vars_ctx_subst_instance //. }
  { rewrite [on_free_vars_terms _ _]forallb_rev //. }
  intros eq.
  rewrite map_rev.
  rewrite PCUICContexts.smash_context_subst_empty.
  eapply map2_set_binder_name_alpha_eq.
  { apply eq_names_subst_context.
    eapply All2_map_left.
    rewrite -(trans_smash_context (shiftnP #|pred.(pparams)| xpred0) []) //.
    { rewrite on_free_vars_ctx_subst_instance //. }
    eapply All2_map_right.
    rewrite -(PCUICUnivSubstitutionConv.subst_instance_smash _ _ []).
    eapply All2_map_right; cbn.
    rewrite /trans_branch.
    elim: is_assumption_context_spec => isass. cbn. cbn in isass.
    { eapply trans_assumption_context in isass.
      rewrite smash_assumption_context //.
      eapply All2_map_left => /=. apply All2_refl. reflexivity. }
    apply eq_names_smash_context. }
  eapply alpha_eq_subst_context.
  eapply alpha_eq_subst_instance in eq.
  symmetry in eq.
  eapply alpha_eq_trans in eq.
  rewrite -(trans_cstr_branch_context_inst p i) //.
  eapply alpha_eq_smash_context. exact eq.
Qed.

Lemma alpha_eq_on_free_vars_ctx {p Γ Δ} :
  eq_context_upto_names Γ Δ ->
  on_free_vars_ctx p Γ ->
  on_free_vars_ctx p Δ.
Proof.
  induction 1 => //.
  rewrite !on_free_vars_ctx_snoc=> /andP[] clx cll.
  apply /andP; split; auto.
  destruct r; unfold ws_decl, test_decl in *; cbn in *; subst; auto; now rewrite -(All2_length X).
Qed.


Lemma trans_inst_case_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ : context} {pred i br ci c mdecl idecl cdecl} :
  let pred' := PCUICAst.map_predicate id trans trans (map_context trans) pred in
  let br' := trans_branch pred' (map_branch trans (map_context trans) br) in
  wf_predicate mdecl idecl pred ->
  wf_branch cdecl br ->
  declared_constructor Σ (ci, c) mdecl idecl cdecl ->
  on_free_vars_terms (shiftnP #|Γ| xpred0) pred.(pparams) ->
  eq_context_upto_names br.(PCUICAst.bcontext) (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  (case_branch_context ci
    (trans_minductive_body mdecl) pred' (forget_types br'.(bcontext)) (trans_constructor_body i mdecl cdecl)) =
    (trans_local (smash_context [] (inst_case_branch_context pred br))).
Proof.
  intros pred' br' wfp wfbr declc onps com.
  eapply (trans_inst_case_branch_context_gen xpred0 (shiftnP #|Γ| xpred0)) => //.
  eapply closed_ctx_on_free_vars; eapply (declared_inductive_closed_params declc).
  rewrite -closedn_ctx_on_free_vars. rewrite Nat.add_comm; eapply (declared_constructor_closed_args declc).
  eapply alpha_eq_on_free_vars_ctx. symmetry; tea.
  rewrite -closedn_ctx_on_free_vars.
  relativize #|pparams pred|. eapply (closed_cstr_branch_context declc).
  rewrite (wf_predicate_length_pars wfp).
  now rewrite (declared_minductive_ind_npars declc).
Qed.

From MetaRocq.PCUIC Require Import PCUICSpine.

Lemma trans_reln l p Γ : map trans (SE.reln l p Γ) =
  reln (map trans l) p (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in l, p |- *; simpl; [auto..|].
  now rewrite IHΓ.
Qed.

Lemma trans_to_extended_list Γ n : map trans (SE.to_extended_list_k Γ n) = to_extended_list_k (trans_local Γ) n.
Proof.
  now rewrite /to_extended_list_k trans_reln.
Qed.

Lemma trans_ind_predicate_context ci mdecl idecl :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP #|ind_params mdecl| xpred0) (ind_indices idecl) ->
  trans_local (PCUICCases.ind_predicate_context ci mdecl idecl) =
  (ind_predicate_context ci (trans_minductive_body mdecl)
      (trans_one_ind_body mdecl (inductive_ind ci) idecl)).
Proof.
  move=> clpars clindices.
  rewrite /ind_predicate_context /=.
  rewrite /trans_decl /=. f_equal.
  f_equal. rewrite trans_mkApps /=. f_equal.
  rewrite trans_to_extended_list trans_local_app /to_extended_list.
  f_equal. f_equal.
  now rewrite (trans_smash_context xpred0).
  now rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)).
  now rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)).
Qed.

Lemma trans_ind_predicate_context_eq p ci mdecl idecl :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP #|ind_params mdecl| xpred0) (ind_indices idecl) ->
  eq_context_upto_names (PCUICAst.pcontext p)
    (PCUICCases.ind_predicate_context ci mdecl idecl) ->
  All2
    (λ (x : binder_annot name) (y : context_decl),
       eq_binder_annot x (decl_name y))
    (map decl_name (trans_local (PCUICAst.pcontext p)))
    (ind_predicate_context ci (trans_minductive_body mdecl)
       (trans_one_ind_body mdecl (inductive_ind ci) idecl)).
Proof.
  move=> clpars clindices.
  rewrite -trans_ind_predicate_context //.
  intros. eapply All2_map, All2_map_left.
  solve_all.
  destruct X; cbn; subst; auto.
Qed.

Lemma trans_cstr_branch_context_eq ci mdecl cdecl p i br :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
  (cstr_args cdecl) ->
  eq_context_upto_names (PCUICAst.bcontext br)
    (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  eq_context_upto_names
    (bcontext (trans_branch p (map_branch trans (map_context trans) br)))
    (cstr_branch_context ci (trans_minductive_body mdecl)
      (trans_constructor_body i mdecl cdecl)).
Proof.
  intros clpars clargs a.
  rewrite -(trans_cstr_branch_context xpred0) //.
  cbn.
  rewrite /trans_branch.
  elim: is_assumption_context_spec => isass.
  { cbn in isass |- *.
    rewrite -(smash_assumption_context (map_context trans (bcontext br))) //.
    eapply alpha_eq_smash_context.
    eapply All2_map. solve_all.
    destruct X; subst; auto; constructor; cbn; auto. }
  { eapply alpha_eq_smash_context.
    eapply All2_map. solve_all.
    destruct X; subst; auto; constructor; cbn; auto. }
Qed.

Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) l l' :
  map f (map2 g l l') = map2 (fun x y => f (g x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  now rewrite IHl.
Qed.

Lemma map2_map_map {A B C D} (f : A -> B -> C) (g : D -> B) l l' :
  map2 (fun x y => f x (g y)) l l' = map2 f l (map g l').
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  now rewrite IHl.
Qed.

Lemma trans_set_binder na y :
  trans_decl (PCUICEnvironment.set_binder_name na y) = set_binder_name na (trans_decl y).
Proof.
  destruct y as [na' [b|] ty]; cbn; auto.
Qed.

From Stdlib Require Import Morphisms.
#[global] Instance map2_Proper {A B C} : Morphisms.Proper (pointwise_relation A (pointwise_relation B (@eq C)) ==> eq ==> eq ==> eq) map2.
Proof.
  intros f g Hfg ? ? -> ? ? ->.
  eapply map2_ext, Hfg.
Qed.

Lemma map2_set_binder_name_eq nas Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  map2 set_binder_name nas Δ = map2 set_binder_name nas Δ'.
Proof.
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  rewrite IHX. destruct r; subst; cbn; reflexivity.
Qed.

Lemma eq_binder_trans (nas : list aname) (Δ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas Δ ->
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas (trans_local Δ).
Proof.
  intros. eapply All2_map_right, All2_impl; tea.
  cbn. intros x y H. destruct y; apply H.
Qed.

Lemma trans_local_set_binder nas Γ :
  trans_local (map2 PCUICEnvironment.set_binder_name nas Γ) =
  map2 set_binder_name nas (trans_local Γ).
Proof.
  rewrite /trans_local map_map2.
  setoid_rewrite trans_set_binder.
  now rewrite map2_map_map.
Qed.

Lemma All2_eq_binder_lift_context (l : list (binder_annot name)) n k (Γ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (PCUICEnvironment.lift_context n k Γ).
Proof.
  induction 1; cbn; rewrite ?PCUICLiftSubst.lift_context_snoc //; constructor; auto.
Qed.

Lemma All2_eq_binder_expand_lets_ctx (l : list (binder_annot name)) (Δ Γ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (PCUICEnvironment.expand_lets_ctx Δ Γ).
Proof.
  intros a.
  now eapply All2_eq_binder_subst_context, All2_eq_binder_lift_context.
Qed.

Lemma trans_local_set_binder_name_eq nas Γ Δ :
  eq_context_upto_names Γ Δ ->
  trans_local (map2 PCUICEnvironment.set_binder_name nas Γ) =
  trans_local (map2 PCUICEnvironment.set_binder_name nas Δ).
Proof.
  intro H.
  f_equal. now apply eq_context_upto_names_map2_set_binder_name_eq.
Qed.

Lemma map2_trans l l' :
  map2
  (λ (x : aname) (y : PCUICEnvironment.context_decl),
      trans_decl (PCUICEnvironment.set_binder_name x y)) l l' =
  map2 (fun (x : aname) (y : PCUICEnvironment.context_decl) =>
    set_binder_name x (trans_decl y)) l l'.
Proof.
  eapply map2_ext.
  intros x y. rewrite /trans_decl. now destruct y; cbn.
Qed.

Lemma closed_ctx_is_closed_context Γ :
  closed_ctx Γ -> is_closed_context Γ.
Proof.
  now rewrite closedn_ctx_on_free_vars closedP_shiftnP shiftnP0.
Qed.
#[local] Hint Resolve closed_ctx_is_closed_context : pcuic.
#[local] Hint Resolve declared_inductive_closed_params : pcuic.

Lemma closedn_ctx_on_free_vars n (Δ : context) :
  closedn_ctx n Δ -> on_free_vars_ctx (shiftnP n xpred0) Δ.
Proof.
  rewrite closedn_ctx_on_free_vars closedP_shiftnP //.
Qed.

#[local] Hint Resolve closedn_ctx_on_free_vars : pcuic.

Lemma declared_inductive_closed_indices {cf} {Σ : PCUICEnvironment.global_env_ext}
  {wfΣ : PCUICTyping.wf Σ} ind mdecl idecl :
  declared_inductive Σ ind mdecl idecl ->
  closedn_ctx #|ind_params mdecl| (ind_indices idecl).
Proof.
  move/declared_inductive_closed_pars_indices.
  rewrite closedn_ctx_app /= => /andP[] //.
Qed.
#[local] Hint Resolve declared_inductive_closed_indices : pcuic.

Lemma on_free_vars_ind_predicate_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  on_free_vars_ctx (closedP (context_assumptions (ind_params mdecl)) xpredT)
    (ind_predicate_context ind mdecl idecl).
Proof.
  intros decli.
  rewrite <- PCUICOnFreeVars.closedn_ctx_on_free_vars.
  eapply PCUICClosed.closed_ind_predicate_context; tea.
  eapply (PCUICClosedTyp.declared_minductive_closed (proj1 decli)).
Qed.

Lemma trans_case_predicate_context {cf} {Σ : PCUICEnvironment.global_env_ext}
  {wfΣ : PCUICTyping.wf Σ} {Γ ci mdecl idecl p} :
  S.declared_inductive Σ ci mdecl idecl ->
  S.consistent_instance_ext Σ (PCUICEnvironment.ind_universes mdecl) (PCUICAst.puinst p) →
  let parctx := (PCUICEnvironment.ind_params mdecl)@[PCUICAst.puinst p] in
  PCUICSpine.spine_subst Σ Γ (PCUICAst.pparams p)
      (List.rev (PCUICAst.pparams p))
      (PCUICEnvironment.smash_context [] parctx) ->
  wf_predicate mdecl idecl p ->
  let p' := map_predicate id trans trans trans_local p in
  (case_predicate_context ci (trans_minductive_body mdecl) (trans_one_ind_body mdecl (inductive_ind ci) idecl) p') =
  (trans_local (PCUICCases.case_predicate_context ci mdecl idecl p)).
Proof.
  intros.
  rewrite /case_predicate_context /PCUICCases.case_predicate_context.
  rewrite /case_predicate_context_gen /PCUICCases.case_predicate_context_gen.
  rewrite /trans_local map_map2 map2_trans.
  rewrite -PCUICUnivSubstitutionConv.map2_map_r. f_equal.
  rewrite /p' /=. now rewrite forget_types_map_context.
  rewrite /pre_case_predicate_context_gen /inst_case_context.
  rewrite /PCUICCases.pre_case_predicate_context_gen /PCUICCases.inst_case_context.
  rewrite [map _ _](trans_subst_context (shiftnP (context_assumptions mdecl.(ind_params)) xpred0)
    (shiftnP #|Γ| xpred0)).
  rewrite -closedP_shiftnP on_free_vars_ctx_subst_instance.
  eapply (on_free_vars_ind_predicate_context H).
  now eapply inst_subslet, subslet_open in X.
  rewrite map_rev. f_equal.
  rewrite trans_subst_instance_ctx.
  rewrite trans_ind_predicate_context; pcuic.
Qed.

Lemma OnOne2All2i_OnOne2All {A B : Type} (l1 l2 : list A) (l3 : list B)
  (R1 : A → A → Type) (R2 : nat → B → A → Type) (n : nat) (R3 : B -> A -> A -> Type) :
  OnOne2 R1 l1 l2 →
  All2i R2 n l3 l1 →
  (forall (n0 : nat) (x y : A) (z : B), R1 x y → R2 n0 z x → R3 z x y) → OnOne2All R3 l3 l1 l2.
Proof.
  induction 1 in n, l3 |- *; intros H; depelim H.
  intros H'. constructor. now eapply H'. eapply (All2i_length _ _ _ _ H).
  intros H'. constructor. now eapply IHX.
Qed.

Lemma trans_eq_binder_annot (Γ : list aname) Δ :
  Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ ->
  Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ (trans_local Δ).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma map_context_trans Γ : map_context trans Γ = trans_local Γ.
Proof.
  rewrite /map_context /trans_local /trans_decl.
  eapply map_ext. intros []; reflexivity.
Qed.

Lemma trans_bcontext p br :
  (bcontext (trans_branch p (map_branch trans (map_context trans) br))) = smash_context [] (trans_local (bcontext br)).
Proof.
  rewrite /trans_branch.
  elim: is_assumption_context_spec => isass.
  rewrite smash_assumption_context //.
  now cbn.
Qed.

Lemma trans_bbody p br :
  (bbody (trans_branch p (map_branch trans (map_context trans) br))) =
  expand_lets (subst_context (List.rev (pparams p)) 0 (trans_local (bcontext br))@[puinst p]) (trans (bbody br)).
Proof.
  rewrite /trans_branch.
  elim: is_assumption_context_spec => isass.
  { rewrite expand_lets_assumption_context //.
    now eapply assumption_context_subst_context, assumption_context_subst_instance. }
  cbn -[expand_lets].
  now cbn.
Qed.

Lemma OnOne2All_map2_map_all {A B I I'} {P} {i : list I} {l l' : list A} (g : B -> I -> I') (f : A -> B) :
  OnOne2All (fun i x y => P (g (f x) i) (f x) (f y)) i l l' -> OnOne2All P (map2 g (map f l) i) (map f l) (map f l').
Proof.
  induction 1; simpl; constructor; try congruence; try assumption. len.
  now rewrite map2_length !length_map.
Qed.

Lemma wt_on_free_vars {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t} : wt Σ Γ t -> on_free_vars (shiftnP #|Γ| xpred0) t.
Proof.
  intros [T wt].  now eapply subject_is_open_term in wt.
Qed.

Ltac fuse_shifts :=
  match goal with
  [ H : is_true (on_free_vars (shiftnP 1 (shiftnP _ _)) _) |- _ ] =>
    rewrite -> shiftnP_add in H; cbn in H
  end.

Ltac tofvs := repeat match goal with [ H : wt _ _ _ |- _ ] => apply wt_on_free_vars in H end;
  try inv_on_free_vars; repeat fuse_shifts.

#[local] Hint Extern 3 (is_true (_ && true)) => rewrite andb_true_r : pcuic.

Lemma length_skipn_map {A B} {n} {f : A -> B} {l} : #|skipn n (map f l)| = #|skipn n l|.
Proof.
  now rewrite !List.length_skipn length_map.
Qed.

Lemma on_free_vars_ctx_cstr_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {c mdecl idecl cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  on_free_vars_ctx (shiftnP (context_assumptions (ind_params mdecl)) xpred0)
    (cstr_branch_context c.1 mdecl cdecl).
Proof.
  intros. eapply closedn_ctx_on_free_vars. eapply (PCUICInstConv.closedn_ctx_cstr_branch_context H).
Qed.

Lemma typing_spine_wt {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {args Γ x2 x3} :
  typing_spine Σ Γ x2 args x3 ->
  All (wt Σ Γ) args.
Proof.
  intros sp.
  dependent induction sp; constructor; auto.
  now exists A.
Qed.

Lemma wt_mkApps_inv {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ f args} :
  wt Σ Γ (mkApps f args) -> wt Σ Γ f × All (wt Σ Γ) args.
Proof.
  intros [ha tapp].
  eapply inversion_mkApps in tapp as [ty [tf targs]].
  split.
  - exists ty; eauto.
  - now eapply typing_spine_wt.
Qed.

Lemma red_expand_lets {cf} (Σ : global_env_ext) {wfΣ : wf Σ} Γ Δ t t' :
  Σ ;;; Γ ,,, Δ ⊢ t ⇝ t' ->
  Σ ;;; Γ ,,, smash_context [] Δ ⊢ expand_lets Δ t ⇝ expand_lets Δ t'.
Proof.
  intros reds.
  rewrite /expand_lets /expand_lets_k. cbn.
  eapply (untyped_closed_red_subst (Γ := _ ,,, _) (Γ' := [])).
  eapply untyped_subslet_extended_subst; tea.
  len => /=. rewrite -shiftnP_add. rewrite foron_free_vars_extended_subst //.
  now move/PCUICAlpha.is_closed_context_app_right: (clrel_ctx reds).
  relativize #|Δ|. relativize (context_assumptions Δ).
  eapply weakening_closed_red; tea. all:try now len. 2:reflexivity.
  eapply is_closed_context_smash_end; fvs.
Qed.

From MetaRocq.PCUIC Require Import PCUICConfluence PCUICNormal.

Lemma red_context_rel_assumptions {cf} {Σ : global_env_ext} {Γ Δ Δ'} :
  red_context_rel Σ Γ Δ Δ' -> context_assumptions Δ = context_assumptions Δ'.
Proof.
  induction 1; cbn; auto. destruct p; cbn; auto. lia.
Qed.

Lemma ws_cumul_pb_expand_lets {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {le} {Δ} {T T'} :
  Σ ;;; Γ ,,, Δ ⊢ T ≤[le] T' ->
  Σ ;;; Γ ,,, smash_context [] Δ ⊢ expand_lets Δ T ≤[le] expand_lets Δ T'.
Proof.
  intros cum.
  pose proof (ws_cumul_pb_is_closed_context cum).
  eapply (weakening_ws_cumul_pb (Γ'' := smash_context [] Δ)) in cum; tea.
  rewrite /expand_lets /expand_lets_k.
  eapply (PCUICConversion.untyped_substitution_ws_cumul_pb (Γ'' := [])) in cum; tea. len in cum; tea.
  simpl.
  len.
  now eapply PCUICContexts.untyped_subslet_extended_subst.
  len. cbn. rewrite -shiftnP_add.
  rewrite foron_free_vars_extended_subst //.
  now move: H; rewrite on_free_vars_ctx_app => /andP[].
  now eapply is_closed_context_smash_end.
Qed.

Lemma red_terms_lift {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ ts us} :
  is_closed_context (Γ ,,, Δ) ->
  red_terms Σ Γ ts us ->
  red_terms Σ (Γ ,,, Δ) (map (lift0 #|Δ|) ts) (map (lift0 #|Δ|) us).
Proof.
  intros r. solve_all.
  eapply (weakening_closed_red (Γ' := [])) => //.
Qed.

Lemma onfvs_app Γ Δ : is_closed_context (Γ ,,, Δ) ->
  is_closed_context Γ /\ on_free_vars_ctx (shiftnP #|Γ| xpred0) Δ.
Proof.
  now rewrite on_free_vars_ctx_app => /andP.
Qed.

Lemma untyped_subslet_ws_cumul_ctx_pb {cf} {Γ Γ' Δ Δ'} {s} :
  untyped_subslet (Γ ,,, Δ) s Γ' ->
  untyped_subslet (Γ ,,, Δ') s Γ'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma weakening_is_closed_context Γ Δ :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, smash_context [] Δ ,,, lift_context (context_assumptions Δ) 0 Δ).
Proof.
  move=> cl. rewrite on_free_vars_ctx_app.
  apply/andP; split.
  now eapply is_closed_context_smash_end.
  eapply on_free_vars_ctx_lift_context0.
  len => /=. rewrite -shiftnP_add addnP_shiftnP.
  now move/PCUICAlpha.is_closed_context_app_right: cl.
Qed.

Lemma red_context_rel_conv_extended_subst {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ'} :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  red_context_rel Σ Γ Δ Δ' ->
  red_terms Σ (Γ ,,, smash_context [] Δ) (extended_subst Δ 0) (extended_subst Δ' 0) ×
  ws_cumul_ctx_pb_rel Conv Σ Γ (smash_context [] Δ) (smash_context [] Δ').
Proof.
  intros wfl wfr cum.
  assert (is_closed_context (Γ ,,, smash_context [] Δ)).
  { eapply is_closed_context_smash_end in wfl. eauto with fvs. }
  induction cum in |- *; simpl; auto.
  - split; constructor => //. constructor.
  - depelim p; simpl.
    move: wfl => /= /on_free_vars_ctx_snoc_ass_inv [] wfl clT.
    move: wfr => /= /on_free_vars_ctx_snoc_ass_inv [] wfr clT';
    specialize (IHcum wfl wfr) as [conv cum'];
    try assert (is_closed_context (Γ,,, smash_context [] Γ0)) by
      (rewrite /= smash_context_acc /= on_free_vars_ctx_snoc in H; now move/andP: H) => //.
    all:auto.
    * split; try constructor; auto.
      + eapply into_closed_red => //. cbn. len. now cbn.
      + rewrite !(lift_extended_subst _ 1).
        move: H.
        rewrite /= ![smash_context [_] _]smash_context_acc /= /map_decl /= => ha.
        eapply (red_terms_lift (Δ := [_])) => //.
      + now move/onfvs_app: H.
      + move: H; simpl; rewrite /= !(smash_context_acc _ [_]) /=;
        constructor; auto.
        apply cum'. rewrite /map_decl /=.
        constructor; auto.
        eapply into_closed_red in r; fvs.
        eapply red_ws_cumul_pb in r.
        eapply ws_cumul_pb_expand_lets in r; tea.
        etransitivity;tea. rewrite /expand_lets /expand_lets_k. simpl.
        rewrite -(length_of cum).
        rewrite -(red_context_rel_assumptions cum).
        move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
        change (Γ ,,, smash_context [] Γ0) with (Γ ,,, smash_context [] Γ0 ,,, []).
        eapply (untyped_substitution_ws_cumul_pb_subst_conv (Γ' := [])); tea.
        now eapply red_terms_ws_cumul_pb_terms in conv.
        3:eapply PCUICContexts.untyped_subslet_extended_subst.
        3:{ eapply untyped_subslet_ws_cumul_ctx_pb.
            now eapply untyped_subslet_extended_subst. }
        now eapply weakening_is_closed_context.
        cbn -[is_closed_context]. rewrite on_free_vars_ctx_app.
        apply/andP; split. now apply is_closed_context_smash_end.
        len => /=. rewrite -shiftnP_add. eapply on_free_vars_ctx_lift_context0.
        rewrite (red_context_rel_assumptions cum) addnP_shiftnP.
        now move/PCUICAlpha.is_closed_context_app_right: wfr.
        rewrite context_assumptions_smash_context /=.
        rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
        relativize #|Γ0|.
        eapply is_open_term_lift.
        len. rewrite (All2_fold_length cum). now len in clT'. reflexivity.
    * move: wfl => /= /on_free_vars_ctx_snoc_def_inv => [] [] clΓ0 clb clT.
      move: wfr => /= /on_free_vars_ctx_snoc_def_inv => [] [] clΓ0' clb' clT'.
      specialize (IHcum clΓ0 clΓ0' ltac:(auto)) as [].
      split; auto.
      constructor; auto.
      len.
      eapply into_closed_red in r; fvs.
      eapply red_expand_lets in r; tea.
      etransitivity; tea. rewrite subst_context_nil.
      rewrite /expand_lets /expand_lets_k. simpl.
      rewrite -(length_of cum).
      rewrite -(red_context_rel_assumptions cum).
      move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
      change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
      cbn. rewrite smash_context_acc /=.
      change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
      eapply (closed_red_red_subst (Γ := _ ,,, _) (Γ' := [])); tea.
      2:{ eapply PCUICContexts.untyped_subslet_extended_subst. }
      { now eapply weakening_is_closed_context. }
      rewrite context_assumptions_smash_context /=.
      rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
      relativize #|Γ0|.
      eapply is_open_term_lift.
      len. rewrite (All2_fold_length cum). now len in clb'. reflexivity.
Qed.

From MetaRocq.PCUIC Require Import PCUICSubstitution.

Lemma is_closed_context_subst Γ Γ' s Δ :
  is_closed_context (Γ ,,, Γ' ,,, Δ) ->
  forallb (is_open_term Γ) s ->
  #|s| = #|Γ'| ->
  is_closed_context (Γ ,,, subst_context s 0 Δ).
Proof.
  intros clΓ cls slen.
  rewrite on_free_vars_ctx_app.
  rewrite  -app_context_assoc on_free_vars_ctx_app in clΓ.
  move/andP: clΓ => [] -> /=; rewrite on_free_vars_ctx_app => /andP[] o o'.
  apply on_free_vars_ctx_subst_context0 => //. now rewrite slen.
Qed.

Lemma red_expand_lets_ctx {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ'' Δ s s' t} :
  is_closed_context (Γ ,,, Γ' ,,, Δ) ->
  is_closed_context (Γ ,,, Γ'' ,,, Δ) ->
  untyped_subslet Γ s Γ' ->
  untyped_subslet Γ s' Γ'' ->
  All2 (closed_red Σ Γ) s s' ->
  is_open_term (Γ ,,, subst_context s 0 Δ) t ->
  Σ ;;; Γ ,,, subst_context s 0 (smash_context [] Δ) ⊢
    (expand_lets (subst_context s 0 Δ) t) ⇝
    (expand_lets (subst_context s' 0 Δ) t).
Proof.
  intros wf wf' subs subs' reds ont.
  rewrite -smash_context_subst /= subst_context_nil.
  have cls : is_closed_context (Γ,,, subst_context s 0 Δ).
  { eapply is_closed_context_subst; tea. eapply closed_red_terms_open_left in reds. solve_all.
    now rewrite -(untyped_subslet_length subs') (All2_length reds). }
  have cls' : is_closed_context (Γ,,, subst_context s' 0 Δ).
  { eapply is_closed_context_subst; tea. eapply closed_red_terms_open_right in reds. solve_all.
    now rewrite -(untyped_subslet_length subs'). }
  etransitivity.
  eapply red_expand_lets; tea.
  eapply into_closed_red; tea. reflexivity.
  rewrite /expand_lets /expand_lets_k. len. cbn.
  eapply (closed_red_red_subst (Γ := _ ,,, _) (Γ' := [])); tea.
  3:{ eapply untyped_subslet_extended_subst. }
  eapply weakening_is_closed_context => //.
  eapply (red_context_rel_conv_extended_subst) => //.
  eapply red_ctx_rel_subst; tea. solve_all. apply X.
  solve_all. apply X.
  rewrite context_assumptions_subst.
  rewrite -[context_assumptions Δ](smash_context_length []).
  relativize #|smash_context [] _|. relativize #|Δ|.
  eapply is_open_term_lift. 2-3:now len. apply ont.
Qed.

From MetaRocq.PCUIC Require Import PCUICSubstitution.

Lemma untyped_subslet_lift (Γ Δ : context) s Δ' :
  untyped_subslet Γ s Δ' ->
  untyped_subslet (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(untyped_subslet_length X).
  rewrite distr_lift_subst. constructor; auto.
Qed.

Lemma OnOne2_All2i_All2 {A B} {P : A -> A -> Type} {Q R} {n} {l l' : list A} {l'' : list B} :
  OnOne2 P l l' ->
  All2i Q n l'' l ->
  (forall n x y z, P x y -> Q n z x -> R x y) ->
  (forall n x z, Q n z x -> R x x) ->
  All2 R l l'.
Proof.
  intros o a. induction a in o, l' |- *. depelim o.
  depelim o.
  - intros. constructor; eauto.
    clear -a X0.
    induction a; constructor; eauto.
  - intros. constructor.
    eapply X0; tea.
    eapply IHa; tea.
Qed.

From MetaRocq.PCUIC Require Import PCUICUnivSubstitutionConv.

Lemma OnOne2_All_OnOne2 {A} {P : A -> A -> Type} {Q R} l l' :
  OnOne2 P l l' ->
  All Q l ->
  (forall x y, Q x -> P x y -> R x y) ->
  OnOne2 R l l'.
Proof.
  induction 1; intros H; depelim H; intros IH; constructor; eauto.
Qed.

Lemma OnOne2_All_All2 {A} {P : A -> A -> Type} {Q R} l l' :
  OnOne2 P l l' ->
  All Q l ->
  (forall x y, Q x -> P x y -> R x y) ->
  (forall x, Q x -> R x x) ->
  All2 R l l'.
Proof.
  induction 1; intros H; depelim H; intros IH; constructor; eauto.
  clear -H X; solve_all.
Qed.

Lemma All2i_map_right_inv {A B C} {P : nat -> A -> B -> Type} {f : C -> B} n (l : list A) l' :
  All2i P n l (map f l') ->
  All2i (fun n x y => P n x (f y)) n l l'.
Proof.
  induction l' in n, l |- *; cbn; intros h; depelim h; constructor; auto.
Qed.

Lemma All2i_map_left_inv {A B C} {P : nat -> A -> B -> Type} {f : C -> A} n l l' :
  All2i P n (map f l) l' ->
  All2i (fun n x y => P n (f x) y) n l l'.
Proof.
  induction l in n, l' |- *; cbn; intros h; depelim h; constructor; auto.
Qed.

Lemma trans_is_closed_context Γ : is_closed_context Γ -> is_closed_context (map_context trans Γ).
Proof.
  move=> cl; eapply on_free_vars_ctx_impl; [|eapply (on_free_vars_ctx_trans 0)].
  intros i. rewrite /closedP; now cbn.
  now rewrite closedP_shiftnP shiftnP0.
Qed.

Lemma on_free_vars_ind_params {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {P ind mdecl idecl u} :
  declared_inductive Σ ind mdecl idecl ->
  on_free_vars_ctx P (ind_params mdecl)@[u].
Proof.
  intros decl.
  eapply on_free_vars_ctx_impl; [|eapply closedn_ctx_on_free_vars]; revgoals.
  rewrite closedn_subst_instance_context.
  eapply (declared_inductive_closed_params decl).
  intros i; rewrite shiftnP0 //.
Qed.

Lemma shiftnP_mon n n' i : n <= n' -> shiftnP n xpred0 i -> shiftnP n' xpred0 i.
Proof.
  rewrite /shiftnP.
  repeat nat_compare_specs; cbn; auto.
Qed.

Lemma is_closed_context_cstr_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ ind mdecl idecl cdecl u} :
  declared_constructor Σ ind mdecl idecl cdecl ->
  is_closed_context Γ ->
  is_closed_context (Γ ,,, (smash_context [] (ind_params mdecl))@[u] ,,, (cstr_branch_context ind.1 mdecl cdecl)@[u]).
Proof.
  intros declc clΓ.
  rewrite -app_context_assoc on_free_vars_ctx_app clΓ /=.
  rewrite on_free_vars_ctx_app.
  apply/andP; split.
  rewrite subst_instance_smash.
  eapply on_free_vars_ctx_smash => //. apply (on_free_vars_ind_params declc).
  len. cbn.
  rewrite on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_impl; [|eapply (on_free_vars_ctx_cstr_branch_context declc)].
  intros i. rewrite shiftnP_add. eapply shiftnP_mon.
  move: (context_assumptions_bound (ind_params mdecl)). lia.
Qed.

Lemma trans_untyped_subslet {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ s Δ} :
  wf_local Σ (Γ ,,, Δ) ->
  All (wt Σ Γ) s ->
  untyped_subslet Γ s Δ ->
  untyped_subslet (trans_local Γ) (map trans s) (trans_local Δ).
Proof.
  induction 3 in |- *; cbn; try constructor; auto.
  cbn. depelim X. now depelim X0.
  depelim X. depelim X0.
  rewrite (trans_subst (shiftnP #|Γ ,,, Δ|  xpred0) (shiftnP #|Γ| xpred0)).
  apply unlift_TermTyp in l. now eapply subject_is_open_term in l. solve_all. now eapply wt_on_free_vars.
  constructor ; auto.
Qed.

Lemma untyped_subslet_length Γ s s' Δ :
  untyped_subslet Γ s Δ -> #|s| = #|s'| -> assumption_context Δ -> untyped_subslet Γ s' Δ.
Proof.
  induction 1 in s' |- *; cbn; destruct s' => /= //. constructor.
  intros [=]. constructor ; auto. eapply IHX; auto. now depelim H.
  intros. exfalso; depelim H0.
Qed.

Lemma wf_local_ind_params_weaken {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ind mdecl u} :
  declared_minductive Σ ind mdecl ->
  wf_local Σ Γ ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (Γ ,,, (ind_params mdecl)@[u]).
Proof.
  intros decli wfΓ cu.
  eapply weaken_wf_local => //.
  now eapply on_minductive_wf_params.
Qed.

Definition cf' cf :=
  {| check_univs := cf.(@check_univs);
     prop_sub_type := cf.(@prop_sub_type);
     indices_matter := cf.(@indices_matter);
     lets_in_constructor_types := false |}.

Notation wf_trans Σ := (@wf (cf' _) (trans_global_env Σ.1)).
Notation wf_ext_trans Σ := (@wf_ext (cf' _) (trans_global Σ)).

Lemma trans_red1 {cf} (Σ : global_env_ext) {wfΣ : wf Σ} {wfΣ' : wf_trans Σ} Γ T U :
  red1 Σ Γ T U ->
  wt Σ Γ T ->
  red (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1 using red1_ind_all; simpl in *; intros wt;
    match goal with
    | |- context [tCase _ _ _ _] => idtac
    | |- context [tFix _ _] => idtac
    | |- context [tCoFix _ _] => idtac
    | _ => eapply wt_inv in wt; tea; cbn in wt; repeat outtimes
    end;
    try solve [econstructor; eauto].

  - simpl. tofvs.
    rewrite (trans_subst_ctx Γ) /=; [pcuic..|]. eapply red1_red; constructor.
  - destruct wt. tofvs. rewrite (trans_subst_ctx Γ); [pcuic..|]. repeat constructor.

  - destruct nth_error eqn:Heq => //. simpl in H. noconf H.
    simpl. destruct c; noconf H => //.
    rewrite (trans_lift _ (shiftnP #|skipn (S i) Γ| xpred0)); eauto.
    eapply All_local_env_nth_error in wt0; tea. apply unlift_TermTyp in wt0.
    now eapply subject_is_open_term.
    do 2 constructor. now rewrite nth_error_map Heq.

  - pose proof (wt_on_free_vars wt).
    inv_on_free_vars.
    destruct wt as [s Hs].
    eapply inversion_Case in Hs as [mdecl [idecl [decli [indices [[] e]]]]].
    epose proof (PCUICValidity.inversion_mkApps scrut_ty) as [? [hc hsp]]; tea.
    eapply inversion_Construct in hc as (mdecl'&idecl'&cdecl&wfΓ&declc&cu&tyc); tea.
    unshelve epose proof (decli_ := declared_inductive_to_gen decli); eauto.
    unshelve epose proof (declc_ := declared_inductive_to_gen declc); eauto.
    destruct (declared_inductive_inj decli_ declc_) as [-> ->]. 2:auto.
    rewrite trans_mkApps /=.
    have lenskip : #|skipn (ci_npar ci) (map trans args)| =
      context_assumptions (cstr_args cdecl).
    { destruct (Construct_Ind_ind_eq _ scrut_ty declc) as [[? e'] _].
      rewrite length_skipn; len; lia. }
    eapply All2i_nth_error_r in brs_ty; tea.
    destruct brs_ty as [cdecl' [Hcdecl' [bctxeq [wfbrctx [hbody hbodyty]]]]].
    rewrite (proj2 declc) in Hcdecl'. noconf Hcdecl'.
    have lenbctx : context_assumptions (cstr_args cdecl) = context_assumptions (bcontext br).
    { rewrite (alpha_eq_context_assumptions _ _ bctxeq).
      rewrite cstr_branch_context_assumptions. lia. }
    relativize (trans (iota_red _ _ _ _)).
    eapply red1_red; eapply red_iota; tea; eauto. all:auto.
    * rewrite !nth_error_map H; reflexivity.
    * rewrite trans_bcontext (context_assumptions_smash_context []) /= context_assumptions_map.
      len. eauto.
    * rewrite /iota_red. rewrite length_skipn_map in lenskip.
      have oninst : on_free_vars_ctx (shiftnP #|Γ| xpred0) (inst_case_branch_context p br).
      { rewrite -(PCUICCasesContexts.inst_case_branch_context_eq bctxeq).
        eapply typing_wf_local in hbody. eapply wf_local_closed_context in hbody.
        rewrite -> on_free_vars_ctx_app in hbody.
        move/andP: hbody => [] //. }
      have onb : on_free_vars (shiftnP #|inst_case_branch_context p br| (shiftnP #|Γ| xpred0)) (bbody br).
      { rewrite -(PCUICCasesContexts.inst_case_branch_context_eq bctxeq).
        eapply subject_is_open_term in hbody. len in hbody. rewrite shiftnP_add //. }
      rewrite (trans_subst_ctx Γ).
      { len. rewrite lenskip.
        rewrite -shiftnP_add.
        eapply on_free_vars_expand_lets_k => //.
        rewrite /inst_case_branch_context /inst_case_context.
        rewrite context_assumptions_subst_context context_assumptions_subst_instance. lia. }
      { rewrite forallb_rev forallb_skipn //.
        rewrite on_free_vars_mkApps in p3. move: p3 => /= //. }
      rewrite map_rev map_skipn. f_equal.
      rewrite (trans_expand_lets (shiftnP #|Γ| xpred0)) //.
      cbn -[expand_lets].
      rewrite expand_lets_assumption_context.
      { apply assumption_context_subst_context.
        apply assumption_context_subst_instance.
        rewrite trans_bcontext.
        apply smash_context_assumption_context => //.
        constructor. }
      f_equal.
      rewrite /inst_case_branch_context /inst_case_context.
      rewrite (trans_subst_context (shiftnP (#|Γ| + #|ind_params mdecl|) xpred0) (shiftnP #|Γ| xpred0)).
      { rewrite on_free_vars_ctx_subst_instance.
        eapply alpha_eq_on_free_vars_ctx; [symmetry; tea|].
        eapply on_free_vars_ctx_impl; [|eapply (on_free_vars_ctx_cstr_branch_context declc)].
        intros i. rewrite /shiftnP. rewrite !orb_false_r.
        move/Nat.ltb_lt => H'. apply Nat.ltb_lt.
        pose proof (context_assumptions_bound (ind_params mdecl)). lia. }
      { rewrite [on_free_vars_terms _ _]forallb_rev //. }
      rewrite map_rev. f_equal.
      rewrite trans_subst_instance_ctx //.
      now rewrite trans_bbody.

  - simpl. rewrite !trans_mkApps /=.
    eapply wt_mkApps_inv in wt as [wtf wtargs].
    unfold is_constructor in H0.
    destruct nth_error eqn:hnth.
    pose proof (nth_error_Some_length hnth).
    destruct args. simpl. exfalso; cbn in H1. lia.
    cbn -[mkApps].
    eapply red1_red, red_fix.
    apply (trans_unfold_fix (shiftnP #|Γ| xpred0)); eauto.
    now eapply wt_on_free_vars in wtf.
    eapply (trans_is_constructor (t0 :: args)).
    now rewrite /is_constructor hnth.
    discriminate.

  - rewrite trans_mkApps.
    rewrite !trans_mkApps; eauto with wf.
    eapply wt_inv in wt. cbn in wt.
    destruct wt as [wtpars [idecl [cdecl []]]].
    eapply wt_mkApps_inv in w2 as [].
    apply (trans_unfold_cofix (shiftnP #|Γ| xpred0)) in H; eauto with wf.
    eapply red1_red, red_cofix_case; eauto.
    now eapply wt_on_free_vars in w2.

  - rewrite !trans_mkApps.
    eapply wt_inv in wt. cbn in wt.
    eapply wt_mkApps_inv in wt as [].
    apply (trans_unfold_cofix (shiftnP #|Γ| xpred0)) in H; eauto with wf.
    eapply red1_red, red_cofix_proj; eauto.
    now eapply wt_on_free_vars in w.

  - rewrite trans_subst_instance. eapply red1_red; econstructor.
    apply (trans_declared_constant _ c decl H).
    destruct decl. now simpl in *; subst cst_body0.

  - rewrite trans_mkApps; eauto with wf.
    simpl. eapply red1_red; constructor; now rewrite nth_error_map H.

  - eapply red_abs; eauto.
  - eapply red_abs; eauto.
  - destruct wt as []; eapply red_letin; eauto.
  - destruct wt as []; eapply red_letin; eauto.
  - destruct wt as []; eapply red_letin; eauto.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply OnOne2_All_mix_left in X; tea.
    relativize (map_predicate id _ _ _ (set_pparams _ _)).
    eapply red_case. 5:reflexivity. all:try reflexivity.
    cbn.
    eapply OnOne2_All2. eapply OnOne2_map.
    2:intros x y h; exact h. 2:reflexivity.
    eapply OnOne2_All_OnOne2; tea. cbv beta.
    intros x y wtt [[r IH] wt]. specialize (IH wt).
    red. apply IH.
    rewrite /trans_branch. cbn.
    eapply All2_map. cbn. eapply All2_map, All_All2_refl.
    eapply All2i_nth_hyp in a0.
    eapply All2i_All_right; tea. cbv beta. clear a0.
    intros ctor cdecl br [hnth [wfbr eqbctx wfbctx eqinst wtb]].
    elim: is_assumption_context_spec => isass.
    { split => //. }
    split => //. cbn [bcontext bbody map_branch]. rewrite /id.
    rewrite (subst_instance_smash _ _ []) /=.
    eapply (red_expand_lets_ctx (cf := cf' cf) (Σ := trans_global Σ)
      (Γ' := (trans_local (smash_context [] (ind_params mdecl))@[puinst p]))
      (Γ'' := (trans_local (smash_context [] (ind_params mdecl))@[puinst p]))).
    *  eapply alpha_eq_on_free_vars_ctx.
      eapply All2_app; [|reflexivity].
      eapply alpha_eq_subst_instance.
      eapply alpha_eq_trans. symmetry. exact eqbctx.
      rewrite - !trans_subst_instance_ctx -!trans_local_app.
      rewrite -[_ ++ _]trans_local_app.
      eapply trans_is_closed_context.
      have declc : declared_constructor Σ (ci, ctor) mdecl idecl cdecl.
      { split; tea. }
      eapply (is_closed_context_cstr_branch_context declc).
      destruct w2 as [? ? % typing_closed_ctx]; eauto.
    * eapply alpha_eq_on_free_vars_ctx.
      eapply All2_app; [|reflexivity].
      eapply alpha_eq_subst_instance.
      eapply alpha_eq_trans. symmetry. exact eqbctx.
      rewrite - !trans_subst_instance_ctx -!trans_local_app.
      rewrite -[_ ++ _]trans_local_app.
      eapply trans_is_closed_context.
      have declc : declared_constructor Σ (ci, ctor) mdecl idecl cdecl.
      { split; tea. }
      eapply (is_closed_context_cstr_branch_context declc).
      destruct w2 as [? ? % typing_closed_ctx]; eauto.
    * rewrite -map_rev.
      eapply trans_untyped_subslet.
      { rewrite subst_instance_smash. eapply wf_local_smash_end.
        eapply wf_local_ind_params_weaken; tea. exact d. exact w2. }
      { solve_all. }
      rewrite subst_instance_smash.
      eapply subslet_untyped_subslet; exact s.
    * rewrite -map_rev.
      eapply trans_untyped_subslet.
      { rewrite subst_instance_smash. eapply wf_local_smash_end.
        eapply wf_local_ind_params_weaken; tea. exact d. exact w2. }
      { solve_all.
        eapply spine_subst_wt_terms in s.
        solve_all. eapply OnOne2_impl_All_r; tea.
        2:solve_all. cbv beta; intros x y wtx [[Hr _]].
        eapply wt_red; tea. }
      eapply untyped_subslet_length.
      rewrite subst_instance_smash. exact s. len.
      eapply (OnOne2_length X).
      pcuic.
    * eapply All2_rev. eapply All2_map.
      eapply OnOne2_All_All2; tea; cbv beta.
      intros x y wtx [[r Hr] wt].
      specialize (Hr wt).
      destruct wtx. eapply into_closed_red => //.
      eapply typing_closed_ctx in t; tea.
      now eapply trans_is_closed_context.
      eapply trans_on_free_vars. len.
      now eapply subject_is_open_term in t.
      intros x []. eapply into_closed_red. reflexivity.
      eapply typing_closed_ctx in t. now eapply trans_is_closed_context. auto.
      eapply subject_is_open_term in t. eapply trans_on_free_vars. now len.
    * len. destruct wtb. cbn in t.
      eapply subject_is_open_term in t.
      len in t. rewrite (case_branch_context_length wfbr) in t.
      now eapply trans_on_free_vars.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply red_case_p.
    symmetry in a. rewrite (inst_case_predicate_context_eq a) in w1.
    specialize (IHX w1).
    rewrite -(inst_case_predicate_context_eq a) in IHX.
    eapply alpha_eq_trans in a.
    rewrite trans_ind_predicate_context in a.
    { eapply closed_ctx_is_closed_context, declared_inductive_closed_params; tea. }
    { epose proof (declared_inductive_closed_indices _ _ _ d).
      now eapply closedn_ctx_on_free_vars in H. }
    set (p' := map_predicate id trans _ _ p).
    rewrite -(inst_case_predicate_context_eq (p:=p') a).
    rewrite (trans_case_predicate_context d c0 s w).
    now rewrite -trans_local_app.

  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply red_case_c; eauto.

  - pose proof (wt_on_free_vars wt). inv_on_free_vars.
    eapply forallb_All in p4.
    eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply red_case_brs.
    do 2 eapply All2_map.
    eapply All2i_All_mix_right in a0; tea.
    eapply OnOne2_All2i_All2; tea; cbv beta.
    intros _ br br' cdecl [[hred ih] eqctx].
    intros [[] onfvs].
    intros ctx. split => //. 2:{ rewrite !trans_bcontext. cbn. now rewrite eqctx. }
    2:{ intros; split; reflexivity. }
    rewrite -{1}(PCUICCasesContexts.inst_case_branch_context_eq a1) in ih.
    specialize (ih w5).
    rewrite trans_local_app in ih.
    cbn -[expand_lets].
    rewrite !trans_bcontext !trans_bbody.
    rewrite (subst_instance_smash _ _ []).
    rewrite -(smash_context_subst []) /=. len. rewrite subst_context_nil /id.
    rewrite -eqctx.
    eapply (red_expand_lets (cf := cf' cf) (trans_global Σ)). cbn.
    rewrite /inst_case_branch_context in ih.
    rewrite /inst_case_context in ih.
    rewrite (trans_subst_context (shiftnP #|pparams p| xpred0) (shiftnP #|Γ| xpred0)) // in ih.
    { rewrite on_free_vars_ctx_subst_instance //.
      move/andP: onfvs. rewrite test_context_k_closed_on_free_vars_ctx.
      now rewrite closedP_shiftnP. }
    { rewrite [on_free_vars_terms _ _]forallb_rev. solve_all. }
    rewrite map_rev in ih.
    rewrite trans_subst_instance_ctx in ih.
    move: ih.
    rewrite -!trans_subst_instance_ctx.
    rewrite -!map_rev -!(trans_subst_context (closedP #|pparams p| xpredT) (shiftnP #|Γ| xpred0)).
    { move/andP: onfvs => [] onctx _. rewrite test_context_k_closed_on_free_vars_ctx in onctx.
      now rewrite on_free_vars_ctx_subst_instance. }
    { rewrite /on_free_vars_terms forallb_rev. solve_all. }
    rewrite -!trans_local_app.
    intros r; eapply into_closed_red => //.
    { eapply trans_is_closed_context.
      rewrite -[SE.subst_context _ _ _](PCUICCasesContexts.inst_case_branch_context_eq (p:=p) a1).
      destruct w5 as [? wt]. now eapply typing_closed_ctx in wt. }
    { eapply trans_on_free_vars.
      move/andP: onfvs => [] onctx onb. len.
      now rewrite -shiftnP_add. }

  - eapply red_proj_c; eauto.
  - eapply red_app; eauto.
  - eapply red_app; eauto.
  - eapply red_prod; eauto.
  - eapply red_prod; eauto.
  - eapply red_fix_congr.
    eapply All2_map.
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H0; reflexivity.
    cbn. congruence.
    intros. repeat split; reflexivity.

  - eapply red_fix_congr.
    eapply All2_map.
    pose proof (wt_on_free_vars wt).
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H1; reflexivity.
    cbn.
    rewrite -(trans_fix_context (shiftnP #|Γ| xpred0) _ idx) //.
    now rewrite trans_local_app in X0. cbn; congruence.
    intros. repeat split; reflexivity.

  - eapply red_cofix_congr.
    eapply All2_map.
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H0; reflexivity.
    cbn. congruence.
    intros. repeat split; reflexivity.

  - eapply red_cofix_congr.
    pose proof (wt_on_free_vars wt).
    eapply All2_map.
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H1; reflexivity.
    cbn.
    rewrite -(trans_fix_context (shiftnP #|Γ| xpred0) _ idx) //.
    now rewrite trans_local_app in X0. cbn; congruence.
    intros. repeat split; reflexivity.

  - cbn. eapply red_primArray_value. cbn. eapply All2_map. depelim wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbn; intuition eauto.

  - cbn; depelim wt. eapply red_primArray_default; cbn; eauto.
  - cbn; depelim wt. eapply red_primArray_type; cbn; eauto.
Qed.

Lemma trans_cmp_global_instance {Σ : global_env} Re Rle gref napp u u' :
  cmp_global_instance Σ Re Rle gref napp u u' ->
  cmp_global_instance (trans_global_env Σ) Re Rle gref napp u u'.
Proof.
  unfold PCUICEquality.cmp_global_instance, PCUICEquality.global_variance.
  destruct gref; simpl; auto.
  - unfold S.lookup_inductive, S.lookup_minductive.
    unfold S.lookup_inductive_gen, S.lookup_minductive_gen.
    unfold lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_mapi.
    destruct nth_error => /= //.
    rewrite trans_destr_arity.
    destruct PCUICAst.destArity as [[ctx ps]|] => /= //.
    now rewrite context_assumptions_map.
  - unfold S.lookup_constructor, S.lookup_inductive, S.lookup_minductive.
    unfold S.lookup_constructor_gen, S.lookup_inductive_gen, S.lookup_minductive_gen.
    unfold lookup_constructor, lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_mapi.
    destruct nth_error => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
Qed.

Lemma trans_eq_context_upto_names_eq_binder_annot Γ Δ :
  eq_context_upto_names Γ Δ ->
  All2 eq_binder_annot (map decl_name (trans_local Γ)) (map decl_name (trans_local Δ)).
Proof.
  intros; do 2 eapply All2_map. solve_all.
  destruct X; cbn; auto.
Qed.

Lemma trans_eq_context_upto_names Γ Δ :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (trans_local Γ) (trans_local Δ).
Proof.
  apply PCUICEquality.trans_eq_context_upto_names.
Qed.

Lemma eq_term_upto_univ_expand_lets {cf} {Σ : global_env} {cmp_universe cmp_sort pb Γ Δ t u napp} :
  subrelation (cmp_universe Conv) (cmp_universe pb) ->
  subrelation (cmp_sort Conv) (cmp_sort pb) ->
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t u ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (expand_lets Γ t) (expand_lets Δ u).
Proof.
  intros subr subr' eqctx eqt.
  rewrite /expand_lets /expand_lets_k.
  eapply eq_term_upto_univ_substs => //.
  rewrite -(eq_context_upto_length eqctx).
  rewrite (eq_context_gen_context_assumptions eqctx).
  now eapply eq_term_upto_univ_lift.
  apply (PCUICConfluence.eq_context_extended_subst eqctx).
Qed.

Lemma trans_eq_term_upto_univ {cf} {Σ : global_env} {cmp_universe cmp_sort pb t u napp} :
  SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv) ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t u ->
  eq_term_upto_univ_napp (trans_global_env Σ) cmp_universe cmp_sort pb napp (trans t) (trans u).
Proof.
  intros substu substu' e.
  induction t using term_forall_list_ind in pb, napp, u, e |- *.
  all: invs e; cbn.
  all: try solve [ constructor ; auto ].
  all: try solve [
    repeat constructor ;
    match goal with
    | ih : forall Rle u (napp : nat), _ |- _ =>
      eapply ih ; eauto using subrelation_refl
    end
  ].
  1,2,3,4,5,6: try solve [ constructor; unfold eq_mfixpoint in *; solve_all; eauto using subrelation_refl ].
  all: try solve [ constructor; now eapply trans_cmp_global_instance ].
  - destruct X1 as [Hpars [Huinst [Hctx Hret]]].
    destruct X as [IHpars [IHctx IHret]].
    constructor; cbn; auto.
    all: unfold eq_predicate, eq_branches in *.
    1: repeat split; cbn; auto.
    + cbn. apply All2_map. solve_all.
    + now apply trans_eq_context_upto_names.
    + cbn. apply All2_map. solve_all.
      destruct b; split.
      * rewrite !trans_bcontext.
        now apply eq_context_upto_names_smash_context, trans_eq_context_upto_names.
      * rewrite !trans_bbody.
        apply eq_term_upto_univ_expand_lets; eauto; tc.
        apply eq_context_upto_subst_context; eauto; tc.
        1: apply eq_context_upto_names_subst_instance; eauto; tc.
        1: now eapply trans_eq_context_upto_names.
        eapply All2_rev, All2_map. solve_all.
  - constructor; depelim X0; cbn in X; try now constructor.
    constructor; cbn; intuition eauto.
    solve_all.
Qed.

Lemma trans_compare_term {cf} {Σ : global_env} {pb ϕ T U} :
  compare_term Σ ϕ pb T U ->
  compare_term (H:=cf' cf) (trans_global_env Σ) ϕ pb (trans T) (trans U).
Proof.
  eapply trans_eq_term_upto_univ ; eauto; tc.
Qed.

Lemma trans_leq_term {cf} {Σ : global_env} ϕ T U :
  PCUICEquality.leq_term Σ ϕ T U ->
  @compare_term (cf' cf) (trans_global_env Σ) ϕ Cumul (trans T) (trans U).
Proof.
  eapply trans_eq_term_upto_univ; eauto; tc.
Qed.

From MetaRocq.PCUIC Require Import PCUICContextConversion.

Lemma wt_red1_wt {cf} {Σ} {wfΣ : wf Σ} {Γ t u} :
  wt Σ Γ t -> red1 Σ Γ t u -> wt Σ Γ u.
Proof.
  intros [s ht] r.
  exists s. eapply subject_reduction1; tea.
Qed.

Section wtcumul.
  Import PCUICAst PCUICTyping PCUICEquality.
  Context {cf : checker_flags}.
  Record wt_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) (Γ : PCUICEnvironment.context) T U :=
  { wt_red1_red1 : PCUICReduction.red1 Σ Γ T U;
    wt_red1_dom : wt Σ Γ T;
    wt_red1_codom : wt Σ Γ U }.

  Reserved Notation " Σ ;;; Γ |-- t <=[ le ] u " (at level 50, Γ, le, t, u at next level).

  Inductive wt_cumul_pb (pb : conv_pb) (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | wt_cumul_refl t u : compare_term Σ.1 (global_ext_constraints Σ) pb t u -> Σ ;;; Γ |-- t <=[pb] u
  | wt_cumul_red_l t u v : wt_red1 Σ Γ t v -> Σ ;;; Γ |-- v <=[pb] u -> Σ ;;; Γ |-- t <=[pb] u
  | wt_cumul_red_r t u v : Σ ;;; Γ |-- t <=[pb] v -> wt_red1 Σ Γ u v -> Σ ;;; Γ |-- t <=[pb] u
  where " Σ ;;; Γ |-- t <=[ pb ] u " := (wt_cumul_pb pb Σ Γ t u) : type_scope.

  Definition wt_cumul := wt_cumul_pb Cumul.
  Definition wt_conv := wt_cumul_pb Conv.

  Lemma cumul_decorate (Σ : global_env_ext) {wfΣ : wf Σ} Γ T U :
    isType Σ Γ T -> isType Σ Γ U ->
    cumulAlgo Σ Γ T U ->
    wt_cumul_pb Cumul Σ Γ T U.
  Proof.
    move/isType_wt => ht.
    move/isType_wt => hu.
    induction 1.
    - constructor. auto.
    - pose proof (wt_red ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHX; tea.
    - pose proof (wt_red hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.

  Lemma conv_decorate (Σ : global_env_ext) {wfΣ : wf Σ} Γ T U :
    wt Σ Γ T -> wt Σ Γ U ->
    convAlgo Σ Γ T U ->
    wt_cumul_pb Conv Σ Γ T U.
  Proof.
    intros ht hu.
    induction 1.
    - constructor. auto.
    - pose proof (wt_red ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHX; tea.
    - pose proof (wt_red hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.

  Definition wt_cumul_pb_ctx {cf} le Σ :=
    All2_fold (fun Γ Γ' => All_decls_alpha_pb le (fun le => wt_cumul_pb le Σ Γ)).

  Definition wt_cumul_pb_ctx_rel {cf} le Σ Γ :=
    All2_fold (fun Δ Δ' => All_decls_alpha_pb le (fun le => wt_cumul_pb le Σ (Γ ,,, Δ))).

End wtcumul.

Lemma trans_conv {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wf_trans Σ ->
  wt_conv Σ Γ T U ->
  cumulAlgo_gen (H := cf' cf) (trans_global Σ) (trans_local Γ) Conv (trans T) (trans U).
Proof.
  intros wfΣ'; induction 1.
  - constructor; auto.
    red in c.
    eapply trans_compare_term in c.
    now rewrite -trans_global_ext_constraints.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto.
    eapply red_conv_conv; tea.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto.
    eapply red_conv_conv_inv; tea.
Qed.

Lemma trans_cumul {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wf_trans Σ ->
  wt_cumul Σ Γ T U ->
  cumulAlgo_gen (H:=cf' cf) (trans_global Σ) (trans_local Γ) Cumul (trans T) (trans U).
Proof.
  intros wfΣ'; induction 1.
  - constructor; auto.
    red in c.
    eapply trans_compare_term in c.
    now rewrite -trans_global_ext_constraints.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto.
    eapply red_cumul_cumul; tea.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto.
    eapply red_cumul_cumul_inv; tea.
Qed.

Definition TTwf_local {cf} Σ Γ := TT.All_local_env (TT.lift_typing (TT.typing (H:=cf' cf)) Σ) Γ.

Lemma trans_lift_typing_it {P Q} {tm tm' : option term} {t t' : term} {u r} :
  forall tu: ST.lift_typing0 P (Judge tm t u r),
  let s := tu.2.π1 in
  match tm', tm with None, _ => unit | Some tm', Some tm => P tm t -> Q tm' t' | _, _ => False end ->
  (P t (tSort s) -> Q t' (tSort s)) ->
  TT.lift_typing0 Q (Judge tm' t' u r).
Proof.
  intros (? & ? & Hs & e) s HPQc HPQs.
  split.
  - destruct tm, tm' => //=. now apply HPQc.
  - eexists. split; [now apply HPQs|].
    destruct u => //.
Qed.


Lemma trans_wf_local' {cf} :
  forall (Σ : SE.global_env_ext) Γ (wfΓ : wf_local Σ Γ),
    let P :=
        (fun Σ0 Γ0 _ (t T : PCUICAst.term) _ =>
           TT.typing (H:=cf' cf) (trans_global Σ0) (trans_local Γ0) (trans t) (trans T))
    in
    ST.All_local_env_over (ST.typing Σ) (P Σ) Γ wfΓ ->
    TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + eapply trans_lift_typing_it with tu => //.
  - simpl. constructor; auto. eapply trans_lift_typing_it with tu => //.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun (Σ : SE.global_env_ext) Γ b ty =>
              wf_trans Σ ->
              ST.typing Σ Γ b ty ×
              TT.typing (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
        Γ ->
  wf_trans Σ ->
  TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. eapply trans_lift_typing_it with t0 => // HT. now apply HT.
  - simpl. constructor; auto. red. eapply trans_lift_typing_it with t0 => // HT. all: now apply HT.
Qed.

Lemma trans_branches {cf} Σ Γ brs btys ps:
  All2
    (fun br bty : nat × PCUICAst.term =>
      (((br.1 = bty.1 × ST.typing Σ Γ br.2 bty.2)
        × TT.typing (trans_global Σ) (trans_local Γ) (trans br.2) (trans bty.2))
      × ST.typing Σ Γ bty.2 (PCUICAst.tSort ps))
      × TT.typing (trans_global Σ) (trans_local Γ) (trans bty.2)
        (trans (PCUICAst.tSort ps))) brs btys ->
  All2
    (fun br bty : nat × term =>
    (br.1 = bty.1 × TT.typing (trans_global Σ) (trans_local Γ) br.2 bty.2)
    × TT.typing (trans_global Σ) (trans_local Γ) bty.2 (tSort ps))
    (map (on_snd trans) brs) (map (fun '(x, y) => (x, trans y)) btys).
Proof.
  induction 1;cbn.
  - constructor.
  - constructor.
    + destruct r as [[[[] ] ] ].
      destruct x,y.
      cbn in *.
      repeat split;trivial.
    + apply IHX.
Qed.

Lemma trans_mfix_All {cf} Σ Γ mfix idx :
  is_open_term Γ (tFix mfix idx) ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ : SE.global_env_ext)
          (Γ : SE.context) (b ty : PCUICAst.term) =>
        ST.typing Σ Γ b ty
        × TT.typing (H := cf' cf) (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
    (Γ ,,, (SE.fix_context mfix)) ->
  TTwf_local (trans_global Σ)
    (trans_local Γ ,,, fix_context (map (map_def trans trans) mfix)).
Proof.
  intros clfix ?.
  rewrite -(trans_fix_context (shiftnP #|Γ| xpred0) _ idx) //.
  match goal with
  |- TTwf_local _ ?A =>
      replace A with (trans_local (Γ ,,, (SE.fix_context mfix)))
  end.
  2: {
    unfold trans_local, app_context.
    now rewrite map_app.
  }

  induction X;cbn;constructor;auto;cbn in *.
  - eapply trans_lift_typing_it with t0 => // HT. now apply HT.
  - eapply trans_lift_typing_it with t0 => // HT. all: now apply HT.
Qed.


Lemma trans_decompose_prod_assum :
  forall Γ t,
    let '(Δ, c) := decompose_prod_assum Γ t in
    decompose_prod_assum (trans_local Γ) (trans t) = (trans_local Δ, trans c).
Proof.
  intros Γ t.
  destruct decompose_prod_assum as [Δ c] eqn:e.
  induction t in Γ, Δ, c, e |- *.
  all: simpl in *.
  all: try solve [ inversion e ; subst ; reflexivity ].
  - eapply IHt2 in e as e'. apply e'.
  - eapply IHt3 in e as e'. assumption.
Qed.

Lemma trans_isApp t : PCUICAst.isApp t = false -> isApp (trans t) = false.
Proof.
  destruct t => //.
Qed.

Lemma trans_nisApp t : ~~ PCUICAst.isApp t -> ~~ isApp (trans t).
Proof.
  destruct t => //.
Qed.

Lemma trans_destInd t : ST.destInd t = TT.destInd (trans t).
Proof.
  destruct t => //.
Qed.

Lemma trans_decompose_app t :
  let '(hd, args) := decompose_app t in
  decompose_app (trans t) = (trans hd, map trans args).
Proof.
  destruct (decompose_app t) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  eapply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps.
  apply decompose_app_mkApps.
  now rewrite trans_isApp.
Qed.

Lemma All2_map_option_out_mapi_Some_spec :
  forall {A B B'} (f : nat -> A -> option B) (g' : B -> B')
    (g : nat -> A -> option B') l t,
    (forall i x t, f i x = Some t -> g i x = Some (g' t)) ->
    map_option_out (mapi f l) = Some t ->
    map_option_out (mapi g l) = Some (map g' t).
Proof.
  intros A B B' f g' g l t.
  unfold mapi. generalize 0.
  intros n h e.
  induction l in n, e, t |- *.
  - simpl in *. apply some_inj in e. subst. reflexivity.
  - simpl in *.
    destruct (f n a) eqn:e'. 2: discriminate.
    eapply h in e' as h'.
    rewrite h'.
    match type of e with
    | context [ map_option_out ?t ] =>
      destruct (map_option_out t) eqn:e''
    end. 2: discriminate.
    eapply IHl in e''. rewrite e''. now noconf e.
Qed.

Lemma on_free_vars_it_mkProd_or_LetIn {P Δ t} :
  on_free_vars P (it_mkProd_or_LetIn Δ t) =
    on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
Proof.
  move: P. induction Δ using rev_ind => P.
  - cbn. now rewrite shiftnP0.
  - destruct x as [na [b|] ty]; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite on_free_vars_ctx_app /= IHΔ !plengths /= shiftnP_add on_free_vars_ctx_tip /=
      /on_free_vars_decl /test_decl /=. ring.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
     /on_free_vars_decl /test_decl /=. ring.
Qed.

Lemma trans_check_one_fix n p def :
  test_def (on_free_vars p) (on_free_vars (shiftnP n p)) def ->
  TT.check_one_fix (map_def trans trans def) = ST.check_one_fix def.
Proof.
  unfold ST.check_one_fix, TT.check_one_fix.
  destruct def as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p'] eqn:decty => /= ->.
  rewrite /test_def /=. move/andP => [] onty onarg.
  eapply decompose_prod_assum_it_mkProd_or_LetIn in decty. cbn in decty.
  subst ty.
  move: onty; rewrite on_free_vars_it_mkProd_or_LetIn => /andP[] onctx onp'.
  rewrite -(trans_smash_context p []) /trans_local //.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error => /= //.
  move: (trans_decompose_app (decl_type c)).
  destruct decompose_app => /=.
  simpl. destruct c. simpl. intros ->.
  now rewrite -trans_destInd.
Qed.

Definition on_free_vars_mfix p n mfix :=
 forallb (test_def (on_free_vars p) (on_free_vars (shiftnP n p))) mfix.

Lemma map_option_out_check_one_fix {p n mfix} :
  on_free_vars_mfix p n mfix ->
  map (fun x => TT.check_one_fix (map_def trans trans x)) mfix =
  map ST.check_one_fix mfix.
Proof.
  move/forallb_All => hmfix. eapply All_map_eq, All_impl; tea; cbv beta.
  apply trans_check_one_fix.
Qed.

Lemma trans_check_one_cofix mfix :
  TT.check_one_cofix (map_def trans trans mfix) = ST.check_one_cofix mfix.
Proof.
  unfold ST.check_one_cofix, TT.check_one_cofix.
  destruct mfix as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p] => -> /=.
  move: (trans_decompose_app p).
  destruct decompose_app => /= ->.
  now rewrite -trans_destInd.
Qed.

Lemma map_option_out_check_one_cofix mfix :
  map (fun x => TT.check_one_cofix (map_def trans trans x)) mfix =
  map ST.check_one_cofix mfix.
Proof.
  eapply map_ext => x. apply trans_check_one_cofix.
Qed.

Lemma trans_check_rec_kind Σ k f :
  ST.check_recursivity_kind (lookup_env Σ) k f = TT.check_recursivity_kind (lookup_env (trans_global_env Σ)) k f.
Proof.
  unfold ST.check_recursivity_kind, TT.check_recursivity_kind.
  rewrite trans_lookup.
  destruct SE.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint Σ p n mfix :
  on_free_vars_mfix p n mfix ->
  TT.wf_fixpoint (trans_global_env Σ) (map (map_def trans trans) mfix) =
  ST.wf_fixpoint Σ mfix.
Proof.
  intros hmfix.
  unfold ST.wf_fixpoint, TT.wf_fixpoint, ST.wf_fixpoint_gen, TT.wf_fixpoint_gen.
  f_equal.
  - rewrite forallb_map /=.
    setoid_rewrite trans_isLambda => //.
  - rewrite map_map_compose.
    rewrite (map_option_out_check_one_fix hmfix).
    destruct map_option_out as [[]|] => //.
    now rewrite (trans_check_rec_kind Σ).
Qed.

Lemma trans_wf_cofixpoint Σ mfix :
  TT.wf_cofixpoint (trans_global_env Σ) (map (map_def trans trans) mfix) =
  ST.wf_cofixpoint Σ mfix.
Proof.
  unfold ST.wf_cofixpoint, TT.wf_cofixpoint.
  unfold ST.wf_cofixpoint_gen, TT.wf_cofixpoint_gen.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_cofix.
  destruct map_option_out as [[]|] => //.
  now rewrite (trans_check_rec_kind Σ).
Qed.

Lemma type_mkApps_napp `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ f u T T' :
  ~~ isApp f ->
  TT.typing Σ Γ f T ->
  typing_spine Σ Γ T u T' ->
  TT.typing Σ Γ (mkApps f u) T'.
Proof.
  intros hf hty hsp.
  depelim hsp. simpl; auto.
  eapply type_ws_cumul_pb; tea.
  eapply type_mkApps; tea.
  econstructor; tea.
Qed.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    TT.fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
  ST.cofix_guard Σ Γ mfix ->
  TT.cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Lemma trans_it_mkLambda_or_LetIn Γ T :
  trans (it_mkLambda_or_LetIn Γ T) = it_mkLambda_or_LetIn (trans_local Γ) (trans T).
Proof.
  induction Γ using rev_ind.
  * cbn; auto.
  * rewrite /=. rewrite PCUICAstUtils.it_mkLambda_or_LetIn_app [trans_local _]map_app
      it_mkLambda_or_LetIn_app.
    destruct x as [na [b|] ty] => /=; cbn; now f_equal.
Qed.

Lemma All2i_All2_mapi {A B C D} P (f : nat -> A -> B) (g : nat -> C -> D) l l' :
  All2i (fun i x y => P (f i x) (g i y)) 0 l l' ->
  All2 P (mapi f l) (mapi g l').
Proof.
  rewrite /mapi. generalize 0.
  induction 1; constructor; auto.
Qed.

Lemma All2i_sym {A B} (P : nat -> A -> B -> Type) n l l' :
  All2i (fun i x y => P i y x) n l' l ->
  All2i P n l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma eq_names_subst_context_pcuic nas Γ s k :
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * rewrite subst_context_nil. constructor.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance_pcuic nas (Γ : context) u :
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

Lemma map_expand_lets_lift_cancel Γ n ts :
  n = #|Γ| ->
  map (expand_lets Γ) (map (lift0 n) ts) =
  map (lift0 (context_assumptions Γ)) ts.
Proof.
  intros ->. solve_all. eapply All_refl.
  intros x. now rewrite expand_lets_lift_cancel.
Qed.

Lemma expand_lets_k_subst_comm Δ k s T :
  expand_lets_k Δ k (subst s k T) =
  subst (map (expand_lets Δ) s) k (expand_lets_k Δ (#|s| + k) T).
Proof.
  rewrite /expand_lets_k.
  rewrite distr_lift_subst_rec.
  rewrite -{1}(Nat.add_0_r k).
  rewrite distr_subst_rec (Nat.add_comm #|s|). len.
  rewrite map_map_compose. reflexivity.
Qed.

Lemma context_assumptions_set_binder_name nas Γ :
  #|nas| = #|Γ| ->
  context_assumptions (map2 set_binder_name nas Γ) = context_assumptions Γ.
Proof.
  induction nas in Γ |- *; destruct Γ; cbn => //.
  intros [=]. destruct c as [na [b|] ty]; cbn; auto.
  rewrite IHnas //.
Qed.

Lemma extended_subst_set_binder_name nas Γ k :
  #|nas| = #|Γ| ->
  extended_subst (map2 set_binder_name nas Γ) k =
  extended_subst Γ k.
Proof.
  induction nas in Γ, k |- *; destruct Γ; cbn => //.
  intros [=]. destruct c as [na [b|] ty]; cbn; f_equal; eauto.
  len. rewrite map2_length //. rewrite H0.
  rewrite IHnas //. rewrite context_assumptions_set_binder_name //.
Qed.

Lemma expand_lets_set_binder_name nas Γ t :
  #|nas| = #|Γ| ->
  expand_lets (map2 set_binder_name nas Γ) t = expand_lets Γ t.
Proof.
  induction nas in Γ |- *; destruct Γ; cbn => //.
  intros [=]. rewrite /expand_lets /expand_lets_k.
  destruct c as [na [b|] ty]; cbn; try len;
  rewrite extended_subst_set_binder_name // map2_length // H0
    !context_assumptions_set_binder_name //.
Qed.

Lemma expand_lets_k_lift n k k' Γ t :
  expand_lets_k (lift_context n k Γ) k' (lift n (#|Γ| + k + k') t) =
  lift n (k + k' + context_assumptions Γ) (expand_lets_k Γ k' t).
Proof.
  rewrite /expand_lets /expand_lets_k /=.
  rewrite extended_subst_lift_context Nat.add_0_r.
  epose proof (distr_lift_subst_rec _ _ _ k' (k + context_assumptions Γ)).
  len. rewrite permute_lift. lia. rewrite !Nat.add_assoc /= in H.
  rewrite (Nat.add_comm _ k') Nat.add_assoc.
  relativize #|Γ|. erewrite <- H. 2:now len.
  now len.
Qed.

Lemma lift_expand_lets_k Δ Γ t :
  closed_ctx Γ ->
  on_free_vars (shiftnP (#|Γ| + #|Δ|) xpred0) t ->
  lift (context_assumptions Δ) #|Δ| (expand_lets_k Γ #|Δ| t) =
  expand_lets_k Γ (#|Δ| + context_assumptions Δ) (lift (context_assumptions Δ) #|Δ| t).
Proof.
  intros cl ont.
  rewrite {1}/expand_lets_k.
  rewrite -{1}(Nat.add_0_r #|Δ|).
  rewrite /expand_lets_k.
  rewrite (lift_closed _ _ (lift (context_assumptions Δ) #|Δ| t) _).
  rewrite on_free_vars_closedn.
  rewrite (Nat.add_comm #|Δ|).
  rewrite -shiftnP_add.
  eapply on_free_vars_lift_impl; rewrite shiftnP_add Nat.add_comm //.
  rewrite (lift_closed _ _ t).
  rewrite on_free_vars_closedn Nat.add_comm //.
  rewrite distr_lift_subst_rec. len.
  rewrite (lift_closed _ _ t).
  rewrite on_free_vars_closedn Nat.add_comm //.
  rewrite closed_subst_map_lift. len.
  rewrite on_free_vars_closedn //. rewrite Nat.add_comm //.
Qed.

Lemma expand_lets_comm Γ Δ t :
  closed_ctx Γ ->
  on_free_vars (shiftnP (#|Γ| + #|Δ|) xpred0) t ->
  expand_lets (expand_lets_ctx Γ Δ) (expand_lets_k Γ #|Δ| t) =
  expand_lets_k Γ (context_assumptions Δ) (expand_lets Δ t).
Proof.
  intros clΓ ont.
  rewrite {2}/expand_lets {3}/expand_lets_k.
  rewrite PCUICInductives.expand_lets_k_subst_comm.
  len. cbn.
  rewrite {1}/expand_lets {1}/expand_lets_k.
  len. f_equal.
  - rewrite /expand_lets_k /expand_lets_ctx /expand_lets_k_ctx subst_extended_subst; len.
    rewrite extended_subst_lift_context; try len. cbn.
    rewrite !map_map_compose. apply map_ext => x.
    now rewrite Nat.add_comm.
  - rewrite lift_expand_lets_k //.
Qed.

Lemma to_extended_list_smash_context_eq Δ Δ' k :
  #|Δ| = #|Δ'| ->
  assumption_context Δ ->
  assumption_context Δ' ->
  to_extended_list_k Δ k =
  to_extended_list_k Δ' k.
Proof.
  induction Δ in Δ', k |- *; cbn; destruct Δ' => /= //.
  intros [=].
  intros ass ass'. destruct a as [na [b|] ty]. exfalso; depelim ass.
  destruct c as [na' [b'|] ty']; cbn. exfalso; depelim ass'.
  rewrite !(reln_acc [_]). f_equal. eapply IHΔ => //.
  now depelim ass. now depelim ass'.
Qed.

Lemma on_free_vars_subst_k s k t :
  forallb (on_free_vars xpred0) s ->
  on_free_vars (shiftnP (#|s| + k) xpred0) t ->
  on_free_vars (shiftnP k xpred0) (subst s k t).
Proof.
  intros ons ont.
  eapply on_free_vars_impl; [|eapply on_free_vars_subst_gen]; tea.
  intros i. rewrite /substP /shiftnP.
  repeat nat_compare_specs; cbn; auto.
  nat_compare_specs => //.
Qed.

Lemma on_free_vars_expand_lets_k P Γ k t :
  on_free_vars_ctx P Γ ->
  on_free_vars (shiftnP (k + #|Γ|) P) t ->
  on_free_vars (shiftnP (k + context_assumptions Γ) P) (expand_lets_k Γ k t).
Proof.
  intros HΓ Ht.
  rewrite /expand_lets_k /=.
  eapply on_free_vars_impl; cycle 1.
  - eapply on_free_vars_subst_gen.
    1:eapply on_free_vars_extended_subst; eauto.
    rewrite -> on_free_vars_lift. eauto.
  - len. rewrite /substP /= /strengthenP /=.
    intros i. simpl. rewrite /shiftnP.
    repeat nat_compare_specs => /= //.
    rewrite Nat.sub_0_r.
    replace (i + #|Γ| - context_assumptions Γ - (k + #|Γ|)) with (i - context_assumptions Γ - k) by lia.
    rewrite /occ_betweenP. repeat nat_compare_specs => /= //.
    rewrite orb_false_r.
    replace (i - context_assumptions Γ - k) with (i - k - context_assumptions Γ) by lia.
    rewrite orb_diag.
    now replace (i - k - context_assumptions Γ) with (i - (k + context_assumptions Γ)) by lia.
Qed.

Lemma on_free_vars_case_predicate_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {P ind mdecl idecl p} :
   let pctx := case_predicate_context ind mdecl idecl p in
   declared_inductive Σ ind mdecl idecl ->
   wf_predicate mdecl idecl p ->
   forallb (on_free_vars P) (pparams p) ->
   on_free_vars_ctx P pctx.
Proof.
  intros pctx decli wfp onps.
  rewrite /pctx /case_predicate_context /case_predicate_context_gen.
  eapply alpha_eq_on_free_vars_ctx. symmetry.
  eapply eq_binder_annots_eq.
  eapply (wf_pre_case_predicate_context_gen wfp).
  rewrite /pre_case_predicate_context_gen.
  eapply on_free_vars_ctx_inst_case_context; tea. reflexivity.
  rewrite test_context_k_closed_on_free_vars_ctx.
  rewrite (wf_predicate_length_pars wfp).
  rewrite (declared_minductive_ind_npars decli).
  exact (on_free_vars_ind_predicate_context (ind:=ind) decli).
Qed.

#[global] Hint Resolve declared_inductive_closed_params : pcuic.

Lemma trans_case_branch_type {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {ci : case_info} {mdecl idecl cdecl i p br} :
  declared_constructor Σ (ci, i) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  eq_context_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  eq_context_upto_names (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
  on_free_vars_terms (shiftnP #|Γ| xpred0) p.(pparams) ->
  on_free_vars (shiftnP (S #|ind_indices idecl|) (shiftnP #|Γ| xpred0)) (preturn p) ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  let p' := map_predicate id trans trans (map_context trans) p in
  let br' :=  (trans_branch p' (map_branch trans (map_context trans) br)) in
  let cbctx := case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl in
  let cbt' := case_branch_type ci (trans_minductive_body mdecl)
    (trans_one_ind_body mdecl (inductive_ind ci) idecl) p' br'
  (it_mkLambda_or_LetIn
    (trans_local (case_predicate_context ci mdecl idecl p))
    (preturn
        (map_predicate id trans trans (map_context trans) p)))
  i (trans_constructor_body (inductive_ind ci) mdecl cdecl) in
  (cbt'.1 = trans_local (smash_context [] cbctx)) *
  (cbt'.2 = trans (expand_lets cbctx (case_branch_type ci mdecl idecl p br ptm i cdecl).2)).
Proof.
  intros declc cu wfp wfbr wfpctx wfbctx onps ptm p' br'.
  have wfbr' : wf_branch cdecl (map_branch trans (map_context trans) br).
  { move: wfbr. rewrite /wf_branch /wf_branch_gen /=.
    intros h. now rewrite forget_types_map_context. }
  rewrite /case_branch_type /case_branch_type_gen /=.
  set (brctx' := case_branch_context_gen _ _ _ _ _ _).
  have eqbrctx' : brctx' = trans_local (smash_context []
    (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)).
  { rewrite /brctx' [case_branch_context_gen _ _ _ _ _ _](trans_inst_case_branch_context
      (Γ := Γ)
      (br := br) wfp wfbr declc) => //.
    erewrite <- PCUICCasesContexts.inst_case_branch_context_eq => //. }
  split => //.
  rewrite expand_lets_mkApps trans_mkApps !lengths /=.
  rewrite !map_app (map_map_compose _ _ _ _ trans).
  f_equal.
  { relativize #|cstr_args cdecl|. erewrite expand_lets_lift_cancel. 2:rewrite case_branch_context_length_args //.
    rewrite case_branch_context_assumptions //.
    rewrite (trans_lift _ (shiftnP #|Γ| xpred0)).
    { rewrite /ptm on_free_vars_it_mkLambda_or_LetIn.
      apply/andP; split.
      eapply (on_free_vars_case_predicate_context declc wfp) => //.
      rewrite (case_predicate_context_length_indices wfp) => //. }
    rewrite -trans_it_mkLambda_or_LetIn //. }
  have onfvsargs : on_free_vars_ctx (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)
    (cstr_args cdecl).
  { pose proof (declared_constructor_closed_args declc).
    now eapply closedn_ctx_on_free_vars. }
  f_equal.
  rewrite !map_map_compose /id.
  pose proof (declared_constructor_closed_indices declc).
  eapply forallb_All in H.
  eapply All_map_eq. eapply All_impl; tea; cbv beta.
  intros x cl.
  { rewrite -(trans_expand_lets (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)) //.
    rewrite shiftnP_add.
    eapply closedn_on_free_vars. red in cl. red. rewrite -cl.
    f_equal. lia.
    rewrite -trans_inds.
    rewrite -trans_subst_instance.
    have fvsexpx : on_free_vars
      (shiftnP (context_assumptions (cstr_args cdecl))
         (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0))
          (expand_lets (cstr_args cdecl) x)@[puinst p].
    { eapply (@closedn_on_free_vars xpred0) in cl.
      rewrite on_free_vars_subst_instance.
      eapply (on_free_vars_expand_lets_k _ _ 0) => //.
      rewrite shiftnP_add. red; rewrite -cl.
      f_equal. f_equal. lia. }
    rewrite -(trans_subst (shiftnP (context_assumptions (cstr_args cdecl)) (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)) xpred0) //.
    eapply (inds_is_open_terms []).
    rewrite -trans_subst_instance_ctx.
    have fvssi : on_free_vars
      (shiftnP #|(ind_params mdecl)@[puinst p]|
        (shiftnP (context_assumptions (cstr_args cdecl)) xpred0))
      (S.subst (inds (inductive_mind ci) (puinst p) (SE.ind_bodies mdecl))
        (#|ind_params mdecl| +
          context_assumptions (trans_local (cstr_args cdecl)))
        (expand_lets (cstr_args cdecl) x)@[puinst p]).
    { len. rewrite shiftnP_add.
      eapply on_free_vars_subst_k. eapply (inds_is_open_terms []).
      len. rewrite shiftnP_add in fvsexpx.
      red; rewrite -fvsexpx. f_equal. f_equal. lia. }
    rewrite -(trans_expand_lets_k (shiftnP (context_assumptions (cstr_args cdecl)) xpred0)) //.
    rewrite on_free_vars_ctx_subst_instance. eapply on_free_vars_ctx_impl.
    2:{ eapply closedn_ctx_on_free_vars. eapply (declared_inductive_closed_params declc). }
    { intros i'. rewrite shiftnP0 //. }
    { len in fvssi. now len. }
    rewrite -map_rev.
    rewrite -(trans_subst (shiftnP (context_assumptions (cstr_args cdecl) + context_assumptions (ind_params mdecl))
      xpred0) (shiftnP #|Γ| xpred0)).
    { relativize (context_assumptions (ind_params mdecl)).
      eapply on_free_vars_expand_lets_k => //.
      destruct declc.
      rewrite on_free_vars_ctx_subst_instance; eauto with pcuic.
      2:now len.
      rewrite shiftnP_add in fvssi. len in fvssi. len.
      rewrite Nat.add_comm => //. }
    { rewrite forallb_rev. eapply forallb_All in onps. solve_all. }
    f_equal.
    rewrite /case_branch_context /case_branch_context_gen.
    rewrite expand_lets_set_binder_name. len.
    { eapply All2_length in wfbctx.
      now rewrite cstr_branch_context_length in wfbctx. }
    rewrite /pre_case_branch_context_gen /inst_case_context.
    relativize #|cstr_args cdecl|.
    erewrite expand_lets_subst_comm. 2:now len.
    rewrite !context_assumptions_subst_instance.
    rewrite cstr_branch_context_assumptions Nat.add_0_r.
    f_equal.
    rewrite /cstr_branch_context; len.
    rewrite Nat.add_comm.
    rewrite expand_lets_subst_instance.
    relativize (SE.context_assumptions _).
    erewrite <-expand_lets_subst_comm. len.
    rewrite subst_instance_expand_lets_ctx.
    relativize #|cstr_args cdecl|.
    erewrite expand_lets_comm. len.
    rewrite subst_instance_subst_context.
    rewrite instantiate_inds //. exact declc. 4:now len.
    4:now len. now rewrite Nat.add_comm. rewrite closedn_subst_instance_context.
    destruct declc. eauto with pcuic.
    len. eapply on_free_vars_subst_k. eapply (inds_is_open_terms []).
    len. rewrite on_free_vars_subst_instance.
    eapply closedn_on_free_vars. rewrite Nat.add_assoc //. }
  cbn. f_equal.
  rewrite -(trans_smash_context (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) []) //.
  rewrite expand_lets_mkApps /= map_app trans_mkApps /=.
  f_equal. f_equal; rewrite map_app. f_equal.
  rewrite map_expand_lets_lift_cancel. now rewrite (case_branch_context_length_args wfbr).
  rewrite (case_branch_context_assumptions wfbr).
  rewrite !map_map_compose.
  eapply forallb_All in onps. eapply All_map_eq, All_impl; tea; cbv beta.
  intros x op. rewrite (trans_lift _ (shiftnP #|Γ| xpred0)) //.
  rewrite -(to_extended_list_case_branch_context ci mdecl p _ _ (Forall2_All2 _ _ wfbr)).
  rewrite map_expand_lets_to_extended_list.
  rewrite -[to_extended_list _]trans_to_extended_list.
  f_equal. eapply to_extended_list_smash_context_eq; pcuic; len.
  now rewrite (case_branch_context_assumptions wfbr).
Qed.

Lemma untyped_subslet_inds Γ ind u u' mdecl :
  untyped_subslet Γ (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance u' (arities_context (ind_bodies mdecl))).
Proof.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4.
  unfold inds.
  induction l using rev_ind; simpl; first constructor.
  simpl. rewrite length_app /= => Hlen.
  unfold arities_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=.
  rewrite /= Nat.add_1_r /=.
  constructor.
  rewrite -rev_map_spec. apply IHl. lia.
Qed.

Lemma ws_cumul_pb_it_mkProd_or_LetIn_smash {cf} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ T :
  is_closed_context Γ -> is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ T = it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T).
Proof.
  intros hfvΓ hfv.
  eapply into_ws_cumul_pb. 1-3:fvs.
  2:{ move: hfv.
      rewrite !on_free_vars_it_mkProd_or_LetIn.
      move/andP=> [] onΔ onT.
      rewrite on_free_vars_ctx_smash // /=.
      len. cbn.
      eapply (on_free_vars_expand_lets_k _ _ 0) => //. }
  eapply red_conv_conv; [|reflexivity].
  clear hfvΓ hfv.
  induction Δ in Γ, T |- * using ctx_length_rev_ind.
  - cbn. rewrite expand_lets_nil. reflexivity.
  - rewrite it_mkProd_or_LetIn_app.
    destruct d as [na [b|] ty]; cbn; [rewrite smash_context_app_def expand_lets_vdef|rewrite smash_context_app_ass expand_lets_vass].
    * etransitivity.
      eapply red1_red. constructor.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
      eapply X. now len.
    * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      eapply red_prod. reflexivity.
      now eapply X.
Qed.

Lemma map_expand_lets_to_extended_list_k_above Γ Δ :
  map (expand_lets Γ) (to_extended_list_k Δ #|Γ|) = to_extended_list_k Δ (context_assumptions Γ).
Proof.
  unfold to_extended_list_k.
  rewrite -(Nat.add_0_r #|Γ|).
  rewrite reln_lift.
  rewrite map_map_compose.
  setoid_rewrite expand_lets_lift_cancel.
  rewrite -reln_lift Nat.add_0_r //.
Qed.

Lemma on_free_vars_to_extended_list_k P ctx k :
  forallb (on_free_vars (shiftnP (k + #|ctx|) P)) (to_extended_list_k ctx k).
Proof.
  rewrite /to_extended_list /to_extended_list_k.
  have: (forallb (on_free_vars (shiftnP (k + #|ctx|) P)) []) by easy.
  generalize (@nil term).
  induction ctx in k |- *; intros l Hn.
  - simpl; auto.
  - simpl.
    destruct a as [? [?|] ?].
    * rewrite /= Nat.add_succ_r in Hn.
      specialize (IHctx (S k) l Hn).
      now rewrite Nat.add_succ_r Nat.add_1_r.
    * rewrite Nat.add_succ_r Nat.add_1_r. eapply (IHctx (S k)).
      rewrite -[_ + _](Nat.add_succ_r k #|ctx|) /= Hn.
      rewrite /shiftnP.
      nat_compare_specs => /= //.
Qed.

Lemma trans_type_of_constructor {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {wfΣ' : wf_trans Σ}
  {mdecl idecl cdecl ind i u} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  consistent_instance_ext (trans_global Σ)
    (ind_universes (trans_minductive_body mdecl)) u ->
  ws_cumul_pb (cf := cf' cf) Conv (trans_global Σ) [] (trans (ST.type_of_constructor mdecl cdecl (ind, i) u))
  (TT.type_of_constructor
    (trans_minductive_body mdecl)
    (trans_constructor_body (inductive_ind ind) mdecl cdecl)
    (ind,i)
    u).
Proof.
  intros oncstr onu.
  unfold ST.type_of_constructor.
  rewrite (trans_subst (shiftnP #|ind_bodies mdecl| xpred0) xpred0).
  eapply declared_constructor_closed_gen_type in oncstr.
  len in oncstr. eapply closedn_on_free_vars. now rewrite closedn_subst_instance.
  eapply (inds_is_open_terms []).
  unfold TT.type_of_constructor.
  rewrite trans_inds.
  eapply (untyped_substitution_ws_cumul_pb (pb:=Conv) (Γ := []) (Γ'' := [])).
  eapply untyped_subslet_inds.
  eapply (inds_is_open_terms []). instantiate (1:=u).
  simpl. rewrite app_context_nil_l.
  pose proof (on_declared_constructor oncstr) as [[onmind onind] [cs [hnth onc]]].
  rewrite (cstr_eq onc).
  rewrite !subst_instance_it_mkProd_or_LetIn.
  rewrite !trans_it_mkProd_or_LetIn.
  have clctx : is_closed_context
  ((arities_context (mapi (trans_one_ind_body mdecl) (ind_bodies mdecl)))@[u],,,
   trans_local (ind_params mdecl)@[u]).
  { pose proof (trans_declared_constructor _ _ _ _ _ oncstr).
    epose proof (declared_inductive_closed_params (cf := cf' cf) (Σ := trans_global Σ) H).
    rewrite on_free_vars_ctx_app !on_free_vars_ctx_subst_instance.
    len.
    rewrite closedn_ctx_on_free_vars.
    rewrite trans_subst_instance_ctx.
    rewrite closedn_subst_instance_context.
    eapply closedn_ctx_upwards; tea. lia.
    rewrite andb_true_r. apply closed_ctx_on_free_vars.
    unshelve epose proof (declared_minductive_closed_arities (cf := cf' cf) (Σ := trans_global Σ) (proj1 (proj1 H))).
    apply H1. }
  epose proof (declared_constructor_closed oncstr).
  rewrite /closed_constructor_body in H.
  move/andP: H => [] /andP[] clargs cli clty.
  have clterm : is_open_term
    ((arities_context (mapi (trans_one_ind_body mdecl) (ind_bodies mdecl)))@[u],,,
    map trans_decl (ind_params mdecl)@[u])
    (it_mkProd_or_LetIn (map trans_decl (cstr_args cdecl)@[u])
      (trans (cstr_concl mdecl (inductive_ind (ind, i).1) cdecl)@[u])).
  { rewrite -trans_it_mkProd_or_LetIn.
    eapply trans_on_free_vars. len.
    rewrite on_free_vars_it_mkProd_or_LetIn.
    apply/andP; split. rewrite on_free_vars_ctx_subst_instance.
    eapply closedn_ctx_on_free_vars. now rewrite Nat.add_comm.
    rewrite shiftnP_add. len. rewrite /cstr_concl.
    rewrite subst_instance_mkApps on_free_vars_mkApps /=.
    rewrite forallb_map forallb_app. apply/and3P; split.
    rewrite /shiftnP orb_false_r. apply Nat.ltb_lt.
    assert (#|ind_bodies mdecl| > 0).
    { destruct oncstr as [[] ?]. clear hnth. eapply nth_error_Some_length in e. lia. }
    lia.
    eapply forallb_impl. 2:eapply on_free_vars_to_extended_list_k.
    intros x hx. rewrite on_free_vars_subst_instance.
    rewrite Nat.add_assoc. rewrite -[shiftnP (_ + #|ind_bodies mdecl|) _]shiftnP_add.
    intros H; exact H. solve_all.
    rewrite on_free_vars_subst_instance. eapply closedn_on_free_vars in H.
    now rewrite Nat.add_comm (Nat.add_comm _ #|ind_params mdecl|) Nat.add_assoc. }
  eapply ws_cumul_pb_it_mkProd_or_LetIn.
  { eapply ws_cumul_ctx_pb_rel_app.
    rewrite -trans_subst_instance_ctx.
    now eapply ws_cumul_ctx_pb_refl. }
  etransitivity.
  eapply ws_cumul_pb_it_mkProd_or_LetIn_smash => //.
  have <-: (expand_lets (map trans_decl (cstr_args cdecl)@[u])
    (trans (cstr_concl mdecl (inductive_ind (ind, i).1) cdecl)@[u])) =
    (trans_cstr_concl mdecl (inductive_ind ind)
    (smash_context [] (trans_local (cstr_args cdecl)))
    (map (expand_lets (trans_local (cstr_args cdecl)))
       (map trans (cstr_indices cdecl))))@[u].
  { rewrite /cstr_concl /trans_cstr_concl.
    rewrite !subst_instance_mkApps !trans_mkApps.
    rewrite expand_lets_mkApps. f_equal.
    rewrite /trans_cstr_concl_head. len.
    rewrite /cstr_concl_head /=.
    relativize #|cstr_args cdecl|. erewrite expand_lets_tRel.
    cbn. rewrite !context_assumptions_map context_assumptions_subst_instance //.
    now len.
    rewrite !map_app. f_equal.
    rewrite !subst_instance_to_extended_list_k. len; cbn.
    rewrite trans_to_extended_list.
    relativize #|cstr_args cdecl|. erewrite map_expand_lets_to_extended_list_k_above.
    rewrite trans_subst_instance_ctx.
    rewrite [map _ _]trans_subst_instance_ctx.
    rewrite context_assumptions_subst_instance //.
    now len. now len.
    rewrite [map trans_decl _]trans_subst_instance_ctx.
    rewrite (map_map_compose _ _ _ _ trans).
    setoid_rewrite trans_subst_instance.
    rewrite -(map_map_compose _ _ _ trans).
    rewrite !map_map_compose.
    now setoid_rewrite subst_instance_expand_lets. }
  rewrite ![map trans_decl _ ]trans_subst_instance_ctx.
  rewrite subst_instance_smash.
  eapply ws_cumul_pb_refl => //.
  now rewrite -trans_subst_instance_ctx.
  rewrite -trans_subst_instance_ctx.
  rewrite on_free_vars_it_mkProd_or_LetIn. len.
  cbn.
  rewrite on_free_vars_ctx_smash //.
  rewrite -closedP_shiftnP.
  rewrite on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_trans. eapply closedn_ctx_on_free_vars.
  now rewrite Nat.add_comm.
  cbn.
  eapply PCUICOnFreeVars.on_free_vars_expand_lets_k. now len.
  rewrite Nat.add_comm on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_trans.
  now eapply closedn_ctx_on_free_vars.
  move: clterm. len.
  rewrite on_free_vars_it_mkProd_or_LetIn.
  move/andP => [] _. now len.
Qed.

Lemma trans_eq_annots (Γ : list aname) Δ :
  eq_annots Γ Δ ->
  eq_annots Γ (trans_local Δ).
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma trans_wf_predicate ci mdecl idecl p :
  wf_predicate mdecl idecl p ->
  wf_predicate (trans_minductive_body mdecl)
    (trans_one_ind_body mdecl (inductive_ind ci) idecl)
    (map_predicate id trans trans trans_local p).
Proof.
  move=> [] eqps eqanns.
  split. cbn.
  now rewrite length_map //.
  rewrite forget_types_map_context.
  move: eqanns; rewrite /idecl_binder /= => eqanns.
  depelim eqanns. rewrite H0.
  constructor. cbn. auto.
  now apply trans_eq_annots.
Qed.

Lemma lookup_globals_trans decls c : lookup_globals (trans_global_decls decls) c = List.map trans_global_decl (lookup_globals decls c).
Proof.
  move: decls. elim => //= => [[kn d]] decls //=.
  elim: eqb_spec => //= -> -> //=.
Qed.

Lemma extends_strictly_on_decls_trans {Σ Σ' : global_env} : extends_strictly_on_decls Σ Σ' -> extends_strictly_on_decls (trans_global_env Σ) (trans_global_env Σ').
Proof.
  intros [onu [Σ'' eq]].
  split => //. exists (trans_global_decls Σ'').
  rewrite /= eq /trans_global_decls /= map_app //.
Qed.

Lemma strictly_extends_decls_trans {Σ Σ' : global_env} : strictly_extends_decls Σ Σ' ->
  strictly_extends_decls (trans_global_env Σ) (trans_global_env Σ').
Proof.
  intros [onu [Σ'' eq]].
  split => //. exists (trans_global_decls Σ'').
  rewrite /= eq /trans_global_decls /= map_app //.
Qed.

Lemma extends_trans {Σ Σ' : global_env} : extends Σ Σ' -> extends (trans_global_env Σ) (trans_global_env Σ').
Proof.
  intros [onu eq].
  split => // c. specialize (eq c). move: eq => [Σ'' eq].
  exists (List.map trans_global_decl Σ'').
  cbv [lookup_envs] in *.
  rewrite /trans_global_env /= !lookup_globals_trans eq map_app //.
Qed.

Lemma extends_decls_trans {Σ Σ' : global_env} : extends_decls Σ Σ' ->
  extends_decls (trans_global_env Σ) (trans_global_env Σ').
Proof.
  intros [onu eq].
  split => // c. specialize (eq c). move: eq => [Σ'' eq].
  exists (List.map trans_global_decl Σ'').
  cbv [lookup_envs] in *.
  rewrite /trans_global_env /= !lookup_globals_trans eq map_app //.
Qed.

(* we make this transparent so we can make use of the fact that the sort is the same in the next proof *)
Lemma weaken_prop_gen {cf} : weaken_env_prop_gen cumulSpec0 (lift_typing typing) (fun Σ Σ' => wf_trans Σ × wf_trans Σ' × extends Σ Σ')
  (lift_typing
   (λ (Σ : global_env_ext) (Γ : context) (t T : term),
      typing (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans t) (trans T))).
Proof.
  intros Σ Σ' u wf wf' ext Γ j Hj.
  apply lift_typing_impl with (1 := Hj); intros.
  eapply (weakening_env (trans_global (Σ, u))), extends_trans; eauto; destruct ext as (wfΣ&wfΣ'&ext); eauto.
Defined.

(* to get a version that fits in one of the non-_gen lemmas, we need a strict enough version of extension to imply [wf_trans] from extension. *)
Lemma weaken_prop {cf} : weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing)
  (fun Σ Γ j => wf_trans Σ -> lift_typing0 (fun t T =>
      typing (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans t) (trans T)) j).
Proof.
  pose weaken_prop_gen as H.
  cbv [weaken_env_strictly_on_decls_prop weaken_env_prop_gen] in *.
  repeat (intro; let x := lazymatch goal with x : _ |- _ => x end in pose (H x) as H'; subst H; rename H' into H).
  move => Hext Γ j Hj wftΣ'.
  pose (fun v wfΣ' wfΣ => H (wfΣ, (wfΣ', ltac:(tc))) Γ j v) as H'; subst H; rename H' into H.
  eapply strictly_extends_decls_wf with (2 := strictly_extends_decls_trans Hext) in wftΣ' as wftΣ.
  eapply H; eauto.
Qed.

Lemma trans_arities_context mdecl :
  arities_context (ind_bodies (trans_minductive_body mdecl)) =
  trans_local (arities_context (ind_bodies mdecl)).
Proof.
  rewrite /arities_context.
  rewrite !rev_map_spec -map_rev -map_rev.
  cbn. rewrite rev_mapi /trans_local map_map_compose map_mapi. cbn.
  rewrite mapi_cst_map. solve_all.
  eapply All_refl. intros; cbn. reflexivity.
Qed.

Lemma trans_subst_telescope p q s n Γ :
  on_free_vars_terms p s -> on_free_vars_ctx q (List.rev Γ) ->
  trans_local (subst_telescope s n Γ) =
  subst_telescope (map trans s) n (trans_local Γ).
Proof.
  induction Γ in s, n, q|- *.
  - cbn; auto.
  - intros ons; rewrite /= on_free_vars_ctx_app => /andP[] /= ona onΓ.
    f_equal; eauto. rewrite!PCUICContextSubst.subst_telescope_cons /=.
    rewrite (trans_subst_decl p q) //. move/andP: ona. now rewrite shiftnP0.
    f_equal. rewrite mapi_rec_Sk. rewrite -(IHΓ (shiftnP 1 q)) //.
    rewrite /subst_telescope. f_equal. unfold mapi.
    apply mapi_rec_ext. intros. now rewrite Nat.add_succ_r.
Qed.

Lemma All2i_All2 {A B} {P : nat -> A -> B -> Type} {Q} n l l' :
  All2i P n l l' ->
  (forall i x y, P i x y -> Q x y) ->
  All2 Q l l'.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma eq_annots_expand_lets_ctx (Γ : list aname) (Δ Δ' : context) :
  eq_annots Γ (expand_lets_ctx Δ Δ') <-> eq_annots Γ Δ'.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  etransitivity. eapply eq_annots_subst_context.
  eapply eq_annots_lift_context.
Qed.

(** We need to go through the intermediate definition which just maps the translation
    on inductive declarations but does not perform smashing of the arguments contexts. *)

Definition map_trans_constructor_body (d : PCUICEnvironment.constructor_body) :=
  let args := trans_local d.(cstr_args) in
  let indices := map trans d.(cstr_indices) in
  {| cstr_name := d.(PCUICEnvironment.cstr_name);
     cstr_args := args;
     cstr_indices := indices;
     cstr_type := trans d.(cstr_type);
     cstr_arity := d.(PCUICEnvironment.cstr_arity) |}.

Definition map_trans_one_ind_body (d : PCUICEnvironment.one_inductive_body) :=
  {| ind_name := d.(PCUICEnvironment.ind_name);
     ind_relevance := d.(PCUICEnvironment.ind_relevance);
     ind_indices := trans_local d.(PCUICEnvironment.ind_indices);
     ind_type := trans d.(PCUICEnvironment.ind_type);
     ind_sort := d.(PCUICEnvironment.ind_sort);
     ind_kelim := d.(PCUICEnvironment.ind_kelim);
     ind_ctors := List.map map_trans_constructor_body d.(PCUICEnvironment.ind_ctors);
     ind_projs := List.map trans_projection_body d.(PCUICEnvironment.ind_projs) |}.

Definition map_trans_minductive_body md :=
  {| ind_finite := md.(PCUICEnvironment.ind_finite);
     ind_npars := md.(PCUICEnvironment.ind_npars);
     ind_params := trans_local md.(PCUICEnvironment.ind_params);
     ind_bodies := map map_trans_one_ind_body md.(PCUICEnvironment.ind_bodies);
     ind_universes := md.(PCUICEnvironment.ind_universes);
     ind_variance := md.(PCUICEnvironment.ind_variance)
  |}.

Lemma trans_case_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {ci c mdecl idecl cdecl p br} {Γ : context} :
  declared_constructor Σ (ci, c) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  eq_context_upto_names (bcontext br)	(cstr_branch_context ci mdecl cdecl) ->
  on_free_vars_terms (shiftnP #|Γ| xpred0) p.(pparams) ->
  let p' := map_predicate id trans trans (map_context trans) p in
  let br' := map_branch trans (map_context trans) br in
  trans_local (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) =
  inst_case_branch_context p' br'.
Proof.
  intros declc wfp wfbr onbctx onpars.
  intros p' br'.
  have onfvsargs : on_free_vars_ctx (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)
  (cstr_args cdecl).
  { pose proof (declared_constructor_closed_args declc).
    now eapply closedn_ctx_on_free_vars. }
  have fvssi : on_free_vars_ctx
    (shiftnP #|ind_params mdecl| xpred0)
    (subst_context
      (inds (inductive_mind ci) (abstract_instance (ind_universes mdecl))
        (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)).
    { eapply on_free_vars_ctx_subst_context. len.
      now rewrite Nat.add_comm. eapply (inds_is_open_terms []). }
  erewrite <-(PCUICCasesContexts.inst_case_branch_context_eq
    (ind := ci) (mdecl := map_trans_minductive_body mdecl)
    (cdecl := map_trans_constructor_body cdecl)).
  rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
  rewrite trans_local_set_binder. f_equal.
  rewrite /br' /=.
  now rewrite forget_types_map_context.
  rewrite /inst_case_context.
  rewrite (trans_subst_context (shiftnP (context_assumptions (ind_params mdecl)) xpred0) (shiftnP #|Γ| xpred0)).
  { rewrite on_free_vars_ctx_subst_instance.
    eapply (on_free_vars_ctx_cstr_branch_context (c := (ci, c)) declc). }
  rewrite [on_free_vars_terms _ _]forallb_rev //.
  rewrite map_rev. f_equal.
  rewrite /cstr_branch_context.
  rewrite trans_subst_instance_ctx.
  destruct declc.
  rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)); eauto with pcuic.
  f_equal. f_equal.
  rewrite (trans_subst_context
    (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) xpred0) //.
  eapply (inds_is_open_terms []).
  f_equal. rewrite trans_inds //. cbn. now len. now len.
  rewrite /br'. cbn [bcontext map_branch].
  eapply alpha_eq_trans in onbctx.
  etransitivity; tea.
  rewrite /cstr_branch_context.
  destruct declc.
  rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)) //. eauto with pcuic.
  rewrite (trans_subst_context (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) xpred0) //.
  eapply (inds_is_open_terms []).
  rewrite trans_inds. len.
  cbn [cstr_args map_trans_constructor_body].
  cbn [ind_params map_trans_minductive_body].
  cbn [ind_universes map_trans_minductive_body].
  rewrite /inds. len. reflexivity.
Qed.

Lemma All_over_All {cf} Σ Γ wfΓ :
  ST.All_local_env_over (ST.typing Σ)
    (fun (Γ : SE.context)
      (_ : wf_local Σ Γ) (t T : PCUICAst.term)
      (_ : ST.typing Σ Γ t T) =>
      wf_trans Σ ->
    TT.typing (H := cf' cf) (trans_global Σ) (trans_local Γ) (trans t) (trans T)) Γ wfΓ ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ0 : SE.global_env_ext) (Γ0 : SE.context)
          (b ty : PCUICAst.term) =>
          wf_trans Σ ->
        ST.typing Σ0 Γ0 b ty
        × TT.typing (H:=cf' cf) (trans_global Σ0) (trans_local Γ0) (trans b) (trans ty)) Σ) Γ.
Proof.
  intros H.
  induction H;cbn.
  - constructor.
  - constructor.
    + apply IHAll_local_env_over_sorting.
    + cbn in *.
      apply lift_sorting_it_impl with tu => //.
      intros HT wfΣ; split; tas. auto.
  - constructor.
    + apply IHAll_local_env_over_sorting.
    + cbn in *.
      apply lift_sorting_it_impl with tu => //=.
      all: intros HT wfΣ; split; tas. all: auto.
Qed.

Lemma trans_prim_ty p prim_ty : trans (prim_type p prim_ty) = prim_type (map_prim trans p) prim_ty.
Proof.
  destruct p as [? []]; simp prim_type; cbn; reflexivity.
Qed.

Theorem pcuic_expand_lets {cf} (Σ : SE.global_env_ext) Γ t T :
  wf Σ ->
  typing Σ Γ t T ->
  wf_trans Σ ->
  typing (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  intros X X0.
  revert Σ X Γ t T X0.
  apply (typing_ind_env (fun Σ Γ t T =>
    wf_trans Σ ->
    TT.typing (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type
    (fun Σ Γ j => wf_trans Σ -> lift_typing0 (fun t T => TT.typing (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans t) (trans T)) j)
    (fun Σ Γ =>
    wf_trans Σ ->
    TT.All_local_env (TT.lift_typing (TT.typing (H:=cf' cf)) (trans_global Σ)) (trans_local Γ))
  );intros.
  - apply lift_typing_impl with (1 := X) => ?? [] _ ? //; auto.
  - eapply trans_wf_local_env => //. now eapply All_over_All.
  - rewrite (trans_lift _ (shiftnP #|skipn (S n) Γ| xpred0)).
    eapply closed_wf_local in wfΓ; tea.
    eapply closedn_ctx_decl in wfΓ; tea.
    move/andP: wfΓ=> /= [] _ cl.
    rewrite length_skipn. eapply nth_error_Some_length in H.
    now apply closedn_on_free_vars.
    rewrite trans_decl_type.
    eapply type_Rel; eauto.
    now apply map_nth_error.
  - econstructor; eauto.
  - eapply TT.type_Prod;auto.
  - eapply TT.type_Lambda;eauto.
  - eapply TT.type_LetIn;eauto.
  - simpl. rewrite (trans_subst10 _ (shiftnP (S #|Γ|) xpred0) (shiftnP #|Γ| xpred0)); eauto with pcuic.
    eapply type_is_open_term in X2.
    move: X2 => /= /andP[]. rewrite shiftnP_add //.
    now eapply subject_is_open_term in X4.
    eapply type_App; eauto.
  - rewrite trans_subst_instance.
    rewrite trans_cst_type.
    eapply TT.type_Const; eauto.
    + now apply trans_declared_constant.
  - rewrite trans_subst_instance.
    rewrite (trans_ind_type mdecl (inductive_ind ind)).
    eapply TT.type_Ind. eauto.
    + eapply (trans_declared_inductive _ _ _ _ isdecl).
    + now apply trans_consistent_instance_ext.
  - eapply (type_ws_cumul_pb (pb:=Conv)).
    eapply TT.type_Construct. eauto.
    + eapply trans_declared_constructor in isdecl; tea.
    + now apply trans_consistent_instance_ext.
    + red in X. epose proof (declared_constructor_inv weaken_prop _ X isdecl) as [cs [hnth onc]].
      destruct onc. red in on_ctype.
      unshelve eapply lift_sorting_ex_it_impl_gen with (on_ctype _) => //= Hs _.
      rewrite /type_of_constructor.
      rewrite (trans_subst (shiftnP #|ind_bodies mdecl| xpred0) (shiftnP 0 xpred0)).
      pose proof (declared_constructor_closed_gen_type isdecl).
      eapply closedn_on_free_vars. len in H0. now rewrite closedn_subst_instance.
      eapply (inds_is_open_terms []).
      eexists; split => //.
      eapply (substitution (Γ := trans_local Γ) (Δ := []) (T:=tSort _@[u])).
      rewrite trans_inds. eapply (weaken_subslet (Γ := trans_local Γ) (Γ' := [])); eauto with pcuic.
      eapply subslet_inds. eapply (trans_declared_inductive _ _ _ _ isdecl).
      now eapply trans_consistent_instance_ext.
      rewrite trans_arities_context /=.
      rewrite -trans_subst_instance_ctx.
      eapply weaken_ctx; eauto.
      clear hnth. eapply trans_declared_constructor in isdecl; eauto.
      cbn in isdecl.
      unshelve eapply @declared_constructor_to_gen with (cf := cf' cf) in isdecl; eauto.
      epose proof (PCUICUnivSubstitutionTyp.typing_subst_instance_decl (trans_global Σ)
        _ _ _ _ _ _ _ (proj1 (proj1 isdecl)) Hs).
      forward X2. now eapply trans_consistent_instance_ext.
      now rewrite trans_subst_instance_ctx trans_subst_instance.
    + symmetry. cbn.
      eapply (weaken_ws_cumul_pb (Γ := []) (trans_local Γ)).
      now eapply wf_local_closed_context in X0.
      eapply (trans_type_of_constructor isdecl).
      now eapply trans_consistent_instance_ext.
  - rewrite trans_mkApps map_app.
    simpl.
    rewrite /ptm trans_it_mkLambda_or_LetIn.
    rewrite /predctx.
    have hty := validity X6.
    eapply isType_mkApps_Ind_smash in hty as []; tea.
    erewrite <- (trans_case_predicate_context (Σ := Σ)); tea.
    2:{ eapply (wf_predicate_length_pars H0). }
    eapply TT.type_Case; auto. 4-5:split; auto.
    + now apply trans_declared_inductive.
    + rewrite (trans_case_predicate_context (Σ := Σ) (Γ := Γ)); tea.
      rewrite -trans_local_app. now eapply X3.
    + rewrite trans_mkApps map_app in X7. now eapply X7.
    + now eapply trans_wf_predicate.
    + cbn [pparams pcontext].
      rewrite (trans_case_predicate_context (Σ := Σ) (Γ := Γ)); tea.
      now rewrite -trans_local_app.
    + rewrite -trans_ind_predicate_context; eauto with pcuic.
      now eapply alpha_eq_trans.
    + rewrite <- trans_global_ext_constraints.
      eassumption.
    + assumption.
    + eassert (ctx_inst _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
      eassert (PCUICEnvTyping.ctx_inst (fun _ _ _ => wf_trans Σ -> @typing (cf' _) _ _ _ _) _ _ _) as IHctxi.
      { eapply ctx_inst_impl with (1 := X5). intros ? ? [? r]; exact r. }
      move: Hctxi IHctxi. cbn.
      have wfctx : wf_local Σ (Γ ,,, (ind_params mdecl,,, ind_indices idecl)@[puinst p]).
      { eapply PCUICWeakeningTyp.weaken_wf_local; tea. eapply on_minductive_wf_params_indices_inst; tea. }
      move: wfctx.
      clear -wfΣ X9.
      rewrite -map_app -[trans_local _ ++ _]trans_local_app.
      rewrite -[map _ (trans_local _)]trans_subst_instance_ctx /id.
      rewrite -[List.rev (trans_local _)]map_rev.
      generalize (pparams p ++ indices).
      change T.PCUICEnvironment.subst_instance_context with subst_instance_context.
      rewrite -/context.
      generalize (ind_params mdecl ,,, ind_indices idecl : context)@[puinst p] as Δ.
      intros c; revert Γ. induction c using ctx_length_rev_ind.
      * intros Γ l wf.
        intros c; depelim c. constructor.
      * intros Δ. rewrite app_context_assoc.
        rewrite List.rev_app_distr /=.
        move=> l wfctx.
        intros H. depelim H.
        { depelim IHctxi.
          cbn; constructor. now apply t2.
          unshelve epose proof (substitution_wf_local (Γ':=[vass na t]) _ wfctx). shelve.
          { now eapply subslet_ass_tip. }
          rewrite subst_telescope_subst_context in H.
          specialize (X (subst_context [i] 0 Γ) ltac:(now len) _ _ X0 H).
          rewrite subst_telescope_subst_context in IHctxi.
          specialize (X IHctxi).
          rewrite -subst_telescope_subst_context in X.
          rewrite [map trans_decl _](trans_subst_telescope (shiftnP #|Δ| xpred0)
            (shiftnP (S #|Δ|) xpred0)) in X.
          cbn. rewrite (subject_is_open_term t0) //. rewrite List.rev_involutive.
          eapply wf_local_closed_context in wfctx.
          now move: wfctx; rewrite on_free_vars_ctx_app /= => /andP[].
          exact X. }
        { intros c; depelim c.
          constructor.
          destruct (All_local_env_app_inv wfctx) as [w _]. depelim w.
          apply unlift_TermTyp in l0 as Hb.
          unshelve epose proof (substitution_wf_local (Γ':=[vdef na b t]) _ wfctx). shelve.
          { now eapply subslet_def_tip. }
          rewrite subst_telescope_subst_context in H.
          specialize (X (subst_context [b] 0 Γ) ltac:(now len) _ _ X0 H).
          rewrite subst_telescope_subst_context in c.
          specialize (X c).
          rewrite -subst_telescope_subst_context in X.
          rewrite [map trans_decl _](trans_subst_telescope (shiftnP #|Δ| xpred0)
            (shiftnP (S #|Δ|) xpred0)) in X.
          cbn. rewrite (subject_is_open_term Hb) //. rewrite List.rev_involutive.
          eapply wf_local_closed_context in wfctx.
          now move: wfctx; rewrite on_free_vars_ctx_app /= => /andP[].
          exact X. }
    + red. eapply Forall2_map_right, Forall2_map.
      eapply Forall2_All2 in H5.
      eapply All2i_All2_mix_left in X8; tea.
      eapply All2i_nth_hyp in X8.
      eapply All2_Forall2. eapply All2i_All2; tea; cbv beta.
      intros i cdecl br [hnth [wfbr [cd _]]].
      have declc : declared_constructor Σ (ci, i) mdecl idecl cdecl.
      { split; tea. }
      move: wfbr; rewrite /wf_branch /wf_branch_gen. cbn.
      rewrite /cstr_branch_context in cd.
      eapply trans_eq_context_upto_names in cd.
      eapply eq_context_upto_names_smash_context in cd.
      intros eqann.
      eapply (eq_annots_subst_context _ (map trans (inds (inductive_mind ci) (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl))) #|ind_params mdecl|).
      eapply (eq_annots_expand_lets_ctx _ (trans_local (ind_params mdecl))).
      rewrite -(smash_context_subst []) /= subst_context_nil.
      rewrite (expand_lets_smash_context _ []) /=. len; rewrite expand_lets_k_ctx_nil.
      rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)) in cd.
      eauto with pcuic.
      { eapply on_free_vars_ctx_subst_context. len.
        apply closedn_ctx_on_free_vars.
        generalize (declared_constructor_closed_args declc).
        now rewrite Nat.add_comm.
        eapply (inds_is_open_terms []). }
      rewrite (trans_subst_context (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) xpred0) in cd.
      { apply closedn_ctx_on_free_vars.
        apply (declared_constructor_closed_args declc). }
      apply (inds_is_open_terms []).
      rewrite !trans_bcontext.
      now eapply eq_context_upto_names_binder_annot in cd.
    + eapply All2i_map. eapply All2i_map_right.
      eapply Forall2_All2 in H5.
      eapply All2i_nth_hyp in X8.
      eapply All2i_All2_mix_left in X8; tea.
      eapply All2i_impl ; tea.
      intros i cdecl br. cbv beta.
      set (cbt := case_branch_type _ _ _ _ _ _ _ _).
      intros (wf & hnth & eqctx & Hbctx & (Hb & IHb) & (Hbty & IHbty)).
      have declc : declared_constructor Σ (ci, i) mdecl idecl cdecl.
      { split; tea. }
      have clargs : on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
        (cstr_args cdecl).
      { apply closedn_ctx_on_free_vars.
        generalize (declared_constructor_closed_args declc). now rewrite Nat.add_comm. }
      split. rewrite -(trans_cstr_branch_context xpred0); auto. eauto with pcuic.
      cbn.
      rewrite trans_bcontext. now eapply alpha_eq_smash_context, alpha_eq_trans.
      rewrite (trans_case_predicate_context declc H1 s H0).
      intros brctxty.
      have trbr := !! (trans_case_branch_type (Γ := Γ) declc H1 H0 wf X1 eqctx).
      forward_keep trbr.
      { eassert (ctx_inst _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
        eapply ctx_inst_open_terms in Hctxi.
        eapply All_app in Hctxi as [].
        now eapply All_forallb, All_impl; tea. }
      forward trbr.
      { eapply subject_is_open_term in pret. move: pret.
        rewrite /predctx; len. rewrite (case_predicate_context_length_indices H0).
        now rewrite shiftnP_add. }
      rewrite -/ptm  in trbr.
      set (p' := map_predicate _ _ _ _ _) in *.
      cbv zeta in trbr.
      set (br' := trans_branch _ _) in *.
      set (cbctx := case_branch_context _ _ _ _ _) in trbr.
      set (brctxty' := case_branch_type _ _ _ _ _ _ _ _) in trbr.
      change brctxty with brctxty'. clear brctxty.
      destruct trbr as [eqbrctx' eqbrty'].
      specialize (IHb X9). specialize (IHbty X9). specialize (Hbctx X9).
      have fvs_cbctx : on_free_vars_ctx (shiftnP #|Γ| xpred0) cbctx.
      { eapply typing_closed_ctx in Hb; eauto.
        now move: Hb; rewrite on_free_vars_ctx_app => /andP[]. }
      repeat split.
      * rewrite eqbrctx'.
        rewrite trans_local_app in Hbctx.
        eapply wf_local_smash_end in Hbctx.
        rewrite (trans_smash_context (shiftnP #|Γ| xpred0)) //.
      * rewrite eqbrctx' eqbrty'.
        rewrite (trans_expand_lets (shiftnP #|Γ| xpred0)) //.
        eapply subject_is_open_term in Hbty.
        move: Hbty. rewrite /cbt. len.
        now rewrite shiftnP_add.
        rewrite (trans_smash_context (shiftnP #|Γ| xpred0)) //.
        assert (bbody br' = expand_lets (trans_local cbctx) (trans (bbody br))) as ->.
        { rewrite trans_bbody. rewrite /br' /trans_branch; cbn [bbody].
          rewrite -/(inst_case_context (pparams p') (puinst p') _).
          cbn -[inst_case_context expand_lets].
          f_equal. rewrite /cbctx.
          rewrite (trans_case_branch_context (Γ := Γ) declc) //. }
        eapply (typing_expand_lets (Σ := trans_global Σ)).
        now rewrite trans_local_app in IHb.
      * rewrite eqbrctx' eqbrty'.
        rewrite (trans_expand_lets (shiftnP #|Γ| xpred0)) //.
        eapply subject_is_open_term in Hbty.
        move: Hbty. rewrite /cbt. len.
        now rewrite shiftnP_add.
        rewrite (trans_smash_context (shiftnP #|Γ| xpred0)) //.
        eapply (typing_expand_lets (Σ := trans_global Σ) _ _ _ (tSort ps)).
        now rewrite trans_local_app in IHbty.

  - rewrite (trans_subst (shiftnP #|projection_context p.(proj_ind) mdecl idecl u| xpred0) (shiftnP #|Γ| xpred0)).
    { rewrite /projection_context /=; len. cbn.
      destruct (declared_projection_type_and_eq _ isdecl) as [[] ?].
      eapply isType_is_open_term in i. cbn in i; len in i.
      rewrite on_free_vars_subst_instance //. }
    { generalize (subject_is_open_term X1). move/type_is_open_term: X1.
      now rewrite on_free_vars_mkApps /= forallb_rev => -> ->. }
    rewrite trans_subst_instance /= map_rev.
    change (trans (proj_type pdecl)) with (trans_projection_body pdecl).(proj_type).
    eapply type_Proj.
    + now apply trans_declared_projection.
    + rewrite trans_mkApps in X2; eauto.
    + rewrite length_map H. now destruct mdecl.
  - rewrite trans_dtype /=.
    assert (is_open_term Γ (tFix mfix n)).
    { eapply (subject_is_open_term (Σ := Σ)). econstructor; tea. }
    eapply TT.type_Fix; auto.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + now apply fix_guard_trans.
    + erewrite map_nth_error.
      2: apply H0.
      destruct decl.
      unfold map_def.
      reflexivity.
    + eapply All_map, (All_impl X1).
      intros d tu.
      eapply trans_lift_typing_it with (tu _) => //.
    + fold trans.
      subst types.
      eapply All_map.
      eapply All_prod with (1 := X3) in X0; tea. clear X1 X2 X3.
      eapply All_impl; tea. intros d (onb & ont); cbn in *; tas.
      eapply trans_lift_typing_it with (onb _) => // HT.
      all: len in HT; len; rewrite -(trans_fix_context _ _ 0 H2).
      all: rewrite -trans_local_app /=.
      all: rewrite -(trans_lift _ (shiftnP #|Γ| xpred0)) /=.
      all: try eapply (isTypeRel_is_open_term (Σ := Σ)); tea.
      all: rewrite -(fix_context_length mfix); eapply HT.
    + rewrite (trans_wf_fixpoint _ (shiftnP #|Γ| xpred0) #|mfix|) //.

  - rewrite trans_dtype. simpl.
    assert (is_open_term Γ (tCoFix mfix n)).
    { eapply (subject_is_open_term (Σ := Σ)). econstructor; tea. }
    eapply TT.type_CoFix; auto.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + now eapply cofix_guard_trans.
    + erewrite map_nth_error.
      2: eassumption.
      destruct decl.
      unfold map_def.
      reflexivity.
    + eapply All_map, (All_impl X1).
      intros d tu.
      eapply trans_lift_typing_it with (tu _) => //.
    + fold trans.
      subst types.
      eapply All_map.
      eapply All_prod with (1 := X3) in X0; tea. clear X1 X2 X3.
      eapply All_impl; tea. intros d (onb & ont); cbn in *; tas.
      eapply trans_lift_typing_it with (onb _) => // HT.
      all: len in HT; len; rewrite -(trans_fix_context _ _ 0 H2).
      all: rewrite -trans_local_app /=.
      all: rewrite -(trans_lift _ (shiftnP #|Γ| xpred0)) /=.
      all: try eapply (isTypeRel_is_open_term (Σ := Σ)); tea.
      all: rewrite -(fix_context_length mfix); eapply HT.
    + rewrite trans_wf_cofixpoint //.
  - cbn. rewrite trans_prim_ty. econstructor; eauto. rewrite prim_val_tag_map //.
    * now eapply trans_declared_constant in H0.
    * destruct p as [? []]; cbn in X0 |- *.
      all:destruct H1 as []; split => //; rewrite ?H1 ?H2 //=.
    * depelim X0; depelim X1; constructor; intuition eauto. cbn. solve_all.
  - eapply (type_ws_cumul_pb (pb:=Cumul)).
    + eauto.
    + now eapply has_sort_isType.
    + eapply cumulSpec_cumulAlgo_curry in X4; fvs.
      eapply ws_cumul_pb_forget in X4.
      eapply cumul_decorate in X4; tea.
      2:eapply validity; tea.
      2:now eapply has_sort_isType.
      eapply into_ws_cumul_pb.
      eapply (trans_cumul (Σ := Σ)); eauto.
      eapply (trans_on_free_vars_ctx 0). now eapply wf_local_closed_context in wfΓ.
      specialize (X1 X5).
      now eapply type_is_open_term in X1.
      now eapply subject_is_open_term in X3.
Qed.

Lemma fresh_global_map {kn} {Σ : global_env} :
  fresh_global kn Σ.(declarations) -> fresh_global kn (trans_global_decls Σ.(declarations)).
Proof.
  intros f.
  now eapply Forall_map; cbn.
Qed.

Lemma fold_right_map {A B C} {f : B -> A -> A} {acc l} {g : C -> B} :
  fold_right f acc (map g l) = fold_right (fun c a => f (g c) a) acc l.
Proof.
  induction l; cbn; auto. now rewrite IHl.
Qed.

Lemma fold_right_ext {A B} {f g : B -> A -> A} {acc l} :
  f =2 g ->
  fold_right f acc l = fold_right g acc l.
Proof.
  induction l; cbn; auto => Hfg. now rewrite IHl.
Qed.

Lemma trans_global_levels {Σ : global_env} : PCUICLookup.global_levels (trans_global_env Σ) = PCUICLookup.global_levels Σ.
Proof. reflexivity. Qed.

Lemma trans_global_constraints {Σ : global_env} : PCUICLookup.global_constraints (trans_global_env Σ) = PCUICLookup.global_constraints Σ.
Proof. reflexivity. Qed.

Lemma type_it_mkProd_or_LetIn_smash_middle {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ' T s} :
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ (it_mkProd_or_LetIn Δ' T) : tSort s ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ (it_mkProd_or_LetIn (smash_context [] Δ') (expand_lets Δ' T)) : tSort s.
Proof.
  intros hit.
  eapply subject_reduction; tea. clear hit.
  eapply red_it_mkProd_or_LetIn.
  revert T Δ; induction Δ' using ctx_length_rev_ind => T.
  - rewrite expand_lets_nil; reflexivity.
  - rewrite !it_mkProd_or_LetIn_app.
    destruct d as [na [b|] ty]; cbn.
    + rewrite smash_context_app_def.
      specialize (X (subst_context [b] 0 Γ0) ltac:(now len) (subst [b] #|Γ0| T)).
      etransitivity. eapply red1_red, red_zeta.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
      now rewrite expand_lets_vdef.
    + rewrite smash_context_app_ass !it_mkProd_or_LetIn_app.
      specialize (X Γ0 ltac:(easy)).
      intros Δ. eapply red_prod. cbn. reflexivity.
      rewrite expand_lets_vass. cbn. rewrite -[_ ,, _](app_context_assoc _ _ [_]). apply X.
Qed.

Lemma subst_context_expand_lets_ctx Δ s Δ' :
  subst_context (map (expand_lets Δ) s) 0 (expand_lets_k_ctx Δ #|s| Δ') =
  expand_lets_ctx Δ (subst_context s 0 Δ').
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  relativize #|s|. erewrite <-subst_app_context. len. cbn.
  2:now len.
  rewrite /expand_lets /expand_lets_k.
  rewrite -map_map_compose.
  rewrite -subst_context_comm. f_equal.
  cbn. now rewrite -distr_lift_subst_context.
Qed.

Lemma ctx_inst_expand_lets {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {univs} {Γ Δ} {s ctx} :
  PCUICTyping.ctx_inst (λ Γ t T , lift_typing typing (Σ, univs) Γ (TermTyp t T)) (Γ ,,, Δ) s ctx ->
  PCUICTyping.ctx_inst (λ Γ t T , lift_typing typing (Σ, univs) Γ (TermTyp t T)) (Γ ,,, smash_context [] Δ) (map (expand_lets Δ) s) (List.rev (expand_lets_ctx Δ (List.rev ctx))).
Proof.
  induction 1.
  - cbn. constructor.
  - cbn. rewrite expand_lets_ctx_app /=.
    rewrite List.rev_app_distr /=. constructor.
    cbn.
    apply lift_typing_f_impl with (1 := t0) => // ?? Hty.
    now eapply typing_expand_lets in Hty.
    rewrite subst_telescope_subst_context.
    rewrite -subst_context_subst_telescope in IHX.
    now rewrite (subst_context_expand_lets_ctx _ [i]).
  - cbn. rewrite expand_lets_ctx_app /=.
    rewrite List.rev_app_distr /=. constructor.
    rewrite subst_telescope_subst_context.
    rewrite -subst_context_subst_telescope in IHX.
    now rewrite (subst_context_expand_lets_ctx _ [b]).
Qed.

Lemma rev_inj {A} {l l' : list A} : List.rev l = List.rev l' -> l = l'.
Proof.
  move: l'. induction l using rev_ind; destruct l' using rev_case => /= //.
  - rewrite List.rev_app_distr /= //.
  - rewrite List.rev_app_distr /= //.
  - rewrite !List.rev_app_distr /= => [=] <- H.
    f_equal; eauto.
Qed.

Lemma trans_local_subst_telescope p q s k Γ :
  on_free_vars_ctx p (List.rev Γ) ->
  on_free_vars_terms q s ->
  trans_local (subst_telescope s k Γ) = subst_telescope (map trans s) k (trans_local Γ).
Proof.
  intros onp onq.
  eapply rev_inj.
  rewrite -subst_context_subst_telescope -map_rev.
  rewrite -subst_context_subst_telescope -map_rev.
  rewrite [map _ _] (trans_subst_context p q) //.
Qed.

Lemma trans_ctx_inst_expand_lets {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ} {s} :
  wf_trans Σ ->
  wf_local Σ (Γ ,,, List.rev Δ) ->
  PCUICTyping.ctx_inst (fun Γ t T => lift_typing typing Σ Γ (TermTyp t T)) Γ s Δ ->
  PCUICTyping.ctx_inst (fun Γ t T => lift_typing (typing (H:=cf' cf)) (trans_global Σ) Γ (TermTyp t T)) (trans_local Γ) (map trans s) (trans_local Δ).
Proof.
  intros wf wfctx i.
  induction i in wfctx |- *.
  - cbn. constructor.
  - cbn. constructor.
    apply lift_typing_f_impl with (1 := t0) => // ?? H.
    eapply pcuic_expand_lets; tea.
    apply unlift_TermTyp in t0.
    cbn in wfctx. rewrite -app_assoc in wfctx.
    unshelve epose proof (substitution_wf_local (Σ := Σ) (Γ' := [vass na t]) _ wfctx). shelve.
    { now eapply subslet_ass_tip. }
    rewrite subst_context_subst_telescope in X. specialize (IHi X).
    rewrite (trans_local_subst_telescope (shiftnP (S #|Γ|) xpred0) (shiftnP #|Γ| xpred0)) in IHi.
    { apply wf_local_closed_context in wfctx.
      now move/onfvs_app: wfctx => /=. }
    { cbn. now rewrite (subject_is_open_term t0). }
    apply IHi.
  - cbn. constructor.
    cbn in wfctx. rewrite -app_assoc in wfctx.
    unshelve epose proof (substitution_wf_local (Σ := Σ) (Γ' := [vdef na b t]) _ wfctx). shelve.
    { eapply subslet_def_tip. eapply All_local_env_app_inv in wfctx as [wf' _]. eapply unlift_TermTyp.
      now depelim wf'. }
    rewrite subst_context_subst_telescope in X. specialize (IHi X).
    rewrite (trans_local_subst_telescope (shiftnP (S #|Γ|) xpred0) (shiftnP #|Γ| xpred0)) in IHi.
    { apply wf_local_closed_context in wfctx.
      now move/onfvs_app: wfctx => /=. }
    { eapply All_local_env_app_inv in wfctx as [wf' _].
      depelim wf'. apply unlift_TermTyp in l. cbn. now rewrite (subject_is_open_term l). }
    apply IHi.
Qed.

Lemma expand_lets_ctx_lift_context_cancel {Γ Δ} :
  expand_lets_ctx Γ (lift_context #|Γ| 0 Δ) =
  lift_context (context_assumptions Γ) 0 Δ.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite (lift_context_lift_context _ 0) Nat.add_comm lift_context_add.
  rewrite subst_context_lift_context_cancel //. now len.
Qed.

#[global] Instance forallb_proper A : Proper (pointwise_relation A eq ==> eq ==> eq) (@forallb A).
Proof.
  intros f g eqfg x y ->. eapply forallb_ext. exact eqfg.
Qed.

#[global] Instance on_free_vars_terms_proper : Proper (pointwise_relation nat eq ==> eq ==> eq) on_free_vars_terms.
Proof.
  unfold on_free_vars_terms.
  intros f g eqfg x y ->. now rewrite eqfg.
Qed.

#[global] Instance istrue_proper : Proper (eq ==> eq) (is_true).
Proof.
  now intros x y ->.
Qed.

Lemma Alli_nth_hyp_ind {A} {P : nat -> A -> Type} {n l} :
  Alli P n l ->
  Alli (fun i x => (n <= i) * (nth_error l (i - n) = Some x) * P i x) n l.
Proof.
  induction 1; constructor.
  rewrite Nat.sub_diag /=. eauto.
  eapply Alli_impl; tea; cbv beta.
  intros. intuition auto. lia.
  pose proof (nth_error_Some_length b0).
  destruct n0. cbn in *. destruct tl. cbn in *. depelim a0. depelim a0.
  cbn in b0. rewrite Nat.sub_succ_l //; lia.
Qed.

Lemma Alli_nth_hyp {A} {P : nat -> A -> Type} {l} :
  Alli P 0 l ->
  Alli (fun i x => (nth_error l i = Some x) * P i x) 0 l.
Proof.
  move/Alli_nth_hyp_ind => a.
  eapply Alli_impl; tea; cbv beta.
  intros n x; rewrite Nat.sub_0_r; intuition auto.
Qed.

Lemma trans_cstr_concl_eq m n cdecl :
  on_free_vars_ctx (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)
    (cstr_args cdecl) ->
  on_free_vars_terms
    (shiftnP (#|cstr_args cdecl| + #|ind_params m| + #|ind_bodies m|) xpred0)
    (cstr_indices cdecl) ->
  (trans_cstr_concl m n
     (trans_local (SE.smash_context [] (cstr_args cdecl)))
           (map trans
              (map (expand_lets (cstr_args cdecl)) (cstr_indices cdecl)))) =
  expand_lets (trans_local (cstr_args cdecl))
    (trans (cstr_concl m n cdecl)).
Proof.
  intros onargs onindices.
  rewrite /trans_cstr_concl /cstr_concl trans_mkApps expand_lets_mkApps.
  f_equal.
  { rewrite /trans_cstr_concl_head /cstr_concl_head. len.
    cbn [trans].
    relativize #|cstr_args cdecl|.
    erewrite expand_lets_tRel. 2:now len.
    now rewrite context_assumptions_map. }
  len. cbn.
  rewrite !map_app. f_equal.
  { rewrite trans_reln /=.
    rewrite -trans_to_extended_list.
    rewrite -/(to_extended_list_k (trans_local (ind_params m)) #|cstr_args cdecl|).
    relativize #|cstr_args cdecl|.
    erewrite map_expand_lets_to_extended_list_k_above. 2:now len.
    rewrite context_assumptions_map.
    rewrite trans_to_extended_list //. }
  { rewrite (trans_expand_lets_map (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) //.
    now rewrite shiftnP_add Nat.add_assoc. }
Qed.

Lemma positive_cstr_smash_middle m n acc Γ Δ T :
  positive_cstr m n acc (it_mkProd_or_LetIn Γ (it_mkProd_or_LetIn Δ T)) ->
  positive_cstr m n acc (it_mkProd_or_LetIn Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T))).
Proof.
  revert Δ acc T.
  induction Γ using ctx_length_rev_ind. cbn.
  - intros Δ. induction Δ using ctx_length_rev_ind.
    { cbn; auto. intros; rewrite expand_lets_nil //. }
    intros acc T. rewrite !it_mkProd_or_LetIn_app.
    destruct d as [na [b|] ty].
    * cbn.
      rewrite smash_context_app_def.
      intros p. depelim p. solve_discr.
      rewrite expand_lets_vdef.
      eapply X. now len.
      rewrite subst_it_mkProd_or_LetIn Nat.add_0_r in p => //.
    * rewrite smash_context_app_ass expand_lets_vass.
      rewrite it_mkProd_or_LetIn_app /=.
      intros p; depelim p. solve_discr.
      cbn in *.
      constructor 3; auto.
  - intros Δ acc T. destruct d as [na [b|] ty]; rewrite !it_mkProd_or_LetIn_app /=; intros p; depelim p;
      try solve_discr.
    * constructor. rewrite !subst_it_mkProd_or_LetIn.
      len => /=. rewrite -(expand_lets_subst_comm _ _ _ _).
      rewrite -(smash_context_subst []).
      eapply X. now len.
      now rewrite !subst_it_mkProd_or_LetIn !Nat.add_0_r in p.
    * constructor => //. cbn.
      cbn in p0. eapply X; auto.
Qed.

Lemma closedn_trans n t : closedn n t -> closedn n (trans t).
Proof. intros cl; rewrite on_free_vars_closedn. eapply trans_on_free_vars.
  now rewrite -on_free_vars_closedn.
Qed.

Lemma trans_destArity ctx t :
  destArity (trans_local ctx) (trans t) = match destArity ctx t with
  | Some (ctx, T) => Some (trans_local ctx, T)
  | None => None
  end.
Proof.
  induction t in ctx |- *; cbn; auto.
  rewrite (IHt2 (ctx ,, vass na t1)) //.
  rewrite (IHt3 (ctx ,, vdef na t1 t2)) //.
Qed.

Lemma trans_ind_realargs m k i :
  ind_realargs i = ind_realargs (trans_one_ind_body m k i).
Proof.
  unfold ind_realargs.
  rewrite (trans_destArity []).
  destruct destArity => //. destruct p.
  now len.
Qed.

Lemma positive_cstr_arg_trans m acc p T :
  positive_cstr_arg m acc T ->
  on_free_vars p T ->
  positive_cstr_arg (trans_minductive_body m) (trans_local acc) (trans T).
Proof.
  induction 1 in p |- *.
  - intros ont.
    constructor; len. now eapply closedn_trans.
  - destruct m0 as [? [? ?]].
    rewrite on_free_vars_mkApps => /= /andP[] onk onl.
    rewrite trans_mkApps. econstructor 2.
    2: {solve_all. len. now eapply closedn_trans. }
    2: {repeat (econstructor; [now len|]).
        len. cbn. rewrite rev_mapi. rewrite nth_error_mapi H1 /= //. }
    len. now rewrite -trans_ind_realargs.
  - cbn. move/and3P => [] onb onty ont.
    constructor 3.
    rewrite (trans_subst (shiftnP 1 p) p) in IHX => /= //.
    now rewrite onb. eapply IHX.
    eapply on_free_vars_subst => /= //. now erewrite onb.
    exact ont.
  - cbn. move/andP=> []onty ont.
    constructor 4. len; now eapply closedn_trans.
    eapply IHX; tea.
Qed.

Lemma positive_cstr_trans m n acc p T :
  positive_cstr m n acc T ->
  on_free_vars p T ->
  positive_cstr (trans_minductive_body m) n (trans_local acc) (trans T).
Proof.
  induction 1 in p |- *.
  - cbn. intros. rewrite trans_mkApps.
    cbn. rewrite /headrel. relativize #|Γ|.
    relativize #|ind_bodies m|.
    constructor. solve_all.
    rewrite on_free_vars_closedn. eapply trans_on_free_vars. len.
    now rewrite -on_free_vars_closedn. all:now len.
  - cbn. move/and3P => [] onb onty ont. constructor.
    rewrite (trans_subst (shiftnP 1 p) p) in IHX => /= //.
    now rewrite onb. eapply IHX.
    eapply on_free_vars_subst => /= //. now erewrite onb. exact ont.
  - cbn. move/andP=> [] onty ont.
    constructor. now eapply positive_cstr_arg_trans.
    now eapply IHX.
Qed.

Lemma cumul_context_Spec_Algo {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} {Γ Γ'} :
  wf_local Σ Γ ->
  wf_local Σ Γ' ->
  cumul_context cumulSpec0 Σ Γ' Γ ->
  cumul_context cumulAlgo_gen Σ Γ' Γ.
Proof.
  intros wfΓ wfΓ'.
  induction 1. constructor.
  depelim wfΓ; depelim wfΓ'; depelim p; constructor; auto; auto.
  - now apply IHX.
  - constructor; auto.
    eapply cumulSpec_cumulAlgo_curry in eqt; tea. 2-4:fvs.
    red in l. now eapply ws_cumul_pb_forget in eqt.
    rewrite (All2_fold_length X). fvs.
  - now apply IHX.
  - destruct l as (? & ? & ? & _), l0 as (? & ? & ? & _); cbn in *.
    constructor; auto.
    eapply convSpec_convAlgo_curry in eqb; tea.
    now apply ws_cumul_pb_forget in eqb.
    1-3:fvs.
    rewrite (All2_fold_length X). fvs.
    eapply cumulSpec_cumulAlgo_curry in eqt; tea. 2-4:fvs.
    2:{ rewrite (All2_fold_length X). fvs. }
    now apply ws_cumul_pb_forget in eqt.
Qed.

Lemma context_cumulativity_spec {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |- t : T ->
  wf_local Σ Γ' ->
  cumul_context cumulSpec0 Σ Γ' Γ ->
  Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  eapply PCUICContextConversionTyp.context_cumulativity; tea.
  eapply cumul_context_Spec_Algo; tea. pcuic.
Qed.

Lemma trans_cumulSpec {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wf_trans Σ ->
  isType Σ Γ T → isType Σ Γ U →
  cumulSpec Σ Γ T U ->
  cumulSpec (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  intros wfΣ' wtT wtU cum.
  eapply cumulSpec_cumulAlgo_curry in cum; fvs.
  eapply ws_cumul_pb_forget in cum.
  eapply cumul_decorate in cum; tea.
  pose proof (trans_cumul wfΣ' cum); tea.
  eapply (cumulAlgo_cumulSpec _ (pb:=Cumul)).
  eapply into_ws_cumul_pb; tea.
  destruct wtT as (_ & ? & ? & _). apply trans_is_closed_context. fvs.
  apply trans_on_free_vars; len; fvs.
  apply trans_on_free_vars; len; fvs.
  destruct wtT as (_ & ? & ? & _). fvs.
Qed.

Lemma trans_convSpec {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wf_trans Σ ->
  wt Σ Γ T → wt Σ Γ U →
  convSpec Σ Γ T U ->
  convSpec (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  intros wfΣ' wtT wtU cum.
  eapply convSpec_convAlgo_curry in cum; tas.
  eapply ws_cumul_pb_forget in cum.
  eapply conv_decorate in cum; tea.
  pose proof (trans_conv wfΣ' cum); tea.
  eapply (cumulAlgo_cumulSpec _ (pb:=Conv)).
  destruct wtT, wtU.
  eapply into_ws_cumul_pb; tea.
  apply trans_is_closed_context. fvs.
  apply trans_on_free_vars; len; fvs.
  apply trans_on_free_vars; len; fvs.
  1-2:destruct wtT; fvs.
  destruct wtU. fvs.
Qed.

Lemma trans_cumul_ctx_rel {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ'} :
  wf_trans Σ ->
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  cumul_ctx_rel cumulSpec0 Σ Γ Δ Δ' ->
  cumul_ctx_rel (cumulSpec0 (cf:=cf' cf)) (trans_global Σ) (trans_local Γ) (trans_local Δ) (trans_local Δ').
Proof.
  intros wf' wfl wfr.
  induction 1; cbn; constructor; auto.
  eapply IHX. now depelim wfl. now depelim wfr.
  destruct p; constructor; cbn in *; auto.
  all: depelim wfl; depelim wfr; destruct l as (? & ? & ? & _), l0 as (? & ? & ? & _); cbn in *.
  - rewrite -trans_local_app.
    eapply trans_cumulSpec in eqt; tea.
    { now eapply has_sort_isType. }
    { eapply has_sort_isType. eapply context_cumulativity_spec; tea.
      eapply All2_fold_app. reflexivity. apply X. }
  - rewrite -trans_local_app.
    eapply (trans_convSpec (Σ := Σ)) => //.
    now exists t.
    { exists t'. eapply context_cumulativity_spec; tea.
      eapply All2_fold_app. reflexivity. apply X. }
  - rewrite -trans_local_app.
    eapply (trans_cumulSpec (Σ := Σ)) => //.
    { now eapply has_sort_isType. }
    { eapply has_sort_isType. eapply context_cumulativity_spec; tea.
      eapply All2_fold_app. reflexivity. apply X. }
Qed.

From MetaRocq.PCUIC Require Import PCUICRedTypeIrrelevance.

Lemma pres_let_bodies_assumption_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ'} :
  #|Γ| = #|Γ'| ->
  assumption_context Γ ->
  assumption_context Γ' ->
  All2_fold (λ _ _ : list context_decl, pres_let_bodies) Γ Γ'.
Proof.
  induction Γ in Γ' |- *; destruct Γ' => /= //; constructor; auto.
  - apply IHΓ. lia. now depelim H0. now depelim H1.
  - red. destruct a as [na [b|] ty], c as [na' [b'|] ty']; cbn in *; try exact tt;
    depelim H0; depelim H1.
Qed.

Lemma cumul_type_irrelevance {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' T U} :
  wf (trans_global Σ) ->
  #|Γ| = #|Γ'| ->
  assumption_context Γ ->
  assumption_context Γ' ->
  cumulAlgo Σ Γ T U ->
  cumulAlgo Σ Γ' T U.
Proof.
  intros wf len ass ass'.
  induction 1. constructor; auto.
  eapply context_pres_let_bodies_red1 in r.
  econstructor 2; tea. now eapply pres_let_bodies_assumption_context.
  eapply context_pres_let_bodies_red1 in r.
  econstructor 3; tea. now eapply pres_let_bodies_assumption_context.
Qed.

Section wtcumul'.
  Import PCUICAst PCUICTyping PCUICEquality.
  Context {cf : checker_flags}.

  Reserved Notation " Σ ;;; Γ | Γ' |-- t <=[ le ] u " (at level 50, Γ, Γ' , le, t, u at next level).

  Inductive wt_cumul_pb_hetero (pb : conv_pb) (Σ : global_env_ext) (Γ Γ' : context) : term -> term -> Type :=
  | wt_cumul_refl' t u : wt Σ Γ t -> wt Σ Γ' u ->
    compare_term Σ.1 (global_ext_constraints Σ) pb t u -> Σ ;;; Γ | Γ' |-- t <=[pb] u
  | wt_cumul_red_l' t u v : wt_red1 Σ Γ t v -> Σ ;;; Γ | Γ' |-- v <=[pb] u -> Σ ;;; Γ | Γ' |-- t <=[pb] u
  | wt_cumul_red_r' t u v : Σ ;;; Γ | Γ' |-- t <=[pb] v -> wt_red1 Σ Γ' u v -> Σ ;;; Γ | Γ' |-- t <=[pb] u
  where " Σ ;;; Γ | Γ' |-- t <=[ le ] u " := (wt_cumul_pb_hetero le Σ Γ Γ' t u) : type_scope.

  Lemma wt_cumul_pb_hetero_inv {le Σ Γ Γ' T U} :
    wt_cumul_pb_hetero le Σ Γ Γ' T U ->
    wt Σ Γ T × wt Σ Γ' U.
  Proof.
    induction 1; intuition auto. destruct w; auto. destruct w; auto.
  Qed.

  Definition wt_cumul_hetero := wt_cumul_pb_hetero Cumul.
  Definition wt_conv_hetero := wt_cumul_pb_hetero Conv.

  Lemma cumul_decorate_hetero (Σ : global_env_ext) {wfΣ : wf Σ} {Γ Γ' T U} :
    isType Σ Γ T -> isType Σ Γ' U ->
    #|Γ| = #|Γ'| ->
    assumption_context Γ ->
    assumption_context Γ' ->
    cumulAlgo Σ Γ T U ->
    wt_cumul_pb_hetero Cumul Σ Γ Γ' T U.
  Proof.
    move/isType_wt => ht.
    move/isType_wt => hu.
    move=> hlen ass ass'.
    induction 1.
    - constructor; auto.
    - pose proof (wt_red ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHX; tea.
    - eapply context_pres_let_bodies_red1 in r.
      2:eapply pres_let_bodies_assumption_context; tea.
      pose proof (wt_red hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.

  Lemma wt_convSpec_convAlgo {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' T U} :
    wt Σ Γ T -> wt Σ Γ' U ->
    #|Γ| = #|Γ'| ->
    convSpec Σ Γ T U ->
    convAlgo Σ Γ T U.
  Proof.
    intros [] [] len c.
    eapply convSpec_convAlgo_curry in c; tea.
    now eapply ws_cumul_pb_forget in c. fvs. fvs. rewrite len; fvs.
  Qed.

  Lemma conv_decorate_hetero (Σ : global_env_ext) {wfΣ : wf Σ} {Γ Γ' T U} :
    wt Σ Γ T -> wt Σ Γ' U ->
    #|Γ| = #|Γ'| ->
    assumption_context Γ ->
    assumption_context Γ' ->
    convSpec Σ Γ T U ->
    wt_cumul_pb_hetero Conv Σ Γ Γ' T U.
  Proof.
    move=> ht hu hlen ass ass' c.
    eapply wt_convSpec_convAlgo in c; tea.
    induction c.
    - constructor; auto.
    - pose proof (wt_red ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHc; tea.
    - eapply context_pres_let_bodies_red1 in r.
      2:eapply pres_let_bodies_assumption_context; tea.
      pose proof (wt_red hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.
End wtcumul'.

Lemma pres_let_bodies_trans Γ Γ' :
  All2_fold (fun _ _ => pres_let_bodies) Γ Γ' ->
  All2_fold (fun _ _ => pres_let_bodies) (trans_local Γ) (trans_local Γ').
Proof.
  intros a; eapply All2_fold_map, All2_fold_impl; tea; cbv beta.
  unfold pres_let_bodies; intros _ _ [] []; cbn.
  destruct decl_body, decl_body0; cbn => //. intros [=]. now subst.
Qed.

Lemma trans_cumul' {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ Γ' T U} {wfΣ : PCUICTyping.wf Σ} :
  wf_trans Σ ->
  wt_cumul_hetero Σ Γ Γ' T U ->
  #|Γ| = #|Γ'| ->
  assumption_context Γ ->
  assumption_context Γ' ->
  cumulAlgo_gen (H:=cf' cf) (trans_global Σ) (trans_local Γ) Cumul (trans T) (trans U).
Proof.
  intros wfΣ'; induction 1.
  - constructor; auto.
    red in c.
    eapply trans_compare_term in c.
    now rewrite -trans_global_ext_constraints.
  - destruct w as [r ht hv].
    intros.
    apply trans_red1 in r; eauto.
    eapply red_cumul_cumul; eauto.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto.
    intros.
    eapply context_pres_let_bodies_red in r.
    intros; eapply red_cumul_cumul_inv; eauto.
    eapply pres_let_bodies_trans; tea.
    eapply pres_let_bodies_assumption_context; tea. now symmetry.
Qed.

Lemma trans_conv' {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ Γ' T U} {wfΣ : PCUICTyping.wf Σ} :
  wf_trans Σ ->
  wt_conv_hetero Σ Γ Γ' T U ->
  #|Γ| = #|Γ'| ->
  assumption_context Γ ->
  assumption_context Γ' ->
  cumulAlgo_gen (H:=cf' cf) (trans_global Σ) (trans_local Γ) Conv (trans T) (trans U).
Proof.
  intros wfΣ'; induction 1.
  - constructor; auto.
    red in c.
    eapply trans_compare_term in c.
    now rewrite -trans_global_ext_constraints.
  - destruct w as [r ht hv].
    intros.
    apply trans_red1 in r; eauto.
    eapply red_conv_conv; eauto.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto.
    intros.
    eapply context_pres_let_bodies_red in r.
    intros; eapply red_conv_conv_inv; eauto.
    eapply pres_let_bodies_trans; tea.
    eapply pres_let_bodies_assumption_context; tea. now symmetry.
Qed.

Lemma trans_convSpec' {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ Γ' T U} {wfΣ : PCUICTyping.wf Σ} :
  wf_trans Σ ->
  wt_conv_hetero Σ Γ Γ' T U ->
  #|Γ| = #|Γ'| ->
  assumption_context Γ ->
  assumption_context Γ' ->
  convSpec (H:=cf' cf) (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  intros wfΣ' cv len ass ass'.
  eapply (cumulAlgo_cumulSpec _ (pb:=Conv)).
  eapply into_ws_cumul_pb; [eapply trans_conv'; tea|eapply wt_cumul_pb_hetero_inv in cv as [[] []]..].
  eapply trans_is_closed_context; fvs.
  eapply trans_on_free_vars; rewrite length_map; fvs.
  eapply trans_on_free_vars; rewrite length_map len; fvs.
Qed.

Lemma trans_cumul_ctx_rel' {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Δ Δ'} :
  wf_trans Σ ->
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ' ,,, Δ') ->
  #|Γ| = #|Γ'| ->
  assumption_context (Γ ,,, Δ) ->
  assumption_context (Γ' ,,, Δ') ->
  cumul_ctx_rel cumulSpec0 Σ Γ Δ Δ' ->
  cumul_ctx_rel (cumulSpec0 (cf:=cf' cf)) (trans_global Σ) (trans_local Γ) (trans_local Δ) (trans_local Δ').
Proof.
  intros wf' wfl wfr eqlen ass ass'.
  induction 1; cbn; constructor; auto.
  eapply IHX. now depelim wfl. now depelim wfr. now depelim ass. now depelim ass'.
  destruct p; constructor; cbn in *; auto.
  - rewrite -trans_local_app.
    depelim wfl; depelim wfr. pose proof (l.2.π2.1). pose proof (l0.2.π2.1). cbn in X0, X1.
    eapply (cumulAlgo_cumulSpec _ (pb:=Cumul)).
    apply into_ws_cumul_pb.
    eapply (trans_cumul' (Σ := Σ) (Γ' := Γ' ,,, Γ'0)) => //.
    eapply cumul_decorate_hetero; eauto using has_sort_isType.
    len. now rewrite (All2_fold_length X) eqlen.
    now depelim ass. now depelim ass'.
    eapply cumulSpec_cumulAlgo_curry in eqt; eauto.
    now apply ws_cumul_pb_forget in eqt. fvs. fvs.
    len.
    rewrite (All2_fold_length X) eqlen.
    rewrite -length_app; fvs. len. eapply All2_fold_length in X. lia.
    now depelim ass. now depelim ass'.
    eapply trans_is_closed_context; fvs.
    eapply trans_on_free_vars; rewrite length_map /app_context; fvs.
    eapply trans_on_free_vars; len.
    rewrite (All2_fold_length X) eqlen -length_app; fvs.
  - exfalso. depelim ass.
  - exfalso; depelim ass.
Qed.

Lemma assumption_context_arities_context mdecl :
  assumption_context (arities_context mdecl).
Proof.
  rewrite /arities_context rev_map_spec -map_rev.
  induction (List.rev mdecl); cbn; auto with pcuic.
Qed.

Lemma expand_lets_smash_context_id Γ x :
  expand_lets (smash_context [] Γ) x = x.
Proof.
  rewrite expand_lets_assumption_context //. pcuic.
Qed.

Lemma expand_lets_expand_lets Γ Δ x :
  expand_lets (Γ ,,, smash_context [] Δ) (expand_lets Δ x) =
  expand_lets (Γ ,,, Δ) x.
Proof.
  rewrite expand_lets_app expand_lets_smash_context_id.
  rewrite context_assumptions_smash_context /=.
  now rewrite -expand_lets_app.
Qed.

Lemma trans_type_local_ctx {cf} {Σ Γ Δ s} :
  wf Σ -> wf_trans Σ ->
  type_local_ctx (PCUICEnvTyping.lift_typing typing) Σ Γ Δ s ->
  type_local_ctx (PCUICEnvTyping.lift_typing (typing (H:=cf' cf))) (trans_global Σ) (trans_local Γ) (trans_local Δ) s.
Proof.
  intros wf wf'.
  induction Δ; cbn.
  unfold PCUICLookup.wf_sort, wf_sort.
  destruct s => //.
  destruct a as [? [?|] ?] => /= //; intuition auto.
  all: apply lift_typing_f_impl with (1 := b) => //; intros.
  all:rewrite -trans_local_app.
  all: now eapply pcuic_expand_lets.
Qed.

Lemma trans_on_context {cf} {Σ Γ} :
  wf Σ -> wf_trans Σ ->
  on_context (PCUICEnvTyping.lift_typing typing) Σ Γ ->
  on_context (PCUICEnvTyping.lift_typing (typing (H:=cf' cf))) (trans_global Σ) (trans_local Γ).
Proof.
  intros wf wf'.
  induction 1; cbn; constructor; auto.
  all: apply lift_typing_f_impl with (1 := t0) => //; intros.
  all: now eapply pcuic_expand_lets.
Qed.

Lemma Alli_map {A B} (P : nat -> B -> Type) {f : A -> B} {n l} :
  Alli (fun n x => P n (f x)) n l ->
  Alli P n (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma trans_projs ind n n' :
  map trans (projs ind n n') = projs ind n n'.
Proof.
  induction n'; cbn; auto. now f_equal.
Qed.

Lemma sub_context_set_empty s : sub_context_set ContextSet.empty s.
Proof.
  red. split.
  intros x hin. cbn in hin. now eapply LevelSetFact.empty_iff in hin.
  intros x hin. cbn in hin. now eapply ConstraintSetFact.empty_iff in hin.
Qed.

Lemma wt_subst_instance {cf} {Σ : global_env} {ϕ : universes_decl} {Γ T u univs} :
  wf_ext_wk (Σ, Polymorphic_ctx univs) ->
  wt (Σ, Polymorphic_ctx univs) Γ T ->
  consistent_instance_ext (Σ, ϕ) (Polymorphic_ctx univs) u ->
  wt (Σ, ϕ) Γ@[u] T@[u].
Proof.
  intros wf [s Hs] cu. exists (s@[u]).
  eapply PCUICUnivSubstitutionTyp.typing_subst_instance'; tea.
Qed.

Lemma wt_expand_lets {cf} {Σ : global_env_ext} {Γ Δ T} :
  wf Σ ->
  wt Σ (Γ ,,, Δ) T ->
  wt Σ (Γ ,,, smash_context [] Δ) (expand_lets Δ T).
Proof.
  intros wf [s Hs]. exists (expand_lets Δ s).
  now eapply typing_expand_lets.
Qed.

Lemma on_free_vars_ctx_mon k k' Γ :
  k <= k' ->
  on_free_vars_ctx (shiftnP k xpred0) Γ ->
  on_free_vars_ctx (shiftnP k' xpred0) Γ.
Proof.
  intros hk. eapply on_free_vars_ctx_impl.
  rewrite /shiftnP => i.
  repeat nat_compare_specs => //.
Qed.

Lemma ctx_inst_wt {cf} {Σ Γ s Δ} :
  ctx_inst Σ Γ s Δ ->
  All (wt Σ Γ) s.
Proof.
  induction 1; try constructor; auto.
  now exists t.
Qed.

Lemma wf_ind_indices {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {mind mdecl i idecl} :
  on_ind_body cumulSpec0 (lift_typing typing) Σ mind mdecl i idecl ->
  wf_local Σ (ind_params mdecl ,,, ind_indices idecl).
Proof.
  intros [].
  rewrite ind_arity_eq in onArity.
  destruct onArity as (_ & s & Hs & _).
  eapply type_it_mkProd_or_LetIn_inv in Hs as [Δs [ts [_ Hs]]].
  eapply type_it_mkProd_or_LetIn_inv in Hs as [Δs' [ts' []]].
  eapply typing_wf_local in t. now rewrite app_context_nil_l in t.
Qed.

Lemma nth_error_smash_onfvs P Γ n c :
  nth_error (smash_context [] Γ) n = Some c ->
  on_free_vars_ctx P (smash_context [] Γ) ->
  on_free_vars_decl (shiftnP (context_assumptions Γ - S n) P) c.
Proof.
  induction Γ in P, n, c |- * using ctx_length_rev_ind.
  - cbn. rewrite nth_error_nil => //.
  - destruct d as [na [b|] ty].
    * rewrite smash_context_app_def.
      intros hnth onfvs.
      specialize (H (subst_context [b] 0 Γ)).
      forward H by now len. len.
      specialize (H _ _ _ hnth onfvs).
      len in H.
    * rewrite smash_context_app_ass.
      destruct (lt_dec n (context_assumptions Γ)); revgoals.
      { intros hnth.
        have hn : n = context_assumptions Γ.
        { apply nth_error_Some_length in hnth. len in hnth. }
        move: hnth.
        subst n. rewrite nth_error_app_ge; len => //.
        cbn. rewrite Nat.sub_diag /=. intros [= <-].
        rewrite on_free_vars_ctx_app /= => /andP[] ond _.
        rewrite /on_free_vars_ctx /= in ond. rewrite shiftnP0 in ond.
        move/andP: ond.
        assert (context_assumptions Γ + 1 - S (context_assumptions Γ) = 0) as -> by lia.
        now rewrite shiftnP0. }
      { rewrite nth_error_app_lt. now len.
        intros hnth onp. len. cbn.
        move: onp; rewrite on_free_vars_ctx_app /= => /andP[] ondecl onctx.
        specialize (H Γ ltac:(now lia) _ _ _ hnth onctx).
        rewrite shiftnP_add in H. red; rewrite -H. lia_f_equal.
      }
Qed.

Lemma on_free_vars_projs p ind n k :
  forallb (on_free_vars (shiftnP 1 p)) (projs ind n k).
Proof.
  induction k; cbn; auto.
Qed.

Lemma trans_on_udecl {cf} {Σ : global_env} {univs} :
  on_udecl Σ univs ->
  on_udecl (trans_global_env Σ) univs.
Proof. auto. Qed.

Lemma trans_wf {cf} {Σ : global_env_ext} : wf Σ -> wf_trans Σ.
Proof.
  rewrite /PCUICEnvironment.fst_ctx.
  destruct Σ as [[gunivs Σ retro] udecl]; cbn. intros [onu wfΣ]; cbn in *.
  induction wfΣ as [|Σ0 kn d X IHX [f udecl' onu' ond]]. constructor; auto. constructor.
  have onud : on_udecl gunivs (PCUICLookup.universes_decl_of_decl (trans_global_decl d)).
  { apply (trans_on_udecl (Σ:= {| universes := gunivs; declarations := Σ0; retroknowledge := retro |})) in onu'. destruct d => //. }
  cbn; constructor; eauto.
  rename Σ0 into Σd.
  set (Σ0 := {| universes := gunivs; declarations := Σd; retroknowledge := retro |}).
  rename X into Xd.
  set (X := (onu, Xd) : wf Σ0).
  constructor; try constructor; auto; try apply IHX.
  { now apply (fresh_global_map (Σ := Σ0)). }
  destruct d; cbn in *.
  * apply lift_typing_f_impl with (1 := ond) => //.
    intros ?? Hty; eapply (pcuic_expand_lets (Σ0, _) [] _ _ X Hty IHX).
  * generalize ond. intros []; econstructor; eauto.
    + cbn.
      eapply (Alli_mapi _ _ _).1, Alli_impl; tea.
      intros n idecl onind; generalize onind; intros []; econstructor; tea.
      { cbn. rewrite ind_arity_eq !trans_it_mkProd_or_LetIn //. }
      { cbn. apply lift_typing_f_impl with (1 := onArity) => // ?? Hty.
        exact (pcuic_expand_lets (Σ0, ind_universes m) [] _ _ X Hty IHX). }
      { instantiate (1 := ind_cunivs).
        red in onConstructors.
        eapply All2_map_left, All2_impl; tea.
        intros cdecl univs onc; generalize onc; intros [].
        have parsfvs: on_free_vars_ctx xpred0 (ind_params m).
        { red in onParams. now eapply wf_local_closed_context in onParams. }
        have oncargs: on_free_vars_ctx (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)
          (cstr_args cdecl).
        { eapply sorts_local_ctx_wf_local in on_cargs.
          eapply wf_local_closed_context in on_cargs.
          now move/onfvs_app: on_cargs; len.
          rewrite cstr_eq in on_ctype. destruct on_ctype as (_ & s & Hs & _).
          eapply typing_wf_local in Hs. eapply weaken_wf_local; tea. }
        have oncindices: on_free_vars_terms (shiftnP (#|cstr_args cdecl| + #|ind_params m| + #|ind_bodies m|) xpred0)
            (cstr_indices cdecl).
        { rewrite cstr_eq in on_ctype. destruct on_ctype as (_ & s & Hs & _).
          eapply subject_is_open_term in Hs. move: Hs.
          rewrite !on_free_vars_it_mkProd_or_LetIn.
          move/and3P => [] _ _. rewrite /cstr_concl.
          rewrite on_free_vars_mkApps /=. move/andP => [] _.
          len. rewrite !shiftnP_add forallb_app. move/andP => [] _ //. }
        econstructor; tea.
        { cbn; rewrite -cstr_args_length.
          rewrite context_assumptions_smash_context context_assumptions_map //. }
        { cbn; rewrite /trans_cstr_concl /trans_cstr_concl_head /cstr_concl_head. now len. }
        { eapply trans_lift_typing_it with on_ctype => // Hty. set (s := _.2.π1) in *; clearbody s.
          epose proof (pcuic_expand_lets (Σ0, ind_universes m) _ _ _ X Hty IHX).
          rewrite trans_arities_context. cbn.
          rewrite cstr_eq in X0. rewrite !trans_it_mkProd_or_LetIn in X0.
          eapply type_it_mkProd_or_LetIn_smash_middle in X0.
          eapply meta_conv_term; tea. f_equal. f_equal.
          rewrite /trans_cstr_concl /cstr_concl /trans_cstr_concl_head /cstr_concl_head. len => /=.
          rewrite trans_mkApps expand_lets_mkApps map_app. f_equal.
          cbn [trans]. relativize #|cstr_args cdecl|. erewrite expand_lets_tRel => //.
          now len. now len.
          rewrite map_app. f_equal.
          rewrite trans_to_extended_list.
          relativize #|cstr_args cdecl|.
          erewrite map_expand_lets_to_extended_list_k_above; now try len.
          now len. }
        { rewrite trans_arities_context /=.
          clear -X onud on_cargs IHX.
          rewrite -trans_local_app.
          induction (cstr_args cdecl) in univs, on_cargs |- * => //.
          destruct a as [na [b|] ty].
          - apply IHc. apply on_cargs.
          - cbn [trans_local map].
            rewrite [smash_context _ (_ :: _)](smash_context_app_expand _ _ [_]).
            rewrite /snoc; cbn. unfold app_context. cbn.
            rewrite expand_lets_ctx_tip /=.
            destruct univs => //.
            split. cbn in IHc. apply IHc, on_cargs.
            destruct on_cargs as [hs hj].
            apply lift_sorting_f_it_impl with (f := fun t => _ (_ t)) (tu := hj) => // ht.
            have fvsc : on_free_vars_ctx (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0) c.
            { eapply typing_wf_local, wf_local_closed_context in ht.
                move/onfvs_app: ht. now len. }
            have fvsty : on_free_vars (shiftnP (#|c| + #|ind_params m| + #|ind_bodies m|) xpred0) ty.
            { eapply subject_is_open_term in ht.
              move: ht. len. rewrite Nat.add_assoc //. }
            eapply typing_expand_lets in ht.
            eapply pcuic_expand_lets in ht; eauto.
            rewrite trans_local_app in ht.
            rewrite -> (trans_smash_context (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) in ht; auto.
            rewrite (trans_expand_lets (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) // in ht.
            rewrite shiftnP_add Nat.add_assoc //. }
        { move: on_cindices.
          len.
          rewrite trans_arities_context; cbn.
          rewrite -(trans_smash_context (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0) []) //.
          rewrite -[trans_local (ind_params m) ++ _]trans_local_app.
          rewrite -[_ ++ _]trans_local_app.
          intros ci.
          eapply (ctx_inst_expand_lets (Σ := (Σ0, ind_universes m))) in ci; cbn in ci.
          rewrite List.rev_involutive in ci.
          rewrite expand_lets_ctx_lift_context_cancel in ci.
          rewrite -(trans_expand_lets_map (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) //.
          rewrite shiftnP_add Nat.add_assoc //.
          rewrite -(trans_lift_context (shiftnP #|ind_params m| xpred0)).
          { rewrite ind_arity_eq in onArity.
            destruct onArity as (_ & s & Hs & _).
            eapply subject_is_open_term in Hs.
            move: Hs; rewrite !on_free_vars_it_mkProd_or_LetIn /=.
            move/and3P => [] _. now rewrite shiftnP0. }
          rewrite -map_rev.
          eapply trans_ctx_inst_expand_lets in ci; tea.
          rewrite List.rev_involutive.
          relativize (context_assumptions (cstr_args cdecl)). cbn.
          eapply weakening_wf_local. 3:now len.
          { rewrite -app_context_assoc.
            eapply weaken_wf_local; tea.
            eapply wf_arities_context'; tea.
            rewrite ind_arity_eq in onArity.
            destruct onArity as (_ & s & Hs & _).
            rewrite -it_mkProd_or_LetIn_app in Hs.
            eapply type_it_mkProd_or_LetIn_inv in Hs as [? [? [Hs _]]].
            eapply PCUICClosedConv.sorts_local_ctx_All_local_env in Hs; eauto.
            now rewrite app_context_nil_l in Hs. }
          { eapply wf_local_smash_end.
            eapply sorts_local_ctx_wf_local in on_cargs => //.
            eapply weaken_wf_local => //.
            eapply wf_arities_context'; eauto. }
        }
        { cbn.
          rewrite -(trans_smash_context (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0) []) //.
          rewrite -(trans_expand_lets_map (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) //.
          rewrite shiftnP_add Nat.add_assoc //.
          rewrite trans_cstr_concl_eq //.
          rewrite -(trans_expand_lets (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) //.
          rewrite shiftnP_add Nat.add_assoc //.
          { rewrite cstr_eq in on_ctype.
            destruct on_ctype as (_ & s & Hs & _).
            eapply subject_is_open_term in Hs. len in Hs.
            move: Hs; rewrite !on_free_vars_it_mkProd_or_LetIn.
            move/and3P => [] onpars onargs onconcl.
            now rewrite !shiftnP_add in onconcl. }
          rewrite -!trans_it_mkProd_or_LetIn.
          rewrite cstr_eq in on_ctype_positive.
          eapply positive_cstr_smash_middle in on_ctype_positive.
          eapply (positive_cstr_trans _ _ _ (shiftnP #|ind_bodies m| xpred0)) in on_ctype_positive.
          exact on_ctype_positive.
          rewrite cstr_eq in on_ctype.
          destruct on_ctype as (_ & s & Hs & _).
          eapply subject_is_open_term in Hs.
          len in Hs.
          move: Hs; rewrite !on_free_vars_it_mkProd_or_LetIn.
          move/and3P => [] onpars onargs onconcl.
          apply/and3P; split => //.
          rewrite on_free_vars_ctx_smash //.
          len. rewrite on_free_vars_expand_lets_k //. }
        { intros v indv.
          move: (on_ctype_variance v indv). clear -indv parsfvs onVariance onc X onu ond onud IHX onParams oncargs oncindices.
          rewrite indv in onVariance.
          eapply variance_universes_insts in onVariance as [univs' [u [u' [eqv hunivs cu cu' equlen eqvlen equ' cli equ]]]].
          rewrite /cstr_respects_variance.
          rewrite eqv.
          intuition auto.
          { cbn [cstr_args trans_constructor_body].
            rewrite smash_context_idempotent.
            cbn [ind_params trans_minductive_body].
            have clpars : is_closed_context (ind_params m).
            { now eapply wf_local_closed_context in onParams. }
            rewrite -(trans_smash_context xpred0 []) //.
            rewrite -(trans_smash_context (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0) []) //.
            rewrite -(trans_expand_lets_ctx xpred0 (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) //.
            rewrite on_free_vars_ctx_smash //.
            rewrite [ind_arities _]trans_arities_context -trans_local_app.
            rewrite -!trans_subst_instance_ctx.
            cbn in a. cbn.
            eapply (trans_cumul_ctx_rel' (Σ := (Σ0, univs'))
              (Γ' := (arities_context (ind_bodies m),,, SE.smash_context [] (ind_params m))@[u'])) => //.
            { rewrite subst_instance_app subst_instance_smash.
              rewrite subst_instance_expand_lets_ctx.
              eapply wf_local_expand_lets.
              rewrite subst_instance_smash. unshelve eapply wf_local_smash_end. cbn; auto.
              rewrite -!subst_instance_app_ctx.
              pose proof (on_cargs onc). simpl in X.
              eapply sorts_local_ctx_wf_local in X0 => //.
              eapply typing_subst_instance_wf_local; tea.
              split => //. cbn. try apply onu.
              destruct ind_universes. cbn in eqv. noconf eqv.
              - now eapply on_udecl_on_udecl_prop.
              - eapply weaken_wf_local => //.
              now eapply wf_arities_context'. }
            { rewrite subst_instance_app subst_instance_smash.
              rewrite subst_instance_expand_lets_ctx.
              eapply wf_local_expand_lets.
              rewrite subst_instance_smash. unshelve eapply wf_local_smash_end. cbn; auto.
              rewrite -!subst_instance_app_ctx.
              pose proof (on_cargs onc). simpl in X0.
              eapply sorts_local_ctx_wf_local in X0 => //.
              eapply typing_subst_instance_wf_local; tea.
              split => //. cbn.
              - destruct ind_universes. cbn in eqv. noconf eqv.
                now eapply on_udecl_on_udecl_prop.
              - eapply weaken_wf_local => //.
                now eapply wf_arities_context'. }
            { now len. }
            { pose proof (assumption_context_arities_context (ind_bodies m)).
              rewrite subst_instance_app_ctx.
              repeat apply assumption_context_app_inv => //; pcuic. }
            { pose proof (assumption_context_arities_context (ind_bodies m)).
              rewrite subst_instance_app_ctx.
              repeat apply assumption_context_app_inv => //; pcuic. }
          }
          { do 3 eapply All2_map.
            eapply All2_map_inv in b.
            eapply All2_All in b. eapply All_All2_refl.
            pose proof (on_cindices onc) as X0.
            eapply ctx_inst_impl in X0. 2: intros ??; apply /unlift_TermTyp.
            apply ctx_inst_wt in X0.
            move/forallb_All: oncindices => hi.
            eapply All_mix in b; tea. clear hi.
            eapply (All_mix X0) in b; clear X0.
            eapply All_impl; tea; cbv beta.
            destruct (ind_universes m) eqn:eqind. noconf eqv.
            intros x [wtx [onfvs cv]].
            rewrite -!(trans_expand_lets (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)) //.
            rewrite shiftnP_add Nat.add_assoc //.
            cbn -[ind_arities].
            rewrite -(trans_smash_context (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0) []) //.
            rewrite [ind_arities _]trans_arities_context.
            rewrite -[trans_local _ ++ _]trans_local_app.
            have fvsparsargs : on_free_vars_ctx (shiftnP #|ind_bodies m| xpred0)
              (ind_params m,,, SE.smash_context [] (cstr_args cdecl)).
            { rewrite on_free_vars_ctx_app; apply /andP; split.
              eapply (on_free_vars_ctx_mon 0); tea. lia.
              rewrite on_free_vars_ctx_smash // shiftnP_add //. }
            rewrite -(trans_smash_context (shiftnP (#|ind_bodies m|) xpred0) []) //.
            rewrite -[_ ++ _]trans_local_app.
            rewrite -[map (map_decl _) _]trans_subst_instance_ctx.
            rewrite -!(trans_expand_lets (shiftnP #|ind_bodies m| xpred0)) //.
            { len => /=.
              rewrite -shiftnP_add.
              rewrite (on_free_vars_expand_lets_k _ _ 0) //  shiftnP_add // /= shiftnP_add //. }
            rewrite -!trans_subst_instance.
            eapply (trans_convSpec' (Σ := (Σ0, univs'))
              (Γ' := (arities_context (ind_bodies m),,,
              SE.smash_context []
                (ind_params m,,, SE.smash_context [] (cstr_args cdecl)))@[u'])); eauto.
            2:now len.
            2-3:pose proof (assumption_context_arities_context (ind_bodies m));
              rewrite subst_instance_app_ctx;
              repeat apply assumption_context_app_inv => //; pcuic.
            eapply conv_decorate_hetero; eauto.
            3:now len.
            3-4:pose proof (assumption_context_arities_context (ind_bodies m));
              rewrite subst_instance_app_ctx;
              repeat apply assumption_context_app_inv => //; pcuic.
            { eapply wt_subst_instance; tea.
              split => //. cbn. now eapply on_udecl_on_udecl_prop.
              eapply wt_expand_lets => //.
              rewrite app_context_assoc.
              eapply wt_expand_lets => //. }
            { eapply wt_subst_instance; tea.
              split => //. cbn. now eapply on_udecl_on_udecl_prop.
              eapply wt_expand_lets => //.
              rewrite app_context_assoc.
              eapply wt_expand_lets => //. }
            rewrite smash_context_app smash_context_idempotent.
            rewrite -smash_context_app.
            now rewrite !expand_lets_expand_lets. }
        }
        { cbn. apply (rwP (is_assumption_context_spec _)). pcuic. }
      }
    { have parsfvs: on_free_vars_ctx xpred0 (ind_params m).
      { red in onParams. now eapply wf_local_closed_context in onParams. }
      simpl ind_projs in *.
      destruct (ind_projs idecl) eqn:indps => //=.
      cbn. destruct (ind_ctors idecl) as [|c []] eqn:hctors => /= //.
      depelim onConstructors. depelim onConstructors.
      have wfargs : wf_local (Σ0, ind_universes m) (arities_context (ind_bodies m),,, ind_params m,,, cstr_args c).
      { destruct o. eapply sorts_local_ctx_wf_local in on_cargs => //.
        rewrite cstr_eq in on_ctype. destruct on_ctype as (_ & s & Hs & _).
        eapply typing_wf_local in Hs. eapply weaken_wf_local; tea. }
      have oncargs: on_free_vars_ctx (shiftnP (#|ind_params m| + #|ind_bodies m|) xpred0)
        (cstr_args c).
      { eapply wf_local_closed_context in wfargs.
        now move/onfvs_app: wfargs; len. }
      clear -indps X onu ond IHX onProjections wfargs oncargs.
      have lenprojs : #|ind_projs idecl| > 0.
      { destruct (ind_projs idecl) => /= //. lia. }
      destruct onProjections; econstructor; eauto; cbn; try len => //.
      rewrite context_assumptions_smash_context /= // context_assumptions_map //.
      eapply Alli_nth_hyp in on_projs.
      eapply Alli_map, Alli_impl; tea; cbv beta.
      move=> n' x [] hnthp. eapply nth_error_Some_length in hnthp.
      rewrite /on_projection.
      cbn [cstr_args trans_constructor_body ind_params trans_minductive_body].
      rewrite (smash_context_app _ (smash_context _ _)).
      rewrite smash_context_idempotent. rewrite -smash_context_app.
      rewrite -[trans_local _ ++ _]trans_local_app.
      rewrite -(trans_smash_context (shiftnP #|ind_bodies m| xpred0) []) //.
      { eapply wf_local_closed_context in wfargs.
        move: wfargs; rewrite -app_context_assoc => /onfvs_app. now len. }
      rewrite nth_error_map. rewrite context_assumptions_smash_context /= context_assumptions_map /=.
      destruct nth_error eqn:hnth => /= //. intros [onna onty onrel]; split; auto.
      simpl. rewrite onty.
      destruct x => /= //. cbn in *. subst proj_type0.
      set (ind := {| inductive_mind := kn; inductive_ind := n |}) in *.
      rewrite -(trans_inds ind).
      have fvsdecl : on_free_vars
        (shiftnP
          (n' + context_assumptions (ind_params m) + #|ind_bodies m|) xpred0)
        (decl_type c0).
      { eapply nth_error_smash_onfvs in hnth.
        2:{ apply on_free_vars_ctx_smash => //.
            eapply wf_local_closed_context in wfargs.
            now move: wfargs; rewrite -app_context_assoc => /onfvs_app. }
        len in hnth.
        move/andP: hnth => [] _ o.
        red; rewrite -o shiftnP_add. lia_f_equal. }
      erewrite <-(trans_lift _ _); tea.
      have fvslift : on_free_vars (shiftnP (n' + 1 + context_assumptions (ind_params m) + #|ind_bodies m|) xpred0)
        (lift 1 n' (decl_type c0)).
      { rewrite -2!shiftnP_add Nat.add_comm.
        eapply on_free_vars_lift_impl.
        rewrite !shiftnP_add //. }
      rewrite (trans_subst (shiftnP 1 (shiftnP (context_assumptions (ind_params m) + #|ind_bodies m|) xpred0)) xpred0).
      { eapply on_free_vars_subst; [eapply on_free_vars_projs|].
        rewrite projs_length !shiftnP_add Nat.add_assoc //. }
      { eapply (inds_is_open_terms [] ind). }
      f_equal. erewrite (trans_subst _ (shiftnP 1 xpred0)); tea.
      2:{ eapply on_free_vars_projs. }
      now rewrite trans_projs.
    }
    { cbn. move: ind_sorts.
      rewrite /check_ind_sorts.
      destruct Sort.to_family => //.
      intuition auto.
      rewrite /PCUICLookup.global_ext_constraints.
      destruct indices_matter => //.
      now eapply (trans_type_local_ctx (Σ := (Σ0, ind_universes m))). }
    { simpl ind_variance in *.
      move: onIndices. rewrite /ind_respects_variance.
      destruct (ind_variance m) => //.
      eapply variance_universes_insts in onVariance as [univs' [u [u' [eqv hunivs cu cu' equlen eqvlen equ' cli equ]]]].
      cbn [variance_universes ind_universes trans_minductive_body].
      rewrite eqv.
      cbn [cstr_args trans_constructor_body].
      cbn [ind_params trans_minductive_body].
      have clpars : is_closed_context (ind_params m).
      { now eapply wf_local_closed_context in onParams. }
      rewrite -(trans_smash_context xpred0 []) //.
      have wfindices := !! wf_ind_indices onind.
      have fvsindices: on_free_vars_ctx (shiftnP (#|ind_params m|) xpred0)
          (ind_indices idecl).
      { move/wf_local_closed_context: wfindices; rewrite on_free_vars_ctx_app => /andP[] //. }
      rewrite -(trans_smash_context (shiftnP (#|ind_params m|) xpred0) []) //.
      rewrite -(trans_expand_lets_ctx xpred0 (shiftnP (#|ind_params m|) xpred0)) //.
      rewrite on_free_vars_ctx_smash //.
      rewrite -!trans_subst_instance_ctx.
      have wf_ext : wf_global_ext Σ0 (ind_universes m).
      { destruct (ind_universes m) eqn:equniv => //.
        cbn. split => //. cbn. now eapply on_udecl_on_udecl_prop. }
      eapply (trans_cumul_ctx_rel' (Σ := (Σ0, univs'))
          (Γ' := (smash_context [] (ind_params m))@[u'])) => //.
      { rewrite subst_instance_expand_lets_ctx.
        rewrite !subst_instance_smash.
        rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
        eapply wf_local_expand_lets.
        rewrite app_context_nil_l. eapply wf_local_smash_end.
        rewrite -subst_instance_app_ctx.
        eapply wf_local_subst_instance; tea. }
      { rewrite subst_instance_expand_lets_ctx.
        rewrite !subst_instance_smash.
        rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
        eapply wf_local_expand_lets.
        rewrite app_context_nil_l. eapply wf_local_smash_end.
        rewrite -subst_instance_app_ctx.
        eapply wf_local_subst_instance; tea. }
      { now len. }
      { repeat apply assumption_context_app_inv; pcuic. }
      { repeat apply assumption_context_app_inv; pcuic. }
    }
  + cbn. eapply (trans_on_context _ _ onParams).
  + cbn. rewrite context_assumptions_map //.
Qed.

Lemma trans_wf_ext {cf} {Σ : global_env_ext} : wf_ext Σ -> wf_ext_trans Σ.
Proof.
  intros; split. now eapply trans_wf. destruct X.
  now eapply trans_on_udecl.
Qed.

(** From a typing derivation in pcuic we build one where there are no lets
  in constructor types, and branches of cases are appropriately substituted. *)
Theorem expand_lets_sound {cf} {Σ : global_env_ext} {Γ t T} {wfΣ : wf Σ} :
  typing Σ Γ t T ->
  typing (H := cf' cf) (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  intros ht; eapply pcuic_expand_lets; tea.
  now eapply trans_wf.
Qed.

(* Print Assumptions expand_lets_sound. *)

From MetaRocq.PCUIC Require Import PCUICWcbvEval PCUICClassification PCUICCSubst.

Lemma trans_csubst a k b :
  closed a ->
  closedn 1 b ->
  trans (csubst a k b) = csubst (trans a) k (trans b).
Proof.
  intros ona onb.
  rewrite closed_subst //.
  rewrite closed_subst //. rewrite on_free_vars_closedn trans_on_free_vars // -on_free_vars_closedn //.
  rewrite (trans_subst (shiftnP 1 xpred0) xpred0) //.
  rewrite closedn_on_free_vars //.
  cbn. now rewrite -(on_free_vars_closedn 0) ona.
Qed.

Lemma eval_wt {cf} {Σ} {wfΣ : wf Σ} {t t'} :
  wt Σ [] t ->
  eval Σ t t' ->
  wt Σ [] t'.
Proof.
  intros [T Ht] ev. exists T.
  now eapply subject_reduction_eval.
Qed.

Lemma wt_closed {cf} {Σ} {wfΣ : wf Σ} {Γ t} :
  wt Σ Γ t ->
  closedn #|Γ| t.
Proof.
  intros [T Ht]. exact (subject_closed Ht).
Qed.

(* Lemma wt_csubst {cf} {Σ} {wfΣ : wf Σ} {na t a b} :
  wt Σ [] a ->
  wt Σ [vass na t] b ->
  wt Σ [] (csubst a 0 b).
Proof.
  intros [Ta Ha] [Tb Hb].
  exists (subst [a] 0 Tb).
  rewrite closed_subst. exact (subject_closed Ha).
  eapply (substitution (Γ := []) (Δ := [])).
  now eapply subslet_ass_tip. rewrite app_context_nil_l. exact Hb. *)

Lemma closed_inst_case_context pars u ctx :
  forallb (closedn 0) pars ->
  closedn_ctx #|pars| ctx ->
  closed_ctx (inst_case_context pars u ctx).
Proof.
  intros hpars hctx.
  rewrite /inst_case_context.
  eapply (closedn_ctx_subst 0 0) => //. len.
  rewrite closedn_subst_instance_context //.
  rewrite forallb_rev //.
Qed.

Lemma trans_closedn k t : closedn k t -> closedn k (trans t).
Proof.
  rewrite !on_free_vars_closedn.
  apply trans_on_free_vars.
Qed.

Lemma isFixApp_trans f : isFixApp f = isFixApp (trans f).
Proof.
  induction f => //. cbn.
  rewrite (isFixApp_mkApps (trans f1) [trans f2]).
  now rewrite (isFixApp_mkApps f1 [f2]).
Qed.

Lemma isConstructApp_trans f : isConstructApp f = isConstructApp (trans f).
Proof.
  induction f => //. cbn.
  rewrite (isConstructApp_mkApps (trans f1) [trans f2]).
  now rewrite (isConstructApp_mkApps f1 [f2]).
Qed.

Lemma isPrimApp_trans f : isPrimApp f = isPrimApp (trans f).
Proof.
  induction f => //. cbn.
  rewrite (isPrimApp_mkApps (trans f1) [trans f2]).
  now rewrite (isPrimApp_mkApps f1 [f2]).
Qed.

Lemma trans_wcbveval {cf} {Σ} {wfΣ : wf Σ} {wfΣ' : wf_trans Σ} t u :
  closed t ->
  eval Σ t u -> eval (trans_global_env Σ) (trans t) (trans u).
Proof.
  intros wt ev; revert wt.
  induction ev.
  - move=> /= /andP[] onf ona. cbn in *. econstructor; eauto.
    clear wfΣ'. eapply eval_closed in onf; tea.
    eapply eval_closed in ona; tea.
    move: onf => /= /andP[] ont onb.
    rewrite -trans_csubst //.
    eapply IHev3. now eapply closed_csubst.
  - move=> /= /andP[] /andP[] onb0 ont onb1.
    clear wfΣ'. econstructor; eauto.
    eapply eval_closed in onb0; tea.
    rewrite -trans_csubst //.
    eapply IHev2.
    now eapply closed_csubst.
  - intros _. cbn. eapply declared_constant_from_gen in isdecl.
    econstructor.
    unshelve eapply @declared_constant_to_gen with (cf :=cf' cf); eauto.
    eapply trans_declared_constant; tea.
    cbn; rewrite e //.
    rewrite -trans_subst_instance; apply IHev.
    rewrite closedn_subst_instance.
    eapply declared_constant_closed_body in isdecl; tea.
  - move=> /= /andP[] /andP[] clp cldiscr clbrs.
    rewrite trans_mkApps in IHev1.
    econstructor.
    * eapply IHev1; eauto.
    * rewrite !nth_error_map e0 //.
    * unshelve eapply @declared_constructor_to_gen with (cf :=cf' cf); eauto.
      eapply trans_declared_constructor; tea.
      apply declared_constructor_from_gen; eauto.
    * len. rewrite e1 /cstr_arity.
      cbn. rewrite context_assumptions_smash_context context_assumptions_map /= //.
    * now rewrite e2.
    * cbn.
      rewrite trans_bcontext.
      rewrite !context_assumptions_smash_context !context_assumptions_map //.
    * rewrite /iota_red.
      cbn -[expand_lets].
      rewrite expand_lets_assumption_context.
      { apply assumption_context_subst_context.
        apply assumption_context_subst_instance.
        rewrite trans_bcontext.
        apply smash_context_assumption_context; pcuic. }
      eapply nth_error_forallb in clbrs; tea.
      move: clbrs => /andP[] clctx clb.
      move/andP: clp => [] /= /andP[] clpars clpctx clpret.
      have clexp: closedn (context_assumptions (bcontext br))
        (expand_lets (inst_case_branch_context p br) (bbody br)).
      { relativize (context_assumptions _).
        eapply (closedn_expand_lets 0) => //. 3:now len.
        2:{ len. rewrite Nat.add_0_r // in clb. }
        eapply closed_inst_case_context => //. }
      have clargs : forallb (closedn 0) args.
      { eapply eval_closed in ev1; tea.
        now move: ev1; rewrite closedn_mkApps /= => ev1. }
      forward IHev2.
      { rewrite /iota_red.
        eapply closedn_subst0 => //.
        now rewrite forallb_rev; apply forallb_skipn.
        cbn; len. rewrite length_skipn e1 /cstr_arity -e2 e3.
        replace (ci_npar ci + context_assumptions (bcontext br) - ci_npar ci)
          with (context_assumptions (bcontext br)) by lia.
        eauto.
        }
      relativize (subst0 _ _). exact IHev2.
      rewrite /iota_red.
      rewrite (trans_subst (shiftnP (context_assumptions (bcontext br)) xpred0) xpred0).
      rewrite closedn_on_free_vars //.
      rewrite forallb_rev forallb_skipn //.
      eapply forallb_impl; tea. intros.
      rewrite -(on_free_vars_closedn 0) //.
      rewrite map_rev map_skipn. f_equal.
      rewrite (trans_expand_lets xpred0).
      rewrite /inst_case_branch_context.
      apply (closedn_ctx_on_free_vars 0).
      eapply closed_inst_case_context => //.
      len. rewrite Nat.add_0_r in clb. rewrite closedn_on_free_vars //.
      f_equal.
      rewrite /inst_case_branch_context /inst_case_context.
      rewrite (trans_subst_context (shiftnP #|pparams p| xpred0) xpred0).
      rewrite on_free_vars_ctx_subst_instance.
      { now apply closedn_ctx_on_free_vars. }
      rewrite /on_free_vars_terms forallb_rev.
      eapply forallb_impl; tea. intros. now eapply (@closedn_on_free_vars xpred0 0).
      rewrite map_rev. rewrite trans_bbody trans_subst_instance_ctx //.

  - cbn => cldiscr.
    specialize (IHev1 cldiscr). rewrite trans_mkApps in IHev1.
    eapply declared_projection_from_gen in d.
    eapply trans_declared_projection in d; tea.
    econstructor; tea.
    unshelve eapply @declared_projection_to_gen with (cf:=cf' cf); eauto.
    { len. rewrite /cstr_arity e0. cbn.
      rewrite context_assumptions_smash_context /= /cstr_arity context_assumptions_map //. }
    rewrite nth_error_map e1 //.
    apply IHev2.
    eapply eval_closed in ev1; tea.
    move: ev1; rewrite closedn_mkApps /= => onargs.
    eapply nth_error_forallb in onargs; tea.

  - move=> /= /andP[] clf cla.
    rewrite trans_mkApps /= in IHev1.
    eapply eval_closed in ev1; tea.
    move: ev1; rewrite closedn_mkApps => /andP[] clfix clargsv.
    rewrite -closed_unfold_fix_cunfold_eq in e1 => //.
    forward IHev3.
    { cbn. apply/andP; split.
      rewrite closedn_mkApps /= clargsv andb_true_r.
      eapply closed_unfold_fix; tea. now eapply eval_closed in ev2. }
    eapply (trans_unfold_fix xpred0) in e1; tea.
    2:now eapply (@closedn_on_free_vars xpred0 0).
    eapply eval_fix; eauto. len.
    rewrite -closed_unfold_fix_cunfold_eq; tea.
    now eapply closedn_trans in clfix.
    cbn in IHev3. rewrite trans_mkApps in IHev3. eapply IHev3.

  - move=> /= /andP[] clf cla.
    rewrite trans_mkApps /= in IHev1.
    eapply eval_closed in ev1; tea.
    move: ev1; rewrite closedn_mkApps => /andP[] clfix clargsv.
    rewrite -closed_unfold_fix_cunfold_eq in e1 => //.
    specialize (IHev1 clf).
    rewrite trans_mkApps /=.
    eapply (trans_unfold_fix xpred0) in e1; tea.
    2:now eapply (@closedn_on_free_vars xpred0 0).
    eapply eval_fix_value. eauto. eauto.
    rewrite -closed_unfold_fix_cunfold_eq; tea.
    now eapply closedn_trans in clfix. now len.

  - move=> /= /andP[] /andP[] clp.
    intros cldiscr clbrs. clear wfΣ'.
    eapply eval_closed in cldiscr as clfix; eauto.
    rewrite closedn_mkApps in clfix.
    revert clfix. move /andP => [].
    intros clfix clargs.

    rewrite -closed_unfold_cofix_cunfold_eq in e => //.
    forward IHev1. eauto.
    forward IHev2.
    { cbn. rewrite clp clbrs closedn_mkApps /=.
      rewrite (closed_unfold_cofix mfix idx narg fn) // clargs //. }
    cbn in IHev2. rewrite trans_mkApps /= in IHev1.
    eapply (trans_unfold_cofix xpred0) in e; tea.
    2:now eapply (@closedn_on_free_vars xpred0 0).
    eapply eval_cofix_case. 2:eauto.
    rewrite -closed_unfold_cofix_cunfold_eq; tea.
    now eapply closedn_trans in clfix.
    rewrite trans_mkApps in IHev2 => //.

  - move=> /=.
    intros cldiscr. clear wfΣ'.
    eapply eval_closed in cldiscr as clfix; eauto.
    revert clfix.
    rewrite closedn_mkApps => /andP[] clfix clargs.
    rewrite -closed_unfold_cofix_cunfold_eq in e => //.
    forward IHev1. eauto.
    forward IHev2.
    { cbn. rewrite closedn_mkApps /=.
      rewrite (closed_unfold_cofix mfix idx narg fn) // clargs //. }
    cbn in IHev2. rewrite trans_mkApps /= in IHev1.
    eapply (trans_unfold_cofix xpred0) in e; tea.
    2:now eapply (@closedn_on_free_vars xpred0 0).
    eapply eval_cofix_proj. 2: eauto.
    rewrite -closed_unfold_cofix_cunfold_eq; tea.
    now eapply closedn_trans in clfix.
    rewrite trans_mkApps in IHev2 => //.

  - move=> /= /andP[] clf cla.
    rewrite trans_mkApps map_app.
    eapply declared_constructor_from_gen in d.
    eapply trans_declared_constructor in d; tea.
    eapply eval_construct; tea.
    + unshelve eapply @declared_constructor_to_gen with (cf:=cf' cf); eauto.
    + move: (IHev1 clf). rewrite trans_mkApps //.
    + move: l; rewrite length_map /cstr_arity /= context_assumptions_smash_context
       context_assumptions_map //.
    + now eapply IHev2.

  - move=> /= /andP[] clf cla.
    eapply eval_app_cong; eauto.
    rewrite -isFixApp_trans -isConstructApp_trans -isPrimApp_trans.
    clear -i. induction f' => /= //.

  - cbn. depelim X; do 2 constructor; eauto; cbn in *; rtoProp; intuition auto.
    eapply All2_undep in a. solve_all.
  - move=> clt. eapply eval_atom.
    destruct t => //.
Qed.

From MetaRocq.PCUIC Require Import PCUICEtaExpand.

Lemma trans_isConstruct t : isConstruct t = isConstruct (trans t).
Proof. destruct t => //. Qed.
Lemma trans_isRel t : isRel t = isRel (trans t).
Proof. destruct t => //. Qed.
Lemma trans_isFix t : isFix t = isFix (trans t).
Proof. destruct t => //. Qed.

(** Let expansion preserves eta-expandedness *)
Set Printing Width 150.

Lemma expanded_expand_lets {cf:checker_flags}
  {Σ : global_env} {wfΣ : wf Σ} Γ t :
  expanded Σ Γ t ->
  expanded (trans_global_env Σ) Γ (PCUICExpandLets.trans t).
Proof.
  induction 1 using expanded_ind; cbn.
  all:try constructor; auto.
  - rewrite trans_mkApps /=. eapply expanded_tRel; tea. now len. solve_all.
  - solve_all.
  - rewrite trans_mkApps. constructor; eauto; [|solve_all].
    now rewrite -trans_isConstruct -trans_isRel -trans_isFix.
  - cbn. solve_all.
  - do 2 eapply Forall_map. repeat toAll. eapply All_impl; tea. cbn.
    intros x [expb IH].
    rewrite trans_bcontext trans_bbody. len; cbn. rewrite /id.
    split. sq.
    { have: (assumption_context (smash_context [] (trans_local (bcontext x)))) by pcuic.
      clear. generalize (smash_context [] (trans_local (bcontext x))).
      induction c; intros; constructor.
      apply IHc. now depelim H.
      destruct a as [na [b|] ty]; cbn; constructor => //.
      now depelim H. }
    relativize (context_assumptions (bcontext x)).
    destruct expb as [[] ?], IH as [[] ?].
    eapply expanded_let_expansion.
    { rewrite /subst_context.
      red; sq. eapply PCUICParallelReduction.All_fold_fold_context_k.
      do 2 eapply All_fold_map_context. cbn.
      eapply All_fold_impl; tea; cbn. clear -H1. intros ??; len; intros []; cbn; constructor.
      eapply expanded_subst. now rewrite repeat_length.
      eapply All_Forall, All_rev, All_map. solve_all. eapply expanded_subst_instance.
      len. rewrite app_assoc -repeat_app.
      now eapply expanded_weakening. }
    len; exact e0.
    now len.
  - rewrite trans_mkApps. cbn. eapply expanded_tFix. solve_all.
    rewrite trans_isLambda //.
    rewrite rev_map_spec. rewrite rev_map_spec in b.
    rewrite map_map_compose. cbn. exact b. solve_all.
    destruct args => //. now rewrite nth_error_map H4. len. now cbn.
  - solve_all.
  - rewrite trans_mkApps; eapply expanded_tConstruct_app.
    unshelve eapply (trans_declared_constructor (empty_ext Σ)) in H.
    4:eauto. len.
    cbn. now rewrite context_assumptions_smash_context context_assumptions_map /=.
    solve_all.
  - depelim H0; constructor; cbn; eauto. solve_all.
Qed.

Lemma expanded_trans_local {cf:checker_flags}
  {Σ : global_env_ext} {wfΣ : wf Σ.1} Γ ctx :
  expanded_context Σ Γ ctx -> expanded_context (trans_global_env Σ) Γ (trans_local ctx).
Proof.
  rewrite /expanded_context.
  intros [a]; split.
  eapply All_fold_map_context, All_fold_impl; tea; cbv beta.
  intros ??; cbn; intros [];
  constructor; len; eapply expanded_expand_lets; eauto.
Qed.

Lemma expanded_smash_context {Σ} Γ ctx :
  expanded_context Σ Γ ctx -> expanded_context Σ Γ (smash_context [] ctx).
Proof.
  rewrite /expanded_context.
  intros [a].
  forward (@smash_context_assumption_context nil ctx). constructor.
  generalize (smash_context [] ctx). clear.
  intros c a; induction a. repeat constructor. destruct IHa; sq.
  now repeat constructor.
Qed.

Lemma wf_cons_inv {cf} univs retro (Σ : global_declarations) d :
  wf {| universes := univs; declarations := d :: Σ; retroknowledge := retro |} ->
  wf {| universes := univs; declarations := Σ; retroknowledge := retro |}.
Proof.
  intros []. split => //. now depelim o0.
Qed.

Lemma expanded_global_env_expand_lets {cf} Σ {wfΣ : wf Σ} :
  PCUICEtaExpand.expanded_global_env Σ ->
  expanded_global_env (trans_global_env Σ).
Proof.
  destruct Σ as [[univs Σ] udecl]. cbn. unfold expanded_global_env; cbn.
  intros etaenv; induction etaenv; cbn; constructor; auto.
  - forward IHetaenv by eapply wf_cons_inv; tea. auto.
  - forward IHetaenv by eapply wf_cons_inv; tea.
    destruct decl as [kn []]; cbn in *; depelim H => //.
    * unfold PCUICExpandLets.trans_constant_body; cbn.
      constructor. cbn.
      destruct (cst_body c); cbn => //. cbn in expanded_body.
      unshelve eapply expanded_expand_lets in expanded_body; eauto.
      destruct wfΣ; econstructor; eauto.
      cbn in *. inversion o0; eauto.
    * set (Σ' := {| T.PCUICEnvironment.universes := _; T.PCUICEnvironment.declarations := Σ |}) in *.
      change {| T.PCUICEnvironment.universes := _ |} with (trans_global_env Σ').
      constructor.
      + cbn. eapply (expanded_trans_local (Σ := (Σ', udecl)) _ _ expanded_params).
      + cbn. solve_all. eapply All_mapi. eapply All_Alli; tea. intros n x [].
        constructor. cbn. solve_all.
        destruct H. constructor.
        { cbn. eapply (expanded_trans_local (Σ := (Σ', udecl))) in expanded_cstr_args.
          eapply (expanded_smash_context (Σ := (trans_global_env Σ', udecl))) in expanded_cstr_args.
          now len. }
        Unshelve. all: eauto.
                  all: unfold Σ'; cbn; destruct wfΣ; econstructor; eauto.
                  all: inversion o0; eauto.
Qed.

From MetaRocq.PCUIC Require Import PCUICProgram PCUICFirstorder.

Lemma expanded_expand_lets_program {cf : checker_flags} p (wtp : wt_pcuic_program p) :
  expanded_pcuic_program p ->
  expanded_pcuic_program (expand_lets_program p).
Proof.
  destruct p as [[Σ udecl] t]; intros [etaenv etat].
  destruct wtp as [wfΣ wtp].
  cbn in *. split; cbn.
  now eapply (expanded_global_env_expand_lets (cf:=cf) (Σ, udecl)).
  cbn in *.
  now eapply expanded_expand_lets in etat.
  Unshelve. all:eauto. destruct wfΣ; eauto.
Qed.

Lemma expand_lets_fo {cf : checker_flags} (Σ : global_env_ext_map) t :
  firstorder_value Σ [] t ->
  let p := (Σ, t) in
  expand_lets_program p =
  (build_global_env_map (PCUICAst.PCUICEnvironment.fst_ctx (PCUICExpandLets.trans_global p.1)), p.1.2, t).
Proof.
  intros p.
  cbn. unfold PCUICExpandLets.expand_lets_program. f_equal. cbn.
  move: p. apply: (firstorder_value_inds _ _ (fun t => trans t = t)).
  intros i n ui u args pandi ht hf ih isp.
  rewrite trans_mkApps /=. f_equal.
  now eapply forall_map_id_spec.
Qed.

Lemma isArity_trans T : isArity T = isArity (PCUICExpandLets.trans T).
Proof.
  induction T => //.
Qed.

Lemma mkApps_trans_inv fn args T :
  mkApps fn args = trans T ->
  ∑ fn' args', T = mkApps fn' args' × fn = trans fn' × args = List.map trans args'.
Proof.
  revert T; induction args using rev_ind; cbn; intros T.
  - intros ->. exists T, []; split => //.
  - rewrite mkApps_app /=. destruct T => //=.
    intros [=]. subst x. eapply IHargs in H0 as [fn' [args' [? []]]]; subst.
    exists fn', (args' ++ [T2])%list. rewrite mkApps_app. split => //.
    split => //. now rewrite List.map_app.
Qed.

Lemma expand_lets_k_tRel_ass {Γ i k x} :
  nth_error Γ i = Some x ->
  decl_body x = None ->
  expand_lets_k Γ k (tRel (k + i)) = tRel (context_assumptions (firstn i Γ) + k).
Proof.
  intros hnth hbo.
  rewrite /expand_lets /expand_lets_k.
  rewrite TL.lift_rel_lt. eapply nth_error_Some_length in hnth. lia.
  cbn.
  destruct (Nat.leb_spec0 k (k + i)); try lia.
  replace (k + i - k) with i by lia.
  rewrite nth_error_extended_subst hnth hbo. cbn. lia_f_equal.
Qed.

Lemma context_assumptions_firstn {n Γ x} :
  n < #|Γ| ->
  nth_error Γ n = Some x -> decl_body x = None ->
  context_assumptions (firstn n Γ) < context_assumptions Γ.
Proof.
  induction n in Γ |- *.
  - rewrite firstn_0 //=.
    destruct Γ => //. intros hl [= <-].
    cbn. intros ->. lia.
  - intros hl. destruct Γ => //=.
    intros hnth hbod. cbn in hl.
    specialize (IHn Γ). forward IHn by lia. specialize (IHn hnth hbod).
    destruct (decl_body c); lia.
Qed.

From MetaRocq.PCUIC Require Import PCUICLiftSubst PCUICContexts PCUICOnFreeVars.

Lemma expand_lets_tFix Γ mfix idx k :
  expand_lets_k Γ k (tFix mfix idx) = tFix (List.map (map_def (expand_lets_k Γ k) (expand_lets_k Γ (#|mfix| + k))) mfix) idx.
Proof.
  cbn. f_equal. len.
  rewrite map_map_compose. eapply map_ext.
  intros []; unfold map_def; cbn. f_equal.
  now rewrite Nat.add_assoc.
Qed.

Lemma expand_lets_tCoFix Γ mfix idx k :
  expand_lets_k Γ k (tCoFix mfix idx) = tCoFix (List.map (map_def (expand_lets_k Γ k) (expand_lets_k Γ (#|mfix| + k))) mfix) idx.
Proof.
  cbn. f_equal. len.
  rewrite map_map_compose. eapply map_ext.
  intros []; unfold map_def; cbn. f_equal.
  now rewrite Nat.add_assoc.
Qed.

Lemma expand_lets_k_ctx_fix_context Γ k mfix :
  expand_lets_k_ctx Γ k (fix_context mfix) =
  fix_context (List.map (map_def (expand_lets_k Γ k) (expand_lets_k Γ (#|fix_context mfix| + k))) mfix).
Proof.
  unfold expand_lets_k_ctx.
  rewrite -PCUICWeakeningConv.lift_fix_context.
  rewrite -PCUICSubstitution.subst_fix_context.
  f_equal. rewrite map_map_compose.
  apply map_ext => [].
  intros []. len. rewrite map_def_map_def /map_def; cbn.
  f_equal. now rewrite Nat.add_assoc.
Qed.

Lemma expand_lets_ctx_fix_context Γ mfix :
  expand_lets_ctx Γ (fix_context mfix) =
  fix_context (List.map (map_def (expand_lets Γ) (expand_lets_k Γ #|fix_context mfix|)) mfix).
Proof.
  rewrite /expand_lets_ctx.
  now rewrite expand_lets_k_ctx_fix_context Nat.add_0_r.
Qed.

Lemma expand_lets_k_rel_lt Γ k i :
  i < k -> expand_lets_k Γ k (tRel i) = tRel i.
Proof.
  intros hi. rewrite /expand_lets_k.
  rewrite lift_rel_lt. lia.
  rewrite subst_rel_lt //.
Qed.

Lemma expand_lets_k_rel_ge k Γ n :
  expand_lets_k Γ n (tRel (k + #|Γ| + n)) = tRel (k + context_assumptions Γ + n).
Proof.
  rewrite /expand_lets /expand_lets_k.
  rewrite lift_rel_ge; try lia.
  rewrite subst_rel_gt; len; try lia.
  lia_f_equal.
Qed.

Lemma expand_lets_inst_case_context (Γ Δ : context) p ctx :
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pparams p| ctx ->
  expand_lets_k_ctx Γ #|Δ| (inst_case_context (pparams p) (puinst p) ctx) =
  inst_case_context (List.map (expand_lets_k Γ #|Δ|) (pparams p)) (puinst p) ctx.
Proof.
  intros hctx.
  rewrite test_context_k_closed_on_free_vars_ctx in hctx.
  unfold inst_case_context.
  unfold expand_lets_k_ctx.
  rewrite distr_lift_subst_context. len.
  rewrite subst_context_subst_context.
  rewrite map_map_compose. len. rewrite map_rev. f_equal.
  rewrite PCUICClosed.closed_ctx_lift.
  rewrite closedn_ctx_on_free_vars.
  rewrite on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_impl; tea. intros i. eapply closedP_mon. lia.
  rewrite PCUICSpine.closed_ctx_subst //.
  rewrite closedn_ctx_on_free_vars.
  rewrite on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_impl; tea. intros i. eapply closedP_mon. lia.
Qed.

Lemma ne_nf_smash_context Σ Γ T :
  (ne Σ Γ T -> is_open_term Γ T -> forall Δ Γ' Δ', Γ = Γ' ,,, Δ ,,, Δ' -> ne Σ (Γ' ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Δ') (expand_lets_k Δ #|Δ'| T)) /\
  (nf Σ Γ T -> is_open_term Γ T -> forall Δ Γ' Δ', Γ = Γ' ,,, Δ ,,, Δ' -> nf Σ (Γ' ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Δ') (expand_lets_k Δ #|Δ'| T)).
Proof.
  apply: (ne_nf_ind_all _
    (fun Γ T => is_open_term Γ T -> forall Δ Γ' Δ', Γ = Γ' ,,, Δ ,,, Δ' -> ne _ _ _)
    (fun Γ T => is_open_term Γ T -> forall Δ Γ' Δ', Γ = Γ' ,,, Δ ,,, Δ' -> nf _ _ _)); intros; subst Γ0;
    try solve [cbn; econstructor; inv_on_free_vars; eauto; solve_all].
  - move: H; unfold app_context. rewrite app_assoc. case: (TL.nth_error_appP (Δ' ++ Δ) Γ' i) => //=.
    * intros x.
      case: (TL.nth_error_appP Δ' Δ i) => //=; intros. noconf e0; noconf H.
      rewrite expand_lets_k_rel_lt //. constructor. cbn.
      rewrite nth_error_app_lt //. rewrite expand_lets_ctx_length. lia.
      rewrite PCUICInductiveInversion.nth_error_expand_lets /= e /= H //.
      noconf e0. noconf H.
      assert (exists i', i' + #|Δ'| = i).
      exists (i - #|Δ'|). lia. destruct H1 as [i' <-]. noconf H.
      rewrite Nat.add_comm.
      replace (i' + #|Δ'| - #|Δ'|) with i' in e by lia.
      rewrite (expand_lets_k_tRel_ass e) //.
      constructor.
      assert (i' < #|Δ|) by lia.
      rewrite nth_error_app_ge.
      rewrite expand_lets_ctx_length; lia.
      rewrite nth_error_app_lt. len. cbn.
      epose proof (context_assumptions_firstn H1 e H); tea. lia.
      destruct (nth_error (smash_context _ _) _) eqn:hnth.
      eapply nth_error_smash_context in hnth. cbn. congruence.
      intros ? ?; rewrite nth_error_nil //.
      eapply nth_error_None in hnth. len in hnth. cbn in hnth.
      pose proof (context_assumptions_firstn H1 e H). lia.
    * intros x. len. intros hnth he.
      assert (exists i', i' + #|Δ| + #|Δ'| = i).
      exists (i - #|Δ'| - #|Δ|). lia. destruct H as [i' <-].
      rewrite expand_lets_k_rel_ge.
      constructor.
      rewrite nth_error_app_ge. rewrite expand_lets_ctx_length. lia.
      rewrite nth_error_app_ge. len; cbn. lia. len; cbn.
      noconf H. rewrite -H. change (Some (decl_body x)) with (option_map decl_body (Some x)).
      rewrite -hnth. lia_f_equal.
  - rewrite expand_lets_k_mkApps.
    rewrite expand_lets_tFix.
    inv_on_free_vars.
    set (mfix' := List.map _ _).
    econstructor; eauto.
    * rewrite !nth_error_map H /= //.
    * rewrite !nth_error_map /= H0 //.
    * solve_all.
    * eapply H2; eauto. toAll. eapply nth_error_all in b; cbn in *; eauto.
    * unfold mfix' at 2. solve_all; inv_on_free_vars; eauto.
      forward H5. { len. len in b0. now rewrite shiftnP_add in b0. }
      specialize (H5 Δ Γ' (Δ' ,,, fix_context mfix)). rewrite app_context_assoc in H5.
      specialize (H5 eq_refl). len in H5.
      rewrite PCUICInductives.expand_lets_ctx_app in H5.
      rewrite expand_lets_k_ctx_fix_context app_context_assoc in H5 => //.
      now len in H5.
  - cbn. econstructor. inv_on_free_vars.
    * now eapply H0.
    * inv_on_free_vars. solve_all. rewrite /id.
      rewrite -/(expand_lets_k Δ _ _).
      rewrite /inst_case_branch_context /=.
      forward H4. {  len; len in H6. rewrite shiftnP_add in H6 => //. }
      specialize (H4 Δ Γ' (Δ' ,,, inst_case_branch_context p x)).
      rewrite app_context_assoc in H4. specialize (H4 eq_refl).
      rewrite PCUICInductives.expand_lets_ctx_app in H4.
      len in H4.
      rewrite expand_lets_inst_case_context ?app_context_assoc in H4 => //.
    * cbn. inv_on_free_vars. solve_all.
    * inv_on_free_vars. rewrite /inst_case_predicate_context /= /id.
      rewrite map_map_compose. rewrite -/(expand_lets_k _ _).
      rewrite -expand_lets_inst_case_context //.
      rewrite test_context_k_closed_on_free_vars_ctx //.
      epose proof (PCUICInstConv.on_free_vars_ctx_inst_case_context_nil _ _ (puinst p) _ p0 p2).
      revert X3 H3; clear. rewrite /inst_case_predicate_context.
      induction 1; try constructor; eauto.
      all:unfold PCUICInduction.on_local_decl in t0; cbn in * |-.
      all:rewrite on_free_vars_ctx_snoc => /andP[] HΓ hna; cbn in hna;
      rewrite -> shiftnP_add in hna; len in hna; try len in t0; try len in t1; try len in t2; specialize (IHX3 HΓ).
      2: move/andP: hna => [] hna0 hna1.
      all: rewrite PCUICInductives.expand_lets_k_ctx_snoc; constructor; eauto; cbn -[expand_lets_k] in *.
      all: eapply lift_wf_term_it_impl with (1 := t0) => // IH.
      all: forward IH by assumption.
      all: specialize (IH Δ Γ' (Δ' ,,, Γ)); forward IH by now rewrite app_context_assoc.
      all: rewrite PCUICInductives.expand_lets_ctx_app app_context_assoc in IH; len in IH.
  * cbn. inv_on_free_vars.
    forward H2. { rewrite shiftnP_add in p1 => //. len in p1. now len. }
    specialize (H2 Δ Γ' (Δ' ,,, inst_case_context (pparams p) (puinst p) (pcontext p))).
    rewrite app_context_assoc in H2. specialize (H2 eq_refl).
    rewrite PCUICInductives.expand_lets_ctx_app app_context_assoc in H2.
    rewrite expand_lets_inst_case_context in H2 => //. rewrite test_context_k_closed_on_free_vars_ctx //.
    len in H2. rewrite Nat.add_assoc. rewrite map_map_compose. exact H2.
  - cbn. inv_on_free_vars. eapply nf_lam; eauto.
    forward H2. { rewrite shiftnP_add in b0. len in b0; cbn. now len. }
    specialize (H2 Δ Γ'  (Δ' ,, vass na A) eq_refl).
    rewrite PCUICInductives.expand_lets_ctx_snoc in H2 => //.
  - inv_on_free_vars. rewrite expand_lets_k_mkApps. rewrite expand_lets_tCoFix.
    eapply nf_cofix. solve_all. inv_on_free_vars.
    forward H1. { len. rewrite shiftnP_add in b0. now len in b0. }
    specialize (H1 Δ Γ' (Δ' ,,, fix_context mfix)). rewrite app_context_assoc in H1; specialize (H1 eq_refl).
    rewrite PCUICInductives.expand_lets_ctx_app app_context_assoc in H1.
    rewrite expand_lets_k_ctx_fix_context in H1. now len in H1.
    inv_on_free_vars.
    now eapply H3.
    solve_all.
  - cbn. inv_on_free_vars. eapply nf_tProd; eauto.
    forward H2. rewrite shiftnP_add in b. cbn; len. now len in b.
    specialize (H2 Δ Γ' (Δ' ,, vass na dom) eq_refl).
    rewrite PCUICInductives.expand_lets_ctx_snoc in H2 => //.
Qed.

Lemma trans_case_context (Γ : context) p br :
  let p' := (map_predicate id trans trans (map_context trans) p) in
  forallb (is_open_term Γ) (pparams p) ->
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pparams p| (bcontext br) ->
  smash_context [] (trans_local (inst_case_context (pparams p) (puinst p) (bcontext br))) =
  inst_case_context (List.map trans (pparams p)) (puinst p)
    (bcontext (trans_branch p' (map_branch trans (map_context trans) br))).
Proof.
  intros p' hpars hbctx.
  unfold trans_branch.
  destruct is_assumption_context eqn:hn.
  - move/is_assumption_context_spec: hn. cbn.
    rewrite -trans_assumption_context.
    intros ass. rewrite smash_assumption_context.
    rewrite -trans_assumption_context.
    rewrite /inst_case_context.
    eapply PCUICInductiveInversion.assumption_context_subst_context.
    now eapply PCUICInductiveInversion.assumption_context_subst_instance.
    unfold inst_case_context.
    erewrite trans_subst_context.
    rewrite map_rev.
    rewrite trans_subst_instance_ctx //.
    rewrite test_context_k_closed_on_free_vars_ctx in hbctx.
    rewrite on_free_vars_ctx_subst_instance; tea.
    rewrite /on_free_vars_terms forallb_rev //. exact hpars.
  - cbn.
    rewrite /inst_case_context.
    erewrite trans_subst_context.
    rewrite map_rev trans_subst_instance_ctx //.
    rewrite PCUICUnivSubstitutionConv.subst_instance_smash.
    rewrite -PCUICClosed.smash_context_subst. cbn.
    rewrite subst_context_nil //.
    rewrite test_context_k_closed_on_free_vars_ctx in hbctx.
    rewrite on_free_vars_ctx_subst_instance; tea.
    rewrite /on_free_vars_terms forallb_rev //. exact hpars.
Qed.

Lemma trans_local_case_context (Γ : context) p ctx :
  let p' := (map_predicate id trans trans (map_context trans) p) in
  forallb (is_open_term Γ) (pparams p) ->
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pparams p| ctx ->
  trans_local (inst_case_context (pparams p) (puinst p) ctx) =
  inst_case_context (List.map trans (pparams p)) (puinst p) (trans_local ctx).
Proof.
  intros p' hpars hbctx.
  rewrite /inst_case_context.
  erewrite trans_subst_context.
  rewrite map_rev.
  rewrite trans_subst_instance_ctx //.
  rewrite test_context_k_closed_on_free_vars_ctx in hbctx.
  rewrite on_free_vars_ctx_subst_instance; tea.
  rewrite /on_free_vars_terms forallb_rev //. exact hpars.
Qed.

Lemma All_local_env_on_free_vars_ctx P P' Γ :
  PCUICTyping.All_local_env (PCUICInduction.on_local_decl P) Γ ->
  on_free_vars_ctx P' Γ ->
  PCUICTyping.All_local_env (PCUICInduction.on_local_decl (fun Γ t => P Γ t × on_free_vars (shiftnP #|Γ| P') t)) Γ.
Proof.
  induction 1; cbn; constructor; eauto; move: H; rewrite alli_app => /andP[] hΓ /= hass; len in hass; intuition eauto;
  unfold on_free_vars_decl, test_decl in *; cbn in *; rtoProp; intuition auto.
  all: apply lift_wf_term_it_impl with (1 := t0) => //.
Qed.

Lemma trans_ne_nf Σ Γ T :
  (ne Σ Γ T -> is_open_term Γ T -> ne (trans_global_env Σ) (trans_local Γ) (trans T)) /\
  (nf Σ Γ T -> is_open_term Γ T -> nf (trans_global_env Σ) (trans_local Γ) (trans T)).
Proof.
  apply: (ne_nf_ind_all _  (fun Γ T => _ -> ne (trans_global_env Σ) (trans_local Γ) (trans T))
    (fun Γ T => _ -> nf (trans_global_env Σ) (trans_local Γ) (trans T))); cbn; intros;
      try solve [constructor; eauto; solve_all].
  - econstructor. rewrite nth_error_map.
    destruct nth_error => //. cbn in H |- *. noconf H. now rewrite H.
  - econstructor. rewrite trans_lookup H /= //. cbn. now rewrite H0.
  - rewrite trans_mkApps /=.
    inv_on_free_vars. econstructor; eauto.
    * rewrite nth_error_map H //.
    * rewrite nth_error_map /= H0 //.
    * solve_all.
    * solve_all. eapply H2. eapply nth_error_all in b; tea. intuition eauto. now destruct b.
    * erewrite <- trans_fix_context => //. solve_all.
      rewrite trans_local_app /trans_local in H5.
      eapply H5.
      inv_on_free_vars. len. now rewrite -shiftnP_add.
      eapply H7. now inv_on_free_vars.
      instantiate (1 := idx).
      cbn. solve_all.
  - econstructor; eauto; solve_all; rtoProp.
    * solve_all.
      rewrite trans_local_app in H8.
      rewrite trans_bbody.
      rewrite /inst_case_branch_context in H8.
      rewrite /inst_case_branch_context /=.
      rewrite -(trans_case_context Γ0); solve_all; eauto.
      forward H8. len. rewrite shiftnP_add in H10 => //.
      unshelve epose proof (proj2 (ne_nf_smash_context (trans_global Σ) _ _) H8 _
        (trans_local (inst_case_context (pparams p) (puinst p) (bcontext x)))
        (trans_local Γ0) [] eq_refl).
      { cbn; len. rewrite shiftnP_add in H10. now apply trans_on_free_vars. }
      rewrite /id. rewrite {2 3}(trans_local_case_context Γ0) in H11; eauto. solve_all.
    * cbn. solve_all.
    * rewrite /inst_case_predicate_context /= /id.
      rewrite /map_context.
      change (List.map trans_decl) with (trans_local).
      rewrite -(trans_local_case_context Γ0) //. solve_all.
      rewrite /inst_case_predicate_context in X3.
      eapply All_local_env_map; cbn; eauto. clear -H5 H3 X3.
      rewrite test_context_k_closed_on_free_vars_ctx in H5.
      eapply (PCUICInstConv.on_free_vars_ctx_inst_case_context_nil _ _ (puinst p)) in H5.
      2:{ eapply All_forallb. solve_all. }
      eapply All_local_env_on_free_vars_ctx in X3; tea.
      eapply All_local_env_impl; tea. cbn. intros.
      apply lift_wf_term_f_impl with (r := j_rel j) (u := j_univ j) (1 := X); intros t (Ht & ont).
      rewrite shiftnP_add in ont. len in Ht. now rewrite trans_local_app in Ht.
    * rewrite -(trans_local_case_context Γ0 p) //. solve_all. cbn; eauto.
      rewrite trans_local_app in H2. eapply H2. len. now rewrite shiftnP_add in H4.
  - rtoProp; intuition auto. eapply nf_lam; eauto.
    rewrite shiftnP_add in H4. eauto.
  - rewrite trans_mkApps /=.
    eapply nf_cofix. inv_on_free_vars.
    erewrite <- (trans_fix_context _ _ idx); tea; eauto.
    2:{ cbn. solve_all. }
    solve_all.
    rewrite trans_local_app in H1; eauto. eapply H1.
    inv_on_free_vars. rewrite shiftnP_add in b0. now len. eapply H3.
    now inv_on_free_vars.
    inv_on_free_vars. solve_all.
  - inv_on_free_vars. rewrite shiftnP_add in b.
    eapply nf_tProd; eauto.
Qed.

Lemma trans_axiom_free Σ : axiom_free Σ -> axiom_free (trans_global_env Σ).
Proof.
  intros ax kn decl.
  rewrite /trans_global_env /= /PCUICAst.declared_constant /= /trans_global_decls.
  intros h; apply PCUICElimination.In_map in h as [[kn' decl']  [hin heq]].
  noconf heq. destruct decl'; noconf H.
  apply ax in hin.
  destruct c as [? [] ? ?] => //.
Qed.

Lemma expand_lets_preserves_fo {cf : checker_flags} (Σ : global_env_ext) Γ v :
  wf Σ ->
  firstorder_value Σ Γ v ->
  firstorder_value (cf := cf' cf) (trans_global Σ) (trans_local Γ) (trans v).
Proof.
  intros wfΣ; move: v; apply: firstorder_value_inds.
  intros i n ui u args pandi hty hargs ihargs isp.
  rewrite trans_mkApps. econstructor.
  apply expand_lets_sound in hty.
  rewrite !trans_mkApps in hty. cbn in hty. exact hty.
  solve_all.
  move/negbTE: isp.
  rewrite /PCUICFirstorder.isPropositional.
  rewrite /lookup_inductive /lookup_inductive_gen /lookup_minductive_gen trans_lookup.
  destruct lookup_env => //. destruct g => //. cbn. rewrite nth_error_mapi.
  destruct nth_error => //=.
  rewrite /PCUICFirstorder.isPropositionalArity.
  rewrite (trans_destArity []). destruct destArity => //.
  destruct p => //. now intros ->.
Qed.

Lemma expand_firstorder_type (Σ : global_declarations) n k t :
  (forall nm, plookup_env (firstorder_env' Σ) nm = Some true ->
    plookup_env (firstorder_env' (trans_global_decls Σ)) nm = Some true) ->
  @PCUICFirstorder.firstorder_type (firstorder_env' Σ) n k t ->
  @PCUICFirstorder.firstorder_type (firstorder_env' (trans_global_decls Σ)) n k (trans t).
Proof.
  rewrite /PCUICFirstorder.firstorder_type /PCUICFirstorder.firstorder_env.
  pose proof (trans_decompose_app t).
  destruct decompose_app. rewrite {}H. cbn.
  case: t0 => //=.
  - intros n' hn. destruct l => //.
  - case => /= kn _ _ hd. destruct l => //.
    destruct plookup_env eqn:hp => //.
    destruct b => //.
    eapply hd in hp. rewrite hp //.
Qed.

Lemma trans_firstorder_mutind (Σ : global_declarations) m :
  (forall nm, plookup_env (firstorder_env' Σ) nm = Some true ->
    plookup_env (firstorder_env' (trans_global_decls Σ)) nm = Some true) ->
  @firstorder_mutind (firstorder_env' Σ) m ->
  @firstorder_mutind (firstorder_env' (trans_global_decls Σ)) (trans_minductive_body m).
Proof.
  intros he.
  rewrite /firstorder_mutind. f_equal.
  rewrite /trans_minductive_body /=.
  rewrite -{1}[ind_bodies m]map_id. rewrite -mapi_cst_map.
  move/andP => [] -> /=.
  eapply forallb_mapi_impl.
  intros n x hnth.
  rewrite /firstorder_oneind. destruct x; cbn.
  move/andP => [] hc ->; rewrite andb_true_r.
  rewrite forallb_map. solve_all.
  move: H; rewrite /firstorder_con /=.
  rewrite !rev_app_distr !alli_app.
  move/andP => [hp ha]. apply/andP; split.
  - len. rewrite /trans_local -map_rev alli_map.
    eapply alli_impl; tea. intros i []. cbn.
    now eapply expand_firstorder_type.
  - len. len in ha. clear -ha he.
    move: ha; generalize (cstr_args x) as args.
    induction args => ha; cbn => //.
    destruct a as [na [] ?] => /=. eapply IHargs. cbn in ha.
    rewrite alli_app in ha. move/andP: ha => [] //.
    cbn. rewrite PCUICSigmaCalculus.smash_context_acc /=.
    cbn in ha. rewrite alli_app in ha. move/andP: ha => [] // hc hd.
    rewrite alli_app. apply/andP. split. apply IHargs => //.
    len. cbn. rewrite andb_true_r. cbn in hd. rewrite andb_true_r in hd. len in hd.
    clear -he hd. move: hd. rewrite /firstorder_type.
    destruct (decompose_app decl_type) eqn:e. cbn.
    destruct t => //; apply decompose_app_inv in e; rewrite e.
    destruct l => //.
    { move/andP => [] /Nat.leb_le hn /Nat.ltb_lt hn'.
      rewrite trans_mkApps PCUICLiftSubst.lift_mkApps PCUICLiftSubst.subst_mkApps
        decompose_app_mkApps //=.
      { destruct nth_error eqn:hnth.
        pose proof (nth_error_Some_length hnth).
        move: hnth H.
        destruct (Nat.leb_spec #|args| n). len. lia. len. lia. now cbn. }
      destruct nth_error eqn:hnth.
      move/nth_error_Some_length: hnth. len. destruct (Nat.leb_spec #|args| n). lia. lia. len.
      destruct (Nat.leb_spec #|args| n). apply/andP. split.
      eapply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
      apply/andP; split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
    { rewrite trans_mkApps PCUICLiftSubst.lift_mkApps PCUICLiftSubst.subst_mkApps
        decompose_app_mkApps //=.
        destruct ind, l => //=. destruct plookup_env eqn:hp => //.
        destruct b => //. apply he in hp. rewrite hp //. }
Qed.

Lemma trans_firstorder_env (Σ : global_declarations) :
  (forall nm, plookup_env (firstorder_env' Σ) nm = Some true ->
    plookup_env (firstorder_env' (trans_global_decls Σ)) nm = Some true).
Proof.
  induction Σ; cbn => //.
  destruct a. destruct g => //=.
  intros nm.
  destruct eqb => //. now apply IHΣ.
  intros nm. destruct eqb => //.
  intros [=]. f_equal.
  now eapply trans_firstorder_mutind. apply IHΣ.
Qed.

Lemma trans_firstorder_ind (Σ : global_env_ext_map) i :
  firstorder_ind Σ (firstorder_env Σ) i ->
  firstorder_ind (build_global_env_map (trans_global_env Σ.1), Σ.2) (firstorder_env' (trans_global_decls (declarations Σ.1))) i.
Proof.
  cbn. rewrite /firstorder_ind /= trans_lookup.
  destruct lookup_env => //. destruct g => //=.
  eapply trans_firstorder_mutind, trans_firstorder_env.
Qed.
