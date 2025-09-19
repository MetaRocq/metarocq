(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool Utf8 CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICCasesContexts PCUICTactics
     PCUICWeakeningConv PCUICWeakeningTyp PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICClosedTyp PCUICGeneration PCUICConversion (* Needs transitivity of cumulativity *)
     PCUICValidity PCUICArities PCUICInversion PCUICInductiveInversion
     PCUICCases PCUICWellScopedCumulativity PCUICSpine PCUICSR
     PCUICSafeLemmata PCUICInductives PCUICInductiveInversion.
Set Warnings "-notation-overridden".

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import Ast TypingWf UnivSubst
     TermEquality LiftSubst Reduction.
Set Warnings "notation-overridden".

From MetaRocq.PCUIC Require Import PCUICEquality.
From MetaRocq.TemplatePCUIC Require Import PCUICToTemplate.

Import MRMonadNotation.

Implicit Types cf : checker_flags. (* Use {cf} to parameterize by checker_flags where needed *)
Set Default Proof Using "Type*".

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(** Translation from PCUIC back to template-rocq terms.

  This translation is not direct due to two peculiarities of template-rocq's syntax:
  - applications are n-ary and not all terms are well-formed, so we have to
    use an induction on the size of derivations to transform the binary applications
    into n-ary ones.
  - The representation of cases in template-rocq is "compact" in the sense that
    the predicate and branches contexts do not appear in the syntax of terms but can
    be canonically rebuilt on-demand, as long as the environment has a declaration for the
    inductive type. In contrast, PCUIC has these contexts explicitely present in terms,
    so that the theory of reduction (confluence) and conversion do not need to rely on any
    such well-formedness arguments about the global environment, considerably simplifying the theory:
    For example one couldn't do recursive calls on such "rebuilt" contexts using simple structural
    recursion, the new contexts having no structural relation to the terms at hand.

    This means that.Common-Rocq's `red1` reduction of cases requires well-formedness conditions
    not readily available in PCUIC's. We solve this conundrum using subject reduction: indeed
    cumulativity is always called starting with two well-sorted types, and we can hence show
    that every one-step reduction in a PCUIC cumulativity derivation goes from a well-typed term
    to a well-typed term. We can hence prove that.Common-Rocq's `red1` reductions follow from the
    untyped PCUIC reduction when restricted to well-typed terms (which have many more invariants).
    We actually just need the term to be reduced to be well-typed to show that the interpretation
    preserves one-step reduction in [trans_red1}].
*)

(** Source = PCUIC, Target = Rocq *)
Module S := PCUICAst.
Module SE := PCUICEnvironment.
Module ST := PCUICTyping.
Module T := Template.Ast.
Module TT := Template.Typing.

Module SL := PCUICLiftSubst.
Module TL := Template.LiftSubst.


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

Lemma trans_lift (t : S.term) n k:
  trans (S.lift n k t) = T.lift n k (trans t).
Proof.
  revert k. induction t using PCUICInduction.term_forall_list_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite IHt1 IHt2.
    rewrite AstUtils.mkAppMkApps.
    rewrite <- mapOne.
    rewrite <- TL.lift_mkApps.
    f_equal.
  - f_equal; auto. destruct X as [? [? ?]].
    rewrite /T.map_predicate /id /PCUICAst.map_predicate /= /trans_predicate /=; f_equal;
      autorewrite with map; solve_all.
    rewrite forget_types_map_context e. now rewrite forget_types_length.
    red in X0; solve_all.
    autorewrite with map. solve_all.
    rewrite /trans_branch /T.map_branch; cbn; f_equal.
    autorewrite with map; solve_all.
    rewrite b. now rewrite forget_types_length map_context_length.
  - f_equal; auto; red in X; solve_list.
  - f_equal; auto; red in X; solve_list.
  - destruct p as [? []]; cbn in X; cbn; f_equal; intuition eauto; solve_all.
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

Lemma trans_in_level_set l Σ:
  LevelSet.In l (S.global_ext_levels Σ) ->
  LevelSet.In l (T.global_ext_levels (trans_global Σ)).
Proof. auto. Qed.

Lemma trans_lookup Σ cst :
  Ast.Env.lookup_env (trans_global_env Σ) cst = option_map trans_global_decl (SE.lookup_env Σ cst).
Proof.
  cbn in *.
  destruct Σ as [univs Σ].
  induction Σ.
  - reflexivity.
  - cbn. case: eqb_spec => intros; subst.
    + destruct a; auto.
    + now rewrite IHΣ.
Qed.

Lemma trans_declared_constant {cf} Σ {wfΣ : wf Σ} cst decl:
  S.declared_constant Σ cst decl ->
  T.declared_constant (trans_global_env Σ) cst (trans_constant_body decl).
Proof.
  intro H. unshelve eapply declared_constant_to_gen in H; eauto.
  unshelve eapply Typing.TemplateDeclarationTyping.declared_constant_from_gen.
  move:H. unfold T.declared_constant, T.declared_constant_gen.
  rewrite trans_lookup.
  unfold S.declared_constant, S.declared_constant_gen.
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
Proof.
  intros H.
  unfold consistent_instance_ext, S.consistent_instance_ext in *.
  unfold consistent_instance, S.consistent_instance in *.
  destruct decl;trivial.
Qed.

Lemma trans_declared_inductive {cf} Σ {wfΣ : wf Σ} ind mdecl idecl:
  S.declared_inductive Σ ind mdecl idecl ->
  T.declared_inductive (trans_global_env Σ) ind (trans_minductive_body mdecl) (trans_one_ind_body idecl).
Proof.
  intro H. unshelve eapply declared_inductive_to_gen in H; eauto.
  unshelve eapply Typing.TemplateDeclarationTyping.declared_inductive_from_gen.
  move:H. intros [].
  split.
  - unfold T.declared_minductive,T.declared_minductive_gen,
           S.declared_minductive,S.declared_minductive_gen in *.
    now rewrite trans_lookup H.
  - now apply map_nth_error.
Qed.

Lemma trans_declared_constructor {cf} Σ {wfΣ : wf Σ} ind mdecl idecl cdecl :
  S.declared_constructor Σ ind mdecl idecl cdecl ->
  T.declared_constructor (trans_global_env Σ) ind (trans_minductive_body mdecl) (trans_one_ind_body idecl)
    (trans_constructor_body cdecl).
Proof.
  intros [].
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
    rewrite <- AstUtils.mkApps_mkApp.
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

Lemma trans_subst xs k t:
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  induction t in k |- * using PCUICInduction.term_forall_list_ind.
  all: cbn;try congruence.
  - destruct Nat.leb;trivial.
    rewrite nth_error_map.
    destruct nth_error;cbn.
    2: now rewrite length_map.
    rewrite trans_lift.
    reflexivity.
  - f_equal.
    do 2 rewrite map_map.
    apply All_map_eq.
    eapply All_forall in X.
    apply X.
  - rewrite IHt1 IHt2.
    destruct (trans t1);cbn;trivial.
    rewrite AstUtils.mkApp_mkApps.
    do 2 f_equal.
    rewrite map_app.
    cbn.
    reflexivity.
  - f_equal; trivial.
    rewrite /trans_predicate /= /id /T.map_predicate /=.
    destruct X as [? [? ?]].
    f_equal; solve_all.
    * rewrite e. now rewrite map_context_length.
    * red in X0; rewrite /trans_branch; autorewrite with map; solve_all.
      rewrite /T.map_branch /=. f_equal; auto.
      rewrite b. now rewrite forget_types_length map_context_length.
  - f_equal.
    rewrite length_map.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e e0.
    + apply IHX.
  - f_equal.
    rewrite length_map.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e e0.
    + apply IHX.
  - destruct p as [? []]; cbn in X |- *; f_equal; intuition eauto; solve_all.
Qed.

Lemma trans_subst10 u B:
  trans (S.subst1 u 0 B) =
  T.subst10 (trans u) (trans B).
Proof.
  unfold S.subst1.
  rewrite trans_subst.
  reflexivity.
Qed.

Lemma trans_subst_instance u t:
  trans (subst_instance u t) =
  subst_instance u (trans t).
Proof.
  induction t using PCUICInduction.term_forall_list_ind;cbn;auto;try congruence.
  - do 2 rewrite map_map.
    f_equal.
    apply All_map_eq.
    apply X.
  - rewrite IHt1 IHt2.
    do 2 rewrite AstUtils.mkAppMkApps.
    rewrite subst_instance_mkApps.
    cbn.
    reflexivity.
  - red in X, X0.
    f_equal; solve_all.
    + rewrite /trans_predicate /= /id /T.map_predicate /=.
      f_equal; solve_all.
    + rewrite /trans_branch; solve_all.
      rewrite /T.map_branch /=. f_equal; auto.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e e0.
    + apply IHX.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e e0.
    + apply IHX.
  - destruct p as [? []]; cbn in X |- *; f_equal; intuition eauto; solve_all.
Qed.

Lemma trans_subst_instance_ctx Γ u :
  trans_local Γ@[u] = (trans_local Γ)@[u].
Proof.
  rewrite /subst_instance /= /trans_local /SE.subst_instance_context /T.Env.subst_instance_context
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

Lemma trans_ind_type idecl:
  trans (SE.ind_type idecl) =
  ind_type (trans_one_ind_body idecl).
Proof.
  reflexivity.
Qed.

Lemma trans_type_of_constructor mdecl cdecl ind i u:
  trans (ST.type_of_constructor mdecl cdecl (ind, i) u) =
  TT.type_of_constructor
    (trans_minductive_body mdecl)
    (trans_constructor_body cdecl)
    (ind,i)
    u.
Proof.
  unfold ST.type_of_constructor.
  rewrite trans_subst.
  unfold TT.type_of_constructor.
  f_equal.
  - cbn [fst].
    rewrite PCUICCases.inds_spec.
    rewrite inds_spec.
    rewrite map_rev.
    rewrite map_mapi.
    destruct mdecl.
    cbn.
    f_equal.
    remember 0 as k.
    induction ind_bodies0 in k |- *.
    + reflexivity.
    + cbn.
      f_equal.
      apply IHind_bodies0.
  - rewrite trans_subst_instance.
    f_equal.
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

Lemma trans_declared_projection {cf} Σ {wfΣ : wf Σ.1} p mdecl idecl cdecl pdecl :
  S.declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  T.declared_projection (trans_global Σ).1 p (trans_minductive_body mdecl) (trans_one_ind_body idecl)
    (trans_constructor_body cdecl) (trans_projection_body pdecl).
Proof.
  intros []. split; [|split].
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
  Ast.destArity [] (trans x) =
  option_map (fun '(xs,u) => (map trans_decl xs,u)) (PCUICAst.destArity [] x).
Proof.
  remember (@nil SE.context_decl) as xs.
  replace (@nil context_decl) with (map trans_decl xs) by (now subst).
  clear Heqxs.
  induction x in xs |- *;cbn;trivial;unfold snoc.
  - rewrite <- IHx2.
    reflexivity.
  - rewrite <- IHx3.
    reflexivity.
  - destruct (trans x1);cbn;trivial.
  - destruct prim as [? []]; eauto.
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
  generalize (trans t1) (trans t2); clear.
  induction t; intros; cbnr.
  destruct prim as [? []]; cbnr.
Qed.

Lemma trans_unfold_fix mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  TT.unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TT.unfold_fix, unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros [= <- <-]. simpl.
  repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef. simpl.
  unfold fix_subst, TT.fix_subst. rewrite length_map.
  generalize mfix at 1 3.
  induction mfix; trivial.
  simpl; intros mfix'. f_equal.
  eapply IHmfix.
Qed.

Lemma trans_unfold_cofix mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  TT.unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TT.unfold_cofix, unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef.
  unfold cofix_subst, TT.cofix_subst. rewrite length_map.
  generalize mfix at 1 3.
  induction mfix; trivial.
  simpl; intros mfix'. f_equal.
  eapply IHmfix.
Qed.

Lemma trans_is_constructor:
  forall (args : list S.term) (narg : nat),
    is_constructor narg args = true -> TT.is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold TT.is_constructor, is_constructor.
  rewrite nth_error_map //. destruct nth_error => //. simpl. intros.
  unfold AstUtils.isConstruct_app, isConstruct_app, decompose_app in *.
  destruct (decompose_app_rec t []) eqn:da. simpl in H.
  destruct t0 => //.
  apply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps /=.
  rewrite AstUtils.decompose_app_mkApps //.
Qed.

Lemma refine_red1_r Σ Γ t u u' : u = u' -> TT.red1 Σ Γ t u -> TT.red1 Σ Γ t u'.
Proof.
  intros ->. trivial.
Qed.

Lemma refine_red1_Γ Σ Γ Γ' t u : Γ = Γ' -> TT.red1 Σ Γ t u -> TT.red1 Σ Γ' t u.
Proof.
  intros ->. trivial.
Qed.
Ltac wf_inv H := try apply WfAst.wf_inv in H; simpl in H; rdest.

Lemma trans_fix_context mfix:
  map trans_decl (SE.fix_context mfix) =
  TT.fix_context (map (map_def trans trans) mfix).
Proof.
  unfold trans_local.
  destruct mfix;trivial.
  unfold TT.fix_context, SE.fix_context.
  rewrite map_rev map_mapi.
  cbn. f_equal.
  2: {
    destruct d. cbn.
    rewrite lift0_p.
    rewrite SL.lift0_p.
    unfold vass.
    reflexivity.
  }
  f_equal.
  unfold vass.
  remember 1 as k.
  induction mfix in k |- *;trivial.
  cbn;f_equal; rewrite /map_decl.
  - cbn. now rewrite trans_lift.
  - apply IHmfix.
Qed.

Lemma trans_subst_context s k Γ :
  trans_local (SE.subst_context s k Γ) = T.Env.subst_context (map trans s) k (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto.
  - rewrite SE.subst_context_snoc /=. rewrite [T.Env.subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst length_map.
  - rewrite SE.subst_context_snoc /=. rewrite [T.Env.subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst length_map.
Qed.

Lemma trans_lift_context n k Γ :
  trans_local (SE.lift_context n k Γ) = T.Env.lift_context n k (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto.
  - rewrite PCUICLiftSubst.lift_context_snoc /= lift_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_lift length_map.
  - rewrite PCUICLiftSubst.lift_context_snoc /= lift_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_lift length_map.
Qed.

Lemma trans_smash_context Γ Δ : trans_local (SE.smash_context Γ Δ) = T.Env.smash_context (trans_local Γ) (trans_local Δ).
Proof.
  induction Δ in Γ |- *; simpl; auto.
  destruct a as [na [b|] ty] => /=.
  rewrite IHΔ. f_equal.
  now rewrite (trans_subst_context [_]).
  rewrite IHΔ. f_equal. rewrite trans_local_app //.
Qed.

Lemma context_assumptions_map ctx : Ast.Env.context_assumptions (map trans_decl ctx) = SE.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; lia.
Qed.

Lemma trans_extended_subst Γ n : map trans (SE.extended_subst Γ n) = extended_subst (trans_local Γ) n.
Proof.
  induction Γ in n |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto.
  rewrite trans_subst trans_lift IHΓ. f_equal. f_equal. len.
  now rewrite context_assumptions_map length_map.
  f_equal; auto.
Qed.

Lemma trans_expand_lets_k Γ k T : trans (SE.expand_lets_k Γ k T) = T.Env.expand_lets_k (trans_local Γ) k (trans T).
Proof.
  rewrite /SE.expand_lets_k.
  rewrite trans_subst trans_lift trans_extended_subst.
  rewrite /T.Env.expand_lets /T.Env.expand_lets_k.
  now rewrite (context_assumptions_map Γ) length_map.
Qed.

Lemma trans_expand_lets Γ T : trans (SE.expand_lets Γ T) = T.Env.expand_lets (trans_local Γ) (trans T).
Proof.
  now rewrite /SE.expand_lets /SE.expand_lets_k trans_expand_lets_k.
Qed.

Lemma alpha_eq_trans {Γ Δ} :
  eq_context_upto_names Γ Δ ->
  TermEquality.eq_context_upto_names (trans_local Γ) (trans_local Δ).
Proof.
  intros.
  eapply All2_map, All2_impl; tea.
  intros x y []; constructor; subst; auto.
Qed.

Definition wt {cf} Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma isType_wt {cf} Σ Γ T : isType Σ Γ T -> wt Σ Γ T.
Proof.
  intros (_ & s & hs & _); now exists (PCUICAst.tSort s).
Qed.
Coercion isType_wt : isType >-> wt.

Section wtsub.
  Context {cf} {Σ : PCUICEnvironment.global_env_ext} {wfΣ : PCUICTyping.wf Σ}.
  Set Warnings "-notation-overridden".
  Import PCUICAst.
  Set Warnings "notation-overridden".

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
         ci.(ci_npar) = mdecl.(ind_npars),
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
    | tPrim p => tPrimProp (wt Γ) p
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
          rewrite subst_instance_expand_lets_ctx PCUICUnivSubstitutionConv.subst_instance_subst_context.
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
    - eapply inversion_Prim in h as (?&?&[]); eauto.
      destruct prim as [? []]; cbn in *; eauto; try exact tt.
      depelim p0. repeat split. now eexists. now eexists. solve_all. now eexists.
  Qed.
End wtsub.

Ltac outtimes :=
  match goal with
  | ih : _ × _ |- _ =>
    destruct ih as [? ?]
  end.

Lemma red1_cumul {cf} (Σ : global_env_ext) pb Γ T U : TT.red1 Σ Γ T U -> TT.cumul_gen Σ Γ pb T U.
Proof.
  intros r.
  econstructor 2; tea. constructor.
  destruct pb.
  - apply TermEquality.eq_term_refl.
  - apply TermEquality.leq_term_refl.
Qed.

Lemma red1_cumul_inv {cf} (Σ : global_env_ext) pb Γ T U : TT.red1 Σ Γ T U -> TT.cumul_gen Σ Γ pb U T.
Proof.
  intros r.
  econstructor 3; tea. constructor.
  destruct pb.
  - eapply TermEquality.eq_term_refl.
  - eapply TermEquality.leq_term_refl.
Qed.

Definition TTconv {cf} (Σ : global_env_ext) Γ : relation term :=
  clos_refl_sym_trans (relation_disjunction (TT.red1 Σ Γ) (TermEquality.eq_term Σ (T.global_ext_constraints Σ))).

Lemma red1_conv {cf} (Σ : global_env_ext) Γ T U : TT.red1 Σ Γ T U -> TTconv Σ Γ T U.
Proof.
  intros r.
  now repeat constructor.
Qed.

Lemma trans_expand_lets_ctx Γ Δ :
  trans_local (SE.expand_lets_ctx Γ Δ) = expand_lets_ctx (trans_local Γ) (trans_local Δ).
Proof.
  rewrite /SE.expand_lets_ctx /SE.expand_lets_k_ctx /expand_lets_ctx /expand_lets_k_ctx.
  now rewrite !trans_subst_context trans_extended_subst trans_lift_context
    context_assumptions_map length_map.
Qed.

Lemma trans_inds ind u mdecl :
  map trans (PCUICAst.inds (inductive_mind ind) u (SE.ind_bodies mdecl)) =
  inds (inductive_mind ind) u (ind_bodies (trans_minductive_body mdecl)).
Proof.
  rewrite PCUICCases.inds_spec inds_spec.
  rewrite map_rev map_mapi. simpl.
  f_equal. rewrite mapi_map. apply mapi_ext => n //.
Qed.

Lemma trans_cstr_branch_context ci mdecl cdecl :
  trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl) =
  cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body cdecl).
Proof.
  rewrite /PCUICCases.cstr_branch_context /cstr_branch_context.
  rewrite trans_expand_lets_ctx trans_subst_context trans_inds.
  repeat f_equal. now cbn; rewrite length_map.
Qed.

Lemma trans_cstr_branch_context_inst ci mdecl cdecl i :
  trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl)@[i] =
  (cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body cdecl))@[i].
Proof.
  now rewrite trans_subst_instance_ctx trans_cstr_branch_context.
Qed.

Lemma map2_set_binder_name_alpha (nas : list aname) (Δ Δ' : context) :
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas Δ ->
  TermEquality.eq_context_upto_names Δ Δ' ->
  TermEquality.eq_context_upto_names (map2 set_binder_name nas Δ) Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  constructor; auto. destruct r; subst; cbn; constructor; auto;
  now transitivity na.
Qed.

Notation eq_names := (All2 (fun x y => x = (decl_name y))).

Lemma eq_names_subst_context nas Γ s k :
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance nas Γ u :
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

Lemma map2_set_binder_name_alpha_eq (nas : list aname) (Δ Δ' : context) :
  All2 (fun x y => x = (decl_name y)) nas Δ' ->
  TermEquality.eq_context_upto_names Δ Δ' ->
  (map2 set_binder_name nas Δ) = Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  f_equal; auto. destruct r; subst; cbn; auto.
Qed.

Lemma trans_inst_case_branch_context p br ci mdecl cdecl :
  let p' := PCUICAst.map_predicate id trans trans (map_context trans) p in
  wf_branch cdecl br ->
  eq_context_upto_names br.(PCUICAst.bcontext) (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  (case_branch_context ci
    (trans_minductive_body mdecl) (trans_constructor_body cdecl) (trans_predicate p')
    (trans_branch (PCUICAst.map_branch trans (map_context trans) br))) =
    (trans_local (inst_case_branch_context p br)).
Proof.
  intros p' wfbr.
  rewrite /inst_case_branch_context.
  rewrite /inst_case_context.
  rewrite /case_branch_context /case_branch_context_gen.
  rewrite trans_subst_context.
  intros eq.
  rewrite map_rev.
  eapply map2_set_binder_name_alpha_eq.
  { apply eq_names_subst_context.
    do 2 eapply All2_map_right.
    cbn. do 2 eapply All2_map_left.
    eapply All2_refl. intros. reflexivity. }
  eapply alpha_eq_subst_context.
  eapply alpha_eq_subst_instance in eq.
  symmetry in eq.
  eapply alpha_eq_trans in eq.
  now rewrite trans_cstr_branch_context_inst in eq.
Qed.

Lemma context_assumptions_map2_set_binder_name nas Γ :
  #|nas| = #|Γ| ->
  context_assumptions (map2 set_binder_name nas Γ) = context_assumptions Γ.
Proof.
  induction Γ in nas |- *; destruct nas; simpl; auto; try discriminate.
  intros [=]. destruct (decl_body a); auto.
  f_equal; auto.
Qed.

Lemma case_branch_context_assumptions ind mdecl cdecl p br :
  Forall2 (fun na decl => eq_binder_annot na decl.(decl_name)) br.(bcontext) (cstr_args cdecl) ->
  context_assumptions (case_branch_context ind mdecl cdecl p br) = context_assumptions (cstr_args cdecl).
Proof.
  rewrite /case_branch_context /case_branch_context_gen.
  intros Hforall.
  rewrite context_assumptions_map2_set_binder_name. len.
  rewrite !lengths.
  eapply (Forall2_length Hforall).
  now do 3 rewrite !context_assumptions_subst_context ?context_assumptions_lift_context ?context_assumptions_subst_instance
    /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
Qed.

Lemma cstr_branch_context_assumptions ci mdecl cdecl :
  SE.context_assumptions (PCUICCases.cstr_branch_context ci mdecl cdecl) =
  SE.context_assumptions (SE.cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context /PCUICEnvironment.expand_lets_ctx
    /PCUICEnvironment.expand_lets_k_ctx.
  now do 2 rewrite !SE.context_assumptions_subst_context ?SE.context_assumptions_lift_context.
Qed.

#[global]
Instance compare_decls_refl : Reflexive (TermEquality.eq_decl_upto_names).
Proof.
  intros [na [b|] ty]; constructor; auto.
Qed.

#[global]
Instance All2_compare_decls_refl : Reflexive (TermEquality.eq_context_upto_names).
Proof.
  intros x; apply All2_refl; reflexivity.
Qed.

#[global]
Instance All2_compare_decls_sym : Symmetric (TermEquality.eq_context_upto_names).
Proof.
  intros x y. eapply All2_symP. clear.
  intros d d' []; subst; constructor; auto; now symmetry.
Qed.

#[global]
Instance All2_compare_decls_trans : Transitive (TermEquality.eq_context_upto_names).
Proof.
  intros x y z. eapply All2_trans. clear.
  intros d d' d'' [] H; depelim H; subst; constructor; auto; now etransitivity.
Qed.

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

Lemma trans_ind_predicate_context  ci mdecl idecl :
  trans_local (PCUICCases.ind_predicate_context ci mdecl idecl) =
  (Ast.ind_predicate_context ci (trans_minductive_body mdecl)
      (trans_one_ind_body idecl)).
Proof.
  rewrite /ind_predicate_context /Ast.ind_predicate_context /=.
  rewrite /trans_decl /=. f_equal.
  f_equal. rewrite trans_mkApps /=. f_equal.
  rewrite trans_to_extended_list trans_local_app /Env.to_extended_list.
  f_equal. f_equal.
  now rewrite trans_smash_context.
  now rewrite trans_expand_lets_ctx.
  now rewrite trans_expand_lets_ctx.
Qed.


Lemma trans_ind_predicate_context_eq p ci mdecl idecl :
  eq_context_upto_names (PCUICAst.pcontext p)
    (PCUICCases.ind_predicate_context ci mdecl idecl) ->
  All2
    (λ (x : binder_annot name) (y : Env.context_decl),
       eq_binder_annot x (decl_name y))
    (map decl_name (trans_local (PCUICAst.pcontext p)))
    (Ast.ind_predicate_context ci (trans_minductive_body mdecl)
       (trans_one_ind_body idecl)).
Proof.
  rewrite -trans_ind_predicate_context.
  intros. eapply All2_map, All2_map_left.
  solve_all.
  destruct X; cbn; subst; auto.
Qed.

Lemma trans_cstr_branch_context_eq ci mdecl cdecl br :
  eq_context_upto_names (PCUICAst.bcontext br)
    (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  All2
    (λ (x : binder_annot name) (y : Env.context_decl),
     eq_binder_annot x (decl_name y))
    (Ast.bcontext (trans_branch (PCUICAst.map_branch trans (map_context trans) br)))
    (Ast.cstr_branch_context ci (trans_minductive_body mdecl)
      (trans_constructor_body cdecl)).
Proof.
  intros.
  rewrite -trans_cstr_branch_context.
  eapply All2_map, All2_map_left. solve_all.
  destruct X; subst; auto.
Qed.

Lemma trans_wf {cf} {Σ : PCUICEnvironment.global_env_ext} {wfΣ : wf Σ} {Γ t} : wt Σ Γ t -> WfAst.wf (trans_global Σ) (trans t).
Proof.
  intros H. induction t in Γ, H |- * using term_forall_list_ind; simpl; eapply wt_inv in H; cbn in H; eauto; try constructor; auto.
  all:try constructor; intuition eauto.
  - destruct H. eauto.
  - destruct H; eauto.
  - destruct H; eauto.
  - now eapply WfAst.wf_mkApp.
  - cbn. destruct b as [mdecl [idecl []]].
    destruct X as [? []]. red in X0. econstructor; cbn; eauto; tea.
    eapply trans_declared_inductive in d; tea. now cbn. cbn.
    eapply trans_ind_predicate_context_eq => //. now symmetry.
    rewrite length_map. cbn. rewrite context_assumptions_map //.
    destruct w. now rewrite -(declared_minductive_ind_npars (proj1 d)).
    cbn. solve_all. eapply All2_map, All2_map_right. solve_all.
    eapply All2i_All2; tea. cbv beta.
    intros cdecl br [] []. destruct a2.
    split; eauto.
    eapply trans_cstr_branch_context_eq => //.
    cbn; eauto. cbn in p0. destruct p0. eauto.
  - cbn. red in X. solve_all.
  - cbn. red in X. solve_all.
  - destruct p as [? []]; cbn in X, H |- *; constructor; solve_all; eauto.
Qed.

#[global] Hint Resolve trans_wf : wf.

Lemma red1_alpha_eq Σ Γ Δ T U :
  TT.red1 Σ Γ T U ->
  TermEquality.eq_context_upto_names Γ Δ ->
  TT.red1 Σ Δ T U.
Proof.
  intros r; revert Δ.
  induction r using TT.red1_ind_all; intros; try solve [econstructor; eauto].
  - constructor. destruct (nth_error Γ i) eqn:heq; noconf H.
    cbn in *. destruct c as [na [b|] ty]; noconf H.
    eapply All2_nth_error_Some in X as [t' [-> h]]; tea.
    now depelim h; subst.
  - constructor; eapply IHr. constructor; auto; reflexivity.
  - constructor; eapply IHr; constructor; auto; reflexivity.
  - constructor; solve_all.
  - econstructor; tea. eapply IHr. eapply All2_app; eauto; reflexivity.
  - econstructor; tea. solve_all. eapply b0. eapply All2_app; auto; reflexivity.
  - constructor. solve_all.
  - constructor. eapply IHr. constructor; auto. reflexivity.
  - constructor. solve_all.
  - constructor. solve_all.
  - eapply Typing.fix_red_body. solve_all.
    eapply b0. eapply All2_app => //. reflexivity.
  - constructor; solve_all.
  - eapply Typing.cofix_red_body; solve_all.
    eapply b0, All2_app => //. reflexivity.
  - eapply Typing.array_red_val. solve_all.
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
#[global]
Instance map2_Proper {A B C} : Morphisms.Proper (pointwise_relation A (pointwise_relation B (@eq C)) ==> eq ==> eq ==> eq) map2.
Proof.
  intros f g Hfg ? ? -> ? ? ->.
  eapply map2_ext, Hfg.
Qed.

Lemma map2_set_binder_name_eq nas Δ Δ' :
  TermEquality.eq_context_upto_names Δ Δ' ->
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
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  f_equal. destruct r; subst; f_equal.
  apply IHX.
Qed.

Lemma map2_trans l l' :
  map2
  (λ (x : aname) (y : PCUICEnvironment.context_decl),
      trans_decl (PCUICEnvironment.set_binder_name x y)) l l' =
  map2 (fun (x : aname) (y : PCUICEnvironment.context_decl) =>
    Ast.Env.set_binder_name x (trans_decl y)) l l'.
Proof.
  eapply map2_ext.
  intros x y. rewrite /trans_decl. now destruct y; cbn.
Qed.

Lemma trans_case_predicate_context {cf} {Σ : PCUICEnvironment.global_env_ext}
  {wfΣ : PCUICTyping.wf Σ} Γ ci mdecl idecl p :
  S.declared_inductive Σ ci mdecl idecl ->
  S.consistent_instance_ext Σ (PCUICEnvironment.ind_universes mdecl) (PCUICAst.puinst p) →
  let parctx := (PCUICEnvironment.ind_params mdecl)@[PCUICAst.puinst p] in
  PCUICSpine.spine_subst Σ Γ (PCUICAst.pparams p)
      (List.rev (PCUICAst.pparams p))
      (PCUICEnvironment.smash_context [] parctx) ->
  wf_predicate mdecl idecl p ->
  let p' := trans_predicate (PCUICAst.map_predicate id trans trans trans_local p) in
  (case_predicate_context ci (trans_minductive_body mdecl) (trans_one_ind_body idecl) p') =
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
  rewrite [map _ _]trans_subst_context map_rev. f_equal.
  rewrite trans_subst_instance_ctx.
  now rewrite trans_ind_predicate_context.
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

Lemma trans_bcontext br :
  (bcontext (trans_branch (PCUICAst.map_branch trans (map_context trans) br))) = forget_types (PCUICAst.bcontext br).
Proof.
  cbn. now rewrite map_context_trans map_map_compose.
Qed.

Lemma OnOne2All_map2_map_all {A B I I'} {P} {i : list I} {l l' : list A} (g : B -> I -> I') (f : A -> B) :
  OnOne2All (fun i x y => P (g (f x) i) (f x) (f y)) i l l' -> OnOne2All P (map2 g (map f l) i) (map f l) (map f l').
Proof.
  induction 1; simpl; constructor; try congruence; try assumption. len.
  now rewrite map2_length !length_map.
Qed.

Lemma trans_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) {wfΣ : PCUICTyping.wf Σ} Γ T U :
  red1 Σ Γ T U ->
  wt Σ Γ T ->
  TT.red1 (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1 using red1_ind_all; simpl in *; intros wt;
    match goal with
    | |- context [tCase _ _ _ _] => idtac
    | _ => eapply wt_inv in wt; tea; cbn in wt; repeat outtimes
    end;
    try solve [econstructor; eauto].

  - simpl.
    rewrite trans_subst; auto. constructor.

  - rewrite trans_subst; eauto. repeat constructor.
  - rewrite trans_lift; eauto. repeat constructor.
    rewrite nth_error_map.
    destruct nth_error eqn:Heq => //. simpl in H. noconf H.
    simpl. destruct c; noconf H => //.

  - destruct wt as [s Hs].
    eapply inversion_Case in Hs as [mdecl [idecl [decli [indices [[] ?]]]]].
    epose proof (PCUICValidity.inversion_mkApps scrut_ty) as [? [hc hsp]]; tea.
    eapply inversion_Construct in hc as (mdecl'&idecl'&cdecl&wfΓ&declc&cu&tyc); tea.
    unshelve epose proof (decli_ := declared_inductive_to_gen decli); eauto.
    unshelve epose proof (declc_ := declared_inductive_to_gen declc); eauto.
    destruct (declared_inductive_inj decli_ declc_) as [-> ->]. 2:auto.
    rewrite trans_mkApps /=.
    relativize (trans (iota_red _ _ _ _)).
    eapply TT.red_iota; tea; eauto. all:auto.
    * rewrite !nth_error_map H; reflexivity.
    * eapply trans_declared_constructor; tea.
    * rewrite length_map H0.
      eapply Forall2_All2 in wf_brs.
      eapply All2_nth_error in wf_brs; tea.
      2:eapply declc.
      eapply All2i_nth_error_r in brs_ty; tea.
      destruct brs_ty as [cdecl' [Hcdecl [eq [wf wf']]]].
      rewrite (proj2 declc) in Hcdecl. noconf Hcdecl.
      rewrite case_branch_context_assumptions.
      do 2 red in wf_brs.
      eapply trans_eq_binder_annot in wf_brs.
      rewrite trans_bcontext. eapply wf_brs.
      eapply PCUICCasesContexts.alpha_eq_context_assumptions in eq as ->.
      rewrite cstr_branch_context_assumptions.
      now rewrite context_assumptions_map.
    * rewrite /iota_red trans_subst trans_expand_lets /TT.iota_red map_rev map_skipn.
      eapply All2i_nth_error in brs_ty as []; tea. 2:apply declc.
      erewrite expand_lets_eq => //.
      rewrite trans_inst_case_branch_context => //.
      eapply Forall2_All2 in wf_brs. eapply All2_nth_error in wf_brs; tea.
      eapply declc. reflexivity.

  - simpl. rewrite !trans_mkApps /=.
    unfold is_constructor in H0.
    destruct nth_error eqn:hnth.
    pose proof (nth_error_Some_length hnth).
    destruct args. simpl. exfalso; cbn in H1. lia.
    cbn -[mkApps].
    eapply TT.red_fix.
    apply trans_unfold_fix; eauto.
    eapply (trans_is_constructor (t0 :: args)).
    now rewrite /is_constructor hnth.
    discriminate.

  - rewrite trans_mkApps.
    rewrite !trans_mkApps; eauto with wf.
    apply trans_unfold_cofix in H; eauto with wf.
    eapply TT.red_cofix_case; eauto.

  - rewrite !trans_mkApps.
    apply trans_unfold_cofix in H; eauto with wf.
    eapply TT.red_cofix_proj; eauto.

  - rewrite trans_subst_instance. econstructor.
    apply (trans_declared_constant _ c decl H).
    destruct decl. now simpl in *; subst cst_body0.

  - rewrite trans_mkApps; eauto with wf.
    simpl. constructor; now rewrite nth_error_map H.

  - destruct wt as []; constructor; auto.
  - destruct wt as []; constructor; auto.
  - destruct wt as []; constructor; auto.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply OnOne2_All_mix_left in X; tea.
    constructor.
    eapply OnOne2_map. solve_all.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    econstructor; eauto. now eapply trans_declared_inductive.
    cbn -[case_predicate_context].
    eapply red1_alpha_eq. eapply IHX.
    { destruct w1 as [sr hs]; exists sr.
      eapply PCUICContextConversionTyp.context_conversion; tea.
      eapply PCUICSafeLemmata.wf_inst_case_context; tea.
      destruct w2. pcuic.
      rewrite /inst_case_context.
      apply PCUICContextConversion.eq_context_upto_names_conv_context.
      eapply All2_app. 2:{ reflexivity. }
      apply (PCUICAlpha.inst_case_predicate_context_eq (ind:=ci) w).
      cbn. now symmetry. }
    rewrite [trans_local _]map_app.
    eapply All2_app; [|reflexivity].
    symmetry. etransitivity.
    rewrite (trans_case_predicate_context _ _ _ _ p d c0 s w).
    reflexivity.
    eapply alpha_eq_trans.
    eapply PCUICAlpha.inst_case_predicate_context_eq => //.

  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    econstructor; eauto.

  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    econstructor; eauto.
    eapply trans_declared_inductive; tea.
    rewrite /case_branches_contexts.
    apply OnOne2All_map2_map_all. cbn.
    apply OnOne2All_map_all.
    eapply OnOne2All2i_OnOne2All; tea.
    intros i br br' ctor.
    simpl. intros [[red IHred] eqctx] [wfrel wtbody].
    unfold on_Trel. split => //. 2:cbn; now rewrite eqctx.
    rewrite [map2 set_binder_name _ _](trans_inst_case_branch_context _ _ ci mdecl ctor) => //.
    rewrite -[_ ++ _]trans_local_app.
    eapply IHred.
    destruct w4 as [s' Hs]. exists s'.
    eapply PCUICContextConversionTyp.context_conversion; tea.
    eapply wf_local_alpha; tea. pcuic.
    now eapply PCUICContextConversion.eq_context_upto_names_conv_context.

  - eapply red1_mkApp; auto. eapply trans_wf; tea.
  - eapply (red1_mkApps_r _ _ _ [_] [_]); auto.
    * eapply trans_wf; tea.
    * repeat constructor. eapply trans_wf; tea.
    * constructor; auto.

  - constructor.
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map. solve_all.
    red; intuition auto. destruct x, y; simpl in *. noconf b0.
    reflexivity.

  - eapply TT.fix_red_body.
    eapply OnOne2_All_mix_left in X; tea.
    unfold on_Trel in *.
    eapply OnOne2_map. solve_all. unfold on_Trel. cbn. split => //.
    simpl. rewrite -trans_fix_context.
    now rewrite /trans_local map_app in X.
    destruct x, y; simpl in *. noconf b0.
    reflexivity.

  - constructor.
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map. solve_all.
    red; intuition auto. destruct x, y; simpl in *. noconf b0.
    reflexivity.

  - apply TT.cofix_red_body.
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map; solve_all.
    red. destruct x, y; simpl in *. noconf b0.
    intuition auto.
    rewrite /trans_local map_app in X.
    now rewrite -trans_fix_context.
  - cbn. apply TT.array_red_val.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_map. solve_all.
Qed.

Lemma trans_cmp_global_instance Σ cmp_universe pb gref napp u u' :
  PCUICEquality.cmp_global_instance Σ cmp_universe pb gref napp u u' ->
  TermEquality.cmp_global_instance (trans_global_env Σ) cmp_universe pb gref napp u u'.
Proof.
  unfold PCUICEquality.cmp_global_instance, PCUICEquality.cmp_global_instance_gen, PCUICEquality.global_variance.
  unfold TermEquality.cmp_global_instance, TermEquality.global_variance.
  destruct gref; simpl; auto.
  - unfold S.lookup_inductive, S.lookup_minductive.
    unfold S.lookup_inductive_gen, S.lookup_minductive_gen.
    unfold lookup_inductive, lookup_minductive.
    unfold lookup_inductive_gen, lookup_minductive_gen.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite trans_destr_arity.
    destruct PCUICAst.destArity as [[ctx ps]|] => /= //.
    now rewrite context_assumptions_map.
  - unfold S.lookup_constructor, S.lookup_inductive, S.lookup_minductive.
    unfold S.lookup_constructor_gen, S.lookup_inductive_gen, S.lookup_minductive_gen.
    unfold lookup_constructor, lookup_inductive, lookup_minductive.
    unfold lookup_constructor_gen, lookup_inductive_gen, lookup_minductive_gen.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
Qed.

Lemma trans_eq_context_gen_eq_binder_annot Γ Δ :
  eq_context_upto_names Γ Δ ->
  All2 eq_binder_annot (map decl_name (trans_local Γ)) (map decl_name (trans_local Δ)).
Proof.
  intros; do 2 eapply All2_map. solve_all.
  destruct X; cbn; auto.
Qed.

Lemma trans_eq_term_upto_univ {cf} Σ cmp_universe cmp_sort pb napp t u :
    PCUICEquality.eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t u ->
    TermEquality.eq_term_upto_univ_napp (trans_global_env Σ) cmp_universe cmp_sort pb napp (trans t) (trans u).
Proof.
  intros e.
  induction t using term_forall_list_ind in pb, napp, u, e |- *.
  all: invs e; cbn.
  all: try solve [ constructor ; auto ].
  all: try solve [
    repeat constructor ;
    match goal with
    | ih : forall Rle u (napp : nat), _ |- _ =>
      eapply ih ; auto
    end
  ].
  1,6,7: try solve [ constructor; unfold eq_mfixpoint in *; solve_all ].
  all: try solve [ constructor; now eapply trans_cmp_global_instance ].
  - eapply (TermEquality.eq_term_upto_univ_mkApps _ _ _ _ _ _ [_] _ [_]); simpl; eauto.
  - destruct X1 as [Hpars [Huinst [Hctx Hret]]].
    destruct X as [IHpars [IHctx IHret]].
    unfold eq_branches, eq_branch in *.
    constructor; cbn; auto. solve_all.
    red in X0.
    eapply trans_eq_context_gen_eq_binder_annot in Hctx.
    now rewrite !map_context_trans.
    red in X0. solve_all_one.
    eapply trans_eq_context_gen_eq_binder_annot in a.
    now rewrite !map_context_trans.
  - depelim X0; cbn in X |- *; try econstructor; intuition eauto; solve_all.
    repeat (constructor; tas).
Qed.

Lemma trans_leq_term {cf} Σ ϕ T U :
  PCUICEquality.leq_term Σ ϕ T U ->
  TermEquality.leq_term (trans_global_env Σ) ϕ (trans T) (trans U).
Proof.
  eapply trans_eq_term_upto_univ ; eauto.
Qed.

From MetaRocq.PCUIC Require Import PCUICCumulativity.

Section wtcumul.
  Set Warnings "-notation-overridden".
  Import PCUICAst PCUICTyping PCUICEquality.
  Set Warnings "notation-overridden".
  Record wt_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) (Γ : PCUICEnvironment.context) T U :=
  { wt_red1_red1 : PCUICReduction.red1 Σ Γ T U;
    wt_red1_dom : isType Σ Γ T;
    wt_red1_codom : isType Σ Γ U }.

  Reserved Notation " Σ ;;; Γ |-- t <= u " (at level 50, Γ, t, u at next level).

  Inductive wt_cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | wt_cumul_refl t u : leq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_l t u v : wt_red1 Σ Γ t v -> Σ ;;; Γ |-- v <= u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_r t u v : Σ ;;; Γ |-- t <= v -> wt_red1 Σ Γ u v -> Σ ;;; Γ |-- t <= u
  where " Σ ;;; Γ |-- t <= u " := (wt_cumul Σ Γ t u) : type_scope.

  Lemma cumul_decorate {cf} (Σ : global_env_ext) {wfΣ : wf Σ} Γ T U :
    isType Σ Γ T -> isType Σ Γ U ->
    cumulAlgo Σ Γ T U ->
    wt_cumul Σ Γ T U.
  Proof.
    intros ht hu.
    induction 1.
    - constructor. auto.
    - pose proof (isType_red1 ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHX; tea.
    - pose proof (isType_red1 hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.
End wtcumul.

Lemma trans_cumul {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wt_cumul Σ Γ T U ->
  TT.cumul_gen (trans_global Σ) (trans_local Γ) Cumul (trans T) (trans U).
Proof.
  induction 1.
  - constructor; auto.
    eapply trans_leq_term in c.
    now rewrite -trans_global_ext_constraints.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto. 2:destruct ht as (_ & s & hs & _); now eexists.
    econstructor 2; tea.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto. 2:destruct ht as (_ & s & hs & _); now eexists.
    econstructor 3; tea.
Qed.

Lemma trans_lift_typing_it {P Q} {tm tm' t t'} {u r} :
  forall tu: ST.lift_typing0 P (Judge tm t u r),
  let s := tu.2.π1 in
  match tm', tm with None, _ => unit | Some tm', Some tm => P tm t -> Q tm' t' | _, _ => False end ->
  (P t (PCUICAst.tSort s) -> Q t' (tSort s)) ->
  TT.lift_typing0 Q (Judge tm' t' u r).
Proof.
  intros (? & ? & Hs & e) s HPQc HPQs.
  split.
  - destruct tm, tm' => //=. now apply HPQc.
  - eexists. split; [now apply HPQs|].
    destruct u => //.
Qed.


Definition TTwf_local {cf} Σ Γ := TT.All_local_env (TT.lift_typing TT.typing Σ) Γ.

Lemma trans_wf_local' {cf} :
  forall (Σ : SE.global_env_ext) Γ (wfΓ : wf_local Σ Γ),
    let P :=
        (fun Γ0 _ (t T : PCUICAst.term) _ =>
           TT.typing (trans_global Σ) (trans_local Γ0) (trans t) (trans T))
    in
    ST.All_local_env_over (ST.typing Σ) P Γ wfΓ ->
    TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor; auto.
    simpl. eapply trans_lift_typing_it with tu => //.
  - simpl. constructor; auto.
    simpl. eapply trans_lift_typing_it with tu => //.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun Σ Γ b ty =>
              ST.typing Σ Γ b ty × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
        Γ ->
  TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor; auto.
    simpl. eapply trans_lift_typing_it with t0 => // HT. now apply HT.
  - simpl. constructor; auto.
    simpl. eapply trans_lift_typing_it with t0 => // HT. all: now apply HT.
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

Lemma trans_mfix_All {cf} Σ Γ mfix:
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ : SE.global_env_ext)
          (Γ : SE.context) (b ty : PCUICAst.term) =>
        ST.typing Σ Γ b ty
        × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
    (Γ ,,, (SE.fix_context mfix)) ->
  TTwf_local (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) mfix)).
Proof.
  intros.
  rewrite <- trans_fix_context.
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

Lemma trans_mfix_All2 {cf} Σ Γ mfix xfix:
  All (on_def_body (lift_typing1
      (fun Γ t T => TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)))
    (SE.fix_context xfix) Γ) mfix ->
  All (TT.on_def_body (fun Γ => TT.lift_typing0 (TT.typing (trans_global Σ) Γ))
    (TT.fix_context (map (map_def trans trans) xfix)) (trans_local Γ)) (map (map_def trans trans) mfix).
Proof.
  induction 1.
  - constructor.
  - simpl; constructor; auto.
    eapply trans_lift_typing_it with p => // HT. 2: set (_.2.π1) as s in *; clearbody s.
    all: unfold app_context in *.
    all: rewrite /trans_local map_app trans_fix_context in HT.
    all: rewrite trans_lift in HT.
    all: replace(#|SE.fix_context xfix|) with
        (#|TT.fix_context (map(map_def trans trans) xfix)|) in HT; tas.

    all: now rewrite TT.fix_context_length length_map fix_context_length.
Qed.

Lemma All_over_All {cf} Σ Γ wfΓ :
  ST.All_local_env_over (ST.typing Σ)
    (fun (Γ : SE.context)
      (_ : wf_local Σ Γ) (t T : PCUICAst.term)
      (_ : ST.typing Σ Γ t T) =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)) Γ wfΓ ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ0 : SE.global_env_ext) (Γ0 : SE.context)
          (b ty : PCUICAst.term) =>
        ST.typing Σ0 Γ0 b ty
        × TT.typing (trans_global Σ0) (trans_local Γ0) (trans b) (trans ty)) Σ) Γ.
Proof.
  intros H.
  induction H;cbn.
  all: constructor; eauto.
  all: apply lift_sorting_it_impl with tu => //.
Qed.

Lemma trans_decompose_prod_assum :
  forall Γ t,
    let '(Δ, c) := decompose_prod_assum Γ t in
    AstUtils.decompose_prod_assum (trans_local Γ) (trans t) = (trans_local Δ, trans c).
Proof.
  intros Γ t.
  destruct decompose_prod_assum as [Δ c] eqn:e.
  induction t in Γ, Δ, c, e |- *.
  all: simpl in *.
  all: try solve [ inversion e ; subst ; reflexivity ].
  - eapply IHt2 in e as e'. apply e'.
  - eapply IHt3 in e as e'. assumption.
  - noconf e. simpl.
    now destruct (mkApp_ex (trans t1) (trans t2)) as [f [args ->]].
  - noconf e. now destruct prim as [? []] => /=.
Qed.

Lemma trans_isApp t : PCUICAst.isApp t = false -> Ast.isApp (trans t) = false.
Proof.
  destruct t => //.
  now destruct prim as [? []].
Qed.

Lemma trans_nisApp t : ~~ PCUICAst.isApp t -> ~~ Ast.isApp (trans t).
Proof.
  destruct t => //.
  now destruct prim as [? []].
Qed.

Lemma trans_destInd t : ST.destInd t = TT.destInd (trans t).
Proof.
  destruct t => //. simpl.
  now destruct (mkApp_ex (trans t1) (trans t2)) as [f [u ->]].
  now destruct prim as [? []].
Qed.

Lemma trans_decompose_app t :
  let '(hd, args) := decompose_app t in
  AstUtils.decompose_app (trans t) = (trans hd, map trans args).
Proof.
  destruct (decompose_app t) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  eapply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps.
  apply AstUtils.decompose_app_mkApps.
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

Lemma trans_check_one_fix mfix :
  TT.check_one_fix (map_def trans trans mfix) = ST.check_one_fix mfix.
Proof.
  unfold ST.check_one_fix, TT.check_one_fix.
  destruct mfix as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p] => /= ->.
  rewrite -(trans_smash_context []) /trans_local.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error => /= //.
  move: (trans_decompose_app (decl_type c)).
  destruct decompose_app => /=.
  simpl. destruct c. simpl. intros ->.
  now rewrite -trans_destInd.
Qed.

Lemma map_option_out_check_one_fix mfix :
  map (fun x => TT.check_one_fix (map_def trans trans x)) mfix =
  map ST.check_one_fix mfix.
Proof.
  eapply map_ext => x. apply trans_check_one_fix.
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
  ST.check_recursivity_kind (SE.lookup_env Σ) k f = TT.check_recursivity_kind (trans_global_env Σ) k f.
Proof.
  unfold ST.check_recursivity_kind, TT.check_recursivity_kind.
  rewrite trans_lookup.
  destruct SE.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint Σ mfix :
  TT.wf_fixpoint (trans_global_env Σ) (map (map_def trans trans) mfix) =
  ST.wf_fixpoint Σ mfix.
Proof.
  unfold ST.wf_fixpoint, ST.wf_fixpoint_gen, TT.wf_fixpoint.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_fix.
  f_equal.
  - rewrite forallb_map. apply forallb_ext => d.
    rewrite /= trans_isLambda //.
  - destruct map_option_out as [[]|] => //.
    now rewrite trans_check_rec_kind.
Qed.

Lemma trans_wf_cofixpoint Σ mfix :
  TT.wf_cofixpoint (trans_global_env Σ) (map (map_def trans trans) mfix) =
  ST.wf_cofixpoint Σ mfix.
Proof.
  unfold ST.wf_cofixpoint, ST.wf_cofixpoint_gen, TT.wf_cofixpoint.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_cofix.
  destruct map_option_out as [[]|] => //.
  now rewrite trans_check_rec_kind.
Qed.

Lemma type_mkApps_napp `{checker_flags} Σ Γ f u T T' :
  ~~ isApp f ->
  TT.typing Σ Γ f T ->
  TT.typing_spine Σ Γ T u T' ->
  TT.typing Σ Γ (mkApps f u) T'.
Proof.
  intros hf hty hsp.
  depelim hsp. simpl; auto.
  rewrite mkApps_tApp.
  destruct f => //. congruence.
  econstructor; eauto.
  destruct f => //. congruence.
  econstructor; eauto.
Qed.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    TT.fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
  ST.cofix_guard Σ Γ mfix ->
  TT.cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

(* This version of typing spine allows to not require [isType] assumptions at the end of the
  application chain, which is crucial to be able to build a spine that both encompasses PCUIC's
  applications and mimicks the typing rule of.Common. Otherwise we would only model:

  |- tProd na A B : s
  |- f : tProd na A B
  |- u : A
  *** |- B [0 := u] : s ***  <- this last hypothesis is problematic, it's not present in PCUIC
  ------------------------      derivations for example.
  |- tApp f u : B [0 := u]

  The typing_spine_nil constructor allows to stack cumulativity steps using transitivity of cumulativity,
  following from confluence.

  In the end a typing derivation for an application that can mix application and cumulativity steps at any
  point:

  tApp (tApp f u) v : T' can be translated to

  typing_spine fty [u; v] T'
*)
Set Warnings "-notation-overridden".
Import PCUICAst PCUICLiftSubst PCUICTyping.
Set Warnings "notation-overridden".

Inductive typing_spine {cf} (Σ : global_env_ext) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_eq ty : typing_spine Σ Γ ty [] ty

| type_spine_nil ty ty' :
  isType Σ Γ ty' ->
  Σ ;;; Γ |- ty <= ty' ->
  typing_spine Σ Γ ty [] ty'

| type_spine_cons hd tl na A B T B' :
  isType Σ Γ (tProd na A B) ->
  Σ ;;; Γ |- T <= tProd na A B ->
  Σ ;;; Γ |- hd : A ->
  typing_spine Σ Γ (subst10 hd B) tl B' ->
  typing_spine Σ Γ T (hd :: tl) B'.
Derive Signature for typing_spine.

(* The size of a spine is the maximal depth of any typing derivation appearing in it *)
Section Typing_Spine_size.
  Context `{checker_flags}.
  Context {Σ : global_env_ext} {Γ : context}.

  Fixpoint typing_spine_size {t T U} (s : typing_spine Σ Γ t T U) : size :=
  match s with
  | type_spine_eq ty => 0
  | type_spine_nil ty ty' ist cum => typing_size ist.2.π2.1
  | type_spine_cons hd tl na A B T B' typrod cumul ty s' =>
    (max (typing_size typrod.2.π2.1) (max (typing_size ty) (typing_spine_size s')))%nat
  end.
End Typing_Spine_size.

(* We can weaken a spine by cumulativity, using the type_spine_nil  *)
Lemma typing_spine_weaken_concl {cf:checker_flags} {Σ Γ T args S S'} {wfΣ : wf Σ.1} :
  typing_spine Σ Γ T args S ->
  isType Σ Γ T ->
  Σ ;;; Γ ⊢ S ≤ S' ->
  isType Σ Γ S' ->
  typing_spine Σ Γ T args S'.
Proof.
  intros sp.
  induction sp in S' => tyT cum.
  * constructor; auto. now eapply ws_cumul_pb_forget in cum.
  * constructor; auto. eapply (into_ws_cumul_pb (pb:=Cumul)) in c; fvs.
    eapply (ws_cumul_pb_forget (pb:=Cumul)). now transitivity ty'.
  * intros isType. econstructor. eauto. eauto. eauto.
    apply IHsp; auto. eapply PCUICArities.isType_apply; tea.
Defined.

(* The size includes the new [isType] hypothesis  *)
Lemma typing_spine_weaken_concl_size {cf:checker_flags} {Σ Γ T args S S'}
  (wf : wf Σ.1)
  (sp  :typing_spine Σ Γ T args S)
  (tyT : isType Σ Γ T)
  (Hs : Σ ;;; Γ ⊢ S ≤ S')
  (ist : isType Σ Γ S') :
  typing_spine_size (typing_spine_weaken_concl sp tyT Hs ist) <=
  max (typing_spine_size sp) (typing_size ist.2.π2.1).
Proof.
  induction sp; simpl; auto. lia.
  rewrite - !Nat.max_assoc.
  specialize (IHsp (PCUICArities.isType_apply i t) Hs). cbn in *. lia.
Qed.

Ltac sig := unshelve eexists.

(** We can also append an argument to a spine *without* requiring a typing for the new conclusion type.
  This would be a derivation for a substitution of [B], hence incomparable in depth to the arguments.
  The invariant is witnessed by the spine size being lower than the arguments.
*)
Lemma typing_spine_app {cf:checker_flags} Σ Γ ty args na A B arg
  (wf : wf Σ.1)
  (isty : isType Σ Γ (tProd na A B))
  (sp : typing_spine Σ Γ ty args (tProd na A B))
  (argd : Σ ;;; Γ |- arg : A) :
  ∑ sp' : typing_spine Σ Γ ty (args ++ [arg]) (B {0 := arg}),
    typing_spine_size sp' <= max (typing_size isty.2.π2.1) (max (typing_spine_size sp) (typing_size argd)).
Proof.
  revert arg argd.
  depind sp.
  - intros arg Harg. simpl.
    sig.
    * econstructor; eauto. reflexivity.
      constructor.
    * simpl. lia.
  - intros arg Harg. simpl.
    sig.
    * econstructor; eauto. constructor.
    * simpl. lia.
  - intros arg Harg. simpl.
    specialize (IHsp wf isty _ Harg) as [sp' Hsp'].
    sig.
    * econstructor. apply i. auto. auto. exact sp'.
    * simpl. cbn in *. lia.
Qed.

(** Likewise, in.Common-Rocq, we can append without re-typing the result *)
Lemma TT_typing_spine_app {cf:checker_flags} Σ Γ ty T' args na A B arg s :
  TT.typing Σ Γ (T.tProd na A B) (T.tSort s) ->
  TT.typing_spine Σ Γ ty args T' ->
  TT.cumul_gen Σ Γ Cumul T' (T.tProd na A B) ->
  TT.typing Σ Γ arg A ->
  TT.typing_spine Σ Γ ty (args ++ [arg]) (T.subst1 arg 0 B).
Proof.
  intros isty H; revert arg.
  remember (T.tProd na A B) as prod.
  revert na A B Heqprod.
  induction H.
  - intros na A B eq arg Harg. simpl. econstructor; eauto. now rewrite <-eq. rewrite <-eq.
    apply Harg.
    constructor.
  - intros na' A' B'' eq arg Harg. simpl.
    econstructor. apply t. auto. auto.
    eapply IHtyping_spine. now rewrite eq. exact eq. apply Harg. apply X.
Defined.

(** This is the central lemma for this translation:
  any PCUIC typing of an application `t` can be decomposed as
  a typing of the head of `t` followed by a typing spine for
  its arguments `l`. *)

Lemma type_app {cf} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) :
  wf Σ.1 ->
  if isApp t then
    let (f, l) := decompose_app t in
    ∑ fty (d' : Σ ;;; Γ |- f : fty),
      ((typing_size d' <= typing_size d) *
      ∑ (sp : typing_spine Σ Γ fty l T),
        (typing_spine_size sp <= typing_size d))%type
  else True.
Proof.
  intros wfΣ.
  induction d; simpl; auto.
  - destruct (isApp t) eqn:isapp.
    destruct (decompose_app (tApp t u)) eqn:da.
    unfold decompose_app in da.
    simpl in da.
    apply decompose_app_rec_inv' in da as [n [napp [equ eqt]]].
    subst t. clear IHd1 IHd3.
    rewrite PCUICAstUtils.decompose_app_mkApps // in IHd2.
    destruct IHd2 as [fty [d' [sp hd']]].
    exists fty, d'.
    split. lia.
    destruct hd' as [sp' Hsp].
    destruct (typing_spine_app _ _ _ _ _ _ _ _ wfΣ (has_sort_isType s d1) sp' d3) as [appsp Happ].
    simpl in Happ.
    move: appsp Happ. rewrite equ firstn_skipn.
    intros app happ. exists app. lia.

    unfold decompose_app. simpl.
    rewrite PCUICAstUtils.atom_decompose_app. destruct t => /= //.
    eexists _, d2. split. lia.
    unshelve eexists.
    econstructor. eapply has_sort_isType; eauto. reflexivity. assumption. constructor.
    simpl. lia.

  - destruct (isApp t) eqn:isapp => //.
    destruct (decompose_app t) eqn:da.
    assert (l <> []).
    { eapply decompose_app_nonnil in da => //. }
    destruct IHd1 as [fty [d' [? ?]]].
    exists fty, d'. split. lia.
    destruct s0 as [sp Hsp].
    unshelve eexists. eapply typing_spine_weaken_concl; eauto. exact (PCUICValidity.validity d').
    eapply cumulSpec_cumulAlgo_curry in c; eauto; fvs.
    eapply (has_sort_isType s d2).
    epose proof (typing_spine_weaken_concl_size wfΣ sp (validity_term wfΣ d')
      (cumulSpec_cumulAlgo_curry Σ wfΣ Γ A B (typing_closed_context d') (type_is_open_term d1) (subject_is_open_term d2) c)
      (has_sort_isType s d2)). simpl in H0. simpl. lia.
Qed.

(** Finally, for each typing spine built above, assuming we can apply the induction hypothesis
  of the translation to any of the typing derivations in the spine, then we can produce a typing
  spine in the n-ary application template-rocq spec.

  We have two cases to consider at the "end" of the spine: either we have the same translation of the
  PCUIC conclusion type, or there is exactly one cumulativity step to get to this type. *)
Lemma make_typing_spine {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ fty l T}
  (sp : PCUICToTemplateCorrectness.typing_spine Σ Γ fty l T) n
  (IH : forall t' T' (Ht' : Σ ;;; Γ |- t' : T'),
      typing_size Ht' <= n ->
      TT.typing (trans_global Σ) (trans_local Γ) (trans t') (trans T')) :
  isType Σ Γ fty ->
  typing_spine_size sp <= n ->
  ∑ T', TT.typing_spine (trans_global Σ) (trans_local Γ) (trans fty) (map trans l) T' *
    ((T' = trans T) +
      (TT.cumul_gen (trans_global Σ) (trans_local Γ) Cumul T' (trans T) *
       ∑ s, TT.typing (trans_global Σ) (trans_local Γ) (trans T) (T.tSort s)))%type.
Proof.
  induction sp; simpl; intros.
  - exists (trans ty); split.
    * constructor.
    * left; auto.
  - exists (trans ty).
    split. constructor. right.
    split.
    eapply cumul_decorate in c; tea.
    now eapply trans_cumul in c.
    destruct i as (?&?&Hty&?); simpl in *.
    specialize (IH _ _ Hty H). now eexists.

  - simpl; intros.
    forward IHsp.
    eapply isType_apply; tea.
    forward IHsp by lia.
    specialize (IH _ _ t) as IHt.
    forward IHt by lia.
    eapply cumul_decorate in c; tea.
    apply trans_cumul in c.
    destruct i as (?&?&Hty&?); simpl in *.
    specialize (IH _ _ Hty) as IHi.
    forward IHi by lia.
    simpl in IHi.
    destruct IHsp as [T' [Hsp eq]].
    destruct eq. subst T'.
    exists (trans B'). split; auto.
    econstructor.
    eauto.
    apply c.
    apply IHt.
    now rewrite trans_subst in Hsp.
    exists T'. split; auto.
    econstructor.
    eauto. apply c. apply IHt.
    now rewrite trans_subst in Hsp.
Qed.

Lemma it_mkLambda_or_LetIn_app l l' t :
  T.Env.it_mkLambda_or_LetIn (l ++ l') t = T.Env.it_mkLambda_or_LetIn l' (T.Env.it_mkLambda_or_LetIn l t).
Proof. induction l in l', t |- *; simpl; auto. Qed.

Lemma trans_it_mkLambda_or_LetIn Γ T :
  trans (it_mkLambda_or_LetIn Γ T) = T.Env.it_mkLambda_or_LetIn (trans_local Γ) (trans T).
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

Lemma trans_case_branch_type {cf} {Σ : global_env_ext} {wfΣ : wf Σ} ci mdecl idecl cdecl i p br :
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_branch cdecl br ->
  eq_context_upto_names (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  Ast.case_branch_type ci (trans_minductive_body mdecl)
  (trans_predicate
    (map_predicate id trans trans (map_context trans) p))
  (Env.it_mkLambda_or_LetIn
    (trans_local (case_predicate_context ci mdecl idecl p))
    (Ast.preturn
        (trans_predicate
          (map_predicate id trans trans (map_context trans) p))))
  i (trans_constructor_body cdecl)
  (trans_branch (map_branch trans (map_context trans) br)) =
  (trans_local (case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl),
   trans (case_branch_type ci mdecl idecl p br ptm i cdecl).2).
Proof.
  intros.
  rewrite /Ast.case_branch_type /Ast.case_branch_type_gen /=. f_equal.
  - rewrite [Ast.case_branch_context_gen _ _ _ _ _ _]trans_inst_case_branch_context => //.
    f_equal.
    rewrite /case_branch_context.
    symmetry.
    erewrite <- PCUICCasesContexts.inst_case_branch_context_eq => //.
  - rewrite trans_mkApps !lengths.
    rewrite trans_lift /ptm trans_it_mkLambda_or_LetIn. f_equal.
    rewrite !map_app (map_map_compose _ _ _ _ trans). f_equal.
    setoid_rewrite trans_subst.
    rewrite -(map_map_compose _ _ _ trans) map_rev. f_equal.
    rewrite (map_map_compose _ _ _ _ trans).
    setoid_rewrite trans_expand_lets_k.
    rewrite /id trans_subst_instance_ctx.
    rewrite -(map_map_compose _ _ _ trans). f_equal.
    rewrite (map_map_compose _ _ _ _ trans).
    setoid_rewrite trans_subst.
    rewrite trans_inds.
    rewrite -(map_map_compose _ _ _ trans). f_equal.
    rewrite !map_map_compose.
    now setoid_rewrite trans_subst_instance.
    cbn. rewrite trans_mkApps map_app; f_equal. f_equal.
    rewrite map_map_compose. setoid_rewrite <- trans_lift.
    rewrite -(map_map_compose _ _ _ _ trans). f_equal.
    now rewrite trans_to_extended_list.
Qed.

From MetaRocq.PCUIC Require Import PCUICClosed PCUICWeakeningEnvConv PCUICWeakeningEnvTyp.

Lemma trans_subst_instance_decl u x : map_decl (subst_instance u) (trans_decl x) = trans_decl (map_decl (subst_instance u) x).
Proof.
  destruct x as [na [b|] ty]; cbn; rewrite /trans_decl /map_decl /=; now rewrite !trans_subst_instance.
Qed.

Lemma subst_telescope_subst_context s k Γ :
  Env.subst_telescope s k (List.rev Γ) = List.rev (Env.subst_context s k Γ).
Proof.
  rewrite /Env.subst_telescope Env.subst_context_alt.
  rewrite rev_mapi. apply mapi_rec_ext.
  intros n [na [b|] ty] le le'; rewrite /= /Env.subst_decl /map_decl /=;
  rewrite List.length_rev Nat.add_0_r in le';
  f_equal. f_equal. f_equal. lia. f_equal; lia.
  f_equal; lia.
Qed.

Theorem pcuic_to_template {cf} (Σ : SE.global_env_ext) Γ t T :
  ST.wf Σ ->
  ST.typing Σ Γ t T ->
  TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  intros X X0.
  revert Σ X Γ t T X0.
  (** We use an induction principle allowing to apply induction to any subderivation of
    functions in applications. *)
  apply (typing_ind_env_app_size (fun Σ Γ t T =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type
    (fun Σ Γ j => TT.lift_typing TT.typing (trans_global Σ) (trans_local Γ) (judgment_map trans j))
    (fun Σ Γ =>
    TT.All_local_env (TT.lift_typing TT.typing (trans_global Σ)) (trans_local Γ))
  );intros.
  - destruct X as (Hb & s & (_ & IHt) & e).
    repeat (eexists; tea); cbn.
    destruct j_term => //=. destruct Hb => //.
  - now eapply trans_wf_local_env, All_over_All.
  - rewrite trans_lift.
    rewrite trans_decl_type.
    eapply TT.type_Rel; eauto.
    + now apply map_nth_error.
  - econstructor; eauto.
  - eapply TT.type_Prod;assumption.
  - eapply TT.type_Lambda;eassumption.
  - eapply TT.type_LetIn;eassumption.
  - simpl. rewrite trans_subst10.
    destruct (isApp t) eqn:isapp.
    move: (type_app Ht wfΣ). rewrite isapp.
    destruct (decompose_app t) eqn:da.
    intros [fty [d' [hd' [sp hsp]]]].
    assert (hd'' : typing_size d' ≤ max (typing_size Ht) (typing_size Hp)) by lia.
    assert (hsp' : typing_spine_size sp ≤ max (typing_size Ht) (typing_size Hp)) by lia.
    assert (IHt := X2 _ _ d' hd'').
    epose proof (make_typing_spine sp (max (typing_size Ht) (typing_size Hp)) X2 (validity d') hsp') as [T' [IH []]].
    * subst T'. rewrite (PCUICAstUtils.decompose_app_inv da).
      rewrite trans_mkApps mkApp_mkApps -AstUtils.mkApps_app.
      pose proof (AstUtils.mkApps_app (trans t0) (map trans l) [trans u]).
      apply decompose_app_notApp in da.
      apply trans_isApp in da.
      eapply type_mkApps_napp. rewrite da //.
      eassumption.
      eapply TT_typing_spine_app. simpl in X1. eapply X0.
      apply IH. apply TT.cumul_refl'.
      apply X4.
    * destruct p as [hcum _].
      rewrite (PCUICAstUtils.decompose_app_inv da).
      rewrite trans_mkApps mkApp_mkApps -AstUtils.mkApps_app.
      pose proof (AstUtils.mkApps_app (trans t0) (map trans l) [trans u]).
      apply decompose_app_notApp in da.
      apply trans_isApp in da.
      eapply type_mkApps_napp. rewrite da //.
      eassumption.
      eapply TT_typing_spine_app. simpl in X0. eapply X0.
      apply IH. apply hcum.
      apply X4.
    * rewrite mkApp_mkApps.
      eapply type_mkApps_napp.
      apply trans_isApp in isapp. rewrite isapp //.
      now simpl in X2.
      econstructor. eapply X0.
      apply TT.cumul_refl'. assumption. constructor.
  - rewrite trans_subst_instance.
    rewrite trans_cst_type.
    eapply TT.type_Const; eauto.
    + now apply trans_declared_constant.
  - rewrite trans_subst_instance.
    rewrite trans_ind_type.
    eapply TT.type_Ind; eauto.
    + now apply trans_declared_inductive.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_type_of_constructor.
    eapply TT.type_Construct; auto.
    + destruct isdecl.
      constructor.
      * now apply trans_declared_inductive.
      * now apply map_nth_error.
  - rewrite trans_mkApps map_app.
    simpl.
    rewrite /ptm trans_it_mkLambda_or_LetIn.
    rewrite /predctx.
    have hty := validity X6.
    eapply isType_mkApps_Ind_smash in hty as []; tea.
    erewrite <- trans_case_predicate_context; tea.
    2:{ eapply (wf_predicate_length_pars H0). }
    eapply TT.type_Case; auto.
    + now apply trans_declared_inductive.
    + cbn. now apply trans_ind_predicate_context_eq.
    + cbn. rewrite PCUICToTemplateCorrectness.context_assumptions_map length_map.
      rewrite (wf_predicate_length_pars H0).
      now rewrite (declared_minductive_ind_npars isdecl).
    + move: X5.
      cbn. rewrite -!map_app. rewrite /id.
      rewrite map_map_compose.
      set (mapd := map (fun x : context_decl => _) _).
      replace mapd with (trans_local (ind_indices idecl ++ ind_params mdecl)@[puinst p]).
      2:{ subst mapd. setoid_rewrite trans_subst_instance_decl. now rewrite -map_map_compose. }
      rewrite -[List.rev (trans_local _)]map_rev.
      clear. unfold app_context. change subst_instance_context with SE.subst_instance_context. unfold context.
      rewrite -map_rev. set (ctx := map _ (List.rev _)). clearbody ctx.
      intro HH; pose proof (ctx_inst_impl _ (fun _ _ _ => TT.typing _ _ _ _ ) _ _ _ HH (fun _ _ H => H.2)); revert X; clear HH.
      now move: ctx; induction 1; cbn; constructor; auto;
        rewrite -(List.rev_involutive (map trans_decl Δ)) subst_telescope_subst_context -map_rev
          -(trans_subst_context [_]) -map_rev -PCUICSpine.subst_telescope_subst_context List.rev_involutive.
    + cbn [Ast.pparams Ast.pcontext trans_predicate].
      rewrite (trans_case_predicate_context Γ); tea.
      now rewrite -trans_local_app.
    + rewrite <- trans_global_ext_constraints.
      eassumption.
    + assumption.
    + now rewrite trans_mkApps map_app in X7.
    + rewrite (trans_case_predicate_context Γ); tea.
      eapply All2i_map. eapply All2i_map_right.
      eapply Forall2_All2 in H5.
      eapply All2i_All2_mix_left in X8; tea.
      eapply All2i_impl ; tea.
      intros i cdecl br. cbv beta.
      set (cbt := case_branch_type _ _ _ _ _ _ _ _).
      intros (wf & eqctx & Hbctx & (Hb & IHb) & Hbty & IHbty) brctxty.
      repeat split.
      * rewrite /brctxty.
        now eapply trans_cstr_branch_context_eq.
      * pose proof (trans_case_branch_type ci mdecl idecl cdecl i p br isdecl H1 wf eqctx).
        rewrite -/brctxty -/ptm in H6. cbn in H6. clearbody brctxty.
        subst brctxty. rewrite -trans_local_app. cbn. apply IHb.
      * pose proof (trans_case_branch_type ci mdecl idecl cdecl i p br isdecl H1 wf eqctx).
        rewrite -/brctxty -/ptm in H6. cbn in H6. clearbody brctxty.
        subst brctxty. rewrite -trans_local_app. cbn. apply IHbty.

  - rewrite trans_subst trans_subst_instance /= map_rev.
    change (trans (proj_type pdecl)) with (trans_projection_body pdecl).(Ast.Env.proj_type).
    eapply TT.type_Proj.
    + apply trans_declared_projection; eauto.
    + rewrite trans_mkApps in X2.
      assumption.
    + rewrite length_map H. now destruct mdecl.
  - rewrite trans_dtype. simpl.
    eapply TT.type_Fix; auto.
    + now rewrite fix_guard_trans.
    + erewrite map_nth_error.
      2: apply H0.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + eapply All_map, X1.
    + fold trans.
      subst types.
      eapply trans_mfix_All2. eassumption.
    + now rewrite trans_wf_fixpoint.
  - rewrite trans_dtype. simpl.
    eapply TT.type_CoFix; auto.
    + now eapply cofix_guard_trans.
    + erewrite map_nth_error.
      2: eassumption.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + fold trans.
      eapply All_map, X1.
    + fold trans;subst types.
      now apply trans_mfix_All2.
    + now rewrite trans_wf_cofixpoint.
  - destruct p as [? []]; simp prim_type; cbn; econstructor; eauto.
    1,3,5,7: eapply trans_declared_constant; tea.
    all:cbn in *.
    all:move: H1; rewrite /Ast.Env.primitive_invariants /primitive_invariants.
    all: try by intros []; split => //;
    destruct cdecl as [ty [?|] ?]; cbn in *; subst; auto => //.
    all:depelim X1; eauto. intros _. solve_all.
  - eapply TT.type_Conv.
    + eassumption.
    + eassumption.
    + eapply cumulSpec_cumulAlgo_curry in X4; tea; fvs.
      eapply ws_cumul_pb_forget in X4.
      eapply cumul_decorate in X4; tea.
      2:eapply validity; tea.
      2:now eapply has_sort_isType.
      now eapply trans_cumul.
Qed.

(* Print Assumptions pcuic_to_template. *)
