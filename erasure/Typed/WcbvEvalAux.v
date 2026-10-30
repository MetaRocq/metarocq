From Equations Require Import Equations.
From MetaRocq.Erasure.Typed Require Import ClosedAux.
From MetaRocq.Utils Require Import MRPrelude.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Erasure Require Import EAstUtils.
From MetaRocq.Erasure Require Import ECSubst.
From MetaRocq.Erasure Require Import ELiftSubst.
From MetaRocq.Erasure Require Import EWcbvEval.
From MetaRocq.Erasure Require Import EOptimizePropDiscr.
From MetaRocq.Utils Require Import utils.

Set Equations Transparent.

Notation "Σ 'e⊢' s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

Global Arguments eval_unique_sig {_ _ _ _ _}.
Global Arguments eval_deterministic {_ _ _ _ _}.
Global Arguments eval_unique {_ _ _ _}.

Section fix_flags.
Context {wfl : WcbvFlags}.

Lemma eval_tApp_head Σ hd arg v :
  Σ e⊢ tApp hd arg ⇓ v ->
  ∑ hdv, Σ e⊢ hd ⇓ hdv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_tApp_arg Σ hd arg v :
  Σ e⊢ tApp hd arg ⇓ v ->
  ∑ argv, Σ e⊢ arg ⇓ argv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_mkApps_head Σ hd args v :
  Σ e⊢ mkApps hd args ⇓ v ->
  ∑ hdv, Σ e⊢ hd ⇓ hdv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  specialize (IHargs _ _ ev) as (? & ?).
  now apply eval_tApp_head in e.
Qed.

Lemma eval_mkApps_args Σ hd args v :
  Σ e⊢ mkApps hd args ⇓ v ->
  ∑ argsv, All2 (eval Σ) args argsv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  apply eval_mkApps_head in ev as ev_hd.
  destruct ev_hd as (hdv & ev_hd).
  specialize (IHargs _ _ ev) as (argsv & all).
  apply eval_tApp_arg in ev_hd as (argv & ev_arg).
  exists (argv :: argsv).
  now constructor.
Qed.

Lemma eval_tApp_heads Σ hd hd' hdv arg v :
  Σ e⊢ hd ⇓ hdv ->
  Σ e⊢ hd' ⇓ hdv ->
  Σ e⊢ tApp hd arg ⇓ v ->
  Σ e⊢ tApp hd' arg ⇓ v.
Proof.
  intros ev_hd ev_hd' ev_app.
  depind ev_app.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_box.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_beta.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix_value.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix'.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_construct.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_app_cong.
  - easy.
Qed.

Derive Signature for eval.
Derive NoConfusionHom for term.

Lemma eval_tLetIn_inv Σ na val body res :
  Σ e⊢ tLetIn na val body ⇓ res ->
  ∑ val_res,
    Σ e⊢ val ⇓ val_res ×
    Σ e⊢ csubst val_res 0 body ⇓ res.
Proof. intros ev; depelim ev; easy. Qed.

Lemma eval_tLambda_inv Σ na body v :
  Σ e⊢ tLambda na body ⇓ v ->
  v = tLambda na body.
Proof. now intros ev; depelim ev. Qed.

Lemma eval_tApp_tLambda_inv Σ na body a v :
  Σ e⊢ tApp (tLambda na body) a ⇓ v ->
  ∑ av,
    Σ e⊢ a ⇓ av ×
    Σ e⊢ csubst av 0 body ⇓ v.
Proof.
  intros ev.
  depelim ev.
  - now apply eval_tLambda_inv in ev1.
  - apply eval_tLambda_inv in ev1.
    inversion ev1; subst; clear ev1.
    easy.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - apply eval_tLambda_inv in ev1.
    inversion ev1.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - now apply eval_tLambda_inv in ev1 as ->.
  - easy.
Qed.

Lemma eval_mkApps_heads Σ hd hd' hdv args v :
  Σ e⊢ hd ⇓ hdv ->
  Σ e⊢ hd' ⇓ hdv ->
  Σ e⊢ mkApps hd args ⇓ v ->
  Σ e⊢ mkApps hd' args ⇓ v.
Proof.
  revert hd hd' hdv v.
  induction args as [|a args]; intros hd hd' hdv v ev_hd ev_hd' ev.
  - cbn in *.
    now rewrite (eval_deterministic ev ev_hd) in *.
  - cbn in *.
    apply eval_mkApps_head in ev as ev_app_hd.
    destruct ev_app_hd as (app_hdv & ev_app_hd).
    eapply IHargs.
    2: {
      eapply eval_tApp_heads; [| |exact ev_app_hd].
      all: easy.
    }
    + easy.
    + easy.
Qed.

Lemma lookup_env_find Σ kn :
  EGlobalEnv.lookup_env Σ kn =
  option_map snd (find (fun '(kn', _) => if eqb kn kn' then true else false) Σ).
Proof.
  induction Σ as [|(kn' & decl) Σ IH]; [easy|].
  cbn.
  now destruct (kn == kn');subst.
Qed.

Lemma closed_constant Σ kn cst body :
  env_closed Σ ->
  EGlobalEnv.declared_constant Σ kn cst ->
  EAst.cst_body cst = Some body ->
  closed body.
Proof.
  intros env_clos decl_const body_eq.
  unfold EGlobalEnv.declared_constant in decl_const.
  rewrite lookup_env_find in decl_const.
  destruct (find _ _) eqn:find; [|easy].
  apply find_some in find.
  eapply forallb_forall in env_clos; [|exact (proj1 find)].
  destruct p.
  cbn in *.
  noconf decl_const.
  cbn in *.
  now rewrite body_eq in env_clos.
Qed.

Lemma closed_unfold_fix mfix idx narg fn :
  closed (tFix mfix idx) ->
  EGlobalEnv.unfold_fix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold EGlobalEnv.unfold_fix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold EGlobalEnv.fix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite EGlobalEnv.fix_subst_length.
Qed.

Lemma closed_unfold_cofix mfix idx narg fn :
  closed (tFix mfix idx) ->
  EGlobalEnv.unfold_cofix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold EGlobalEnv.unfold_cofix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold EGlobalEnv.cofix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite EGlobalEnv.cofix_subst_length.
Qed.

Lemma all_closed Σ args args' :
  Forall (closedn 0) args ->
  All2 (eval Σ) args args' ->
  Forall2 (fun t v => closed t -> closed v) args args' ->
  Forall (closedn 0) args'.
Proof.
  intros args_clos args_eval impl_clos.
  induction args_eval; [easy|].
  depelim args_clos.
  depelim impl_clos.
  easy.
Qed.

Lemma closed_iota_red pars args br :
  Forall (fun a => closed a) args ->
  closedn #|skipn pars args| br.2 ->
  closed (EGlobalEnv.iota_red pars args br).
Proof.
  intros clos_args clos_brs.
  unfold EGlobalEnv.iota_red.
  apply closed_substl.
  - apply forallb_Forall.
    apply Forall_rev.
    now apply Forall_skipn.
  - rewrite Nat.add_0_r.
    rewrite List.length_rev;auto.
Qed.

Lemma closed_cunfold_fix defs n narg f :
  EGlobalEnv.cunfold_fix defs n = Some (narg, f) ->
  closed (tFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_fix_cunfold_eq in eq by easy.
  now eapply closed_unfold_fix.
Qed.

Lemma closed_cunfold_cofix defs n narg f :
  EGlobalEnv.cunfold_cofix defs n = Some (narg, f) ->
  closed (tCoFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_cofix_cunfold_eq in eq by easy.
  now eapply closed_unfold_cofix.
Qed.

Definition eval_prim_length {wfl : WcbvFlags} {Σ p p'} (len : forall t v, Σ e⊢ t ⇓ v -> nat) (d : eval_primitive (eval Σ) p p') : nat :=
  match d with
  | evalPrimInt _ | evalPrimFloat _ | evalPrimString _ => 0
  | evalPrimArray v d v' d' av ev =>
    len _ _ ev + EPrimitive.all2_size _ len av
  end.

Fixpoint deriv_length {Σ t v} (ev : Σ e⊢ t ⇓ v) : nat :=
  match ev with
  | eval_atom _ _ => 1
  | eval_delta _ _ _ _ _ _ ev
  | eval_proj_prop _ _ _ ev _ => S (deriv_length ev)
  | eval_cofix_proj _ _ _ _ _ _ _ _ ev1 _ ev2
  | eval_box _ _ _ ev1 ev2
  | eval_zeta _ _ _ _ _ ev1 ev2
  | eval_iota_block _ _ _ _ _ _ _ _ _ _ ev1 _ _ _ _ ev2
  | eval_iota _ _ _ _ _ _ _ _ _ _ ev1 _ _ _ _ ev2
  | eval_iota_sing _ _ _ _ _ _ _ _ ev1 _ _ ev2
  | eval_fix_value _ _ _ _ _ _ _ _ _ ev1 ev2 _ _
  | eval_cofix_case _ _ _ _ _ _ _ _ _ ev1 _ ev2
  | eval_proj _ _ _ _ _ _ _ ev1 _ _ _ ev2
  | eval_proj_block _ _ _ _ _ _ _ ev1 _ _ _ ev2
  | eval_construct _ _ _ _ _ _ _ _ _ _ _ ev1 _ ev2
  | eval_app_cong _ _ _ _ ev1 _ ev2 => S (deriv_length ev1 + deriv_length ev2)
  | eval_beta _ _ _ _ _ _ ev1 ev2 ev3
  | eval_fix' _ _ _ _ _ _ _ _ _ ev1 _ ev2 ev3
  | eval_fix _ _ _ _ _ _ _ _ _ ev1 ev2 _ ev3 =>
      S (deriv_length ev1 + deriv_length ev2 + deriv_length ev3)
  | eval_construct_block _ _ _ _ _ args _ _ _ _ _ => S #|args|
  | eval_prim _ _ ev => S (eval_prim_length (@deriv_length _) ev)
  | eval_force _ _ _ ev ev' => S (deriv_length ev + deriv_length ev')
  end.

Lemma deriv_length_min {Σ t v} (ev : Σ e⊢ t ⇓ v) :
  1 <= deriv_length ev.
Proof.
  destruct ev; cbn in *;lia.
Qed.

Lemma eval_tApp_deriv {Σ hd arg v} (ev : Σ e⊢ tApp hd arg ⇓ v) :
  ∑ hdv (ev_hd : Σ e⊢ hd ⇓ hdv) argv (ev_arg : Σ e⊢ arg ⇓ argv),
    S (deriv_length ev_hd + deriv_length ev_arg) <= deriv_length ev.
Proof.
  depelim ev; cbn in *;
    try now eexists _, ev1, _, ev2.
  easy.
Qed.

Fixpoint sum_deriv_lengths {Σ ts tsv} (a : All2 (eval Σ) ts tsv) : nat :=
  match a with
  | All2_nil => 0
  | All2_cons _ _ _ _ ev a => deriv_length ev + sum_deriv_lengths a
  end.

Fixpoint app_All2
         {A B}
         {T : A -> B -> Type}
         {la lb la' lb'}
         (a1 : All2 T la lb)
         (a2 : All2 T la' lb') : All2 T (la ++ la') (lb ++ lb').
Proof.
  destruct a1.
  - exact a2.
  - refine (All2_cons t _).
    exact (app_All2 _ _ _ _ _ _ _ a1 a2).
Defined.

Lemma eval_mkApps_deriv {Σ hd args v} (ev : Σ e⊢ mkApps hd args ⇓ v) :
  ∑ hdv (ev_hd : Σ e⊢ hd ⇓ hdv) argsv (ev_args : All2 (eval Σ) args argsv),
    deriv_length ev_hd + #|args| + sum_deriv_lengths ev_args <= deriv_length ev.
Proof.
  revert hd v ev.
  induction args; intros hd v ev; cbn in *.
  - exists _, ev, [], All2_nil.
    now cbn.
  - specialize (IHargs _ _ ev) as (hdv & ev_hd & argsv & ev_args & len).
    specialize (eval_tApp_deriv ev_hd) as (hdv' & ev_hdv' & argv & ev_argv & len').
    exists _, ev_hdv', (argv :: argsv).
    exists (All2_cons ev_argv ev_args).
    cbn in *.
    lia.
Qed.

Lemma All2_split_eq
      {X Y} {T : X -> Y -> Type}
      {xs ys xs' ys'}
      (a : All2 T (xs ++ xs') (ys ++ ys')) :
  #|xs| = #|ys| ->
  ∑ apref asuf, a = app_All2 apref asuf.
Proof.
  intros eq.
  induction xs in xs, ys, xs', ys', a, eq |- *.
  - destruct ys; [|easy].
    cbn in *.
    now exists All2_nil, a.
  - destruct ys; [easy|].
    cbn in *.
    depelim a.
    specialize (IHxs ys xs' ys' a ltac:(easy)) as (apref & asuf & ->).
    now exists (All2_cons t apref), asuf.
Qed.

Lemma All2_rev_rect X Y (T : X -> Y -> Type) (P : forall xs ys, All2 T xs ys -> Type) :
  P [] [] All2_nil ->
  (forall x y xs ys (t : T x y) (a : All2 T xs ys),
      P xs ys a -> P (xs ++ [x]) (ys ++ [y]) (app_All2 a (All2_cons t All2_nil))) ->
  forall xs ys (a : All2 T xs ys), P xs ys a.
Proof.
  intros nil_case snoc_case.
  induction xs using MRList.rev_ind; intros ys a.
  - now depelim a.
  - destruct ys as [|y ys _] using MRList.rev_ind.
    + apply All2_length in a as ?.
      rewrite length_app in *.
      now cbn in *.
    + unshelve epose proof (All2_split_eq a _) as (? & ? & ->).
      * apply All2_length in a.
        rewrite !length_app in a.
        now cbn in *.
      * depelim x1.
        depelim x3.
        apply snoc_case.
        apply IHxs.
Qed.

Inductive All2_eval_app_spec Σ : list term -> term ->
                                 list term -> term ->
                                 forall ts tsv, All2 (eval Σ) ts tsv -> Type :=
| All2_eval_app_intro {ts tsv} (a : All2 (eval Σ) ts tsv)
                      {x xv} (evx : Σ e⊢ x ⇓ xv) :
    All2_eval_app_spec
      Σ ts x tsv xv
      (ts ++ [x])
      (tsv ++ [xv])
      (app_All2 a (All2_cons evx All2_nil)).

Derive Signature for All2.
Derive NoConfusionHom for All2.

Lemma All2_eval_snoc_elim
      {Σ ts tsv x xv} (a : All2 (eval Σ) (ts ++ [x]) (tsv ++ [xv])) :
  All2_eval_app_spec Σ ts x tsv xv _ _ a.
Proof.
  unshelve epose proof (All2_split_eq a _) as (? & ev & ->).
  - apply All2_length in a.
    rewrite !length_app in a.
    now cbn in *.
  - depelim ev.
    depelim ev.
    constructor.
Qed.

Lemma eval_tApp_heads_deriv {Σ hd hd' hdv arg v}
      (ev_hd : Σ e⊢ hd ⇓ hdv)
      (ev_hd' : Σ e⊢ hd' ⇓ hdv)
      (ev_app : Σ e⊢ tApp hd arg ⇓ v) :
  ∑ (ev_app' : Σ e⊢ tApp hd' arg ⇓ v),
    (deriv_length ev_app + deriv_length ev_hd' = deriv_length ev_app' + deriv_length ev_hd)%nat.
Proof.
  depind ev_app.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_box|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_beta|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_fix|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_fix_value|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_fix'|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_construct|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_app_cong|].
    cbn; lia.
  - easy.
Qed.

Lemma eval_mkApps_heads_deriv {Σ hd hd' hdv args v}
      (ev_hd : Σ e⊢ hd ⇓ hdv)
      (ev_hd' : Σ e⊢ hd' ⇓ hdv)
      (ev_apps : Σ e⊢ mkApps hd args ⇓ v) :
  ∑ (ev_apps' : Σ e⊢ mkApps hd' args ⇓ v),
  (deriv_length ev_apps + deriv_length ev_hd' = deriv_length ev_apps' + deriv_length ev_hd)%nat.
Proof.
  revert hd hd' hdv v ev_hd ev_hd' ev_apps.
  induction args using MRList.rev_ind; intros; cbn in *.
  - pose proof (eval_unique_sig ev_hd ev_apps) as H; noconf H.
    exists ev_hd'; lia.
  - revert ev_apps; rewrite !mkApps_app; intros.
    cbn in *.
    eapply eval_tApp_head in ev_apps as ev_apps'.
    destruct ev_apps' as (? & ev_apps').
    specialize (IHargs _ _ _ _ ev_hd ev_hd' ev_apps') as (ev_apps'' & ?).
    pose proof (eval_tApp_heads_deriv ev_apps' ev_apps'' ev_apps) as (ev & ?).
    exists ev.
    lia.
Qed.

End fix_flags.
