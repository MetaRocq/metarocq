(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICPosition PCUICCases PCUICSigmaCalculus
     PCUICUnivSubst PCUICContextSubst PCUICTyping
     PCUICWeakeningEnvConv PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICClosed PCUICClosedConv PCUICClosedTyp
     PCUICReduction PCUICWeakeningConv PCUICWeakeningTyp PCUICCumulativity PCUICUnivSubstitutionConv
     PCUICRenameDef PCUICRenameConv PCUICInstDef PCUICInstConv PCUICInstTyp PCUICOnFreeVars.

From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

(** * Substitution lemmas for typing derivations. Substitution is now derived from a general
      instantiation lemma, but the rest of the theory is using substituion lemmas instead
      of the slightly more general but also more technical instantiation lemmas.
*)

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Local Set Keyed Unification.

Set Default Goal Selector "!".

#[global]
Hint Rewrite @app_context_length : wf.

Generalizable Variables Σ Γ t T.

Local Open Scope sigma_scope.

(** Well-typed substitution into a context with *no* let-ins *)

Inductive subs {cf:checker_flags} (Σ : global_env_ext) (Γ : context) : list term -> context -> Type :=
| emptys : subs Σ Γ [] []
| cons_ass Δ s na t T : subs Σ Γ s Δ -> Σ ;;; Γ |- t : subst0 s T -> subs Σ Γ (t :: s) (Δ ,, vass na T).

Lemma subs_length {cf:checker_flags} {Σ} {Γ s Δ} : subs Σ Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; auto. f_equal. auto.
Qed.

(** Well-typed substitution into a context with let-ins *)

Inductive subslet {cf:checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptyslet : subslet Σ Γ [] []
| cons_let_ass Δ s na t T : subslet Σ Γ s Δ ->
              Σ ;;; Γ |- t : subst0 s T ->
             subslet Σ Γ (t :: s) (Δ ,, vass na T)
| cons_let_def Δ s na t T :
    subslet Σ Γ s Δ ->
    Σ ;;; Γ |- subst0 s t : subst0 s T ->
    subslet Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T).

#[global] Hint Constructors subslet : pcuic.

Lemma subslet_def {cf} {Σ : global_env_ext} {Γ Δ s na t T t'} :
  subslet Σ Γ s Δ ->
  Σ;;; Γ |- subst0 s t : subst0 s T ->
  t' = subst0 s t ->
  subslet Σ Γ (t' :: s) (Δ ,, vdef na t T).
Proof.
  now intros sub Ht ->; constructor.
Qed.

Lemma subslet_ass_tip {cf} {Σ : global_env_ext} {Γ na t T} :
  Σ;;; Γ |- t : T ->
  subslet Σ Γ [t] [vass na T].
Proof.
  intros; repeat constructor.
  now rewrite !subst_empty.
Qed.

Lemma subslet_def_tip {cf} {Σ : global_env_ext} {Γ na t T} :
  Σ;;; Γ |- t : T ->
  subslet Σ Γ [t] [vdef na t T].
Proof.
  intros; apply subslet_def; try constructor.
  all:now rewrite !subst_empty.
Qed.

#[global] Hint Resolve subslet_ass_tip subslet_def_tip : pcuic.

Lemma subslet_nth_error {cf:checker_flags} {Σ Γ s Δ decl n} :
  subslet Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  ∑ t, nth_error s n = Some t ×
  let ty := subst0 (skipn (S n) s) (decl_type decl) in
  Σ ;;; Γ |- t : ty ×
  match decl_body decl return Type with
  | Some t' =>
    let b := subst0 (skipn (S n) s) t' in
    (t = b)
  | None => unit
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. exists t; split; auto.
    simpl. split; auto.
  - intros. destruct decl as [na' [b|] ty]; cbn in *.
    + specialize (IHX _ H) as [t' [hnth [hty heq]]]. exists t'; intuition auto.
    + now apply IHX.
  - intros [= <-]. eexists; split; eauto.
    simpl. split; auto.
  - apply IHX.
Qed.

Lemma subslet_length {cf:checker_flags} {Σ Γ s Δ} : subslet Σ Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; f_equal; auto.
Qed.

Lemma subst_decl_closed n k d : closed_decl k d -> subst_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /subst_decl /map_decl /=.
  - move/andb_and => [cb cty]. rewrite !subst_closedn //.
  - move=> cty; now rewrite !subst_closedn //.
Qed.

Lemma closed_ctx_subst n k ctx : closed_ctx ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  rewrite closedn_ctx_cons.
  move/andb_and => /= [Hctx Hd].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
  now apply: closed_decl_upwards.
Qed.

Lemma closed_tele_subst n k ctx :
  closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => subst_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite test_context_k_eq /mapi. simpl. generalize 0.
  induction ctx using rev_ind; try easy.
  move=> n0.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move/andb_and => [closedx Hctx].
  rewrite subst_decl_closed //.
  - rewrite (closed_decl_upwards n0) //; lia.
  - f_equal. now rewrite IHctx.
Qed.

Lemma map_vass_map_def_subst g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (subst n k) g) l)) =
  (mapi (fun i d => map_decl (subst n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite commut_lift_subst_rec. 1: lia. f_equal; lia.
Qed.

Lemma subst_length {cf:checker_flags} Σ Γ s Γ' : subs Σ Γ s Γ' -> #|s| = #|Γ'|.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma subs_nth_error_ge {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subs Σ Γ s Γ' ->
  #|Γ' ,,, Γ''| <= v ->
  nth_error (Γ ,,, Γ' ,,, Γ'') v =
  nth_error (Γ ,,, subst_context s 0 Γ'') (v - #|Γ'|).
Proof.
  simpl.
  intros. rewrite app_context_length in H.
  rewrite !nth_error_app_ge; autorewrite with wf; f_equal; try lia.
Qed.

Lemma nth_error_subst_context (Γ' : context) s (v : nat) k :
    nth_error (subst_context s k Γ') v =
    option_map (subst_decl s (#|Γ'| - S v + k)) (nth_error Γ' v).
Proof.
  induction Γ' in v |- *; intros.
  - simpl. unfold subst_context, fold_context_k; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct v; rewrite subst_context_snoc.
    + simpl. repeat f_equal; try lia.
    + simpl. rewrite IHΓ'; simpl in *. lia_f_equal.
Qed.

Lemma subs_nth_error_lt {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subs Σ Γ s Γ' ->
  v < #|Γ''| ->
  nth_error (Γ ,,, subst_context s 0 Γ'') v =
  option_map (map_decl (subst s (#|Γ''| - S v))) (nth_error (Γ ,,, Γ' ,,, Γ'') v).
Proof.
  simpl. intros Hs Hv.
  rewrite !nth_error_app_lt; autorewrite with wf; f_equal; try lia.
  erewrite nth_error_subst_context. f_equal. unfold subst_decl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma subslet_nth_error_lt {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subslet Σ Γ s Γ' ->
  v < #|Γ''| ->
  nth_error (Γ ,,, subst_context s 0 Γ'') v =
  option_map (map_decl (subst s (#|Γ''| - S v))) (nth_error (Γ ,,, Γ' ,,, Γ'') v).
Proof.
  simpl. intros Hs Hv.
  rewrite !nth_error_app_lt; autorewrite with wf; f_equal; try lia.
  erewrite nth_error_subst_context. f_equal. unfold subst_decl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma expand_lets_subst_comm' Γ s k x :
  closedn (k + #|Γ|) x ->
  expand_lets (subst_context s k Γ) x = subst s (k + context_assumptions Γ) (expand_lets Γ x).
Proof.
  unfold expand_lets, expand_lets_k; simpl; intros clx.
  len.
  rewrite !subst_extended_subst.
  rewrite distr_subst. f_equal.
  len. rewrite subst_closedn //.
  rewrite Nat.add_assoc; eapply closedn_lift.
  now rewrite Nat.add_comm.
Qed.

Notation subst_predicate s := (map_predicate_k id (subst s)).

Lemma subst_iota_red s p k pars args br :
  #|skipn pars args| = context_assumptions br.(bcontext) ->
  closedn_ctx #|pparams p| (bcontext br) ->
  subst s k (iota_red pars p args br) =
  iota_red pars (subst_predicate s k p) (List.map (subst s k) args) (map_branch_k (subst s) id k br).
Proof.
  intros hctx cl. rewrite !subst_inst.
  rewrite inst_iota_red //.
  f_equal.
  - rewrite /inst_predicate /map_predicate_k.
    f_equal.
    * apply map_ext => ?. now rewrite subst_inst.
    * now rewrite subst_inst up_Upn Upn_Upn.
  - eapply map_ext => ?. now rewrite subst_inst.
  - now rewrite /inst_branch /map_branch_k subst_inst up_Upn Upn_Upn.
Qed.

Lemma subst_unfold_fix n k mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  move=> [= <- <-] /=. f_equal. f_equal.
  solve_all.
  erewrite (distr_subst_rec _ _ _ k 0).
  rewrite fix_subst_length. simpl. f_equal.
  unfold fix_subst. rewrite !length_map.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
#[global]
Hint Resolve subst_unfold_fix : core.

Lemma subst_unfold_cofix n k mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. do 2 f_equal. solve_all.
  erewrite (distr_subst_rec _ _ _ k 0).
  rewrite cofix_subst_length. simpl. f_equal.
  unfold cofix_subst. rewrite !length_map.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
#[global]
Hint Resolve subst_unfold_cofix : core.

Lemma decompose_app_rec_subst n k t l :
  let (f, a) := decompose_app_rec t l in
  subst n k f = f ->
  decompose_app_rec (subst n k t) (map (subst n k) l)  = (f, map (subst n k) a).
Proof.
  induction t in k, l |- *; simpl; auto; try congruence.

  - destruct Nat.leb; try reflexivity.
    destruct nth_error.
    + simpl. intros ->. simpl. reflexivity.
    + intros ->. simpl. reflexivity.
  - specialize (IHt1 k (t2 :: l)).
    destruct decompose_app_rec. intros H. rewrite IHt1; auto.
Qed.

Lemma decompose_app_subst n k t f a :
  decompose_app t = (f, a) -> subst n k f = f ->
  decompose_app (subst n k t) = (subst n k f, map (subst n k) a).
Proof.
  generalize (decompose_app_rec_subst n k t []).
  unfold decompose_app. destruct decompose_app_rec.
  move=> Heq [= <- <-] Heq'. now rewrite Heq' (Heq Heq').
Qed.
#[global]
Hint Rewrite decompose_app_subst using auto : lift.

Lemma subst_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (subst n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl. intros.
  unfold isConstruct_app in *.
  destruct (decompose_app t) eqn:Heq. eapply decompose_app_subst in Heq as ->.
  - destruct t0; try discriminate || reflexivity.
  - destruct t0; try discriminate || reflexivity.
Qed.
#[global]
Hint Resolve subst_is_constructor : core.
#[global]
Hint Constructors All_local_env : core.

Lemma typed_subst `{checker_flags} Σ Γ t T n k :
  wf Σ.1 -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> subst n k T = T /\ subst n k t = t.
Proof.
  intros wfΣ Hk Hty.
  pose proof (typing_wf_local Hty).
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ [Hcl [Ht HT]%andb_and]].
  pose proof (closed_upwards k Ht).
  simpl in *. forward H0 by lia.
  pose proof (closed_upwards k HT).
  simpl in *. forward H1 by lia.
  apply (subst_closedn n) in H0; apply (subst_closedn n) in H1; auto.
Qed.

Lemma subst_wf_local `{checker_flags} Σ Γ n k :
  wf Σ.1 ->
  wf_local Σ Γ ->
  subst_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold subst_context, snoc; rewrite fold_context_k_snoc0;
    auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl.
  - destruct t0 as (_ & s & Ht & _). unfold vass. simpl. f_equal.
    eapply typed_subst; eauto. lia.
  - unfold vdef.
    destruct t0 as (Hb & s & Ht & _). cbn in Hb.
    f_equal.
    + f_equal. eapply typed_subst; eauto. lia.
    + eapply typed_subst; eauto. lia.
Qed.

Lemma subst_declared_constant `{H:checker_flags} Σ cst decl n k u :
  wf Σ ->
  declared_constant Σ cst decl ->
  map_constant_body (subst n k) (map_constant_body (subst_instance u) decl) =
  map_constant_body (subst_instance u) decl.
Proof.
  intros. unshelve eapply declared_constant_to_gen in H0; eauto.
  eapply declared_decl_closed in H0 as [Hb Ht]%andb_and; eauto.
  unfold map_constant_body. cbn in *.
  f_equal.
  - rewrite <- (closedn_subst_instance 0 _ u) in Ht.
    apply subst_closedn; eauto using closed_upwards with arith wf.
  - destruct cst_body; cbn in *; auto.
    f_equal.
    rewrite <- (closedn_subst_instance 0 _ u) in Hb.
    eapply subst_closedn; eauto using closed_upwards with arith wf.
Qed.

Definition subst_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => subst n (k' + k)) m.

Lemma subst_fix_context:
  forall (mfix : list (def term)) n (k : nat),
    fix_context (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) =
    subst_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def_subst rev_mapi.
  fold (fix_context mfix).
  rewrite (subst_context_alt n k (fix_context mfix)).
   now rewrite /subst_decl mapi_length fix_context_length.
Qed.

(* Lemma subst_declared_minductive {cf:checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive Σ cst decl ->
  subst_mutual_inductive_body n k decl = decl.
Proof.
  intros wfΣ Hdecl.
  pose proof (on_declared_minductive wfΣ Hdecl). apply onNpars in X.
  apply (declared_inductive_closed (Σ:=(empty_ext Σ))) in Hdecl; auto.
  move: Hdecl.
  rewrite /closed_inductive_decl /lift_mutual_inductive_body.
  destruct decl; simpl.
  move/andb_and => [clpar clbodies]. f_equal.
  - now rewrite [fold_context_k _ _]closed_ctx_subst.
  - eapply forallb_All in clbodies.
    eapply Alli_mapi_id.
    * eapply (All_Alli clbodies). intros; eauto.
      intros. eapply H.
    * simpl; intros.
      move: H. rewrite /closed_inductive_body.
      destruct x; simpl. move=> /andb_and[/andb_and [ci ct] cp].
      f_equal.
      + rewrite subst_closedn; eauto.
        eapply closed_upwards; eauto; lia.
      + eapply All_map_id. eapply forallb_All in ct.
        eapply (All_impl ct). intros x.
        destruct x as [[id ty] arg]; unfold on_pi2; intros c; simpl; repeat f_equal.
        apply subst_closedn. unfold cstr_type in c; simpl in c.
        eapply closed_upwards; eauto; lia.
      + simpl in X. rewrite -X in cp.
        eapply forallb_All in cp. eapply All_map_id; eauto.
        eapply (All_impl cp); pcuicfo.
        destruct x; unfold on_snd; simpl; f_equal.
        apply subst_closedn. rewrite context_assumptions_fold.
        eapply closed_upwards; eauto; lia.
Qed.

Lemma subst_declared_inductive {cf:checker_flags} ind Σ mdecl idecl n k :
  wf Σ ->
  declared_inductive Σ ind mdecl idecl ->
  map_one_inductive_body (context_assumptions mdecl.(ind_params))
                         (length (arities_context mdecl.(ind_bodies)))
                         (fun k' => subst n (k' + k)) (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
   eapply (subst_declared_minductive _ _ _ n k) in Hmdecl. 2: auto.
  unfold subst_mutual_inductive_body in Hmdecl.
  destruct mdecl. simpl in *.
  injection Hmdecl. intros Heq.
  clear Hmdecl.
  pose proof Hidecl as Hidecl'.
  rewrite <- Heq in Hidecl'.
  rewrite nth_error_mapi in Hidecl'.
  clear Heq.
  unfold option_map in Hidecl'. rewrite Hidecl in Hidecl'.
  congruence.
Qed.

Lemma subst0_inds_subst ind u mdecl n k t :
  (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
          (subst n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  subst n k (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
  pose proof (distr_subst_rec t (inds (inductive_mind ind) u (ind_bodies mdecl)) n k 0).
  simpl in H. rewrite H.
  unfold arities_context. rewrite length_rev_map inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma subst_declared_constructor {cf:checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ -> declared_constructor Σ c mdecl idecl cdecl ->
  subst (map (subst_instance u) n) k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
  eapply (subst_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  unfold type_of_constructor. destruct cdecl as [[id t'] arity].
  destruct idecl; simpl in *.
  injection Hidecl. intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H0 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros.
  rewrite <- H2 at 2.
  rewrite <- subst0_inds_subst. f_equal.
  now rewrite <- subst_instance_subst.
Qed.

Lemma subst_declared_projection {cf:checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection Σ c mdecl idecl pdecl ->
  on_snd (subst n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros.
  eapply (declared_projection_closed (Σ:=empty_ext Σ)) in H; auto.
  unfold on_snd. simpl.
  rewrite subst_closedn.
  - eapply closed_upwards; eauto; try lia.
  - destruct pdecl; reflexivity.
Qed.
*)
Lemma subst_destArity ctx t n k :
  match destArity ctx t with
  | Some (args, s) =>
    destArity (subst_context n k ctx) (subst n (#|ctx| + k) t) = Some (subst_context n k args, s)
  | None => True
  end.
Proof.
  revert ctx.
  induction t in n, k |- * using term_forall_list_ind; intros ctx; simpl; trivial.
  - move: (IHt2 n k (ctx,, vass n0 t1)).
    now rewrite subst_context_snoc /= /subst_decl /map_decl /vass /=.
  - move: (IHt3 n k (ctx,, vdef n0 t1 t2)).
    now rewrite subst_context_snoc /= /subst_decl /map_decl /vass /=.
Qed.

Lemma decompose_prod_n_assum0 ctx t : decompose_prod_n_assum ctx 0 t = Some (ctx, t).
Proof. destruct t; simpl; reflexivity. Qed.
(*
Lemma subst_instantiate_params_subst n k params args s t :
  forall s' t',
    instantiate_params_subst params args s t = Some (s', t') ->
    instantiate_params_subst
      (mapi_rec (fun k' decl => subst_decl n (k' + k) decl) params #|s|)
      (map (subst n k) args) (map (subst n k) s) (subst n (#|s| + k) t) =
    Some (map (subst n k) s', subst n (#|s| + k + #|params|) t').
Proof.
  induction params in args, t, n, k, s |- *; intros ctx' t'.
  - destruct args; simpl; rewrite ?Nat.add_0_r; try congruence.
  - simpl.
    destruct a as [na [body|] ty]; simpl; try congruence;
    destruct t; try congruence.
    -- intros Ht'.
       specialize (IHparams n k _ _ _ _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       rewrite <- IHparams. f_equal.
       now rewrite distr_subst.
    -- intros Ht'. destruct args; try congruence. simpl.
       specialize (IHparams n k _ _ _ _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       now rewrite <- IHparams.
Qed.

Lemma subst_instantiate_params n k params args t ty :
  closed_ctx params ->
  instantiate_params params args t = Some ty ->
  instantiate_params params (map (subst n k) args) (subst n k t) = Some (subst n k ty).
Proof.
  unfold instantiate_params.
  move/(closed_tele_subst n k params)=> Heq.
  rewrite -{2}Heq //.
  specialize (subst_instantiate_params_subst n k (List.rev params) args [] t).
  move=> /= Heq'.
  case E: (instantiate_params_subst (List.rev params) args)=> /= [[l' t']|] /= //.
  specialize (Heq' _ _ E). rewrite Heq'. move=> [= <-]. f_equal.
  rewrite distr_subst //.
  move/instantiate_params_subst_length: E => -> /=. do 2 f_equal. lia.
Qed.
Hint Rewrite subst_instantiate_params : lift.
*)

Lemma to_extended_list_k_map_subst:
  forall n (k : nat) (c : context) k',
    #|c| + k' <= k ->
    to_extended_list_k c k' = map (subst n k) (to_extended_list_k c k').
Proof.
  intros n k c k'.
  pose proof (to_extended_list_k_spec c k').
  symmetry. solve_all.
  destruct H as [x' [-> Hx']]. intuition. simpl.
  destruct (leb_spec_Set k x').
  - lia.
  - reflexivity.
Qed.

Lemma wf_arities_context' {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {mind mdecl} :
  on_inductive cumulSpec0 (lift_typing typing) Σ mind mdecl ->
  wf_local Σ (arities_context (ind_bodies mdecl)).
Proof.
  intros Hdecl.
  apply onInductives in Hdecl.
  unfold arities_context.
  revert Hdecl.
  induction (ind_bodies mdecl) using rev_ind. 1: constructor.
  intros Ha.
  rewrite rev_map_app.
  simpl. apply Alli_app in Ha as [Hl Hx].
  inv Hx. clear X0.
  apply onArity in X as (_ & s & Hs & _ & Her).
  specialize (IHl Hl).
  econstructor; eauto.
  fold (arities_context l) in *.
  cbn in Her.
  repeat (eexists; cbn; tea).
  now eapply weaken_ctx in Hs.
Qed.

Lemma wf_arities_context {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mind mdecl} :
  declared_minductive Σ mind mdecl -> wf_local (Σ, ind_universes mdecl) (arities_context mdecl.(ind_bodies)).
Proof.
  intros Hdecl.
  eapply declared_minductive_inv in Hdecl. 2:exact weaken_env_prop_typing. all:eauto.
  eapply wf_arities_context'; eauto.
Qed.

Lemma on_constructor_closed_arities {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mind mdecl idecl indices cdecl cs} :
  on_constructor cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind mind) indices idecl cdecl cs ->
  closedn #|arities_context (ind_bodies mdecl)| cdecl.(cstr_type).
Proof.
  intros [? ? (_ & s & Hs & _) _ _ _ _].
  pose proof (typing_wf_local Hs).
  destruct cdecl as [id cty car].
  apply subject_closed in Hs; eauto.
Qed.

Lemma on_constructor_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mind mdecl u idecl indices cdecl cs} :
  on_constructor cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind mind) indices idecl cdecl cs ->
  let cty := subst0 (inds (inductive_mind mind) u (ind_bodies mdecl))
                    (subst_instance u cdecl.(cstr_type))
  in closed cty.
Proof.
  intros [? ? (_ & s & Hs & _) _ _ _ _].
  pose proof (typing_wf_local Hs).
  destruct cdecl as [id cty car].
  apply subject_closed in Hs; eauto.
  rewrite arities_context_length in Hs.
  simpl in *.
  eapply (closedn_subst _ 0 0).
  - clear. unfold inds.
    induction #|ind_bodies mdecl|; simpl; try constructor; auto.
  - simpl. now rewrite -> inds_length, closedn_subst_instance.
Qed.

Lemma subst_cstr_concl_head ind u mdecl (arity : context) args :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance u (mkApps head (to_extended_list_k (ind_params mdecl) #|arity| ++ args)))
  = mkApps (tInd ind u) (to_extended_list_k (ind_params mdecl) #|arity| ++
                        map (subst s (#|arity| + #|ind_params mdecl|)) (map (subst_instance u) args)).
Proof.
  intros.
  rewrite subst_instance_mkApps subst_mkApps.
  f_equal.
  - subst head. simpl subst_instance.
    rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
    subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
    elim nth_error_spec.
    + intros. simpl.
      f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
    + rewrite List.length_rev. lia.
  - rewrite !map_app. f_equal.
    rewrite map_subst_instance_to_extended_list_k.
    erewrite to_extended_list_k_map_subst at 2.
    + now rewrite Nat.add_comm.
    + lia.
Qed.

Lemma subst_to_extended_list_k s k args ctx :
  make_context_subst (List.rev ctx) args [] = Some s ->
  map (subst s k) (to_extended_list_k ctx k) = map (lift0 k) args.
Proof.
  move/make_context_subst_spec. rewrite List.rev_involutive.
  move=> H; induction H; simpl; auto.
  - rewrite map_app -IHcontext_subst //.
    rewrite to_extended_list_k_cons /= !map_app.
    f_equal.
    + rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
      pose proof (to_extended_list_k_spec Γ k).
      solve_all. destruct H0 as [n [-> Hn]].
      rewrite /lift (subst_app_decomp [a] s k); auto with wf.
      rewrite subst_rel_gt.
      * simpl. lia.
      * unf_term. repeat (f_equal; simpl; try lia).
    + now rewrite /map (subst_rel_eq _ _ 0 a).
  - rewrite -IHcontext_subst // to_extended_list_k_cons /=.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    solve_all. destruct H0 as [n [-> Hn]].
    rewrite /lift (subst_app_decomp [subst0 s b] s k); auto with wf.
    rewrite subst_rel_gt.
    + simpl; lia.
    + unf_term. repeat (f_equal; simpl; try lia).
Qed.


Lemma Alli_map_option_out_mapi_Some_spec' {A B} (f g : nat -> A -> option B) h l t P :
  All P l ->
  (forall i x t, P x -> f i x = Some t -> g i x = Some (h t)) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some (map h t).
Proof.
  unfold mapi. generalize 0.
  move => n Ha Hfg. move: t.
  induction Ha in n |- *; try constructor; auto.
  - destruct t; cbnr; discriminate.
  - move=> t /=. case E: (f n x) => [b|]; try congruence.
    rewrite (Hfg n _ _ p E).
    case E' : map_option_out => [b'|]; try congruence.
    move=> [= <-]. now rewrite (IHHa _ _ E').
Qed.

(*
Lemma subst_build_case_predicate_type ind mdecl idecl u params ps pty n k :
  closed_ctx (subst_instance u (ind_params mdecl)) ->
  closed (ind_type idecl) ->
  build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
  build_case_predicate_type ind mdecl
    (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            (length (arities_context (ind_bodies mdecl))) (fun k' => subst n (k' + k))
            (inductive_ind ind) idecl)
    (map (subst n k) params) u ps
  = Some (subst n k pty).
Proof.
  intros closedparams closedtype.
  unfold build_case_predicate_type; simpl.
  case_eq (instantiate_params (subst_instance u (ind_params mdecl)) params
                              (subst_instance u (ind_type idecl)));
    [|discriminate ].
  intros ipars Hipars.
  apply (subst_instantiate_params n k) in Hipars; tas.
  rewrite ind_type_map. simpl.
  rewrite subst_closedn in Hipars.
  { rewrite closedn_subst_instance; eapply closed_upwards; tea; lia. }
  rewrite subst_closedn; [eapply closed_upwards; tea; lia|].
  rewrite Hipars.
  specialize (subst_destArity [] ipars n k);
    destruct (destArity [] ipars) as [[ctx s]|]; [|discriminate].
  simpl. cbn. move => -> /some_inj-HH. simpl. f_equal.
  etransitivity.
  2: exact (f_equal (subst n k) HH).
  rewrite subst_it_mkProd_or_LetIn. unf_term. simpl. f_equal. f_equal.
  { destruct idecl; reflexivity. }
  rewrite subst_mkApps; simpl. f_equal.
  rewrite map_app; f_equal.
  - rewrite !map_map; apply map_ext; clear; intro.
    rewrite subst_context_length.
    rewrite -> commut_lift_subst_rec by lia.
    f_equal. lia.
  - rewrite /to_extended_list to_extended_list_k_subst.
    rewrite <- to_extended_list_k_map_subst by lia. reflexivity.
Qed.

Lemma subst_build_branches_type {cf:checker_flags}
      n k Σ ind mdecl idecl indices args u p brs cs :
  wf Σ ->
  declared_inductive Σ ind mdecl idecl ->
  closed_ctx (subst_instance u (ind_params mdecl)) ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind ind) mdecl ->
  on_constructors (lift_typing typing) (Σ, ind_universes mdecl)
                  mdecl (inductive_ind ind) idecl indices (ind_ctors idecl) cs ->
  map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
  map_option_out (build_branches_type ind mdecl
         idecl (map (subst n k) args) u (subst n k p)) =
         Some (map (on_snd (subst n k)) brs).
Proof.
  intros wfΣ wfidecl closedparams onmind Honcs.
  rewrite !build_branches_type_. cbn.
  eapply Alli_map_option_out_mapi_Some_spec'.
  { eapply All2_All_left; tea. intros x y u'; exact (y; u'). }
  clear Honcs brs.
  intros j [[id t] i] [t' k'] [cs' Honc].
  case_eq (instantiate_params (subst_instance u (ind_params mdecl)) args
                              (subst0 (inds (inductive_mind ind) u
                                            (ind_bodies mdecl))
                                      (subst_instance u t)));
    [|discriminate].
  intros ty Heq; cbn.
  pose proof (on_constructor_closed wfΣ (u:=u) Honc) as clt; cbn in clt.
  eapply (closed_upwards k) in clt; try lia.
  remember (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
                   (subst_instance u t)) as ty'.
  apply (subst_instantiate_params n k) in Heq as Heq'; tas.
  erewrite subst_closedn in Heq'; tas.
  rewrite Heq'.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [Hty [Hsubst Ht0]]]]].
  subst ty; simpl.
  rewrite Heqty' in Hty.
  destruct Honc as [Hcstr_args ? cdecl_eq Hty' _ _]; unfold cstr_type in *; simpl in *.
  rewrite cdecl_eq in Hty.
  rewrite -> !subst_instance_it_mkProd_or_LetIn in Hty.
  rewrite !subst_it_mkProd_or_LetIn in Hty.
  assert (H0: #|subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
                (subst_instance u (ind_params mdecl))|
          = #|subst_instance u (ind_params mdecl)|). {
    now rewrite subst_context_length. }
  rewrite <- H0 in Hty.
  rewrite decompose_prod_n_assum_it_mkProd in Hty.
  injection Hty. clear Hty.
  intros Heqty'' <-. revert Heqty''.
  rewrite !subst_instance_length Nat.add_0_r.
  rewrite subst_context_length subst_instance_length.
  rewrite (subst_cstr_concl_head ind u mdecl cs'.(cstr_args) cs'.(cstr_indices)).
  { destruct wfidecl as [Hmdecl Hnth].
    now apply nth_error_Some_length in Hnth.
  }
  intros <-. rewrite !subst_it_mkProd_or_LetIn !subst_mkApps /=.
  rewrite !decompose_prod_assum_it_mkProd /=;
          try by rewrite is_ind_app_head_mkApps.
  rewrite !decompose_app_mkApps; try by reflexivity.
  simpl. rewrite !map_app !subst_context_length
                 !subst_instance_length Nat.add_0_r.
  eapply subst_to_extended_list_k with (k:=#|cs'.(cstr_args)|) in Hsubst as XX.
  rewrite map_subst_instance_to_extended_list_k in XX.
  rewrite !XX; clear XX.
  apply make_context_subst_spec in Hsubst as Hsubst'.
  rewrite rev_involutive in Hsubst'.
  pose proof (context_subst_assumptions_length Hsubst') as H1.
  case E: chop => [l l'].
  have chopm := (chop_map _ _ _ _ _ E).
  move: E chopm.
  rewrite chop_n_app ?length_map. {
    rewrite <- H1. apply onNpars in onmind.
    now rewrite context_assumptions_subst_instance. }
  move=> [= <- <-] chopm.
  move: {chopm}(chopm _ (subst n (#|cs'.(cstr_args)| + k))).
  rewrite map_app.
  move=> chopm; rewrite {}chopm /=.
  inversion 1; subst. f_equal. unfold on_snd; cbn; f_equal.
  rewrite !app_nil_r /on_snd /=.
  rewrite subst_it_mkProd_or_LetIn !subst_context_length !subst_mkApps
          !subst_instance_length !map_app.
  f_equal. f_equal.
  -- rewrite -> commut_lift_subst_rec by lia. arith_congr.
  -- f_equal. simpl. f_equal.
     rewrite !subst_mkApps /= !map_app. f_equal.
     f_equal.
     rewrite /to_extended_list -to_extended_list_k_map_subst.
     ++ rewrite !subst_context_length subst_instance_length. lia.
     ++ now rewrite to_extended_list_k_subst.
Qed.
*)

#[global]
Hint Unfold subst1 : subst.
#[global]
Hint Rewrite subst_mkApps distr_subst: subst.

Inductive untyped_subslet (Γ : context) : list term -> context -> Type :=
| untyped_emptyslet : untyped_subslet Γ [] []
| untyped_cons_let_ass Δ s na t T :
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ (t :: s) (Δ ,, vass na T)
| untyped_cons_let_def Δ s na t T :
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ (subst0 s t :: s) (Δ ,, vdef na t T).

Lemma subslet_untyped_subslet {cf:checker_flags} Σ Γ s Γ' : subslet Σ Γ s Γ' -> untyped_subslet Γ s Γ'.
Proof.
  induction 1; constructor; auto.
Qed.
Coercion subslet_untyped_subslet : subslet >-> untyped_subslet.

Lemma decompose_prod_assum_it_mkProd_or_LetIn ctx t ctx' t' :
 decompose_prod_assum ctx t = (ctx', t') ->
 it_mkProd_or_LetIn ctx t = it_mkProd_or_LetIn ctx' t'.
Proof.
  induction t in ctx, ctx', t' |- *; simpl; try intros [= -> <-]; auto.
  - intros H. now apply IHt2 in H.
  - intros H. now apply IHt3 in H.
Qed.

Inductive decompose_prod_assum_graph : term -> (context * term) -> Type :=
| decompose_arity ctx t : decompose_prod_assum_graph (it_mkProd_or_LetIn ctx t) (ctx, t).

Lemma decompose_prod_assum_spec ctx t :
  decompose_prod_assum_graph (it_mkProd_or_LetIn ctx t) (decompose_prod_assum ctx t).
Proof.
 induction t in ctx |- *; simpl; try constructor 1.
 - specialize (IHt2 (vass na t1 :: ctx)).
   apply IHt2.
 - apply (IHt3 (vdef na t1 t2 :: ctx)).
Qed.

Lemma subst_decompose_prod_assum_rec ctx t s k :
  let (ctx', t') := decompose_prod_assum ctx t in
  ∑ ctx'' t'',
    (decompose_prod_assum [] (subst s (#|ctx'| + k) t') = (ctx'', t'')) *
  (decompose_prod_assum (subst_context s k ctx) (subst s (length ctx + k) t) =
  (subst_context s k ctx' ,,, ctx'', t'')).
Proof.
  induction t in ctx, k |- *; simpl; try solve [ eexists _, _; pcuicfo ].
  - elim: leb_spec_Set => comp.
    + destruct (nth_error s (n - (#|ctx| + k))) eqn:Heq.
      * destruct decompose_prod_assum eqn:Heq'.
        eexists _, _; intuition eauto.
        now rewrite decompose_prod_assum_ctx Heq'.
      * eexists _,_; pcuicfo.
    + eexists _,_; pcuicfo.
  - destruct decompose_prod_assum eqn:Heq.
    rewrite decompose_prod_assum_ctx in Heq.
    destruct (decompose_prod_assum [] t2) eqn:Heq'.
    noconf Heq.
    specialize (IHt2 ctx (S k)).
    rewrite decompose_prod_assum_ctx in IHt2.
    rewrite Heq' in IHt2.
    destruct IHt2 as [ctx'' [t'' [eqt eqt2]]].
    exists ctx'', t''. rewrite -eqt.
    split.
    * unfold snoc; simpl. rewrite !app_context_length.
      simpl. lia_f_equal.
    * rewrite decompose_prod_assum_ctx in eqt2.
      rewrite decompose_prod_assum_ctx.
      rewrite Nat.add_succ_r in eqt2.
      destruct (decompose_prod_assum   []  (subst s _ t2)) eqn:Heq''.
      rewrite subst_context_app in eqt2.
      rewrite !subst_context_app subst_context_snoc.
      injection eqt2. intros <-.
      intros eqctx. f_equal.
      unfold app_context in eqctx.
      rewrite app_assoc in eqctx.
      apply app_inv_tail in eqctx.
      subst c. rewrite app_context_assoc.
      unfold snoc. simpl. lia_f_equal.
  - destruct decompose_prod_assum eqn:Heq.
    rewrite decompose_prod_assum_ctx in Heq.
    destruct (decompose_prod_assum [] t3) eqn:Heq'.
    noconf Heq.
    specialize (IHt3 ctx (S k)).
    rewrite decompose_prod_assum_ctx in IHt3.
    rewrite Heq' in IHt3.
    destruct IHt3 as [ctx'' [t'' [eqt eqt3]]].
    exists ctx'', t''. rewrite -eqt.
    split.
    * unfold snoc; simpl. rewrite !app_context_length.
      simpl. lia_f_equal.
    * rewrite decompose_prod_assum_ctx in eqt3.
      rewrite decompose_prod_assum_ctx.
      rewrite Nat.add_succ_r in eqt3.
      destruct (decompose_prod_assum   []  (subst s _ t3)) eqn:Heq''.
      rewrite subst_context_app in eqt3.
      rewrite !subst_context_app subst_context_snoc.
      injection eqt3. intros <-.
      intros eqctx. f_equal.
      unfold app_context in eqctx.
      rewrite app_assoc in eqctx.
      apply app_inv_tail in eqctx.
      subst c. rewrite app_context_assoc.
      unfold snoc. simpl. lia_f_equal.
Qed.
(*

Lemma subst_decompose_prod_assum_rec ctx t s k :
  let (ctx', t') := decompose_prod_assum ctx t in
  let (ctx'', t'') := decompose_prod_assum (subst_context s k ctx) (subst s (length ctx + k) t) in
  subst s k (it_mkProd_or_LetIn ctx' t') = it_mkProd_or_LetIn ctx'' t''.
Proof.
  rewrite decompose_prod_assum_ctx.
  destruct decompose_prod_assum eqn:Heq.
  destruct (decompose_prod_assum (subst_context _ _ _) _) eqn:Heq'.
  apply decompose_prod_assum_it_mkProd_or_LetIn in Heq.
  apply decompose_prod_assum_it_mkProd_or_LetIn in Heq'.
  rewrite subst_it_mkProd_or_LetIn.
  rewrite subst_context_app.
  rewrite it_mkProd_or_LetIn_app.
  rewrite -Heq'. f_equal.
  simpl in Heq.
  rewrite Heq.
  rewrite subst_it_mkProd_or_LetIn.
  rewrite app_context_length.
  lia_f_equal.
Qed. *)

Arguments Nat.sub : simpl nomatch.

Lemma assumption_context_skipn Γ n :
  assumption_context Γ ->
  assumption_context (skipn n Γ).
Proof.
  induction 1 in n |- *; simpl.
  - destruct n; constructor.
  - destruct n.
    * rewrite skipn_0. constructor; auto.
    * now rewrite skipn_S.
Qed.

#[global]
Hint Rewrite idsn_length : len.

Lemma subst_fn_eq s s' x : s = s' -> subst_fn s x = subst_fn s' x.
Proof.
  intros -> ; reflexivity.
Qed.

Lemma map_option_out_impl {A B} (l : list A) (f g : A -> option B) x :
  (forall x y, f x = Some y -> g x = Some y) ->
  map_option_out (map f l) = Some x ->
  map_option_out (map g l) = Some x.
Proof.
  intros Hfg.
  induction l in x |- *; simpl; auto.
  destruct (f a) eqn:fa.
  - rewrite (Hfg _ _ fa).
    move: IHl; destruct map_option_out.
    * move=> H'. specialize (H' _ eq_refl).
      rewrite H'. congruence.
    * discriminate.
  - discriminate.
Qed.

Lemma substitution_check_one_fix s k mfix inds :
  map_option_out (map check_one_fix mfix) = Some inds ->
  map_option_out (map (fun x : def term =>
    check_one_fix (map_def (subst s k) (subst s (#|mfix| + k)) x)) mfix) = Some inds.
Proof.
  apply map_option_out_impl.
  move=> [na ty def rarg] /=.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  destruct (decompose_prod_assum [] ty) eqn:decty.
  noconf decomp. rewrite !app_context_nil_l.
  pose proof (subst_decompose_prod_assum_rec [] ty s k).
  rewrite decty in X.
  destruct X as [ctx'' [t'' [dect decty']]].
  rewrite subst_context_nil in decty'; simpl in decty'.
  rewrite decty'. intros ind.
  rewrite smash_context_app.
  rewrite (smash_context_acc _ (smash_context _ _)).
  rewrite List.rev_app_distr.
  destruct (nth_error_spec (List.rev (smash_context [] c0)) rarg) => /= //;
  autorewrite with len in l; simpl in *.
  rewrite nth_error_app_lt; autorewrite with len; simpl; try lia.
  rewrite (smash_context_subst []) /=.
  rewrite nth_error_rev_inv; autorewrite with len; simpl; try lia.
  rewrite nth_error_subst_context /=.
  autorewrite with len.
  rewrite nth_error_rev_inv in e; autorewrite with len; auto.
  autorewrite with len in e. simpl in e. rewrite e.
  simpl.
  destruct (decompose_app (decl_type x)) eqn:Happ.
  destruct t0; try discriminate. simpl in *.
  erewrite decompose_app_subst; eauto. simpl. auto.
Qed.

Lemma substitution_check_one_cofix s k mfix inds :
  map_option_out (map check_one_cofix mfix) = Some inds ->
  map_option_out (map (fun x : def term =>
     check_one_cofix (map_def (subst s k) (subst s (#|mfix| + k)) x)) mfix) = Some inds.
Proof.
  apply map_option_out_impl. move=> [na ty def rarg] /= ind.
  destruct (decompose_prod_assum [] ty) eqn:decty.
  destruct (decompose_app t) eqn:eqapp.
  destruct t0; try discriminate. simpl.
  pose proof (subst_decompose_prod_assum_rec [] ty s k).
  rewrite decty in X.
  destruct X as [ctx'' [t'' [dect decty']]].
  rewrite decty'.
  apply decompose_app_inv in eqapp.
  subst t.
  rewrite subst_mkApps /= in dect.
  rewrite decompose_prod_assum_mkApps in dect. noconf dect.
  rewrite decompose_app_mkApps //.
Qed.

Lemma subs_nth_error {cf:checker_flags} Σ Γ s Δ decl n t :
  subs Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  nth_error s n = Some t ->
  match decl_body decl return Type with
  | Some t' => False
  | None =>
    let ty := subst0 (skipn (S n) s) (decl_type decl) in
    Σ ;;; Γ |- t : ty
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. intros [= ->].
    simpl. exact t1.
  - intros. destruct decl as [na' [b|] ty]; cbn in *.
    + eapply IHX. all: eauto.
    + now apply IHX.
Qed.

Lemma untyped_subslet_nth_error Γ s Δ decl n t :
  untyped_subslet Γ s Δ ->
  nth_error Δ n = Some decl ->
  nth_error s n = Some t ->
  match decl_body decl return Type with
  | Some t' => t = subst0 (skipn (S n) s) t'
  | None => True
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. intros [= ->].
    simpl. auto.
  - intros. destruct decl as [na' [b|] ty]; cbn in *. 2: auto.
    specialize (IHX _ H H0). intuition auto.
  - intros [= <-]. intros [= <-].
    simpl. split; auto.
  - apply IHX.
Qed.

Arguments iota_red : simpl never.

(** Substitution without lets in Γ' *)
Lemma subs_usubst {cf:checker_flags} Σ Γ Γ' Γ'' s :
  subs Σ Γ s Γ' ->
  usubst (Γ,,, Γ',,, Γ'') (⇑^#|Γ''| (s ⋅n ids)) (Γ,,, subst_context s 0 Γ'').
Proof.
  intros subs n decl.
  case: (nth_error_app_context (Γ ,,, Γ') Γ'' n) => // x hnth hlt [=] hx; subst x => b hb.
  - left; eexists n, _.
    split; auto.
    * rewrite Upn_eq /subst_consn idsn_lt //.
    * rewrite nth_error_app_lt; len => //.
      change (fun m => S (n + m)) with (lift_renaming (S n) 0).
      rewrite nth_error_subst_context /= hnth /=. split; eauto.
      rewrite /= hb /=. f_equal.
      rewrite subst_inst. rewrite Nat.add_0_r.
      rewrite rename_inst.
      replace #|Γ''| with ((#|Γ''| - S n) + S n) at 2 by lia.
      set (k := S n).
      sigma. apply inst_ext.
      rewrite /rshiftk. rewrite (ren_shiftk (S n)).
      rewrite -shiftn_Upn - !Upn_Upn. intros i; lia_f_equal.
  - move: hnth.
    case: (nth_error_app_context Γ Γ' _) => // x' hnth hn' [=] eq; subst x'.
    * exfalso.
      revert subs hnth hb; generalize (n - #|Γ''|); clear.
      intros n subs; induction subs in n |- *; simpl => //.
      { now rewrite nth_error_nil //. }
      { destruct n; simpl.
        * intros [= <-] => //.
        * intros hnth. now specialize (IHsubs _ hnth). }
    * left; exists (n - #|Γ'|), decl.
      repeat split.
      + rewrite Upn_eq /subst_consn nth_error_idsn_None //; try lia.
        unfold subst_compose.
        apply subs_length in subs.
        rewrite (proj2 (nth_error_None _ _)); try (len; lia).
        simpl. len. unfold shiftk. lia_f_equal.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + rewrite -lift_renaming_0_rshift hb /=.
        f_equal. rewrite rename_inst. rewrite lift_renaming_spec shiftn0 ren_shiftk.
        apply inst_ext.
        apply subs_length in subs.
        replace (S n) with ((S (n - #|Γ''|)) + #|Γ''|) by lia.
        rewrite -shiftk_compose subst_compose_assoc.
        rewrite shiftn_Upn -subst_compose_assoc.
        replace (S (n - #|Γ''|)) with ((S (n - #|Γ''|) - #|Γ'|) + #|Γ'|) by lia.
        rewrite -shiftk_compose !subst_compose_assoc.
        rewrite -(subst_compose_assoc _ _ (↑^#|Γ''|)).
        rewrite subst_consn_shiftn //.
        rewrite !shiftk_compose. intros i; lia_f_equal.
Qed.

Lemma untyped_subslet_length {Γ s Δ} : untyped_subslet Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; lia.
Qed.

(* Let-expanding substitution *)
Lemma subslet_usubst {Γ Δ Γ' s} :
  untyped_subslet Γ s Δ ->
  usubst (Γ,,, Δ,,, Γ') (⇑^#|Γ'| (s ⋅n ids)) (Γ,,, subst_context s 0 Γ').
Proof.
  intros subs n decl.
  case: (nth_error_app_context (Γ ,,, Δ) Γ' n) => // x hnth hlt [=] hx; subst x => b hb.
  - left; eexists n, _.
    split; auto.
    * rewrite Upn_eq /subst_consn idsn_lt //.
    * rewrite nth_error_app_lt; len => //.
      change (rshiftk (S n)) with (lift_renaming (S n) 0).
      rewrite nth_error_subst_context /= hnth /=. split; eauto.
      rewrite /= hb /=. f_equal.
      rewrite subst_inst. rewrite Nat.add_0_r.
      rewrite rename_inst. rewrite ren_lift_renaming Upn_0.
      replace #|Γ'| with ((#|Γ'| - S n) + S n) at 2 by lia.
      set (k := S n).
      sigma. apply inst_ext.
      rewrite -shiftn_Upn - !Upn_Upn. intros i; lia_f_equal.
  - move: hnth.
    case: (nth_error_app_context Γ Δ _) => // x' hnth hn' [=] eq; subst x'.
    * right.
      pose proof (untyped_subslet_length subs).
      rewrite Upn_eq {1}/subst_consn nth_error_idsn_None; try lia.
      len. rewrite subst_consn_compose subst_consn_lt; len; try lia.
      rewrite /subst_fn nth_error_map.
      case: nth_error_spec; try lia. move=> x hs hns /=.
      epose proof (untyped_subslet_nth_error _ _ _ _ _ _ subs hnth hs).
      rewrite hb in X; rewrite X; cbn.
      rewrite subst_inst Upn_0 inst_assoc. apply inst_ext.
      (rewrite skipn_subst; try by lia); [].
      rewrite !subst_compose_assoc.
      rewrite subst_consn_compose. sigma.
      rewrite -subst_compose_assoc -shiftk_shift -subst_compose_assoc.
      rewrite -shiftk_shift.
      (rewrite (shift_subst_consn_ge (S n)); try by len; lia); [].
      now len.
    * left; exists (n - #|s|), decl.
      pose proof (untyped_subslet_length subs).
      repeat split.
      + rewrite Upn_eq /subst_consn nth_error_idsn_None //; try lia.
        unfold subst_compose.
        rewrite (proj2 (nth_error_None _ _)); try (len; lia).
        simpl. len. unfold shiftk. lia_f_equal.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + rewrite -lift_renaming_0_rshift hb /=.
        f_equal; sigma.
        apply inst_ext. rewrite -shiftk_shift.
        rewrite - !subst_compose_assoc -shiftk_shift.
        replace (S n) with ((S n - #|Γ'|) + #|Γ'|) by lia.
        rewrite -shiftk_compose subst_compose_assoc shiftn_Upn.
        replace (S n - #|Γ'|) with (S (n - #|Γ'| - #|s|) + #|s|) by lia.
        rewrite -shiftk_compose subst_compose_assoc -(subst_compose_assoc (↑^#|s|)).
        rewrite subst_consn_shiftn //. sigma.
        rewrite -shiftk_shift. rewrite -shiftk_shift_l shiftk_compose.
        now replace (n - #|Γ'| - #|s| + S #|Γ'|) with (S (n - #|s|)) by lia.
Qed.

Lemma subst_skipn {n s k t} : n <= #|s| -> subst (skipn n s) k t = subst s k (lift n k t).
Proof.
  intros Hn.
  assert (#|firstn n s| = n) by (rewrite firstn_length_le; lia).
  rewrite <- (firstn_skipn n s) at 2.
  rewrite subst_app_simpl. rewrite H.
  rewrite <- commut_lift_subst_rec; auto with arith.
  rewrite -{3}H. now rewrite simpl_subst_k.
Qed.

Lemma subst_compare_term {cf:checker_flags} Σ (φ : UnivConstraintSet.t) pb (l : list term) (k : nat) (T U : term) :
  compare_term Σ φ pb T U -> compare_term Σ φ pb (subst l k T) (subst l k U).
Proof.
  destruct pb; simpl.
  - apply subst_eq_term.
  - apply subst_leq_term.
Qed.

Lemma subst_compare_decl `{checker_flags} {Σ ϕ pb l k d d'} :
  compare_decl Σ ϕ pb d d' -> compare_decl Σ ϕ pb (subst_decl l k d) (subst_decl l k d').
Proof.
  intros []; constructor; auto; destruct pb;
    intuition eauto using subst_compare_term, subst_eq_term, subst_leq_term.
Qed.

Lemma subst_compare_context `{checker_flags} Σ φ pb l l' n k :
  compare_context Σ φ pb l l' ->
  compare_context Σ φ pb (subst_context n k l) (subst_context n k l').
Proof.
  induction 1; rewrite ?subst_context_snoc /=; constructor; auto.
  erewrite (All2_fold_length X). simpl.
  apply (subst_compare_decl p).
Qed.

From Stdlib Require Import ssrbool.

Section CtxReduction.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  Lemma red_abs_alt Γ na M M' N N' : red Σ Γ M M' -> red Σ (Γ ,, vass na M) N N' ->
                                 red Σ Γ (tLambda na M N) (tLambda na M' N').
  Proof using Type.
    intros. transitivity (tLambda na M N').
    * now eapply (red_ctx_congr (tCtxLambda_r _ _ tCtxHole)).
    * now eapply (red_ctx_congr (tCtxLambda_l _ tCtxHole _)).
  Qed.

  Lemma red_letin_alt Γ na d0 d1 t0 t1 b0 b1 :
    red Σ Γ d0 d1 -> red Σ Γ t0 t1 -> red Σ (Γ ,, vdef na d0 t0) b0 b1 ->
    red Σ Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1).
  Proof using Type.
    intros; transitivity (tLetIn na d0 t0 b1).
    * now eapply (red_ctx_congr (tCtxLetIn_r _ _ _ tCtxHole)).
    * transitivity (tLetIn na d0 t1 b1).
      + now eapply (red_ctx_congr (tCtxLetIn_b _ _ tCtxHole _)).
      + now apply (red_ctx_congr (tCtxLetIn_l _ tCtxHole _ _)).
  Qed.
End CtxReduction.

Record wt_cumul_pb {cf} (pb : conv_pb) Σ (Γ : context) T U :=
  { wt_cumul_pb_dom : isType Σ Γ T;
    wt_cumul_pb_codom : isType Σ Γ U;
    wt_cumul_pb_eq : cumulAlgo_gen Σ Γ pb T U }.

Arguments wt_cumul_pb_dom {cf pb Σ Γ T U}.
Arguments wt_cumul_pb_codom {cf pb Σ Γ T U}.
Arguments wt_cumul_pb_eq {cf pb Σ Γ T U}.

Definition wt_cumul {cf} Σ Γ := wt_cumul_pb Cumul Σ Γ.
Definition wt_conv {cf} Σ Γ := wt_cumul_pb Conv Σ Γ.

Notation " Σ ;;; Γ |- t <= u ✓" := (wt_cumul Σ Γ t u) (at level 50, Γ, t, u at next level).
Notation " Σ ;;; Γ |- t = u ✓" := (wt_conv Σ Γ t u) (at level 50, Γ, t, u at next level).

Definition wt_cumul_cum {cf} {Σ Γ T U} : Σ ;;; Γ |- T <= U ✓ -> Σ ;;; Γ |- T <= U.
Proof. intros H. apply (wt_cumul_pb_eq H). Defined.
Coercion wt_cumul_cum : wt_cumul >-> cumulAlgo.

Definition wt_conv_conv {cf} {Σ Γ T U} : Σ ;;; Γ |- T = U ✓ -> Σ ;;; Γ |- T = U.
Proof. intros H; apply (wt_cumul_pb_eq H). Defined.
Coercion wt_conv_conv : wt_conv >-> convAlgo.

Definition red1P P Σ Γ t v :=
  on_ctx_free_vars P Γ × on_free_vars P t × red1 Σ Γ t v.

Definition red1P_red1 {P Σ Γ t v} : red1P P Σ Γ t v -> red1 Σ Γ t v := fun x => x.2.2.
Definition red1P_on_free_vars_left {P Σ Γ t v} : red1P P Σ Γ t v -> on_free_vars P t := fun x => x.2.1.
Definition red1P_on_free_vars_ctx {P Σ Γ t v} : red1P P Σ Γ t v -> on_ctx_free_vars P Γ := fun x => x.1.
Definition red1P_on_free_vars_right {cf} {P Σ} {wfΣ : wf Σ} {Γ t v} : red1P P Σ Γ t v -> on_free_vars P v.
Proof.
  intros [onΓ [ont red]].
  eapply red1_on_free_vars; tea.
Qed.

Reserved Notation " Σ ;;; Γ |-[ P ] t <=[ le ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  |-[ P ]  t  <=[ le ]  u").

Inductive cumulP {cf} (pb : conv_pb) (Σ : global_env_ext) (P : nat -> bool) (Γ : context) : term -> term -> Type :=
| wt_cumul_refl t u : compare_term Σ.1 (global_ext_constraints Σ) pb t u -> Σ ;;; Γ |-[P] t <=[pb] u
| wt_cumul_red_l t u v : red1P P Σ Γ t v -> Σ ;;; Γ |-[P] v <=[pb] u -> Σ ;;; Γ |-[P] t <=[pb] u
| wt_cumul_red_r t u v : Σ ;;; Γ |-[P] t <=[pb] v -> red1P P Σ Γ u v -> Σ ;;; Γ |-[P] t <=[pb] u
where " Σ ;;; Γ |-[ P ] t <=[ pb ] u " := (cumulP pb Σ P Γ t u) : type_scope.

Notation " Σ ;;; Γ |-[ P ] t <= u " := (cumulP Cumul Σ P Γ t u) (at level 50, Γ, t, u at next level,
    format "Σ  ;;;  Γ  |-[ P ]  t  <=  u") : type_scope.

Notation " Σ ;;; Γ |-[ P ] t = u " := (cumulP Conv Σ P Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  |-[ P ]  t  =  u") : type_scope.

Lemma isType_wf_local {cf:checker_flags} {Σ Γ T} : isType Σ Γ T -> wf_local Σ Γ.
Proof.
  intros (_ & s & Hs & _).
  now eapply typing_wf_local.
Qed.

Lemma shiftnPF_closedPT (Γ : context) : shiftnP #|Γ| xpred0 ≐1 closedP #|Γ| xpredT.
Proof.
  intros i; rewrite /shiftnP /closedP orb_false_r.
  now destruct Nat.ltb.
Qed.

Section SubstitutionLemmas.
  Context {cf} {Σ} {wfΣ : wf Σ}.

  Lemma isType_closedPT Γ T : isType Σ Γ T -> on_free_vars (closedP #|Γ| xpredT) T.
  Proof using wfΣ.
    move/isType_closed/(closedn_on_free_vars (P:=xpred0)).
    now rewrite shiftnPF_closedPT.
  Qed.

  Lemma wt_cumul_pb_equalityP {pb} {Γ : context} {T U} : wt_cumul_pb pb Σ Γ T U -> cumulP pb Σ (closedP #|Γ| xpredT) Γ T U.
  Proof using wfΣ.
    move=> [] dom.
    move: (isType_wf_local dom) => /closed_wf_local clΓ.
    rewrite closed_ctx_on_ctx_free_vars in clΓ; tea.
    move/isType_closedPT: dom => clT.
    move/isType_closedPT => clU cum.
    induction cum.
    - constructor; auto.
    - econstructor 2.
      * econstructor; [|split]; tea.
      * eapply IHcum => //.
        now eapply red1_on_free_vars in r.
    - econstructor 3.
      * eapply IHcum => //.
        now eapply red1_on_free_vars.
      * econstructor; [|split]; tea.
  Qed.

  Lemma substitution_red1 {Γ Γ' Γ'' s M N} :
    subs Σ Γ s Γ' -> wf_local Σ Γ ->
    is_open_term (Γ,,, Γ',,, Γ'') M ->
    red1 Σ (Γ ,,, Γ' ,,, Γ'') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
  Proof using wfΣ.
    intros Hs wfΓ H.
    rewrite !subst_inst.
    eapply red1_inst; eauto.
    now eapply subs_usubst.
  Qed.

  Lemma substitution_let_red {Γ Δ Γ' s M N} :
    subslet Σ Γ s Δ ->
    is_open_term (Γ,,, Δ,,, Γ') M ->
    red1 Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros Hs wfΓ H.
    rewrite !subst_inst.
    eapply red1_inst; eauto.
    now eapply (subslet_usubst Hs).
  Qed.

  Lemma substitution_untyped_let_red {Γ Δ Γ' s M N} :
    untyped_subslet Γ s Δ ->
    is_open_term (Γ,,, Δ,,, Γ') M ->
    red1 Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros Hs H.
    rewrite !subst_inst.
    eapply red1_inst; eauto.
    now eapply subslet_usubst.
  Qed.

  Lemma substitution_untyped_red {Γ Δ Γ' s M N} :
    untyped_subslet Γ s Δ ->
    is_open_term (Γ ,,, Δ ,,, Γ') M ->
    on_ctx_free_vars (shiftnP #|Γ,,, Δ,,, Γ'| xpred0) (Γ,,, Δ,,, Γ') ->
    red Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros subsl onM onΓ.
    induction 1; trea.
    - eapply substitution_untyped_let_red; eassumption.
    - etransitivity; [eapply IHX1|eapply IHX2]; tea.
      eapply red_on_free_vars in X1; tea.
  Qed.

  Lemma substitution_red {Γ Δ Γ' s M N} :
    subslet Σ Γ s Δ -> wf_local Σ Γ ->
    is_open_term (Γ ,,, Δ ,,, Γ') M ->
    on_ctx_free_vars (shiftnP #|Γ,,, Δ,,, Γ'| xpred0) (Γ,,, Δ,,, Γ') ->
    red Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros Hs Hl onM onctx Hred. induction Hred; trea.
    - eapply substitution_let_red; eauto.
    - etransitivity; [eapply IHHred1|eapply IHHred2]; tea.
      eapply red_on_free_vars in Hred1; eauto.
  Qed.

  (* Lemma red_red_onctx {P Γ Δ Γ' s s' ctx} :
    untyped_subslet Γ s Δ ->
    onctx
      (fun b : term =>
      forall Δ Γ'0 : context,
      untyped_subslet Γ s Δ ->
      red Σ (Γ,,, Γ'0) (subst s #|Γ'0| b) (subst s' #|Γ'0| b)) ctx ->
    All2_fold
    (fun (Γ0 Δ0 : context) (d d' : context_decl) =>
      red_decls Σ (Γ,,, Γ',,, mapi_context (shiftf (subst s) #|Γ'|) Γ0)
        (Γ,,, Γ',,, mapi_context (shiftf (subst s') #|Γ'|) Δ0)
        (map_decl (shiftf (subst s) #|Γ'| #|Γ0|) d)
        (map_decl (shiftf (subst s') #|Γ'| #|Γ0|) d')) ctx ctx.
  Proof.
    intros hsubs.
    induction 1; constructor; auto.
    destruct p. destruct x as [na [b|] ty]; constructor; auto; simpl in *;
    rewrite /shiftf.
    - specialize (o _ (Γ' ,,, mapi_context (fun k' => subst s (k' + #|Γ'|)) l) hsubs).
      len in o. now rewrite -app_context_assoc.
    - specialize (r _ (Γ' ,,, mapi_context (fun k' => subst s (k' + #|Γ'|)) l) hsubs).
      len in r. now rewrite -app_context_assoc.
    - specialize (r _ (Γ' ,,, mapi_context (fun k' => subst s (k' + #|Γ'|)) l) hsubs).
      len in r. now rewrite -app_context_assoc.
  Qed. *)

  Ltac simpl_IHs :=
    repeat match goal with
      | [ H : ?A -> ?B, H' : ?A |- _ ] =>
        specialize (H H')
       end.

  Lemma subst_inst_case_context_wf s k pars puinst ctx :
    test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pars| ctx ->
    subst_context s k (inst_case_context pars puinst ctx) =
    inst_case_context (map (subst s k) pars) puinst ctx.
  Proof using Type.
    intros Hctx.
    rewrite subst_context_inst_context.
    rewrite inst_inst_case_context_wf //. f_equal.
    apply map_ext => x. now rewrite subst_inst.
  Qed.

  Lemma on_ctx_free_vars_snoc p Γ d :
    on_ctx_free_vars (shiftnP 1 p) (Γ ,, d) = on_ctx_free_vars p Γ && on_free_vars_decl p d.
  Proof using Type.
    now rewrite (on_ctx_free_vars_concat _ _ [_]) on_ctx_free_vars_tip /= addnP_shiftnP.
  Qed.

  Lemma addnP_shiftnP_k k n p : addnP (k + n) (shiftnP k p) ≐1 addnP n p.
  Proof using Type.
    now rewrite Nat.add_comm -addnP_add addnP_shiftnP.
  Qed.

Lemma subst_context_app' s k Γ Δ :
  subst_context s k (Γ ,,, Δ) = subst_context s k Γ ,,, subst_context s (k + #|Γ|) Δ.
Proof using Type.
  rewrite subst_context_app. lia_f_equal.
Qed.

  Lemma red_red {P Γ Δ Γ' s s' b} :
    on_ctx_free_vars P (Γ ,,, Δ ,,, Γ') ->
    on_free_vars P b ->
    All2 (red Σ Γ) s s' ->
    All (on_free_vars (addnP (#|Γ'| + #|Δ|) P)) s ->
    untyped_subslet Γ s Δ ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
  Proof using wfΣ.
    intros onΓ onb Hall ons Hsubs.
    revert P b onb Γ Δ Γ' onΓ Hall Hsubs ons.
    apply: term_on_free_vars_ind;
          intros; match goal with
                    |- context [tRel _] => idtac
                  | |- _ => cbn -[plus]
                  end; try easy;
        autorewrite with map;
        rewrite ?Nat.add_assoc;
        try solve [f_equal; auto; solve_all].

    - unfold subst.
      destruct (#|Γ'| <=? i) eqn:Heq.
      + destruct nth_error eqn:Heq'.
        * destruct (All2_nth_error_Some _ _ Hall Heq') as [t' [-> Ptt']].
          intros. relativize #|Γ'|; [eapply (weakening_red (Γ':=[]))|]; tea.
          2:now eapply nth_error_all in ons; tea.
          2:now len.
          simpl.
          rewrite !on_ctx_free_vars_app in onΓ.
          setoid_rewrite addnP_add in onΓ.
          rewrite Nat.add_comm in onΓ. now move/and3P: onΓ => [].
         * rewrite (All2_nth_error_None _ Hall Heq').
           apply All2_length in Hall as ->. reflexivity.
      + reflexivity.

    - apply red_evar. eapply All2_map, All_All2; tea. intuition auto.
      specialize (X1 _ _ _ onΓ). now simpl_IHs.
    - apply red_prod; eauto.
      specialize (X0 Γ Δ (Γ' ,, vass na dom)).
      rewrite subst_context_snoc Nat.add_0_r in X0. apply X0 => //.
      * rewrite /= on_ctx_free_vars_snoc onΓ /=; auto with fvs.
      * cbn. eapply (All_impl ons) => ?; now rewrite (addnP_shiftnP_k 1).

    - apply red_abs_alt; eauto.
      specialize (X0 Γ Δ (Γ' ,, vass na ty)).
      rewrite subst_context_snoc Nat.add_0_r in X0. apply X0 => //.
      * rewrite /= on_ctx_free_vars_snoc onΓ /=; auto with fvs.
      * cbn. apply (All_impl ons) => ?; now rewrite (addnP_shiftnP_k 1).

    - apply red_letin_alt; eauto.
      specialize (X1 Γ Δ (Γ' ,, vdef na def ty)).
      rewrite subst_context_snoc Nat.add_0_r in X1. apply X1 => //.
      * rewrite /= on_ctx_free_vars_snoc onΓ /=; auto with fvs.
      * cbn. apply (All_impl ons) => ?; now rewrite (addnP_shiftnP_k 1).

    - apply red_app; eauto.
    - eapply (red_case (p:=(map_predicate_k id (subst s) #|Γ'| pred))); simpl; solve_all.
      * eapply All_All2; tea. solve_all. eapply b; eauto; solve_all.
      * rewrite /map_predicate_k /= /PCUICCases.inst_case_predicate_context /=.
        rewrite map_subst_inst.
        rewrite -inst_inst_case_context_wf //.
        { rewrite test_context_k_closed_on_free_vars_ctx //. }
        rewrite -subst_context_inst_context -app_context_assoc -(subst_context_app' _ 0).
        relativize (_ + _); [eapply X2|]; tea; auto; len; solve_all.
        { rewrite !app_context_assoc.
          relativize #|pcontext pred|; [erewrite on_ctx_free_vars_extend|]; len => //.
          rewrite onΓ => /=.
          eapply on_free_vars_ctx_inst_case_context; trea; revgoals.
          { erewrite test_context_k_closed_on_free_vars_ctx; tea. }
          { solve_all. } }
        { len. rewrite Nat.add_comm -addnP_add Nat.add_comm -addnP_add addnP_shiftnP addnP_add Nat.add_comm //. }
      * eapply X3; eauto; solve_all.
      * red. solve_all.
        eapply All_All2; tea => /=. solve_all; unfold on_Trel; simpl.
        + rewrite /inst_case_branch_context /= map_subst_inst -inst_inst_case_context_wf //.
          { rewrite test_context_k_closed_on_free_vars_ctx //. apply X. }
          rewrite -subst_context_inst_context -app_context_assoc -(subst_context_app' _ 0).
          relativize (_ + _); [eapply X|]; tea; auto; len; solve_all.
          { rewrite !app_context_assoc.
            relativize #|bcontext x|; [erewrite on_ctx_free_vars_extend|]; len => //.
            rewrite onΓ => /=. eapply on_free_vars_ctx_inst_case_context; trea; solve_all.
            erewrite test_context_k_closed_on_free_vars_ctx; tea. apply X. }
        { len. rewrite Nat.add_comm -addnP_add Nat.add_comm -addnP_add addnP_shiftnP addnP_add Nat.add_comm //. }
    - apply red_proj_c; eauto.
    - apply red_fix_congr; eauto.
      solve_all. eapply All_All2; tea; simpl; solve_all.
      * eapply a; tea; solve_all.
      * rewrite subst_fix_context.
        specialize (b1 Γ Δ (Γ' ,,, (fix_context m))).
        rewrite (subst_context_app' _ 0) !app_context_assoc /= in b1. len in b1.
        eapply b1; eauto; len; solve_all.
        { relativize #|m|; [erewrite on_ctx_free_vars_extend|]; len => //.
          rewrite onΓ. apply on_free_vars_fix_context. rewrite /test_def. solve_all.
          now len in b2. }
        now rewrite -Nat.add_assoc addnP_shiftnP_k.
    - apply red_cofix_congr; eauto.
      solve_all. eapply All_All2; tea; simpl; solve_all.
      * eapply a; tea; solve_all.
      * rewrite subst_fix_context.
        specialize (b1 Γ Δ (Γ' ,,, (fix_context m))).
        rewrite (subst_context_app' _ 0) !app_context_assoc /= in b1. len in b1.
        eapply b1; eauto; len; solve_all.
        { relativize #|m|; [erewrite on_ctx_free_vars_extend|]; len => //.
          rewrite onΓ. apply on_free_vars_fix_context. rewrite /test_def. solve_all.
          now len in b2. }
        now rewrite -Nat.add_assoc addnP_shiftnP_k.
    - destruct pr as [? []] => //.
      eapply red_primArray_congr => //.
      * cbn. solve_all. cbn in X1. destruct X1 as [? []].
        eapply All_All2; tea; simpl; solve_all. eapply b1; tea; solve_all.
      * cbn in X, X0. intuition eauto.
      * cbn in X, X0; intuition eauto.
  Qed.

  Lemma untyped_substitution_red {Γ Δ Γ' s M N} :
    untyped_subslet Γ s Δ ->
    on_ctx_free_vars (shiftnP #|Γ,,, Δ,,, Γ'| xpred0) (Γ ,,, Δ ,,, Γ') ->
    is_open_term (Γ ,,, Δ ,,, Γ') M ->
    red Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros Hs onΓ onM Hred. induction Hred; trea.
    - eapply substitution_untyped_let_red; eauto.
    - etransitivity; [eapply IHHred1|eapply IHHred2]; eauto.
      eapply red_on_free_vars in Hred1; tea.
  Qed.

  (** The cumulativity relation is substitutive, yay! *)

  Lemma substitution_untyped_cumul {Γ Γ' Γ'' s M N} :
    untyped_subslet Γ s Γ' ->
    is_open_term (Γ ,,, Γ' ,,, Γ'') M ->
    is_open_term (Γ ,,, Γ' ,,, Γ'') N ->
    on_ctx_free_vars (shiftnP #|Γ ,,, Γ' ,,, Γ''| xpred0) (Γ ,,, Γ' ,,, Γ'') ->
    Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M <= N ->
    Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M <= subst s #|Γ''| N.
  Proof using wfΣ.
    intros Hs onN onM onΓ h. induction h.
    - constructor.
      now apply subst_leq_term.
    - epose proof (substitution_untyped_let_red Hs onN r); tea.
      eapply red_cumul_cumul; eauto.
      eapply IHh; tea. eapply red1_on_free_vars in r; tea.
    - epose proof (substitution_untyped_let_red Hs onM r).
      eapply red_cumul_cumul_inv; eauto.
      eapply IHh; tea. eapply red1_on_free_vars in r; tea.
  Qed.

  Lemma substitution_cumul0 {Γ na t u u' a} :
    on_ctx_free_vars (shiftnP #|Γ ,, vass na t| xpred0) (Γ ,, vass na t) ->
    is_open_term (Γ ,, vass na t) u ->
    is_open_term (Γ ,, vass na t) u' ->
    Σ ;;; Γ ,, vass na t |- u <= u' ->
    Σ ;;; Γ |- subst10 a u <= subst10 a u'.
  Proof using wfΣ.
    move=> onΓ onu onu' Hu.
    pose proof (@substitution_untyped_cumul Γ [vass na t] [] [a] u u').
    forward X.
    { constructor. constructor. }
    simpl in X. now apply X.
  Qed.

  Lemma substitution_cumul_let {Γ na t ty u u'} :
  on_ctx_free_vars (shiftnP #|Γ ,, vdef na t ty| xpred0) (Γ ,, vdef na t ty) ->
  is_open_term (Γ ,, vdef na t ty) u ->
  is_open_term (Γ ,, vdef na t ty) u' ->
  Σ ;;; Γ ,, vdef na t ty |- u <= u' ->
    Σ ;;; Γ |- subst10 t u <= subst10 t u'.
  Proof using wfΣ.
    move=> onΓ onu onu' Hu.
    pose proof (@substitution_untyped_cumul Γ [vdef na t ty] [] [t] u u').
    forward X.
    { rewrite - {1}(subst_empty 0 t). constructor. constructor. }
    simpl in X. now apply X.
  Qed.

  Lemma usubst_well_subst {Γ σ Δ} :
    usubst Γ σ Δ ->
    (forall x decl, nth_error Γ x = Some decl ->
      Σ ;;; Δ |- σ x : (decl.(decl_type)).[↑^(S x) ∘s σ]) ->
    well_subst Σ Γ σ Δ.
  Proof using Type.
    intros us hty. split; eauto.
    intros x decl hnth. specialize (hty x decl hnth). now sigma.
  Qed.

  Lemma subslet_well_subst {Γ Γ' s Δ} :
    subslet Σ Γ s Γ' ->
    wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
    well_subst Σ (Γ ,,, Γ' ,,, Δ) (⇑^#|Δ| (s ⋅n ids)) (Γ ,,, subst_context s 0 Δ).
  Proof using wfΣ.
    intros hs hsΔ.
    apply usubst_well_subst.
    * apply (subslet_usubst hs).
    * intros x decl.
      case: nth_error_app_context => //.
      { intros d hnth hn [= ->].
        rewrite {1}Upn_eq subst_consn_lt; len => //. rewrite /subst_fn.
        rewrite idsn_lt //.
        eapply meta_conv.
        - econstructor; auto.
          rewrite nth_error_app_lt; len => //.
          now rewrite nth_error_subst_context hnth.
        - rewrite /subst_decl. simpl.
        sigma. rewrite -shiftk_shift -subst_compose_assoc -shiftk_shift.
        (* rewrite lift0_inst !subst_inst_aux Nat.add_0_r. *)
          rewrite subst_shift_comm.
          rewrite -subst_fn_subst_consn. lia_f_equal. }
      { intros n hnth; len; intros hd [= ->].
        pose proof (subslet_length hs).
        move: hnth; case: nth_error_app_context => //.
        * intros n hnth hx [= ->].
          rewrite {1}Upn_eq subst_consn_ge; len => //; try lia.
          rewrite subst_consn_compose.
          rewrite subst_consn_lt; len; try lia.
          unfold subst_fn. rewrite nth_error_map.
          destruct (subslet_nth_error hs hnth) as [t [hnths [hty hb]]].
          rewrite hnths /=. sigma in hty.
          eapply meta_conv in hty.
          2:now rewrite skipn_subst ?Upn_0; try lia.
          eapply (shift_typing (Δ := subst_context s 0 Δ)) in hty.
          2:tas.
          2:now len.
          rewrite inst_assoc in hty.
          rewrite Upn_eq.
          eapply meta_conv; eauto.
          eapply inst_ext.
          rewrite (shift_subst_consn_ge (S x)); len; try lia.
          rewrite subst_compose_assoc.
          now replace (S x - #|Δ|) with (S (x - #|Δ|)) by lia.
        * intros n hnth hn [= ->].
          eapply meta_conv_all.
          2:reflexivity.
          2:{ rewrite Upn_subst_consn_ge; try lia. rewrite compose_ids_l.
              instantiate (1 := tRel (x - #|s|)).
              rewrite /shiftk. lia_f_equal. }
          2:{ econstructor; eauto. }
          eapply meta_conv.
          { econstructor; tas.
            rewrite nth_error_app_context_ge; len; try lia.
            rewrite H. erewrite <- hnth. lia_f_equal. }
          rewrite lift0_inst.
          rewrite Upn_eq.
          rewrite shift_subst_consn_ge; len; try lia.
          rewrite subst_consn_compose shift_subst_consn_ge; len; try lia.
          rewrite H. rewrite shiftk_compose. lia_f_equal.
      }
  Qed.

  Lemma All_local_env_inst {Γ0 Γ' Δ s} :
    All_local_env (fun Γ j =>
      forall (Δ : PCUICEnvironment.context) (σ : nat -> term),
      wf_local Σ Δ -> well_subst Σ Γ σ Δ ->
      (lift_typing0 (fun t T => Σ;;; Δ |- t.[σ] : T.[σ])) j)
      (Γ0,,, Γ',,, Δ) ->
    wf_local Σ Γ0 ->
    subslet Σ Γ0 s Γ' ->
    wf_local Σ (Γ0,,, subst_context s 0 Δ).
  Proof using wfΣ.
    intros HΓ HΓ0 sub.
    rewrite subst_context_inst_context.
    eapply (wf_local_app_inst _ (Γ0 ,,, Γ')); eauto.
    * now eapply All_local_env_app_inv in HΓ as [].
    * eapply (subslet_well_subst (Δ:=[])) in sub;
      rewrite ?subst_context_nil in sub |- *.
      + apply sub.
      + pcuicfo.
  Qed.
End SubstitutionLemmas.

Theorem substitution_prop {cf} : env_prop
  (fun Σ Γ0 t T =>
    forall (Γ Γ' Δ : context) (s : list term)
    (sub : subslet Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
    Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T)
  (fun Σ Γ0 j =>
    forall (Γ Γ' Δ : context) (s : list term)
    (sub : subslet Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
    lift_typing0 (fun t T => Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T) j)
  (fun Σ Γ0 =>
    forall (Γ Γ' Δ : context) (s : list term)
    (sub : subslet Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_local Σ (Γ ,,, subst_context s 0 Δ)).
Proof.
  intros Σ wfΣ Γ t T HT.
  pose proof (type_inst Σ wfΣ Γ t T HT) as [HΣ [HΓ HTy]].
  intuition auto.
  3:{
    subst Γ.
    rewrite !subst_inst. eapply HTy => //.
    eapply subslet_well_subst; eauto. }
  2:{ subst Γ.
      eapply typing_wf_local in HT.
      eapply All_local_env_app_inv in HT as [HΓ0 _].
      eapply All_local_env_app_inv in HΓ0 as [HΓ0 _].
      eapply All_local_env_inst; eauto. }
  unshelve eapply on_wf_global_env_impl ; tea.
  clear. intros * HΣ HP HQ Hty.
  intros. subst Γ.
  unshelve eapply lift_typing_impl with (1 := Hty _ _ X _) => [||t T HT].
  3: rewrite !subst_inst; eapply HT => //.
  now unshelve eapply subslet_well_subst.
Qed.

Corollary substitution {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s Δ t T} :
  subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros Hs Ht.
  eapply (env_prop_typing substitution_prop); trea.
  eapply (env_prop_wf_local substitution_prop); trea.
  now eapply typing_wf_local in Ht.
Qed.

Corollary lift_typing_substitution {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s Δ} j :
  subslet Σ Γ s Γ' ->
  lift_typing typing Σ (Γ ,,, Γ' ,,, Δ) j ->
  lift_typing typing Σ (Γ ,,, subst_context s 0 Δ) (judgment_map (subst s #|Δ|) j).
Proof.
  intros Hs HT.
  apply lift_typing_f_impl with (1 := HT) => // ?? Ht.
  eapply substitution in Ht; tea.
Qed.

Corollary lift_typing_subst {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s} j :
  subslet Σ Γ s Γ' ->
  lift_typing typing Σ (Γ ,,, Γ') j ->
  lift_typing typing Σ Γ (judgment_map (subst0 s) j).
Proof.
  now apply @lift_typing_substitution with (Δ := []).
Qed.

Corollary isType_substitution {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s Δ T} :
  subslet Σ Γ s Γ' ->
  isType Σ (Γ ,,, Γ' ,,, Δ) T ->
  isType Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T).
Proof.
  apply lift_typing_substitution.
Qed.

Corollary isType_subst {cf} {Σ} {wfΣ : wf Σ} {Γ Δ s T} :
  subslet Σ Γ s Δ ->
  isType Σ (Γ ,,, Δ) T ->
  isType Σ Γ (subst0 s T).
Proof.
  apply lift_typing_subst.
Qed.

Corollary isTypeRel_substitution {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s Δ T r} :
  subslet Σ Γ s Γ' ->
  isTypeRel Σ (Γ ,,, Γ' ,,, Δ) T r ->
  isTypeRel Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T) r.
Proof.
  apply lift_typing_substitution.
Qed.

Corollary isTypeRel_subst {cf} {Σ} {wfΣ : wf Σ} {Γ Δ s T r} :
  subslet Σ Γ s Δ ->
  isTypeRel Σ (Γ ,,, Δ) T r ->
  isTypeRel Σ Γ (subst0 s T) r.
Proof.
  apply lift_typing_subst.
Qed.

Corollary substitution_wf_local {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s Δ} :
  subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, Γ' ,,, Δ) ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ).
Proof.
  intros Hs Ht.
  eapply (env_prop_wf_local substitution_prop); trea.
Qed.

Lemma substitution0 {cf} {Σ} {wfΣ : wf Σ} {Γ n u U t T} :
  Σ ;;; Γ ,, vass n U |- t : T -> Σ ;;; Γ |- u : U ->
  Σ ;;; Γ |- t {0 := u} : T {0 := u}.
Proof.
  intros Ht Hu.
  assert (wfΓ : wf_local Σ Γ).
  { apply typing_wf_local in Hu; eauto. }
  eapply (substitution (Γ' := [vass n U]) (Δ := [])); tea.
  now eapply subslet_ass_tip.
Qed.

Lemma substitution_let {cf} {Σ} {wfΣ : wf Σ} {Γ n u U t T} :
  Σ ;;; Γ ,, vdef n u U |- t : T ->
  Σ ;;; Γ |- t {0 := u} : T {0 := u}.
Proof.
  intros Ht.
  assert ((wf_local Σ Γ) * (Σ ;;; Γ |- u : U)%type) as [wfΓ tyu].
  { apply typing_wf_local in Ht; eauto with wf.
    depelim Ht; split; tas. now destruct l as (? & _).
  }
  eapply (substitution (Γ':=[vdef n u U]) (Δ := [])); tea.
  now eapply subslet_def_tip.
Qed.

(** Substitution into a *well-typed* cumulativity/conversion derivation. *)

Lemma substitution_wt_cumul_pb {cf} {Σ} {wfΣ : wf Σ} {pb Γ Γ' Γ'' s M N} :
  subslet Σ Γ s Γ' ->
  wt_cumul_pb pb Σ (Γ ,,, Γ' ,,, Γ'') M N ->
  wt_cumul_pb pb Σ (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
Proof.
  move=> Hs wteq; split.
  + eapply (isType_substitution Hs), wteq.
  + eapply (isType_substitution Hs), wteq.
  + move/wt_cumul_pb_equalityP: wteq; elim.
    - intros t u cmp.
      constructor. now eapply subst_compare_term.
    - move=> t u v red cum.
      destruct pb.
      * eapply red_conv_conv.
        eapply substitution_let_red; tea; eauto with wf; apply red.
      * eapply red_cumul_cumul.
        eapply substitution_let_red; tea; eauto with wf; apply red.
    - move=> t u v red cum red'.
      destruct pb.
      * eapply red_conv_conv_inv; tea.
        eapply substitution_let_red; tea; apply red'.
      * eapply red_cumul_cumul_inv; tea.
        eapply substitution_let_red; tea; apply red'.
Qed.

Lemma substitution_cumul {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' Γ'' s M N} :
  subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M <= N ✓ ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |-  subst s #|Γ''| M <= subst s #|Γ''| N ✓.
Proof. apply substitution_wt_cumul_pb. Qed.

Lemma substitution_conv {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' Γ'' s M N} :
  subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M = N ✓ ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |-  subst s #|Γ''| M = subst s #|Γ''| N ✓.
Proof. apply substitution_wt_cumul_pb. Qed.
