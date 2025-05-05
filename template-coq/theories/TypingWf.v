(* Distributed under the terms of the MIT license. *)
Require Import ssreflect ssrbool.
Require PeanoNat.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config Reflect.
From MetaCoq.Template Require Import Ast AstUtils Induction UnivSubst WfAst Typing.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags).

Existing Class wf.

(** * Well-formedness of terms and types in typing derivations

  The internal representation of terms is not canonical, so we show
  that only well-formed terms and types can appear in typing derivations
  and the global context.
*)

Lemma All_local_env_wf_decl Σ :
  forall (Γ : context),
    All (wf_decl Σ) Γ -> All_local_env (wf_decl_pred Σ) Γ.
Proof.
  intros Γ X.
  induction Γ in X |- *.
  - constructor; eauto.
  - destruct a as [na [body|] ty].
    + econstructor.
      * apply IHΓ. inv X; eauto.
      * red. inv X. split.
        -- apply X0.
        -- constructor.
      * red. inv X. eauto.
    + econstructor.
      * apply IHΓ. inv X; eauto.
      * red. inv X. split.
        -- apply X0.
        -- constructor.
Qed.

Lemma on_global_decl_impl `{checker_flags} Σ P Q kn d :
  (forall Σ Γ t T, on_global_env cumul_gen P Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  on_global_env cumul_gen P Σ.1 ->
  on_global_decl cumul_gen P Σ kn d -> on_global_decl cumul_gen Q Σ kn d.
Proof.
  unfold on_global_env.
  intros X X0 o.
  destruct d; simpl.
  - destruct c; simpl. destruct cst_body0; simpl in *.
    red in o |- *. simpl in *. now eapply X.
    red in o |- *. simpl in *. now eapply X.
  - simpl in *.
    destruct o as [onI onP onNP].
    constructor; auto.
    -- eapply Alli_impl. exact onI. eauto. intros.

       refine {| ind_arity_eq := X1.(ind_arity_eq);
                 ind_cunivs := X1.(ind_cunivs) |}.
       --- apply onArity in X1. unfold on_type in *; simpl in *.
           now eapply X.
       --- pose proof X1.(onConstructors) as X11. red in X11.
           eapply All2_impl; eauto.
           simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
           * apply X; eauto.
           * clear -X0 X on_cargs. revert on_cargs.
              generalize (cstr_args x0), y.
              induction c; destruct y0; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
           split; intuition eauto.
           * clear -X0 X on_cindices.
             revert on_cindices.
             generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
             generalize (cstr_indices x0).
             induction 1; simpl; constructor; auto.
       --- simpl; intros. apply (onProjections X1).
       --- destruct X1. simpl. unfold check_ind_sorts in *.
           destruct Universe.is_prop; auto.
           destruct Universe.is_sprop; auto.
           split. apply ind_sorts. destruct indices_matter; auto.
           eapply type_local_ctx_impl. eapply ind_sorts. auto.
       --- apply (onIndices X1).
    -- red in onP. red.
       eapply All_local_env_impl. eauto.
       intros. now apply X.
Qed.

Lemma on_global_env_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, on_global_env cumul_gen P Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  on_global_env cumul_gen P Σ -> on_global_env cumul_gen Q Σ.
Proof.
  destruct Σ as [univs Σ]; cbn.
  intros X [cu X0]; split => /= //. cbn in *.
  induction X0; try destruct o; constructor; auto; constructor; eauto.
  clear IHX0.
  eapply on_global_decl_impl; tea. split => //.
Qed.

Lemma All_local_env_wf_decl_inv Σ (a : context_decl) (Γ : list context_decl)
         (X : All_local_env (wf_decl_pred Σ) (a :: Γ)) :
    on_local_decl (wf_decl_pred Σ) Γ a * All_local_env (wf_decl_pred Σ) Γ.
Proof.
  inv X; intuition; red; simpl; eauto.
Qed.

Lemma unfold_fix_wf:
  forall Σ (mfix : mfixpoint term) (idx : nat) (narg : nat) (fn : term),
    unfold_fix mfix idx = Some (narg, fn) ->
    WfAst.wf Σ (tFix mfix idx) ->
    WfAst.wf Σ fn.
Proof.
  intros Σ mfix idx narg fn Hf Hwf.
  unfold unfold_fix in Hf. inv Hwf.
  destruct nth_error eqn:eqnth; try congruence.
  pose proof (nth_error_all eqnth X) as [ _ wfd].
  injection Hf. intros <- <-.
  apply wf_subst; auto. clear wfd Hf eqnth.
  assert(forall n, WfAst.wf Σ (tFix mfix n)). constructor; auto.
  unfold fix_subst. generalize #|mfix|; intros. induction n; auto.
Qed.

Lemma unfold_cofix_wf Σ:
  forall (mfix : mfixpoint term) (idx : nat) (narg : nat) (fn : term),
    unfold_cofix mfix idx = Some (narg, fn) ->
    WfAst.wf Σ (tCoFix mfix idx) -> WfAst.wf Σ fn.
Proof.
  intros mfix idx narg fn Hf Hwf.
  unfold unfold_cofix in Hf. inv Hwf.
  destruct nth_error eqn:eqnth; try congruence.
  pose proof (nth_error_all eqnth X) as [_ wfd].
  injection Hf. intros <- <-.
  apply wf_subst; auto. clear wfd Hf eqnth.
  assert(forall n, WfAst.wf Σ (tCoFix mfix n)). constructor; auto.
  unfold cofix_subst. generalize #|mfix|; intros. induction n; auto.
Qed.

Lemma red1_isLambda Σ Γ t u :
  red1 Σ Γ t u -> isLambda t -> isLambda u.
Proof.
  induction 1 using red1_ind_all; simpl; try discriminate; auto.
Qed.


Ltac wf := intuition try (eauto with wf || congruence || solve [constructor]).
#[global]
Hint Unfold wf_decl vass vdef : wf.
#[global]
Hint Extern 10 => progress simpl : wf.
#[global]
Hint Unfold snoc : wf.
#[global]
Hint Extern 3 => apply wf_lift || apply wf_subst || apply wf_subst_instance : wf.
#[global]
Hint Extern 10 => constructor : wf.
#[global]
Hint Resolve All_skipn : wf.

Lemma on_global_decls_extends_not_fresh {cf} {univs retro} k (Σ : global_declarations) k' (Σ' : global_declarations) P :
  on_global_decls cumul_gen P univs retro ((k :: Σ) ++ [k'] ++ Σ') -> k.1 = k'.1 -> False.
Proof.
  intros H eq.
  depelim H. destruct o as [f ? ? ?].
  eapply Forall_app in f as [_ f].
  depelim f. cbn in *. subst. contradiction.
Qed.

Lemma lookup_env_extends {cf : checker_flags} (Σ : global_env) k d (Σ' : global_env) P :
  on_global_env cumul_gen P Σ' ->
  lookup_env Σ k = Some d ->
  extends Σ Σ' -> lookup_env Σ' k = Some d.
Proof.
  intro H; eapply lookup_env_extends_NoDup, NoDup_on_global_decls, H.
Qed.

Lemma In_lookup_globals k decls : In k (map fst decls) -> #| lookup_globals decls k | >= 1.
Proof.
  induction decls; cbn => //.
  case_eq (k == a.1).
  - intros e _. cbn. lia.
  - intros e [].
   + rewrite H in e. rewrite eqb_refl in e. inversion e.
   + now apply IHdecls.
Qed.

Lemma NoDup_extends (Σ : global_env) (Σ' : global_env) :
        NoDup (map fst (declarations Σ')) -> extends Σ Σ' -> NoDup (map fst (declarations Σ)).
Proof.
  intros Hl [_ Hex _].
  destruct Σ, Σ'; cbn in *. clear - Hl Hex.
  induction declarations0; cbn in *; econstructor.
  - intros H. specialize (Hex a.1). destruct Hex as [decls Hdecls].
    pose proof (NoDup_length_lookup_globals _ Hl a.1).
    rewrite eqb_refl in Hdecls. apply In_lookup_globals in H.
    rewrite Hdecls in H0. rewrite app_length in H0. cbn in H0.
    destruct lookup_global; lia.
  - eapply IHdeclarations0. intros. specialize (Hex c).
    destruct Hex as [decls Hdecls]. case_eq (c == a.1).
    + intros e. exists (decls ++ [a.2]). rewrite Hdecls e.
      now rewrite <- app_assoc.
    + intros e. exists decls. now rewrite Hdecls e.
Qed.

Lemma declared_env_extends {cf : checker_flags} (Σ : global_env) k d (Σ' : global_env) P :
  on_global_env cumul_gen P Σ' ->
  In (k, InductiveDecl d) (declarations Σ) -> extends Σ Σ' -> In (k,InductiveDecl d) (declarations Σ').
Proof.
  intros; apply lookup_global_Some_iff_In_NoDup.
  - destruct X; eapply NoDup_on_global_decls; eauto.
  - eapply lookup_env_extends; eauto.
    destruct X; eapply lookup_global_Some_iff_In_NoDup; eauto.
    eapply NoDup_extends; eauto.
    now eapply NoDup_on_global_decls.
Qed.

Lemma wf_extends {cf} {Σ : global_env} T {Σ' : global_env} P :
  on_global_env cumul_gen P Σ' -> WfAst.wf Σ T -> extends Σ Σ' -> WfAst.wf Σ' T.
Proof.
  intros wfΣ'.
  induction 1 using term_wf_forall_list_ind; try solve [econstructor; eauto; solve_all].
  - intros. destruct H. destruct X0.
    unfold declared_minductive in H.
    eapply declared_env_extends in H; tea.
    econstructor; repeat split; eauto; solve_all.
Qed.

Lemma wf_decl_extends {cf} {Σ : global_env} T {Σ' : global_env} P :
  on_global_env cumul_gen P Σ' -> wf_decl Σ T -> extends Σ Σ' -> wf_decl Σ' T.
Proof.
  intros wf [] ext. red. destruct decl_body; split; eauto using wf_extends.
Qed.

Arguments lookup_on_global_env {H} {Pcmp P Σ c decl}.

Lemma declared_inductive_wf {cf:checker_flags} {Σ : global_env} ind
         (mdecl : mutual_inductive_body) (idecl : one_inductive_body) :
  on_global_env cumul_gen wf_decl_pred Σ ->
  declared_inductive Σ ind mdecl idecl -> WfAst.wf Σ (ind_type idecl).
Proof.
  intros.
  destruct H as [Hmdecl Hidecl]. red in Hmdecl.
  eapply lookup_global_Some_iff_In_NoDup in  Hmdecl; eauto.
  2: destruct X; now eapply NoDup_on_global_decls.
  destruct (lookup_on_global_env X Hmdecl) as [Σ' [wfΣ' [ext prf]]]; eauto.
  apply onInductives in prf.
  eapply nth_error_alli in Hidecl; eauto.
  eapply onArity in Hidecl.
  destruct Hidecl.
  eapply wf_extends in w; tea; typeclasses eauto.
Qed.

Lemma wf_it_mkProd_or_LetIn Σ Γ t
  : WfAst.wf Σ (it_mkProd_or_LetIn Γ t) -> All (wf_decl Σ) Γ * WfAst.wf Σ t.
Proof.
  revert t. induction Γ; [simpl; auto with wf|]. intros t XX.
  destruct a, decl_body; simpl in *.
  apply IHΓ in XX as []. depelim w; simpl in *; split; auto with wf.
  apply IHΓ in XX as []. depelim w. simpl in *.
  split; auto. constructor; auto with wf.
Qed.

Lemma declared_inductive_wf_indices {cf:checker_flags} {Σ : global_env} {ind mdecl idecl} :
  on_global_env cumul_gen wf_decl_pred Σ ->
  declared_inductive Σ ind mdecl idecl -> All (wf_decl Σ) (ind_indices idecl).
Proof.
  intros.
  destruct H as [Hmdecl Hidecl]. red in Hmdecl.
  eapply lookup_global_Some_iff_In_NoDup in  Hmdecl; eauto.
  2: destruct X; now eapply NoDup_on_global_decls.
  destruct (lookup_on_global_env X Hmdecl) as [Σ' [wfΣ' [ext prf]]]; eauto.
  apply onInductives in prf.
  eapply nth_error_alli in Hidecl; eauto.
  pose proof (onArity Hidecl).
  rewrite Hidecl.(ind_arity_eq) in X0.
  destruct X0 as [s Hs]; wf.
  eapply wf_it_mkProd_or_LetIn in s as [? H].
  eapply wf_it_mkProd_or_LetIn in H as [].
  solve_all. eapply wf_decl_extends; tea; typeclasses eauto.
Qed.

Lemma declared_inductive_wf_ctors {cf:checker_flags} {Σ} {ind} {mdecl idecl} :
  on_global_env cumul_gen wf_decl_pred Σ ->
  declared_inductive Σ ind mdecl idecl ->
  All (fun ctor => All (wf_decl Σ) ctor.(cstr_args)) (ind_ctors idecl).
Proof.
  intros.
  destruct H as [Hmdecl Hidecl]. red in Hmdecl.
  eapply lookup_global_Some_iff_In_NoDup in  Hmdecl; eauto.
  2: destruct X; now eapply NoDup_on_global_decls.
  destruct (lookup_on_global_env X Hmdecl) as [Σ' [wfΣ' [ext prf]]]; eauto.
  apply onInductives in prf.
  eapply nth_error_alli in Hidecl; eauto.
  pose proof (onConstructors Hidecl). red in X0.
  solve_all. destruct X0.
  clear -X ext on_cargs.
  induction (cstr_args x) as [|[na [b|] ty] args] in on_cargs, y |- * ;
    try destruct on_cargs;
   constructor; unfold wf_decl in *; cbn in *; intuition eauto using wf_extends; simpl in *.
   destruct b0. intuition eauto using wf_extends with typeclass_instances.
   destruct a. intuition eauto using wf_extends with typeclass_instances.
   destruct y => //. destruct on_cargs. destruct w; eauto using wf_extends with typeclass_instances.
   destruct y => //. eapply IHargs; intuition eauto.
Qed.

Lemma All_local_env_wf_decls Σ ctx :
  TemplateEnvTyping.All_local_env (wf_decl_pred Σ) ctx ->
  All (wf_decl Σ) ctx.
Proof.
  induction 1; constructor; auto.
  destruct t0 as [s Hs]. split; simpl; intuition auto.
Qed.

Lemma on_global_inductive_wf_params {cf:checker_flags} {Σ : global_env_ext} {kn mdecl} :
  on_global_decl cumul_gen (fun Σ : global_env_ext => wf_decl_pred Σ) Σ kn (InductiveDecl mdecl) ->
  All (wf_decl Σ) (ind_params mdecl).
Proof.
  intros prf.
  apply onParams in prf. red in prf.
  apply All_local_env_wf_decls in prf.
  solve_all.
Qed.

Lemma destArity_spec ctx T :
  match destArity ctx T with
  | Some (ctx', s) => it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s)
  | None => True
  end.
Proof.
  induction T in ctx |- *; simpl; try easy.
  - specialize (IHT2 (ctx,, vass na T1)). now destruct destArity.
  - specialize (IHT3 (ctx,, vdef na T1 T2)). now destruct destArity.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma it_mkProd_or_LetIn_inj ctx s ctx' s' :
  it_mkProd_or_LetIn ctx (tSort s) = it_mkProd_or_LetIn ctx' (tSort s') ->
  ctx = ctx' /\ s = s'.
Proof.
  move/(f_equal (destArity [])).
  rewrite !destArity_it_mkProd_or_LetIn /=.
  now rewrite !app_context_nil_l => [= -> ->].
Qed.

(*
Lemma case_predicate_contextP ind mdecl idecl params uinst pctx :
  build_case_predicate_context ind mdecl idecl params uinst = Some pctx <~>
  case_predicate_context ind mdecl idecl params uinst pctx.
Proof.
  unfold build_case_predicate_context.
  unfold instantiate_params.
  destruct instantiate_params_subst as [[ictx p]|] eqn:ipars => /= //.
  2:{ split => //. intros H. depelim H.
      eapply instantiate_params_substP in i.
      rewrite ipars in i. discriminate. }
  move: (destArity_spec [] (subst0 ictx p)).
  destruct destArity as [[idctx inds]|] eqn:da => //.
  simpl. intros eqs.
  split.
  eapply instantiate_params_substP in ipars.
  intros [= <-]. econstructor. eauto. eauto.
  intros H. depelim H. subst sty.
  eapply instantiate_params_substP in i.
  rewrite ipars in i. noconf i. rewrite eqs in e.
  eapply it_mkProd_or_LetIn_inj in e as [<- <-].
  reflexivity.
  split => // [] [] s ty ictxt inds.
  move/instantiate_params_substP.
  rewrite ipars /= => [=] <- <- H.
  rewrite H destArity_it_mkProd_or_LetIn in da.
  noconf da.
Qed.
*)

Lemma wf_subst_context Σ s k Γ : All (wf_decl Σ) Γ -> All (WfAst.wf Σ) s -> All (wf_decl Σ) (subst_context s k Γ).
Proof.
  intros wfΓ. induction wfΓ in s |- *.
  - intros. constructor.
  - rewrite subst_context_snoc. constructor; auto.
    destruct p. destruct x as [? [] ?]; constructor; simpl in *; wf.
Qed.

Lemma wf_smash_context Σ Γ Δ : All (wf_decl Σ) Γ -> All (wf_decl Σ) Δ ->
  All (wf_decl Σ) (smash_context Δ Γ).
Proof.
  intros wfΓ; induction wfΓ in Δ |- *; intros wfΔ; simpl; auto.
  destruct x as [? [] ?]; simpl. apply IHwfΓ.
  eapply wf_subst_context; auto. constructor; auto. apply p.
  eapply IHwfΓ. apply All_app_inv; auto.
Qed.

Section WfAst.
  Context {cf:checker_flags}.
  Context {Σ : global_env}.

  Lemma wf_reln n acc Γ : All (WfAst.wf Σ) acc -> All (WfAst.wf Σ) (reln acc n Γ).
  Proof using Type.
    induction Γ in acc, n |- * => wfacc /= //.
    destruct a as [? [|] ?] => //. now eapply IHΓ.
    eapply IHΓ. constructor; auto. constructor.
  Qed.

  #[local]
  Hint Resolve wf_reln : wf.

  (* Lemma wf_instantiate_params_subst_spec params pars s ty s' ty' :
    instantiate_params_subst_spec params pars s ty s' ty' ->
    All (wf_decl Σ) params ->
    WfAst.wf Σ ty ->
    All (WfAst.wf Σ) pars ->
    All (WfAst.wf Σ) s ->
    All (WfAst.wf Σ) s' * WfAst.wf Σ ty'.
  Proof.
    intros ipars. induction ipars; intros wfparams wfty wfpars wfs => //.
    depelim wfparams. depelim wfpars. depelim wfty.
    apply IHipars; auto.
    depelim wfparams. depelim wfty. destruct H; simpl in *.
    apply IHipars; auto with wf.
  Qed. *)

  Lemma wf_map2_set_binder_name l l' :
    All (wf_decl Σ) l' ->
    All (wf_decl Σ) (map2 set_binder_name l l').
  Proof using Type.
    induction 1 in l |- *; destruct l; simpl; constructor.
    apply p. apply IHX.
  Qed.

  Definition lift_context_snoc0 n k Γ d : lift_context n k (d :: Γ) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
  Proof using Type. unfold lift_context. now rewrite fold_context_k_snoc0. Qed.
  Hint Rewrite lift_context_snoc0 : lift.

  Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
  Proof using Type.
    unfold snoc. apply lift_context_snoc0.
  Qed.
  Hint Rewrite lift_context_snoc : lift.


  Lemma wf_lift_context n k Γ : All (wf_decl Σ) Γ -> All (wf_decl Σ) (lift_context n k Γ).
  Proof using Type.
    intros wfΓ. induction wfΓ in n, k |- *.
    - intros. constructor.
    - rewrite lift_context_snoc0. constructor; auto.
      destruct p. destruct x as [? [] ?]; constructor; simpl in *; wf.
  Qed.

  Lemma wf_subst_instance_context u Γ :
    All (wf_decl Σ) Γ ->
    All (wf_decl Σ) (subst_instance u Γ).
  Proof using Type.
    induction 1; constructor; auto.
    destruct x as [na [b|] ty]; simpl in *.
    destruct p. now split; apply wf_subst_instance.
    destruct p. now split; auto; apply wf_subst_instance.
  Qed.

  Lemma wf_extended_subst Γ n :
    All (wf_decl Σ) Γ ->
    All (WfAst.wf Σ) (extended_subst Γ n).
  Proof using Type.
    induction 1 in n |- *.
    - simpl; constructor.
    - destruct x as [na [b|] ty]; simpl; constructor; auto.
      2:constructor.
      eapply wf_subst; auto.
      eapply wf_lift. apply p.
  Qed.

  Lemma wf_case_predicate_context ind mdecl idecl p :
    declared_inductive Σ ind mdecl idecl ->
    All (wf_decl Σ) mdecl.(ind_params) ->
    All (wf_decl Σ) (ind_indices idecl) ->
    All (WfAst.wf Σ) p.(pparams) ->
    All (wf_decl Σ) (case_predicate_context ind mdecl idecl p).
  Proof using Type.
    intros decl wfparams wfindty wfpars.
    unfold case_predicate_context. destruct p.
    apply wf_map2_set_binder_name.
    unfold pre_case_predicate_context_gen. cbn [Ast.pparams Ast.puinst].
    unfold inst_case_context.
    eapply wf_subst_context => //.
    2:now eapply All_rev.
    apply wf_subst_instance_context.
    rewrite /ind_predicate_context.
    constructor.
    simpl; split; auto. simpl. auto. simpl.
    eapply wf_mkApps. now econstructor.
    apply wf_reln. constructor.
    eapply wf_subst_context.
    now apply wf_lift_context.
    now apply wf_extended_subst.
  Qed.

  Lemma Forall_decls_on_global_wf :
    Forall_decls_typing
      (fun (Σ : global_env_ext) (_ : context) (t T : term) =>
      WfAst.wf Σ t * WfAst.wf Σ T) Σ ->
    on_global_env cumul_gen wf_decl_pred Σ.
  Proof using Type.
    apply on_global_env_impl => Σ' Γ t []; simpl; unfold wf_decl_pred;
    intros; auto. destruct X0 as [s []]; intuition auto.
  Qed.

  (* Hint Resolve on_global_wf_Forall_decls : wf. *)
  Lemma wf_inds mind u mdecl :
    All (WfAst.wf Σ) (inds mind u mdecl.(ind_bodies)).
  Proof using Type.
    unfold inds. induction #|ind_bodies mdecl|; constructor; auto.
    now constructor.
  Qed.

  Hint Resolve wf_inds : wf.

  Lemma on_inductive_wf_params {Σ' : global_env_ext} {kn mdecl} :
      forall (oib : on_inductive cumul_gen wf_decl_pred Σ'  kn mdecl),
      All (wf_decl Σ') (ind_params mdecl).
  Proof using Type.
    intros oib. apply onParams in oib.
    red in oib.
    induction (ind_params mdecl) as [|[? [] ?] ?]; simpl in oib; inv oib; constructor;
      try red in X0; try red in X1; try red; simpl; intuition auto.
  Qed.

  Lemma declared_inductive_wf_params {ind mdecl idecl} :
    on_global_env cumul_gen wf_decl_pred Σ ->
    declared_inductive Σ ind mdecl idecl -> All (wf_decl Σ) (ind_params mdecl).
  Proof using Type.
    intros.
    destruct H as [Hmdecl Hidecl]. red in Hmdecl.
    eapply lookup_global_Some_iff_In_NoDup in  Hmdecl; eauto.
    2: destruct X; now eapply NoDup_on_global_decls.
      destruct (lookup_on_global_env X Hmdecl) as [Σ' [wfΣ' [ext prf]]]; eauto.
    eapply on_global_inductive_wf_params in prf.
    solve_all. eapply wf_decl_extends; tea; typeclasses eauto.
  Qed.

  Lemma declared_constructor_wf
    (ind : inductive) (i : nat) (u : list Level.t)
          (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body) :
      on_global_env cumul_gen wf_decl_pred Σ ->
      declared_constructor Σ (ind, i) mdecl idecl cdecl ->
      WfAst.wf Σ (cstr_type cdecl).
  Proof using Type.
    intros X isdecl.
    destruct isdecl as [[Hmdecl Hidecl] Hcdecl]. red in Hmdecl.
    eapply lookup_global_Some_iff_In_NoDup in  Hmdecl; eauto.
    2: destruct X; now eapply NoDup_on_global_decls.
      destruct (lookup_on_global_env X Hmdecl) as [Σ' [wfΣ' [ext prf]]]; eauto. red in prf.
    apply onInductives in prf.
    eapply nth_error_alli in Hidecl; eauto. simpl in *.
    pose proof (onConstructors Hidecl) as h. unfold on_constructors in h.
    eapply All2_nth_error_Some in Hcdecl. 2: eassumption.
    destruct Hcdecl as [cs [Hnth [? ? [? ?]]]].
    eapply wf_extends; tea; typeclasses eauto.
  Qed.

  Lemma wf_case_branch_context_gen {ind mdecl idecl cdecl p br} :
    on_global_env cumul_gen wf_decl_pred Σ ->
    declared_constructor Σ ind mdecl idecl cdecl ->
    All (WfAst.wf Σ) (pparams p) ->
    All (fun ctor => All (wf_decl Σ) (cstr_args ctor)) (ind_ctors idecl) ->
    All (wf_decl Σ) (case_branch_context (fst ind) mdecl cdecl p br).
  Proof using Type.
    intros ong decli wfpars.
    intros Hforall.
    destruct decli as [decli hcstr].
    eapply nth_error_all in Hforall; tea. cbn in Hforall.
    unfold case_branch_context, case_branch_context_gen.
    eapply wf_map2_set_binder_name.
    apply wf_subst_context; auto.
    apply wf_subst_instance_context.
    rewrite /cstr_branch_context.
    unfold expand_lets_ctx, expand_lets_k_ctx.
    eapply wf_subst_context.
    eapply wf_lift_context.
    eapply wf_subst_context => //.
    eapply wf_inds.
    apply wf_extended_subst.
    eapply declared_inductive_wf_params in decli => //.
    now eapply All_rev.
  Qed.

  Lemma wf_case_branches_context ind mdecl idecl p brs :
    on_global_env cumul_gen wf_decl_pred Σ ->
    declared_inductive Σ ind mdecl idecl ->
    All (WfAst.wf Σ) (pparams p) ->
    All (fun ctor => All (wf_decl Σ) (cstr_args ctor)) (ind_ctors idecl) ->
    All (fun ctx => All (wf_decl Σ) ctx) (case_branches_contexts ind mdecl idecl p brs).
  Proof using Type.
    intros ong decli wfpars.
    unfold case_branches_contexts.
    intros Hforall.
    induction Hforall in brs |- *; destruct brs; cbn; constructor; auto.
    unfold case_branch_context_gen.
    eapply wf_map2_set_binder_name.
    apply wf_subst_context; auto.
    apply wf_subst_instance_context.
    2:now eapply All_rev.
    rewrite /cstr_branch_context.
    unfold expand_lets_ctx, expand_lets_k_ctx.
    eapply wf_subst_context.
    eapply wf_lift_context.
    eapply wf_subst_context => //.
    eapply wf_inds.
    apply wf_extended_subst.
    now eapply declared_inductive_wf_params in decli.
  Qed.

End WfAst.

Record wf_inductive_body Σ idecl := {
  wf_ind_type : WfAst.wf Σ (ind_type idecl);
  wf_ind_indices : All (WfAst.wf_decl Σ) (ind_indices idecl);
  wf_ind_ctors : All (fun cdecl => WfAst.wf Σ (cstr_type cdecl)) (ind_ctors idecl);
  wf_ind_ctor_args : All (fun cs => All (wf_decl Σ) (cstr_args cs)) idecl.(ind_ctors);
  wf_ind_ctors_indices : All (fun cdecl => All (WfAst.wf Σ) (cstr_indices cdecl)) (ind_ctors idecl);
  wf_ind_projs : All (fun pdecl => WfAst.wf Σ pdecl.(proj_type)) (ind_projs idecl)
}.

Section WfLookup.
  Context {cf:checker_flags}.
  Context {Σ : global_env_ext}.

  Lemma wf_projs ind npars p : All (WfAst.wf Σ) (projs ind npars p).
  Proof using Type.
    unfold projs. induction p; constructor; wf.
  Qed.

  Lemma on_global_inductive_wf_bodies {kn mdecl} :
    on_global_decl cumul_gen wf_decl_pred Σ kn (InductiveDecl mdecl) ->
    All (wf_inductive_body Σ) mdecl.(ind_bodies).
  Proof using Type.
    cbn. intros oni.
    have wfpars : All (wf_decl Σ) (ind_params mdecl).
    { now eapply on_inductive_wf_params in oni. }
    eapply onInductives in oni.
    solve_all.
    induction oni; constructor; auto.
    clear oni IHoni.
    destruct p.

    have wfargs : All (fun cs => All (wf_decl Σ) (cstr_args cs)) hd.(ind_ctors).
    { unfold on_constructors in onConstructors.
      clear -onConstructors.
      induction onConstructors; constructor; auto.
      destruct r.
      clear -on_cargs.
      revert on_cargs. revert y. generalize (cstr_args x).
      induction c as [|[? [] ?] ?]; simpl;
        destruct y; intuition auto;
        constructor;
        try red; simpl; try red in a0, b0; intuition eauto.
        now red in b. }
    split => //.
    - now destruct onArity.
    - rewrite ind_arity_eq in onArity .
      destruct onArity as [ona _].
      eapply wf_it_mkProd_or_LetIn in ona as [_ ona].
      now eapply wf_it_mkProd_or_LetIn in ona as [].
    - unfold on_constructors in onConstructors.
      clear -onConstructors.
      induction onConstructors; constructor; auto.
      destruct r.
      eapply on_ctype.
    - unfold on_constructors in onConstructors.
      clear -onConstructors.
      induction onConstructors; constructor; auto.
      destruct r.
      rewrite cstr_eq in on_ctype.
      destruct on_ctype as [wf _].
      eapply wf_it_mkProd_or_LetIn in wf as [_ wf].
      eapply wf_it_mkProd_or_LetIn in wf as [_ wf].
      rewrite /cstr_concl in wf.
      eapply wf_mkApps_inv in wf.
      now apply All_app in wf as [].
    - rename onProjections into on_projs.
      destruct (ind_projs hd) eqn:eqprojs. constructor.
      destruct (ind_ctors hd) as [|? [|]] eqn:Heq; try contradiction.
      destruct on_projs. rewrite eqprojs in on_projs.
      solve_all. eapply Alli_All; tea.
      intros. red in H.
      destruct (nth_error (smash_context _ _) _) eqn:Heq'; try contradiction.
      simpl in Heq. inv wfargs. clear X0.
      destruct H as [onna ->].
      eapply wf_subst.
      eapply wf_inds. eapply wf_subst.
      eapply wf_projs.
      eapply wf_lift.
      eapply All_app_inv in wfpars; [|eapply X].
      eapply (wf_smash_context _ _ []) in wfpars.
      2:constructor.
      eapply nth_error_all in Heq'; eauto.
      apply Heq'.
  Qed.

End WfLookup.

Section WfRed.
  Context {cf:checker_flags}.
  Context {Σ : global_env}.

  Lemma wf_red1 Γ M N :
    on_global_env cumul_gen wf_decl_pred Σ ->
    All (wf_decl Σ) Γ ->
    WfAst.wf Σ M ->
    red1 Σ Γ M N ->
    WfAst.wf Σ N.
  Proof using Type.
    intros wfΣ wfΓ wfM H.
    induction H using red1_ind_all in wfM, wfΓ |- *.
    all: inv wfM.
    all: try solve[ constructor; intuition auto with wf ].
    all:auto.

    - inv X. inv X0.
      eauto with wf.
    - auto with wf.
    - apply wf_lift.
      unfold option_map in H. destruct nth_error eqn:Heq; try discriminate.
      eapply nth_error_all in wfΓ; eauto. unfold wf_decl in *.
      apply some_inj in H; rewrite H in wfΓ; apply wfΓ.
    - unfold iota_red.
      eapply wf_mkApps_inv in X2.
      apply wf_subst. eapply All_rev. now eapply All_skipn.
      rewrite /expand_lets /expand_lets_k.
      apply wf_subst. apply wf_extended_subst. rewrite /bctx.
      eapply (wf_case_branch_context_gen (ind := (ci_ind ci, c))); tea.
      eapply declared_inductive_wf_ctors; tea. apply H0.
      eapply wf_lift. solve_all.
      now eapply All2_nth_error_Some_r in X3 as [cb [? []]]; tea.
    - eapply unfold_fix_wf in H; eauto. eapply wf_mkApps; auto.
    - econstructor; eauto. apply wf_mkApps_napp in X2 as [Hcof Hargs]; auto.
      eapply unfold_cofix_wf in H; eauto.
      apply wf_mkApps; intuition auto.
    - constructor; auto. apply wf_mkApps_napp in X as [Hcof Hargs]; auto.
      eapply unfold_cofix_wf in H; eauto.
      apply wf_mkApps; intuition auto.
    - apply wf_subst_instance.
      unfold declared_constant in H.
      eapply lookup_global_Some_iff_In_NoDup in H; eauto.
      2: destruct wfΣ; now eapply NoDup_on_global_decls.
      eapply lookup_on_global_env in H as [Σ' [onΣ' [ext prf]]]; eauto.
      destruct decl; simpl in *.
      subst cst_body0; simpl in *; unfold on_constant_decl in prf; cbn in prf.
      unfold wf_decl_pred in prf. intuition eauto using wf_extends with typeclass_instances.
    - apply wf_mkApps_inv in X.
      eapply nth_error_all in X; eauto.
    - simpl in *. econstructor; eauto. cbn.
      now rewrite -(OnOne2_length X).
      cbn. clear H1. induction X; constructor; inv X1; intuition auto.
    - econstructor; eauto; simpl in *.
      apply IHred1; eauto.
      apply All_app_inv => //.
      apply wf_case_predicate_context; auto.
      eapply declared_inductive_wf_params in isdecl; eauto.
      eapply declared_inductive_wf_indices; eauto; wf.
    - econstructor; eauto.
    - econstructor; eauto.
      assert (wf := wf_case_branches_context _ _ _ _ brs wfΣ isdecl X1).
      forward wf.
      eapply declared_inductive_wf_ctors; eauto; wf.
      solve_all.
      eapply OnOne2All_All2_All2; tea. cbn. intuition auto.
      now rewrite b0 in a1.
      apply b2 => //.
      apply All_app_inv => //.
    - now eapply wf_mkApps.
    - constructor; auto. induction X; auto; congruence.
      clear H X0 H0. induction X; inv X1; constructor; intuition auto; try congruence.
    - constructor.
      induction X; inv X0; constructor; intuition auto.
    - constructor; auto.
      induction X; inv X0; constructor; intuition auto; congruence.
    - constructor; auto. solve_all.
      pose proof X0 as H'. revert X0.
      apply (OnOne2_All_All X). clear X.
      intros [na bo ty ra] [nb bb tb rb] [[r ih] e] [? ?].
      simpl in *.
      inversion e. subst. clear e.
      intuition eauto.
      eapply ih. 2: assumption.
      solve_all.
      apply All_app_inv. 2: assumption.
      unfold fix_context. apply All_rev. eapply All_mapi.
      eapply All_Alli. 1: exact H'.
      cbn. unfold wf_decl. simpl.
      intros ? [? ? ? ?] ?. simpl in *.
      intuition eauto with wf.
    - constructor; auto.
      induction X; inv X0; constructor; intuition auto; congruence.
    - constructor; auto. solve_all.
      pose proof X0 as H'. revert X0.
      apply (OnOne2_All_All X). clear X.
      intros [na bo ty ra] [nb bb tb rb] [[r ih] e] [? ?].
      simpl in *.
      inversion e. subst. clear e.
      intuition eauto.
      eapply ih. 2: assumption.
      solve_all. apply All_app_inv. 2: assumption.
      unfold fix_context. apply All_rev. eapply All_mapi.
      eapply All_Alli. 1: exact H'.
      cbn. unfold wf_decl. simpl.
      intros ? [? ? ? ?] ?. simpl in *.
      intuition eauto with wf.
  Qed.


  Lemma wf_lift_wf n k t : WfAst.wf Σ (lift n k t) -> WfAst.wf Σ t.
  Proof using Type.
    induction t in n, k |- * using term_forall_list_rect; simpl in *;
      intros Hwf; inv Hwf; try constructor; eauto;
        repeat (unfold snd, on_snd in *; simpl in *; solve_all).

    - destruct t; try reflexivity. discriminate.
    - destruct l; simpl in *; congruence.
    - eapply All2_map_right_inv in X5. econstructor; eauto; solve_all.
      now rewrite map_length in H1.
  Qed.

  Lemma declared_projection_wf (p : projection)
          (mdecl : mutual_inductive_body) (idecl : one_inductive_body) cdecl pdecl :
      declared_projection Σ p mdecl idecl cdecl pdecl ->
      on_global_env cumul_gen wf_decl_pred Σ ->
      WfAst.wf Σ pdecl.(proj_type).
  Proof using Type.
    intros isdecl X.
    destruct isdecl as [[[Hmdecl Hidecl] Hcdecl] Hpdecl].
    eapply lookup_global_Some_iff_In_NoDup in Hmdecl; eauto.
    2: destruct X; now eapply NoDup_on_global_decls.
    destruct (lookup_on_global_env X Hmdecl) as [Σ' [wfΣ' [ext prf]]]; eauto.
    assert (wfpars := on_inductive_wf_params prf).
    eapply on_global_inductive_wf_bodies in prf => //.
    eapply nth_error_all in Hidecl; eauto. intuition auto.
    destruct Hidecl.
    eapply nth_error_all in wf_ind_projs0; eauto. intuition auto.
    eauto using wf_extends with typeclass_instances.
  Qed.

  Lemma declared_constant_wf cst decl :
    on_global_env cumul_gen wf_decl_pred Σ ->
    declared_constant Σ cst decl ->
    WfAst.wf Σ decl.(cst_type) *
    on_some_or_none (WfAst.wf Σ) decl.(cst_body).
  Proof using Type.
    intros wΣ h.
    unfold declared_constant in h.
    eapply lookup_global_Some_iff_In_NoDup in h; eauto.
    2: destruct wΣ; now eapply NoDup_on_global_decls.
    destruct (lookup_on_global_env wΣ h) as [Σ' [wΣ' [ext h']]].
    simpl in h'.
    destruct decl as [ty [bo|]]. all: cbn in *.
    - destruct h'. intuition eauto using wf_extends with typeclass_instances.
    - destruct h'. intuition eauto using wf_extends with typeclass_instances.
  Qed.

  Lemma wf_it_mkProd_or_LetIn_inv (Σ' : global_env_ext) Γ (wfΓ : wf_local Σ' Γ)
    : All_local_env_over typing
    (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ)
      (t T : term) (_ : Σ;;; Γ |- t : T) => WfAst.wf Σ t * WfAst.wf Σ T) Σ'
          Γ wfΓ
  -> forall t, WfAst.wf Σ' t -> WfAst.wf Σ' (it_mkProd_or_LetIn Γ t).
  Proof using Type.
    induction 1; simpl.
    - trivial.
    - intros t0 Ht0. apply IHX. constructor. apply Hs. assumption.
    - intros t0 Ht0. apply IHX. constructor. apply Hc. apply Hc. assumption.
  Qed.

  Lemma wf_Lambda_or_LetIn {d t} :
    wf_decl Σ d ->
    WfAst.wf Σ t ->
    WfAst.wf Σ (mkLambda_or_LetIn d t).
  Proof using Type.
    destruct d as [? [|] ?]; simpl; wf;
    unfold wf_decl, mkLambda_or_LetIn in *; simpl in *.
    constructor; intuition auto.
    constructor; intuition auto.
  Qed.

  Lemma wf_it_mkLambda_or_LetIn {Γ t} :
    All (wf_decl Σ) Γ ->
    WfAst.wf Σ t ->
    WfAst.wf Σ (it_mkLambda_or_LetIn Γ t).
  Proof using Type.
    intros wfΓ wft; induction wfΓ in t, wft |- *; simpl.
    - trivial.
    - apply IHwfΓ. now apply wf_Lambda_or_LetIn.
  Qed.

End WfRed.

#[global]
Hint Resolve wf_extends strictly_extends_decls_extends_decls strictly_extends_decls_extends_strictly_on_decls extends_decls_extends extends_strictly_on_decls_extends : wf.

Lemma cstr_branch_context_length ind mdecl cdecl :
  #|cstr_branch_context ind mdecl cdecl| = #|cdecl.(cstr_args)|.
Proof. rewrite /cstr_branch_context. now len. Qed.

Global Hint Rewrite cstr_branch_context_length : len.

(* Lemma case_branch_context_gen_length ind mdecl p puinst pctx :
  #|case_branch_context_gen ind mdecl p puinst pctx | = #|pctx|. *)

Section TypingWf.
  Context {cf}.

  Ltac specialize_goal :=
    repeat match goal with
    | H : ?P -> _, H' : ?P |- _ => specialize (H H')
    end.

  Lemma typing_wf_gen :
    env_prop
      (fun Σ Γ t T => WfAst.wf Σ t * WfAst.wf Σ T)
      (fun Σ Γ wfΓ => All (wf_decl Σ) Γ).
  Proof using Type.
    apply typing_ind_env; intros; auto with wf;
      specialize_goal;
      try solve [split; try constructor; intuition auto with wf].

    - eapply All_local_env_wf_decls.
      induction X; constructor; auto; red; intuition auto.
    - split; wf. apply wf_lift.
      apply (nth_error_all H X).
    - split. constructor; auto. wf.
      clear -X1.
      induction X1; constructor; now auto.
      destruct X0 as [_ X0].
      clear X H H0.
      induction X1; auto. apply IHX1.
      apply wf_subst. now destruct p0. destruct p. now inv w.
    - split. wf. apply wf_subst_instance. wf.
      eapply lookup_global_Some_iff_In_NoDup in H; eauto.
      2: destruct wfΣ; now eapply NoDup_on_global_decls.
      destruct (lookup_on_global_env X H) as [Σ' [wfΣ' [ext prf]]]; eauto.
      red in prf. destruct decl; destruct cst_body0; red in prf; simpl in *; wf.
      destruct prf as [s []]. wf.

    - split. wf. apply wf_subst_instance.
      eapply declared_inductive_wf; eauto.
      now eapply Forall_decls_on_global_wf.

    - split. wf. unfold type_of_constructor.
      apply wf_subst; auto with wf.
      apply wf_inds.
      apply wf_subst_instance.
      eapply declared_constructor_wf; eauto.
      now eapply Forall_decls_on_global_wf.

    - destruct X3 as [wfret wps].
      destruct X6 as [wfc wfapps].
      eapply wf_mkApps_inv in wfapps.
      eapply All_app in wfapps as [wfp wfindices].
      assert (All (wf_decl Σ) predctx).
      { now apply All_app in X4 as [? ?]. }
      split; [econstructor; simpl; eauto; solve_all|].
      eapply All2i_All2; tea; repeat intuition auto.
      apply wf_mkApps. subst ptm. wf. apply wf_it_mkLambda_or_LetIn; auto.
      apply All_app_inv; auto.
    - split. wf. apply wf_subst. solve_all. constructor. wf.
      apply wf_mkApps_inv in b. apply All_rev. solve_all.
      eapply declared_projection_wf in isdecl; eauto.
      now eapply wf_subst_instance.
      now eapply Forall_decls_on_global_wf.

    - subst types.
      clear H.
      split.
      + constructor.
        solve_all; destruct a, b.
        all: intuition.
      + eapply All_nth_error in X0; eauto.
        destruct X0 as [s ?]; intuition.

    - subst types.
      split.
      + constructor.
        solve_all; destruct a, b.
        all: intuition.
      + eapply All_nth_error in X0; eauto. destruct X0 as [s ?]; intuition.
  Qed.

  Lemma typing_all_wf_decl Σ (wfΣ : wf Σ.1) Γ (wfΓ : wf_local Σ Γ) :
    All (wf_decl Σ.1) Γ.
  Proof using Type.
    eapply (env_prop_wf_local typing_wf_gen); eauto.
  Qed.
  Hint Resolve typing_all_wf_decl : wf.

  Lemma typing_wf_sigma Σ (wfΣ : wf Σ) :
    on_global_env cumul_gen wf_decl_pred Σ.
  Proof using Type.
    intros.
    pose proof (env_prop_sigma typing_wf_gen _ wfΣ). red in X.
    do 2 red in wfΣ.
    eapply on_global_env_impl; eauto; simpl; intros.
    destruct T. red. apply X1. red. destruct X1 as [x [a wfs]]. split; auto.
  Qed.

  Lemma typing_wf Σ (wfΣ : wf Σ.1) Γ t T :
    Σ ;;; Γ |- t : T -> WfAst.wf Σ.1 t * WfAst.wf Σ.1 T.
  Proof using Type.
    intros. eapply typing_wf_gen in X; intuition eauto with wf.
  Qed.

  Lemma declared_minductive_wf {Σ : global_env} {mind mdecl} {wfΣ : wf Σ} :
    declared_minductive Σ mind mdecl ->
    All (wf_decl Σ) (ind_params mdecl) *
    All (@wf_inductive_body Σ) (ind_bodies mdecl).
  Proof using Type.
    intros declm.
    pose proof (typing_wf_gen (Env.empty_ext Σ) wfΣ _ localenv_nil _ _ (type_Prop _)) as [X _].
    eapply Forall_decls_on_global_wf in X.
    eapply lookup_global_Some_iff_In_NoDup in declm; eauto.
    2: destruct X; now eapply NoDup_on_global_decls.
    destruct (lookup_on_global_env X declm) as [? [? [ext ?]]]; eauto.
    split. eapply on_global_inductive_wf_params in o0. solve_all. eauto using wf_decl_extends with typeclass_instances.
    eapply on_global_inductive_wf_bodies in o0. solve_all.
    destruct X0; split; solve_all; eauto using wf_extends, wf_decl_extends with typeclass_instances.
  Qed.

  Lemma declared_inductive_wf_case_predicate_context
     {Σ : global_env} {wfΣ : wf Σ} {ind mdecl idecl p} :
    declared_inductive Σ ind mdecl idecl ->
    All (WfAst.wf Σ) p.(pparams) ->
    All (wf_decl Σ) (case_predicate_context ind mdecl idecl p).
  Proof using Type.
    intros decli.
    destruct (declared_minductive_wf (proj1 decli)) as [wfp wfb].
    intros wfpars.
    eapply wf_case_predicate_context => //.
    destruct decli as [declm hi].
    eapply nth_error_all in wfb; tea. apply wfb.
  Qed.

  Lemma declared_constructor_wf_case_branch_context
    {Σ} {wfΣ : wf Σ} {ind mdecl idecl cdecl p br} :
    declared_constructor Σ ind mdecl idecl cdecl ->
    All (WfAst.wf Σ) (pparams p) ->
    All (wf_decl Σ) (case_branch_context (fst ind) mdecl cdecl p br).
  Proof using Type.
    intros.
    eapply wf_case_branch_context_gen; tea => //.
    now apply typing_wf_sigma.
    destruct (declared_minductive_wf (proj1 (proj1 H))).
    destruct H as [[hm hnth] hnth'].
    eapply nth_error_all in a0; tea.
    now eapply wf_ind_ctor_args.
  Qed.

  Lemma mkApp_ex_wf Σ t u : WfAst.wf Σ (mkApp t u) ->
    exists f args, mkApp t u = tApp f args /\ ~~ isApp f.
  Proof using Type.
    induction t; simpl; try solve [eexists _, _; split; reflexivity].
    intros wf.
    eapply wf_inv in wf as [[[appt _] wft] wfargs].
    eapply All_app in wfargs as [wfargs wfu]. depelim wfu.
    forward IHt. eapply wf_mkApp; intuition auto.
    destruct IHt as [f [ar [eqf isap]]].
    eexists _, _; split; auto. rewrite appt //.
  Qed.

  Lemma decompose_app_mkApp f u :
    (decompose_app (mkApp f u)).2 <> [].
  Proof using Type.
    induction f; simpl; auto; try congruence.
    destruct args; simpl; congruence.
  Qed.

  Lemma mkApps_tApp' f u f' u' :
    ~~ isApp f' ->
    mkApp f u = tApp f' u' -> mkApps f [u] = mkApps f' u'.
  Proof using Type.
    intros.
    rewrite -(mkApp_mkApps f u []).
    simpl. rewrite H0.
    rewrite -(mkApps_tApp f') // ?H //.
    destruct u' => //.
    eapply (f_equal decompose_app) in H0.
    simpl in H0. pose proof (decompose_app_mkApp f u).
    rewrite H0 /= in H1. congruence.
  Qed.

  Lemma eq_decompose_app Σ x y :
    WfAst.wf Σ x -> WfAst.wf Σ y ->
    decompose_app x = decompose_app y -> x = y.
  Proof using Type.
    intros wfx; revert y.
    induction wfx using term_wf_forall_list_ind; intros [] wfy;
    eapply wf_inv in wfy; simpl in wfy; simpl;
    intros [= ?]; try intuition congruence.
  Qed.

  Lemma mkApp_ex t u : ∑ f args, mkApp t u = tApp f args.
  Proof using Type.
    induction t; simpl; try solve [eexists _, _; reflexivity].
  Qed.

  Lemma strip_casts_decompose_app Σ t :
    WfAst.wf Σ t ->
    forall f l, decompose_app t = (f, l) ->
    strip_casts t = mkApps (strip_casts f) (map strip_casts l).
  Proof using Type.
    intros wf.
    induction wf using term_wf_forall_list_ind; simpl; intros; auto; noconf H;
    try noconf H0;
      rewrite ?map_map_compose  ?compose_on_snd ?compose_map_def ?map_length;
        f_equal; solve_all; eauto.
    - now noconf H1.
    - now noconf H1.
    - now noconf H2.
  Qed.

  Lemma mkApps_tApp f args :
    ~~ isApp f ->
    ~~ is_empty args ->
    tApp f args = mkApps f args.
  Proof using Type.
    intros.
    destruct args, f; try discriminate; auto.
  Qed.

  Lemma strip_casts_mkApps_napp_wf Σ f u :
    ~~ isApp f -> WfAst.wf Σ f -> All (WfAst.wf Σ) u ->
    strip_casts (mkApps f u) = mkApps (strip_casts f) (map strip_casts u).
  Proof using Type.
    intros nisapp wf wf'.
    destruct u.
    simpl. auto.
    rewrite -(mkApps_tApp f (t :: u)) //.
  Qed.

  Lemma mkApp_mkApps f u : mkApp f u = mkApps f [u].
  Proof using Type. reflexivity. Qed.

  Lemma decompose_app_inv Σ f l hd args :
    WfAst.wf Σ f ->
    decompose_app (mkApps f l) = (hd, args) ->
    ∑ n, ~~ isApp hd /\ l = skipn n args /\ f = mkApps hd (firstn n args).
  Proof using Type.
    destruct (isApp f) eqn:Heq.
    revert l args hd.
    induction f; try discriminate. intros.
    simpl in X.
    move/wf_inv: X => /= [[[isAppf Hargs] wff] wfargs].
    rewrite mkApps_tApp ?isAppf in H => //. destruct args => //.
    rewrite -mkApps_app in H.
    rewrite decompose_app_mkApps ?isAppf in H; auto. noconf H.
    exists #|args|; split; auto. now rewrite isAppf.
    rewrite skipn_all_app.
    rewrite firstn_app. rewrite firstn_all2. lia.
    rewrite Nat.sub_diag firstn_O app_nil_r. split; auto.
    rewrite mkApps_tApp ?isAppf //. now destruct args.

    intros wff fl.
    rewrite decompose_app_mkApps in fl; auto. now apply negbT.
    inversion fl. subst; exists 0.
    split; auto. now eapply negbT.
  Qed.

  Lemma eq_tip_skipn {A} (x : A) n l : [x] = skipn n l ->
    exists l', l = l' ++ [x] /\ n = #|l'|.
  Proof using Type.
    induction l in n |- *. rewrite skipn_nil //.
    destruct n. simpl. destruct l => //.
    intros eq. noconf eq. exists []; split; auto.
    rewrite skipn_S. intros Hx.
    destruct (IHl _ Hx) as [l' [-> ->]].
    exists (a :: l'); split; reflexivity.
  Qed.

  Lemma strip_casts_mkApp_wf Σ f u :
    WfAst.wf Σ f -> WfAst.wf Σ u ->
    strip_casts (mkApp f u) = mkApp (strip_casts f) (strip_casts u).
  Proof using Type.
    intros wf wf'.
    assert (wfa : WfAst.wf Σ (mkApp f u)). now apply wf_mkApp.
    destruct (mkApp_ex_wf Σ f u wfa) as [f' [args [eq isapp]]].
    eapply (f_equal decompose_app) in eq. simpl in eq.
    epose proof (strip_casts_decompose_app Σ _ wfa _ _ eq).
    rewrite H.
    rewrite mkApp_mkApps in eq.
    destruct (decompose_app_inv Σ _ _ _ _ wf eq) as [n [ng [stripeq stripf]]].
    apply eq_tip_skipn in stripeq. destruct stripeq as [l' [eqargs eqn]].
    subst n args. rewrite firstn_app_left // in stripf. subst f.
    eapply wf_mkApps_napp in wf as [wff' wfl] => //.
    rewrite (strip_casts_mkApps_napp_wf Σ) //.
    now rewrite mkApp_mkApps -mkApps_app map_app.
  Qed.

  Lemma strip_casts_mkApps_wf Σ f u :
    WfAst.wf Σ f -> All (WfAst.wf Σ) u ->
    strip_casts (mkApps f u) = mkApps (strip_casts f) (map strip_casts u).
  Proof using Type.
    intros wf wf'. induction wf' in f, wf |- *.
    simpl. auto.
    rewrite -mkApps_mkApp IHwf'.
    apply wf_mkApp; auto with wf.
    rewrite (strip_casts_mkApp_wf Σ) //.
    now rewrite mkApps_mkApp.
  Qed.
End TypingWf.
