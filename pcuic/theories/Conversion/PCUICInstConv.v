(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICTactics PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICTyping PCUICReduction PCUICCumulativity
  PCUICEquality PCUICGlobalEnv PCUICClosed PCUICClosedConv PCUICClosedTyp PCUICEquality PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICWeakeningConv PCUICInstDef PCUICWeakeningTyp
  PCUICGuardCondition PCUICUnivSubstitutionConv PCUICOnFreeVars PCUICOnFreeVarsConv.


From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".
Implicit Types cf : checker_flags.

(** * Type preservation for σ-calculus instantiation *)

Open Scope sigma_scope.

Definition inst_constructor_body mdecl f c :=
  map_constructor_body #|mdecl.(ind_params)| #|mdecl.(ind_bodies)|
   (fun k => inst  (up k f)) c.

Definition rigid_head t :=
  match t with
  | tVar _
  | tSort _
  | tConst _ _
  | tInd _ _
  | tConstruct _ _ _ => true
  | _ => false
  end.



Lemma inst_context_snoc s Γ d : inst_context s (Γ ,, d) = inst_context s Γ ,, map_decl (inst (⇑^#|Γ| s)) d.
Proof.
  unfold snoc. apply inst_context_snoc0.
Qed.
#[global]
Hint Rewrite inst_context_snoc : sigma.

Lemma inst_context_alt s Γ :
  inst_context s Γ =
  mapi (fun k' d => map_decl (inst (⇑^(Nat.pred #|Γ| - k') s)) d) Γ.
Proof.
  unfold inst_context. apply: fold_context_k_alt.
Qed.

Lemma inst_context_length s Γ : #|inst_context s Γ| = #|Γ|.
Proof. apply fold_context_k_length. Qed.
#[global]
Hint Rewrite inst_context_length : sigma wf.

(** Substitution in contexts is just a particular kind of instantiation. *)

Lemma subst_context_inst_context s k Γ :
  subst_context s k Γ = inst_context (⇑^k (s ⋅n ids)) Γ.
Proof.
  rewrite /subst_context.
  now setoid_rewrite subst_inst'; setoid_rewrite Upn_Upn.
Qed.

Lemma subst_context0_inst_context s Γ :
  subst_context s 0 Γ = inst_context (s ⋅n ids) Γ.
Proof.
  now rewrite subst_context_inst_context Upn_0.
Qed.

Lemma inst_mkApps f l σ : (mkApps f l).[σ] = mkApps f.[σ] (map (inst σ) l).
Proof.
  induction l in f |- *; simpl; [auto|]. rewrite IHl.
  now autorewrite with sigma.
Qed.
#[global]
Hint Rewrite inst_mkApps : sigma.

Lemma lift0_inst n t : lift0 n t = t.[↑^n].
Proof. by rewrite lift_rename rename_inst lift_renaming_0 -ren_shiftk. Qed.
#[global]
Hint Rewrite lift0_inst : sigma.

Lemma rename_decl_inst_decl : forall f d, rename_decl f d = inst_decl (ren f) d.
Proof.
  intros f d.
  unfold rename_decl, inst_decl.
  destruct d. unfold map_decl.
  autorewrite with sigma.
  f_equal.
Qed.

#[global]
Hint Rewrite rename_decl_inst_decl : sigma.

Lemma rename_context_inst_context :
  forall f Γ,
    rename_context f Γ = inst_context (ren f) Γ.
Proof.
  intros f Γ.
  induction Γ.
  - reflexivity.
  - autorewrite with sigma. rewrite IHΓ. f_equal.
    destruct a. unfold inst_decl. unfold map_decl. simpl.
    f_equal.
    + destruct decl_body. 2: reflexivity.
      simpl. f_equal. autorewrite with sigma.
      now rewrite -up_Upn ren_shiftn.
    + autorewrite with sigma.
      now rewrite -up_Upn ren_shiftn.
Qed.
#[global]
Hint Rewrite rename_context_inst_context : sigma.

Lemma inst_subst0 a b τ : (subst0 a b).[τ] = (subst0 (map (inst τ) a) b.[⇑^#|a| τ]).
Proof.
  simpl. rewrite !subst_inst !Upn_0. sigma.
  apply inst_ext.
  rewrite Upn_comp //; now len.
Qed.
#[global]
Hint Rewrite inst_subst0 : sigma.

Lemma subst10_inst a b τ : b {0 := a}.[τ] = (b.[⇑ τ] {0 := a.[τ]}).
Proof.
  unfold subst10. sigma. simpl. rewrite subst_consn_tip /= //.
Qed.
#[global]
Hint Rewrite subst10_inst : sigma.

Lemma inst_closed0 σ t : closedn 0 t -> t.[σ] = t.
Proof. intros. rewrite -{2}[t](inst_closed σ 0) //. now sigma. Qed.

Lemma mapi_context_eqP_onctx_k_spec {P : nat -> term -> Type} {k} {ctx} {f g : nat -> term -> term} :
  onctx_k P k ctx ->
  (forall i x, P (i + k) x -> f i x = g i x) ->
  mapi_context f ctx = mapi_context g ctx.
Proof.
  move=> Ha Hfg.
  rewrite !mapi_context_fold.
  rewrite !fold_context_k_alt.
  eapply Alli_mapi_spec; tea.
  move=> /= n x ond.
  eapply map_decl_eq_spec; tea.
  intros t Ht.
  now eapply Hfg.
Qed.

Lemma inst_ext_closed s s' k t :
  (forall x, x < k -> s x = s' x) ->
  closedn k t ->
  inst s t = inst s' t.
Proof.
  clear.
  intros Hs clt. revert k t clt s s' Hs.
  apply: term_closedn_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].
  - f_equal; eauto.
    eapply H0; eauto. intros. eapply up_ext_closed; eauto.
  - f_equal; eauto. now eapply H0, (up_ext_closed _ 1).
  - f_equal; eauto.
    now eapply H1, (up_ext_closed _ 1).
  - destruct X as [ppars pret].
    f_equal; eauto.
    * unfold test_predicate in *. simpl in *. solve_all.
      eapply map_predicate_shift_eq_spec; solve_all.
      now eapply b, up_ext_closed.
    * red in X0.
      eapply All_map_eq. solve_all.
      eapply map_branch_shift_eq_spec; solve_all.
      now eapply b0, up_ext_closed.
  - f_equal; eauto. red in X. solve_all.
    eapply b; eauto. len. now apply up_ext_closed.
  - f_equal; eauto. red in X. solve_all.
    eapply b; eauto. len; now apply up_ext_closed.
Qed.

Lemma subst_id s Γ t :
  closedn #|s| t ->
  assumption_context Γ ->
  s = List.rev (to_extended_list Γ) ->
  subst s 0 t = t.
Proof.
  intros cl ass eq.
  autorewrite with sigma.
  rewrite -{2}(subst_ids t).
  eapply inst_ext_closed; eauto.
  intros.
  unfold ids, subst_consn. simpl.
  destruct (snd (nth_error_Some' s x) H). rewrite e.
  subst s.
  rewrite /to_extended_list /to_extended_list_k in e.
  rewrite List.length_rev in cl, H. autorewrite with len in *.
  rewrite reln_alt_eq in e.
  rewrite app_nil_r List.rev_involutive in e.
  clear -ass e. revert e.
  rewrite -{2}(Nat.add_0_r x).
  generalize 0.
  induction Γ in x, ass, x0 |- * => n.
  - simpl in *. rewrite nth_error_nil => //.
  - depelim ass; simpl.
    destruct x; simpl in *; try congruence.
    move=> e; specialize (IHΓ ass); simpl in e.
    specialize (IHΓ _ _ _ e). subst x0. f_equal. lia.
Qed.

Lemma map_inst_idsn l l' n :
  #|l| = n ->
  map (inst (l ⋅n l')) (idsn n) = l.
Proof.
  induction n in l, l' |- *.
  - destruct l => //.
  - destruct l as [|l a] using rev_case => // /=.
    rewrite length_app /= Nat.add_1_r => [=].
    intros; subst n.
    simpl. rewrite map_app.
    f_equal; auto.
    + rewrite subst_consn_app.
      now apply IHn.
    + simpl.
      rewrite subst_consn_lt /= ?List.length_app /= //; try lia.
      now rewrite /subst_fn nth_error_app_ge /= // Nat.sub_diag /=.
Qed.

Lemma inst_decl_closed :
  forall σ k d,
    closed_decl k d ->
    inst_decl (⇑^k σ) d = d.
Proof.
  intros σ k d.
  move/(ondeclP reflectT_pred) => ond.
  eapply map_decl_id_spec; tea => /=.
  apply inst_closed.
Qed.

Lemma closed_tele_inst :
  forall σ ctx,
    closed_ctx ctx ->
    mapi (fun i decl => inst_decl (⇑^i σ) decl) (List.rev ctx) =
    List.rev ctx.
Proof.
  intros σ ctx.
  rewrite test_context_k_eq.
  rewrite /mapi. simpl. generalize 0.
  induction ctx using rev_ind; try easy.
  move => n.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move /andb_and => [closedx Hctx].
  rewrite inst_decl_closed //.
  f_equal. now rewrite IHctx.
Qed.

Lemma inst_closedn_ctx f n Γ :
  closedn_ctx n Γ ->
  inst_context (⇑^n f) Γ = Γ.
Proof.
  rewrite test_context_k_eq.
  apply alli_fold_context_k.
  intros. rewrite -Upn_Upn Nat.add_comm.
  now rewrite [map_decl _ _]inst_decl_closed.
Qed.

Lemma typed_inst {cf} :
  forall Σ Γ t T k σ,
    wf Σ.1 ->
    k >= #|Γ| ->
    Σ ;;; Γ |- t : T ->
    T.[⇑^k σ] = T /\ t.[⇑^k σ] = t.
Proof.
  intros Σ Γ t T k σ hΣ hk h.
  apply typing_wf_local in h as hΓ.
  apply typecheck_closed in h. all: eauto.
  destruct h as [_ [hclΓ hcl]].
  rewrite -> andb_and in hcl. destruct hcl as [clt clT].
  pose proof (closed_upwards k clt) as ht.
  pose proof (closed_upwards k clT) as hT.
  forward ht by lia.
  forward hT by lia.
  rewrite !inst_closed. all: auto.
Qed.

Lemma inst_wf_local {cf} :
  forall Σ Γ σ,
    wf Σ.1 ->
    wf_local Σ Γ ->
    inst_context σ Γ = Γ.
Proof.
  intros Σ Γ σ hΣ h.
  induction h.
  - reflexivity.
  - unfold inst_context, snoc. rewrite fold_context_k_snoc0.
    unfold snoc. f_equal. all: auto.
    unfold map_decl. simpl. unfold vass. f_equal.
    destruct t0 as (_ & s & ht & _). eapply typed_inst. all: eauto.
  - unfold inst_context, snoc. rewrite fold_context_k_snoc0.
    unfold snoc. f_equal. all: auto.
    destruct t0 as (hb & s & ht & _). cbn in hb.
    unfold map_decl. simpl. unfold vdef. f_equal.
    + f_equal. eapply typed_inst. all: eauto.
    + eapply typed_inst. all: eauto.
Qed.

Lemma inst_destArity :
  forall ctx t σ args s,
    destArity ctx t = Some (args, s) ->
    destArity (inst_context σ ctx) t.[⇑^#|ctx| σ] =
    Some (inst_context σ args, s).
Proof.
  intros ctx t σ args s h.
  induction t in ctx, σ, args, s, h |- * using term_forall_list_ind.
  all: simpl in *. all: try discriminate.
  - inversion h. reflexivity.
  - erewrite <- IHt2 ; try eassumption.
    simpl. autorewrite with sigma. reflexivity.
  - erewrite <- IHt3. all: try eassumption.
    simpl. autorewrite with sigma. reflexivity.
Qed.

Lemma Up_subst_instance u σ :
  ⇑ (subst_instance u ∘ σ) ≐1 subst_instance u ∘ ⇑ σ.
Proof.
  intros i => /=.
  rewrite - !up_Up /up.
  nat_compare_specs => //.
  now rewrite rename_subst_instance.
Qed.

Lemma upn_subst_instance u n σ :
  up n (subst_instance u ∘ σ) ≐1 subst_instance u ∘ up n σ.
Proof.
  intros i => /=.
  rewrite /up.
  nat_compare_specs => //.
  now rewrite rename_subst_instance.
Qed.

Lemma Upn_subst_instance u n σ :
  ⇑^n (subst_instance u ∘ σ) ≐1 subst_instance u ∘ ⇑^n σ.
Proof.
  rewrite - !up_Upn. rewrite upn_subst_instance.
  intros i. now rewrite up_Upn.
Qed.

Lemma inst_subst_instance :
  forall u t σ,
    (subst_instance u t).[subst_instance u ∘ σ] =
    subst_instance u t.[σ].
Proof.
  intros u t σ.
  rewrite /subst_instance /=.
  induction t in σ |- * using term_forall_list_ind.
  all: try solve [
    simpl ;
    rewrite ?IHt ?IHt1 ?IHt2 ;
    easy
  ].
  all: simpl. all: auto.
  all: autorewrite with map.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  all: try now rewrite IHt1; sigma; rewrite-IHt2 -?IHt3 ?Up_subst_instance.
  - simpl. rewrite IHt. f_equal.
    * unfold map_predicate, inst_predicate; destruct p; simpl; f_equal; solve_all;
      now rewrite upn_subst_instance.
    * red in X0; solve_all.
      unfold inst_branch, map_branch. simpl in *.
      f_equal; solve_all; now rewrite upn_subst_instance.
  - f_equal. solve_all.
    now rewrite upn_subst_instance.
  - f_equal; solve_all.
    now rewrite upn_subst_instance.
Qed.

Lemma map_vass_map_def_inst g l s :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (inst s) g) l)) =
  (mapi (fun i d => map_decl (inst (⇑^i s)) d)
        (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite !lift0_inst.
  now sigma.
Qed.

Lemma inst_fix_context:
  forall (mfix : list (def term)) s,
    fix_context (map (map_def (inst s) (inst (⇑^#|mfix| s))) mfix) =
    inst_context s (fix_context mfix).
Proof.
  intros mfix s. unfold fix_context.
  rewrite map_vass_map_def_inst rev_mapi.
  fold (fix_context mfix).
  rewrite (inst_context_alt s (fix_context mfix)).
   now rewrite mapi_length fix_context_length.
Qed.

Lemma inst_fix_context_up :
  forall (mfix : list (def term)) s,
    fix_context (map (map_def (inst s) (inst (up #|mfix| s))) mfix) =
    inst_context s (fix_context mfix).
Proof.
  intros mfix s. unfold fix_context.
  rewrite map_vass_map_def_inst rev_mapi.
  fold (fix_context mfix).
  rewrite (inst_context_alt s (fix_context mfix)).
   now rewrite mapi_length fix_context_length.
Qed.

Lemma mapi_context_inst σ ctx :
  mapi_context (fun k : nat => inst (up k σ)) ctx =
  inst_context σ ctx.
Proof.
  now rewrite mapi_context_fold; setoid_rewrite up_Upn.
Qed.

Lemma inst_predicate_pcontext f (p : predicate term) :
  (pcontext p) = pcontext (inst_predicate f p).
Proof. rewrite /inst_predicate /= //. Qed.

Lemma inst_predicate_preturn f p :
  inst (⇑^#|p.(pcontext)| f) (preturn p) =
  preturn (inst_predicate f p).
Proof. rewrite -up_Upn. reflexivity. Qed.

Lemma inst_mkLambda_or_LetIn f d t :
  inst f (mkLambda_or_LetIn d t) =
  mkLambda_or_LetIn (inst_decl f d) (inst (⇑ f) t).
Proof.
  destruct d as [na [] ty]; rewrite /= /mkLambda_or_LetIn /=; f_equal; now rewrite up_Up.
Qed.

Lemma inst_it_mkLambda_or_LetIn f ctx t :
  inst f (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (inst_context f ctx) (inst (⇑^#|ctx| f) t).
Proof.
  move: t.
  induction ctx; simpl => t.
  - now rewrite Upn_0.
  - rewrite /= IHctx inst_context_snoc /snoc /=. f_equal.
    now rewrite inst_mkLambda_or_LetIn /=; sigma.
Qed.

Lemma inst_reln f ctx n acc :
  forallb (closedn (n + #|ctx|)) acc ->
  map (inst (⇑^(n + #|ctx|) f)) (reln acc n ctx) =
  reln acc n ctx.
Proof.
  induction ctx in n, acc |- *; simpl; auto.
  - intros clacc. solve_all.
    now rewrite inst_closed.
  - intros clacc.
    destruct a as [? [] ?].
    * rewrite Nat.add_succ_r.
      change (S (n + #|ctx|)) with (S n + #|ctx|).
      rewrite Nat.add_1_r IHctx // /= -Nat.add_succ_r //.
    * rewrite Nat.add_succ_r Nat.add_1_r. rewrite (IHctx (S n)) /= // -Nat.add_succ_r //.
      simpl. rewrite clacc andb_true_r.
      eapply Nat.ltb_lt. lia.
Qed.

Lemma inst_to_extended_list f ctx :
  map (inst (⇑^#|ctx| f)) (to_extended_list ctx) = to_extended_list ctx.
Proof.
  unfold to_extended_list, to_extended_list_k.
  now apply (inst_reln _ _ 0).
Qed.

Lemma inst_subst :
  forall f s n t,
    inst (⇑^n f) (subst s n t) =
    subst (map (inst f) s) n (inst (⇑^n (⇑^#|s| f)) t).
Proof.
  intros f s n t.
  autorewrite with sigma.
  eapply inst_ext. intro i. unfold Upn.
  unfold subst_consn, shiftk, subst_compose. simpl.
  destruct (Nat.ltb_spec i n).
  - rewrite idsn_lt //. simpl.
    rewrite idsn_lt //.
  - rewrite nth_error_idsn_None //. len.
    rewrite !inst_assoc. unfold subst_compose. simpl.
    destruct (Nat.ltb_spec (i - n) #|s|).
    * rewrite idsn_lt //. simpl.
      rewrite nth_error_idsn_None //; try lia.
      rewrite nth_error_map.
      replace (n + (i - n) - n) with (i - n) by lia.
      destruct nth_error eqn:hnth => /=.
      ** sigma. apply inst_ext.
        intros k. cbn.
        elim: (Nat.ltb_spec (n + k) n); try lia.
        intros. eapply nth_error_Some_length in hnth.
        rewrite nth_error_idsn_None //. unfold subst_compose.
        lia_f_equal.
      ** eapply nth_error_None in hnth. lia.
    * len.
      rewrite nth_error_idsn_None; try lia.
      rewrite inst_assoc. simpl.
      destruct nth_error eqn:hnth.
      ** eapply nth_error_Some_length in hnth. lia.
      ** simpl.
        eapply nth_error_None in hnth.
        rewrite nth_error_idsn_None; try lia.
        unfold subst_compose. simpl.
        assert (n + (i - n - #|s|) - n = (i - n - #|s|)) as -> by lia.
        apply inst_ext => k.
        rewrite nth_error_idsn_None //; try lia.
        destruct nth_error eqn:hnth'; simpl; len.
        eapply nth_error_Some_length in hnth'. len in hnth'.
Qed.

Lemma inst_context_subst_k f s k Γ :
  inst_context (up k f) (subst_context s k Γ) =
  subst_context (map (inst f) s) k (inst_context (⇑^(k + #|s|) f) Γ).
Proof.
  rewrite !inst_context_alt !subst_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /subst_decl !compose_map_decl.
  apply map_decl_ext => t.
  len.
  generalize (Nat.pred #|Γ| - i).
  intros. rewrite up_Upn -Upn_Upn inst_subst.
  now sigma.
Qed.

Lemma inst_context_subst f s Γ :
  inst_context f (subst_context s 0 Γ) =
  subst_context (map (inst f) s) 0 (inst_context (⇑^#|s| f) Γ).
Proof.
  now rewrite -inst_context_subst_k up_Upn Upn_0.
Qed.

Lemma closedn_ctx_expand_lets (k : nat) (Γ Δ : list context_decl) :
  closedn_ctx k (Γ ,,, Δ) ->
  closedn_ctx (k + context_assumptions Γ) (expand_lets_ctx Γ Δ).
Proof.
  rewrite closedn_ctx_app.
  move/andP => [HΓ HΔ].
  now apply closedn_ctx_expand_lets.
Qed.

Lemma inst_case_predicate_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  inst_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (inst_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite /inst_context.
  rewrite -map2_set_binder_name_fold //.
  - len. len.
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal. rewrite -/(inst_context f _).
    rewrite /pre_case_predicate_context_gen /inst_case_context.
    rewrite /ind_predicate_context /= !subst_instance_cons !subst_context_snoc inst_context_snoc.
    rewrite inst_context_subst map_rev. f_equal.
    * rewrite /map_decl /=. f_equal.
      len. rewrite inst_closedn_ctx //.
      epose proof (closedn_ctx_expand_lets 0 (ind_params mdecl) (ind_indices idecl)
      (declared_inductive_closed_pars_indices decli)).
      simpl in H.
      rewrite closedn_subst_instance_context.
      rewrite (wf_predicate_length_pars wfp).
      now rewrite (declared_minductive_ind_npars decli).
    * rewrite /map_decl /= /subst_decl /map_decl /=.
      f_equal. len. rewrite -map_rev.
      rewrite subst_instance_mkApps.
      rewrite !subst_inst inst_assoc.
      eapply (inst_ext_closed _ _ (context_assumptions (ind_params mdecl) + #|ind_indices idecl|)).
      + intros x hx.
        rewrite Upn_compose subst_consn_compose. sigma.
        rewrite Upn_subst_consn_lt; len.
        { rewrite ?(wf_predicate_length_pars wfp).
          rewrite (declared_minductive_ind_npars decli). lia. }
        rewrite Upn_subst_consn_lt //; len.
        { rewrite ?(wf_predicate_length_pars wfp).
          rewrite (declared_minductive_ind_npars decli). lia. }
      + rewrite closedn_mkApps /=.
        rewrite subst_instance_to_extended_list.
        relativize (_ + _); [eapply closedn_to_extended_list|].
        now len.
Qed.

Lemma inst_wf_predicate mdecl idecl f p :
  wf_predicate mdecl idecl p ->
  wf_predicate mdecl idecl (inst_predicate f p).
Proof.
  intros []. split => //. now len.
Qed.

Lemma inst_wf_branch cdecl f br :
  wf_branch cdecl br ->
  wf_branch cdecl (map_branch_shift inst up f br).
Proof.
  unfold wf_branch, wf_branch_gen; auto.
Qed.

Lemma inst_wf_branches cdecl f brs :
  wf_branches cdecl brs ->
  wf_branches cdecl (map (fun br => map_branch_shift inst up f br) brs).
Proof.
  unfold wf_branches, wf_branches_gen.
  intros h. solve_all.
Qed.

Lemma inst_closed_decl k f d : closed_decl k d -> map_decl (inst (up k f)) d = d.
Proof.
  rewrite /map_decl.
  destruct d as [? [] ?] => /=.
  - move/andP=> [] clt clty.
    rewrite up_Upn !inst_closed //.
  - move=> clt. rewrite !up_Upn !inst_closed //.
Qed.

Lemma inst_closed_constructor_body mdecl cdecl f :
  closed_constructor_body mdecl cdecl ->
  inst_constructor_body mdecl f cdecl = cdecl.
Proof.
  rewrite /closed_constructor_body /inst_constructor_body /map_constructor_body.
  move/andP=> [] /andP [] clctx clind clty.
  destruct cdecl; cbn -[fold_context_k] in *; f_equal.
  + move: clctx. rewrite test_context_k_eq.
    apply alli_fold_context_k => i d cldecl.
    rewrite inst_closed_decl //.
    red; rewrite -cldecl; lia_f_equal.
  + solve_all. rewrite up_Upn inst_closed //.
    red. rewrite -H. lia_f_equal.
  + now rewrite up_Upn inst_closed.
Qed.

Lemma inst_cstr_args mdecl f cdecl :
  cstr_args (inst_constructor_body mdecl f cdecl) =
  inst_context (up (#|mdecl.(ind_params)| + #|ind_bodies mdecl|) f) (cstr_args cdecl).
Proof.
  simpl. unfold inst_context.
  apply fold_context_k_ext => i t.
  now rewrite !up_Upn !Upn_Upn.
Qed.

Lemma inst_closedn_terms f n ts :
  forallb (closedn n) ts -> map (inst (up n f)) ts = ts.
Proof.
  solve_all.
  now rewrite up_Upn inst_closed.
Qed.

Lemma inst_closed_extended_subst f Γ :
  closed_ctx Γ ->
  map (inst (up (context_assumptions Γ) f)) (extended_subst Γ 0) = extended_subst Γ 0.
Proof.
  intros cl. apply inst_closedn_terms.
  now apply (closedn_extended_subst_gen Γ 0 0).
Qed.

Lemma inst_lift :
  forall f n k t,
    inst (⇑^(n + k) f) (lift n k t) = lift n k (inst (⇑^k f) t).
Proof.
  intros f n k t. sigma.
  eapply inst_ext.
  rewrite -Upn_Upn Nat.add_comm Upn_Upn.
  now rewrite !Upn_compose shiftn_Upn.
Qed.

Lemma inst_context_lift f n k Γ :
  inst_context (up (n + k) f) (lift_context n k Γ) =
  lift_context n k (inst_context (up k f) Γ).
Proof.
  rewrite !inst_context_alt !lift_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /lift_decl !compose_map_decl.
  apply map_decl_ext => t; len.
  generalize (Nat.pred #|Γ| - i).
  intros.
  rewrite !up_Upn -Upn_Upn.
  rewrite (Nat.add_comm n k) Nat.add_assoc Nat.add_comm.
  now rewrite inst_lift Upn_Upn.
Qed.

Lemma inst_inds f ind pu bodies : map (inst f) (inds ind pu bodies) = inds ind pu bodies.
Proof.
  unfold inds.
  induction #|bodies|; simpl; auto. f_equal.
  apply IHn.
Qed.

Lemma closed_ctx_args n bctx ctx :
  #|bctx| = #|ctx| ->
  closedn_ctx n ctx ->
  closedn_ctx n (map2 set_binder_name bctx ctx).
Proof.
  induction ctx in bctx |- *; destruct bctx; simpl; auto.
  move=> [=] hlen.
  move/andP=> [cla clctx].
  rewrite IHctx // /=.
  rewrite map2_length //.
  now rewrite hlen.
Qed.

Lemma inst_context_set_binder_name f ctx ctx' :
  #|ctx| = #|ctx'| ->
  inst_context f (map2 set_binder_name ctx ctx') =
  map2 set_binder_name ctx (inst_context f ctx').
Proof.
  induction ctx in ctx' |- *; destruct ctx'; simpl; auto.
  rewrite !inst_context_snoc /= /snoc.
  intros [=]. f_equal; auto.
  rewrite /set_binder_name /map_decl /=; f_equal.
  - rewrite map2_length // H0 //.
  - rewrite map2_length // H0 //.
Qed.

Lemma inst_context_subst_instance f u Γ :
  inst_context (subst_instance u ∘ f) (subst_instance u Γ) =
  subst_instance u (inst_context f Γ).
Proof.
  unfold inst_context.
  rewrite fold_context_k_map // [subst_instance _ _]map_fold_context_k.
  apply fold_context_k_ext => k x.
  rewrite Upn_subst_instance.
  now rewrite inst_subst_instance.
Qed.

Lemma inst_inst_case_context f pars puinst ctx :
  on_free_vars_ctx (closedP #|pars| xpredT) ctx ->
  inst_context f (inst_case_context pars puinst ctx) =
  inst_case_context (map (inst f) pars) puinst
    (inst_context (⇑^#|pars| f) ctx).
Proof.
  intros clctx. rewrite /inst_case_context.
  rewrite inst_context_subst map_rev List.length_rev.
  rewrite !inst_closedn_ctx //.
  - now rewrite closedn_subst_instance_context closedn_ctx_on_free_vars.
  - now rewrite closedn_ctx_on_free_vars.
Qed.

Lemma inst_inst_case_context_wf f pars puinst ctx :
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pars| ctx ->
  inst_context f (inst_case_context pars puinst ctx) =
    inst_case_context (map (inst f) pars) puinst ctx.
Proof.
  rewrite test_context_k_closed_on_free_vars_ctx => H.
  rewrite inst_inst_case_context //. f_equal.
  now rewrite inst_closedn_ctx // closedn_ctx_on_free_vars.
Qed.

Lemma inst_cstr_branch_context f ind mdecl cdecl :
  closed_ctx (ind_params mdecl) ->
  inst_context (up (context_assumptions (ind_params mdecl)) f) (cstr_branch_context ind mdecl cdecl) =
  cstr_branch_context ind mdecl (inst_constructor_body mdecl f cdecl).
Proof.
  intros clctx.
  rewrite /cstr_branch_context.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite inst_context_subst.
  rewrite inst_closed_extended_subst //. f_equal.
  rewrite -up_Upn up_up Nat.add_comm. len.
  rewrite inst_context_lift. f_equal.
  rewrite inst_context_subst_k inst_inds /=; len.
  setoid_rewrite <-Nat.add_assoc. f_equal.
  setoid_rewrite <-up_up. now repeat setoid_rewrite up_Upn.
Qed.

Lemma closedn_ctx_cstr_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {c mdecl idecl cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closedn_ctx (context_assumptions (ind_params mdecl)) (cstr_branch_context c.1 mdecl cdecl).
Proof.
  intros cl.
  rewrite /cstr_branch_context.
  apply (closedn_ctx_expand_lets 0).
  rewrite closedn_ctx_app.
  rewrite (declared_inductive_closed_params cl) /=.
  eapply (closedn_ctx_subst 0) => /=; len.
  { rewrite Nat.add_comm (declared_constructor_closed_args cl) //. }
  eapply closed_inds.
Qed.

Lemma inst_case_branch_context_gen {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {ind i idecl mdecl f p bctx cdecl} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  #|bctx| = #|cstr_args cdecl| ->
  #|pparams p| = context_assumptions (ind_params mdecl) ->
  inst_context f (case_branch_context ind mdecl p bctx cdecl) =
  case_branch_context ind mdecl (inst_predicate f p) bctx
    (inst_constructor_body mdecl f cdecl).
Proof.
  intros declc hlen hlen'.
  unfold case_branch_context, case_branch_context_gen, pre_case_branch_context_gen.
  rewrite inst_context_set_binder_name; len => //. f_equal.
  rewrite inst_inst_case_context_wf.
  { rewrite test_context_k_closed_on_free_vars_ctx.
    rewrite -closedn_ctx_on_free_vars hlen'.
    apply (closedn_ctx_cstr_branch_context declc). }
  f_equal. f_equal.
  rewrite inst_closed_constructor_body //.
  apply (declared_constructor_closed declc).
Qed.
Lemma up_0 f : up 0 f ≐1 f.
Proof.
  rewrite /up /=; setoid_rewrite Nat.sub_0_r.
  intros i. now rewrite rename_ren_id.
Qed.

Lemma forallb_map_spec {A B : Type} {p : A -> bool}
      {l : list A} {f g : A -> B} :
  (forall x : A, p x -> f x = g x) ->
  forallb p l ->
  map f l = map g l.
Proof.
  induction l; simpl; trivial.
  rewrite andb_and. intros Hx [px pl].
  f_equal. - now apply Hx. - now apply IHl.
Qed.

Lemma inst_case_branch_type {cf} {Σ : global_env_ext} {wfΣ : wf Σ} f (ci : case_info) i mdecl idecl p br cdecl :
  declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let pctx := case_predicate_context ci mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn pctx (preturn p) in
  let p' := inst_predicate f p in
  let pctx' := case_predicate_context ci mdecl idecl p' in
  let ptm' := it_mkLambda_or_LetIn pctx' (preturn p') in
  case_branch_type ci mdecl idecl
     (inst_predicate f p)
     (inst_branch f br)
     ptm' i (inst_constructor_body mdecl f cdecl) =
  map_pair (inst_context f) (inst (up #|bcontext br| f))
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite (inst_case_branch_context_gen decli) //.
  - len. apply (wf_branch_length wfb).
  - rewrite -(declared_minductive_ind_npars decli).
    apply (wf_predicate_length_pars wfp).
  - f_equal.
    rewrite inst_mkApps map_app map_map_compose.
    rewrite (wf_branch_length wfb).
    f_equal.
    * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !inst_it_mkLambda_or_LetIn.
      rewrite !lift_rename. f_equal.
      ++ rewrite /p'. len.
        epose proof (inst_context_lift f #|cstr_args cdecl| 0).
        rewrite Nat.add_0_r in H.
        rewrite H.
        rewrite /ptm. rewrite up_0.
        rewrite (inst_case_predicate_context decli) //.
      ++ rewrite /p' case_predicate_context_length //.
         { now apply inst_wf_predicate. }
        rewrite Nat.add_0_r. simpl.
        len. rewrite !up_Upn -Upn_Upn. rewrite - !lift_rename.
        rewrite Nat.add_comm inst_lift.
        rewrite /ptm case_predicate_context_length //.
    * rewrite /= inst_mkApps /=. f_equal.
      ++ rewrite !map_map_compose /id.
        generalize (declared_constructor_closed_indices decli).
        apply forallb_map_spec => t clt.
        rewrite !up_Upn.
        rewrite /expand_lets /expand_lets_k.
        rewrite -inst_subst_instance. len.
        rewrite inst_subst map_rev List.length_rev. f_equal.
        rewrite inst_subst. rewrite (wf_predicate_length_pars wfp).
        rewrite (declared_minductive_ind_npars decli).
        rewrite -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
        setoid_rewrite <- up_Upn at 1.
        rewrite inst_closed_extended_subst.
        { rewrite closedn_subst_instance_context.
          apply (declared_inductive_closed_params decli). }
        f_equal. len. rewrite - !Upn_Upn.
        rewrite (Nat.add_comm _ (context_assumptions _)) inst_lift.
        f_equal. rewrite Nat.add_comm inst_subst.
        rewrite inst_inds. f_equal.
        rewrite - Upn_Upn. len.
        rewrite inst_closed ?closedn_subst_instance //.
        { eapply closed_upwards; tea; lia. }
        etransitivity.
        { eapply inst_ext. intros x.
          rewrite -(Upn_subst_instance _ _ _ _). reflexivity. }
        rewrite inst_closed ?closedn_subst_instance //.
        { eapply closed_upwards; tea; lia. }
      ++ unfold id. f_equal. f_equal.
        rewrite map_app map_map_compose.
        rewrite map_map_compose.
        setoid_rewrite up_Upn. len.
        f_equal.
        { apply map_ext. intros. now sigma. }
        rewrite inst_to_extended_list.
        now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

#[global]
Instance map_def_ext {A B} : Proper (`≐1` ==> `≐1` ==> `≐1`) (@map_def A B).
Proof.
  intros f g Hfg f' g' Hfg' x.
  unfold map_def; destruct x; simpl.
  now rewrite Hfg Hfg'.
Qed.

Lemma inst_decompose_prod_assum f Γ t :
  decompose_prod_assum (inst_context f Γ) (inst (up #|Γ| f) t)
  = let '(Γ, t) := decompose_prod_assum Γ t in
    let '(Γ', t') := decompose_prod_assum [] (inst (up #|Γ| f) t) in
    (Γ' ++ inst_context f Γ, t').
Proof.
  induction t in Γ |- *. all: simpl; try (rewrite ?app_nil_r; reflexivity).
  - simpl.
    now rewrite decompose_prod_assum_ctx.
  - specialize (IHt2 (Γ ,, vass na t1)).
    rewrite inst_context_snoc /= in IHt2.
    rewrite <-up_Upn in IHt2.
    simpl. now rewrite up_up IHt2.
  - specialize (IHt3 (Γ ,, vdef na t1 t2)).
    rewrite inst_context_snoc /= in IHt3.
    simpl. rewrite <- up_Upn in IHt3.
    simpl. now rewrite up_up IHt3.
Qed.

Lemma decompose_prod_assum_mkApps ctx ind u args :
  decompose_prod_assum ctx (mkApps (tInd ind u) args) = (ctx, mkApps (tInd ind u) args).
Proof.
  apply (decompose_prod_assum_it_mkProd ctx []).
  now rewrite is_ind_app_head_mkApps.
Qed.

Lemma inst_app_context f Γ Δ :
  inst_context f (Γ ,,, Δ) =
  inst_context f Γ ,,, inst_context (up #|Γ| f) Δ.
Proof.
  rewrite /inst_context fold_context_k_app /app_context. f_equal.
  apply fold_context_k_ext. intros i x. now rewrite up_Upn Nat.add_comm Upn_Upn.
Qed.

Lemma inst_smash_context f Γ Δ :
  inst_context f (smash_context Γ Δ) =
  smash_context (inst_context (up #|Δ| f) Γ) (inst_context f Δ).
Proof.
  rewrite up_Upn.
  induction Δ as [|[na [b|] ty] Δ] in Γ |- *; simpl; auto;
    rewrite ?Upn_0 // ?inst_context_snoc IHΔ /=; len.
  - f_equal. now rewrite inst_context_subst /= -Upn_Upn.
  - f_equal. rewrite inst_app_context /map_decl /= /app_context.
    f_equal.
    * now rewrite up_Upn -Upn_Upn.
    * rewrite /inst_context fold_context_k_tip /map_decl /=. do 2 f_equal.
      now rewrite Upn_0.
Qed.

Lemma nth_error_inst_context f Γ n :
  nth_error (inst_context f Γ) n =
  option_map (map_decl (inst (up (#|Γ| - S n) f))) (nth_error Γ n).
Proof.
  induction Γ in n |- *; intros.
  - simpl. unfold inst_context, fold_context_k; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct n; rewrite inst_context_snoc.
    + simpl. rewrite up_Upn. lia_f_equal.
    + simpl. rewrite Nat.sub_succ -IHΓ; simpl in *; (lia || congruence).
Qed.

Lemma inst_check_one_fix f (mfix : mfixpoint term) d x :
  check_one_fix d = Some x ->
  check_one_fix (map_def (inst f) (inst (up #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (inst_decompose_prod_assum f [] dtype).
  rewrite up_0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_prod_assum as [Γ' t'].
  rewrite smash_context_app (smash_context_acc (inst_context _ _)).
  rewrite -(inst_smash_context f []).
  destruct nth_error eqn:hnth => //.
  have hlen := nth_error_Some_length hnth. len in hlen.
  simpl in hlen.
  destruct (nth_error (List.rev (_ ++ inst_context _ _)) _) eqn:hnth'.
  2:{ eapply nth_error_None in hnth'. len in hnth'. }
  rewrite nth_error_rev_inv in hnth; len; auto.
  len in hnth. simpl in hnth.
  rewrite nth_error_rev_inv in hnth'; len; auto; try lia.
  len in hnth'. simpl in hnth'.
  rewrite nth_error_app_ge in hnth'; len; try lia. len in hnth'.
  simpl in hnth'.
  replace (context_assumptions Γ' + context_assumptions c - S rarg - context_assumptions Γ') with
    (context_assumptions c - S rarg) in hnth' by lia.
  rewrite /= nth_error_inst_context /= hnth /= in hnth'. noconf hnth'.
  simpl.
  destruct decompose_app eqn:da. len.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da.
  rewrite inst_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma inst_check_one_cofix f (mfix : mfixpoint term) d x :
  check_one_cofix d = Some x ->
  check_one_cofix (map_def (inst f) (inst (up #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (inst_decompose_prod_assum f [] dtype).
  rewrite up_0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_prod_assum eqn:dp.
  destruct decompose_app eqn:da.
  destruct (decompose_app t0) eqn:da'.
  destruct t1 => /= //.
  eapply decompose_app_inv in da. subst t.
  simp sigma in dp. rewrite decompose_prod_assum_mkApps /= in dp.
  noconf dp. rewrite decompose_app_mkApps // in da'. noconf da' => //.
Qed.

Lemma inst_wf_fixpoint Σ f mfix :
  wf_fixpoint Σ mfix ->
  wf_fixpoint Σ (map (map_def (inst f) (inst (up #|mfix| f))) mfix).
Proof.
  unfold wf_fixpoint, wf_fixpoint_gen.
  move/andb_and => [] hmfix ho.
  apply/andP; split.
  { rewrite forallb_map; eapply forallb_impl; tea; cbn => x hx hl.
    destruct (dbody x) => /= //. }
  rewrite map_map_compose.
  destruct (map_option_out (map check_one_fix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (inst_check_one_fix f mfix). }
  now rewrite hmap.
Qed.

Lemma inst_wf_cofixpoint Σ f mfix :
  wf_cofixpoint Σ mfix ->
  wf_cofixpoint Σ (map (map_def (inst f) (inst (up #|mfix| f))) mfix).
Proof.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  rewrite map_map_compose.
  destruct (map_option_out (map check_one_cofix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (inst_check_one_cofix f mfix). }
  now rewrite hmap.
Qed.

Lemma inst_extended_subst f Γ :
  map (inst (up (context_assumptions Γ) f)) (extended_subst Γ 0) =
  extended_subst (inst_context f Γ) 0.
Proof.
  induction Γ as [|[na [b|] ty] Γ]; auto; rewrite inst_context_snoc /=; len.
  - rewrite !inst_subst0.
    rewrite IHΓ. len. f_equal. f_equal.
    rewrite up_Upn -Upn_Upn Nat.add_comm.
    now rewrite inst_lift.
  - f_equal; auto.
    rewrite !(lift_extended_subst _ 1).
    rewrite map_map_compose.
    setoid_rewrite up_Upn; setoid_rewrite lift0_inst; setoid_rewrite inst_assoc.
    setoid_rewrite (Upn_Upn 1); setoid_rewrite shiftn_Upn;
    setoid_rewrite <- up_Upn; setoid_rewrite <-inst_assoc.
    setoid_rewrite <- lift0_inst.
    rewrite -map_map_compose. now f_equal.
Qed.

Lemma inst_iota_red :
  forall f p pars args br,
  #|skipn pars args| = context_assumptions br.(bcontext) ->
  closedn_ctx #|pparams p| br.(bcontext) ->
  inst f (iota_red pars p args br) =
  iota_red pars (inst_predicate f p) (map (inst f) args) (inst_branch f br).
Proof.
  intros f p pars args br hlen hlen'.
  unfold iota_red.
  rewrite inst_subst0 map_rev map_skipn. f_equal.
  rewrite List.length_rev /expand_lets /expand_lets_k.
  rewrite inst_subst0. len.
  rewrite -Upn_Upn -hlen Nat.add_comm up_Upn inst_lift.
  rewrite hlen -up_Upn.
  relativize (context_assumptions _); [erewrite inst_extended_subst|now len].
  f_equal. f_equal.
  rewrite inst_inst_case_context.
  { now rewrite -closedn_ctx_on_free_vars. }
  rewrite /inst_case_branch_context /=.
  now rewrite inst_closedn_ctx.
Qed.

Lemma inst_unfold_fix :
  forall mfix idx narg fn f,
    unfold_fix mfix idx = Some (narg, fn) ->
    unfold_fix (map (map_def (inst f) (inst (up #|mfix| f))) mfix) idx
    = Some (narg, inst f fn).
Proof.
  intros mfix idx narg fn f h.
  unfold unfold_fix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h. clear h.
  simpl.
  f_equal. f_equal.
  rewrite inst_subst0. rewrite fix_subst_length.
  f_equal.
  * unfold fix_subst. rewrite length_map.
    generalize #|mfix| at 2 3. intro n.
    induction n.
    - reflexivity.
    - simpl. f_equal. rewrite IHn. reflexivity.
  * now rewrite up_Upn.
Qed.

Lemma inst_unfold_cofix :
  forall mfix idx narg fn f,
    unfold_cofix mfix idx = Some (narg, fn) ->
    unfold_cofix (map (map_def (inst f) (inst (up #|mfix| f))) mfix) idx
    = Some (narg, inst f fn).
Proof.
  intros mfix idx narg fn f h.
  unfold unfold_cofix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h.
  simpl. f_equal. f_equal.
  rewrite inst_subst0. rewrite cofix_subst_length.
  rewrite up_Upn.
  f_equal.
  unfold cofix_subst. rewrite length_map.
  generalize #|mfix| at 2 3. intro n.
  induction n.
  - reflexivity.
  - simpl. rewrite up_Upn.
    f_equal. rewrite IHn. reflexivity.
Qed.


Lemma decompose_app_inst :
  forall f t u l,
    decompose_app t = (u, l) ->
    rigid_head u ->
    decompose_app (inst f t) = (inst f u, map (inst f) l).
Proof.
  assert (aux : forall f t u l acc,
    decompose_app_rec t acc = (u, l) ->
    rigid_head u ->
    decompose_app_rec (inst f t) (map (inst f) acc) =
    (inst f u, map (inst f) l)
  ).
  { intros f t u l acc h.
    induction t in acc, h |- *.
    all: simpl in *; try solve [ inversion h ; reflexivity ].
    * noconf h => /= //.
    * simpl. intros ru. simpl in h. specialize IHt1 with (1 := h).
      now apply IHt1.
  }
  intros f t u l.
  unfold decompose_app.
  eapply aux.
Qed.

Lemma isConstruct_app_inst :
  forall t f,
    isConstruct_app t ->
    isConstruct_app (inst f t).
Proof.
  intros t f h.
  unfold isConstruct_app in *.
  case_eq (decompose_app t). intros u l e.
  apply decompose_app_inst with (f := f) in e as e'.
  * destruct (decompose_app t); simpl in *. destruct t0 => /= //. noconf e.
    now rewrite e'.
  * rewrite e in h. simpl in h.
    destruct u => //.
Qed.

Lemma is_constructor_inst :
  forall n l f,
    is_constructor n l ->
    is_constructor n (map (inst f) l).
Proof.
  intros n l f h.
  unfold is_constructor in *.
  rewrite nth_error_map.
  destruct nth_error.
  - simpl. apply isConstruct_app_inst. assumption.
  - simpl. discriminate.
Qed.

Lemma inst_predicate_set_pparams f p params :
  inst_predicate f (set_pparams p params) =
  set_pparams (inst_predicate f p) (map (inst f) params).
Proof. reflexivity. Qed.

(* Lemma inst_predicate_set_pcontext f p pcontext' :
  #|pcontext'| = #|p.(pcontext)| ->
  inst_predicate f (set_pcontext p pcontext') =
  set_pcontext (inst_predicate f p)
  (mapi_context (fun k => inst (up k f)) pcontext').
Proof. rewrite /inst_predicate /= /set_pcontext. simpl. intros ->. reflexivity. Qed. *)


Lemma inst_predicate_set_preturn f p pret :
  inst_predicate f (set_preturn p pret) =
  set_preturn (inst_predicate f p) (inst (up #|pcontext p| f) pret).
Proof. reflexivity. Qed.



Lemma on_free_vars_rename_S Δ t n A :
  on_free_vars (shiftnP #|Δ| xpred0) t ->
  on_free_vars (shiftnP (#|Δ ,, vass n A|) xpred0) (rename S t).
Proof.
  intro Ht. rewrite on_free_vars_rename.
  cbn. eapply on_free_vars_impl. 2:tea.
  cbn; intros. induction i; eauto.
Defined.

Lemma up_ext_cond (P : nat -> bool) n s s':
  (forall i, P i -> s i = s' i) ->
  forall k,
  shiftnP n P k ->
   up n s k = up n s' k.
Proof.
  move => Hs k.
  rewrite /up /shiftnP (Nat.leb_antisym k n).
  elim: (Nat.ltb_spec0 k n) => //= _ ?.
  now f_equal.
Qed.

Lemma inst_ext_cond (P : nat -> bool) s s' :
  (forall i, P i -> s i = s' i) ->
  forall t,
  on_free_vars P t ->
  inst s t = inst s' t.
Proof.
  intros Hs t Ht. revert P s s' Hs Ht.
  elim t using term_forall_list_ind; cbn in |- *; intros; try easy.
  8-9: rewrite /test_def in Ht.
  1-5,7-9,10:
    try rewrite H; try rewrite H0 ; try rewrite H1 ; try easy ;
    solve [f_equal; solve_all; eauto using up_ext_cond].

  - f_equal; solve_all.
    * eapply map_predicate_shift_eq_spec; solve_all; eauto using up_ext_cond.
    * apply map_branch_shift_eq_spec; solve_all; eauto using up_ext_cond.
Qed.

Lemma inst_on_free_vars n t σ :
  on_free_vars (shiftnP n xpred0) t -> t.[⇑^n σ] = t.
Proof.
  intros H.
  erewrite inst_ext_cond ; tea.
  1: eapply subst_ids.
  move => i.
  now rewrite /shiftnP /Upn orb_false_r => /Nat.ltb_spec0 /subst_idsn_consn_lt ->.
Qed.

Lemma on_free_vars_up (P Q : nat -> bool) n s:
  (forall i, Q i -> on_free_vars P (s i)) ->
  forall i,
  shiftnP n Q i ->
  on_free_vars (shiftnP n P) (up n s i).
Proof.
  intros H i.
  rewrite /up.
  destruct (Nat.leb_spec0 n i) as [Hi|Hi].
  + rewrite on_free_vars_rename.
    erewrite on_free_vars_ext.
    2: now eapply addnP_shiftnP.
    rewrite /shiftnP => /orP [].
    1: move => /Nat.ltb_spec0 ? ; lia.
    intros.
    now eapply H.
  + rewrite /= /shiftnP.
    now move: Hi => /Nat.nle_gt /Nat.ltb_spec0 ->.
Qed.

Lemma on_free_vars_inst (P Q : nat -> bool) s t :
  (forall i, Q i -> on_free_vars P (s i)) ->
  on_free_vars Q t ->
  on_free_vars P t.[s].
Proof.
  intros Hs Ht.
  induction t in P, Q, s, Hs, Ht |- * using term_forall_list_ind ; cbn in |- *; intros ; try easy.
  7-8: rewrite /= /test_def in Ht |- *.

  all:
    cbn in Ht ;
    try rewrite Hs; try rewrite H0 ; try rewrite H1 ; try easy ;
    solve [solve_all; eauto using on_free_vars_up].
Qed.


Lemma usubst_on_free_vars_shift Γ Δ σ u n :
   closed_subst Γ σ Δ ->
   is_closed_context Γ ->
   on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)) u ->
   on_free_vars (shiftnP n (shiftnP #|Δ| xpred0)) u.[up n σ].
Proof.
  intros.
  eapply on_free_vars_inst ; tea.
  intros i.
  destruct X as [iΔ [d usub]].
  rewrite /shiftnP.
  destruct (Nat.ltb_spec0 i n) ; cbn.
  1:{
    rewrite /up.
    destruct (Nat.leb_spec0 n i) ; cbn.
    1: lia.
    now destruct (Nat.ltb_spec0 i n).
  }
  destruct (Nat.ltb_spec0 (i-n) #|Γ|) => // _.
  rewrite /up.
  destruct (Nat.leb_spec0 n i).
  2: lia.
  erewrite on_free_vars_rename.
  eapply on_free_vars_impl.
  2: now eapply nth_error_Some' in l as [].
  intros j.
  rewrite /shiftnP.
  nat_compare_specs => // _.
  nat_compare_specs => //=.
  nat_compare_specs => //=.
Qed.

Section Sigma.

Context `{cf: checker_flags}.

Lemma usubst_ext {Δ σ σ' Γ} :
  usubst Γ σ Δ ->
  σ ≐1 σ' ->
  usubst Γ σ' Δ.
Proof using Type.
  intros Hσ eq n decl hnth.
  specialize (Hσ n decl hnth) as hb.
  intros b hd. specialize (hb b hd).
    destruct hb as [[x' [decl' [eqn [hnth' hsome]]]]|h].
    * left; exists x', decl'. rewrite -(eq n). repeat split; auto.
      now rewrite -eq.
    * right. now rewrite -(eq n) -eq.
Qed.

Lemma closed_subst_ext {Δ σ σ' Γ} :
  closed_subst Γ σ Δ ->
  σ ≐1 σ' ->
  closed_subst Γ σ' Δ.
  intros [HΔ Hσ] eq. destruct Hσ as [closed_σ Hσ]. repeat split; eauto.
  - intros n decl hnth. rewrite <- (eq n). eapply closed_σ; eauto.
  - eapply usubst_ext; eauto.
Qed.

Lemma well_subst_ext Σ Δ σ σ' Γ :
  Σ ;;; Δ ⊢ σ : Γ ->
  σ ≐1 σ' ->
  Σ ;;; Δ ⊢ σ' : Γ.
Proof using Type.
  intros Hσ eq. destruct Hσ as [typed_σ Hσ]. split.
  - intros n decl hnth. rewrite -(eq n).
    eapply meta_conv. 2:now rewrite -eq. eapply typed_σ; eauto.
  - eapply usubst_ext; eauto.
Qed.

Lemma usubst_Up {Γ Δ σ na A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vass na A) (⇑ σ) (Δ ,, vass na A.[σ]).
Proof.
  intros h [|n] decl e.
    * simpl in *. inversion e. subst. clear e. simpl => //.
    * cbn -[rshiftk] in *.
      specialize (h _ _ e) as h1.
      intros b hb.
        specialize (h1 _ hb) as [[x' [decl' [hrel [hnth hdecl]]]]|].
        ++ left. exists (S x'), decl'.
        split.
        ** unfold subst_compose at 1. now rewrite hrel.
        ** cbn -[rshiftk]. split; auto.
         destruct (decl_body decl') => //. cbn -[rshiftk] in hdecl |- *.
         noconf hdecl. f_equal.
         replace (S (S n)) with (S n + 1) by lia.
         rewrite -shiftk_compose subst_compose_assoc.
         rewrite -Upn_1_Up (shiftn_Upn 1) -subst_compose_assoc -inst_assoc -H.
         sigma. now rewrite ren_shift compose_ren.
      ++ right.
      unfold subst_compose at 1. rewrite e0.
      now rewrite inst_assoc.
Defined.

Lemma closed_subst_Up {Γ Δ σ na A} :
  closed_subst Γ σ Δ ->
  is_open_term Δ A.[σ] ->
  closed_subst (Γ ,, vass na A) (⇑ σ) (Δ ,, vass na A.[σ]).
Proof using Type.
  intros [HΔ h] HAσ; repeat split.
  - rewrite on_free_vars_ctx_snoc. solve_all.
  - intros [|n] decl e.
    * now inversion e.
    * cbn -[rshiftk] in *.
      rewrite /subst_compose.
      eapply on_free_vars_inst.
      2: now eapply h.
      now easy.
  - eapply usubst_Up; eauto; intuition.
Qed.

Lemma well_subst_Up {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ na A} :
  wf_local Σ (Δ ,, vass na A.[σ]) ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,, vass na A.[σ] ⊢ ⇑ σ : Γ ,, vass na A.
Proof using Type.
  intros hΔ h. split.
  - intros [|n] decl e.
    + simpl in *. inversion e. subst. clear e. simpl.
      eapply meta_conv.
      * econstructor ; auto.
        reflexivity.
      * simpl. now autorewrite with sigma.
    + sigma. specialize (h.1 _ _ e) as h1. sigma in h1.
      eapply meta_conv.
      * epose proof (weakening_rename_typing (Γ' := []) (Γ'' := [_]) hΔ h1).
        simpl in X.
        sigma in X. eapply X.
      * eapply inst_ext. rewrite ren_lift_renaming.
        now sigma.
  - eapply usubst_Up; eauto; intuition auto with *.
Qed.



Lemma usubst_Up' {Γ Δ σ na t A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vdef na t A) (⇑ σ) (Δ ,, vdef na t.[σ] A.[σ]).
Proof using Type.
  intros h [|n] decl e.
    * simpl in *. inversion e. subst. clear e. simpl.
      intros b [= ->].
      left. exists 0. eexists _; intuition eauto.
      simpl. sigma. reflexivity.
    * cbn -[rshiftk] in *.
      specialize (h _ _ e) as h2.
      + intros b hb.
        specialize (h2 _ hb) as [[x' [decl' [hrel [hnth hdecl]]]]|].
      ++ left. exists (S x'), decl'.
      split.
      ** unfold subst_compose at 1. now rewrite hrel.
      ** cbn -[rshiftk]. split; auto.
        destruct (decl_body decl') => //. cbn -[rshiftk] in hdecl |- *.
        noconf hdecl. f_equal.
        replace (S (S n)) with (S n + 1) by lia.
        rewrite -shiftk_compose subst_compose_assoc.
        rewrite -Upn_1_Up (shiftn_Upn 1) -subst_compose_assoc -inst_assoc -H.
        sigma. now rewrite ren_shift compose_ren.
    ++ right.
      unfold subst_compose at 1. rewrite e0.
      now rewrite inst_assoc.
Qed.

Lemma closed_subst_Up' {Γ Δ σ na t A} :
  closed_subst Γ σ Δ ->
  is_open_term Δ A.[σ] ->
  is_open_term Δ t.[σ] ->
  closed_subst (Γ ,, vdef na t A) (⇑ σ) (Δ ,, vdef na t.[σ] A.[σ]).
Proof using Type.
  intros [HΔ h] HAσ Htσ; repeat split.
  - rewrite on_free_vars_ctx_snoc; solve_all.
    unfold is_open_decl, test_decl; solve_all.
  - intros [|n] decl e.
    * simpl in *. inversion e. subst. clear e. simpl. eauto.
    * cbn -[rshiftk] in *.
      rewrite /subst_compose.
      eapply on_free_vars_inst.
      2: now eapply h.
      now easy.
  - eapply usubst_Up'; eauto; intuition auto with *.
Qed.

Lemma well_subst_Up' {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ na t A} :
  wf_local Σ (Δ ,, vdef na t.[σ] A.[σ]) ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,, vdef na t.[σ] A.[σ] ⊢ ⇑ σ : Γ ,, vdef na t A.
Proof using Type.
  intros wf h. split.
  - intros [|n] decl e.
    * simpl in *. inversion e. subst. clear e. simpl.
    rewrite lift_rename. rewrite rename_inst.
    autorewrite with sigma.
    eapply meta_conv.
      + econstructor; auto; reflexivity.
      + rewrite lift0_inst /=.
        now autorewrite with sigma.
   * cbn -[rshiftk] in *.
      specialize (h.1 _ _ e).
     sigma. sigma in h. intro.
      eapply meta_conv.
      + epose proof (weakening_rename_typing (Γ' := []) (Γ'' := [_]) wf X).
        simpl in X0.
        sigma in X0. eapply X0.
      + eapply inst_ext. rewrite ren_lift_renaming.
        now sigma.
  - eapply usubst_Up'; eauto; intuition auto with *.
Qed.



Lemma usubst_app {Γ Δ σ Δ'} :
  usubst Γ σ Δ ->
  usubst (Γ ,,, Δ') (⇑^#|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof.
  intros hs.
  induction Δ' as [|[na [b|] ty] Δ'].
  - eapply usubst_ext; eauto.
    now rewrite Upn_0.
  - rewrite inst_context_snoc.
    eapply usubst_ext.
    2:now rewrite Upn_S. simpl.
    apply usubst_Up'. intuition.
  - rewrite inst_context_snoc. eapply usubst_ext.
    2:now rewrite Upn_S. simpl.
    apply usubst_Up. intuition.
Defined.

Lemma closed_subst_app {Γ Δ σ Δ'} :
  closed_subst Γ σ Δ ->
  on_free_vars_ctx (shiftnP #|Δ| xpred0) (inst_context σ Δ') ->
  closed_subst (Γ ,,, Δ') (⇑^#|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof.
  intros hs hΔ'.
  induction Δ' as [|[na [b|] ty] Δ'].
  - eapply closed_subst_ext; eauto.
    now rewrite Upn_0.
  - rewrite inst_context_snoc. rewrite inst_context_snoc in hΔ'.
    rewrite on_free_vars_ctx_snoc in hΔ'. toProp hΔ'.
    eapply closed_subst_ext.
    2:now rewrite Upn_S. simpl.
    apply closed_subst_Up'.
    + intuition.
    + solve_all. unfold on_free_vars_decl, test_decl in H0. toProp H0.
      cbn in H0. rewrite shiftnP_add in H0. rewrite <- length_app in H0.
      destruct H0; tea.
    + solve_all. unfold on_free_vars_decl, test_decl in H0. toProp H0.
      cbn in H0. rewrite shiftnP_add in H0. rewrite <- length_app in H0.
      destruct H0; tea.
  - rewrite inst_context_snoc. rewrite inst_context_snoc in hΔ'.
    rewrite on_free_vars_ctx_snoc in hΔ'. toProp hΔ'.
    eapply closed_subst_ext.
    2:now rewrite Upn_S. simpl.
    apply closed_subst_Up.
    + intuition.
    + solve_all. unfold on_free_vars_decl, test_decl in H0. toProp H0.
      cbn in H0. rewrite shiftnP_add in H0. rewrite <- length_app in H0.
      destruct H0; tea.
Defined.

Lemma well_subst_app {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ Δ'} :
  wf_local Σ (Δ ,,, inst_context σ Δ') ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,,, inst_context σ Δ' ⊢ ⇑^#|Δ'| σ : Γ ,,, Δ'.
Proof using Type.
  induction Δ' as [|[na [b|] ty] Δ']; simpl => hwf hsub.
  - eapply well_subst_ext; eauto.
    now rewrite Upn_0.
  - rewrite inst_context_snoc.
    eapply well_subst_ext.
    2:now rewrite Upn_S. simpl.
    apply well_subst_Up'.
    * rewrite inst_context_snoc in hwf.
      apply hwf.
    * rewrite inst_context_snoc in hwf.
      depelim hwf. apply IHΔ' => //.
  - rewrite inst_context_snoc.
    eapply well_subst_ext.
    2:now rewrite Upn_S. simpl.
    apply well_subst_Up.
    * rewrite inst_context_snoc in hwf.
      apply hwf.
    * rewrite inst_context_snoc in hwf.
      depelim hwf. apply IHΔ' => //.
Qed.


Lemma usubst_app_up {Γ Δ σ Δ'} :
  usubst Γ σ Δ ->
  usubst (Γ ,,, Δ') (up #|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof using Type.
  intros hs hΔ'.
  eapply usubst_ext; [eapply usubst_app; eauto|].
  now sigma.
Qed.

Lemma closed_subst_app_up {Γ Δ σ Δ'} :
  closed_subst Γ σ Δ ->
  on_free_vars_ctx (shiftnP #|Δ| xpred0) (inst_context σ Δ') ->
  closed_subst (Γ ,,, Δ') (up #|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof using Type.
  intros hs hΔ'.
  eapply closed_subst_ext; [eapply closed_subst_app; eauto|].
  now sigma.
Qed.

Lemma well_subst_app_up {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ Δ'} :
  wf_local Σ (Δ ,,, inst_context σ Δ') ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,,, inst_context σ Δ' ⊢ up #|Δ'| σ : Γ ,,, Δ'.
Proof using Type.
  intros wf Hσ.
  eapply well_subst_ext.
  2:now rewrite up_Upn.
  now apply well_subst_app.
Qed.

Lemma wf_local_app_inst (Σ : global_env_ext) {wfΣ : wf Σ} Γ Δ :
  All_local_rel (fun Γ j =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    lift_typing0 (fun t T => Σ ;;; Δ |- t.[σ] : T.[σ]) j) Γ Δ ->
  forall Δ' σ,
  Σ ;;; Δ' ⊢ σ : Γ ->
  wf_local Σ Δ' ->
  wf_local Σ (Δ' ,,, inst_context σ Δ).
Proof using Type.
  intros.
  induction X using All_local_rel_ind1.
  - now simpl.
  - rewrite inst_context_snoc /=.
    apply All_local_env_snoc; auto.
    apply lift_typing_map with (j := j_decl _) => //.
    eapply X; tas.
    eapply well_subst_app; auto.
Qed.

Lemma usubst_up_vass {Γ Δ σ na A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vass na A) (up 1 σ) (Δ ,, vass na A.[σ]).
Proof using Type.
  intros H HA.
  eapply usubst_ext; [eapply usubst_Up; tea|].
  now rewrite up_Upn; sigma.
Qed.

Lemma closed_subst_up_vass {Γ Δ σ na A} :
  closed_subst Γ σ Δ ->
  is_open_term Δ A.[σ] ->
  closed_subst (Γ ,, vass na A) (up 1 σ) (Δ ,, vass na A.[σ]).
Proof using Type.
  intros H HA.
  eapply closed_subst_ext; [eapply closed_subst_Up; tea|].
  now rewrite up_Upn; sigma.
Qed.

Lemma usubst_up_vdef {Γ Δ σ na t A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vdef na t A) (up 1 σ) (Δ ,, vdef na t.[σ] A.[σ]).
Proof using Type.
  intros H. eapply usubst_ext; [eapply usubst_Up'; tea|].
  now rewrite up_Upn; sigma.
Qed.

Lemma closed_subst_up_vdef {Γ Δ σ na t A} :
  closed_subst Γ σ Δ ->
  is_open_term Δ A.[σ] ->
  is_open_term Δ t.[σ] ->
  closed_subst (Γ ,, vdef na t A) (up 1 σ) (Δ ,, vdef na t.[σ] A.[σ]).
Proof using Type.
  intros H Ha Ht.
  eapply closed_subst_ext; [eapply closed_subst_Up'; tea|].
  now rewrite up_Upn; sigma.
Qed.

Lemma inst_is_open_term Γ Δ σ u :
   closed_subst Γ σ Δ ->
   is_closed_context Γ ->
   is_open_term Γ u ->
   is_open_term Δ u.[σ].
Proof using Type.
  intros H ? ?.
  eapply on_free_vars_inst ; tea.
  intros i.
  rewrite {1}/shiftnP orb_false_r => /Nat.ltb_spec0 Hi.
  eapply nth_error_Some' in Hi as [].
  now eapply H.
Qed.

Lemma on_free_vars_ctx_inst_case_context_nil
  (P : nat -> bool)
  (pars : list term) (puinst : Instance.t)
  (pctx : list context_decl) :
  forallb (on_free_vars P) pars ->
  on_free_vars_ctx (closedP #|pars| xpredT) pctx ->
  on_free_vars_ctx P (inst_case_context pars puinst pctx).
Proof.
  intros.
  assert (on_free_vars_ctx P ([] ,,, inst_case_context pars puinst pctx)).
  { apply on_free_vars_ctx_inst_case_context.
    - cbn. rewrite shiftnP0; eauto.
    - eauto.
    - eauto.
  }
  rewrite on_free_vars_ctx_app in H1. solve_all. cbn in *. rewrite shiftnP0 in H2. tea.
Defined.

Lemma map_array_model_set_value f arr value :
  map_array_model f (set_array_value arr value) =
  set_array_value (map_array_model f arr) (List.map f value).
Proof.
  destruct arr; cbn => //.
Qed.

Lemma map_array_model_set_default f arr value :
  map_array_model f (set_array_default arr value) =
  set_array_default (map_array_model f arr) (f value).
Proof.
  destruct arr; cbn => //.
Qed.

Lemma map_array_model_set_type f arr value :
  map_array_model f (set_array_type arr value) =
  set_array_type (map_array_model f arr) (f value).
Proof.
  destruct arr; cbn => //.
Qed.

Lemma red1_inst {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ u v σ} :
  usubst Γ σ Δ ->
  is_open_term Γ u ->
  red1 Σ Γ u v ->
  red Σ Δ u.[σ] v.[σ].
Proof.
  intros hσ Hu h.
  induction h using red1_ind_all in Hu, σ, Δ, hσ |- *.
  all:try inv_on_free_vars.
  all: try solve [
    try (cbn in hav; rtoProp);
    simpl ; constructor ; eapply IHh ;
    eassumption
  ].
  - rewrite subst10_inst. sigma. do 2 constructor.
  - rewrite subst10_inst. sigma. do 2 constructor.
  - destruct (nth_error Γ i) eqn:hnth; noconf H.
    red in hσ. specialize hσ with (1 := hnth) as IH.
    specialize IH with (1:=H) as [[x' [decl' [hi [hnth' eqbod]]]]|eqr].
    * rewrite /= hi. sigma.
      destruct (decl_body decl') eqn:hdecl => //. noconf eqbod.
      rewrite -H0. sigma.
      relativize (t.[_]); [do 2 econstructor|].
      { now rewrite hnth' /= hdecl. }
      rewrite lift0_inst. now sigma.
    * rewrite /= eqr. sigma. reflexivity.
  - cbn. rewrite inst_mkApps. simpl.
    rewrite inst_iota_red //.
    * rewrite length_skipn; lia.
    * change (bcontext br) with (bcontext (inst_branch σ br)).
      eapply nth_error_forallb in p4; tea. simpl in p4.
      move/andP: p4 => [] clbctx clbod.
      rewrite closedn_ctx_on_free_vars.
      now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
    * constructor. constructor.
      + rewrite nth_error_map H /= //.
      + simpl. now len.
  - rewrite 2!inst_mkApps. simpl.
    do 2 econstructor.
    + eapply inst_unfold_fix. eassumption.
    + eapply is_constructor_inst. assumption.
  - simpl. rewrite !inst_mkApps. simpl.
    constructor. eapply red_cofix_case.
    eapply inst_unfold_cofix. eassumption.
  - simpl. rewrite 2!inst_mkApps. simpl.
    constructor; eapply red_cofix_proj.
    eapply inst_unfold_cofix. eassumption.
  - simpl.
    rewrite inst_closed0.
    * rewrite closedn_subst_instance.
      eapply declared_constant_closed_body. all: eauto.
    * do 2 econstructor; eauto.
  - simpl. rewrite inst_mkApps. simpl.
    do 2 econstructor. rewrite nth_error_map. rewrite H. reflexivity.
  - simpl. eapply red_abs; eauto.
  - simpl; eapply red_abs; eauto.
    eapply IHh; tea.
    + eapply usubst_up_vass; eauto.
    + rewrite shiftnP_add in b. change 1 with #|[vass na N]| in b. rewrite  <- length_app in b. apply b.
  - simpl; eapply red_letin; eauto.
  - simpl; eapply red_letin; eauto.
  - simpl; pcuicfo. eapply red_letin; eauto.
    eapply IHh; tea; try eapply usubst_up_vdef; try eapply inst_is_open_term; eauto.
    + rewrite shiftnP_add in p1. tea.
  - simpl. rewrite inst_predicate_set_pparams.
    eapply red_case_pars.
    simpl. eapply All2_map.
    solve_all. eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; eauto; solve_all.
  - simpl. rewrite inst_predicate_set_preturn.
    eapply red_case_p; eauto.
    simpl.
    eapply IHh; eauto.
    + rewrite /PCUICCases.inst_case_predicate_context.
      rewrite /= -inst_inst_case_context_wf //.
      { now rewrite test_context_k_closed_on_free_vars_ctx. }
      relativize #|pcontext p|; [eapply usubst_app_up|now len]; eauto.
    + rewrite shiftnP_add in p1. rewrite <- inst_case_predicate_context_length in p1.
      rewrite <- length_app in p1. tea.
  - simpl. eapply red_case_c; eauto.
  - simpl. eapply red_case_brs; eauto.
    red.
    eapply All2_map.
    solve_all. eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2 in X; eauto; clear X.
    * intros x y [[[? ?] ?] ?].
      simpl; rewrite -e. intuition auto.
      move/andP: i => [] clctx clb.
      eapply r0; tea.
      + rewrite /inst_case_branch_context.
      rewrite -inst_inst_case_context_wf //; simpl.
      relativize #|bcontext x|; [eapply usubst_app_up|now len]; eauto.
      + rewrite shiftnP_add in clb. erewrite <- inst_case_branch_context_length in clb.
        rewrite <- length_app in clb. tea.
    * intros x. unfold on_Trel; split; auto.
  - simpl. now eapply red_proj_c.
  - simpl. now eapply red_app.
  - simpl. now eapply red_app_r.
  - simpl. now eapply red_prod.
  - simpl. eapply red_prod_r, IHh; tea.
    * eapply usubst_up_vass; eauto.
    * rewrite shiftnP_add in b. change 1 with #|[vass na M1]| in b.
    rewrite <- length_app in b. tea.
  - simpl. cbn in Hu. solve_all.
    eapply OnOne2_All_mix_left in X; tea.
    eapply red_evar.
    eapply All2_map. eapply OnOne2_All2; eauto; solve_all.
  - simpl. cbn in Hu. solve_all.
    eapply OnOne2_All_mix_left in X; tea.
    eapply red_fix_one_ty.
    rewrite (OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    noconf b0. rewrite H H0 H1. split; auto.
    eapply b1; tea.
    now move/andP: b => [].
  - simpl. cbn in Hu; solve_all.
    eapply OnOne2_All_mix_left in X; tea.
    eapply red_fix_one_body.
    rewrite -(OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    noconf b0. rewrite H H0 H1. split; auto.
    move/andP: b => [] onty onb.
    eapply b1; tea.
    * eapply usubst_ext.
      + rewrite inst_fix_context_up. eapply usubst_app_up; eauto.
      + now len.
    *  rewrite shiftnP_add in onb. rewrite <- fix_context_length in onb. rewrite <- length_app in onb. tea.
  - simpl. cbn in Hu; solve_all. eapply OnOne2_All_mix_left in X; tea.
    eapply red_cofix_one_ty.
    rewrite (OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    noconf b0. rewrite H H0 H1. split; auto.
    move/andP: b => [] clty clb. eapply b1; tea.
  - simpl. cbn in Hu; solve_all. eapply OnOne2_All_mix_left in X; tea.
    eapply red_cofix_one_body.
    rewrite -(OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    move/andP: b => [] clty clb.
    noconf b0. rewrite H H0 H1. split; auto.
    eapply b1; tea.
    * eapply usubst_ext.
      + rewrite inst_fix_context_up. eapply usubst_app_up; eauto.
      + now len.
    *  rewrite shiftnP_add in clb. rewrite <- fix_context_length in clb. rewrite <- length_app in clb. tea.
  - cbn. toAll. eapply OnOne2_All_mix_left in X; tea.
    rewrite map_array_model_set_value.
    eapply red_primArray_one_value. cbn.
    eapply OnOne2_map; solve_all. red; simpl; eauto.
  - cbn. rewrite map_array_model_set_default.
    eapply red_primArray_default; cbn; eauto.
  - cbn. rewrite map_array_model_set_type.
    eapply red_primArray_type; cbn; eauto.
Defined.

Lemma eq_term_upto_univ_inst Σ cmp_universe cmp_sort pb napp u v σ :
    RelationClasses.Reflexive (cmp_universe Conv) ->
    RelationClasses.Reflexive (cmp_universe pb) ->
    RelationClasses.Reflexive (cmp_sort Conv) ->
    RelationClasses.Reflexive (cmp_sort pb) ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp u v ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp u.[σ] v.[σ].
Proof using Type.
  intros refl_univ_conv refl_univ_pb refl_sort_conv refl_sort_pb h.
  induction u in v, pb, napp, σ, refl_univ_pb, refl_sort_pb, h |- * using term_forall_list_ind.
  all: dependent destruction h.
  all: try solve [
    simpl ; constructor ; eauto
  ].
  - simpl. reflexivity.
  - simpl. constructor.
    induction X in a, args' |- *.
    + inversion a. constructor.
    + inversion a. subst. simpl. constructor.
      all: eauto.
  - simpl. constructor. all: eauto.
  * rewrite /inst_predicate.
    destruct X; destruct e as [? [? [ectx ?]]].
    rewrite (All2_length ectx). red.
    intuition auto; simpl; solve_all.
  * unfold eq_branches, eq_branch in *; solve_all.
    rewrite (All2_length a1).
    now eapply b0.
  - simpl. constructor.
    apply All2_length in e as eq. rewrite <- eq.
    generalize #|m|. intro k. unfold eq_mfixpoint in *.
    eapply All2_map. simpl. solve_all.
  - simpl. constructor.
    apply All2_length in e as eq. rewrite <- eq.
    generalize #|m|. intro k. unfold eq_mfixpoint in *.
    eapply All2_map. simpl. solve_all.
  - simpl. constructor.
    eapply onPrims_map_prop; tea. cbn; intuition eauto.
Qed.

Lemma inst_conv {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ A B} :
  usubst Γ σ Δ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  on_ctx_free_vars (shiftnP #|Γ| xpred0) Γ ->
  Σ ;;; Γ |- A = B ->
  Σ ;;; Δ |- A.[σ] = B.[σ].
Proof using Type.
  intros hσ onA onB onΓ h.
  induction h.
  - eapply cumul_refl.
    eapply eq_term_upto_univ_inst. all:try typeclasses eauto. assumption.
  - eapply red_conv_conv.
    + eapply red1_inst; tea.
    + apply IHh; tea.
      eapply red1_on_free_vars; tea.
  - eapply red_conv_conv_inv.
    + eapply red1_inst; tea.
    + eapply IHh; eauto.
      eapply red1_on_free_vars; tea.
Qed.

Lemma inst_cumul {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ A B} :
  usubst Γ σ Δ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  on_ctx_free_vars (shiftnP #|Γ| xpred0) Γ ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Δ |- A.[σ] <= B.[σ].
Proof using Type.
  intros hσ onA onB onΓ h.
  induction h.
  - eapply cumul_refl.
    eapply eq_term_upto_univ_inst. all:try typeclasses eauto. assumption.
  - eapply red_cumul_cumul.
    + eapply red1_inst; tea.
    + apply IHh; tea.
      eapply red1_on_free_vars; tea.
  - eapply red_cumul_cumul_inv.
    + eapply red1_inst; tea.
    + eapply IHh; eauto.
      eapply red1_on_free_vars; tea.
Qed.

Ltac inv_on_free_vars_decl :=
  match goal with
  | [ H : is_true (on_free_vars_decl _ _) |- _ ] =>
    move/andP: H => [] /= ? ?
  end.

Lemma inst_conv_decls {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Δ Δ' σ} d d' :
  usubst Γ σ Δ ->
  usubst Γ' σ Δ' ->
  is_open_decl Γ d ->
  is_open_decl Γ d' ->
  on_ctx_free_vars (shiftnP #|Γ| xpred0) Γ ->
  conv_decls cumulAlgo_gen Σ Γ Γ' d d' ->
  conv_decls cumulAlgo_gen Σ Δ Δ' (inst_decl σ d) (inst_decl σ d').
Proof using Type.
  intros usubst usubst' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    eapply inst_conv; simpl; cbn in *; tea.
  all:now repeat inv_on_free_vars_decl.
Qed.

Lemma inst_cumul_decls {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Δ Δ' σ} d d' :
  usubst Γ σ Δ ->
  usubst Γ' σ Δ' ->
  is_open_decl Γ d ->
  is_open_decl Γ d' ->
  on_ctx_free_vars (shiftnP #|Γ| xpred0) Γ ->
  cumul_decls cumulAlgo_gen Σ Γ Γ' d d' ->
  cumul_decls cumulAlgo_gen Σ Δ Δ' (inst_decl σ d) (inst_decl σ d').
Proof using Type.
  intros usubst usubst' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply inst_conv || eapply inst_cumul); tea.
  all:now repeat inv_on_free_vars_decl.
Qed.

Definition on_free_vars_decls P d d' :=
  on_free_vars_decl P d && on_free_vars_decl P d'.

Lemma on_ctx_free_vars_app P Γ Δ :
  on_ctx_free_vars P (Γ ,,, Δ) =
  on_ctx_free_vars P Δ && on_ctx_free_vars (addnP #|Δ| P) Γ.
Proof using Type.
  rewrite /on_ctx_free_vars.
  rewrite alli_app Nat.add_0_r. f_equal.
  rewrite alli_shift.
  apply alli_ext => i d.
  rewrite /addnP. rewrite Nat.add_comm. f_equal.
  apply on_free_vars_decl_proper => //.
  intros i'. lia_f_equal.
Qed.

Definition on_free_vars_ctxs P Γ Δ :=
  All2_fold (fun Δ Δ' => on_free_vars_decls (shiftnP #|Δ| P)) Γ Δ.

Lemma on_free_vars_ctx_prod {P Γ Δ} :
  #|Γ| = #|Δ| ->
  on_free_vars_ctx P Γ ->
  on_free_vars_ctx P Δ ->
  on_free_vars_ctxs P Γ Δ.
Proof using Type.
  move=> hlen.
  move/alli_Alli/Alli_rev_All_fold => onΓ.
  move/alli_Alli/Alli_rev_All_fold => onΔ.
  cbn in *.
  eapply All_fold_prod; tea.
  cbn; intros.
  now rewrite /on_free_vars_decls H (All2_fold_length X1) H0.
Qed.

Lemma on_free_vars_ctx_prod_inv {P Γ Δ} :
  on_free_vars_ctxs P Γ Δ ->
  on_free_vars_ctx P Γ /\ on_free_vars_ctx P Δ.
Proof using Type.
  induction 1 => //.
  rewrite !on_free_vars_ctx_snoc.
  move/andP: p => [] ->. rewrite -(All2_fold_length X).
  now move=> -> /=; rewrite !andb_true_r.
Qed.

Lemma All_fold_on_free_vars_ctx {P Γ} :
  All_fold (fun Γ d => on_free_vars_decl (shiftnP #|Γ| P) d) Γ ->
  on_free_vars_ctx P Γ.
Proof using Type.
  induction 1 => //.
  rewrite on_free_vars_ctx_snoc IHX //.
Qed.

Lemma on_ctx_free_vars_xpredT Γ :
  on_ctx_free_vars xpredT Γ = on_free_vars_ctx xpredT Γ.
Proof using Type.
  rewrite -{1}(shiftnP_xpredT #|Γ|).
  now rewrite on_free_vars_ctx_on_ctx_free_vars.
Qed.

Lemma addnP_xpredT n : addnP n xpredT ≐1 xpredT.
Proof using Type.
  now rewrite /addnP.
Qed.

Definition inst_telescope r Γ :=
  mapi (fun i => map_decl (inst (up i r))) Γ.

Lemma inst_subst_telescope f s Γ :
  inst_telescope f (subst_telescope s 0 Γ) =
  subst_telescope (map (inst f) s) 0
    (inst_telescope (⇑^#|s| f) Γ).
Proof using Type.
  rewrite /inst_telescope /subst_telescope.
  rewrite !mapi_compose. apply mapi_ext => k' d.
  rewrite !compose_map_decl; apply map_decl_ext => t'.
  rewrite Nat.add_0_r. rewrite !up_Upn.
  now rewrite inst_subst.
Qed.

Instance inst_telescope_ext : Proper (`≐1` ==> `≐1`) inst_telescope.
Proof using Type.
  intros f g Hfg Γ.
  rewrite /inst_telescope. apply mapi_ext => n x.
  now rewrite Hfg.
Qed.

Lemma inst_telescope_upn0 f Γ : inst_telescope (⇑^0 f) Γ = inst_telescope f Γ.
Proof using Type. now sigma. Qed.

Lemma inst_telescope_cons f d Γ :
  inst_telescope f (d :: Γ) = inst_decl f d :: inst_telescope (⇑^1 f) Γ.
Proof using Type.
  rewrite /inst_telescope mapi_cons /inst_decl.
  f_equal; sigma => //.
  apply mapi_ext => i x. now rewrite -up_Upn up_up Nat.add_1_r.
Qed.

Lemma inst_context_telescope r Γ : List.rev (inst_context r Γ) = inst_telescope r (List.rev Γ).
Proof using Type.
  rewrite !inst_context_alt /inst_telescope.
  rewrite mapi_rev.
  f_equal. apply mapi_ext => k' d.
  apply map_decl_ext => t. sigma. lia_f_equal.
Qed.


End Sigma.
