(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICUtils PCUICOnOne
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv PCUICWeakeningEnvConv
     PCUICWeakeningEnvTyp PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSubstitution PCUICContextSubst PCUICCasesContexts PCUICClosed PCUICClosedTyp PCUICClosedConv
     PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICContextConversionTyp
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICWellScopedCumulativity PCUICGuardCondition
     PCUICParallelReduction PCUICSpine PCUICInductives PCUICInductiveInversion PCUICSigmaCalculus.

From Stdlib Require Import ssreflect ssrbool Utf8.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.
Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Derive Signature for OnOne2_local_env.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Arguments Nat.sub : simpl nomatch.
Arguments Sort.sort_of_product : simpl nomatch.

(* Preservation of wf_*fixpoint *)

Lemma wf_fixpoint_red1_type {cf Σ} {wfΣ : wf Σ} Γ mfix mfix1 :
  wf_fixpoint Σ mfix ->
  OnOne2
  (fun x y : def term =>
   closed_red1 Σ Γ (dtype x) (dtype y)
   × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ mfix1.
Proof.
  intros wffix o.
  move: wffix; unfold wf_fixpoint, wf_fixpoint_gen.
  move/andb_and => [] isl wf. apply/andP; split.
  { clear wf. solve_all.
    revert isl.
    induction o; depelim isl; constructor; auto. destruct p.
    destruct c. noconf e. congruence. }
  clear isl. move: wf.
  enough (forall inds, map_option_out (map check_one_fix mfix) = Some inds ->
     map_option_out (map check_one_fix mfix1) = Some inds) => //.
  destruct map_option_out. now specialize (H _ eq_refl) as ->.
  discriminate.
  induction o; intros inds.
  - simpl.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs.
    destruct (decompose_prod_assum [] dtype) eqn:decomp.
    destruct nth_error eqn:Hnth.
    apply decompose_prod_assum_it_mkProd_or_LetIn in decomp.
    simpl in decomp.
    subst dtype.
    destruct (red1_it_mkProd_or_LetIn_smash redty Hnth) as
      (ctx & t' & decomp & d & [hnth di]).
    rewrite decomp hnth.
    unfold head in di. destruct decompose_app; simpl in *.
    destruct destInd as [[ind u]|]; try discriminate.
    destruct decompose_app. simpl in di. rewrite di. auto.
    discriminate.
  - simpl map.
    simpl map_option_out.
    destruct check_one_fix => //.
    destruct map_option_out. specialize (IHo _ eq_refl).
    move=> [= <-]. now rewrite IHo.
    discriminate.
Qed.

Lemma wf_fixpoint_red1_body {cf Σ} {wfΣ : wf Σ} Γ mfix mfix1 :
  wf_fixpoint Σ mfix ->
  OnOne2
  (fun x y : def term =>
   closed_red1 Σ Γ (dbody x) (dbody y)
   × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ mfix1.
Proof.
  intros wffix o.
  move: wffix; unfold wf_fixpoint, wf_fixpoint_gen.
  move/andb_and => [] isl wf. apply/andP; split.
  { clear wf. solve_all.
    revert isl.
    induction o; depelim isl; constructor; auto. destruct p.
    destruct c. noconf e.
    destruct (dbody hd) => //. depelim clrel_rel; solve_discr.
    now rewrite H. now rewrite H. }
  clear isl. move: wf.
  enough (map check_one_fix mfix = map check_one_fix mfix1) as -> => //.
  induction o.
  - simpl. f_equal.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs. reflexivity.
  - simpl. now rewrite IHo.
Qed.

Lemma wf_cofixpoint_red1_type {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 :
  wf Σ.1 ->
  wf_cofixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   Σ ;;; Γ ⊢ dtype x ⇝ dtype y
   × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
  wf_cofixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_cofixpoint, wf_cofixpoint_gen.
  enough (forall inds, map_option_out (map check_one_cofix mfix) = Some inds ->
     map_option_out (map check_one_cofix mfix1) = Some inds) => //.
  destruct map_option_out. now specialize (H _ eq_refl) as ->.
  discriminate.
  induction o; intros inds.
  - simpl.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs.
    destruct (decompose_prod_assum [] dtype) eqn:decomp.
    apply decompose_prod_assum_it_mkProd_or_LetIn in decomp.
    simpl in decomp.
    subst dtype.
    destruct (decompose_app t) as [f l] eqn:decomp.
    destruct f; try discriminate. simpl.
    apply decompose_app_inv in decomp. subst t.
    eapply red_it_mkProd_or_LetIn_mkApps_Ind in redty as [ctx' [args' ->]]; auto.
    erewrite decompose_prod_assum_it_mkProd => //.
    2:{ now rewrite is_ind_app_head_mkApps. }
    rewrite decompose_app_mkApps => //.
  - simpl map.
    simpl map_option_out.
    destruct check_one_cofix => //.
    destruct map_option_out. specialize (IHo _ eq_refl).
    move=> [= <-]. now rewrite IHo.
    discriminate.
Qed.

Lemma wf_cofixpoint_red1_body {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 :
  wf Σ.1 ->
  wf_cofixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dbody x) (dbody y)
   × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1 ->
  wf_cofixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_cofixpoint, wf_cofixpoint_gen.
  enough (map check_one_cofix mfix = map check_one_cofix mfix1) as -> => //.
  induction o.
  - simpl. f_equal.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs. reflexivity.
  - simpl. now rewrite IHo.
Qed.

#[global] Hint Extern 0 (conv_decls _ _ _ _ _) => constructor : pcuic.
#[global] Hint Extern 0 (cumul_decls _ _ _ _ _) => constructor : pcuic.
#[global] Hint Extern 0 (conv_context _ _ _) => constructor : pcuic.
#[global] Hint Extern 0 (cumul_context _ _ _) => constructor : pcuic.

Ltac unfold_pcuic :=
  progress (unfold PCUICTypingDef.typing, PCUICLookup.wf_sort in * ).
#[global] Hint Extern 10 => unfold_pcuic : pcuic.

#[global] Hint Resolve red_conv red1_red red_cumul : pcuic.
#[global] Hint Transparent global_env_ext : pcuic.
#[global] Hint Constructors All_local_env : pcuic.
Ltac pcuics := try typeclasses eauto with pcuic.

Lemma declared_projection_declared_constructor {cf}
  {Σ} {wfΣ : wf Σ} {p mdecl mdecl' idecl idecl' pdecl cdecl cdecl'} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  declared_constructor Σ (p.(proj_ind), 0) mdecl' idecl' cdecl' ->
  mdecl = mdecl' /\ idecl = idecl' /\ cdecl = cdecl'.
Proof.
  intros [[] ?] [].
  unshelve eapply declared_inductive_to_gen in H, H2; eauto.
  pose proof (declared_inductive_inj H H2). intuition auto. subst.
  rewrite H0 in H3. congruence.
Qed.

Ltac hide H :=
  match type of H with
  | ?ty => change ty with (@hidebody _ ty) in H
  end.

Lemma conv_context_smash_end {cf Σ} {wfΣ : wf Σ} (Γ Δ Δ' : context) :
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  Σ ⊢ Γ ,,, Δ = Γ ,,, Δ' ->
  Σ ⊢ Γ ,,, smash_context [] Δ = Γ ,,, smash_context [] Δ'.
Proof.
  intros wf wf' cv.
  eapply ws_cumul_ctx_pb_rel_app.
  apply ws_cumul_ctx_pb_rel_app in cv.
  eapply ws_cumul_ctx_pb_rel_smash => //.
Qed.

Lemma expand_lets_eq Γ t :
  expand_lets Γ t =
  subst0 (extended_subst Γ 0) (lift (context_assumptions Γ) #|Γ| t).
Proof.
  rewrite /expand_lets /expand_lets_k /= //.
Qed.

Lemma expand_lets_eq_map Γ l :
  map (expand_lets Γ) l =
  map (subst0 (extended_subst Γ 0)) (map (lift (context_assumptions Γ) #|Γ|) l).
Proof.
  rewrite /expand_lets /expand_lets_k /= map_map_compose //.
Qed.

Lemma map_expand_lets_to_extended_list Γ :
  map (expand_lets Γ) (to_extended_list Γ) = to_extended_list (smash_context [] Γ).
Proof.
  now rewrite expand_lets_eq_map map_subst_extended_subst_lift_to_extended_list_k.
Qed.

Lemma conv_context_rel_reln {cf} {Σ} {le} Γ Δ Δ' :
  ws_cumul_ctx_pb_rel le Σ Γ Δ Δ' ->
  forall acc n, reln acc n Δ = reln acc n Δ'.
Proof.
  intros [cl a]. induction a.
  - constructor.
  - intros acc n; destruct p; simpl; auto.
Qed.

Lemma conv_context_rel_to_extended_list {cf} {Σ} {le} {Γ Δ Δ'} :
  ws_cumul_ctx_pb_rel le Σ Γ Δ Δ' ->
  to_extended_list Δ = to_extended_list Δ'.
Proof.
  unfold to_extended_list, to_extended_list_k.
  intros; now eapply conv_context_rel_reln.
Qed.

From MetaCoq.PCUIC Require Import PCUICOnFreeVars.

Lemma eq_context_alpha_conv {cf} {Σ} {wfΣ : wf Σ} Γ Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  ws_cumul_ctx_pb_rel Conv Σ Γ Δ Δ'.
Proof.
  induction 1.
  - constructor; auto. constructor.
  - rewrite /= !on_free_vars_ctx_snoc => /andP[] cl;
    generalize cl; rewrite on_free_vars_ctx_app => /andP[] clΓ cll clx /andP[] clΓ' cly.
    intros; destruct r; constructor => //.
    * constructor. apply IHX => //. constructor; auto; subst.
      cbn in clx, cly.
      eapply into_ws_cumul_pb; eauto.
    * constructor. apply IHX => //.
      move/andP: clx => /= [clb clty].
      move/andP: cly => /= [clb' clty'].
      constructor; auto; subst.
      eapply into_ws_cumul_pb; eauto.
      eapply into_ws_cumul_pb; eauto.
Qed.

Lemma eq_context_alpha_reln Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  forall acc n, reln acc n Δ = reln acc n Δ'.
Proof.
  induction 1.
  - constructor.
  - intros acc n; destruct r; simpl; auto.
Qed.

Lemma eq_context_alpha_to_extended_list Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  to_extended_list Δ = to_extended_list Δ'.
Proof.
  unfold to_extended_list, to_extended_list_k.
  intros; now eapply eq_context_alpha_reln.
Qed.

Lemma reln_set_binder_name brctx Γ :
  All2 (fun (x : binder_annot name) (y : context_decl) =>
    eq_binder_annot x (decl_name y)) brctx Γ ->
  forall acc n, reln acc n (map2 set_binder_name brctx Γ) = reln acc n Γ.
Proof.
  move/All2_length => hl.
  induction brctx in Γ, hl |- *; destruct Γ as [|hd tl]; simpl in hl |- *; try congruence.
  intros acc n.
  destruct hd as [na [b|] ty]; cbn; apply IHbrctx; congruence.
Qed.

Lemma to_extended_list_set_binder_name brctx Γ :
  All2 (fun (x : binder_annot name) (y : context_decl) =>
    eq_binder_annot x (decl_name y)) brctx Γ ->
  to_extended_list_k (map2 set_binder_name brctx Γ) =1 to_extended_list_k Γ.
Proof.
  now intros hl x; eapply reln_set_binder_name.
Qed.

Lemma to_extended_list_case_branch_context ci mdecl p brctx cdecl :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) brctx (cstr_args cdecl) ->
  to_extended_list (case_branch_context ci mdecl p brctx cdecl) =
  to_extended_list (cstr_args cdecl).
Proof.
  intros hlen.
  rewrite /to_extended_list /case_branch_context /case_branch_context_gen.
  rewrite /pre_case_branch_context_gen /inst_case_context /cstr_branch_context.
  rewrite to_extended_list_set_binder_name //; try by
  rewrite to_extended_list_k_subst /expand_lets_ctx /expand_lets_k_ctx; substu;
  rewrite to_extended_list_k_subst
    to_extended_list_k_lift_context to_extended_list_k_subst
    PCUICLiftSubst.map_subst_instance_to_extended_list_k //.
  induction hlen; cbn. constructor.
  rewrite subst_context_snoc /= expand_lets_ctx_snoc subst_context_snoc.
  constructor. now cbn. apply IHhlen.
Qed.

Lemma spine_subst_inst_subst {cf} {Σ} {Γ inst s Δ Δ'} :
  spine_subst Σ Γ inst s Δ ->
  subst_context s 0 Δ' = subst_context (List.rev inst) 0 (expand_lets_ctx Δ Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite subst_context_subst_context. len.
  rewrite subst_context_lift_context_cancel. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

Lemma spine_subst_inst_subst_term {cf} {Σ} {Γ inst s Δ Δ'} :
  spine_subst Σ Γ inst s Δ ->
  subst s 0 Δ' = subst (List.rev inst) 0 (expand_lets Δ Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite distr_subst. len.
  rewrite simpl_subst_k. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

Lemma subst_context_subst_context s k s' Γ :
  subst_context s k (subst_context s' k Γ) =
  subst_context (map (subst0 s) s') k (subst_context s (k + #|s'|) Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto;
    rewrite !subst_context_snoc /= /subst_decl /map_decl /=; f_equal;
    auto; f_equal; len;
  rewrite -{1}(Nat.add_0_r (#|Γ'| + k)) distr_subst_rec; lia_f_equal.
Qed.

Lemma spine_subst_inst_subst_k {cf} {Σ} {Γ inst s Δ k Δ'} :
  spine_subst Σ Γ inst s Δ ->
  subst_context s k Δ' = subst_context (List.rev inst) k (expand_lets_k_ctx Δ k Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite subst_context_subst_context. len.
  rewrite subst_context_lift_context_cancel. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

Lemma spine_subst_inst_subst_term_k {cf} {Σ} {Γ inst s Δ k Δ'} :
  spine_subst Σ Γ inst s Δ ->
  subst s k Δ' = subst (List.rev inst) k (expand_lets_k Δ k Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev /expand_lets_k.
  rewrite -{2}(Nat.add_0_r k) distr_subst_rec. len.
  rewrite simpl_subst_k. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

Lemma isType_weaken {cf} {Σ Γ Δ T} {wfΣ : wf Σ} :
  wf_local Σ Δ ->
  isType Σ Γ T ->
  isType Σ (Δ ,,, Γ) T.
Proof.
  intros wfΔ HT.
  apply lift_typing_impl with (1 := HT) => ?? Hs.
  eapply weaken_ctx => //.
Qed.

(** The crucial property on constructors of cumulative inductive types for type preservation:
    we don't need to compare their instances when fully applied. *)
Lemma cmp_global_instance_cstr_irrelevant {cf} {Σ} {wfΣ  : wf Σ} {ci c} {mdecl idecl cdecl u u'} :
  declared_constructor Σ (ci, c) mdecl idecl cdecl ->
  cmp_ind_universes Σ ci (context_assumptions (ind_params mdecl) + #|cstr_indices cdecl|) u u' ->
  cmp_global_instance Σ.1 (compare_universe Σ) Conv (ConstructRef ci c)
    (ind_npars mdecl + context_assumptions (cstr_args cdecl)) u u'.
Proof.
  intros declc.
  pose proof (on_declared_constructor declc).
  pose proof (on_declared_constructor declc) as [[onind oib] [ctor_sorts [hnth onc]]].
  intros Hu. pose proof (cmp_global_instance_length _ _ _ _ _ _ _ Hu).
  rewrite /cmp_global_instance_gen /cmp_opt_variance /= /lookup_constructor /lookup_constructor_gen.
  unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
  rewrite (declared_inductive_lookup_gen declc'.p1) (proj2 declc').
  rewrite -(cstr_args_length onc).
  case: leb_spec_Set; try lia.
Qed.

Lemma wf_pre_case_branch_context {cf} {Σ} {wfΣ : wf Σ} {Γ ci mdecl idecl p} {br : branch term} {cdecl} :
  declared_inductive Σ ci mdecl idecl ->
  wf_branch_gen cdecl (forget_types (bcontext br)) ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_local Σ (Γ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) ->
  wf_local Σ (Γ,,, pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
Proof.
  move=> decli wfbr cu wf.
  eapply wf_local_alpha; tea.
  eapply All2_app. 2:eapply All2_refl; reflexivity.
  eapply All2_symP. tc.
  rewrite /case_branch_context_gen.
  eapply pre_case_branch_context_eq; eauto.
Qed.

Lemma conv_refl' {cf} {Σ} {wfΣ : wf Σ} {Γ x y} :
  x = y ->
  Σ ;;; Γ |- x = y.
Proof. now intros ->. Qed.

Lemma expand_lets_lift_cancel Γ x :
  expand_lets Γ (lift0 #|Γ| x) = lift0 (context_assumptions Γ) x.
Proof.
  rewrite /expand_lets /expand_lets_k.
  simpl. rewrite simpl_lift; try lia.
  rewrite Nat.add_comm.
  rewrite -(simpl_lift _ _ _ _ 0); try lia.
  rewrite simpl_subst_k //. now len.
Qed.

Lemma context_assumptions_expand_lets_k_ctx {Γ k Δ} :
  context_assumptions (expand_lets_k_ctx Γ k Δ) = context_assumptions Δ.
Proof.
  now rewrite /expand_lets_k_ctx; len.
Qed.
#[global]
Hint Rewrite @context_assumptions_expand_lets_k_ctx : len.

Lemma closedn_expand_lets (k : nat) (Γ : context) (t : term) :
  closedn_ctx k Γ ->
  closedn (k + #|Γ|) t ->
  closedn (k + context_assumptions Γ) (expand_lets Γ t).
Proof.
  rewrite /expand_lets /expand_lets_k.
  intros clΓ cl.
  eapply closedn_subst0.
  eapply (closedn_extended_subst_gen _ _ 0) => //.
  len.
  rewrite Nat.add_comm Nat.add_assoc. eapply closedn_lift.
  now rewrite Nat.add_comm.
Qed.

Lemma smash_context_subst_context_let_expand s Γ Δ :
  smash_context [] (subst_context_let_expand s Γ Δ) =
  subst_context_let_expand s Γ (smash_context [] Δ).
Proof.
  rewrite /subst_context_let_expand.
  rewrite (smash_context_subst []).
  now rewrite /expand_lets_ctx /expand_lets_k_ctx (smash_context_subst [])
    (smash_context_lift []).
Qed.

Lemma on_constructor_wf_args {cf} {Σ} {wfΣ : wf Σ} {ind c mdecl idecl cdecl u} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (subst_instance u (ind_params mdecl) ,,,
    (subst_context (ind_subst mdecl ind u)) #|ind_params mdecl| (subst_instance u (cstr_args cdecl))).
Proof.
  intros decl cu.
  pose proof (on_constructor_inst decl _ cu) as [wf _].
  rewrite !subst_instance_app_ctx in wf.
  rewrite -app_context_assoc -(app_context_nil_l (_ ,,, _)) app_context_assoc in wf.
  eapply substitution_wf_local in wf; tea.
  2:eapply (subslet_inds decl cu).
  rewrite app_context_nil_l subst_context_app closed_ctx_subst in wf.
  rewrite closedn_subst_instance_context.
  eapply (declared_inductive_closed_params decl).
  now simpl in wf; len in wf.
Qed.

#[global]
Instance conv_context_refl {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Reflexive (All2_fold (conv_decls cumulAlgo_gen Σ)).
Proof.
  intros x. reflexivity.
Qed.

(* Instance conv_context_sym {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Symmetric (All2_fold (conv_decls Σ)).
Proof.
  intros x y. now apply conv_context_sym.
Qed.

Instance conv_context_trans {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Transitive (All2_fold (conv_decls Σ)).
Proof.
  intros x y z. now apply conv_context_trans.
Qed. *)

Lemma on_free_vars_ctx_set_binder_name P Γ nas :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Γ ->
  on_free_vars_ctx P (map2 set_binder_name nas Γ) = on_free_vars_ctx P Γ.
Proof.
  induction 1.
  - simpl; auto.
  - cbn [map2]; rewrite !on_free_vars_ctx_snoc IHX; bool_congr.
    rewrite map2_length. apply (All2_length X).
    rewrite (All2_length X).
    destruct y as [na [b|] ty]; cbn; auto.
Qed.

Lemma is_closed_context_set_binder_name Γ Δ nas :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
  is_closed_context (Γ ,,, map2 set_binder_name nas Δ) = is_closed_context (Γ ,,, Δ).
Proof.
  induction 1 in Γ |- *. cbn; auto.
  rewrite !on_free_vars_ctx_app.
  cbn [map2]. rewrite !on_free_vars_ctx_snoc /=.
  specialize (IHX Γ).
  rewrite !on_free_vars_ctx_app in IHX.
  rewrite andb_assoc IHX -andb_assoc. bool_congr. bool_congr.
  rewrite map2_length; eauto using All2_length.
  rewrite (All2_length X).
  destruct y as [na [bod|] ty]; cbn; auto.
Qed.

Lemma conv_ctx_set_binder_name {cf} {Σ : global_env_ext} {wfΣ : wf Σ} (Γ Δ Δ' : context) (nas : list aname) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ' ->
  ws_cumul_ctx_pb_rel Conv Σ Γ Δ Δ' ->
  ws_cumul_ctx_pb_rel Conv Σ Γ (map2 set_binder_name nas Δ) (map2 set_binder_name nas Δ').
Proof.
  induction 1 in Δ' |- *; intros H; depelim H; intros [cl H']; split; auto;
  depelim H'. cbn. constructor; auto. eapply IHX; auto. split; auto.
  have clΓl' : is_closed_context (Γ ,,, l').
  { depelim a; cbn in *; now apply ws_cumul_pb_is_closed_context in eqt. }
  have eqctx : Σ ⊢ Γ,,, map2 set_binder_name l l' = Γ,,, l'.
  { eapply eq_context_upto_ws_cumul_ctx_pb => //.
    rewrite is_closed_context_set_binder_name //.
    apply eq_context_upto_cat. reflexivity.
    apply eq_context_upto_names_eq_context_upto; tc.
    apply eq_binder_annots_eq => //. }
  depelim a; cbn in *; constructor; auto;
  eapply (ws_cumul_pb_ws_cumul_ctx (pb':=Conv)); tea.
Qed.

Lemma OnOne2_All2_All2 {A B : Type} {l1 l2 : list A} {l3 : list B} {R1  : A -> A -> Type} {R2 R3 : A -> B -> Type} :
  OnOne2 R1 l1 l2 ->
  All2 R2 l1 l3 ->
  (forall x y, R2 x y -> R3 x y) ->
  (forall x y z, R1 x y -> R2 x z -> R3 y z) ->
  All2 R3 l2 l3.
Proof.
  intros o. induction o in l3 |- *.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf'  _ _ _ p r). constructor; auto.
  eapply All2_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo _ H Hf).
  constructor; auto.
Qed.

Lemma OnOne2_All2i_All2i {A B : Type} {l1 l2 : list A} {l3 : list B} {R1  : A -> A -> Type}
  {R2 R3 : nat -> B -> A -> Type} {n} :
  OnOne2 R1 l1 l2 ->
  All2i R2 n l3 l1 ->
  (forall n x y, R2 n x y -> R3 n x y) ->
  (forall n x y z, R1 x y -> R2 n z x -> R3 n z y) ->
  All2i R3 n l3 l2.
Proof.
  intros o. induction o in n, l3 |- *.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf' _  _ _ _ p r0). constructor; auto.
  eapply All2i_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo _ _ H Hf).
  constructor; auto.
Qed.

(* Lemma conv_context_set_binder_name {cf} {Σ} {wfΣ : wf Σ} {Δ nas Γ Γ'} :
  All2 (fun na decl => eq_binder_annot na decl.(decl_name)) nas Γ ->
  conv_context_rel Σ Δ Γ Γ' ->
  conv_context_rel Σ Δ Γ (map2 set_binder_name nas Γ').
Proof.
  intros hlen h. induction h in nas, hlen |- *; case: nas hlen => //.
  * constructor.
  * move=> a l /= h. depelim h.
  * move=> h'; depelim h'.
  * move=> a l /= h'. depelim h'.
    destruct p; cbn; constructor; try constructor; cbn; eauto; try reflexivity.
    eapply IHh; eauto.
    specialize (IHh _ h'). now symmetry.
    eapply IHh; eauto.
    now symmetry.
Qed. *)

(* Lemma conv_context_set_binder_name_inv {cf} {Σ} {wfΣ : wf Σ} {Δ nas Γ Γ'} :
  All2 (fun na decl => eq_binder_annot na decl.(decl_name)) nas Γ' ->
  conv_context_rel Σ Δ Γ (map2 set_binder_name nas Γ') ->
  conv_context_rel Σ Δ Γ Γ'.
Proof.
  intros hlen h. induction Γ' in nas, Γ, h, hlen |- *.
  * case: nas h hlen => h; depelim h; try constructor.
    move=> l h /= //.
  * depelim hlen. depelim h. depelim a0.
    destruct a => //; noconf H.
    constructor; auto. eapply IHΓ'; tea. constructor; auto. simpl in e.
    now transitivity x.
    destruct a as [na' [b''|] ty']; noconf H.
    constructor; auto. eapply IHΓ'; tea. constructor; auto.
    now transitivity x.
Qed. *)

Lemma OnOne2_local_env_forget_types P ctx ctx' :
  OnOne2_local_env (fun Γ => on_one_decl1 P Γ) ctx ctx' ->
  forget_types ctx = forget_types ctx'.
Proof.
  induction 1; simpl.
  - depelim p; subst; auto.
  - depelim p; subst; auto.
  - f_equal; auto.
Qed.

(* Lemma OnOne2_local_env_All Σ P Q R ctx ctx' :
  OnOne2_local_env (fun Γ => on_one_decl1 P Γ) ctx ctx' ->
  All_local_env (lift_typing Q Σ) ctx ->
  (forall Γ t t' ty, All_local_env (lift_typing R Σ) Γ ->
    lift_typing Q Σ Γ t ty -> P Γ t t' -> lift_typing R Σ Γ t' ty) ->
  (forall Γ, All_local_env (lift_typing Q Σ) Γ -> All_local_env (lift_typing R Σ) Γ) ->
  All_local_env (lift_typing R Σ) ctx'.
Proof.
  intros o a H.
  induction o in a |- *; simpl.
  - depelim p; depelim a; constructor; auto.
    destruct l as [s Hs]; exists s. eauto.
    specialize (H Γ t t' (Some (tSort s))). simpl in H. eauto.
  - depelim p; subst; auto. depelim a.
    destruct l as [s' Hs].
    intros IH.
    destruct s as [[? <-]|[? <-]]; subst; constructor; auto.
    specialize (H Γ t t' None). eapply H; eauto.
    now exists s'.
    specialize (H Γ b b (Some t')). eapply H; eauto.
    now exists s'.

    exists s'; eauto. specialize (H Γ t' b t). eapply H. eauto. exact Hs.
  - f_equal; auto.
Qed. *)
From MetaCoq.PCUIC Require Import PCUICContextReduction PCUICOnFreeVars.

(* Lemma red_one_decl_conv_context {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} :
  OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  conv_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  intros o.
  eapply red_ctx_conv_context.
  eapply red_ctx_red_context.
  eapply red_context_app. reflexivity.
  apply red_ctx_rel_red_context_rel; tea.
  constructor. exact o.
Qed. *)

Lemma red_one_decl_red_ctx {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} :
  is_closed_context (Γ ,,, Δ) ->
  OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  red_ctx Σ (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  intros iscl o.
  eapply red_ctx_red_context.
  apply red_context_app.
  eapply red_context_refl.
  apply red_ctx_rel_red_context_rel. tea.
  now apply on_free_vars_ctx_on_ctx_free_vars_closedP_impl.
  constructor. exact o.
Qed.

Lemma into_closed_red_ctx {cf} {Σ} {wfΣ : wf Σ} {Γ Δ} :
  is_closed_context Γ ->
  red_ctx Σ Γ Δ ->
  closed_red_ctx Σ Γ Δ.
Proof.
  intros iscl red.
  apply on_free_vars_ctx_All_fold in iscl.
  eapply All2_fold_All_fold_mix_left in red; tea. cbn in red. clear iscl.
  eapply All2_fold_impl_ind ; tea.
  intros ???? IH IH' [wf ad].
  eapply All_decls_on_free_vars_impl; tea.
  intros t t' clt redt.
  eapply into_closed_red; tea.
  eapply All2_fold_prod_inv in IH as [IH _].
  eapply All2_fold_All_left in IH.
  now eapply on_free_vars_ctx_All_fold in IH.
Qed.

Lemma red_one_decl_red_context {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} :
  is_closed_context (Γ ,,, Δ) ->
  OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  Σ ⊢ Γ ,,, Δ ⇝ Γ ,,, Δ'.
Proof.
  intros iscl o.
  eapply into_closed_red_ctx => //.
  now apply red_one_decl_red_ctx.
Qed.

Lemma red_one_decl_ws_cumul_ctx_pb {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} :
  is_closed_context (Γ ,,, Δ) ->
  OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  Σ ⊢ Γ ,,, Δ = Γ ,,, Δ'.
Proof.
  intros; now eapply red_ctx_ws_cumul_ctx_pb, red_one_decl_red_context.
Qed.

Lemma red1_it_mkLambda_or_LetIn_ctx {cf} {Σ} {wfΣ : wf Σ} Γ Δ Δ' u :
  OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  red1 Σ Γ (it_mkLambda_or_LetIn Δ u)
       (it_mkLambda_or_LetIn Δ' u).
Proof.
  induction 1 in u |- *.
  - depelim p; subst; rewrite /it_mkLambda_or_LetIn /=. eapply red1_it_mkLambda_or_LetIn.
    simpl. now constructor.
  - depelim p; subst; rewrite /=; eapply red1_it_mkLambda_or_LetIn.
    destruct s as [[red ->]|[red ->]]; constructor; auto.
  - simpl. apply IHX.
Qed.

(* Lemma onone_red_cont_context_subst {cf} {Σ} {wfΣ : wf Σ} Γ s s' Δ Δ' :
  wf_local Σ (Γ ,,, Δ' ,,, Δ) ->
  untyped_subslet Γ (List.rev s) Δ' ->
  untyped_subslet Γ (List.rev s') Δ' ->
  OnOne2 (red1 Σ Γ) s s' ->
  conv_context Σ (Γ ,,, subst_context (List.rev s) 0 Δ)
    (Γ ,,, subst_context (List.rev s') 0 Δ).
Proof.
  intros wf us us'.
  intros.
  eapply conv_context_app.
  eapply (conv_ctx_subst (Γ'' := [])). exact wf.
  eapply conv_context_rel_app. reflexivity.
  eapply All2_rev. eapply OnOne2_All2; tea.
  intros. now eapply red_conv, red1_red. reflexivity.
  all:tea.
Qed. *)

Lemma ctx_inst_merge {cf} {Σ} {wfΣ : wf Σ} Γ inst inst' Δ :
  wf_local Σ (Γ ,,, (List.rev Δ)) ->
  PCUICTyping.ctx_inst
    (fun (Γ : context) (t T : term) =>
    forall u : term, closed_red1 Σ Γ t u -> Σ;;; Γ |- u : T) Γ inst Δ ->
  ctx_inst Σ Γ inst Δ ->
  OnOne2 (closed_red1 Σ Γ) inst inst' ->
  ctx_inst Σ Γ inst' Δ.
Proof.
  intros wf c.
  induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
  - depelim o.
  - depelim o. constructor. apply t0. auto.
    rewrite -(List.rev_involutive Δ).
    rewrite subst_telescope_subst_context.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    eapply ctx_inst_cumul.
    2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
        rewrite -subst_telescope_subst_context List.rev_involutive. exact ctxi. }
    eapply ws_cumul_ctx_pb_rel_app.
    eapply conv_cumul_context.
    eapply substitution_ws_cumul_ctx_pb_red_subst.
    now eapply wf_local_closed_context in wf.
    pose proof (wf_local_closed_context (typing_wf_local t2)).
    constructor; [|constructor].
    now eapply closed_red1_red.
    repeat constructor.
    specialize (t0 _ c0).
    eapply All_local_env_app_inv, substitution_wf_local; tea.
    now eapply subslet_ass_tip.
    eapply All_local_env_app_inv, substitution_wf_local; tea.
    now eapply subslet_ass_tip.
    constructor; auto. eapply IHc.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_local; tea.
    repeat (constructor; tea). rewrite subst_empty; tea.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    exact wf. tas. tas.
  - constructor. eapply IHc; eauto.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_local; tea.
    repeat (constructor; tea). eapply subslet_def. constructor.
    all:rewrite !subst_empty //.
    eapply All_local_env_app_inv in wf as [wf _]. depelim wf. now eapply unlift_TermTyp.
Qed.

Lemma ctx_inst_merge' {cf} {Σ} {wfΣ : wf Σ} Γ inst inst' Δ :
  wf_local Σ (Γ ,,, Δ) ->
  PCUICTyping.ctx_inst
    (fun (Γ : context) (t T : term) =>
    forall u : term, closed_red1 Σ Γ t u → Σ;;; Γ |- u : T) Γ inst (List.rev Δ) ->
  ctx_inst Σ Γ inst (List.rev Δ) ->
  OnOne2 (closed_red1 Σ Γ) inst inst' ->
  ctx_inst Σ Γ inst' (List.rev Δ).
Proof.
  intros. eapply ctx_inst_merge; try rewrite ?(List.rev_involutive Δ) //; tea.
Qed.

Lemma is_open_term_snoc (Γ : context) M d : on_free_vars (shiftnP 1 (shiftnP #|Γ| xpred0)) M -> is_open_term (Γ ,, d) M.
Proof.
  rewrite /=.
  now rewrite [shiftnP (S #|Γ|) _]shiftnP_S.
Qed.

#[global] Hint Resolve is_open_term_snoc : fvs.

Ltac forward_keep H :=
  match type of H with
  ?X -> _ =>
    let H' := fresh in
    assert (H' : X) ; [|specialize (H H')]
  end.
(** The subject reduction property of the system: *)

Definition SR_red1 {cf} Σ Γ t T :=
  forall u (Hu : closed_red1 Σ Γ t u), Σ ;;; Γ |- u : T.
  Ltac inv_on_free_vars :=
    match goal with
    | [ H : is_true (on_free_vars_decl _ _) |- _ ] => progress cbn in H
    | [ H : is_true (on_free_vars_decl _ (vdef _ _ _)) |- _ ] => unfold on_free_vars_decl, test_decl in H
    | [ H : is_true (_ && _) |- _ ] =>
      move/andP: H => []; intros
    | [ H : is_true (on_free_vars ?P ?t) |- _ ] =>
      progress (cbn in H || rewrite on_free_vars_mkApps in H);
      (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] ||
        eapply forallb_All in H); intros
    | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
      move/andP: H => []; rewrite ?shiftnP_xpredT; intros
    | [ H : is_true (test_context_k _ _ _ ) |- _ ] =>
      rewrite -> test_context_k_closed_on_free_vars_ctx in H
    end.

Lemma closed_red1_ind (Σ : global_env_ext) (P0 : context -> term -> term -> Type)
  (P := fun Γ t u => is_closed_context Γ -> is_open_term Γ t -> P0 Γ t u) :
  (forall (Γ : context) (na : aname) (t b a : term),
    P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

  (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

  (forall (Γ : context) (i : nat) (body : term),
  option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

  (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
    (p : predicate term) (brs : list (branch term)) br,
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
        (iota_red ci.(ci_npar) p args br)) ->

  (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
  unfold_fix mfix idx = Some (narg, fn) ->
  is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

  (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
    (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
  unfold_cofix mfix idx = Some (narg, fn) ->
  P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

  (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
    (narg : nat) (fn : term),
  unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

  (forall (Γ : context) c (decl : constant_body) (body : term),
  declared_constant Σ c decl ->
  forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

  (forall (Γ : context) p (args : list term) (u : Instance.t)
    (arg : term),
      nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
      P Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

  (forall (Γ : context) (na : aname) (M M' N : term),
  closed_red1 Σ Γ M M' -> P0 Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

  (forall (Γ : context) (na : aname) (M M' N : term),
  closed_red1 Σ (Γ,, vass na N) M M' -> P0 (Γ,, vass na N) M M' ->
  P Γ (tLambda na N M) (tLambda na N M')) ->

  (forall (Γ : context) (na : aname) (b t b' r : term),
  closed_red1 Σ Γ b r -> P0 Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

  (forall (Γ : context) (na : aname) (b t b' r : term),
  closed_red1 Σ Γ t r -> P0 Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

  (forall (Γ : context) (na : aname) (b t b' r : term),
  closed_red1 Σ (Γ,, vdef na b t) b' r -> P0 (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

  (forall (Γ : context) (ci : case_info) p params' c brs,
    OnOne2 (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) p.(pparams) params' ->
      P Γ (tCase ci p c brs)
          (tCase ci (set_pparams p params') c brs)) ->

  (* (forall (Γ : context) (ci : case_info) p pcontext' c brs,
    OnOne2_local_env (on_one_decl (fun Γ' => P (Γ ,,, Γ'))) p.(pcontext) pcontext' ->
    P Γ (tCase ci p c brs)
      (tCase ci (set_pcontext p pcontext') c brs)) ->
*)
  (forall (Γ : context) (ci : case_info) p preturn' c brs,
    closed_red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
    P0 (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
    P Γ (tCase ci p c brs)
        (tCase ci (set_preturn p preturn') c brs)) ->

  (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
  closed_red1 Σ Γ c c' -> P0 Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

  (forall (Γ : context) ci p c brs brs',
    OnOne2 (fun br br' =>
    (on_Trel_eq (Trel_conj (closed_red1 Σ (Γ ,,, inst_case_branch_context p br))
      (P0 (Γ ,,, inst_case_branch_context p br)))
      bbody bcontext br br')) brs brs' ->
    P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

  (forall (Γ : context) (p : projection) (c c' : term),
    closed_red1 Σ Γ c c' -> P0 Γ c c' ->
    P Γ (tProj p c) (tProj p c')) ->

  (forall (Γ : context) (M1 N1 : term) (M2 : term),
  closed_red1 Σ Γ M1 N1 -> P0 Γ M1 N1 ->
  P Γ (tApp M1 M2) (tApp N1 M2)) ->

  (forall (Γ : context) (M2 N2 : term) (M1 : term),
  closed_red1 Σ Γ M2 N2 -> P0 Γ M2 N2 ->
  P Γ (tApp M1 M2) (tApp M1 N2)) ->

  (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
  closed_red1 Σ Γ M1 N1 -> P0 Γ M1 N1 ->
  P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

  (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
  closed_red1 Σ (Γ,, vass na M1) M2 N2 ->
  P0 (Γ,, vass na M1) M2 N2 ->
  P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

  (forall (Γ : context) (ev : nat) (l l' : list term),
      OnOne2 (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) l l' ->
      P Γ (tEvar ev l) (tEvar ev l')) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
  P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ (Γ ,,, fix_context mfix0))
                                (P0 (Γ ,,, fix_context mfix0))) dbody
                      (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
  P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
  P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ (Γ ,,, fix_context mfix0))
                                (P0 (Γ ,,, fix_context mfix0))) dbody
                      (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
  P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

  (forall (Γ : context) (arr : array_model term)
  (value : list term),
  OnOne2 (Trel_conj (closed_red1 Σ Γ) (P Γ)) (array_value arr) value ->
  P Γ (tPrim (primArray; primArrayModel arr))
    (tPrim (primArray; primArrayModel (set_array_value arr value)))) ->

(forall (Γ : context) (arr : array_model term)
  (def : term), closed_red1 Σ Γ (array_default arr) def ->
P Γ (array_default arr) def ->
P Γ (tPrim (primArray; primArrayModel arr))
  (tPrim (primArray; primArrayModel (set_array_default arr def)))) ->

(forall (Γ : context) (arr : array_model term)
  (ty : term), closed_red1 Σ Γ (array_type arr) ty ->
P Γ (array_type arr) ty ->
P Γ (tPrim (primArray; primArrayModel arr))
  (tPrim (primArray; primArrayModel (set_array_type arr ty)))) ->

  forall (Γ : context) (t t0 : term), closed_red1 Σ Γ t t0 -> P0 Γ t t0.
Proof.
  intros.
  destruct X30 as [clΓ clt r].
  move: clΓ clt.
  Ltac t :=
    eauto; try split; eauto;
    try apply on_free_vars_ctx_snoc_ass => //;
    try apply on_free_vars_ctx_snoc_def => //;
    try apply is_open_term_snoc => //;
    repeat (try inv_on_free_vars; eauto with fvs; cbn).
  induction r using red1_ind_all; intros;
    try solve [multimatch goal with
    | H : _ |- _ => eapply H
    end; t].
  - eapply X13. 2-3:t.
    inv_on_free_vars.
    eapply forallb_All in p0.
    eapply OnOne2_All_mix_left in X30; tea.
    eapply OnOne2_impl; tea; repeat (intuition auto; t).
  - forward_keep IHr.
    { rewrite on_free_vars_ctx_app clΓ.
      eapply on_free_vars_ctx_inst_case_context; trea; t. }
    forward_keep IHr.
    { repeat inv_on_free_vars.
      rewrite length_app inst_case_predicate_context_length -shiftnP_add //. }
    apply X14 => //.
  - eapply X16 => //.
    inv_on_free_vars.
    eapply forallb_All in p4.
    eapply OnOne2_All_mix_left in X30; tea. cbn in X30.
    eapply OnOne2_impl; tea; cbn; intros ?? [[[]] ?].
    forward_keep p5.
    { rewrite on_free_vars_ctx_app clΓ /=.
      eapply on_free_vars_ctx_inst_case_context; trea; t. }
    forward_keep p5.
    { repeat inv_on_free_vars.
      rewrite length_app inst_case_branch_context_length -shiftnP_add //. }
    intuition auto. split; auto.
  - eapply X22 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X30; tea.
    eapply OnOne2_impl; tea; cbn; intuition auto; t.
  - eapply X23 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X30; tea.
    eapply OnOne2_impl; tea; cbn; intuition auto; t.
  - eapply X24 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X30; tea.
    eapply OnOne2_impl; tea; cbn; intros ?? [[[]] ?].
    forward_keep p.
    { rewrite on_free_vars_ctx_app clΓ /=.
      eapply on_free_vars_fix_context; trea; t. }
    forward_keep p. {
      rewrite length_app fix_context_length -shiftnP_add //.
      now inv_on_free_vars. }
    intuition auto. split; auto.
  - eapply X25 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X30; tea.
    eapply OnOne2_impl; tea; cbn; intuition auto; t.
  - eapply X26 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X30; tea.
    eapply OnOne2_impl; tea; cbn; intros ?? [[[]] ?].
    forward_keep p.
    { rewrite on_free_vars_ctx_app clΓ /=.
      eapply on_free_vars_fix_context; trea; t. }
    forward_keep p. {
      rewrite length_app fix_context_length -shiftnP_add //.
      now inv_on_free_vars. }
    intuition auto. split; auto.
  - eapply X27 => //.
    cbn in clt; rtoProp. eapply forallb_All in H.
    eapply OnOne2_All_mix_left in X30; tea.
    eapply OnOne2_impl; tea; cbn; intros ?? [[]]. split; eauto.
    split; eauto.
Qed.

Definition closed_red1_ind' :=
    ltac:(let T := type of closed_red1_ind in
    let T' := eval cbn in T in
      exact (closed_red1_ind : T')).
(*
Ltac revert_until x :=
  repeat lazymatch goal with
  | [ H : _ |- _ ] => revert H
  end. *)

Ltac invert_closed_red H :=
  generalize_eqs H; destruct H using closed_red1_ind'; simplify_dep_elim.

Ltac invert_mkApps_fix_eq :=
  match goal with
  | [ H : mkApps (tFix _ _) _ = _ |- _ ] =>
    apply mkApps_Fix_spec in H; noconf H
  end.

Coercion closed_red1_red : closed_red1 >-> closed_red.

Lemma wt_cumul_pb_refl {cf} {Σ} {wfΣ : wf Σ} {Γ t T} : Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ t = t.
Proof.
  intros. apply ws_cumul_pb_refl.
  apply wf_local_closed_context; pcuic.
  now apply subject_closed in X; apply closedn_on_free_vars.
Qed.

Lemma ws_cumul_pb_meta_refl {cf} {Σ} {wfΣ : wf Σ} {Γ T U} :
  is_closed_context Γ -> closedn #|Γ| T -> T = U -> Σ ;;; Γ ⊢ T = U.
Proof.
  intros clΓ cl ->. apply ws_cumul_pb_refl => //. now apply closedn_on_free_vars.
Qed.

Lemma ws_cumul_pb_eq_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} :
  Σ ;;; Γ ⊢ T = U -> U = V -> Σ ;;; Γ ⊢ T = V.
Proof.
  now intros tr ->.
Qed.

Lemma eq_ws_cumul_pb_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} :
  T = U -> Σ ;;; Γ ⊢ U = V -> Σ ;;; Γ ⊢ T = V.
Proof.
  now intros -> tr.
Qed.

Lemma ws_cumul_pb_terms_eq_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} :
  ws_cumul_pb_terms Σ Γ T U -> U = V -> ws_cumul_pb_terms Σ Γ T V.
Proof.
  now intros tr ->.
Qed.

Lemma eq_ws_cumul_pb_terms_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} :
  T = U -> ws_cumul_pb_terms Σ Γ U V -> ws_cumul_pb_terms Σ Γ T V.
Proof.
  now intros -> tr.
Qed.

Lemma red_terms_refl {Σ Γ ts} :
  is_closed_context Γ ->
  forallb (is_open_term Γ) ts -> red_terms Σ Γ ts ts.
Proof.
  solve_all.
  eapply All_All2; tea. cbn.
  firstorder auto.
Qed.

Local Notation welltyped Σ Γ t := (∑ T, Σ ;;; Γ |- t : T).
Local Notation welltyped_terms Σ Γ := (All (fun t => welltyped Σ Γ t)).

Lemma spine_subst_wt_terms {cf} {Σ Γ inst s Δ} : spine_subst Σ Γ inst s Δ ->
  welltyped_terms Σ Γ inst.
Proof.
  move/spine_subst_ctx_inst.
  induction 1; try constructor; auto.
  now exists t.
Qed.

Lemma wt_terms_ws_cumul_pb {cf} {Σ} {wfΣ : wf Σ} {Γ ts} : welltyped_terms Σ Γ ts -> ws_cumul_pb_terms Σ Γ ts ts.
Proof.
  intros; eapply All_All2; tea. cbn; intros x [T HT].
  now eapply wt_cumul_pb_refl.
Qed.

Lemma weakening_ws_cumul_ctx_pb {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ0 Δ1} :
  Σ ⊢ Γ ,,, Δ0 = Γ ,,, Δ1 ->
  Σ ⊢ Γ ,,, Δ = Γ ,,, Δ ->
  Σ ⊢ Γ ,,, Δ ,,, lift_context #|Δ| 0 Δ0 = Γ ,,, Δ ,,, lift_context #|Δ| 0 Δ1.
Proof.
  intros h h'.
  eapply ws_cumul_ctx_pb_rel_app.
  eapply ws_cumul_ctx_pb_rel_app in h.
  induction h.
  induction b; cbn. constructor. fvs.
  constructor.
  depelim p; cbn; rewrite !lift_context_snoc; constructor; auto; fvs;
  rewrite /lift_decl /map_decl /=; constructor; auto with fvs. apply IHb.
  constructor; auto. rewrite !Nat.add_0_r. rewrite -(All2_fold_length b).
  eapply weakening_ws_cumul_pb => //. fvs. apply IHb.
  constructor; auto; rewrite !Nat.add_0_r -(All2_fold_length b);
  apply weakening_ws_cumul_pb => //; fvs.
Qed.

Lemma on_constructor_closed_indices {cf} {Σ} {wfΣ : wf Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (is_open_term (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) (cstr_indices cdecl).
Proof.
  intros.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  eapply ctx_inst_impl in X. 2: intros ??; apply unlift_TermTyp.
  now eapply ctx_inst_open_terms in X.
Qed.

Lemma on_constructor_wf_arities_pars_args {cf} {Σ} {wfΣ : wf Σ} {i mdecl idecl cdecl} :
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  wf_local (Σ.1, ind_universes mdecl) (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl).
Proof.
  move=> H.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  move/on_cargs/sorts_local_ctx_wf_local: onc => H'.
  apply H'.
  apply weaken_wf_local; tea.
  eapply (wf_arities_context H).
  now apply onParams in onmind.
Qed.

Lemma closedP_shiftnP_eq k : closedP k xpredT =1 shiftnP k xpred0.
Proof.
  rewrite /closedP /shiftnP. intros i; nat_compare_specs => //.
Qed.

Lemma on_free_vars_closedn k t : closedn k t = on_free_vars (shiftnP k xpred0) t.
Proof.
  rewrite closedP_on_free_vars.
  eapply on_free_vars_ext, closedP_shiftnP_eq.
Qed.

Lemma on_constructor_closed_indices_inst {cf} {Σ} {wfΣ : wf Σ} {i mdecl idecl cdecl u} :
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  All (is_open_term (ind_params mdecl ,,, cstr_args cdecl)@[u])
    (map (subst (inds (inductive_mind (fst i)) u (ind_bodies mdecl))
           (#|cstr_args cdecl| + #|ind_params mdecl|)) (cstr_indices cdecl)@[u]).
Proof.
  intros H cu.
  unshelve epose proof (H' := declared_constructor_to_gen H); eauto.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  eapply ctx_inst_impl in X. 2: intros ??; apply unlift_TermTyp.
  eapply ctx_inst_inst in X; tea.
  eapply ctx_inst_open_terms in X.
  eapply All_map, All_impl; tea.
  cbn; intros x clx.
  rewrite -[_ ,,, _]app_context_nil_l -[_ ,,, cstr_args cdecl]app_context_assoc app_context_assoc in clx.
  rewrite !subst_instance_app_ctx in clx.
  eapply (is_open_term_subst (Γ := []) (s:=inds (inductive_mind i.1) u (ind_bodies mdecl))) in clx.
  3:eapply inds_is_open_terms. 3:len.
  rewrite app_context_nil_l subst_context_app in clx.
  rewrite closed_ctx_subst in clx.
  eapply declared_inductive_closed_params_inst.
  unshelve eapply declared_inductive_from_gen; eauto.
  len in clx. len.
  rewrite app_context_nil_l app_context_assoc.
  epose proof (on_constructor_wf_arities_pars_args H).
  eapply (wf_local_instantiate (decl:=InductiveDecl mdecl)) in X0; tea.
  rewrite !subst_instance_app_ctx in X0.
  now eapply wf_local_closed_context in X0. apply H'.
  eapply declared_inductive_wf_global_ext; eauto.
  unshelve eapply declared_minductive_from_gen; eauto.
Qed.

Arguments pair {A B}%_type_scope &.

Lemma ws_cumul_pb_terms_refl {cf} {Σ} {wfΣ : wf Σ} {Γ u} :
  is_closed_context Γ ->
  forallb (is_open_term Γ) u ->
  ws_cumul_pb_terms Σ Γ u u.
Proof.
  intros. eapply into_ws_cumul_pb_terms => //.
  eapply All2_refl; reflexivity.
Qed.

Lemma map2_set_binder_name_expand_lets nas Γ Δ :
  #|nas| = #|Δ| ->
  map2 set_binder_name nas (expand_lets_ctx Γ Δ) =
  expand_lets_ctx Γ (map2 set_binder_name nas Δ).
Proof.
  move=> hlen.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite PCUICRenameConv.map2_set_binder_name_fold ?lengths //.
  rewrite PCUICRenameConv.map2_set_binder_name_fold ?lengths //.
Qed.

Lemma closed_red1_eq_context_upto_names {Σ Γ Γ'} {t u} :
  eq_context_upto_names Γ Γ' → closed_red1 Σ Γ t u → closed_red1 Σ Γ' t u.
Proof.
  intros eqctx []; split; auto.
  - eapply eq_context_upto_names_on_free_vars; tea.
  - now rewrite -(All2_length eqctx).
  - eapply red1_eq_context_upto_names; tea.
Qed.

Lemma closed_red1_ws_cumul_pb {cf} {Σ} {wfΣ : wf Σ} {Γ} {t u} :
  closed_red1 Σ Γ t u -> ws_cumul_pb Conv Σ Γ t u.
Proof.
  intros cl. now eapply red_conv, closed_red1_red.
Qed.

Notation "Σ ;;; Γ ⊢ t ⇝1 u" := (closed_red1 Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ⇝1  u").

Lemma on_free_vars_ctx_tip P d : on_free_vars_ctx P [d] = on_free_vars_decl P d.
Proof. cbn; rewrite andb_true_r // shiftnP0 //. Qed.

Lemma on_free_vars_it_mkLambda_or_LetIn {P Δ t} :
  on_free_vars P (it_mkLambda_or_LetIn Δ t) =
    on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
Proof.
  move: P. induction Δ using rev_ind => P.
  - cbn. now rewrite shiftnP0.
  - destruct x as [na [b|] ty]; rewrite it_mkLambda_or_LetIn_app /= /mkLambda_or_LetIn /=.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
      /on_free_vars_decl /test_decl /=. ring.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
     /on_free_vars_decl /test_decl /=. ring.
Qed.

Lemma closed_red1_it_mkLambda_or_LetIn {cf} {Σ} {wfΣ : wf Σ} {Γ} {Δ t u} :
  Σ ;;; Γ ,,, Δ ⊢ t ⇝1 u -> Σ ;;; Γ ⊢ it_mkLambda_or_LetIn Δ t ⇝1 it_mkLambda_or_LetIn Δ u.
Proof.
  intros [clΓΔ opt r].
  split; eauto with fvs.
  - rewrite on_free_vars_ctx_app in clΓΔ. now move/andP: clΓΔ.
  - rewrite on_free_vars_it_mkLambda_or_LetIn.
    rewrite on_free_vars_ctx_app in clΓΔ. move/andP: clΓΔ => [].
    rewrite shiftnP_add -length_app opt andb_true_r //.
  - now eapply red1_it_mkLambda_or_LetIn.
Qed.

Lemma closed_red1_mkApps_left {cf} {Σ} {wfΣ : wf Σ} {Γ} {t u ts} :
  Σ ;;; Γ ⊢ t ⇝1 u ->
  forallb (is_open_term Γ) ts ->
  Σ ;;; Γ ⊢ mkApps t ts ⇝1 mkApps u ts.
Proof.
  intros r cl.
  split; eauto with fvs.
  - rewrite on_free_vars_mkApps (clrel_src r) //.
  - eapply red1_mkApps_f, r.
Qed.

Lemma weakening_closed_red1 {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' Γ'' : context} {M N} :
  closed_red1 Σ (Γ,,, Γ') M N ->
  is_closed_context (Γ ,,, Γ'') ->
  closed_red1 Σ (Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros r cl. split => //.
  apply is_closed_context_lift => //. apply r.
  apply is_open_term_lift, r.
  apply weakening_red1 => //. eapply on_free_vars_impl, r => //.
  apply r.
Qed.

Lemma closed_red1_case_branch_type {cf} {Σ} {wfΣ : wf Σ} {Γ} {ret ret'} {ind mdecl idecl k cdecl br p} :
  let cb := case_branch_type ind mdecl idecl p br ret k cdecl in
  let cb' := case_branch_type ind mdecl idecl p br ret' k cdecl in
  wf_branch cdecl br ->
  is_open_term (Γ ,,, cb.1) cb.2 ->
  is_closed_context (Γ ,,, cb.1) ->
  Σ ;;; Γ ⊢ ret ⇝1 ret' ->
  Σ ;;; Γ ,,, cb.1 ⊢ cb.2 ⇝1 cb'.2.
Proof.
  intros cb cb' wfbr op r.
  split => //.
  eapply closed_red1_mkApps_left => //.
  - relativize #|cstr_args cdecl|; [eapply (weakening_closed_red1 (Γ':=[]))|] => //.
    apply (case_branch_context_length_args wfbr).
  - move: op; rewrite on_free_vars_mkApps => /andP[] //.
Qed.

Lemma inst_case_branch_context_eq {cf} {Σ} {wfΣ : wf Σ} {p br} {ind mdecl cdecl} :
  declared_minductive Σ (inductive_mind ind) mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
  eq_context_upto_names br.(bcontext) (cstr_branch_context ind mdecl cdecl) ->
  eq_context_upto_names (inst_case_branch_context p br) (pre_case_branch_context ind mdecl p.(pparams) p.(puinst) cdecl).
Proof.
  intros declm cu eqbr.
  rewrite /inst_case_branch_context /pre_case_branch_context.
  rewrite /inst_case_context.
  eapply alpha_eq_subst_context.
  etransitivity; tea.
  - eapply alpha_eq_subst_instance; tea.
  - rewrite /cstr_branch_context subst_instance_expand_lets_ctx subst_instance_subst_context //.
    rewrite instantiate_inds //.
    reflexivity.
Qed.

Lemma skipn_nil_length {A} (l : list A) n : skipn n l = [] -> #|l| <= n.
Proof.
  induction n in l |- *; destruct l; simpl; rewrite ?skipn_0 ?skipn_S; auto; try congruence; try lia.
  intros hs. specialize (IHn _ hs). lia.
Qed.

Lemma context_assumptions_bound Γ : context_assumptions Γ <= #|Γ|.
Proof.
  induction Γ as [|[? [] ?] ?]; intros; cbn; lia.
Qed.

Lemma declared_projection_indices {cf} {Σ} {wfΣ : wf Σ} {p mdecl idecl cdecl pdecl} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  #|ind_indices idecl| = 0.
Proof.
  move=> isdecl.
  case: (on_declared_projection isdecl) => onind. cbn.
  destruct ind_cunivs as [] => /= // => [] [] [] [] //.
  destruct l as [] => //. intros sorts onprojs hp.
  now destruct onprojs.
Qed.

Lemma map_subst_lift0_subst s k l : map (subst s k ∘ lift0 k) l = map (lift0 k ∘ subst0 s) l.
Proof.
  eapply map_ext => x. now rewrite subst_lift_subst.
Qed.

Lemma substitution_ws_cumul_pb_subst_conv {cf} {Σ} {wfΣ : wf Σ} {le Γ Γ0 Γ1 Δ s s' T U} :
  subslet Σ Γ s Γ0 ->
  wf_subslet Σ Γ s' Γ1 ->
  ws_cumul_pb_terms Σ Γ s s' ->
  Σ;;; Γ ,,, Γ0 ,,, Δ ⊢ T ≤[le] U ->
  Σ;;; Γ ,,, subst_context s 0 Δ ⊢ subst s #|Δ| T ≤[le] subst s' #|Δ| U.
Proof.
  intros subs subs' eq.
  eapply substitution_ws_cumul_pb_subst_conv; tea.
  * now eapply subslet_untyped_subslet.
  * eapply subslet_untyped_subslet, subs'.
  * eapply wf_local_closed_context, subs'.
Qed.

Lemma wf_subslet_skipn {cf Σ Γ s Δ n} :
  wf_subslet Σ Γ s Δ → wf_subslet Σ Γ (skipn n s) (skipn n Δ).
Proof.
  intros []; split; auto using subslet_skipn.
  now eapply All_local_env_app_skipn.
Qed.

Lemma isType_subst_arities {cf} {Σ} {wfΣ : wf Σ} {ind mdecl idecl u} {Γ T} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ ((arities_context (ind_bodies mdecl))@[u] ,,, Γ) T ->
  isType Σ (subst_context (ind_subst mdecl ind u) 0 Γ) (subst (ind_subst mdecl ind u) #|Γ| T).
Proof.
  intros isdecl cu.
  rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
  move/(isType_substitution (subslet_inds isdecl cu)).
  rewrite app_context_nil_l //.
Qed.

Lemma wt_closed_red1 {cf} {Σ} {wfΣ : wf Σ} {Γ T U} :
  welltyped Σ Γ T ->
  red1 Σ Γ T U ->
  Σ ;;; Γ ⊢ T ⇝1 U.
Proof.
  intros [ty HT] r.
  split => //.
  eapply wf_local_closed_context; pcuic.
  now eapply subject_is_open_term in HT.
Qed.

Lemma isType_expand_lets  {cf} {Σ} {wfΣ : wf Σ} {Γ Δ T} :
  isType Σ (Γ ,,, Δ) T ->
  isType Σ (smash_context [] Γ ,,, expand_lets_ctx Γ Δ) (expand_lets_k Γ #|Δ| T).
Proof.
  intros (_ & s & Hs & _). eapply has_sort_isType. revert Hs.
  rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
  move/typing_expand_lets_gen; rewrite app_context_nil_l => hs.
  apply hs.
Qed.

Lemma isType_subst_extended_subst {cf} {Σ} {wfΣ : wf Σ} {Γ Δ T} :
  isType Σ (Γ ,,, Δ) T ->
  isType Σ (smash_context [] Γ ,,, subst_context (extended_subst Γ 0) 0 Δ)
    (subst (extended_subst Γ 0) #|Δ| T).
Proof.
  intros (_ & s & Hs & _). eapply has_sort_isType.
  have wfctx := typing_wf_local Hs.
  generalize Hs.
  rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
  move/typing_expand_lets_gen; rewrite app_context_nil_l => hs.
  rewrite /expand_lets_ctx /expand_lets_k_ctx in hs.
  rewrite closed_ctx_lift /= in hs.
  move/closed_wf_local: wfctx. rewrite closedn_ctx_app => /andP[] //.
  rewrite /expand_lets_k /= in hs.
  rewrite lift_closed in hs. eapply subject_closed in Hs.
  now len in Hs.
  apply hs.
Qed.

Lemma isType_mkApps_Ind_proj_inv {cf:checker_flags} {Σ Γ p u pars} (wfΣ : wf Σ.1)
  {mdecl idecl cdecl pdecl} (declm : declared_projection Σ.1 p mdecl idecl cdecl pdecl) :
  isType Σ Γ (mkApps (tInd p.(proj_ind) u) pars) ->
    let parctx := (subst_instance u (ind_params mdecl)) in
    [× spine_subst Σ Γ pars (List.rev pars) (smash_context [] parctx),
       #|pars| = ind_npars mdecl,
       idecl.(ind_indices) = [] &
       consistent_instance_ext Σ (ind_universes mdecl) u].
Proof.
  move=> isTy. generalize isTy. apply isType_wf_local in isTy.
  move/(isType_mkApps_Ind_inv _ declm isTy) => [parsubst [argsubst [sp sargs hp hargs cu]]].
  generalize (declared_projection_indices declm).
  move/length_nil => hindices.
  move: hargs; rewrite hindices /=.
  move/length_nil/skipn_nil_length.
  move/firstn_length_le_inv: hp => hle hge.
  have heq: #|pars| = ind_npars mdecl by lia.
  split => //.
  rewrite -heq in sp.
  rewrite firstn_all in sp.
  now apply: spine_subst_smash.
Qed.

Lemma type_Cumul_alt {cf} {Σ} {wfΣ : wf Σ} (Γ : context) (t T T' : term) :
  Σ;;; Γ |- t : T → isType Σ Γ T' →
  Σ;;; Γ |- T <= T' → Σ;;; Γ |- t : T'.
Proof.
  intros Ht isty cum.
  eapply (type_ws_cumul_pb (pb:=Cumul)); tea.
  eapply into_ws_cumul_pb; fvs.
Qed.

Lemma lift_judgment_SR {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ na na' tm tm' ty ty' u :
  lift_typing0 (fun t T : term =>
    Σ ;;; Γ |- t : T ×
    forall u : term, Σ ;;; Γ ⊢ t ⇝1 u -> Σ;;; Γ |- u : T)
    (j_decl_s (mkdecl na tm ty) u) ->
  on_one_decl (fun t t' => Σ ;;; Γ ⊢ t ⇝1 t') (mkdecl na tm ty) (mkdecl na' tm' ty') ->
  lift_typing typing Σ Γ (j_decl_s (mkdecl na' tm' ty') u).
Proof.
  cbn; intros tu Hdecl.
  destruct tm as [tm|], tm' as [tm'|] => //; destruct Hdecl as (<- & h). 1: destruct h as [[h <-] | [h <-]].
  all: apply lift_sorting_it_impl_gen with tu => //= [] [] HT IHT; eauto.
  eapply type_ws_cumul_pb; tea.
  { eapply lift_sorting_forget_univ, lift_sorting_it_impl_gen with tu => // Ht. now apply Ht. }
  eapply (red_ws_cumul_pb (pb:=Cumul)).
  now eapply closed_red1_red.
Qed.

Lemma sr_red1 {cf:checker_flags} :
  env_prop SR_red1
    (fun Σ Γ j =>
      lift_typing0 (fun t T => Σ ;;; Γ |- t : T × forall u, Σ ;;; Γ ⊢ t ⇝1 u -> Σ ;;; Γ |- u : T) j)
      (fun Σ Γ => wf_local Σ Γ ×
        (forall Γ' Δ' Δ,
          Γ = Γ' ,,, Δ' ->
          OnOne2_local_env (fun Δ : context => on_one_decl (closed_red1 Σ (Γ',,, Δ))) Δ' Δ ->
          wf_local_rel Σ Γ' Δ)).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps; auto.
  2-15:match goal with
    | [H : (_ ;;; _ |- _ <=s _) |- _ ] => idtac
    | _ =>
      invert_closed_red Hu;
      try solve [invert_mkApps_fix_eq];
      try solve [econstructor; eauto];
      try solve [
        match goal with
        | h : _ = mkApps _ ?args |- _ =>
          let e := fresh "e" in
          apply (f_equal nApp) in h as e ; simpl in e ;
          rewrite nApp_mkApps in e ; simpl in e ;
          destruct args ; discriminate
        end
      ]
    end.

  - (* Contexts *)
    split; auto. intros Γ' Δ' Δ ->. clear X0.
    induction 1.
    * depelim X. apply All_local_rel_abs.
      now eapply All_local_env_app_inv.
      eapply lift_judgment_SR with (2 := p).
      eapply lift_sorting_it_impl_gen with (tu := tu) => //.
    * depelim X. apply All_local_rel_def.
      now eapply All_local_env_app_inv.
      eapply lift_judgment_SR with (2 := p); tea.
      eapply lift_sorting_it_impl_gen with tu => //=.

    * assert (wf_local Σ (Γ' ,,, Γ'0) × lift_typing typing Σ (Γ' ,,, Γ) (j_decl d) × is_closed_context (Γ' ,,, Γ)) as (wfΓ' & ond & clΓ').
      { depelim X; specialize (IHX0 _ X); clear X; pose proof (wf_local_closed_context all).
        all: split; [|now split].
        all: eapply All_local_env_app_inv in all as [wfΓ _]; eapply All_local_env_app in wfΓ; tea. }
      clear wfΓ X IHX0.
      apply All_local_rel_snoc.
      1: now apply All_local_env_app_inv in wfΓ'.
      apply lift_typing_impl with (1 := ond) => // ?? Hty.
      eapply closed_context_conversion; tea.
      eapply red_one_decl_ws_cumul_ctx_pb => //.
      eapply OnOne2_local_env_impl; tea.
      intros ???. eapply on_one_decl_impl => ???; firstorder.

  - (* Rel delta reduction *)
    rewrite heq_nth_error in H. destruct decl as [na b ty]; noconf H.
    simpl.
    eapply All_local_env_nth_error in wfΓ as X0; tea.
    apply unlift_TermTyp in X0.
    cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    eapply weakening_length; auto.
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    now unfold app_context; rewrite firstn_skipn.

  - (* Prod *)
    assert (X1' : lift_typing typing Σ Γ (j_vass_s na N1 s1)).
    1: now unshelve eapply lift_judgment_SR with (1 := X1) => //.
    constructor; eauto.
    unshelve eapply (closed_context_conversion _ typeb).
    1: constructor; tas.
    1: now eapply lift_sorting_forget_univ.
    constructor.
    now eapply ws_cumul_ctx_pb_refl, wf_local_closed_context.
    constructor; auto. eapply red_conv.
    now eapply closed_red1_red.

  - (* Lambda *)
    assert (X1' : lift_typing typing Σ Γ (j_vass na M')).
    1: now unshelve eapply lift_judgment_SR with (1 := X1) => //.
    eapply type_Cumul_alt. eapply type_Lambda; eauto.
    unshelve eapply (closed_context_conversion _ typeb). pcuic.
    constructor. now eapply ws_cumul_ctx_pb_refl, wf_local_closed_context.
    constructor; auto. eapply red_conv. now eapply closed_red1_red.
    assert (Σ ;;; Γ |- tLambda na t b : tProd na t bty). econstructor; pcuics.
    now eapply validity in X2.
    econstructor 3. eapply cumul_refl'.
    constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul_alt.
    apply (@substitution_let _ _ _ Γ na b b_ty b' b'_ty typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn na b b_ty b' : tLetIn na b b_ty b'_ty).
    econstructor; eauto.
    eapply (validity X2).
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    assert (X1' : lift_typing typing Σ Γ (j_vdef na r b_ty)).
    { unshelve eapply lift_judgment_SR with (1 := X1); tea. now constructor; [|right]. }
    eapply type_Cumul_alt.
    econstructor; eauto.
    unshelve eapply (closed_context_conversion _ typeb'). pcuic.
    constructor. eapply ws_cumul_ctx_pb_refl; eauto. constructor; auto.
    now eapply red_conv, closed_red1_red. apply ws_cumul_pb_refl; eauto. now repeat inv_on_free_vars.
    assert (Σ ;;; Γ |- tLetIn na b b_ty b' : tLetIn na b b_ty b'_ty). econstructor; eauto.
    eapply (validity X2).
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn type annotation *)
    assert (X1' : lift_typing typing Σ Γ (j_vdef na b r)).
    { unshelve eapply lift_judgment_SR with (1 := X1); tea. now constructor; [|left]. }
    eapply type_Cumul_alt.
    econstructor; eauto.
    unshelve eapply (closed_context_conversion _ typeb'). pcuic.
    constructor; auto. eapply ws_cumul_ctx_pb_refl; eauto. constructor; auto.
    eapply ws_cumul_pb_refl; eauto; repeat inv_on_free_vars =>//.
    apply: red_conv Hu.
    assert (Σ ;;; Γ |- tLetIn na b b_ty b' : tLetIn na b b_ty b'_ty). econstructor; eauto.
    eapply (validity X2).
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as (B' & Ht & Hb & HU) =>//.
    apply cumul_Prod_inv in HU as [eqann eqA leqB] => //.
    pose proof (validity typet) as i.
    eapply isType_tProd in i as [Hdom Hcodom]; auto.
    eapply type_ws_cumul_pb; eauto.
    destruct Hcodom as (_ & scodom & Hcodom & _).
    unshelve eapply (closed_context_conversion _ Hb); pcuic.
    constructor. now apply ws_cumul_ctx_pb_refl. constructor; auto.

  - (* Fixpoint unfolding *)
    assert (args <> []) by (destruct args; simpl in *; congruence).
    symmetry in H3. apply tApp_mkApps_inj in H3 as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H4). rewrite <- Hu in e. rewrite <- e.
    clear e.
    specialize (inversion_mkApps typet) as [T' [appty spty]].
    have vT' := (validity appty).
    eapply type_tFix_inv in appty as [T [arg [fn' [[[Hnth wffix] Hty]]]]]; auto.
    rewrite H in Hnth. noconf Hnth.
    eapply type_App; eauto.
    eapply type_mkApps; [|tea].
    eapply type_ws_cumul_pb; eauto.

  - (* Application congruence for argument *)
    intuition auto.
    eapply type_Cumul_alt; [eapply type_App| |]; eauto with wf.
    eapply validity.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (@red_red _ _ wf _ Γ [vass na A] [] [u] [N2]); eauto.
    erewrite -> on_free_vars_ctx_on_ctx_free_vars.
    eapply on_free_vars_ctx_snoc_ass; tea.
    eapply type_closed in typeu. now eapply closedn_on_free_vars.
    eapply type_closed in typet. cbn in typet; repeat inv_on_free_vars.
    cbn. now eapply closedn_on_free_vars. constructor. apply: red1_red Hu. constructor.
    all:repeat constructor. cbn.
    rewrite -(shiftnP_add 1) addnP_shiftnP. repeat inv_on_free_vars => //.

  - (* Constant unfolding *)
    unshelve epose proof (H' := declared_constant_to_gen H); eauto.
    unshelve epose proof (H0' := declared_constant_to_gen H0); eauto.
    unshelve epose proof (declared_constant_inj decl decl0 _ _); tea; subst decl.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    eapply on_declared_constant in H as (Hb & s & Ht & _); tas; cbn in Hb, Ht.
    rewrite <- (app_context_nil_l Γ).
    apply subject_closed in Hb as clb; tas.
    apply type_closed in Hb as clty; tas.
    replace (subst_instance u body)
      with (lift0 #|Γ| (subst_instance u body)).
    replace (subst_instance u ty)
      with (lift0 #|Γ| (subst_instance u ty)).
    2-3: rewrite -subst_instance_lift lift_closed; cbnr; tas.
    eapply weakening; tea.
    now rewrite app_context_nil_l.
    eapply @typing_subst_instance_decl with (Γ:=[]); tea.

  - (* iota reduction *)
    clear forall_u forall_u0 X X0.
    unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
    destruct X4 as [wfcpc IHcpc].
    eassert (ctx_inst _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as IHctxi.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    hide X8.
    pose proof typec as typec''.
    unfold iota_red.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl [wfl [declc [Hu tyc]]]]]].
    eapply typing_spine_strengthen in tyargs; tea.
    have openargs : forallb (is_open_term Γ) args.
    { repeat inv_on_free_vars; auto. }
    clear tyc.
    2:{ eapply validity. econstructor; tea. }
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
    pose proof (declared_inductive_inj isdecl' (proj1 declc')) as [-> ->].
    destruct typec' as [[[[[_ equ] cu] cu'] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci']]]]].
    destruct ci' as [cparsubst0 iparsubst0 idxsubst0 subsidx [s [typectx [Hpars Hargs]]]].
    pose proof (on_declared_constructor declc) as [[onind oib] [ctor_sorts [hnth onc]]].
    (* pose proof (PCUICContextSubst.context_subst_fun csubst (iparsubst0.(inst_ctx_subst))). subst iparsubst. *)
    unshelve epose proof (constructor_cumulative_indices declc Hu cu' equ _ _ _ _ _ cparsubst0 iparsubst0 Hpars).
    set (argctxu1 := subst_context _ _ _) in X |- *.
    set (argctxu := subst_context _ _ _) in X |- *.
    simpl in X.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in X |- *.
    set (pargctxu := subst_context iparsubst 0 argctxu) in X |- *.
    destruct X as [cumargs convidx]; eauto.
    assert(wfparu : wf_local Σ (subst_instance (puinst p) (ind_params mdecl))).
    { eapply on_minductive_wf_params; eauto.
      destruct isdecl; eauto.  }
    assert (wfps : wf_sort Σ ps).
    { eapply validity in IHp; auto. eapply PCUICWfUniverses.isType_wf_universes in IHp; tea.
      move: IHp => /= /PCUICWfUniverses.wf_sort_reflect //. }
    have lenpars := (wf_predicate_length_pars H0).
    unfold hidebody in X8.
    set (ptm := it_mkLambda_or_LetIn _ _).
    rename c0 into c.
    assert (isType Σ Γ (mkApps ptm (indices ++ [mkApps (tConstruct ci c u) args]))).
    { eapply validity. econstructor; eauto. all :constructor; eauto. apply (All2i_impl X8). intuition auto. }
    eapply All2i_nth_error in X8; tea.
    2:{ destruct declc. simpl in e. exact e. }
    cbn in X8.
    destruct X8 as (bctxeq & (wfcbc & _) & (hb & _) & cbty & _).
    cbn -[case_branch_type_gen] in hb.
    rewrite case_branch_type_fst in hb.
    set (prebrctx := pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
    set (ibrctx := (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)) in *.
    set (brctx := (inst_case_context (pparams p) (puinst p) (bcontext br))).
    assert (wfbr : wf_branch cdecl br).
    { eapply Forall2_All2, All2_nth_error in H4; tea.
      eapply declc. }
    assert(eqctx : eq_context_upto_names ibrctx brctx).
    { rewrite /brctx /ibrctx.
      rewrite /case_branch_context /case_branch_context_gen.
      etransitivity.
      eapply eq_binder_annots_eq.
      eapply wf_pre_case_branch_context_gen; tea.
      unfold pre_case_branch_context_gen.
      rewrite /inst_case_context.
      now eapply alpha_eq_subst_context, alpha_eq_subst_instance. }
    assert (convbrctx' : Σ ⊢ Γ ,,, brctx = Γ ,,, ibrctx).
    { etransitivity; tea.
      eapply ws_cumul_ctx_pb_app; revgoals.
      3:eapply ws_cumul_ctx_pb_refl; eapply wf_local_closed_context; auto.
      split. apply ws_cumul_ctx_pb_refl. pcuic.
      eapply eq_context_alpha_conv => //. now symmetry.
      eapply wf_local_closed_context. eapply typing_wf_local in hb.
      eapply wf_local_alpha; tea. eapply All2_app => //. reflexivity.
      now apply typing_wf_local, wf_local_closed_context in hb.
      rewrite /brctx /ibrctx; len.
      rewrite case_branch_context_length //. }
    assert (convbrctx'' : Σ ⊢ Γ ,,, ibrctx = Γ ,,, prebrctx).
    { rewrite /ibrctx /prebrctx.
      symmetry.
      apply ws_cumul_ctx_pb_rel_app.
      eapply eq_context_alpha_conv.
      eapply pre_case_branch_context_eq; tea.
      eapply wf_local_closed_context. eapply wf_pre_case_branch_context; tea.
      now apply typing_wf_local, wf_local_closed_context in cbty. }
    assert (prewf : wf_local Σ (Γ ,,, prebrctx)).
    { eapply wf_pre_case_branch_context; tea. }
    assert (prewfs : wf_local Σ (Γ ,,, smash_context [] prebrctx)).
    { eapply wf_local_smash_end; tea. }
    assert (wfbrctx' : wf_local Σ (Γ ,,, brctx)).
    { eapply wf_local_alpha. eapply All2_app; tea. eapply All2_refl; reflexivity. assumption. }
    assert (convbrctxsmash : Σ ⊢
        Γ ,,, smash_context [] (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) =
        Γ ,,, smash_context [] brctx).
    { eapply conv_context_smash_end; tea. now symmetry. }
    assert (spbrctx : spine_subst Σ Γ (skipn (ind_npars mdecl) args) (List.rev (skipn (ind_npars mdecl) args))
      (smash_context [] prebrctx)).
    { pose proof (spine_subst_smash idxsubst0).
      eapply spine_subst_cumul in X0. eapply X0. all:tea.
      1-2:apply smash_context_assumption_context; pcuic.
      eapply X0.
      move: cumargs.
      rewrite /pargctxu /argctxu.
      move: iparsubst0.
      rewrite (firstn_app_left).
      now rewrite (wf_predicate_length_pars H0).
      intros iparsubst0.
      clear X5 IHctxi. unshelve epose proof (ctx_inst_spine_subst _ Hctxi).
      eapply weaken_wf_local; tea. exact (on_minductive_wf_params_indices_inst isdecl _ cu').
      rewrite (spine_subst_inst_subst iparsubst0).
      intros cum.
      eapply ws_cumul_ctx_pb_rel_trans; tea.
      apply ws_cumul_ctx_pb_rel_app.
      apply ws_cumul_ctx_pb_refl.
      now apply wf_local_closed_context in prewfs. }
    eapply closed_context_conversion in hb.
    3:{ symmetry. eapply convbrctx'. }
    eapply typing_expand_lets in hb.
    eapply (PCUICSubstitution.substitution (Δ := [])) in hb.
    2:{ eapply (spine_subst_cumul (Γ' := smash_context [] brctx)) in spbrctx; tea.
        eapply spbrctx.
        1-2:apply smash_context_assumption_context; pcuic.
        now apply wf_local_smash_end.
        apply ws_cumul_ctx_pb_rel_smash => //.
        apply ws_cumul_ctx_pb_rel_app. apply ws_cumul_ctx_pb_eq_le. symmetry.
        etransitivity; tea. }
    rewrite subst_context_nil -heq_ind_npars in hb *.
    eapply (type_ws_cumul_pb (pb:=Cumul)). exact hb. 3:auto.
    assumption. clear hb.
    rewrite /case_branch_type.
    set cbtyg := (case_branch_type_gen _ _ _ _ _ _ _ _ _).
    (* Move back to the canonical branch context for the rest of the proof *)
    transitivity (subst0 (List.rev (skipn (ind_npars mdecl) args)) (expand_lets prebrctx cbtyg.2)).
    { eapply ws_cumul_pb_eq_le.
      eapply (substitution_ws_cumul_pb (Γ'' := [])). eapply spbrctx.
      symmetry. apply (ws_cumul_pb_expand_lets_ws_cumul_ctx (pb:=Cumul)); tea.
      eapply wt_cumul_pb_refl.
      rewrite case_branch_type_fst in cbty.
      eapply closed_context_conversion in cbty. exact cbty.
      auto. auto.
      eapply ws_cumul_ctx_pb_rel_app; tea. eapply ws_cumul_ctx_pb_eq_le.
      symmetry. now transitivity (Γ ,,, ibrctx). }
    cbn.
    rewrite lift_mkApps !subst_mkApps.
    pose proof (wf_branch_length wfbr).
    have lenskip: #|skipn (ind_npars mdecl) args| = (context_assumptions (cstr_args cdecl)).
    { rewrite List.length_skipn eqargs; lia. }
    have lenfirst: #|firstn (ind_npars mdecl) args| = (context_assumptions (ind_params mdecl)).
    { rewrite firstn_length_le; try lia. now rewrite -(declared_minductive_ind_npars isdecl). }
    have brctxlen : #|prebrctx| = #|cstr_args cdecl|.
    { now rewrite /prebrctx !lengths. }
    have pparamsl : #|pparams p| = context_assumptions (ind_params mdecl).
    { move: (wf_predicate_length_pars H0).
      now rewrite (declared_minductive_ind_npars isdecl). }

    rewrite simpl_lift; try lia.
    rewrite subst_subst_lift // !(context_assumptions_subst_context, subst_context_length, lengths) //; try lia.
    rewrite map_app /= !map_app. eapply ws_cumul_pb_eq_le.
    have wfparsargs : wf_local Σ
      (subst_instance u (ind_params mdecl),,,
        subst_context (inds (inductive_mind ci) u (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance u (cstr_args cdecl))).
    { exact (on_constructor_wf_args declc Hu). }
    have wfparsargs' : wf_local Σ
      (subst_instance (puinst p) (ind_params mdecl),,,
        subst_context (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance (puinst p) (cstr_args cdecl))).
    { exact (on_constructor_wf_args declc cu'). }
    eapply ws_cumul_pb_mkApps; tea.
    { eapply wt_cumul_pb_refl. eapply type_it_mkLambda_or_LetIn; tea. }
    rewrite firstn_app_left // /= in iparsubst0.
    rewrite firstn_app_left // /= in Hpars.
    rewrite skipn_all_app_eq // in subsidx.
    have brctxass : context_assumptions prebrctx = context_assumptions (cstr_args cdecl).
    { now rewrite /prebrctx !lengths. }
    assert (eqargts : ws_cumul_pb_terms Σ Γ (skipn (ind_npars mdecl) args)
      (skipn (ind_npars mdecl) args)).
    { pose proof (spine_subst_ctx_inst spbrctx).
      apply ctx_inst_open_terms in X0.
      eapply All_All2; tea. cbn; intros.
      apply ws_cumul_pb_refl; tea. }

    eapply All2_app.
    * set(indsub := inds _ _ _).
      relativize (map (subst0 _) _).
      2:{
        rewrite !map_map_compose. apply map_ext => x.
        symmetry.
        rewrite -/(subst_let_expand _ _ _) -/(subst_let_expand_k _ _ _ _).
        rewrite -brctxass -brctxlen -expand_lets_eq.
        rewrite {1 2}/prebrctx {1 2}/pre_case_branch_context {1}subst_context_length.
        rewrite /subst_let_expand_k (expand_lets_subst_comm _ _ _) !lengths.
        relativize (context_assumptions _).
        erewrite <- subst_app_simpl. 2:now rewrite !lengths.
        rewrite subst_app_decomp.
        relativize #|cstr_args cdecl|.
        erewrite subst_let_expand_app.
        2-4:rewrite ?lengths; try lia; reflexivity.
        rewrite /subst_let_expand.
        reflexivity. }
      move: Hargs.
      move: convidx.
      intros cv convidx.
      eapply (ws_cumul_pb_terms_subst (Δ := [])) in cv.
      3:{ exact (spine_subst_smash idxsubst0). }
      3:{ exact (spine_subst_smash idxsubst0). }
      all:tea. 2:{ eapply wf_local_closed_context. eapply wf_local_smash_end; tea. eapply idxsubst0. }
      2:{ eapply All2_rev => //. }
      rewrite subst_context_nil /= in cv. simpl in cv.
      rewrite skipn_all_app_eq // in convidx.

      assert(ws_cumul_pb_terms Σ Γ
        (map
         (fun x : term =>
          subst0 (List.rev args)
            (expand_lets (argctxu1 ++ subst_instance u (ind_params mdecl)) (subst_instance u x)))
          (cstr_indices cdecl)) indices).
      { eapply eq_ws_cumul_pb_terms_trans; tea.
        pose proof (positive_cstr_closed_indices declc).
        eapply All_map_inv in X0.
        eapply All_map_eq, All_impl; tea.
        cbn; intros x.
        intros cl.
        epose proof
          ( @spine_subst_app _ Σ Γ (subst_instance u (ind_params mdecl))
            (subst_context
              (inds (inductive_mind ci) u (ind_bodies mdecl))
               #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))
          (firstn (ind_npars mdecl) args)
          (skipn (ind_npars mdecl) args) (cargsubst ++ cparsubst)) as X3.
        rewrite lenfirst in X3. len in X3.
        specialize (X3 eq_refl).
        forward X3. { rewrite -app_context_assoc. eapply weaken_wf_local; tea. }
        forward X3. {
          rewrite skipn_all_app_eq; len.
          now rewrite -(PCUICContextSubst.context_subst_length idxsubst0); len.
          apply cparsubst0. }
        forward X3. {
          pose proof (PCUICContextSubst.context_subst_length idxsubst0).
          len in H8.
          rewrite firstn_app H8 firstn_all Nat.sub_diag /= app_nil_r skipn_all_app_eq //. }
        rewrite firstn_skipn in X3.
        rewrite (spine_subst_inst_subst_term X3).
        f_equal.
        pose proof (PCUICInductiveInversion.on_constructor_wf_args declc).
        eapply closed_wf_local in X4; tea.
        rewrite !closedn_ctx_app /= in X4 *.
        move/andb_and: X4 => [] /andb_and [] clar clp clargs.
        len in clargs.
        rewrite -(subst_closedn (inds (inductive_mind ci) u (ind_bodies mdecl))
              (context_assumptions (ind_params mdecl ,,, cstr_args cdecl))
              (expand_lets _ _)).
        { rewrite /argctxu1.
          relativize (context_assumptions _).
          eapply (closedn_expand_lets 0).
          rewrite !closedn_ctx_app /=.
          apply andb_true_iff; split.
          rewrite closedn_subst_instance_context.
          eapply (declared_inductive_closed_params isdecl).
          rewrite subst_instance_length.
          eapply (closedn_ctx_subst 0). simpl.
          rewrite /ind_subst inds_length.
          now rewrite closedn_subst_instance_context.
          eapply (declared_minductive_closed_inds isdecl).
          rewrite /= length_app subst_context_length !subst_instance_length.
          rewrite Nat.add_comm in cl.
          eapply (PCUICClosed.closedn_expand_lets) in cl.
          rewrite closedn_subst_instance.
          now rewrite Nat.add_comm.
          rewrite /= !context_assumptions_app /= context_assumptions_subst_context //
            !context_assumptions_subst_instance //. }
        (* rewrite -subst_instance_app_ctx -subst_instance_expand_lets closedn_subst_instance. *)
        relativize (context_assumptions _).
        erewrite <-(expand_lets_subst_comm _ _ _).
        2:{ now rewrite /argctxu1 !context_assumptions_app
              !context_assumptions_subst_context !context_assumptions_subst_instance. }
        f_equal.
        * rewrite subst_context_app closed_ctx_subst.
          rewrite closedn_subst_instance_context.
          now apply (declared_inductive_closed_params isdecl).
          f_equal. len.
          rewrite closed_ctx_subst //.
          rewrite /argctxu1. simpl.
          eapply (closedn_ctx_subst 0). simpl.
          rewrite /ind_subst inds_length closedn_subst_instance_context //.
          eapply (declared_minductive_closed_inds isdecl).
        * now rewrite /argctxu1; len. }
      clear convidx.
      etransitivity; tea.
      eapply (eq_ws_cumul_pb_terms_trans (U:=
       (map (subst0 (List.rev (skipn (ind_npars mdecl) args)))
      (map (subst iparsubst (context_assumptions (cstr_args cdecl)))
         (map (expand_lets argctxu)
            (map (subst_instance (puinst p)) (cstr_indices cdecl))))))).
      2:{
        rewrite !map_map_compose.
        rewrite !map_map_compose in cv.
        eapply All2_map_inv, All2_All in cv.
        eapply All2_map, All_All2; tea.
        cbn; intros x Hx.
        eapply ws_cumul_pb_eq_trans.
        symmetry; tea.
        rewrite (spine_subst_inst_subst_term_k cparsubst0).
        pose proof (subst_let_expand_app).
        relativize (context_assumptions (cstr_args cdecl)).
        erewrite <-subst_app_simpl. 2:now len.
        rewrite -List.rev_app_distr firstn_skipn. len.
        rewrite lenskip expand_lets_app /argctxu1.
        rewrite context_assumptions_subst_context context_assumptions_subst_instance //. }

      (* clear -H4 pparamsl wfbrctx convbrctx cumargs wfcbc wfparsargs Hpars lenskip lenfirst lenpars heq_ind_npars wf cparsubst0 idxsubst0 iparsubst0 isdecl declc. *)
      rewrite /argctxu. simpl.
      rewrite !map_map_compose. apply All_map_eq.
      eapply All_impl.
      exact (All_map_inv _ _ _ (positive_cstr_closed_indices declc)).
      cbn => x.
      rewrite -(closed_ctx_subst indsub 0 (subst_instance _ _ ,,, _)).
      { now eapply closed_wf_local in wfparsargs'. }
      relativize (#|ind_params _| + _).
      erewrite expand_lets_subst_comm; rewrite !lengths.
      2:rewrite !lengths; lia.
      rewrite -context_assumptions_app Nat.add_comm.
      move/(PCUICClosed.closedn_expand_lets) => /=. rewrite /= !lengths => clx.
      rewrite (subst_closedn indsub (_ + _)).
      relativize (_ + _). eapply (closedn_expand_lets 0).
      2-3:rewrite /= !lengths // closedn_subst_instance //.
      eapply closed_wf_local; tea. now rewrite Nat.add_comm.
      rewrite (spine_subst_inst_subst_term_k iparsubst0).
      change (ind_subst _ _ _) with indsub.
      relativize (context_assumptions _).
      erewrite <-subst_app_simpl. 2:now len.
      rewrite List.length_rev lenskip /=.
      relativize (context_assumptions _).
      erewrite <- expand_lets_app => //.
      now rewrite !lengths.

    * rewrite lift_mkApps /= !subst_mkApps /=. constructor. 2:constructor.
      rewrite !map_app.
      rewrite -{3}(firstn_skipn (ind_npars mdecl) args) -brctxlen -brctxass.
      rewrite - !expand_lets_eq_map.
      rewrite -/(expand_lets_k (bcontext br) 0 _).
      relativize (to_extended_list (cstr_args cdecl)).
      erewrite map_expand_lets_to_extended_list.
      2:{ etransitivity.
        2:apply to_extended_list_case_branch_context.
        rewrite /prebrctx.
        eapply conv_context_rel_to_extended_list.
        apply ws_cumul_ctx_pb_rel_app. symmetry. tea.
        now eapply Forall2_All2 in wfbr. }
      rewrite -map_expand_lets_to_extended_list.
      rewrite !map_map_compose.
      rewrite [map (fun x => _) (to_extended_list _)](@map_subst_let_expand_to_extended_list _ Σ _ Γ); tea.
      relativize (map _ _).
      2:{ eapply map_ext => x. rewrite -/(subst_let_expand _ _ _).
          now rewrite subst_let_expand_lift_id //; len. }
      rewrite map_id.
      transitivity (mkApps (tConstruct ci c (puinst p)) args).
      rewrite -(firstn_skipn (ind_npars mdecl) args).
      eapply ws_cumul_pb_mkApps; tea.
      eapply ws_cumul_pb_refl => //.
      eapply All2_app. eapply All2_symP => //. intro; now symmetry.
      rewrite firstn_skipn //.
      rewrite firstn_skipn. constructor => //.
      { rewrite on_free_vars_mkApps /= //. }
      { rewrite on_free_vars_mkApps /= //. }
      eapply eq_term_upto_univ_mkApps.
      2:reflexivity.
      constructor. eapply cmp_global_instance_sym; tc.
      rewrite eqargs.
      now eapply (cmp_global_instance_cstr_irrelevant declc).

  - (* Case congruence: on a cofix, impossible *)
    eapply inversion_mkApps in typec as [? [tcof ?]] =>  //.
    eapply type_tCoFix_inv in tcof as [d [[[Hnth wfcofix] ?] ?]] => //.
    unfold unfold_cofix in H.
    rewrite Hnth in H. noconf H.
    pose proof (validity t0).
    eapply typing_spine_strengthen in t; eauto.
    eapply wf_cofixpoint_typing_spine in t; eauto.
    unfold check_recursivity_kind in t.
    unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
    rewrite isdecl'.p1 in t.
    apply ReflectEq.eqb_eq in t. rewrite t /= in heq_isCoFinite.
    discriminate.

  - (* Case congruence on a parameter *)
    eassert (ctx_inst _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    destruct X0, X4.
    assert (isType Σ Γ (mkApps (it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p)) (indices ++ [c]))).
    { eapply validity. econstructor; eauto. all: econstructor; eauto.
      eapply (All2i_impl X8); intuition auto. }
    set (ptm := it_mkLambda_or_LetIn _ _) in *.
    cbn -[ptm it_mkLambda_or_LetIn] in *.
    have wfparinds : wf_local Σ
      (Γ,,, subst_instance (puinst p) (ind_params mdecl,,, ind_indices idecl)).
    { eapply weaken_wf_local; tea.
      eapply (on_minductive_wf_params_indices_inst isdecl _ H1). }
    have ctxi' : ctx_inst Σ Γ (params' ++ indices)
        (List.rev
           (subst_instance p.(puinst) (ind_params mdecl,,, ind_indices idecl))).
    { eapply OnOne2_prod_inv in X3 as [X3 _].
      eapply OnOne2_app_r in X3.
      unshelve eapply (ctx_inst_merge' _ _ _ _ _ X6 X5); tea. }
    pose proof X5 as X5'.
    unshelve epose proof (ctx_inst_spine_subst _ X5); tea.
    eapply spine_subst_smash in X4; tea.
    eapply ctx_inst_length in X5. len in X5.
    rewrite context_assumptions_rev in X5. len in X5.
    pose proof (wf_predicate_length_pars H0). simpl in H.
    pose proof (declared_minductive_ind_npars isdecl).
    have lenidx : (#|List.rev indices| = (context_assumptions (ind_indices idecl))) by (len; lia).
    rewrite subst_instance_app smash_context_app_expand in X4.
    eapply spine_subst_app_inv in X4 as [sppars spargs]; tea. 2:len.
    len in sppars. len in spargs.
    rewrite List.rev_app_distr in sppars spargs.
    rewrite skipn_app - !lenidx !skipn_all /= Nat.sub_diag skipn_0 in sppars spargs.
    rewrite firstn_app firstn_all Nat.sub_diag /= app_nil_r in spargs.
    rewrite subst_instance_app List.rev_app_distr in X6.
    have lenpars' := (OnOne2_length X3).
    unshelve epose proof (ctx_inst_spine_subst _ ctxi');tea.
    pose proof (spine_codom_wf _ _ _ _ _ X4);tea.
    pose proof (spine_subst_smash X4); tea. all:tea.
    rewrite subst_instance_app smash_context_app_expand in X9.
    eapply spine_subst_app_inv in X9 as [sppars' spargs']; tea.
    2:len. len in sppars'. len in spargs'.
    rewrite List.rev_app_distr in sppars' spargs'.
    rewrite skipn_app - !lenidx !skipn_all /= Nat.sub_diag skipn_0 in sppars' spargs'.
    rewrite firstn_app firstn_all Nat.sub_diag /= app_nil_r in spargs'.
    have wfp' : wf_predicate mdecl idecl (set_pparams p params').
    { move: H0. rewrite /wf_predicate /wf_predicate_gen /=.
      rewrite (OnOne2_length X3). intuition auto. }
    have redpars : red_terms Σ Γ (pparams p) params'.
    { eapply OnOne2_prod_inv in X3 as [cv _].
      clear -cv H H3. inv_on_free_vars.
      cbn in *; repeat inv_on_free_vars. clear b a2 a1 a0.
      induction cv; cbn; constructor; auto using closed_red1_red;
      cbn in *; repeat inv_on_free_vars; auto.
      apply red_terms_refl => //. now apply into_closed_red. }
    have convctx' :
      Σ ⊢ (case_predicate_context ci mdecl idecl p ++ Γ) =
      (case_predicate_context ci mdecl idecl (set_pparams p params') ++ Γ).
    { move: X2 => cv.
      rewrite /case_predicate_context /case_predicate_context_gen.
      eapply ws_cumul_ctx_pb_rel_app.
      eapply conv_ctx_set_binder_name.
      { change (pcontext (set_pparams p params')) with (pcontext p).
        eapply wf_pre_case_predicate_context_gen; tea. }
      { now eapply wf_pre_case_predicate_context_gen. }
      rewrite /pre_case_predicate_context_gen /inst_case_context.
      cbn [pparams puinst set_pparams].
      eapply ws_cumul_ctx_pb_rel_app.
      eapply substitution_ws_cumul_ctx_pb_red_subst.
      3:eapply subslet_untyped_subslet, sppars.
      2:eapply All2_rev => //.
      clear cv.
      rewrite -app_context_assoc. eapply is_closed_context_weaken. fvs.
      rewrite -on_free_vars_ctx_on_ctx_free_vars -closedP_shiftnP_eq
       -closed_ctx_on_ctx_free_vars.
      rewrite closedn_ctx_app !lengths.
      apply/andP; split. 2:cbn -[ind_predicate_context].
      2:rewrite closedn_subst_instance_context. 2:eapply closed_ind_predicate_context; tea.
      2:eapply declared_minductive_closed, isdecl.
      eapply closedn_smash_context.
      now eapply declared_inductive_closed_params_inst. }
    have isty' : isType Σ Γ (mkApps (tInd ci (puinst p)) (params' ++ indices)).
    { eapply has_sort_isType; eapply isType_mkApps_Ind; tea. }
    have wfcpc' : wf_local Σ (Γ ,,, case_predicate_context ci mdecl idecl (set_pparams p params')).
    { eapply wf_case_predicate_context; tea. }
    have eqindices : ws_cumul_pb_terms Σ Γ indices indices.
    { now eapply spine_subst_wt_terms, wt_terms_ws_cumul_pb in spargs'. }
    have typec' : Σ;;; Γ |- c : mkApps (tInd ci (puinst p)) (params' ++ indices).
    { eapply type_ws_cumul_pb; tea.
      eapply ws_cumul_pb_eq_le. eapply ws_cumul_pb_mkApps; pcuic.
      eapply All2_app => //. now apply: red_terms_ws_cumul_pb_terms. }
    set (pctx := (inst_case_predicate_context (set_pparams p params'))) in *.
    pose proof X1 as X9. symmetry in X9. move:X9.
    change (pcontext p) with (pcontext (set_pparams p params')).
    move/(PCUICAlpha.inst_case_predicate_context_eq wfp') => eqctx.
    have wfpctx : wf_local Σ (Γ,,, inst_case_predicate_context (set_pparams p params')).
    { eapply wf_local_alpha; tea; auto.
      eapply All2_app => //. reflexivity. }
    have eqpctx : Σ ⊢ Γ ,,, pctx = Γ ,,, case_predicate_context ci mdecl idecl (set_pparams p params').
    { symmetry.
      rewrite /pctx.
      eapply into_ws_cumul_ctx_pb => //.
      now eapply wf_local_closed_context.
      now eapply wf_local_closed_context.
      eapply upto_names_conv_context.
      eapply eq_context_upto_cat. apply eq_context_upto_refl; tc.
      now apply eq_context_upto_names_eq_context_alpha. }
    epose proof (wf_case_branches_types' (p:=set_pparams p params') ps _ brs isdecl isty' wfp').
    cbv zeta in X9; forward_keep X9.
    { eapply closed_context_conversion; tea. }
    do 2 forward X9 by auto.
    eapply type_ws_cumul_pb; tea.
    { econstructor; tea. all: econstructor; tea.
      (* The branches contexts also depend on the parameters. *)
      apply All2i_nth_hyp in X9.
      eapply All2i_All2i_mix in X8; tea. clear X9.
      eapply (All2i_impl X8); clear X8.
      intros cstr cdecl br. cbv zeta.
      rewrite !case_branch_type_fst.
      do 2 case. move=> hnth [] wfbr wfbctxargs wfbrctx wfcbc' wfcbcty'.
      case => eqbctx. case. case => wfbctx _.
      move=> [] [] Hbody IHbody [] brty IHbrty.
      eapply and_assum. solve_all. move=> cvcbc.
      apply and_assum; [|move=> wfcb'].
      { now eapply typing_wf_local in wfcbcty'. }
      split => //.
      have declc : declared_constructor Σ (ci, cstr) mdecl idecl cdecl.
      { split => //. }
      have convbctx : Σ ⊢ Γ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl =
        Γ,,, case_branch_context ci mdecl (set_pparams p params') (forget_types (bcontext br)) cdecl.
      { rewrite /case_branch_context /case_branch_context_gen.
        eapply ws_cumul_ctx_pb_rel_app.
        eapply conv_ctx_set_binder_name. eapply wf_pre_case_branch_context_gen; tea.
        eapply wf_pre_case_branch_context_gen; tea.
        rewrite /case_branch_context /case_branch_context_gen.
        eapply (substitution_ws_cumul_ctx_pb_subst_conv (Γ' := smash_context [] (ind_params mdecl)@[puinst p]) (Γ'':=[])).
        2:{ eapply All2_rev.
          eapply OnOne2_prod_inv in X3 as [redp _].
          now eapply red_terms_ws_cumul_pb_terms. }
        apply ws_cumul_ctx_pb_rel_app.
        eapply ws_cumul_ctx_pb_refl, wf_local_closed_context.
        rewrite /=. rewrite /cstr_branch_context.
        rewrite subst_instance_expand_lets_ctx.
        eapply wf_local_expand_lets.
        epose proof (on_constructor_inst_wf_args declc (puinst p) H1) as onc.
        rewrite -app_context_assoc; eapply weaken_wf_local; auto.
        rewrite subst_instance_subst_context.
        now rewrite subst_instance_inds (subst_instance_id_mdecl _ _ _ H1).
        eapply subslet_untyped_subslet, sppars. eapply subslet_untyped_subslet, sppars'.
        eapply wf_local_closed_context.
        eapply wf_local_smash_end.
        apply weaken_wf_local => //. eapply on_minductive_wf_params; tea. eapply isdecl. }
      eapply (type_ws_cumul_pb (pb:=Conv)); tea.
      + eapply closed_context_conversion; tea.
      + eapply has_sort_isType with (s := ps). exact wfcbcty'.
      + eapply ws_cumul_pb_mkApps; tea.
        { rewrite /ptm. cbn [preturn set_pparams].
          rewrite !lift_it_mkLambda_or_LetIn.
          eapply ws_cumul_pb_it_mkLambda_or_LetIn.
          relativize #|cstr_args cdecl|.
          eapply weakening_ws_cumul_ctx_pb; tea.
          apply ws_cumul_ctx_pb_refl, wf_local_closed_context => //.
          now apply (case_branch_context_length_args wfbr).
          rewrite !case_predicate_context_length // /= Nat.add_0_r.
          relativize #|pcontext p|. relativize #|cstr_args cdecl|.
          eapply weakening_ws_cumul_pb; tea.
          apply isType_ws_cumul_pb_refl. now eapply has_sort_isType.
          now apply wf_local_closed_context.
          now apply case_branch_context_length_args.
          now rewrite case_predicate_context_length. }
        cbn.
        eapply All2_app.
        - rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context
          /pre_case_branch_context_gen /inst_case_context. cbn.
          symmetry. rewrite /subst_context PCUICRenameConv.map2_set_binder_name_fold ?lengths.
          now apply wf_branch_length.
          rewrite -/(subst_context _ _ _).
          relativize #|cstr_args cdecl|.
          eapply ws_cumul_pb_terms_subst.
          2:eapply subslet_untyped_subslet, sppars'.
          2:eapply subslet_untyped_subslet, sppars.
          { eapply wf_local_closed_context, wf_local_smash_end, weaken_wf_local => //.
            eapply (on_minductive_wf_params isdecl) => //. }
          { apply All2_rev; symmetry. now apply red_terms_ws_cumul_pb_terms. }
          { epose proof (on_constructor_closed_indices_inst declc (u:=puinst p) H1).
            eapply ws_cumul_pb_terms_refl.
            { rewrite /cstr_branch_context.
              apply wf_local_closed_context.
              move: wfbrctx.
              move/wf_local_expand_lets. cbn.
              rewrite subst_instance_expand_lets_ctx map2_set_binder_name_expand_lets ?lengths //.
              apply (wf_branch_length wfbr).
              rewrite subst_instance_subst_context instantiate_inds //.
              eapply declc. }
            rewrite 2!forallb_map.
            eapply All_map_inv in X8. eapply All_forallb, All_impl; tea.
            cbn; intros x clx.
            apply closedn_on_free_vars.
            rewrite -on_free_vars_closedn in clx.
            len. rewrite !map2_length !lengths.
            now apply wf_branch_length. rewrite lengths in clx.
            rewrite (wf_branch_length wfbr).
            rewrite (Nat.add_comm _ #|Γ|) Nat.add_assoc (Nat.add_comm _ #|Γ|).
            rewrite -(context_assumptions_subst_instance (puinst p)) closedn_expand_lets_eq.
            eapply closedn_ctx_upwards. eapply (declared_inductive_closed_params_inst declc). lia.
            len. rewrite (Nat.add_comm #|ind_params mdecl|).
            eapply closed_upwards; tea. len. }
          pose proof (wf_branch_length wfbr).
          now rewrite map2_length !lengths.
        - apply All2_tip, ws_cumul_pb_mkApps; [apply into_ws_cumul_pb => //; try reflexivity|].
          now eapply wf_local_closed_context.
          eapply All2_app. eapply All2_map.
          eapply OnOne2_prod_inv in X3 as [X3 _].
          eapply red_terms_ws_cumul_pb_terms in redpars.
          eapply All2_impl; tea. intros.
          relativize #|cstr_args cdecl|; [eapply (weakening_ws_cumul_pb (Γ' := []))|] => //.
          now eapply wf_local_closed_context.
          now eapply case_branch_context_length_args.
          eapply ws_cumul_pb_terms_refl. now apply wf_local_closed_context.
          eapply forallb_impl. 2:eapply closedn_to_extended_list.
          intros. rewrite !lengths. rewrite case_branch_context_length_args //.
          eapply closedn_on_free_vars, closed_upwards; tea. lia. }
    + rewrite /ptm.
      eapply ws_cumul_pb_mkApps.
      { eapply ws_cumul_pb_it_mkLambda_or_LetIn => //.
        now symmetry. cbn [preturn set_pparams].
        eapply wt_cumul_pb_refl; eauto. }
      eapply All2_app; eauto. apply All2_tip.
      now eapply wt_cumul_pb_refl.

  - (* Case congruence on the return clause context *)
    clear IHHu. destruct X0, X4 as [].
    eassert (ctx_inst _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    set (ptm := it_mkLambda_or_LetIn _ _).
    assert (isType Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validity. econstructor; eauto. econstructor; eauto.
      split; eauto.
      apply (All2i_impl X8). intuition auto. }
    assert (closed_red1 Σ (Γ,,, case_predicate_context ci mdecl idecl p)
      (preturn p) preturn').
    { eapply closed_red1_eq_context_upto_names; tea.
      rewrite PCUICCasesContexts.inst_case_predicate_context_eq => //.
      reflexivity. }
    eapply type_ws_cumul_pb; tea.
    * eapply type_Case; eauto. constructor; eauto. constructor; eauto.
      epose proof (wf_case_branches_types' (p:=set_preturn p preturn') ps _ brs isdecl (validity typec) H0
        (forall_u _ X3) H4 X1).
      eapply All2i_All2_mix_left in X8. 2:exact (Forall2_All2 _ _ H4). clear H4.
      eapply (All2i_All2i_mix X4) in X8. clear X4.
      eapply (All2i_impl X8); intuition auto; clear X8.
      rewrite !case_branch_type_fst in a3 a4 *.
      set (cbty' := case_branch_type _ _ _ _ _ _ _ _) in *.
      set (cbty := case_branch_type _ _ _ _ _ _ _ _) in b0.
      have btyred : Σ ;;; Γ,,, cbty.1 ⊢ cbty.2 ⇝1 cbty'.2.
      { rewrite /cbty /cbty'.
        apply: closed_red1_case_branch_type => //.
        eapply subject_closed in a4. now apply closedn_on_free_vars.
        now eapply wf_local_closed_context.
        now apply closed_red1_it_mkLambda_or_LetIn. }
      destruct a1 as [wfparctx wfparctx' wfcbc wfcbty].
      split => //. split => //.
      eapply type_ws_cumul_pb; tea.
      now eapply has_sort_isType.
      eapply (ws_cumul_pb_ws_cumul_ctx (pb':=Cumul)); tea.
      2:eapply closed_red1_ws_cumul_pb, btyred.
      now apply ws_cumul_ctx_pb_refl, wf_local_closed_context.
    * eapply ws_cumul_pb_eq_le, ws_cumul_pb_mkApps; tea.
      2:{ eapply ws_cumul_pb_terms_refl => //.
          eapply isType_open in X0.
          rewrite on_free_vars_mkApps in X0.
          now move/andP: X0=> []. }
      eapply ws_cumul_pb_it_mkLambda_or_LetIn; tea.
      now eapply ws_cumul_ctx_pb_refl, wf_local_closed_context.
      cbn [preturn set_preturn].
      symmetry; apply closed_red1_ws_cumul_pb => //.

  - (* Case congruence on discriminee *)
    destruct X0, X4.
    eassert (ctx_inst _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    set (ptm := it_mkLambda_or_LetIn _ _).
    assert (isType Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validity. econstructor; eauto. econstructor; eauto.
      constructor; eauto.
      apply (All2i_impl X8). intuition auto. }
    eapply type_ws_cumul_pb. eapply type_Case; eauto. 1: econstructor; eauto.
    1:econstructor; eauto.
    * solve_all.
    * tas.
    * eapply ws_cumul_pb_eq_le, ws_cumul_pb_mkApps; tea.
      eapply wt_cumul_pb_refl. eapply type_it_mkLambda_or_LetIn; tea.
      apply into_ws_cumul_pb_terms.
      + eapply All2_app. apply All2_refl. reflexivity.
        apply All2_tip. eapply (cumulAlgo_cumulSpec _ (pb:=Conv)).
        symmetry. now eapply closed_red1_ws_cumul_pb.
      + now apply wf_local_closed_context.
      + eapply isType_open in X0.
        rewrite on_free_vars_mkApps in X0.
        move/andP: X0=> []. generalize (closed_red1_open_right Hu).
        rewrite !forallb_app /= => clc' clptm /and3P[] -> /=.
        now rewrite clc'.
      + eapply isType_open in X0. rewrite on_free_vars_mkApps in X0.
        now move/andP: X0 => [].

  - (* Case congruence on branches *)
    destruct X0, X4.
    eassert (ctx_inst _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    eapply type_Case; eauto. econstructor; eauto.
    econstructor; eauto.
    * eapply Forall2_All2 in H4.
      move: (All2_sym _ _ _ H4) => wfb.
      red. eapply All2_Forall2.
      apply All2_sym.
      eapply (OnOne2_All2_All2 X3 wfb); auto.
      intros [] []; simpl. intros.
      destruct X0 as [_ eq]. subst bcontext0. exact H5.
    * apply Forall2_All2 in H4. eapply All2i_All2_mix_left in X8; tea.
      eapply (OnOne2_All2i_All2i X3 X8).
      intros n [] []; simpl. intros. intuition auto.
      intros n [ctx b] [ctx' b'] cdecl; cbn.
      rewrite !case_branch_type_fst.
      intros [red <-].
      move=> [] wfbr [] convctx [] [] wfcbc IHcbc [] [] Hb IHb [] Hbty IHbty.
      intuition auto. clear b0.
      eapply IHb. eapply closed_red1_eq_context_upto_names; tea.
      eapply All2_app.
      2:reflexivity. etransitivity.
      2:eapply pre_case_branch_context_eq; cbn; tea.
      apply inst_case_branch_context_eq => //. apply isdecl.

  - (* Proj CoFix reduction *)
    assert(typecofix : Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args0) : subst0 (mkApps (tCoFix mfix idx) args0 :: List.rev args)
      (subst_instance u pdecl.(proj_type))).
    { econstructor; eauto. }
    inv_on_free_vars.
    generalize typec.
    move/inversion_mkApps => [ty [tcof tsp]]; auto.
    move/type_tCoFix_inv: (tcof) => [d [[[Hnth wfcofix] Hbody] Hcum]]; auto.
    rewrite /unfold_cofix Hnth in H; noconf H.
    simpl in *.
    generalize typec.
    move/validity/(isType_mkApps_Ind_proj_inv _ isdecl) => [sppars hargs hinds cu].
    have lenargs : #|args| = context_assumptions (ind_params mdecl).
    { move: (subslet_length sppars); now len. }
    eapply type_Cumul_alt; [econstructor|..]; eauto.
    + eapply typing_spine_strengthen in tsp. 3:tea.
      eapply type_mkApps. eauto. eauto.
      now eapply validity in Hbody.
    + now eapply validity in typecofix.
    + eapply conv_cumul.
      rewrite (subst_app_simpl [mkApps (subst0 (cofix_subst mfix) (dbody d)) args0]) (subst_app_simpl [mkApps (tCoFix mfix idx) args0]).
      eapply conv_sym, PCUICCumulativity.red_conv.
      destruct (on_declared_projection isdecl) as [[oi hctors] onp].
      eassert (projsubs := subslet_projs (args := args) isdecl).
      set (oib := declared_inductive_inv _ _ _ _) in *. simpl in onp, projsubs.
      rewrite hctors in projsubs.
      destruct onp as [[[tyargctx onps] Hp2] onp].
      destruct (ind_cunivs oib) as [|? []] eqn:hcunivs; try rewrite hcunivs // in tyargctx.
      specialize (projsubs onps).
      epose proof (declared_projection_type_and_eq wf isdecl) as [[hctors' hty] [decl'' [Hdecl Hty wfdecl peq peq']]].
      red in onp.
      unfold projection_type, projection_type' in *.
      set (indsubst := inds _ _ _) in *.
      set (projsubst := projs _ _ _) in *.
      set (indb := vass _ _) in *.
      rewrite -peq peq'. cbn.
      rewrite subst_instance_subst.
      rewrite (distr_subst_rec _ _ _ 1 0) /=.
      rewrite [_@[u]]subst_instance_projs.
      rewrite projs_subst_above //.
      rewrite !distr_subst !subst_projs_inst /=.
      rewrite projs_length Nat.add_0_r.
      rewrite !subst_instance_subst.
      rewrite -(Nat.add_1_r p.(proj_arg)) subst_instance_lift.
      rewrite -commut_lift_subst_rec // -(commut_lift_subst_rec _ _ 1 p.(proj_arg)) //.
      rewrite !simpl_subst_k //.
      specialize (projsubs _ _ _ typec).

      eapply (closed_red_red_subst0 (Γ := Γ)
        (Δ := skipn (context_assumptions (cstr_args cdecl) - p.(proj_arg))
          (subst_context (List.rev args) 0
          (subst_context (extended_subst (ind_params mdecl)@[u] 0) 0 (smash_context []
          (subst_context (inds (inductive_mind p.(proj_ind)) u (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))))))); auto.
      ** eapply wf_local_closed_context.
          eapply All_local_env_app_skipn.
          apply wf_subslet_ctx in projsubs.
          apply projsubs.
      ** elim: p.(proj_arg). simpl. constructor.
        intros n Hn. constructor; auto.
        eapply closed_red1_red.
        split. fvs. cbn. rewrite on_free_vars_mkApps.
        apply/andP; split; fvs.
        eapply red_cofix_proj.
        unfold unfold_cofix. rewrite Hnth. reflexivity.

      ** rewrite -subst_projs_inst.
        have: (p.(proj_arg) = context_assumptions (cstr_args cdecl) -
           (context_assumptions (cstr_args cdecl) - p.(proj_arg))) by lia.
        move=> {1}->. rewrite -skipn_projs map_skipn subst_projs_inst.
        eapply untyped_subslet_skipn. destruct p as [[[? ?] ?] ?]. simpl in *.
        rewrite /indsubst.
        eapply subslet_untyped_subslet.
        eapply projsubs.

      ** move: Hty.
        move/(isType_subst_instance_decl _ _ _ _ (InductiveDecl mdecl) u _ _).
        unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
        move/(_ _ isdecl'.p1.p1.p1 cu).
        rewrite !subst_instance_app_ctx -app_context_assoc.
        move/(isType_subst_arities isdecl cu).
        rewrite subst_context_app.
        rewrite closed_k_ctx_subst //.
        eapply (declared_inductive_closed_params_inst isdecl).
        move/isType_subst_extended_subst.
        move/(isType_weaken wfΓ); rewrite app_context_assoc.
        move/(isType_subst_gen _ sppars).
        rewrite -skipn_subst_instance - !skipn_subst_context.
        rewrite -(subst_context_smash_context _ _ []).
        rewrite subst_instance_smash /=.
        len.
        rewrite length_skipn; len.
        assert (context_assumptions (cstr_args cdecl) -
            (context_assumptions (cstr_args cdecl) - p.(proj_arg)) = p.(proj_arg)) by lia.
        rewrite H.
        move/isType_open. len.
        rewrite !length_skipn; len. rewrite H //.
        rewrite subst_instance_subst // /indsubst.
        rewrite subst_instance_inds.
        rewrite (subst_instance_id_mdecl _ _ _ cu) //.
        rewrite subst_instance_extended_subst //.

  - (* Proj Constructor reduction *)
    pose proof (validity typec).
    simpl in typec.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    pose proof typec' as typec''.
    destruct (declared_projection_declared_constructor isdecl declc) as [? []]. subst mdecl' idecl' cdecl'.
    epose proof (declared_projection_type_and_eq wf isdecl).
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    destruct (on_declared_constructor declc) as [[onmind oin] [cs [Hnth onc]]].
    simpl in typec'. simpl in X2.
    eassert (projsubsl := subslet_projs (args := map (lift0 #|ind_params mdecl|) args) isdecl).
    set(oib := declared_inductive_inv _ wf wf _) in *.
    pose proof (onProjections oib) as onProjs. clearbody oib.
    destruct (isdecl) as [_ [hnth _]].
    destruct (ind_projs idecl).
    eapply nth_error_Some_length in hnth. simpl in hnth.
    lia.
    simpl in *.
    move: (proj2 declc).
    destruct ind_ctors as [|? []] => //. intros [= ->].
    destruct X2 as [[_ projty] projeq].
    destruct typec' as [[[[[_ equ] _] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as [cparsubst0 iparsubst0 idxsubst0 subsidx [s [typectx [Hpars Hargs]]]].
    destruct ind_cunivs as [|? ?] => //; noconf Hnth.
    specialize (projsubsl onProjs).
    have noidx := (on_projections_indices onProjs).
    destruct onProjs.
    eapply nth_error_alli in on_projs; eauto.
    2:eapply isdecl. simpl in on_projs.
    epose proof (declared_constructor_valid_ty _ _ _ _ _ 0 cdecl _ wf wfΓ declc Hu) as Hty.
    eapply typing_spine_strengthen in tyargs; tea.
    rewrite -(firstn_skipn (ind_npars mdecl) args0) in tyargs, H |- *.
    assert(#|firstn (ind_npars mdecl) args0| = ind_npars mdecl).
    rewrite firstn_length_le. lia. lia.
    rewrite nth_error_app_ge in H. rewrite H2.
    pose proof (onNpars onmind).
    pose proof (proj2 (proj2 isdecl)). simpl in *. lia.
    rewrite H2 in H. destruct (proj2 isdecl). simpl in H4.
    destruct p as [pind pnpars parg]. cbn in *. subst pnpars.
    replace (ind_npars mdecl + parg - ind_npars mdecl) with parg in H by lia.
    unfold type_of_constructor in tyargs, Hty.
    rewrite onc.(cstr_eq) in tyargs, Hty.
    rewrite !subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn in tyargs, Hty.
    eapply typing_spine_inv in tyargs as [arg_sub [spargs sp]]; eauto.
    2:{ rewrite !context_assumptions_fold.
        rewrite context_assumptions_subst_instance. rewrite H2.
        apply onNpars in onmind. lia. }
    rewrite closed_ctx_subst in spargs.
    { eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto.
      destruct declc as [[] ?]; eauto. }
    pose proof (spine_subst_inj_subst spargs cparsubst0). subst arg_sub.
    clear Hty.
    rewrite subst_it_mkProd_or_LetIn in sp.
    rewrite !subst_instance_mkApps !subst_mkApps in sp.
    eapply typing_spine_nth_error in sp; eauto.
    2:{ rewrite !context_assumptions_fold. rewrite context_assumptions_subst_instance.
        clear sp. eapply nth_error_Some_length in H.
        rewrite List.length_skipn in H. lia. }
    destruct sp as [decl [Hnth Hu0]].
    simpl in on_projs. red in on_projs. len in Hnth.
    eapply (type_ws_cumul_pb (pb:=Cumul)); eauto.
    { rewrite firstn_skipn.
      unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
      eapply (isType_subst_instance_decl _ _ _ _ _ u wf isdecl'.p1.p1.p1) in projty; eauto.
      apply lift_sorting_f_it_impl with (tu := projty) => // Hs.
      rewrite /= /map_decl /= in Hs.
      eapply (weaken_ctx Γ) in Hs; auto.
      rewrite (subst_app_simpl [_]).
      destruct projeq as [decl' [hnthargs hty wf' projeq1 projty']].
      eapply (substitution0 (T := tSort _)).
      eapply (PCUICSubstitution.substitution (Γ' := subst_instance u (smash_context [] (ind_params mdecl)))
        (Δ := [vass _ _]) (T := tSort _)); eauto.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_smash.
      eapply iparsubst0. exact Hs. simpl.
      rewrite subst_instance_mkApps subst_mkApps /=.
      rewrite [subst_instance_instance _ _](subst_instance_id_mdecl Σ) // subst_instance_to_extended_list.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_smash /=.
      rewrite /to_extended_list (spine_subst_subst_to_extended_list_k iparsubst0).
      assumption. }
    rewrite firstn_skipn.
    rewrite smash_context_app smash_context_acc in on_projs.
    rewrite nth_error_app_lt in on_projs.
    { autorewrite with len. simpl.
      eapply nth_error_Some_length in Hnth. autorewrite with len in Hnth.
      now simpl in Hnth. }
    rewrite nth_error_subst_context in on_projs.
    epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))) as dnth.
    autorewrite with len in dnth. simpl in dnth.
    erewrite -> dnth in on_projs. clear dnth.
    unshelve epose proof (constructor_cumulative_indices declc Hu cu equ _ _ _ _ _ spargs iparsubst0 Hpars).
    move: X2.
    set (argsu1 := subst_instance u0 (cstr_args cdecl)) in *.
    set (argsu := subst_instance u (cstr_args cdecl)) in *.
    set (argctxu1 := subst_context _ _ argsu1) in *.
    set (argctxu := subst_context _ _ argsu) in *.
    simpl.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in *.
    set (pargctxu := subst_context iparsubst 0 argctxu) in *.
    move=> [cumargs _]; eauto.
    destruct cumargs as [clargs cumargs].
    eapply PCUICRedTypeIrrelevance.All2_fold_nth_ass in cumargs.
    3:eapply smash_context_assumption_context; constructor.
    2:{ unfold pargctxu1, argctxu1, argsu1.
        autorewrite with len in Hnth. eapply Hnth. }
    destruct cumargs as [decl' [Hdecl' cum]].
    rewrite !(smash_context_subst []) in Hnth.
    rewrite -(subst_instance_smash u0 _ []) !nth_error_subst_context nth_error_map in Hnth.
    destruct projeq as [decl'' [Hdecl Hty wfdecl Hty1 Hty2]].
    rewrite Hdecl /= in on_projs, Hnth.
    destruct on_projs as [declna decltyeq declrel].
    noconf Hnth. simpl in *.
    move: Hu0; len.
    assert (parg < context_assumptions (cstr_args cdecl)).
    eapply nth_error_Some_length in H3. lia.
    replace (context_assumptions (cstr_args cdecl) -
      S (context_assumptions (cstr_args cdecl) - S parg))
      with parg by lia.
    move=> Hu0. rewrite -Hty1 Hty2. clear decltyeq.
    unfold projection_type'.
    set (indsubst1 := inds _ _ _).
    (* set (indsubst := ind_subst _ _ _). *)
    set (projsubst := projs _ _ _).
    rewrite !subst_instance_subst subst_instance_lift !subst_instance_subst.
    epose proof (commut_lift_subst_rec _ _ 1 parg parg ltac:(reflexivity)) as hnarg.
    rewrite Nat.add_1_r in hnarg. rewrite <- hnarg => //. clear hnarg.
    rewrite (subst_app_decomp [_]) !lengths heq_length /= lift_mkApps /=.
    rewrite (distr_subst [_]) /= !lengths.
    rewrite simpl_subst_k // [subst_instance _ projsubst]subst_instance_projs.
    epose proof (subst_app_simpl (List.rev (firstn parg (skipn (ind_npars mdecl) args0))) _ 0) as hs.
    rewrite !lengths /= in hs.
    assert(#|firstn parg (skipn (ind_npars mdecl) args0)| = parg) as hnarg.
    { rewrite firstn_length_le // length_skipn; lia. }
    rewrite hnarg in hs. rewrite <- hs. clear hs. rewrite subst_app_decomp.
    epose proof (subst_app_simpl
      (map (subst0 [mkApps (tConstruct pind 0 u0) (map (lift0 (ind_npars mdecl)) args0)])
        (projs pind (ind_npars mdecl) parg))) as hs.
    rewrite !lengths in hs.
    rewrite -{}hs subst_app_decomp !lengths (distr_subst (List.rev args)) !lengths.
    assert (map (subst0 (List.rev args)) (subst_instance u (extended_subst (ind_params mdecl) 0)) =
      iparsubst) as ->.
    { rewrite firstn_all2 in iparsubst0. lia.
      rewrite subst_instance_extended_subst.
      pose proof (inst_ctx_subst iparsubst0).
      eapply context_subst_extended_subst in X2.
      rewrite X2. eapply map_ext.
      intros. now rewrite subst_inst Upn_0. }
    len in cum. simpl in cum.
    move: Hdecl'.
    rewrite /pargctxu /argctxu /argsu !smash_context_subst_empty -(subst_instance_smash _ _ []).
    rewrite !nth_error_subst_context nth_error_map Hdecl. simpl => [= Hdecl'].
    subst decl'. simpl in cum.
    len in cum; simpl in cum.
    assert(context_assumptions (cstr_args cdecl) -
      S (context_assumptions (cstr_args cdecl) - S parg) = parg) by lia.
    rewrite H5 in cum.
    set (idx := S (context_assumptions (cstr_args cdecl) - S parg)) in *.
    assert (wfpargctxu1 : wf_local Σ (Γ ,,, skipn idx (smash_context [] pargctxu1))).
    { simpl. apply All_local_env_app_skipn. apply wf_local_smash_end; auto.
      apply idxsubst0. }
    destruct cum as [[cr mapd] cumdecls].
    destruct decl'' as [na [b|] ty]; simpl in mapd; try discriminate.
    depelim cumdecls. cbn in *. rename eqt into cum.
    eapply (substitution_ws_cumul_pb (Γ' := skipn idx (smash_context [] pargctxu1)) (Γ'' := [])
      (s := skipn idx (List.rev (skipn (ind_npars mdecl) args0)))) in cum.
    2:{ eapply spine_subst_smash in idxsubst0; eauto.
        eapply subslet_skipn, idxsubst0. }
    assert (skipn idx (List.rev (skipn (ind_npars mdecl) args0)) = (List.rev (firstn parg (skipn (ind_npars mdecl) args0)))) as eq.
    { rewrite /idx skipn_rev. lia_f_equal. rewrite length_skipn; lia. }
    assert (parg = #|List.rev (firstn parg (skipn (ind_npars mdecl) args0))|) as hnarg'.
    { rewrite !lengths firstn_length_le ?length_skipn; lia. }
    rewrite eq in cum.
    rewrite subst_context_nil in cum. simpl in cum.
    rewrite -(subst_app_simpl' _ _ 0) in cum => //.
    rewrite subst_app_decomp in cum.
    etransitivity; [eapply cum|clear cum].
    rewrite -(subst_app_simpl' _ _ 0) //.
    rewrite subst_app_decomp.
    rewrite (subslet_length iparsubst0); len.
    assert (wf_local Σ (Γ ,,, subst_instance u (ind_params mdecl))).
    { eapply weaken_wf_local; eauto. eapply on_minductive_wf_params => //. pcuic.
      apply declc. }
    eapply (substitution_ws_cumul_pb (Γ'' := [])); eauto. eapply iparsubst0.
    simpl.
    rewrite (distr_subst_rec _ _ _ #|ind_params mdecl| 0); len => /=.
    rewrite /indsubst1 subst_instance_inds.
    rewrite (subst_instance_id_mdecl Σ u mdecl) //.
    rewrite (subst_closedn (List.rev args)).
    { eapply (closedn_subst _ 0).
      eapply declared_minductive_closed_inds; eauto. exact isdecl.
      simpl; len.
      rewrite closedn_subst_instance.
      clear projsubsl.
      eapply closed_wf_local in wfdecl.
      rewrite closedn_ctx_app in wfdecl.
      move/andb_and: wfdecl => [_ wfdecl]. len in wfdecl.
      simpl in wfdecl.
      eapply closedn_ctx_decl in wfdecl; eauto.
      len in wfdecl.
      simpl in wfdecl.
      eapply closed_upwards. eauto.
      lia. auto. }
    assert (ind_npars mdecl = #|List.rev args|) as eqargs'. len.
    rewrite map_map_compose map_subst_lift0_subst -(map_map_compose _ _ _ (subst0 _)).
    rewrite subst_projs_inst projs_inst_subst subst_mkApps /=.
    rewrite {3}eqargs' map_map_compose map_subst_lift_id.
    eapply (weakening _ _ ((ind_params mdecl)@[u])) in typec'' => //.
    rewrite !lift_mkApps in typec''. len in typec''.
    eapply (substitution_ws_cumul_pb_subst_conv (Γ := _ ,,, _) (Δ := [])); auto.
    { rewrite -(subst_instance_length u).
      eapply subslet_lift; eauto. rewrite -eq.
      eapply spine_subst_smash in idxsubst0; eauto.
      eapply subslet_skipn. eapply idxsubst0. }
    { specialize (projsubsl (Γ ,,, subst_instance u (ind_params mdecl))).
      rewrite -projs_inst_lift.
      rewrite -{1}H5 -projs_inst_skipn.
      specialize (projsubsl (lift0 #|ind_params mdecl| (mkApps (tConstruct pind 0 u0) args0)) u).
      forward projsubsl.
      rewrite lift_mkApps //.
      eapply wf_subslet_skipn, projsubsl. }
    { eapply All2_map.
      eapply All2_from_nth_error.
      { autorewrite with len. lia. }
      intros n x x' Hn nth nth'.
      rewrite nth_error_projs_inst in nth'.
      lia. noconf nth'.
      rewrite /= lift_mkApps /=.
      symmetry. eapply red_conv.
      eapply closed_red1_red.
      eapply wt_closed_red1.
      { eapply nth_error_Some_length in H3.
        have: parg - S n < #|ind_projs idecl| by lia.
        clear hnth.
        move/nth_error_Some' => [pdecl' hnth].
       eexists. econstructor; tea. split; [eapply isdecl|]. cbn. split => //. tea. len. }
      constructor.
      eapply (f_equal (option_map (lift0 #|ind_params mdecl|))) in nth.
      simpl in nth. rewrite -nth nth_error_map. f_equal.
      rewrite nth_error_rev_inv; autorewrite with len; try lia.
      rewrite hnarg.
      rewrite firstn_skipn_comm nth_error_skipn.
      rewrite -{1}[args0](firstn_skipn (ind_npars mdecl + parg)).
      rewrite nth_error_app1 // firstn_length_le; autorewrite with len; try lia. cbn. lia. }
    { simpl. autorewrite with len.
      rewrite -(subst_instance_length u (ind_params mdecl)).
      simpl. eapply ws_cumul_pb_refl.
      rewrite -skipn_lift_context.
      eapply wf_local_closed_context.
      eapply All_local_env_app_skipn.
      eapply weakening_wf_local => //.
      eapply wf_local_smash_end, idxsubst0.
      move: Hty.
      unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
      move/(isType_subst_instance_decl _ _ _ _ (InductiveDecl mdecl) u _ _).
      rewrite !subst_instance_app_ctx -app_context_assoc.
      intro foo. pose (fun x y z => isType_subst_arities isdecl cu (foo x y z)).
      move:i. clear foo.
      intro foo. pose (fun x y z => isType_open (foo x y z)).
      move:i. clear foo. len.
      rewrite length_skipn; len.
      assert (context_assumptions (cstr_args cdecl) -
          (context_assumptions (cstr_args cdecl) - parg) = parg) by lia.
      cbn. rewrite H6.
      rewrite length_skipn; len. rewrite H5. intro foo.
      eapply on_free_vars_impl; [| eapply foo]; eauto.
      move=> i'. rewrite /shiftnP !orb_false_r.
      move/Nat.ltb_lt => lt. apply/Nat.ltb_lt. lia. }

  - (* Proj congruence: discriminee reduction *)
    eapply type_ws_cumul_pb; [econstructor|..]; eauto.
    eapply validity; eauto.
    instantiate (1:= tProj p c).
    econstructor; eauto.
    eapply ws_cumul_pb_eq_le.
    rewrite (subst_app_simpl [c']) (subst_app_simpl [c]).
    set(bann := {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |}).
    eapply (untyped_substitution_ws_cumul_pb_subst_conv (Γ := Γ)
      (Γ' := []) (Δ := [vass bann (mkApps (tInd p.(proj_ind) u) args)])
      (Δ' := [vass bann (mkApps (tInd p.(proj_ind) u) args)])); auto.
    4-5:repeat constructor.
    * symmetry. apply red_terms_ws_cumul_pb_terms; constructor; auto.
      now apply closed_red1_red.
    * rewrite on_free_vars_ctx_app andb_true_r on_free_vars_ctx_app H /=.
      cbn. rewrite shiftnP_add /=.
      move/validity/isType_open: typec => -> //.
    * rewrite on_free_vars_ctx_app andb_true_r on_free_vars_ctx_app H /=.
      cbn. rewrite shiftnP_add /=.
      move/validity/isType_open: typec => -> //.
    * have := (declared_projection_type_and_eq wf isdecl).
      move=> [[hctors isTy] Hdecl].
      move/validity/(isType_mkApps_Ind_proj_inv _ isdecl): typec => [sppars hpars hargs cu].
      move/(isType_subst_instance_decl _ _ _ _ (InductiveDecl mdecl) u _ _) : isTy.
      unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
      move/(_ _ isdecl'.p1.p1.p1 cu).
      move/(isType_weaken wfΓ).
      rewrite [_@[u]](subst_instance_app_ctx _ _ [_]).
      rewrite app_context_assoc subst_instance_smash.
      move/(isType_substitution sppars) => /=. len.
      move/isType_open => /=. now cbn.

  - (* Fix congruence *)
    apply mkApps_Fix_spec in H5. simpl in H5. subst args.
    simpl. destruct narg; discriminate.

  - (* Fix congruence: type reduction *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : conv_context cumulAlgo_gen Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf wfΓ X X4 H2 fixl.
      eapply All2_fold_app => //.
      apply conv_ctx_refl. clear X.
      eapply All2_fold_impl.
      eapply (conv_decls_fix_context (Γ := Γ)) => //.
      move: H2.
      assert (clΓ := wf_local_closed_context wfΓ).
      clear fixl. move: #|mfix|. induction X4; constructor.
      * destruct p as [[r p] e]. noconf e. split.
        now apply closed_red1_ws_cumul_pb. rewrite H. reflexivity.
      * cbn in H2. move/andP: H2 => [_ Htl].
        eapply forallb_All in Htl. eapply All_All2; tea.
        move=> [dname dty dbod] /= h. rewrite /test_def /=;
        move/andP=> [hty _]. split; try reflexivity.
        eapply ws_cumul_pb_refl => //.
      * move/andP: H2 => [/andP [Hty _] _].
        split; try reflexivity. apply ws_cumul_pb_refl => //.
      * eapply IHX4. simpl in H2; now move/andP: H2 => [].
      * cbn. intros ???? []; constructor; eauto; now apply ws_cumul_pb_forget_conv. }
    assert (All (on_def_type (lift_typing typing Σ) Γ) mfix1).
    { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        apply lift_sorting_it_impl_gen with HT' => //; now intros [_ IH]. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_alt.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
      apply (OnOne2_All_All X4 X3).
      + intros d Hj.
        unfold on_def_body. rewrite -fixl.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT IHT.
        eapply context_conversion; eauto.
      + move=> [na ty b rarg] [na' ty' b' rarg'] [[[red Hred] eq] HT] HB.
        rewrite /= in red, Hred, eq, HB, HT.
        noconf eq.
        destruct HB as ((Hb & IHb) & s & (Ht & IHt) & e); cbn in *.
        eassert (Σ ;;; Γ ,,, _ |- lift0 _ ty' : tSort s).
        2: repeat (eexists; cbn).
        2,3: eapply context_conversion; eauto.
        all: rewrite -fixl.
        { eapply IHt. eapply @weakening_closed_red1 with (Γ' := []); eauto. now eapply wf_local_closed_context. }
        eapply type_Cumul_alt. eapply Hb.
        eapply has_sort_isType. rewrite fixl. eassumption.
        apply red_cumul, red1_red.
        eapply (weakening_red1 _ []); auto.
        2:eapply red.
        pose proof (Hs := HT.2.π2.1.1).
        eapply subject_closed in Hs.
        eapply (closedn_on_free_vars (P:=xpredT)) in Hs.
        now eapply on_free_vars_any_xpredT.

    * eapply wf_fixpoint_red1_type; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply All_nth_error in X0; eauto.
    * apply conv_cumul, conv_sym. destruct disj as [<-|[[red Hred] eq]] => //.
      reflexivity. eapply PCUICCumulativity.red_conv.
      apply red1_red, red.

  - (* Fix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf X4.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction X4.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n'; f_equal. apply IHX4. }
    assert (All (on_def_type (lift_typing typing Σ) Γ) mfix1).
    { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        noconf eq. unfold on_def_type in HT' |- *. rewrite -H4.
        apply lift_typing_impl with (1 := HT'); now intros ?? []. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_alt.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      apply fix_red_body; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
       apply (OnOne2_All_All X4 X3).
      + intros d Hj.
        rewrite -convctx.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT //.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[[red IH] eq] HT] HB.
        noconf eq.
        rewrite -convctx.
        apply lift_sorting_it_impl_gen with HB => //= [] [Ht IHt] //. eauto.
    * eapply wf_fixpoint_red1_body; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply All_nth_error in X0; eauto.
    * apply conv_cumul, conv_sym. destruct disj as [<-|[_ eq]].
      reflexivity. noconf eq. rewrite H4; reflexivity.

  - (* CoFix congruence: type reduction *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : conv_context cumulAlgo_gen Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf wfΓ X X4 H2 fixl.
      eapply All2_fold_app => //; trea.
      clear X. eapply All2_fold_impl.
      eapply (conv_decls_fix_context (Γ := Γ)) => //.
      move: H2.
      assert (clΓ := wf_local_closed_context wfΓ).
      clear fixl. move: #|mfix|. induction X4; constructor.
      * destruct p as [[r p] e]. noconf e. split.
        now apply closed_red1_ws_cumul_pb. rewrite H. reflexivity.
      * cbn in H2. move/andP: H2 => [_ Htl].
        eapply forallb_All in Htl. eapply All_All2; tea.
        move=> [dname dty dbod] /= h. rewrite /test_def /=;
        move/andP=> [hty _]. split; try reflexivity.
        eapply ws_cumul_pb_refl => //.
      * move/andP: H2 => [/andP [Hty _] _].
        split; try reflexivity. apply ws_cumul_pb_refl => //.
      * eapply IHX4. simpl in H2; now move/andP: H2 => [].
      * cbn. intros ???? []; constructor; eauto; now apply ws_cumul_pb_forget_conv. }
    assert (All (on_def_type (lift_typing typing Σ) Γ) mfix1).
      { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        apply lift_sorting_it_impl_gen with HT' => //. now intros [_ IH]. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_alt.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
      apply (OnOne2_All_All X4 X3).
      + intros d Hj.
        unfold on_def_body. rewrite -fixl.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT IHT.
        eapply context_conversion; eauto.
      + move=> [na ty b rarg] [na' ty' b' rarg'] [[[red Hred] eq] HT] HB.
        rewrite /= in red, Hred, eq, HB, HT.
        noconf eq.
        destruct HB as ((Hb & IHb) & s & (Ht & IHt) & e); cbn in *.
        eassert (Σ ;;; Γ ,,, _ |- lift0 _ ty' : tSort s).
        2: repeat (eexists; cbn).
        2,3: eapply context_conversion; eauto.
        all: rewrite -fixl.
        { eapply IHt. eapply @weakening_closed_red1 with (Γ' := []); eauto. now eapply wf_local_closed_context. }
        eapply type_Cumul_alt. eapply Hb.
        eapply has_sort_isType. rewrite fixl. eassumption.
        apply red_cumul, red1_red.
        eapply (weakening_red1 _ []); auto.
        2:eapply red.
        pose proof (Hs := HT.2.π2.1.1).
        eapply subject_closed in Hs.
        eapply (closedn_on_free_vars (P:=xpredT)) in Hs.
        now eapply on_free_vars_any_xpredT.

    * eapply (wf_cofixpoint_red1_type _ Γ); eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto;
      now eapply closed_red1_red.
    * eapply All_nth_error in X0; eauto.
    * apply conv_cumul, conv_sym. destruct disj as [<-|[[red Hred] eq]] => //.
      reflexivity. eapply PCUICCumulativity.red_conv.
      apply red1_red, red.

  - (* CoFix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf X4.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction X4.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n'; f_equal. apply IHX4. }
    assert (All (on_def_type (lift_typing typing Σ) Γ) mfix1).
    { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        noconf eq. unfold on_def_type in HT' |- *. rewrite -H4.
        apply lift_typing_impl with (1 := HT'); now intros ?? []. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_alt.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0); eauto.
      apply cofix_red_body; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
       apply (OnOne2_All_All X4 X3).
       + intros d Hj.
        rewrite -convctx.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT //.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[[red IH] eq] HT] HB.
        noconf eq.
        rewrite -convctx.
        apply lift_sorting_it_impl_gen with HB => //= [] [Ht IHt] //. eauto.
    * eapply wf_cofixpoint_red1_body; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply All_nth_error in X0; eauto.
    * apply conv_cumul, conv_sym. destruct disj as [<-|[_ eq]].
      reflexivity. noconf eq. rewrite H4; reflexivity.

  - eapply OnOne2_prod_inv in X2 as [X2 _].
    destruct X. depelim X0. depelim X1.
    Transparent prim_type.
    eapply (type_Prim _ _ (primArray; primArrayModel (set_array_value arr value))); tea.
    constructor; cbn; eauto.
    solve_all.
    eapply OnOne2_All_All; tea; cbn; intuition eauto.

  - destruct X. depelim X0. depelim X1.
    Transparent prim_type.
    eapply (type_Prim _ _ (primArray; primArrayModel (set_array_default arr def))); tea.
    constructor; cbn; eauto.

  - pose proof (type_Prim _ _ _ _ _ wfΓ heq_primitive_constant H0 H1 X0). eapply validity in X3.
    destruct X. depelim X0. depelim X1.
    eapply (type_ws_cumul_pb (pb:=Conv)); tea.
    eapply (type_Prim _ _ (primArray; primArrayModel (set_array_type arr ty))); tea.
    constructor; cbn; eauto.
    * eapply type_ws_cumul_pb; tea. eapply has_sort_isType; eauto.
      now eapply (red_ws_cumul_pb (pb:=Conv)), closed_red1_red.
    * solve_all.
      eapply type_ws_cumul_pb; tea. eapply has_sort_isType; eauto.
      now eapply (red_ws_cumul_pb (pb:=Conv)), closed_red1_red.
    * simp prim_type. eapply ws_cumul_pb_App.
      eapply ws_cumul_pb_refl; fvs. cbn.
      now symmetry; eapply red_ws_cumul_pb, closed_red1_red.

  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; tea.
Qed.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Lemma typing_closed_red1 {cf:checker_flags} {Σ : global_env_ext} {Γ t u T} {wfΣ : wf Σ} :
   Σ ;;; Γ |- t : T ->
   red1 Σ Γ t u ->
   Σ ;;; Γ ⊢ t ⇝1 u.
Proof.
  intros Ht hr. split; auto.
  * now apply typing_wf_local, wf_local_closed_context in Ht.
  * now eapply subject_is_open_term.
Qed.

Lemma typing_closed_red {cf:checker_flags} {Σ : global_env_ext} {Γ t u T} {wfΣ : wf Σ} :
   Σ ;;; Γ |- t : T ->
   red Σ Γ t u ->
   Σ ;;; Γ ⊢ t ⇝ u.
Proof.
  intros Ht hr. split; auto.
  * now apply typing_wf_local, wf_local_closed_context in Ht.
  * now eapply subject_is_open_term.
Qed.

Lemma subject_reduction1 {cf Σ} {wfΣ : wf Σ} {Γ t u T}
  : Σ ;;; Γ |- t : T -> red1 Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply (env_prop_typing sr_red1); tea.
  now eapply typing_closed_red1.
Defined.

Theorem subject_reduction {cf:checker_flags} :
  forall (Σ : global_env_ext) Γ t u T, wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred; eauto.
  eapply (env_prop_typing sr_red1); eauto.
  now eapply typing_closed_red1.
Qed.

Corollary subject_reduction1_closed {cf:checker_flags} :
  forall (Σ : global_env_ext) Γ t u T, wf Σ ->
  Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ t ⇝1 u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  now eapply (env_prop_typing sr_red1).
Qed.

Corollary subject_reduction_closed {cf:checker_flags} :
  forall (Σ : global_env_ext) Γ t u T, wf Σ ->
  Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  eapply subject_reduction; tea. apply Hred.
Qed.

Lemma type_reduction {cf} {Σ} {wfΣ : wf Σ} {Γ t A B} :
  Σ ;;; Γ |- t : A -> red Σ Γ A B -> Σ ;;; Γ |- t : B.
Proof.
  intros Ht Hr.
  eapply type_Cumul_alt. eassumption.
  apply lift_sorting_it_impl_gen with (validity Ht) => // HA.
  eapply subject_reduction; eassumption.
  eapply conv_cumul. now apply PCUICCumulativity.red_conv.
Defined.

Lemma type_reduction_closed {cf} {Σ} {wfΣ : wf Σ} {Γ t A B} :
  Σ ;;; Γ |- t : A -> Σ ;;; Γ ⊢ A ⇝ B -> Σ ;;; Γ |- t : B.
Proof.
  intros Ht Hr. eapply type_reduction; tea. exact Hr.
Defined.

Section SRContext.
  Context {cf:checker_flags}.

  Hint Constructors OnOne2_local_env : aa.
  Hint Unfold red1_ctx : aa.

  Lemma red1_ctx_app (Σ : global_env) Γ Γ' Δ :
    red1_ctx Σ Γ Γ' ->
    red1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof using Type.
    induction Δ. trivial.
    intro H. simpl. constructor. now apply IHΔ.
  Qed.

  Lemma red1_red_ctx (Σ : global_env_ext) Γ Γ' :
    red1_ctx Σ Γ Γ' ->
    red_ctx Σ Γ Γ'.
  Proof using Type.
    induction 1; cbn in *.
    - constructor; try reflexivity.
      destruct p; subst.
      constructor. cbn; eauto using red1_red.
    - constructor; try reflexivity.
      destruct p as [-> [[? []]|[? []]]]; constructor; cbn; eauto using red1_red.
    - constructor; auto. reflexivity.
  Qed.

  Definition closed_red1_ctx Σ :=
    OnOne2_local_env
      (fun (Δ : context) => on_one_decl (fun (t t' : term) => closed_red1 Σ Δ t t')).

  Notation "Σ ⊢ Γ ⇝1 Δ" := (closed_red1_ctx Σ Γ Δ) (at level 50, Γ, Δ at next level,
    format "Σ  ⊢  Γ  ⇝1  Δ") : pcuic.

  Lemma wf_local_isType_nth {Σ} {wfΣ : wf Σ} Γ n decl :
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |- lift0 (S n) (decl_type decl) : tSort s.
  Proof using Type.
    intros wfΓ Hnth.
    eapply All_local_env_nth_error in wfΓ as H; tea.
    apply nth_error_Some_length in Hnth.
    destruct H as (_ & s & Hs & _).
    eapply weakening with (Γ' := firstn (S n) Γ) in Hs; cbn in Hs; eauto.
    2: rewrite /app_context firstn_skipn //.
    rewrite firstn_length_le // /app_context firstn_skipn in Hs.
    now eexists.
  Qed.

  Ltac invs H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H.

  Lemma subject_reduction_ctx {Σ} {wfΣ : wf Σ} Γ Γ' t T :
    red1_ctx Σ Γ Γ' ->
    Σ ;;; Γ |- t : T -> Σ ;;; Γ' |- t : T.
  Proof using Type.
    assert(OnOne2_local_env
      (fun (Δ : context) => on_one_decl
         (fun (t t' : term) => red1 Σ.1 Δ t t')) Γ Γ' ->
         conv_context cumulAlgo_gen Σ Γ Γ').
    { clear. induction 1.
      - destruct p as [<- r]. constructor; auto.
        apply conv_ctx_refl. constructor. reflexivity.
        now apply PCUICCumulativity.red_conv, red1_red.
      - destruct p; subst. constructor.
        apply conv_ctx_refl.
        destruct s as [[red ->]|[red ->]].
        constructor; pcuics.
        now apply PCUICCumulativity.red_conv, red1_red.
        constructor. pcuic. now apply PCUICCumulativity.red_conv, red1_red.
        reflexivity.
      - constructor; auto. reflexivity. }
    intros r H.
    specialize (X r).
    assert(wf_local Σ Γ').
    apply typing_wf_local in H.
    induction H in Γ', r, X |-  *; depelim r.
    - constructor; auto. cbn in o.
      destruct o as [<- r].
      apply lift_sorting_it_impl_gen with t1 => // Hs.
      eapply subject_reduction1 in Hs; eauto.
    - depelim X.
      constructor; auto.
      apply lift_sorting_it_impl_gen with t1 => // Hs.
      eapply context_conversion; eauto.
    - depelim X.
      destruct o as [<- [[r ->]|[r <-]]].
      all: constructor; auto.
      all: apply lift_sorting_it_impl_gen with t1 => // Hs.
      + eapply type_reduction; tea. pcuic.
      + eapply subject_reduction1; eauto.
      + eapply subject_reduction1; eauto.
    - depelim X.
      constructor; auto.
      apply lift_sorting_it_impl_gen with t1 => // Hs.
      all: eapply context_conversion; eauto.
    - eapply context_conversion; eauto.
  Qed.

  Lemma wf_local_red1 {Σ} {wfΣ : wf Σ} {Γ Γ'} :
    red1_ctx Σ Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof using Type.
    induction 1; cbn in *.
    - destruct p as [-> r]. intro e. inversion e; subst; cbn in *.
      constructor; tas.
      apply lift_sorting_it_impl_gen with X0 => // Hs.
      eapply subject_reduction1; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [-> [[? []]|[? []]]]; constructor; cbn; tas.
      all: apply lift_sorting_it_impl_gen with X0 => // Hs.
      + eapply type_reduction; tea. pcuic.
      + eapply subject_reduction1; tea.
      + eapply subject_reduction1; tea.
    - intro H; inversion H; subst; constructor; cbn in *; auto.
      all: apply lift_sorting_it_impl_gen with X1 => // Hs.
      all: eapply subject_reduction_ctx; tea.
  Qed.

  Lemma red_ctx_clos_rt_red1_ctx Σ : Relation_Properties.inclusion (red_ctx Σ)
      (clos_refl_trans (red1_ctx Σ)).
  Proof using cf.
    intros x y H.
    induction H; try firstorder.
    destruct p.
    - transitivity (Γ ,, vass na t').
      eapply clos_rt_OnOne2_local_env_incl. constructor.
      cbn. split; auto.
      clear r H.
      induction IHAll2_fold; try solve[repeat constructor; auto].
      etransitivity; eauto.
    - transitivity (Γ ,, vdef na b t').
      * eapply clos_rt_OnOne2_local_env_incl. constructor 2.
        cbn. split; auto.
      * transitivity (Γ ,, vdef na b' t').
        + eapply clos_rt_OnOne2_local_env_incl.
          constructor 2. cbn. split; auto.
        + clear -IHAll2_fold.
          induction IHAll2_fold; try solve[repeat constructor; auto].
          etransitivity; eauto.
  Qed.

  Lemma wf_local_red {Σ} {wfΣ : wf Σ} {Γ Γ'} :
    red_ctx Σ Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof using Type.
    intros h. red in h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1.
  Qed.

  Lemma eq_context_upto_names_upto_names Γ Δ :
    eq_context_upto_names Γ Δ -> Γ ≡Γ Δ.
  Proof using Type.
    induction 1; cbnr; try constructor; eauto.
    depelim r; constructor; subst; auto.
    all:cbnr; eauto.
  Qed.

  Lemma wf_local_subst1 {Σ} {wfΣ : wf Σ} Γ na b t Γ' :
      wf_local Σ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local Σ (Γ ,,, subst_context [b] 0 Γ').
  Proof using Type.
    induction Γ' as [|d Γ']; [now inversion 1|].
    change (d :: Γ') with (Γ' ,, d).
    destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *.
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app_l in X. inversion X; subst; cbn in *; now eapply unlift_TermTyp.
      }
      constructor; cbn; auto.
      apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
      eapply PCUICSubstitution.substitution; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *.
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app_l in X. inversion X; subst; cbn in *; now eapply unlift_TermTyp. }
      constructor; cbn; auto.
      apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
      eapply PCUICSubstitution.substitution; tea.
  Qed.


  Lemma red_ctx_app_context_l {Σ Γ Γ' Δ}
    : red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof using Type.
    induction Δ as [|[na [bd|] ty] Δ]; [trivial| |];
      intro H; simpl; constructor; cbn; try constructor; eauto; now apply IHΔ.
  Qed.

  Lemma isType_red1 {Σ : global_env_ext} {wfΣ : wf Σ} {Γ A B} :
     isType Σ Γ A ->
     red1 Σ Γ A B ->
     isType Σ Γ B.
   Proof using Type.
     intros HT red.
     apply lift_sorting_it_impl_gen with HT => // Hs.
     eapply subject_reduction1; eauto.
   Qed.

   Lemma isWfArity_red1 {Σ} {wfΣ : wf Σ} {Γ A B} :
     isWfArity Σ Γ A ->
     red1 Σ Γ A B ->
     isWfArity Σ Γ B.
   Proof using Type.
     intros [isty H] re.
     split. eapply isType_red1; eauto.
     clear isty; revert H.
     induction re using red1_ind_all.
     all: intros [ctx [s H1]]; cbn in *; try discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         [|rewrite ee in H1; discriminate].
       pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
       rewrite ee in H. eexists _, s'. eassumption.
     - rewrite destArity_tFix in H1; discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHre. { eexists _, s'; tea. }
       destruct IHre as [ctx'' [s'' ee']].
       eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHre. { eexists _, s'; tea. }
       destruct IHre as [ctx'' [s'' ee']].
       eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
   Qed.

   Lemma isWfArity_red {Σ} {wfΣ : wf Σ} {Γ A B} :
     isWfArity Σ Γ A ->
     red Σ Γ A B ->
     isWfArity Σ Γ B.
   Proof using Type.
     induction 2 using red_rect'.
     - easy.
     - now eapply isWfArity_red1.
   Qed.

   Lemma isType_red {Σ} {wfΣ : wf Σ} {Γ T U} :
    isType Σ Γ T -> red Σ Γ T U -> isType Σ Γ U.
   Proof using Type.
     intros HT red; apply lift_sorting_it_impl_gen with HT => // Hs.
     eapply subject_reduction; eauto.
   Qed.

End SRContext.

Lemma isType_tLetIn {cf} {Σ} {HΣ' : wf Σ} {Γ} {na t A B}
  : isType Σ Γ (tLetIn na t A B)
    <~> (lift_typing typing Σ Γ (j_vdef na t A) × isType Σ (Γ,, vdef na t A) B).
Proof.
  split; intro HH.
  - destruct HH as (_ & s & H & _).
    apply inversion_LetIn in H as (A' & HtA & HB & H); tas.
    split; tas.
    apply ws_cumul_pb_Sort_r_inv in H as [s' [H H']].
    eapply has_sort_isType.
    eapply type_reduction; tea.
    apply invert_red_letin in H as [[? [? [? [H ? ? ?]]]]|H]; tas.
    * discriminate.
    * etransitivity.
      + exact (@red_rel_all _ (Γ ,, vdef na t A) 0 t A' eq_refl).
      + eapply (weakening_red_0 (Γ' := [_]) (N := tSort _)); tea; [reflexivity|..].
        erewrite -> on_free_vars_ctx_on_ctx_free_vars. apply H.
        apply H. apply H.
  - destruct HH as (HtA & HB).
    apply lift_sorting_f_it_impl with HB => // Hs.
    eapply type_reduction; tas.
    * econstructor; tea.
    * apply red1_red.
      apply red_zeta with (b':=tSort _).
Defined.

(** Keep at the end to not disturb asynchronous proof processing *)
(* Print Assumptions sr_red1. *)
