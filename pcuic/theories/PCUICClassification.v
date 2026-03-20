(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion PCUICViews
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity.

Local Existing Instance config.extraction_checker_flags.

From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation_Properties.

Set Default Proof Using "Type*".

Lemma negb_False (p : bool) : negb p -> p -> False.
Proof.
intros n pos. rewrite pos in n => //.
Qed.

(* Arities*)

Lemma isArity_subst:
  forall x2 : term, forall s n, isArity x2 -> isArity (subst s n x2).
Proof.
  induction x2; cbn in *; try tauto; intros; eauto.
Qed.

Lemma isArity_typing_spine {cf:checker_flags} {Σ : global_env_ext} {Γ L T T'} {wfΣ : wf Σ} :
  wf_local Σ Γ ->
  typing_spine Σ Γ T' L T ->
  Is_conv_to_Arity Σ Γ T' ->
  Is_conv_to_Arity Σ Γ T.
Proof.
  intros wfΓ sp isc.
  depind sp.
  - destruct isc as (? & ? & ?). sq.
    eapply red_ws_cumul_pb_inv in H.
    eapply (ws_cumul_pb_trans _ _ _ H) in w; tea.
    eapply PCUICConversion.invert_cumul_arity_l in w; eauto.
  - eapply IHsp.
    destruct isc as (? & ? & ?). sq.
    eapply red_ws_cumul_pb_inv in H.
    eapply (ws_cumul_pb_trans _ _ _ H) in w; tea.
    eapply invert_cumul_arity_l in w; eauto.
    destruct w as (? & H1 & H2). sq.
    eapply invert_red_prod in H1 as (? & ? & []); eauto; subst.
    exists (x2 {0 := hd}). split; sq.
    eapply (closed_red_untyped_substitution0 (Δ := [_])); eauto. econstructor. econstructor.
    cbn; fvs.
    now eapply isArity_subst.
Qed.

Ltac destruct_sigma H :=
  repeat match type of H with
  | @sigT _ (fun x => _) => let v := fresh x in
    destruct H as (v & H); simpl in H
  | (_ × _)%type => destruct H as (? & H); simpl in H
  end.

Lemma closedn_mkApps k f args : closedn k (mkApps f args) = closedn k f && forallb (closedn k) args.
Proof.
  induction args using rev_ind; simpl => //.
  - now rewrite andb_true_r.
  - now rewrite mkApps_app /= IHargs forallb_app andb_assoc /= andb_true_r.
Qed.


Section Arities.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Lemma invert_cumul_arity_l_gen (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ ;;; Γ ⊢ C ≤ T -> Is_conv_to_Arity Σ Γ T.
  Proof.
    intros [ar [red isA]]. sq.
    intros cum.
    have: Σ ;;; Γ ⊢ ar ≤ T.
    { eapply ws_cumul_pb_red_l_inv; tea. exact red. }
    now eapply invert_cumul_arity_l.
  Qed.

  Lemma invert_cumul_arity_r_gen (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ;;; Γ ⊢ T ≤ C -> Is_conv_to_Arity Σ Γ T.
  Proof.
    intros [ar [red isA]]. sq.
    intros cum.
    have: Σ ;;; Γ ⊢ T ≤ ar.
    { eapply ws_cumul_pb_red_r_inv; tea. exact red. }
    now eapply invert_cumul_arity_r.
  Qed.

  Lemma isArity_ind ind i args : isArity (mkApps (tInd ind i) args) -> False.
  Proof. destruct args using rev_case; rewrite ?mkApps_app; auto. Qed.

  Lemma Is_conv_to_Arity_ind Γ ind i args : Is_conv_to_Arity Σ Γ (mkApps (tInd ind i) args) -> False.
  Proof.
    intros [ar [red eq]]. sq.
    eapply invert_red_mkApps_tInd in red as (? & []); auto. subst ar.
    now eapply isArity_ind in eq.
  Qed.

  Lemma typing_spine_arity_mkApps_Ind Γ T l i u args :
    wf_local Σ Γ ->
    PCUICArities.typing_spine Σ Γ T l (mkApps (tInd i u) args) ->
    Is_conv_to_Arity Σ Γ T -> False.
  Proof.
    intros wf sp isc.
    eapply (isArity_typing_spine wf sp) in isc.
    now eapply Is_conv_to_Arity_ind.
  Qed.

End Arities.

Section Spines.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext}.
  Context (wfΣ : wf Σ.1).

  Lemma wf_fixpoint_inv mfix idx decl :
    wf_fixpoint Σ mfix ->
    nth_error mfix idx = Some decl ->
    ∑ mind, (check_one_fix decl = Some mind)  *
      check_recursivity_kind (lookup_env Σ) mind Finite.
  Proof.
    rewrite /wf_fixpoint => wffix nthe.
    unfold wf_fixpoint_gen in *.
    move: wffix; case E: (map_option_out (map check_one_fix mfix)) => [l|] //.
    apply map_option_Some in E.
    eapply All2_map_left' in E.
    eapply All2_nth_error_Some in E; eauto.
    destruct E as [kn [Hl Hcheck]].
    destruct l as [|hd tl].
    now rewrite nth_error_nil in Hl => //.
    move/and3P=> [hmfix eqhd checkrec].
    exists kn. split; auto.
    enough (hd = kn) as -> => //.
    clear -Hl eqhd.
    eapply forallb_All in eqhd.
    destruct idx; simpl in Hl; [congruence|].
    eapply All_nth_error in eqhd; eauto.
    now eapply ReflectEq.eqb_eq in eqhd.
    rewrite andb_false_r => //.
  Qed.

  Lemma wf_cofixpoint_inv mfix idx decl :
    wf_cofixpoint Σ mfix ->
    nth_error mfix idx = Some decl ->
    ∑ mind, (check_one_cofix decl = Some mind)  *
      check_recursivity_kind (lookup_env Σ) mind CoFinite.
  Proof.
    rewrite /wf_cofixpoint => wffix nthe.
    unfold wf_cofixpoint_gen in *.
    move: wffix; case E: (map_option_out (map check_one_cofix mfix)) => [l|] //.
    apply map_option_Some in E.
    eapply All2_map_left' in E.
    eapply All2_nth_error_Some in E; eauto.
    destruct E as [kn [Hl Hcheck]].
    destruct l as [|hd tl].
    now rewrite nth_error_nil in Hl => //.
    move/andP=> [eqhd checkrec].
    exists kn. split; auto.
    enough (hd = kn) as -> => //.
    clear -Hl eqhd.
    eapply forallb_All in eqhd.
    destruct idx; simpl in Hl; [congruence|].
    eapply All_nth_error in eqhd; eauto.
    now eapply ReflectEq.eqb_eq in eqhd.
  Qed.

    Lemma on_free_vars_it_mkLambda_or_LetIn {P Δ t} :
      on_free_vars P (it_mkProd_or_LetIn Δ t) =
      on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
  Proof.
    move: P. induction Δ using rev_ind => P.
    - cbn. now rewrite shiftnP0.
    - destruct x as [na [b|] ty]; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
        /on_free_vars_decl /test_decl /=. ring.
      rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
      /on_free_vars_decl /test_decl /=. ring.
  Qed.

  Lemma red_it_mkProd_or_LetIn_smash Γ Δ T :
    is_closed_context Γ ->
    is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
    Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ T ⇝ it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T).
  Proof.
    intros clΓ clt.
    eapply into_closed_red => //.
    induction Δ in Γ, T |- * using ctx_length_rev_ind; simpl; auto.
    - rewrite expand_lets_nil. reflexivity.
    - rewrite smash_context_app_expand /=.
      destruct d as [na [b|] ty].
      * rewrite expand_lets_vdef {1}it_mkProd_or_LetIn_app /= subst_context_nil app_context_nil_l.
        rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil.
        rewrite /expand_lets_ctx /expand_lets_k_ctx /= subst_empty lift0_id lift0_context.
        rewrite /mkProd_or_LetIn /=.
        etransitivity.
        + eapply red1_red, red_zeta.
        + rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
          now eapply X; len.
      * rewrite expand_lets_vass it_mkProd_or_LetIn_app /=.
        rewrite it_mkProd_or_LetIn_app /=.
        eapply red_prod. reflexivity.
        rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil.
        rewrite expand_lets_ctx_assumption_context. repeat constructor.
        now eapply X.
  Qed.

  Lemma cumul_it_mkProd_or_LetIn_smash Γ Δ T :
    is_closed_context Γ ->
    is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
    Σ ;;; Γ ⊢ it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T) = it_mkProd_or_LetIn Δ T.
  Proof.
    intros clΓ clp. symmetry. eapply red_ws_cumul_pb.
    now apply red_it_mkProd_or_LetIn_smash.
  Qed.

  Lemma typing_spine_smash Γ Δ T args T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    typing_spine Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T)) args T'.
  Proof.
    intros sp.
    have ty := (typing_spine_isType_dom sp).
    have r := (red_it_mkProd_or_LetIn_smash Γ Δ T).
    specialize (r (wf_local_closed_context (isType_wf_local ty)) (isType_is_open_term ty)).
    eapply typing_spine_strengthen; tea.
    eapply isType_red; tea. eapply r.
    eapply ws_cumul_pb_eq_le; symmetry.
    now eapply red_ws_cumul_pb.
  Qed.

Lemma assumption_context_assumptions {Γ} :
  assumption_context Γ ->
  context_assumptions Γ = #|Γ|.
Proof.
  induction 1; cbn; auto. congruence.
Qed.


  Lemma typing_spine_nth_error Γ Δ T args T' n arg decl :
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = Some arg ->
    nth_error (List.rev Δ) n = Some decl ->
    Σ ;;; Γ |- arg : subst (List.rev (firstn n args)) 0 decl.(decl_type).
  Proof.
    intros ass wf sp hnth hdecl.
    eapply typing_spine_nth_error in sp; tea.
    2:{ eapply nth_error_Some_length in hdecl. len in hdecl.
        move: (context_assumptions_bound Δ).
        pose proof (assumption_context_assumptions ass). lia. }
    destruct sp as [decl' [hdecl' harg]].
    pose proof (nth_error_Some_length hdecl).
    rewrite (smash_assumption_context _ ass) in hdecl'.
    rewrite nth_error_rev // List.rev_involutive in hdecl.
    len in hdecl. rewrite (assumption_context_assumptions ass) in hdecl'.
    rewrite hdecl in hdecl'. noconf hdecl'. exact harg.
  Qed.

  Lemma typing_spine_all_inv Γ Δ T args T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    #|args| = context_assumptions Δ ->
    (Σ ;;; Γ ⊢ subst (List.rev args) 0 (expand_lets Δ T) ≤ T') * (isType Σ Γ T').
  Proof.
    induction Δ in args, T |- * using ctx_length_rev_ind.
    - simpl. destruct args => // sp _ /=; rewrite subst_empty expand_lets_nil.
      now depelim sp.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_inv in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp).
        forward X by now len.
        now rewrite expand_lets_vdef.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => hargs. simpl in hargs.
        rewrite Nat.add_1_r in hargs. destruct args => //.
        depelim sp. noconf hargs.
        eapply ws_cumul_pb_Prod_Prod_inv in w as [eqna dom codom].
        rewrite expand_lets_vass. simpl.
        eapply (substitution0_ws_cumul_pb (t:=t)) in codom; eauto.
        eapply typing_spine_strengthen in sp. 3:tea.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [t] 0 Γ0) ltac:(len; reflexivity) (subst [t] #|Γ0| T) _ sp).
        forward X by now len.
        rewrite subst_app_simpl /=; len; rewrite H.
        now rewrite -(expand_lets_subst_comm _ _ _).
        eapply isType_apply in i; tea.
        eapply (type_ws_cumul_pb (pb:=Conv)); tea. 2:now symmetry.
        eapply isTypeRel_isType.
        now eapply isType_tProd in i as [].
  Qed.

  Lemma typing_spine_more_inv Γ Δ ind u args args' T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
    #|args'| > context_assumptions Δ -> False.
  Proof.
    induction Δ in args, args' |- * using ctx_length_rev_ind.
    - simpl. destruct args' using rev_case => /= // sp hargs // /=; try lia.
      depelim sp. eapply (f_equal (@length _)) in H; simpl in H; len in H; simpl in H.
      now eapply invert_cumul_ind_prod in w.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_inv in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp). now len.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => /= hargs.
        rewrite Nat.add_1_r in hargs. destruct args'; simpl in * => //. lia.
        depelim sp.
        eapply ws_cumul_pb_Prod_Prod_inv in w as [eqna dom codom]; pcuic.
        eapply (substitution0_ws_cumul_pb (t:=t)) in codom; eauto.
        eapply typing_spine_strengthen in sp. 3:tea.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [t] 0 Γ0) ltac:(len; reflexivity) _ _ sp).
        now len.
        eapply isType_apply in i; tea.
        eapply (type_ws_cumul_pb (pb:=Conv)); tea. 2:now symmetry.
        eapply isTypeRel_isType.
        now eapply isType_tProd in i as [].
  Qed.

  Lemma firstn_subst_context (Γ : context) n k s :
    assumption_context Γ ->
    firstn (#|Γ| - n) (subst_context s k Γ) =
    subst_context s (k + n) (firstn (#|Γ| - n) Γ).
  Proof.
    induction Γ in n, k |-  * using ctx_length_rev_ind; simpl; auto.
    destruct d as [na [b|] ty]; simpl; len; simpl; auto;
    rewrite subst_context_app /=.
    intros ass. eapply assumption_context_app in ass as [_ ass]. depelim ass.
    intros ass. eapply assumption_context_app in ass as [ass _].
    destruct n.
    rewrite Nat.sub_0_r.
    rewrite !firstn_all2;
     rewrite ?length_app ?app_context_length ?subst_context_length ?Nat.add_0_r /=; simpl; try lia.
    now rewrite subst_context_app.
    replace (#|Γ| + 1 - S n) with (#|Γ| - n) by lia.
    rewrite /app_context !firstn_app ?subst_context_length /= Nat.sub_0_r.
    replace (#|Γ| - n - #|Γ|) with 0 by lia. simpl.
    rewrite Nat.add_succ_r !app_nil_r. apply H; now try lia.
  Qed.

  Lemma typing_spine_nth_error_None Γ Δ T args T' :
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args #|Δ| = None ->
    Σ ;;; Γ ⊢ (subst0 (List.rev args) (it_mkProd_or_LetIn (firstn (#|Δ| - #|args|) Δ) T)) ≤ T'.
  Proof.
    induction Δ in args, T |- * using ctx_length_rev_ind.
    { intros. eapply nth_error_None in H0. simpl in H0 |- *. destruct args => //; simpl in H0; try lia.
      rewrite subst_empty. simpl in X0. now depelim X0. }
    destruct d as [na [b|] ty]; intros ass; eapply assumption_context_app in ass as [assΓ ass].
    * exfalso; depelim ass.
    * simpl. rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= //.
      intros wf sp.
      pose proof (All_local_env_app_inv wf) as [_ wfty].
      eapply All_local_env_app_inv in wfty as [wfty _]. depelim wfty.
      intros Hargs. eapply nth_error_None in Hargs.
      len in Hargs. len; simpl.
      depelim sp.
      + eapply ws_cumul_pb_Prod_l_inv in w as [na' [dom [codom [eqna eqd eqc]]]].
        simpl. rewrite subst_empty. simpl; len.
        simpl. rewrite Nat.sub_0_r firstn_app_2. simpl.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        etransitivity.
        2:{ eapply ws_cumul_pb_eq_le. symmetry. now eapply red_ws_cumul_pb. }
        eapply ws_cumul_pb_Prod; eauto.
      + eapply ws_cumul_pb_Prod_Prod_inv in w as [eqna dom codom].
        assert (Σ ;;; Γ |- hd : ty).
        { eapply type_ws_cumul_pb; pcuic. eapply ws_cumul_pb_eq_le. now symmetry. }
        eapply (substitution0_ws_cumul_pb (t:=hd)) in codom; eauto.
        eapply typing_spine_strengthen in sp. 3:eauto.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        simpl. replace (#|Γ0| + 1 - S #|tl|) with (#|Γ0| - #|tl|) by lia.
        rewrite firstn_app. rewrite (firstn_0 _ (_ - _ - _)); try lia; rewrite app_nil_r.
        move: Hargs; simpl; rewrite Nat.add_1_r => hlen.
        specialize (X (subst_context [hd] 0 Γ0) ltac:(len; reflexivity) (subst [hd] #|Γ0| T) tl).
        forward X by now eapply assumption_context_fold.
        forward X.
        { eapply substitution_wf_local; eauto. constructor. constructor. now rewrite subst_empty.
          now rewrite app_context_assoc in wf. }
        specialize (X sp).
        forward X. len. apply nth_error_None. lia.
        rewrite subst_app_simpl.
        simpl. rewrite subst_it_mkProd_or_LetIn.
        simpl. len.
        len in X.
        rewrite firstn_length_le. lia.
        replace (#|Γ0| - #|tl| + #|tl|)%nat with #|Γ0| by lia.
        rewrite firstn_subst_context in X => //.
        eapply isType_apply; tea.
  Qed.

  Lemma assumption_context_firstn n Γ :
    assumption_context Γ ->
    assumption_context (firstn n Γ).
  Proof.
    induction n in Γ |- *; simpl; try constructor; auto.
    intros. destruct Γ; simpl; try constructor.
    depelim H. constructor. auto.
  Qed.

  Lemma typing_spine_nth_error_None_prod Γ Δ T args T' n decl :
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = None ->
    nth_error (List.rev Δ) n = Some decl ->
    ∑ na dom codom, Σ ;;; Γ ⊢ tProd na dom codom ≤ T'.
  Proof.
    intros ass wf sp nth nth'.
    eapply typing_spine_nth_error_None in sp; eauto;
    eapply nth_error_None in nth;
    eapply nth_error_Some_length in nth'; len in nth'.
    rewrite subst_it_mkProd_or_LetIn in sp.
    2:{ eapply nth_error_None. lia. }
    set (ctx := subst_context (List.rev args) 0 (firstn (#|Δ| - #|args|) Δ)) in *.
    assert (#|ctx| > 0).
    { rewrite /ctx; len. rewrite firstn_length_le; lia. }
    assert (assumption_context ctx).
    { rewrite /ctx. apply assumption_context_fold. now apply assumption_context_firstn. }
    destruct ctx using rev_case; simpl in *. lia.
    rewrite it_mkProd_or_LetIn_app in sp.
    move/assumption_context_app: H0 => [ass' assx].
    destruct x as [na [b|] ty]. exfalso. depelim assx.
    rewrite /mkProd_or_LetIn in sp.
    eexists _, _, _; eauto. eapply sp.
  Qed.

  Lemma wf_fixpoint_spine Γ mfix idx decl args ty :
    wf_fixpoint Σ.1 mfix ->
    nth_error mfix idx = Some decl ->
    isType Σ Γ (dtype decl) ->
    typing_spine Σ Γ (dtype decl) args ty ->
    match nth_error args decl.(rarg) with
    | Some arg =>
      ∑ ind u indargs,
      (Σ ;;; Γ |- arg : mkApps (tInd ind u) indargs) *
      check_recursivity_kind (lookup_env Σ) (inductive_mind ind) Finite
    | None => ∑ na dom codom, Σ ;;; Γ ⊢ tProd na dom codom ≤ ty
    end.
  Proof.
    move=> wffix nthe isty.
    eapply wf_fixpoint_inv in nthe; eauto.
    destruct nthe as [mind' [cfix ck]].
    move=> sp.
    destruct decl as [dna dty dbod rarg].
    rewrite /check_one_fix in cfix. simpl in *.
    case E: (decompose_prod_assum [] dty) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst dty.
    destruct (nth_error _ rarg) eqn:Hnth => //.
    pose proof (nth_error_Some_length Hnth).
    len in H. simpl in H.
    eapply typing_spine_smash in sp.
    destruct (nth_error args rarg) eqn:hargs.
    - eapply typing_spine_nth_error in sp; eauto; cycle 1.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct isty as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
      * destruct (decompose_app (decl_type c)) as [hd tl] eqn:da.
        destruct (destInd hd) as [[i u]|] eqn:di => //.
        destruct i as [mind i]. noconf cfix.
        eapply decompose_app_inv in da. rewrite da in sp.
        rewrite subst_mkApps in sp.
        destruct hd => //; noconf di. simpl in sp.
        eexists _, ui, _; intuition eauto.
    - eapply typing_spine_nth_error_None_prod in sp; eauto.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct isty as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
  Qed.

  Lemma wf_cofixpoint_spine Γ mfix idx decl args ty :
    wf_cofixpoint Σ.1 mfix ->
    nth_error mfix idx = Some decl ->
    isType Σ Γ (dtype decl) ->
    typing_spine Σ Γ (dtype decl) args ty ->
    ∑ Γ' T, (decompose_prod_assum [] (dtype decl) = (Γ', T)) *
    ∑ ind u indargs, (T = mkApps (tInd ind u) indargs) *
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite *
    if #|args| <? context_assumptions Γ' then
      (Σ ;;; Γ ⊢ subst0 (List.rev args)
      (it_mkProd_or_LetIn (firstn (context_assumptions Γ' - #|args|) (smash_context [] Γ'))
        (expand_lets Γ' T)) ≤ ty)
    else
      (#|args| = context_assumptions Γ') *
      (Σ ;;; Γ ⊢ subst (List.rev args) 0 (expand_lets Γ' T) ≤ ty).
  Proof.
    move=> wffix nthe isty.
    eapply wf_cofixpoint_inv in nthe; eauto.
    destruct nthe as [mind' [cfix ck]].
    move=> sp.
    destruct decl as [dna dty dbod rarg].
    rewrite /check_one_cofix in cfix. simpl in *.
    case E: (decompose_prod_assum [] dty) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst dty. exists Γ', concl. split; auto.
    destruct (decompose_app concl) as [hd tl] eqn:da.
    destruct (destInd hd) as [[mind i]|] eqn:di => //.
    destruct mind => //. destruct hd => //.
    noconf di. noconf cfix.
    eapply decompose_app_inv in da.
    eexists _, _, _; intuition eauto.
    destruct (Nat.ltb #|args| (context_assumptions Γ')) eqn:lt; [
      eapply Nat.ltb_lt in lt|eapply Nat.ltb_nlt in lt; destruct (Nat.eqb #|args| (context_assumptions Γ')) eqn:eq;
      [eapply Nat.eqb_eq in eq|eapply Nat.eqb_neq in eq]].
    - eapply typing_spine_smash in sp.
      destruct (nth_error args #|args|) eqn:hargs.
      { rewrite (proj2 (nth_error_None _ _)) // in hargs. }
      destruct (nth_error (List.rev (smash_context [] Γ')) #|args|) as [decl|] eqn:hnth.
      eapply typing_spine_nth_error_None in sp; eauto.
      * len in sp.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct isty as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
      * len; simpl. eapply nth_error_None in hargs => //.
        eapply nth_error_None. lia.
      * eapply nth_error_None in hnth => //. len in hnth.
    - eapply typing_spine_all_inv in sp => //.
      subst concl.
      rewrite expand_lets_mkApps subst_mkApps /= in sp.
      destruct sp. split; auto.
      now rewrite expand_lets_mkApps subst_mkApps /=.
    - subst concl; eapply typing_spine_more_inv in sp; try lia.
  Qed.

End Spines.

(** Evaluation is a subrelation of reduction: *)

Tactic Notation "redt" uconstr(y) := eapply (CRelationClasses.transitivity (R:=red _ _) (y:=y)).

Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.

Fixpoint axiom_free_value Σ args t :=
  match t with
  | tApp hd arg => axiom_free_value Σ (axiom_free_value Σ [] arg :: args) hd
  | tConst kn _ => match lookup_env Σ kn with
                   | Some (ConstantDecl {| cst_body := None |}) => false
                   | _ => true
                   end
  | tCase _ _ discr _ => axiom_free_value Σ [] discr
  | tProj _ t => axiom_free_value Σ [] t
  | tFix defs i =>
    match nth_error defs i with
    | Some def => nth (rarg def) args true
    | None => true
    end
  | _ => true
  end.

Lemma axiom_free_axiom_free_value Σ t :
  axiom_free Σ ->
  axiom_free_value Σ [] t.
Proof.
  intros axfree.
  cut (Forall is_true []); [|constructor].
  generalize ([] : list bool).
  induction t using term_forall_list_ind; intros axfree_args all_true; cbn; auto.
  - destruct lookup_env eqn:find; auto.
    destruct g; auto.
    destruct c; auto.
    apply declared_constant_from_gen in find.
    apply axfree in find; cbn in *.
    now destruct cst_body0.
  - destruct nth_error; auto.
    rewrite nth_nth_error.
    destruct nth_error eqn:nth; auto.
    eapply nth_error_forall in nth; eauto.
Qed.

Section classification.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Abbreviation wh_neutral := (whne RedFlags.default).
  Abbreviation wh_normal := (whnf RedFlags.default).

  Transparent construct_cofix_discr.

  Lemma value_whnf t : closed t -> value Σ t -> wh_normal Σ [] t.
  Proof.
    intros cl ev.
    induction ev in cl |- * using value_values_ind.
    destruct t; simpl in H; try discriminate; try solve [constructor; constructor].
    - eapply (whnf_indapp _ _ [] _ _ []).
    - eapply (whnf_cstrapp _ _ [] _ _ _ []).
    - eapply (whnf_fixapp _ _ [] _ _ []).
      destruct nth_error as [rarg|] => /= //; [|easy].
      left ; eexists; split; eauto.
      now rewrite nth_error_nil.
    - eapply (whnf_cofixapp _ _ [] _ _ []).
    - eapply whnf_prim.
    - destruct X => //.
      pose proof cl as cl'.
      rewrite closedn_mkApps in cl'. move/andP: cl' => [clfix _].
      rewrite -closed_unfold_fix_cunfold_eq in e => //.
      rewrite /unfold_fix in e.
      destruct nth_error eqn:nth => //. noconf e.
      eapply whnf_fixapp. rewrite nth. left; eexists; split; eauto.
      now eapply nth_error_None.
  Qed.

  Lemma eval_whne t t' : closed t -> eval Σ t t' -> wh_normal Σ [] t'.
  Proof.
    intros cl ev.
    pose proof (eval_closed Σ _ _ cl ev).
    eapply eval_to_value in ev.
    now eapply value_whnf.
  Qed.

  Lemma typing_var {Γ n ty} : Σ ;;; Γ |- (tVar n) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Lemma typing_evar {Γ n l ty} : Σ ;;; Γ |- (tEvar n l) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Lemma typing_cofix_coind {Γ mfix idx args ind u indargs} :
    Σ ;;; Γ |- mkApps (tCoFix mfix idx) args : mkApps (tInd ind u) indargs ->
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.
  Proof.
    intros tyarg.
    eapply inversion_mkApps in tyarg as [A [Hcof sp]]; auto.
    eapply inversion_CoFix in Hcof as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto.
    simpl in a.
    apply isTypeRel_isType in a.
    eapply typing_spine_strengthen in sp; eauto.
    eapply wf_cofixpoint_spine in sp as (Γ' & concl & da & ?); eauto.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in da.
    simpl in da.
    move: s => [ind' [u' [indargs' [[ceq ccum] ck]]]].
    subst concl.  move: ck.
    elim: Nat.ltb_spec => Hargs.
    - rewrite subst_it_mkProd_or_LetIn; len.
      set (ctx := subst_context _ _ _).
      assert(assumption_context ctx).
      eapply assumption_context_fold, assumption_context_firstn, smash_context_assumption_context; constructor.
      assert (#|ctx| > 0).
      { rewrite /ctx; len; rewrite firstn_length_le. len; lia. lia. }
      destruct ctx as [|ctx [na [b|] ty]] using rev_case. simpl in H0; lia.
      exfalso; move/assumption_context_app: H => [ass assd]; depelim assd.
      move/assumption_context_app: H => [ass assd]; depelim assd.
      rewrite it_mkProd_or_LetIn_app /mkProd_or_LetIn /= => cum.
      now eapply invert_cumul_prod_ind in cum.
    - move=> [hargs ccum'].
      rewrite expand_lets_mkApps subst_mkApps /= in ccum'.
      eapply invert_cumul_ind_ind in ccum' as ((? & r) & ?).
      len in r. eapply ReflectEq.eqb_eq in i0. now subst ind'.
  Qed.

  Lemma check_recursivity_kind_inj {mind rk rk'} :
    check_recursivity_kind (lookup_env Σ) mind rk ->
    check_recursivity_kind (lookup_env Σ) mind rk' -> rk = rk'.
  Proof.
    rewrite /check_recursivity_kind.
    case: lookup_env => //; case => // m.
    elim: ReflectEq.eqb_spec;
    elim: ReflectEq.eqb_spec; congruence.
  Qed.

  Lemma wt_closed_red_refl {Γ t T} : Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ t ⇝ t.
  Proof.
    intros Hs.
    eapply closed_red_refl.
    now eapply typing_wf_local, wf_local_closed_context in Hs.
    now eapply subject_is_open_term.
  Qed.

  Lemma invert_ind_ind Γ ind u args ind' u' args' :
    Σ;;; Γ |- mkApps (tInd ind u) args : mkApps (tInd ind' u') args' -> False.
  Proof.
    intros typ.
    eapply inversion_mkApps in typ as (?&?&?); auto.
    eapply inversion_Ind in t as (?&?&?&decl&?&?); auto.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    pose proof (on_declared_inductive decl) as [onind oib].
    rewrite oib.(ind_arity_eq) in t0.
    rewrite !subst_instance_it_mkProd_or_LetIn in t0.
    eapply typing_spine_arity_mkApps_Ind in t0; eauto.
    eapply typing_spine_isType_dom in t0 as (_ & s & Hs & _).
    eexists; split; [sq|]. now eapply wt_closed_red_refl.
    now do 2 eapply isArity_it_mkProd_or_LetIn.
    now eapply isTypeRel_isType, (declared_inductive_valid_type decl).
  Qed.

  Lemma invert_fix_ind Γ mfix i args ind u args' :
    match unfold_fix mfix i with
    | Some (rarg, _) => nth_error args rarg = None
    | _ => True
    end ->
    Σ;;; Γ |- mkApps (tFix mfix i) args : mkApps (tInd ind u) args' -> False.
  Proof.
    intros no_arg typ.
    eapply inversion_mkApps in typ as (?&?&?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    unfold unfold_fix in no_arg.
    rewrite e in no_arg.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite no_arg in t0. destruct t0 as [na [dom [codom cum]]].
    eapply ws_cumul_pb_Prod_l_inv in cum as (? & ? & ? & []).
    eapply invert_red_mkApps_tInd in c as [? [eq _]]; auto.
    solve_discr.
  Qed.


  Lemma axiom_free_value_mkApps Σ' args hd args' :
    axiom_free_value Σ' args (mkApps hd args') =
    axiom_free_value Σ' (map (axiom_free_value Σ' []) args' ++ args) hd.
  Proof.
    revert hd args.
    induction args' using MRList.rev_ind; intros hd args; cbn; auto.
    rewrite mkApps_app /=.
    rewrite IHargs'.
    now rewrite map_app /= -app_assoc.
  Qed.

  Lemma wh_neutral_empty_gen Γ free t ty :
    axiom_free_value Σ free t ->
    wh_neutral Σ [] t ->
    Σ ;;; Γ |- t : ty ->
    Γ = [] ->
    False.
  Proof.
    intros axfree ne typed.
    induction ne in free, t, ty, axfree, ne, typed |- *; intros ->; simpl in *; try discriminate.
    - apply inversion_Rel in typed as (?&?&?&?); auto.
      rewrite nth_error_nil in e0; discriminate.
    - now eapply typing_var in typed.
    - now eapply typing_evar in typed.
    - apply inversion_Const in typed as [decl' [wfd [declc [cu cum]]]]; eauto.
      unshelve eapply declared_constant_to_gen in declc; eauto.
      red in declc. rewrite declc in e, axfree.
      noconf e.
      destruct decl; cbn in *.
      rewrite e0 in axfree; congruence.
    - eapply inversion_App in typed as [na [A [B [Hf _]]]]; eauto.
    - eapply inversion_mkApps in typed as (? & ? & ?); eauto.
      eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
      eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
      eapply typing_spine_strengthen in t0; eauto.
      rewrite /unfold_fix in e. rewrite e1 in e. noconf e.
      eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
      rewrite e0 in t0. destruct t0 as [ind [u [indargs [tyarg ckind]]]].
      rewrite axiom_free_value_mkApps in axfree.
      cbn in axfree.
      rewrite e1 nth_nth_error nth_error_app1 in axfree.
      1: { rewrite length_map.
           apply nth_error_Some_length in e0; auto. }
      rewrite nth_error_map e0 in axfree.
      cbn in axfree.
      eauto.
    - eapply inversion_Case in typed as (? & ? & ? & ? & [] & ?); tas; eauto.
    - eapply inversion_Proj in typed as (? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
  Qed.

  Lemma wh_neutral_empty t ty :
    axiom_free_value Σ [] t ->
    wh_neutral Σ [] t ->
    Σ ;;; [] |- t : ty ->
    False.
  Proof. eauto using wh_neutral_empty_gen. Qed.

  Lemma whnf_classification' t i u args :
    axiom_free_value Σ [] t ->
    wh_normal Σ [] t ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t).
  Proof.
    intros axfree ne typed.
    pose proof (subject_closed typed) as cl.
    depelim ne; simpl in *.
    - exfalso. eauto using wh_neutral_empty.
    - eapply inversion_Sort in typed as (? & ? & e); auto.
      now eapply invert_cumul_sort_ind in e.
    - eapply inversion_Prod in typed as (? & ? & ? & ? & e); auto.
      now eapply invert_cumul_sort_ind in e.
    - eapply inversion_Lambda in typed as (? & ? & ? & e); auto.
      now eapply invert_cumul_prod_ind in e.
    - now rewrite head_mkApps /= /head /=.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
      unfold unfold_fix. destruct nth_error; [|easy].
      destruct o as [[? [? ?]]|]; [|easy]. inversion H; eauto.
    - now rewrite head_mkApps /head /=.
    - eapply inversion_Prim in typed as [prim_ty [cdecl [? ? ? ? hp]]]; eauto.
      destruct p as [? []]; simp prim_type in w.
      1-3:eapply (invert_cumul_axiom_ind (args := [])) in w; eauto; destruct p0 as [? []]; eauto.
      eapply (invert_cumul_axiom_ind (args := [array_type a0])) in w; eauto. destruct p0 as [s []]; eauto.
  Qed.

  Lemma whnf_classification t i u args :
    axiom_free Σ ->
    wh_normal Σ [] t ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t).
  Proof.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply whnf_classification'; eauto.
  Qed.

  Definition notCoInductive Σ ind :=
    ~check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.

  Lemma ind_whnf_classification' t ind u indargs :
    axiom_free_value Σ [] t -> notCoInductive Σ ind ->
    Σ ;;; [] |- t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t.
  Proof.
    intros axfree ck typed whnf.
    rewrite /isConstruct_app.
    eapply whnf_classification' in whnf; eauto.
    rewrite /head in whnf.
    destruct (decompose_app t) as [hd tl] eqn:da; simpl in *.
    destruct hd eqn:eqh => //. subst hd.
    eapply decompose_app_inv in da. subst.
    eapply typing_cofix_coind in typed.
    congruence.
  Qed.

  Lemma ind_whnf_classification t ind u indargs :
    axiom_free Σ -> notCoInductive Σ ind ->
    Σ ;;; [] |- t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t.
  Proof.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply ind_whnf_classification'; eauto.
  Qed.

  Lemma fix_app_is_constructor {mfix idx args ty narg fn} :
    Σ;;; [] |- mkApps (tFix mfix idx) args : ty ->
    unfold_fix mfix idx = Some (narg, fn) ->
    match nth_error args narg return Type with
    | Some a => axiom_free_value Σ [] a -> wh_normal Σ [] a -> isConstruct_app a
    | None => ∑ na dom codom, Σ ;;; [] ⊢ tProd na dom codom ≤ ty
    end.
  Proof.
    intros typed unf.
    eapply inversion_mkApps in typed as (? & ? & ?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
    eapply typing_spine_strengthen in t0; eauto.
    rewrite /unfold_fix in unf. rewrite e in unf.
    noconf unf.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite /is_constructor. destruct (nth_error args (rarg x0)) eqn:hnth; [|assumption].
    destruct_sigma t0.
    intros axfree norm.
    eapply ind_whnf_classification' in t1; eauto.
    intros chk.
    pose proof (check_recursivity_kind_inj chk t0).
    discriminate.
  Qed.


  Lemma value_axiom_free Σ' t :
    value Σ' t ->
    axiom_free_value Σ' [] t.
  Proof.
    intros val.
    induction val using value_values_ind.
    - destruct t; try discriminate; auto.
      cbn.
      destruct ?; auto.
      destruct ?; auto.
    - cbn. constructor.
    - rewrite axiom_free_value_mkApps.
      rewrite app_nil_r.
      destruct X; try constructor.
      cbn.
      unfold isStuckFix, cunfold_fix in e.
      destruct nth_error; auto.
      rewrite nth_overflow; auto. len. now noconf e.
  Qed.

  (** Evaluation on well-typed terms corresponds to reduction.
      It differs in two ways from standard reduction:
      - using closed substitution operations applicable only on closed terms
      - it does not check that fixpoints that are applied to enough arguments
        have a constructor at their recursive argument as it is ensured by typing
        + classification. *)

  Import PCUICGlobalEnv.

  Lemma wcbveval_red t ty u :
    Σ ;;; [] |- t : ty ->
    eval Σ t u -> red Σ [] t u.
  Proof.
    intros Hc He.
    revert ty Hc.
    induction He; simpl; move=> ty Ht;
      try solve[econstructor; eauto].

    - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
      redt (tApp (tLambda na t b) a); eauto.
      eapply red_app; eauto.
      redt (tApp (tLambda na t b) a'). eapply red_app; eauto.
      specialize (IHHe1 _ t0). specialize (IHHe2 _ t1).
      redt (csubst a' 0 b).
      rewrite (closed_subst a' 0 b).
      eapply eval_closed; eauto. now eapply subject_closed in t1.
      eapply red1_red. constructor.
      pose proof (subject_closed t1); auto.
      eapply eval_closed in H; eauto.
      eapply subject_reduction in IHHe1. 2-3:eauto.
      eapply inversion_Lambda in IHHe1 as (? & ? & ? & e); eauto.
      eapply (substitution0 (Γ := [])) in t2; eauto.
      eapply IHHe3.
      rewrite (closed_subst a' 0 b); auto.
      rewrite /subst1 in t2. eapply t2.
      eapply (type_ws_cumul_pb (pb:=Conv)); eauto.
      eapply subject_reduction in IHHe2; eauto.
      now eapply isTypeRel_isType.
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna dom codom]; eauto.
      now symmetry.

    - eapply inversion_LetIn in Ht as (? & ? & ? & ?); auto.
      apply unlift_TermTyp in l as t0'.
      redt (tLetIn na b0' t b1); eauto.
      eapply red_letin; eauto.
      redt (b1 {0 := b0'}); auto.
      do 2 econstructor.
      specialize (IHHe1 _ t0').
      rewrite /subst1.
      rewrite -(closed_subst b0' 0 b1).
      eapply subject_reduction in t0'; eauto. eapply subject_closed in t0'; eauto.
      eapply IHHe2.
      rewrite closed_subst.
      eapply subject_reduction in t0'; eauto. eapply subject_closed in t0'; eauto.
      pose proof (subject_is_open_term t0).
      eapply substitution_let in t0; eauto.
      eapply subject_reduction in t0.
      3:{ eapply (red_red (Δ := [vass na t]) (Γ' := [])); eauto. 3:repeat constructor.
          cbn. rewrite addnP_shiftnP. eapply type_is_open_term in t0'. now erewrite t0'.
          repeat constructor. cbn. rewrite addnP_shiftnP.
          eapply subject_is_open_term in t0'. cbn in t0'. now setoid_rewrite shiftnP0 in t0'. }
      apply t0. auto.

    - redt (subst_instance u body); auto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.
      eapply IHHe. eapply subject_reduction; eauto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Case in Ht; auto. destruct_sigma Ht.
      unshelve epose proof (isdecl_ := declared_inductive_to_gen isdecl); eauto.
      destruct (declared_inductive_inj d isdecl_); subst mdecl0 idecl0.
      destruct c0.
      specialize (IHHe1 _ scrut_ty).
      assert (red Σ [] (tCase ci p discr brs) (iota_red ci.(ci_npar) p args br)).
      { clear X. redt _.
        eapply red_case; eauto.
        eapply All2_refl; intros; eauto. red.
        eapply All2_refl; split; reflexivity.
        eapply red1_red. destruct p => /= //.
        eapply red_iota; tea.
        rewrite e1 /cstr_arity eq_npars e3 //. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Proj in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      assert (red Σ [] (tProj p discr) a).
      { redt _.
        eapply red_proj_c; eauto.
        eapply red1_red; constructor; auto. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_App in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      epose proof (subject_reduction Σ [] _ _ _ wfΣ t IHHe1) as Ht2.
      epose proof (subject_reduction Σ [] _ _ _ wfΣ t0 IHHe2) as Ha2.
      assert (red Σ [] (tApp f4 a) (tApp (mkApps fn argsv) av)).
      { redt _.
        eapply red_app; eauto.
        rewrite -![tApp _ _](mkApps_app _ _ [_]).
        eapply red1_red.
        rewrite -closed_unfold_fix_cunfold_eq in e1.
        { eapply subject_closed in Ht2; auto.
          rewrite closedn_mkApps in Ht2. now move/andP: Ht2 => [clf _]. }
        eapply red_fix; eauto.
        assert (Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : B {0 := av}).
        { rewrite mkApps_app /=. eapply type_App'; eauto. }
        epose proof (fix_app_is_constructor X0 e1); eauto.
        rewrite /is_constructor.
        destruct nth_error eqn:hnth => //.
        2:{ eapply nth_error_None in hnth. len in hnth. }
        assert (All (closedn 0) (argsv ++ [av])).
        { eapply subject_closed in X0; eauto.
          rewrite closedn_mkApps in X0.
          move/andP: X0 => [clfix clargs].
          now eapply forallb_All in clargs. }
        assert (All (value Σ) (argsv ++ [av])).
        { eapply All_app_inv; [|constructor; [|constructor]].
          eapply eval_to_value in He1.
          eapply value_mkApps_inv in He1 as [[-> Hat]|[vh vargs]] => //.
          now eapply eval_to_value in He2. }
        solve_all.
        eapply nth_error_all in X3; eauto. simpl in X3.
        destruct X3 as [cl val]. eapply X1, value_whnf; auto.
        now eapply value_axiom_free. }
      redt _; eauto.

    - apply inversion_App in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      now eapply red_app.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Case in Ht; auto; destruct_sigma Ht.
      destruct c.
      specialize (IHHe1 _ scrut_ty).
      unshelve epose proof (subject_reduction Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closed X0).
      etransitivity. eapply red_case_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)).
      { eapply red1_red. eapply red_cofix_case.
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
      redt _; eauto.
      eapply IHHe2.
      eapply subject_reduction. 3: eapply X1. eauto.
      eapply subject_reduction. 3: eapply red_case_c; eauto. all:eauto.
    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Proj in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      unshelve epose proof (subject_reduction Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closed X0).
      etransitivity. eapply red_proj_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))).
      { eapply red1_red. eapply red_cofix_proj.
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
        redt _; eauto.
      eapply IHHe2.
      eapply subject_reduction. 3: eapply X1. eauto.
      eapply subject_reduction. 3: eapply red_proj_c; eauto. all:eauto.

    - eapply inversion_App in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      rewrite mkApps_app /=. now eapply red_app.

    - eapply inversion_App in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      now eapply red_app.

    - eapply inversion_Prim in Ht as [prim_type [decl []]]; eauto.
      depelim X. 1-3:reflexivity.
      depelim p1. specialize (r _ hdef).
      eapply red_primArray_congr; eauto.
      eapply All2_undep in a. solve_all.
  Qed.

  Theorem subject_reduction_eval {t u T} :
    Σ ;;; [] |- t : T -> eval Σ t u -> Σ ;;; [] |- u : T.
  Proof.
    intros Hty Hred.
    eapply wcbveval_red in Hred; eauto. eapply subject_reduction; eauto.
  Qed.

  Lemma value_classification {t i u args} :
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    value Σ t ->
    construct_cofix_discr (head t).
  Proof.
    intros Ht Hvalue.
    eapply value_axiom_free in Hvalue as H.
    eapply whnf_classification'; eauto.
    eapply eval_whne.
    2: eapply value_final; eauto.
    eapply @subject_closed with (Γ := []); eauto.
  Qed.

  Lemma eval_classification {t i u args} :
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    forall t', eval Σ t t' ->
    construct_cofix_discr (head t').
  Proof.
    intros Ht t' eval.
    pose proof (subject_closed Ht).
    eapply subject_reduction in Ht. 3:eapply wcbveval_red; eauto. 2:auto.
    eapply eval_to_value in eval as axfree.
    eapply value_axiom_free in axfree.
    eapply eval_whne in eval; auto.
    eapply whnf_classification'; eauto.
  Qed.

End classification.

(* Print Assumptions eval_ind_canonical. *)
