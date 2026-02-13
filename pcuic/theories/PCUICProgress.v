(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICViews
  PCUICWellScopedCumulativity PCUICClassification PCUICWcbvEval.

From Equations Require Import Equations.

Lemma eval_tCase {cf : checker_flags} {Σ : global_env_ext}  ci p discr brs res T :
  wf Σ ->
  Σ ;;; [] |- tCase ci p discr brs : T ->
  eval Σ (tCase ci p discr brs) res ->
  ∑ c u args, red Σ [] (tCase ci p discr brs) (tCase ci p ((mkApps (tConstruct ci.(ci_ind) c u) args)) brs).
Proof.
  intros wf wt H. depind H; try now (cbn in *; congruence).
  - eapply inversion_Case in wt as (? & ? & ? & ? & cinv & ?); eauto.
    eexists _, _, _. eapply red_case_c. eapply wcbveval_red. 2: eauto. eapply cinv.
  - eapply inversion_Case in wt as wt'; eauto. destruct wt' as (? & ? & ? & ? & cinv & ?).
    assert (Hwcbv_red1 : Σ;;; [] |- tCase ip p discr brs ⇝* tCase ip p (mkApps fn args) brs). {
      etransitivity. { eapply red_case_c. eapply wcbveval_red. 2: eauto. eapply cinv. }
      econstructor. econstructor.
      rewrite closed_unfold_cofix_cunfold_eq. eauto.
      enough (closed (mkApps (tCoFix mfix idx) args)) as Hcl by (rewrite closedn_mkApps in Hcl; solve_all).
      eapply eval_closed. eauto.
      2: eauto. eapply @subject_closed with (Γ := []); eauto. eapply cinv. tea.
    }
    edestruct IHeval2 as (c & u & args0 & IH); eauto using subject_reduction.
    exists c, u, args0. etransitivity; eauto.
Qed.

Local Existing Instance config.extraction_checker_flags.

Inductive typing_spine_pred {cf : checker_flags} Σ (Γ : context) (P : forall t T (H : Σ ;;; Γ |- t : T), Type) : term -> list term -> term -> Type :=
| type_spine_pred_nil ty ty' (* s s' *) :
    isType Σ Γ ty ->
    isType Σ Γ ty' ->
    (* forall H : Σ ;;; Γ |- ty : tSort s,
    P ty (tSort s) H ->
    forall H' : Σ ;;; Γ |- ty' : tSort s',
    P ty' (tSort s') H' ->
     *) Σ ;;; Γ ⊢ ty ≤ ty' ->
    typing_spine_pred Σ Γ P ty [] ty'

| type_spine_pred_cons ty hd tl na A B B' s' :
    isType Σ Γ ty ->
    forall H' : Σ ;;; Γ |- tProd na A B : tSort s',
    P (tProd na A B) (tSort s') H' ->
    Σ ;;; Γ ⊢ ty ≤ tProd na A B ->
    forall H : Σ ;;; Γ |- hd : A,
    P hd A H ->
    typing_spine_pred Σ Γ P (subst10 hd B) tl B' ->
    typing_spine_pred Σ Γ P ty (hd :: tl) B'.

Section WfEnv.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma typing_spine_pred_strengthen {Γ P T args U} :
    typing_spine_pred Σ Γ P T args U ->
    isType Σ Γ T ->
    forall T',
    isType Σ Γ T' ->
    Σ ;;; Γ ⊢ T' ≤ T ->
    typing_spine_pred Σ Γ P T' args U.
  Proof using wfΣ.
    induction 1 in |- *; intros T' isTy redT.
    - constructor; eauto. transitivity ty; auto.
    - specialize IHX with (T' := (B {0 := hd})).
      assert (isType Σ Γ (B {0 := hd})) as HH. {
        clear p.
        eapply inversion_Prod in H' as (? & ? & ? & ? & ?); tea.
        eapply isType_subst. econstructor. econstructor. rewrite subst_empty; eauto.
        econstructor; cbn; eauto.
      }
      do 3 forward IHX by pcuic.
      intros Hsub.
      eapply type_spine_pred_cons; eauto.
      etransitivity; eauto.
  Qed.

End WfEnv.

Lemma inversion_mkApps {cf : checker_flags} {Σ} {wfΣ :  wf Σ.1} {Γ f u T} s :
  forall (H : Σ ;;; Γ |- mkApps f u : T) (HT : Σ ;;; Γ |- T : tSort s),
  { A : term & { Hf : Σ ;;; Γ |- f : A & {s' & {HA : Σ ;;; Γ |- A : tSort s' &
   typing_size Hf <= typing_size H ×
   typing_size HA <= max (typing_size H) (typing_size HT) ×
  typing_spine_pred Σ Γ (fun x ty Hx => typing_size Hx <= typing_size H) A u T}}}}.
Proof.
  revert f T.
  induction u; intros f T. simpl. intros.
  { exists T, H, s, HT. intuition pcuic.
    econstructor. 3: eapply isType_ws_cumul_pb_refl. all: now eapply has_sort_isType. }
  intros Hf Ht. simpl in Hf.
  specialize (IHu (tApp f a) T).
  edestruct (IHu Hf) as (T' & H' & s' & H1 & H2 & H3 & H4); tea.
  edestruct @inversion_App_size with (H := H') as (na' & A' & B' & s_ & Hf' & Ha & HA & Hs1 & Hs2 & Hs3 & HA'''); tea.
  exists (tProd na' A' B'). exists Hf'. exists s_. exists HA.
  split. rewrite <- H2. lia.
  split. rewrite <- Nat.le_max_l, <- H2. lia.

  unshelve econstructor.
  5: eauto. 1: eauto.
  3:eapply isType_ws_cumul_pb_refl; now eapply has_sort_isType.
  1: now eapply has_sort_isType.
  1, 2: rewrite <- H2; lia.
  eapply typing_spine_pred_strengthen; tea.
  now eapply has_sort_isType. clear Hs3.
  eapply inversion_Prod in HA as (? & ? & ? & ? & ?); tea.
  eapply isType_subst. econstructor. econstructor. rewrite subst_empty; eauto.
  econstructor;  cbn; eauto.
  Unshelve. eauto.
Qed.

Lemma typing_ind_env_app_size `{cf : checker_flags} :
forall (P : global_env_ext -> context -> term -> term -> Type)
       (Pj : global_env_ext -> context -> judgment -> Type)
       (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
       (PΓ : global_env_ext -> context -> Type),

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (* (wfΓ : wf_local Σ Γ) *) j,
    lift_typing_conj (typing Σ) (P Σ) Γ j -> Pj Σ Γ j) ->

  (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ),
    All_local_env_over (typing Σ) (Pdecl Σ) Γ wfΓ -> All_local_env (Pj Σ) Γ -> PΓ Σ Γ) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
      nth_error Γ n = Some decl ->
      PΓ Σ Γ ->
      P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (u : sort),
      PΓ Σ Γ ->
      wf_sort Σ u ->
      P Σ Γ (tSort u) (tSort (Sort.super u))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (na : aname) (t b : term) (s1 s2 : sort),
      PΓ Σ Γ ->
      lift_typing typing Σ Γ (j_vass_s na t s1) ->
      Pj Σ Γ (j_vass_s na t s1) ->
      Σ ;;; Γ,, vass na t |- b : tSort s2 ->
      P Σ (Γ,, vass na t) b (tSort s2) -> P Σ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (na : aname) (t b bty : term),
      PΓ Σ Γ ->
      lift_typing typing Σ Γ (j_vass na t) ->
      Pj Σ Γ (j_vass na t) ->
      Σ ;;; Γ,, vass na t |- b : bty -> P Σ (Γ,, vass na t) b bty -> P Σ Γ (tLambda na t b) (tProd na t bty)) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (na : aname) (b b_ty b' b'_ty : term),
      PΓ Σ Γ ->
      lift_typing typing Σ Γ (j_vdef na b b_ty) ->
      Pj Σ Γ (j_vdef na b b_ty) ->
      Σ ;;; Γ,, vdef na b b_ty |- b' : b'_ty ->
      P Σ (Γ,, vdef na b b_ty) b' b'_ty -> P Σ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) T B L s,
      PΓ Σ Γ ->
      Σ ;;; Γ |- T : tSort s -> P Σ Γ T (tSort s) ->
      forall (Ht : Σ ;;; Γ |- t : T), P Σ Γ t T ->

      (* Give a stronger induction hypothesis allowing to crawl under applications *)
      (forall t' T' (Ht' : Σ ;;; Γ |- t' : T'), typing_size Ht' <= typing_size Ht -> P Σ Γ t' T') ->
      typing_spine_pred Σ Γ (fun u ty H => Σ ;;; Γ |- u : ty × P Σ Γ u ty) T L B ->

      P Σ Γ (mkApps t L) B) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
      on_global_env cumulSpec0 Pj Σ.1 ->
      PΓ Σ Γ ->
      declared_constant Σ.1 cst decl ->
      consistent_instance_ext Σ decl.(cst_universes) u ->
      P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
        mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
      on_global_env cumulSpec0 Pj Σ.1 ->
      PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
          mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
      on_global_env cumulSpec0 Pj Σ.1 ->
      PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
     forall (ci : case_info) p c brs indices ps mdecl idecl
       (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
       on_global_env cumulSpec0 Pj Σ.1 ->
       PΓ Σ Γ ->
       mdecl.(ind_npars) = ci.(ci_npar) ->
       eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
       let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
       wf_predicate mdecl idecl p ->
       consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
       forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
       P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
       wf_local Σ (Γ ,,, predctx) ->
       PΓ Σ (Γ ,,, predctx) ->
       is_allowed_elimination Σ idecl.(ind_kelim) ps ->
       PCUICTyping.ctx_inst (Prop_conj typing P Σ) Γ (p.(pparams) ++ indices)
         (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices) : context))) ->
       Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
       P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
       isCoFinite mdecl.(ind_finite) = false ->
       let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
       wf_branches idecl brs ->
       All2i (fun i cdecl br =>
         (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
         let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
         (PΓ Σ (Γ ,,, brctxty.1) ×
         (Prop_conj typing P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
         (Prop_conj typing P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))) 0 idecl.(ind_ctors) brs ->
       P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
        mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
      on_global_env cumulSpec0 Pj Σ.1 -> PΓ Σ Γ ->
      Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
      P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
      #|args| = ind_npars mdecl ->
      P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (pdecl.(proj_type)@[u]))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing typing Σ) Γ) mfix ->
      All (on_def_type (Pj Σ) Γ) mfix ->
      All (on_def_body (lift_typing typing Σ) types Γ) mfix ->
      All (on_def_body (Pj Σ) types Γ) mfix ->
      wf_fixpoint Σ.1 mfix ->
      P Σ Γ (tFix mfix n) decl.(dtype)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing typing Σ) Γ) mfix ->
      All (on_def_type (Pj Σ) Γ) mfix ->
      All (on_def_body (lift_typing typing Σ) types Γ) mfix ->
      All (on_def_body (Pj Σ) types Γ) mfix ->
      wf_cofixpoint Σ.1 mfix ->
      P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

  (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : prim_val) prim_ty cdecl,
      PΓ Σ Γ ->
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants (prim_val_tag p) cdecl ->
      primitive_typing_hyps typing Σ Γ p ->
      primitive_typing_hyps P Σ Γ p ->
      P Σ Γ (tPrim p) (prim_type p prim_ty)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) s,
      PΓ Σ Γ ->
      Σ ;;; Γ |- t : A ->
      P Σ Γ t A ->
      Σ ;;; Γ |- B : tSort s ->
      P Σ Γ B (tSort s) ->
      Σ ;;; Γ |- A <=s B ->
      P Σ Γ t B) ->

     env_prop P Pj PΓ.
Proof.
 intros P Pj Pdecl PΓ.
 intros Xj XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 Σ wfΣ Γ t T H.
 eapply typing_ind_env_app_size; eauto. clear Σ wfΣ Γ t T H.
 intros Σ wfΣ Γ wfΓ t na A B u s HΓ Hprod IHprod Ht IHt IH Hu IHu.
 pose proof (mkApps_decompose_app t).
 destruct (decompose_app t) as [t1 L].
 subst. rename t1 into t. cbn in *.
 replace (tApp (mkApps t L) u) with (mkApps t (L ++ [u])) by now rewrite mkApps_app.

 pose proof (@inversion_mkApps cf) as Happs. specialize Happs with (H := Ht).
 forward Happs; eauto.
 destruct (Happs _ Hprod) as (A' & Hf & s' & HA & sz_f & sz_A & HL).
 destruct @inversion_Prod_size with (H := Hprod) as (s1 & s2 & H1 & H2 & Hs1 & Hs2 & Hsub); [ eauto | ].
 eapply X4. 6:eauto. 4: exact HA. all: eauto.
 - intros. eapply (IH _ _ Hf). lia.
 - Unshelve. 2:exact Hf. intros. eapply (IH _ _ Ht'). lia.
 - clear sz_A. induction L in A', Hf, (* HA, sz_A, *) Ht, HL, t, Hf, IH (*, s' *) |- *.
   + inversion HL; subst. inversion X13. econstructor. econstructor; eauto. eauto. eauto. eauto. eauto. eauto.
     econstructor. 1,2: eapply isType_apply; eauto. eapply ws_cumul_pb_refl.
     eapply typing_closed_context; eauto. eapply type_is_open_term.
     eapply type_App; eauto.
   + cbn. inversion HL. subst. clear HL.
     eapply inversion_Prod in H' as Hx; eauto. destruct Hx as (? & ? & ? & ? & ?).
     econstructor.
     7: unshelve eapply IHL.
     now eauto. now eauto. split. now eauto. unshelve eapply IH. eauto. lia.
     now eauto. now eauto. split. now eauto. unshelve eapply IH. eauto. lia.
     2: now eauto. eauto.
     econstructor; eauto. econstructor; eauto. now eapply cumulAlgo_cumulSpec in X14.
     eauto.
Qed.

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pj : global_env_ext -> context -> judgment -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
         (PΓ : global_env_ext -> context -> Type),

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (* (wfΓ : wf_local Σ Γ) *) j,
        lift_typing_conj (typing Σ) (P Σ) Γ j -> Pj Σ Γ j) ->

    (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ),
        All_local_env_over (typing Σ) (Pdecl Σ) Γ wfΓ -> All_local_env (Pj Σ) Γ -> PΓ Σ Γ) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (u : sort),
        PΓ Σ Γ ->
        wf_sort Σ u ->
        P Σ Γ (tSort u) (tSort (Sort.super u))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (na : aname) (t b : term) (s1 s2 : sort),
        PΓ Σ Γ ->
        lift_typing typing Σ Γ (j_vass_s na t s1) ->
        Pj Σ Γ (j_vass_s na t s1) ->
        Σ ;;; Γ,, vass na t |- b : tSort s2 ->
        P Σ (Γ,, vass na t) b (tSort s2) -> P Σ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (na : aname) (t b bty : term),
        PΓ Σ Γ ->
        lift_typing typing Σ Γ (j_vass na t) ->
        Pj Σ Γ (j_vass na t) ->
        Σ ;;; Γ,, vass na t |- b : bty -> P Σ (Γ,, vass na t) b bty -> P Σ Γ (tLambda na t b) (tProd na t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (na : aname) (b b_ty b' b'_ty : term),
        PΓ Σ Γ ->
        lift_typing typing Σ Γ (j_vdef na b b_ty) ->
        Pj Σ Γ (j_vdef na b b_ty) ->
        Σ ;;; Γ,, vdef na b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef na b b_ty) b' b'_ty -> P Σ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) T B L s,
        PΓ Σ Γ ->
        Σ ;;; Γ |- T : tSort s -> P Σ Γ T (tSort s) ->
        forall (Ht : Σ ;;; Γ |- t : T), P Σ Γ t T ->

        (* Give a stronger induction hypothesis allowing to crawl under applications *)
        typing_spine_pred Σ Γ (fun u ty H => Σ ;;; Γ |- u : ty × P Σ Γ u ty) T L B ->

        P Σ Γ (mkApps t L) B) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
        on_global_env cumulSpec0 Pj Σ.1 ->
        PΓ Σ Γ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
        on_global_env cumulSpec0 Pj Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
        on_global_env cumulSpec0 Pj Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
    forall (ci : case_info) p c brs indices ps mdecl idecl
      (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
      on_global_env cumulSpec0 Pj Σ.1 ->
      PΓ Σ Γ ->
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
      forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
      P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
      wf_local Σ (Γ ,,, predctx) ->
      PΓ Σ (Γ ,,, predctx) ->
      is_allowed_elimination Σ idecl.(ind_kelim) ps ->
      PCUICTyping.ctx_inst (Prop_conj typing P Σ) Γ (p.(pparams) ++ indices)
        (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices) : context))) ->
      Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
      P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
      isCoFinite mdecl.(ind_finite) = false ->
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        (PΓ Σ (Γ ,,, brctxty.1) ×
          (Prop_conj typing P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
          (Prop_conj typing P) Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))) 0 idecl.(ind_ctors) brs ->
      P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        on_global_env cumulSpec0 Pj Σ.1 -> PΓ Σ Γ ->
        Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
        P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
        #|args| = ind_npars mdecl ->
        P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing typing Σ) Γ) mfix ->
        All (on_def_type (Pj Σ) Γ) mfix ->
        All (on_def_body (lift_typing typing Σ) types Γ) mfix ->
        All (on_def_body (Pj Σ) types Γ) mfix ->
        wf_fixpoint Σ.1 mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing typing Σ) Γ) mfix ->
        All (on_def_type (Pj Σ) Γ) mfix ->
        All (on_def_body (lift_typing typing Σ) types Γ) mfix ->
        All (on_def_body (Pj Σ) types Γ) mfix ->
        wf_cofixpoint Σ.1 mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->


    (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : prim_val) prim_ty cdecl,
      PΓ Σ Γ ->
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants (prim_val_tag p) cdecl ->
      primitive_typing_hyps typing Σ Γ p ->
      primitive_typing_hyps P Σ Γ p ->
      P Σ Γ (tPrim p) (prim_type p prim_ty)) ->


    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) s,
        PΓ Σ Γ ->
        Σ ;;; Γ |- t : A ->
        P Σ Γ t A ->
        Σ ;;; Γ |- B : tSort s ->
        P Σ Γ B (tSort s) ->
        Σ ;;; Γ |- A <=s B ->
        P Σ Γ t B) ->

       env_prop P Pj PΓ.
Proof.
  intros P Pdecl PΓ; unfold env_prop.
  intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  apply typing_ind_env_app_size; eauto.
Qed.

Local Hint Constructors value wcbv_red1 : wcbv.

Lemma value_stuck_fix Σ mfix idx args : isStuckFix (tFix mfix idx) args -> All (value Σ) args -> value Σ (mkApps (tFix mfix idx) args).
Proof.
  unfold isStuckFix; intros isstuck vargs.
  eapply value_app => //.
  destruct cunfold_fix as [[rarg fn]|] eqn:cunf => //.
  econstructor; tea. now eapply Nat.leb_le.
Qed.

Lemma typing_spine_length {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ ind u args args' T' :
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
  #|args'| <= context_assumptions Δ.
Proof.
  intros hsp.
  pose proof (typing_spine_more_inv _ _ _ _ _ _ _ _ hsp).
  destruct (Compare_dec.le_dec #|args'| (context_assumptions Δ)). lia. lia.
Qed.

Lemma declared_constructor_ind_decl {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind c} {mdecl idecl cdecl} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  inductive_ind ind < #|ind_bodies mdecl|.
Proof.
  intros [[hm hi] hc]. now eapply nth_error_Some_length in hi.
Qed.

Import PCUICGlobalEnv.

Lemma typing_constructor_arity_exact {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind c u u' args}
  {mdecl idecl cdecl indices} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  Σ ;;; [] |- mkApps (tConstruct ind c u) args : mkApps (tInd ind u') indices ->
  #|args| = cstr_arity mdecl cdecl.
Proof.
  intros declc hc.
  eapply Construct_Ind_ind_eq in hc; tea.
  intuition auto.
Qed.

Lemma typing_constructor_arity {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind c u args T} {mdecl idecl cdecl} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  Σ ;;; [] |- mkApps (tConstruct ind c u) args : T ->
  #|args| <= cstr_arity mdecl cdecl.
Proof.
  intros declc hc.
  pose proof (validity hc).
  eapply PCUICSpine.inversion_mkApps_direct in hc as [A' [u' [s' [hs hsp]]]]; eauto.
  eapply inversion_Construct in s' as [mdecl' [idecl' [cdecl' [wf [declc' [cu cum]]]]]]; tea.
  unshelve epose proof (declc_ := declared_constructor_to_gen declc); eauto.
  unshelve epose proof (declc'_ := declared_constructor_to_gen declc'); eauto.
  destruct (PCUICGlobalEnv.declared_constructor_inj declc_ declc'_) as [? []]. subst mdecl' idecl' cdecl'.
  clear declc'.
  eapply typing_spine_strengthen in hsp. 3:exact cum.
  2:{ eapply validity. econstructor; tea. }
  unfold type_of_constructor in hsp.
  destruct (on_declared_constructor declc) as [[] [cunivs [_ onc]]].
  rewrite onc.(cstr_eq) in hsp.
  rewrite <-it_mkProd_or_LetIn_app in hsp.
  rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn in hsp.
  epose proof (subst_cstr_concl_head ind u mdecl (cstr_args cdecl) (cstr_indices cdecl)). cbn in H.
  unfold cstr_concl in hsp. cbn in hsp. len in hsp. rewrite H in hsp. clear H.
  eapply (declared_constructor_ind_decl declc). clear H.
  eapply typing_spine_length in hsp. len in hsp. unfold cstr_arity.
  now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars declc).
Qed.

Lemma value_mkApps_inv' Σ f args :
  negb (isApp f) ->
  value Σ (mkApps f args) ->
  atomic_value (value Σ) f × All (value Σ) args.
Proof.
  intros napp. move/value_mkApps_inv => [] => //.
  - intros [-> hf]. split => //.
  - intros []. split; auto. destruct v; now constructor.
Qed.

Global Hint Resolve All_app_inv : pcuic.

Lemma wcbv_red1_mkApps_left {Σ f f' args} : Σ ⊢ f ⇝ᵥ f' -> Σ ⊢ mkApps f args ⇝ᵥ mkApps f' args.
Proof.
  induction args using rev_ind.
  - auto.
  - intros. rewrite !mkApps_app.
    eapply wcbv_red_app_left. now apply IHargs.
Qed.

Lemma typing_spine_sort {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ s args T :
  typing_spine Σ Γ (tSort s) args T -> args = [].
Proof.
  induction args => //.
  intros sp. depelim sp.
  now eapply ws_cumul_pb_Sort_Prod_inv in w.
Qed.

Lemma typing_spine_axiom {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ cst u cdecl args args' T :
  declared_constant Σ cst cdecl ->
  cdecl.(cst_body) = None ->
  typing_spine Σ Γ (mkApps (tConst cst u) args) args' T -> args' = [].
Proof.
  intros hdecl hb.
  induction args' => //.
  intros sp. depelim sp.
  now eapply invert_cumul_axiom_prod in w.
Qed.

Lemma typing_spine_prim_type {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ prim prim_ty cdecl args T :
  declared_constant Σ prim_ty cdecl ->
  primitive_invariants (prim_val_tag prim) cdecl ->
  typing_spine Σ Γ (prim_type prim prim_ty) args T -> args = [].
Proof.
  intros hdecl hb.
  induction args => //.
  destruct prim as [? []]; cbn in *; intros sp; destruct hb; simp prim_type in *.
  1-3:eapply (typing_spine_axiom _ _ _ _ []) in sp; tea.
  eapply (typing_spine_axiom _ _ _ _ [array_type a0]) in sp; tea.
Qed.

Lemma typing_value_head_napp {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} fn args hd T :
  negb (isApp fn) ->
  Σ ;;; [] |- mkApps fn (args ++ [hd]) : T ->
  value Σ hd -> closed hd ->
  value Σ (mkApps fn args) ->
  (∑ t' : term, Σ ⊢ mkApps fn (args ++ [hd]) ⇝ᵥ t') +
  value Σ (mkApps fn (args ++ [hd])).
Proof.
  intros napp ht vhd clhd vapp.
  pose proof ht as ht'.
  destruct (value_mkApps_inv' _ _ _ napp vapp).
  eapply PCUICSpine.inversion_mkApps_direct in ht' as [A' [u [hfn [hhd hcum]]]]; tea.
  2:{ now eapply validity. }
  destruct fn => //; try depelim a; cbn in * => //.
  * eapply inversion_Sort in hfn as [? [? cu]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity; econstructor; eauto. }
    now eapply typing_spine_sort, app_tip_nil in hcum.
  * eapply inversion_Prod in hfn as [? [? [? [? cu]]]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity. econstructor; eauto. }
    now eapply typing_spine_sort, app_tip_nil in hcum.
  * (* Lambda *) left. destruct args.
    - cbn. eexists. now eapply wcbv_red_beta.
    - eexists. rewrite mkApps_app. rewrite (mkApps_app _ [t] args). do 2 eapply wcbv_red1_mkApps_left.
      cbn. eapply wcbv_red_beta. now depelim a0.
  * (* Inductive *)
    eapply inversion_Ind in hfn as [? [? [? [? [? cu]]]]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity. econstructor; eauto. }
    right. eapply value_app. constructor. eauto with pcuic.
  * (* constructor *)
    right. eapply value_app; auto. 2:{ eapply All_app_inv; eauto. }
    pose proof hfn as hfn'.
    eapply inversion_Construct in hfn' as [mdecl [idecl [cdecl [wf [declc _]]]]]; tea.
    eapply (typing_constructor_arity declc) in ht.
    econstructor; tea. unshelve eapply declared_constructor_to_gen; eauto.
  * (* fix *)
    destruct (isStuckFix (tFix mfix idx) (args ++ [hd])) eqn:E.
    + right. eapply value_stuck_fix; eauto with pcuic.
    + cbn in E.
      eapply inversion_Fix in hfn as ([] & ? & Efix & ? & ? & ?); eauto.
      unfold cunfold_fix in E. rewrite Efix in E. cbn in E.
      len in E. cbn in E. assert (rarg = #|args|).
      eapply stuck_fix_value_args in vapp; tea. 2:{ unfold cunfold_fix. now rewrite Efix. }
      cbn in vapp. apply Nat.leb_gt in E. lia. subst rarg.
      left. eexists. rewrite mkApps_app /=. eapply wcbv_red_fix. eauto. eauto.
      unfold unfold_fix. now rewrite Efix.
      eapply fix_app_is_constructor in ht.
      2:{ unfold unfold_fix. now rewrite Efix. }
      cbn in ht. rewrite nth_error_app_ge // /= in ht.
      replace (#|args| - #|args|) with 0 in ht by lia. cbn in ht. apply ht.
      eapply value_axiom_free; eauto.
      eapply value_whnf; eauto.
  * (* cofix *)
    right. eapply value_app; eauto with pcuic.
    now constructor.
  * (* primitive *)
    cbn.
    eapply inversion_Prim in hfn as [prim_ty [cdecl [hwf hp hdecl hinv hty hcum']]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity; econstructor; eauto. }
    now eapply typing_spine_prim_type, app_tip_nil in hcum.
Qed.

Lemma typing_value_head {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} fn args hd T :
  Σ ;;; [] |- mkApps fn (args ++ [hd]) : T ->
  value Σ hd -> closed hd ->
  value Σ (mkApps fn args) ->
  (∑ t' : term, Σ ⊢ mkApps fn (args ++ [hd]) ⇝ᵥ t') +
  value Σ (mkApps fn (args ++ [hd])).
Proof.
  destruct (decompose_app fn) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  rewrite (decompose_app_inv da).
  rewrite -mkApps_app app_assoc.
  intros; eapply typing_value_head_napp; tea. now rewrite H.
  rewrite mkApps_app //.
Qed.

Lemma cstr_branch_context_assumptions ci mdecl cdecl :
  context_assumptions (cstr_branch_context ci mdecl cdecl) =
  context_assumptions (cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context /PCUICEnvironment.expand_lets_ctx
    /PCUICEnvironment.expand_lets_k_ctx.
  now do 2 rewrite !context_assumptions_subst_context ?context_assumptions_lift_context.
Qed.

#[global] Hint Constructors atomic_value : wcbv.

Lemma All_or_disj {A} (P Q : A -> Type) l : All (fun x => P x + Q x)%type l ->
  (∑ n v, All Q (firstn n l) × (nth_error l n = Some v × P v)) + All Q l.
Proof.
  induction 1.
  - right; auto.
  - destruct IHX.
    * destruct s as [n [v [? []]]].
      destruct p.
      + left. exists 0, x; intuition auto.
      + left. exists (S n), v; intuition cbn; auto.
    * destruct p.
      + left. exists 0, x; intuition auto.
      + right; eauto.
Qed.

Lemma progress_env_prop `{cf : checker_flags}:
  env_prop (fun Σ Γ t T => axiom_free Σ -> Γ = [] -> Σ ;;; Γ |- t : T -> {t' & Σ ⊢ t ⇝ᵥ t'} + (value Σ t))
           (fun Σ Γ j => axiom_free Σ -> Γ = [] -> lift_typing0 (fun t T => Σ ;;; Γ |- t : T -> {t' & Σ ⊢ t ⇝ᵥ t'} + (value Σ t)) j)
           (fun _ _ => True).
Proof with eauto with wcbv; try congruence.
  eapply typing_ind_env...
  - intros Σ wfΣ Γ j Hj Hax eq.
    apply lift_typing_impl with (1 := Hj) => ?? [] // H IH //. now apply IH.
  - intros Σ wfΣ Γ wfΓ n decl Hdecl _ Hax -> Hty.
    destruct n; inv Hdecl.
  - intros Σ wfΣ Γ _ n b b_ty b' b'_ty _ Hb IHb Hb' IHb' Hax -> H.
    specialize (IHb Hax eq_refl).
    apply unlift_TermTyp in Hb, IHb as [ [t' IH] | IH]; eauto with wcbv.
  - intros Σ wfΣ Γ _ t T B L s _ HT IHT Ht IHt HL Hax -> H.
    clear HT IHT.
    induction HL in H, t, Ht, IHt |- *.
    + cbn. eauto.
    + cbn. eapply IHHL.
      2:{ do 2 (econstructor; eauto). now eapply cumulAlgo_cumulSpec in w. }
      intros _ Happ.
      destruct (IHt Hax eq_refl Ht) as [[t' IH] | IH]; eauto with wcbv.
      assert (Ht' : Σ ;;; [] |- t : tProd na A B) by (econstructor; eauto; now eapply cumulAlgo_cumulSpec in w).
      destruct p0 as [_ [[t' Hstep] | Hval]]; eauto using wcbv_red1.
      intros htapp.
      pose proof (typing_value_head t [] hd _ htapp Hval).
      forward X. now eapply subject_closed in H0. cbn in X.
      specialize (X IH). exact X.
      now cbn in H.
  - intros Σ wf Γ _ cst u decl Hdecls _ Hdecl Hcons Hax -> H.
    destruct (decl.(cst_body)) as [body | ] eqn:E.
    + eauto with wcbv.
    + red in Hax. eapply Hax in E; eauto.
  - intros Σ wfΣ Γ _ ci p c brs indices ps mdecl idecl Hidecl Hforall _ Heq Heq_context predctx Hwfpred Hcon Hreturn IHreturn Hwfl _.
    intros Helim Hctxinst Hc IHc Hcof ptm Hwfbranches Hall Hax -> H.
    specialize (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv.
    pose proof IH as IHv.
    eapply value_classification in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc, IHv |- *.
    destruct (decompose_app c) as [h l].
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + eapply invert_Case_Construct in H as H_; sq; eauto. destruct H_ as (Eq & H_); subst.
      left.
      destruct (nth_error brs n) as [br | ] eqn:E.
      2:{ exfalso. destruct H_ as [? []]; congruence. }
      assert (#|l| = ci_npar ci + context_assumptions (bcontext br)) as Hl.
      { destruct H_ as [? []]; auto. now noconf H0. }
      clear H_. eapply Construct_Ind_ind_eq' in Hc as (? & ? & ? & ? & _); eauto.
      eexists.
      unshelve epose proof (d_ := declared_constructor_to_gen d); eauto.
      unshelve epose proof (Hidecl_ := declared_inductive_to_gen Hidecl); eauto.
      destruct (declared_inductive_inj d_ Hidecl_); subst x x0.
      eapply All2i_nth_error in Hall as [eqctx _]; tea; [|eapply d].
      eapply PCUICCasesContexts.alpha_eq_context_assumptions in eqctx.
      rewrite cstr_branch_context_assumptions in eqctx.
      eapply wcbv_red_iota; eauto.
      { rewrite /cstr_arity Hl. rewrite -Heq. lia. }
      eapply value_mkApps_inv in IHv as [[-> ]|[]]; eauto.

    + eapply inversion_Case in H as (? & ? & ? & ? & [] & ?); eauto.
      eapply PCUICValidity.inversion_mkApps in scrut_ty as (? & ? & ?); eauto.
      eapply inversion_CoFix in t as (? & ? & ? & ? & ? & ? & ?); eauto.
      left. eexists. eapply wcbv_red_cofix_case. unfold cunfold_cofix. rewrite e. reflexivity.
      eapply value_mkApps_inv in IHv as [[-> ]|[]]; eauto.
  - intros Σ wfΣ Γ _ p c u mdecl idecl cdecl pdecl Hcon args Hargs _ Hc IHc
           Hlen Hax -> H.
    destruct (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv; clear IHc.
    pose proof IH as Hval.
    eapply value_classification in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc, Hval |- *.
    destruct (decompose_app c) as [h l].
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + eapply invert_Proj_Construct in H as H_; sq; eauto. destruct H_ as (<- & -> & Hl).
      left. eapply nth_error_Some' in Hl as [x Hx].
      eexists.
      eapply wcbv_red_proj; eauto.
      unshelve eapply declared_projection_to_gen; eauto.
      now eapply (typing_constructor_arity_exact Hcon) in Hc.
      eapply value_mkApps_inv in Hval as [[-> Hval] | [? ? Hval]]; eauto.
    + left. eapply inversion_Proj in H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      eapply PCUICValidity.inversion_mkApps in t as (? & ? & ?); eauto.
      eapply inversion_CoFix in t as (? & ? & ? & ? & ? & ? & ?); eauto.
      eexists. eapply wcbv_red_cofix_proj. unfold cunfold_cofix. rewrite e0. reflexivity.
      eapply value_mkApps_inv in Hval as [[-> ]|[]]; eauto.
  - intros Σ wfΣ Γ _ p c u mdecl idecl cdecl pdecl Hcon args Hargs -> hp.
    depelim args... 1-2:right; constructor; constructor 2; constructor.
    right. constructor. constructor 2. constructor.
    depelim Hcon.
    destruct hdef; eauto.
    + left. destruct s as [t' hred]. exists (tPrim (prim_array (set_array_default a t'))). now constructor.
    + destruct a as []; cbn in *.
      clear hty.
      solve_all. clear -hvalue0 Hargs v.
      set (a := {| array_universe := _ |}).
      assert (All (fun x : term => ((∑ t' : term, Σ ⊢ x ⇝ᵥ t') + value Σ x))%type array_value).
      { solve_all. } clear hvalue0 Hargs.
      eapply All_or_disj in X as [].
      * destruct s as [n [v' [? []]]]. destruct s as [t' ht'].
        left. exists (tPrim (prim_array (set_array_value a (firstn n array_value ++ t' :: skipn (S n) array_value)))).
        econstructor; eauto.
      * right. constructor. constructor 2. constructor; eauto.
Qed.

Lemma progress `{cf : checker_flags}:
  forall (Σ:global_env_ext) t T,
    axiom_free Σ -> wf Σ ->
    Σ ;;; [] |- t : T ->
    {t' & Σ ⊢ t ⇝ᵥ t'} + (value Σ t).
Proof.
  intros.
  edestruct progress_env_prop as [_ [_ [[t' Ht'] | Hval]]]; eauto.
Defined.

Notation "¬ A" := (A -> False) (at level 50).

Lemma whnf_progress `{cf : checker_flags}:
  forall (Σ:global_env_ext) t T,
    axiom_free Σ -> wf Σ ->
    Σ ;;; [] |- t : T ->
    ¬ { t' & Σ ;;; [] |- t ⇝ t' } ->
    whnf RedFlags.default Σ [] t.
Proof.
  intros.
  edestruct progress_env_prop as [_ [_ [[t' Ht'] | Hval]]]; eauto.
  eapply wcbv_red1_red1 in Ht'.
  exfalso; apply H0. eexists; eauto.
  eapply subject_closed in X0; eauto.
  eapply value_whnf in Hval. eauto.
  eapply subject_closed in X0; eauto.
Qed.

Lemma classification : forall (Σ:global_env_ext) t i u args,
  axiom_free Σ -> wf Σ ->
  ¬ { t' & Σ ;;; [] |- t ⇝ t'} ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  construct_cofix_discr (head t).
Proof.
  intros; eapply whnf_classification; eauto.
  eapply whnf_progress; eauto.
Qed.



