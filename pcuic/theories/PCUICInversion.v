(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICCases PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICCumulativity PCUICConfluence PCUICConversion
     PCUICOnFreeVars PCUICClosedTyp PCUICWellScopedCumulativity.

From Equations.Prop Require Import DepElim.
(* TODO: make wf arguments implicit *)
Section Inversion.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  Lemma into_ws_cumul {Γ t T U s} :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ |- U : tSort s ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Γ ⊢ T ≤ U.
  Proof using wfΣ.
    intros. eapply into_ws_cumul_pb; tea.
    - eapply typing_wf_local in X; eauto with fvs.
    - eapply PCUICClosedTyp.type_closed in X.
      eapply PCUICOnFreeVars.closedn_on_free_vars in X; tea.
    - eapply PCUICClosedTyp.subject_closed in X0.
      eapply PCUICOnFreeVars.closedn_on_free_vars in X0; tea.
  Qed.

  Lemma typing_closed_ctx Γ t T :
    Σ ;;; Γ |- t : T ->
    is_closed_context Γ.
  Proof using wfΣ.
    move/typing_wf_local; eauto with fvs.
  Qed.
  Hint Immediate typing_closed_ctx : fvs.

  Lemma typing_ws_cumul_pb le Γ t T :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ ⊢ T ≤[le] T.
  Proof using wfΣ.
    intros ht. apply into_ws_cumul_pb; auto. destruct le ; reflexivity.
    eauto with fvs.
    eapply PCUICClosedTyp.type_closed in ht.
    now rewrite -is_open_term_closed.
    eapply PCUICClosedTyp.type_closed in ht.
    now rewrite -is_open_term_closed.
  Qed.
  Hint Immediate typing_closed_ctx : fvs.

  Ltac invtac h :=
    dependent induction h ; [
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | try reflexivity ] .. | try solve [eapply typing_ws_cumul_pb; econstructor; eauto] ]
    | repeat outsum ;
      repeat outtimes ;
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | reflexivity ] ..
      | try etransitivity ; try eassumption;
        try eauto with pcuic;
        try solve [eapply into_ws_cumul; tea] ]
    ].

  Derive Signature for typing.

  Import PCUICClosed PCUICOnFreeVars.

  Lemma nth_error_closed_context {Γ n d} :
    is_closed_context Γ ->
    nth_error Γ n = Some d ->
    is_open_term Γ (lift0 (S n) (decl_type d)).
  Proof using Type.
    intros isc hnth.
    rewrite -on_free_vars_ctx_on_ctx_free_vars in isc.
    rewrite <- (addnP0) in isc.
    eapply nth_error_on_free_vars_ctx in isc; tea.
    2:{ rewrite /shiftnP orb_false_r. eapply Nat.ltb_lt.
        eapply nth_error_Some_length in hnth. lia. }
    now move/andP: isc=> [] _ /on_free_vars_lift0 /=.
  Qed.

  Lemma inversion_Rel :
    forall {Γ n T},
      Σ ;;; Γ |- tRel n : T ->
      ∑ decl,
        wf_local Σ Γ ×
        (nth_error Γ n = Some decl) ×
        Σ ;;; Γ ⊢ lift0 (S n) (decl_type decl) ≤ T.
  Proof using wfΣ.
    intros Γ n T h. invtac h.
  Qed.

  Lemma inversion_Var :
    forall {Γ i T},
      Σ ;;; Γ |- tVar i : T -> False.
  Proof using Type.
    intros Γ i T h. dependent induction h. assumption.
  Qed.

  Lemma inversion_Evar :
    forall {Γ n l T},
      Σ ;;; Γ |- tEvar n l : T -> False.
  Proof using Type.
    intros Γ n l T h. dependent induction h. assumption.
  Qed.

  Lemma inversion_Sort :
    forall {Γ s T},
      Σ ;;; Γ |- tSort s : T ->
      wf_local Σ Γ ×
      wf_sort Σ s ×
      Σ ;;; Γ ⊢ tSort (Sort.super s) ≤ T.
  Proof using wfΣ.
    intros Γ s T h. invtac h.
  Qed.

  Lemma inversion_Prod :
    forall {Γ na A B T},
      Σ ;;; Γ |- tProd na A B : T ->
      ∑ s1 s2,
        lift_typing typing Σ Γ (j_vass_s na A s1) ×
        Σ ;;; Γ ,, vass na A |- B : tSort s2 ×
        Σ ;;; Γ ⊢ tSort (Sort.sort_of_product s1 s2) ≤ T.
  Proof using wfΣ.
    intros Γ na A B T h. invtac h.
  Qed.

  Lemma inversion_Prod_size :
    forall {Γ na A B T},
      forall H : Σ ;;; Γ |- tProd na A B : T,
      ∑ s1 s2 (H1 : lift_typing typing Σ Γ (j_vass_s na A s1)) (H2 : Σ ;;; Γ ,, vass na A |- B : tSort s2),
        lift_typing_size (@typing_size _ _ _) _ H1 < typing_size H × typing_size H2 < typing_size H ×
        Σ ;;; Γ ⊢ tSort (Sort.sort_of_product s1 s2) ≤ T.
  Proof using wfΣ.
    intros Γ na A B T h. unshelve invtac h; eauto.
    all: try revert l; try revert l0; simpl; cbn; lia.
  Qed.

  Lemma inversion_Lambda :
    forall {Γ na A t T},
      Σ ;;; Γ |- tLambda na A t : T ->
      ∑ B,
        lift_typing typing Σ Γ (j_vass na A) ×
        Σ ;;; Γ ,, vass na A |- t : B ×
        Σ ;;; Γ ⊢ tProd na A B ≤ T.
  Proof using wfΣ.
    intros Γ na A t T h. invtac h.
  Qed.

  Lemma inversion_LetIn :
    forall {Γ na b B t T},
      Σ ;;; Γ |- tLetIn na b B t : T ->
      ∑ A,
        lift_typing typing Σ Γ (j_vdef na b B) ×
        Σ ;;; Γ ,, vdef na b B |- t : A ×
        Σ ;;; Γ ⊢ tLetIn na b B A ≤ T.
  Proof using wfΣ.
    intros Γ na b B t T h. invtac h.
  Qed.

  Lemma inversion_App :
    forall {Γ u v T},
      Σ ;;; Γ |- tApp u v : T ->
      ∑ na A B,
        Σ ;;; Γ |- u : tProd na A B ×
        Σ ;;; Γ |- v : A ×
        Σ ;;; Γ ⊢ B{ 0 := v } ≤ T.
  Proof using wfΣ.
    intros Γ u v T h. invtac h.
  Qed.

  Lemma inversion_App_size :
  forall {Γ u v T}
      (H : Σ ;;; Γ |- tApp u v : T),
      ∑ na A B s  (H1 : Σ ;;; Γ |- u : tProd na A B) (H2 : Σ ;;; Γ |- v : A) (H3 : Σ ;;; Γ |- tProd na A B : tSort s),
      typing_size H1 < typing_size H × typing_size H2 < typing_size H × typing_size H3 < typing_size H ×
        Σ ;;; Γ ⊢ B{ 0 := v } ≤ T.
  Proof using wfΣ.
    intros Γ u v T h. unshelve invtac h.
    4,5,6,10,11,12: eauto.
    all: unfold typing_size at 2; fold (typing_size h1); fold (typing_size h2); try fold (typing_size h3); lia.
  Qed.

  Lemma inversion_Const :
    forall {Γ c u T},
      Σ ;;; Γ |- tConst c u : T ->
      ∑ decl,
        wf_local Σ Γ ×
        declared_constant Σ c decl ×
        (consistent_instance_ext Σ decl.(cst_universes) u) ×
        Σ ;;; Γ ⊢ subst_instance u (cst_type decl) ≤ T.
  Proof using wfΣ.
    intros Γ c u T h. invtac h.
  Qed.

  Lemma inversion_Ind :
    forall {Γ ind u T},
      Σ ;;; Γ |- tInd ind u : T ->
      ∑ mdecl idecl,
        wf_local Σ Γ ×
        declared_inductive Σ ind mdecl idecl ×
        consistent_instance_ext Σ (ind_universes mdecl) u ×
        Σ ;;; Γ ⊢ subst_instance u idecl.(ind_type) ≤ T.
  Proof using wfΣ.
    intros Γ ind u T h. invtac h.
  Qed.

  Lemma inversion_Construct :
    forall {Γ ind i u T},
      Σ ;;; Γ |- tConstruct ind i u : T ->
      ∑ mdecl idecl cdecl,
        wf_local Σ Γ ×
        declared_constructor (fst Σ) (ind, i) mdecl idecl cdecl ×
        consistent_instance_ext Σ (ind_universes mdecl) u ×
        Σ;;; Γ ⊢ type_of_constructor mdecl cdecl (ind, i) u ≤ T.
  Proof using wfΣ.
    intros Γ ind i u T h. invtac h.
  Qed.
  Import PCUICEquality.
  Variant case_inversion_data Γ ci p c brs mdecl idecl indices :=
   | case_inv
       (ps : sort)
       (eq_npars : mdecl.(ind_npars) = ci.(ci_npar))
       (predctx := case_predicate_context ci.(ci_ind) mdecl idecl p)
       (wf_pred : wf_predicate mdecl idecl p)
       (cons : consistent_instance_ext Σ (ind_universes mdecl) p.(puinst))
       (wf_pctx : wf_local Σ (Γ ,,, predctx))
       (conv_pctx : eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl))
       (pret_ty : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps)
       (allowed_elim : is_allowed_elimination Σ idecl.(ind_kelim) ps)
       (elim_relevance : isSortRel ps ci.(ci_relevance))
       (ind_inst : ctx_inst (typing Σ) Γ (p.(pparams) ++ indices)
                            (List.rev (subst_instance p.(puinst)
                                                      (ind_params mdecl ,,, ind_indices idecl : context))))
       (scrut_ty : Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices))
       (not_cofinite : isCoFinite mdecl.(ind_finite) = false)
       (ptm := it_mkLambda_or_LetIn predctx p.(preturn))
       (wf_brs : wf_branches idecl brs)
       (brs_ty :
          All2i (fun i cdecl br =>
                   eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
                   let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
                   (wf_local Σ (Γ ,,, brctxty.1) ×
                   ((Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2) ×
                    (Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps))))
                0 idecl.(ind_ctors) brs).

  Lemma inversion_Case :
    forall {Γ ci p c brs T},
      Σ ;;; Γ |- tCase ci p c brs : T ->
      ∑ mdecl idecl (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl) indices,
        let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
        let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
        case_inversion_data Γ ci p c brs mdecl idecl indices ×
        Σ ;;; Γ ⊢ mkApps ptm (indices ++ [c]) ≤ T.
  Proof using wfΣ.
    intros Γ ci p c brs T h.
    dependent induction h.
    {  remember c0; remember c1. destruct c0, c1. repeat insum; repeat intimes; try eapply case_inv ;
	    [ try first [ eassumption | reflexivity ].. | try eapply typing_ws_cumul_pb; econstructor; eauto ]. }
    repeat outsum; repeat outtimes; repeat insum; repeat intimes ; tea;
      [ try first
      [ eassumption | reflexivity ]..
      | try etransitivity; try eassumption; eapply into_ws_cumul; tea; eauto with pcuic ].
  Qed.

  Lemma inversion_Proj :
    forall {Γ p c T},
      Σ ;;; Γ |- tProj p c : T ->
      ∑ u mdecl idecl cdecl pdecl args,
        declared_projection Σ p mdecl idecl cdecl pdecl ×
        Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ×
        #|args| = ind_npars mdecl ×
        Σ ;;; Γ ⊢ (subst0 (c :: List.rev args)) pdecl.(proj_type)@[u] ≤ T.
  Proof using wfΣ.
    intros Γ p c T h. invtac h.
  Qed.

  Lemma inversion_Fix :
    forall {Γ mfix n T},
      Σ ;;; Γ |- tFix mfix n : T ->
      ∑ decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ×
        nth_error mfix n = Some decl ×
        All (on_def_type (lift_typing typing Σ) Γ) mfix ×
        All (on_def_body (lift_typing typing Σ) (fix_context mfix) Γ) mfix ×
        wf_fixpoint Σ mfix ×
        Σ ;;; Γ ⊢ dtype decl ≤ T.
  Proof using wfΣ.
    intros Γ mfix n T h. invtac h.
  Qed.

  Lemma inversion_CoFix :
    forall {Γ mfix idx T},
      Σ ;;; Γ |- tCoFix mfix idx : T ->
      ∑ decl,
        cofix_guard Σ Γ mfix ×
        let types := fix_context mfix in
        nth_error mfix idx = Some decl ×
        All (on_def_type (lift_typing typing Σ) Γ) mfix ×
        All (on_def_body (lift_typing typing Σ) (fix_context mfix) Γ) mfix ×
        wf_cofixpoint Σ mfix ×
        Σ ;;; Γ ⊢ decl.(dtype) ≤ T.
  Proof using wfΣ.
    intros Γ mfix idx T h. invtac h.
  Qed.

  Lemma inversion_Prim :
    forall {Γ p T},
    Σ ;;; Γ |- tPrim p : T ->
    ∑ prim_ty cdecl,
      [× wf_local Σ Γ,
        primitive_constant Σ (prim_val_tag p) = Some prim_ty,
        declared_constant Σ prim_ty cdecl,
        primitive_invariants (prim_val_tag p) cdecl,
        primitive_typing_hyps (typing Σ) Σ Γ p &
        Σ ;;; Γ ⊢ prim_type p prim_ty ≤ T].
  Proof.
    intros Γ p T h. depind h.
    - exists prim_ty, cdecl; split => //.
      eapply ws_cumul_pb_refl; fvs.
      depelim p1 => //=; simp prim_type => //=. fvs.
    - destruct IHh1 as [prim_ty [cdecl []]].
      exists prim_ty, cdecl. split => //.
      transitivity A; tea. eapply cumulSpec_cumulAlgo_curry; tea; fvs.
  Qed.

  Lemma inversion_it_mkLambda_or_LetIn :
    forall {Γ Δ t T},
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : T ->
      ∑ A,
        Σ ;;; Γ ,,, Δ |- t : A ×
        Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ A ≤ T.
  Proof using wfΣ.
    intros Γ Δ t T h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - eexists. split ; eauto. cbn.
      eapply into_ws_cumul_pb; [reflexivity|..].
      eauto with fvs.
      eapply type_closed in h.
      now eapply closedn_on_free_vars in h.
      eapply type_closed in h.
      now eapply closedn_on_free_vars in h.
    - simpl. apply ih in h. cbn in h.
      destruct h as [B [h c]].
      apply inversion_LetIn in h as hh.
      destruct hh as (A' & wfA' & Ht & hlt).
      exists A'. split ; eauto.
      cbn. etransitivity; tea.
      eapply ws_cumul_pb_it_mkProd_or_LetIn_codom.
      assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [B [h c]].
      apply inversion_Lambda in h as hh.
      pose proof hh as (B' & wfB' & Ht & hlt).
      exists B'. split ; eauto.
      cbn. etransitivity; tea.
      eapply ws_cumul_pb_it_mkProd_or_LetIn_codom.
      assumption.
  Qed.

End Inversion.
