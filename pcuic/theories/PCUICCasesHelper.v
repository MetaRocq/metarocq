From Stdlib Require Import ssreflect ssrbool ssrfun.
Set Warnings "-notation-overridden".
From MetaRocq.Utils Require Import utils monad_utils.
Set Warnings "notation-overridden".
From MetaRocq.Common Require Import config.

From MetaRocq.PCUIC Require Import PCUICTyping PCUICArities PCUICInductives PCUICSpine
  PCUICWeakeningTyp PCUICUnivSubstitutionConv PCUICValidity PCUICGeneration
  PCUICAst PCUICPrimitive PCUICCases PCUICProgram
  PCUICSubstitution PCUICConversion PCUICInductiveInversion
  PCUICContextSubst PCUICOnFreeVars PCUICSR PCUICTactics PCUICClosed.

From Equations Require Import Equations.


Definition make_case_pred (ind : inductive) (mib : mutual_inductive_body) (oib : one_inductive_body) (pparams : list term) (puinst : Instance.t) (rettyp : term) : predicate term :=
  (* let pnames := {| binder_name := nNamed (ind_name oib); binder_relevance := oib.(ind_relevance) |} :: forget_types oib.(ind_indices) in *)
  {| pparams := pparams; puinst := puinst
  ;  pcontext := ind_predicate_context ind mib oib
   (* pre_case_predicate_context_gen ind mib oib pparams puinst *)
  ;  preturn := rettyp |}.

Definition make_br ind mib (* pparams puinst *) cdecl t :=
  (* let bnames := forget_types cdecl.(cstr_args) in *)
  {| bcontext := cstr_branch_context ind mib cdecl ;
  (* case_branch_context_gen ind mib pparams puinst bnames cdecl; *)
   bbody := t |}.

Definition make_case (ind : inductive) (mib : mutual_inductive_body) (oib : one_inductive_body) (pparams : list term) (puinst : Instance.t) (discr : term) (rettyp : term) (brs : list term) :=
  let ci := {| ci_ind := ind; ci_npar := mib.(ind_npars); ci_relevance := oib.(ind_relevance) |} in
  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let brs := map2 (make_br ind mib (*pparams puinst *)) oib.(ind_ctors) brs in
  tCase ci p discr brs.


(* Sets the definition of let-bindings in the hypotheses context *)
(* Problem with folding of terms that mention another term being set *)
Ltac let_to_set t :=
  let h := eval cbv beta in t in
  match h with
  | let x := ?u in @?v x => set x := u ; let_to_set (v x)
  | _ => idtac
  end.


Lemma forget_types_inst_case_context pparams puinst Γ:
  forget_types (inst_case_context pparams puinst Γ) = forget_types Γ.
Proof.
  rewrite /inst_case_context /subst_context forget_types_fold_context_k forget_types_subst_instance //.
Qed.

Lemma weakening0 {cf : checker_flags} Σ Γ t T :
  wf Σ.1 -> wf_local Σ Γ ->
  Σ ;;; [] |- t : T -> Σ ;;; Γ |- lift0 #|Γ| t : lift0 #|Γ| T.
Proof.
  rewrite -{1 2}[Γ]app_context_nil_l; apply: weakening.
Qed.

Arguments weakening0 {_ _} _ {_ _ _ _} _.


(* Unused *)
Lemma weakening_type_local_ctx {cf:checker_flags} Σ Γ Δ Δ' ctxs :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ) ->
  type_local_ctx (lift_typing typing) Σ Γ Δ' ctxs ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Δ) (lift_context #|Δ| 0 Δ') ctxs.
Proof.
  induction Δ'; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + simpl; rewrite PCUICLiftSubst.lift_context_snoc /= Nat.add_0_r;
    split; tas.
    apply lift_typing_f_impl with (1 := b0) => // ?? Hs.
    now eapply weakening_typing in Hs.
  + rewrite PCUICLiftSubst.lift_context_snoc /= Nat.add_0_r.
    split; tas.
    apply lift_typing_f_impl with (1 := b) => // ?? Hs.
    now eapply weakening_typing in Hs.
Qed.

Lemma wf_local_expand_lets0 {cf : checker_flags} {Σ : global_env_ext} :
  wf Σ ->
  forall Δ Γ : context,
  wf_local Σ (Δ,,, Γ) ->
  wf_local Σ (smash_context [] Δ,,, expand_lets_ctx Δ Γ).
Proof.
  move=> ? Δ ?.
  rewrite -{1}[Δ]app_context_nil_l -{1}[smash_context _ _]app_context_nil_l.
  apply: wf_local_expand_lets.
Qed.

Lemma map_lift_map_lift k0 k1 n0 n1 l :
 k1 <= n1 + n0 -> n1 <= k1 -> map (lift k0 k1) (map (lift n0 n1) l) = map (lift (k0 + n0) n1) l.
Proof.
  move=> *; rewrite !map_map; apply: map_ext=> ?; by apply: PCUICLiftSubst.simpl_lift.
Qed.



Section WithCheckerFlags.
  Context `{cf : checker_flags}.

  Lemma AritiesToGeneration_typing_spine Σ Δ T s U :
    PCUICArities.typing_spine Σ Δ T s U ->
    PCUICGeneration.typing_spine Σ Δ T s U.
  Proof using cf.
    move=> z; depind z; econstructor=> //; try eassumption.
    all: by apply: PCUICConversion.cumulAlgo_cumulSpec.
  Qed.

  Lemma isType_lift {Σ : global_env_ext} {n Γ Δ ty}
    (isdecl : n <= #|Γ|):
    wf Σ -> wf_local Σ (Γ ,,, lift_context n 0 Δ) ->
    isType Σ (skipn n Γ ,,, Δ) ty ->
    isType Σ (Γ,,, lift_context n 0 Δ) (lift n #|Δ| ty).
  Proof using cf.
    intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
    assert (n = #|firstn n Γ|).
    { rewrite firstn_length_le; auto with arith. }
    apply lift_typing_f_impl with (1 := wfty) => // ?? Hs.
    rewrite {3 4 5}H.
    eapply (weakening_typing (Γ := skipn n Γ) (Γ' := Δ) (Γ'' := firstn n Γ));
      eauto with wf.
  Qed.


End WithCheckerFlags.



Section CaseDefinitions.
  Context
    `{cf : checker_flags}
    (ind : inductive)
    (mib : mutual_inductive_body)
    (oib : one_inductive_body)
    (pparams : list term)
    (puinst : Instance.t).

  Definition inddecl_name :=
    {| binder_name := nNamed (ind_name oib) ; binder_relevance := ind_relevance oib |}.

  Definition indpred_ctx :=
    let indxctx := subst_context (List.rev pparams) 0 (expand_lets_ctx mib.(ind_params) oib.(ind_indices))@[puinst] in
    let indty := mkApps (tInd ind puinst) (map (lift0 #|ind_indices oib|) pparams ++ to_extended_list oib.(ind_indices)) in
    indxctx ,, vass (inddecl_name) indty.

  Lemma pre_case_predicate_context_gen_indpred_ctx Σ Γ :
    spine_subst Σ Γ pparams (List.rev pparams) (smash_context [] (ind_params mib)@[puinst]) ->
    consistent_instance_ext Σ (ind_universes mib) puinst ->
    pre_case_predicate_context_gen ind mib oib pparams puinst = indpred_ctx.
  Proof using cf.
    move=> pparamssubst ?.
    rewrite /pre_case_predicate_context_gen /ind_predicate_context /indpred_ctx /inst_case_context.
    rewrite PCUICUnivSubst.subst_instance_cons subst_context_snoc. f_equal.
    rewrite /vass /inddecl_name subst_instance_length expand_lets_ctx_length.
    rewrite {1}/subst_instance /= /subst_decl /map_decl /=; f_equal.
    rewrite PCUICUnivSubst.subst_instance_mkApps PCUICLiftSubst.subst_mkApps.
    f_equal => /=; first (f_equal; apply: subst_instance_id_mdecl; eassumption).
    rewrite PCUICUnivSubst.map_subst_instance_to_extended_list_k.
    rewrite PCUICContexts.to_extended_list_k_app.
    rewrite map_app; f_equal.
    - rewrite expand_lets_ctx_length Nat.add_0_r.
      rewrite -{2}[#|_|]Nat.add_0_r PCUICLiftSubst.lift_to_extended_list_k map_map.
      erewrite map_ext; last (move=> ?; rewrite subst_lift_subst; reflexivity).
      rewrite -map_map; f_equal.
      rewrite -(PCUICLiftSubst.map_subst_instance_to_extended_list_k puinst) subst_instance_smash.
      apply: spine_subst_subst_to_extended_list_k; eassumption.
    - rewrite -PCUICSubstitution.to_extended_list_k_map_subst ?expand_lets_ctx_length //.
      rewrite to_extended_list_k_expand_lets //.
  Qed.



End CaseDefinitions.



(****************************)
(* Lemmas on Case branches  *)
(****************************)

Definition case_branch_context ind mib p (b : branch term) cdecl :=
  case_branch_context_gen ind mib (pparams p) (puinst p) (forget_types (bcontext b)) cdecl.

Definition instantiate_cstr_indices ind mib params puinst cdecl :=
  let upars := (ind_params mib)@[puinst] in
  let arglen := #|cstr_args cdecl| in
  let inds := inds (inductive_mind ind) puinst (ind_bodies mib) in
  map (subst (List.rev params) arglen)
    (map (expand_lets_k upars arglen)
      (map (subst inds (#|ind_params mib| + arglen))
        (map (subst_instance puinst) (cstr_indices cdecl)))).


Definition case_branch_type_only_gen ind mib params puinst ptm i cdecl :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list (cstr_args cdecl) in
  let cstrapp := mkApps cstr (map (lift0 #|cstr_args cdecl|) params ++ args) in
  let indices := instantiate_cstr_indices ind mib params puinst cdecl in
  mkApps (lift0 #|cstr_args cdecl| ptm) (indices ++ [cstrapp]).

Definition case_branch_type_only ind mib p ptm i cdecl :=
  case_branch_type_only_gen ind mib (pparams p) (puinst p) ptm i cdecl.

Lemma case_branch_type_gen_split ind mib oib params puinst ptm names i cdecl :
  case_branch_type_gen ind mib oib params puinst names ptm i cdecl =
  (case_branch_context_gen ind mib params puinst names cdecl,
  case_branch_type_only_gen ind mib params puinst ptm i cdecl).
Proof. reflexivity. Qed.

Lemma case_branch_type_split ind mib oib p b ptm i cdecl :
  case_branch_type ind mib oib p b ptm i cdecl =
  (case_branch_context ind mib p b cdecl, case_branch_type_only ind mib p ptm i cdecl).
Proof. reflexivity. Qed.

Definition case_branch_type_subst_gen ind mib params puinst predctx rettyp i cdecl :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list (cstr_args cdecl) in
  let cstrapp := mkApps cstr (map (lift0 #|cstr_args cdecl|) params ++ args) in
  let indices := instantiate_cstr_indices ind mib params puinst cdecl in
  let ctx := lift_context #|cstr_args cdecl| 0 predctx in
  let s := mk_ctx_subst ctx (indices ++ [cstrapp]) in
  subst0 s (lift #|cstr_args cdecl| #|predctx| rettyp).

Definition case_branch_type_subst ind mib p predctx rettyp i cdecl :=
  case_branch_type_subst_gen ind mib (pparams p) (puinst p) predctx rettyp i cdecl.


(************************************************)
(* Beta-reduction of match's motive in branches *)
(************************************************)

Section CaseBranchTypeBeta.
  Context `{cf : checker_flags}.
  Lemma pre_case_branch_context_gen_length ind mib params puinst cb :
    #|cstr_args cb| =  #|pre_case_branch_context_gen ind mib cb params puinst|.
  Proof using. rewrite /pre_case_branch_context_gen; by len. Qed.

  Lemma case_branch_context_unfold ind mib oib params puinst rettyp cb t :
    let p := make_case_pred ind mib oib params puinst rettyp in
    case_branch_context ind mib p (make_br ind mib cb t) cb =
    pre_case_branch_context_gen ind mib cb params puinst.
  Proof using.
    move=> p.
    rewrite /case_branch_context -/(PCUICCases.case_branch_context ind mib p _ cb).
    rewrite PCUICCasesContexts.inst_case_branch_context_eq //.
    reflexivity.
  Qed.


  Lemma case_branch_type_beta (Σ : global_env_ext) Γ ind mib params puinst predctx rettyp i cb :
    wf Σ ->
    closedn #|Γ ,,, predctx| rettyp ->
    closed_ctx (Γ ,,, predctx) ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in
    closed_ctx (Γ ,,, cstr_ctx) ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    PCUICReduction.red Σ.1 (Γ ,,, cstr_ctx)
      (case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb)
      (case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb).
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ clret clpred clcstr indxseq.
    apply: red_betas; first (rewrite /instantiate_cstr_indices /Δ; by len).
    - have -> : #|Γ ,,, cstr_ctx ,,, Δ| = #|Γ ,,, predctx| + #|cstr_args cb|
      by rewrite /Δ !length_app /cstr_ctx /pre_case_branch_context_gen; len; lia.
      by apply: PCUICClosed.closedn_lift.
    - rewrite PCUICClosed.closedn_ctx_app clcstr /= /Δ length_app.
      have -> : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len; lia.
      apply: PCUICClosed.closedn_ctx_lift.
      by apply: closed_ctx_app.
  Qed.


  Lemma case_branch_type_conv_beta (Σ : global_env_ext) Γ ind mib oib params puinst predctx rettyp i cb :
    wf Σ ->
    closedn #|Γ ,,, predctx| rettyp ->
    closed_ctx (Γ ,,, predctx) ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in
    closed_ctx (Γ ,,, cstr_ctx) ->
    forallb (closedn #|Γ|) params ->
    #|params| = ind_npars mib ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    declared_inductive Σ ind mib oib ->
    declared_constructor Σ (ind,i) mib oib cb ->
    Σ ;;; Γ ,,, cstr_ctx |-
      case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb =s
      case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb.
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ clret clpred clcstr clpar pareq indxseq declind declctor.
    pose proof (declmind := proj1 declind).
    have eqcstrctx : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len; lia.
    apply: conv_betas.
    - have -> : #|Γ ,,, cstr_ctx ,,, Δ| = #|Γ ,,, predctx| + #|cstr_args cb|
      by rewrite /Δ !length_app eqcstrctx; len; lia.
      by apply: PCUICClosed.closedn_lift.
    - rewrite PCUICClosed.closedn_ctx_app clcstr /= /Δ length_app eqcstrctx.
      apply: PCUICClosed.closedn_ctx_lift.
      by apply: closed_ctx_app.
    - rewrite forallb_app; apply/andP; split.
      + rewrite /instantiate_cstr_indices !forallb_map.
        apply: All_forallb.
        apply: All_impl; first (apply: on_constructor_closed_indices; eassumption).
        move=> x /=.
        rewrite -PCUICClosedTyp.is_open_term_closed eqcstrctx !length_app=> clx.
        rewrite Nat.add_comm.
        apply: PCUICClosed.closedn_subst; first by rewrite forallb_rev.
        set G := (_ @[_]). have -> : #|List.rev params| = context_assumptions G.
        1: by rewrite /G context_assumptions_subst_instance -(PCUICGlobalEnv.declared_minductive_ind_npars declmind) List.length_rev.
        rewrite PCUICClosed.closedn_expand_lets_eq {}/G.
        1:{
          rewrite PCUICClosed.closedn_subst_instance_context.
          apply: (PCUICClosed.closedn_ctx_upwards 0); last lia.
          apply: PCUICClosedTyp.declared_inductive_closed_params declind.
        }
        rewrite subst_instance_length -Nat.add_assoc [X in _ + X]Nat.add_comm.
        apply: PCUICClosed.closedn_subst.
        1:{
          apply: forallb_impl; last apply: PCUICClosed.closed_inds.
          move=> ???; apply: PCUICLiftSubst.closed_upwards; first eassumption; lia.
        }
        rewrite inds_length PCUICClosed.closedn_subst_instance.
        apply: PCUICLiftSubst.closed_upwards; first eassumption.
        rewrite arities_context_length eqcstrctx; lia.
      + rewrite /= andb_true_r PCUICClosed.closedn_mkApps /= forallb_app ; apply/andP; split.
        * rewrite forallb_map. apply: forallb_impl; last eassumption.
          move=> x _ clx; rewrite length_app eqcstrctx Nat.add_comm.
          by apply: PCUICClosed.closedn_lift.
        * apply: forallb_impl; last apply: PCUICClosed.closedn_to_extended_list.
          move=> ? _ ?; apply: PCUICLiftSubst.closed_upwards; first eassumption.
          rewrite length_app eqcstrctx ; lia.
    - rewrite /Δ /instantiate_cstr_indices; by len.
  Qed.


  Lemma case_branch_type_beta_typed (Σ : global_env_ext) Γ ind mib params puinst predctx rettyp i cb :
    wf Σ ->
    isType Σ (Γ ,,, predctx) rettyp ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in
    wf_local Σ (Γ,,, cstr_ctx) ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    PCUICReduction.red Σ.1 (Γ ,,, cstr_ctx)
      (case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb)
      (case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb).
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ retWty wfcstr_ctx ?. destruct retWty as (_ & ps & retWty & _).
    apply: red_betas_typed; first by rewrite /Δ /instantiate_cstr_indices; len; lia.
    rewrite /Δ; have -> : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len.
    apply: weakening_typing; eassumption.
  Qed.

End CaseBranchTypeBeta.


(*****************)
(* Random lemmas *)
(*****************)

Section RandomLemmas.
  Context `{cf: checker_flags}.


  Lemma cstr_indices_length {Σ} {wfΣ : wf Σ} {ind mib oib cb} :
    declared_constructor Σ ind mib oib cb ->
    #|cstr_indices cb| = context_assumptions (ind_indices oib).
  Proof using cf.
    move=> declctor.
    unshelve epose proof (X := PCUICWeakeningEnvTyp.on_declared_constructor declctor).
    move: X => [] _ [] ? [_] /on_cindices /ctx_inst_length.
    rewrite context_assumptions_rev context_assumptions_lift; apply.
  Qed.

  Lemma isType_mkApps_Ind_inv_spine
    (ind : inductive)
    (mib : mutual_inductive_body)
    (oib : one_inductive_body)
    (pparams : list term)
    (puinst : Instance.t)
    (indices : list term)
    (Σ : global_env_ext) Γ :
    wf_ext Σ ->
    declared_inductive Σ ind mib oib ->
    #|pparams| = ind_npars mib ->
    isType Σ Γ (mkApps (tInd ind puinst) (pparams ++ indices)) ->
    ∑ s, spine_subst Σ Γ (pparams ++ indices) s (ind_params mib,,, ind_indices oib)@[puinst].
  Proof using cf.
    move=> wfΣ inddecl pparamslen discrtypok.
    have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtypok.2.π2.1).
    move: (inddecl)=> /(PCUICWeakeningEnvTyp.on_declared_inductive (Σ:=Σ.1)) [on_ind on_body].
    have wfΣ1 := (wfΣ : wf Σ.1).
    have wfΣwk := declared_inductive_wf_ext_wk _ _ _ wfΣ (proj1 inddecl).

    move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
    rewrite firstn_app_left // skipn_all_app_eq //.
    move=> [parsubst [indxsubst]].
    match goal with [|- ?t -> _] => let_to_set t end.
    move=> [sspparams ssindices _ indiceslen puinstok].

    exists (indxsubst ++ parsubst).

    rewrite subst_instance_app_ctx.
    have indxsubstlen : #|(ind_indices oib)@[puinst]| = #|indxsubst|.
    {
      rewrite -(subst_context_length parsubst 0 _).
      symmetry. apply: PCUICSubstitution.subslet_length.
      exact (ssindices.(inst_subslet)).
    }
    apply: spine_subst_app.
    * rewrite pparamslen context_assumptions_subst_instance.
      apply: PCUICGlobalEnv.declared_minductive_ind_npars; exact: proj1 inddecl.
    * rewrite -app_context_assoc-subst_instance_app_ctx; apply: weaken_wf_local=> //.
      set (Δ := _ ,,, _). destruct Σ as [Σ1 Σ2].
      refine (PCUICUnivSubstitutionTyp.typing_subst_instance_wf_local Σ1 Σ2 Δ puinst (ind_universes mib) _ _ _)=> //.
      destruct (onArity on_body) as (_ & s & lind & _). move: lind => /=.
      rewrite (PCUICGlobalMaps.ind_arity_eq on_body).
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uparams [? [slparams + _ _]]].
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uindxs [? [slindxs + _ _]]].
      move=> indsortTyp.
      pose proof (h := typing_wf_local indsortTyp); move: h.
      rewrite app_context_nil_l //.
    * rewrite skipn_all_app_eq //.
    * rewrite firstn_app_left // skipn_all_app_eq //.
  Qed.

End RandomLemmas.



Lemma type_Case_helper
  `{cf : checker_flags}
  (ind : inductive)
  (mib : mutual_inductive_body)
  (oib : one_inductive_body)
  (pparams : list term)
  (puinst : Instance.t)
  (discr : term)
  (rettyp : term)
  (brs : list term)
  (indices : list term)
  (ps : sort) (Σ : global_env_ext) Γ :
  wf_ext Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->

  Σ;;; Γ |- discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let predctx := case_predicate_context ind mib oib p in


  (wf_local Σ (Γ,,, predctx) -> Σ ;;; Γ,,, predctx |- preturn p : tSort ps) ->

  (* consistent_instance_ext Σ (ind_universes mib) puinst -> *)

  is_allowed_elimination Σ (ind_kelim oib) ps ->
  isSortRel ps oib.(ind_relevance) ->

  isCoFinite (ind_finite mib) = false ->

  #|brs| = #|ind_ctors oib| ->

  let ptm := it_mkLambda_or_LetIn predctx rettyp in

  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib (* pparams puinst *) cdecl brt in
      let brctxty := case_branch_type ind mib oib p br ptm i cdecl in
        wf_local Σ (Γ,,, brctxty.1) ->
        typing Σ (Γ,,, brctxty.1) brctxty.2 (tSort ps) ->
        typing Σ (Γ,,, brctxty.1) (bbody br) brctxty.2
    )
    0 (ind_ctors oib) brs ->

  (* Why do we create a β-redex rather than substituting the indices and term ? *)
  let subst_rettyp := mkApps ptm (indices ++ [discr]) in

  Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : subst_rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp p predctx ptyp (* puinstok *) pselimok Her isfinite brslen ptm brstyp srettyp.
  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (wfΣ : wf Σ.1).
  have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtyp).

  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply PCUICEquality.eq_context_upto_names_binder_annot; reflexivity.
  }

  pose proof (discrtypok := validity discrtyp).

  have predctxwf : wf_local Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.

  specialize (ptyp predctxwf).

  have puinstok : consistent_instance_ext Σ (ind_universes mib) puinst.
  by move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf) [? [?] [?? _ ?]]//.

  have [s ssparamsindxs] : ∑ s, spine_subst Σ Γ (pparams ++ indices) s
                        (ind_params mib,,, ind_indices oib)@[puinst]
  by (apply: isType_mkApps_Ind_inv_spine => //; eassumption).

  apply: type_Case=> //.
  - apply: ptyp.
  - rewrite -/ci -/predctx. constructor=> //=; first reflexivity.
    apply: (spine_subst_ctx_inst ssparamsindxs).
  - have wfbrs : wf_branches oib (map2 (make_br ind mib) (ind_ctors oib) brs).
    {
      rewrite /wf_branches.
      elim: (ind_ctors oib) {brstyp}brs brslen=> [|decl ctors ih] //= [|br brs] //=.
      intro hlen; apply Nat.succ_inj in hlen.
      move/ih: hlen => h; constructor=> // {h}.
      hnf=>/=.
      rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
      rewrite /subst_context /lift_context !forget_types_fold_context_k.
      apply PCUICEquality.eq_context_upto_names_binder_annot. reflexivity.
    }

    constructor=> //.

    apply: All2i_map2_right.
    rewrite -/ci -/p -/ptm -/predctx.
    apply Forall2_All2 in wfbrs.
    apply All2_map2_right_inv in wfbrs=> //.
    pose proof (declctors := declared_ind_declared_constructors inddecl).
    epose proof (alls := All2i_All2_mix_left wfbrs (All2i_Alli_mix_left declctors brstyp)).

    apply: (All2i_impl alls) => i x y.

    move=> [wfbr [declctor]].
    set (br := make_br _ _ _  _). rewrite -/br in wfbr.
    set (brctxty := case_branch_type _ _ _ _ _ _ _ _).

    move=> bodytyp.
    split; first (apply: All2_refl; reflexivity).
    unshelve epose proof (X := wf_case_branch_type (Γ:=Γ)(p:=p) (ci:=ci) ps indices inddecl discrtypok wfpredp ptyp _ i x br declctor wfbr).
    1: reflexivity.
    move: X=> [] *. split=> //. split=> //.
    apply: bodytyp=> //.
Qed.



Lemma type_Case_subst_helper
  `{cf : checker_flags}
  (ind : inductive)
  (mib : mutual_inductive_body)
  (oib : one_inductive_body)
  (pparams : list term)
  (puinst : Instance.t)
  (discr : term)
  (rettyp : term)
  (brs : list term)
  (indices : list term)
  (ps : sort) (Σ : global_env_ext) Γ :
  wf_ext Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->

  Σ;;; Γ |- discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let predctx := case_predicate_context ind mib oib p in


  (wf_local Σ (Γ,,, predctx) -> Σ ;;; Γ,,, predctx |- preturn p : tSort ps) ->

  is_allowed_elimination Σ (ind_kelim oib) ps ->
  isSortRel ps oib.(ind_relevance) ->

  isCoFinite (ind_finite mib) = false ->

  #|brs| = #|ind_ctors oib| ->


  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib cdecl brt in
      let brctx := case_branch_context ind mib p br cdecl in
      let brty := case_branch_type_subst ind mib p predctx rettyp i cdecl in
      wf_local Σ (Γ,,, brctx) ->
      typing Σ (Γ,,, brctx) brty (tSort ps) ->
      typing Σ (Γ,,, brctx) (bbody br) brty
    )
    0 (ind_ctors oib) brs ->

  let subst_rettyp := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp in

  Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : subst_rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp p predctx predWty elimok Her finok brslen brsok substrettyp.

  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (wfΣ : wf Σ.1).
  have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtyp).

  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply PCUICEquality.eq_context_upto_names_binder_annot; reflexivity.
  }


  pose proof (discrtypok := validity discrtyp).

  have predctxwf : wf_local Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.


  move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
  rewrite firstn_app_left // skipn_all_app_eq //.
  move=> [parsubst [indxsubst]].
  move=> [sspparams ssindices _ indiceslen puinstok].

  set ptm := it_mkLambda_or_LetIn predctx rettyp.
  set redex_rettyp := mkApps ptm (indices ++ [discr]).


  have ?: closedn #|Γ,,, predctx| rettyp
  by apply: PCUICClosedTyp.subject_closed; exact: (predWty predctxwf).
  have ?: closed_ctx (Γ,,, predctx)
  by apply: PCUICClosedTyp.closed_wf_local; exact: predctxwf.

  have mk_caseWtyp : Σ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : redex_rettyp.
  {
    apply: type_Case_helper=> //; try eassumption.
    pose proof (declctors := declared_ind_declared_constructors inddecl).
    apply: (All2i_impl (All2i_Alli_mix_left declctors brsok)) => i x t [declctor h] br.
    rewrite case_branch_type_split.
    set brctx := (x in (x, _)).
    set brty := (x in (_, x)).
    move=> /= wf wfty.

    have ?: closed_ctx (Γ,,, pre_case_branch_context_gen ind mib x pparams puinst)
    by apply: PCUICClosedTyp.closed_wf_local; rewrite -(case_branch_context_unfold _ _ oib _ _ rettyp _ t).

    have ?: #|cstr_indices x| + 1 = context_assumptions predctx.
    {
      rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
      rewrite (cstr_indices_length declctor); len.
    }

    econstructor; try eassumption.
    + apply: (h wf).
      eapply subject_reduction; try eassumption.
      rewrite case_branch_context_unfold.
      apply: case_branch_type_beta=> //.
    + apply: cumul_Sym.
      rewrite /brctx case_branch_context_unfold.
      apply: case_branch_type_conv_beta=> //; try eassumption.
      exact: closed_spine_subst_inst sspparams.
  }


  specialize (predWty predctxwf).

  have ?: #|indices ++ [discr]| = context_assumptions predctx.
  by len; rewrite indiceslen /predctx PCUICCasesContexts.inst_case_predicate_context_eq;
     first reflexivity; len.

  have red_rettyp : PCUICReduction.red Σ.1 Γ redex_rettyp substrettyp
  by apply: red_betas=> //.

  econstructor.
  1: exact: mk_caseWtyp.
  - apply: subject_reduction; last exact red_rettyp.
    exact: (validity mk_caseWtyp).2.π2.1.
  - apply: convSpec_cumulSpec.
    apply: conv_betas=> //.
    rewrite forallb_app /= (PCUICClosedTyp.subject_closed discrtyp) !andb_true_r.
    apply: closed_spine_subst_inst ssindices.
Qed.

Lemma type_Case_simple_subst_helper
  `{cf : checker_flags}
  (ind : inductive)
  (mib : mutual_inductive_body)
  (oib : one_inductive_body)
  (pparams : list term)
  (puinst : Instance.t)
  (discr : term)
  (rettyp : term)
  (brs : list term)
  (indices : list term)
  (ps : sort) (Σ : global_env_ext) Γ :
  wf_ext Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->

  Σ;;; Γ |- discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let rettyp' := lift0 (S #|ind_indices oib|) rettyp in

  let p := make_case_pred ind mib oib pparams puinst rettyp' in
  let predctx := case_predicate_context ind mib oib p in


  Σ ;;; Γ |- rettyp : tSort ps ->

  is_allowed_elimination Σ (ind_kelim oib) ps ->
  isSortRel ps oib.(ind_relevance) ->

  isCoFinite (ind_finite mib) = false ->

  #|brs| = #|ind_ctors oib| ->


  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib cdecl brt in
      let brctx := case_branch_context ind mib p br cdecl in
      let brty := lift0 #|brctx| rettyp in
      wf_local Σ (Γ,,, brctx) ->
      typing Σ (Γ,,, brctx) brty (tSort ps) ->
      typing Σ (Γ,,, brctx) (bbody br) brty
    )
    0 (ind_ctors oib) brs ->


  Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp' brs : rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp rettyp' p predctx predWty elimok Her finok brslen brsok.

  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (wfΣ : wf Σ.1).
  have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtyp).

  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply PCUICEquality.eq_context_upto_names_binder_annot; reflexivity.
  }


  pose proof (discrtypok := validity discrtyp).

  have predctxwf : wf_local Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.


  move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
  rewrite firstn_app_left // skipn_all_app_eq //.
  move=> [parsubst [indxsubst]].
  move=> [sspparams ssindices _ indiceslen puinstok].

  have predctxlen : S #|ind_indices oib| = #|predctx|
  by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity; len.

  have ? : context_assumptions predctx = S #|indices|
  by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; try reflexivity; len.

  set subst_rettyp' := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp'.
  have -> : rettyp = subst_rettyp'.
  by rewrite /subst_rettyp' /rettyp' PCUICLiftSubst.simpl_subst_k // mk_ctx_subst_length //; len.

  apply: type_Case_subst_helper=> //; try eassumption.
  - rewrite -/predctx=> ? /=.
    have -> : tSort ps = lift0 (S #|ind_indices oib|) (tSort ps) by reflexivity.
    apply: weakening_gen=> //.
  - pose proof (declctors := declared_ind_declared_constructors inddecl).
    apply: (All2i_impl (All2i_Alli_mix_left declctors brsok)) => i x t [declctor h] br brctx brty wfctx wfty.
    move: (h wfctx). rewrite -/brctx -/br.
    set brty' := (lift0 _ _).
    have <- : brty = brty'; last by apply.
    rewrite /brty' /brty /rettyp' /case_branch_type_subst /case_branch_type_subst_gen /=.
    rewrite -/predctx -predctxlen. set s := (_ ++ _).
    rewrite PCUICLiftSubst.simpl_lift. 1,2: lia.
    rewrite PCUICContexts.subst_lift_above.
    + rewrite mk_ctx_subst_length /s; len.
      rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
      rewrite (cstr_indices_length declctor); len.
    + f_equal. rewrite /brctx case_branch_context_unfold; len.
Qed.

