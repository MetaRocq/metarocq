(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool Utf8.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

From Stdlib Require Import Bool String List Program.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICArities PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICReduction
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICClosed PCUICClosedTyp
     PCUICSafeLemmata PCUICSubstitution PCUICValidity
     PCUICGeneration PCUICInversion PCUICValidity PCUICInductives PCUICInductiveInversion PCUICReduction
     PCUICSpine PCUICSR PCUICCumulativity PCUICConversion PCUICConfluence PCUICArities
     PCUICContexts PCUICContextConversion PCUICContextConversionTyp PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICSafeLemmata PCUICSN PCUICConvCumInversion.

From MetaRocq.PCUIC Require Import BDTyping BDToPCUIC BDFromPCUIC BDUnique.

From MetaRocq.SafeChecker Require Import PCUICErrors PCUICSafeReduce PCUICWfEnv.

(** Allow reduction to run inside Rocq *)
Transparent Acc_intro_generator.

Local Open Scope string_scope.
Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.
Import MonadNotation.

#[global]
Hint Constructors assumption_context : pcuic.

Derive NoConfusion for type_error.

Set Equations With UIP.
Set Equations Transparent.

Add Search Blacklist "_graph_mut".
Add Search Blacklist "obligation".

From Stdlib Require Import ssreflect.

Lemma into_ws_cumul_pb_terms_Algo {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ l l'} :
  All2 (convAlgo Σ Γ) l l' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) l ->
  forallb (is_open_term Γ) l' ->
  ws_cumul_pb_terms Σ Γ l l'.
Proof.
  solve_all.
  now eapply into_ws_cumul_pb.
Qed.

Lemma on_free_vars_ind_predicate_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl →
  on_free_vars_ctx (closedP (context_assumptions (ind_params mdecl)) xpredT)
    (ind_predicate_context ind mdecl idecl).
Proof.
  intros decli.
  rewrite <- closedn_ctx_on_free_vars.
  eapply closed_ind_predicate_context; tea.
  eapply (declared_minductive_closed decli).
Qed.

Inductive wellinferred {cf: checker_flags} Σ Γ t : Prop :=
  | iswellinferred T : Σ ;;; Γ |- t ▹ T -> wellinferred Σ Γ t.

Definition well_sorted {cf:checker_flags} Σ Γ T :=
  ∥ ∑ u, Σ ;;; Γ |- T ▹□ u ∥.

Lemma well_sorted_wellinferred {cf:checker_flags} {Σ Γ T} :
  well_sorted Σ Γ T -> wellinferred Σ Γ T.
Proof.
  intros [[s []]].
  now econstructor.
Qed.

Coercion well_sorted_wellinferred : well_sorted >-> wellinferred.

Lemma spine_subst_smash_inv {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ inst Δ s} :
  wf_local Σ (Γ ,,, Δ) ->
  spine_subst Σ Γ inst s (smash_context [] Δ) ->
  ∑ s', spine_subst Σ Γ inst s' Δ.
Proof.
  intros wf.
  move/spine_subst_ctx_inst.
  intros c. eapply ctx_inst_smash in c.
  unshelve epose proof (ctx_inst_spine_subst _ c); auto.
  now eexists.
Qed.

(** Smashed variant that is easier to use *)
Lemma inductive_cumulative_indices_smash {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} :
  forall {ind mdecl idecl u u' napp},
  declared_inductive Σ ind mdecl idecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  PCUICEquality.cmp_ind_universes Σ ind napp u u' ->
  forall Γ pars pars',
  spine_subst Σ Γ pars (List.rev pars) (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_subst Σ Γ pars' (List.rev pars') (smash_context [] (subst_instance u' (ind_params mdecl))) ->
  ws_cumul_pb_terms Σ Γ pars pars' ->
  let indctx := idecl.(ind_indices)@[u] in
  let indctx' := idecl.(ind_indices)@[u'] in
  let pindctx := subst_context_let_expand (List.rev pars) (ind_params mdecl)@[u] (smash_context [] indctx) in
  let pindctx' := subst_context_let_expand (List.rev pars') (ind_params mdecl)@[u'] (smash_context [] indctx') in
  ws_cumul_ctx_pb_rel Cumul Σ Γ pindctx pindctx'.
Proof.
  intros ind mdecl idecl u u' napp isdecl up cu cu' hR Γ pars pars' sppars sppars' eq.
  unshelve epose proof (spine_subst_smash_inv _ sppars) as [parsubst sppars2].
  eapply weaken_wf_local; tea. apply sppars.
  eapply (on_minductive_wf_params isdecl cu).
  unshelve epose proof (spine_subst_smash_inv _ sppars') as [parsubst' sppars3].
  eapply weaken_wf_local; tea. apply sppars.
  eapply (on_minductive_wf_params isdecl cu').
  epose proof (inductive_cumulative_indices isdecl cu cu' hR Γ pars pars' _ _ sppars2 sppars3 eq).
  intros.
  cbn in X.
  rewrite (spine_subst_inst_subst sppars2) in X.
  rewrite (spine_subst_inst_subst sppars3) in X.
  rewrite /pindctx /pindctx'.
  rewrite - !smash_context_subst_context_let_expand.
  apply X.
Qed.

(** * Retyping

  The [infer] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Section TypeOf.
Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Ltac specialize_Σ wfΣ :=
    repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end.

  Definition on_subterm P Pty Γ t : Type :=
  match t with
  | tProd na t b => Pty Γ t * Pty (Γ ,, vass na t) b
  | tLetIn na d t t' =>
    Pty Γ t * P Γ d * P (Γ ,, vdef na d t) t'
  | tLambda na t b => Pty Γ t * P (Γ ,, vass na t) b
  | _ => True
  end.

Lemma welltyped_subterm {Σ Γ t} :
  wellinferred Σ Γ t -> on_subterm (wellinferred Σ) (well_sorted Σ) Γ t.
Proof using Type.
  destruct t; simpl; auto; intros [T HT]; sq.
  - inversion HT ; subst. apply unlift_TypUniv in X0. split; now do 2 econstructor.
  - inversion HT ; subst. destruct X0 as (_ & ? & ? & _); cbn in *. split; econstructor ; [econstructor|..]; eassumption.
  - inversion HT ; subst. destruct X0 as (X0' & ? & ? & _); cbn in *.
    inversion X0'. split; [split|]; econstructor ; [econstructor|..]; eassumption.
Qed.

  #[local] Abbreviation ret t := (t; _).

  #[local] Definition principal_type Γ t :=
    ∑ T : term, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- t ▹ T ∥.
  #[local] Definition principal_sort Γ T :=
    ∑ u, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- T ▹□ u ∥.
  #[local] Definition principal_type_type {Γ t} (wt : principal_type Γ t) : term
    := projT1 wt.
  #[local] Definition principal_sort_sort {Γ T} (ps : principal_sort Γ T) : sort
    := projT1 ps.
  #[local] Coercion principal_type_type : principal_type >-> term.
  #[local] Coercion principal_sort_sort : principal_sort >-> sort.

  Program Definition infer_as_sort {Γ T}
    (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ Γ ∥)
    (wf : forall Σ (wfΣ : abstract_env_ext_rel X Σ), well_sorted Σ Γ T)
    (tx : principal_type Γ T) : principal_sort Γ T :=
    match @reduce_to_sort cf nor _ X _ Γ tx _ with
    | Checked_comp (u;_) => (u;_)
    | TypeError_comp e _ => !
    end.
  Next Obligation.
    destruct tx ; cbn in *.
    destruct (wf _ wfΣ) as [[]], (hΣ _ wfΣ) as [wΣ].
    specialize_Σ wfΣ.
    sq.
    eapply infering_typing, validity in s as (_ & s & Hs & _); eauto.
    now eexists.
  Defined.
  Next Obligation.
    clear Heq_anonymous.
    destruct tx. specialize_Σ wfΣ.
    pose proof (s Σ wfΣ) as s'.
    cbn in *.
    sq.
    econstructor ; tea.
    now eapply closed_red_red.
  Qed.
  Next Obligation.
    clear Heq_anonymous.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct tx. specialize_Σ wfΣ.
    pose proof (s Σ wfΣ) as s'.
        cbn in *.
    sq.
    destruct wf as [[? i]], (hΣ _ wfΣ) as [wΣ].
    eapply infering_sort_infering in i ; eauto.
    eapply wildcard'. exists x0. intros.
    erewrite(abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto.
  Qed.

  Program Definition infer_as_prod Γ T
    (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ Γ ∥)
    (wf : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ T)
    (isprod : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ∑ na A B, red Σ Γ T (tProd na A B) ∥) :
    ∑ na' A' B', forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥ :=
    match @reduce_to_prod cf nor _ X _ Γ T wf with
    | Checked_comp p => p
    | TypeError_comp e _ => !
    end.
    Next Obligation.
      clear Heq_anonymous.
      destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      pose (hΣ _ wfΣ). specialize_Σ wfΣ.
      sq.
      destruct isprod as (?&?&?&?).
      apply wildcard'.
      do 3 eexists.
      intros. sq.
      erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      eapply into_closed_red ; tea.
      1: fvs.
      destruct wf.
      now eapply subject_is_open_term.
      Unshelve. eauto.
    Qed.

  Equations lookup_ind_decl ind : typing_result
        (∑ decl body, forall Σ (wfΣ : abstract_env_ext_rel X Σ), declared_inductive (fst Σ) ind decl body) :=
  lookup_ind_decl ind with inspect (abstract_env_lookup X ind.(inductive_mind)) :=
    { | exist (Some (InductiveDecl decl)) look with inspect (nth_error decl.(ind_bodies) ind.(inductive_ind)) :=
      { | exist (Some body) eqnth => Checked (decl; body; _);
        | exist None _ => raise (UndeclaredInductive ind) };
      | _ => raise (UndeclaredInductive ind) }.
  Next Obligation.
    split.
    - symmetry in look.
      eapply declared_minductive_from_gen. etransitivity.
      erewrite (abstract_env_lookup_correct' X); eauto.
      reflexivity.
    - now symmetry.
  Defined.

  Lemma lookup_ind_decl_complete Σ (wfΣ : abstract_env_ext_rel X Σ) ind e : lookup_ind_decl ind = TypeError e ->
    ((∑ mdecl idecl, declared_inductive Σ ind mdecl idecl) -> False).
  Proof using Type.
    cbn. pose proof (abstract_env_ext_wf _ wfΣ) as [[? ?]].
    apply_funelim (lookup_ind_decl ind).
    1-2: intros * _ her [mdecl [idecl [declm decli]]];
      unshelve eapply declared_minductive_to_gen in declm; eauto;
      red in declm;
      erewrite <- abstract_env_lookup_correct', declm in e0; eauto;
      congruence.
    1-2:intros * _ _ => // => _ [mdecl [idecl [declm /= decli]]].
    unshelve eapply declared_minductive_to_gen in declm; eauto;
    red in declm. erewrite <- abstract_env_lookup_correct', declm in look; eauto.
    noconf look.
    congruence.
  Qed.

  Obligation Tactic := intros ;
    try match goal with
      | infer : context [wellinferred _ _ _ -> principal_type _ _ ],
        wt : wellinferred _ _ _ |- _ =>
        try clear infer ; destruct wt as [T HT]
    end.

  Equations infer (Γ : context) (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ Γ ∥) (t : term)
    (wt : forall Σ (wfΣ : abstract_env_ext_rel X Σ), wellinferred Σ Γ t) :
    principal_type Γ t
    by struct t :=
   infer Γ wfΓ (tRel n) wt with
    inspect (option_map (lift0 (S n) ∘ decl_type) (nth_error Γ n)) :=
    { | exist None _ => !
      | exist (Some t) _ => ret t };

    infer Γ wfΓ (tVar n) wt := !;
    infer Γ wfΓ (tEvar ev args) wt := !;

    infer Γ wfΓ (tSort s) wt := ret (tSort (Sort.super s));

    infer Γ wfΓ (tProd n ty b) wt :=
      let wfΓ' : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ (Γ ,, vass n ty) ∥ := _ in
      let ty1 := infer Γ wfΓ ty (fun a b => (welltyped_subterm (wt a b)).1) in
      let s1 := infer_as_sort wfΓ (fun a b => (welltyped_subterm (wt a b)).1) ty1 in
      let ty2 := infer (Γ ,, vass n ty) wfΓ' b (fun a b => (welltyped_subterm (wt a b)).2) in
      let s2 := infer_as_sort wfΓ' (fun a b => (welltyped_subterm (wt a b)).2) ty2 in
      ret (tSort (Sort.sort_of_product s1 s2));

    infer Γ wfΓ (tLambda n t b) wt :=
      let t2 := infer (Γ ,, vass n t) _ b (fun a b => (welltyped_subterm (wt a b)).2) in
      ret (tProd n t t2);

    infer Γ wfΓ (tLetIn n b b_ty b') wt :=
      let b'_ty := infer (Γ ,, vdef n b b_ty) _ b' (fun a b => (welltyped_subterm (wt a b)).2) in
      ret (tLetIn n b b_ty b'_ty);

    infer Γ wfΓ (tApp t a) wt :=
      let ty := infer Γ wfΓ t _ in
      let pi := infer_as_prod Γ ty wfΓ _ _ in
      ret (subst10 a pi.π2.π2.π1);

    infer Γ wfΓ (tConst cst u) wt with inspect (abstract_env_lookup X cst) :=
      { | exist (Some (ConstantDecl d)) _ := ret (subst_instance u d.(cst_type))
        |  _ := ! };

    infer Γ wfΓ (tInd ind u) wt with inspect (lookup_ind_decl ind) :=
      { | exist (Checked decl) _ := ret (subst_instance u decl.π2.π1.(ind_type))
        | exist (TypeError e) _ := ! };

    infer Γ wfΓ (tConstruct ind k u) wt with inspect (lookup_ind_decl ind) :=
      { | exist (Checked decl) _ with inspect (nth_error decl.π2.π1.(ind_ctors) k) :=
        { | exist (Some cdecl) _ => ret (type_of_constructor decl.π1 cdecl (ind, k) u)
          | exist None _ => ! }
      | exist (TypeError e) _ => ! };

    infer Γ wfΓ (tCase ci p c brs) wt
      with inspect (reduce_to_ind Γ (infer Γ wfΓ c _) _) :=
      { | exist (Checked_comp indargs) _ =>
          let ptm := it_mkLambda_or_LetIn (inst_case_predicate_context p) p.(preturn) in
          ret (mkApps ptm (List.skipn ci.(ci_npar) indargs.π2.π2.π1 ++ [c]));
        | exist (TypeError_comp _ _) _ => ! };

    infer Γ wfΓ (tProj p c) wt with inspect (@lookup_ind_decl p.(proj_ind)) :=
      { | exist (Checked d) _ with inspect (nth_error d.π2.π1.(ind_projs) p.(proj_arg)) :=
        { | exist (Some pdecl) _ with inspect (reduce_to_ind Γ (infer Γ wfΓ c _) _) :=
          { | exist (Checked_comp indargs) _ =>
              let ty := pdecl.(proj_type) in
              ret (subst0 (c :: List.rev (indargs.π2.π2.π1)) (subst_instance indargs.π2.π1 ty))
            | exist (TypeError_comp _ _) _ => ! }
         | exist None _ => ! }
        | exist (TypeError e) _ => ! };

    infer Γ wfΓ (tFix mfix n) wt with inspect (nth_error mfix n) :=
      { | exist (Some f) _ => ret f.(dtype)
        | exist None _ => ! };

    infer Γ wfΓ (tCoFix mfix n) wt with inspect (nth_error mfix n) :=
      { | exist (Some f) _ => ret f.(dtype)
        | exist None _ => ! };

    infer Γ wfΓ (tPrim p) wt with inspect (abstract_primitive_constant X p.π1) :=
      { | exist (Some prim_ty) eqp => ret (prim_type p prim_ty)
        | exist None _ => ! }.

  Next Obligation.
    cbn; intros; sq.
    destruct (nth_error Γ n) eqn:hnth => //.
    noconf e.
    now constructor.
  Defined.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. cbn in e.
    inversion wt; subst. inversion X0; subst.
    rewrite H0 in e => //.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. now inversion wt.
  Defined.

  Next Obligation.
  destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
  specialize_Σ wfΣ. now inversion wt.
  Defined.

  Next Obligation.
  cbn; intros. specialize_Σ wfΣ.
  inversion wt. now inversion X0.
  Defined.

  Next Obligation.
    pose (hΣ _ wfΣ). specialize_Σ wfΣ.
    inversion wt.
    sq.
    constructor ; tea.
    inversion X0.
    apply lift_sorting_forget_univ in X1.
    now eapply lift_sorting_lift_typing in X1.
  Defined.
  Next Obligation.
    cbn ; intros. destruct s1, s2.
    cbn. specialize_Σ wfΣ.
    pose (hΣ _ wfΣ).
    specialize (wfΓ' _ wfΣ) as wfΓ''.
    sq.
    constructor; eauto.
    inversion wfΓ''; subst.
    apply lift_typing_lift_sorting in X1; tas.
    pose proof (lift_sorting_extract X1).
    assert (X1.2.π1 = x) as <-; tas.
    clear X2.
    destruct X1 as (? & x' & X1 & ?); cbn.
    eapply infering_sort_sort; tea.
  Defined.

  Next Obligation.
    pose (hΣ _ wfΣ). specialize_Σ wfΣ. inversion wt. sq.
    inversion X0 ; subst.
    constructor ; tea.
    now eapply lift_sorting_lift_typing.
  Defined.
  Next Obligation.
    case t2 as []. intros; cbn.  specialize_Σ wfΣ.
    inversion wt.
    sq.
    inversion X0 ; subst.
    now econstructor.
  Defined.

  Next Obligation.
    pose (hΣ _ wfΣ). specialize_Σ wfΣ. inversion wt. sq.
    inversion X0 ; subst.
    constructor ; tea.
    now eapply lift_sorting_lift_typing.
  Defined.
  Next Obligation.
   cbn; intros; case b'_ty as []. cbn.
   specialize_Σ wfΣ. inversion wt. sq.
   inversion X0 ; subst.
   now econstructor.
  Defined.

  Next Obligation.
  specialize_Σ wfΣ. inversion wt. sq.
    inversion X0 ; subst.
    inversion X1.
    now econstructor.
  Defined.
  Next Obligation.
    case ty as [].
    cbn. specialize_Σ wfΣ. inversion wt.
    apply wat_welltyped ; tea.
    pose (hΣ _ wfΣ). sq.
    eapply validity, infering_typing ; eauto.
  Defined.
  Next Obligation.
    case ty as [].
    cbn. specialize_Σ wfΣ. inversion wt.
    pose (hΣ _ wfΣ). sq.
    inversion X0 ; subst.
    eapply infering_prod_infering in X1 as (?&?&[]); eauto.
    do 3 eexists.
    now apply closed_red_red.
  Defined.
  Next Obligation.
    cbn; intros. case pi as (?&?&[]).
    case ty as []. cbn in *. specialize_Σ wfΣ.
    pose (hΣ _ wfΣ). inversion wt. sq.
    inversion X0 ; subst.
    inversion X2 ; subst.
    move: (X1) => tyt.
    apply infering_prod_typing, validity, isType_tProd in tyt as [] ; eauto.
    eapply infering_prod_prod in X1 as (?&?&[]).
    4: econstructor.
    2-4: eauto.
    2: now apply closed_red_red.
    econstructor.
    1: econstructor ; tea.
    1: now apply closed_red_red.
    econstructor ; tea.
    eapply ws_cumul_pb_forget_cumul.
    etransitivity.
    - eapply into_ws_cumul_pb ; tea.
      1,3: fvs.
      now eapply type_is_open_term, infering_typing.
    - etransitivity.
      1: now eapply red_ws_cumul_pb.
      now eapply red_ws_cumul_pb_inv.
  Defined.

  Next Obligation.
    cbn in *; intros. pose (hΣ _ wfΣ). specialize_Σ wfΣ.
    inversion wt. sq.
    inversion X0; subst.
    erewrite <- abstract_env_lookup_correct' in e; eauto.
    unshelve eapply declared_constant_to_gen in isdecl; eauto.
    rewrite isdecl in e. inversion e. subst. assumption.
  Defined.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose (hΣ _ wfΣ). sq. specialize_Σ wfΣ. inversion wt.
    inversion X0 ; subst.
    clear wildcard. erewrite <- abstract_env_lookup_correct' in e; eauto.
    unshelve eapply declared_constant_to_gen in isdecl; eauto.
    rewrite isdecl in e. inversion e.
  Defined.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose (hΣ _ wfΣ). sq. specialize_Σ wfΣ. inversion wt.
    inversion X0 ; subst.
    clear wildcard. erewrite <- abstract_env_lookup_correct' in e; eauto.
    unshelve eapply declared_constant_to_gen in isdecl; eauto.
    rewrite isdecl in e. inversion e.
  Defined.
  Next Obligation.
    cbn in *; intros. pose (hΣ _ wfΣ). specialize_Σ wfΣ.
    inversion wt. sq.
    inversion X0; subst.
    clear e.
    destruct decl as (?&?&isdecl').
    cbn.
    unshelve eapply declared_inductive_to_gen in isdecl, isdecl'; eauto.
    eapply declared_inductive_inj in isdecl' as [].
    2: { exact isdecl. }
    subst. assumption.
  Defined.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. inversion wt.
    inversion X0 ; subst.
    eapply lookup_ind_decl_complete. 1: eauto.
    1: now symmetry.
    now do 2 eexists.
  Defined.

  Next Obligation.
    cbn; intros. specialize_Σ wfΣ. pose (hΣ _ wfΣ). inversion wt. sq.
    inversion X0 ; subst.
    clear e.
    destruct decl as (?&?&isdecl').
    cbn in *.
    unshelve eapply declared_constructor_to_gen in isdecl; eauto.
    pose proof (isdecl'_ := isdecl').
    unshelve eapply declared_inductive_to_gen in isdecl'; eauto.
    eapply declared_constructor_inj in isdecl as (?&[]).
    2: { econstructor. now eapply isdecl'. now idtac. }
    subst.
    econstructor ; tea.
    econstructor. now eapply isdecl'_. now idtac.
  Defined.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose (hΣ _ wfΣ). sq. specialize_Σ wfΣ. inversion wt.
    inversion X0 ; subst.
    clear e.
    destruct decl as (?&?&isdecl').
    unshelve eapply declared_constructor_to_gen in isdecl; eauto.
    pose proof (isdecl'_ := isdecl'). cbn in *.
    unshelve eapply declared_inductive_to_gen in isdecl'; eauto.
    destruct isdecl as [isdecl]; cbn -[lookup_ind_decl] in *.
    eapply declared_inductive_inj in isdecl' as [].
    2: exact isdecl. subst.
    now congruence.
  Defined.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. inversion wt.
    inversion X0 ; subst.
    destruct isdecl.
    eapply lookup_ind_decl_complete. 1:eauto.
    1: now symmetry.
    now do 2 eexists.
  Defined.
  Next Obligation.
    specialize_Σ wfΣ. inversion wt.
    inversion X0 ; subst.
    inversion X1.
    now econstructor.
  Defined.
  Next Obligation.
    cbn in *. pose proof wt. specialize_Σ wfΣ.
    destruct infer.
    pose (hΣ _ wfΣ). cbn. specialize_Σ wfΣ. sq.
    eapply infering_typing, validity in s as (_ & ? & ? & _) ; eauto.
    now eexists.
  Defined.


  Next Obligation.
    cbn in *. intros.
    set (H := λ (Σ0 : global_env_ext) (wfΣ0 : abstract_env_ext_rel X Σ0),
    infer_obligations_obligation_24 Γ ci p c brs wt Σ0
      wfΣ0) in indargs. cbn in *.
    set (infer _ wfΓ c H) in *. unfold H in *. clear H.
    pose proof p0.π2 as p02.
    destruct indargs as (?&?&?&?).
    cbn in *. pose proof wt; pose proof wfΓ
    ; pose proof s as s'.
    specialize_Σ wfΣ. cbn in *. inversion H.
    pose (hΣ _ wfΣ); sq.
    inversion X0 ; subst.
    move: (X1) => inf.
    eapply infering_ind_ind in inf as [? []].
    2,3: eauto.
    2: now econstructor ; tea;  eapply closed_red_red.
    subst.
    rewrite /ptm.
    erewrite <- PCUICCasesContexts.inst_case_predicate_context_eq ; tea.
    econstructor ; tea.
    + econstructor ; tea.
      now apply closed_red_red.
    + replace #|x1| with #|args| ; tea.
      etransitivity.
      2: symmetry.
      all: eapply All2_length ; eassumption.
    + eapply All2_impl.
      2:intros; now eapply ws_cumul_pb_forget_conv.
      etransitivity.
      1: eapply All2_firstn.
      1: etransitivity.
      1: now eapply red_terms_ws_cumul_pb_terms.
      1: symmetry.
      1: now eapply red_terms_ws_cumul_pb_terms.
      eapply PCUICConvCumInversion.alt_into_ws_cumul_pb_terms ; tea.
      * fvs.
      * eapply infering_ind_typing, validity, isType_is_open_term in X1 ; auto.
        rewrite on_free_vars_mkApps in X1.
        move: X1 => /andP [] _ /forallb_All ?.
        now eapply All_forallb, All_firstn.
      * apply infering_typing, subject_is_open_term in X0 ; auto.
        move: X0 => /= /andP [] //.
  Defined.
  Next Obligation.
  cbn in *. intros.
  set (H := λ (Σ : global_env_ext) (wfΣ : abstract_env_ext_rel X Σ),
  infer_obligations_obligation_24 Γ ci p c brs wt Σ wfΣ) in a0.
  cbn in *.
  set (infer _ wfΓ c H) in *.
  unfold H in *. clear H e.
   destruct p0 as [? i].
    cbn in *.
    pose proof wt; pose proof wfΓ.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. cbn in *. inversion H.
    pose (hΣ _ wfΣ); sq.
    apply a0.
    inversion X0 ; subst.
    eapply infering_ind_infering in i as [? []] ; eauto.
    do 3 eexists. intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. eauto.
  Defined.
  Next Obligation.
  specialize_Σ wfΣ. destruct wt.
    inversion X0. inversion X1.
    now econstructor.
  Defined.
  Next Obligation.
    destruct infer.
    pose proof s as s'; pose proof wfΓ as wfΓ'.
    specialize_Σ wfΣ.
    pose (hΣ _ wfΣ); sq.
    cbn.
    eapply infering_typing, validity in s' as (_ & ? & ? & _); eauto.
    now eexists.
  Defined.
  Next Obligation.
  cbn in *. intros.
  set (H := λ (Σ0 : global_env_ext) (wfΣ0 : abstract_env_ext_rel X Σ0),
  infer_obligations_obligation_28 Γ p c wt Σ0 wfΣ0) in indargs. cbn in *.
  set (infer _ wfΓ c H) in *. unfold H in *. clear H.
  pose proof p0.π2 as p02.
  destruct indargs as (?&?&?&?).
    destruct d as (?&?&isdecl).
    clear e.
    cbn -[lookup_ind_decl] in *.
    pose proof wt; pose proof wfΓ
    ; pose proof s as s'.
    specialize_Σ wfΣ. cbn in *. inversion H.
    pose (hΣ _ wfΣ); sq.
    inversion X0 ; subst.
    destruct H3 as [[isdecl' ] []].
    cbn -[nth_error] in *.
    unshelve eapply declared_inductive_to_gen in isdecl, isdecl'; eauto.
    eapply declared_inductive_inj in isdecl' as [].
    2: eexact isdecl.
    subst.
    eapply infering_ind_ind in X1 as [? []].
    2-3: eauto.
    2: now econstructor ; tea ; apply closed_red_red.
    subst.
    econstructor.
    - do 2 split; eauto. eapply declared_inductive_from_gen; eauto.
    - econstructor ; tea.
      now apply closed_red_red.
    - etransitivity ; tea.
      etransitivity.
      2: symmetry; eapply All2_length ; eassumption.
      now eapply All2_length.
  Defined.
  Next Obligation.
    cbn in *.
    set (H := (λ (Σ0 : global_env_ext)
    (wfΣ0 : abstract_env_ext_rel X Σ0),
    infer_obligations_obligation_28 Γ p c wt Σ0 wfΣ0)) in a0.
      cbn in *.
      set (infer _ wfΓ c H) in *.
      unfold H in *. clear H e1.
    destruct p0.
    cbn -[lookup_ind_decl] in *.
    pose proof wt; pose proof wfΓ.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. cbn in *. inversion H.
    pose (hΣ _ wfΣ); sq.
    inversion X0.
    eapply infering_ind_infering in s as [? []] ; eauto.
    apply a0.
    do 3 eexists.
    intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto.
  Defined.
  Next Obligation.
    destruct d as (?&?&isdecl).
    clear e.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose (hΣ Σ wfΣ). sq. specialize (wt _ wfΣ). destruct wt. inversion X0.
    destruct H1 as [[] []].
    cbn -[lookup_ind_decl nth_error] in *.
    unshelve eapply declared_inductive_to_gen in isdecl, H1; eauto.
    eapply declared_inductive_inj in isdecl as []. 2: exact H1.
    subst.
    now congruence.
  Qed.
  Next Obligation.
    cbn -[lookup_ind_decl] in *.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize (wt _ wfΣ). destruct wt. inversion X0.
    eapply lookup_ind_decl_complete ; eauto.
    do 2 eexists.
    exact H1.
  Qed.

  Next Obligation.
    sq.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize (wt _ wfΣ). destruct wt. inversion X0.
    subst.
    intros; erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now constructor.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    cbn in e.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize (wt _ wfΣ). destruct wt. inversion X0.
    congruence.
  Qed.

  Next Obligation.
    sq.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize (wt _ wfΣ). destruct wt. inversion X0.
    subst.
    intros; erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now constructor.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    cbn in e.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize (wt _ wfΣ). destruct wt. inversion X0.
    congruence.
  Qed.

  Next Obligation.
    cbn.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    intros. specialize (wt _ wfΣ). destruct wt.
    inversion X0; subst.
    cbn in eqp. rewrite (abstract_primitive_constant_correct _ _ Σ) // in eqp.
    rewrite /= -eqp in H0. noconf H0. split.
    intros; erewrite (abstract_env_ext_irr _ wfΣ0 wfΣ); eauto.
  Qed.

  Next Obligation.
    cbn in *.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    intros. specialize (wt _ wfΣ). destruct wt.
    inversion X0; subst.
    rewrite (abstract_primitive_constant_correct _ _ Σ) // in e.
    rewrite /= -e in H0. noconf H0.
  Qed.

  Definition type_of Γ wfΓ t wt : term := (infer Γ wfΓ t wt).

  Definition principal_typing Σ Γ t P :=
    forall T, Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ P ≤ T.

  Program Definition type_of_typing Γ t (wt : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t) : ∑ T, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ (Σ ;;; Γ |- t : T) × principal_typing Σ Γ t T ∥ :=
    let it := infer Γ _ t _ in
    (it.π1; _).
  Next Obligation.
    specialize_Σ wfΣ. destruct wt; sq; pcuic.
  Qed.
  Next Obligation.
    specialize_Σ wfΣ. pose (hΣ _ wfΣ); sq.
    destruct wt as [T Ht].
    eapply BDFromPCUIC.typing_infering in Ht as [T' [inf _]].
    now exists T'.
  Qed.
  Next Obligation.
    cbn in *. subst it. intros. pose proof wt as wt'.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct infer as []; cbn.
    specialize_Σ wfΣ. destruct wt' as [T' HT'].
    sq.
    split.
    eapply BDToPCUIC.infering_typing in s; pcuic.
    intros T'' HT''.
    apply typing_infering in HT'' as [P [HP HP']].
    eapply infering_checking;tea. 1-2: pcuic.
    fvs.
    econstructor; tea. now eapply ws_cumul_pb_forget in HP'.
  Defined.

  Lemma squash_isType_welltyped :
    forall {Σ : global_env_ext} {Γ : context} {T : term},
    ∥ isType Σ Γ T ∥ -> welltyped Σ Γ T.
  Proof using Type. intros. destruct H. now eapply isType_welltyped. Qed.

  Opaque type_of_typing.
  Equations? sort_of_type (Γ : context) (t : PCUICAst.term)
    (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ isType Σ Γ t ∥) :
    (∑ u : sort, forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
      ∥ Σ ;;; Γ |- t : tSort u ∥) :=
    sort_of_type Γ t wt with (@type_of_typing Γ t _) :=
      { | T with inspect (reduce_to_sort (X:=X) Γ T.π1 _) :=
        { | exist (Checked_comp (u; Hu)) hr => (u; _)
          | exist (TypeError_comp _ _) ns => False_rect _ _ } }.
  Proof.
    - eapply squash_isType_welltyped, wt; eauto.
    - cbn.
      specialize (wt _ wfΣ) as [wt].
      destruct T as [T HT].
      destruct (HT _ wfΣ) as [[Ht _]].
      pose proof (abstract_env_ext_wf _ wfΣ) as [wf].
      eapply validity in Ht.
      now eapply isType_welltyped.
    - clear hr.
      pose proof (abstract_env_ext_wf _ H) as [wf].
      specialize (Hu _ H) as [Hred]. cbn in Hred.
      destruct T as [T HT].
      destruct (HT _ H) as [[Ht _]]. cbn in Hred.
      sq. eapply type_reduction_closed; tea.
    - epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      symmetry in ns. pose proof (reduce_to_sort_complete _ wfΣ _ _ ns).
      cbn in ns. clear ns.
      specialize (wt _ wfΣ). destruct T as [T HT].
      cbn in *. destruct (HT _ wfΣ) as [[hty hp]].
      eapply validity in hty. destruct wt as [(_ & s & Hs & _)].
      red in hp. specialize (hp _ Hs).
      eapply ws_cumul_pb_Sort_r_inv in hp as [s' [hs' _]].
      eapply (H s' hs').
  Defined.
  Transparent type_of_typing.

  Open Scope type_scope.

  Definition map_typing_result {A B} (f : A -> B) (e : typing_result A) : typing_result B :=
    match e with
    | Checked a => Checked (f a)
    | TypeError e => TypeError e
    end.

  Arguments iswelltyped {cf Σ Γ t A}.

  Equations? type_of_subtype {Γ t T} (wt : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- t : T ∥) :
  forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ type_of Γ _ t _ ≤ T ∥ :=
    type_of_subtype wt := _.
  Proof.
    - erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      specialize_Σ wfΣ.  case wt as [wt'].
      apply sq.
      now exact (typing_wf_local wt').
    - erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      specialize_Σ wfΣ.  case wt as [wt'].
      case (hΣ _ wfΣ) as [hΣ'].
      apply typing_infering in wt'.
      case wt' as [T' [i]].
      exists T'.
      exact i.
    - unfold type_of.
      destruct infer as [P HP]. cbn.
      specialize_Σ wfΣ.
      pose (hΣ _ wfΣ) ; sq. simpl.
      eapply infering_checking ; eauto.
      + now eapply typing_wf_local.
      + now eapply type_is_open_term.
      + now eapply typing_checking.
      Unshelve. all: eauto.
  Defined.

  (* Note the careful use of squashing here: the principal type is accessible
    computationally but the proof it is principal is squashed (in Prop).
    The [PCUICPrincipality.principal_type] proof gives an unsquashed version of the same theorem. *)

  Theorem principal_types {Γ t} (wt : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t) :
    ∑ P, ∥ forall T Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ |- t : T -> (Σ ;;; Γ |- t : P) * (Σ ;;; Γ ⊢ P ≤ T) ∥.
  Proof using nor normalization_in.
    unshelve eexists (infer Γ _ t _); intros.
    - destruct (wt _ wfΣ).
      pose (hΣ _ wfΣ); sq.
      now eapply typing_wf_local.
    - pose (hΣ _ wfΣ); sq.
      destruct (wt _ wfΣ) as [? wt'].
      eapply typing_infering in wt' as [? []].
      econstructor.
      eassumption.
    - cbn.
      set (H := (λ (Σ0 : global_env_ext) (wfΣ0 : abstract_env_ext_rel X Σ0),
      match hΣ Σ0 wfΣ0 with
      | sq H =>
          match wt Σ0 wfΣ0 with
          | @iswelltyped _ _ _ _ A H0 =>
              let (x, p) := typing_infering H0 in
              let (a, _) := p in iswellinferred Σ0 Γ t x a
          end
      end)).
  set (H' := (fun (Σ : _)
      (wfΣ : _ X Σ)
    => match
      wt Σ wfΣ
    with
    | @iswelltyped _ _ _ _ A x =>
        match
          hΣ Σ wfΣ
        with
        | sq _ =>
            @sq (All_local_env (lift_typing (@typing cf) Σ) Γ)
              (@typing_wf_local cf Σ Γ t A x)
        end
    end)).
    cbn.
    set (infer Γ H' t H). clearbody p.
    clear H H'. destruct p as [T i]; eauto.
    cbn.       destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose (hΣ _ wfΣ). specialize_Σ wfΣ. sq.
    intros T' ? ?.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    clear Σ0 wfΣ0. intros. split.
      + apply infering_typing ; eauto.
        now eapply typing_wf_local.
      + eapply infering_checking ; eauto.
        * now eapply typing_wf_local.
        * now eapply type_is_open_term.
        * now eapply typing_checking.
    Unshelve. all: eauto.
  Qed.

End TypeOf.
