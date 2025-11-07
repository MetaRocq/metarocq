(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph EnvMap.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICTyping PCUICNormal PCUICSR
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICConversion PCUICWfUniverses
     PCUICGlobalEnv
     (* Used for support lemmas *)
     PCUICInductives PCUICWfUniverses
     PCUICContexts PCUICSubstitution PCUICSpine PCUICInductiveInversion
     PCUICClosed PCUICClosedTyp PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICOnFreeVars PCUICWellScopedCumulativity
     BDTyping BDFromPCUIC BDToPCUIC.

From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICSafeReduce PCUICErrors
  PCUICSafeConversion PCUICWfReduction PCUICWfEnv PCUICTypeChecker.

From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool ssrfun.

Local Set Keyed Unification.
Set Equations Transparent.

Import MRMonadNotation.
From Stdlib Require Import Morphisms.

Implicit Types (cf : checker_flags).

(* Global Instance proper_add_uctx cstrs : Morphisms.Proper (Equal_graph ==> Equal_graph)%signature (push_uctx cstrs).
Proof.
  intros g g' eq. rewrite /add_uctx; cbn.
  split. cbn. now rewrite (proj1 eq).
  cbn. split => //.
  rewrite /add_level_edges. now rewrite (proj1 (proj2 eq)).
  apply eq.
Qed. *)


Definition cs_equal (x y : ContextSet.t) : Prop :=
  LevelSet.Equal x.1 y.1 /\ UnivConstraintSet.Equal x.2 y.2.


  (* Global Instance make_graph_proper : Proper (gcs_equal ==> Equal_graph) make_graph.
  Proof.
    intros [v c] [v' c'] [eqv eqc]; cbn.
    unfold make_graph; cbn in *.
    split; cbn; auto.
    split; cbn; try reflexivity.
    now rewrite eqc eqv.
  Qed.*)
  Require Import SetoidTactics.

  Global Instance model_of_uctx_proper {cf} G : Proper (cs_equal ==> iff) (model_of_uctx G).
  Proof.
    intros [l c] [l' c'] [eql eqc]; cbn.
    unfold model_of_uctx; cbn. cbn in *.
    split. intros []; split. now rewrite -eql.
    rewrite -eqc.

  Admitted.


(** It otherwise tries [auto with *], very bad idea. *)
Ltac Corelib.Program.Tactics.program_solve_wf ::=
  match goal with
  | |- @Wf.well_founded _ _ => auto with subterm wf
  | |- ?T => match type of T with
                | Prop => auto
                end
  end.


Definition check_eq_true_lazy@{u u0 u1} {T : Type@{u} -> Type@{u0}} {E : Type@{u1}} {M : Monad T} {ME : MonadExc E T} (b : bool) (fe : unit -> E) : T b :=
  if b as b0 return (T b0) then ret eq_refl else raise (fe tt).

Section OnUdecl.
  Context {cf:checker_flags}.

  Lemma In_unfold_inj {A} (f : nat -> A) n i :
    (forall i j, f i = f j -> i = j) ->
    In (f i) (unfold n f) <-> i < n.
  Proof using Type.
    intros hf. split.
    now apply In_unfold_inj.
    intros.
    induction n in i, H |- *; simpl => //. lia.
    eapply in_app_iff.
    destruct (eq_dec i n). subst. right; left; auto.
    left. eapply IHn. lia.
  Qed.

  Lemma In_Var_global_ext_poly {n Σ inst cstrs} :
    n < #|inst| ->
    LevelSet.mem (Level.lvar n) (global_ext_levels (Σ, Polymorphic_ctx (inst, cstrs))).
  Proof using Type.
    intros Hn.
    unfold global_ext_levels; simpl.
      apply LevelSet.mem_spec; rewrite LevelSet.union_spec. left.
    rewrite /AUContext.levels /= mapi_unfold.
    apply LevelSetProp.of_list_1, InA_In_eq.
    eapply In_unfold_inj; try congruence.
  Qed.
(*
  Lemma bounded_poly_ext (ls : Universe.t) (inst : list name) (cstrs : UnivConstraintSet.t) Σ :
    LevelSet.Subset (Universe.levels ls) (LevelSet.union (levels_of_udecl (Polymorphic_ctx (inst, cstrs))) (global_ext_levels Σ)) -> closedu_universe #|inst| ls.
  Proof.
    have hb := LSet_in_poly_bounded _ inst cstrs.
    move/subset_levels => hl.
    Search closedu_universe. *)

  Lemma on_udecl_poly_bounded X inst cstrs :
    wf X ->
    on_udecl X (Polymorphic_ctx (inst, cstrs)) ->
    closedu_cstrs #|inst| cstrs.
  Proof using Type.
    rewrite /on_udecl. intros wfX [_ [nlevs _]].
    red.
    rewrite /closedu_cstrs.
    intros x incstrs. simpl in nlevs.
    specialize (nlevs x incstrs).
    destruct x as [[l1 p] l2].
    destruct nlevs.
    cbn. toProp; unshelve eapply bounded_poly_global_levels; tea.
  Qed.

  Lemma subst_instance_level_lift inst l :
    closedu_level #|inst| l ->
    subst_instance_level (lift_instance #|inst| (Instance.of_level_instance (level_var_instance 0 inst))) l = Universe.of_level @@ lift_level #|inst| l.
  Proof using Type.
    clear cf.
    destruct l => // /= /Nat.ltb_lt ltn.
    rewrite nth_error_map.
    destruct nth_error eqn:eq. move:eq.
    - rewrite nth_error_map /level_var_instance [mapi_rec _ _ _]mapi_unfold (proj1 (nth_error_unfold _ _ _) ltn).
      simpl. intros [=]. subst t.
      unfold lift_universe. rewrite map_singleton //=.
    - eapply nth_error_None in eq; len in eq.
  Qed.

  Lemma subst_instance_universe_lift inst l :
    closedu_universe #|inst| l ->
    subst_instance (lift_instance #|inst| (Instance.of_level_instance (level_var_instance 0 inst))) l = lift_universe #|inst| l.
  Proof. Admitted.

  Lemma subst_instance_level_var_instance inst l :
    closedu_level #|inst| l ->
    subst_instance_level (level_var_instance 0 inst) l = Universe.of_level l.
  Proof using Type.
    destruct l => // /= /Nat.ltb_lt ltn.
    rewrite /level_var_instance nth_error_map.
    now rewrite /level_var_instance [mapi_rec _ _ _]mapi_unfold (proj1 (nth_error_unfold _ _ _) ltn).
  Qed.


  Lemma subst_instance_universe_var_instance inst l :
    closedu_universe #|inst| l ->
    subst_instance (level_var_instance 0 inst) l = l.
  Proof using Type.
  Admitted.

  Lemma lift_universe_singleton n n' : lift_universe n (Universe.of_level (Level.lvar n')) = Universe.of_level (Level.lvar (n + n')).
  Proof. Admitted.

  Lemma variance_universes_spec Σ ctx v univs u u' :
    wf_ext (Σ, ctx) ->
    wf_ext (Σ, univs) ->
    variance_universes ctx v = Some (univs, u, u') ->
    consistent_instance_ext (Σ, univs) ctx u ×
    consistent_instance_ext (Σ, univs) ctx u'.
  Proof using Type.
    intros wfctx wfext.
    unfold variance_universes. destruct ctx as [|[inst cstrs]] => //.
    intros [= eq].
    set (vcstrs := UnivConstraintSet.union _ _) in *.
    subst univs. simpl.
    subst u u'. autorewrite with len.
    repeat (split; auto).
    - rewrite forallb_map /level_var_instance.
      rewrite forallb_map.
      rewrite [mapi_rec _ _ _]mapi_unfold forallb_unfold /= //.
      intros x Hx. rewrite lift_universe_singleton //= Universe.levels_singleton //=.
      apply LevelSet.subset_spec => lk. move/LS.singleton_spec => ->.
      apply LevelSet.mem_spec.
      apply In_Var_global_ext_poly. len.
    - destruct wfext as [onX onu]. simpl in *.
      destruct onu as [_ [_ [sat _]]].
      unfold PCUICLookup.global_ext_constraints in sat. simpl in sat.
      red. destruct check_univs => //.
      unfold valid_constraints0.
      intros val vsat.
      destruct sat as [val' allsat].
      red.
      intro. red in vsat.
      specialize (vsat x). intros hin. apply vsat.
      unfold global_ext_constraints. simpl.
      rewrite UnivConstraintSet.union_spec; left.
      rewrite /vcstrs !UnivConstraintSet.union_spec.
      left. right.
      rewrite In_lift_constraints.
      rewrite -> In_subst_instance_cstrs in hin.
      destruct hin as [c' [eqx inc']]. clear vsat.
      subst x. eexists. unfold subst_instance_univ_cstr.
      unfold lift_constraint. split; eauto. destruct c' as [[l comp] r].
      simpl.
      destruct wfctx as [_ wfctx]. simpl in wfctx.
      eapply on_udecl_poly_bounded in wfctx; auto.
      specialize (wfctx _ inc'). simpl in wfctx.
      move/andP: wfctx => [cll clr].
      rewrite !subst_instance_universe_lift //.
    - rewrite /level_var_instance.
      rewrite forallb_map [mapi_rec _ _ _]mapi_unfold forallb_unfold /= //.
      intros x Hx.
      apply LevelSet.subset_spec => lk. move/LS.singleton_spec => ->.
      apply LevelSet.mem_spec.
      apply In_Var_global_ext_poly. len.
    - destruct wfext as [onX onu]. simpl in *.
      destruct onu as [_ [_ [sat _]]].
      unfold PCUICLookup.global_ext_constraints in sat. simpl in sat.
      red. destruct check_univs => //.
      unfold valid_constraints0.
      intros val vsat.
      destruct sat as [val' allsat].
      red.
      intro. red in vsat.
      specialize (vsat x). intros hin. apply vsat.
      unfold global_ext_constraints. simpl.
      rewrite UnivConstraintSet.union_spec; left.
      rewrite /vcstrs !UnivConstraintSet.union_spec.
      left. left.
      rewrite -> In_subst_instance_cstrs in hin.
      destruct hin as [c' [eqx inc']]. clear vsat.
      subst x.
      destruct c' as [[l comp] r].
      simpl.
      destruct wfctx as [_ wfctx]. simpl in wfctx.
      eapply on_udecl_poly_bounded in wfctx; auto.
      specialize (wfctx _ inc'). simpl in wfctx.
      move/andP: wfctx => [cll clr]. rewrite /subst_instance_univ_cstr /=.
      rewrite !subst_instance_universe_var_instance //.
  Qed.

End OnUdecl.

Section CheckEnv.
  Context {cf:checker_flags} {nor : normalizing_flags}.

  Context (X_impl : abstract_env_impl).

  Definition X_env_ext_type := X_impl.π2.π1.

  Definition X_env_type := X_impl.π1.

  Implicit Type X_ext : X_env_ext_type.

  Implicit Type X : X_env_type.


(*  Local Definition gX := abstract_env_rel Σ. *)

  Local Definition heΣ X Σ (wfΣ : abstract_env_rel X Σ) :
    ∥ wf Σ ∥ :=  abstract_env_wf _ wfΣ.

  Local Definition hΣ X_ext Σ (wfΣ : abstract_env_ext_rel X_ext Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Definition check_wf_type (kn : kername) X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} t :
    EnvCheck X_env_ext_type (forall Σ : global_env_ext, abstract_env_ext_rel X_ext Σ -> ∥ isType Σ [] t ∥) :=
    wrap_error _ X_ext (string_of_kername kn) (check_isType X_impl X_ext [] (fun _ _ => sq_wfl_nil _) t).

  Definition check_wf_judgement kn X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} t ty :
  EnvCheck X_env_ext_type (forall Σ : global_env_ext, abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; [] |- t : ty ∥)
    :=  wrap_error _ X_ext (string_of_kername kn) (check X_impl X_ext [] (fun _ _ => sq_wfl_nil _) t ty).

  Definition infer_term X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} t :=
    wrap_error _ X_ext "toplevel term" (infer X_impl X_ext [] (fun _ _ => sq_wfl_nil _) t).

  Definition abstract_env_ext_empty := @abstract_env_empty_ext _ X_impl abstract_env_empty.

  Program Fixpoint check_fresh id env :
    EnvCheck X_env_ext_type (∥ fresh_global id env ∥) :=
    match env with
    | [] => ret (sq (Forall_nil _))
    | g :: env =>
      p <- check_fresh id env;;
      match eq_constant id g.1 with
      | true => EnvError X_env_ext_type abstract_env_ext_empty (AlreadyDeclared (string_of_kername id))
      | false => ret _
      end
    end.
  Next Obligation.
    sq. constructor; tas. simpl.
    change (false = eqb id k) in Heq_anonymous.
    destruct (eqb_spec id k); [discriminate|].
    easy.
  Qed.

  Section UniverseChecks.
  Obligation Tactic := idtac.

  (* Lemma consistent_extension_on_global Σ uctx :
    consistent_extension_on (global_uctx Σ) uctx ->
    consistent_extension_on Σ uctx.
  Proof using Type.
    move=> hext v {}/hext [v' [satv' eqv']].
    exists v'; split=> // x hx; apply: eqv'.
    apply/LevelSet.union_spec; by left.
  Qed. *)

  Definition declared_universe (ls : LevelSet.t) u : bool :=
    LevelSet.subset (Universe.levels u) ls.

  Definition abstract_declared_universe X (ls : LevelSet.t) u : bool :=
    LevelSet.for_all (abstract_env_level_mem' (abstract_env_empty_ext X) ls) (Universe.levels u).

  Lemma abstract_declared_universe_spec X u ls :
    abstract_declared_universe X ls u <->
    (forall Σ : global_env, abstract_env_rel X Σ -> LevelSet.Subset (Universe.levels u) (LevelSet.union ls (global_levels Σ))).
  Proof.
    split.
    - intros hd Σ eq.
      destruct (abstract_env_wf _ eq) as [wfΣ].
      red in hd.
      apply LevelSet.for_all_spec in hd.
      apply subset_levels.
      intros [l k] hin.
      specialize (hd l).
      move: hd => /fwd. apply Universe.levels_spec. now exists k.
      rewrite -(abstract_env_level_mem_correct' (abstract_env_empty_ext X) (Σ := (Σ, Monomorphic_ctx))) //.
      rewrite -abstract_env_empty_ext_rel. split => //.
      move/LevelSet.mem_spec => //. tc.
    - intros h; apply LevelSet.for_all_spec; tc.
      destruct (abstract_env_exists X) as [[Σ hΣ]].
      specialize (h _ hΣ).
      destruct (abstract_env_wf _ hΣ) => l.
      move/h => hin.
      rewrite -(abstract_env_level_mem_correct' (abstract_env_empty_ext X) (Σ := (Σ, Monomorphic_ctx))) //.
      rewrite -abstract_env_empty_ext_rel. split => //.
      now apply LevelSet.mem_spec.
  Qed.

  Definition uctx_of_udecl decl := (levels_of_udecl decl, constraints_of_udecl decl).

  Program Definition check_udecl id X (udecl : universes_decl)
    : EnvCheck X_env_ext_type (forall Σ : global_env, abstract_env_rel X Σ -> ∥ on_udecl Σ udecl ∥) :=
    let levels := levels_of_udecl udecl in
    check_eq_true_lazy (LevelSet.for_all (fun l => Level.is_var l) levels)
       (fun _ => (abstract_env_empty_ext X, IllFormedDecl id (Msg ("non fresh level in " ^ print_lset levels))));;
    check_eq_true_lazy (UnivConstraintSet.for_all (fun '(l1, _, l2) => abstract_declared_universe X levels l1 &&
      abstract_declared_universe X levels l2) (constraints_of_udecl udecl))
       (fun _ => (abstract_env_empty_ext X, IllFormedDecl id (Msg ("non declared level in " ^ print_lset levels ^
                                    " |= " ^ print_univ_constraint_set (constraints_of_udecl udecl)))));;
    check_eq_true (abstract_env_is_consistent X (uctx_of_udecl udecl))
        (abstract_env_empty_ext X, IllFormedDecl id (Msg "constraints not satisfiable"));;
      ret _.
  Next Obligation.
    simpl. intros id X udecl H H0 uctx' Σ wfΣ.
    split.
    pose proof (abstract_env_wf _ wfΣ) as [hΣ].
    assert (HH: UnivConstraintSet.For_all
                  (declared_univ_cstr_levels (LS.union (levels_of_udecl udecl) (global_levels Σ)))
                  (constraints_of_udecl udecl)).
    {
      clear -H0 wfΣ. apply UnivConstraintSet.for_all_spec in H0.
      2: now intros x y [].
      intros [[l ct] l'] Hl. specialize (H0 _ Hl). simpl in H0.
      apply andb_true_iff in H0. destruct H0 as [H H0].
      move/abstract_declared_universe_spec: H => /(_ _ wfΣ).
      move/abstract_declared_universe_spec: H0 => /(_ _ wfΣ).
      now cbn. }
    split; auto.
    - clear -H wfΣ. apply LevelSet.for_all_spec in H.
      2: now intros x y [].
      intros l Hl Hlglob.
      move: (wf_env_non_var_levels Σ (heΣ _ _ wfΣ) l Hlglob).
      now rewrite (H l Hl).
    - split; eauto.
      pose (HΣ := abstract_env_wf _ wfΣ); sq.
      apply wf_global_uctx_invariants in HΣ.
      (* enough (valid_on_mono_udecl (global_uctx Σ) udecl).
      1: { split. apply wf_consistent_extension_on_consistent => //.
           apply: consistent_extension_on_global=> //. } *)
      red. cbn.
      eapply abstract_env_is_consistent_correct in uctx'; tea.
      cbn in uctx'. rewrite /global_constraints in uctx'.
      rewrite /univs_ext_constraints. now rewrite UnivConstraintSetProp.union_sym.
      split => //.
      intros l hin hin'. apply LevelSet.for_all_spec in H.
      specialize (H l hin).
      have h := not_var_global_levels hΣ l hin' => //.
      now rewrite H in h. tc.
  Qed.

  Definition check_wf_env_ext_prop X X_ext ext :=
      (forall Σ : global_env, abstract_env_rel X Σ -> abstract_env_ext_rel X_ext (Σ, ext))
      /\ (forall Σ : global_env_ext, abstract_env_ext_rel X_ext Σ -> abstract_env_rel X Σ.1).

  Program Definition make_abstract_env_ext X (id : kername) (ext : universes_decl)
    :
    EnvCheck X_env_ext_type ({ X_ext | check_wf_env_ext_prop X X_ext ext})  :=
    match ext with
    | Monomorphic_ctx => ret (exist (abstract_env_empty_ext X) _)
    | Polymorphic_ctx _ =>
      uctx <- check_udecl (string_of_kername id) X ext ;;
      let X' := abstract_env_add_udecl X ext _ in
      ret (exist X' _)
    end.
  Next Obligation.
    simpl; intros. split; intros; try split.
    - cbn. pose proof (abstract_env_wf _ H). sq.
      eapply abstract_env_empty_ext_rel; eauto.
    - now apply abstract_env_empty_ext_rel in H.
  Qed.
  Next Obligation.
    simpl; cbn; intros. now apply uctx.
  Qed.
  Next Obligation.
    simpl; cbn; intros. split; intros ? ?.
    { rewrite Heq_ext. cbn.
      eapply abstract_env_add_udecl_rel; cbn; eauto. }
    { eapply abstract_env_add_udecl_rel with (udecl := ext) in H; cbn; try now eauto. }
  Qed.

  End UniverseChecks.

  Ltac specialize_Σ wfΣ :=
    repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end.

  Equations infer_typing X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ
      (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) t :
      typing_result (∑ T, forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; Γ |- t : T ∥) :=
    infer_typing X_ext Γ wfΓ t := typing_error_forget (infer X_impl X_ext Γ wfΓ t) ;;  ret _.
  Next Obligation.
    exists y. intros.
    pose proof (hΣ _ _ H). specialize_Σ H. sq. cbn in *. now apply infering_typing.
  Qed.

  Definition check_type_wf_env X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥)
      t T : typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; Γ |- t : T ∥) :=
    check X_impl X_ext Γ wfΓ t T.

  Definition infer_wf_env X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) t :
    typing_result (∑ T, forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; Γ |- t ▹ T ∥) :=
    infer X_impl X_ext Γ wfΓ t.

  Definition check_judgment_wf_env X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X_ext Σ), ∥ wf_local Σ Γ ∥) j (Hu : j_univ j = None)
    : typing_result (forall Σ (wfΣ : abstract_env_ext_rel X_ext Σ), ∥ lift_typing typing Σ Γ j ∥).
    eapply typing_error_forget.
    pose proof (infer_judgment X_impl X_ext (infer X_impl X_ext) Γ wfΓ (j_term j) (j_typ j) (j_rel j)) as X.
    rewrite -Hu in X.
    apply X.
  Defined.

  Definition infer_judgment_wf_env X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X_ext Σ), ∥ wf_local Σ Γ ∥) j (Hs : forall Σ (wfΣ : abstract_env_ext_rel X_ext Σ), option_default (fun s => ∥ wf_sort Σ s ∥) (j_univ j) True)
    : typing_result (∑ s', option_default (fun s => s = s') (j_univ j) True /\ forall Σ (wfΣ : abstract_env_ext_rel X_ext Σ), ∥ lift_typing typing Σ Γ (Judge (j_term j) (j_typ j) (Some s') (j_rel j)) ∥) :=
    infer_judgment0 X_impl X_ext (infer X_impl X_ext) Γ wfΓ (j_term j) (j_typ j) (j_univ j) Hs (j_rel j).

  Equations infer_type_wf_env X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) t :
    typing_result (∑ s, forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; Γ |- t : tSort s∥) :=
    infer_type_wf_env X_ext Γ wfΓ t :=
      '(y ; H) <- typing_error_forget (infer_type X_impl X_ext (infer X_impl X_ext) Γ wfΓ t) ;;
      ret (y ; _).
  Next Obligation.
    intros. pose proof (abstract_env_ext_wf _ H0). specialize_Σ H0.
    sq. now apply infering_sort_typing.
  Qed.

  Definition check_context_wf_env X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} (Γ : context) :
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) :=
    check_context X_impl X_ext (infer X_impl X_ext) Γ.

  (* Notation " ' pat <- m ;; f " := (bind m (fun pat => f)) (pat pattern, right associativity, at level 100, m at next level). *)

  Lemma inversion_it_mkProd_or_LetIn (Σ : global_env_ext) {wfΣ : wf Σ}:
    forall {Γ Δ s A},
      Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) : A ->
      isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s)).
  Proof using Type.
    intros Γ Δ s A h.
    enough (∑ s', Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) : tSort s').
    1: destruct X as (? & ?); now eapply has_sort_isType.
    revert Γ s A h.
    induction Δ using rev_ind; intros.
    - simpl in h |- *. eapply inversion_Sort in h as (?&?&?).
      eexists; constructor; eauto. apply wfΣ.
    - destruct x as [na [b|] ty]; simpl in *;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in h *.
      * eapply inversion_LetIn in h as [s' [? [? ?]]]; auto.
        specialize (IHΔ _ _ _ t) as [s'' vdefty].
        exists s''.
        eapply type_Cumul_alt. econstructor; eauto. pcuic.
        eapply red_cumul. repeat constructor.
      * eapply inversion_Prod in h as [? [? [h1 [? ?]]]]; auto.
        specialize (IHΔ _ _ _ t) as [s'' Hs''].
        exists (Sort.sort_of_product x s'').
        eapply type_Cumul'; eauto. econstructor; pcuic.
        apply unlift_TypUniv in h1. pcuic.
        reflexivity.
  Qed.

  Program Fixpoint check_type_local_ctx X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ}
     Γ Δ s (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) :
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ type_local_ctx (lift_typing typing) Σ Γ Δ s ∥) :=
    match Δ with
    | [] => match abstract_env_ext_wf_sortb X_ext s with true => ret _ | false => raise (Msg "Ill-formed universe") end
    | {| decl_body := None |} as decl :: Δ =>
      checkΔ <- check_type_local_ctx X_ext Γ Δ s wfΓ ;;
      checkty <- infer_judgment_wf_env X_ext (Γ ,,, Δ) _ (j_decl_s decl (Some s)) _ ;;
      ret _
    | {| decl_body := Some b |} as decl :: Δ =>
      checkΔ <- check_type_local_ctx X_ext Γ Δ s wfΓ ;;
      checkty <- check_judgment_wf_env X_ext (Γ ,,, Δ) _ (j_decl decl) _ ;;
      ret _
    end.
    Next Obligation.
      erewrite <- abstract_env_ext_wf_sortb_correct in Heq_anonymous; eauto.
      now sq; apply/PCUICWfUniverses.wf_sort_reflect.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq. now eapply PCUICContexts.type_local_ctx_wf_local in checkΔ.
    Qed.
    Next Obligation.
      pose proof (abstract_env_ext_wf _ wfΣ).
      specialize_Σ wfΣ. sq.
      now eapply PCUICInductives.type_local_ctx_wf.
    Qed.
    Next Obligation.
      specialize_Σ H.
      sq. split; auto.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq. now eapply PCUICContexts.type_local_ctx_wf_local in checkΔ.
    Qed.
    Next Obligation.
      specialize_Σ H. sq.
      split; auto.
    Qed.

  Program Fixpoint infer_sorts_local_ctx X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ Δ (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) :
    typing_result (∑ s, forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ sorts_local_ctx (lift_typing typing) Σ Γ Δ s ∥) :=
    match Δ with
    | [] => ret ([]; fun _ _ => sq _)
    | {| decl_body := None |} as decl :: Δ =>
      '(Δs; Δinfer) <- infer_sorts_local_ctx X_ext Γ Δ wfΓ ;;
      '(tys; tyinfer) <- infer_judgment_wf_env X_ext (Γ ,,, Δ) _ (j_decl decl) _ ;;
      ret ((tys :: Δs); _)
    | {| decl_body := Some _ |} as decl :: Δ =>
      '(Δs; Δinfer) <- infer_sorts_local_ctx X_ext Γ Δ wfΓ ;;
      checkty <- check_judgment_wf_env X_ext (Γ ,,, Δ) _ (j_decl decl) _ ;;
      ret (Δs; _)
    end.
    Next Obligation. exact tt. Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq. now eapply PCUICContexts.sorts_local_ctx_wf_local in Δinfer.
    Qed.
    Next Obligation.
      specialize_Σ H. sq. split; auto.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq. now eapply PCUICContexts.sorts_local_ctx_wf_local in Δinfer.
    Qed.
    Next Obligation.
      specialize_Σ H. sq. split; auto.
    Qed.

  Definition cumul_decl Pcmp Σ Γ (d d' : context_decl) : Type := cumul_decls Pcmp Σ Γ Γ d d'.

  Program Definition wf_env_conv X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} (le : conv_pb) (Γ : context) (t u : term) :
    (forall Σ, abstract_env_ext_rel X_ext Σ -> welltyped Σ Γ t) ->
    (forall Σ, abstract_env_ext_rel X_ext Σ -> welltyped Σ Γ u) ->
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ ->  ∥ Σ ;;; Γ ⊢ t ≤[le] u ∥) :=
    convert X_impl X_ext le Γ t u.

  Program Definition wf_env_check_cumul_decl X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} le Γ d d' :=
    check_ws_cumul_pb_decl X_impl X_ext le Γ d d'.

  Program Definition wf_env_check_ws_cumul_ctx (le : conv_pb) X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ Δ Δ'
    (wfΔ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ (Γ ,,, Δ) ∥)
    (wfΔ' : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ (Γ ,,, Δ') ∥) :
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ ws_cumul_ctx_pb_rel le Σ Γ Δ Δ' ∥) :=
    check_ws_cumul_ctx X_impl X_ext le Γ Δ Δ' wfΔ wfΔ'.

  Notation eqb_term_conv X conv_pb := (eqb_term_upto_univ (abstract_env_compare_universe X) (abstract_env_compare_sort X) (abstract_env_compare_global_instance _ X) conv_pb).

  Program Definition check_eq_term pb X_ext t u
     (wft : forall Σ, abstract_env_ext_rel X_ext Σ -> wf_universes Σ t)
     (wfu : forall Σ, abstract_env_ext_rel X_ext Σ -> wf_universes Σ u) :
      typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ compare_term Σ Σ pb t u ∥) :=
     check <- check_eq_true (eqb_term_conv X_ext pb t u) (Msg "Terms are not equal") ;;
    ret _.
    Next Obligation.
      simpl in *; sq.
      eapply cmpb_term_correct in check; sq; eauto.
    Qed.

  Program Definition check_eq_decl pb X_ext d d'
     (wfd : forall Σ, abstract_env_ext_rel X_ext Σ -> wf_decl_universes Σ d)
     (wfd' : forall Σ, abstract_env_ext_rel X_ext Σ -> wf_decl_universes Σ d') :
     typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ compare_decl Σ Σ pb d d' ∥) :=
    match d, d' return (forall Σ, abstract_env_ext_rel X_ext Σ -> wf_decl_universes Σ d) ->
                       (forall Σ, abstract_env_ext_rel X_ext Σ -> wf_decl_universes Σ d') ->
                       typing_result _ with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |},
      {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => fun _ _ =>
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      eqb <- check_eq_term Conv X_ext b b' _ _;;
      leqty <- check_eq_term pb X_ext ty ty' _ _;;
      ret (fun Σ wfΣ => _)
    | {| decl_name := na; decl_body := None; decl_type := ty |},
      {| decl_name := na'; decl_body := None; decl_type := ty' |} => fun _ _ =>
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumt <- check_eq_term pb X_ext ty ty' _ _ ;;
      ret (fun Σ wfΣ => _)
    | _, _ => fun _ _ => raise (Msg "While checking syntactic cumulativity of contexts: declarations do not match")
    end wfd wfd'.
    Next Obligation.
      specialize_Σ H. now pose proof i as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i0 as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i0 as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq.
      eapply eqb_binder_annot_spec in eqna.
      constructor; auto.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq.
      eapply eqb_binder_annot_spec in eqna.
      constructor; auto.
    Qed.

  Program Fixpoint check_compare_context (pb : conv_pb) X_ext Γ Δ
     (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> wf_ctx_universes Σ Γ)
     (wfΔ : forall Σ, abstract_env_ext_rel X_ext Σ -> wf_ctx_universes Σ Δ) :
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ PCUICEquality.compare_context Σ Σ pb Γ Δ ∥) :=
    match Γ, Δ return  (forall Σ, abstract_env_ext_rel X_ext Σ -> wf_ctx_universes Σ Γ) ->
                       (forall Σ, abstract_env_ext_rel X_ext Σ -> wf_ctx_universes Σ Δ) -> typing_result _
    with
    | [], [] => fun _ _ => ret (fun Σ wfΣ => sq (All2_fold_nil _))
    | decl :: Γ, decl' :: Δ => fun _ _ =>
      cctx <- check_compare_context pb X_ext Γ Δ _ _ ;;
      cdecl <- check_eq_decl pb X_ext decl decl' _ _ ;;
      ret (fun Σ wfΣ => _)
    | _, _ => fun _ _ => raise (Msg "While checking ws_cumul_pb of contexts: contexts do not have the same length")
    end wfΓ wfΔ.
    Next Obligation.
      specialize_Σ H. now pose proof i as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i0 as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i0 as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq.
      constructor; auto.
    Qed.

  Program Fixpoint check_leq_terms (pb : conv_pb) X_ext l l'
    (wfl : forall Σ, abstract_env_ext_rel X_ext Σ -> forallb (wf_universes Σ) l)
    (wfl' : forall Σ, abstract_env_ext_rel X_ext Σ -> forallb (wf_universes Σ) l') :
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ All2 (compare_term Σ Σ pb) l l' ∥) :=
    match l, l' return (forall Σ, abstract_env_ext_rel X_ext Σ -> forallb (wf_universes Σ) l) ->
                       (forall Σ, abstract_env_ext_rel X_ext Σ -> forallb (wf_universes Σ) l') -> _ with
    | [], [] => fun  _ _ => ret (fun Σ wfΣ => sq _)
    | t :: l, t' :: l' => fun _ _ =>
      cctx <- check_leq_terms pb X_ext l l' _ _ ;;
      cdecl <- check_eq_term pb X_ext t t' _ _;;
      ret (fun Σ wfΣ => _)
    | _, _ => fun _ _ => raise (Msg "While checking ws_cumul_pb of term lists: lists do not have the same length")
    end wfl wfl'.
    Next Obligation. apply All2_nil. Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i0 as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ H. now pose proof i0 as [? ?]%andb_and.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq. constructor; auto.
    Qed.

  Definition wt_terms Σ Γ l := Forall (welltyped Σ Γ) l.

  Program Fixpoint check_conv_args X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ (wfΓ : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) l l'
    (wfl : forall Σ, abstract_env_ext_rel X_ext Σ -> wt_terms Σ Γ l)
    (wfl' : forall Σ, abstract_env_ext_rel X_ext Σ -> wt_terms Σ Γ l') :
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ ws_cumul_pb_terms Σ Γ l l' ∥) :=
    match l, l' with
    | [], [] => ret (fun Σ wfΣ => sq All2_nil)
    | t :: l, t' :: l' =>
      checkt <- wf_env_conv X_ext Conv Γ t t' _ _ ;;
      checkts <- check_conv_args X_ext Γ wfΓ l l' _ _ ;;
      ret (fun Σ wfΣ => _)
    | _, _ => raise (Msg "While checking convertibility of arguments: lists have not the same length")
    end.
    Next Obligation.
      specialize_Σ H. now depelim wfl.
    Qed.
    Next Obligation.
      specialize_Σ H. now depelim wfl'.
    Qed.
    Next Obligation.
      specialize_Σ H. now depelim wfl.
    Qed.
    Next Obligation.
     specialize_Σ H. now depelim wfl'.
    Qed.
    Next Obligation.
      specialize_Σ wfΣ. sq. constructor; auto.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.

  Section MonadMapi.
    Context {T} {M : Monad T} {A B : Type} (f : nat -> A -> T B).

    Fixpoint monad_mapi_rec (n : nat) (l : list A) : T (list B) :=
      match l with
      | [] => ret []
      | x :: xs => x' <- f n x ;;
        xs' <- monad_mapi_rec (S n) xs ;;
        ret (x' :: xs')
      end.

    Definition monad_mapi (l : list A) := monad_mapi_rec 0 l.
  End MonadMapi.

  Definition check_constructor_spec Σ (ind : nat) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
    (cdecl : constructor_body) (cs : constructor_univs) :=
    isType Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl) *
    (cstr_type cdecl =
      it_mkProd_or_LetIn
        (mdecl.(ind_params) ,,, cdecl.(cstr_args))
        (mkApps (tRel (#|mdecl.(ind_params) ,,, cdecl.(cstr_args)| + (#|ind_bodies mdecl| - ind)))
          (to_extended_list_k mdecl.(ind_params) #|cdecl.(cstr_args)| ++
          cdecl.(cstr_indices)))) *
    (sorts_local_ctx (lift_typing typing) Σ
      (arities_context mdecl.(ind_bodies) ,,, ind_params mdecl) cdecl.(cstr_args)
      cs) *
    (cstr_arity cdecl = context_assumptions cdecl.(cstr_args)).

  Program Definition isRel_n n (t : term) : typing_result (t = tRel n) :=
    match t with
    | tRel k => match eqb k n with true => ret _ | false => raise (Msg "De-bruijn error") end
    | _ => raise (Msg "isRel_n: not a variable")
    end.
    Next Obligation.
      symmetry in Heq_anonymous.
      change (eqb k n : Prop) in Heq_anonymous.
      destruct (eqb_spec k n). congruence. discriminate.
    Qed.

  Program Definition decompose_cstr_concl mdecl (k : nat) argctx (t : term) : typing_result
    (∑ args, t = mkApps (tRel (#|mdecl.(ind_bodies)| - k + #|mdecl.(ind_params) ,,, argctx|)) args) :=
    let '(hd, args) := decompose_app t in
    eqr <- isRel_n (#|mdecl.(ind_bodies)| - k + #|mdecl.(ind_params) ,,, argctx|) hd ;;
    ret (args; _).
    Next Obligation.
      symmetry in Heq_anonymous.
      now apply decompose_app_inv in Heq_anonymous.
    Qed.

  Lemma decompose_prod_n_assum_inv ctx n t ctx' t' :
    decompose_prod_n_assum ctx n t = Some (ctx', t') ->
    it_mkProd_or_LetIn ctx t = it_mkProd_or_LetIn ctx' t'.
  Proof using Type.
    induction n in t, ctx, ctx', t' |- *; simpl.
    intros [= ->]. subst; auto.
    destruct t => //.
    intros Heq. specialize (IHn _ _ _ _ Heq).
    apply IHn.
    intros Heq. specialize (IHn _ _ _ _ Heq).
    apply IHn.
  Qed.

  Arguments eqb : simpl never.

  Definition wf_ind_type (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) :=
    isType Σ [] idecl.(ind_type) ×
    idecl.(ind_type) = it_mkProd_or_LetIn mdecl.(ind_params) (it_mkProd_or_LetIn idecl.(ind_indices) (tSort idecl.(ind_sort))) ×
    isSortRel idecl.(ind_sort) idecl.(ind_relevance).

  Definition wf_ind_types (Σ : global_env_ext) (mdecl : mutual_inductive_body) :=
    All (wf_ind_type Σ mdecl) mdecl.(ind_bodies).

  Lemma wf_ind_types_wf_arities (Σ : global_env_ext) (wfX : wf Σ) mdecl :
    wf_ind_types Σ mdecl ->
    wf_local Σ (arities_context mdecl.(ind_bodies)).
  Proof using Type.
    rewrite /wf_ind_types.
    unfold arities_context.
    induction 1; simpl; auto.
    assert (isty : isTypeRel Σ [] (ind_type x) Relevant)
    by (destruct p as (a & b & c); rewrite b in a |- *; eapply PCUICInductiveInversion.ind_arity_relevant => //).
    rewrite rev_map_cons /=.
    eapply All_local_env_app. constructor; pcuic.
    eapply All_local_env_impl; eauto.
    intros Γ j Hj.
    apply lift_typing_impl with (1 := Hj) => t T HT.
    eapply weaken_ctx; eauto.
    constructor; pcuic.
  Qed.

  Program Definition check_constructor X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} (ind : nat) (mdecl : mutual_inductive_body)
    (wfar : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ (ind_params mdecl) ∥)
    (idecl : one_inductive_body) (cdecl : constructor_body) :
    EnvCheck X_env_ext_type (∑ cs : constructor_univs, forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ check_constructor_spec Σ ind mdecl idecl cdecl cs ∥) :=

    Hs <- wrap_error _ X_ext ("While checking type of constructor: " ^ cdecl.(cstr_name))
      (check_judgment_wf_env X_ext (arities_context mdecl.(ind_bodies)) _ (Typ cdecl.(cstr_type)) _) ;;
    match decompose_prod_n_assum [] #|mdecl.(ind_params)| cdecl.(cstr_type) with
    | Some (params, concl) =>
      eqpars <- wrap_error _ X_ext cdecl.(cstr_name)
         (check_eq_true (eqb params mdecl.(ind_params))
        (Msg "Constructor parameters do not match the parameters of the mutual declaration"));;
      let '(args, concl) := decompose_prod_assum [] concl in
      eqarglen <- wrap_error _ X_ext cdecl.(cstr_name)
        (check_eq_true (eqb (context_assumptions args) cdecl.(cstr_arity))
          (Msg "Constructor arguments do not match the argument number of the declaration"));;
      eqarglen <- wrap_error _ X_ext cdecl.(cstr_name)
        (check_eq_true (eqb args cdecl.(cstr_args))
          (Msg "Constructor arguments do not match the arguments of the declaration"));;
        '(conclargs; Hargs) <- wrap_error _ X_ext cdecl.(cstr_name)
        (decompose_cstr_concl mdecl ind args concl) ;;
      eqbpars <- wrap_error _ X_ext cdecl.(cstr_name)
        (check_eq_true (eqb (firstn mdecl.(ind_npars) conclargs) (to_extended_list_k mdecl.(ind_params) #|args|))
          (Msg "Parameters in the conclusion of the constructor type do not match the inductive parameters")) ;;
      eqbindices <- wrap_error _ X_ext cdecl.(cstr_name)
        (check_eq_true (eqb (skipn mdecl.(ind_npars) conclargs) cdecl.(cstr_indices))
          (Msg "Indices in the conclusion of the constructor type do not match the indices of the declaration")) ;;
      '(cs; Hcs) <- wrap_error _ X_ext cdecl.(cstr_name)
        (infer_sorts_local_ctx X_ext (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params)) args _) ;;
      ret (cs; fun Σ wfΣ => _)
    | None =>
      raise (X_ext, IllFormedDecl cdecl.(cstr_name) (Msg "Not enough parameters in constructor type"))
    end.

    Next Obligation.
      pose proof (abstract_env_ext_wf _ wfΣ); specialize_Σ wfΣ; sq.
      now apply wf_ind_types_wf_arities in wfar.
    Qed.
    Next Obligation.
      pose proof (abstract_env_ext_wf _ H); specialize_Σ H; sq.
      apply wf_ind_types_wf_arities in wfar; eauto.
      now eapply weaken_wf_local; eauto.
    Qed.
    Next Obligation.
      pose proof (abstract_env_ext_wf _ wfΣ); specialize_Σ wfΣ.
      symmetry in Heq_anonymous0.
      eapply decompose_prod_n_assum_inv in Heq_anonymous0; simpl in Heq_anonymous0; subst.
      destruct (eqb_spec params (ind_params mdecl)) => //. subst params.
      destruct (eqb_spec args (cstr_args cdecl)) => //. subst args.
      eapply eqb_eq in eqarglen0.
      eapply eqb_eq in eqbindices.
      eapply eqb_eq in eqbpars.
      sq; red; cbn. intuition auto.
      symmetry in Heq_anonymous. eapply PCUICSubstitution.decompose_prod_assum_it_mkProd_or_LetIn in Heq_anonymous.
      simpl in Heq_anonymous. subst concl0.
      rewrite it_mkProd_or_LetIn_app.
      rewrite Heq_anonymous0. do 4 f_equal. len.
      rewrite -(firstn_skipn (ind_npars mdecl) x0); congruence.
    Qed.

  Fixpoint All_sigma {A B} {P : A -> B -> Type} {l : list A} (a : All (fun x => ∑ y : B, P x y) l) :
    ∑ l' : list B, All2 P l l' :=
    match a with
    | All_nil => ([]; All2_nil)
    | All_cons x l px pl =>
      let '(l'; pl') := All_sigma pl in
      ((px.π1 :: l'); All2_cons px.π2 pl')
    end.

  Fixpoint All2_sq {A B AA BB} {P : forall (a:AA), (BB a) -> A -> B -> Type} {l : list A} {l' : list B}
    (a : All2 (fun x y => forall (aa:AA) (bb:BB aa), ∥ P aa bb x y ∥) l l') (aa:AA) (bb:BB aa) : ∥ All2 (P aa bb) l l' ∥ :=
    match a with
    | All2_nil => sq All2_nil
    | All2_cons _ _ _ _ rxy all' =>
      let 'sq all := All2_sq all' aa bb in
      let 'sq rxy := rxy aa bb in
      sq (All2_cons rxy all)
    end.

   Definition check_constructors_univs X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} (id : ident) (mdecl : mutual_inductive_body)
    (wfar : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ (ind_params mdecl) ∥)
    (ind : nat) (idecl : one_inductive_body)
    (cstrs : list constructor_body) : EnvCheck X_env_ext_type (∑ cs : list constructor_univs,
     forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ All2 (fun cstr cs => check_constructor_spec Σ ind mdecl idecl cstr cs) cstrs cs ∥) :=
    css <- monad_All (fun d => check_constructor X_ext ind mdecl wfar wfpars idecl d) cstrs ;;
    let '(cs; all2) := All_sigma css in
    ret (cs ; fun Σ wfΣ => All2_sq all2 Σ wfΣ).

  Lemma isType_it_mkProd_or_LetIn_inv {Σ : global_env_ext} Γ Δ T :
    wf Σ ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    isType Σ (Γ ,,, Δ) T.
  Proof using Type.
    move=> wfX H.
    apply lift_sorting_it_impl_gen with H => // Hu.
    now eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hu.
  Qed.

  Lemma isType_mkApps_inv {Σ : global_env_ext} (wfΣ : wf Σ) Γ f args :
    isType Σ Γ (mkApps f args) ->
    ∑ fty s, (Σ ;;; Γ |- f : fty) *
      typing_spine Σ Γ fty args (tSort s).
  Proof using Type.
    intros (_ & s & Hs & _).
    eapply inversion_mkApps in Hs as [fty [Hf Hargs]]; auto.
    now exists fty, s.
  Qed.

  Definition smash_telescope acc Γ :=
    List.rev (smash_context acc (List.rev Γ)).

  Lemma ctx_inst_smash {Σ : global_env_ext} (wfΣ : wf Σ) (Γ Δ : context) args :
    ctx_inst Σ Γ args (smash_telescope [] Δ) ->
    ctx_inst Σ Γ args Δ.
  Proof using Type.
    rewrite /smash_telescope.
    intros H. apply ctx_inst_smash in H. now rewrite List.rev_involutive in H.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_inv {Σ : global_env_ext} {wfX : wf Σ} {Γ Δ s args s'} :
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) args (tSort s') ->
    ctx_inst Σ Γ args (List.rev Δ).
  Proof using Type.
    intros wf sp.
    pose proof (wf_local_smash_end _ _ wf). clear wf.
    eapply PCUICClassification.typing_spine_smash in sp; auto.
    unfold expand_lets, expand_lets_k in sp. simpl in sp.
    apply ctx_inst_smash; auto.
    rewrite /smash_telescope List.rev_involutive.
    revert X sp.
    move: (@smash_context_assumption_context [] Δ assumption_context_nil).
    move: (smash_context [] Δ) => {}Δ.
    induction Δ using PCUICInduction.ctx_length_rev_ind in s, s', args |- *; simpl;
      rewrite ?it_mkProd_or_LetIn_app;
    intros ass wf sp; dependent elimination sp as [spnil isty isty' e|spcons isty isty' e e' cum]; try constructor.
    * now eapply ws_cumul_pb_Sort_Prod_inv in e.
    * apply assumption_context_app in ass as [ass assd].
      destruct d as [na [b|] ty]; unfold mkProd_or_LetIn in e; simpl in *.
      exfalso; depelim assd.
      eapply ws_cumul_pb_Prod_Sort_inv in e; auto.
    * apply assumption_context_app in ass as [ass assd].
      destruct d as [na' [b'|] ty']; unfold mkProd_or_LetIn in e; simpl in *.
      exfalso; depelim assd.
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqann eqdom codom]; auto.
      rewrite List.rev_app_distr.
      constructor.
      eapply All_local_env_app_inv in wf as [wfΓ wfr].
      eapply All_local_env_app_inv in wfr as [wfd wfΓ0].
      depelim wfd. destruct l as [? Hs].
      eapply type_ws_cumul_pb; pcuic. eapply ws_cumul_pb_eq_le. now symmetry.
      rewrite subst_telescope_subst_context. cbn in *.
      have tyhd : Σ ;;; Γ |- hd0 : ty'.
      { eapply type_ws_cumul_pb; tea. eapply isType_tProd in isty as [].
        pcuic. eapply ws_cumul_pb_eq_le. now symmetry. }
      eapply X. now len.
      pcuic.
      eapply substitution_wf_local; eauto. eapply subslet_ass_tip; tea.
      rewrite app_context_assoc in wf; eapply wf.
      eapply typing_spine_strengthen; eauto.
      eapply isType_apply in isty; tea.
      now rewrite /subst1 subst_it_mkProd_or_LetIn in isty.
      eapply substitution0_ws_cumul_pb in codom; eauto.
      now rewrite /subst1 subst_it_mkProd_or_LetIn in codom.
  Qed.

  (* Lemma lift_LetIn na b ty T n k :
    lift n k (tLetIn na b ty T) =
    tLetIn na (lift n k b) (lift n k ty) (lift n (S k) T).
  Proof. reflexivity. Qed. *)

  Lemma typing_spine_letin_inv' {Σ : global_env_ext} {wfX : wf Σ} {Γ na b ty Δ T args T'} :
    let decl := {| decl_name := na; decl_body := Some b; decl_type := ty |} in
    isType Σ (Γ ,, decl) T ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (mkProd_or_LetIn (lift_decl (#|Δ| + 1) 0 decl) (lift (#|Δ| + 1) 1 T)) args T' ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (lift #|Δ| 0 T) args T'.
  Proof using Type.
    intros decl  isty.
    cbn. intros sp.
    pose proof (typing_spine_isType_dom sp) as isty'.
    eapply typing_spine_strengthen; eauto.
    eapply isType_lift; auto. len.  pcuic.
    now rewrite skipn_all_app.
    eapply ws_cumul_pb_eq_le.
    etransitivity.
    2:{ symmetry; eapply red_conv. repeat constructor.
        * now eapply isType_wf_local, wf_local_closed_context in isty'.
        * now eapply isType_is_open_term in isty'. }
    epose proof (distr_lift_subst _ [b] (#|Δ|+1) 0). cbn in H.
    rewrite /subst1. erewrite <- H.
    etransitivity.
    symmetry.
    epose proof (red_expand_let (isType_wf_local isty)).
    epose proof (weakening_ws_cumul_pb (pb:=Conv) (Γ := Γ ,, decl) (Γ' := []) (Γ'' := Δ)).
    simpl in X0.
    eapply X0.
    symmetry. eapply red_conv. apply X. fvs. eapply isType_wf_local, wf_local_closed_context in isty'. fvs.
    rewrite simpl_lift. lia. lia.
    eapply ws_cumul_pb_refl. eapply isType_wf_local in isty'. fvs.
    apply on_free_vars_lift0. rewrite /app_context /snoc; len.
    replace (#|Δ| + S #|Γ|) with (S #|Δ| + #|Γ|). 2:lia. rewrite Nat.add_1_r.
    rewrite -shiftnP_add addnP_shiftnP. eapply on_free_vars_subst.
    eapply isType_wf_local in isty. depelim isty. apply unlift_TermTyp in l as l0. cbn.
    rewrite andb_true_r. fvs.
    eapply isType_is_open_term in isty. cbn. now rewrite shiftnP_add.
  Qed.

  Lemma typing_spine_prod_inv {Σ : global_env_ext} {wfX : wf Σ} {Γ na ty Δ T args T'} :
    let decl := {| decl_name := na; decl_body := None; decl_type := ty |} in
    isType Σ (Γ ,, decl) T ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (mkProd_or_LetIn (lift_decl (#|Δ| + 1) 0 decl) (lift (#|Δ| + 1) 1 T))
      (tRel #|Δ| :: args) T' ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (lift #|Δ| 0 T) args T'.
  Proof using Type.
    intros decl wf.
    cbn. intros sp.
    dependent elimination sp as [spcons isty isty' e e' cum].
    have istyl : isType Σ (Γ,, decl,,, Δ) (lift0 #|Δ| T).
    { eapply isType_lift; tea. len. pcuic. now rewrite skipn_all_app. }
    eapply typing_spine_strengthen; eauto.
    eapply ws_cumul_pb_Prod_Prod_inv in e as [eqann eqdom eqcodom]; auto.
    eapply (substitution0_ws_cumul_pb (t:=tRel #|Δ|)) in eqcodom; auto.
    etransitivity; eauto.
    rewrite /subst1.
    replace ([tRel #|Δ|]) with (map (lift #|Δ| 0) [tRel 0]). 2:simpl; lia_f_equal.
    rewrite -(simpl_lift T _ _ _ 1); try lia.
    change 1 with (0 + #|[tRel 0]| + 0) at 1.
    rewrite -distr_lift_subst_rec /= //.
    rewrite subst_rel0_lift_id.
    now eapply ws_cumul_pb_eq_le, isType_ws_cumul_pb_refl.
  Qed.

  (** Non-trivial lemma:
    this shows that instantiating a product/let-in type with the identity substitution on some
    sub-context of the current context is the same as typechecking the remainder of the
    type approapriately lifted to directly refer to the variables in the subcontext.
    This is a quite common operation in tactics. Making this work up-to unfolding of
    let-ins is the tricky part.
  *)
  Lemma typing_spine_it_mkProd_or_LetIn_ext_list_inv_gen {Σ : global_env_ext} {wfX : wf Σ} {Γ Δ Δ' Δ'' : context} {s args s'} :
    wf_local Σ (Γ ,,, Δ ,,, Δ'') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ ,,, Δ'| 0 (Δ ,,, Δ'')) (tSort s))
      (to_extended_list_k Δ #|Δ'| ++ args) (tSort s') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ'| 0 Δ'') (tSort s))
      args (tSort s').
  Proof using Type.
    induction Δ using PCUICInduction.ctx_length_rev_ind in Γ, s, s', args, Δ' |- *; simpl;
      rewrite ?it_mkProd_or_LetIn_app;
    intros wf sp.
    * len in sp.
      now rewrite app_context_nil_l in sp.
    * set (decl := d) in *.
      assert (wf_sort Σ s).
      { eapply typing_spine_isType_dom in sp.
        eapply isType_it_mkProd_or_LetIn_inv in sp; auto.
        destruct sp as (_ & ? & Hs & _). now eapply inversion_Sort in Hs as [? []]. }
      destruct d as [na [b|] ty]. simpl in sp; unfold mkProd_or_LetIn in sp; simpl in *.
      - len in sp.
        rewrite lift_context_app /= it_mkProd_or_LetIn_app lift_context_app it_mkProd_or_LetIn_app /=
          -it_mkProd_or_LetIn_app in sp.
        replace (Γ,,, (Γ0 ++ [decl]),,, Δ') with (Γ,, decl,,, (Γ0,,, Δ')) in sp.
        2:rewrite !app_context_assoc //.
        epose proof (typing_spine_letin_inv' (Γ := Γ) (na:=na) (b:=b) (ty:=ty) (Δ := Γ0 ,,, Δ')).
        fold decl in X0.
        rewrite /lift_decl in X0. len in X0.
        rewrite Nat.add_assoc in sp.
        len in sp.
        rewrite -[_ ++ _](lift_context_app (#|Δ'| + #|Γ0| + 1) 1 Γ0 Δ'') in sp.
        rewrite -(lift_it_mkProd_or_LetIn _ _ _ (tSort _)) in sp.
        eapply X0 in sp. clear X0.
        rewrite lift_it_mkProd_or_LetIn in sp.
        rewrite app_context_assoc.
        rewrite to_extended_list_k_app in sp. simpl in sp.
        specialize (X Γ0 ltac:(now len) (Γ ,, decl) Δ' s args s').
        simpl in X.
        rewrite app_context_assoc in wf. specialize (X wf).
        forward X. rewrite app_context_assoc in sp. len.
        exact X.
        eapply isType_it_mkProd_or_LetIn; tea.
        eapply isType_Sort => //.
        now rewrite !app_context_assoc in wf *.
      - len in sp.
        rewrite lift_context_app /= it_mkProd_or_LetIn_app lift_context_app it_mkProd_or_LetIn_app /=
          -it_mkProd_or_LetIn_app in sp.
        replace (Γ,,, (Γ0 ++ [decl]),,, Δ') with (Γ,, decl,,, (Γ0,,, Δ')) in sp.
        2:rewrite !app_context_assoc //.
        rewrite to_extended_list_k_app in sp. simpl in sp.
        epose proof (typing_spine_prod_inv (na := na) (ty := ty) (Δ := Γ0 ,,, Δ')).
        fold decl in X0.
        rewrite /lift_decl in X0. len in X0.
        rewrite Nat.add_assoc in sp.
        len in sp.
        rewrite -[_ ++ _](lift_context_app (#|Δ'| + #|Γ0| + 1) 1 Γ0 Δ'') in sp.
        rewrite -(lift_it_mkProd_or_LetIn _ _ _ (tSort _)) in sp.
        rewrite {3}(Nat.add_comm #|Δ'| #|Γ0|) in X0.
        eapply X0 in sp. clear X0.
        rewrite lift_it_mkProd_or_LetIn in sp.
        rewrite app_context_assoc.
        specialize (X Γ0 ltac:(now len) (Γ ,, decl) Δ' s args s').
        simpl in X.
        rewrite app_context_assoc in wf. specialize (X wf).
        len in X. rewrite app_context_assoc in sp.
        now specialize (X sp).
        rewrite app_context_assoc in wf.
        eapply isType_it_mkProd_or_LetIn; auto.
        eapply isType_Sort; eauto. now rewrite app_context_assoc.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_ext_list_inv {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ' Δ'' s args s'} :
    wf_local Σ (Γ ,,, Δ ,,, Δ'') ->
    closedn_ctx 0 (Δ ,,, Δ'') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (Δ ,,, Δ'') (tSort s))
      (to_extended_list_k Δ #|Δ'| ++ args) (tSort s') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ'| 0 Δ'') (tSort s))
      args (tSort s').
  Proof using Type.
    intros.
    eapply typing_spine_it_mkProd_or_LetIn_ext_list_inv_gen; eauto.
    rewrite closed_ctx_lift //.
  Qed.

  Lemma firstn_all_app_eq {A : Type} (n : nat) (l l' : list A) :
    n = #|l| -> firstn n (l ++ l') = l.
  Proof using Type.
    intros ->.
    now rewrite -(Nat.add_0_r #|l|) firstn_app_2 firstn_0 // app_nil_r.
  Qed.

  Notation "'if' c 'then' vT 'else' vF" :=
    (match c with true => vT | false => vF end)
    (at level 200, c, vT, vF at level 200, only parsing).

  Equations discr_prod_letin (t : term) : Prop :=
    discr_prod_letin (tProd _ _ _) := False ;
    discr_prod_letin (tLetIn _ _ _ _) := False ;
    discr_prod_letin _ := True.

  Variant prod_letin_view : term -> Type :=
  | prod_letin_tProd : forall na dom codom, prod_letin_view (tProd na dom codom)
  | prod_letin_tLetIn : forall na b ty t, prod_letin_view (tLetIn na b ty t)
  | prod_letin_other : forall t, discr_prod_letin t -> prod_letin_view t.

  Equations prod_letin_viewc t : prod_letin_view t :=
    prod_letin_viewc (tProd na ty t) := prod_letin_tProd na ty t ;
    prod_letin_viewc (tLetIn na b ty t) := prod_letin_tLetIn na b ty t ;
    prod_letin_viewc t := prod_letin_other t I.

  Lemma welltyped_prod_inv {Σ : global_env_ext} {Γ na ty ty'} {wfΣ : wf Σ} :
    welltyped Σ Γ (tProd na ty ty') ->
    welltyped Σ Γ ty * welltyped Σ (Γ ,, vass na ty) ty'.
  Proof using Type.
    intros [s [s1 [s2 [hty [hty' hcum]]]]%inversion_Prod]; auto.
    apply unlift_TypUniv in hty; cbn in hty.
    split; eexists; eauto.
  Qed.

  Lemma welltyped_letin_inv {Σ : global_env_ext} {Γ na b ty t} {wfΣ : wf Σ} :
    welltyped Σ Γ (tLetIn na b ty t) ->
    welltyped Σ Γ ty *
    welltyped Σ Γ b *
    welltyped Σ (Γ ,, vdef na b ty) t.
  Proof using Type.
    intros [s [s1 [hty [hty' hcum]]]%inversion_LetIn]; auto.
    destruct hty as (hdef & s2 & hty & _); cbn in *.
    split; [split|]; eexists; eauto.
  Qed.

  Lemma welltyped_letin_red {Σ : global_env_ext} {Γ na b ty t} {wfX : wf Σ} :
    welltyped Σ Γ (tLetIn na b ty t) ->
    welltyped Σ Γ (subst0 [b] t).
  Proof using Type.
    intros [s [s1 [hdef [hty' hcum]]]%inversion_LetIn]; auto.
    exists (subst0 [b] s1).
    now eapply substitution_let in hty'.
  Qed.

  Section PositivityCheck.

    Context {X_ext : X_env_ext_type}.

    Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ}.

    Obligation Tactic := Program.Tactics.program_simpl.

    Program Definition isRel (t : term) : typing_result (∑ n, t = tRel n) :=
      match t with
      | tRel k => ret (k; _)
      | _ => raise (Msg "isRel: not a variable")
      end.

    (** Positivity checking involves reducing let-ins, so it can only be applied to
        already well-typed terms to ensure termination.

        We could also intersperse weak-head normalizations to reduce the types.
        This would need to be done in sync with a change in the spec in EnvironmentTyping though. *)

    Program Fixpoint check_positive_cstr_arg
      mdecl Γ t (wt : forall Σ, abstract_env_ext_rel X_ext Σ -> welltyped Σ Γ t) Δ
      {measure (Γ; t; wt) (@redp_subterm_rel cf _ X_ext)} : typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ positive_cstr_arg mdecl Δ t ∥) :=
      if closedn #|Δ| t then ret _
      else
      match prod_letin_viewc t in prod_letin_view t' with
      | prod_letin_tProd na ty t =>
        posarg <- check_eq_true (closedn #|Δ| ty) (Msg "Non-positive occurrence.");;
        post <- check_positive_cstr_arg mdecl (vass na ty :: Γ) t _ (vass na ty :: Δ) ;;
        ret _
      | prod_letin_tLetIn na b ty t =>
        post <- check_positive_cstr_arg mdecl Γ (subst0 [b] t) _ Δ ;;
        ret _
      | prod_letin_other t nprodlet =>
        let '(hd, args) := decompose_app t in
        '(hdrel; eqr) <- isRel hd ;;
        isind <- check_eq_true ((#|Δ| <=? hdrel) && (hdrel <? #|Δ| + #|ind_bodies mdecl|)) (Msg "Conclusion is not an inductive type") ;;
        (** Actually this is the only necessary check *)
        check_closed <- check_eq_true (forallb (closedn #|Δ|) args) (Msg "Conclusion arguments refer to the inductive type being defined") ;;
        match nth_error (List.rev mdecl.(ind_bodies)) (hdrel - #|Δ|) with
        | Some i =>
          check_eq_true (eqb (ind_realargs i) #|args|) (Msg "Partial application of inductive") ;;
          ret _
        | None => False_rect _ _
        end
      end.

      Next Obligation. sq.
        now constructor; rewrite -Heq_anonymous.
      Qed.

      Next Obligation.
        pose proof (abstract_env_ext_wf _ H); specialize_Σ H. sq.
        clear check_positive_cstr_arg.
        apply (welltyped_prod_inv wt).
      Qed.

      Next Obligation.
        sq. right. unshelve eexists. repeat constructor. now reflexivity.
      Qed.

      Next Obligation.
        pose proof (abstract_env_ext_wf _ H); specialize_Σ H. sq. constructor 4.
        now rewrite posarg.
        apply post.
      Qed.

      Next Obligation.
        pose proof (abstract_env_ext_wf _ H);  specialize_Σ H. sq.
        eapply (welltyped_letin_red wt).
      Qed.

      Next Obligation.
        sq; left. split; auto. repeat constructor.
      Qed.

      Next Obligation. pose proof (abstract_env_ext_wf _ H); specialize_Σ H. sq.
        now constructor 3.
      Qed.

      Next Obligation.
        clear eqr.
        move/andP: isind => [/Nat.leb_le le /Nat.ltb_lt lt].
        eapply forallb_All in check_closed. sq.
        symmetry in Heq_anonymous2; eapply decompose_app_inv in Heq_anonymous2.
        subst t0. econstructor 2; repeat constructor; eauto.
        match goal with [ H : is_true (eqb _ _) |- _ ] => now apply eqb_eq in H end.
      Qed.

      Next Obligation.
        clear eqr.
        move/andP: isind => [/Nat.leb_le le /Nat.ltb_lt lt].
        eapply forallb_All in check_closed. sq.
        symmetry in Heq_anonymous2; eapply decompose_app_inv in Heq_anonymous2.
        subst t0. symmetry in Heq_anonymous.
        eapply nth_error_None in Heq_anonymous.
        len in Heq_anonymous.
      Qed.

      Next Obligation.
        eapply Wf.measure_wf.
        unshelve eapply wf_redp_subterm; eauto.
      Defined.

    (** We already assume that constructor types are of the form `it_mkProd_or_LetIn (params,,, args) concl` so
        we don't need to reduce further. *)
    Program Fixpoint check_positive_cstr mdecl n Γ t
      (wt : forall Σ, abstract_env_ext_rel X_ext Σ -> welltyped Σ Γ t) Δ
      { measure (Γ; t; wt) (@redp_subterm_rel cf _ X_ext) }
      : typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ positive_cstr mdecl n Δ t ∥) :=
      match prod_letin_viewc t in prod_letin_view t' with
      | prod_letin_tProd na ty t =>
        posarg <- check_positive_cstr_arg mdecl Γ ty _ Δ ;;
        post <- check_positive_cstr mdecl n (vass na ty :: Γ) t _ (vass na ty :: Δ) ;;
        ret _
      | prod_letin_tLetIn na b ty t =>
        (* Do reduction *)
        post <- check_positive_cstr mdecl n Γ (subst0 [b] t) _ Δ ;;
        ret _
      | prod_letin_other t Ht =>
        let '(hd, indices) := decompose_app t in
        eqhd <- check_eq_true (eqb hd (tRel (#|ind_bodies mdecl| - S n + #|Δ|)))
          (Msg "Conclusion of constructor is not the right inductive type") ;;
          (* actually impossible with prior typing checks. *)
        closedargs <- check_eq_true (forallb (closedn #|Δ|) indices)
          (Msg "Arguments of the inductive in the conclusion of a constructor mention the inductive itself");;
        ret _
      end.

      Next Obligation.
        pose proof (abstract_env_ext_wf _ H);  specialize_Σ H. sq. eapply (welltyped_prod_inv wt).
      Qed.
      Next Obligation.
        pose proof (abstract_env_ext_wf _ H);  specialize_Σ H. sq. eapply (welltyped_prod_inv wt).
      Qed.
      Next Obligation.
        pose proof (abstract_env_ext_wf _ wfΣ); specialize_Σ wfΣ. sq. right. unshelve eexists. repeat constructor. reflexivity.
      Qed.
      Next Obligation.
        pose proof (abstract_env_ext_wf _ H); specialize_Σ H. sq. constructor 3; eauto.
      Qed.
      Next Obligation.
        pose proof (abstract_env_ext_wf _ H); specialize_Σ H. sq. eapply (welltyped_letin_red wt).
      Qed.
      Next Obligation.
        sq. left. repeat constructor.
      Qed.
      Next Obligation.
        pose proof (abstract_env_ext_wf _ H); specialize_Σ H. sq. now constructor 2.
      Qed.
      Next Obligation.
        pose proof (abstract_env_ext_wf _ H); specialize_Σ H. rename Heq_anonymous into eqa.
        symmetry in eqa; eapply decompose_app_inv in eqa.
        subst t0.
        move: eqhd; case: eqb_spec => // -> _.
        sq. constructor.
        now eapply forallb_All in closedargs.
      Qed.
      Next Obligation.
        eapply Wf.measure_wf.
        unshelve eapply wf_redp_subterm; eauto.
      Defined.
  End PositivityCheck.

  Definition wt_indices Σ mdecl indices cs :=
    wf_local Σ (ind_arities mdecl,,, ind_params mdecl,,, cs.(cstr_args)) *
    ctx_inst Σ (ind_arities mdecl,,, ind_params mdecl,,, cs.(cstr_args))
      (cs.(cstr_indices)) (List.rev (lift_context #|cs.(cstr_args)| 0 indices)).

  Lemma ctx_inst_wt Σ Γ s Δ :
    ctx_inst Σ Γ s Δ ->
    Forall (welltyped Σ Γ) s.
  Proof using Type.
    induction 1; try constructor; auto.
    now exists t.
  Qed.

  (* Now in PCUIC *)
  Lemma type_smash {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ : context} {t T} :
    Σ ;;; Γ ,,, Δ |- t : T ->
    Σ ;;; Γ ,,, smash_context [] Δ |- expand_lets Δ t : expand_lets Δ T.
  Proof using Type.
    revert Γ t T.
    induction Δ as [|[na [b|] ty] Δ] using PCUICInduction.ctx_length_rev_ind; simpl; auto.
    - intros. now rewrite! expand_lets_nil.
    - intros Γ t T h.
      rewrite !smash_context_app_def !expand_lets_vdef.
      eapply X. now len.
      eapply PCUICSubstitution.substitution; eauto.
      2:{ now rewrite app_context_assoc in h. }
      rewrite -{1}(subst_empty 0 b). repeat constructor.
      rewrite !subst_empty.
      eapply typing_wf_local in h.
      rewrite app_context_assoc in h. eapply All_local_env_app_inv in h as [h _].
      depelim h. now eapply unlift_TermTyp.
    - intros Γ t T h.
      rewrite !smash_context_app_ass !expand_lets_vass.
      rewrite app_context_assoc. eapply X. lia.
      now rewrite app_context_assoc in h.
  Qed.

  Lemma sub_context_set_empty Σ : sub_context_set ContextSet.empty (global_context_set Σ).
  Proof using Type.
    split; simpl.
    intros x hin. now eapply LS.empty_spec in hin.
    intros x hin. now eapply UCS.empty_spec in hin.
  Qed.

  Lemma cumul_ctx_rel_close' Σ Γ Δ Δ' :
    cumul_context cumulSpec0 Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
    cumul_ctx_rel cumulSpec0 Σ Γ Δ Δ'.
  Proof using Type.
    intros H.
    eapply All2_fold_app_inv in H as [cumΓ cumΔs]; auto.
    eapply All2_fold_length in H. len in H.
  Qed.

  Lemma wt_cstrs {n mdecl idecl cstrs cs} X_ext :
    (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ All2
      (fun (cstr : constructor_body) (cs0 : constructor_univs) =>
      check_constructor_spec Σ n mdecl idecl cstr cs0) cstrs cs ∥) ->
      forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ All (fun cstr => welltyped Σ (arities_context mdecl.(ind_bodies)) (cstr_type cstr)) cstrs ∥.
  Proof using Type.
    intros. specialize_Σ H0;  sq.
    solve_all. simpl.
    destruct X as [[[isTy _] _] _]. simpl in isTy.
    now eapply isType_welltyped in isTy.
  Qed.

  Lemma get_wt_indices {mdecl cstrs cs} X_ext
    (wfar : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ (ind_params mdecl) ∥)
    (n : nat) (idecl : one_inductive_body)
    (hnth : nth_error mdecl.(ind_bodies) n = Some idecl) :
    (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ All2
      (fun (cstr :constructor_body) (cs0 : constructor_univs) =>
      check_constructor_spec Σ (S n) mdecl idecl cstr cs0) cstrs cs ∥) ->
    forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ All (fun cs => wt_indices Σ mdecl idecl.(ind_indices) cs) cstrs ∥.
  Proof using Type.
    intros. pose proof (abstract_env_ext_wf _ H0) as wf; specialize_Σ H0. sq.
    solve_all. simpl.
    destruct X as [[[isTy eq] sorts] eq']. simpl in *.
    pose proof (wfars := wfar).
    eapply nth_error_all in wfar as (wfar & eqind); eauto.
    rewrite -it_mkProd_or_LetIn_app in eqind.
    assert(wf_local Σ (ind_params mdecl,,, idecl.(ind_indices))).
    { rewrite eqind in wfar.
      eapply isType_it_mkProd_or_LetIn_wf_local in wfar.
      now rewrite app_context_nil_l in wfar. }
    red. rewrite eq in isTy.
    eapply isType_it_mkProd_or_LetIn_inv in isTy; eauto.
    eapply isType_mkApps_inv in isTy as [fty [s [Hf Hsp]]]; auto.
    eapply inversion_Rel in Hf as [decl [wfctx [Hnth cum]]]; auto.
    rewrite nth_error_app_ge in Hnth. lia.
    split. now rewrite app_context_assoc in wfctx.
    replace (#|ind_params mdecl,,, cstr_args x| + (#|ind_bodies mdecl| - S n) -
    #|ind_params mdecl,,, cstr_args x|) with (#|ind_bodies mdecl| - S n) in Hnth by lia.
    pose proof (nth_error_Some_length hnth).
    rewrite nth_error_rev in hnth => //.
    assert (H1 := nth_error_arities_context _ _ _ hnth).
    rewrite Hnth in H1.
    noconf H1; simpl in *.
    eapply PCUICSpine.typing_spine_strengthen in Hsp; eauto.
    clear cum.
    move: Hsp. rewrite eqind.
    rewrite lift_it_mkProd_or_LetIn /= => Hs.
    rewrite closed_ctx_lift in Hs. eapply closed_wf_local; eauto.
    rewrite app_context_assoc in Hs wfctx.
    eapply typing_spine_it_mkProd_or_LetIn_ext_list_inv in Hs; auto.
    2:{ rewrite -app_context_assoc. eapply weaken_wf_local; auto.
        now eapply wf_ind_types_wf_arities. }
    2:{ eapply closed_wf_local; eauto. }
    eapply typing_spine_it_mkProd_or_LetIn_inv in Hs => //. auto.
    eapply weakening_wf_local; eauto.
    rewrite -app_context_assoc.
    eapply weaken_wf_local; eauto.
    now eapply wf_ind_types_wf_arities.
    len.
    rewrite nth_error_rev in hnth. len.
    rewrite List.rev_involutive in hnth. len in hnth.
    rewrite lift_closed; [now eapply isType_closed in wfar|].
    now eapply isType_weaken.
  Qed.

  Equations? check_variance {X} (name : kername) univs (variances : option (list Variance.t))
    (wfunivs : forall Σ, abstract_env_rel X Σ -> ∥ wf_ext (Σ, univs) ∥) :
    EnvCheck X_env_ext_type (forall Σ, abstract_env_rel X Σ -> ∥ on_variance Σ univs variances ∥) :=
    | name, univs, None, wfunivs := ret _
    | name, univs, Some v, wfunivs with inspect (variance_universes univs v) := {
      | exist (Some (univs', i, i')) eqvu =>
        check_leq <-
          check_eq_true (eqb #|v| #|polymorphic_instance univs|)
            (abstract_env_empty_ext abstract_env_empty, IllFormedDecl (string_of_kername name) (Msg "Variance annotation does not have the right length"));;
        Σ' <- make_abstract_env_ext X name univs' ;;
        ret _
        | exist None eqvu => raise (abstract_env_empty_ext abstract_env_empty, IllFormedDecl (string_of_kername name) (Msg "Ill-formed variance annotation")) }.
  Proof.
    - destruct H0 as [? ?]; eauto. specialize_Σ H.
      have [wfΣ] := abstract_env_ext_wf _ H0. sq.
      destruct univs => //.
      symmetry in eqvu.
      destruct (variance_universes_spec _ _ _ _ _ _ _ _ eqvu).
      exists univs', i, i'; split => //;
      now eapply eqb_eq in check_leq.
    - sq. red. destruct univs; auto.
  Qed.

  Definition Build_on_inductive_sq {X_ext ind mdecl}
    : (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ Alli (on_ind_body cumulSpec0 (lift_typing typing) Σ ind mdecl) 0 (ind_bodies mdecl) ∥) ->
      (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ (ind_params mdecl) ∥) ->
      context_assumptions (ind_params mdecl) = ind_npars mdecl ->
      (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_variance Σ (ind_universes mdecl) (ind_variance mdecl) ∥) ->
      forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_inductive cumulSpec0 (lift_typing typing) Σ ind mdecl ∥.
  Proof using Type.
    intros H H0 H1 H2 ? wf. specialize_Σ wf. sq. econstructor; try eassumption.
  Qed.

  Program Definition check_cstr_variance X mdecl (id : kername) indices
    (mdeclvar : forall Σ, abstract_env_rel X Σ -> ∥ on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance) ∥) cs
    (wfX : forall Σ, abstract_env_rel X Σ -> ∥ wf_ext (Σ, ind_universes mdecl) ∥)
    (wfΓ : forall Σ, abstract_env_rel X Σ -> ∥ wt_indices (Σ, ind_universes mdecl) mdecl indices cs ∥) :
    EnvCheck X_env_ext_type (forall Σ, abstract_env_rel X Σ -> ∥ forall v : list Variance.t,
                    mdecl.(ind_variance) = Some v ->
                    cstr_respects_variance cumulSpec0 Σ mdecl v cs ∥) :=
    match mdecl.(ind_variance) with
    | None => ret _
    | Some v =>
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some ((univs0, u), u') =>
        '(exist X' Xprop) <- make_abstract_env_ext X id univs0 ;;
        (* Incompleteness: this is an underapproximation of cumulativity of the contexts:
           in general we should allow unfolding and reduction to happen before comparing the types of arguments.
           However in many cases it will be sufficient. E.g. for lists and regular structures this is enough
           to check variance.

           Note that both contexts are well-typed in different contexts:
           ind_arities@{u} ,,, params@{u} for args@{u} and
           ind_arities@{u'} ,,, params@{u'} for args@{u'}.

           Hence we cannot use check_cumul_ctx here to verify the variance up-to conversion: the terms to be
           converted would be in different, incompatible contexts.

           TODO: do as in Rocq's kernel and implement a routine that takes whnfs of both sides and compare
           syntactically the heads. *)
        check_args <- wrap_error _ X' (string_of_kername id)
          (check_compare_context Cumul X'
            (subst_instance u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs))))
            (subst_instance u' (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs))))
             _ _) ;;
        check_indices <- wrap_error _ X' (string_of_kername id)
          (check_leq_terms Conv X'
            (map (subst_instance u ∘ expand_lets (ind_params mdecl ,,, cs.(cstr_args))) (cstr_indices cs))
            (map (subst_instance u' ∘ expand_lets (ind_params mdecl ,,, cs.(cstr_args))) (cstr_indices cs))
            _ _ ) ;;
        ret _
      | None => False_rect _ _
      end
    end.


  Lemma wf_decl_universes_subst_instance Σ udecl udecl' d u :
    wf_ext (Σ, udecl) ->
    wf_instance (Σ, udecl') u ->
    wf_decl_universes (Σ, udecl) d ->
    wf_decl_universes (Σ, udecl') d@[u].
  Proof using Type.
    intros [wfΣ onud] cu.
    destruct d => /=; rewrite /wf_decl_universes /on_decl_universes /= .
    move/andP => [] ondbody ontype.
    apply/andP; split.
    2:{ eapply (wf_universes_inst (Σ := (Σ, udecl')) udecl); cbn => //. apply onud. }
    destruct decl_body as [|] => /= //.
    eapply (wf_universes_inst (Σ := (Σ, udecl')) udecl); cbn => //. apply onud.
  Qed.

  Lemma wf_ctx_universes_subst_instance Σ udecl udecl' Γ u :
    wf_ext (Σ, udecl) ->
    wf_instance (Σ, udecl') u ->
    wf_ctx_universes (Σ, udecl) Γ ->
    wf_ctx_universes (Σ, udecl') Γ@[u].
  Proof using Type.
    intros wfΣ cu.
    induction Γ; cbn => //.
    move/andP=> [] wfa wfΓ.
    rewrite [forallb _ _](IHΓ wfΓ) andb_true_r.
    eapply wf_decl_universes_subst_instance; tea.
  Qed.

  Lemma wf_local_wf_ctx_universes {Σ Γ} : wf_ext Σ ->
    wf_local Σ Γ -> wf_ctx_universes Σ Γ.
  Proof using Type.
    intros wfΣ. unfold wf_ctx_universes.
    induction 1 => //=; rewrite IHX andb_true_r.
    destruct t0 as (_ & s & Hs & _). move/typing_wf_universes: Hs => /andP[] //.
    destruct t0 as (Hb & s & Hs & _). cbn in Hb. move/typing_wf_universes: Hb => /andP[] //.
  Qed.

  Lemma wf_ctx_universes_app {Σ Γ Δ} :
    wf_ctx_universes Σ (Γ ,,, Δ) = wf_ctx_universes Σ Γ && wf_ctx_universes Σ Δ.
  Proof using Type.
    now rewrite /wf_ctx_universes /app_context forallb_app andb_comm.
  Qed.

  Next Obligation.
      sq. by [].
    Qed.
    Next Obligation.
      pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
      specialize (mdeclvar _ wfΣ0). specialize_Σ wfΣ0.
      destruct Xprop as [Xprop ?]; eauto.
      unshelve erewrite (abstract_env_ext_irr _ _ (Xprop _ _)); eauto.
      sq. symmetry in Heq_anonymous.
      destruct H0. specialize (H0 _ wfΣ0).
      apply abstract_env_ext_wf in H0. destruct H0.
      eapply variance_universes_spec in Heq_anonymous; tea.
      eapply wf_ctx_universes_subst_instance; tea.
      destruct Heq_anonymous. now eapply consistent_instance_ext_wf in c.
      destruct wfΓ.
      eapply wf_local_smash_end in a.
      eapply wf_local_expand_lets in a.
      eapply wf_local_wf_ctx_universes in a; tea.
      rewrite wf_ctx_universes_app in a. move/andP: a => [] //.
    Qed.
    Next Obligation.
      pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
      specialize (mdeclvar _ wfΣ0). specialize_Σ wfΣ0.
      destruct Xprop as [Xprop ?]; eauto.
      unshelve erewrite (abstract_env_ext_irr _ _ (Xprop _ _)); eauto.
      sq.
      symmetry in Heq_anonymous.
      destruct H0. specialize (H0 _ wfΣ0).
      apply abstract_env_ext_wf in H0. destruct H0.
      eapply variance_universes_spec in Heq_anonymous; tea.
      eapply wf_ctx_universes_subst_instance; tea.
      destruct Heq_anonymous. now eapply consistent_instance_ext_wf in c0.
      destruct wfΓ.
      eapply wf_local_smash_end in a.
      eapply wf_local_expand_lets in a.
      eapply wf_local_wf_ctx_universes in a; tea.
      rewrite wf_ctx_universes_app in a. move/andP: a => [] //.
    Qed.

    Next Obligation.
      pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
      specialize (mdeclvar _ wfΣ0). specialize_Σ wfΣ0.
      destruct Xprop as [Xprop ?]; eauto.
      unshelve erewrite (abstract_env_ext_irr _ _ (Xprop _ _)); eauto.
      sq.
      symmetry in Heq_anonymous.
      destruct H0. specialize (H0 _ wfΣ0).
      apply abstract_env_ext_wf in H0. destruct H0.
      eapply variance_universes_spec in Heq_anonymous; tea.
      destruct Heq_anonymous as [c c0].
      destruct wfΓ as [wfargs wfinds]. eapply ctx_inst_wt in wfinds.
      solve_all. destruct H0 as [T wt].
      rewrite -app_context_assoc in wt.
      eapply typing_expand_lets in wt.
      eapply wf_universes_inst. eauto. eapply wfX.
      now eapply consistent_instance_ext_wf in c.
      cbn. eapply typing_wf_universes in wt; eauto.
      move/andP: wt => [] //.
    Qed.
    Next Obligation.
      pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
      specialize (mdeclvar _ wfΣ0). specialize_Σ wfΣ0.
      destruct Xprop as [Xprop ?]; eauto.
      unshelve erewrite (abstract_env_ext_irr _ _ (Xprop _ _)); eauto.
      sq.
      symmetry in Heq_anonymous.
      destruct H0. specialize (H0 _ wfΣ0).
      apply abstract_env_ext_wf in H0. destruct H0.
      eapply variance_universes_spec in Heq_anonymous; tea.
      destruct Heq_anonymous as [c c0].
      destruct wfΓ as [wfargs wfinds]. eapply ctx_inst_wt in wfinds.
      solve_all. destruct H0 as [T wt].
      rewrite -app_context_assoc in wt.
      eapply typing_expand_lets in wt.
      eapply wf_universes_inst. eauto. eapply wfX.
      now eapply consistent_instance_ext_wf in c0.
      cbn. eapply typing_wf_universes in wt; eauto.
      move/andP: wt => [] //.
    Qed.
    Next Obligation.
      pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
      destruct Xprop as [Xprop ?]; eauto.
      specialize (Xprop Σ0 wfΣ0). specialize_Σ Xprop. sq.
      intros v0 [= <-].
      red. rewrite -Heq_anonymous.
      split; auto. erewrite (abstract_env_irr _ _ wfΣ0); eauto.
      now eapply PCUICContextConversionTyp.eq_context_cumul_Spec_rel.
      clear check_args.
      eapply All2_impl. eauto. simpl; intros. erewrite (abstract_env_irr _ _ wfΣ0); eauto.
      now eapply eq_term_upto_univ_cumulSpec.
      Unshelve. all: eauto.
    Qed.
    Next Obligation.
      pose proof (abstract_env_exists X) as [[Σ wfΣ]]. specialize_Σ wfΣ. sq.
      sq. rewrite -Heq_anonymous0 in mdeclvar.
      symmetry in Heq_anonymous.
      eapply (variance_universes_insts (Σ := (empty_ext Σ))) in mdeclvar as [univs' [i [i' []]]].
      rewrite Heq_anonymous in e. discriminate.
    Qed.


  (** Moving it causes a universe bug... *)
  Section MonadAllAll.
    Context {AA : Type} {BB : AA -> Type} {T : Type -> Type} {M : Monad T} {A} {P : forall (aa:AA), BB aa -> A -> Type} {Q : forall (aa:AA), BB aa -> A -> Type}
    (f : forall x, (forall aa bb, ∥ Q aa bb x ∥) -> T (forall aa bb, ∥ P aa bb x ∥)).
    Program Fixpoint monad_All_All l :
      (forall (aa:AA) (bb: BB aa), ∥ All (Q aa bb) l ∥) ->
      T (forall (aa:AA) (bb:BB aa), ∥ All (P aa bb) l ∥) :=
      match l return (forall (aa:AA) (bb: BB aa), ∥ All (Q aa bb) l ∥) -> T (forall (aa:AA) (bb:BB aa) , ∥ All (P aa bb) l ∥) with
        | [] => fun _ => ret (fun aa bb  => sq All_nil)
        | a :: l => fun allq =>
        X <- f a _ ;;
        Y <- monad_All_All l _ ;;
        ret (fun aa bb  => _)
        end.
    Next Obligation.
      specialize_Σ bb. sq. now depelim allq.
    Qed.
    Next Obligation.
      specialize_Σ bb. sq. now depelim allq.
    Qed.
    Next Obligation.
      specialize_Σ bb. sq. constructor; assumption.
    Qed.
    End MonadAllAll.

    Section MonadLiftExt.
      Context {X:X_env_type} {X_ext:X_env_ext_type} {ext:universes_decl}
      {T : Type -> Type} {M : Monad T}
      {P : forall (Σ:global_env), abstract_env_rel X Σ -> Type}
      (XX_ext : forall (Σ:global_env_ext), abstract_env_ext_rel X_ext Σ -> abstract_env_rel X Σ.1)
      (XX_ext' : forall (Σ:global_env), abstract_env_rel X Σ -> abstract_env_ext_rel X_ext (Σ,ext)).

    Program Definition monad_lift_ext :
        T (forall (Σ:global_env) (wfΣ : abstract_env_rel X Σ), P Σ wfΣ) ->
        T (forall (Σ:global_env_ext) (wfΣ : abstract_env_ext_rel X_ext Σ), P Σ (XX_ext Σ wfΣ)) := fun x =>
        f <- x ;;
        ret _.

    End MonadLiftExt.

  Program Definition check_constructors X X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ}
    (id : kername) (mdecl : mutual_inductive_body)
    (HX : check_wf_env_ext_prop X X_ext (ind_universes mdecl))
    (wfar : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ (ind_params mdecl) ∥)
    (mdeclvar : forall Σ0, abstract_env_rel X Σ0 -> ∥ on_variance Σ0 mdecl.(ind_universes) mdecl.(ind_variance) ∥)
    (n : nat) (idecl : one_inductive_body)
    (hnth : nth_error mdecl.(ind_bodies) n = Some idecl)
    : EnvCheck X_env_ext_type (∑ cs : list constructor_univs,
    forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_constructors cumulSpec0 (lift_typing typing) Σ mdecl n idecl idecl.(ind_indices) (ind_ctors idecl) cs ∥) :=

    '(cs; Hcs) <- (check_constructors_univs X_ext (string_of_kername id) mdecl wfar
        wfpars (S n) idecl idecl.(ind_ctors));;
    posc <- wrap_error _ X_ext (string_of_kername id)
      (monad_All_All
       (fun x px =>
        @check_positive_cstr X_ext _ mdecl n
          (arities_context mdecl.(ind_bodies)) (cstr_type x) _ [])
        idecl.(ind_ctors) (wt_cstrs (cs:=cs) X_ext Hcs)) ;;
    var <- (monad_All_All
              (fun cs px => @monad_lift_ext X X_ext (EnvCheck X_env_ext_type) _ _ _
                                            (check_cstr_variance X mdecl id idecl.(ind_indices) mdeclvar cs _ _))
              idecl.(ind_ctors) (get_wt_indices X_ext wfar wfpars n idecl hnth Hcs)) ;;
    lets <-
       monad_All (P := fun x => if @lets_in_constructor_types _ as _ return Prop then true else is_assumption_context (cstr_args x))
     (fun cs => if @lets_in_constructor_types _
      then ret _ else
       (if is_assumption_context (cstr_args cs) then ret _
       else EnvError X_env_ext_type X_ext
       (IllFormedDecl "No lets in constructor types allowed, you need to set the checker flag lets_in_constructor_types to [true]."
        (Msg "No lets in constructor types allowed, you need to set the checker flag lets_in_constructor_types to [true].")  ))
    ) idecl.(ind_ctors) ;;
    ret (cs; _).
    Next Obligation. specialize_Σ H. now sq. Qed.
    Next Obligation. destruct HX as [? HX]; eauto. Qed.
    Next Obligation. specialize_Σ H. destruct HX as [? ?].
          specialize_Σ H. now pose proof (abstract_env_ext_wf _ H0). Qed.
    Next Obligation. specialize_Σ H. now destruct HX as [? ?].  Qed.
    Next Obligation.
      destruct lets_in_constructor_types.
      + reflexivity.
      + red. congruence.
    Qed.
    Next Obligation.
      destruct lets_in_constructor_types; congruence.
    Qed.
    Next Obligation.
      epose proof (get_wt_indices X_ext wfar wfpars _ _ hnth Hcs).
      destruct HX.
      specialize_Σ H.
      pose proof (abstract_env_ext_wf _ (H1 _ H2)) as wfΣ.
      unfold check_constructor_spec in Hcs; simpl in *. sq.
      solve_all.
      eapply All2_impl; eauto. simpl.
      intros.
      destruct X1 as [[lets [wtinds [wfvar posc]]] [[[isTy eq]] eq']].
      econstructor => //.
      - rewrite eq.
        rewrite it_mkProd_or_LetIn_app. autorewrite with len. lia_f_equal.
        rewrite /cstr_concl /=. f_equal. rewrite /cstr_concl_head. lia_f_equal.
      - eapply All_nth_error in wfar; tea.
        destruct wfar as (isty & e & eqrel), wtinds.
        eapply PCUICInductiveInversion.isTypeRel_cstr_type; eauto. apply wfΣ.
      - destruct wtinds as (? & ci).
        apply PCUICEnvTyping.ctx_inst_impl with (1 := ci) => t T HT.
        split; auto.
        unshelve eapply validity in HT as []; eauto.
        apply wfΣ.
      - destruct lets_in_constructor_types; eauto.
    Qed.

  Definition check_projections_type (mind : kername)
    (mdecl : mutual_inductive_body) (i : nat) (idecl : one_inductive_body)
    (indices : context) :=
    match ind_projs idecl, idecl.(ind_ctors) return Type with
    | [], _ => True
    | _, [cs] => on_projections mdecl mind i idecl indices cs
    | _, _ => False
    end.

  Program Definition check_projection X_ext (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context)
    (cdecl : constructor_body) (cs : constructor_univs)
    (oncs : forall Σ, abstract_env_ext_rel X_ext Σ ->  ∥ on_constructors cumulSpec0 (lift_typing typing) Σ mdecl i idecl indices [cdecl] [cs] ∥)
    (k : nat) p (hnth : nth_error idecl.(ind_projs) k = Some p)
    (heq : #|idecl.(ind_projs)| = context_assumptions cdecl.(cstr_args))
    : typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_projection mdecl mind i cdecl k p ∥) :=
    let Γ :=  smash_context [] (cdecl.(cstr_args) ++ ind_params mdecl) in
    match nth_error Γ (context_assumptions (cdecl.(cstr_args)) - S k) with
    | Some decl =>
      let u := abstract_instance (ind_universes mdecl) in
      let ind := {| inductive_mind := mind; inductive_ind := i |} in
      check_na <- check_eq_true (eqb (binder_name (decl_name decl)) (nNamed p.(proj_name)))
        (Msg "Projection name does not match argument binder name");;
      check_rel <- check_eq_true (eqb (binder_relevance (decl_name decl)) p.(proj_relevance))
        (Msg "Projection relevance does not match argument binder relevance");;
      check_eq <- check_eq_true (eqb p.(proj_type)
          (subst (inds mind u (ind_bodies mdecl)) (S (ind_npars mdecl))
          (subst0 (projs ind (ind_npars mdecl) k) (lift 1 k (decl_type decl)))))
        (Msg "Projection type does not match argument type") ;;
      ret _
    | None => False_rect _ _
    end.
  Next Obligation.
    eapply eqb_eq in check_na.
    eapply eqb_eq in check_rel.
    eapply eqb_eq in check_eq.
    sq.
    red. rewrite -Heq_anonymous. simpl. split; auto.
  Qed.
  Next Obligation.
    pose proof (abstract_env_ext_exists X_ext) as [[? H]]. specialize_Σ H. depelim oncs.
    rename Heq_anonymous into hnth'.
    symmetry in hnth'. eapply nth_error_None in hnth'.
    eapply nth_error_Some_length in hnth.
    len in hnth'.
  Qed.

  Section monad_Alli_nth_forall.
  Context {AA : Type} {BB : AA -> Type}  {T} {M : Monad T} {A} {P : forall (aa:AA), BB aa -> nat -> A -> Type}.
  Program Fixpoint monad_Alli_nth_gen_forall l k
    (f : forall n x, nth_error l n = Some x -> T (forall aa bb, ∥ P aa bb (k + n) x ∥)) :
    T (forall aa bb, ∥ @Alli A (P aa bb) k l ∥)
    := match l with
      | [] => ret (fun _ _ => sq Alli_nil)
      | a :: l => X <- f 0 a _ ;;
                  Y <- monad_Alli_nth_gen_forall l (S k) (fun n x hnth => px <- f (S n) x hnth;; ret _) ;;
                  ret _
      end.
    Next Obligation.
      specialize_Σ bb. sq. now rewrite Nat.add_succ_r in px.
    Qed.
    Next Obligation.
      specialize_Σ bb. sq. rewrite Nat.add_0_r in X. constructor; auto.
    Qed.

  Definition monad_Alli_nth_forall l (f : forall n x, nth_error l n = Some x -> T (forall aa bb, ∥ P aa bb n x ∥)) :
    T (forall aa bb, ∥ @Alli A (P aa bb) 0 l ∥) :=
    monad_Alli_nth_gen_forall l 0 f.

End monad_Alli_nth_forall.


  Program Definition check_projections_cs X_ext (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context)
    (cdecl : constructor_body) (cs : constructor_univs)
    (oncs : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_constructors cumulSpec0 (lift_typing typing) Σ mdecl i idecl indices [cdecl] [cs] ∥)
    (onec : #|idecl.(ind_ctors)| = 1) :
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_projections mdecl mind i idecl indices cdecl ∥) :=
    check_indices <- check_eq_true (eqb [] indices) (Msg "Primitive records cannot have indices") ;;
    check_elim <- check_eq_true (eqb (ind_kelim idecl) IntoAny) (Msg "Primitive records must be eliminable to Type");;
    check_length <- check_eq_true (eqb #|idecl.(ind_projs)| (context_assumptions cdecl.(cstr_args)))
      (Msg "Invalid number of projections") ;;
     check_projs <- monad_Alli_nth_forall idecl.(ind_projs)
      (fun n p hnth => check_projection X_ext mind mdecl i idecl indices cdecl cs oncs n p hnth (eqb_eq _ _ check_length)) ;;
    ret _.

    Next Obligation.
      specialize_Σ H. sq. depelim oncs. depelim oncs.
      eapply eqb_eq in check_indices; subst indices.
      eapply eqb_eq in check_elim. eapply eqb_eq in check_length.
      constructor => //.
    Qed.

  Program Definition check_projections X_ext (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) (cs : list constructor_univs) :
    (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_constructors cumulSpec0 (lift_typing typing) Σ mdecl i idecl indices idecl.(ind_ctors) cs ∥) ->
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ check_projections_type mind mdecl i idecl indices ∥) :=
    match ind_projs idecl with
    | [] => fun _ => ret _
    | _ =>
      match idecl.(ind_ctors) as x, cs with
      | [ cdecl ], [ cs ] => fun oncs =>
        ccs <- check_projections_cs X_ext mind mdecl i idecl indices cdecl cs _ _ ;;
        ret _
      | _, _ => fun oncs => raise (Msg "Projections can only be declared for an inductive type with a single constructor")
      end
    end.
  Next Obligation.
    rename Heq_anonymous into eqp.
    sq. red. rewrite -eqp. exact I.
  Qed.
  (* Obligation automatically solved in the presence of Rocq PR #18921
  Next Obligation. specialize_Σ H. Show. sq. Show. rewrite Heq_x. eauto. Qed.
  *)
  Next Obligation.
    specialize_Σ H. sq. red. intros. rewrite -Heq_x //.
    destruct ind_projs => //.
  Qed.

  Definition checkb_constructors_smaller X_ext (cs : list constructor_univs) (ind_sort : sort) :=
    List.forallb (List.forallb (fun argsort => abstract_env_compare_sort X_ext Cumul argsort ind_sort)) cs.

  Definition wf_cs_sorts X_ext cs :=
    forall Σ, abstract_env_ext_rel X_ext Σ -> Forall (Forall (wf_sort Σ)) cs.

  Lemma check_constructors_smallerP X_ext cs ind_sort :
    wf_cs_sorts X_ext cs ->
    (forall Σ, abstract_env_ext_rel X_ext Σ -> wf_sort Σ ind_sort) ->
    forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ reflect (check_constructors_smaller Σ cs ind_sort) (checkb_constructors_smaller X_ext cs ind_sort) ∥.
  Proof using Type.
    unfold check_constructors_smaller, checkb_constructors_smaller.
    intros wfcs wfind ? ?. specialize_Σ H.
    sq.
    eapply forallbP_cond; eauto. clear wfcs.
    simpl; intros c wfc.
    eapply forallbP_cond; eauto. simpl. intros x wfx. specialize_Σ H.
    apply iff_reflect. apply (abstract_env_compare_sort_correct _ H Cumul); eauto.
  Qed.

  Program Definition do_check_ind_sorts X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} (params : context)
    (wfparams : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ params ∥)
    (kelim : allowed_eliminations) (indices : context)
    (cs : list constructor_univs)
    (wfcs : wf_cs_sorts X_ext cs)
    (ind_sort : sort)
    (wfi : forall Σ, abstract_env_ext_rel X_ext Σ -> wf_sort Σ ind_sort):
    typing_result (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ check_ind_sorts (lift_typing typing) Σ params kelim indices cs ind_sort ∥) :=
    match ind_sort with
    | sSProp =>
      check_eq_true (allowed_eliminations_subset kelim (elim_sort_sprop_ind cs))
        (Msg "Incorrect allowed_elimination for inductive") ;;
      ret _
    | sProp =>
      check_eq_true (allowed_eliminations_subset kelim (elim_sort_prop_ind cs))
        (Msg "Incorrect allowed_elimination for inductive") ;; ret _
    | sType u =>
      check_eq_true (checkb_constructors_smaller X_ext cs ind_sort)
        (Msg ("Incorrect inductive sort: The constructor arguments universes are not smaller than the declared inductive sort")) ;;
      match indices_matter with
      | true =>
        (* FIXME this is a strict underapproximation, we should use sorts_local_ctx as the indices might be
          in sorts which don't necessarily have a sup. *)
        tyloc <- check_type_local_ctx X_ext params indices ind_sort wfparams ;;
        ret _
      | false => ret _
      end
    end.

    Next Obligation.
      unfold check_ind_sorts. simpl.
      pose proof (check_constructors_smallerP X_ext cs (sType u) wfcs wfi).
      rewrite -Heq_anonymous. specialize_Σ H.  sq. split => //.
      match goal with [ H : reflect _ _ |- _ ] => destruct H => // end.
    Qed.
    Next Obligation.
      unfold check_ind_sorts. simpl.
      pose proof (check_constructors_smallerP X_ext cs (sType u) wfcs wfi).
      specialize_Σ H. sq. split.
      match goal with [ H : reflect _ _ |- _ ] => destruct H => // end.
      rewrite -Heq_anonymous; auto.
    Qed.

  Lemma sorts_local_ctx_wf_sorts (Σ : global_env_ext) {wfX : wf Σ} Γ Δ s :
    sorts_local_ctx (lift_typing typing) Σ Γ Δ s ->
    Forall (wf_sort Σ) s.
  Proof using Type.
    induction Δ in s |- *; destruct s; simpl; auto.
    destruct a as [na [b|] ty].
    - intros []. eauto.
    - intros []; eauto. constructor; eauto.
      apply unlift_TypUniv in l.
      now eapply typing_wf_sort in l.
  Qed.

  Obligation Tactic := Program.Tactics.program_simplify.

  Program Definition check_indices X mdecl (id : kername)
    (wfX : forall Σ, abstract_env_rel X Σ -> ∥ wf_ext (Σ, ind_universes mdecl) ∥)
    (mdeclvar : forall Σ, abstract_env_rel X Σ -> ∥ on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance) ∥)
    indices (wfΓ : forall Σ, abstract_env_rel X Σ -> ∥ wf_local (Σ, ind_universes mdecl) (ind_params mdecl ,,, indices) ∥) :
    EnvCheck X_env_ext_type (forall Σ, abstract_env_rel X Σ -> ∥ match mdecl.(ind_variance) with
                    None => True | Some v =>
                    ind_respects_variance cumulSpec0 Σ mdecl v indices end ∥) :=
    match mdecl.(ind_variance) with
    | None => ret _
    | Some v =>
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some ((univs0, u), u') =>
        '(exist wfext eq) <- make_abstract_env_ext X id univs0 ;;
        checkctx <- wrap_error _ wfext (string_of_kername id)
          (check_compare_context Cumul wfext (subst_instance u (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
            (subst_instance u' (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
            _ _) ;;
        ret _
      | None => False_rect _ _
      end
    end.
  Next Obligation.
    sq. exact I.
  Qed.
  Next Obligation.
    pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
    specialize (mdeclvar _ wfΣ0). specialize_Σ wfΣ0.
    destruct H0 as [Xprop ?]; eauto.
    unshelve erewrite (abstract_env_ext_irr _ _ (Xprop _ _)); eauto.
    sq. symmetry in Heq_anonymous.
    specialize (Xprop _ wfΣ0).
    apply abstract_env_ext_wf in Xprop. destruct Xprop.
    eapply variance_universes_spec in Heq_anonymous as [cu cu']; tea.
    eapply wf_ctx_universes_subst_instance; tea.
    now eapply consistent_instance_ext_wf in cu.
    move/wf_local_smash_end: wfΓ.
    rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
    move/wf_local_expand_lets; rewrite app_context_nil_l.
    move/wf_local_wf_ctx_universes. rewrite wf_ctx_universes_app.
    move/andP => [] //.
  Qed.
  Next Obligation.
    pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
    specialize (mdeclvar _ wfΣ0). specialize_Σ wfΣ0.
    destruct H0 as [Xprop ?]; eauto.
    unshelve erewrite (abstract_env_ext_irr _ _ (Xprop _ _)); eauto.
    sq. symmetry in Heq_anonymous.
    specialize (Xprop _ wfΣ0).
    apply abstract_env_ext_wf in Xprop. destruct Xprop.
    eapply variance_universes_spec in Heq_anonymous as [cu cu']; tea.
    eapply wf_ctx_universes_subst_instance; tea.
    now eapply consistent_instance_ext_wf in cu'.
    move/wf_local_smash_end: wfΓ.
    rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
    move/wf_local_expand_lets; rewrite app_context_nil_l.
    move/wf_local_wf_ctx_universes. rewrite wf_ctx_universes_app.
    move/andP => [] //.
  Qed.
  Next Obligation.
    destruct eq as [? ?]; eauto. specialize_Σ H.
    specialize_Σ H1.
    rename Heq_anonymous0 into eqvar.
    rename Heq_anonymous into eqvaru.
    sq. red. simpl.
    rewrite -eqvaru.
    unfold variance_universes in eqvaru.
    unfold on_variance in mdeclvar.
    rewrite -eqvar in mdeclvar.
    destruct (ind_universes mdecl) as [|[inst cstrs]] => //.
    now eapply PCUICContextConversionTyp.eq_context_cumul_Spec_rel.
  Qed.

  Next Obligation.
    rename Heq_anonymous0 into eqvar.
    rename Heq_anonymous into eqvaru.
    pose proof (abstract_env_exists X) as [[Σ H]]. specialize_Σ H.
    sq. rewrite -eqvar in mdeclvar.
    eapply (variance_universes_insts (Σ := empty_ext Σ)) in mdeclvar as [univs' [i [i' []]]].
    rewrite -eqvaru in e; discriminate.
  Qed.

  Program Definition check_ind_type X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
    : EnvCheck X_env_ext_type (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_ind_type Σ mdecl idecl ∥) :=

    '(ctxinds; p) <-
      wrap_error _ X_ext idecl.(ind_name) ((match destArity [] idecl.(ind_type) as da return da = destArity [] idecl.(ind_type) -> typing_result (∑ ctxs, idecl.(ind_type) = it_mkProd_or_LetIn ctxs.1 (tSort ctxs.2)) with
      | Some (ctx, s) => fun eq => ret ((ctx, s); _)
      | None => fun _ => raise (NotAnArity idecl.(ind_type))
      end eq_refl)) ;;
    let '(indices, params) := split_at (#|ctxinds.1| - #|mdecl.(ind_params)|) ctxinds.1 in
    eqsort <- wrap_error _ X_ext idecl.(ind_name)
      (check_eq_true (eqb ctxinds.2 idecl.(ind_sort))
      (Msg "Inductive body sort does not match the sort of the inductive type"));;
    check <- wrap_error _ X_ext idecl.(ind_name) (check_eq_true (relevance_of_sort (ind_sort idecl) == (ind_relevance idecl)) (Msg "Wrong relevance")) ;;
    (* Can probably be deduced instead of checked *)
    eqpars <- wrap_error _ X_ext idecl.(ind_name)
      (check_eq_true (eqb params mdecl.(ind_params))
      (Msg "Inductive arity parameters do not match the parameters of the mutual declaration"));;
    eqindices <- wrap_error _ X_ext idecl.(ind_name)
      (check_eq_true (eqb indices idecl.(ind_indices))
      (Msg "Inductive arity indices do not match the indices of the mutual declaration"));;
    isty <- wrap_error _ X_ext idecl.(ind_name)
      (infer_type_wf_env X_ext [] (fun _ _ => sq_wfl_nil _) idecl.(ind_type)) ;;
    ret _.

  Next Obligation.
    symmetry in eq.
    apply destArity_spec_Some in eq. now simpl in eq.
  Qed.
  Next Obligation.
    specialize_Σ H.
    sq. splits.
    solve_all.
    - now exists isty.
    - destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
      rewrite split_at_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
      rewrite -it_mkProd_or_LetIn_app {1}H0. apply eqb_eq in eqindices, eqsort.
      rewrite -eqindices -eqsort. now rewrite /app_context firstn_skipn.
    - apply eqb_eq, check.
  Qed.

  Program Definition check_ind_types X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} (mdecl : mutual_inductive_body)
      : EnvCheck X_env_ext_type (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_ind_types Σ mdecl ∥) :=
    indtys <- monad_All (check_ind_type X_ext mdecl) mdecl.(ind_bodies) ;;
    ret _.
  Next Obligation.
    eapply All_sq, All_impl with (1 := indtys) => idecl Hi.
    now apply Hi.
  Qed.

  Program Definition check_one_ind_body X X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ}
      (mind : kername) (mdecl : mutual_inductive_body)
      (pf : check_wf_env_ext_prop X X_ext (ind_universes mdecl))
      (wfpars : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ mdecl.(ind_params) ∥)
      (wfars : forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ wf_ind_types Σ mdecl ∥)
      (mdeclvar : forall Σ, abstract_env_rel X Σ -> ∥ on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance) ∥)
      (i : nat) (idecl : one_inductive_body)
      (hnth : nth_error mdecl.(ind_bodies) i = Some idecl)
      : EnvCheck X_env_ext_type (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_ind_body cumulSpec0 (lift_typing typing) Σ mind mdecl i idecl ∥) :=
      let id := string_of_kername mind in
      '(cs; oncstrs) <- (check_constructors X X_ext mind mdecl pf wfars wfpars mdeclvar i idecl hnth) ;;
      onprojs <- wrap_error _ X_ext ("Checking projections of " ^ id)
       (check_projections X_ext mind mdecl i idecl idecl.(ind_indices) cs oncstrs) ;;
      onsorts <- wrap_error _ X_ext ("Checking universes of " ^ id)
        (do_check_ind_sorts X_ext mdecl.(ind_params) wfpars idecl.(ind_kelim)
           idecl.(ind_indices) cs _ idecl.(ind_sort) _) ;;
      onindices <- check_indices X mdecl mind _ mdeclvar idecl.(ind_indices) _ ;;
      ret _.

  Next Obligation.
    intros ? ?. pose proof (abstract_env_ext_wf _ H).
    destruct pf as [pf ?]. specialize_Σ H. destruct Σ as [Σ ext].
    pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]]. specialize_Σ wfΣ0.
    pose proof (abstract_env_ext_wf _ pf) as wf.
    sq. clear - H pf X0 wf.  induction X0; eauto. constructor; eauto. destruct r.
    eapply sorts_local_ctx_wf_sorts; eauto.
    erewrite (abstract_env_ext_irr _ _ pf); eauto.
    Unshelve. eauto.
  Qed.

  Next Obligation. cbn in *. specialize_Σ H. sq.
  pose proof (abstract_env_ext_wf _ H).  destruct Σ as [Σ ext].
  pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
  destruct pf as [pf ?]; eauto. specialize_Σ H. specialize_Σ wfΣ0.
  pose proof (abstract_env_ext_wf _ pf). sq.
  eapply nth_error_all in wfars; eauto; simpl in wfars.
  destruct wfars as ((_ & s & Hs & _) & e & _).
  clear X0; rewrite e -it_mkProd_or_LetIn_app in Hs.
  eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs; eauto.
  eapply inversion_Sort in Hs as [_ [? _]]; eauto.
  Qed.

  Next Obligation.
     destruct pf as [pf ?]; specialize_Σ H.
     now pose proof (abstract_env_ext_wf _ pf).
  Qed.
  Next Obligation.
    destruct pf as [pf pf']. specialize_Σ H. specialize_Σ pf.
    pose proof (abstract_env_ext_wf _ pf) as wf.
    sq.
    clear onprojs onsorts X0.
    red in wfars. eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as ((_ & s & Hs & _) & e & _).
    rewrite e -it_mkProd_or_LetIn_app in Hs.
    eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs; eauto.
    eapply typing_wf_local in Hs. now rewrite app_context_nil_l in Hs.
  Qed.

  Next Obligation.
    rename x into cs. destruct Σ as [Σ ext].
    pose proof (abstract_env_ext_wf _ H).
    pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
    destruct pf as [pf pf']; eauto. specialize_Σ H. specialize_Σ wfΣ0. sq.
    eapply All_nth_error in wfars as (isty & e & eqrel); tea.
    refine
    {| ind_arity_eq := e; onArity := _;
       ind_cunivs := cs;
       onConstructors := oncstrs;
       onProjections := onprojs;
       ind_sorts := onsorts;
       ind_relevance_compat := eqrel;
       onIndices := _; |}.
    - rewrite e in isty |- *; apply PCUICInductiveInversion.ind_arity_relevant => //. apply H0.
    - erewrite (abstract_env_ext_irr _ _ pf); eauto.
      destruct (ind_variance mdecl) => //.
    Unshelve. eauto.
  Qed.

  Program Definition check_wf_decl X X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ}
    kn (d : global_decl)
    (pf : check_wf_env_ext_prop X X_ext (universes_decl_of_decl d))
    : EnvCheck X_env_ext_type (forall Σ, abstract_env_ext_rel X_ext Σ -> ∥ on_global_decl cumulSpec0 (lift_typing typing) Σ kn d ∥) :=
    match d with
    | ConstantDecl cst =>
      wrap_error _ X_ext (string_of_kername kn)
        (check_judgment_wf_env X_ext [] (fun _ _ => sq_wfl_nil _) (TermoptTypRel (cst_body cst) (cst_type cst) (cst_relevance cst)) eq_refl)
        ;; ret _
    | InductiveDecl mdecl =>
      let id := string_of_kername kn in
      check_var <- @check_variance X kn (ind_universes mdecl) (ind_variance mdecl) _ ;;
      check_pars <- wrap_error _ X_ext id (check_context_wf_env X_ext (ind_params mdecl)) ;;
      check_npars <- wrap_error _ X_ext id
        (check_eq_nat (context_assumptions (ind_params mdecl))
            (ind_npars mdecl) (Msg "wrong number of parameters")) ;;
      onarities <- check_ind_types X_ext mdecl ;;
      check_bodies <- monad_Alli_nth_forall mdecl.(ind_bodies) (fun i oib Hoib => check_one_ind_body X X_ext kn mdecl _ check_pars onarities check_var i oib Hoib);;
      ret (Build_on_inductive_sq  check_bodies check_pars check_npars _)
    end.
  Next Obligation.
    destruct pf.
    specialize_Σ H.
    pose proof (abstract_env_ext_wf _ (H0 _ H1)) as wfΣ.
    sq. assumption.
  Qed.
  Next Obligation.
      edestruct pf as [? ?]; specialize_Σ H. now pose proof (abstract_env_ext_wf _ H0).
  Qed.
  Obligation Tactic := idtac.
  Next Obligation. intros. cbn in *.
    rewrite <- Heq_d in pf. exact pf.
  Qed.
  Next Obligation.
    intros. destruct pf as [pf pf']. specialize_Σ H.
    pose proof (abstract_env_exists X) as [[Σ0 wfΣ0]].
    specialize_Σ wfΣ0.
    sq. now erewrite (abstract_env_ext_irr _ _ pf).
    Unshelve. eauto.
  Qed.

  Import EnvMap.

  Definition global_uctx_univs (univs : ContextSet.t) :=
    (global_levels univs, ContextSet.constraints univs).

  Obligation Tactic := idtac.

  Lemma levels_global_levels_declared univs :
    LevelSet.mem Level.lzero (ContextSet.levels univs) ->
    LevelSet.Equal (PCUICLookup.global_levels (LevelSet.remove Level.lzero univs.1, univs.2)) (ContextSet.levels univs).
  Proof using Type.
    clear. move / LevelSet.mem_spec. intros Hin l. unfold global_levels. rewrite LS.union_spec LevelSet.singleton_spec.
    cbn. rewrite LevelSet.remove_spec. firstorder. now subst.
    destruct l => //. now right. left. intuition. congruence.
     left. intuition. congruence.
  Qed.

  Lemma add_singleton l : LevelSet.add l (LevelSet.singleton l) =_lset LevelSet.singleton l.
  Proof.
    lsets.
  Qed.

  Program Definition check_univs (univs : ContextSet.t) (retro : Retroknowledge.t)
    : EnvCheck X_env_ext_type ({ X : X_env_type |
      (forall Σ, abstract_env_rel X Σ -> Σ = {| universes := univs; declarations := []; retroknowledge := retro |})
                      /\ ∥ on_global_univs univs ∥ }) :=
    let id := "toplevel" in
    let levels := ContextSet.levels univs in
    check_eq_true_lazy (~~ (LevelSet.mem Level.lzero levels))
       (fun _ => (abstract_env_ext_empty, IllFormedDecl id (Msg ("Level zero is not declared in the global levels " ^ print_lset levels))));;
    check_eq_true_lazy (LevelSet.for_all (fun l => negb (Level.is_var l)) levels)
       (fun _ => (abstract_env_ext_empty, IllFormedDecl id (Msg ("Variable level in the global levels " ^ print_lset levels))));;
    check_eq_true_lazy (UnivConstraintSet.for_all (fun c => declared_universe (LevelSet.add Level.lzero levels) c.1.1 && declared_universe (LevelSet.add Level.lzero levels) c.2) (ContextSet.constraints univs))
       (fun _ => (abstract_env_ext_empty, IllFormedDecl id (Msg ("Non declared level in " ^ print_lset levels ^
                                    " |= " ^ print_univ_constraint_set (ContextSet.constraints univs)))));;
    check_eq_true_lazy (@abstract_env_is_consistent_empty _ X_impl univs)
        (fun _ => (abstract_env_ext_empty, IllFormedDecl id (Msg ("Constraints are not satisfiable:" ^
          print_univ_constraint_set (ContextSet.constraints univs))))) ;;
    ret (let Hunivs := _ in exist (abstract_env_init (univs.1, univs.2) retro Hunivs) _).
  Next Obligation.
    intros. have decll :
          UnivConstraintSet.For_all (declared_univ_cstr_levels (LevelSet.add Level.lzero (ContextSet.levels univs))) (ContextSet.constraints univs).
    { clear -i1. apply UnivConstraintSet.for_all_spec in i1.
      2: now intros x y [].
      move=> [[l ct] l'] /i1 /andb_true_iff //=> [] h h'.
      apply LevelSet.subset_spec in h. apply LevelSet.subset_spec in h'.
      now split. }
      intros. split; eauto.
      { intros l Hl. specialize (decll l Hl). red. destruct l, p. unfold PCUICLookup.global_levels. cbn.
        (* rewrite -LevelSetProp.union_sym -LevelSetProp.add_union_singleton levelset_add_remove. *)
        cbn in Hl. destruct decll. split; lsets. }
      split; eauto.  unfold declared_univ_cstr_levels. cbn.
      repeat split => //.
    + clear - i i0. apply LevelSet.for_all_spec in i0.
      2: now intros x y [].
      subst levels.
      rewrite /i0 => l. cbn. destruct l => //=.
      rewrite /PCUICLookup.global_levels //=.
      rewrite LevelSet.union_spec LevelSet.singleton_spec => //.
      move: (i0 (Level.lvar n)) => hl.
      intros [|]. cbn in hl. specialize (hl H). congruence.
      congruence.
    + unfold abstract_env_is_consistent_empty in i2.
      pose proof (abs_init := abstract_env_init_correct (abstract_env_impl := X_env_type)
      (LevelSet.singleton Level.lzero, UCS.empty) Retroknowledge.empty PCUICWfEnv.abstract_env_empty_obligation_1).
      epose proof (abs_consist := abstract_env_is_consistent_correct _ _ univs abs_init); cbn in *.
      rewrite /declared_univ_cstr_levels //= in abs_consist.
      forward abs_consist.
      { split.
        { move=> l hin hin'. apply LevelSet.singleton_spec in hin'. subst l.
          move/LevelSet.mem_spec: hin => e. now rewrite e in i. }
        unfold global_levels. cbn.
        rewrite LevelSetProp.union_sym -LevelSetProp.add_union_singleton add_singleton -LevelSetProp.add_union_singleton //. }
      rewrite /global_uctx //= /global_levels /global_constraints //= in abs_consist.
      pose (abstract_env_wf _ abs_init). sq.
      apply abs_consist in i2; eauto ; clear abs_consist; cbn; sq.
  Qed.
  Next Obligation.
     cbv beta. intros [] retro name levels H nv hd habs Hunivs. clearbody Hunivs.
      split.
    - intros. eapply (abstract_env_irr _ _ (abstract_env_init_correct _ _ _)); eauto.
    - now sq.
    Unshelve. eauto.
  Qed.

  Obligation Tactic := Tactics.program_simpl.

  Program Fixpoint check_wf_decls (univs : ContextSet.t) (retro : Retroknowledge.t)
    (decls : global_declarations) :
    (* this is exactly what we need, I don't understand this function enough to know what the appropriate generalization is - JasonGross *)
    forall {normalization_in
        : forall (d : kername × global_decl)
               (decls' : global_declarations)
               (Hdecls' : exists n, List.skipn n decls = decls')
               (x : {X : X_env_type | forall Σ : global_env, Σ ∼ X -> Σ = {| universes := univs; declarations := decls'; retroknowledge := retro |}})
               (X : X_env_type)
               (wf_ : forall Σ : global_env, Σ ∼ X -> Σ = {| universes := univs; declarations := decls'; retroknowledge := retro |})
               (isfresh : ∥ PCUICAst.fresh_global d.1 decls' ∥)
               (udecl := universes_decl_of_decl d.2 : universes_decl)
               (X' : {X_ext : X_env_ext_type | check_wf_env_ext_prop X X_ext udecl}),
        forall Σ : global_env_ext, wf_ext Σ -> Σ ∼_ext ` X' -> NormalizationIn Σ},
      EnvCheck X_env_ext_type ({ X : X_env_type |
    (forall Σ, abstract_env_rel X Σ -> Σ = {| universes := univs; declarations := decls; retroknowledge := retro |})})
    :=
    match decls with
    [] => fun _ =>
      X <- check_univs univs retro ;;
      ret (exist (proj1_sig X) _)
    | d :: decls => fun normalization_in =>
      '(exist X wf_) <- @check_wf_decls univs retro decls _ ;;
      isfresh <- check_fresh d.1 decls ;;
      let udecl := universes_decl_of_decl d.2 in
      X' <- make_abstract_env_ext X d.1 udecl ;;
      @check_wf_decl X (proj1_sig X') _ d.1 d.2 (proj2_sig X') ;;
      ret (exist (abstract_env_add_decl X d.1 d.2 _) _)
    end.

  Obligation Tactic := intros.
  Next Obligation.
    let H := match goal with H : @ex nat _ |- _ => H end in
    destruct H as [n H];
    eapply normalization_in; try solve [ exists (S n); exact H ];
    eassumption.
  Qed.
  Obligation Tactic := Tactics.program_simpl.

  Next Obligation.
    unshelve eapply normalization_in; try ((idtac + unshelve econstructor); eassumption).
    exists 1; reflexivity.
  Qed.

  Next Obligation.
    cbn in *. destruct H0.
    specialize_Σ a. specialize_Σ H. rewrite wf_.  cbn in *.
    specialize_Σ H0. sq.
    split; eauto.
    - pose proof (abstract_env_ext_wf _ H0). sq. destruct H3.
      cbn in *. now rewrite wf_ in o0.
    - sq; now rewrite wf_ in y.
  Qed.

  Next Obligation.
    pose proof (abstract_env_exists X) as [[? ?]].
    epose (abstract_env_add_decl_correct X _ k g _ a).
    erewrite (abstract_env_irr _ H a0).
    pose proof (wf_ _ a) as eq.
    unfold add_global_decl. now rewrite eq.
  Qed.

  Program Definition check_wf_env (Σ : global_env)
    (* this is the hypothesis we need, idk how to simplify it or appropriately generalize it *)
    {normalization_in
      : forall (g : global_decl) (Hdecls' : nat) X,
        (forall Σ0 : global_env,
            Σ0 ∼ X ->
            Σ0 =
              {|
                universes := Σ;
                declarations := skipn Hdecls' (declarations Σ);
                retroknowledge := retroknowledge Σ
              |}) ->
        forall X' : X_env_ext_type,
          check_wf_env_ext_prop X X' (universes_decl_of_decl g) ->
          forall Σ0 : global_env_ext, wf_ext Σ0 -> Σ0 ∼_ext X' -> NormalizationIn Σ0}
    :
    EnvCheck X_env_ext_type ({ X : X_env_type | abstract_env_rel X Σ}) :=
    X <- @check_wf_decls Σ.(universes) Σ.(retroknowledge) Σ.(declarations) _ ;;
    ret (exist (proj1_sig X) _).

  Next Obligation.
    pose proof (abstract_env_exists X) as [[Σ' wfΣ]].
    specialize_Σ wfΣ. subst. now destruct Σ.
  Qed.

  Program Definition check_wf_ext (Σ : global_env_ext)
    (* this is the hypothesis we need, idk how to simplify it or appropriately generalize it, maybe use check_wf_env_ext_prop to simplify Σ0 ∼_ext X' into _ ∼ X so that we get an equality? *)
    {normalization_in
      : forall (g : global_decl) (Hdecls' : nat) X,
        (forall Σ0 : global_env,
            Σ0 ∼ X ->
            Σ0 =
              {|
                universes := Σ;
                declarations := skipn Hdecls' (declarations Σ);
                retroknowledge := retroknowledge Σ
              |}) ->
        forall X' : X_env_ext_type,
          check_wf_env_ext_prop X X' (universes_decl_of_decl g) ->
          forall Σ0 : global_env_ext, wf_ext Σ0 -> Σ0 ∼_ext X' -> NormalizationIn Σ0}
    :
    EnvCheck X_env_ext_type ({ X : X_env_ext_type | abstract_env_ext_rel X Σ}) :=
    X <- @check_wf_env Σ.1 _ ;;
    X' <- make_abstract_env_ext (proj1_sig X) (MPfile [], "toplevel term") Σ.2 ;;
    ret (exist (proj1_sig X') _).

  Next Obligation.
    specialize_Σ a. now destruct H as [? ?], Σ.
  Qed.

  Definition check_type_wf_env_bool X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ
    (wfΓ : forall Σ,  abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) t T : bool :=
    match check_type_wf_env X_ext Γ wfΓ t T with
    | Checked _ => true
    | TypeError e => false
    end.

  Definition check_wf_env_bool_spec X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ
    (wfΓ : forall Σ,  abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool X_ext Γ wfΓ t T = true ->
    forall Σ,  abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; Γ |- t : T ∥.
  Proof using Type.
    unfold check_type_wf_env_bool.
    destruct check_type_wf_env ; auto.
    discriminate.
  Qed.

  Definition check_wf_env_bool_spec2 X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ
    (wfΓ : forall Σ,  abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool X_ext Γ wfΓ t T = false -> type_error.
  Proof.
    unfold check_type_wf_env_bool.
    destruct check_type_wf_env; auto.
    discriminate.
  Defined.

  (* This function is appropriate for live evaluation inside Rocq:
     it forgets about the derivation produced by typing and replaces it with an opaque constant. *)

  Program Definition check_type_wf_env_fast X_ext {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ} Γ
  (wfΓ : forall Σ,  abstract_env_ext_rel X_ext Σ -> ∥ wf_local Σ Γ ∥) t {T} :
  typing_result (forall Σ,  abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; Γ |- t : T ∥) :=
    (if check_type_wf_env_bool X_ext Γ wfΓ t T as x return (check_type_wf_env_bool X_ext Γ wfΓ t T = x -> typing_result _) then
      fun eq => ret _
    else fun eq => raise (check_wf_env_bool_spec2 X_ext Γ wfΓ t T eq)) eq_refl.

  Next Obligation.
    now apply (check_wf_env_bool_spec X_ext Γ wfΓ t0 T eq).
  Qed.

  Obligation Tactic := Program.Tactics.program_simpl.

  Definition EnvCheck_X_env_ext_type {cf:checker_flags} := EnvCheck X_env_ext_type.

  Instance Monad_EnvCheck_X_env_ext_type {cf:checker_flags} : Monad EnvCheck_X_env_ext_type := _.

  Program Definition typecheck_program (p : program) φ
    (* this is the hypothesis we need, idk how to simplify it or appropriately generalize it, maybe use check_wf_env_ext_prop to simplify Σ0 ∼_ext X' into _ ∼ X so that we get an equality? *)
    {normalization_in
      : forall (g : global_decl) (Hdecls' : nat) X,
        (forall Σ0 : global_env,
            Σ0 ∼ X ->
            Σ0 =
              {|
                universes := p.1;
                declarations := skipn Hdecls' (declarations p.1);
                retroknowledge := retroknowledge p.1
              |}) ->
        forall X' : X_env_ext_type,
          check_wf_env_ext_prop X X' (universes_decl_of_decl g) ->
          forall Σ0 : global_env_ext, wf_ext Σ0 -> Σ0 ∼_ext X' -> NormalizationIn Σ0}
    {normalization_in'
      : forall x : X_env_ext_type,
        (p.1, φ) ∼_ext x -> forall Σ : global_env_ext, wf_ext Σ -> Σ ∼_ext x -> NormalizationIn Σ}
    : EnvCheck_X_env_ext_type (∑ A, { X: X_env_ext_type | ∥ abstract_env_ext_rel X (p.1, φ) ×
                                                          wf_ext (p.1, φ) × (p.1, φ) ;;; [] |- p.2 ▹ A ∥}) :=
    '(exist xx pf) <- @check_wf_ext (p.1, φ) _ ;;
    inft <- @infer_term xx _ p.2 ;;
    ret (inft.π1; (exist xx _)).
 Next Obligation.
    cbn in *. specialize_Σ pf. pose proof (abstract_env_ext_wf _ pf).
    sq. split; auto.
  Qed.

  End CheckEnv.

(* Print Assumptions typecheck_program. *)
