(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ProofIrrelevance ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICConversion PCUICEquality PCUICConversion
     PCUICSafeLemmata PCUICNormal PCUICInversion PCUICReduction PCUICPosition
     PCUICPrincipality PCUICContextConversion PCUICContextConversionTyp PCUICSN PCUICUtils PCUICWfUniverses
     PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICClosed PCUICClosedTyp PCUICConvCumInversion .
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICSafeReduce PCUICEqualityDec.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

#[global]
Instance red_brs_refl Σ p Γ: CRelationClasses.Reflexive (@red_brs Σ p Γ).
Proof.
  intros brs.
  eapply All2_same; unfold on_Trel; split; reflexivity.
Qed.

#[global]
Instance conv_cum_trans {cf leq} {Σ : global_env_ext} {Γ} : wf Σ -> RelationClasses.Transitive (@conv_cum cf leq Σ Γ).
Proof.
  intros x y z; unfold conv_cum. intros; sq.
  now etransitivity.
Qed.

Lemma closed_red_mkApps_tConst_axiom {cf} {Σ} {wfΣ : wf Σ} {Γ} {cst u} {args : list term} {cb c} :
  declared_constant Σ cst cb -> cst_body cb = None ->
  Σ ;;; Γ ⊢ mkApps (tConst cst u) args ⇝ c ->
  ∑ args' : list term,
  (c = mkApps (tConst cst u) args') * (red_terms Σ Γ args args').
Proof.
  intros decl hcb [clΓ clt r].
  eapply (PCUICConfluence.red_mkApps_tConst_axiom (Γ := exist Γ clΓ)) in decl as [args' [eq r']]; tea.
  * exists args'; split; auto.
    eapply into_red_terms; auto.
    inv_on_free_vars. solve_all.
  * cbn. inv_on_free_vars; solve_all.
Qed.

(** * Conversion for PCUIC without fuel

  Following PCUICSafeReduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)

Section Conversion.

  Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Set Equations Transparent.
  Set Equations With UIP.

  Inductive state :=
  | Reduction
  | Term
  | Args
  | Fallback.

  Inductive stateR : state -> state -> Prop :=
  | stateR_Term_Reduction : stateR Term Reduction
  | stateR_Args_Term : stateR Args Term
  | stateR_Fallback_Term : stateR Fallback Term
  | stateR_Args_Fallback : stateR Args Fallback.

  Derive Signature for stateR.

  Lemma stateR_Acc :
    forall s, Acc stateR s.
  Proof using Type.
    assert (Acc stateR Args) as hArgs.
    { constructor. intros s h.
      dependent induction h.
      all: discriminate.
    }
    assert (Acc stateR Fallback) as hFall.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hArgs.
    }
    assert (Acc stateR Term) as hTerm.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      - apply hArgs.
      - apply hFall.
    }
    assert (Acc stateR Reduction) as hRed.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hTerm.
    }
    intro s. destruct s ; eauto.
  Qed.

  Notation wtp Γ t π :=
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zipc t π)) (only parsing).

  Set Primitive Projections.

  Record pack (Γ : context) := mkpack {
    st   : state ;
    tm1  : term ;
    stk1 : stack ;
    tm2  : term ;
    stk2 : stack ;
    wth  : wtp Γ tm2 stk2
  }.

  Arguments st {_} _.
  Arguments tm1 {_} _.
  Arguments stk1 {_} _.
  Arguments tm2 {_} _.
  Arguments stk2 {_} _.
  Arguments wth {_} _.

  Definition wterm Γ := { t : term | forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t }.

  Definition wcored Γ (u v : wterm Γ) :=
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored' Σ Γ (` u) (` v).

  Lemma wcored_wf :
    forall Γ, well_founded (wcored Γ).
  Proof using normalization_in.
    intros Γ [u hu].
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (heΣ _ wfΣ) as [heΣ].
    pose proof (hu _ wfΣ) as h.
    apply normalization_upto in h. 2: now apply normalization_in.
    dependent induction h.
    constructor. intros [y hy] r.
    unfold wcored in r. cbn in r.
    eapply H0. eapply r; eauto.
  Qed.

  Definition eqt u v := ∥ u = v :> term ∥.

  Lemma eqt_eqterm {Σ} {wfΣ : abstract_env_ext_rel X Σ} {u v} :
    u = v -> eq_term Σ Σ u v.
  Proof using Type.
    intros <-.
    reflexivity.
  Qed.

  Local Instance eqt_refl : RelationClasses.Reflexive eqt.
  Proof using Type. red. intros x; constructor. reflexivity. Qed.

  Lemma eq_term_valid_pos :
    forall {u v p},
      validpos u p ->
      eqt u v ->
      validpos v p.
  Proof using X.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    intros u v p vp e.
    destruct e as [e'].
    eapply eq_term_valid_pos. all: eauto. now eapply eqt_eqterm.
    Unshelve. all:eauto.
  Qed.

  Definition weqt {Γ} (u v : wterm Γ) :=
    eqt (` u) (` v).

  Equations R_aux (Γ : context) :
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) ->
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) -> Prop :=
    R_aux Γ :=
      t ⊨ eqt \ fun t t' => forall Σ, abstract_env_ext_rel X Σ -> cored' Σ Γ t t' by _ ⨷
      @posR t ⊗
      w ⊨ weqt \ wcored Γ by _ ⨷
      @posR (` w) ⊗
      stateR.
  Next Obligation.
    split. 2: intuition eauto.
    exists (` p).
    destruct p as [p hp].
    eapply eq_term_valid_pos. all: eauto.
  Defined.
  Next Obligation.
    split. 2: assumption.
    exists (` p).
    destruct x as [u hu], x' as [v hv].
    destruct p as [p hp].
    simpl in *.
    eapply eq_term_valid_pos. all: eauto.
  Defined.

  Derive Signature for Subterm.lexprod.

  Lemma R_aux_Acc :
    forall Γ t p w q s,
      (forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) ->
      Acc (R_aux Γ) (t ; (p, (w ; (q, s)))).
  Proof using normalization_in.
    intros Γ t p w q s ht.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    rewrite R_aux_equation_1.
    unshelve eapply dlexmod_Acc.
    - intros x y [e]; eauto.  constructor. now symmetry.
    - intros x y z [e1] [e2]; eauto. constructor. now etransitivity; tea.
    - intro u. eapply Subterm.wf_lexprod.
      + intro. eapply posR_Acc.
      + intros [w' q'].
        unshelve eapply dlexmod_Acc.
        * intros x y [e]; eauto. constructor. now symmetry.
        * intros x y z [e1] [e2]; eauto. constructor.
          now etransitivity; tea.
        * intros [t' h']. eapply Subterm.wf_lexprod.
          -- intro. eapply posR_Acc.
          -- intro. eapply stateR_Acc.
        * eintros x x' y [e] [y' [x'' [r [[e1] [e2]]]]]; eauto.
          eexists _,_. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
          intuition eauto using sq.
          constructor. etransitivity; tea.
        * intros x.
          exists (@eqt_refl _).
          unfold weqt, eqt.
          intros [[q'' h] ?].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * cbn. intros x x' [[q'' h] ?] e.
          destruct e as [e'].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * intros x y z e1 e2 [[q'' h] ?].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * intros [t1 ht1] [t2 ht2] e [[q1 hq1] s1] [[q2 hq2] s2] h.
          destruct e as [e'].
          simpl in *.
          dependent destruction h.
          -- left. unfold posR in *. simpl in *. assumption.
          -- match goal with
             | |- context [ exist q1 ?hq1 ] =>
               assert (ee : hq1 = hq2) by eapply uip
             end.
            rewrite ee. right. clear ee. assumption.
        * eapply wcored_wf.
    - eintros x x' y [e] [y' [x'' [r [[e1] [e2]]]]]; eauto.
      intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      eexists _,_. intuition eauto using sq.
      constructor. etransitivity; eauto.
    - intros x. exists (@eqt_refl _). intros [[q' h] [? [? ?]]].
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x x' [[q' h] [? [? ?]]] e.
      destruct e as [e']; eauto.
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x y z e1 e2 [[q' h] [? [? ?]]].
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x x' e
             [[p1 hp1] [[u hu] [[q1 hq1] s1]]]
             [[p2 hp2] [[v hv] [[q2 hq2] s2]]] hl.
      destruct e as [e']; eauto.
      simpl in *.
      dependent destruction hl.
      + left. unfold posR in *.
        simpl in *.
        assumption.
      + match goal with
        | |- context [ exist p1 ?hp1 ] =>
          assert (ee : hp1 = hp2) by eapply uip
        end.
        rewrite ee. right. clear ee.
        dependent destruction H.
        * left. assumption.
        * unshelve econstructor 2. 1: assumption.
          dependent destruction H.
          -- left. unfold posR in *.
             simpl in *. assumption.
          -- right. assumption.
    - pose proof (heΣ _ wfΣ) as [?].
      eapply Acc_equiv; try eapply normalization_upto; eauto.
      split; eauto; intros.
      erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto.
  Qed.

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos (tm1 u) (stk1 u)) (only parsing).
  Notation pwt u := (exist (P := fun t => forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ _ t)
                                 _ (fun Σ wfΣ => wth u Σ wfΣ)) (only parsing).
  Notation pps2 u := (stack_pos (tm2 u) (stk2 u)) (only parsing).

  Notation obpack u:=
    (pzt u ; (pps1 u, (pwt u; (pps2 u, st u)))) (only parsing).

  Definition R Γ (u v : pack Γ) :=
    R_aux Γ (obpack u) (obpack v).

  Lemma R_Acc :
    forall Γ u,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zipc (tm1 u) (stk1 u))) ->
      Acc (R Γ) u.
  Proof using normalization_in.
    intros Γ u h.
    eapply Acc_fun with (f := fun x => obpack x).
    apply R_aux_Acc. assumption.
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma R_aux_irrelevance Γ x y z :
    ((x.π1; x.π2.1), (existT (fun x => pos x × state) (` x.π2.2.π1) x.π2.2.π2)) =
    ((y.π1; y.π2.1), (existT (fun x => pos x × state) (` y.π2.2.π1) y.π2.2.π2)) ->
    R_aux Γ z x -> R_aux Γ z y.
  Proof using Type.
    destruct x as [t [pt [w [pw s]]]], y as [t' [pt' [w' [pw' s']]]].
    destruct z as [tz [ptz [wz [pwz sz]]]].
    cbn. intros [=]. subst. noconf H1. destruct w as [w wt], w' as [w' wt'].
    cbn in *. subst w'. noconf H3.
    unfold R_aux.
    intros hr. depelim hr.
    - now constructor.
    - cbn in H.
      eapply right_dlexmod with e. cbn.
      depelim H.
      * constructor. exact H.
      * constructor 2.
        depelim H.
        + now constructor.
        + eapply right_dlexmod with e0. cbn in H.
          depelim H.
          { constructor 1. cbn. exact H. }
          { constructor 2. exact H. }
  Qed.

  Lemma R_irrelevance Γ x y z :
    (x.(st), x.(tm1), x.(stk1), x.(tm2), x.(stk2)) =
    (y.(st), y.(tm1), y.(stk1), y.(tm2), y.(stk2)) ->
    R Γ z x -> R Γ z y.
  Proof using Type.
    destruct x, y; cbn.
    intros [=]; subst.
    unfold R. eapply R_aux_irrelevance; cbn.
    reflexivity.
  Qed.

  Lemma R_cored :
    forall Γ p1 p2,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored Σ Γ (pzt p1) (pzt p2)) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ p1 p2 h.
    left. intros. eapply cored_cored'. eapply h; eauto.
  Qed.

  Lemma R_aux_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      eqt t1 t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof using Type.
    intros Γ t1 t2 p1 p2 [? [? ?]] s2 e h.
    unshelve eright.
    - eauto.
    - left. unfold posR. simpl. assumption.
  Qed.

  Lemma R_positionR :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      positionR (` (pps1 p1)) (` (pps1 p2)) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e h. simpl in *.
    eapply R_aux_positionR ; simpl.
    - assumption.
    - assumption.
  Qed.

  Lemma R_aux_cored2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored' Σ Γ (` w1) (` w2)) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof using Type.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 h.
    cbn in e2. cbn in h. subst.
    unshelve eright.
    - auto.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      left. assumption.
  Qed.

  Lemma R_cored2 :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
          cored Σ Γ (` (pwt p1)) (` (pwt p2))) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e1 e2 h. simpl in *.
    eapply R_aux_cored2. all: simpl. all: auto.
    destruct s1, s2.
    all: intros; eapply cored_cored'.
    all: eauto.
  Qed.

  Lemma R_aux_positionR2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (eqt (` w1) (` w2)) ->
      positionR (` q1) (` q2) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof using Type.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 e3 h.
    cbn in e2. cbn in e3. subst.
    unshelve eright.
    - auto.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      unshelve eright.
      + auto.
      + left. unfold posR. simpl. assumption.
  Qed.

  Lemma R_positionR2 :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (eqt (` (pwt p1)) (` (pwt p2))) ->
      positionR (` (pps2 p1)) (` (pps2 p2)) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e1 e2 e3 h.
    simpl in *.
    eapply R_aux_positionR2. all: simpl. all: auto.
  Qed.

  Lemma R_aux_stateR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2 ,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (eqt (` w1) (` w2)) ->
      ` q1 = ` q2 ->
      stateR s1 s2 ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof using Type.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] [q1 hq1] [q2 hq2] s1 s2
           e1 e2 e3 e4 h.
    cbn in e2. cbn in e3. cbn in e4. subst.
    unshelve eright.
    - auto.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      unshelve eright.
      + auto.
      + unfold R_aux_obligations_obligation_2. simpl.
        match goal with
        | |- context [ exist q2 ?hq1 ] =>
          assert (e' : hq1 = hq2) by eapply uip
        end.
        rewrite e'.
        right. assumption.
  Qed.

  Lemma R_stateR :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (eqt (` (pwt p1)) (` (pwt p2))) ->
      ` (pps2 p1) = ` (pps2 p2) ->
      stateR (st p1) (st p2) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e1 e2 e3 e4 h.
    simpl in *.
    eapply R_aux_stateR. all: simpl. all: auto.
  Qed.

  Definition abstract_env_compare_global_instance := compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X).

  Notation eqb_ctx := (eqb_ctx_upto (abstract_env_compare_universe X) (abstract_env_compare_sort X) abstract_env_compare_global_instance Conv).
  Notation cmpb_term_napp := (eqb_term_upto_univ_napp (abstract_env_compare_universe X) (abstract_env_compare_sort X) abstract_env_compare_global_instance).
  Notation cmpb_term pb := (eqb_term_upto_univ (abstract_env_compare_universe X) (abstract_env_compare_sort X) abstract_env_compare_global_instance pb).
  Notation eqb_term := (cmpb_term Conv).
  Notation leqb_term := (cmpb_term Cumul).

  Definition eqb_term_stack t1 π1 t2 π2 :=
    eqb_ctx (stack_context π1) (stack_context π2) &&
    eqb_term (zipp t1 π1) (zipp t2 π2).

  Lemma iff_reflect (P : Prop) (b : bool) :
    P <-> b -> reflect P b.
  Proof using Type.
    intro H. apply ssrbool.introP.
    - intuition.
    - destruct b; intuition.
  Qed.

  Definition wf_universe_iff  Σ u :
    wf_universeb Σ u <-> wf_universe Σ u.
  Proof using Type.
    symmetry; apply reflect_iff. eapply wf_universe_reflect.
  Qed.

  Definition wf_sort_iff Σ s :
    wf_sortb Σ s <-> wf_sort Σ s.
  Proof using Type.
    symmetry; apply reflect_iff. eapply wf_sort_reflect.
  Qed.

  Definition wf_instance_iff Σ u :
    wf_instanceb Σ u <-> wf_instance Σ u.
  Proof using Type.
    symmetry; apply reflect_iff. eapply wf_instanceP.
  Qed.

  Notation conv_stack_ctx Γ π1 π2 :=
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ (Σ ⊢ Γ ,,, stack_context π1 = Γ ,,, stack_context π2) ∥).

  Notation conv_term leq Γ t π t' π' :=
    (forall Σ, abstract_env_ext_rel X Σ -> conv_cum leq Σ (Γ ,,, stack_context π) (zipp t π) (zipp t' π'))
      (only parsing).

  Notation alt_conv_term Γ t π t' π' :=
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ,,, stack_context π ⊢ zipp t π = zipp t' π' ∥)
      (only parsing).

  Inductive ConversionResult (P : Prop) :=
  | Success (h : P)
  | Error (e : ConversionError) (h : ~P).

  Arguments Success {_} _.
  Arguments Error {_} _.

  Definition isred_full Γ t π :=
    isApp t = false /\
    forall Σ, abstract_env_ext_rel X Σ -> ∥whnf RedFlags.nodelta Σ (Γ,,, stack_context π) (zipp t π)∥.

  Lemma isred_full_nobeta Γ t π :
    isred_full Γ t π ->
    isLambda t ->
    isStackApp π = false.
  Proof using Type.
    intros (?&isr) islam.
    destruct t; cbn in *; try easy.
    unfold zipp in isr.
    destruct π as [|[]]; cbn in *; try easy.
    destruct (decompose_stack π) in isr.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (isr _ wfΣ) as [isr'].
    depelim isr'; rewrite -> mkApps_tApp in *; try solve [solve_discr].
    apply whne_mkApps_inv in w; [|easy].
    destruct w as [|(?&?&?&?&?&?&?&?)]; [|discriminate].
    depelim w; solve_discr; discriminate.
   Qed.

  Lemma eta_pair {A B} (p q : A * B) :
    p = q ->
    (p.1, p.2) = (q.1, q.2).
  Proof using Type. now destruct p, q. Qed.

  Ltac is_var t :=
    match goal with
    | v : _ |- _ =>
      match t with
      | v => idtac
      end
    end.

  Lemma zipp_stack_cat_decompose_stack t π π' :
    zipp t (π ++ (decompose_stack π').2) = zipp t π.
  Proof using Type.
    rewrite zipp_stack_cat; auto.
    destruct decompose_stack eqn:decomp.
    now apply decompose_stack_noStackApp in decomp.
  Qed.

  Lemma zipc_decompose_stack_empty t π :
    (decompose_stack π).2 = [] ->
    zipc t π = zipp t π.
  Proof using Type.
    destruct decompose_stack eqn:decomp.
    apply decompose_stack_eq in decomp as ->.
    cbn; intros ->.
    rewrite zipc_appstack zipp_as_mkApps decompose_stack_appstack.
    cbn.
    now rewrite app_nil_r.
  Qed.

  Ltac reduce_stack_facts Σ wfΣ :=
    repeat
      match goal with
      | [H: (?a, ?b) = reduce_stack ?f _ ?X ?Γ ?t ?π ?h |- _] =>
        let rid := fresh "r" in
        let decompid := fresh "d" in
        let whid := fresh "w" in
        let isr := fresh "isr" in
        pose proof (reduce_stack_sound f _ X Σ wfΣ Γ t π h) as [rid];
        pose proof (reduce_stack_decompose f _ X Γ t π h) as decompid;
        pose proof (reduce_stack_whnf f _ X Γ t π h Σ wfΣ) as whid;
        pose proof (reduce_stack_isred f _ X Γ t π h) as isr;
        rewrite <- H in rid, decompid, whid, isr; cbn in rid, decompid, whid, isr;
        clear H
      end.

  Lemma zipc_unfold_decompose_stack t π :
    zipc t π = zipc (mkApps t (decompose_stack π).1) (decompose_stack π).2.
  Proof using Type.
    rewrite <- zipc_appstack.
    destruct (decompose_stack π) eqn:decomp.
    now apply decompose_stack_eq in decomp as ->.
  Qed.

  Ltac simpl_stacks :=
    (repeat
       match goal with
       | [H: (?a, ?b) = decompose_stack ?π |- _] =>
         is_var a;
         is_var b;
         apply eta_pair in H; cbn in H; noconf H
       end);
    (repeat
       match goal with
       | [H: context[decompose_stack (appstack ?l ?ρ)] |- _] =>
         (rewrite (decompose_stack_appstack l ρ) in H; cbn in H) || fail 2
       | [H: context[stack_context (?π ++ ?π')] |- _] =>
         (rewrite (stack_context_stack_cat π' π) in H; cbn in H) || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[zipc ?t ?π] |- _] =>
         (rewrite (zipc_decompose_stack_empty t π H) in H'; cbn in H') || fail 2
       | [H: context[stack_context (decompose_stack ?π).2] |- _] =>
         (rewrite (stack_context_decompose π) in H; cbn in H) || fail 2
       | [H: context[zipp ?t (?π ++ (decompose_stack ?π').2)] |- _] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π') in H; cbn in H) || fail 2
       | [H: context[zipc ?t (appstack ?args ?π)] |- _] =>
         (rewrite (@zipc_appstack t args π) in H; cbn in H) || fail 2
       | [H: context[zipc ?t (?π ++ ?π')] |- _] =>
         (rewrite (zipc_stack_cat t π π') in H; cbn in H) || fail 2
       | [H: context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2] |- _] =>
         unfold zip in H
       | [H: context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2] |- _] =>
         (rewrite <- (zipc_unfold_decompose_stack t π) in H; cbn in H) || fail 2
       | [H: isStackApp ?π = false, H': context[zipp ?t ?π] |- _] =>
         (rewrite (zipp_noStackApp t π H) in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2, H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π') in H'; cbn in H')
         || fail 2

       | [|- context[decompose_stack (appstack ?l ?ρ)]] =>
         (rewrite (decompose_stack_appstack l ρ); cbn) || fail 2
       | [|- context[stack_context (?π ++ ?π')]] =>
         (rewrite (stack_context_stack_cat π' π); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H; cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[zipc ?t ?π]] =>
         (rewrite (zipc_decompose_stack_empty t π H); cbn) || fail 2
       | [|- context[stack_context (decompose_stack ?π).2]] =>
         (rewrite (stack_context_decompose π); cbn) || fail 2
       | [|- context[zipp ?t (?π ++ (decompose_stack ?π').2)]] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π'); cbn) || fail 2
       | [|- context[zipc ?t (appstack ?args ?π)]] =>
         (rewrite (@zipc_appstack t args π); cbn) || fail 2
       | [|- context[zipc ?t (?π ++ ?π')]] =>
         (rewrite (zipc_stack_cat t π π'); cbn) || fail 2
       | [|- context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2]] =>
         unfold zip
       | [|- context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2]] =>
         (rewrite <- (zipc_unfold_decompose_stack t π); cbn) || fail 2
       | [H: isStackApp ?π = false |- context[zipp ?t ?π]] =>
         (rewrite (zipp_noStackApp t π H); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2 |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π'); cbn) || fail 2
       end);
    repeat
      match goal with
      | [H: context[zipp ?t ?π] |- _] => rewrite (zipp_as_mkApps t π) in H
      | [|- context[zipp ?t ?π]] => rewrite (zipp_as_mkApps t π)
      end.

  Ltac simpl_reduce_stack Σ wfΣ := reduce_stack_facts Σ wfΣ ; simpl_stacks.

  (* Tailored view for isconv_prog and precondition for fallback case *)
  Equations prog_discr (t1 t2 : term) : Prop :=
    prog_discr (tApp _ _) (tApp _ _) := False ;
    prog_discr (tConst _ _) (tConst _ _) := False ;
    prog_discr (tLambda _ _ _) (tLambda _ _ _) := False ;
    prog_discr (tProd _ _ _) (tProd _ _ _) := False ;
    prog_discr (tCase _ _ _ _) (tCase _ _ _ _) := False ;
    prog_discr (tProj _ _) (tProj _ _) := False ;
    prog_discr (tFix _ _) (tFix _ _) := False ;
    prog_discr (tCoFix _ _) (tCoFix _ _) := False ;
    prog_discr (tPrim _) (tPrim _) := False ;
    prog_discr _ _ := True.

  (* Note that the arity of this should be the same for all s as otherwise
     the extracted code is not correct *)
  Definition Ret s Γ t π t' π' :=
    forall (leq : conv_pb),
      conv_stack_ctx Γ π π' ->
      (match s with Fallback | Term => isred_full Γ t π | _ => True end) ->
      (match s with Fallback | Term => isred_full Γ t' π' | _ => True end) ->
      (match s with | Fallback => prog_discr t t' | _ => True end) ->
      match s with
      | Reduction
      | Term
      | Fallback => ConversionResult (conv_term leq Γ t π t' π')
      | Args => ConversionResult (forall Σ, abstract_env_ext_rel X Σ -> ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π)
                                   (decompose_stack π).1
                                   (decompose_stack π').1∥)
      end.

  Definition Aux s Γ t1 π1 t2 π2 h2 :=
     forall s' t1' π1' t2' π2'
       (h1' : wtp Γ t1' π1')
       (h2' : wtp Γ t2' π2'),
       conv_stack_ctx Γ π1 π2 ->
       R Γ
         (mkpack Γ s' t1' π1' t2' π2' h2')
         (mkpack Γ s t1 π1 t2 π2 h2) ->
       Ret s' Γ t1' π1' t2' π2'.

  Notation expand aux := (fun a b c d e f g h i => aux _ _ _ _ _ _ _ _ _) (only parsing).

  Local Notation yes := (Success _) (only parsing).
  Local Notation no := (fun e => Error e _) (only parsing).

  (* TODO NOTE
     repack could also take another argument of type
     ConversionError -> ConversionError
     to keep a full error trace (we currently only do it partially).
  *)
  Local Notation repack e :=
    (match e with Success h => Success _ | Error er h => Error er _ end)
    (only parsing).

  Notation isconv_red_raw leq t1 π1 t2 π2 aux :=
    (aux Reduction t1 π1 t2 π2 _ _ _ _ leq _ I I I) (only parsing).
  Notation isconv_prog_raw leq t1 π1 t2 π2 aux :=
    (aux Term t1 π1 t2 π2 _ _ _ _ leq _ _ _ I) (only parsing).
  Notation isconv_args_raw leq t1 π1 t2 π2 aux :=
    (aux Args t1 π1 t2 π2 _ _ _ _ leq _ I I I) (only parsing).
  Notation isconv_fallback_raw leq t1 π1 t2 π2 aux :=
    (aux Fallback t1 π1 t2 π2 _ _ _ _ leq _ _ _ _) (only parsing).

  Notation isconv_red leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args leq t1 π1 t2 π2 aux :=
    (repack (isconv_args_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_fallback leq t1 π1 t2 π2 aux :=
    (repack (isconv_fallback_raw leq t1 π1 t2 π2 aux)) (only parsing).

  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Reduction Γ t1 π1 t2 π2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=

    _isconv_red Γ leq t1 π1 h1 t2 π2 h2 hx aux
    with inspect (decompose_stack π1) := {
    | @exist (args1, ρ1) e1 with inspect (decompose_stack π2) := {
      | @exist (args2, ρ2) e2
        with inspect (reduce_stack RedFlags.nodelta _ X
                                   (Γ ,,, stack_context π1)
                                   t1 (appstack args1 []) _) := {
        | @exist (t1',π1') eq1
          with inspect (reduce_stack RedFlags.nodelta _ X
                                     (Γ ,,, stack_context π2)
                                     t2 (appstack args2 []) _) := {
          | @exist (t2',π2') eq2 => isconv_prog leq t1' (π1' ++ ρ1) t2' (π2' ++ ρ2) aux
          }
        }
      }
    }.
  Next Obligation.
    symmetry in e1.
    pose proof (heΣ _ wfΣ); sq.
    eapply welltyped_zipc_stack_context ; eauto.
  Qed.
  Next Obligation.
    clear aux eq1.
    symmetry in e2.
    pose proof (heΣ _ wfΣ); sq.
    now eapply welltyped_zipc_stack_context ; eauto.
  Qed.
  Next Obligation.
    simpl_reduce_stack Σ wfΣ.
    pose proof (hΣ _ wfΣ); sq.
    eapply red_welltyped ; try assumption ; revgoals.
    - zip fold. eapply red_context_zip. simpl_stacks. eapply r0.
    - cbn. simpl_stacks. eauto.
  Qed.
  Next Obligation.
    simpl_reduce_stack Σ wfΣ.
    pose proof (hΣ _ wfΣ); sq.
    eapply red_welltyped ; try assumption ; revgoals.
    - zip fold. eapply red_context_zip. simpl_stacks. eapply r.
    - cbn. simpl_stacks. eauto.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ X Γ t π h) as c1
    end.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match type of eq1 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?hh =>
      pose proof (reduce_stack_Req f _ X _ wfΣ _ _ _ hh) as [ e | h ]
    end.
     - assert (ee1 := eq1). rewrite e in ee1. inversion ee1. subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?X ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2 ;
        pose proof (reduce_stack_context f Σ X Γ t π h) as c2
      end.
      rewrite <- eq2 in d2. cbn in d2.
      rewrite <- eq2 in c2. cbn in c2.
      rewrite stack_context_appstack in c2. cbn in c2.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
      match type of eq2 with
      | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?hh =>
        pose proof (reduce_stack_Req f _ X Σ wfΣ _ _ _ hh) as [ ee | h ]
      end.
      + assert (ee2 := eq2). rewrite ee in ee2. inversion ee2. subst.
        unshelve eapply R_stateR.
        * simpl. rewrite stack_cat_appstack. red. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. constructor.
      + rewrite <- eq2 in h.
        rewrite stack_context_appstack in h.
        dependent destruction h.
        * cbn in H. rewrite zipc_appstack in H. cbn in H.
          unshelve eapply R_cored2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl.
             rewrite zipc_appstack. rewrite zipc_stack_cat.
             repeat zip fold. intros; eapply cored_context.
             erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
        * destruct y' as [q hq].
          cbn in H0. inversion H0. subst.
          unshelve eapply R_positionR2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. f_equal.
             rewrite zipc_stack_cat.
             rewrite <- H2.
             rewrite 2!zipc_appstack. cbn. reflexivity.
          -- simpl.
             unfold posR in H. cbn in H.
             rewrite stack_position_appstack in H. cbn in H.
             rewrite stack_position_stack_cat.
             rewrite stack_position_appstack.
             eapply positionR_poscat.
             assumption.
    - rewrite <- eq1 in h.
      rewrite stack_context_appstack in h.
      dependent destruction h.
      + cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply R_cored. simpl.
        rewrite zipc_appstack. rewrite zipc_stack_cat.
        repeat zip fold. intros; eapply cored_context.
        erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      + destruct y' as [q hq].
        cbn in H0. inversion H0. (* Why is noconf failing at this point? *)
        subst.
        unshelve eapply R_positionR ; simpl.
        * f_equal.
          rewrite zipc_stack_cat.
          rewrite <- H2.
          rewrite 2!zipc_appstack. cbn. reflexivity.
        * unfold posR in H. cbn in H.
          rewrite stack_position_appstack in H. cbn in H.
          rewrite stack_position_stack_cat.
          rewrite stack_position_appstack.
          eapply positionR_poscat.
          assumption.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    simpl_reduce_stack Σ wfΣ.
    eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    simpl_reduce_stack Σ wfΣ.
    specialize (isr0 eq_refl) as (?&?).
    split; [easy|].
    simpl_stacks.
    intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&?).
    split; [easy|].
    simpl_stacks.
    intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    simpl_reduce_stack Σ wfΣ.
    destruct (hΣ _ wfΣ), (hx _ wfΣ).
    apply -> conv_cum_red_conv_iff; eauto.
    eapply h; eauto.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    simpl_reduce_stack Σ wfΣ.
    destruct (hΣ _ wfΣ), (hx _ wfΣ).
    apply <- conv_cum_red_conv_iff; eauto.
    eapply H; eauto.
  Qed.

  Opaque reduce_stack.
  Equations unfold_one_fix (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : wtp Γ (tFix mfix idx) π)
    : option (term * stack) :=

    unfold_one_fix Γ mfix idx π h with inspect (unfold_fix mfix idx) := {
    | @exist (Some (arg, fn)) eq1 with inspect (decompose_stack_at π arg) := {
      | @exist (Some (l, c, θ)) eq2 with inspect (reduce_stack RedFlags.default _ X
                                                               (Γ ,,, stack_context θ) c [] _) := {
        | @exist (cred, ρ) eq3 with construct_viewc cred := {
          | view_construct ind n ui := Some (fn, appstack l (App_l (zipc (tConstruct ind n ui) ρ) :: θ)) ;
          | view_other cred h' := None
          }
        } ;
      | _ := None
      } ;
    | _ := None
    }.
  Next Obligation.
    destruct (hΣ _ wfΣ).
    cbn. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    rewrite zipc_appstack in h. cbn in h.
    zip fold in h. specialize (h _ wfΣ). apply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_App in h as hh ; auto.
    destruct hh as [na [A' [B' [? [? ?]]]]].
    eexists. eassumption.
  Qed.
  Transparent reduce_stack.

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red_zipp :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp fn ξ) ∥.
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; try discriminate.
    all: noconf eq.
    unfold zipp.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack θ). intros l' s' e'.
    simpl.
    match type of eq3 with
    | _ = reduce_stack ?flags _ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags _ X Σ wfΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags _ X Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    constructor.
    rewrite stack_context_appstack. simpl.
    rewrite 2!mkApps_app. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    rewrite stack_context_appstack.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge; auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps; auto.
  Qed.

  Lemma unfold_one_fix_red_zippx :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) Γ (zippx (tFix mfix idx) π) (zippx fn ξ) ∥.
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    unfold zippx.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack θ). intros l' s' e'.
    simpl.
    match type of eq3 with
    | _ = reduce_stack ?flags _ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags _ X Σ wfΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags _ X Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    constructor. eapply red_it_mkLambda_or_LetIn.
    rewrite 2!mkApps_app. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite -> nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite -> decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_red :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) Γ (zipc (tFix mfix idx) π) (zipc fn ξ) ∥.
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of eq3 with
    | _ = reduce_stack ?flags _ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags _ X Σ wfΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags _ X Γ t π h) as hd
    end.
    clear Heq1 Heq2. cbn in r1.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    do 2 zip fold. constructor. eapply red_context_zip.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite -> nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps; auto.
  Qed.

  Lemma unfold_one_fix_cored :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored (fst Σ) Γ (zipc fn ξ) (zipc (tFix mfix idx) π).
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros ; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of eq3 with
    | _ = reduce_stack ?flags _ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags _ X Σ wfΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags _ X Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    do 2 zip fold. eapply cored_context.
    eapply cored_red_trans.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite -> nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite -> decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_decompose :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. cbn.
    case_eq (decompose_stack θ). intros l0 s1 H2.
    reflexivity.
  Qed.

  Lemma unfold_one_fix_None Γ mfix idx π wf :
    None = unfold_one_fix Γ mfix idx π wf ->
    ∥∑args,
     forall Σ (wfΣ : abstract_env_ext_rel X Σ),
      All2 (red Σ (Γ,,, stack_context π)) (decompose_stack π).1 args ×
      whnf RedFlags.default Σ (Γ,,, stack_context π) (mkApps (tFix mfix idx) args)∥.
  Proof using Type.
    funelim (unfold_one_fix Γ mfix idx π wf).
    all: intros [=].
    - constructor; eexists _; split; [apply All2_same; reflexivity|].
      eapply whnf_fixapp.
      clear -e. unfold unfold_fix in e. now destruct nth_error.
    - constructor; eexists _; split; [apply All2_same; reflexivity|].
      eapply whnf_fixapp.
      clear -e eq1. unfold unfold_fix in eq1. symmetry in e.
      destruct (decompose_stack π) eqn:decomp.
      apply decompose_stack_noStackApp in decomp as ?.
      apply decompose_stack_eq in decomp as ->.
      apply decompose_stack_at_appstack_None in e; eauto.
      destruct nth_error ; [|now right].
      left. eexists; split; eauto; cbn. now inversion eq1.
    - try clear Heqcall. destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      match type of eq3 with
      | _ = reduce_stack ?a ?b ?c ?d ?e ?f ?g =>
        pose proof (reduce_stack_sound a b c Σ wfΣ d e f g) as [r];
        pose proof (reduce_stack_whnf a b c d e f g) as wh;
        pose proof (reduce_stack_decompose a b c d e f g) as decomp;
        pose proof (reduce_stack_isred a b c d e f g) as isr
      end.
      rewrite <- eq3 in r, wh, decomp, isr.
      specialize (isr eq_refl) as (noapp&_).
      cbn in *.
      clear H eq3 H0.
      destruct (heΣ Σ wfΣ).
      symmetry in eq2.
      apply decompose_stack_at_length in eq2 as ?.
      apply decompose_stack_at_eq in eq2 as ->.
      rewrite stack_context_appstack.
      cbn. specialize (h Σ wfΣ).
      apply welltyped_zipc_zipp in h; auto.
      rewrite <- (stack_context_decompose ρ), decomp in wh.
      change (App_l c :: θ) with (appstack [c] θ) in *.
      rewrite !decompose_stack_appstack.
      rewrite zipp_as_mkApps !decompose_stack_appstack in h.
      destruct h as (ty&typ).
      cbn in *.
      rewrite stack_context_appstack in typ.
      cbn in *.
      destruct (decompose_stack ρ) eqn:decomp'.
      apply decompose_stack_eq in decomp' as ->.
      rewrite zipc_appstack in r.
      rewrite zipp_appstack in wh.
      cbn in *; subst; cbn in *.
      destruct (hΣ Σ wfΣ), (wh Σ wfΣ).
      constructor; exists (l ++ (mkApps cred l0) :: (decompose_stack θ).1).
      intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: apply red_mkApps; [reflexivity|].
      1: split.
      1,3: apply All2_app; [apply All2_same; reflexivity|].
      1,2: constructor; [|apply All2_same; reflexivity].
      1-2: eapply r.
      inversion H1. unfold unfold_fix in H0.
      case_eq (nth_error mfix idx); [intros d e | intro e]; rewrite e in H0; inversion H0.
      apply whnf_ne.
      econstructor.
      + eauto.
      + rewrite -> nth_error_snoc by easy.
        eauto.
      + eapply whnf_fix_arg_whne; eauto.
        now destruct cred.
      Unshelve. eauto.
  Qed.

  Inductive prog_view : term -> term -> Type :=
  | prog_view_App u1 v1 u2 v2 :
      prog_view (tApp u1 v1) (tApp u2 v2)

  | prog_view_Const c1 u1 c2 u2 :
      prog_view (tConst c1 u1) (tConst c2 u2)

  | prog_view_Lambda na1 A1 b1 na2 A2 b2 :
      prog_view (tLambda na1 A1 b1) (tLambda na2 A2 b2)

  | prog_view_Prod na1 A1 B1 na2 A2 B2 :
      prog_view (tProd na1 A1 B1) (tProd na2 A2 B2)

  | prog_view_Case ci p c brs ci' p' c' brs' :
      prog_view (tCase ci p c brs) (tCase ci' p' c' brs')

  | prog_view_Proj p c p' c' :
      prog_view (tProj p c) (tProj p' c')

  | prog_view_Fix mfix idx mfix' idx' :
      prog_view (tFix mfix idx) (tFix mfix' idx')

  | prog_view_CoFix mfix idx mfix' idx' :
      prog_view (tCoFix mfix idx) (tCoFix mfix' idx')

  | prog_view_Prim p p' :
      prog_view (tPrim p) (tPrim p')

  | prog_view_other :
      forall u v, prog_discr u v -> prog_view u v.

  Equations prog_viewc u v : prog_view u v :=
    prog_viewc (tApp u1 v1) (tApp u2 v2) :=
      prog_view_App u1 v1 u2 v2 ;

    prog_viewc (tConst c1 u1) (tConst c2 u2) :=
      prog_view_Const c1 u1 c2 u2 ;

    prog_viewc (tLambda na1 A1 b1) (tLambda na2 A2 b2) :=
      prog_view_Lambda na1 A1 b1 na2 A2 b2 ;

    prog_viewc (tProd na1 A1 B1) (tProd na2 A2 B2) :=
      prog_view_Prod na1 A1 B1 na2 A2 B2 ;

    prog_viewc (tCase ci p c brs) (tCase ci' p' c' brs') :=
      prog_view_Case ci p c brs ci' p' c' brs' ;

    prog_viewc (tProj p c) (tProj p' c') :=
      prog_view_Proj p c p' c' ;

    prog_viewc (tFix mfix idx) (tFix mfix' idx') :=
      prog_view_Fix mfix idx mfix' idx' ;

    prog_viewc (tCoFix mfix idx) (tCoFix mfix' idx') :=
      prog_view_CoFix mfix idx mfix' idx' ;

    prog_viewc (tPrim p) (tPrim p') :=
      prog_view_Prim p p' ;

    prog_viewc u v := prog_view_other u v I.

  Lemma welltyped_wf_local Σ Γ t :
    welltyped Σ Γ t ->
    ∥ wf_local Σ Γ ∥.
  Proof using Type.
    intros []; sq.
    eapply typing_wf_local in X0; eauto.
  Qed.

  Definition eqb_universe_instance :=
    compare_universe_instance (abstract_env_compare_universe X Conv).

  Lemma eqb_universe_instance_spec :
    forall u v Σ (wfΣ : abstract_env_ext_rel X Σ),
      forallb (wf_universeb Σ) (map Universe.make' u) ->
      forallb (wf_universeb Σ) (map Universe.make' v) ->
      eqb_universe_instance u v ->
      cmp_universe_instance (eq_universe (global_ext_constraints Σ)) u v.
  Proof using Type.
    intros u v Σ wfΣ Hu Hv.
    eapply elimT.
    eapply reflect_reflectT, reflect_cmp_universe_instance; tea.
    intros.
    apply iff_reflect.
    eapply abstract_env_compare_universe_correct with (conv_pb := Conv); tas.
    all: now eapply wf_universe_iff.
  Qed.

  Arguments LevelSet.mem : simpl never.

  Lemma compare_universeb_complete Σ (wfΣ : abstract_env_ext_rel X Σ) pb u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    compare_universe (global_ext_constraints Σ) pb u u' ->
    abstract_env_compare_universe X pb u u'.
  Proof using Type.
    intros all1 all2 conv.
    destruct (heΣ _ wfΣ).
    eapply abstract_env_compare_universe_correct; eauto.
Qed.

  Lemma get_level_make l :
    LevelExpr.get_level (LevelExpr.make l) = l.
  Proof using Type. now destruct l. Qed.

  Lemma compare_universeb_make_complete Σ (wfΣ : abstract_env_ext_rel X Σ) pb x y :
    wf_level Σ x ->
    wf_level Σ y ->
    compare_universe (global_ext_constraints Σ) pb (Universe.make' x) (Universe.make' y) ->
    abstract_env_compare_universe X pb (Universe.make' x) (Universe.make' y).
  Proof using Type.
    intros wfx wfy r.
    eapply compare_universeb_complete; eauto.
    - intros ? ->%LevelExprSet.singleton_spec; auto.
    - intros ? ->%LevelExprSet.singleton_spec; auto.
  Qed.

  Lemma eqb_universe_instance_complete Σ (wfΣ : abstract_env_ext_rel X Σ) u u' :
    wf_instance Σ u ->
    wf_instance Σ u' ->
    cmp_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
    eqb_universe_instance u u'.
  Proof using Type.
    intros memu memu'.
    eapply introT.
    unfold wf_instance in *.
    eapply reflect_reflectT, reflect_cmp_universe_instance with (p := wf_universeb Σ); tea.
    1: intros ????; eapply iff_reflect, abstract_env_compare_universe_correct with (conv_pb := Conv); tea.
    1,2: now eapply wf_universe_iff.
    all: solve_all; eapply wf_universe_iff; intros ? ->%LevelExprSet.singleton_spec; auto.
  Qed.

  Lemma compare_universe_variance_complete Σ (wfΣ : abstract_env_ext_rel X Σ) pb v u u' :
    wf_level Σ u ->
    wf_level Σ u' ->
    cmp_universe_variance (compare_universe Σ) pb v u u' ->
    compare_universe_variance (abstract_env_compare_universe X) pb v u u'.
  Proof using Type.
    intros memu memu' r.
    destruct v; cbn in *; eauto.
    - eapply compare_universeb_make_complete; eauto.
    - eapply compare_universeb_make_complete with (pb := Conv); eauto.
  Qed.

  Lemma compare_universe_instance_variance_complete Σ (wfΣ : abstract_env_ext_rel X Σ) pb v u u' :
    wf_instance Σ u ->
    wf_instance Σ u' ->
    cmp_universe_instance_variance (compare_universe Σ) pb v u u' ->
    compare_universe_instance_variance (abstract_env_compare_universe X) pb v u u'.
  Proof using Type.
    intros memu memu' r.
    induction r in memu, memu' |- *; cbnr.
    - depelim memu.
      depelim memu'.
      apply Bool.andb_true_iff.
      split.
      + eapply compare_universe_variance_complete; eauto.
      + now apply IHr.
  Qed.


  Lemma consistent_instance_ext_wf Σ udecl u :
    consistent_instance_ext Σ udecl u ->
    wf_instance Σ u.
  Proof using Type.
    intros cons.
    unfold consistent_instance_ext, consistent_instance in *.
    destruct udecl.
    - destruct u; cbn in *; [|congruence].
      constructor.
    - destruct cons as (mems&_&_).
      apply forallb_Forall in mems.
      eapply Forall_impl; eauto.
      cbn.
      intros ? ?%LevelSet.mem_spec; auto.
  Qed.

  Lemma welltyped_zipc_tConst_inv Σ (wfΣ : abstract_env_ext_rel X Σ) Γ c u π :
    welltyped Σ Γ (zipc (tConst c u) π) ->
    exists cst,
      declared_constant Σ c cst
      × consistent_instance_ext Σ (cst_universes cst) u.
  Proof using Type.
    intros h.
    zip fold in h.
    destruct (heΣ _ wfΣ).
    apply welltyped_context in h; auto.
    destruct h as (?&typ).
    apply inversion_Const in typ as (?&?&?&wfu&_); auto.
    now unfold declared_constant in d.
  Qed.

  Lemma red_conv_cum_l {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ u v.
  Proof using Type.
    intros r. pose proof (hΣ _ wfΣ). sq. now apply red_ws_cumul_pb.
  Qed.

  Lemma red_conv_cum_r {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ v u.
  Proof using Type.
    intros r. pose proof (hΣ _ wfΣ). sq. now apply red_ws_cumul_pb_inv.
  Qed.

  Lemma closed_red_zipp {Σ Γ t u π} :
    is_open_term Γ (zipp t π) ->
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Γ ⊢ zipp t π ⇝ zipp u π.
  Proof using Type.
    intros cltπ [clΓ clt r].
    eapply into_closed_red; tea.
    now eapply red_zipp.
  Qed.

  Ltac specialize_Σ wfΣ :=
    repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end.

  Equations(noeqns) unfold_constants (Γ : context) (leq : conv_pb)
            (c : kername) (u : Instance.t) (π1 : stack)
            (h1 : wtp Γ (tConst c u) π1)
            (c' : kername) (u' : Instance.t) (π2 : stack)
            (h2 : wtp Γ (tConst c' u') π2)
            (ne : c <> c' \/ (c = c' /\ ~eqb_universe_instance u u'))
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tConst c u) π1 (tConst c' u') π2 h2)
    : ConversionResult (conv_term leq Γ (tConst c u) π1 (tConst c' u') π2) :=

    unfold_constants Γ leq c u π1 h1 c' u' π2 h2 ne hx aux
    with inspect (abstract_env_lookup X c') := {
    | @exist (Some (ConstantDecl {| cst_body := Some b |})) eq1 :=
      isconv_red leq (tConst c u) π1 (subst_instance u' b) π2 aux ;
    (* Inductive or not found *)
    | @exist _ eq1 with inspect (abstract_env_lookup X c) := {
      | @exist (Some (ConstantDecl {| cst_body := Some b |})) eq2 :=
        isconv_red leq (subst_instance u b) π1
                        (tConst c' u') π2 aux ;
      (* Both Inductive or not found *)
      | @exist _ eq2 := no (NotFoundConstants c c')
      }
    }.
(*
    Solve Obligations of unfold_constants with
  try destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
  exfalso;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try erewrite <- abstract_env_lookup_correct' in eq1; eauto ;
  try erewrite <- abstract_env_lookup_correct' in eq2; eauto ;
  try clear aux; specialize_Σ wfΣ;
  try solve
      [match goal with
       | [H: welltyped ?Σ ?Γ ?t |- _] =>
         let id := fresh in
         apply welltyped_zipc_tConst_inv in H as id; eauto;
           destruct id as (?&?&?);
           unfold declared_constant in *;
           congruence
       end].*)
  Ltac  solve_unfold_constants aux eq1 eq2 Σ wfΣ :=
  try destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
  exfalso; pose (hΣ Σ wfΣ); sq;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try erewrite <- abstract_env_lookup_correct' in eq1; eauto ;
  try erewrite <- abstract_env_lookup_correct' in eq2; eauto ;
  try unshelve eapply declared_constant_to_gen in eq1; eauto ;
  try unshelve eapply declared_constant_to_gen in eq2; eauto ;
  try clear aux; specialize_Σ wfΣ;
  solve
      [match goal with
       | [H: welltyped ?Σ ?Γ ?t |- _] =>
         let id := fresh in
         apply welltyped_zipc_tConst_inv in H as id; eauto;
           destruct id as (?&decl&?);
           unshelve eapply declared_constant_to_gen in decl; eauto;
           congruence
       end].

  Next Obligation.
    try rewrite <- wf_env_lookup_correct in eq1.
    pose proof (hΣ _ wfΣ).
    sq.
    eapply red_welltyped; try eapply h2; eauto.
    eapply red_zipc.
    eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros. eapply cored_zipc.
    eapply cored_const. erewrite abstract_env_lookup_correct'; eassumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; destruct (hΣ _ wfΣ).
    etransitivity; try eauto.
    eapply red_conv_cum_r ; try assumption.
    specialize (hx _ wfΣ).
    eapply closed_red_zipp.
    * clear aux. eapply welltyped_zipc_zipp in h2; eauto.
      eapply welltyped_is_open_term in h2.
      sq. now rewrite (All2_fold_length hx).
    * eapply into_closed_red; fvs.
      + eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
      + red in h. sq. fvs.
   Unshelve. eauto.
  Qed.
  Next Obligation.
    (* Contraposition of previous goal *)
    apply h; clear h. intros Σ wfΣ.
    destruct (hΣ _ wfΣ).
    etransitivity ; try eauto.
    specialize (hx _ wfΣ).
    eapply red_conv_cum_l ; try assumption.
    eapply closed_red_zipp.
    * clear aux; eapply welltyped_zipc_zipp in h2; eauto.
      eapply welltyped_is_open_term in h2. sq. now rewrite (All2_fold_length hx).
    * eapply into_closed_red; fvs.
      + eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
      + sq. fvs.
  Unshelve. eauto.
  Qed.
  Next Obligation.
    pose proof (hΣ _ wfΣ). sq.
    eapply red_welltyped ; [eauto|exact (h1 _ wfΣ)|..].
    eapply red_zipc.
    eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros. eapply cored_zipc.
    eapply cored_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (heΣ _ wfΣ) as [wΣ].
    etransitivity ; try eauto.
    eapply red_conv_cum_l ; try assumption.
    eapply closed_red_zipp.
    { eapply welltyped_zipc_zipp in h1; auto; fvs. }
    eapply into_closed_red; fvs.
    + eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
    + specialize (hx _ wfΣ). clear -hx wΣ. sq.  fvs.
    Unshelve. all : eauto.
  Qed.
  Next Obligation.
    (* Contraposition of previous goal *)
    apply h; clear h. intros Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    etransitivity ; try eauto.
    eapply red_conv_cum_r ; try assumption.
    eapply closed_red_zipp.
    { eapply welltyped_zipc_zipp in h1; auto; fvs. }
    eapply into_closed_red; fvs.
    + eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
    + specialize (hx _ wfΣ). sq; fvs.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    (* Both c and c' are axioms. Either they are different constants or they are not
       convertible because the universes are different. *)
      destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (H _ wfΣ).
      apply conv_cum_alt in H as [(?&?&[r1 r2 eq])]; auto.
    2: pose proof (hΣ _ wfΣ); sq ; eauto.
    rewrite !zipp_as_mkApps in r1, r2.
    erewrite <- !abstract_env_lookup_correct' in eq1, eq2; eauto.
    symmetry in eq1, eq2.
    eapply declared_constant_from_gen in eq1, eq2.
    generalize hΣ. eintros []; eauto.
    unshelve eapply closed_red_mkApps_tConst_axiom in r1 as (?&->&?); eauto.
    eapply closed_red_mkApps_tConst_axiom in r2 as (?&->&?); eauto.
    apply eq_termp_mkApps_inv in eq as (eq&?); [|easy|easy].
    depelim eq.
    destruct ne as [|(_&ne)]; [congruence|].

    clear aux. specialize (h1 _ wfΣ). specialize (h2 _ wfΣ).
    apply welltyped_zipc_tConst_inv in h1 as (cst1&decl1&cons1); eauto.
    apply welltyped_zipc_tConst_inv in h2 as (cst2&decl2&cons2); eauto.
    unshelve eapply declared_constant_to_gen in decl1, decl2; eauto.
    eapply declared_constant_inj in decl1; eauto; subst.
    apply consistent_instance_ext_wf in cons1.
    apply consistent_instance_ext_wf in cons2.
    eapply eqb_universe_instance_complete in c1; auto.
  Qed.
  (* Why Solve All Obligations is not working here ??? *)
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Defined.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ H. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ H. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.
  Next Obligation. solve_unfold_constants aux eq1 eq2 Σ wfΣ. Qed.

  Lemma welltyped_zipc_tCase_brs_length Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci motive discr brs π :
    welltyped Σ Γ (zipc (tCase ci motive discr brs) π) ->
    exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|.
  Proof using Type.
    pose proof (hΣ _ wfΣ). sq.
    intros wf.
    zip fold in wf.
    apply welltyped_context in wf; [|auto].
    destruct wf as [ctyp typ].
    apply inversion_Case in typ as (mdecl&idecl&?&?&[]&?); auto.
    exists mdecl, idecl.
    split; [easy|].
    now apply All2i_length in brs_ty.
  Qed.

  Equations (noeqns) isconv_context_aux
            (Γ Γ' Δ Δ' : context)
            (cc : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥Σ ⊢ Γ = Γ'∥)
            (check :
               forall (leq : conv_pb) (Δh : context_hole) (t : term) (Δh' : context_hole) (t' : term),
                 Δ = fill_context_hole Δh t ->
                 Δ' = fill_context_hole Δh' t' ->
                 (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_ctx_pb_rel Conv Σ Γ (context_hole_context Δh) (context_hole_context Δh')∥) ->
                 ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), conv_cum leq Σ (Γ,,, context_hole_context Δh) t t'))
            (Δpre Δ'pre Δpost Δ'post : context)
            (eq : Δ = Δpre ,,, Δpost)
            (eq' : Δ' = Δ'pre ,,, Δ'post) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_ctx_pb_rel Conv Σ Γ Δpre Δ'pre∥) by struct Δpre := {

    isconv_context_aux Γ Γ' Δ Δ' cc check [] [] Δpost Δ'post eq eq' => yes;

    isconv_context_aux Γ Γ' Δ Δ' cc check
                           (mkdecl na bd ty :: Δpre)
                           (mkdecl na' bd' ty' :: Δ'pre)
                           Δpost Δ'post eq eq'
      with isconv_context_aux
             Γ Γ' Δ Δ' cc check Δpre Δ'pre
             (Δpost ++ [mkdecl na bd ty])
             (Δ'post ++ [mkdecl na' bd' ty']) _ _ := {

      | Error ce not_conv_rest => no ce;

      | Success conv_rest
        with inspect (eqb_binder_annot na na') := {

        | exist false neq_binders => no (ContextNotConvertibleAnn
                                           (Γ,,, Δpre) (mkdecl na bd ty)
                                           (Γ',,, Δ'pre) (mkdecl na' bd' ty'));

        | exist true eq_binders
          with check Conv
               (Δpre, decl_hole_type na bd, Δpost) ty
               (Δ'pre, decl_hole_type na' bd', Δ'post) ty'
               _ _ conv_rest := {

          | Error ce not_conv_type => no (ContextNotConvertibleType
                                            (Γ,,, Δpre) (mkdecl na bd ty)
                                            (Γ',,, Δ'pre) (mkdecl na' bd' ty'));

          | Success conv_type with bd, bd' := {

            | Some body | Some body'
                with check Conv
                     (Δpre, decl_hole_body na ty, Δpost) body
                     (Δ'pre, decl_hole_body na' ty', Δ'post) body'
                     _ _ conv_rest := {
              | Error ce not_conv_body => no (ContextNotConvertibleBody
                                                (Γ,,, Δpre) (mkdecl na bd ty)
                                                (Γ',,, Δ'pre) (mkdecl na' bd' ty'));

              | Success conv_body => yes
              };

            | None | None => yes;

            | _ | _ => no (ContextNotConvertibleBody
                             (Γ,,, Δpre) (mkdecl na bd ty)
                             (Γ',,, Δ'pre) (mkdecl na' bd' ty'))
            }
          }
        }
      };

    isconv_context_aux Γ Γ' Δ Δ' cc check
                       Δpre Δ'pre Δpost Δ'post eq eq' => no ContextNotConvertibleLength
    }.
  Next Obligation.
    pose proof (heΣ _ wfΣ). specialize (cc _ wfΣ). sq.
    constructor; fvs.
    - constructor.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
    depelim H. depelim a.
  Qed.
  Next Obligation.
  destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
  pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
  destruct H as [H]; depelim H. depelim a.
  Qed.
  Next Obligation.
    unfold app_context.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    unfold app_context.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    unfold conv_cum in conv_type, conv_body.
    pose proof (hΣ _ wfΣ). specialize_Σ wfΣ.
    sq. constructor; fvs.
    constructor; auto.
    * now destruct conv_rest.
    * constructor; auto.
      apply eqb_annot_spec; auto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
    destruct H as [H].
    contradiction not_conv_body.
    depelim H.
    depelim a. depelim a0. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    constructor; auto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
    destruct H as [H].
    depelim H.
    depelim a. depelim a0.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
    destruct H as [H].
    depelim H.
    depelim a. depelim a0.
  Qed.
  Next Obligation.
    red in conv_type. pose proof (hΣ _ wfΣ). specialize_Σ wfΣ.
    sq. constructor; fvs.
    constructor; auto.
    * now destruct conv_rest.
    * constructor; auto.
      apply eqb_annot_spec; auto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
    destruct H as [H].
    contradiction not_conv_type.
    depelim H. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    constructor.
    depelim a; auto. depelim a0; eauto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
    destruct H as [H].
    depelim H.
    depelim a. depelim a0.
    - apply eqb_annot_spec in eqna; congruence.
    - apply eqb_annot_spec in eqna; congruence.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ). specialize (H _ wfΣ). sq.
    destruct H as [H].
    contradiction not_conv_rest.
    depelim H.
    depelim a. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    constructor; auto.
    split; auto.
    Unshelve. all: eauto.
  Qed.

  Definition isconv_context
            (Γ Γ' Δ Δ' : context)
            (cc : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ⊢ Γ = Γ' ∥)
            (check :
               forall (leq : conv_pb) (Δh : context_hole) (t : term) (Δh' : context_hole) (t' : term),
                 Δ = fill_context_hole Δh t ->
                 Δ' = fill_context_hole Δh' t' ->
                 (forall Σ (wfΣ : abstract_env_ext_rel X Σ),  ∥ws_cumul_ctx_pb_rel Conv Σ Γ (context_hole_context Δh) (context_hole_context Δh')∥) ->
                 ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), conv_cum leq Σ (Γ,,, context_hole_context Δh) t t'))
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_ctx_pb_rel Conv Σ Γ Δ Δ'∥) :=
    isconv_context_aux Γ Γ' Δ Δ' cc check Δ Δ' [] [] eq_refl eq_refl.

  Lemma case_conv_brs_inv {Γ ci br br' p c brs1 brs2 π}
  (h : wtp Γ (tCase ci p c (brs1 ++ br :: brs2)) π)
  (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
  (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ br' :: brs2')) π')
  (hx : conv_stack_ctx Γ π π')
  (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
  (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥) :
  ∥ ∑ mdecl idecl,
    [× forall Σ (wfΣ : abstract_env_ext_rel X Σ), declared_inductive Σ ci mdecl idecl,
       #|pparams p| = ind_npars mdecl,
       #|pparams p'| = ind_npars mdecl,
       eq_context_upto_names br.(bcontext) br'.(bcontext),
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p| br.(bcontext) &
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p'| br'.(bcontext)] ∥.
  Proof using Type.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ) as [hΣ]. specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct hp as [hp].
    destruct h1 as [h1].
    eapply welltyped_zipc_zipp in h; auto.
    eapply welltyped_zipc_zipp in h'; auto.
    rewrite !zipp_as_mkApps in h, h'.
    destruct h as [s h]. destruct h' as [s' h'].
    eapply PCUICValidity.inversion_mkApps in h as [A [hcase _]].
    eapply PCUICValidity.inversion_mkApps in h' as [A' [hcase' _]].
    destruct hp as [].
    eapply inversion_Case in hcase as [mdecl [idecl [decli [indices [hcase _]]]]]; auto.
    eapply inversion_Case in hcase' as [mdecl' [idecl' [decli' [indices' [hcase' _]]]]]; auto.
    pose proof (decli_ := decli); pose proof (decli'_ := decli').
    unshelve eapply declared_inductive_to_gen in decli, decli'; eauto.
    destruct (declared_inductive_inj decli decli'). subst mdecl' idecl'.
    constructor.
    assert (clm' : test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
      #|pparams p'| br'.(bcontext)).
    { rewrite test_context_k_closed_on_free_vars_ctx.
      destruct hcase'.
      eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
      depelim a2. clear a1 a2.
      destruct p0 as [p0 _].
      cbn in p0.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact p0.
      rewrite <-closedn_ctx_on_free_vars.
      destruct ci. cbn.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (PCUICInstConv.closedn_ctx_cstr_branch_context (c:=(ci_ind, #|x|)) (idecl:=idecl)).
        split; auto. rewrite e; cbn. rewrite nth_error_app_ge; auto.
        now rewrite Nat.sub_diag; cbn. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
    }
    rewrite test_context_k_closed_on_free_vars_ctx.
    destruct hcase.
    eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
    depelim a2. eapply All2i_length in a1; clear a2.
    destruct p0 as [p0 _].
    destruct hcase'.
    eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
    depelim a3. eapply All2i_length in a2. clear a3.
    destruct p1 as [p1 _].
    rewrite e in e0. cbn in *.
    pose proof (All2_length h1). rewrite <- a1 in H.
    rewrite <- a2 in H. eapply app_inj_length_l in e0 as [-> eq]; auto.
    noconf eq. exists mdecl, idecl.
    split; tea.
    - intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    - eapply (wf_predicate_length_pars wf_pred).
    - eapply (wf_predicate_length_pars wf_pred0).
    - etransitivity; tea.
      now symmetry.
    - eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact p0.
      rewrite <- closedn_ctx_on_free_vars.
      destruct ci. cbn.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (PCUICInstConv.closedn_ctx_cstr_branch_context (c:=(ci_ind, #|x0|)) (idecl:=idecl)).
        split; auto. rewrite e; cbn. rewrite nth_error_app_ge; auto.
        now rewrite Nat.sub_diag; cbn. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
      Unshelve. all: eauto.
  Qed.


  Equations isconv_branches (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs1 brs2 : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c (brs1 ++ brs2)) π)
    (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ brs2')) π')
    (hx : conv_stack_ctx Γ π π')
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥)
    (aux : Aux Term Γ (tCase ci p c (brs1 ++ brs2)) π (tCase ci p' c' (brs1' ++ brs2')) π' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs2 brs2' ∥)
    by struct brs2 :=

    isconv_branches Γ ci
      p c brs1 ({| bcontext := m; bbody := br |} :: brs2) π h
      p' c' brs1' ({| bcontext := m'; bbody := br' |} :: brs2') π' h' hx hp h1 aux
     with isconv_red_raw Conv
              br (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π)
              br' (Case_branch ci p' c' (brs1', branch_hole_body m', brs2') :: π') aux := {
      | Success h2
        with isconv_branches Γ ci
              p c (brs1 ++ [{|bcontext := m; bbody := br|}]) brs2 π _
              p' c' (brs1' ++ [{| bcontext := m'; bbody := br'|}]) brs2' π' _ hx hp _ (expand aux) := {
        | Success h3 := yes ;
        | Error e h'' := no e
        } ;
      | Error e nconv := no e
    } ;

    isconv_branches Γ ci
      p c brs1 [] π h
      p' c' brs1' [] π' h' hx hp h1 aux := yes ;

    isconv_branches Γ ci
      p c brs1 brs2 π h
      p' c' brs1' brs2' π' h' hx hp h1 aux := False_rect _ _.
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    clear aux.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. destruct (hΣ _ wfΣ).
    destruct h1 as [h1].
    apply All2_length in h1 as e1.
    apply welltyped_zipc_tCase_brs_length in h as (?&?&?&?); eauto.
    apply welltyped_zipc_tCase_brs_length in h' as (?&?&?&?); eauto.
    unshelve eapply declared_inductive_to_gen in H, H1; eauto.
    pose proof (PCUICInductiveInversion.declared_inductive_unique_sig H H1) as u; noconf u.
    rewrite !length_app in H0, H2.
    cbn in *.
    lia.
  Qed.
  Next Obligation.
    clear aux.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. destruct (hΣ _ wfΣ).
    destruct h1 as [h1].
    apply All2_length in h1 as e1.
    apply welltyped_zipc_tCase_brs_length in h as (?&?&?&?); eauto.
    apply welltyped_zipc_tCase_brs_length in h' as (?&?&?&?); eauto.
    unshelve eapply declared_inductive_to_gen in H, H1; eauto.
    pose proof (PCUICInductiveInversion.declared_inductive_unique_sig H H1) as u; noconf u.
    rewrite !length_app in H0, H2.
    cbn in *.
    lia.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    1: reflexivity.
    rewrite <- app_nil_r.
    rewrite stack_position_cons.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    eapply case_conv_brs_inv in h1; tea.
    rename H into wfΣ; pose proof (hΣ _ wfΣ).
    specialize_Σ wfΣ.
    sq. destruct h1 as [mdecl [idecl [decli eqp eqp' eqm clm clm']]].
    transitivity (Γ ,,, stack_context π ,,, inst_case_context (pparams p') (puinst p') m').
    - unfold app_context; rewrite <-app_assoc.
      inv_on_free_vars.
      eapply inst_case_ws_cumul_ctx_pb; tea.
      * fvs.
      * fvs.
      * eapply hp.
      * eapply hp.
    - unfold app_context. rewrite <- app_assoc. eapply ws_cumul_ctx_pb_app_same; auto.
      rewrite on_free_vars_ctx_app.
      apply andb_true_iff. split; auto. 1:now apply ws_cumul_ctx_pb_closed_left in hx.
      eapply on_free_vars_ctx_inst_case_context; trea.
      destruct hp.
      now eapply (ws_cumul_pb_terms_open_terms_right a).
  Qed.
  Next Obligation.
    now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    destruct (case_conv_brs_inv h p' c' brs1' brs2' _ h') as [[mdecl [idecl [decli eqp eqp' eqm clm clm']]]]; tea.
    specialize_Σ wfΣ.
    destruct h1 as [h1], h2 as [h2].
    constructor. apply All2_app.
    - assumption.
    - constructor.
      2: now constructor.
      simpl.
      unfold zipp in h2.
      split; auto.
      cbn in h2.
      unfold inst_case_branch_context. cbn.
      now unfold app_context; rewrite app_assoc.
  Qed.
  Next Obligation.
    clear aux. unfold isconv_branches_obligations_obligation_13.
    eapply R_irrelevance. 2:tea. cbn.
    f_equal. f_equal. 2:{ f_equal. now rewrite <-app_assoc. }
    f_equal. f_equal. f_equal. now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    destruct (case_conv_brs_inv h p' c' brs1' brs2' _ h') as [[mdecl [idecl [decli eqp eqp' eqm clm clm']]]]; tea.
    specialize_Σ wfΣ.
    destruct h2 as [h2], h3 as [h3].
    constructor.
    constructor; auto.
    unfold zipp in *; simpl in *.
    split; auto.
    rewrite app_context_assoc in h2; auto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h''; clear h''. intros. specialize_Σ wfΣ.
    destruct H as [H]; inversion H; now constructor.
  Qed.
  Next Obligation.
    (* Contrapositive of 3rd obligation above *)
    apply nconv; clear nconv. intros Σ wfΣ. specialize_Σ wfΣ.
    destruct h1 as [h1], H as [h2].
    constructor. inversion h2; clear h2.
    destruct X0 as [_ h2]. simpl in h2. cbn.
    now rewrite app_context_assoc.
  Qed.

  Equations isconv_branches' (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c brs) π)
    (ci' : case_info)
    (p' : predicate term) (c' : term) (brs' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci' p' c' brs') π')
    (hx : conv_stack_ctx Γ π π')
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (ei : ci = ci')
    (aux : Aux Term Γ (tCase ci p c brs) π (tCase ci' p' c' brs') π' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs brs' ∥) :=

    isconv_branches' Γ ci p c brs π h ci' p' c' brs' π' h' hx hp eci aux :=
      isconv_branches Γ ci p c [] brs π _ p' c' [] brs' π' _ _ _ _ (expand aux).
  Next Obligation.
    constructor. constructor.
  Qed.

  (* Factorise notions of fixpoints *)
  Inductive fix_kind :=
  | IndFix
  | CoIndFix.

  Definition mFix k :=
    match k with
    | IndFix => tFix
    | CoIndFix => tCoFix
    end.

  Definition mFix_mfix fk :=
    match fk with
    | IndFix => Fix
    | CoIndFix => CoFix
    end.

  Definition mFixRargMismatch fk :=
    match fk with
    | IndFix => FixRargMismatch
    | CoIndFix => CoFixRargMismatch
    end.

  Definition mFixMfixMismatch fk :=
    match fk with
    | IndFix => FixMfixMismatch
    | CoIndFix => CoFixMfixMismatch
    end.

  Equations isws_cumul_pb_fix_types (fk : fix_kind) (Γ : context)
    (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v =>
                   (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
                   (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
            ) mfix1 mfix1' ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v =>
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix2 mfix2' ∥)
    by struct mfix2 :=

    isws_cumul_pb_fix_types
      fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 aux
    with inspect (eqb u.(rarg) v.(rarg)) := {
    | @exist true eq1
      with inspect (eqb_binder_annot u.(dname) v.(dname)) := {
      | @exist true eqann
        with isconv_red_raw Conv
             u.(dtype)
             (mFix_mfix fk (mfix1, def_hole_type u.(dname) u.(dbody) u.(rarg), mfix2) idx :: π)
             v.(dtype)
             (mFix_mfix fk (mfix1', def_hole_type v.(dname) v.(dbody) v.(rarg), mfix2') idx :: π')
             aux
      := {
      | Success h2 with
          isws_cumul_pb_fix_types fk Γ idx
            (mfix1 ++ [u]) mfix2 π _
            (mfix1' ++ [v]) mfix2' π' _
            hx _ (expand aux)
        := {
        | Success h3 := yes ;
        | Error e h'' := no e
        } ;
      | Error e h'' := no e
      } ;
      | @exist false neqann := no (
        FixRargMismatch idx
          (Γ ,,, stack_context π) u mfix1 mfix2
          (Γ ,,, stack_context π') v mfix1' mfix2'
      ) };
    | @exist false eq1 := no (
        mFixRargMismatch fk idx
          (Γ ,,, stack_context π) u mfix1 mfix2
          (Γ ,,, stack_context π') v mfix1' mfix2'
      )
    } ;

    isws_cumul_pb_fix_types fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 aux := yes ;

    (* TODO It might be more efficient to check the lengths first
       and then conclude this case is not possible.
    *)
    isws_cumul_pb_fix_types fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 aux :=
      no (
        mFixMfixMismatch fk idx
          (Γ ,,, stack_context π) (mfix1 ++ mfix2)
          (Γ ,,, stack_context π') (mfix1' ++ mfix2')
      ).

  Next Obligation.
    (* Left list is empty *)
    destruct H as [H]; inversion H.
  Qed.
  Next Obligation.
    (* Right list is empty *)
    destruct H as [H]; inversion H.
  Qed.
  Next Obligation.
    destruct u. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    destruct v. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    - destruct u. destruct fk. all: reflexivity.
    - rewrite <- app_nil_r, stack_position_cons. destruct fk.
      + eapply positionR_poscat. constructor.
      + eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct fk.
    - simpl. eauto.
    - simpl. eauto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2.
    constructor.
    apply All2_app. 1: assumption.
    constructor. 2: constructor.
    change (true = eqb u.(rarg) v.(rarg)) in eq1.
    destruct (eqb_specT u.(rarg) v.(rarg)). 2: discriminate.
    symmetry in eqann.
    apply eqb_binder_annot_spec in eqann.
    split; auto.
    destruct fk; simpl in *; auto.
    all: intros; erewrite (abstract_env_ext_irr _ _ wfΣ); intuition eauto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    clear aux.
    eapply R_irrelevance; tea; cbn.
    now rewrite <- !app_assoc.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2. sq.
    constructor.
    2: eauto.
    change (true = eqb u.(rarg) v.(rarg)) in eq1.
    destruct (eqb_specT u.(rarg) v.(rarg)). 2: discriminate.
    symmetry in eqann.
    apply eqb_binder_annot_spec in eqann.
    clear eq1.
    destruct fk.
    all: split; [ intros; erewrite (abstract_env_ext_irr _ _ wfΣ) | ]; intuition eauto .
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h''; clear h''.
    destruct H as [H]; inversion H.
    constructor; assumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct H as [H]; inversion H; destruct X0 as [eq_uv _].
    apply h''; clear h''; constructor.
    destruct fk; apply eq_uv; eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct H as [H]; inversion H; destruct X0 as [_ [eq_uv eqann]].
    change (?ru =? ?rv) with (eqb ru rv) in eq1.
    symmetry in neqann.
    (* would be simpler using ssr's move/ tactic *)
    pose proof (eqb_annot_reflect (dname u) (dname v)) as r.
    now apply (ssrbool.elimF r neqann).
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct H as [H]; inversion H; destruct X0 as [_ [eq_uv eqann]].
    change (?ru =? ?rv) with (eqb ru rv) in eq1.
    destruct (eqb_specT (rarg u) (rarg v)) as [|neq_uv]; [discriminate|].
    exact (neq_uv eq_uv).
  Qed.

  (* TODO MOVE *)
  Lemma conv_context_decl Pcmp :
    forall Σ Γ Δ d d',
      conv_context Pcmp Σ Γ Δ ->
      conv_decls Pcmp Σ Γ Δ d d' ->
      conv_context Pcmp Σ (Γ ,, d) (Δ ,, d').
  Proof using Type.
    intros Γ Δ d d' hx h.
    destruct h.
    all: constructor. all: try assumption.
    all: constructor. all: assumption.
  Qed.

  Lemma stack_entry_context_mFix_mfix_bd :
    forall fk na ty ra mfix1 mfix2 idx,
      stack_entry_context (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx) =
      fix_context_alt (map def_sig mfix1 ++ (na,ty) :: map def_sig mfix2).
  Proof using Type.
    intros fk na ty ra mfix1 mfix2 idx.
    destruct fk. all: reflexivity.
  Qed.

  Equations isws_cumul_pb_fix_bodies (fk : fix_kind) (Γ : context) (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix1 mfix1' ∥)
    (ha : ∥ All2 (fun u v =>
                    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
                    (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
           ) (mfix1 ++ mfix2) (mfix1' ++ mfix2') ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix2 mfix2' ∥)
    by struct mfix2 :=

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 ha aux
  with isconv_red_raw Conv
        u.(dbody)
        (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π)
        v.(dbody)
        (mFix_mfix fk (mfix1', def_hole_body v.(dname) v.(dtype) v.(rarg), mfix2') idx :: π')
        aux
  := {
  | Success h2
    with isws_cumul_pb_fix_bodies fk Γ idx
           (mfix1 ++ [u]) mfix2 π _
           (mfix1' ++ [v]) mfix2' π' _
           hx _ _ (expand aux)
    := {
    | Success h3 := yes ;
    | Error e h'' := no e
    } ;
  | Error e h'' := no e
  } ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 ha aux := yes ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 ha aux :=
    False_rect _ _.

  Next Obligation.
    destruct h1 as [h1], ha as [ha].
    apply All2_length in h1 as e1.
    apply All2_length in ha as ea.
    rewrite !length_app in ea. simpl in ea. lia.
  Qed.
  Next Obligation.
    destruct h1 as [h1], ha as [ha].
    apply All2_length in h1 as e1.
    apply All2_length in ha as ea.
    rewrite !length_app in ea. simpl in ea. lia.
  Qed.
  Next Obligation.
    destruct u. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    destruct v. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    - destruct u. destruct fk. all: reflexivity.
    - rewrite <- app_nil_r, stack_position_cons.
      destruct fk.
      + eapply positionR_poscat. constructor.
      + eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _  wfΣ) as [wΣ], ha as [ha], hx as [hx].
    clear - wfΣ wΣ ha hx. constructor.
    rewrite 2!stack_entry_context_mFix_mfix_bd.
    change (dname u, dtype u) with (def_sig u).
    change (dname v, dtype v) with (def_sig v).
    repeat match goal with
    | |- context [ ?f ?x :: map ?f ?l ] =>
      change (f x :: map f l) with (map f (x :: l))
    end.
    rewrite <- 2!map_app.
    revert ha.
    generalize (mfix1 ++ u :: mfix2). intro Δ.
    generalize (mfix1' ++ v :: mfix2'). intro Δ'.
    intro ha.
    rewrite !app_context_assoc.
    revert hx ha.
    generalize (Γ ,,, stack_context π').
    generalize (Γ ,,, stack_context π).
    clear Γ. intros Γ Γ' hx ha.
    assert (h :
      All2
        (fun d d' => (Σ ;;; Γ ⊢ d.2 = d'.2) * eq_binder_annot d.1 d'.1)
        (map def_sig Δ) (map def_sig Δ')
    ).
    { apply All2_map. eapply All2_impl. 1: eassumption.
      intros [na ty bo ra] [na' ty' bo' ra'] [? [? ?]].
      specialize (w _ wfΣ). simpl in *. split; tas.
    }
    clear ha.
    revert h.
    generalize (map def_sig Δ). clear Δ. intro Δ.
    generalize (map def_sig Δ'). clear Δ'. intro Δ'.
    intro h.
    unfold fix_context_alt.
    match goal with
    | |- ws_cumul_ctx_pb _ _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') =>
      assert (hi :
        All2i (fun i d d' =>
          forall Ξ,
            is_closed_context (Γ ,,, Ξ) ->
            #|Ξ| = i ->
            ws_cumul_decls Conv Σ (Γ ,,, Ξ) d d'
        ) 0 l l'
      )
    end.
    { eapply All2i_mapi.
      generalize 0 at 3. intro n.
      induction h in n |- *. 1: constructor.
      constructor. 2: eapply IHh.
      destruct r.
      intros Ξ cl eΞ. constructor; tas.
      rewrite <- eΞ.
      eapply @weakening_ws_cumul_pb with (Γ' := []). all: try assumption.

    }
    clear h.
    revert hi.
    match goal with
    | |- context [ ws_cumul_ctx_pb _ _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') ] =>
      generalize l' ;
      generalize l
    end.
    clear Δ Δ'. intros Δ Δ' h.
    apply All2i_rev in h. simpl in h.
    revert h.
    rewrite <- (List.length_rev Δ).
    generalize (List.rev Δ). clear Δ. intro Δ.
    generalize (List.rev Δ'). clear Δ'. intro Δ'.
    intro h.
    set (ln := #|Δ|) in *.
    set (m := 0) in *.
    assert (e : ln - m = #|Δ|) by lia.
    clearbody ln m.
    induction h.
    - eauto.
    - simpl in *.
      forward IHh by lia.
      constructor.
      + eapply IHh.
      + eapply r0. 2:lia.
        clear - wΣ IHh. fvs.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2], ha as [ha].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2. (* simpl in h2. *)
    constructor.
    apply All2_app.
    - eapply All2_impl. 1: exact h1.
      simpl. intros [? ? ? ?] [? ? ? ?] hh.
      simpl in *.
      rewrite map_app. simpl.
      rewrite <- !app_assoc. simpl.
      assumption.
    - constructor. 2: constructor.
      rewrite map_app. simpl.
      rewrite <- !app_assoc. simpl.
      destruct u as [na ty bo ra], v as [na' ty' bo' ra']. simpl in *.
      unfold def_sig at 2. simpl.
      destruct fk.
      + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.
       + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct ha as [ha].
    constructor.
    rewrite <- !app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    clear aux.
    eapply R_irrelevance; tea; cbn.
    now rewrite <- !app_assoc.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2], h3 as [h3].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2. simpl in h2.
    constructor.
    constructor.
    - destruct u as [na ty bo ra], v as [na' ty' bo' ra']. simpl in *.
      unfold def_sig at 2. simpl.
      destruct fk.
      + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.
      + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.

    - eapply All2_impl. 1: exact h3.
      simpl. intros [? ? ? ?] [? ? ? ?] hh.
      simpl in *.
      rewrite map_app in hh. simpl in hh.
      rewrite <- !app_assoc in hh. simpl in hh.
      assumption.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    apply h''; clear h''.
    destruct H as [H]; inversion H; constructor.
    rewrite map_app -app_assoc; simpl; assumption.
  Qed.
  Next Obligation.
    apply h''; clear h''.
    destruct H as [H]; inversion H; constructor.
    destruct fk; cbn -[app_context].
    all: rewrite app_context_assoc; apply X0; eauto.
  Qed.

  Equations isws_cumul_pb_Fix (fk : fix_kind) (Γ : context)
    (mfix : mfixpoint term) (idx : nat) (π : stack)
    (h : wtp Γ (mFix fk mfix idx) π)
    (mfix' : mfixpoint term) (idx' : nat) (π' : stack)
    (h' : wtp Γ (mFix fk mfix' idx') π')
    (hx : conv_stack_ctx Γ π π')
    (ei : idx = idx')
    (aux : Aux Term Γ (mFix fk mfix idx) π (mFix fk mfix' idx') π' h')
    : ConversionResult (∥ All2 (fun u v =>
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context mfix ⊢ u.(dbody) = v.(dbody)) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix' ∥) :=

      isws_cumul_pb_Fix fk Γ mfix idx π h mfix' idx' π' h' hx ei aux
    with
      isws_cumul_pb_fix_types fk Γ idx
        [] mfix π _
        [] mfix' π' _
        hx _ (expand aux)
    := {
    | Success h1
      with
        isws_cumul_pb_fix_bodies fk Γ idx
          [] mfix π _
          [] mfix' π' _
          hx _ _ (expand aux)
      := {
      | Success h2 := yes ;
      | Error e h'' := no e
      } ;
    | Error e h'' := no e
    }.

  Next Obligation.
    destruct h1 as [h1], h2 as [h2].
    constructor.
    rewrite fix_context_fix_context_alt.
    pose proof (All2_mix h1 h2) as h3.
    eapply All2_impl. 1: exact h3.
    intros [? ? ? ?] [? ? ? ?] ?. simpl in *.
    intuition eauto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h''; clear h''.
    destruct H as [H]; constructor.
    apply (All2_impl H).
    rewrite <- fix_context_fix_context_alt. intuition.
  Qed.
  Next Obligation.
    (* Contrapositive of pre-previous obligation *)
    apply h''; clear h''.
    destruct H as [H]; constructor; apply (All2_impl H).
    intuition.
  Qed.

  Lemma invert_type_mkApps_tProd Σ (wfΣ : abstract_env_ext_rel X Σ) Γ na A b args T :
    Σ;;; Γ |- mkApps (tProd na A b) args : T -> args = [].
  Proof using Type.
    intros typ.
    destruct (hΣ _ wfΣ).
    apply PCUICValidity.inversion_mkApps in typ as (?&[typ_prod typ_args]).
    apply inversion_Prod in typ_prod as (?&?&h1&?&?); [|easy].
    eapply PCUICSpine.typing_spine_strengthen in typ_args; eauto.
    2:{ eapply PCUICArities.isType_Sort. 2:pcuic.
        eapply unlift_TypUniv in h1.
        eapply wf_sort_product; now eapply typing_wf_sort. }
    clear -typ_args.
    depelim typ_args.
    - easy.
    - now apply ws_cumul_pb_Sort_Prod_inv in w.
  Qed.

  Lemma welltyped_zipc_tProd_appstack_nil Σ (wfΣ : abstract_env_ext_rel X Σ) {Γ na A B l ρ} :
    welltyped Σ Γ (zipc (tProd na A B) (appstack l ρ)) -> l = [].
  Proof using Type.
    pose proof (hΣ _ wfΣ) as [hΣ].
    intros wh.
    rewrite zipc_appstack in wh.
    zip fold in wh.
    apply welltyped_context in wh; [|easy].
    cbn in wh.
    destruct l as [|? ? _] using List.rev_ind; [easy|].
    rewrite mkApps_app in wh.
    cbn in wh. destruct wh as (?&typ); auto.
    change (tApp ?h ?a) with (mkApps h [a]) in typ.
    rewrite <-mkApps_app in typ.
    now apply invert_type_mkApps_tProd in typ.
  Qed.

  Definition compare_global_instance_correct {Σ}
    (wfΣ : abstract_env_ext_rel X Σ) pb ref n l l' :
      wf_instance Σ l ->
      wf_instance Σ l' ->
      cmp_global_instance Σ (compare_universe Σ) pb ref n l l' <->
      abstract_env_compare_global_instance pb ref n l l'.
  Proof.
    intros hl hl'. apply reflect_iff. eapply reflect_cmp_global_instance; eauto.
    all: try rewrite -> wf_universeb_instance_forall.
    - intros ? ? Hu Hu'; apply iff_reflect; apply (abstract_env_compare_universe_correct _ wfΣ).
      all: now apply wf_universe_iff.
    - intros ? ? Hu Hu'; apply iff_reflect; apply (abstract_env_compare_universe_correct _ wfΣ).
      all: now apply wf_universe_iff.
    - intros; now eapply abstract_env_lookup_correct'.
    - revert hl. apply reflect_iff, wf_instanceP.
    - revert hl'. apply reflect_iff, wf_instanceP.
  Qed.

  Lemma cmpb_term_correct Σ (wfΣ : abstract_env_ext_rel X Σ) pb napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    cmpb_term_napp pb napp t u <~>
    compare_term_napp Σ Σ pb napp t u.
  Proof.
    intros ht hu.
    eassert _ as H.
    2: split; [eapply elimT|eapply introT]; apply H.
    eapply reflect_eq_term_upto_univ; tea.
    1,2: intros ????; apply iff_reflect, abstract_env_compare_universe_correct; tea; now apply wf_universe_iff.
    1,2: intros ????; apply iff_reflect, abstract_env_compare_sort_correct; tea; now apply wf_sort_iff.
    1,2: intros ??????; apply iff_reflect, compare_global_instance_correct; tea.
    all: rewrite -> wf_universeb_instance_forall in *; now eapply wf_instance_iff.
  Qed.

  Lemma reduced_case_discriminee_whne Σ (wfΣ : abstract_env_ext_rel X Σ) Γ π ci p c brs h :
    eqb_term (reduce_term
                RedFlags.default
                _ X (Γ,,, stack_context π) c h) c = true ->
    isred_full Γ (tCase ci p c brs) π ->
    ∥whne RedFlags.default Σ (Γ,,, stack_context π) c∥.
  Proof using Type.
    intros eq ir. pose proof (heΣ _ wfΣ) as [[]].
    pose proof (hΣ _ wfΣ).
    edestruct ir as (_&[wh]); eauto.
    eapply cmpb_term_correct in eq; tea.
    - epose proof (reduce_term_complete _ _ _ _ _ _ _ h) as [wh'].
      eapply whnf_eq_term in eq; [|exact wh'].
      rewrite zipp_as_mkApps in wh.
      depelim wh; solve_discr.
      apply whne_mkApps_inv in w as [|(?&?&?&?&?&?&?&?)]; [|easy|easy].
      depelim w; cbn in *; try easy; solve_discr.
      apply whnf_whne_nodelta_upgrade in eq; auto using sq.
    - pose proof (reduce_term_sound RedFlags.default X_type X (Γ,,, stack_context π) c h) as Hreduce.
      specialize_Σ wfΣ. pose proof (h _ wfΣ) as [C hc]. sq.
      apply closed_red_red in Hreduce. eapply PCUICSR.subject_reduction in hc; eauto.
      Opaque reduce_term.
      eapply typing_wf_universes in hc as [? ?]%andb_and; eauto.
    - clear eq. specialize_Σ wfΣ. sq. destruct h as [? h].
      eapply typing_wf_universes in h as [h h']%andb_and; eauto.
    Unshelve. all:eauto.
  Qed.

  Lemma welltyped_zipp_inv Σ Γ t π :
    wf Σ ->  welltyped Σ Γ (zipp t π) -> welltyped Σ Γ t.
  Proof using Type.
    induction π; cbn; auto.
    unfold zipp.
    destruct decompose_stack.
    intros ? [s' Hs].
    eapply PCUICValidity.inversion_mkApps in Hs as [? []].
    now exists x.
  Qed.

  Lemma welltyped_zipc_inv Σ Γ t π : wf Σ -> welltyped Σ Γ (zipc t π) -> welltyped Σ (Γ,,, stack_context π) t.
  Proof using Type.
    intros ? Ht. apply welltyped_zipc_zipp in Ht; eauto.
    apply welltyped_zipp_inv in Ht; eauto.
  Defined.

  Lemma welltyped_wf Σ Γ t : wf Σ -> welltyped Σ Γ t -> wf_universes Σ t.
  Proof using Type.
    intros ? [? Ht]. apply typing_wf_universes in Ht; eauto.
    cbn in Ht. rtoProp; intuition.
  Qed.

  Lemma inv_reduced_discriminees_case Σ (wfΣ : abstract_env_ext_rel X Σ) leq Γ π π' ci ci' p p' c c' brs brs' h h' :
    conv_stack_ctx Γ π π' ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       _ X (Γ,,, stack_context π) c h) c ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       _ X (Γ,,, stack_context π') c' h') c' ->
    welltyped Σ Γ (zipc (tCase ci p c brs) π) ->
    welltyped Σ Γ (zipc (tCase ci' p' c' brs') π') ->
    isred_full Γ (tCase ci p c brs) π ->
    isred_full Γ (tCase ci' p' c' brs') π' ->
    conv_cum
      leq Σ (Γ,,, stack_context π)
      (zipp (tCase ci p c brs) π)
      (zipp (tCase ci' p' c' brs') π') ->
    ∥[× ci = ci',
     ws_cumul_pb_predicate Σ (Γ,,, stack_context π) p p',
     Σ;;; Γ,,, stack_context π ⊢ c = c',
     ws_cumul_pb_brs Σ (Γ,,, stack_context π) p brs brs' &
     ws_cumul_pb_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1]∥.
  Proof using Type.
    eintros [] c_is_red%eq_sym c'_is_red%eq_sym wtc wtc' isr1 isr2 cc; eauto.
    eapply reduced_case_discriminee_whne in c_is_red as wh1; eauto.
    eapply reduced_case_discriminee_whne in c'_is_red as wh2; eauto.
    destruct (hΣ _ wfΣ) as [hΣ], wh1 as [wh1], wh2 as [wh2].
    rewrite !zipp_as_mkApps in cc.
    eapply whne_conv_context in wh2.
    2:{ symmetry in X0. eapply ws_cumul_ctx_pb_forget in X0. exact X0. }
    apply conv_cum_mkApps_inv in cc as [(ws_cumul_pb_Case&conv_args)]; eauto using whnf_mkApps.
    red in isr1.
    eapply welltyped_zipc_zipp, welltyped_zipp_inv in wtc; eauto.
    eapply welltyped_zipc_zipp, welltyped_zipp_inv in wtc'; eauto.
    destruct wtc. eapply inversion_Case in X1 as [mdecl [idecl [isdecl [indices [[] ?]]]]]; tea.
    destruct wtc'. eapply inversion_Case in X1 as [mdecl' [idecl' [isdecl' [indices' [[] ?]]]]] ; tea; eauto.
    eapply conv_cum_tCase_inv in ws_cumul_pb_Case; eauto.
    destruct ws_cumul_pb_Case as [[<- ? ? ?]].
    split; split; auto.
  Qed.

  Lemma reduced_proj_body_whne Σ (wfΣ : abstract_env_ext_rel X Σ) Γ π p c h :
    true = eqb_term (reduce_term
                RedFlags.default
                _ X (Γ,,, stack_context π) c h) c ->
    isred_full Γ (tProj p c) π ->
    ∥whne RedFlags.default Σ (Γ,,, stack_context π) c∥.
  Proof using Type.
    intros eq%eq_sym ir.
    edestruct ir as (_&[wh]); eauto.
    pose proof (hΣ _ wfΣ).
    eapply cmpb_term_correct in eq; tea.
    - epose proof (reduce_term_complete _ _ _ _ _ _ _ h) as [wh'].
      eapply whnf_eq_term in eq; [|exact wh'].
      rewrite zipp_as_mkApps in wh.
      depelim wh; solve_discr.
      apply whne_mkApps_inv in w as [|(?&?&?&?&?&?&?&?)]; [|easy|easy].
      depelim w; cbn in *; try easy; solve_discr.
      apply whnf_whne_nodelta_upgrade in eq; auto using sq.
    - pose proof (reduce_term_sound RedFlags.default X_type X (Γ,,, stack_context π) c h) as Hreduce.
      specialize_Σ wfΣ. pose proof (h _ wfΣ) as [C hc]. sq.
      apply closed_red_red in Hreduce. eapply PCUICSR.subject_reduction in hc; eauto.
      Opaque reduce_term.
      eapply typing_wf_universes in hc as [? ?]%andb_and; eauto.
    - clear eq. specialize_Σ wfΣ. sq. destruct h as [? h].
    eapply typing_wf_universes in h as [h h']%andb_and; eauto.
    Unshelve. all:eauto.
  Qed.

  Lemma inv_reduced_body_proj Σ (wfΣ : abstract_env_ext_rel X Σ) leq Γ π π' p p' c c' h h' :
    conv_stack_ctx Γ π π' ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       _ X (Γ,,, stack_context π) c h) c ->
    true = eqb_term (reduce_term
                       RedFlags.default
                      _ X (Γ,,, stack_context π') c' h') c' ->
    isred_full Γ (tProj p c) π ->
    isred_full Γ (tProj p' c') π' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tProj p c) π) (zipp (tProj p' c') π') ->
    ∥p = p' ×
     Σ;;; Γ,,, stack_context π ⊢ c = c' ×
     ws_cumul_pb_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof using Type.
    eintros [] c_is_red c'_is_red isr1 isr2 cc; eauto.
    eapply reduced_proj_body_whne in c_is_red as wh1; eauto.
    eapply reduced_proj_body_whne in c'_is_red as wh2; eauto.
    destruct (hΣ _ wfΣ) as [hΣ], wh1 as [wh1], wh2 as [wh2].
    rewrite !zipp_as_mkApps in cc.
    eapply whne_conv_context in wh2.
    2:{ symmetry in X0. eapply ws_cumul_ctx_pb_forget in X0. exact X0. }
    apply conv_cum_mkApps_inv in cc as [(conv_proj&conv_args)]; eauto using whnf_mkApps.
    eapply conv_cum_tProj_inv in conv_proj; eauto.
    destruct conv_proj as [(<-&?)].
    constructor; auto.
  Qed.

  Lemma conv_cum_red_conv_inv Σ (wfΣ : abstract_env_ext_rel X Σ) leq Γ Γ' t1 t2 t1' t2' :
    ws_cumul_ctx_pb Conv Σ Γ Γ' ->
    red Σ Γ t1 t1' ->
    red Σ Γ' t2 t2' ->
    sq_ws_cumul_pb leq Σ Γ t1 t2 ->
    sq_ws_cumul_pb leq Σ Γ t1' t2'.
  Proof using Type.
    intros. destruct (hΣ _ wfΣ) as [wΣ].
    eapply conv_cum_red_conv_inv; eauto.
    all:eapply into_closed_red; tea.
    * fvs.
    * destruct H; fvs.
    * fvs.
    * destruct H. rewrite <-(All2_fold_length X0). now eapply ws_cumul_pb_is_open_term_right.
  Qed.

  Lemma inv_stuck_fixes Σ (wfΣ : abstract_env_ext_rel X Σ) leq Γ mfix idx π mfix' idx' π' h h' :
    conv_stack_ctx Γ π π' ->
    None = unfold_one_fix Γ mfix idx π h ->
    None = unfold_one_fix Γ mfix' idx' π' h' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp (tFix mfix' idx') π') ->
    ∥[× idx = idx',
     All2 (fun d d' =>
             rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
             Σ;;; Γ,,, stack_context π ⊢ dtype d = dtype d' ×
             Σ;;; Γ,,, stack_context π,,, fix_context mfix ⊢ dbody d = dbody d')
          mfix mfix' &
     ws_cumul_pb_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1]∥.
  Proof using Type.
    eintros [?] uf1 uf2 cc; eauto.
    rewrite !zipp_as_mkApps in cc; eauto.
    apply unfold_one_fix_None in uf1.
    edestruct uf1 as [(?&?&?)]; eauto.
    apply unfold_one_fix_None in uf2.
    edestruct uf2 as [(?&?&?)]; eauto.
    destruct (hΣ _ wfΣ).
    eapply conv_cum_red_conv_inv in cc.
    2: eassumption.
    2: exact X0.
    2: eapply red_mkApps; [reflexivity|exact a].
    2: apply red_mkApps; [reflexivity|exact a0].
    apply conv_cum_mkApps_inv in cc as [(ws_cumul_pb_Fix&conv_args)]; auto.
    2:{ eapply whnf_conv_context; eauto.
        symmetry in X0. now eapply ws_cumul_ctx_pb_forget in X0. }
    apply conv_cum_tFix_inv in ws_cumul_pb_Fix as [(<-&?)]; auto.
    sq; split; auto.
    * eapply All2_impl; tea; cbn. intros ? ? []. repeat split; auto.
    * eapply ws_cumul_pb_terms_red_conv; eauto.
      all:eapply into_red_terms; tea.
      1,3:fvs.
      + specialize_Σ wfΣ. eapply welltyped_zipc_zipp in h; auto.
        destruct h as [s h].
        rewrite zipp_as_mkApps in h.
        eapply subject_is_open_term in h.
        rewrite on_free_vars_mkApps in h. now apply andb_true_iff in h.
      + specialize_Σ wfΣ. eapply welltyped_zipc_zipp in h'; auto.
        destruct h' as [s h'].
        rewrite zipp_as_mkApps in h'.
        eapply subject_is_open_term in h'.
        rewrite on_free_vars_mkApps in h'. now apply andb_true_iff in h'.
  Qed.

  Lemma inv_stuck_cofixes Σ (wfΣ : abstract_env_ext_rel X Σ) leq Γ mfix idx π mfix' idx' π' :
    conv_stack_ctx Γ π π' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tCoFix mfix idx) π) (zipp (tCoFix mfix' idx') π') ->
    ∥idx = idx' ×
     All2 (fun d d' =>
             rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
             Σ;;; Γ,,, stack_context π ⊢ dtype d = dtype d' ×
             Σ;;; Γ,,, stack_context π,,, fix_context mfix ⊢ dbody d = dbody d')
          mfix mfix' ×
     ws_cumul_pb_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof using Type.
    eintros [?] cc; eauto. specialize_Σ wfΣ.
    rewrite !zipp_as_mkApps in cc.
    destruct (hΣ _ wfΣ).
    apply conv_cum_mkApps_inv in cc as [(ws_cumul_pb_CoFix&conv_args)]; auto.
    apply conv_cum_tCoFix_inv in ws_cumul_pb_CoFix as [(<-&?)]; auto.
    constructor; split; [|split]; auto.
    eapply All2_impl; tea. intros ? ? []. repeat split; auto.
  Qed.

  Equations (noeqns) isconv_predicate_params_aux
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2)
            (pre1 pre2 post1 post2 : list term)
            (eq1 : p1.(pparams) = pre1 ++ post1)
            (eq2 : p2.(pparams) = pre2 ++ post2) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π1) post1 post2∥) :=
    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2
      hx aux pre1 pre2 [] [] eq1 eq2 => yes;

    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2
      hx aux pre1 pre2 (t1 :: post1) (t2 :: post2) eq1 eq2
      with isconv_red_raw
           Conv
           t1 (Case_pred
                 ci1
                 (pred_hole_params pre1 post1 p1.(puinst) p1.(pcontext) p1.(preturn))
                 c1 brs1 :: π1)
           t2 (Case_pred
                 ci2
                 (pred_hole_params pre2 post2 p2.(puinst) p2.(pcontext) p2.(preturn))
                 c2 brs2 :: π2) aux := {

      | Error ce not_conv_term => no ce;

      | Success conv_tm
          with isconv_predicate_params_aux
               Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux
               (pre1 ++ [t1]) (pre2 ++ [t2]) post1 post2 _ _ := {

        | Error ce not_conv_rest => no ce;

        | Success conv_rest => yes
        }
      };

    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux
      pre1 pre2 post1 post2 eq eq2 => no (CasePredParamsUnequalLength
                                            (Γ,,, stack_context π1) ci1 p1 c1 brs1
                                            (Γ,,, stack_context π2) ci2 p2 c2 brs2).
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    destruct H as [H].
    depelim H.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    destruct H as [H].
    depelim H.
  Qed.
  Next Obligation.
    destruct p1; auto.
  Qed.
  Next Obligation.
    destruct p2; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct p1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    specialize_Σ wfΣ.
    destruct conv_tm, conv_rest.
    unfold zipp in X; simpl in *.
    constructor; constructor; auto.
  Qed.
  Next Obligation.
    contradiction not_conv_rest. intros.
    specialize_Σ wfΣ.
    destruct H as [H]; depelim H.
    constructor; auto.
  Qed.
  Next Obligation.
    contradiction not_conv_term. intros Σ wfΣ.
    specialize_Σ wfΣ.
    destruct H as [H]; depelim H.
    constructor; auto.
  Qed.

  Lemma case_conv_preds_inv Σ (wfΣ : abstract_env_ext_rel X Σ) {Γ ci p c brs brs' π}
  (h : wtp Γ (tCase ci p c brs) π)
  (p' : predicate term) (c' : term)
  (π' : stack) (h' : wtp Γ (tCase ci p' c' brs') π')
  (hx : conv_stack_ctx Γ π π')
  (hp : ∥ ws_cumul_pb_terms Σ (Γ,,, stack_context π) (pparams p) (pparams p') ∥) :
  ∥ ∑ mdecl idecl,
    [× declared_inductive Σ ci mdecl idecl,
      forallb (wf_universeb Σ) (map Universe.make' (puinst p)),
      forallb (wf_universeb Σ) (map Universe.make' (puinst p')),
       #|pparams p| = ind_npars mdecl,
       #|pparams p'| = ind_npars mdecl,
       eq_context_upto_names p.(pcontext) p'.(pcontext),
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p| p.(pcontext) &
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p'| p'.(pcontext)] ∥.
  Proof using Type.
    destruct (hΣ _ wfΣ). specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct hp as [hp].
    eapply welltyped_zipc_zipp in h; auto.
    eapply welltyped_zipc_zipp in h'; auto.
    rewrite !zipp_as_mkApps in h, h'.
    destruct h as [s h]. destruct h' as [s' h'].
    eapply PCUICValidity.inversion_mkApps in h as [A [hcase _]].
    eapply PCUICValidity.inversion_mkApps in h' as [A' [hcase' _]].
    eapply inversion_Case in hcase as [mdecl [idecl [decli [indices [hcase _]]]]]; auto.
    eapply inversion_Case in hcase' as [mdecl' [idecl' [decli' [indices' [hcase' _]]]]]; auto.
    pose proof (decli_ := decli); pose proof (decli'_ := decli').
    unshelve eapply declared_inductive_to_gen in decli, decli'; eauto.
    destruct (declared_inductive_inj decli decli'). subst mdecl' idecl'.
    constructor.
    assert (clp : test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
      #|pparams p| p.(pcontext)).
    { rewrite test_context_k_closed_on_free_vars_ctx.
      destruct hcase.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact conv_pctx.
      rewrite <- closedn_ctx_on_free_vars.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (closed_ind_predicate_context); tea.
        eapply declared_minductive_closed; tea. exact decli'_. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
    }
    rewrite test_context_k_closed_on_free_vars_ctx.
    exists mdecl, idecl.
    destruct hcase. destruct hcase'.
    split; tea.
    - eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
      intros; apply wf_universe_iff; eauto.
    - eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
      intros; apply wf_universe_iff; eauto.
    - eapply (wf_predicate_length_pars wf_pred).
    - eapply (wf_predicate_length_pars wf_pred0).
    - etransitivity; tea.
      now symmetry.
    - now rewrite <- test_context_k_closed_on_free_vars_ctx.
    - rewrite test_context_k_closed_on_free_vars_ctx.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact conv_pctx0.
      rewrite <- closedn_ctx_on_free_vars.
      relativize #|pparams p'|.
      { eapply (closed_ind_predicate_context); tea.
        eapply declared_minductive_closed; tea. exact decli'_. }
      rewrite (wf_predicate_length_pars wf_pred0).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
  Qed.

  Definition forallb2_proper A B (R R' : A -> B -> bool) l l':
    (forall a b, R a b = R' a b) ->
    forallb2 R l l' =
    forallb2 R' l l'.
  Proof using Type.
    intro e. revert l'.
    induction l; destruct l'; eauto.
    cbn; intros. rewrite <- e.
    apply eq_true_iff_eq. split; intros.
     all: apply andb_and; now apply andb_and in H.
  Qed.

  Definition isconv_predicate_params
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2) :=
    isconv_predicate_params_aux Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux [] []
                                p1.(pparams) p2.(pparams) eq_refl eq_refl.

  Equations (noeqns) isconv_predicate
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (eqci : ci1 = ci2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2)
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_predicate Σ (Γ,,, stack_context π1) p1 p2∥) :=

    isconv_predicate Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx eqci aux
      with isconv_predicate_params
           Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux := {

      | Error ce not_conv_params => no ce;

      | Success conv_params
        with inspect (eqb_universe_instance p1.(puinst) p2.(puinst)) := {

        | exist false not_eq_insts => no (CasePredUnequalUniverseInstances
                                            (Γ,,, stack_context π1) ci1 p1 c1 brs1
                                            (Γ,,, stack_context π2) ci2 p2 c2 brs2);

        | exist true eq_insts
            with isconv_red_raw
                 Conv p1.(preturn)
                      (Case_pred ci1 (pred_hole_return p1.(pparams) p1.(puinst) p1.(pcontext))
                                 c1 brs1 :: π1)
                      p2.(preturn)
                      (Case_pred ci2 (pred_hole_return p2.(pparams) p2.(puinst) p2.(pcontext))
                                 c2 brs2 :: π2)
                      aux := {

            | Error ce not_conv_ret => no ce;

            | Success conv_ret => yes
          }
        }
      }.
  Next Obligation.
    destruct p1; cbn in *; subst; auto.
  Qed.
  Next Obligation.
    destruct p2; cbn in *; subst; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct p1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ).
    eapply eq_sym, eqb_universe_instance_spec in eq_insts; eauto.
    - destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params _ wfΣ)) as []; tea.
      specialize_Σ wfΣ.    destruct hx as [hx].
    destruct conv_params as [conv_params].
    constructor.
    unfold app_context; rewrite <- !app_assoc.
    destruct X1 as [mdecl [idecl []]].
    etransitivity.
    * inv_on_free_vars. eapply (inst_case_ws_cumul_ctx_pb d e e0 i1 i2); tea. fvs.
    * eapply ws_cumul_ctx_pb_app_same. 2:eapply hx.
      rewrite on_free_vars_ctx_app.
      apply andb_true_iff. split; auto.
      1:now eapply ws_cumul_ctx_pb_closed_left in hx.
      eapply on_free_vars_ctx_inst_case_context; trea.
      fvs.
     - destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params Σ wfΣ)) as []; tea.
       destruct X1 as [mdecl [idecl []]]. eauto.
     - destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params Σ wfΣ)) as []; tea.
       destruct X1 as [mdecl [idecl []]]. eauto.
  Qed.
  Next Obligation.
    unfold zipp in conv_ret; simpl in conv_ret.
    destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params Σ wfΣ)) as []; tea.
    eapply eq_sym, eqb_universe_instance_spec in eq_insts; eauto.
    - specialize_Σ wfΣ. destruct hx as [hx]. destruct conv_params as [conv_params].
    destruct conv_ret as [h].
    split. split; auto.
    2:rewrite app_context_assoc in h; auto.
    now destruct X0 as [mdecl [idecl []]].
    - now destruct X0 as [mdecl [idecl []]].
    - now destruct X0 as [mdecl [idecl []]].
  Qed.
  Next Obligation.
    unfold zipp in not_conv_ret; simpl in not_conv_ret.
    contradiction not_conv_ret.
    rewrite app_context_assoc. intros Σ wfΣ. specialize_Σ wfΣ.
    destruct H as [[]]; constructor; auto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ).
    zip fold in h1.
    eapply welltyped_context in h1 as (?&typ1); eauto.
    eapply inversion_Case in typ1 as (?&?&?&?&[]&?); auto.
    zip fold in h2.
    clear aux.
    eapply welltyped_context in h2 as (?&typ2); eauto.
    apply inversion_Case in typ2 as (?&?&?&?&[]&?); auto.
    apply consistent_instance_ext_wf in cons.
    apply consistent_instance_ext_wf in cons0.
    specialize_Σ wfΣ; destruct H as [[]].
    apply eqb_universe_instance_complete in c; eauto.
    congruence.
  Qed.
  Next Obligation.
    contradiction not_conv_params. intros Σ wfΣ.
    specialize_Σ wfΣ.
    destruct H as [[]]; constructor; auto.
  Qed.

Notation tPrimArray a := (tPrim (primArray; primArrayModel a)).

Equations (noeqns) isconv_array_values_aux
            (Γ : context)
            (a1 : array_model term)
            (π1 : stack)
            (h1 : wtp Γ (tPrimArray a1) π1)
            (a2 : array_model term)
            (π2 : stack)
            (h2 : wtp Γ (tPrimArray a2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tPrimArray a1) π1 (tPrimArray a2) π2 h2)
            (pre1 pre2 post1 post2 : list term)
            (eq1 : a1.(array_value) = pre1 ++ post1)
            (eq2 : a2.(array_value) = pre2 ++ post2) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π1) post1 post2∥) :=
    isconv_array_values_aux
      Γ a1 π1 h1 a2 π2 h2
      hx aux pre1 pre2 [] [] eq1 eq2 => yes;

    isconv_array_values_aux
      Γ a1 π1 h1 a2 π2 h2
      hx aux pre1 pre2 (t1 :: post1) (t2 :: post2) eq1 eq2
      with isconv_red_raw
           Conv
           t1 (PrimArray_val a1.(array_level)
                pre1 post1
                a1.(array_default) a1.(array_type) :: π1)
           t2 (PrimArray_val a2.(array_level)
                pre2 post2
                a2.(array_default) a2.(array_type) :: π2) aux := {

      | Error ce not_conv_term => no ce;

      | Success conv_tm
          with isconv_array_values_aux
               Γ a1 π1 h1 a2 π2 h2 hx aux
               (pre1 ++ [t1]) (pre2 ++ [t2]) post1 post2 _ _ := {

        | Error ce not_conv_rest => no ce;

        | Success conv_rest => yes
        }
      };

    isconv_array_values_aux
      Γ a1 π1 h1 a2 π2 h2 hx aux
      pre1 pre2 post1 post2 eq eq2 => no (ArrayValuesNotSameLength
                                            (Γ,,, stack_context π1) a1
                                            (Γ,,, stack_context π2) a2).
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    destruct H as [H].
    depelim H.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    destruct H as [H].
    depelim H.
  Qed.
  Next Obligation.
    destruct a1; auto.
  Qed.
  Next Obligation.
    destruct a2; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct a1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    specialize_Σ wfΣ.
    destruct conv_tm, conv_rest.
    unfold zipp in X; simpl in *.
    constructor; constructor; auto.
  Qed.
  Next Obligation.
    contradiction not_conv_rest. intros.
    specialize_Σ wfΣ.
    destruct H as [H]; depelim H.
    constructor; auto.
  Qed.
  Next Obligation.
    contradiction not_conv_term. intros Σ wfΣ.
    specialize_Σ wfΣ.
    destruct H as [H]; depelim H.
    constructor; auto.
  Qed.

  Definition isconv_array_values
    (Γ : context)
    (a1 : array_model term)
    (π1 : stack)
    (h1 : wtp Γ (tPrimArray a1) π1)
    (a2 : array_model term)
    (π2 : stack)
    (h2 : wtp Γ (tPrimArray a2) π2)
    (hx : conv_stack_ctx Γ π1 π2)
    (aux : Aux Term Γ (tPrimArray a1) π1 (tPrimArray a2) π2 h2) :=
    isconv_array_values_aux Γ a1 π1 h1 a2 π2 h2 hx aux [] [] a1.(array_value) a2.(array_value) eq_refl eq_refl.

  Lemma conv_cum_red_inv Σ (wfΣ : abstract_env_ext_rel X Σ) leq Γ t1 t2 t1' t2' :
    red Σ Γ t1 t1' ->
    red Σ Γ t2 t2' ->
    sq_ws_cumul_pb leq Σ Γ t1 t2 ->
    sq_ws_cumul_pb leq Σ Γ t1' t2'.
  Proof using Type.
    intros. destruct (hΣ _ wfΣ).
    destruct H. eapply conv_cum_red_inv; tea. 3:split; eauto.
    all:eapply into_closed_red; tea; fvs.
  Qed.



  (* See https://github.com/coq/coq/blob/master/kernel/reduction.ml#L367 *)
  Opaque reduce_stack.
  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (ir1 : isred_full Γ t1 π1) (ir2 : isred_full Γ t2 π2)
            (aux : Aux Term Γ t1 π1 t2 π2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=

    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 hx ir1 ir2 aux with prog_viewc t1 t2 := {
    | prog_view_App _ _ _ _ := False_rect _ _;

    | prog_view_Const c u c' u' with eq_dec c c' := {
      | left eq1 with inspect (eqb_universe_instance u u') := {
        | @exist true eq2 with isconv_args_raw leq (tConst c u) π1 (tConst c' u') π2 aux := {
          | Success h := yes ;
          (* Unfold both constants at once *)
          | Error e h with inspect (abstract_env_lookup X c) := {
            | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq3 :=
              isconv_red leq (subst_instance u body) π1
                             (subst_instance u' body) π2 aux ;
            (* Inductive or not found *)
            | @exist _ _ := no (NotFoundConstant c)
            }
          } ;
        (* If universes are different, we unfold one of the constants *)
        | @exist false uneq_u := unfold_constants Γ leq c u π1 h1 c' u' π2 h2 _ hx aux
        } ;
      (* If the two constants are different, we unfold one of them *)
      | right uneq_c := unfold_constants Γ leq c u π1 h1 c' u' π2 h2 _ hx aux
      } ;

    | prog_view_Lambda na A1 t1 na' A2 t2
      with isconv_red_raw Conv A1 (Lambda_ty na t1 :: π1)
                               A2 (Lambda_ty na' t2 :: π2) aux := {
      | Success h with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red Conv
                     t1 (Lambda_bd na A1 :: π1)
                     t2 (Lambda_bd na' A2 :: π2) aux ;
        | exist false e :=
          no (
            LambdaNotConvertibleAnn
              (Γ ,,, stack_context π1) na A1 t1
              (Γ ,,, stack_context π2) na' A2 t2
          ) };
      | Error e h :=
        no (
          LambdaNotConvertibleTypes
            (Γ ,,, stack_context π1) na A1 t1
            (Γ ,,, stack_context π2) na' A2 t2 e
        )
      } ;

    | prog_view_Prod na A1 B1 na' A2 B2
      with isconv_red_raw Conv A1 (Prod_l na B1 :: π1) A2 (Prod_l na' B2 :: π2) aux := {
      | Success h  with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red leq
                   B1 (Prod_r na A1 :: π1)
                   B2 (Prod_r na' A2 :: π2) aux ;
        | exist false e :=
          no (
            ProdNotConvertibleAnn
              (Γ ,,, stack_context π1) na A1 B1
              (Γ ,,, stack_context π2) na' A2 B2
          ) };
      | Error e h :=
        no (
          ProdNotConvertibleDomains
            (Γ ,,, stack_context π1) na A1 B1
            (Γ ,,, stack_context π2) na' A2 B2 e
        )
      } ;

    | prog_view_Case ci p c brs ci' p' c' brs'
      with inspect (reduce_term RedFlags.default _ X (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq2 with inspect (reduce_term RedFlags.default _ X (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq3 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb ci ci') := {
              | @exist true eq5
                  with isconv_predicate Γ ci p c brs π1 _ ci' p' c' brs' π2 _ _ _ aux := {
                | Success convp with isconv_red_raw Conv
                                  c (Case_discr ci p brs :: π1)
                                  c' (Case_discr ci' p' brs' :: π2) aux := {
                  | Success convdiscr with isconv_branches' Γ ci p c brs π1 _ ci' p' c' brs' π2 _ _ _ _ aux := {
                    | Success convbrs with isconv_args_raw leq (tCase ci p c brs) π1 (tCase ci' p' c' brs') π2 aux := {
                      | Success convargs := yes ;
                      | Error e h := no e
                      } ;
                    | Error e h := no e
                    } ;
                  | Error e h := no e
                  } ;
                | Error e h := no e
                } ;
              | @exist false eq5 :=
                no (
                  CaseOnDifferentInd
                    (Γ ,,, stack_context π1) ci p c brs
                    (Γ ,,, stack_context π2) ci' p' c' brs'
                )
              } ;
            | @exist false eq4 :=
              isconv_red leq
                (tCase ci p c brs) π1
                (tCase ci' p' cred' brs') π2
                aux
            }
          } ;
        | @exist false eq3 :=
          isconv_red leq
            (tCase ci p cred brs) π1
            (tCase ci' p' c' brs') π2
            aux
        }
      } ;

    | prog_view_Proj p c p' c' with inspect (reduce_term RedFlags.default _ X (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq3 with inspect (reduce_term RedFlags.default _ X (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq2 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb p p') := {
              | @exist true eq5 with isconv_red_raw Conv c (Proj p :: π1) c' (Proj p' :: π2) aux := {
                | Success convdiscr := isconv_args leq (tProj p c) π1 (tProj p' c') π2 aux ;
                | Error e h := no e
                } ;
              | @exist false eq5 :=
                no (
                  DistinctStuckProj
                    (Γ ,,, stack_context π1) p c
                    (Γ ,,, stack_context π2) p' c'
                )
              } ;
            | @exist false eq4 :=
              isconv_red leq
                (tProj p c) π1
                (tProj p' cred') π2
                aux
          }
        } ;
        | @exist false eq3 :=
          isconv_red leq
            (tProj p cred) π1
            (tProj p' c') π2
            aux
      }
    } ;
    | prog_view_Fix mfix idx mfix' idx'
      with inspect (unfold_one_fix Γ mfix idx π1 _) := {
      | @exist (Some (fn, θ)) eq1 with inspect (decompose_stack θ) := {
        | @exist (l', θ') eq2
          with inspect (reduce_stack RedFlags.nodelta _ X (Γ ,,, stack_context θ') fn (appstack l' []) _) := {
          | @exist (fn', ρ) eq3 :=
            isconv_prog leq fn' (ρ ++ θ') (tFix mfix' idx') π2 aux
          }
        } ;
      | @exist None eee with inspect (unfold_one_fix Γ mfix' idx' π2 _) := {
        | @exist (Some (fn, θ)) eq1
          with inspect (decompose_stack θ) := {
          | @exist (l', θ') eq2
            with inspect (reduce_stack RedFlags.nodelta _ X (Γ ,,, stack_context θ') fn (appstack l' []) _) := {
            | @exist (fn', ρ) eq3 :=
              isconv_prog leq (tFix mfix idx) π1 fn' (ρ ++ θ') aux
            }
          } ;
        | @exist None eq1 with inspect (eqb idx idx') := {
          | @exist true eq4 with isws_cumul_pb_Fix IndFix Γ mfix idx π1 _ mfix' idx' π2 _ _ _ aux := {
            | Success convfix with isconv_args_raw leq (tFix mfix idx) π1 (tFix mfix' idx') π2 aux := {
              | Success convargs := yes ;
              | Error e h := no e
              } ;
            | Error e h := no e
            } ;
          | @exist false idx_uneq :=
            no (
              CannotUnfoldFix
                (Γ ,,, stack_context π1) mfix idx
                (Γ ,,, stack_context π2) mfix' idx'
            )
          }
        }
      } ;

    | prog_view_CoFix mfix idx mfix' idx'
      with inspect (eqb idx idx') := {
      | @exist true eq4 with isws_cumul_pb_Fix CoIndFix Γ mfix idx π1 _ mfix' idx' π2 _ _ _ aux := {
        | Success convfix with isconv_args_raw leq (tCoFix mfix idx) π1 (tCoFix mfix' idx') π2 aux := {
          | Success convargs := yes ;
          | Error e h := no e
          } ;
        | Error e h := no e
        } ;
      | @exist false idx_uneq :=
        no (
          DistinctCoFix
            (Γ ,,, stack_context π1) mfix idx
            (Γ ,,, stack_context π2) mfix' idx'
        )
      } ;

    | prog_view_Prim p p' with eq_dec (prim_val_tag p) (prim_val_tag p') := {
      | right tag_uneq := no (DistinctPrimTags (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p')
      | left eqtag with p, p' := {
        | (primInt; primIntModel i) | (primInt; primIntModel i') with inspect (eqb i i') :=
          { | @exist true eqi := yes
            | @exist false neqi := no (DistinctPrimValues (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p') }
        | (primFloat; primFloatModel f) | (primFloat; primFloatModel f') with inspect (eqb f f') :=
          { | @exist true eqf := yes
            | @exist false neqf := no (DistinctPrimValues (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p') }
        | (primString; primStringModel f) | (primString; primStringModel f') with inspect (eqb f f') :=
          { | @exist true eqf := yes
            | @exist false neqf := no (DistinctPrimValues (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p') }
        | (primArray; primArrayModel a) | (primArray; primArrayModel a')
          with inspect (abstract_env_compare_universe X Conv (Universe.make' (array_level a)) (Universe.make' (array_level a'))) :=
          { | @exist false neql := no (ArrayNotConvertibleLevels (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a')
            | @exist true eql with isconv_red_raw Conv (array_type a) (PrimArray_ty a.(array_level) a.(array_value) a.(array_default) :: π1)
                (array_type a') (PrimArray_ty a'.(array_level) a'.(array_value) a'.(array_default) :: π2) aux := {
              | Success convdiscrty with isconv_red_raw Conv (array_default a) (PrimArray_def a.(array_level) a.(array_value) a.(array_type) :: π1)
                  (array_default a') (PrimArray_def a'.(array_level) a'.(array_value) a'.(array_type) :: π2) aux := {
                | Success convdiscrdef with isconv_array_values Γ a π1 _ a' π2 _ hx aux := {
                  | Success convdiscrval := yes
                  | Error e h := no (ArrayNotConvertibleValues (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a' e)
                }
                | Error e h := no (ArrayNotConvertibleDefault (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a' e)
              } ;
            | Error e h := no (ArrayNotConvertibleTypes (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a' e)
            }
          }
        }
    } ;

    | prog_view_other t1 t2 h :=
      isconv_fallback leq t1 π1 t2 π2 aux
    }.

  (* tApp *)
  Next Obligation.
    destruct ir1 as [ha1 _]. discriminate ha1.
  Qed.

  (* tConst *)
  Next Obligation.
    eapply R_stateR. all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; destruct (hΣ _ wfΣ). clear aux.
    specialize_Σ wfΣ.
    apply conv_cum_zipp; auto.
    constructor. eapply ws_cumul_eq_pb.
    constructor. all:fvs.
    - destruct h. eapply welltyped_zipc_zipp in h1; auto. fvs.
    - constructor. eapply eqb_universe_instance_spec; eauto.
      + eapply welltyped_zipc_tConst_inv in h1 as (?&?&?); eauto;
        eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
        intros; apply wf_universe_iff; eauto.
      + eapply welltyped_zipc_tConst_inv in h2 as (?&?&?); eauto;
        eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
        intros; apply wf_universe_iff; eauto.
  Qed.
  Next Obligation.
    pose (heΣ _ wfΣ). specialize_Σ wfΣ. sq.
    eapply red_welltyped ; [auto|..].
    - exact h1.
    - eapply red_zipc.
      eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    pose (heΣ _ wfΣ). clear aux. specialize_Σ wfΣ. sq.
    eapply red_welltyped ; [auto|..].
    - exact h2.
    - eapply red_zipc.
      eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros.
    eapply cored_zipc.
    eapply cored_const.
    erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (hΣ _ wfΣ).
    specialize_Σ wfΣ.
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply closed_red_zipp. 1:eapply welltyped_zipc_zipp in h1; fvs.
      eapply into_closed_red.
      * eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
      * eapply welltyped_zipc_zipp in h1; fvs.
      * eapply welltyped_zipc_zipp in h1; fvs.
    - etransitivity ; try eassumption.
      eapply red_conv_cum_r ; try assumption.
      eapply closed_red_zipp; auto.
      2:{ eapply into_closed_red; auto.
        * eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
        * eapply welltyped_zipc_zipp in h1; fvs. }
      clear aux. eapply welltyped_zipc_zipp in h2; eauto.
      destruct hx as [hx]. rewrite (All2_fold_length hx); fvs.
      Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros Σ wfΣ.
    destruct (hΣ _ wfΣ).
    eapply conv_cum_red_inv.
    - eauto.
    - apply red_zipp.
      eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
    - apply red_zipp.
      eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
    - now eapply H.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    rewrite !zipp_as_mkApps in H.
    destruct (hΣ _ wfΣ).
    eapply conv_cum_mkApps_inv in H as [(?&?)]; eauto.
    - apply whnf_mkApps.
      eapply whne_const.
      + erewrite abstract_env_lookup_correct'; eauto.
      + eauto.
    - apply whnf_mkApps.
      eapply whne_const.
      + erewrite abstract_env_lookup_correct'; eauto.
      + eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    eapply welltyped_zipc_tConst_inv in h1 as (?&?&?); eauto.
    unfold declared_constant in *.
    erewrite abstract_env_lookup_correct in d; eauto. congruence.
  Qed.
  Next Obligation.
  destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
  eapply welltyped_zipc_tConst_inv in h1 as (?&?&?); eauto.
  unfold declared_constant in *.
  erewrite abstract_env_lookup_correct in d; eauto. congruence.
Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    right; split; [easy|].
    now rewrite <- uneq_u.
  Qed.

  (* tLambda *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in e. now apply eqb_binder_annot_spec.
    - assumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct h0 as [h0].
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct (hΣ _ wfΣ).
    symmetry in e; apply eqb_binder_annot_spec in e.
    now eapply conv_cum_Lambda.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h; clear h. intros Σ wfΣ; specialize_Σ wfΣ.
    destruct h0 as [h0].
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct (hΣ _ wfΣ).
    symmetry in e; apply eqb_binder_annot_spec in e.
    apply Lambda_conv_cum_inv in H as (?&?&?); auto.
  Qed.
  Next Obligation.
    symmetry in e0.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct (hΣ _ wfΣ).
    apply Lambda_conv_cum_inv in H as (?&?&?); auto.
    eapply (ssrbool.elimF (eqb_annot_reflect _ _)) in e0; auto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h; clear h. intros Σ wfΣ. specialize_Σ wfΣ.
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct (hΣ _ wfΣ).
    apply Lambda_conv_cum_inv in H as (?&?&?); auto.
  Qed.

  (* tProd *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in e.
      now apply eqb_binder_annot_spec.
    - assumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct h0 as [h0].
    destruct hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    apply mkApps_Prod_nil in h1 as ->; auto.
    apply mkApps_Prod_nil in h2 as ->; auto.
    destruct h.
    symmetry in e.
    apply eqb_binder_annot_spec in e.
    split; eapply ws_cumul_pb_Prod; auto.
  Qed.
  Next Obligation.
    (* Codomains are not convertible *)
    apply h; clear h.
    symmetry in e. apply eqb_binder_annot_spec in e.
    intros Σ wfΣ. specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ], h0 as [h0], hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2 |- *.
    apply mkApps_Prod_nil in h1; auto.
    apply mkApps_Prod_nil in h2; auto.
    rewrite h1 h2 in H.
    apply Prod_conv_cum_inv in H as (?&_&?); auto.
  Qed.
  Next Obligation.
    (* Annotations are not convertible *)
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2 |- *.
    apply mkApps_Prod_nil in h1; auto.
    apply mkApps_Prod_nil in h2; auto.
    rewrite h1 h2 in H.
    apply Prod_conv_cum_inv in H as (?&?&?); auto.
    eapply (ssrbool.elimF (eqb_annot_reflect _ _)); tea.
    now unfold eqb_binder_annot.
  Qed.
  Next Obligation.
    (* Domains are not convertible *)
    apply h; clear h. intros Σ wfΣ. specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ], hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2, H |- *.
    apply mkApps_Prod_nil in h1; auto.
    apply mkApps_Prod_nil in h2; auto.
    rewrite h1 h2 in H.
    apply Prod_conv_cum_inv in H as (?&?&_); auto.
  Qed.
  (* tCase *)
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    zip fold in h1. apply welltyped_context in h1 ; auto. simpl in h1.
    destruct h1 as [T h1].
    apply inversion_Case in h1 as hh ; auto.
    destruct hh as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    clear aux.
    zip fold in h2. eapply welltyped_context in h2 ; eauto. simpl in h2.
    destruct h2 as [T h2].
    apply inversion_Case in h2 as hh ; auto.
    destruct hh as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    now apply eqb_eq.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    1: reflexivity.
    rewrite <- app_nil_r, stack_position_cons.
    eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    now apply eqb_eq.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    pose proof hx as hx'.
    rename H into wfΣ; specialize_Σ wfΣ.
    pose proof (heΣ _ wfΣ) as [].
    apply conv_cum_zipp; auto.
    destruct convp as [h1'], convbrs as [h2'], convargs as [h3].
    destruct convdiscr as [cdiscr]. cbn in cdiscr.
    unfold zipp in h1, h2. simpl in h1, h2.
    sq.
    apply ws_cumul_eq_pb.
    change (eq_dec_to_bool ci ci') with (eqb ci ci') in eq5.
    destruct (eqb_specT ci ci'). 2: discriminate.
    subst. eapply ws_cumul_pb_Case. all: tas.
    * clear aux eq2 eq4. eapply welltyped_zipc_zipp in h1; eauto.
      eapply welltyped_is_open_term in h1.
      rewrite zipp_as_mkApps in h1.
      rewrite on_free_vars_mkApps in h1.
      now apply andb_true_iff in h1 as [].
    * clear aux eq2 eq4. eapply welltyped_zipc_zipp in h2; eauto.
      eapply welltyped_is_open_term in h2.
      rewrite zipp_as_mkApps in h2.
      rewrite on_free_vars_mkApps in h2.
      unfold is_open_case. rewrite (All2_fold_length hx').
      now apply andb_true_iff in h2 as [].
  Qed.
  Next Obligation.
    apply h; clear h. intros.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
    now destruct (eqb_spec ci ci).
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ) as []. pose proof h2 as h2'.
    specialize_Σ wfΣ.
    match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    eapply red_welltyped ; [auto|..].
    - exact h2'.
    - eapply red_zipc.
      eapply red_case_c; auto. eapply hr.
  Qed.
  Next Obligation.
    edestruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c' [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq4.
      Transparent reduce_term.
      unfold reduce_term.
      rewrite e'. cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq4.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros.  eapply cored_zipc. eapply cored_case.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.

  Next Obligation.
    rename H into wfΣ; pose proof (hΣ _ wfΣ) as w.
    pose proof hx as hx'; specialize_Σ wfΣ. destruct w.
    destruct hx' as [hx'].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eassumption.
    - eapply conv_cum_conv_ctx; tea.
      eapply red_conv_cum_r ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_case_c. eapply hr'.
      * fvs.
      * clear aux eq4 h hr'.
        clear hr. eapply welltyped_zipc_zipp in h2; fvs.
        Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    pose proof (hΣ _ wfΣ) as []. pose proof hx as hx'.
    specialize_Σ wfΣ.
    destruct hx'.
    epose proof (reduce_term_sound _ _ _ _ _ _) as Hr; edestruct Hr as [r]; eauto.
    eapply conv_cum_red_conv_inv.
    all: tea.
    1: reflexivity.
    eapply red_zipp.
    apply red_case_c.
    exact r.
  Qed.

  Next Obligation.
    pose proof (heΣ _ wfΣ) as []. pose proof h1 as h1'.
    clear aux eq3. specialize_Σ wfΣ.
    match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    sq.
    eapply red_welltyped ; [auto|..].
    - exact h1'.
    - eapply red_zipc.
      apply red_case_c, hr.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq3.
      unfold reduce_term.
      rewrite e'.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq3.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    unshelve eapply R_cored.
    simpl. intros; eapply cored_zipc. eapply cored_case.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_case_c, hr'.
      * fvs.
      * clear eq3 h hr' hr; eapply welltyped_zipc_zipp in h1; fvs.
    - assumption.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    pose proof (hΣ _ wfΣ) as [].
    destruct (hx _ wfΣ).
    epose proof (reduce_term_sound _ _ _ _ _ _) as Hr; edestruct Hr as [r]; eauto.
    eapply conv_cum_red_inv.
    1: eauto.
    2: reflexivity.
    - apply red_zipp, red_case_c, r.
    - destruct (H _ wfΣ) as []. sq; eauto.
  Qed.

  (* tProj *)
  Next Obligation.
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    zip fold in h1. eapply welltyped_context in h1 ; eauto. simpl in h1.
    destruct h1 as [T h1].
    apply inversion_Proj in h1 as hh. 2: auto.
    destruct hh as [? [? [? [? [? [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    zip fold in h2. eapply welltyped_context in h2 as h2' ; eauto. simpl in h2'.
    destruct h2' as [T h2'].
    apply inversion_Proj in h2' as hh. 2: auto.
    destruct hh as [? [? [? [? [? [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    eapply R_aux_positionR. all: simpl.
    - reflexivity.
    - rewrite <- app_nil_r, stack_position_cons. apply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (heΣ _ wfΣ) as [wΣ].
    specialize_Σ wfΣ.
    destruct convdiscr as [h1'].
    change (true = eqb p p') in eq5.
    destruct (eqb_spec p p'). 2: discriminate. subst.
    apply conv_cum_zipp; auto.
    clear eq3 eq4 aux. eapply conv_conv_cum_l.
    now eapply ws_cumul_pb_Proj_c.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros Σ wfΣ.
    eapply inv_reduced_body_proj in H; eauto.
    destruct H as [(<-&?&?)].
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros Σ wfΣ.
    eapply inv_reduced_body_proj in H; eauto.
    destruct H as [(<-&?&?)].
    constructor; auto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    eapply inv_reduced_body_proj in H; eauto.
    destruct H as [(<-&?&?)].
    now rewrite eqb_refl in eq5.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ) as [].
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    eapply red_welltyped ; [auto|..].
    - exact (h2 _ wfΣ).
    - eapply red_zipc.
      eapply red_proj_c, hr.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c' [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq4.
      unfold reduce_term.
      rewrite e'.
      cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq4.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros; eapply cored_zipc. eapply cored_proj.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eassumption.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ. specialize_Σ wfΣ.
    pose proof (hΣ _ wfΣ) as w. destruct w.
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eassumption.
    - eapply conv_cum_conv_ctx; tea.
      eapply red_conv_cum_r ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr'.
      * fvs.
      * clear hr hr' h eq4 aux. eapply welltyped_zipc_zipp in h2; fvs.
      Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros Σ wfΣ.
    pose proof (hΣ _ wfΣ) as w. destruct w.
    specialize_Σ wfΣ.
    destruct hx as [hx].
    match type of eq4 with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity; [eassumption|].
    eapply conv_cum_conv_ctx; eauto.
    eapply red_conv_cum_l ; try assumption.
    eapply into_closed_red.
    * eapply red_zipp.
      eapply red_proj_c, hr'.
    * fvs.
    * clear eq4 aux hr hr'. eapply welltyped_zipc_zipp in h2; fvs.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ) as [].
    match goal with
      | |- context [ reduce_term ?f _ ?X ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f _ X Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    sq.
    eapply red_welltyped ; [auto|..].
    - exact (h1 _ wfΣ).
    - eapply red_zipc.
      eapply red_proj_c, hr.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq3.
      unfold reduce_term.
      rewrite e'.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq3.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    unshelve eapply R_cored.
    simpl. intros; eapply cored_zipc. eapply cored_proj.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eassumption.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ. specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr'.
      * fvs.
      * clear eq3 aux hr hr' h. eapply welltyped_zipc_zipp in h1; fvs.
    - assumption.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h. intros Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ]. specialize_Σ wfΣ.
    destruct hx as [hx].
    match type of eq3 with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eapply red_conv_cum_r ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr'.
      * fvs.
      * clear hr hr' H eq3. eapply welltyped_zipc_zipp in h1; fvs.
    - assumption.
    Unshelve. all:eauto.
  Qed.

  (* tFix *)
  Next Obligation.
    pose proof (hΣ _ wfΣ) as hΣ.
    cbn. rewrite zipc_appstack. cbn.
    eapply unfold_one_fix_red_zipp in eq1 as r; eauto.
    sq.
    apply unfold_one_fix_decompose in eq1 as d.
    rewrite <- eq2 in d. simpl in d.
    unfold zipp in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    rewrite e1 in r.
    rewrite e1 in d. simpl in d. subst.
    eapply welltyped_zipc_zipp in h1 as hh1; eauto.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    unfold zipp in hh1. rewrite e1 in hh1.
    pose proof (red_welltyped _ hΣ hh1 r) as hh.
    rewrite stack_context_appstack in hh.
    assumption.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ).
    eapply unfold_one_fix_red in eq1 as r1; eauto.
    eapply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ wfΣ.
    simpl_stacks.
    sq.
    eapply red_welltyped.
    1: eauto.
    1: exact (h1 _ wfΣ).
    etransitivity.
    2: { apply red_zipc.
         rewrite stack_context_decompose.
         exact r. }
    simpl_stacks.
    eassumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (heΣ _ wfΣ) as heΣ.
    specialize_Σ wf.
    eapply unfold_one_fix_cored in eq1 as r1; eauto.
    eapply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored. simpl. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    eapply red_cored_cored ; try eassumption.
    eapply clrel_rel in r2.
    apply red_context_zip in r2. cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    assumption.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ H.
    now simpl_stacks.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; [easy|]. intros.
    cbn in *. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now simpl_stacks.
    Unshelve. all:eauto.
  Qed.

  Lemma wt_zip_mkapps Σ (wfΣ:abstract_env_ext_rel X Σ) Γ f π : welltyped Σ Γ (zipc f π) -> is_open_term (Γ ,,, stack_context π) (mkApps f (decompose_stack π).1).
  Proof using Type.
    pose (heΣ _ wfΣ).
    sq.
    intros. apply welltyped_zipc_zipp in H; auto.
    rewrite zipp_as_mkApps in H. fvs.
  Qed.

  Next Obligation.
    eapply unfold_one_fix_red_zipp in eq1 as r1; eauto.
    eapply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ H.
    simpl_reduce_stack Σ H.
    destruct (hΣ _ H), r1  as [r1].
    eapply conv_cum_trans; auto.
    eapply red_conv_cum_l.
    etransitivity. 2:eauto.
    eapply into_closed_red; tea; [fvs|].
    eapply (f_equal stack_context) in d1.
    rewrite !stack_context_decompose in d1. rewrite <- d1.
    now eapply wt_zip_mkapps.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    eapply unfold_one_fix_red_zipp in eq1 as r1; eauto.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ wfΣ.
    simpl_reduce_stack Σ wfΣ.
    destruct (hΣ _ wfΣ), r1 as [r1].
    eapply conv_cum_red_inv.
    * eauto.
    * exact r.
    * auto.
    * specialize_Σ wfΣ. etransitivity; eauto.
      split. eapply ws_cumul_eq_pb. symmetry.
      eapply red_ws_cumul_pb.
      eapply into_closed_red.
      + eapply r1.
      + fvs.
      + eapply (f_equal stack_context) in d1.
        rewrite !stack_context_decompose in d1. rewrite <- d1.
        now eapply wt_zip_mkapps.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ).
    eapply unfold_one_fix_red_zipp in eq1 as r; eauto.
    sq.
    apply unfold_one_fix_decompose in eq1 as d.
    clear aux eq1.
    eapply welltyped_zipc_zipp in h2; eauto.
    cbn in *.
    simpl_stacks.
    eapply red_welltyped; eauto.
  Qed.
  Next Obligation.
    pose proof (hΣ _ wfΣ) as hΣ.
    eapply unfold_one_fix_red in eq1 as r1; eauto.
    sq.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f _ X Γ t π h) as c2
    end.
    rewrite <- eq3 in r2. cbn in r2. rewrite zipc_appstack in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in c2. cbn in c2. rewrite stack_context_appstack in c2.
    cbn in c2.
    case_eq (decompose_stack ρ). intros l ξ e.
    rewrite e in d2. cbn in d2. subst.
    pose proof (red_welltyped _ hΣ (h2 _ wfΣ) r1) as hh.
    apply clrel_rel, red_context_zip in r2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in hh. cbn in r2.
    pose proof (red_welltyped _ hΣ hh r2) as hh'.
    rewrite zipc_stack_cat. assumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (heΣ _ wfΣ) as heΣ.
    eapply unfold_one_fix_cored in eq1 as r1; eauto.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored2. all: try reflexivity. simpl. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    eapply red_cored_cored ; try eassumption.
    cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    do 2 zip fold. eapply red_context_zip, r2.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in d2. cbn in d2.
     rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq2 in d1. simpl in d1.
    case_eq (decompose_stack π2). intros args2 ρ2 e2.
    rewrite e2 in d1. simpl in d1. subst.
    case_eq (decompose_stack ρ). intros l ξ e'.
    rewrite e' in d2. simpl in d2. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack.
    rewrite stack_context_appstack.
    apply decompose_stack_eq in e2 as ?. subst.
    clear eq3.
    rewrite stack_context_appstack in hx.
    eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; [easy|]. intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    simpl_stacks.
    eauto.
  Unshelve. all: eauto.
  Qed.
  Next Obligation.
    eapply unfold_one_fix_red_zipp in eq1 as r1; eauto.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ H.
    simpl_reduce_stack Σ H.
    destruct r1 as [r1]. specialize_Σ H.
    destruct (hΣ _ H), hx.
    eapply conv_cum_red_conv.
    1,4: eauto.
    * eapply closed_red_refl; [fvs|].
      now eapply wt_zip_mkapps.
    * etransitivity; eauto.
      eapply into_closed_red.
      + eapply r1.
      + fvs.
      + eapply (f_equal stack_context) in d1.
        rewrite !stack_context_decompose in d1. rewrite <- d1.
        now eapply wt_zip_mkapps.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    eapply unfold_one_fix_red_zipp in eq1 as r1; eauto.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ wfΣ.
    simpl_reduce_stack Σ wfΣ.
    destruct r1 as [r1].
    destruct (hΣ Σ wfΣ), (hx Σ wfΣ).
    specialize (H Σ wfΣ).
    eapply conv_cum_red_conv_inv.
    1,2,5: eauto.
    * eapply closed_red_refl. 1:fvs.
      now eapply wt_zip_mkapps.
    * etransitivity; eauto. sq.
      eapply r.
  Qed.
  Next Obligation.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    eapply R_stateR.
    all: simpl.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    pose proof (hΣ _ H) as [hΣ]. specialize_Σ H.
    apply conv_cum_zipp; auto.
    destruct convfix as [h1'].
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_specT idx idx'). 2: discriminate.
    subst.
    eapply ws_cumul_pb_Fix; eauto.
    - clear aux eee. eapply welltyped_zipc_zipp in h1; fvs.
    - eapply All2_impl; eauto. intros.
      split; try eapply X0; eauto.
      split; try eapply X0; eauto.
  Qed.
  Next Obligation.
    apply h; clear h. intros.
    eapply inv_stuck_fixes in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    apply h; clear h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    eapply inv_stuck_fixes in H as [[<-]]; eauto.
    constructor; auto.
    eapply All2_impl; eauto. cbn; intros.
    destruct X0 as [Xr [Xe [Xd Xb]]].
    cbn; intros. repeat split; intros; eauto.
    - erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    - erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    eapply inv_stuck_fixes in H as [[<-]]; eauto.
    now rewrite eqb_refl in idx_uneq.
  Qed.

  (* tCoFix *)
  Next Obligation.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    eapply R_stateR.
    all: simpl.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    apply conv_cum_zipp; auto.
    destruct convfix as [h1'].
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_specT idx idx'). 2: discriminate.
    subst.
    eapply ws_cumul_pb_CoFix; eauto.
    - clear aux h1'. eapply welltyped_zipc_zipp in h1; fvs.
    - eapply All2_impl; eauto. now cbn; intros.
  Qed.
  Next Obligation.
    apply h; clear h. intros.
    eapply inv_stuck_cofixes in H as [(<-&?&?)]; eauto.
  Qed.
  Next Obligation.
    apply h; clear h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    eapply inv_stuck_cofixes in H as [(<-&?&?)]; eauto.
    constructor; auto.
    eapply All2_impl; eauto; cbn; intros.
    destruct X0 as [Xr [Xe [Xd Xb]]].
    repeat split; intros; eauto.
    - erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    - erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    eapply inv_stuck_cofixes in H as [(<-&?&?)]; eauto.
    rewrite eqb_refl in idx_uneq.
    congruence.
  Qed.

  (* Primitive arrays *)
  Next Obligation.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    eapply conv_cum_zipp; eauto.
    * sq. eapply ws_cumul_pb_Prim; eauto.
      + symmetry in eqi; eapply eqb_eq in eqi. subst i'.
        constructor.
      + specialize (hx Σ wfΣ) as []. fvs.
    * specialize (hx Σ wfΣ).
      specialize (h1 Σ wfΣ).
      apply welltyped_zipc_zipp in h1; auto.
      clear aux.
      eapply welltyped_zipc_zipp in h2; eauto.
      rewrite !zipp_as_mkApps in h1, h2 |- *.
      apply mkApps_Prim_nil in h1 as ->; auto.
      apply mkApps_Prim_nil in h2 as ->; auto.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
    specialize (H _ wfΣ).
    specialize (hx Σ wfΣ).
    specialize (h1 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2 |- *.
    apply mkApps_Prim_nil in h1; auto.
    apply mkApps_Prim_nil in h2; auto.
    rewrite h1 h2 in H.
    destruct H as [H]. cbn in H.
    eapply invert_cumul_Prim in H; depelim H.
    now rewrite eqb_refl in neqi.
  Qed.

  Next Obligation.
  Proof.
    symmetry in eqf.
    apply eqb_eq in eqf; subst f'.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    clear aux.
    specialize (hx Σ wfΣ).
    specialize (h1 Σ wfΣ).
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    apply mkApps_Prim_nil in h1; auto.
    apply mkApps_Prim_nil in h2; auto.
    rewrite h1 h2; cbn.
    red. sq. eapply ws_cumul_pb_Prim; eauto; fvs.
    constructor.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
    specialize (H _ wfΣ).
    specialize (hx Σ wfΣ).
    specialize (h1 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2, H |- *.
    apply mkApps_Prim_nil in h1; auto.
    apply mkApps_Prim_nil in h2; auto.
    rewrite h1 h2 in H.
    destruct H as [H]. cbn in H.
    eapply invert_cumul_Prim in H; depelim H.
    now rewrite eqb_refl in neqf.
  Qed.

  Next Obligation.
  Proof.
    symmetry in eqf.
    apply eqb_eq in eqf; subst f'.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    clear aux.
    specialize (hx Σ wfΣ).
    specialize (h1 Σ wfΣ).
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    apply mkApps_Prim_nil in h1; auto.
    apply mkApps_Prim_nil in h2; auto.
    rewrite h1 h2; cbn.
    red. sq. eapply ws_cumul_pb_Prim; eauto; fvs.
    constructor.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
    specialize (H _ wfΣ).
    specialize (hx Σ wfΣ).
    specialize (h1 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2, H |- *.
    apply mkApps_Prim_nil in h1; auto.
    apply mkApps_Prim_nil in h2; auto.
    rewrite h1 h2 in H.
    destruct H as [H]. cbn in H.
    eapply invert_cumul_Prim in H; depelim H.
    now rewrite eqb_refl in neqf.
  Qed.

  Next Obligation.
  Proof.
    destruct a; eauto.
  Qed.

  Next Obligation.
  Proof.
    destruct a'; eauto.
  Qed.

  Next Obligation.
  Proof.
    eapply R_positionR. all: simpl.
    - now destruct a.
    - rewrite <- app_nil_r, stack_position_cons.
      eapply positionR_poscat. constructor.
  Qed.

  Next Obligation.
  Proof.
    now destruct a.
  Qed.

  Next Obligation.
  Proof.
    now destruct a'; eauto.
  Qed.

  Next Obligation.
  Proof.
    eapply R_positionR. all: simpl.
    - now destruct a.
    - rewrite <- app_nil_r, stack_position_cons.
      eapply positionR_poscat. constructor.
  Qed.

  Next Obligation.
  Proof.
    pose proof (hΣ _ H) as [hΣ].
    specialize (h1 Σ H). clear aux.
    specialize (h2 Σ H).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h1); auto.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h2); auto.
    rewrite H0 H1; cbn.
    specialize (convdiscrty _ H) as [convty].
    specialize (convdiscrdef _ H) as [convdef].
    specialize (convdiscrval _ H) as [convval].
    cbn in convty, convdef.
    symmetry in eql.
    eapply abstract_env_compare_universe_correct with (conv_pb := Conv) in eql; eauto.
    2:{ destruct h1 as [? ty]; eapply typing_wf_universes in ty; eauto.
        move/andP: ty => []. rewrite H0 /=. cbn -[wf_universeb].
        rtoProp; intuition auto.
        now move/wf_universe_reflect: H3. }
    2:{ destruct h2 as [? ty]; eapply typing_wf_universes in ty; eauto.
        move/andP: ty => []. rewrite H1 /=. cbn -[wf_universeb].
        rtoProp; intuition auto.
        now move/wf_universe_reflect: H3. }
    constructor. eapply ws_cumul_pb_Prim; eauto; fvs.
    constructor; eauto.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
    specialize (h1 Σ wfΣ). clear aux.
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h1); auto.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h2); auto.
    rewrite H0 H1 in H; cbn.
    specialize (H _ wfΣ).
    apply h. intros ? H2.
    pose proof (abstract_env_ext_irr _ wfΣ H2). subst Σ0.
    cbn in H.
    destruct H as [H]; eapply invert_cumul_Prim in H; depelim H. now sq.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
        specialize (h1 Σ wfΣ). clear aux.
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h1); auto.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h2); auto.
    rewrite H0 H1 in H; cbn.
    specialize (H _ wfΣ).
    apply h. intros ? H2.
    pose proof (abstract_env_ext_irr _ wfΣ H2). subst Σ0.
    cbn in H.
    destruct H as [H]; eapply invert_cumul_Prim in H; depelim H. now sq.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
    specialize (h1 Σ wfΣ). clear aux.
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h1); auto.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h2); auto.
    rewrite H0 H1 in H; cbn.
    specialize (H _ wfΣ).
    apply h. intros ? H2.
    pose proof (abstract_env_ext_irr _ wfΣ H2). subst Σ0.
    cbn in H.
    destruct H as [H]; eapply invert_cumul_Prim in H; depelim H. now sq.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
    specialize (h1 Σ wfΣ). clear aux.
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h1); auto.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h2); auto.
    rewrite H0 H1 in H; cbn.
    specialize (H _ wfΣ).
    symmetry in neql.
    destruct H as [H]; eapply invert_cumul_Prim in H; depelim H.
    enough false by auto. rewrite <- neql.
    unshelve eapply (abstract_env_compare_universe_correct _ _ Conv) in e0; eauto.
    - rewrite H0 in h1. destruct h1 as [? wt].
      eapply typing_wf_universes in wt; eauto.
      move/andP: wt => []. cbn -[wf_universeb wf_universe]. rtoProp; intuition auto.
      now move/wf_universe_reflect: H2.
    - rewrite H1 in h2. destruct h2 as [? wt].
      eapply typing_wf_universes in wt; eauto.
      move/andP: wt => []. cbn -[wf_universeb wf_universe]. rtoProp; intuition auto.
      now move/wf_universe_reflect: H2.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hΣ _ wfΣ) as [hΣ].
    specialize (h1 Σ wfΣ). clear aux.
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in H, h1, h2.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h1); auto.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h2); auto.
    rewrite H0 H1 in H; cbn.
    specialize (H _ wfΣ).
    rewrite H0 /= in h1; rewrite H1 /= in h2.
    destruct H as [H]; eapply invert_cumul_Prim in H; depelim H.
    all:cbn in tag_uneq; congruence.
  Qed.

  (* Fallback *)
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.

  Definition Aux' Γ t1 args1 l1 π1 t2 π2 h2 :=
    forall u1 u2 ca1 a1 ρ2
      (h1' : wtp Γ u1 (App_r (mkApps t1 ca1) :: appstack a1 π1))
      (h2' : wtp Γ u2 ρ2),
      let x :=
        mkpack Γ Reduction u1 (App_r (mkApps t1 ca1) :: (appstack a1 π1)) u2 ρ2 h2'
      in
      let y := mkpack Γ Args (mkApps t1 args1) (appstack l1 π1) t2 π2 h2 in
      (S #|ca1| + #|a1| = #|args1| + #|l1|)%nat ->
      pzt x = pzt y /\
      positionR (` (pps1 x)) (` (pps1 y)) ->
      Ret Reduction Γ u1 (App_r (mkApps t1 ca1) :: (appstack a1 π1)) u2 ρ2.

  Equations(noeqns) _isconv_args' (leq : conv_pb) (Γ : context)
            (t1 : term) (args1 : list term)
            (l1 : list term) (π1 : stack)
            (h1 : wtp Γ (mkApps t1 args1) (appstack l1 π1))
            (hπ1 : isStackApp π1 = false)
            (t2 : term)
            (l2 : list term) (π2 : stack)
            (h2 : wtp Γ t2 (appstack l2 π2))
            (hπ2 : isStackApp π2 = false)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux' Γ t1 args1 l1 π1 t2 (appstack l2 π2) h2)
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π1) l1 l2∥) by struct l1 :=
    _isconv_args' leq Γ t1 args1 (u1 :: l1) π1 h1 hπ1 t2 (u2 :: l2) π2 h2 hπ2 hx aux
    with aux u1 u2 args1 l1 (App_r t2 :: (appstack l2 π2)) _ _ _ _ Conv _ I I I := {
    | Success H1 with _isconv_args' leq Γ t1 (args1 ++ [u1]) l1 π1 _ _ (tApp t2 u2) l2 π2 _ _ _ (expand aux) := {
      | Success H2 := yes ;
      | Error e herr :=
        no (
          StackTailError
            leq
            (Γ ,,, stack_context π1) t1 args1 u1 l1
            (Γ ,,, stack_context π2) t2 u2 l2 e
        )
      } ;
    | Error e herr :=
      no (
        StackHeadError
          leq
          (Γ ,,, stack_context π1) t1 args1 u1 l1
          (Γ ,,, stack_context π2) t2 u2 l2 e
      )
    } ;

    _isconv_args' leq Γ t1 args1 [] π1 h1 hπ1 t2 [] π2 h2 hπ2 hx aux := yes ;

    _isconv_args' leq Γ t1 args1 l1 π1 h1 hπ1 t2 l2 π2 h2 hπ2 hx aux :=
      no (
        StackMismatch
          (Γ ,,, stack_context π1) t1 args1 l1
          (Γ ,,, stack_context π2) t2 l2
      ).
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (H _ wfΣ) as [H']; depelim H'.
  Defined.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (H _ wfΣ) as [H']; depelim H'.
  Defined.
  Next Obligation.
    split. 1: reflexivity.
    rewrite !stack_position_cons.
    eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rewrite 2!stack_context_appstack.
    eauto.
  Qed.
  Next Obligation.
    rewrite mkApps_app. eauto.
  Qed.
  Next Obligation.
    rewrite length_app in h. cbn in h. lia.
  Defined.
  Next Obligation.
    rewrite length_app in h. cbn in h.
      simpl. split.
      + rewrite mkApps_app in H. assumption.
      + rewrite !stack_position_cons !stack_position_appstack.
        rewrite <- !app_assoc. apply positionR_poscat.
        assert (h' : forall n m, positionR (repeat app_l n ++ [app_r]) (repeat app_l m)).
        { clear. intro n. induction n ; intro m.
          - destruct m ; constructor.
          - destruct m.
            + constructor.
            + cbn. constructor. apply IHn.
        }
        simpl.
        rewrite <- repeat_snoc.
        apply (h' #|d| (S #|l1|)).
  Qed.
  Next Obligation.
    specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct H1 as [H1].
    unfold zipp. simpl.
    unfold zipp in H1. simpl in H1.
    rewrite stack_context_appstack in H1.
    destruct H2 as [H2].
    constructor; constructor; auto.
  Qed.
  Next Obligation.
    apply herr; clear herr. intros Σ wfΣ. specialize_Σ wfΣ.
    destruct H as [H]; depelim H.
    constructor; auto.
  Defined.
  Next Obligation.
    apply herr; cbn; clear herr. intros Σ wfΣ. specialize_Σ wfΣ.
    destruct H as [H]; depelim H.
    rewrite stack_context_appstack.
    constructor; auto.
  Defined.

  Equations(noeqns) _isconv_args (leq : conv_pb) (Γ : context)
           (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
           (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
           (hx : conv_stack_ctx Γ π1 π2)
           (aux : Aux Args Γ t1 π1 t2 π2 h2)
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π1)
                         (decompose_stack π1).1
                         (decompose_stack π2).1∥) :=
    _isconv_args leq Γ t1 π1 h1 t2 π2 h2 hx aux with inspect (decompose_stack π1) := {
    | @exist (l1, θ1) eq1 with inspect (decompose_stack π2) := {
      | @exist (l2, θ2) eq2 with _isconv_args' leq Γ t1 [] l1 θ1 _ _ t2 l2 θ2 _ _ _ _ := {
        | Success h := yes ;
        | Error e h := no e
        }
      }
    }.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    eauto.
  Qed.
  Next Obligation.
    eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    eauto.
  Qed.
  Next Obligation.
    eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite 2!stack_context_appstack in hx.
    eauto.
  Qed.
  Next Obligation.
    eapply (aux Reduction). all: auto.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    instantiate (1 := h2').
    simpl in H0. destruct H0 as [eq hp].
    unshelve eapply R_positionR. 2: assumption.
    simpl. rewrite eq. reflexivity.
  Defined.
  (* The obligation tactic wipes out a useful hypothesis here? *)
  Obligation Tactic := idtac.
  Next Obligation.
    intros; cbn in *.
    rewrite <- (stack_context_decompose π1).
    rewrite <- eq1, <- eq2.
    auto.
  Qed.
  Next Obligation.
    intros; cbn in *.
    rewrite <- (stack_context_decompose π1).
    rewrite <- eq1, <- eq2.
    auto.
  Qed.
  Obligation Tactic :=
    Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf.

  Equations unfold_one_case (Γ : context) (ci : case_info)
            (p : predicate term) (c : term) (brs : list (branch term))
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (tCase ci p c brs)) : option term :=
    unfold_one_case Γ ci p c brs h
    with inspect (reduce_stack RedFlags.default _ X Γ c [] _) := {
    | @exist (cred, ρ) eq with cc_viewc cred := {
      | ccview_construct ind' n ui with inspect (decompose_stack ρ) := {
        | @exist (args, ξ) eq' with inspect (nth_error brs n) := {
          | exist (Some br) eqbr := Some (iota_red ci.(ci_npar) p args br) ;
          | exist None eqbr := False_rect _ _ }
        } ;
      | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
        | @exist (Some (narg, fn)) eq2 with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' := Some (tCase ci p (mkApps fn args) brs) } ;
        | @exist None eq2 := False_rect _ _
        } ;
      | ccview_other cred _ := None
      }
    }.
  Next Obligation.
    destruct (hΣ _ wfΣ) as [wΣ]. specialize_Σ wfΣ.
    cbn. destruct h as [T h].
    apply inversion_Case in h ; auto.
    destruct h as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (hΣ _ wfΣ) as [hΣ].
    assert (r' : red Σ Γ (tCase ci p c brs)
      (tCase ci p (mkApps (tConstruct ind' n ui) (decompose_stack ρ).1) brs))
      by eapply red_case_c, r.
    pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
    destruct h'.
    apply PCUICInductiveInversion.invert_Case_Construct in X0 as (?&?&?&?); auto.
    congruence.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (h _ wfΣ) as (?&typ); auto.
    destruct (hΣ _ wfΣ).
    apply inversion_Case in typ as [mdecl [idecl [isdecl [indices [[] cum]]]]]; auto.
    eapply PCUICSR.subject_reduction in scrut_ty. 2:auto. 2:exact r.
    eapply PCUICValidity.inversion_mkApps in scrut_ty as (?&typ&?); auto.
    apply inversion_CoFix in typ as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in eq2.
    now rewrite e in eq2.
  Qed.

  Lemma unfold_one_case_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci p c brs h t,
      Some t = unfold_one_case Γ ci p c brs h ->
      cored Σ Γ t (tCase ci p c brs).
  Proof using Type.
    intros Σ wfΣ Γ ci p c brs h t e.
    revert e.
    funelim (unfold_one_case Γ ci p c brs h).
    all:try Program.Tactics.bang.
    all: intros eq'' ; noconf eq''.
    - clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      destruct (hΣ _ wfΣ) as [hΣ].
      assert (r' : red Σ Γ (tCase ci p c brs)
          (tCase ci p (mkApps (tConstruct ind' n ui) (decompose_stack ρ).1) brs))
        by eapply red_case_c, r.
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      eapply Case_Construct_ind_eq in h' ; eauto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_iota. 1: now symmetry.
        destruct (h _ wfΣ) as (?&typ).
        eapply PCUICSR.subject_reduction in typ; eauto.
        apply PCUICInductiveInversion.invert_Case_Construct in typ as (?&?&?&?); auto.
        rewrite H0 in eqbr; noconf eqbr. eauto.
      + eapply red_case_c, r.
    - clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      assert (r' : red Σ Γ (tCase ci p c brs)
                     (tCase ci p (mkApps (tCoFix mfix idx) (decompose_stack ρ).1) brs))
        by eapply red_case_c, r.
      destruct (hΣ _ wfΣ) as [hΣ].
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_case. eauto.
      + eapply red_case_c, r.
  Qed.

  Lemma unfold_one_case_None Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci p c brs h :
    None = unfold_one_case Γ ci p c brs h ->
    ∥∑ c', red Σ Γ c c' × whne RedFlags.default Σ Γ c'∥.
  Proof using Type.
    funelim (unfold_one_case Γ ci p c brs h); intros [=].
    - clear H.
      simpl_reduce_stack Σ wfΣ.
      destruct (h _ wfΣ) as (?&typ); auto.
      destruct (hΣ _ wfΣ), w.
      constructor; exists (mkApps cred (decompose_stack ρ).1).
      split; [exact r|].
      specialize (isr eq_refl) as (noapp&_).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: eapply red_case_c, r.
      eapply whnf_case_arg_whne; eauto.
      now destruct cred.
    - match type of H3 with
      | _ = False_rect _ ?f => destruct f
      end.
    - match type of H2 with
      | _ = False_rect _ ?f => destruct f
      end.
  Qed.

  Equations unfold_one_proj (Γ : context) (p : projection) (c : term)
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (tProj p c)) : option term :=

    unfold_one_proj Γ p c h with p := {
    | mkProjection i pars narg with inspect (reduce_stack RedFlags.default _ X Γ c [] _) := {
      | @exist (cred, ρ) eq with cc0_viewc cred := {
        | cc0view_construct ind' ui with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (nth_error args (pars + narg)) := {
            | @exist (Some arg) eq2 := Some arg ;
            | @exist None eq2 := False_rect _ _
            }
          } ;
        | cc0view_cofix mfix idx with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (unfold_cofix mfix idx) := {
            | @exist (Some (rarg, fn)) eq2 :=
              Some (tProj p (mkApps fn args)) ;
            | @exist None eq2 := False_rect _ _
            }
          } ;
        | cc0view_other cred _ := None
        }
      }
    }.
  Next Obligation.
    destruct (hΣ _ wfΣ) as [wΣ].
    cbn. destruct (h _ wfΣ) as [T h'].
    apply inversion_Proj in h' ; auto.
    destruct h' as [uni [mdecl [idecl [pdecl [args' [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (h _ wfΣ) as (?&typ); auto.
    destruct (hΣ _ wfΣ).
    eapply PCUICSR.subject_reduction in typ.
    2: auto.
    2: apply red_proj_c, r.
    apply PCUICInductiveInversion.invert_Proj_Construct in typ as (<-&_&?); auto.
    apply eq_sym, nth_error_None in eq2. cbn in H.
    lia.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (h _ wfΣ) as (?&typ); auto.
    destruct (hΣ _ wfΣ).
    apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?&?); auto.
    eapply PCUICSR.subject_reduction in t. 2:eauto. 2:exact r.
    apply PCUICValidity.inversion_mkApps in t as (?&?&?); auto.
    apply inversion_CoFix in t as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in eq2.
    rewrite e0 in eq2.
    congruence.
  Qed.

  Lemma unfold_one_proj_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ p c h t,
      Some t = unfold_one_proj Γ p c h ->
      cored Σ Γ t (tProj p c).
  Proof using Type.
    intros Σ wfΣ Γ p c h t e.
    revert e.
    funelim (unfold_one_proj Γ p c h).
    all: intros eq'' ; noconf eq''.
    - set (p := {| proj_ind := i; proj_npars := pars; proj_arg := narg |}).
       clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      pose proof (red_proj_c p _ _ r) as r'.
      destruct (hΣ _ wfΣ) as [hΣ].
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      apply Proj_Construct_ind_eq in h' ; auto. subst.
      eapply cored_red_cored.
      + constructor. eapply (red_proj _ _ p). eauto.
      + eapply red_proj_c, r.
    - match type of eq'' with
      | _ = False_rect _ ?f => destruct f
      end.
    -  set (p := {| proj_ind := i; proj_npars := pars; proj_arg := narg |}).
      clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      pose proof (red_proj_c p _ _ r) as r'.
      destruct (hΣ _ wfΣ) as [hΣ].
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_proj. eauto.
      + eapply red_proj_c, r.
    - match type of eq'' with
      | _ = False_rect _ ?f => destruct f
      end.
  Qed.

  Lemma unfold_one_proj_None Σ (wfΣ : abstract_env_ext_rel X Σ) Γ p c h :
    None = unfold_one_proj Γ p c h ->
    ∥∑ c', red Σ Γ c c' × whne RedFlags.default Σ Γ c'∥.
  Proof using Type.
    funelim (unfold_one_proj Γ p c h); intros [=].
    - clear H.
      simpl_reduce_stack Σ wfΣ.
      destruct (hΣ _ wfΣ), w.
      destruct (h _ wfΣ) as (?&typ); auto.
      constructor; exists (mkApps cred (decompose_stack ρ).1).
      split; [exact r|].
      specialize (isr eq_refl) as (noapp&_).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: eapply red_proj_c, r.
      eapply whnf_proj_arg_whne ; eauto.
      now destruct cred.
    - match type of H3 with
      | _ = False_rect _ ?f => destruct f
      end.
    - match type of H3 with
      | _ = False_rect _ ?f => destruct f
      end.
  Qed.

  Equations reducible_head (Γ : context) (t : term) (π : stack)
            (h : wtp Γ t π)
    : option (term × stack) :=

    reducible_head Γ (tFix mfix idx) π h := unfold_one_fix Γ mfix idx π h ;

    reducible_head Γ (tCase ci p c brs) π h
    with inspect (unfold_one_case (Γ ,,, stack_context π) ci p c brs _) := {
    | @exist (Some t) eq :=Some (t, π) ;
    | @exist None _ := None
    } ;

    reducible_head Γ (tProj p c) π h
    with inspect (unfold_one_proj (Γ ,,, stack_context π) p c _) := {
    | @exist (Some t) eq := Some (t, π) ;
    | @exist None _ := None
    } ;

    reducible_head Γ (tConst c u) π h
    with inspect (abstract_env_lookup X c) := {
    | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq :=
      Some (subst_instance u body, π) ;
    | @exist _ _ := None
    } ;

    reducible_head Γ _ π h := None.
  Next Obligation.
    zip fold in h.
    pose (abstract_env_ext_sq_wf _ X _ wfΣ).
    sq.
    eapply welltyped_context in h ; eauto.
  Qed.
  Next Obligation.
    pose (abstract_env_ext_sq_wf _ X _ wfΣ).
    sq.
    zip fold in h.
    eapply welltyped_context in h ; eauto.
  Qed.

  Lemma reducible_head_red_zipp :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp t π) (zipp fn ξ) ∥.
  Proof using Type.
    intros Σ wfΣ Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_red_zipp; eauto.
    - constructor. simpl_stacks.
      eapply red_mkApps_f.
      eapply trans_red.
      + reflexivity.
      + eapply red_delta.
      * unfold declared_constant, declared_constant_gen.
        erewrite abstract_env_lookup_correct; eauto.
        * reflexivity.
    - eapply unfold_one_case_cored in eq as r; eauto.
      apply cored_red in r.
      destruct r as [r].
      constructor. simpl_stacks.
      eapply red_mkApps_f.
      assumption.
    - eapply unfold_one_proj_cored in eq as r; eauto.
      apply cored_red in r.
      destruct r as [r].
      constructor. simpl_stacks.
      eapply red_mkApps_f.
      assumption.
  Qed.

  Lemma reducible_head_red_zippx :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) Γ (zippx t π) (zippx fn ξ) ∥.
  Proof using Type.
    intros Σ wfΣ Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_red_zippx; eauto.
    - constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s eq'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      eapply trans_red.
      + reflexivity.
      + eapply red_delta.
        * unfold declared_constant, declared_constant_gen.
          erewrite abstract_env_lookup_correct;  eauto.
        * reflexivity.
    - eapply unfold_one_case_cored in eq as r; eauto. apply cored_red in r.
      destruct r as [r].
      constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s e'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply decompose_stack_eq in e'. subst.
      rewrite stack_context_appstack in r. assumption.
    - eapply unfold_one_proj_cored in eq as r;eauto. apply cored_red in r.
      destruct r as [r].
      constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s e'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply decompose_stack_eq in e'. subst.
      rewrite stack_context_appstack in r. assumption.
  Qed.

  Lemma reducible_head_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      cored Σ Γ (zipc fn ξ) (zipc t π).
  Proof using Type.
    intros Σ wfΣ Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_cored; eauto.
    - repeat zip fold. eapply cored_context.
      constructor. eapply red_delta.
      + unfold declared_constant, declared_constant_gen.
        erewrite abstract_env_lookup_correct; eauto.
      + reflexivity.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_case_cored; eauto.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_proj_cored; eauto.
  Qed.

  Lemma reducible_head_decompose :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof using Type.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_decompose. eassumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* TODO move to PCUICNormal *)
  Lemma whnf_mkApps_tPrim_inv :
    forall (f : RedFlags.t) (Σ : global_env) (Γ : context) p (args : list term),
      whnf f Σ Γ (mkApps (tPrim p) args) -> args = [].
  Proof using Type.
    intros * wh.
    inversion wh; solve_discr.
    clear -X0.
    remember (mkApps (tPrim p) args) eqn:teq.
    exfalso.
    revert teq.
    induction X0 in args |- *; intros; solve_discr.
    destruct args as [|? ? _] using MRList.rev_ind; [easy|].
    rewrite mkApps_app in teq.
    cbn in teq. noconf teq.
    eauto.
  Qed.

  Lemma reducible_head_None Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h :
    isApp t = false ->
    whnf RedFlags.nodelta Σ (Γ,,, stack_context π) (mkApps t (decompose_stack π).1) ->
    None = reducible_head Γ t π h ->
    ∥∑ t' args',
      whnf_red Σ (Γ,,, stack_context π) t t' ×
      All2 (red Σ (Γ,,, stack_context π)) (decompose_stack π).1 args' ×
      whnf RedFlags.default Σ (Γ,,, stack_context π) (mkApps t' args')∥.
  Proof using Type.
    funelim (reducible_head Γ t π h); intros notapp wh [=].
    - apply whnf_mkApps_inv in wh.
      depelim wh; solve_discr.
      depelim w; solve_discr; try discriminate.
      constructor; eexists _, (decompose_stack π).1.
      split; [now constructor|].
      split; eauto with pcuic.
      apply whnf_mkApps.
      eauto with pcuic.
    - apply whnf_mkApps_inv in wh; auto.
      depelim wh; solve_discr.
      constructor; eexists _, (decompose_stack π).1.
      split; [constructor|].
      split; eauto with pcuic.
      apply whnf_mkApps.
      constructor.
    - apply whnf_mkApps_inv in wh; auto.
      depelim wh; solve_discr.
      constructor; eexists _, (decompose_stack π).1.
      split; [constructor; eauto with pcuic|].
      split; eauto with pcuic.
      apply whnf_mkApps.
      depelim w; solve_discr; eauto with pcuic.
    - apply whnf_mkApps_tSort_inv in wh as ->.
      constructor; eexists _, [].
      eauto using whnf_red with pcuic.
    - apply whnf_mkApps_tProd_inv in wh as ->.
      constructor; eexists _, [].
      eauto using whnf_red with pcuic.
    - depelim wh; solve_discr.
      + apply whne_mkApps_inv in w as [|(?&?&?&?&?&?&?&?)]; auto; try discriminate.
        depelim w; solve_discr.
        discriminate.
      + rewrite H1.
        constructor; eexists _, []; eauto using whnf_red with pcuic.
    - apply whnf_mkApps_inv in wh; auto.
      depelim wh; solve_discr.
      depelim w; solve_discr.
      discriminate.
    - discriminate.
    - constructor; eexists _, (decompose_stack π).1; eauto using whnf_red with pcuic.
    - constructor; eexists _, (decompose_stack π).1; eauto using whnf_red with pcuic.
    - eapply unfold_one_fix_None in H0 as [(?&?&?)]; eauto.
      constructor; eexists _, x.
      split; [constructor; eauto with pcuic|].
      eauto with pcuic.
    - constructor; eexists _, (decompose_stack π).1.
      split; [constructor; eauto with pcuic|].
      eauto with pcuic.
    - apply whnf_mkApps_tPrim_inv in wh as ->.
      constructor; eexists (tPrim prim), [].
      split.
      * constructor. destruct prim as [? []]; constructor; auto.
        eapply All2_same. intros; reflexivity.
      * split; [constructor|]. eapply whnf_prim.
    - constructor; eexists _, (decompose_stack π).1.
      clear H. erewrite <- abstract_env_lookup_correct' in e; eauto.
      split; [econstructor|]; eauto.
      split; [eauto with pcuic|].
      apply whnf_mkApps.
      eapply whne_const; eauto.
    - zip fold in h. try clear Heqcall.
      destruct (hΣ _ wfΣ).
      eapply welltyped_context in h; eauto.
      destruct h as (?&typ); auto.
      apply inversion_Const in typ as (?&?&?&?); auto.
      unshelve eapply declared_constant_to_gen in d; eauto.
      clear H. erewrite <- abstract_env_lookup_correct' in e; eauto.
      congruence.
    - zip fold in h. try clear Heqcall.
      destruct (hΣ _ wfΣ).
      eapply welltyped_context in h; eauto.
      destruct h as (?&typ); auto.
      apply inversion_Const in typ as (?&?&?&?); auto.
      unshelve eapply declared_constant_to_gen in d; eauto.
      clear H. erewrite <- abstract_env_lookup_correct' in e; eauto.
      congruence.
    - clear H.
      eapply unfold_one_case_None in e as [(c'&r&whcase)]; eauto.
      constructor; exists (tCase ci p c' brs), (decompose_stack π).1.
      split.
      + destruct p. constructor; eauto with pcuic.
      + split; [eauto with pcuic|].
        apply whnf_mkApps.
        auto.
    - clear H.
      eapply unfold_one_proj_None in e as [(c'&r&whproj)]; eauto.
      constructor; exists (tProj p c'), (decompose_stack π).1.
      split.
      + constructor; eauto with pcuic.
      + split; [eauto with pcuic|].
        apply whnf_mkApps.
        auto.
  Qed.

  (* TODO Factorise *)
  Equations(noeqns) _isconv_fallback (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (ir1 : isred_full Γ t1 π1) (ir2 : isred_full Γ t2 π2)
            (hdiscr : prog_discr t1 t2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Fallback Γ t1 π1 t2 π2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=
    _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 ir1 ir2 hdiscr hx aux
    with inspect (reducible_head Γ t1 π1 h1) := {
    | exist (Some (rt1, ρ1)) eq1 with inspect (decompose_stack ρ1) := {
      | exist (l1, θ1) eq2
        with inspect (reduce_stack RedFlags.nodelta _ X (Γ ,,, stack_context ρ1) rt1 (appstack l1 []) _) := {
        | exist (rt1', θ1') eq3 :=
          isconv_prog leq rt1' (θ1' ++ θ1) t2 π2 aux
        }
      } ;
    | exist None nored1 with inspect (reducible_head Γ t2 π2 h2) := {
      | exist (Some (rt2, ρ2)) eq1 with inspect (decompose_stack ρ2) := {
        | exist (l2, θ2) eq2
          with inspect (reduce_stack RedFlags.nodelta _ X (Γ ,,, stack_context ρ2) rt2 (appstack l2 []) _) := {
          | exist (rt2', θ2') eq3 :=
            isconv_prog leq t1 π1 rt2' (θ2' ++ θ2) aux
          }
        } ;
      | exist None nored2 with inspect (cmpb_term_napp leq #|(decompose_stack π1).1| t1 t2) := {
        | exist true eq1 := isconv_args leq t1 π1 t2 π2 aux;
        | exist false noteq :=
          no (
              HeadMismatch
                leq
                (Γ ,,, stack_context π1) t1
                (Γ ,,, stack_context π2) t2
            )
        }
      }
    }.
  Next Obligation.
    eapply reducible_head_red_zipp in eq1 as r; eauto.
    pose proof (hΣ := hΣ _ wfΣ).
    sq.
    apply reducible_head_decompose in eq1 as d.
    eapply welltyped_zipc_zipp in h1 as hh1; eauto.
    cbn in *.
    pose proof (red_welltyped _ hΣ hh1 r) as hh.
    simpl_stacks.
    assumption.
  Qed.
  Next Obligation.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply cored_red in r1.
    pose proof (hΣ _ wfΣ).
    sq.
    simpl_reduce_stack Σ wfΣ.
    eapply red_welltyped; revgoals. 3:auto.
    - zip fold. eapply red_context_zip. simpl_stacks. exact r.
    - cbn.
      simpl_stacks.
      eapply red_welltyped. 1:auto.
      2: exact r1.
      eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π1). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X Σ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ1'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply red_context_zip, r2.
  Qed.
  Next Obligation.
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ H.
    eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; auto. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now simpl_stacks.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    eapply reducible_head_red_zipp in eq1 as r1; eauto.
    destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ H.
    destruct (hΣ _ H) as [wΣ].
    etransitivity ; try eauto.
    eapply red_conv_cum_l; try eauto.
    etransitivity ; try eassumption.
    eapply into_closed_red; tea.
    * fvs.
    * eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1. rewrite <- d1.
      now eapply wt_zip_mkapps.
  Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    eapply reducible_head_red_zipp in eq1 as r1; eauto.
    destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    etransitivity ; try eauto.
    eapply red_conv_cum_r ; try assumption.
    etransitivity; tea.
    eapply (f_equal stack_context) in d1.
    rewrite !stack_context_decompose in d1.
    eapply into_closed_red; [exact r1|..]. 1:fvs.
    rewrite <- d1. now eapply wt_zip_mkapps.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    eapply reducible_head_red_zipp in eq1 as r; eauto.
    pose proof (hΣ := hΣ _ wfΣ).
    sq.
    apply reducible_head_decompose in eq1 as d.
    cbn.
    eapply welltyped_zipc_zipp in h2 as hh2 ; eauto.
    pose proof (red_welltyped _ hΣ hh2 r) as hh.
    simpl_stacks.
    assumption.
  Qed.
  Next Obligation.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply cored_red in r1.
    pose proof (hΣ := hΣ _ wfΣ).
    sq.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    rewrite stack_cat_appstack.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    pose proof (eq_sym eq2) as eq2'.
    apply decompose_stack_eq in eq2'. subst.
    rewrite stack_context_appstack in r2.
    eapply red_welltyped; [auto|..] ; revgoals.
    - zip fold. eapply red_context_zip, r2.
    - rewrite zipc_appstack in r1. cbn.
      eapply red_welltyped; try apply r1 ; eauto.
  Qed.
  Next Obligation.
    eapply R_cored2. all: simpl. all: try reflexivity.
    intros.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π2). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply red_context_zip, r2.
  Qed.
  Next Obligation.
    eapply reducible_head_decompose in eq1 as d1.
    now simpl_reduce_stack Σ H.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; auto. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now simpl_stacks.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (hΣ _ H) as [wΣ].
    eapply reducible_head_red_zipp in eq1 as r1; eauto.
    destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ H.
    destruct (hx _ H) as [hx'].
    etransitivity ; try eauto.
    eapply conv_cum_conv_ctx.
    - eapply red_conv_cum_r.
      etransitivity; tea.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      rewrite <- d1. now eapply wt_zip_mkapps.
    - eauto.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    (* Contrapositive of previous case *)
    destruct (hΣ _ wfΣ) as [wΣ].
    eapply reducible_head_red_zipp in eq1 as r1; eauto.
    destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ wfΣ.
    destruct (hx _ wfΣ) as [hx'].
    etransitivity ; try eauto.
    eapply conv_cum_conv_ctx.
    - eapply red_conv_cum_l.
      etransitivity; tea.
      eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      rewrite <- d1; now eapply wt_zip_mkapps.
    - eauto.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    eapply R_stateR. all: simpl. all: try reflexivity.
    constructor.
    Qed.

  Next Obligation.
    destruct (h _ H), (hΣ _ H).
    eapply ws_cumul_pb_terms_alt in X0 as (argsr&argsr'&[]).
    rewrite !zipp_as_mkApps.
    apply conv_cum_alt; auto.
    constructor; eexists _, _.
    constructor.
    - apply PCUICInductiveInversion.closed_red_mkApps; tea.
      * clear aux nored1. eapply welltyped_zipc_zipp in h1; fvs.
      * clear aux nored1. eapply wt_zip_mkapps in h1; eauto.
        rewrite on_free_vars_mkApps in h1. now apply andb_true_iff in h1.
    - apply PCUICInductiveInversion.closed_red_mkApps; tea.
      * clear aux nored1. eapply welltyped_zipc_zipp in h1; fvs.
      * clear aux nored1 nored2. eapply wt_zip_mkapps in h1; eauto.
        eapply wt_zip_mkapps in h2; eauto.  destruct (hx _ H).
        rewrite (All2_fold_length X0).
        rewrite on_free_vars_mkApps in h2. now apply andb_true_iff in h2.
    - apply eq_term_upto_univ_napp_mkApps; auto.
      rewrite Nat.add_0_r.
      apply All2_length in a.
      rewrite a in eq1.
      eapply cmpb_term_correct; tea.
      + pose proof h1 as Hc. specialize_Σ H. pose proof (hΣ _  H); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
      + pose proof h2 as Hc. specialize_Σ H. pose proof (hΣ _  H); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
      + now symmetry.
  Qed.
  Next Obligation.
    apply h; clear h. intros Σ wfΣ.
    edestruct ir1 as (notapp1&[whδ1]), ir2 as (notapp2&[whδ2]); eauto.
    erewrite !zipp_as_mkApps in *.
    eapply reducible_head_None in nored1 as [(?&?&s1&r1&wh1)]; eauto.
    eapply reducible_head_None in nored2 as [(?&?&s2&r2&wh2)]; eauto.
    destruct (hΣ _ wfΣ), (hx _ wfΣ).
    apply whnf_red_red in s1 as ?.
    apply whnf_red_red in s2 as ?.
    eapply conv_cum_red_conv_inv in H.
    2: eassumption.
    2: eassumption.
    2: eapply red_mkApps; eauto.
    2: apply red_mkApps; eauto.
    2: eauto.
    eapply conv_cum_mkApps_inv in H as [(?&?)]; eauto.
    2: now depelim s1.
    2: now depelim s2.
    2: eapply whnf_conv_context; eauto.
    2: symmetry in X1; eapply ws_cumul_ctx_pb_forget in X1; eauto.
    constructor.
    eapply ws_cumul_pb_terms_red_conv; eauto.
    all:eapply into_red_terms; tea.
    1:fvs. 2:fvs.
    all:clear aux.
    * eapply wt_zip_mkapps in h1; eauto.
      rewrite on_free_vars_mkApps in h1. now apply andb_true_iff in h1 as [].
    * eapply wt_zip_mkapps in h2; eauto.
      rewrite on_free_vars_mkApps in h2. now apply andb_true_iff in h2 as [].
  Qed.

  Next Obligation.
    unfold eqb_termp_napp in noteq.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    edestruct ir1 as (notapp1&[whδ1]), ir2 as (notapp2&[whδ2]); eauto.
    erewrite !zipp_as_mkApps in *.
    eapply reducible_head_None in nored1 as [(?&?&s1&rargs1&wh1)]; eauto.
    eapply reducible_head_None in nored2 as [(?&?&s2&rargs2&wh2)]; eauto.
    destruct (hΣ _ wfΣ), (hx _ wfΣ).
    apply whnf_red_red in s1 as ?.
    apply whnf_red_red in s2 as ?.
    eapply conv_cum_red_conv_inv in H.
    2: eassumption.
    2: eassumption.
    2: apply red_mkApps; eassumption.
    2: apply red_mkApps; eassumption.
    2: eassumption.
    apply conv_cum_mkApps_inv in H as [(conv_hds&_)]; auto.
    2: now inversion s1; subst.
    2: now inversion s2; subst.
    2: eapply whnf_conv_context; eauto.
    2: { symmetry in X1. eapply ws_cumul_ctx_pb_forget in X1; tea. }
    apply whnf_mkApps_inv in wh1.
    destruct t1; cbn in *.
    all: inversion s1; subst; clear s1.
    9: { destruct conv_hds as [H].
         inversion H; subst; clear H.
         inversion s2; subst; clear s2.
         zip fold in h1.
         zip fold in h2.
         eapply welltyped_context in h1; eauto.
         clear aux.
         eapply welltyped_context in h2; eauto.
         destruct h1 as (?&typ1); auto.
         destruct h2 as (?&typ2); auto.
         apply inversion_Ind in typ1 as (?&?&?&?&?&?); auto.
         apply inversion_Ind in typ2 as (?&?&?&?&?&?); auto.
         apply consistent_instance_ext_wf in c0.
         apply consistent_instance_ext_wf in c.
         eapply compare_global_instance_correct in H3; eauto.
         rewrite eqb_refl in noteq.
         apply All2_length in rargs1.
         rewrite <- rargs1 in H3.
         apply ssrbool.not_false_is_true. rewrite noteq.
         destruct leq; eauto.
}
    9: { destruct conv_hds as [H].
         inversion H; subst; clear H.
         inversion s2; subst; clear s2.
         zip fold in h1.
         zip fold in h2.
         eapply welltyped_context in h1; eauto.
         clear aux.
         eapply welltyped_context in h2; eauto.
         destruct h1 as (?&typ1); auto.
         destruct h2 as (?&typ2); auto.
         apply inversion_Construct in typ1 as (?&?&?&?&?&?&?); auto.
         apply inversion_Construct in typ2 as (?&?&?&?&?&?&?); auto.
         apply consistent_instance_ext_wf in c0.
         apply consistent_instance_ext_wf in c.
         rewrite !eqb_refl in noteq.
         apply All2_length in rargs1.
         rewrite <- rargs1 in H4.
         apply ssrbool.not_false_is_true. rewrite noteq. cbn.
         eapply compare_global_instance_correct; eauto.
         }
    all: apply conv_cum_alt in conv_hds as [(?&?&[r1 r2 ?])]; auto.
    all: eapply whnf_red_inv in r1; auto.
    all: inversion r1; subst; clear r1.
    all: inversion c; subst; clear c.
    all: apply whnf_mkApps_inv in wh2.
    all: eapply whnf_conv_context in wh2; [|symmetry in X1; eapply ws_cumul_ctx_pb_forget in X1; exact X1].
    all: eapply whnf_red_inv in r2; auto.
    all: inversion r2; subst; clear r2.
    all: inversion s2; subst; clear s2.
    all: destruct hdiscr.
    all: try now rewrite eqb_refl in noteq.
    - zip fold in h1.
      eapply welltyped_context in h1; eauto.
      destruct h1 as (?&typ).
      now apply inversion_Evar in typ.
    - zip fold in h1.
      zip fold in h2.
      eapply welltyped_context in h1 as [s1 h1]; eauto.
      clear aux.
      eapply welltyped_context in h2 as [s2 h2]; eauto.
      simpl in h2.
      apply inversion_Sort in h2 as (_&h2&_); auto.
      apply inversion_Sort in h1 as (_&h1&_); auto.
      eapply abstract_env_compare_sort_correct in H0; eauto.
      destruct leq; cbn in *; easy.
      Unshelve. all:eauto.
  Qed.

  Equations _isconv (s : state) (Γ : context)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (aux : Aux s Γ t1 π1 t2 π2 h2)
  : Ret s Γ t1 π1 t2 π2 :=
    _isconv Reduction Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | _ | _ | _ := _isconv_red Γ leq t1 π1 h1 t2 π2 h2 hx aux } ;

    _isconv Term Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | r1 | r2 | _ := _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 hx r1 r2 aux } ;

    _isconv Args Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | _ | _ | _ := _isconv_args leq Γ t1 π1 h1 t2 π2 h2 hx aux } ;

    _isconv Fallback Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | r1 | r2 | hd := _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 r1 r2 hd hx aux }.

  Lemma welltyped_R_zipc Σ (wfΣ : abstract_env_ext_rel X Σ) Γ :
    forall x y : pack Γ, welltyped Σ Γ (zipc (tm1 x) (stk1 x)) -> R Γ y x -> welltyped Σ Γ (zipc (tm1 y) (stk1 y)).
  Proof using Type.
    intros x y H HR.
    pose proof (heΣ := heΣ _ wfΣ).
    pose proof (hΣ := hΣ _ wfΣ). cbn.
    sq.
    destruct x, y; cbn in *.
    red in HR. cbn in HR. red in HR. cbn in HR.
    depind HR.
    - cbn in *. specialize_Σ wfΣ.
      eapply cored'_postpone in H as [u' [cor eq]].
      eapply cored_welltyped in cor; tea.
      now destruct eq as [<-].
    - simpl in *. destruct e. now rewrite e.
  Qed.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
    : Ret s Γ t1 π1 t2 π2 :=

    isconv_full s Γ t1 π1 h1 t2 π2 h2 hx :=
      Fix_F (R := R Γ)
            (fun '(mkpack s' t1' π1' t2' π2' h2') =>
              wtp Γ t1' π1' ->
              wtp Γ t2' π2' ->
              Ret s' Γ t1' π1' t2' π2'
            )
            (fun pp f => _)
            (x := mkpack Γ s t1 π1 t2 π2 _)
            _ _ _ _.
  Next Obligation.
    unshelve eapply _isconv. all: try assumption.
    intros s' t1' π1' t2' π2' h1' h2' hx' hR.
    eapply (f (mkpack Γ s' t1' π1' t2' π2' h2')); tea.
    destruct pp. eapply R_irrelevance; tea; cbn. reflexivity.
  Defined.
  Next Obligation.
  match goal with | |- Acc _ ?X => set (u := X) end.
  revert h1.
  change ((forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ (zipc (tm1 u) (stk1 u))) -> Acc (R Γ) u).
  generalize u.
  refine (Acc_intro_generator
            (R:=R Γ)
            (P:=fun u => forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zipc (tm1 u) (stk1 u)))
            (fun x y Px Hy => _) 1000 _); intros.
  - simpl in *. eapply welltyped_R_zipc; eauto.
  - destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. eapply R_Acc; eassumption.
  Defined.

  Inductive ConversionResultSummary :=
  | ConvSuccess : ConversionResultSummary
  | ConvError : ConversionError -> ConversionResultSummary.

  Definition isconv Γ leq t1 π1 h1 t2 π2 h2 hx :=
    match isconv_full Reduction Γ t1 π1 h1 t2 π2 h2 leq hx I I I with
    | Success _ => ConvSuccess
    | Error e _ => ConvError e
    end.

  Theorem isconv_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ leq t1 π1 h1 t2 π2 h2 hx,
      isconv Γ leq t1 π1 h1 t2 π2 h2 hx = ConvSuccess ->
      conv_cum leq Σ (Γ ,,, stack_context π1) (zipp t1 π1) (zipp t2 π2).
  Proof using Type.
    unfold isconv.
    intros Σ wfΣ Γ leq t1 π1 h1 t2 π2 h2 hx.
    destruct isconv_full as [].
    - auto.
    - discriminate.
  Qed.

  Theorem isconv_complete :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ leq t1 π1 h1 t2 π2 h2 hx e,
      isconv Γ leq t1 π1 h1 t2 π2 h2 hx = ConvError e ->
      ~conv_cum leq Σ (Γ ,,, stack_context π1) (zipp t1 π1) (zipp t2 π2).
  Proof using Type.
    unfold isconv.
    intros Σ wfΣ Γ leq t1 π1 h1 t2 π2 h2 hx.
    destruct isconv_full as []; eauto.
    - intros ? [=].
    - intros. intro not; eapply h. intros.
      erewrite (abstract_env_ext_irr _ _ wfΣ) ; eauto.
      Unshelve. eauto.
  Qed.

  Program Definition isconv_term Γ leq t1 (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t1) t2 (h2 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t2) :=
    isconv Γ leq t1 [] h1 t2 [] h2 _.

  Next Obligation.
    destruct (h1 _ H), (hΣ _ H) as [wΣ].
    sq. eapply ws_cumul_ctx_pb_refl.
    fvs.
  Qed.

  Theorem isconv_term_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ leq t1 h1 t2 h2,
      isconv_term Γ leq t1 h1 t2 h2 = ConvSuccess ->
      conv_cum leq Σ Γ t1 t2.
  Proof using Type.
    intros Σ wfΣ Γ leq t1 h1 t2 h2.
    unfold isconv_term. intro h.
    eapply isconv_sound in h; eauto.
  Qed.

  Theorem isconv_term_complete :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ leq t1 h1 t2 h2 e,
      isconv_term Γ leq t1 h1 t2 h2 = ConvError e ->
      ~conv_cum leq Σ Γ t1 t2.
  Proof using Type.
    intros Σ wfΣ Γ leq t1 h1 t2 h2 e.
    unfold isconv_term. intro h.
    eapply isconv_complete in h; eauto.
  Qed.
  Transparent reduce_stack.

End Conversion.

(*
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
Definition default_normal : @normalizing_flags default_checker_flags.
now econstructor.
Defined.

Lemma test_conv :
match
  isconv_term (cf := default_checker_flags)
    (nor := default_normal)
     canonical_abstract_env_ext_impl
    {|
      referenced_impl_env_ext :=
        ({|
           universes :=
             (LevelSet.add Level.lzero LevelSet.empty, UnivConstraintSet.empty);
           declarations := []
         |}, Monomorphic_ctx);
      referenced_impl_ext_wf := TODO "foo"
    |} [] Cumul (tSort (Universe.lType (Universe.make' (Level.lzero, 0))))
    (TODO "") (tSort (Universe.lType (Universe.make' (Level.lzero, 0))))
    (TODO "")
with
| ConvSuccess => "success"
| ConvError _ => TODO "foo"
end = "success".
Proof.
  lazy. reflexivity.
Defined.
*)
