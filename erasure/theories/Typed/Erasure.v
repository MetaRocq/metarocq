From Stdlib Require Import Program.
From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Erasure.Typed Require Import ExAst.
From Equations Require Import Equations.
From MetaRocq.Erasure Require Import EArities.
From MetaRocq.Erasure Require Import EAstUtils.
From MetaRocq.Erasure Require ErasureFunction.
From MetaRocq.PCUIC Require Import PCUICArities.
From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.PCUIC Require Import PCUICCanonicity.
From MetaRocq.PCUIC Require Import PCUICConfluence.
From MetaRocq.PCUIC Require Import PCUICContextConversion.
From MetaRocq.PCUIC Require Import PCUICContexts.
From MetaRocq.PCUIC Require Import PCUICConversion.
From MetaRocq.PCUIC Require Import PCUICInductiveInversion.
From MetaRocq.PCUIC Require Import PCUICInversion.
From MetaRocq.PCUIC Require Import PCUICLiftSubst.
From MetaRocq.PCUIC Require Import PCUICNormal.
From MetaRocq.PCUIC Require Import PCUICSN.
From MetaRocq.PCUIC Require Import PCUICSR.
From MetaRocq.PCUIC Require Import PCUICSafeLemmata.
From MetaRocq.PCUIC Require Import PCUICSubstitution.
From MetaRocq.PCUIC Require Import PCUICTyping.
From MetaRocq.PCUIC Require Import PCUICValidity.
From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity.
From MetaRocq.PCUIC Require Import PCUICCumulativity.
From MetaRocq.SafeChecker Require Import PCUICSafeReduce.
From MetaRocq.SafeChecker Require Import PCUICSafeRetyping.
From MetaRocq.SafeChecker Require Import PCUICWfEnv.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import config.

Import PCUICAst.PCUICEnvTyping.
Import PCUICErrors.
Import PCUICReduction.

(* Import VectorDef.VectorNotations. *)
Set Equations Transparent.

Module P := PCUICAst.
Module Ex := ExAst.

Import PCUICAst.

Implicit Types (cf : checker_flags).
Local Existing Instance extraction_checker_flags.

Local Obligation Tactic := simpl in *; program_simplify; CoreTactics.equations_simpl;
                              try program_solve_wf.

Section FixSigmaExt.
Import ErasureFunction.

Context {X_type : abstract_env_impl}
        {X : X_type.π2.π1}
        {no : normalizing_flags}
        {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ := abstract_env_ext_wf _ wfΣ.
Local Definition HΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.


Opaque ErasureFunction.wf_reduction.
Opaque reduce_term.

Lemma sq_red_transitivity {Σ} {Γ A} B {C} :
  ∥red Σ Γ A B∥ ->
  ∥red Σ Γ B C∥ ->
  ∥red Σ Γ A C∥.
Proof.
  intros.
  sq.
  now transitivity B.
Qed.

Lemma isArity_red (Σ : global_env_ext) Γ u v :
  isArity u ->
  red Σ Γ u v ->
  isArity v.
Proof.
  intros arity_u r.
  induction r using red_rect'; [easy|].
  eapply isArity_red1; eassumption.
Qed.

Lemma isType_red_sq Σ0 (wf : ∥ wf_ext Σ0 ∥) Γ t t' :
  ∥isType Σ0 Γ t∥ ->
  ∥red Σ0 Γ t t'∥ ->
  ∥isType Σ0 Γ t'∥.
Proof.
  intros [(_ & s & typ & _)] [r].
  sq.
  eapply has_sort_isType.
  eapply subject_reduction; eauto.
Qed.

Hint Resolve isType_red_sq : erase.

Lemma isType_prod_dom Σ0 (wf : ∥ wf_ext Σ0 ∥) Γ na A B :
  ∥isType Σ0 Γ (tProd na A B)∥ ->
  ∥isType Σ0 Γ A∥.
Proof.
  intros [(_ & s & typ & _)].
  sq.
  apply inversion_Prod in typ as (s' & ? & ? & ? & ?); [|now eauto].
  now eapply lift_sorting_forget_univ, lift_sorting_forget_rel.
Qed.

Hint Resolve isType_prod_dom : erase.

Lemma isType_prod_cod Σ0 (wf : ∥ wf_ext Σ0 ∥) Γ na A B :
  ∥isType Σ0 Γ (tProd na A B)∥ ->
  ∥isType Σ0 (Γ,, vass na A) B∥.
Proof.
  intros [(_ & s & typ & _)].
  sq.
  apply inversion_Prod in typ as (s' & ? & ? & ? & ?); [|now eauto].
  now eapply has_sort_isType.
Qed.

Hint Resolve isType_prod_cod : erase.

Hint Resolve Is_conv_to_Arity_red : erase.

Hint Resolve reduce_term_sound sq existT pair : erase.

Definition is_prod_or_sort (t : term) : bool :=
  match t with
  | tProd _ _ _
  | tSort _ => true
  | _ => false
  end.

Lemma not_prod_or_sort_hnf {Σ} {wfΣ : abstract_env_ext_rel X Σ}
  {Γ : context} {t : term}
  {h : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t} :
  negb (is_prod_or_sort (hnf (X_type := X_type) Γ t h)) ->
  ~Is_conv_to_Arity Σ Γ t.
Proof.
  intros nar car.
  unfold hnf in nar.
  specialize_Σ wfΣ. pose proof (h _ wfΣ) as [C hc].
  pose proof (reduce_term_sound RedFlags.default _ _ Γ t h Σ wfΣ) as [r].
  apply PCUICWellScopedCumulativity.closed_red_red in r as r''.
  pose proof (reduce_term_complete RedFlags.default _ _ Σ wfΣ Γ t h) as wh.
  assert (H : ∥ wf Σ ∥) by now apply HΣ. destruct H.
  apply Is_conv_to_Arity_inv in car as [(?&?&?&[r'])|(?&[r'])]; auto.
  - eapply closed_red_confluence in r' as (?&r1&r2); eauto.
    apply invert_red_prod in r2 as [? [? [? ?]]]; subst; auto.
    destruct wh as [wh].
    eapply whnf_red_inv in wh; eauto.
    depelim wh.
    rewrite H in nar.
    now cbn in nar.
  - eapply closed_red_confluence in r' as (?&r1&r2); eauto.
    apply invert_red_sort in r2 as ->; auto.
    destruct wh as [wh].
    eapply whnf_red_inv in wh; eauto.
    depelim wh.
    rewrite H in nar.
    now cbn in nar.
Qed.

Inductive term_sub_ctx : context * term -> context * term -> Prop :=
| sub_prod_dom Γ na A B : term_sub_ctx (Γ, A) (Γ, tProd na A B)
| sub_prod_cod Γ na A B : term_sub_ctx (Γ,, vass na A, B) (Γ, tProd na A B)
| sub_app_arg Γ arg hd arg1 :
    In arg (decompose_app (tApp hd arg1)).2 ->
    term_sub_ctx (Γ, arg) (Γ, tApp hd arg1).

Derive Signature for term_sub_ctx.

Lemma In_app_inv {Y} (x : Y) xs ys :
  In x (xs ++ ys) ->
  In x xs \/ In x ys.
Proof.
  intros isin.
  induction xs; [easy|].
  cbn in *.
  destruct isin as [->|]; [easy|].
  apply IHxs in H.
  now destruct H.
Qed.

Lemma well_founded_term_sub_ctx : well_founded term_sub_ctx.
Proof.
  intros (Γ & t).
  induction t in Γ |- *; constructor; intros (Γs & ts) rel; try solve [inversion rel].
  - now depelim rel.
  - depelim rel.
    destruct (mkApps_elim t1 []).
    cbn in *.
    rewrite -> decompose_app_rec_mkApps, atom_decompose_app in H by assumption.
    cbn in *.
    apply In_app_inv in H.
    destruct H as [|[|]]; cbn in *; subst; [|easy|easy].
    apply (IHt1 Γ).
    destruct (firstn n l) using List.rev_ind; [easy|].
    rewrite mkApps_app.
    constructor.
    cbn.
    now rewrite -> decompose_app_rec_mkApps, atom_decompose_app.
Qed.

Context (rΣ : global_env_ext)
        (wfrΣ : rΣ ∼_ext X).

Definition erase_rel : Relation_Definitions.relation (∑ Γ t, welltyped rΣ Γ t) :=
  fun '(Γs; ts; wfs) '(Γl; tl; wfl) =>
  ∥∑m, red rΣ Γl tl m × term_sub_ctx (Γs, ts) (Γl, m)∥.

Lemma cored_prod_l (Σ : global_env_ext) Γ na A A' B :
  cored Σ Γ A A' ->
  cored Σ Γ (tProd na A B) (tProd na A' B).
Proof.
  intros cor.
  depelim cor.
  - eapply cored_red_trans; [easy|].
    now constructor.
  - apply cored_red in cor as [cor].
    eapply cored_red_trans.
    2: now apply prod_red_l.
    now apply red_prod_l.
Qed.

Lemma cored_prod_r (Σ : global_env_ext) Γ na A B B' :
  cored Σ (Γ,, vass na A) B B' ->
  cored Σ Γ (tProd na A B) (tProd na A B').
Proof.
  intros cor.
  depelim cor.
  - eapply cored_red_trans; [easy|].
    now constructor.
  - apply cored_red in cor as [cor].
    eapply cored_red_trans.
    2: now apply prod_red_r.
    now apply red_prod_r.
Qed.

Lemma well_founded_erase_rel : well_founded erase_rel.
Proof.
  intros (Γl & l & wfl).
  assert (w : ∥ wf_ext rΣ ∥) by now apply heΣ. sq.
  induction (normalization_in rΣ w wfrΣ Γl l wfl) as [l _ IH].
  remember (Γl, l) as p.
  revert wfl IH.
  replace Γl with (fst p) by (now subst).
  replace l with (snd p) by (now subst).
  clear Γl l Heqp.
  intros wfl IH.
  induction (well_founded_term_sub_ctx p) as [p _ IH'] in p, wfl, IH |- *.
  constructor.
  intros (Γs & s & wfs) [(m & mred & msub)].
  inversion msub; subst; clear msub.
  - eapply Relation_Properties.clos_rt_rtn1 in mred. inversion mred; subst.
    + rewrite H0 in wfl,mred,IH.
      apply (IH' (p.1, s)).
      { replace p with (p.1, tProd na s B) by (now destruct p; cbn in *; congruence).
        cbn.
        constructor. }
      intros y cor wfly.
      cbn in *.
      assert (Hred_prod : ∥rΣ;;; p.1 |- tProd na s B ⇝* tProd na y B ∥).
      { eapply cored_red in cor as [cor].
        constructor.
        now apply red_prod_l. }
      destruct Hred_prod.
      unshelve eapply (IH (tProd na y B)).
      3: now repeat econstructor.
      1: { eapply red_welltyped in wfl; eauto. }
      now apply cored_prod_l.
    + apply Relation_Properties.clos_rtn1_rt in X1.
      unshelve eapply (IH (tProd na s B)).
      3: now repeat econstructor.
      1: { eapply red_welltyped in wfl; eauto.
           now apply Relation_Properties.clos_rtn1_rt in mred. }
      eapply red_neq_cored.
      { now apply Relation_Properties.clos_rtn1_rt in mred. }
      intros eq.
      destruct p as [Γ t];cbn in *;subst.
      eapply cored_red_trans in X0; eauto.
      eapply ErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalization_in; eauto.
  - eapply Relation_Properties.clos_rt_rtn1 in mred; inversion mred; subst.
    + apply (IH' (p.1,, vass na A, s)).
      { replace p with (p.1, tProd na A s) by (destruct p; cbn in *; congruence).
        cbn.
        now constructor. }
      intros y cor wfly.
      cbn in *.
      eapply cored_red in cor as Hcored.
      destruct Hcored.
      unshelve eapply IH.
      4: { constructor.
           eexists.
           split; try easy.
           constructor. }
      1: { eapply red_welltyped; eauto.
           rewrite H0.
           now apply red_prod. }
      rewrite H0.
      now apply cored_prod_r.
    + apply Relation_Properties.clos_rtn1_rt in X1.
      unshelve eapply IH.
      4: { constructor.
           eexists.
           split; try easy.
           constructor. }
      1: { eapply red_welltyped in wfl; eauto.
           now apply Relation_Properties.clos_rtn1_rt in mred. }
      eapply red_neq_cored.
      { now apply Relation_Properties.clos_rtn1_rt in mred. }
      intros eq.
      destruct p as [Γ t];cbn in *;subst.
      eapply cored_red_trans in X0; eauto.
      eapply ErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalization_in; eauto.
  - eapply Relation_Properties.clos_rt_rtn1 in mred; inversion mred; subst.
    + apply (IH' (p.1, s)).
      { replace p with (p.1, tApp hd arg1) by (destruct p; cbn in *; congruence).
        now constructor. }
      intros y cor wfly.
      destruct (mkApps_elim hd []).
      cbn in *.
      rewrite -> decompose_app_rec_mkApps, atom_decompose_app in H0 by assumption.
      change (tApp ?hd ?arg) with (mkApps hd [arg]) in *.
      rewrite <- mkApps_app in *.
      set (args := (firstn n l ++ [arg1])%list) in *.
      clearbody args.
      cbn in *.
      assert (cor1 : cored rΣ p.1 y s) by easy.
      eapply cored_red in cor as [cor].

      apply In_split in H0 as (args_pref & args_suf & ->).
      unshelve eapply (IH (mkApps f (args_pref ++ y :: args_suf))).
      3: { constructor.
           econstructor.
           split; [easy|].
           destruct args_suf using rev_ind.
           - rewrite mkApps_app.
             constructor.
             cbn.
             rewrite -> decompose_app_rec_mkApps, atom_decompose_app by auto.
             cbn.
             now apply in_or_app; right; left.
           - rewrite <- app_tip_assoc, app_assoc.
             rewrite mkApps_app.
             constructor.
             cbn.
             rewrite -> decompose_app_rec_mkApps, atom_decompose_app by auto.
             cbn.
             apply in_or_app; left.
             apply in_or_app; left.
             now apply in_or_app; right; left. }
      1: { eapply red_welltyped in wfl; eauto.
           rewrite H1.
           apply red_mkApps; [easy|].
           apply All2_app; [now apply All2_refl|].
           constructor; [easy|].
           now apply All2_refl. }

      depelim cor1; cycle 1.
      * eapply cored_red in cor1 as [cor1].
        eapply cored_red_trans.
        2: apply PCUICReduction.red1_mkApps_r.
        2: eapply OnOne2_app.
        2: now constructor.
        rewrite H1.
        apply red_mkApps; [easy|].
        apply All2_app; [now apply All2_refl|].
        constructor; [easy|].
        now apply All2_refl.
      * rewrite H1.
        constructor.
        apply PCUICReduction.red1_mkApps_r.
        eapply OnOne2_app.
        now constructor.
    + apply Relation_Properties.clos_rtn1_rt in X1.
      unshelve eapply (IH (tApp hd arg1)).
      3: { constructor.
           eexists.
           split; try easy.
           now constructor. }
      1: { eapply red_welltyped in wfl; eauto.
           etransitivity; [exact X1|].
           now constructor. }
      apply red_neq_cored.
      { etransitivity; [exact X1|].
        now constructor. }
      intros eq.
      destruct p;cbn in *;subst.
      eapply cored_red_trans in X0; eauto.
      eapply ErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalization_in; eauto.
Qed.

Instance WellFounded_erase_rel : WellFounded erase_rel :=
  Wf.Acc_intro_generator 1000 well_founded_erase_rel.
Opaque WellFounded_erase_rel.

Hint Constructors term_sub_ctx : erase.

Inductive fot_view : term -> Type :=
| fot_view_prod na A B : fot_view (tProd na A B)
| fot_view_sort univ : fot_view (tSort univ)
| fot_view_other t : negb (is_prod_or_sort t) -> fot_view t.

Equations fot_viewc (t : term) : fot_view t :=
fot_viewc (tProd na A B) := fot_view_prod na A B;
fot_viewc (tSort univ) := fot_view_sort univ;
fot_viewc t := fot_view_other t _.

Lemma tywt {Γ T Σ0} (isT : ∥isType Σ0 Γ T∥) : welltyped Σ0 Γ T.
Proof. destruct isT. now apply isType_welltyped. Qed.

(** Definition of normalized arities *)
Definition arity_ass := aname * term.

Fixpoint mkNormalArity (l : list arity_ass) (s : sort) : term :=
  match l with
  | []%list => tSort s
  | ((na, A) :: l)%list => tProd na A (mkNormalArity l s)
  end.

Lemma isArity_mkNormalArity l s :
  isArity (mkNormalArity l s).
Proof.
  induction l as [|(na & A) l IH]; cbn; auto.
Qed.

Record conv_arity {Σ Γ T} : Type := build_conv_arity {
  conv_ar_context : list arity_ass;
  conv_ar_univ : sort;
  conv_ar_red : ∥closed_red Σ Γ T (mkNormalArity conv_ar_context conv_ar_univ)∥
}.

Global Arguments conv_arity : clear implicits.

Definition conv_arity_or_not Σ Γ T : Type :=
  (conv_arity Σ Γ T) + (~∥conv_arity Σ Γ T∥).

Definition Is_conv_to_Sort Σ Γ T : Prop :=
  exists univ, ∥red Σ Γ T (tSort univ)∥.

Definition is_sort {Σ Γ T} (c : conv_arity_or_not Σ Γ T) : option (Is_conv_to_Sort Σ Γ T).
Proof.
  destruct c as [c|not_conv_ar].
  - destruct c as [[|(na & A) ctx] univ r].
    + apply Some.
      sq. destruct r.
      eexists. easy.
    + exact None.
  - exact None.
Defined.

Import PCUICSigmaCalculus.

Lemma red_it_mkProd_or_LetIn_smash_context Σ Γ Δ t :
  red Σ Γ
      (it_mkProd_or_LetIn Δ t)
      (it_mkProd_or_LetIn (smash_context []%list Δ) (expand_lets Δ t)).
Proof.
  induction Δ in Γ, t |- * using PCUICInduction.ctx_length_rev_ind; cbn.
  - now rewrite expand_lets_nil.
  - change (Γ0 ++ [d]) with ([d],,, Γ0).
    rewrite smash_context_app_expand.
    destruct d as [na [b|] ty]; cbn.
    + unfold app_context.
      rewrite -> expand_lets_vdef, it_mkProd_or_LetIn_app, app_nil_r.
      cbn.
      rewrite -> lift0_context, lift0_id, subst_empty.
      rewrite subst_context_smash_context.
      cbn.
      etransitivity.
      { apply red1_red.
        apply red_zeta. }
      unfold subst1.
      rewrite subst_it_mkProd_or_LetIn.
      rewrite Nat.add_0_r.
      apply X0.
      now rewrite subst_context_length.
    + unfold app_context.
      rewrite -> expand_lets_vass, !it_mkProd_or_LetIn_app.
      cbn.
      apply red_prod_r.
      rewrite -> subst_context_lift_id by lia.
      rewrite lift0_context.
      now apply X0.
Qed.

Global Arguments conv_arity : clear implicits.

Lemma conv_arity_Is_conv_to_Arity {Σ Γ T} :
  conv_arity Σ Γ T ->
  Is_conv_to_Arity Σ Γ T.
Proof.
  intros [asses univ r].
  eexists.
  split; [sq|];tea.
  apply isArity_mkNormalArity.
Qed.

Lemma Is_conv_to_Arity_conv_arity {Σ : global_env_ext} {Γ T} :
  ∥ wf Σ ∥ ->
  Is_conv_to_Arity Σ Γ T ->
  ∥conv_arity Σ Γ T∥.
Proof.
  intros wfΣ (t & [r] & isar).
  sq.
  destruct (destArity [] t) as [(ctx & univ)|] eqn:dar.
  + set (ctx' := rev_map (fun d => (decl_name d, decl_type d)) (smash_context [] ctx)).
    apply (build_conv_arity _ _ _ ctx' univ).
    apply PCUICWellScopedCumulativity.closed_red_red in r as r'.
    sq.
    transitivity t;tea.
    apply PCUICLiftSubst.destArity_spec_Some in dar.
    cbn in dar.
    subst.
    replace (mkNormalArity ctx' univ) with (it_mkProd_or_LetIn (smash_context [] ctx) (tSort univ)).
    { destruct r.
      assert (PCUICOnFreeVars.on_free_vars (PCUICOnFreeVars.shiftnP #|Γ| (fun _ : nat => false)) (it_mkProd_or_LetIn ctx (tSort univ))) by (eapply PCUICClosedTyp.red_on_free_vars;eauto;
        now rewrite PCUICOnFreeVars.on_free_vars_ctx_on_ctx_free_vars).
      constructor;auto.
      apply red_it_mkProd_or_LetIn_smash_context. }
    subst ctx'.
    pose proof (@smash_context_assumption_context [] ctx assumption_context_nil).
    clear -H.
    induction (smash_context [] ctx) using List.rev_ind; [easy|].
    rewrite -> it_mkProd_or_LetIn_app in *.
    rewrite rev_map_app.
    cbn.
    apply assumption_context_app in H as (? & ass_x).
    depelim ass_x.
    cbn.
    f_equal.
    now apply IHc.
  + exfalso.
    clear -isar dar.
    revert dar.
    generalize ([] : context).
    induction t; intros ctx; cbn in *; eauto; try congruence.
Qed.

Definition is_arity {Σ : global_env_ext} {Γ T} (wfΣ : ∥ wf Σ ∥) (c : conv_arity_or_not Σ Γ T) :
  {Is_conv_to_Arity Σ Γ T} + {~Is_conv_to_Arity Σ Γ T}.
Proof.
  destruct c; [left|right].
  - eapply conv_arity_Is_conv_to_Arity;eauto.
  - abstract (intros conv; apply Is_conv_to_Arity_conv_arity in conv; tauto).
Defined.

(** type_flag of a term indexed by the term's type. For example, for
      t    :   T
   eq_refl : 5 = 5 : Prop
   we would pass T to flag_of_type below, and it would give
   is_logical = true, conv_ar = right _. On the other hand, for
   (fun (X : Type) => X) : Type -> Type
   we would pass Type -> Type and get is_logical = false, conv_ar = left _.
*)
Record type_flag {Σ Γ T} :=
  build_flag
    { (** Type is proposition when fully applied, i.e. either
         (T : Prop, or T a0 .. an : Prop). If this is an arity,
         indicates whether this is a logical arity (i.e. into Prop). *)
      is_logical : bool;
      (** Arity that this type is convertible to *)
      conv_ar : conv_arity_or_not Σ Γ T;
    }.

Global Arguments type_flag : clear implicits.

Hint Resolve abstract_env_wf : erase.

Definition isTT Γ T :=
  forall Σ0 (wfΣ : abstract_env_ext_rel X Σ0), ∥isType Σ0 Γ T∥.

Equations(noeqns) flag_of_type (Γ : context) (T : term)
         (isT : forall Σ0 (wfΣ : abstract_env_ext_rel X Σ0), ∥isType Σ0 Γ T∥)
  : type_flag rΣ Γ T
  by wf ((Γ;T; (tywt (isT rΣ wfrΣ))) : (∑ Γ t, welltyped rΣ Γ t)) erase_rel :=
flag_of_type Γ T isT with inspect (hnf (X_type := X_type) Γ T (fun Σ h => (tywt (isT Σ h)))) :=
  | exist T0 is_hnf with fot_viewc T0 := {
    | fot_view_prod na A B with flag_of_type (Γ,, vass na A) B _ := {
      | flag_cod := {| is_logical := is_logical flag_cod;
                       conv_ar := match conv_ar flag_cod with
                                  | inl car =>
                                    inl {| conv_ar_context := (na, A) :: conv_ar_context car;
                                           conv_ar_univ := conv_ar_univ car |}
                                  | inr notar => inr _
                                  end
                    |}
      };
    | fot_view_sort univ := {| is_logical := Sort.is_prop univ;
                               conv_ar := inl {| conv_ar_context := [];
                                                 conv_ar_univ := univ; |} |} ;
    | fot_view_other T0 discr
        with infer X_type X Γ _ T0 _ :=
        {
      | @existT K princK with inspect (reduce_to_sort Γ K _) := {
        | exist (Checked_comp (existT _ univ red_univ)) eq :=
          {| is_logical := Sort.is_prop univ;
             conv_ar := inr _ |};
        | exist (TypeError_comp t) eq := !
        };
      } ;
    }.
Ltac reduce_term_sound :=
  unfold hnf in *;
  match goal with
  | [H : reduce_term ?flags _ _ ?Γ ?t ?wft = ?a |- _] =>
      let r := fresh "r" in
      pose proof (@reduce_term_sound _ _ flags _ _ _ Γ t wft _ (ltac:(eassumption))) as [r];
      rewrite -> H in r
  end.

Next Obligation.
  assert ( ∥ wf_ext Σ0 ∥) by now apply heΣ.
  reduce_term_sound.
  apply PCUICWellScopedCumulativity.closed_red_red in r;eauto with erase.
Qed.
Next Obligation.
  reduce_term_sound.
  apply PCUICWellScopedCumulativity.closed_red_red in r;eauto with erase.
Qed.
Next Obligation.
  reduce_term_sound.
  destruct car as [ctx univ [r']].
  cbn.
  constructor.
  transitivity (tProd na A B). auto.
  now apply closed_red_prod_codom.
Qed.
Next Obligation.
  reduce_term_sound.
  contradiction notar.
  assert (Hwf : ∥ wf rΣ ∥) by now apply HΣ.
  apply Is_conv_to_Arity_conv_arity;sq;auto.
  specialize r as r'.
  destruct r'.
  assert (prod_conv : Is_conv_to_Arity rΣ Γ (tProd na A B)).
  { eapply Is_conv_to_Arity_red;eauto.
    apply conv_arity_Is_conv_to_Arity;assumption. }
  destruct prod_conv as [tm [[redtm] ar]].
  apply invert_red_prod in redtm.
  destruct redtm as [A' [B' [-> [redAA' redBB']]]].
  exists B'; easy.
Qed.
Next Obligation.
  remember (hnf _ _ _) as b. symmetry in Heqb.
  reduce_term_sound; eauto with erase.
Qed.
Next Obligation.
  specialize (isT Σ wfΣ) as isT'.
  sq. destruct isT' as (_ & u & Htype & _).
  now eapply typing_wf_local.
Qed.
Next Obligation.
  apply well_sorted_wellinferred.
  assert (Hwf : ∥ wf_ext Σ ∥) by now apply heΣ.
  destruct Hwf.
  remember (hnf Γ T _) as nf. symmetry in Heqnf.
  reduce_term_sound.
  assert (tyT : ∥ isType Σ Γ T ∥) by eauto.
  assert (tyNf : ∥ isType Σ Γ nf ∥).
  { sq. eapply isType_red;eauto.
    now apply PCUICWellScopedCumulativity.closed_red_red. }
  sq.
  now apply BDFromPCUIC.isType_infering_sort.
Defined.
Next Obligation.
  remember (hnf Γ T _) as nf. symmetry in Heqnf.
  reduce_term_sound.
  specialize (princK Σ wfΣ) as HH.
  assert (∥ wf Σ ∥) by now apply HΣ.
  assert (tyT : ∥ isType Σ Γ T ∥) by eauto.
  assert (tyNf : ∥ isType Σ Γ nf ∥).
  { sq. eapply isType_red;eauto.
    now apply PCUICWellScopedCumulativity.closed_red_red. }
  sq.
  destruct tyT as (_ & u & tyT & _).
  apply typing_wf_local in tyT.
  apply BDToPCUIC.infering_typing in HH;sq;eauto.
  eapply isType_welltyped.
  eapply validity; eauto.
Qed.
Next Obligation.
  clear eq.
  specialize (@not_prod_or_sort_hnf rΣ wfrΣ _ _ _ discr) as d.
  clear red_univ.
  remember (hnf Γ T _) as nf. symmetry in Heqnf.
  reduce_term_sound.
  destruct r.
  destruct H as [car].
  apply conv_arity_Is_conv_to_Arity in car;eauto.
Qed.
Next Obligation.
  pose proof (PCUICSafeReduce.reduce_to_sort_complete _ wfrΣ _ _ eq).
  clear eq.
  apply (@not_prod_or_sort_hnf rΣ wfrΣ) in discr.
  remember (hnf Γ T _) as nf. symmetry in Heqnf.
  reduce_term_sound.
  destruct r.
  specialize (princK rΣ wfrΣ) as HH.
  assert (∥ wf rΣ ∥) by now apply HΣ.
  assert (∥ wf_ext rΣ ∥) by now apply heΣ.
  assert (tyT : ∥ isType rΣ Γ T ∥) by eauto.
  assert (tyNf : ∥ isType rΣ Γ nf ∥).
  { sq. eapply isType_red;eauto. }
  sq.
  destruct tyT as (_ & u & tyT & _).
  destruct tyNf as (_ & v & tyNf & _).
  apply typing_wf_local in tyT.
  apply BDToPCUIC.infering_typing in HH;sq;eauto.
  specialize (PCUICPrincipality.common_typing _ _ HH tyNf) as [x[x_le_K[x_le_sort?]]].
  apply ws_cumul_pb_Sort_r_inv in x_le_sort as (? & x_red & ?).
  specialize (ws_cumul_pb_red_l_inv _ x_le_K x_red) as K_ge_sort.
  apply ws_cumul_pb_Sort_l_inv in K_ge_sort as (? & K_red & ?).
  exact (H _ K_red).
Qed.

Equations erase_type_discr (t : term) : Prop := {
  | tRel _ := False;
  | tSort _ := False;
  | tProd _ _ _ := False;
  | tApp _ _ := False;
  | tConst _ _ := False;
  | tInd _ _ := False;
  | _ := True
  }.

Inductive erase_type_view : term -> Type :=
| et_view_rel i : erase_type_view (tRel i)
| et_view_sort u : erase_type_view (tSort u)
| et_view_prod na A B : erase_type_view (tProd na A B)
| et_view_app hd arg : erase_type_view (tApp hd arg)
| et_view_const kn u : erase_type_view (tConst kn u)
| et_view_ind ind u : erase_type_view (tInd ind u)
| et_view_other t : erase_type_discr t -> erase_type_view t.

Equations erase_type_viewc (t : term) : erase_type_view t := {
  | tRel i := et_view_rel i;
  | tSort u := et_view_sort u;
  | tProd na A B := et_view_prod na A B;
  | tApp hd arg := et_view_app hd arg;
  | tConst kn u := et_view_const kn u;
  | tInd ind u := et_view_ind ind u;
  | t := et_view_other t _
  }.

Inductive tRel_kind :=
(** tRel refers to type variable n in the list of type vars *)
| RelTypeVar (n : nat)
(** tRel refers to an inductive type (used in constructors of inductives) *)
| RelInductive (ind : inductive)
(** tRel refers to something else, for example something logical or a value *)
| RelOther.

Import VectorDef.VectorNotations.
Open Scope list_scope.

Equations(noeqns) erase_type_aux
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (isT : forall Σ (wfΣ : PCUICWfEnv.abstract_env_ext_rel X Σ), ∥isType Σ Γ t∥)
          (** The index of the next type variable that is being
              produced, or None if no more type variables should be
              produced (when not at the top level). For example, in
              Type -> nat we should erase to nat with one type var,
              while in (Type -> nat) -> nat we should erase to (TBox ->
              nat) -> nat with no type vars. *)
          (next_tvar : option nat) : list name × box_type
  by wf ((Γ; t; (tywt (isT rΣ wfrΣ))) : (∑ Γ t, welltyped rΣ Γ t)) erase_rel :=
erase_type_aux Γ erΓ t isT next_tvar
  with inspect (reduce_term RedFlags.nodelta X_type X Γ t (fun Σ h => (tywt (isT Σ h)))) :=

  | exist t0 eq_hnf with is_logical (flag_of_type Γ t0 _) := {

    | true := ([], TBox);

    | false with erase_type_viewc t0 := {

      | et_view_rel i with @Vector.nth_order _ _ erΓ i _ := {
        | RelTypeVar n := ([], TVar n);
        | RelInductive ind := ([], TInd ind);
        | RelOther := ([], TAny)
        };

      | et_view_sort _ := ([], TBox);

      | et_view_prod na A B with flag_of_type Γ A _ := {
          (** For logical things we just box and proceed *)
        | {| is_logical := true |} =>
          on_snd
            (TArr TBox)
            (erase_type_aux (Γ,, vass na A) (RelOther :: erΓ)%vector B _ next_tvar);

          (** If the type isn't an arity now, then the domain is a "normal" type like nat. *)
        | {| conv_ar := inr _ |} :=
          let '(_, dom) := erase_type_aux Γ erΓ A _ None in
          on_snd
            (TArr dom)
            (erase_type_aux (Γ,, vass na A) (RelOther :: erΓ)%vector B _ next_tvar);

        (** Ok, so it is an arity. We add type variables for all
            arities (even non-sorts) because more things are typable without
            coercions this way. In particular, type schemes only used
            in contravariant positions extract to something typable
            even without higher-kinded types. For example:
            Definition test (T : Type -> Type) (x : T nat) (y : T bool) : nat := 0.
            Definition bar := test option None None.
            Here [bar] is perfectly extractable without coercions if T becomes a type
            variable. *)

        | _ =>
          let var :=
              match next_tvar with
              | Some i => RelTypeVar i
              | None => RelOther
              end in
          let '(tvars, cod) :=
              erase_type_aux
                (Γ,, vass na A) (var :: erΓ)%vector
                B _
                (option_map S next_tvar) in
          (if next_tvar then binder_name na :: tvars else tvars, TArr TBox cod)
        };

      | et_view_app orig_hd orig_arg with inspect (decompose_app (tApp orig_hd orig_arg)) := {
        | exist (hd, decomp_args) eq_decomp :=

          let hdbt :=
              match hd as h return h = hd -> _ with
              | tRel i =>
                fun _ =>
                  match @Vector.nth_order _ _ erΓ i _ with
                  | RelInductive ind => TInd ind
                  | RelTypeVar i => TVar i
                  | RelOther => TAny
                  end
              | tConst kn _ => fun _ => TConst kn
              | tInd ind _ => fun _ => TInd ind
              | _ => fun _ => TAny
              end eq_refl in

          (** Now for heads that can take args, add args.
              Otherwise drop all args. *)
          if can_have_args hdbt then
            let erase_arg (a : term) (i : In a decomp_args) : box_type :=
                let (aT, princaT) := infer X_type X Γ _ a _ in
                match flag_of_type Γ aT _ with
                | {| is_logical := true |} => TBox
                | {| conv_ar := car |} =>
                  match is_sort car with
                  | Some conv_sort => snd (erase_type_aux Γ erΓ a _ None)
                  | None => TAny (* non-sort arity or value *)
                  end
                end in
            ([], mkTApps hdbt (map_In decomp_args erase_arg))
          else
            ([], hdbt)
        };

      | et_view_const kn _ := ([], TConst kn);

      | et_view_ind ind _ := ([], TInd ind);

      | et_view_other t0 _ := ([], TAny)

      }
    }.
Ltac wfAbstractEnv :=
match goal with
  | [H : ?Σ ∼_ext ?X |- _] =>
      pose proof (@abstract_env_ext_wf _ _ _ _ _ X Σ H)
  end.
Solve All Obligations with
  Tactics.program_simplify;
  CoreTactics.equations_simpl; try (reduce_term_sound; destruct r); wfAbstractEnv; eauto with erase.
Next Obligation.
  remember (reduce_term _ _ _ _ _ _) as _b;symmetry in Heq_b.
  reduce_term_sound; destruct r; epose abstract_env_ext_wf; eauto with erase.
Qed.
Next Obligation.
  reduce_term_sound.
  destruct (isT _ wfrΣ) as [(_ & ? & typ & _)].
  assert (∥ wf rΣ ∥) by now apply HΣ. sq.
  destruct r.
  eapply subject_reduction with (u := tRel i) in typ; eauto.
  apply inversion_Rel in typ as (? & _ & ? & _);[|easy].
  now apply nth_error_Some.
Qed.
Next Obligation.
  destruct (isT _ wfrΣ) as [(_ & ? & typ & _)].
  assert (∥ wf rΣ ∥) by eauto using HΣ;sq.
  reduce_term_sound;destruct r.
  eapply subject_reduction in typ; eauto.
  replace (tApp orig_hd orig_arg) with (mkApps (tRel i) decomp_args) in typ; cycle 1.
  { symmetry. apply decompose_app_inv.
    now rewrite <- eq_decomp. }
  apply inversion_mkApps in typ.
  destruct typ as (rel_type & rel_typed & spine).
  apply inversion_Rel in rel_typed; [|easy].
  apply nth_error_Some.
  destruct rel_typed as (? & _ & ? & _).
  congruence.
Qed.
Next Obligation.
  specialize (isT _ wfΣ) as isT'.
  sq. destruct isT' as (_ & u & Htype & _).
  now eapply typing_wf_local.
Qed.
Next Obligation.
  destruct (isT _ wfΣ) as [(_ & ? & typ & _)].
  assert (w : ∥ wf Σ ∥) by eauto using HΣ;sq.
  reduce_term_sound;destruct r.
  eapply subject_reduction in typ; eauto.
  replace (tApp orig_hd orig_arg) with (mkApps hd decomp_args) in typ; cycle 1.
  { symmetry. apply decompose_app_inv.
    now rewrite <- eq_decomp. }
  apply inversion_mkApps in typ.
  destruct typ as (? & ? & spine).
  sq.
  clear -spine i w.
  induction spine; [easy|].
  destruct i.
  + subst a.
    eapply BDFromPCUIC.typing_infering in t.
    destruct t as (? & ? & ?).
    econstructor;eauto.
  + easy.
Qed.
Next Obligation.
  clear eq_hnf.
  destruct (princaT _ wfΣ) as [inf_aT].
  assert (HH : ∥ wf_ext Σ0 ∥) by now apply heΣ.
  destruct HH.
  specialize (isT _ wfΣ) as [(_ & ? & Hty & _)].
  apply typing_wf_local in Hty.
  apply BDToPCUIC.infering_typing in inf_aT;eauto with erase.
  sq.
  now eapply validity.
Qed.
Next Obligation.
  clear eq_hnf.
  assert (rΣ = Σ).
  { eapply abstract_env_ext_irr;eauto. }
  subst.
  destruct (princaT _ wfΣ) as [inf_aT].
  assert (HH : ∥ wf_ext Σ ∥) by now apply heΣ.
  destruct HH.
  specialize (isT _ wfΣ) as [(_ & ? & Hty & _)].
  apply typing_wf_local in Hty.
  apply BDToPCUIC.infering_typing in inf_aT;eauto with erase.
  destruct conv_sort as (univ & reduniv).
  sq.
  eapply has_sort_isType.
  eapply type_reduction;eauto.
Qed.
Next Obligation.
  reduce_term_sound;destruct r.
  sq.
  exists (tApp orig_hd orig_arg).
  split; [easy|].
  constructor.
  rewrite eq_decomp.
  easy.
Qed.

Definition erase_type (t : term) (isT :forall Σ (wfΣ : PCUICWfEnv.abstract_env_ext_rel X Σ), ∥isType Σ [] t∥) : list name × box_type :=
  erase_type_aux [] []%vector t isT (Some 0).

Lemma typwt {Γ t T} Σ0 :
  ∥Σ0 ;;; Γ |- t : T∥ ->
  welltyped Σ0 Γ t.
Proof.
  intros [typ].
  econstructor; eauto.
Qed.

Inductive erase_type_scheme_view : term -> Type :=
| erase_type_scheme_view_lam na A B : erase_type_scheme_view (tLambda na A B)
| erase_type_scheme_view_other t : negb (isLambda t) -> erase_type_scheme_view t.

Equations erase_type_scheme_viewc (t : term) : erase_type_scheme_view t :=
erase_type_scheme_viewc (tLambda na A B) := erase_type_scheme_view_lam na A B;
erase_type_scheme_viewc t := erase_type_scheme_view_other t _.

Definition type_var_info_of_flag (na : aname) {Σ : global_env_ext} {Γ t} (w : ∥ wf Σ ∥) (f : type_flag Σ Γ t) : type_var_info :=
  {| tvar_name := binder_name na;
     tvar_is_logical := is_logical f;
     tvar_is_arity := if is_arity w (conv_ar f) then true else false;
     tvar_is_sort := if is_sort (conv_ar f) then true else false; |}.

(** For a non-lambda type scheme, i.e.
    t : T1 -> T2 -> ... -> Tn -> Type
    where t is not a lambda, finish erasing it as a type scheme
    by repeatedly eta expanding it *)
Equations (noeqns) erase_type_scheme_eta
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (ar_ctx : list arity_ass)
          (ar_univ : sort)
          (typ : ∥rΣ;;; Γ |- t : mkNormalArity ar_ctx ar_univ∥)
          (next_tvar : nat) : list type_var_info × box_type :=
erase_type_scheme_eta Γ erΓ t [] univ typ next_tvar => ([], (erase_type_aux Γ erΓ t _ None).2);
erase_type_scheme_eta Γ erΓ t ((na, A) :: ar_ctx) univ typ next_tvar =>
let inf := type_var_info_of_flag na (HΣ _ wfrΣ) (flag_of_type Γ A _) in
let (kind, new_next_tvar) :=
    if tvar_is_arity inf then
      (RelTypeVar next_tvar, S next_tvar)
    else
      (RelOther, next_tvar) in
let '(infs, bt) := erase_type_scheme_eta
                     (Γ,, vass na A)
                     (kind :: erΓ)%vector
                     (tApp (lift0 1 t) (tRel 0))
                     ar_ctx univ _
                     new_next_tvar in
(inf :: infs, bt).
Next Obligation.
  assert (H : rΣ = Σ).
  { eapply abstract_env_ext_irr;eauto. }
  rewrite <- H.
  destruct typ.
  assert (wf_local rΣ Γ) by (eapply typing_wf_local; eauto).
  assert (∥ wf rΣ ∥) by now apply HΣ .
  constructor; eapply has_sort_isType;eassumption.
Qed.
Next Obligation.
  destruct typ as [typ].
  assert (H : rΣ = Σ0).
  { eapply abstract_env_ext_irr;eauto. }
  rewrite <- H.
  assert (wf_local rΣ Γ) by (eapply typing_wf_local; eauto).
  assert (∥ wf rΣ ∥) by now apply HΣ . sq.
  apply validity in typ; auto.
  apply isType_tProd in typ; auto.
  exact (fst typ).
Qed.
Next Obligation.
  assert (∥ wf rΣ ∥) by now apply HΣ . sq.
  apply typing_wf_local in typ as wfl.
  assert (wflext : wf_local rΣ (Γ,, vass na A)).
  { apply validity in typ; auto.
    apply isType_tProd in typ as (_ & typ); auto.
    eapply isType_wf_local; eauto. }
  rewrite <- (subst_rel0_lift_id 0 (mkNormalArity ar_ctx univ)).
  eapply validity in typ as typ_valid;auto.
  destruct typ_valid as (_ & u & Hty & _).
  eapply type_App.
  + eapply validity in typ as (_ & ? & typ & _);auto.
    eapply (PCUICWeakeningTyp.weakening _ _ [_] _ _ _ wflext Hty).
  + eapply (PCUICWeakeningTyp.weakening _ _ [_] _ _ _ wflext typ).
  + fold lift.
    eapply (type_Rel _ _ _ (vass na A)); auto.
Qed.

Equations? (noeqns) erase_type_scheme
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (ar_ctx : list arity_ass)
          (ar_univ : sort)
          (typ : forall Σ0 (wfΣ : PCUICWfEnv.abstract_env_ext_rel X Σ0), ∥Σ0;;; Γ |- t : mkNormalArity ar_ctx ar_univ∥)
          (next_tvar : nat) : list type_var_info × box_type :=
erase_type_scheme Γ erΓ t [] univ typ next_tvar => ([], (erase_type_aux Γ erΓ t _ None).2);
erase_type_scheme Γ erΓ t ((na', A') :: ar_ctx) univ typ next_tvar
  with inspect (reduce_term RedFlags.nodelta X_type X Γ t (fun Σ0 h => (typwt _ (typ Σ0 h)))) := {
  | exist thnf eq_hnf with erase_type_scheme_viewc thnf := {
    | erase_type_scheme_view_lam na A body =>
      let inf := type_var_info_of_flag na (HΣ _ wfrΣ) (flag_of_type Γ A _) in
      let (kind, new_next_tvar) :=
          if tvar_is_arity inf then
            (RelTypeVar next_tvar, S next_tvar)
          else
            (RelOther, next_tvar) in
      let '(infs, bt) := erase_type_scheme
                          (Γ,, vass na A) (kind :: erΓ)%vector
                          body ar_ctx univ _ new_next_tvar in
      (inf :: infs, bt);
    | erase_type_scheme_view_other thnf _ =>
      erase_type_scheme_eta Γ erΓ t ((na', A') :: ar_ctx) univ (typ _ wfrΣ) next_tvar
    }
  }.
Proof.
  - destruct (typ _ wfΣ).
    constructor; eapply has_sort_isType; eauto.
  - destruct (typ _ wfΣ) as [typ0].
    reduce_term_sound.
    assert (∥ wf Σ0 ∥) by now apply HΣ.
    sq.
    destruct r as [?? r].
    eapply subject_reduction in r; eauto.
    apply inversion_Lambda in r as (?&h1&?&?); auto.
    eapply isTypeRel_isType in h1; auto.
  - clear inf.
    destruct (typ _ wfΣ) as [typ0].
    reduce_term_sound.
    assert (∥ wf Σ0 ∥) by now apply HΣ.
    sq.
    destruct r as [?? r].
    assert (rΣ = Σ0).
    { eapply abstract_env_ext_irr;eauto. }
    subst.
    eapply subject_reduction in r; eauto.
    apply inversion_Lambda in r as (?&?&?&c); auto.
    assert (wf_local Σ0 Γ) by (eapply typing_wf_local; eauto).
    apply ws_cumul_pb_Prod_Prod_inv_l in c as [???]; auto.
    eapply validity in typ0 as typ0; auto.
    apply isType_tProd in typ0 as (_ & (_&u&?&_)); auto.
    assert (PCUICCumulativity.conv_context cumulAlgo_gen Σ0 (Γ,, vass na' A') (Γ,, vass na A)).
    { constructor; [reflexivity|].
      constructor. now symmetry.
      apply ws_cumul_pb_forget_conv. now symmetry.
    }
    eapply type_Cumul.
    + eassumption.
    + eapply PCUICContextConversionTyp.context_conversion; eauto.
    + now apply cumulAlgo_cumulSpec.
Qed.

Import ExAst.

Equations? erase_arity
         (cst : PCUICEnvironment.constant_body)
         (car : conv_arity rΣ [] (PCUICEnvironment.cst_type cst))
         (wt : ∥on_constant_decl (lift_typing typing) rΣ cst∥)
  : option (list type_var_info × box_type) :=
  erase_arity cst car wt with inspect (PCUICEnvironment.cst_body cst) := {
    | exist (Some body) body_eq =>
                Some (erase_type_scheme [] []%vector body (conv_ar_context car) (conv_ar_univ car) _ 0);
    | exist None _ => None
    }.
Proof.
  unfold on_constant_decl in wt.
  rewrite body_eq in wt.
  cbn in *.
  assert (rΣ = Σ0).
  { eapply abstract_env_ext_irr;eauto. }
  subst.
  assert (∥ wf Σ0 ∥) by now apply HΣ.
  destruct car as [ctx univ r].
  sq.
  apply unlift_TermTyp in wt.
  eapply type_reduction in wt; eauto;cbn.
  now destruct r.
Qed.

Equations? erase_constant_decl
          (cst : PCUICEnvironment.constant_body)
          (wt : ∥on_constant_decl (lift_typing typing) rΣ cst∥)
  : constant_body + option (list type_var_info × box_type) :=
erase_constant_decl cst wt with flag_of_type [] (PCUICEnvironment.cst_type cst) _ := {
    | {| conv_ar := inl car |} =>
        inr (erase_arity cst car wt)
    | {| conv_ar := inr notar |} =>
        let erased_body := erase_constant_body X_type X (normalization_in := normalization_in) cst _ in
        inl {| cst_type := erase_type (PCUICEnvironment.cst_type cst) _; cst_body := EAst.cst_body (fst erased_body) |}
    }.
Proof.
  - assert (rΣ = Σ0).
    { eapply abstract_env_ext_irr;eauto. }
    subst.
    assert (∥ wf Σ0 ∥) by now apply HΣ.
    unfold on_constant_decl in wt.
    sq.
    now apply lift_sorting_forget_body, lift_sorting_forget_rel in wt.
  - assert (rΣ = Σ).
    { eapply abstract_env_ext_irr;eauto. }
    subst; assumption.
  - assert (rΣ = Σ).
    { eapply abstract_env_ext_irr;eauto. }
    subst.
    assert (∥ wf Σ ∥) by now apply HΣ.
    unfold on_constant_decl in wt.
    sq.
    now apply lift_sorting_forget_body, lift_sorting_forget_rel in wt.
Qed.

Import P.

Equations? (noeqns) erase_ind_arity
          (Γ : context)
          (t : term)
          (isT : forall Σ (wfΣ : PCUICWfEnv.abstract_env_ext_rel X Σ), ∥isType Σ Γ t∥) : list type_var_info
  by wf ((Γ; t; tywt (isT _ wfrΣ)) : (∑ Γ t, welltyped rΣ Γ t)) erase_rel :=
erase_ind_arity Γ t isT with inspect (hnf (X_type := X_type) Γ t (fun Σ h => (tywt (isT Σ h)))) := {
  | exist (tProd na A B) hnf_eq =>
    let hd := type_var_info_of_flag na (HΣ _ wfrΣ)(flag_of_type Γ A _) in
    let tl := erase_ind_arity (Γ,, vass na A) B _ in
    hd :: tl;
  | exist _ _ := []
  }.
Proof.
  all: specialize (isT _ wfrΣ) as typ.
  - assert (∥ wf_ext Σ0 ∥) by (now apply heΣ);
      assert (rΣ = Σ0) by (eapply abstract_env_ext_irr;eauto);subst;
      reduce_term_sound; destruct r; eauto with erase.
  - assert (∥ wf_ext Σ ∥) by (now apply heΣ);
      assert (rΣ = Σ) by (eapply abstract_env_ext_irr;eauto);subst;
      reduce_term_sound; destruct r; eauto with erase.
  - reduce_term_sound; destruct r; eauto with erase.
Qed.

Definition ind_aname (oib : PCUICEnvironment.one_inductive_body) :=
  {| binder_name := nNamed (PCUICEnvironment.ind_name oib);
     binder_relevance := rel_of_Type |}.

Definition arities_contexts
         (mind : kername)
         (oibs : list PCUICEnvironment.one_inductive_body) : ∑Γ, Vector.t tRel_kind #|Γ| :=
  (fix f (oibs : list PCUICEnvironment.one_inductive_body)
       (i : nat)
       (Γ : context) (erΓ : Vector.t tRel_kind #|Γ|) :=
    match oibs with
    | [] => (Γ; erΓ)
    | oib :: oibs =>
      f oibs
        (S i)
        (Γ,, vass (ind_aname oib) (PCUICEnvironment.ind_type oib))
        (RelInductive {| inductive_mind := mind;
                         inductive_ind := i |} :: erΓ)%vector
    end) oibs 0 [] []%vector.

Lemma arities_contexts_cons_1 mind oib oibs :
  (arities_contexts mind (oib :: oibs)).π1 =
  (arities_contexts mind oibs).π1 ++ [vass (ind_aname oib) (PCUICEnvironment.ind_type oib)].
Proof.
  unfold arities_contexts.
  match goal with
  | |- (?f' _ _ _ _).π1 = _ => set (f := f')
  end.
  assert (H : forall oibs n Γ erΓ, (f oibs n Γ erΓ).π1 = (f oibs 0 [] []%vector).π1 ++ Γ).
  { clear.
    intros oibs.
    induction oibs as [|oib oibs IH]; [easy|].
    intros n Γ erΓ.
    cbn.
    rewrite IH; symmetry; rewrite IH.
    now rewrite <- List.app_assoc. }
  now rewrite H.
Qed.

Lemma arities_contexts_1 mind oibs :
  (arities_contexts mind oibs).π1 = arities_context oibs.
Proof.
  induction oibs as [|oib oibs IH]; [easy|].
  rewrite arities_contexts_cons_1.
  unfold arities_context.
  rewrite rev_map_cons.
  f_equal.
  apply IH.
Qed.

Inductive view_prod : term -> Type :=
| view_prod_prod na A B : view_prod (tProd na A B)
| view_prod_other t : negb (isProd t) -> view_prod t.

Equations view_prodc (t : term) : view_prod t :=
| tProd na A B => view_prod_prod na A B;
| t => view_prod_other t _.

(** Constructors are treated slightly differently to types as we always
    generate type variables for parameters *)
Equations? (noeqns) erase_ind_ctor
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (isT : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥isType Σ Γ t∥)
          (next_par : nat)
          (tvars : list type_var_info) : box_type
  by struct tvars :=
erase_ind_ctor Γ erΓ t isT next_par [] := (erase_type_aux Γ erΓ t isT None).2;

erase_ind_ctor Γ erΓ t isT next_par (tvar :: tvars)
  with inspect (reduce_term RedFlags.nodelta X_type X Γ t (fun Σ0 h => (tywt (isT Σ0 h)))) :=
  | exist t0 eq_red with view_prodc t0 := {
    | view_prod_prod na A B =>
      let rel_kind := if tvar_is_arity tvar then RelTypeVar next_par else RelOther in
      let '(_, dom) := erase_type_aux Γ erΓ A _ None in
      let cod := erase_ind_ctor (Γ,, vass na A) (rel_kind :: erΓ)%vector B _ (S next_par) tvars in
      TArr dom cod;
    | view_prod_other _ _ => TAny (* unreachable *)
    }.
Proof.
  1-2: assert (rΣ = Σ) by (eapply abstract_env_ext_irr;eauto);subst.
  all: assert (∥ wf_ext Σ ∥) by (now apply heΣ).
  all: specialize (isT _ wfrΣ) as typ.
  all: reduce_term_sound; destruct r; subst;eauto with erase.
Qed.

Import ExAst.
Definition erase_ind_body
        (mind : kername)
        (mib : PCUICEnvironment.mutual_inductive_body)
        (oib : PCUICEnvironment.one_inductive_body)
        (wt : ∥∑i, on_ind_body cumulSpec0 (lift_typing typing) rΣ mind mib i oib∥) : one_inductive_body.
Proof.
  unshelve refine (
  let is_propositional :=
      match destArity [] (ind_type oib) with
      | Some (_, u) => Sort.is_propositional u
      | None => false
      end in
  let oib_tvars := erase_ind_arity [] (PCUICEnvironment.ind_type oib) _ in

  let ctx := inspect (arities_contexts mind (PCUICEnvironment.ind_bodies mib)) in

  let ind_params := firstn (PCUICEnvironment.ind_npars mib) oib_tvars in
  let erase_ind_ctor (p : PCUICEnvironment.constructor_body) (is_in : In p (PCUICEnvironment.ind_ctors oib)) :=
      let bt := erase_ind_ctor (proj1_sig ctx).π1 (proj1_sig ctx).π2 p.(PCUICEnvironment.cstr_type) _ 0 ind_params in
      let '(ctor_args, _) := decompose_arr bt in
      let fix decomp_names ty :=
          match ty with
          | P.tProd na A B => binder_name na :: decomp_names B
          | P.tLetIn na a A b => decomp_names b
          | _ => []
          end in
      (p.(PCUICEnvironment.cstr_name), combine (decomp_names p.(PCUICEnvironment.cstr_type)) ctor_args, p.(PCUICEnvironment.cstr_arity)) in

  let ctors := map_In (PCUICEnvironment.ind_ctors oib) erase_ind_ctor in

  let erase_ind_proj (p : PCUICEnvironment.projection_body) (is_in : In p (PCUICEnvironment.ind_projs oib)) :=
      (p.(PCUICEnvironment.proj_name), TBox) (* TODO *) in

  let projs := map_In (PCUICEnvironment.ind_projs oib) erase_ind_proj in

  {| ind_name := PCUICEnvironment.ind_name oib;
     ind_propositional := is_propositional;
     ind_kelim := PCUICEnvironment.ind_kelim oib;
     ind_type_vars := oib_tvars;
     ind_ctors := ctors;
     ind_projs := projs |}).
  all: intros;assert (rΣ = Σ) by (eapply abstract_env_ext_irr;eauto);subst.
  - abstract (
      destruct wt as [wt];sq;
      eapply isTypeRel_isType;
      exact (onArity wt.π2)).
  - abstract (
      destruct p;
      cbn in *;
      destruct wt as [[ind_index wt]];
      pose proof (onConstructors wt) as on_ctors;
      unfold on_constructors in *;
      induction on_ctors; [easy|];
      destruct is_in as [->|later]; [|easy];
      constructor;
      destruct (on_ctype r) as (_ & s & typ & _);
      rewrite <- (arities_contexts_1 mind) in typ;
      cbn in *;
      now eapply has_sort_isType).
Defined.

Program Definition erase_ind
        (kn : kername)
        (mib : PCUICEnvironment.mutual_inductive_body)
        (wt : ∥on_inductive cumulSpec0 (lift_typing typing) rΣ kn mib∥) : mutual_inductive_body :=
  let inds := map_In (PCUICEnvironment.ind_bodies mib) (fun oib is_in => erase_ind_body kn mib oib _) in
  {| ind_npars := PCUICEnvironment.ind_npars mib; ind_bodies := inds; ind_finite := PCUICEnvironment.ind_finite mib |}.
Next Obligation.
  apply In_nth_error in is_in.
  destruct is_in as (i & nth_some).
  destruct wt as [wt].
  constructor.
  exists i.
  specialize (onInductives wt).

  change i with (0 + i).
  generalize 0 as n.
  revert i nth_some.

  induction (PCUICEnvironment.ind_bodies mib) as [|? oibs IH]; intros i nth_some n inds_wt.
  - now rewrite nth_error_nil in nth_some.
  - inversion inds_wt; subst; clear inds_wt.
    destruct i; cbn in *.
    + replace a with oib in * by congruence.
      now rewrite Nat.add_0_r.
    + specialize (IH _ nth_some (S n)).
      now rewrite Nat.add_succ_r.
Qed.

End FixSigmaExt.

Section EraseEnv.
Local Existing Instance extraction_checker_flags.
Local Existing Instance extraction_normalizing.

Import ExAst.

Definition fake_guard_impl : FixCoFix -> global_env_ext -> PCUICEnvironment.context
                             -> BasicAst.mfixpoint PCUICAst.term -> bool :=
  fun fix_cofix Σ Γ mfix => true.

Axiom fake_guard_correct : forall (fix_cofix : FixCoFix) (Σ : global_env_ext)
                    (Γ : PCUICEnvironment.context) (mfix : BasicAst.mfixpoint PCUICAst.term),
      guard fix_cofix Σ Γ mfix <-> fake_guard_impl fix_cofix Σ Γ mfix.

Instance fake_guard_impl_instance : abstract_guard_impl :=
  {| guard_impl := fake_guard_impl;
     guard_correct := fake_guard_correct |}.

Axiom fake_normalization : PCUICSN.Normalization.
Global Existing Instance fake_normalization.
(* Definition norm := forall Σ : global_env_ext, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ. *)
Program Definition erase_global_decl {X_type : abstract_env_impl} {X : X_type.π2.π1}
  (Σext : global_env_ext)
  (hr : Σext ∼_ext X)
  (kn : kername)
  (decl : PCUICEnvironment.global_decl)
  (wt : ∥on_global_decl cumulSpec0 (lift_typing typing) Σext kn decl∥)
  : global_decl :=
  match decl with
  | PCUICEnvironment.ConstantDecl cst =>
    match @erase_constant_decl X_type X _ _ Σext hr cst _ with
    | inl cst => ConstantDecl cst
    | inr ta => TypeAliasDecl ta
    end
  | PCUICEnvironment.InductiveDecl mib => InductiveDecl (@erase_ind X_type X _ _ Σext hr kn mib _)
  end.
Next Obligation. now eapply fake_normalization. Defined.
Next Obligation. eapply fake_normalization; auto. Defined.

Fixpoint box_type_deps (t : box_type) : KernameSet.t :=
  match t with
  | TBox
  | TAny
  | TVar _ => KernameSet.empty
  | TArr t1 t2
  | TApp t1 t2 => KernameSet.union (box_type_deps t1) (box_type_deps t2)
  | TInd ind => KernameSet.singleton (inductive_mind ind)
  | TConst kn => KernameSet.singleton kn
  end.

Definition decl_deps (decl : global_decl) : KernameSet.t :=
  match decl with
  | ConstantDecl body =>
    let seen :=
        match cst_body body with
        | Some body => term_global_deps body
        | None => KernameSet.empty
        end in
    KernameSet.union (box_type_deps (cst_type body).2) seen
  | InductiveDecl mib =>
    let one_inductive_body_deps oib :=
        let seen := fold_left (fun seen '(_, bt) => KernameSet.union seen (box_type_deps bt))
                              (flat_map (compose snd fst) (ind_ctors oib))
                              KernameSet.empty in
        fold_left (fun seen bt => KernameSet.union seen (box_type_deps bt))
                  (map snd (ind_projs oib)) seen in
    fold_left (fun seen oib => KernameSet.union seen (one_inductive_body_deps oib))
              (ind_bodies mib)
              KernameSet.empty
  | TypeAliasDecl (Some (nms, ty)) => box_type_deps ty
  | _ => KernameSet.empty
  end.

Import PCUICWfEnv.

Lemma abstract_eq_wf (X_type : abstract_env_impl) (X : X_type.π1) Σ :
  (forall Σ', Σ' ∼ X -> Σ' = Σ) -> Σ ∼ X × ∥ wf Σ ∥.
Proof.
  intros heq.
  pose proof (abstract_env_exists X) as [[Σ' hΣ']].
  pose proof (abstract_env_wf _ hΣ').
  rewrite <- (heq _ hΣ'). split; auto.
Qed.

Lemma wf_pop_decl Σ kn decl decls :
  wf Σ ->
  Σ.(declarations) = (kn, decl) :: decls ->
  wf_ext ({| universes := Σ.(universes); retroknowledge := Σ.(retroknowledge);
             declarations := decls |}, universes_decl_of_decl decl).
Proof.
  intros [] h. rewrite h in o0.
  depelim o0.
  split. cbn.
  split; cbn; eauto. cbn.
  now depelim o1.
Qed.

Lemma sq_wf_pop_decl Σ kn decl decls :
  ∥ wf Σ ∥ ->
  Σ.(declarations) = (kn, decl) :: decls ->
  ∥ wf_ext ({| universes := Σ.(universes); retroknowledge := Σ.(retroknowledge);
             declarations := decls |}, universes_decl_of_decl decl) ∥.
Proof.
  intros [[]] h; sq. rewrite h in o0.
  depelim o0.
  split. cbn.
  split; cbn; eauto. cbn.
  now depelim o1.
Qed.

(** Erase the global declarations by the specified names and their
    non-erased dependencies recursively. Ignore dependencies for which
    [ignore_deps] returnes [true] *)
Program Fixpoint erase_global_decls_deps_recursive
  {X_type : abstract_env_impl} {X : X_type.π1}
  (decls : PCUICEnvironment.global_declarations)
  (univs : ContextSet.t)
  (retro : Retroknowledge.t)
  (prop : forall Σ', abstract_env_rel X Σ' -> Σ' = {| declarations := decls; universes := univs; retroknowledge := retro |})
  (include : KernameSet.t)
  (ignore_deps : kername -> bool) : global_env :=
  match decls with
  | [] => []
  | (kn, decl) :: Σ =>
    let Σext := (Σ, universes_decl_of_decl decl) in
    let X' := abstract_pop_decls X in
    let Xext := abstract_make_wf_env_ext (X_type := X_type) X' (universes_decl_of_decl decl) _ in
    let env := (mk_global_env univs Σ retro, universes_decl_of_decl decl) in
    if KernameSet.mem kn include then
      (** We still erase ignored inductives and constants for two reasons:
          - For inductives, we want to allow pattern matches on them and we need
            information about them to print names.
          - For constants, we use their type to do deboxing. *)
      let decl := @erase_global_decl X_type Xext env _ kn decl _ in
      let with_deps := negb (ignore_deps kn) in
      let new_deps := if with_deps then decl_deps decl else KernameSet.empty in
      let Σer := erase_global_decls_deps_recursive (X:=X')
                   Σ univs retro _
                   (KernameSet.union new_deps include) ignore_deps in
      (kn, with_deps, decl) :: Σer
    else
      erase_global_decls_deps_recursive (X:=X') Σ univs retro _ include ignore_deps
  end.
Ltac invert_wf :=
  match goal with
  | [H : ∥ wf _ ∥ |- _] => sq; inversion H;subst;clear H;cbn in *
  | [H : on_global_decls _ _ _ _ (_ :: _) |- _] => inversion H;subst;clear H;cbn in *
  | [H : on_global_decls_data _ _ _ _ _ _ _ |- _] => inversion H; subst; clear H; cbn in *
  end.
Next Obligation.
  eapply abstract_eq_wf in prop as [hΣ [wf]].
  eapply abstract_pop_decls_correct in H; tea.
  2:{ cbn. intros Σ0' hΣ0'. pose proof (abstract_env_irr _ hΣ hΣ0'). subst Σ0'.
      exists (kn, decl). reflexivity. }
  destruct Σ0. cbn in *.
  destruct H as [? []]. subst.
  eapply wf_pop_decl in wf; cbn; eauto.
Qed.
Next Obligation.
  pose proof (abstract_env_exists X) as [[Σr hΣr]].
  pose proof (abstract_env_wf _ hΣr) as [wf].
  set (X' := abstract_make_wf_env_ext _ _ _).
  set (prf := fun (Σ0 : PCUICEnvironment.global_env) (_ : _) => _) in X'.
  clearbody prf.
  specialize (prop _ hΣr). subst.
  pose proof (abstract_env_ext_exists (abstract_make_wf_env_ext (abstract_pop_decls X)
  (universes_decl_of_decl decl) prf)).
  pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop hΣpop]].
  eapply (abstract_pop_decls_correct X Σ) in hΣr; tea.
  2:{ intros. pose proof (abstract_env_irr _ H0 hΣr). subst. now eexists. }
  destruct hΣr as [? []]. subst.
  destruct H as [[Σext hΣext]].
  epose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X) (universes_decl_of_decl decl) prf _ _ hΣpop hΣext).
  subst Σext. destruct Σpop. cbn in *. now subst.
Qed.
Next Obligation.
  eapply abstract_eq_wf in prop as [equiv [wf]].
  sq.
  depelim wf; cbn in *. depelim o0. now depelim o1.
Qed.
Next Obligation.
  eapply abstract_eq_wf in prop as [equiv [wf]].
  eapply abstract_pop_decls_correct in H; tea.
  2:{ cbn. intros Σ0' hΣ0'. pose proof (abstract_env_irr _ equiv hΣ0'). subst Σ0'.
      exists (kn, decl0). reflexivity. }
  destruct Σ', H as [? []]. subst. cbn.
  noconf H0. cbn in H1. subst retro. reflexivity.
Qed.
Next Obligation.
  pose proof (abstract_env_exists X) as [[Σr hΣr]].
  pose proof (abstract_env_wf _ hΣr) as [wf].
  sq. specialize (prop _ hΣr). subst Σr.
  eapply abstract_pop_decls_correct in H; tea.
  2:{ cbn. intros Σ0' hΣ0'. pose proof (abstract_env_irr _ hΣr hΣ0'). subst Σ0'.
      exists (kn, decl). reflexivity. }
  destruct Σ', H as [? []]. subst. cbn.
  noconf H0. cbn in H1. subst retro. reflexivity.
Qed.

Program Fixpoint erase_global_decls_recursive
  {X_type : abstract_env_impl} {X : X_type.π1}
  (decls : PCUICEnvironment.global_declarations)
  (univs : ContextSet.t)
  (retro : Retroknowledge.t)
  (prop : forall Σ', abstract_env_rel X Σ' -> Σ' = {| declarations := decls; universes := univs; retroknowledge := retro |})
  : global_env :=
  match decls with
  | [] => []
  | (kn, decl) :: Σ =>
    let Σext := (Σ, universes_decl_of_decl decl) in
    let X' := abstract_pop_decls X in
    let Xext := abstract_make_wf_env_ext (X_type := X_type) X' (universes_decl_of_decl decl) _ in
    let env := (mk_global_env univs Σ retro, universes_decl_of_decl decl) in
    (** We still erase ignored inductives and constants for two reasons:
      - For inductives, we want to allow pattern matches on them and we need
        information about them to print names.
      - For constants, we use their type to do deboxing. *)
    let decl := @erase_global_decl X_type Xext env _ kn decl _ in
    let Σer := erase_global_decls_recursive (X:=X') Σ univs retro _ in
    (kn, true, decl) :: Σer
  end.
Next Obligation.
  eapply erase_global_decls_deps_recursive_obligation_1; trea.
Defined.
Next Obligation.
  eapply (erase_global_decls_deps_recursive_obligation_2 X_type X); trea.
Defined.
Next Obligation.
  eapply erase_global_decls_deps_recursive_obligation_3; trea.
Qed.
Next Obligation.
  eapply erase_global_decls_deps_recursive_obligation_4; trea.
Defined.

End EraseEnv.

Global Arguments is_logical {_ _ _}.
Global Arguments conv_ar {_ _ _}.
Global Arguments is_sort {_ _ _}.
Global Arguments is_arity {_ _ _}.
