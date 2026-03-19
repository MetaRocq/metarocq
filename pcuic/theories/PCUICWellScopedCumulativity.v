(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping PCUICCumulativity
     PCUICReduction PCUICWeakeningConv PCUICWeakeningTyp PCUICEquality PCUICUnivSubstitutionConv
     PCUICSigmaCalculus PCUICContextReduction
     PCUICParallelReduction PCUICParallelReductionConfluence PCUICClosedConv PCUICClosedTyp
     PCUICRedTypeIrrelevance PCUICOnFreeVars PCUICConfluence PCUICSubstitution.

From Stdlib Require Import CRelationClasses CMorphisms.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.

Local Ltac intuition_solver ::= auto with *.

(* We show that conversion/cumulativity starting from well-typed terms is transitive.
  We first use typing to decorate the reductions/comparisons with invariants
  showing that all the considered contexts/terms are well-scoped. In a second step
  we use confluence of one-step reduction on well-scoped terms [ws_red_confluence], which also
  commutes with alpha,universe-equivalence of contexts and terms [red1_eq_context_upto_l].
  We can now derive transitivity of the conversion relation on *well-scoped*
  terms. To deal with the closedness side condition we put them in the definition
  of conversion/cumulativity: as terms need to move between contexts, and
  we sometimes need to consider conversion in open contexts, we work with
  them in an unpacked style.
  This allows to state theorems about conversion/cumulativity of general terms
  and contexts without wrapping/unwrapping them constantly into subsets.
*)

Reserved Notation " Σ ;;; Γ ⊢ t ≤[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤[ pb ]  u").

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Inductive ws_cumul_pb {cf} (pb : conv_pb) (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| ws_cumul_pb_compare (t u : term) :
  is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
  compare_term Σ.1 (global_ext_constraints Σ) pb t u -> Σ ;;; Γ ⊢ t ≤[pb] u
| ws_cumul_pb_red_l (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  red1 Σ Γ t v -> Σ ;;; Γ ⊢ v ≤[pb] u -> Σ ;;; Γ ⊢ t ≤[pb] u
| ws_cumul_pb_red_r (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  Σ ;;; Γ ⊢ t ≤[pb] v -> red1 Σ Γ u v -> Σ ;;; Γ ⊢ t ≤[pb] u
where " Σ ;;; Γ ⊢ t ≤[ pb ] u " := (ws_cumul_pb pb Σ Γ t u) : type_scope.
Derive Signature NoConfusion for ws_cumul_pb.

Notation " Σ ;;; Γ ⊢ t ≤ u " := (ws_cumul_pb Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
    format "Σ  ;;;  Γ  ⊢  t  ≤  u") : type_scope.

Notation " Σ ;;; Γ ⊢ t = u " := (ws_cumul_pb Conv Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  =  u") : type_scope.

Lemma ws_cumul_pb_refl' {pb} {cf} {Σ} (Γ : closed_context) (t : open_term Γ) : ws_cumul_pb pb Σ Γ t t.
Proof.
  constructor; eauto with fvs. reflexivity.
Qed.

#[global]
Instance ws_cumul_pb_sym {cf Σ Γ} : Symmetric (ws_cumul_pb Conv Σ Γ).
Proof.
  move=> x y; elim.
  - move=> t u clΓ clt clu eq.
    constructor 1; eauto with fvs.
    cbn in *; now symmetry.
  - move=> t u v clΓ clt clu clv r c c'.
    econstructor 3; tea.
  - move=> t u v clΓ clt clu clv r c c'.
    econstructor 2; tea.
Qed.

Lemma red1_is_open_term {cf : checker_flags} {Σ} {wfΣ : wf Σ} {Γ : context} x y :
  red1 Σ Γ x y ->
  is_closed_context Γ ->
  is_open_term Γ x ->
  is_open_term Γ y.
Proof.
  intros. eapply red1_on_free_vars; eauto with fvs.
Qed.
#[global] Hint Immediate red1_is_open_term : fvs.

Lemma red_is_open_term {cf : checker_flags} {Σ} {wfΣ : wf Σ} {Γ : context} x y :
  red Σ Γ x y ->
  is_closed_context Γ ->
  is_open_term Γ x ->
  is_open_term Γ y.
Proof.
  intros. eapply red_on_free_vars; eauto with fvs.
Qed.
#[global] Hint Immediate red_is_open_term : fvs.

Lemma ws_cumul_pb_is_open_term {cf : checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {x y} :
  ws_cumul_pb pb Σ Γ x y ->
  [&& is_closed_context Γ, is_open_term Γ x & is_open_term Γ y].
Proof.
  now induction 1; rewrite ?i ?i0 ?i1 ?i2.
Qed.

Lemma ws_cumul_pb_is_closed_context {cf : checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {x y} :
  ws_cumul_pb pb Σ Γ x y -> is_closed_context Γ.
Proof.
  now induction 1; rewrite ?i ?i0 ?i1 ?i2.
Qed.

Lemma ws_cumul_pb_is_open_term_left {cf : checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ : context} {x y} :
  ws_cumul_pb pb Σ Γ x y -> is_open_term Γ x.
Proof.
  now induction 1; rewrite ?i ?i0 ?i1 ?i2.
Qed.

Lemma ws_cumul_pb_is_open_term_right {cf : checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {x y} :
  ws_cumul_pb pb Σ Γ x y -> is_open_term Γ y.
Proof.
  now induction 1; rewrite ?i ?i0 ?i1.
Qed.

#[global] Hint Resolve ws_cumul_pb_is_closed_context ws_cumul_pb_is_open_term_left ws_cumul_pb_is_open_term_right : fvs.

Lemma ws_cumul_pb_alt `{cf : checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} Γ t u :
  Σ ;;; Γ ⊢ t ≤[pb] u <~>
  ∑ v v',
    [× is_closed_context Γ, is_open_term Γ t, is_open_term Γ u,
      red Σ Γ t v, red Σ Γ u v' & compare_term Σ (global_ext_constraints Σ) pb v v'].
Proof.
  split.
  - induction 1.
    + exists t, u. intuition auto.
    + destruct IHX as (v' & v'' & [-> _ -> redv redv' leqv]).
      rewrite i0 /=.
      exists v', v''. split; auto. now eapply red_step.
    + destruct IHX as (v' & v'' & [-> -> cl redv redv' leqv ]).
      exists v', v''. split; auto. now eapply red_step.
  - intros (v' & v'' & [clΓ clt clu redv redv' leqv]).
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv in u, v'', redv', leqv, clt, clu |- *.
    * induction redv' in x, leqv, clt, clu |- *.
    ** constructor; auto.
    ** econstructor 3; tas. 2:eapply IHredv'. all:tea; eauto with fvs.
    * econstructor 2; revgoals. eapply IHredv; cbn; eauto with fvs. all:eauto with fvs.
Qed.

Lemma ws_cumul_eq_pb {cf:checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {t u} :
  Σ ;;; Γ ⊢ t = u ->
  Σ ;;; Γ ⊢ t ≤[pb] u.
Proof.
  move/ws_cumul_pb_alt.
  intros (t' & u' & []).
  apply ws_cumul_pb_alt.
  eexists t', u'; split; tas.
  destruct pb => //; by apply eq_term_leq_term.
Qed.

Lemma ws_cumul_pb_forget {cf:checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {x y} :
  ws_cumul_pb pb Σ Γ x y -> Σ ;;; Γ |- x <=[pb] y.
Proof.
  induction 1.
  - constructor; auto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma ws_cumul_pb_forget_cumul {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {x y} :
  ws_cumul_pb Cumul Σ Γ x y -> Σ ;;; Γ |- x <=[Cumul] y.
Proof. apply (ws_cumul_pb_forget (pb:=Cumul)). Qed.

Lemma ws_cumul_pb_forget_conv {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {x y} :
  ws_cumul_pb Conv Σ Γ x y -> Σ ;;; Γ |- x <=[Conv] y.
Proof. apply (ws_cumul_pb_forget (pb:=Conv)). Qed.
#[global] Hint Resolve ws_cumul_pb_forget_cumul ws_cumul_pb_forget_conv : pcuic.

#[global]
Instance ws_cumul_pb_trans {cf:checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} :
  Transitive (ws_cumul_pb pb Σ Γ).
Proof.
  move=> t u v /ws_cumul_pb_alt [t' [u' [clΓ clt clu tt' uu' eq]]]
    /ws_cumul_pb_alt[u'' [v' [_ clu' clv uu'' vv' eq']]].
  eapply ws_cumul_pb_alt.
  destruct (red_confluence (Γ := exist Γ clΓ) (t:=exist u clu) uu' uu'') as [u'nf [ul ur]].
  destruct pb; cbn in *.
  { eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; try tc.
    eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; try tc.
    exists tnf, unf.
    split; auto; eauto with fvs.
    - now transitivity t'.
    - now transitivity v'.
    - now transitivity u'nf. }
  { eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; try tc.
    eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; try tc.
    exists tnf, unf.
    split; eauto with fvs.
    - now transitivity t'.
    - now transitivity v'.
    - now transitivity u'nf. }
Qed.

Arguments wt_cumul_pb_dom {cf pb Σ Γ T U}.
Arguments wt_cumul_pb_codom {cf pb Σ Γ T U}.
Arguments wt_cumul_pb_eq {cf pb Σ Γ T U}.

Section EqualityLemmas.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma into_ws_cumul_pb {pb} {Γ : context} {T U} :
    Σ;;; Γ |- T <=[pb] U ->
    is_closed_context Γ -> is_open_term Γ T ->
    is_open_term Γ U ->
    Σ ;;; Γ ⊢ T ≤[pb] U.
  Proof using wfΣ.
    induction 1.
    - constructor; auto.
    - intros. econstructor 2 with v; cbn; eauto with fvs.
    - econstructor 3 with v; cbn; eauto with fvs.
  Qed.

  Lemma isType_ws_cumul_pb_refl {pb} Γ T : isType Σ Γ T -> Σ ;;; Γ ⊢ T ≤[pb] T.
  Proof using wfΣ.
    intros H.
    pose proof (isType_wf_local H).
    eapply (ws_cumul_pb_refl' (exist Γ (wf_local_closed_context X)) (exist T (isType_is_open_term H))).
  Qed.

  (** From well-typed to simply well-scoped equality. *)
  Lemma wt_cumul_pb_ws_cumul_pb {pb} {Γ : context} {T U} :
    wt_cumul_pb pb Σ Γ T U ->
    ws_cumul_pb pb Σ Γ T U.
  Proof using wfΣ.
    move=> [] dom codom equiv; cbn.
    generalize (wf_local_closed_context (isType_wf_local dom)).
    generalize (isType_is_open_term dom) (isType_is_open_term codom). clear -wfΣ equiv.
    intros. apply into_ws_cumul_pb => //.
  Qed.

  Lemma wt_cumul_pb_trans pb Γ :
    Transitive (wt_cumul_pb pb Σ Γ).
  Proof using wfΣ.
    intros x y z cum cum'.
    have wscum := (wt_cumul_pb_ws_cumul_pb cum).
    have wscum' := (wt_cumul_pb_ws_cumul_pb cum').
    generalize (transitivity wscum wscum'). clear wscum wscum'.
    destruct cum, cum'; split=> //.
    apply ws_cumul_pb_forget in X. now cbn in X.
  Qed.

  Global Instance conv_trans Γ : Transitive (wt_conv Σ Γ).
  Proof using wfΣ. apply wt_cumul_pb_trans. Qed.

  Global Instance cumul_trans Γ : Transitive (wt_cumul Σ Γ).
  Proof using wfΣ. apply wt_cumul_pb_trans. Qed.

End EqualityLemmas.

Set Warnings "-uniform-inheritance".
Coercion wt_cumul_pb_ws_cumul_pb : wt_cumul_pb >-> ws_cumul_pb.
Set Warnings "uniform-inheritance".

#[global] Hint Immediate isType_ws_cumul_pb_refl : pcuic.

Record closed_relation {R : context -> term -> term -> Type} {Γ T U} :=
  { clrel_ctx : is_closed_context Γ;
    clrel_src : is_open_term Γ T;
    clrel_rel : R Γ T U }.
Arguments closed_relation : clear implicits.

#[global] Hint Immediate clrel_ctx clrel_src : fvs.

Definition closed_red1 Σ := (closed_relation (red1 Σ)).
Definition closed_red1_red1 {Σ Γ T U} (r : closed_red1 Σ Γ T U) := clrel_rel r.
#[global] Hint Resolve closed_red1_red1 : fvs.
Coercion closed_red1_red1 : closed_red1 >-> red1.

Lemma closed_red1_open_right {cf} {Σ Γ T U} {wfΣ : wf Σ} (r : closed_red1 Σ Γ T U) : is_open_term Γ U.
Proof.
  destruct r. eauto with fvs.
Qed.

Definition closed_red Σ := (closed_relation (red Σ)).
Definition closed_red_red {Σ Γ T U} (r : closed_red Σ Γ T U) := clrel_rel r.
#[global] Hint Immediate closed_red_red : fvs.
Coercion closed_red_red : closed_red >-> red.

Lemma closed_red_open_right {cf} {Σ Γ T U} {wfΣ : wf Σ} (r : closed_red Σ Γ T U) : is_open_term Γ U.
Proof.
  destruct r. eauto with fvs.
Qed.

From Equations.Type Require Import Relation_Properties.

(* \rightsquigarrow *)
Notation "Σ ;;; Γ ⊢ t ⇝ u" := (closed_red Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ⇝  u").

Lemma closed_red1_red {Σ Γ t t'} : closed_red1 Σ Γ t t' -> Σ ;;; Γ ⊢ t ⇝ t'.
Proof.
  intros []. split => //.
  now eapply red1_red.
Qed.

Lemma ws_cumul_pb_alt_closed {cf} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} Γ t u :
  Σ ;;; Γ ⊢ t ≤[pb] u <~>
  ∑ v v',
    [× closed_red Σ Γ t v, closed_red Σ Γ u v' &
       compare_term Σ (global_ext_constraints Σ) pb v v'].
Proof.
  etransitivity. apply ws_cumul_pb_alt.
  split; intros (v & v' & cl); exists v, v'; intuition.
Qed.

Lemma biimpl_introT {T} {U} : Logic.BiImpl T U -> T -> U.
Proof. intros [] => //. Qed.

Hint View for move/ biimpl_introT|2.

Lemma ws_cumul_pb_refl {cf} {Σ} {pb Γ t} : is_closed_context Γ -> is_open_term Γ t -> Σ ;;; Γ ⊢ t ≤[pb] t.
Proof.
  move=> clΓ clt.
  constructor; cbn; eauto with fvs. reflexivity.
Qed.
#[global] Hint Immediate ws_cumul_pb_refl : pcuic.

Section RedConv.
  Context {cf} {Σ} {wfΣ : wf Σ}.

  Lemma red_conv {pb Γ t u} : Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ≤[pb] u.
  Proof using wfΣ.
    move=> [clΓ clT /clos_rt_rt1n_iff r].
    induction r.
    - now apply ws_cumul_pb_refl.
    - econstructor 2. 5:tea.
      all:eauto with fvs.
  Qed.

  Lemma red_ws_cumul_pb_left {pb Γ} {t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ u ≤[pb] v -> Σ ;;; Γ ⊢ t ≤[pb] v.
  Proof using wfΣ.
    move=> [clΓ clT /clos_rt_rt1n_iff r].
    induction r; auto.
    econstructor 2. 5:tea. all:eauto with fvs.
  Qed.

  Lemma red_ws_cumul_pb_right {pb Γ t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ v ≤[pb] u -> Σ ;;; Γ ⊢ v ≤[pb] t.
  Proof using wfΣ.
    move=> [clΓ clT /clos_rt_rt1n_iff r].
    induction r; auto.
    econstructor 3. 5:eapply IHr. all:eauto with fvs.
  Qed.

  (* synonym of red_conv *)
  Lemma red_ws_cumul_pb {pb Γ t u} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ≤[pb] u.
  Proof using wfΣ.
    move=> r; eapply red_ws_cumul_pb_left; tea.
    eapply ws_cumul_pb_refl; eauto with fvs.
  Qed.

  Lemma red_ws_cumul_pb_inv {pb Γ t u} :
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Γ ⊢ u ≤[pb] t.
  Proof using wfΣ.
    move=> r; eapply red_ws_cumul_pb_right; tea.
    eapply ws_cumul_pb_refl; eauto with fvs.
  Qed.
End RedConv.

#[global] Hint Resolve red_conv red_ws_cumul_pb red_ws_cumul_pb_inv : pcuic.

Set SimplIsCbn.

Definition conv_cum {cf:checker_flags} pb Σ Γ T T' :=
  Σ ;;; Γ |- T <=[pb] T'.

Abbreviation ws_decl Γ d := (on_free_vars_decl (shiftnP #|Γ| xpred0) d).

Definition open_decl (Γ : context) := { d : context_decl | ws_decl Γ d }.
Definition open_decl_proj {Γ : context} (d : open_decl Γ) := proj1_sig d.
Coercion open_decl_proj : open_decl >-> context_decl.

Definition vass_open_decl {Γ : closed_context} (na : binder_annot name) (t : open_term Γ) : open_decl Γ :=
  exist (vass na t) (proj2_sig t).

Definition ws_cumul_decls {cf : checker_flags} (pb : conv_pb) (Σ : global_env_ext)
  (Γ : context) (d : context_decl) (d' : context_decl) :=
  All_decls_alpha_pb pb (fun pb => @ws_cumul_pb cf pb Σ Γ) d d'.

Lemma ws_cumul_decls_wf_decl_left {cf} {pb} {Σ} {wfΣ : wf Σ} {Γ d d'} :
  ws_cumul_decls pb Σ Γ d d' -> ws_decl Γ d.
Proof.
  intros []; cbn; eauto with fvs.
Qed.

Lemma ws_cumul_decls_wf_decl_right {cf} {pb} {Σ} {wfΣ : wf Σ} {Γ d d'} :
  ws_cumul_decls pb Σ Γ d d' -> ws_decl Γ d'.
Proof.
  intros []; cbn; eauto with fvs.
Qed.
#[global] Hint Immediate ws_cumul_decls_wf_decl_left ws_cumul_decls_wf_decl_right : fvs.

Lemma ws_cumul_decls_cumul_pb_decls {cf : checker_flags} (pb : conv_pb) {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ Γ' : context} {d d'} :
  ws_cumul_decls pb Σ Γ d d' ->
  cumul_pb_decls cumulAlgo_gen pb Σ Γ Γ' d d'.
Proof.
  intros. intuition eauto with fvs.
  destruct X; destruct pb; constructor; pcuic.
Qed.

Lemma into_ws_cumul_decls {cf : checker_flags} {pb : conv_pb} {Σ : global_env_ext} {wfΣ : wf Σ}
  (Γ Γ' : context) d d' :
  cumul_pb_decls cumulAlgo_gen pb Σ Γ Γ' d d' ->
  on_free_vars_ctx xpred0 Γ ->
  on_free_vars_ctx xpred0 Γ' ->
  is_open_decl Γ d ->
  is_open_decl Γ d' ->
  ws_cumul_decls pb Σ Γ d d'.
Proof.
  case: pb; move=> pb clΓ clΓ' isd isd';
    destruct pb; cbn; constructor; auto; try inv_on_free_vars; eauto with fvs.
  all:try apply: into_ws_cumul_pb; tea; eauto 3 with fvs.
Qed.

Lemma ws_cumul_decls_inv {cf} (pb : conv_pb) {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ Γ' : context} {d d'} :
  ws_cumul_decls pb Σ Γ d d' ->
  [× on_free_vars_ctx xpred0 Γ, is_open_decl Γ d, is_open_decl Γ d' & cumul_pb_decls cumulAlgo_gen pb Σ Γ Γ' d d'].
Proof.
  intros. split; eauto with fvs.
  - destruct X; now destruct eqt.
  - now eapply ws_cumul_decls_cumul_pb_decls.
Qed.

#[global]
Instance ws_cumul_decls_trans {cf : checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} :
  Transitive (ws_cumul_decls pb Σ Γ).
Proof.
  intros d d' d''.
  rewrite /ws_cumul_decls.
  intros ond ond'; destruct ond; depelim ond'.
  econstructor; now etransitivity.
  econstructor; etransitivity; tea.
Qed.

Inductive wt_cumul_pb_decls {cf : checker_flags} (pb : conv_pb) (Σ : global_env_ext) (Γ Γ' : context) : context_decl -> context_decl -> Type :=
| wt_cumul_pb_vass {na na' : binder_annot name} {T T' : term} :
    lift_typing typing Σ Γ (j_vass na T) ->
    lift_typing typing Σ Γ' (j_vass na' T') ->
    eq_binder_annot na na' ->
    conv_cum pb Σ Γ T T' ->
    wt_cumul_pb_decls pb Σ Γ Γ' (vass na T) (vass na' T')
| wt_cumul_pb_vdef {na na' : binder_annot name} {b b' T T'} :
    lift_typing typing Σ Γ (j_vdef na b T) ->
    lift_typing typing Σ Γ' (j_vdef na' b' T') ->
    eq_binder_annot na na' ->
    Σ ;;; Γ |- b = b' ->
    conv_cum pb Σ Γ T T' ->
    wt_cumul_pb_decls pb Σ Γ Γ' (vdef na b T) (vdef na' b' T').
Derive Signature for wt_cumul_pb_decls.

Definition ws_cumul_ctx_pb {cf:checker_flags} (pb : conv_pb) (Σ : global_env_ext) (Γ Γ' : context) :=
  All2_fold (fun Γ Γ' => ws_cumul_decls pb Σ Γ) Γ Γ'.

Notation "Σ ⊢ Γ ≤[ pb ] Δ" := (ws_cumul_ctx_pb pb Σ Γ Δ) (at level 50, Γ, Δ at next level,
  format "Σ  ⊢  Γ  ≤[ pb ]  Δ") : pcuic.

Notation "Σ ⊢ Γ = Δ" := (ws_cumul_ctx_pb Conv Σ Γ Δ) (at level 50, Γ, Δ at next level,
  format "Σ  ⊢  Γ  =  Δ") : pcuic.

Notation "Σ ⊢ Γ ≤ Δ" := (ws_cumul_ctx_pb Cumul Σ Γ Δ) (at level 50, Γ, Δ at next level,
  format "Σ  ⊢  Γ  ≤  Δ") : pcuic.

Lemma ws_cumul_ctx_pb_closed_right {cf:checker_flags} {pb : conv_pb} {Σ} {wfΣ : wf Σ} {Γ Γ'}:
  ws_cumul_ctx_pb pb Σ Γ Γ' -> is_closed_context Γ'.
Proof.
  intros X. red in X.
  induction X; auto.
  rewrite on_free_vars_ctx_snoc IHX /= //.
  rewrite -(All2_fold_length X); eauto with fvs.
Qed.

Lemma ws_cumul_ctx_pb_closed_left {cf:checker_flags} {pb : conv_pb} {Σ} {wfΣ : wf Σ} {Γ Γ'}:
  ws_cumul_ctx_pb pb Σ Γ Γ' -> is_closed_context Γ.
Proof.
  intros X. red in X.
  induction X; auto.
  rewrite on_free_vars_ctx_snoc IHX /=.
  eauto with fvs.
Qed.

#[global] Hint Resolve ws_cumul_ctx_pb_closed_left ws_cumul_ctx_pb_closed_right : fvs.

Definition wt_cumul_ctx_pb {cf:checker_flags} (pb : conv_pb) (Σ : global_env_ext) :=
  All2_fold (wt_cumul_pb_decls pb Σ).

Notation "Σ ⊢ Γ ≤[ pb ] Δ ✓" := (wt_cumul_ctx_pb pb Σ Γ Δ) (at level 50, Γ, Δ at next level,
  format "Σ  ⊢  Γ  ≤[ pb ]  Δ  ✓") : pcuic.

Abbreviation wt_cumul_context Σ := (wt_cumul_ctx_pb Cumul Σ).
Abbreviation wt_conv_context Σ := (wt_cumul_ctx_pb Conv Σ).

Section WtContextConversion.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma wf_local_All_fold Γ :
    wf_local Σ Γ <~>
    All_fold (fun Γ decl => lift_typing typing Σ Γ (j_decl decl)) Γ.
  Proof using Type.
    apply All_local_env_All_fold.
  Qed.

  Lemma wt_cumul_ctx_pb_forget {pb} {Γ Γ' : context} :
    wt_cumul_ctx_pb pb Σ Γ Γ' ->
    [× wf_local Σ Γ, wf_local Σ Γ' & cumul_pb_context cumulAlgo_gen pb Σ Γ Γ'].
  Proof using Type.
    move=> wteq.
    eapply (All2_fold_impl (Q:=fun Γ Γ' d d' => lift_typing typing Σ Γ (j_decl d) × lift_typing typing Σ Γ' (j_decl d') × cumul_pb_decls cumulAlgo_gen pb Σ Γ Γ' d d')) in wteq.
    2:{ intros ???? []; intuition (cbn; try constructor; auto). }
    eapply All2_fold_All_fold_mix_inv in wteq as (wteq & wfΓ & wfΓ').
    eapply wf_local_All_fold in wfΓ. eapply wf_local_All_fold in wfΓ'.
    split; auto.
  Qed.

  Lemma into_wt_cumul_ctx_pb {pb} {Γ Γ' : context} :
    wf_local Σ Γ -> wf_local Σ Γ' ->
    cumul_pb_context cumulAlgo_gen pb Σ Γ Γ' ->
    wt_cumul_ctx_pb pb Σ Γ Γ'.
  Proof using Type.
    move=> /wf_local_All_fold wfΓ /wf_local_All_fold wfΓ'.
    destruct pb=> eq.
    eapply All2_fold_All_fold_mix in eq; tea.
    eapply All2_fold_impl; tea; clear => Γ Γ' d d' [wtd [wtd' cum]] /=.
    destruct cum; cbn in wtd, wtd'; constructor; intuition auto.
    eapply All2_fold_All_fold_mix in eq; tea.
    eapply All2_fold_impl; tea; clear => Γ Γ' d d' [wtd [wtd' cum]] /=.
    destruct cum; cbn in wtd, wtd'; constructor; intuition auto.
  Qed.

  Lemma wt_ws_ws_cumul_ctx_pb {pb} {Γ Γ' : context} :
    wt_cumul_ctx_pb pb Σ Γ Γ' ->
    ws_cumul_ctx_pb pb Σ Γ Γ'.
  Proof using wfΣ.
    intros a; eapply All2_fold_impl_ind; tea. clear Γ Γ' a.
    intros ???? wt ws eq;
    destruct eq.
    - apply lift_typing_wf_local in l as wfΓ.
      apply wf_local_closed_context in wfΓ.
      apply lift_typing_is_open_term in l as [_ clT], l0 as [_ clT'].
      eapply into_ws_cumul_decls with Δ; eauto with fvs.
      constructor; auto.
      rewrite (All2_fold_length ws) //.
    - apply lift_typing_wf_local in l as wfΓ.
      apply wf_local_closed_context in wfΓ.
      apply lift_typing_is_open_term in l as [clb clT], l0 as [clb' clT'].
      eapply into_ws_cumul_decls with Δ; eauto with fvs.
      constructor; auto.
      rewrite (All2_fold_length ws); eauto with fvs.
  Qed.

  Lemma ws_cumul_ctx_pb_inv {pb} {Γ Γ' : context} :
    ws_cumul_ctx_pb pb Σ Γ Γ' ->
    [× on_free_vars_ctx xpred0 Γ, on_free_vars_ctx xpred0 Γ' & cumul_pb_context cumulAlgo_gen pb Σ Γ Γ'].
  Proof using wfΣ.
    move=> wteq.
    split; eauto with fvs.
    eapply All2_fold_impl; tea; move=> ???? []; constructor; eauto with pcuic.
    all:try now eapply ws_cumul_pb_forget in eqt.
  Qed.

  #[global]
  Instance ws_cumul_decls_sym Γ : Symmetric (ws_cumul_decls Conv Σ Γ).
  Proof using Type.
    move=> x y [na na' T T' eqan cv|na na' b b' T T' eqna eqb eqT];
    constructor; now symmetry.
  Qed.

  Lemma ws_cumul_ctx_pb_forget {pb Γ Γ'} :
    ws_cumul_ctx_pb pb Σ Γ Γ' -> cumul_pb_context cumulAlgo_gen pb Σ Γ Γ'.
  Proof using wfΣ.
    now move/ws_cumul_ctx_pb_inv => [].
  Qed.

  Lemma ws_cumul_ctx_pb_refl pb Γ : is_closed_context Γ -> ws_cumul_ctx_pb pb Σ Γ Γ.
  Proof using wfΣ.
    move=> onΓ. cbn.
    move/on_free_vars_ctx_All_fold: onΓ => a.
    eapply (All_fold_All2_fold_impl a). clear -wfΣ.
    move=> Γ d a IH ond.
    move/on_free_vars_ctx_All_fold: a => clΓ.
    eapply (into_ws_cumul_decls _ Γ); auto.
    destruct d as [na [b|] ty]; constructor; auto; reflexivity.
  Qed.

End WtContextConversion.
