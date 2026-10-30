From Stdlib Require Import ssreflect.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICLiftSubst
  PCUICReduction PCUICContextReduction.

From Stdlib Require Import CRelationClasses.

(** Types and names of variables are irrelevant during reduction.
    More precisely, we only need to preserve bodies of let declarations
    in contexts for reductions to be preserved.
*)

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

Lemma All2_fold_nth_ass {P n Γ Γ' d} :
  All2_fold P Γ Γ' -> nth_error Γ n = Some d ->
  assumption_context Γ ->
  { d' & ((nth_error Γ' n = Some d') *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          All2_fold P Γs Γs' *
          (d.(decl_body) = None) *
          P Γs Γs' d d')%type }.
Proof.
  induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
  - depelim Hrel. intro ass.
    simpl. eexists; intuition eauto.
    now depelim ass.
  - intros ass. depelim Hrel.
    destruct (IHn _ _ _ Hrel H).
    now depelim ass.
    cbn -[skipn] in *.
    eexists; intuition eauto.
Qed.

(** Types of variables and names are irrelevant during reduction:
  Only bodies of let-bindings should be preserved to get the same reductions.
*)

Section ContextChangeTypesReduction.

  Context {cf : checker_flags}.
  Context (Σ : global_env).

Definition pres_let_bodies (c : context_decl) (c' : context_decl) : Type :=
  match c.(decl_body) with
  | None => unit
  | Some b => decl_body c' = Some b
  end.

Global Instance pres_let_bodies_refl : Reflexive pres_let_bodies.
Proof using Type. intros [? [|]]; constructor; reflexivity. Qed.

(* Global Instance pres_let_bodies_sym : Symmetric pres_let_bodies.
Proof.
  intros x y rel.
  depelim rel; constructor; now symmetry.
Qed. *)

Global Instance pres_let_bodies_trans : Transitive pres_let_bodies.
Proof using Type.
  intros x y z; unfold pres_let_bodies.
  now destruct decl_body => // ->.
Qed.

(* Global Instance pres_let_bodies_equiv : Equivalence pres_let_bodies.
Proof. constructor; typeclasses eauto. Qed. *)

Lemma OnOne2All_All3 {A B} (P Q : A -> B -> B -> Type) l l' l'' :
  OnOne2All P l l' l'' ->
  (forall x y z, P x y z -> Q x y z) ->
  (forall x y, Q x y y) ->
  All3 Q l l' l''.
Proof using Type.
  intros H ? ?. induction H; constructor; auto.
  induction tl in bs, e |- *; destruct bs; simpl in e; try constructor; auto; try congruence.
Qed.

Local Hint Extern 4 (pres_let_bodies _ _) => exact tt || exact eq_refl : core.
Local Hint Extern 4 (All2_fold (fun _ _ => _) (_ ,, _) (_ ,, _)) => constructor : core.
Hint Constructors unit : core.

Lemma pres_let_bodies_ctx_refl :
  Reflexive (All2_fold (fun _ _ : context => pres_let_bodies)).
Proof using Type.
  intros x.
  eapply All2_fold_refl. intros. reflexivity.
Qed.

Lemma context_pres_let_bodies_red1 Γ Γ' s t :
  All2_fold (fun _ _ => pres_let_bodies) Γ Γ' ->
  red1 Σ Γ s t -> red1 Σ Γ' s t.
Proof using Type.
  intros HT X0. induction X0 using red1_ind_all in Γ', HT |- *; eauto.
  all:pcuic.
  all:try solve [econstructor; eauto; solve_all].
  - econstructor.
    move: H; case: nth_error_spec => [x hnth hi|hi] /= // [=] hbod.
    eapply All2_fold_nth in HT as [d' [hnth' [_ pres]]]; eauto.
    rw /pres_let_bodies hbod in pres.
    now rw hnth' /= pres.
  - econstructor; eauto.
    eapply IHX0. eapply All2_fold_app; auto.
    eapply All2_fold_refl.
    intros; reflexivity.
  - econstructor; eauto. solve_all.
    eapply b0; eauto.
    eapply All2_fold_app; eauto.
    eapply All2_fold_refl; intros; reflexivity.
  - eapply fix_red_body; eauto. solve_all.
    destruct x as [? ? ? ?], y as [? ? ? ?]. simpl in *. noconf b.
    eapply b0; eauto.
    eapply All2_fold_app; eauto.
    eapply pres_let_bodies_ctx_refl.
  - eapply cofix_red_body; eauto; solve_all.
    eapply b0.
    eapply All2_fold_app; eauto.
    eapply pres_let_bodies_ctx_refl.
Qed.

Lemma context_pres_let_bodies_red Γ Γ' s t :
  All2_fold (fun _ _ => pres_let_bodies) Γ Γ' ->
  red Σ Γ s t -> red Σ Γ' s t.
Proof using Type.
  intros pres.
  eapply clos_rt_monotone => x y.
  now apply context_pres_let_bodies_red1.
Qed.

End ContextChangeTypesReduction.

Lemma fix_context_pres_let_bodies Γ mfix mfix' :
  #|mfix| = #|mfix'| ->
  All2_fold (fun _ _ => pres_let_bodies) (Γ,,, fix_context mfix) (Γ,,, fix_context mfix').
Proof.
  intros len.
  apply All2_fold_app.
  - apply All2_fold_refl.
    intros.
    destruct x.
    destruct decl_body; constructor;
    reflexivity.
  - unfold fix_context, mapi.
    generalize 0 at 2 4.
    induction mfix in mfix', len |- *; intros n.
    + destruct mfix'; [|cbn in *; discriminate len].
      constructor.
    + destruct mfix'; cbn in *; [discriminate len|].
      apply All2_fold_app.
      * constructor; [constructor|].
        constructor.
      * apply IHmfix; lia.
Qed.
