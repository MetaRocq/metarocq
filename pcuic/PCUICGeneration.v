(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Section Generation.
  Context `{cf : config.checker_flags}.

  Inductive typing_spine (Σ : global_env_ext) (Γ : context) :
    term -> list term -> term -> Type :=
  | type_spine_nil ty ty' :
      isType Σ Γ ty' ->
      Σ ;;; Γ |- ty <=s ty' ->
      typing_spine Σ Γ ty [] ty'

  | type_spine_cons hd tl na A B T B' :
      isType Σ Γ (tProd na A B) ->
      Σ ;;; Γ |- T <=s tProd na A B ->
      Σ ;;; Γ |- hd : A ->
      typing_spine Σ Γ (subst10 hd B) tl B' ->
      typing_spine Σ Γ T (hd :: tl) B'.

  Lemma type_mkApps Σ Γ t u T t_ty :
    Σ ;;; Γ |- t : t_ty ->
    typing_spine Σ Γ t_ty u T ->
    Σ ;;; Γ |- mkApps t u : T.
  Proof using Type.
    intros Ht Hsp.
    revert t Ht. induction Hsp; simpl; auto.
    intros t Ht. eapply type_Cumul; eauto. eapply i.2.π2.1.

    intros.
    specialize (IHHsp (tApp t0 hd)). apply IHHsp.
    eapply type_App; eauto. eapply i.2.π2.1.
    eapply type_Cumul; eauto. eapply i.2.π2.1.
  Qed.

  Lemma type_it_mkLambda_or_LetIn :
    forall Σ Γ Δ t A,
      Σ ;;; Γ ,,, Δ |- t : A ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : it_mkProd_or_LetIn Δ A.
  Proof using Type.
    intros Σ Γ Δ t A h.
    induction Δ as [| [na [b|] B] Δ ih ] in t, A, h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      simpl in h. pose proof (typing_wf_local h) as hc.
      apply All_local_env_tip in hc as [hc ona].
      econstructor; try eassumption.
    - simpl. cbn. eapply ih.
      pose proof (typing_wf_local h) as hc. cbn in hc.
      apply All_local_env_tip in hc as [hc ona].
      econstructor; try eassumption.
  Qed.

End Generation.
