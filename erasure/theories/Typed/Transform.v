From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import WcbvEvalAux.

Import MRString.
Import MonadNotation.

Definition Transform (A : Type) := A -> result A string.

Definition TemplateTransform := Transform Ast.Env.global_env.

Definition ExtractTransform := Transform ExAst.global_env.

Definition ExtractTransformCorrect `{wcbvf : EWcbvEval.WcbvFlags} (transform : ExtractTransform) : Type :=
  forall Σ Σopt kn ind c,
    EWcbvEval.with_constructor_as_block = false ->
    transform Σ = Ok Σopt ->
    trans_env Σ e⊢ tConst kn ⇓ tConstruct ind c [] ->
    trans_env Σopt e⊢ tConst kn ⇓ tConstruct ind c [].

Definition CorrectExtractTransform `{EWcbvEval.WcbvFlags} := ∑ t, ExtractTransformCorrect t.

Fixpoint compose_transforms {A : Type} (transforms : list (Transform A)) : Transform A :=
  match transforms with
  | [] => Ok
  | t :: transforms =>
    fun Σ : A =>
      match t Σ with
      | Ok Σopt => compose_transforms transforms Σopt
      | Err e => Err e
      end
  end.

Lemma compose_transforms_correct `{EWcbvEval.WcbvFlags} transforms :
  All ExtractTransformCorrect transforms ->
  ExtractTransformCorrect (compose_transforms transforms).
Proof.
  intros all. intros Σ Σopt kn ind c ? success ev.
  induction all in Σ, success, ev |- *; cbn in *.
  - now injection success as ->.
  - destruct x eqn:teq; [|congruence].
    eapply (p _ _ kn ind c) in teq; eauto.
Qed.
