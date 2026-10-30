
Record squash (A : Type) : Prop := sq { _ : A }.

Notation "∥ T ∥" := (squash T) (at level 10).
Arguments sq {_} _.

Lemma map_squash {A B} (f : A -> B) : ∥ A ∥ -> ∥ B ∥.
Proof.
  intros []; constructor; auto.
Qed.

Ltac sq :=
  repeat match goal with
  | H : ∥ _ ∥ |- _ => case H; clear H; intro H
  end; try eapply sq.
