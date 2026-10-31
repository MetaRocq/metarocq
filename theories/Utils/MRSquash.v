
Record squash (A : Type) : Prop := sq { _ : A }.

(* Not at level 0: application arguments are parsed at level 0, so the closing
   [∥] would be read as the start of another squashed argument. *)
#[warning="-closed-notation-not-level-0"]
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
