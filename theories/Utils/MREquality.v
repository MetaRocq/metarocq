
Definition transport {A} (P : A -> Type) {x y : A} (e : x = y) : P x -> P y
  := fun u => eq_rect x P u y e.

Notation "p # x" := (transport _ p x) (right associativity, at level 65).

(* to convert some eq_rects into transports *)
Lemma eq_rect_transport A x P u y p
  : @eq_rect A x P u y p = transport P p u.
Proof. reflexivity. Defined.
