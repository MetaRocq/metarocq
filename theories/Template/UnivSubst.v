(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Environment.
From MetaRocq.Template Require Import Ast AstUtils Induction.

(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)

Lemma subst_instance_cons {A} {ua : UnivSubst A} u x xs :
  subst_instance u (x :: xs) = subst_instance u x :: subst_instance u xs.
Proof. reflexivity. Qed.

Lemma subst_instance_lift u c n k :
  lift n k (subst_instance u c) = subst_instance u (lift n k c).
Proof.
  unfold subst_instance; cbn.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
            ?map_predicate_map_predicate, ?map_predicate_subst_instance_predicate,
            ?map_branch_map_branch;
    f_equal; eauto; solve_all; eauto.
Qed.

Lemma subst_instance_mkApps u f a :
  subst_instance u (mkApps f a) =
  mkApps (subst_instance u f) (map (subst_instance u) a).
Proof.
  unfold subst_instance; cbn.
  induction a in f |- *; auto.
  simpl map. simpl. destruct f; try reflexivity.
  simpl; now rewrite map_app.
Qed.

Lemma subst_instance_it_mkProd_or_LetIn u ctx t :
  subst_instance u (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_instance u ctx) (subst_instance u t).
Proof.
  induction ctx in u, t |- *; simpl; try congruence.
  rewrite IHctx. unfold mkProd_or_LetIn; cbn. f_equal.
  destruct (decl_body a); eauto.
Qed.

Lemma subst_instance_length u ctx
  : #|subst_instance u ctx| = #|ctx|.
Proof.
  unfold subst_instance, subst_instance_context, map_context; simpl.
  now rewrite length_map.
Qed.

Lemma subst_instance_subst u c N k :
  subst (map (subst_instance u) N) k (subst_instance u c) =
  subst_instance u (subst N k c).
Proof.
  unfold subst_instance; cbn.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
            ?map_predicate_map_predicate,
            ?map_branch_map_branch; simpl;
    try solve [f_equal; eauto; solve_all; eauto].

  - elim (Nat.leb k n). rewrite nth_error_map.
    destruct (nth_error N (n - k)). simpl.
    apply subst_instance_lift. reflexivity. reflexivity.

  - rewrite subst_instance_mkApps. f_equal; auto.
    rewrite map_map_compose. solve_all.
Qed.

Lemma map_subst_instance_to_extended_list_k u ctx k :
  map (subst_instance u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all. now destruct H as [n [-> _]].
Qed.

Lemma closedu_subst_instance u t
  : closedu 0 t -> subst_instance u t = t.
Proof.
  unfold subst_instance; cbn.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map,
               ?map_predicate_map_predicate, ?map_branch_map_branch;
    try f_equal; eauto with substu; unfold test_def, test_predicate in *;
      try solve [f_equal; eauto; repeat (rtoProp; solve_all; eauto with substu)].
Qed.

Lemma subst_instance_closedu (u : Instance.t) (Hcl : closedu_instance 0 u) t :
  closedu #|u| t -> closedu 0 (subst_instance u t).
Proof.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map, ?forallb_map,
               ?map_predicate_map_predicate;
    try f_equal; auto with substu;
      unfold test_def, test_predicate in *; simpl;
      try solve [f_equal; eauto; repeat (rtoProp; solve_all); intuition auto with substu].
Qed.
