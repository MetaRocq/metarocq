(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.


Local Ltac inv H := inversion H; subst.

(** Closed single substitution: no lifting involved and one term at a time. *)

Fixpoint csubst t k u :=
  match u with
  | tBox => tBox
  | tRel n =>
     match Nat.compare k n with
    | Datatypes.Eq => t
    | Gt => tRel n
    | Lt => tRel (Nat.pred n)
    end
  | tEvar ev args => tEvar ev (List.map (csubst t k) args)
  | tLambda na M => tLambda na (csubst t (S k) M)
  | tApp u v => tApp (csubst t k u) (csubst t k v)
  | tLetIn na b b' => tLetIn na (csubst t k b) (csubst t (S k) b')
  | tCase ind c brs =>
    let brs' := List.map (fun br => (br.1, csubst t (#|br.1| + k) br.2)) brs in
    tCase ind (csubst t k c) brs'
  | tProj p c => tProj p (csubst t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k')) mfix in
    tCoFix mfix' idx
  | tConstruct ind n args => tConstruct ind n (map (csubst t k) args)
  | tPrim p => tPrim (map_prim (csubst t k) p)
  | tLazy u => tLazy (csubst t k u)
  | tForce u => tForce (csubst t k u)
  | x => x
  end.

Definition substl defs body : term :=
  fold_left (fun bod term => csubst term 0 bod)
    defs body.

(** It is equivalent to general substitution on closed terms. *)
Lemma closed_subst t k u : closed t ->
    csubst t k u = subst [t] k u.
Proof.
  revert k; induction u using term_forall_list_ind; intros k Hs;
    simpl; try f_equal; eauto; solve_all.
  - destruct (PeanoNat.Nat.compare_spec k n).
    + subst k.
      rw PeanoNat.Nat.leb_refl Nat.sub_diag /=.
      now rw lift_closed.
    + destruct (leb_spec_Set k n); try lia.
      destruct (nth_error_spec [t] (n - k) ).
      simpl in l0; lia.
      now rw Nat.sub_1_r.
    + now destruct (Nat.leb_spec k n); try lia.
Qed.

Lemma substl_subst s u : forallb (closedn 0) s ->
  substl s u = subst s 0 u.
Proof.
  unfold substl.
  induction s in u |- *; cbn; intros H.
  - now rw subst_empty.
  - move/andP: H => [cla cls]. rw IHs; try eassumption.
    rw closed_subst; try eassumption.
    change (a :: s) with ([a] ++ s).
    rw subst_app_decomp. cbn.
    repeat f_equal. rw lift_closed; eauto.
Qed.

(*
Lemma closedn_subst s k k' t :
  forallb (closedn k) s -> closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. solve_all. revert H.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    simpl closed in *; try change_Sk; repeat (rtoProp; solve_all);
    unfold compose, test_def, on_snd, test_snd in *; simpl in *; eauto with all.

  - elim (Nat.leb_spec k' n); intros. simpl.
    apply Nat.ltb_lt in H.
    destruct nth_error eqn:Heq.
    -- eapply closedn_lift.
       now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. lia.
    -- simpl. apply Nat.ltb_lt in H0.
       apply Nat.ltb_lt. apply Nat.ltb_lt in H0. lia.

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3. eauto.
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (b0 (#|m| + k')). unfold is_true. rewrite <- b0. f_equal. lia.
    unfold is_true. rewrite <- H0. f_equal. lia.
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (b0 (#|m| + k')). unfold is_true. rewrite <- b0. f_equal. lia.
    unfold is_true. rewrite <- H0. f_equal. lia.
Qed.

Lemma closedn_subst0 s k t :
  forallb (closedn k) s -> closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros.
  generalize (closedn_subst s k 0 t H).
  rewrite Nat.add_0_r. eauto.
Qed.



Lemma closed_csubst t k u : closed t -> closedn (S k) u -> closedn k (csubst t 0 u).
Proof.
  intros.
  rewrite closed_subst; auto.
  eapply closedn_subst0. simpl. erewrite closed_upwards; eauto. lia.
  simpl. now rewrite Nat.add_1_r.
Qed.
*)

Lemma closed_csubst t k u :
  closed t ->
  closedn (S k) u ->
  closedn k (ECSubst.csubst t 0 u).
Proof.
  intros.
  rw ECSubst.closed_subst //.
  eapply closedn_subst => /= //.
  rw andb_true_r. eapply closed_upwards; tea. lia.
Qed.

Lemma closed_substl ts k u :
  forallb (closedn 0) ts ->
  closedn (#|ts| + k) u ->
  closedn k (ECSubst.substl ts u).
Proof.
  induction ts in u |- *; cbn => //.
  move/andP=> [] cla clts.
  intros clu. eapply IHts => //.
  eapply closed_csubst => //.
Qed.

Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
Proof.
  induction l using rev_ind; simpl; auto.
  rw mkApps_app /= IHl.
  now rw -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
Qed.

Lemma csubst_closed t k x : closedn k x -> csubst t k x = x.
Proof.
  induction x in k |- * using EInduction.term_forall_list_ind; simpl; auto.
  all:try solve [intros; f_equal; solve_all; eauto].
  intros Hn. eapply Nat.ltb_lt in Hn.
  - destruct (Nat.compare_spec k n); try lia. reflexivity.
  - move/andP => []. intros. f_equal; solve_all; eauto.
  - move/andP => []. intros. f_equal; solve_all; eauto.
  - move/andP => []. intros. f_equal; solve_all; eauto.
Qed.

Lemma subst_csubst_comm l t k b :
  forallb (closedn 0) l -> closed t ->
  subst l 0 (csubst t (#|l| + k) b) =
  csubst t k (subst l 0 b).
Proof.
  intros hl cl.
  rw !closed_subst //.
  rw distr_subst. f_equal.
  symmetry. solve_all.
  rw subst_closed //.
  eapply closed_upwards; tea. lia.
Qed.

Lemma substl_csubst_comm l t k b :
  forallb (closedn 0) l -> closed t ->
  substl l (csubst t (#|l| + k) b) =
  csubst t k (substl l b).
Proof.
  intros hl cl.
  rw substl_subst //.
  rw substl_subst //.
  apply subst_csubst_comm => //.
Qed.


Lemma isLambda_csubst a k t : isLambda t -> isLambda (csubst a k t).
Proof. destruct t => //. Qed.
Lemma isBox_csubst a k t : isBox t -> isBox (csubst a k t).
Proof. destruct t => //. Qed.