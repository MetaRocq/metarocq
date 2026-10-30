From Stdlib Require Import List.
From Stdlib Require Import ssrbool.
From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EPrimitive EAst.
From MetaRocq.Erasure Require Import EAstUtils.
From MetaRocq.Erasure Require Import ECSubst.
From MetaRocq.Erasure Require Import EInduction.
From MetaRocq.Erasure Require Import ELiftSubst.

Lemma closedn_mkApps k hd args :
  closedn k hd ->
  Forall (closedn k) args ->
  closedn k (mkApps hd args).
Proof.
  intros clos_hd clos_args.
  induction args in k, hd, args, clos_hd, clos_args |- * using List.rev_ind; [easy|].
  rewrite mkApps_app.
  cbn.
  propify.
  now apply Forall_snoc in clos_args as (clos_args & clos_x).
Qed.

Lemma closed_mkApps hd args :
  closed hd ->
  Forall (closedn 0) args ->
  closed (mkApps hd args).
Proof. now intros; apply closedn_mkApps. Qed.

Lemma closed_mkApps_inv hd args :
  closed (mkApps hd args) ->
  closed hd /\
  Forall (closedn 0) args.
Proof.
  revert hd.
  induction args using List.rev_ind; [easy|]; intros hd clos.
  rewrite mkApps_app in clos.
  cbn in clos.
  propify.
  specialize (IHargs hd ltac:(easy)).
  split; [easy|].
  apply app_Forall; [easy|].
  constructor; easy.
Qed.

Lemma closed_mkApps_head hd args :
  closed (mkApps hd args) ->
  closed hd.
Proof.
  intros clos.
  now pose proof (closed_mkApps_inv _ _ clos).
Qed.

Lemma closed_mkApps_args hd args :
  closed (mkApps hd args) ->
  Forall (closedn 0) args.
Proof.
  intros clos.
  now pose proof (closed_mkApps_inv _ _ clos).
Qed.

Definition decl_closed (decl : EAst.global_decl) : bool :=
  match decl with
  | ConstantDecl cst =>
    match cst_body cst with
    | Some body => closed body
    | _ => true
    end
  | _ => true
  end.

Definition env_closed (Σ : EAst.global_declarations) : bool :=
  forallb (decl_closed ∘ snd) Σ.

Arguments Nat.ltb : simpl nomatch.

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert n k k'.
  induction t using term_forall_list_ind; intros n' k k' clos;
    cbn in *; auto; propify.
  - destruct (Nat.leb_spec k' n);
      cbn; propify; lia.
  - induction X; cbn in *; propify; easy.
  - erewrite <- IHt by eassumption.
    easy.
  - erewrite <- IHt1 at 1 by easy.
    erewrite <- IHt2 by easy.
    easy.
  - easy.
  - apply forallb_Forall in clos.
    rewrite forallb_map.
    apply forallb_Forall.
    apply All_Forall in X.
    rewrite Forall_forall in *.
    intros. eapply X;eauto. now apply clos.
  - split; [easy|].
    destruct clos as (_ & clos).
    induction X; cbn in *; propify;auto.
    replace (#|x.1| + (k + n')) with ((#|x.1| + k) + n') by lia.
    intuition;eauto.
  - rewrite length_map.
    revert n' k k' clos.
    induction X; intros n' k k' clos; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k)) _) by easy.
      f_equal.
      lia.
    + erewrite <- (IHX n' (S k) (S k'));
        repeat (f_equal; try lia).
      rewrite <- (proj2 clos);
        repeat (f_equal; try lia).
  - rewrite length_map.
    revert n' k k' clos.
    induction X; intros n' k k' clos; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k)) _) by easy.
      f_equal.
      lia.
    + erewrite <- (IHX n' (S k) (S k'));
        repeat (f_equal; try lia).
      rewrite <- (proj2 clos);
        repeat (f_equal; try lia).
  - solve_all_k 6.
Qed.

Lemma closedn_subst s k k' t :
  Forall (closedn k) s -> closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  revert k k'.
  induction t using term_forall_list_ind; intros k k' all clos;
    cbn in *; auto; propify.
  - destruct (Nat.leb_spec k' n); cbn in *; propify.
    + destruct nth_error eqn:eq;
        cbn in *.
      * apply closedn_lift.
        rewrite Forall_forall in all.
        apply nth_error_In in eq.
        easy.
      * propify.
        apply nth_error_None in eq.
        lia.
    + lia.
  - induction X; cbn in *; propify; easy.
  - erewrite <- (IHt _ (S k')); [|easy|rewrite <- clos; f_equal; lia].
    f_equal; lia.
  - split; [easy|].
    erewrite <- (IHt2 _ (S k')); [|easy|].
    + f_equal; lia.
    + rewrite <- (proj2 clos); f_equal; lia.
  - easy.
  - apply forallb_Forall in clos.
    rewrite forallb_map.
    apply forallb_Forall.
    apply All_Forall in X.
    clear X.
    induction clos;auto.
    constructor.
    rewrite <- closedn_subst_eq by now apply forallb_Forall.
    assumption.
    apply IHclos.
  - split; [easy|].
    induction X; cbn in *; propify;auto.
    replace (#|x.1| + (k + k' + #|s|)) with (k + (#|x.1| + k') + #|s|) in * by lia.
    replace (#|x.1| + (k + k')) with ( k + (#|x.1| + k')) by lia.
    easy.
  - rewrite length_map.
    revert k k' all clos.
    induction X; intros k k' all all'; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k'))); [|easy|].
      * f_equal; lia.
      * rewrite <- (proj1 all').
        f_equal; lia.
    + erewrite <- (IHX _ (S k')); [|easy|].
      * repeat (f_equal; try lia).
      * rewrite <- (proj2 all').
        repeat (f_equal; try lia).
  - rewrite length_map.
    revert k k' all clos.
    induction X; intros k k' all all'; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k'))); [|easy|].
      * f_equal; lia.
      * rewrite <- (proj1 all').
        f_equal; lia.
    + erewrite <- (IHX _ (S k')); [|easy|].
      * repeat (f_equal; try lia).
      * rewrite <- (proj2 all').
        repeat (f_equal; try lia).
  - solve_all. eapply primProp_map.
    eapply primProp_impl; tea. cbn. intuition eauto. eapply a; tea. solve_all.
Qed.

Lemma closedn_subst0 s k t :
  Forall (closedn k) s ->
  closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros all clos.
  rewrite <- (Nat.add_0_r k).
  apply closedn_subst; [easy|].
  now rewrite Nat.add_0_r.
Qed.

Lemma closed_csubst t k u : closed t -> closedn (S k) u -> closedn k (csubst t 0 u).
Proof.
  intros clost closu.
  rewrite closed_subst by easy.
  apply closedn_subst0.
  - constructor; [|easy].
    now eapply closed_upwards.
  - cbn.
    now rewrite Nat.add_1_r.
Qed.
