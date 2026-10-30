(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From Stdlib Require Import ssreflect ssrfun ssrbool.
From MetaRocq.Utils Require Import utils MRPred.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICEquality PCUICSigmaCalculus PCUICClosed.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

(** * Preservation of free variables *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".

(** Hint database for solving closed/on_free_vars goals *)
Create HintDb fvs.
Ltac fvs := eauto with fvs.

Implicit Type (cf : checker_flags).

Definition shiftnP k p i :=
  (i <? k) || p (i - k).

#[global]
Instance shiftnP_ext k : Proper (`≐1` ==> `≐1`) (shiftnP k).
Proof. intros f g Hfg i. now rw /shiftnP Hfg. Qed.

Lemma shiftnP0 P : shiftnP 0 P ≐1 P.
Proof. rw /shiftnP. intros i; rw Nat.sub_0_r //. Qed.

Lemma shiftnP_add n k P : shiftnP n (shiftnP k P) ≐1 shiftnP (n + k) P.
Proof. rw /shiftnP. intros i; repeat nat_compare_specs => // /=. lia_f_equal. Qed.

Lemma shiftnP_shiftn P f i : (shiftnP i P) ∘ (shiftn i f) ≐1 shiftnP i (P ∘ f).
Proof.
  intros k.
  rw !/shiftnP /shiftn.
  destruct (Nat.ltb_spec k i) => /=.
  all: nat_compare_specs => //=.
  by rw Nat.add_comm Nat.add_sub.
Qed.

Lemma shiftnP_impl (p q : nat -> bool) : (forall i, p i -> q i) ->
  forall n i, shiftnP n p i -> shiftnP n q i.
Proof.
  intros Hi n i. rw /shiftnP.
  nat_compare_specs => //. apply Hi.
Qed.

Lemma shiftnP_S P n : shiftnP (S n) P ≐1 shiftnP 1 (shiftnP n P).
Proof. now rw (shiftnP_add 1). Qed.

Definition closedP (n : nat) (P : nat -> bool) :=
  fun i => if i <? n then P i else false.

#[global]
Instance closedP_proper n : Proper (`≐1` ==> `≐1`) (closedP n).
Proof. intros f g Hfg. intros i; rw /closedP. now rw Hfg. Qed.

Lemma shiftnP_closedP k n P : shiftnP k (closedP n P) ≐1 closedP (k + n) (shiftnP k P).
Proof.
  intros i; rw /shiftnP /closedP.
  repeat nat_compare_specs => //.
Qed.

Fixpoint on_free_vars (p : nat -> bool) (t : term) : bool :=
  match t with
  | tRel i => p i
  | tEvar ev args => List.forallb (on_free_vars p) args
  | tLambda _ T M | tProd _ T M => on_free_vars p T && on_free_vars (shiftnP 1 p) M
  | tApp u v => on_free_vars p u && on_free_vars p v
  | tLetIn na b t b' => [&& on_free_vars p b, on_free_vars p t & on_free_vars (shiftnP 1 p) b']
  | tCase ind pred c brs =>
    [&& forallb (on_free_vars p) pred.(pparams),
      on_free_vars (shiftnP #|pred.(pcontext)| p) pred.(preturn),
      test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pred.(pparams)| pred.(pcontext),
      on_free_vars p c &
      forallb (fun br =>
        test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pred.(pparams)| br.(bcontext) &&
        on_free_vars (shiftnP #|br.(bcontext)| p) br.(bbody)) brs]
  | tProj _ c => on_free_vars p c
  | tFix mfix idx | tCoFix mfix idx =>
    List.forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|mfix| p))) mfix
  | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => true
  | tPrim pr => test_prim (on_free_vars p) pr
  end.

Lemma on_free_vars_ext (p q : nat -> bool) t :
  p ≐1 q ->
  on_free_vars p t = on_free_vars q t.
Proof.
  revert p q.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; intros;
    unfold test_def;
    rw ?forallb_map; try eapply All_forallb_eq_forallb; tea; eauto 2.
  all: try now rw (IHt1 p q) // ?(IHt2 (shiftnP 1 p) (shiftnP 1 q)) // H.
  - now rw (IHt1 p q) // ?(IHt2 p q) // (IHt3 (shiftnP 1 p) (shiftnP 1 q)) // H.
  - rw (IHt1 p q) // (IHt2 p q) //.
  - destruct X as [? [? ?]]. red in X0.
    f_equal.
    * eapply All_forallb_eq_forallb; tea. solve_all.
    * f_equal; [eapply e; rw H //|].
      f_equal.
      f_equal; [eapply IHt; rw H //|].
        eapply All_forallb_eq_forallb; tea. intros.
        destruct X.
        f_equal. eapply e0; rw H //.
  - simpl; intuition auto. f_equal; eauto 2.
    eapply b; rw H //.
  - simpl; intuition auto. f_equal; eauto 2.
    eapply b; rw H //.
  - solve_all.
Qed.

#[global]
Instance on_free_vars_proper : Proper (`≐1` ==> Logic.eq ==> Logic.eq) on_free_vars.
Proof. intros f g Hfg ? ? ->. now apply on_free_vars_ext. Qed.

#[global]
Instance on_free_vars_proper_pointwise : Proper (`≐1` ==> `≐1`) on_free_vars.
Proof. intros f g Hfg x. now apply on_free_vars_ext. Qed.

Lemma shiftnP_xpredT n : shiftnP n xpredT ≐1 xpredT.
Proof. intros i; rw /shiftnP. nat_compare_specs => //. Qed.

Lemma test_context_k_ctx p k (ctx : context) : test_context_k (fun=> p) k ctx = test_context p ctx.
Proof.
  induction ctx; simpl; auto.
Qed.
#[global]
Hint Rewrite test_context_k_ctx : map.

(* (* (* Lemma on_free_vars_true t : on_free_vars xpredT t.
Proof.
  revert t.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
  all:try (rtoProp; now rewrite ?shiftnP_xpredT ?IHt1 ?IHt2 ?IHt3; eauto 2;
    try rtoProp; solve_all).
  - rtoProp. setoid_rewrite shiftnP_xpredT.
    rewrite test_context_k_ctx.
    now move/onctxP: a0.
  - setoid_rewrite shiftnP_xpredT.
    rewrite test_context_k_ctx.
    now move/onctxP: a1.
  - unfold test_def in *. apply /andP. now rewrite shiftnP_xpredT.
  - unfold test_def in *. apply /andP. now rewrite shiftnP_xpredT.
Qed. *)

Lemma on_free_vars_xpredT : on_free_vars xpredT ≐1 xpredT.
Proof.
  intros t; apply on_free_vars_true.
Qed. *)

Lemma test_context_k_true n ctx : test_context_k (fun=> on_free_vars xpredT) n ctx.
Proof.
  setoid_rewrite on_free_vars_xpredT.
  induction ctx; simpl; auto.
  rewrite /test_decl IHctx /=.
  destruct a as [na [b|] ty] => /= //.
Qed. *)

Lemma on_free_vars_impl (p q : nat -> bool) t :
  (forall i, p i -> q i) ->
  on_free_vars p t ->
  on_free_vars q t.
Proof.
  unfold pointwise_relation, Basics.impl.
  intros Himpl onf. revert onf Himpl.
  revert t p q.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
  all:unfold test_def in *; rtoProp; now (eauto using shiftnP_impl with all).
Qed.

Lemma closedP_on_free_vars {n t} : closedn n t = on_free_vars (closedP n xpredT) t.
Proof.
  revert t n.
  apply: term_forall_list_ind; simpl => //; intros.
  all:(rw ?shiftnP_closedP ?shiftnP_xpredT).
  all:try (rtoProp; now rw ?H ?H0 ?H1 ?andb_assoc).
  - rw /closedP /=. now nat_compare_specs.
  - solve_all.
  - destruct X. rtoProp. rw /test_predicate_k /= !andb_assoc.
    rw H /=. f_equal. 2:solve_all.
    * f_equal. rw andb_comm andb_assoc. f_equal; solve_all.
      rw andb_comm. f_equal; solve_all.
    * rw /test_branch_k. f_equal; solve_all.
      rw b0.
      now rw shiftnP_closedP shiftnP_xpredT.
  - unfold test_def. solve_all.
    rw shiftnP_closedP shiftnP_xpredT.
    now len in b.
  - unfold test_def; solve_all.
    rw shiftnP_closedP shiftnP_xpredT.
    now len in b.
  - solve_all.
Qed.

Lemma closedn_on_free_vars {P n t} : closedn n t -> on_free_vars (shiftnP n P) t.
Proof.
  rw closedP_on_free_vars.
  eapply on_free_vars_impl.
  intros i; rw /closedP /shiftnP /= //.
  nat_compare_specs => //.
Qed.

(** Any predicate is admissible as there are no free variables to consider *)
Lemma closed_on_free_vars_none {t} : closed t = on_free_vars xpred0 t.
Proof.
  now rw closedP_on_free_vars /closedP /=.
Qed.

Lemma closed_on_free_vars {P t} : closed t -> on_free_vars P t.
Proof.
  rw closedP_on_free_vars /closedP /=.
  eapply on_free_vars_impl => //.
Qed.

Lemma on_free_vars_subst_instance {p u t} : on_free_vars p (subst_instance u t) = on_free_vars p t.
Proof.
  rw /subst_instance /=. revert t p.
  apply: term_forall_list_ind; simpl => //; intros.
  all:try (rtoProp; now rw -?IHt1 -?IHt2 -?IHt3).
  - rw forallb_map. eapply All_forallb_eq_forallb; eauto.
  - repeat (solve_all; f_equal).
  - unfold test_def. solve_all.
  - unfold test_def; solve_all.
  - solve_all.
Qed.

Definition on_free_vars_decl P d :=
  test_decl (on_free_vars P) d.

#[global]
Instance on_free_vars_decl_proper : Proper (`≐1` ==> Logic.eq ==> Logic.eq) on_free_vars_decl.
Proof. rw /on_free_vars_decl => f g Hfg x y <-. now rw Hfg. Qed.

#[global]
Instance on_free_vars_decl_proper_pointwise : Proper (`≐1` ==> `≐1`) on_free_vars_decl.
Proof. rw /on_free_vars_decl => f g Hfg x. now rw Hfg. Qed.

Definition on_free_vars_ctx P ctx :=
  alli (fun k => (on_free_vars_decl (shiftnP k P))) 0 (List.rev ctx).

#[global]
Instance on_free_vars_ctx_proper : Proper (`≐1` ==> `≐1`) on_free_vars_ctx.
Proof.
  rw /on_free_vars_ctx => f g Hfg x.
  now setoid_rewrite Hfg.
Qed.

Abbreviation is_open_term Γ := (on_free_vars (shiftnP #|Γ| xpred0)).
Abbreviation is_open_decl Γ := (on_free_vars_decl (shiftnP #|Γ| xpred0)).
Abbreviation is_closed_context := (on_free_vars_ctx xpred0).


Lemma on_free_vars_decl_impl (p q : nat -> bool) d :
  (forall i, p i -> q i) ->
  on_free_vars_decl p d -> on_free_vars_decl q d.
Proof.
  intros hpi.
  apply test_decl_impl. intros t.
  now apply on_free_vars_impl.
Qed.

Lemma on_free_vars_ctx_impl (p q : nat -> bool) ctx :
  (forall i, p i -> q i) ->
  on_free_vars_ctx p ctx -> on_free_vars_ctx q ctx.
Proof.
  intros hpi.
  eapply alli_impl => i x.
  apply on_free_vars_decl_impl.
  intros k; rw /shiftnP.
  now nat_compare_specs.
Qed.

Lemma closed_decl_on_free_vars {n d} : closed_decl n d = on_free_vars_decl (closedP n xpredT) d.
Proof.
  rw /on_free_vars_decl /test_decl.
  rw !closedP_on_free_vars /=.
  destruct (decl_body d) eqn:db => /= //.
  now rw closedP_on_free_vars.
Qed.

Lemma closedn_ctx_on_free_vars {n ctx} : closedn_ctx n ctx = on_free_vars_ctx (closedP n xpredT) ctx.
Proof.
  rw /on_free_vars_ctx test_context_k_eq.
  eapply alli_ext. intros i d.
  rw shiftnP_closedP shiftnP_xpredT Nat.add_comm.
  apply closed_decl_on_free_vars.
Qed.

Lemma closedP_shiftnP (n : nat) : closedP n xpredT ≐1 shiftnP n xpred0.
Proof.
  rw /closedP /shiftnP => i.
  destruct Nat.ltb => //.
Qed.

Lemma closedP_shiftnP_impl n P i : closedP n xpredT i -> shiftnP n P i.
Proof.
  rw closedP_shiftnP.
  rw /shiftnP.
  nat_compare_specs => //.
Qed.

Lemma closedn_ctx_on_free_vars_shift {n ctx P} :
  closedn_ctx n ctx ->
  on_free_vars_ctx (shiftnP n P) ctx.
Proof.
  rw closedn_ctx_on_free_vars.
  rw /on_free_vars_ctx.
  apply alli_impl => i x.
  eapply on_free_vars_decl_impl => //.
  intros k. rw shiftnP_add shiftnP_closedP shiftnP_xpredT.
  apply closedP_shiftnP_impl.
Qed.

(** This uses absurdity elimination as [ctx] can't have any free variable *)
Lemma closed_ctx_on_free_vars P ctx : closed_ctx ctx -> on_free_vars_ctx P ctx.
Proof.
  rw closedn_ctx_on_free_vars => /=.
  rw /closedP /=.
  eapply on_free_vars_ctx_impl => //.
Qed.

Definition nocc_betweenp k n i :=
  (i <? k) || (k + n <=? i).

Definition nocc_between k n t :=
  (on_free_vars (nocc_betweenp k n) t).

Definition noccur_shift p k := fun i => (i <? k) || p (i - k).

#[global] Hint Resolve All_forallb_eq_forallb : all.

Definition strengthenP k n (p : nat -> bool) :=
  fun i => if i <? k then p i else
    if i <? k + n then false
    else p (i - n).

#[global]
Instance strengthenP_proper n k : Proper (`≐1` ==> `≐1`) (strengthenP n k).
Proof.
  intros f g Hfg i. rw /strengthenP. now rw (Hfg i) (Hfg (i - k)).
Qed.

Lemma shiftnP_strengthenP k' k n p :
  shiftnP k' (strengthenP k n p) ≐1 strengthenP (k' + k) n (shiftnP k' p).
Proof.
  intros i. rw /shiftnP /strengthenP.
  repeat nat_compare_specs => /= //.
  lia_f_equal.
Qed.

Lemma on_free_vars_lift (p : nat -> bool) n k t :
  on_free_vars (strengthenP k n p) (lift n k t) = on_free_vars p t.
Proof.
  intros. revert t n k p.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; intros;
    rw ?forallb_map; try eapply All_forallb_eq_forallb; tea; simpl.
  2-6:try now rw ?shiftnP_strengthenP ?IHt1 ?IHt2 ?IHt3.
  - rename n0 into i. rw /strengthenP.
    repeat nat_compare_specs => //.
    lia_f_equal.
  - rtoProp; solve_all. len; rw !shiftnP_strengthenP e IHt.
    f_equal; solve_all. f_equal; solve_all. f_equal; solve_all. f_equal.
    solve_all.
    f_equal; solve_all.
    len. now rw !shiftnP_strengthenP.
  - unfold test_def in *. simpl; intros ? [].
    len; rw shiftnP_strengthenP. f_equal; eauto.
  - unfold test_def in *. simpl; intros ? [].
    len; rw shiftnP_strengthenP. f_equal; eauto.
  - solve_all.
Qed.

Definition on_free_vars_terms p s :=
  forallb (on_free_vars p) s.

Definition substP (k : nat) n (q p : nat -> bool) : nat -> bool :=
  fun i =>
    if i <? k then p i
    else p (i + n) || strengthenP 0 k q i.

Lemma shiftnP_substP k' k n q p :
  shiftnP k' (substP k n q p) ≐1 substP (k' + k) n q (shiftnP k' p).
Proof.
  intros i; rw /shiftnP /substP.
  repeat nat_compare_specs => /= //.
  f_equal; [f_equal|] => /= //.
  * lia_f_equal.
  * rw /strengthenP. simpl.
    repeat nat_compare_specs => //.
    lia_f_equal.
Qed.

Lemma on_free_vars_subst_gen (p q : nat -> bool) s k t :
  on_free_vars_terms q s ->
  on_free_vars p t ->
  on_free_vars (substP k #|s| q p) (subst s k t).
Proof.
  revert t p k.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; intros;
    simpl.
  all:try (rtoProp; rw ?shiftnP_substP; now rw ?IHt1 ?IHt2 ?IHt3);
  try solve [solve_all].
  - intros. destruct (Nat.leb_spec k n).
    * destruct nth_error eqn:eq.
      + unfold on_free_vars_terms in *. toAll.
        pose proof (nth_error_Some_length eq).
        eapply nth_error_all in eq; eauto.
        simpl in eq. rw /substP.
        eapply on_free_vars_impl.
        2:now rewrite -> on_free_vars_lift.
        rw /strengthenP. simpl.
        intros i. nat_compare_specs => //.
        intros ->. now rw orb_true_r.
      + eapply nth_error_None in eq.
        simpl. rw /substP.
        replace (n - #|s| + #|s|) with n by lia.
        nat_compare_specs.
        now rw H0.
    * simpl. rw /substP /strengthenP /=.
      rw H0. now nat_compare_specs.
  - rtoProp. destruct X. solve_all.
    * len. rw shiftnP_substP. solve_all.
    * len. rw shiftnP_substP; solve_all.
  - unfold test_def in *; red in X; solve_all.
    rtoProp. rw shiftnP_substP; len. solve_all.
  - unfold test_def in *; solve_all. rtoProp.
    rw shiftnP_substP; len. solve_all.
Qed.

Lemma rshiftk_S x f : S (rshiftk x f) = rshiftk (S x) f.
Proof. reflexivity. Qed.

Lemma substP_shiftnP n p :
  substP 0 n p (shiftnP n p) ≐1 p.
Proof.
  intros i; rw /shiftnP /substP /= /strengthenP /=.
  nat_compare_specs.
  replace (i + n - n) with i by lia.
  now rw Nat.sub_0_r orb_diag.
Qed.

Lemma on_free_vars_subst (p : nat -> bool) s t :
  forallb (on_free_vars p) s ->
  on_free_vars (shiftnP #|s| p) t ->
  on_free_vars p (subst s 0 t).
Proof.
  intros hs ht.
  epose proof (on_free_vars_subst_gen (shiftnP #|s| p) p s 0 t).
  rewrite -> substP_shiftnP in H.
  apply H.
  - exact hs.
  - apply ht.
Qed.

Lemma on_free_vars_subst1 (p : nat -> bool) s t :
  on_free_vars p s ->
  on_free_vars (shiftnP 1 p) t ->
  on_free_vars p (subst1 s 0 t).
Proof.
  intros hs ht.
  rw /subst1.
  epose proof (on_free_vars_subst_gen (shiftnP 1 p) p [s] 0 t).
  rewrite -> substP_shiftnP in H.
  apply H.
  - now rw /on_free_vars_terms /= hs.
  - apply ht.
Qed.

Definition addnP n (p : nat -> bool) :=
  fun i => p (n + i).

#[global]
Instance addnP_proper n : Proper (`≐1` ==> Logic.eq ==> Logic.eq) (addnP n).
Proof.
  intros i f g Hfg; now rw /addnP.
Qed.

#[global]
Instance addnP_proper_pointwise : Proper (Logic.eq ==> `≐1` ==> `≐1`) addnP.
Proof.
  intros i f g Hfg; now rw /addnP.
Qed.

Lemma addnP_add n k p : addnP n (addnP k p) ≐1 addnP (n + k) p.
Proof.
  rw /addnP => i. lia_f_equal.
Qed.

Lemma addnP0 p : addnP 0 p ≐1 p.
Proof. reflexivity. Qed.

Lemma addnP_shiftnP n P : addnP n (shiftnP n P) ≐1 P.
Proof.
  intros i; rw /addnP /shiftnP /=.
  nat_compare_specs => /=. lia_f_equal.
Qed.

Lemma addnP_orP n p q : addnP n (predU p q) ≐1 predU (addnP n p) (addnP n q).
Proof. reflexivity. Qed.

Definition on_ctx_free_vars P ctx :=
  alli (fun k d => P k ==> (on_free_vars_decl (addnP (S k) P) d)) 0 ctx.

#[global]
Instance on_ctx_free_vars_proper : Proper (`≐1` ==> eq ==> eq) on_ctx_free_vars.
Proof.
  rw /on_ctx_free_vars => f g Hfg x y <-.
  apply alli_ext => k.
  now setoid_rewrite Hfg.
Qed.

#[global]
Instance on_ctx_free_vars_proper_pointwise : Proper (`≐1` ==> `≐1`) on_ctx_free_vars.
Proof.
  rw /on_ctx_free_vars => f g Hfg x.
  apply alli_ext => k.
  now setoid_rewrite Hfg.
Qed.

Lemma nth_error_on_free_vars_ctx P n ctx i d :
  on_ctx_free_vars (addnP n P) ctx ->
  P (n + i) ->
  nth_error ctx i = Some d ->
  test_decl (on_free_vars (addnP (n + S i) P)) d.
Proof.
  rw /on_ctx_free_vars.
  solve_all.
  eapply alli_Alli, Alli_nth_error in H; eauto.
  rw /= {1}/addnP H0 /= in H.
  now rw Nat.add_comm -addnP_add.
Qed.

Definition aboveP k (p : nat -> bool) :=
  fun i => if i <? k then false else p i.

Lemma strengthenP_addn i p : strengthenP 0 i (addnP i p) ≐1 aboveP i p.
Proof.
   intros k.
   rw /strengthenP /= /addnP /aboveP.
   nat_compare_specs => //.
   lia_f_equal.
Qed.

Lemma on_free_vars_lift0 i p t :
  on_free_vars (addnP i p) t ->
  on_free_vars p (lift0 i t).
Proof.
  rw -(on_free_vars_lift _ i 0).
  rw /strengthenP /= /aboveP /addnP.
  unshelve eapply on_free_vars_impl.
  simpl. intros i'. nat_compare_specs => //.
  now replace (i + (i' - i)) with i' by lia.
Qed.

Lemma on_free_vars_lift0_above i p t :
  on_free_vars (addnP i p) t = on_free_vars (aboveP i p) (lift0 i t).
Proof.
  rw -(on_free_vars_lift _ i 0).
  rw /strengthenP /= /aboveP /addnP.
  unshelve eapply on_free_vars_ext.
  simpl. intros i'. nat_compare_specs => //.
  now replace (i' - i + i) with i' by lia.
Qed.

Lemma on_free_vars_mkApps p f args :
  on_free_vars p (mkApps f args) = on_free_vars p f && forallb (on_free_vars p) args.
Proof.
  induction args in f |- * => /=.
  - now rw andb_true_r.
  - now rw IHargs /= andb_assoc.
Qed.

Lemma extended_subst_shiftn p ctx n k :
  forallb (on_free_vars (strengthenP 0 n (shiftnP (k + context_assumptions ctx) p)))
    (extended_subst ctx (n + k)) =
  forallb (on_free_vars (shiftnP (k + (context_assumptions ctx)) p))
    (extended_subst ctx k).
Proof.
  rw lift_extended_subst' forallb_map.
  eapply forallb_ext => t.
  rw -(on_free_vars_lift _ n 0 t) //.
Qed.

Lemma extended_subst_shiftn_aboveP p ctx n k :
  forallb (on_free_vars (aboveP n p)) (extended_subst ctx (n + k)) =
  forallb (on_free_vars (addnP n p)) (extended_subst ctx k).
Proof.
  rw lift_extended_subst' forallb_map.
  eapply forallb_ext => t.
  rw -(on_free_vars_lift0_above) //.
Qed.

Lemma extended_subst_shiftn_impl p ctx n k :
  forallb (on_free_vars (shiftnP (k + (context_assumptions ctx)) p))
    (extended_subst ctx k) ->
  forallb (on_free_vars (shiftnP (n + k + context_assumptions ctx) p))
    (extended_subst ctx (n + k)).
Proof.
  rw lift_extended_subst' forallb_map.
  eapply forallb_impl => t _.
  rw -(on_free_vars_lift _ n 0 t).
  rw /strengthenP /=.
  apply on_free_vars_impl => i.
  rw /shiftnP.
  repeat nat_compare_specs => /= //.
  intros.
  red; rw -H2. lia_f_equal.
Qed.

Definition occ_betweenP k n :=
  fun i => (k <=? i) && (i <? k + n).

Lemma on_free_vars_decl_all_term P d s :
  on_free_vars_decl P d = on_free_vars P (mkProd_or_LetIn d (tSort s)).
Proof.
  rw /on_free_vars_decl /= /test_decl.
  destruct d as [na [b|] ty] => /= //; now rw andb_true_r.
Qed.

Lemma on_free_vars_mkProd_or_LetIn P d t :
  on_free_vars P (mkProd_or_LetIn d t) =
  on_free_vars_decl P d && on_free_vars (shiftnP 1 P) t.
Proof.
  destruct d as [na [b|] ty]; rw /mkProd_or_LetIn /on_free_vars_decl /test_decl /=
    ?andb_assoc /foroptb /=; try bool_congr.
Qed.

Lemma on_free_vars_ctx_all_term P ctx s :
  on_free_vars_ctx P ctx = on_free_vars P (it_mkProd_or_LetIn ctx (tSort s)).
Proof.
  rw /on_free_vars_ctx.
  rw -{2}[P](shiftnP0 P).
  generalize 0 as k.
  induction ctx using rev_ind; simpl; auto; intros k.
  rw List.rev_app_distr alli_app /= andb_true_r.
  rw IHctx it_mkProd_or_LetIn_app /= on_free_vars_mkProd_or_LetIn.
  now rw shiftnP_add.
Qed.

Definition on_free_vars_ctx_k P n ctx :=
  alli (fun k => (on_free_vars_decl (shiftnP k P))) n (List.rev ctx).

Definition predA {A} (p q : pred A) : simpl_pred A :=
  [pred i | p i ==> q i].

Definition eq_simpl_pred {A} (x y : simpl_pred A) :=
  `≐1` x y.

#[global]
Instance implP_Proper {A} : Proper (`≐1` ==> `≐1` ==> eq_simpl_pred) (@predA A).
Proof.
  intros f g Hfg f' g' Hfg' i; rw /predA /=.
  now rw Hfg Hfg'.
Qed.

Lemma on_free_vars_implP p q t :
  predA p q ≐1 xpredT ->
  on_free_vars p t -> on_free_vars q t.
Proof.
  rw /predA /=. intros Hp.
  eapply on_free_vars_impl.
  intros i hp. specialize (Hp i). now rw /= hp in Hp.
Qed.

Definition shiftnP_predU n p q :
  shiftnP n (predU p q) ≐1 predU (shiftnP n p) (shiftnP n q).
Proof.
  intros i.
  rw /shiftnP /predU /=.
  repeat nat_compare_specs => //.
Qed.

#[global]
Instance orP_Proper {A} : Proper (`≐1` ==> `≐1` ==> eq_simpl_pred) (@predU A).
Proof.
  intros f g Hfg f' g' Hfg' i; rw /predU /=.
  now rw Hfg Hfg'.
Qed.

#[global]
Instance andP_Proper A : Proper (`≐1` ==> `≐1` ==> eq_simpl_pred) (@predI A).
Proof.
  intros f g Hfg f' g' Hfg' i; rw /predI /=.
  now rw Hfg Hfg'.
Qed.

#[global]
Instance pred_of_simpl_proper {A} : Proper (eq_simpl_pred ==> `≐1`) (@PredOfSimpl.coerce A).
Proof.
  now move=> f g; rw /eq_simpl_pred => Hfg.
Qed.

Lemma orPL (p q : pred nat) : (predA p (predU p q)) ≐1 predT.
Proof.
  intros i. rw /predA /predU /=.
  rw (ssrbool.implybE (p i)).
  destruct (p i) => //.
Qed.


Lemma orPR (p q : nat -> bool) i : q i -> (predU p q) i.
Proof.
  rw /predU /= => ->; rw orb_true_r //.
Qed.

(** We need a disjunction here as the substitution can be made of
    expanded lets (properly lifted) or just the variables of
    [ctx] (lifted by [k]).

    The proof could certainly be simplified using a more high-level handling of
    free-variables predicate, which form a simple classical algebra.
    To investigate: does ssr's library support this? *)

Lemma on_free_vars_extended_subst p k ctx :
  on_free_vars_ctx_k p k ctx ->
  forallb (on_free_vars
    (predU (strengthenP 0 (context_assumptions ctx + k) (shiftnP k p))
      (occ_betweenP k (context_assumptions ctx))))
    (extended_subst ctx k).
Proof.
  rw /on_free_vars_ctx_k.
  induction ctx as [|[na [b|] ty] ctx] in p, k |- *; auto.
  - simpl. rw alli_app /= andb_true_r => /andP [] hctx.
    rw /on_free_vars_decl /test_decl /=; len => /andP [] hty /= hb.
    specialize (IHctx _ k hctx).
    rw IHctx // andb_true_r.
    eapply on_free_vars_subst => //.
    len. erewrite on_free_vars_implP => //; cycle 1.
    { erewrite on_free_vars_lift; eauto. }
    now rw shiftnP_predU /= shiftnP_strengthenP Nat.add_0_r shiftnP_add /= orPL.
  - cbn. rw alli_app /= andb_true_r => /andP [] hctx.
    rw /on_free_vars_decl /test_decl /= => hty.
    len in hty.
    specialize (IHctx p k).
    rw andb_idl.
    * move => _. rw /occ_betweenP. repeat nat_compare_specs => /= //.
    * specialize (IHctx hctx).
      rw (lift_extended_subst' _ 1).
      rw forallb_map.
      solve_all.
      apply on_free_vars_lift0.
      rw addnP_orP.
      eapply on_free_vars_implP; eauto.
      intros i. rw /predA /predU /=.
      rw /strengthenP /= /addnP /=.
      repeat nat_compare_specs => /= //.
      + rw /occ_betweenP /implb => /=.
        repeat nat_compare_specs => /= //.
      + rw /shiftnP /occ_betweenP /=.
        repeat nat_compare_specs => /= //.
        rw !orb_false_r.
        replace (i + 1 - S (context_assumptions ctx + k) - k) with
          (i - (context_assumptions ctx + k) - k) by lia.
        rw implybE. destruct p; auto.
Qed.

Lemma on_free_vars_expand_lets_k P Γ n t :
  n = context_assumptions Γ ->
  on_free_vars_ctx P Γ ->
  on_free_vars (shiftnP #|Γ| P) t ->
  on_free_vars (shiftnP n P) (expand_lets_k Γ 0 t).
Proof.
  intros -> HΓ Ht.
  rw /expand_lets_k /=.
  eapply on_free_vars_impl; cycle 1.
  - eapply on_free_vars_subst_gen.
    1:eapply on_free_vars_extended_subst; eauto.
    rewrite -> on_free_vars_lift. eauto.
  - autorewrite with len; cbn -[strengthenP]. rw /substP /= /strengthenP /=.
    intros i. simpl. rw /shiftnP.
    repeat nat_compare_specs => /= //.
    rw Nat.sub_0_r. rw /orP.
    replace (i + #|Γ| - context_assumptions Γ - #|Γ|) with (i - context_assumptions Γ) by lia.
    rw /occ_betweenP. repeat nat_compare_specs => /= //.
    rw orb_false_r Nat.sub_0_r.
    now rw orb_diag.
Qed.

Lemma on_free_vars_terms_inds P ind puinst bodies :
  on_free_vars_terms P (inds ind puinst bodies).
Proof.
  rw /inds.
  induction #|bodies|; simpl; auto.
Qed.

Lemma on_free_vars_decl_map P f d :
  (forall i, on_free_vars P i = on_free_vars P (f i)) ->
  on_free_vars_decl P d = on_free_vars_decl P (map_decl f d).
Proof.
  intros Hi.
  rw /on_free_vars_decl /test_decl.
  rw Hi. f_equal.
  simpl. destruct (decl_body d) => //.
  now rw /foroptb /= (Hi t).
Qed.

Lemma on_free_vars_ctx_subst_instance P u Γ :
  on_free_vars_ctx P (subst_instance u Γ) = on_free_vars_ctx P Γ.
Proof.
  rw /on_free_vars_ctx.
  rw /subst_instance -map_rev alli_map.
  apply alli_ext => i d.
  symmetry. apply on_free_vars_decl_map.
  intros. now rw on_free_vars_subst_instance.
Qed.

Lemma on_free_vars_map2_cstr_args p bctx ctx :
  #|bctx| = #|ctx| ->
  on_free_vars_ctx p ctx =
  on_free_vars_ctx p (map2 set_binder_name bctx ctx).
Proof.
  rw /on_free_vars_ctx.
  induction ctx as [|d ctx] in bctx |- *; simpl; auto.
  - destruct bctx; reflexivity.
  - destruct bctx => /= //.
    intros [= hlen].
    rw alli_app (IHctx bctx) // alli_app. f_equal.
    len. rw map2_length // hlen. f_equal.
Qed.


Lemma on_free_vars_to_extended_list P ctx :
  forallb (on_free_vars (shiftnP #|ctx| P)) (to_extended_list ctx).
Proof.
  rw /to_extended_list /to_extended_list_k.
  change #|ctx| with (0 + #|ctx|).
  have: (forallb (on_free_vars (shiftnP (0 + #|ctx|) P)) []) by easy.
  generalize (@nil term), 0.
  induction ctx; intros l n.
  - simpl; auto.
  - simpl. intros Hl.
    destruct a as [? [?|] ?].
    * rw Nat.add_succ_r in Hl.
      specialize (IHctx _ (S n) Hl).
      now rw Nat.add_succ_r Nat.add_1_r.
    * rw Nat.add_succ_r Nat.add_1_r. eapply (IHctx _ (S n)).
      rw -[_ + _](Nat.add_succ_r n #|ctx|) /= Hl.
      rw /shiftnP.
      nat_compare_specs => /= //.
Qed.

(** This is less precise than the strengthenP lemma above *)
Lemma on_free_vars_lift_impl (p : nat -> bool) (n k : nat) (t : term) :
  on_free_vars (shiftnP k p) t ->
  on_free_vars (shiftnP (n + k) p) (lift n k t).
Proof.
  rw -(on_free_vars_lift _ n k t).
  eapply on_free_vars_impl.
  intros i.
  rw /shiftnP /strengthenP.
  repeat nat_compare_specs => /= //.
  now replace (i - n - k) with (i - (n + k)) by lia.
Qed.


Lemma foron_free_vars_extended_subst brctx p :
  on_free_vars_ctx p brctx ->
  forallb (on_free_vars (shiftnP (context_assumptions brctx) p))
    (extended_subst brctx 0).
Proof.
  move/on_free_vars_extended_subst.
  eapply forallb_impl.
  intros x hin.
  rw Nat.add_0_r shiftnP0.
  eapply on_free_vars_impl.
  intros i. rw /orP /strengthenP /= /occ_betweenP /shiftnP.
  repeat nat_compare_specs => /= //.
  now rw orb_false_r.
Qed.

Lemma on_free_vars_fix_subst P mfix idx :
  on_free_vars P (tFix mfix idx) ->
  forallb (on_free_vars P) (fix_subst mfix).
Proof.
  move=> /=; rw /fix_subst.
  intros hmfix. generalize hmfix.
  induction mfix at 2 4; simpl; auto.
  move/andP => [ha hm]. rw IHm // andb_true_r //.
Qed.

Lemma on_free_vars_unfold_fix P mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  on_free_vars P (tFix mfix idx) ->
  on_free_vars P fn.
Proof.
  rw /unfold_fix.
  destruct nth_error eqn:hnth => // [=] _ <- /=.
  intros hmfix; generalize hmfix.
  move/forallb_All/(nth_error_all hnth) => /andP [] _ Hbody.
  eapply on_free_vars_subst; len => //.
  eapply (on_free_vars_fix_subst _ _ idx) => //.
Qed.

Lemma on_free_vars_cofix_subst P mfix idx :
  on_free_vars P (tCoFix mfix idx) ->
  forallb (on_free_vars P) (cofix_subst mfix).
Proof.
  move=> /=; rw /cofix_subst.
  intros hmfix. generalize hmfix.
  induction mfix at 2 4; simpl; auto.
  move/andP => [ha hm]. rw IHm // andb_true_r //.
Qed.

Lemma on_free_vars_unfold_cofix P mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  on_free_vars P (tCoFix mfix idx) ->
  on_free_vars P fn.
Proof.
  rw /unfold_cofix.
  destruct nth_error eqn:hnth => // [=] _ <- /=.
  intros hmfix; generalize hmfix.
  move/forallb_All/(nth_error_all hnth) => /andP [] _ Hbody.
  eapply on_free_vars_subst; len => //.
  eapply (on_free_vars_cofix_subst _ _ idx) => //.
Qed.

Lemma lenm_eq {n m} : n <= m -> n - m = 0.
Proof. lia. Qed.

Lemma addnP_shiftnP_comm n (P : nat -> bool) : P 0 -> addnP 1 (shiftnP n P) ≐1 shiftnP n (addnP 1 P).
Proof.
  intros p0 i; rw /addnP /shiftnP /=.
  repeat nat_compare_specs => /= //.
  - now rw (lenm_eq H0).
  - lia_f_equal.
Qed.

Lemma on_ctx_free_vars_concat P Γ Δ :
  on_ctx_free_vars (shiftnP #|Δ| P) (Γ ,,, Δ) =
  on_ctx_free_vars P Γ && on_ctx_free_vars (shiftnP #|Δ| P) Δ.
Proof.
  rw /on_ctx_free_vars alli_app.
  rw /= alli_shiftn andb_comm; f_equal.
  eapply alli_ext => i d /=.
  rw {1}/shiftnP. nat_compare_specs.
  replace (#|Δ| + i - #|Δ|) with i by lia.
  simpl. f_equal.
  replace (S (#|Δ| + i)) with (S i + #|Δ|) by lia.
  now rw -addnP_add addnP_shiftnP.
Qed.

Lemma on_ctx_free_vars_tip P d : on_ctx_free_vars P [d] = P 0 ==> on_free_vars_decl (addnP 1 P) d.
Proof.
  now rw /on_ctx_free_vars /= /= andb_true_r.
Qed.

Lemma shiftnPS n P : shiftnP (S n) P n.
Proof.
  rw /shiftnP /=.
  now nat_compare_specs.
Qed.

Lemma shiftnPSS n i P : shiftnP (S n) P (S i) = shiftnP n P i.
Proof.
  rw /shiftnP /=. lia_f_equal.
Qed.

Lemma closedP_xpredT n i : closedP n xpredT i -> xpredT i.
Proof.
  rw /closedP /xpredT. auto.
Qed.

Lemma on_free_vars_ctx_on_ctx_free_vars {P Γ} :
  on_ctx_free_vars (PCUICOnFreeVars.shiftnP #|Γ| P) Γ =
  on_free_vars_ctx P Γ.
Proof.
  induction Γ => /= //.
  rw /on_free_vars_ctx /= alli_app /= andb_true_r; len.
  setoid_rewrite <-(shiftnP_add 1 #|Γ|); rw addnP_shiftnP andb_comm.
  f_equal. rw /on_free_vars_ctx in IHΓ. rw -IHΓ.
  rw (alli_shift _ _ 1) /=.
  apply alli_ext => i d /=.
  now rw shiftnPSS -(Nat.add_1_r (S i)) -addnP_add addnP_shiftnP.
Qed.

(* Lemma on_ctx_free_vars_impl {P Q Γ} *)

Lemma on_free_vars_ctx_on_ctx_free_vars_xpredT {P Γ} :
  on_free_vars_ctx P Γ ->
  on_ctx_free_vars xpredT Γ.
Proof.
  move/(on_free_vars_ctx_impl _ xpredT _ ltac:(easy)).
  now rw -on_free_vars_ctx_on_ctx_free_vars shiftnP_xpredT.
Qed.

Lemma on_ctx_free_vars_extend P Γ Δ :
  on_ctx_free_vars (shiftnP #|Δ| P) (Γ ,,, Δ) =
  on_ctx_free_vars P Γ && on_free_vars_ctx P Δ.
Proof.
  rw on_ctx_free_vars_concat => //. f_equal.
  apply on_free_vars_ctx_on_ctx_free_vars.
Qed.

Lemma on_free_vars_fix_context P mfix :
  All (fun x : def term =>
      test_def (on_free_vars P) (on_free_vars (shiftnP #|mfix| P)) x)
      mfix ->
  on_free_vars_ctx P (fix_context mfix).
Proof.
  intros a.
  assert (All (fun x => on_free_vars P x.(dtype)) mfix).
  { solve_all. now move/andP: H=> []. } clear a.
  induction mfix using rev_ind; simpl; auto.
  rw /fix_context /= mapi_app List.rev_app_distr /=.
  rw /on_free_vars_ctx /= alli_app. len.
  rw andb_true_r.
  eapply All_app in X as [X Hx].
  depelim Hx. clear Hx.
  specialize (IHmfix X).
  rw /on_free_vars_ctx in IHmfix.
  rw IHmfix /= /on_free_vars_decl /test_decl /= /=.
  apply on_free_vars_lift0.
  now rw addnP_shiftnP.
Qed.

Lemma test_context_k_on_free_vars_ctx P ctx :
  test_context_k (fun k => on_free_vars (shiftnP k P)) 0 ctx =
  on_free_vars_ctx P ctx.
Proof.
  now rw test_context_k_eq.
Qed.

(* Not necessary for the above lemma, but still useful at some point presumably,
   e.g. for strenghtening *)
(*
Lemma on_free_vars_case_predicate_context {cf} {Σ} {wfΣ : wf Σ} {P ci mdecl idecl p} :
   let pctx := case_predicate_context ci mdecl idecl p in
   declared_inductive Σ ci mdecl idecl ->
   wf_predicate mdecl idecl p ->
   forallb (on_free_vars P) (pparams p) ->
   on_free_vars (shiftnP #|pcontext p| P) (preturn p) ->
   on_free_vars_ctx P pctx.
 Proof.
   intros pctx decli wfp wfb havp.
   rewrite /pctx /case_predicate_context /case_predicate_context_gen
     /pre_case_predicate_context_gen /ind_predicate_context.
   set (ibinder := {| decl_name := _ |}).
   rewrite -on_free_vars_map2_cstr_args /=; len.
   { eapply (wf_predicate_length_pcontext wfp). }
   rewrite alli_app; len; rewrite andb_true_r.
   apply andb_true_iff. split.
   - rewrite -/(on_free_vars_ctx P _).
     rewrite (on_free_vars_ctx_all_term _ _ Sort.type0).
     rewrite -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
     apply on_free_vars_subst.
     { rewrite forallb_rev => //. }
     rewrite -on_free_vars_ctx_all_term.
     rewrite on_free_vars_ctx_subst_instance.
     rewrite (on_free_vars_ctx_all_term _ _ Sort.type0).
     rewrite -(expand_lets_it_mkProd_or_LetIn _ _ 0 (tSort _)).
     eapply on_free_vars_expand_lets_k; len.
     * rewrite (wf_predicate_length_pars wfp).
       apply (declared_minductive_ind_npars decli).
     * eapply closed_ctx_on_free_vars.
       apply (declared_inductive_closed_params decli).
     * eapply on_free_vars_impl; cycle 1.
       { rewrite <- on_free_vars_ctx_all_term.
         instantiate (1 := closedP #|mdecl.(ind_params)| xpredT).
         eapply closedn_ctx_on_free_vars.
         move: (declared_inductive_closed_pars_indices wfΣ decli).
         now rewrite closedn_ctx_app => /andP []. }
        intros i'.
       rewrite /substP /= /closedP /shiftnP. len.
       now repeat nat_compare_specs => /= //.
   - rewrite /on_free_vars_decl /ibinder /test_decl /= /foroptb /=.
     rewrite on_free_vars_mkApps /= forallb_app /=.
     rewrite on_free_vars_to_extended_list /= andb_true_r.
     rewrite -/(is_true _).
     rewrite forallb_map. unshelve eapply (forallb_impl _ _ _ _ wfb).
     intros. simpl.
     eapply on_free_vars_lift0. now rewrite addnP_shiftnP.
 Qed.

 Lemma on_free_vars_case_branch_context {cf} {Σ} {wfΣ : wf Σ} {P ci i mdecl idecl p br cdecl} :
   let brctx := case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl in
   declared_constructor Σ (ci, i) mdecl idecl cdecl ->
   wf_predicate mdecl idecl p ->
   wf_branch cdecl br ->
   forallb (on_free_vars P) (pparams p) ->
   on_free_vars_ctx P brctx.
 Proof.
   intros brctx decli wfp wfb havp.
   rewrite /brctx /case_branch_context /case_branch_context_gen.
   rewrite (on_free_vars_ctx_all_term _ _ Sort.type0).
   rewrite -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
   apply on_free_vars_subst => //.
   { rewrite forallb_rev //. }
   rewrite -(expand_lets_it_mkProd_or_LetIn _ _ 0 (tSort _)).
   eapply on_free_vars_expand_lets_k; len.
   * rewrite (wf_predicate_length_pars wfp).
     apply (declared_minductive_ind_npars decli).
   * eapply closed_ctx_on_free_vars.
     rewrite closedn_subst_instance_context.
     apply (declared_inductive_closed_params decli).
   * rewrite -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
     eapply on_free_vars_impl; cycle 1.
     + eapply (on_free_vars_subst_gen _ P).
       { eapply on_free_vars_terms_inds. }
       rewrite -on_free_vars_ctx_all_term.
       rewrite on_free_vars_ctx_subst_instance.
       rewrite -on_free_vars_map2_cstr_args.
       { len. apply (wf_branch_length wfb). }
       instantiate (1 := closedP (#|mdecl.(ind_bodies)| + #|mdecl.(ind_params)|) xpredT).
       eapply closedn_ctx_on_free_vars.
       now move/andP: (declared_constructor_closed wfΣ decli) => [] /andP [].
     + intros i'.
       rewrite /substP /= /closedP /shiftnP. len.
       now repeat nat_compare_specs => /= //.
 Qed.
*)

Lemma on_free_vars_ctx_inst_case_context P n pars puinst ctx :
  n = #|pars| ->
  forallb (on_free_vars P) pars ->
  test_context_k (fun k => on_free_vars (closedP k xpredT)) n ctx ->
  on_free_vars_ctx P (inst_case_context pars puinst ctx).
Proof.
  intros hpars hn.
  rw /inst_case_context.
  rw test_context_k_eq.
  rw (on_free_vars_ctx_all_term _ _ Sort.type0).
  rw -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
  intros a.
  apply on_free_vars_subst => //.
  { rw forallb_rev //. }
  rw -on_free_vars_ctx_all_term.
  rw on_free_vars_ctx_subst_instance.
  len. subst n.
  rw /on_free_vars_ctx.
  setoid_rewrite shiftnP_add.
  unshelve eapply (alli_impl _ _ _ _ _ a).
  cbn; intros.
  rw /on_free_vars_decl.
  eapply test_decl_impl; tea.
  intros. eapply on_free_vars_impl; tea.
  intros k. rw Nat.add_comm.
  apply closedP_shiftnP_impl.
Qed.

Lemma on_ctx_free_vars_snoc {P Γ d} :
  on_ctx_free_vars (shiftnP 1 P) (Γ ,, d) =
  on_ctx_free_vars P Γ && on_free_vars_decl P d.
Proof.
  rw (on_ctx_free_vars_concat _ _ [_]) /=. f_equal.
  now rw on_ctx_free_vars_tip {1}/shiftnP /= addnP_shiftnP.
Qed.

#[global]
Hint Rewrite @on_ctx_free_vars_snoc : fvs.

Lemma test_context_k_closed_on_free_vars_ctx k ctx :
  test_context_k (fun k => on_free_vars (closedP k xpredT)) k ctx =
  on_free_vars_ctx (closedP k xpredT) ctx.
Proof.
  rw test_context_k_eq /on_free_vars_ctx.
  now setoid_rewrite shiftnP_closedP; setoid_rewrite shiftnP_xpredT; setoid_rewrite Nat.add_comm at 1.
Qed.

Lemma inv_on_free_vars_decl {P d} :
  on_free_vars_decl P d ->
  match d with
  | {| decl_body := None; decl_type := t |} => on_free_vars P t
  | {| decl_body := Some b; decl_type := t |} => on_free_vars P b /\ on_free_vars P t
  end.
Proof.
  unfold on_free_vars_decl, test_decl; destruct d; cbn => //.
  move/andP => [] //. destruct decl_body; cbn => //.
Qed.

Ltac inv_on_free_vars_orig :=
  repeat match goal with
  | [ H : is_true (on_free_vars_decl _ (vass _ _)) |- _ ] => apply inv_on_free_vars_decl in H; cbn in H
  | [ H : is_true (on_free_vars_decl _ (vdef _ _ _)) |- _ ] => apply inv_on_free_vars_decl in H as []
  | [ H : is_true (_ && _) |- _ ] =>
    move/andP: H => []; intros
  | [ H : is_true (on_free_vars ?P ?t) |- _ ] =>
    progress (cbn in H || rw on_free_vars_mkApps in H);
    (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] ||
      eapply forallb_All in H); intros
  | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
    move/andP: H => []; rw ?shiftnP_xpredT; intros
  | [ H : is_true (test_context_k _ _ _ ) |- _ ] =>
    rewrite -> test_context_k_closed_on_free_vars_ctx in H
  end.

Ltac inv_on_free_vars := inv_on_free_vars_orig.

(* cf https://github.com/rocq-prover/rocq/pull/20391
   TODO somehow cleanup redefinitions of this tactic *)
Ltac inv_on_free_vars ::= inv_on_free_vars_orig.

Abbreviation byfvs := (ltac:(cbn; eauto with fvs)) (only parsing).

Lemma on_free_vars_vass {P na t} :
  on_free_vars P t ->
  on_free_vars_decl P (vass na t).
Proof.
  rw /on_free_vars_decl /= /test_decl /=. rtoProp; tauto.
Qed.

Lemma on_free_vars_vdef {P na b t} :
  on_free_vars P b -> on_free_vars P t ->
  on_free_vars_decl P (vdef na b t).
Proof.
  rw /on_free_vars_decl /= /test_decl /=. rtoProp; tauto.
Qed.

#[global] Hint Resolve on_free_vars_vass on_free_vars_vdef : fvs.

Lemma onctx_All_fold P Q (Γ : context) :
  onctx P Γ ->
  (forall Γ x, All_fold Q Γ -> ondecl P x -> Q Γ x) ->
  All_fold Q Γ.
Proof.
  intros o H; induction o; constructor; auto.
Qed.

Lemma substP_shiftnP_gen k n p :
  substP k n p (shiftnP (k + n) p) ≐1 shiftnP k p.
Proof.
  intros i; rw /shiftnP /substP /= /strengthenP /=.
  repeat nat_compare_specs.
  - cbn.
    assert (i + n - (k + n) = i - k) by lia.
    rw H1. now rw orb_diag.
Qed.

Lemma on_free_vars_ctx_subst_context P s k ctx :
  on_free_vars_ctx (shiftnP (k + #|s|) P) ctx ->
  forallb (on_free_vars P) s ->
  on_free_vars_ctx (shiftnP k P) (subst_context s k ctx).
Proof.
  intros onctx ons.
  rw (on_free_vars_ctx_all_term _ _ Sort.type0).
  rw -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
  eapply on_free_vars_impl; revgoals.
  - eapply on_free_vars_subst_gen => //; tea.
    rw -on_free_vars_ctx_all_term //. exact onctx.
  - intros i. rw substP_shiftnP_gen //.
Qed.

Lemma on_free_vars_ctx_subst_context0 P s ctx :
  on_free_vars_ctx (shiftnP #|s| P) ctx ->
  forallb (on_free_vars P) s ->
  on_free_vars_ctx P (subst_context s 0 ctx).
Proof.
  intros onctx ons.
  rw -(shiftnP0 P). eapply on_free_vars_ctx_subst_context => /= //.
Qed.

Lemma on_free_vars_ctx_lift_context p k n ctx :
  on_free_vars_ctx p ctx =
  on_free_vars_ctx (strengthenP k n p) (lift_context n k ctx).
Proof.
  rw !(on_free_vars_ctx_all_term _ _ Sort.type0).
  rw -(lift_it_mkProd_or_LetIn _ _ _ (tSort _)).
  rw on_free_vars_lift => //.
Qed.

Lemma on_free_vars_ctx_lift_context0 p n ctx :
  on_free_vars_ctx (addnP n p) ctx ->
  on_free_vars_ctx p (lift_context n 0 ctx).
Proof.
  rw {1}(on_free_vars_ctx_lift_context _ 0 n) => h.
  eapply on_free_vars_ctx_impl; tea.
  rw /strengthenP /= /shiftnP /addnP => i.
  repeat nat_compare_specs => // /=.
  now replace (n + (i - n)) with i by lia.
Qed.


Lemma on_free_vars_ctx_snoc {P Γ d} :
  on_free_vars_ctx P (Γ ,, d) =
  on_free_vars_ctx P Γ && on_free_vars_decl (shiftnP #|Γ| P) d.
Proof.
  rw - !on_free_vars_ctx_on_ctx_free_vars /snoc /=.
  rw -(shiftnP_add 1) (on_ctx_free_vars_concat _ _ [_]) /=. f_equal.
  now rw on_ctx_free_vars_tip {1 2}/shiftnP /= addnP_shiftnP.
Qed.

Lemma on_free_vars_ctx_snoc_impl {P Γ d} :
  on_free_vars_ctx P (Γ ,, d) ->
  on_free_vars_ctx P Γ /\ on_free_vars_decl (shiftnP #|Γ| P) d.
Proof.
  now rw on_free_vars_ctx_snoc => /andP.
Qed.

Lemma on_free_vars_ctx_smash P Γ acc :
  on_free_vars_ctx P Γ ->
  on_free_vars_ctx (shiftnP #|Γ| P) acc ->
  on_free_vars_ctx P (smash_context acc Γ).
Proof.
  induction Γ in P, acc |- *.
  - cbn. now rw shiftnP0.
  - destruct a as [na [b|] ty].
    * rw /= on_free_vars_ctx_snoc /= => /andP[] onΓ.
      rw /on_free_vars_decl /test_decl /= /= => /andP[] onb onty onacc.
      eapply IHΓ => //.
      eapply on_free_vars_ctx_subst_context0 => /= //.
      + rw shiftnP_add //.
      + now rw onb //.
    * rw /= on_free_vars_ctx_snoc /= => /andP[] onΓ ont onacc.
      eapply IHΓ => //.
      rw -on_free_vars_ctx_on_ctx_free_vars /=; len.
      rw shiftnP_add -Nat.add_assoc -(shiftnP_add).
      rw on_ctx_free_vars_concat.
      rw on_free_vars_ctx_on_ctx_free_vars onacc /=.
      now rw /on_ctx_free_vars /= ont.
Qed.

Lemma on_free_vars_ctx_subst_context_xpredT s ctx :
  on_free_vars_ctx xpredT ctx ->
  forallb (on_free_vars xpredT) s ->
  on_free_vars_ctx xpredT (subst_context s 0 ctx).
Proof.
  intros onctx ons.
  apply on_free_vars_ctx_subst_context0 => //.
  rw shiftnP_xpredT //.
Qed.

Lemma on_free_vars_ctx_All_fold P Γ :
  on_free_vars_ctx P Γ <~> All_fold (fun Γ => on_free_vars_decl (shiftnP #|Γ| P)) Γ.
Proof.
  split.
  - now move/alli_Alli/Alli_rev_All_fold.
  - intros a. apply (All_fold_Alli_rev (fun k => on_free_vars_decl (shiftnP k P)) 0) in a.
    now apply alli_Alli.
Qed.


Lemma term_on_free_vars_ind :
  forall (P : (nat -> bool) -> term -> Type),
    (forall (p : nat -> bool) (i : nat), p i -> P p (tRel i)) ->
    (forall p (i : ident), P p (tVar i)) ->
    (forall p (id : nat) (l : list term),
      All (on_free_vars p) l ->
      All (P p) l ->
      P p (tEvar id l)) ->
    (forall p s, P p (tSort s)) ->
    (forall p (na : aname) (t : term) dom codom,
      on_free_vars p dom ->
      P p dom ->
      on_free_vars (shiftnP 1 p) codom ->
      P (shiftnP 1 p) codom ->
      P p (tProd na dom codom)) ->
    (forall p (na : aname) (ty : term) (body : term),
      on_free_vars p ty -> P p ty ->
      on_free_vars (shiftnP 1 p) body -> P (shiftnP 1 p) body ->
      P p (tLambda na ty body)) ->
    (forall p (na : aname) (def : term) (ty : term) body,
      on_free_vars p def -> P p def ->
      on_free_vars p ty -> P p ty ->
      on_free_vars (shiftnP 1 p) body -> P (shiftnP 1 p) body ->
      P p (tLetIn na def ty body)) ->
    (forall p (t u : term),
      on_free_vars p t -> P p t ->
      on_free_vars p u -> P p u -> P p (tApp t u)) ->
    (forall p s (u : Instance.t), P p (tConst s u)) ->
    (forall p (i : inductive) (u : Instance.t), P p (tInd i u)) ->
    (forall p (i : inductive) (c : nat) (u : Instance.t), P p (tConstruct i c u)) ->
    (forall p (ci : case_info) (pred : predicate term) discr brs,
      All (on_free_vars p) pred.(pparams) ->
      All (P p) pred.(pparams) ->
      on_free_vars_ctx (closedP #|pred.(pparams)| xpredT) pred.(pcontext) ->
      All_fold (fun Γ => ondecl (P (closedP (#|Γ| + #|pred.(pparams)|) xpredT))) pred.(pcontext) ->
      on_free_vars (shiftnP #|pred.(pcontext)| p) pred.(preturn) ->
      P (shiftnP #|pred.(pcontext)| p) pred.(preturn) ->
      on_free_vars p discr ->
      P p discr ->
      All (fun br =>
        [× on_free_vars_ctx (closedP #|pred.(pparams)| xpredT) br.(bcontext),
          All_fold (fun Γ => ondecl (P (closedP (#|Γ| + #|pred.(pparams)|) xpredT))) br.(bcontext),
          on_free_vars (shiftnP #|br.(bcontext)| p) br.(bbody) &
          P (shiftnP #|br.(bcontext)| p) br.(bbody)]) brs ->
      P p (tCase ci pred discr brs)) ->
    (forall p (s : projection) (t : term),
      on_free_vars p t -> P p t -> P p (tProj s t)) ->
    (forall p (m : mfixpoint term) (i : nat),
      tFixProp (on_free_vars p) (on_free_vars (shiftnP #|fix_context m| p)) m ->
      tFixProp (P p) (P (shiftnP #|fix_context m| p)) m -> P p (tFix m i)) ->
    (forall p (m : mfixpoint term) (i : nat),
      tFixProp (on_free_vars p) (on_free_vars (shiftnP #|fix_context m| p)) m ->
      tFixProp (P p) (P (shiftnP #|fix_context m| p)) m -> P p (tCoFix m i)) ->
    (forall p pr, tPrimProp (on_free_vars p) pr -> tPrimProp (P p) pr -> P p (tPrim pr)) ->
    forall p (t : term), on_free_vars p t -> P p t.
Proof.
  intros until t. revert p t.
  fix auxt 2.
  move auxt at top.
  intros p t.
  destruct t; intros clt;  match goal with
                 H : _ |- _ => apply H
              end; auto; simpl in clt;
            try move/andP: clt => [cl1 cl2];
            try move/andP: cl2 => [cl2 cl3];
            try move/andP: cl3 => [cl3 cl4];
            try move/andP: cl4 => [cl4 cl5];
            try solve[apply auxt; auto]; simpl in *;
            try inv_on_free_vars; tas.

  - solve_all.
  - revert l clt.
    fix auxl' 1.
    destruct l; constructor; [|apply auxl'].
    * apply auxt. simpl in clt. now move/andP: clt  => [clt cll].
    * now move/andP: clt => [clt cll].

  - solve_all.
  - revert cl1. generalize (pparams p0).
    fix auxl' 1.
    case => [|t' ts] /= //; cbn => /andP[] Ht' Hts; constructor; [apply auxt|apply auxl'] => //.
  - rw -test_context_k_closed_on_free_vars_ctx in cl3.
    revert cl3. clear -auxt.
    generalize (pcontext p0).
    fix auxl 1.
    intros [].
    * cbn. intros _. constructor.
    * cbn. move/andP => [] cll clc.
      constructor.
      + now apply auxl.
      + destruct c as [na [b|] ty]; cbn in *; constructor; cbn; apply auxt || exact tt.
        { now move/andP: clc => []. }
        { now move/andP: clc => []. }
        apply clc.

  - rename cl5 into cl. revert brs cl. clear -auxt.
    fix auxl' 1.
    destruct brs; [constructor|].
    move=> /= /andP [/andP [clctx clb] cll].
    constructor; tas.
    * split => //.
      + now rw test_context_k_closed_on_free_vars_ctx in clctx.
      + move: clctx. clear -auxt.
        generalize (bcontext b).
        fix auxl 1.
        { intros [].
        * cbn. intros _. constructor.
        * cbn. move/andP => [] cll clc.
          constructor.
          + now apply auxl.
          + destruct c as [na [b'|] ty]; cbn in *; constructor; cbn; apply auxt || exact tt.
            { now move/andP: clc => []. }
            { now move/andP: clc => []. }
            apply clc. }
      + now apply auxt.
    * now apply auxl'.

  - red. len; solve_all;
     now move/andP: H=> [].

  - red.
    rw fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1.
    destruct mfix; [constructor|].
    move=> n /= /andP[] /andP[] clb clty clmfix; constructor.
    * split => //; apply auxt => //.
    * now apply auxm.

  - red. len; solve_all;
    now move/andP: H=> [].

  - red.
    rw fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1.
    destruct mfix; [constructor|].
    move=> n /= /andP[] /andP[] clb clty clmfix; constructor.
    * split => //; apply auxt => //.
    * now apply auxm.

  - destruct prim as [? []]; cbn => //. cbn in clt.
    rtoProp. split => //. split => //.
    revert H. generalize (array_value a).
    fix auxm 1; destruct l; constructor.
    * now move/andP: H.
    * apply auxm. now move/andP: H.

  - destruct prim as [? []]; cbn => //. cbn in clt.
    rtoProp. split => //; eauto. split; eauto.
    move: (array_value a) H.
    fix auxm 1; destruct array_value; constructor; eauto.
    * eapply auxt. now move/andP: H.
    * eapply auxm; now move/andP: H.
Defined.

Lemma alpha_eq_on_free_vars P (Γ Δ : context) :
  PCUICEquality.eq_context_upto_names Γ Δ ->
  on_free_vars_ctx P Γ -> on_free_vars_ctx P Δ.
Proof.
  induction 1; cbn; auto.
  rw !alli_app /= !andb_true_r.
  move/andP => [] IH hx.
  specialize (IHX IH).
  unfold PCUICOnFreeVars.on_free_vars_ctx in IHX.
  rw IHX /=.
  len in hx. len. rw -(All2_length X).
  destruct r; cbn in *; subst; auto.
Qed.

Lemma on_free_vars_ctx_any_xpredT P Γ :
  on_free_vars_ctx P Γ -> on_free_vars_ctx xpredT Γ.
Proof.
  intros. eapply on_free_vars_ctx_impl; tea => //.
Qed.

Lemma on_free_vars_ctx_on_ctx_free_vars_closedP Γ :
  on_ctx_free_vars (closedP #|Γ| xpredT) Γ =
  on_free_vars_ctx xpred0 Γ.
Proof.
  rw closedP_shiftnP on_free_vars_ctx_on_ctx_free_vars //.
Qed.

Lemma on_free_vars_ctx_on_ctx_free_vars_closedP_impl Γ :
  on_free_vars_ctx xpred0 Γ ->
  on_ctx_free_vars (closedP #|Γ| xpredT) Γ.
Proof.
  now rw on_free_vars_ctx_on_ctx_free_vars_closedP.
Qed.

Lemma on_free_vars_ctx_app P Γ Δ :
  on_free_vars_ctx P (Γ ,,, Δ) =
  on_free_vars_ctx P Γ && on_free_vars_ctx (shiftnP #|Γ| P) Δ.
Proof.
  rw /on_free_vars_ctx List.rev_app_distr alli_app. f_equal.
  rw List.length_rev alli_shift.
  setoid_rewrite shiftnP_add.
  setoid_rewrite Nat.add_comm at 1.
  now setoid_rewrite Nat.add_0_r.
Qed.

#[global] Hint Extern 4 (is_true (on_free_vars_ctx _ (_ ,,, _))) =>
  rw on_free_vars_ctx_app : fvs.

Lemma on_ctx_free_vars_snoc_ass P Γ na ty :
  on_ctx_free_vars P Γ ->
  on_free_vars P ty ->
  on_ctx_free_vars (PCUICOnFreeVars.shiftnP 1 P) (Γ ,, vass na ty).
Proof.
  now rw on_ctx_free_vars_snoc => -> /=; rw /on_free_vars_decl /test_decl /=.
Qed.

Lemma on_ctx_free_vars_snoc_def P Γ na def ty :
  on_ctx_free_vars P Γ ->
  on_free_vars P ty ->
  on_free_vars P def ->
  on_ctx_free_vars (PCUICOnFreeVars.shiftnP 1 P) (Γ ,, vdef na def ty).
Proof.
  now rw on_ctx_free_vars_snoc => -> /=; rw /on_free_vars_decl /test_decl /= => -> ->.
Qed.
#[global] Hint Resolve on_ctx_free_vars_snoc_def on_ctx_free_vars_snoc_ass : pcuic.

Lemma on_ctx_free_vars_snocS P Γ d :
  on_ctx_free_vars (PCUICOnFreeVars.shiftnP (S #|Γ|) P) (d :: Γ) =
  on_ctx_free_vars (PCUICOnFreeVars.shiftnP #|Γ| P) Γ && on_free_vars_decl (PCUICOnFreeVars.shiftnP #|Γ| P) d.
Proof.
  rw -(shiftnP_add 1).
  now rw on_ctx_free_vars_snoc.
Qed.

Lemma on_ctx_free_vars_inst_case_context P Γ pars puinst pctx :
  forallb (on_free_vars P) pars ->
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pars| pctx ->
  on_ctx_free_vars P Γ ->
  on_ctx_free_vars (shiftnP #|pctx| P) (Γ ,,, inst_case_context pars puinst pctx).
Proof.
  intros.
  relativize #|pctx|; [erewrite on_ctx_free_vars_concat|]; try now len.
  rw H1 /=.
  rw on_free_vars_ctx_on_ctx_free_vars.
  eapply on_free_vars_ctx_inst_case_context; trea.
Qed.
#[global] Hint Resolve on_ctx_free_vars_inst_case_context : fvs.

Lemma on_free_vars_ctx_inst_case_context_weak P Γ pars puinst pctx :
  forallb (on_free_vars (shiftnP #|Γ| P)) pars ->
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pars| pctx ->
  on_free_vars_ctx P Γ ->
  on_free_vars_ctx P (Γ ,,, inst_case_context pars puinst pctx).
Proof.
  intros.
  rw on_free_vars_ctx_app H1 /=.
  eapply on_free_vars_ctx_inst_case_context; trea.
Qed.
#[global] Hint Resolve on_free_vars_ctx_inst_case_context : fvs.

Lemma on_ctx_free_vars_fix_context P Γ mfix :
  All (fun x : def term => test_def (on_free_vars P) (on_free_vars (shiftnP #|mfix| P)) x) mfix ->
  on_ctx_free_vars P Γ ->
  on_ctx_free_vars (shiftnP #|mfix| P) (Γ ,,, fix_context mfix).
Proof.
  intros.
  relativize #|mfix|; [erewrite on_ctx_free_vars_concat|].
  - rw H /=.
    rw on_free_vars_ctx_on_ctx_free_vars.
    eapply on_free_vars_fix_context => //.
  - now len.
Qed.

Lemma on_free_vars_ctx_fix_context_weak P Γ mfix :
  All (fun x : def term => test_def (on_free_vars (shiftnP #|Γ| P)) (on_free_vars (shiftnP #|mfix| (shiftnP #|Γ| P))) x) mfix ->
  on_free_vars_ctx P Γ ->
  on_free_vars_ctx P (Γ ,,, fix_context mfix).
Proof.
  intros.
  rw -on_free_vars_ctx_on_ctx_free_vars; len.
  rw -shiftnP_add.
  eapply on_ctx_free_vars_fix_context => //.
  now rw on_free_vars_ctx_on_ctx_free_vars.
Qed.

#[global] Hint Resolve on_ctx_free_vars_fix_context : fvs.
#[global] Hint Resolve on_free_vars_ctx_fix_context_weak : fvs.
#[global] Hint Resolve on_ctx_free_vars_snoc_ass on_ctx_free_vars_snoc_def : fvs.
#[global] Hint Resolve on_ctx_free_vars_inst_case_context : fvs.
#[global] Hint Extern 3 (is_true (_ && _)) => apply/andP; idtac : fvs.
#[global] Hint Extern 4 (is_true (on_ctx_free_vars (shiftnP _ xpred0) _)) =>
  rw on_free_vars_ctx_on_ctx_free_vars : fvs.

Lemma on_free_vars_ctx_snoc_ass P Γ na t :
  on_free_vars_ctx P Γ ->
  on_free_vars (shiftnP #|Γ| P) t ->
  on_free_vars_ctx P (Γ ,, vass na t).
Proof.
  intros onΓ ont.
  rw on_free_vars_ctx_snoc onΓ /=; eauto with fvs.
Qed.

Lemma on_free_vars_ctx_snoc_def P Γ na b t :
  on_free_vars_ctx P Γ ->
  on_free_vars (shiftnP #|Γ| P) b ->
  on_free_vars (shiftnP #|Γ| P) t ->
  on_free_vars_ctx P (Γ ,, vdef na b t).
Proof.
  intros onΓ ont.
  rw on_free_vars_ctx_snoc onΓ /=; eauto with fvs.
Qed.

#[global] Hint Resolve on_free_vars_ctx_snoc_ass on_free_vars_ctx_snoc_def : fvs.

Lemma on_free_vars_all_subst P s :
  All (on_free_vars P) s ->
  forall x, on_free_vars xpredT ((s ⋅n ids) x).
Proof.
  induction 1 => n; rw /subst_consn /subst_compose /=.
  - rw nth_error_nil //.
  - destruct n => /=; eauto.
    now eapply on_free_vars_impl; tea.
Qed.
