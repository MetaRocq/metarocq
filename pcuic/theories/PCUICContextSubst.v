(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
    PCUICLiftSubst.

From Stdlib Require Import ssreflect.
From Equations Require Import Equations.

(** * Substitution lemmas for typing derivations. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".

#[global]
Hint Rewrite @app_context_length : wf.

Generalizable Variables Σ Γ t T.


(** Linking a context (with let-ins), an instance (reversed substitution)
    for its assumptions and a well-formed substitution for it. *)

Inductive context_subst : context -> list term -> list term -> Type :=
| context_subst_nil : context_subst [] [] []
| context_subst_ass Γ args s na t a :
    context_subst Γ args s ->
    context_subst (vass na t :: Γ) (args ++ [a]) (a :: s)
| context_subst_def Γ args s na b t :
    context_subst Γ args s ->
    context_subst (vdef na b t :: Γ) args (subst s 0 b :: s).
Derive Signature for context_subst.

(** Promoting a substitution for the non-let declarations of ctx into a
    substitution for the whole context *)

Fixpoint make_context_subst ctx args s :=
  match ctx with
  | [] => match args with
          | [] => Some s
          | a :: args => None
          end
  | d :: ctx =>
    match d.(decl_body) with
    | Some body => make_context_subst ctx args (subst0 s body :: s)
    | None => match args with
              | a :: args => make_context_subst ctx args (a :: s)
              | [] => None
              end
    end
  end.

Lemma context_subst_length {Γ a s} : context_subst Γ a s -> #|Γ| = #|s|.
Proof. induction 1; simpl; congruence. Qed.

Lemma context_subst_assumptions_length {Γ a s} : context_subst Γ a s -> context_assumptions Γ = #|a|.
Proof. induction 1; simpl; try congruence. rewrite length_app /=. lia. Qed.

(* Lemma context_subst_app {cf:checker_flags} Γ Γ' a s : *)
(*   context_subst (Γ' ++ Γ) a s -> *)
(*   { a0 & { a1 & { s0 & { s1 & (context_subst Γ a0 s0 * context_subst (subst_context s0 0 Γ') a1 s1 *)
(*                                * (a = a0 ++ a1) * (s = s1 ++ s0))%type } } } }. *)
(* Proof. *)
(*   induction Γ' in Γ, a, s |- *. simpl. *)
(*   exists a, [], s, []. rewrite app_nil_r; intuition. constructor. *)

(*   simpl. intros Hs. *)
(*   inv Hs. *)
(*   - specialize (IHΓ' _ _ _ H). *)
(*     destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0). *)
(*     subst. exists a0', (a1' ++ [a1]), s1, (a1 :: s2). intuition eauto. *)
(*     rewrite subst_context_snoc. constructor. auto. now rewrite app_assoc. *)
(*   - specialize (IHΓ' _ _ _ H). *)
(*     destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0). *)
(*     subst. exists a0', a1', s1, (subst s2 0 (subst s1 #|Γ'| b) :: s2). intuition eauto. *)
(*     rewrite -> subst_context_snoc, Nat.add_0_r. *)
(*     unfold subst_decl; simpl. unfold map_decl. simpl. *)
(*     econstructor. auto. simpl. f_equal. *)
(*     rewrite -> subst_app_simpl; auto. simpl. *)
(*     pose proof(context_subst_length _ _ _ sa1) as Hs1. *)
(*     rewrite subst_context_length in Hs1. rewrite -> Hs1. auto. *)
(* Qed. *)



Lemma make_context_subst_rec_spec ctx args s tele args' s' :
  context_subst ctx args s ->
  make_context_subst tele args' s = Some s' ->
  context_subst (List.rev tele ++ ctx) (args ++ args') s'.
Proof.
  induction tele in ctx, args, s, args', s' |- *.
  - move=> /= Hc. case: args'.
    + move => [= <-].
      now rewrite app_nil_r.
    + move=> a l //.
  - move=> Hc /=. case: a => [na [body|] ty] /=.
    -- specialize (IHtele (vdef na body ty :: ctx) args (subst0 s body :: s) args' s').
       move=> /=. rewrite <- app_assoc.
       move/(IHtele _). move=> H /=. apply H.
       constructor. auto.
    -- case: args' => [|a args']; try congruence.
       specialize (IHtele (vass na ty :: ctx) (args ++ [a]) (a :: s) args' s').
       move=> /=. rewrite <- app_assoc.
       move/(IHtele _). move=> H /=. simpl in H. rewrite <- app_assoc in H. apply H.
       constructor. auto.
Qed.

Lemma make_context_subst_spec tele args s' :
  make_context_subst tele args [] = Some s' ->
  context_subst (List.rev tele) args s'.
Proof.
  move/(make_context_subst_rec_spec [] [] [] _ _ _ context_subst_nil).
  rewrite app_nil_r /= //.
Qed.

Lemma subst_telescope_cons s k d Γ :
  subst_telescope s k (d :: Γ) =
  map_decl (subst s k) d :: subst_telescope s (S k) Γ.
Proof.
  simpl.
  unfold subst_telescope, mapi. simpl. f_equal.
  rewrite mapi_rec_Sk. apply mapi_rec_ext.
  intros. simpl. now rewrite Nat.add_succ_r.
Qed.

Lemma subst_telescope_comm_rec s k s' k' Γ:
  subst_telescope (map (subst s' k) s) k' (subst_telescope s' (#|s| + k' + k) Γ) =
  subst_telescope s' (k' + k) (subst_telescope s k' Γ).
Proof.
  induction Γ in k, k' |- *; rewrite ?subst_telescope_cons; simpl; auto.
  f_equal.
  * unfold map_decl. simpl.
    f_equal.
    + destruct a as [na [b|] ty]; simpl; auto.
      f_equal. now rewrite distr_subst_rec.
    + now rewrite distr_subst_rec.
  * specialize (IHΓ k (S k')). now rewrite Nat.add_succ_r in IHΓ.
Qed.

Lemma subst_telescope_comm s k s' Γ:
  subst_telescope (map (subst s' k) s) 0 (subst_telescope s' (#|s| + k) Γ) =
  subst_telescope s' k (subst_telescope s 0 Γ).
Proof.
  now rewrite -(subst_telescope_comm_rec _ _ _ 0) Nat.add_0_r.
Qed.

Lemma decompose_prod_n_assum_extend_ctx {ctx n t ctx' t'} ctx'' :
  decompose_prod_n_assum ctx n t = Some (ctx', t') ->
  decompose_prod_n_assum (ctx ++ ctx'') n t = Some (ctx' ++ ctx'', t').
Proof.
  induction n in ctx, t, ctx', t', ctx'' |- *.
  - simpl. intros [= -> ->]. eauto.
  - simpl.
    destruct t; simpl; try congruence.
    + intros H. eapply (IHn _ _ _ _ ctx'' H).
    + intros H. eapply (IHn _ _ _ _ ctx'' H).
Qed.

Lemma context_subst_length2 {ctx args s} : context_subst ctx args s -> #|args| = context_assumptions ctx.
Proof.
  induction 1; simpl; auto.
  rewrite length_app; simpl; lia.
Qed.

Lemma context_subst_fun {ctx args s s'} : context_subst ctx args s -> context_subst ctx args s' -> s = s'.
Proof.
  induction 1 in s' |- *; intros H'; depelim H'; auto.
  - eapply app_inj_tail in H. intuition subst.
    now specialize (IHX _ H').
  - now specialize (IHX _ H').
Qed.

Lemma context_subst_fun' {ctx args args' s s'} : context_subst ctx args s -> context_subst ctx args' s' -> #|args| = #|args'|.
Proof.
  induction 1 as [ | ? ? ? ? ? ? ? IHX | ? ? ? ? ? ? ? IHX ] in args', s' |- *; intros H'; depelim H'; auto.
  - now rewrite !length_app; specialize (IHX _ _ H').
  - now specialize (IHX _ _ H').
Qed.

#[global] Hint Constructors context_subst : core.

Lemma context_subst_app {ctx ctx' args s} :
  context_subst (ctx ++ ctx') args s ->
  context_subst (subst_context (skipn #|ctx| s) 0 ctx) (skipn (context_assumptions ctx') args) (firstn #|ctx| s) *
  context_subst ctx' (firstn (context_assumptions ctx') args) (skipn #|ctx| s).
Proof.
  revert ctx' args s.
  induction ctx; intros ctx' args s; simpl.
  - intros Hc.
    rewrite - !(context_subst_length2 Hc).
    now rewrite firstn_all skipn_all.
  - intros Hc.
    depelim Hc.
    * rewrite skipn_S.
      specialize (IHctx _ _ _ Hc) as [IHctx IHctx'].
      pose proof (context_subst_length2 IHctx).
      pose proof (context_subst_length2 IHctx').
      pose proof (context_subst_length2 Hc).
      rewrite context_assumptions_app in H1.
      rewrite firstn_app. rewrite (firstn_0 [a0]).
      { rewrite firstn_length_le in H0; lia. }
      rewrite app_nil_r. split; auto.
      rewrite skipn_app_le; try lia.
      rewrite subst_context_snoc.
      cbn. now constructor.

    * specialize (IHctx _ _ _ Hc).
      split; try now rewrite skipn_S.
      pose proof (context_subst_length2 Hc).
      rewrite context_assumptions_app in H.
      destruct IHctx as [IHctx _].
      pose proof (context_subst_length IHctx).
      rewrite subst_context_snoc. rewrite !skipn_S.
      rewrite /subst_decl /map_decl /= Nat.add_0_r.
      rewrite -{4}(firstn_skipn #|ctx| s0).
      rewrite subst_app_simpl. simpl.
      rewrite subst_context_length in H0. rewrite -H0.
      cbn. now constructor.
Qed.

Lemma make_context_subst_recP ctx args s tele args' s' :
  context_subst ctx args s ->
  (make_context_subst tele args' s = Some s') <~>
  context_subst (List.rev tele ++ ctx) (args ++ args') s'.
Proof.
  induction tele in ctx, args, s, args', s' |- *.
  - move=> /= Hc. case: args'.
    * split.
      + move => [= <-].
        now rewrite app_nil_r.
      + rewrite app_nil_r.
        move/context_subst_fun => Hs. now specialize (Hs _ Hc).
    * intros. split; try discriminate.
      intros H2. pose proof (context_subst_fun' Hc H2).
      rewrite length_app /= in H. now lia.
  - move=> Hc /=. case: a => [na [body|] ty] /=.
    * specialize (IHtele (vdef na body ty :: ctx) args (subst0 s body :: s) args' s').
      move=> /=. rewrite <- app_assoc.
      now forward IHtele by (constructor; auto).
    * destruct args' as [|a args'].
      + split; [congruence | ]. intros Hc'.
        pose proof (context_subst_length2 Hc').
        rewrite !context_assumptions_app ?length_app ?List.length_rev /= Nat.add_0_r in H.
        pose proof (context_subst_length2 Hc). lia.

      + specialize (IHtele (vass na ty :: ctx) (args ++ [a]) (a :: s) args' s').
        forward IHtele. { econstructor. auto. }
        rewrite -app_assoc. rewrite -app_comm_cons /=.
        rewrite -app_assoc in IHtele. apply IHtele.
Qed.

Lemma make_context_subst_spec_inv : forall (tele : list context_decl) (args s' : list term),
  context_subst (List.rev tele) args s' ->
  make_context_subst tele args [] = Some s'.
Proof.
  intros. assert (H:=make_context_subst_recP [] [] [] tele args s').
  forward H by constructor.
  rewrite app_nil_r in H. destruct H.
  simpl in *. auto.
Qed.

Lemma context_subst_subst_extended_subst inst s Δ :
  context_subst Δ inst s ->
  s = map (subst0 (List.rev inst)) (extended_subst Δ 0).
Proof using Type.
  intros sp.
  induction sp.
  - simpl; auto.
  - rewrite List.rev_app_distr /= lift0_id. f_equal.
    rewrite lift_extended_subst.
    rewrite map_map_compose. rewrite IHsp. apply map_ext.
    intros. rewrite (subst_app_decomp [_]). f_equal.
    simpl. rewrite simpl_subst ?lift0_id //.
  - simpl. len.
    f_equal; auto.
    rewrite IHsp.
    rewrite distr_subst. f_equal.
    simpl; len.
    pose proof (context_subst_length2 sp).
    rewrite -H. rewrite -(List.length_rev args).
    rewrite -(Nat.add_0_r #|List.rev args|).
    rewrite simpl_subst_rec; try lia.
    now rewrite lift0_id.
Qed.

From MetaRocq.PCUIC Require Import PCUICSigmaCalculus.


(**************************)
(* Section  mk_ctx_subst  *)
(**************************)

Lemma context_subst_subst_expand_lets inst s Δ t k :
  context_subst Δ inst s ->
  subst s k t = subst (List.rev inst) k (expand_lets_k Δ k t).
Proof.
  move=> /[dup] H /context_subst_subst_extended_subst ->.
  apply: map_subst_expand_lets_k.
  rewrite List.length_rev.
  apply: context_subst_assumptions_length; eassumption.
Qed.


Lemma make_context_subst_context_assumptions Δ args s :
  context_assumptions Δ = #|args| ->
  ∑ s', make_context_subst Δ args s = Some s'.
Proof.
  elim: Δ args s=> [|[?[?|]?] Δ ih].
  + move=> []//=;eexists; reflexivity.
  + move=> /= ??; apply:ih.
  + move=> /= [//|hd tl /=] s eq. apply Nat.succ_inj in eq. apply: ih. exact eq.
Qed.

Definition mk_ctx_subst Δ args := option_get [] (make_context_subst (List.rev Δ) args []).

Lemma mk_ctx_subst_spec {Δ args} :
  context_assumptions Δ = #|args| ->
  context_subst Δ args (mk_ctx_subst Δ args).
Proof.
  rewrite /mk_ctx_subst -context_assumptions_rev.
  move=> /(make_context_subst_context_assumptions _ _ []) [? /[dup] ? ->] /=.
  rewrite -[Δ]rev_involutive.
  by apply: make_context_subst_spec.
Qed.


Lemma mk_ctx_subst_length Δ l :
  context_assumptions Δ = #|l| -> #|mk_ctx_subst Δ l| = #|Δ|.
Proof.
  move=> /mk_ctx_subst_spec /context_subst_length //.
Qed.

From Stdlib Require Import ssrbool.
From MetaRocq.PCUIC Require Import PCUICClosed.
Lemma closedn_ctx_subst_forall n Δ l s :
  context_subst Δ l s ->
  closedn_ctx n Δ ->
  forallb (closedn n) l ->
  forallb (closedn n) s.
Proof.
  move=> z; depind z=> //= /andP[/=? d].
  - rewrite forallb_app=> /andP[?] /andP[/= -> _] /=; by apply: IHz.
  - move=> ?.
    have ? : forallb (closedn n) s by apply: IHz.
    apply/andP; split=> //; apply: closedn_subst0=> //.
    move: d=> /andP /= []; rewrite (context_subst_length z) Nat.add_comm //.
Qed.
