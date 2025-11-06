From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Erasure.Typed Require Import ClosedAux.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Erasure.Typed Require Import Optimize.
From MetaRocq.Erasure.Typed Require Import Transform.
From MetaRocq.Erasure.Typed Require Import WcbvEvalAux.
From Stdlib Require Import Btauto.
From Stdlib Require Import btauto.Algebra.
From Stdlib Require Import List.
From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import PeanoNat.
From Equations Require Import Equations.
From MetaRocq.Erasure Require Import EPrimitive EAstUtils.
From MetaRocq.Erasure Require Import ECSubst.
From MetaRocq.Erasure Require Import EInduction.
From MetaRocq.Erasure Require Import ELiftSubst.
From MetaRocq.Erasure Require Import EWcbvEval.
From MetaRocq.Erasure Require Import EGlobalEnv EWellformed.
From MetaRocq.Utils Require Import MRList.
From MetaRocq.Utils Require Import MRPrelude.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import All_Forall.
Require ssreflect.

Import ExAst.
Import Kernames.
Import ListNotations.

Unset SsrRewrite.

Local Set Firstorder Solver auto.
Ltac Tauto.intuition_solver ::= auto with *.

Lemma lookup_env_trans_env Σ kn :
  EGlobalEnv.lookup_env (trans_env Σ) kn =
  option_map trans_global_decl (lookup_env Σ kn).
Proof.
  unfold lookup_env.
  induction Σ as [|((kn' & has_deps') & cst') Σ IH]; [easy|].
  cbn in *.
  unfold ReflectEq.eqb.
  destruct Kername.reflect_kername as [eq Heq].
  now destruct (Heq kn kn').
Qed.

Lemma declared_constant_trans_env Σ kn ecst :
  declared_constant (trans_env Σ) kn ecst ->
  (exists cst, ecst = trans_cst cst /\ lookup_env Σ kn = Some (ConstantDecl cst)) \/
  (exists ta, ecst = {| EAst.cst_body := option_map (fun _ => tBox) ta |} /\
              lookup_env Σ kn = Some (TypeAliasDecl ta)).
Proof.
  unfold declared_constant.
  rewrite lookup_env_trans_env.
  cbn.
  intros decl.
  destruct (lookup_env Σ kn) as [cst|]; cbn in *; [|congruence].
  destruct cst; cbn in *; [|congruence|]; noconf decl; eauto.
Qed.

Lemma dearg_lambdas_nil t :
  dearg_lambdas [] t = t.
Proof.
  induction t; auto.
  cbn.
  now rewrite IHt2.
Qed.

(** We use our own "properly ordered" contexts to represent the lambdas/lets
    that we debox away. Unlike the rest of MetaRocq, these contexts actually
    have the first declaration at the beginning. *)
Fixpoint subst_context (t : term) (k : nat) (Γ : context) : context :=
  match Γ with
  | [] => []
  | cd :: Γ => map_decl (csubst t k) cd :: subst_context t (S k) Γ
  end.

Definition mkLambda_or_LetIn (cd : context_decl) (t : term) : term :=
  match decl_body cd with
  | None => tLambda (decl_name cd) t
  | Some body => tLetIn (decl_name cd) body t
  end.

Definition it_mkLambda_or_LetIn (Γ : context) (u : term) : term :=
  fold_right mkLambda_or_LetIn u Γ.

Fixpoint decompose_body_masked (mask : bitmask) (t : term) : context * term :=
  match mask, t with
  | _, tLetIn na val body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vdef na val :: Γ, t)
  | b :: mask, tLambda na body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vass na :: Γ, t)
  | _, _ => ([], t)
  end.

Definition vasses (Γ : context) : context :=
  filter (fun cd => match decl_body cd with
                    | Some _ => false
                    | None => true
                    end) Γ.

Lemma vasses_app Γ Γ' :
  vasses (Γ ++ Γ') = vasses Γ ++ vasses Γ'.
Proof.
  unfold vasses.
  now rewrite filter_app.
Qed.

Ltac refold :=
  repeat
    match goal with
    | [H : context[fold_right _ ?t ?Γ] |- _] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [ |- context[fold_right _ ?t ?Γ]] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [H : context[filter _ ?Γ] |- _] => progress (fold (vasses Γ) in * )
    | [ |- context[filter _ ?Γ]] => progress (fold (vasses Γ) in * )
    end.

(*
From Equations Require Import Equations.
Import EEtaExpandedFix EOptimizePropDiscr ESpineView.
Import TermSpineView EInduction.

Lemma list_size_pos {A} (l : list A) (h : l <> []) (size : A -> nat) : list_size size l > 0.
Proof.
  induction l; cbn; try lia. now elim h.
Qed.
Section DeargAuxDecomp.

Context (ind_masks : list (kername * mib_masks)).
Context (const_masks : list (kername * bitmask)).
Notation get_ctor_mask := (get_ctor_mask ind_masks).
Notation get_mib_masks := (get_mib_masks ind_masks).
Notation get_const_mask := (get_const_mask const_masks).

Set Equations Debug.
Equations? dearg_aux_decomp (t : term) : term by wf t (fun x y : EAst.term => size x < size y) :=
  dearg_aux_decomp t with TermSpineView.view t := {
  | tRel i => EAst.tRel i
  | tVar v => EAst.tVar v
  | tBox => EAst.tBox
  | tEvar ev l => EAst.tEvar ev (map_In l (fun x H => dearg_aux_decomp x))
  | tLambda na t => EAst.tLambda na (dearg_aux_decomp t)
  | tLetIn na b t => EAst.tLetIn na (dearg_aux_decomp b) (dearg_aux_decomp t)
  | tApp f args napp nempty with f := {
      | EAst.tConstruct ind c cargs => dearg_single (get_ctor_mask ind c) (EAst.tConstruct ind c cargs) (map_In args (fun x H => dearg_aux_decomp x))
      | EAst.tConst kn => dearg_single (get_const_mask kn) (EAst.tConst kn) (map_In args (fun x H => dearg_aux_decomp x))
      | EAst.tCase (ind, npars) discr brs :=
        let discr := dearg_aux_decomp discr in
        let brs := map_In brs (fun br hin => (br.1, dearg_aux_decomp br.2)) in
        EAst.mkApps (dearg_case ind_masks ind npars discr brs) (map_In args (fun x H => dearg_aux_decomp x))
      | EAst.tProj (mkProjection ind npars arg) t =>
        mkApps (dearg_proj ind_masks ind npars arg (dearg_aux_decomp t)) (map_In args (fun x H => dearg_aux_decomp x))
      | hd => mkApps (dearg_aux_decomp hd) (map_In args (fun x H => dearg_aux_decomp x)) }
  | tConstruct ind c cargs => dearg_single (get_ctor_mask ind c) (EAst.tConstruct ind c cargs) []
  | tConst kn => dearg_single (get_const_mask kn) (EAst.tConst kn) []
  | tCase (ind, npars) discr brs :=
    let discr := dearg_aux_decomp discr in
    let brs := map_In brs (fun br hin => (br.1, dearg_aux_decomp br.2)) in
    dearg_case ind_masks ind npars discr brs
  | tProj (mkProjection ind npars arg) t =>
    dearg_proj ind_masks ind npars arg (dearg_aux_decomp t)
  | tFix mfix idx =>
    EAst.tFix (map_In mfix (fun d hin => {| dname := d.(dname); dbody := dearg_aux_decomp d.(dbody); rarg := d.(rarg) |})) idx
  | tCoFix mfix idx =>
    EAst.tCoFix (map_In mfix (fun d hin => {| dname := d.(dname); dbody := dearg_aux_decomp d.(dbody); rarg := d.(rarg) |})) idx
  | tPrim p => EAst.tPrim (map_primIn p (fun x H => dearg_aux_decomp x)) }.
Proof.
  all:try subst discr; try subst brs; clear dearg_aux_decomp.
  all: cbn.
  all: try lia.
  all:rewrite ?size_mkApps; cbn [size].
  all:(try match goal with H : In ?x ?l |- _ => try (let H' := fresh in assert (H' := In_size id size H); unfold id in H'; change (fun x => size x) with size in H') end); eauto.
  all:(try match goal with H : ?l <> [] |- context [ list_size ?size ?l ] => try (let H' := fresh in assert (H' := list_size_pos l H size)) end); eauto; try lia.
  pose proof (H0 := In_size snd size hin); cbn in H0. lia.
  pose proof (H0 := In_size snd size hin); cbn in H0. lia.
  pose proof (H0 := In_size dbody size hin); cbn in H0. lia.
  pose proof (H0 := In_size dbody size hin); cbn in H0. lia.
  now apply InPrim_size.
Qed. *)

Lemma decompose_body_masked_spec mask Γ t t' :
  valid_dearg_mask mask t ->
  (Γ, t') = decompose_body_masked mask t ->
  #|vasses Γ| = #|mask| /\
  it_mkLambda_or_LetIn Γ t' = t.
Proof.
  revert Γ t' mask.
  induction t using term_forall_list_ind; intros Γ t' mask valid_mask eq.
  all: cbn in *.
  all: try solve [destruct mask; [|easy]; inversion eq; easy].
  - destruct mask as [|b mask]; inversion eq; subst; clear eq; [easy|].
    cbn in *.
    destruct (decompose_body_masked mask t) as (Γ' & t'') eqn:decomp_eq.
    inversion H0; subst; clear H0.
    symmetry in decomp_eq.
    cbn.
    refold.
    propify.
    now destruct (IHt _ _ _ (proj2 valid_mask) decomp_eq) as (-> & ->).
  - destruct (decompose_body_masked mask t2) eqn:decomp_eq.
    symmetry in decomp_eq.
    destruct (IHt2 _ _ _ valid_mask decomp_eq).
    now destruct mask; inversion eq; subst.
Qed.

Lemma valid_dearg_mask_spec mask t :
  valid_dearg_mask mask t ->
  ∑ Γ inner,
    #|vasses Γ| = #|mask| /\ it_mkLambda_or_LetIn Γ inner = t.
Proof.
  intros is_valid.
  destruct (decompose_body_masked mask t) as (Γ & inner) eqn:decomp.
  exists Γ, inner.
  now apply decompose_body_masked_spec.
Qed.

Import Lia.

Lemma subst_it_mkLambda_or_LetIn t k Γ u :
  csubst t k (it_mkLambda_or_LetIn Γ u) =
  it_mkLambda_or_LetIn (subst_context t k Γ) (csubst t (k + length Γ) u).
Proof.
  revert t k u.
  induction Γ as [|cd Γ IH]; intros t k u.
  - cbn.
    f_equal; lia.
  - cbn in *; refold.
    destruct cd as [na [val|]];
      cbn in *; refold;
      repeat (f_equal; rewrite ?IH; try lia).
Qed.

Lemma length_subst_context t k Γ :
  #|subst_context t k Γ| = #|Γ|.
Proof.
  revert t k.
  induction Γ; [easy|]; intros t k.
  cbn.
  now rewrite IHΓ.
Qed.

Lemma is_dead_closed k t n :
  closedn k t ->
  k <= n ->
  is_dead n t.
Proof.
  revert k n.
  induction t using term_forall_list_ind; intros k n' clos klen;
    cbn in *; auto.
  - propify.
    destruct (Nat.eqb_spec n n'); lia.
  - induction X; [easy|].
    cbn in *.
    propify.
    easy.
  - easy.
  - propify.
    easy.
  - propify.
    easy.
  - propify.
    induction X; [easy|].
    cbn in *.
    propify.
    easy.
  - propify.
    induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - easy.
  - revert k n' clos klen.
    induction X; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    rewrite <- Nat.add_succ_r in *.
    now eapply IHX.
  - revert k n' clos klen.
    induction X; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    rewrite <- Nat.add_succ_r in *.
    now eapply IHX.
  - solve_all.
  - solve_all.
  - solve_all.
Qed.

Lemma is_dead_csubst k t u k' :
  is_dead k t ->
  closedn k u ->
  k < k' ->
  is_dead k (csubst u k' t).
Proof.
  revert k u k'.
  induction t using term_forall_list_ind; intros k u k' use_eq clos kltn;
    cbn in *; propify; auto.
  - destruct (Nat.compare_spec k' n) as [->| |].
    + now apply is_dead_closed with k.
    + cbn.
      propify.
      lia.
    + cbn.
      propify.
      lia.
  - induction X; [easy|].
    cbn in *.
    propify.
    easy.
  - apply IHt; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - induction X; [easy|].
    cbn in *.
    propify.
    intuition.
  - induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    assert (closedn (#|l0| + k) u = true) by now eapply closed_upwards.
    easy.
  - rewrite length_map.
    revert k k' kltn use_eq clos.
    induction X; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    split.
    + apply p; [easy| |easy].
      now eapply closed_upwards.
    + rewrite <- !Nat.add_succ_r in *.
      apply IHX; [easy|easy|].
      now eapply closed_upwards.
  - rewrite length_map.
    revert k k' kltn use_eq clos.
    induction X; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    split.
    + apply p; [easy| |easy].
      now eapply closed_upwards.
    + rewrite <- !Nat.add_succ_r in *.
      apply IHX; [easy|easy|].
      now eapply closed_upwards.
  - solve_all_k 6.
Qed.

Lemma valid_dearg_mask_nil t : valid_dearg_mask [] t.
Proof. induction t; easy. Qed.

Lemma valid_dearg_mask_csubst mask t u k :
  valid_dearg_mask mask t ->
  closed u ->
  valid_dearg_mask mask (csubst u k t).
Proof.
  revert mask u k.
  induction t using term_forall_list_ind; intros mask u k valid_mask clos;
    cbn in *;
    try solve [now destruct mask].
  - destruct mask; [|easy].
    apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    propify.
    split.
    + destruct b; [|easy].
      propify.
      now apply (is_dead_csubst 0).
    + now apply IHt.
Qed.

Lemma vasses_subst_context t k Γ :
  vasses (subst_context t k Γ) = vasses Γ.
Proof.
  revert t k.
  induction Γ as [|cd Γ IH]; [easy|]; intros t k.
  cbn in *.
  unfold map_decl.
  destruct cd.
  cbn in *.
  destruct decl_body; cbn.
  - easy.
  - f_equal.
    easy.
Qed.

Lemma dearg_lambdas_subst mask s k Γ inner :
  #|vasses Γ| = #|mask| ->
  dearg_lambdas mask (subst [s] k (it_mkLambda_or_LetIn Γ inner)) =
  subst [s] k (dearg_lambdas mask (it_mkLambda_or_LetIn Γ inner)).
Proof.
  revert mask s k inner.
  induction Γ as [|cd Γ IH]; intros mask s k inner len_eq.
  - destruct mask; [|easy].
    cbn in *.
    rewrite !dearg_lambdas_nil.
    now f_equal.
  - destruct cd as [na [body|]];
      cbn in *; refold.
    + now rewrite IH by easy.
    + destruct mask as [|[] mask].
      * easy.
      * rewrite IH by easy.
        cbn in *.
        unfold subst1.
        now rewrite !distr_subst.
      * now rewrite IH.
Qed.

Lemma dearg_single_masked mask t args :
  #|mask| <= #|args| ->
  dearg_single mask t args = mkApps t (masked mask args).
Proof.
  intros le.
  induction mask in mask, t, args, le |- *.
  - now destruct args.
  - destruct args; [easy|].
    now destruct a; cbn in *; apply IHmask.
Qed.

Lemma eval_dearg_lambdas_inv {wfl : WcbvFlags} Σ mask Γ inner v :
  env_closed Σ ->
  closed (it_mkLambda_or_LetIn Γ inner) ->
  #|mask| = #|vasses Γ| ->
  Σ e⊢ dearg_lambdas mask (it_mkLambda_or_LetIn Γ inner) ⇓ v ->
  ∑ tv, Σ e⊢ it_mkLambda_or_LetIn Γ inner ⇓ tv.
Proof.
  intros env_clos clos len_eq ev.
  induction #|Γ| as [|Γlen IH] eqn:Γlen_eq in Γ, mask, inner, v, clos, len_eq, ev |- *.
  - destruct Γ, mask; try easy.
    cbn in *.
    now rewrite dearg_lambdas_nil in *.
  - destruct Γ as [|[na [body|]] Γ];
      cbn in *; refold.
    + easy.
    + apply eval_tLetIn_inv in ev as (bodyv & ev_body & ev_let).
      propify.
      assert (closed bodyv) by (now eapply eval_closed).
      rewrite closed_subst in ev_let by easy.
      rewrite <- dearg_lambdas_subst in ev_let by easy.
      rewrite <- closed_subst in ev_let by easy.
      rewrite subst_it_mkLambda_or_LetIn in ev_let.
      cbn in *.
      apply IH in ev_let as (tv & ev_tv).
      * exists tv.
        rewrite <- subst_it_mkLambda_or_LetIn in ev_tv.
        now econstructor.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * now rewrite length_subst_context.
    + destruct mask as [|[] mask].
      * easy.
      * eexists.
        now eapply eval_atom.
      * eexists.
        now eapply eval_atom.
Qed.

Lemma no_use_subst k t s s' :
  is_dead k t ->
  subst [s] k t = subst [s'] k t.
Proof.
  revert k.
  induction t using term_forall_list_ind; cbn in *; intros k no_use; propify.
  - easy.
  - destruct (Nat.leb_spec k n).
    + now rewrite !(proj2 (nth_error_None _ _)) by (cbn; lia).
    + easy.
  - easy.
  - f_equal.
    induction X; [easy|].
    cbn in *.
    propify.
    now f_equal.
  - now f_equal.
  - now f_equal.
  - now f_equal.
  - easy.
  - f_equal.
    induction X;cbn in *;propify;intuition.
  - f_equal; [easy|].
    destruct no_use as (_ & no_use).
    induction X; [easy|].
    cbn in *.
    propify.
    destruct x;inversion no_use.
    f_equal; [|easy].
    now f_equal.
  - now f_equal.
  - f_equal.
    revert k no_use.
    induction X; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply p.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- Nat.add_succ_r in *.
      now apply IHX.
  - f_equal.
    revert k no_use.
    induction X; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply p.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- !Nat.add_succ_r in *.
      now apply IHX.
  - f_equal; solve_all.
  - f_equal; solve_all.
  - f_equal; solve_all.
Qed.

Lemma masked_nil {X} mask :
  @masked X mask [] = [].
Proof. now destruct mask as [|[] ?]. Qed.

Lemma All2_masked {X Y} {T : X -> Y -> Type} xs ys mask :
  All2 T xs ys ->
  All2 T (masked mask xs) (masked mask ys).
Proof.
  intros all.
  induction all in mask |- *.
  - now rewrite !masked_nil.
  - destruct mask as [|[] mask]; [now constructor| |]; cbn in *.
    + now apply IHall.
    + now constructor.
Qed.

Lemma dearg_lambdas_correct {wfl : WcbvFlags} Σ body args mask v :
  env_closed Σ ->
  closed body ->
  Forall (closedn 0) args ->
  valid_dearg_mask mask body ->
  #|mask| <= #|args| ->
  Σ e⊢ mkApps body args ⇓ v ->
  Σ e⊢ mkApps (dearg_lambdas mask body) (masked mask args) ⇓ v.
Proof.
  intros env_clos body_clos args_clos valid_mask l ev.
  destruct (valid_dearg_mask_spec _ _ valid_mask) as (Γ & inner & vasses_len & <-).
  induction #|Γ| as [|Γlen IH] eqn:eq
    in Γ, mask, valid_mask, args, body_clos, args_clos, inner, ev, l, vasses_len |- *.
  1: { destruct Γ, mask, args; try easy; cbn in *;
       now rewrite dearg_lambdas_nil. }
  destruct Γ as [|[na [body|]] Γ];
    cbn in *; refold.
  - easy.
  - apply eval_mkApps_head in ev as ev_let.
    destruct ev_let as (letv & ev_let).
    apply eval_tLetIn_inv in ev_let as ev_subst.
    destruct ev_subst as (bodyv & ev_body & ev_subst).
    propify.
    assert (closed bodyv) by (now eapply eval_closed).
    unshelve epose proof
             (IH args mask
                 (subst_context bodyv 0 Γ)
                 (csubst bodyv #|Γ| inner)
                 _ _ _ _ _ _ _) as IH.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply closed_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply valid_dearg_mask_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      eapply (eval_mkApps_heads _ _ _ letv); [easy|easy|].
      now eapply eval_mkApps_heads; [exact ev_let| |]; easy.
    + now rewrite vasses_subst_context.
    + now rewrite length_subst_context.
    + rewrite <- subst_it_mkLambda_or_LetIn in IH.
      apply eval_mkApps_head in IH as ev_top.
      destruct ev_top as (topv & ev_top).
      rewrite subst_it_mkLambda_or_LetIn in ev_top.
      apply eval_dearg_lambdas_inv in ev_top as ev_sub_top; cycle 1.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * destruct ev_sub_top as (sub_top & ev_sub_top).
        rewrite <- subst_it_mkLambda_or_LetIn in ev_top.
        eapply eval_mkApps_heads; [| |now eauto]; [now eauto|].
        econstructor; [easy|].
        rewrite !closed_subst in * by easy.
        now rewrite <- dearg_lambdas_subst.
  - destruct mask as [|b mask]; [easy|];
      cbn in *; refold.
    destruct args as [|a args]; cbn in *; [easy|].
    apply eval_mkApps_head in ev as ev_app.
    destruct ev_app as (appv & ev_app).
    apply eval_tApp_tLambda_inv in ev_app as ev_subst.
    destruct ev_subst as (av & ev_a & ev_subst).
    assert (closed av).
    { apply Forall_inv in args_clos.
      now eapply eval_closed. }
    unshelve epose proof
    (IH args mask
        (subst_context av 0 Γ)
        (csubst av #|Γ| inner)
        _ _ _ _ _ _ _) as IH.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply closed_csubst.
    + now apply Forall_inv_tail in args_clos.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      propify.
      now apply valid_dearg_mask_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now eapply eval_mkApps_heads; [exact ev_app| |]; easy.
    + now rewrite vasses_subst_context.
    + now rewrite length_subst_context.
    + apply eval_mkApps_head in IH as ev_top.
      destruct ev_top as (topv & ev_top).
      apply eval_dearg_lambdas_inv in ev_top as ev_sub_top; cycle 1.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * rewrite <- !subst_it_mkLambda_or_LetIn in *.
        destruct ev_sub_top as (sub_top & ev_sub_top).
        rewrite !closed_subst in * by easy.
        destruct b; cbn in *.
        -- eapply eval_mkApps_heads; [| |now eauto]; [now eauto|].
           unfold subst1.
           rewrite <- dearg_lambdas_subst by easy.
           propify.
           now erewrite no_use_subst.
        -- eapply eval_mkApps_heads; [| |now eauto]; [now eauto|].
           rewrite dearg_lambdas_subst in ev_top by easy.
           rewrite <- closed_subst in ev_top by easy.
           eapply eval_beta; [|easy|easy].
           now eapply eval_atom.
Qed.

Section dearg_correct.
Context (ind_masks : list (kername * mib_masks)).
Context (const_masks : list (kername * bitmask)).
Notation get_ctor_mask := (get_ctor_mask ind_masks).
Notation get_mib_masks := (get_mib_masks ind_masks).
Notation get_const_mask := (get_const_mask const_masks).
Notation dearg := (dearg ind_masks const_masks).
Notation dearg_aux := (dearg_aux ind_masks const_masks).
Notation dearg_env := (dearg_env ind_masks const_masks).
Notation dearg_decl := (dearg_decl ind_masks const_masks).
Notation dearg_cst := (dearg_cst ind_masks const_masks).
Notation dearg_case := (dearg_case ind_masks).
Notation dearg_proj := (dearg_proj ind_masks).
Notation valid_case_masks := (valid_case_masks ind_masks).
Notation valid_proj := (valid_proj ind_masks).
Notation valid_cases := (valid_cases ind_masks).
Notation valid_masks_decl := (valid_masks_decl ind_masks const_masks).
Notation valid_masks_env := (valid_masks_env ind_masks const_masks).
Notation is_expanded_aux := (is_expanded_aux ind_masks const_masks).
Notation is_expanded := (is_expanded ind_masks const_masks).
Notation is_expanded_env := (is_expanded_env ind_masks const_masks).

Lemma dearg_aux_mkApps args args' hd :
  dearg_aux args (mkApps hd args') = dearg_aux (map dearg args' ++ args) hd.
Proof.
  revert args hd.
  induction args' as [|a args' IH]; intros args hd; [easy|].
  cbn.
  now rewrite IH.
Qed.

Lemma dearg_mkApps hd args :
  dearg (mkApps hd args) = dearg_aux (map dearg args) hd.
Proof.
  unfold dearg.
  now rewrite dearg_aux_mkApps, app_nil_r.
Qed.

Ltac refold' :=
  refold;
  change (dearg_aux []) with dearg in *.

Lemma subst_dearg_single s k mask t args :
  subst s k (dearg_single mask t args) =
  dearg_single mask (subst s k t) (map (subst s k) args).
Proof.
  induction mask as [|[] mask IH] in mask, args, k, t |- *; cbn in *.
  - now rewrite subst_mkApps.
  - destruct args.
    + cbn.
      f_equal.
      rewrite IH.
      now rewrite <- commut_lift_subst.
    + apply IH.
  - destruct args.
    + cbn.
      f_equal.
      rewrite IH.
      cbn.
      now rewrite commut_lift_subst.
    + apply IH.
Qed.

Lemma lift_dearg_single n k mask t args :
  lift n k (dearg_single mask t args) = dearg_single mask (lift n k t) (map (lift n k) args).
Proof.
  induction mask as [|[] mask IH] in mask, t, args, k |- *; cbn in *.
  - now rewrite lift_mkApps.
  - destruct args.
    + cbn.
      rewrite IH.
      cbn.
      now symmetry; rewrite permute_lift.
    + apply IH.
  - destruct args; cbn.
    + rewrite IH.
      cbn.
      now symmetry; rewrite permute_lift.
    + apply IH.
Qed.

Lemma dearg_lambdas_lift mask n k t :
  dearg_lambdas mask (lift n k t) = lift n k (dearg_lambdas mask t).
Proof.
  induction t in mask, n, k, t |- *; cbn in *; try easy.
  - now destruct (_ <=? _).
  - destruct mask as [|[] mask]; [easy| |].
    + rewrite IHt.
      change tBox with (lift n k tBox).
      now rewrite <- distr_lift_subst10.
    + now rewrite IHt.
Qed.

Lemma masked_count_zeros {A} (l : list A) mask :
  #|mask| <= #|l| ->
  #|masked mask l| = count_zeros mask + (#|l| - #|mask|).
Proof.
  revert l.
  induction mask.
  - cbn. intros. lia.
  - cbn. intros. destruct l.
    * cbn in *. lia.
    * cbn in *;assert (#|mask| <= #|l|) by lia.
      destruct a;cbn in *.
      ** assert (#|mask| <= #|l|) by lia.
         rewrite IHmask by assumption.
         unfold count_zeros. lia.
      ** rewrite IHmask by assumption.
         unfold count_zeros. lia.
Qed.

Lemma dearg_branch_body_rec_lift i mask n k t :
  (dearg_branch_body_rec i mask (lift n (i + #|mask| + k ) t) ).2 =
    lift n (i + count_zeros mask + k) (dearg_branch_body_rec i mask t).2.
Proof.
  induction mask in i, n, k, t |- *; cbn in *;auto.
  destruct a;cbn.
  - unfold dearg_branch_body_rec in *.
    unfold subst1.
    replace (i + S #|mask| + k) with (i + 1 + (#|mask| + k)) by lia.
    specialize (distr_lift_subst_rec t [tBox] n i (#|mask| + k)) as H.
    cbn in H.
    rewrite <- H.
    now rewrite <- IHmask.
  - replace (i + S #|filter negb mask| + k) with (S i + #|filter negb mask| + k) by lia.
    replace (i + S #|mask| + k) with (S i + #|mask| + k) by lia.
    easy.
Qed.

Lemma lift_dearg_aux n k args t :
  lift n k (dearg_aux args t) = dearg_aux (map (lift n k) args) (lift n k t).
Proof.
  induction t in k, args, t |- * using term_forall_list_ind; cbn in *.
  - now rewrite lift_mkApps.
  - rewrite lift_mkApps.
    cbn.
    now destruct (_ <=? _).
  - now rewrite lift_mkApps.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    induction X; [easy|].
    cbn in *.
    now rewrite p, IHX.
  - rewrite lift_mkApps.
    cbn.
    now rewrite IHt.
  - rewrite lift_mkApps.
    cbn.
    now rewrite IHt1, IHt2.
  - rewrite IHt1.
    cbn.
    now rewrite IHt2.
  - apply lift_dearg_single.
  - now rewrite lift_dearg_single.
  - destruct p.
    rewrite lift_mkApps.
    f_equal.
    unfold dearg_case.
    destruct (get_mib_masks _); last first.
    + cbn.
      rewrite IHt.
      f_equal.
      induction X; [easy|].
      cbn.
      now rewrite p, IHX.
    + cbn.
      rewrite IHt.
      f_equal.
      unfold mapi.
      generalize 0.
      induction X; [easy|]; intros ?.
      cbn in *.
      rewrite IHX.
      f_equal.
      unfold dearg_case_branch,dearg_branch_body.
      remember (complete_ctx_mask _ _) as ctx_mask.
      cbn in *.
      destruct (_ <=? _) eqn:Hmask.
      * f_equal.
        cbn.
        rewrite <- (p _ []).
        propify.
        assert (#|ctx_mask| = #|x.1|) by
          now subst;apply complete_ctx_mask_length.
        rewrite masked_count_zeros by lia.
        rewrite <- Nat.add_assoc.
        specialize (dearg_branch_body_rec_lift 0 ctx_mask n (#|x.1| - #|ctx_mask| + k)) as H1.
        cbn in H1.
        rewrite <- H1.
        now replace (#|ctx_mask| + (#|x.1| - #|ctx_mask| + k)) with (#|x.1| + k) by lia.
      * cbn. unfold on_snd. cbn. now rewrite p.
  - destruct s as [ind c npars].
    rewrite lift_mkApps.
    f_equal.
    unfold dearg_proj.
    destruct (get_mib_masks _); cbn; now rewrite IHt.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    rewrite length_map.
    induction X in k |- *; [easy|].
    cbn in *.
    rewrite <- Nat.add_succ_r.
    rewrite IHX.
    f_equal.
    unfold map_def.
    cbn.
    f_equal.
    now rewrite p.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    rewrite length_map.
    induction X in k |- *; [easy|].
    cbn in *.
    rewrite <- Nat.add_succ_r.
    rewrite IHX.
    f_equal.
    unfold map_def.
    cbn.
    f_equal.
    now rewrite p.
  - rewrite lift_mkApps. f_equal. simpl lift. f_equal. solve_all.
  - rewrite lift_mkApps. f_equal. simpl lift. f_equal. solve_all.
  - rewrite lift_mkApps. f_equal. simpl lift. f_equal. solve_all.
Qed.

Lemma lift_dearg n k t :
  lift n k (dearg t) = dearg (lift n k t).
Proof. apply lift_dearg_aux. Qed.

Lemma is_dead_lift_other k k' n t :
  k < k' ->
  is_dead k (lift n k' t) = is_dead k t.
Proof.
  intros lt.
  induction t using term_forall_list_ind in t, k, k', lt |- *; cbn in *.
  - easy.
  - repeat
      (try destruct (_ <=? _) eqn:?; propify;
       try destruct (_ =? _) eqn:?; propify;
       cbn in * );
       lia.
  - easy.
  - induction X; [easy|].
    cbn in *.
    now rewrite p, IHX.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - easy.
  - induction X; [easy|].
    cbn in *;propify.
    rewrite IHX.
    now rewrite p by lia.
  - rewrite IHt by easy.
    f_equal.
    induction X; [easy|].
    destruct x;cbn in *.
    now rewrite p0, IHX.
  - now rewrite IHt.
  - rewrite length_map.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by lia.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - rewrite length_map.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by lia.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - solve_all.
  - solve_all.
  - solve_all.
Qed.

Lemma is_dead_lift_all k k' n t :
  k <= k' ->
  k' < n + k ->
  is_dead k' (lift n k t).
Proof.
  intros l1 l2.
  induction t using term_forall_list_ind in t, n, k, k', l1, l2 |- *; cbn in *; auto.
  - destruct (_ <=? _) eqn:?; cbn; propify; lia.
  - induction X; [easy|].
    cbn in *.
    now rewrite p.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - induction X; [easy|].
    cbn in *;propify.
    rewrite IHX.
    now rewrite p by lia.
  - rewrite IHt by easy.
    cbn.
    clear IHt.
    induction X; [easy|].
    cbn.
    now rewrite p0.
  - rewrite length_map.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - rewrite length_map.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - solve_all.
Qed.

Lemma is_dead_subst_other k k' s t :
  k < k' ->
  is_dead k (subst s k' t) = is_dead k t.
Proof.
  intros lt.
  induction t in t, k, k', lt |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _) eqn:?, (_ =? _) eqn:?; propify; subst.
    + lia.
    + destruct (nth_error _ _) eqn:nth.
      * now apply is_dead_lift_all.
      * cbn.
        destruct (_ =? _) eqn:?; propify; [|easy].
        apply nth_error_None in nth.
        lia.
    + cbn.
      now rewrite Nat.eqb_refl.
    + cbn.
      propify.
      lia.
  - induction X; [easy|].
    cbn in *.
    now rewrite p.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - induction X; [easy|].
    cbn in *;propify.
    rewrite IHX.
    now rewrite p by lia.
  - rewrite IHt by easy; cbn; clear IHt.
    f_equal.
    induction X; [easy|].
    destruct x;cbn in *.
    now rewrite p0.
  - rewrite length_map.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by easy.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - rewrite length_map.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by easy.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - solve_all.
Qed.

Lemma valid_dearg_mask_lift mask n k t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (lift n k t).
Proof.
  intros valid.
  induction t in mask, n, k, t, valid |- *; cbn in *; try easy.
  - destruct mask; [|easy].
    now apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    destruct b; [|now apply IHt].
    propify.
    now rewrite is_dead_lift_other by easy.
Qed.

Lemma valid_dearg_mask_branch_lift i mask t n k k' :
  i + #|mask| <= k' ->
  valid_dearg_mask_branch i mask t = true ->
  valid_dearg_mask_branch i mask (lift n (k' + k) t) = true.
Proof.
  intros valid.
  induction mask in mask, i, n, k, k', t, valid |- *;cbn in *;try easy.
  destruct a.
  - propify.
    split.
    * now rewrite is_dead_lift_other by lia.
    * replace (i + S #|mask| + k) with (S i + #|mask| + k) by lia.
      now apply IHmask.
  - cbn.
    now apply IHmask.
Qed.

Lemma valid_dearg_mask_subst mask s k t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (subst s k t).
Proof.
  intros valid.
  induction t in mask, k, t, valid |- *; cbn in *; try easy.
  - destruct mask; [|easy].
    now apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    destruct b; [|now apply IHt].
    propify.
    now rewrite is_dead_subst_other by easy.
Qed.

Lemma subst_dearg_lambdas s k mask t :
  valid_dearg_mask mask t ->
  subst s k (dearg_lambdas mask t) = dearg_lambdas mask (subst s k t).
Proof.
  intros valid.
  induction t in k, mask, t, valid |- *; cbn in *; try easy.
  - destruct mask; [|easy].
    now rewrite dearg_lambdas_nil.
  - destruct mask as [|[] mask]; [easy| |]; cbn in *; propify.
    + unfold subst1.
      now rewrite distr_subst, IHt.
    + now rewrite IHt.
  - now rewrite IHt2.
Qed.

Lemma dearg_branch_body_rec_subst i mask s k t :
  (dearg_branch_body_rec i mask (subst s (i + #|mask| + k ) t)).2 =
    subst s (i + count_zeros mask + k) (dearg_branch_body_rec i mask t).2.
Proof.
  induction mask in i, s, k, t |- *; cbn in *;auto.
  destruct a;cbn.
  - unfold dearg_branch_body_rec in *.
    unfold subst1.
    replace (i + S #|mask| + k) with (i + 1 + (#|mask| + k)) by lia.
    specialize (distr_subst_rec t [tBox] s (#|mask| + k) i) as H.
    cbn in H.
    rewrite <- H.
    now rewrite <- IHmask.
  - replace (i + S #|filter negb mask| + k) with (S i + #|filter negb mask| + k) by lia.
    replace (i + S #|mask| + k) with (S i + #|mask| + k) by lia.
    easy.
Qed.

Lemma subst_dearg_case s k ind c discr brs :
  valid_case_masks ind c brs ->
  subst s k (dearg_case ind c discr brs) =
  dearg_case ind c (subst s k discr) (map (fun br : list BasicAst.name × term => (br.1, subst s (#|br.1| + k) br.2)) brs).
Proof.
  intros valid.
  unfold dearg_case, valid_case_masks in *.
  destruct (get_mib_masks _) as [masks|];cbn;[|easy].
  cbn.
  f_equal.
  rewrite map_mapi, mapi_map.
  propify.
  destruct valid as (? & valid).
  eapply Alli_mapi_spec; [apply alli_Alli; eassumption|]. cbn.
  clear valid.
  intros ? [bctx t] valid.
  cbn in *.
  unfold dearg_case_branch.
  cbn.
  f_equal.
  apply andb_true_iff in valid as [Hmasks ?].
  rewrite Hmasks;cbn.
  unfold dearg_branch_body;cbn.
  remember (complete_ctx_mask _ _) as ctx_mask.
  assert (#|ctx_mask| = #|bctx|) by now subst;propify;apply complete_ctx_mask_length.
  rewrite masked_count_zeros by lia.
  f_equal. symmetry.
  rewrite <- Nat.add_assoc.
  specialize (dearg_branch_body_rec_subst 0 ctx_mask s (#|bctx| - #|ctx_mask| + k) t) as Hb.
  cbn in Hb.
  now replace (#|ctx_mask| + (#|bctx| - #|ctx_mask| + k)) with (#|bctx| + k) in Hb by lia.
Qed.

Lemma dearg_single_enough_args mask t args :
  dearg_single mask t args =
  mkApps (dearg_single mask t (firstn #|mask| args)) (skipn #|mask| args).
Proof.
  induction mask as [|b mask IH] in mask, t, args |- *; cbn in *.
  - now rewrite skipn_0.
  - destruct args as [|a args].
    + now rewrite skipn_nil.
    + cbn.
      rewrite skipn_cons.
      destruct b; apply IH.
Qed.

Lemma dearg_expanded_aux k t args :
  is_expanded_aux k t ->
  dearg_aux args t = mkApps (dearg_aux (firstn k args) t) (skipn k args).
Proof.
  intros expanded.
  induction t in k, t, args, expanded |- * using term_forall_list_ind; cbn in *;
    refold';
    try now rewrite <- mkApps_app, firstn_skipn.
  - propify; intuition auto.
    now erewrite IHt1 by eassumption.
  - propify.
    symmetry; rewrite dearg_single_enough_args; symmetry.
    rewrite <- mkApps_app, firstn_firstn.
    replace (Init.Nat.min _ _) with #|get_const_mask s| by lia.
    rewrite dearg_single_enough_args.
    f_equal.
    now rewrite skipn_firstn_slice by assumption.
  - propify.
    symmetry; rewrite dearg_single_enough_args; symmetry.
    rewrite <- mkApps_app, firstn_firstn.
    replace (Init.Nat.min _ _) with #|get_ctor_mask i n| by lia.
    rewrite dearg_single_enough_args.
    f_equal.
    now rewrite skipn_firstn_slice by assumption.
  - destruct p.
    now rewrite <- mkApps_app, firstn_skipn.
  - destruct s.
    now rewrite <- mkApps_app, firstn_skipn.
Qed.

Lemma dearg_expanded t args :
  is_expanded t ->
  dearg_aux args t = mkApps (dearg t) args.
Proof. apply dearg_expanded_aux. Qed.

Lemma is_expanded_aux_lift k n k' t :
  is_expanded_aux k (lift n k' t) = is_expanded_aux k t.
Proof.
  induction t in n, k, k', t |- * using term_forall_list_ind; cbn in *; auto.
  - now destruct (_ <=? _).
  - induction X; [easy|].
    cbn in *.
    now rewrite p, IHX.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - induction X in k' |- *; [now f_equal|].
    cbn.
    rewrite p0.
    destruct (is_expanded_aux _ x.2);cbn;auto.
    btauto.
  - induction X in k' |- *; [easy|].
    cbn.
    rewrite <- Nat.add_succ_r.
    now rewrite p, IHX.
  - induction X in k' |- *; [easy|].
    cbn.
    rewrite <- Nat.add_succ_r.
    now rewrite p, IHX.
  - solve_all.
Qed.

Lemma is_expanded_lift n k t :
  is_expanded (lift n k t) = is_expanded t.
Proof. apply is_expanded_aux_lift. Qed.

Lemma is_dead_mkApps k t args :
  is_dead k (mkApps t args) = is_dead k t && forallb (is_dead k) args.
Proof.
  induction args using List.rev_ind; cbn in *.
  - now btauto.
  - rewrite mkApps_app, forallb_app.
    cbn.
    rewrite IHargs.
    now btauto.
Qed.

Lemma is_dead_lift k k' n t :
  k' <= k ->
  n + k' <= k ->
  is_dead k (lift n k' t) = is_dead (k - n) t.
Proof.
  intros l1 l2.
  induction t in k, k', n, t, l1, l2 |- * using term_forall_list_ind; cbn in *; auto.
  - repeat
      (try destruct (_ <=? _) eqn:?; propify;
       try destruct (_ =? _) eqn:?; propify;
       cbn in * );
       lia.
  - induction X; [easy|].
    cbn in *.
    now rewrite p.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - induction X; [easy|].
    cbn in *;propify.
    rewrite IHX.
    now rewrite p by lia.
  - rewrite IHt by easy.
    f_equal.
    induction X; cbn in *; [easy|].
    destruct x;cbn.
    f_equal.
    * now rewrite p0;cbn;auto.
    * apply IHX.
  - rewrite length_map.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    rewrite IHX by easy.
    now replace (S (k - n)) with (S k - n) by lia.
  - rewrite length_map.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    rewrite IHX by easy.
    now replace (S (k - n)) with (S k - n) by lia.
  - solve_all.
Qed.

Lemma is_dead_dearg_single k mask t args :
  is_dead k t ->
  Forall (is_dead k) args ->
  is_dead k (dearg_single mask t args).
Proof.
  intros no_use args_no_use.
  induction mask as [|[] mask IH] in k, mask, t, args, no_use, args_no_use |- *; cbn in *.
  - rewrite is_dead_mkApps, no_use.
    now apply forallb_Forall.
  - destruct args; cbn.
    + apply IH; [|easy].
      rewrite is_dead_lift by lia.
      cbn.
      now rewrite Nat.sub_0_r.
    + apply IH; [easy|].
      now inversion args_no_use.
  - destruct args; cbn.
    + apply IH; [|easy].
      cbn.
      rewrite Bool.andb_true_r.
      rewrite is_dead_lift by lia.
      cbn.
      now rewrite Nat.sub_0_r.
    + inversion args_no_use.
      apply IH; [|easy].
      cbn.
      now propify.
Qed.

Ltac bia :=
  repeat (destruct (is_dead _ _); cbn;
          rewrite ?Bool.orb_true_r, ?Bool.orb_false_r, ?Bool.andb_false_r; auto).

Lemma is_dead_subst s k k' t :
  k' <= k ->
  is_dead k (subst [s] k' t) =
  is_dead (S k) t && (is_dead k' t || is_dead (k - k') s).
Proof.
  intros le.
  induction t in t, k, k', le |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _) eqn:?; propify; cbn.
    + destruct (nth_error _ _) eqn:nth.
      * replace n with k' in * by (now apply nth_error_Some_length in nth; cbn in * ).
        rewrite Nat.sub_diag in nth.
        cbn in *.
        noconf nth.
        rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq _ _)) by easy.
        now rewrite is_dead_lift.
      * cbn.
        apply nth_error_None in nth.
        cbn in *.
        repeat (destruct (_ =? _) eqn:?; propify); auto; try lia.
    + destruct (n =? k) eqn:?, (n =? S k) eqn:?, (n =? k') eqn:?; propify; cbn in *; auto; lia.
   - induction X; [easy|].
     cbn.
     rewrite !p, !IHX by easy.
     bia.
   - now rewrite IHt.
   - rewrite IHt1, IHt2 by easy.
     replace (S k - S k') with (k - k') by lia.
     bia.
   - rewrite IHt1, IHt2 by easy.
     bia.
   - induction X; [easy|].
     cbn in *;propify.
     rewrite IHX.
     rewrite p by lia.
     bia.
   - rewrite IHt by easy.
     clear IHt.
     induction X; cbn in *; [bia|].
     destruct x as [bctx br];cbn in *.
     rewrite p0 by easy.
     replace (#|bctx| + S k) with (S (#|bctx| + k)) by lia.
     replace (#|bctx| + k - (#|bctx| + k')) with (k - k') by lia.
     bia;cbn in *.
     + now rewrite Bool.orb_true_r in IHX.
     + now rewrite Bool.orb_false_r in IHX.
   - rewrite length_map.
     induction X in X, m, k, k', le |- *; cbn in *; [easy|].
     rewrite p by easy.
     specialize (IHX (S k) (S k') ltac:(lia)).
     rewrite !Nat.sub_succ in *.
     replace (#|l| + k - (#|l| + k')) with (k - k') by lia.
     rewrite <- !Nat.add_succ_r.
     rewrite IHX.
     bia.
   - rewrite length_map.
     induction X in X, m, k, k', le |- *; cbn in *; [easy|].
     rewrite p by easy.
     specialize (IHX (S k) (S k') ltac:(lia)).
     rewrite !Nat.sub_succ in *.
     replace (#|l| + k - (#|l| + k')) with (k - k') by lia.
     rewrite <- !Nat.add_succ_r.
     rewrite IHX.
     bia.
    - solve_all. rtoProp; intuition eauto.
      depelim X; cbn; eauto.
      destruct a; unfold test_array_model; cbn.
      destruct p. cbn in *. rewrite e; eauto.
      rewrite <- !andb_assoc. f_equal.
      rewrite andb_comm.
      induction a; cbn. rewrite andb_true_r; auto.
      rewrite <- !andb_assoc.
      rewrite IHa. rewrite p;eauto.
      rewrite <- !andb_assoc. f_equal.
      rewrite andb_comm.
      rewrite <- !andb_assoc. f_equal.
      bia. now rewrite andb_true_r.
Qed.

Lemma is_dead_dearg_lambdas k mask t :
  is_dead k (dearg_lambdas mask t) = is_dead k t.
Proof.
  induction t in k, mask, t |- *; cbn in *; try easy.
  destruct mask as [|[] mask]; [easy| |]; cbn in *.
  - unfold subst1.
    rewrite is_dead_subst, IHt, Nat.sub_0_r by easy.
    cbn.
    now btauto.
  - now rewrite IHt.
Qed.

Lemma is_dead_dearg_branch_body i k mask t :
  is_dead (i + count_zeros mask + k) ((dearg_branch_body_rec i mask t)).2 = is_dead (i + #|mask| + k) t.
Proof.
  induction mask in t, i, k, mask, t |- *; cbn in *;auto.
  destruct a;cbn.
  - unfold subst1.
    replace (i + S #|mask| + k) with (S i + #|mask| + k) by lia.
    unfold dearg_branch_body_rec in IHmask.
    rewrite IHmask.
    rewrite is_dead_subst by lia.
    replace (i + #|mask| + k - i) with (#|mask| + k) by lia.
    cbn.
    now btauto.
  - replace (i + S #|mask| + k) with (S i + #|mask| + k) by lia.
    replace (i + S #|filter negb mask| + k) with (S i + #|filter negb mask| + k) by lia.
    apply IHmask.
Qed.

Lemma is_dead_dearg_case k ind npars discr brs :
  is_dead k (dearg_case ind npars discr brs) =
  is_dead k discr && forallb (fun '(ctx, t) => is_dead (#|ctx| + k) t) brs.
Proof.
  unfold dearg_case.
  destruct (get_mib_masks _); cbn; [|easy].
  f_equal.
  unfold mapi.
  generalize 0.
  induction brs; intros; [easy|].
  cbn in *.
  rewrite IHbrs.
  f_equal.
  destruct a;cbn. unfold dearg_case_branch;cbn.
  destruct (_ <=? _) eqn:Hmask.
  - cbn.
    remember (complete_ctx_mask _ _) as mm.
    assert (#|mm| = #|l|) by now subst;propify;apply complete_ctx_mask_length.
    rewrite masked_count_zeros by lia.
    specialize (is_dead_dearg_branch_body 0 ((#|l| - #|mm|) + k) mm t) as b.
    cbn in b.
    replace (#|mm| + (#|l| - #|mm| + k)) with (#|l| + k) in b by lia.
    now rewrite <- Nat.add_assoc.
  - reflexivity.
Qed.

Lemma is_dead_dearg_aux k t args :
  is_dead k t ->
  Forall (is_dead k) args ->
  is_dead k (dearg_aux args t).
Proof.
  intros no_use args_no_use.
  induction t using term_forall_list_ind in k, t, args, no_use, args_no_use |- *;
    cbn in *; rewrite ?is_dead_mkApps; cbn.
  - now apply forallb_Forall.
  - now rewrite no_use; apply forallb_Forall.
  - now apply forallb_Forall.
  - propify; split; [|now apply forallb_Forall].
    induction X; [easy|]; cbn in *; propify.
    now rewrite p, IHX.
  - rewrite IHt by easy.
    now apply forallb_Forall.
  - propify.
    rewrite IHt1, IHt2 by easy.
    split; [easy|now apply forallb_Forall].
  - propify.
    now rewrite IHt1.
  - now apply is_dead_dearg_single.
  - now apply is_dead_dearg_single.
  - destruct p.
    rewrite is_dead_mkApps, is_dead_dearg_case.
    propify.
    split; [|now apply forallb_Forall].
    split; [now apply IHt|].
    induction X; [easy|]; cbn in *; propify.
    destruct x;cbn in *.
    rewrite p by easy.
    split; [easy|].
    now apply IHX.
  - destruct s.
    rewrite is_dead_mkApps.
    propify; split; [|now apply forallb_Forall].
    unfold dearg_proj.
    now destruct (get_mib_masks _); apply IHt.
  - rewrite length_map.
    propify; split; [|now apply forallb_Forall].
    induction X in k, m, X, no_use |- *; [easy|].
    cbn in *; propify.
    rewrite <- !Nat.add_succ_r in *.
    rewrite p by easy.
    split; [easy|].
    now apply IHX.
  - rewrite length_map.
    propify; split; [|now apply forallb_Forall].
    induction X in k, m, X, no_use |- *; [easy|].
    cbn in *; propify.
    rewrite <- !Nat.add_succ_r in *.
    rewrite p by easy.
    split; [easy|].
    now apply IHX.
  - solve_all. rtoProp; intuition solve_all.
  - solve_all. rtoProp; intuition solve_all.
  - solve_all. rtoProp; intuition solve_all.
Qed.

Lemma valid_dearg_mask_dearg mask t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (dearg t).
Proof.
  intros valid.
  induction t in mask, t, valid |- *; cbn in *; try easy;
    try solve [destruct mask; [|easy]; apply valid_dearg_mask_nil].
  destruct mask as [|[] mask]; try easy.
  cbn in *.
  propify.
  now rewrite is_dead_dearg_aux.
Qed.

Lemma valid_dearg_mask_branch_dearg mask t i :
  valid_dearg_mask_branch i mask t ->
  valid_dearg_mask_branch i mask (dearg t).
Proof.
  intros.
  induction mask in i, H |- *;cbn in *;auto.
  destruct a.
  - propify. rewrite IHmask.
    unfold dearg. now rewrite is_dead_dearg_aux.
    easy.
  - easy.
Qed.

Lemma valid_case_masks_dearg_branches ind npars brs :
  valid_case_masks ind npars brs ->
  valid_case_masks ind npars (map (on_snd dearg) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  propify.
  destruct valid.
  split; [easy|].
  apply alli_Alli.
  apply alli_Alli in H0.
  rewrite <- mapi_cst_map.
  unfold mapi.
  apply Alli_mapi with (f := (fun _ : nat => on_snd dearg)).
  eapply Alli_impl; [eassumption|].
  cbn.
  intros n [] valid.
  propify.
  split; [easy|].
  cbn.
  now apply valid_dearg_mask_branch_dearg.
Qed.

Lemma dearg_aux_subst s k t args :
  valid_cases t ->
  Forall (fun s => is_expanded s) s ->
  dearg_aux (map (subst (map dearg s) k ∘ dearg) args) (subst s k t) =
  subst (map dearg s) k (dearg_aux (map dearg args) t).
Proof.
  intros vcases es.
  induction t using term_forall_list_ind in s, k, t, args, vcases, es |- *; cbn in *; refold'.
  - now rewrite subst_mkApps, map_map.
  - rewrite subst_mkApps, map_map.
    cbn in *.
    destruct (_ <=? _) eqn:?; propify; [|easy].
    rewrite nth_error_map.
    destruct (nth_error _ _) eqn:nth; cbn.
    + rewrite dearg_expanded, lift_dearg; [easy|].
      rewrite is_expanded_lift.
      now eapply nth_error_forall in nth; [|eassumption].
    + now rewrite length_map.
  - now rewrite subst_mkApps, map_map.
  - rewrite subst_mkApps, map_map.
    cbn in *.
    rewrite !map_map.
    f_equal.
    f_equal.
    induction X; [easy|].
    cbn in *.
    propify.
    f_equal.
    + now apply (p _ _ []).
    + now apply IHX.
  - rewrite subst_mkApps, map_map.
    cbn.
    f_equal.
    f_equal.
    now apply (IHt _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    propify.
    f_equal.
    f_equal.
    + now apply (IHt1 _ _ []).
    + now apply (IHt2 _ _ []).
  - propify.
    specialize (IHt1 s k (t2 :: args)).
    cbn in *.
    rewrite <- IHt1 by easy.
    f_equal.
    f_equal.
    now apply (IHt2 _ _ []).
  - now rewrite subst_dearg_single, map_map.
  - destruct args0;try congruence.
    now rewrite subst_dearg_single, map_map.
  - destruct p.
    propify.
    rewrite subst_mkApps, !map_map, subst_dearg_case by (now apply valid_case_masks_dearg_branches).
    f_equal.
    f_equal; [now apply (IHt _ _ [])|].
    destruct vcases as ((_ & vcases) & _).
    clear -X vcases es X.
    induction X; [easy|].
    cbn in *.
    propify.
    f_equal; [f_equal|].
    + specialize (p s (#|x.1| + k) []). cbn in *.
      unfold dearg in *;cbn in *.
      now rewrite <- p.
    + now apply IHX.
  - destruct s0.
    rewrite subst_mkApps, map_map.
    f_equal.
    unfold dearg_proj.
    cbn in *; propify.
    f_equal.
    now apply (IHt _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    rewrite !map_map.
    f_equal.
    cbn.
    f_equal.
    rewrite length_map.
    revert k; induction X; intros k; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    f_equal; [|now apply IHX].
    unfold map_def; cbn.
    f_equal.
    now apply (p _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    rewrite !map_map.
    f_equal.
    cbn.
    f_equal.
    rewrite length_map.
    revert k; induction X; intros k; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    f_equal; [|now apply IHX].
    unfold map_def; cbn.
    f_equal.
    now apply (p _ _ []).
  - rewrite subst_mkApps, map_map; cbn; f_equal. f_equal.
    solve_all. eapply map_prim_eq_prop; tea; cbn; intuition eauto.
    specialize (a s k []). eauto.
  - rewrite subst_mkApps, map_map; cbn; f_equal.
    f_equal. specialize (IHt s k []); cbn in IHt. eauto.
  - rewrite subst_mkApps, map_map; cbn; f_equal.
    f_equal. specialize (IHt s k []); cbn in IHt. eauto.
Qed.

Lemma dearg_subst s k t :
  valid_cases t ->
  Forall (fun s => is_expanded s) s ->
  dearg (subst s k t) = subst (map dearg s) k (dearg t).
Proof. now intros; apply (dearg_aux_subst _ _ _ []). Qed.

Lemma valid_cases_mkApps_inv hd args :
  valid_cases (mkApps hd args) ->
  valid_cases hd /\ Forall valid_cases args.
Proof.
  intros valid.
  induction args using List.rev_ind; [easy|].
  rewrite mkApps_app in *.
  cbn in *.
  propify.
  intuition auto.
  apply app_Forall; intuition.
Qed.

Lemma is_expanded_aux_mkApps_eq n hd args :
  is_expanded_aux n (mkApps hd args) =
  is_expanded_aux (n + #|args|) hd && forallb is_expanded args.
Proof.
  induction args in args, n |- * using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, forallb_app.
    cbn.
    rewrite IHargs.
    rewrite length_app, Bool.andb_true_r.
    cbn in *.
    rewrite !Bool.andb_assoc.
    symmetry; rewrite Bool.andb_comm; symmetry.
    rewrite <- !Bool.andb_assoc.
    f_equal.
    f_equal.
    f_equal.
    lia.
Qed.

Lemma is_expanded_mkApps_eq hd args :
  is_expanded (mkApps hd args) = is_expanded_aux #|args| hd && forallb is_expanded args.
Proof. now apply is_expanded_aux_mkApps_eq. Qed.

Lemma is_expanded_aux_mkApps_inv n hd args :
  is_expanded_aux n (mkApps hd args) ->
  is_expanded_aux (n + #|args|) hd /\ Forall is_expanded args.
Proof.
  intros exp.
  rewrite is_expanded_aux_mkApps_eq in exp.
  propify.
  split; [easy|].
  now apply forallb_Forall.
Qed.

Lemma is_expanded_aux_mkApps n hd args :
  is_expanded_aux (n + #|args|) hd ->
  Forall (fun a => is_expanded a) args ->
  is_expanded_aux n (mkApps hd args).
Proof.
  intros exp_hd exp_args.
  rewrite is_expanded_aux_mkApps_eq.
  rewrite exp_hd.
  now apply forallb_Forall.
Qed.

Lemma is_expanded_aux_upwards n t n' :
  is_expanded_aux n t ->
  n <= n' ->
  is_expanded_aux n' t.
Proof.
  intros exp l.
  induction t in n, t, n', l, exp |- * using term_forall_list_ind; cbn in *; propify; easy.
Qed.

Lemma is_expanded_csubst s n t k :
  is_expanded_aux 0 s ->
  is_expanded_aux n t ->
  is_expanded_aux n (csubst s k t).
Proof.
  intros exps expt.
  induction t in s, n, t, k, exps, expt |- * using term_forall_list_ind; cbn in *.
  - easy.
  - destruct (Nat.compare_spec k n0) as [<-| |].
    + now eapply is_expanded_aux_upwards.
    + easy.
    + easy.
  - easy.
  - induction X; [easy|].
    cbn in *; propify.
    now rewrite p, IHX.
  - now apply IHt.
  - now propify.
  - now propify.
  - easy.
  - easy.
  - propify.
    split.
    * now rewrite IHt.
    * rewrite forallb_map;cbn.
      induction X in X, k, expt |- *; [easy|].
      cbn in *. now propify.
  - easy.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
  - solve_all_k 6.
  - solve_all.
  - solve_all.
Qed.

Lemma is_expanded_aux_subst s n t k :
  is_expanded_aux 0 s ->
  is_expanded_aux n t ->
  is_expanded_aux n (subst [s] k t).
Proof.
  intros exps expt.
  induction t in s, n, t, k, exps, expt |- * using term_forall_list_ind; cbn in *.
  - easy.
  - destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|easy].
    destruct (_ - _); cbn in *.
    + noconf nth.
      rewrite is_expanded_aux_lift.
      now eapply is_expanded_aux_upwards.
    + now rewrite nth_error_nil in nth.
  - easy.
  - induction X; [easy|].
    cbn in *; propify.
    now rewrite p, IHX.
  - now apply IHt.
  - now propify.
  - now propify.
  - easy.
  - easy.
  - propify.
    split.
    * now rewrite IHt.
    * rewrite forallb_map;cbn.
      induction X in X, k, expt |- *; [easy|].
      cbn in *. now propify.
  - easy.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
  - solve_all_k 6.
  - solve_all.
  - solve_all.
Qed.

Lemma is_expanded_substl s n t :
  Forall (fun s => is_expanded s) s ->
  is_expanded_aux n t ->
  is_expanded_aux n (substl s t).
Proof.
  intros all exp.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_snoc in all.
  now apply is_expanded_csubst.
Qed.

Lemma Forall_is_expanded_fix_subst defs :
  Forall (is_expanded ∘ dbody) defs ->
  Forall is_expanded (fix_subst defs).
Proof.
  intros all.
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma Forall_is_expanded_cofix_subst defs :
  Forall (is_expanded ∘ dbody) defs ->
  Forall is_expanded (cofix_subst defs).
Proof.
  intros all.
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma is_expanded_cunfold_fix defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  Forall (fun d => is_expanded (dbody d)) defs ->
  is_expanded f.
Proof.
  intros cuf all.
  unfold cunfold_fix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply is_expanded_substl; [|easy].
  now apply Forall_is_expanded_fix_subst.
Qed.

Lemma is_expanded_cunfold_cofix defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  Forall (fun d => is_expanded (dbody d)) defs ->
  is_expanded f.
Proof.
  intros cuf all.
  unfold cunfold_cofix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply is_expanded_substl; [|easy].
  now apply Forall_is_expanded_cofix_subst.
Qed.

Lemma eq_kername_eq (kn0 kn1 : kername) :
  kn0 == kn1 -> kn0 = kn1.
Proof.
  intros kn_eq.
  unfold eq_kername in *.
  destruct Kername.reflect_kername as [eq Heq].
  now destruct (Heq kn0 kn1).
Qed.

Lemma lookup_env_Forall {P} Σ kn decl :
  lookup_env Σ kn = Some decl ->
  Forall P Σ ->
  ∑ b, P (kn, b, decl).
Proof.
  intros look all.
  unfold lookup_env in *.
  destruct find as [((kn' & b) & decl')|] eqn:find; cbn in *; [|congruence].
  noconf look.
  apply find_some in find as (isin & name_eq).
  apply eq_kername_eq in name_eq.
  rewrite Forall_forall in all;subst.
  now eexists; apply all.
Qed.

Lemma is_expanded_constant Σ kn cst body :
  is_expanded_env Σ ->
  EGlobalEnv.declared_constant (trans_env Σ) kn cst ->
  EAst.cst_body cst = Some body ->
  is_expanded body.
Proof.
  intros exp_env decl body_eq.
  unfold is_expanded_env in *.
  apply forallb_Forall in exp_env.
  apply declared_constant_trans_env in decl as [(? & -> & look)|(? & -> & look)]; cbn in *.
  - eapply lookup_env_Forall in look as (? & P); eauto.
    destruct x.
    cbn in *.
    now rewrite body_eq in P.
  - destruct x; cbn in *; [|congruence].
    now replace body with tBox by congruence.
Qed.

Lemma eval_is_expanded_aux {wfl : WcbvFlags} Σ t v k :
  with_constructor_as_block = false ->
  trans_env Σ e⊢ t ⇓ v ->
  is_expanded_env Σ ->
  is_expanded_aux k t ->
  is_expanded_aux k v.
Proof.
  intros ? ev exp_env exp_t.
  induction ev in t, v, k, ev, exp_t |- *; auto; cbn in *; propify;try congruence.
  - apply IHev3.
    apply is_expanded_csubst; intuition auto.
    now eapply is_expanded_aux_upwards.
  - apply IHev2.
    apply is_expanded_csubst; intuition auto.
    now eapply is_expanded_aux_upwards.
  - apply IHev2.
    unfold EGlobalEnv.iota_red.
    specialize (IHev1 0 ltac:(easy)).
    apply is_expanded_aux_mkApps_inv in IHev1 as (exp_hd & exp_args); cbn in *.
    apply is_expanded_substl.
    + apply Forall_rev. now apply Forall_skipn.
    + destruct br as [bctx br];cbn in *.
      destruct exp_t as [? exp_brs].
      eapply forallb_nth_error in exp_brs;eauto;cbn in *.
      rewrite e2 in exp_brs;cbn in *.
      now eapply is_expanded_aux_upwards.
  - apply IHev2.
    apply is_expanded_substl.
    + induction n in n |- *;cbn;auto.
    + subst;cbn in *. propify.
      now eapply is_expanded_aux_upwards.
  - apply IHev3; clear IHev3.
    specialize (IHev1 (S k)).
    specialize (IHev2 0).
    propify; split; [easy|].
    intuition auto.
    apply is_expanded_aux_mkApps_inv in H3 as (? & ?).
    apply is_expanded_aux_mkApps.
    + apply (is_expanded_aux_upwards 0); [|lia].
      eapply is_expanded_cunfold_fix; [eassumption|].
      now apply forallb_Forall.
    + easy.
  - easy.
  - apply IHev3; clear IHev3.
    specialize (IHev1 (S k)).
    specialize (IHev2 0).
    propify; split; [easy|].
    intuition auto.
    apply (is_expanded_aux_upwards 0); [|lia].
    eapply is_expanded_cunfold_fix; [eassumption|].
    now apply forallb_Forall.
  - apply IHev2.
    destruct exp_t as [H1 H2].
    specialize (IHev1 0 H1).
    apply is_expanded_aux_mkApps_inv in IHev1.
    propify;split; [|easy].
    apply is_expanded_aux_mkApps.
    + apply (is_expanded_aux_upwards 0); [|lia].
      eapply is_expanded_cunfold_cofix; [eassumption|].
      now apply forallb_Forall.
    + easy.
  - apply IHev2; clear IHev2.
    specialize (IHev1 _ exp_t).
    apply is_expanded_aux_mkApps_inv in IHev1 as (exp_hd & exp_args).
    apply is_expanded_aux_mkApps.
    + apply (is_expanded_aux_upwards 0); [|lia].
      eapply is_expanded_cunfold_cofix; [eassumption|].
      now apply forallb_Forall.
    + easy.
  - apply IHev.
    apply (is_expanded_aux_upwards 0); [|easy].
    now eapply is_expanded_constant.
  - apply IHev2; clear IHev2.
    specialize (IHev1 _ exp_t).
    apply is_expanded_aux_mkApps_inv in IHev1 as (exp_hd & exp_args).
    destruct (nth_error _ _) eqn:nth; [|easy].
    inversion e3;subst;clear e3.
    eapply nth_error_forall in nth; [|eassumption].
    cbn in *.
    now apply (is_expanded_aux_upwards 0).
  - easy.
  - easy.
  - depelim X; auto.
    eapply All2_over_undep in a. eapply All2_Set_All2 in ev. solve_all. subst a0 a'; cbn in *.
    depelim exp_t; constructor; cbn in *; intuition eauto. solve_all.
  - eapply IHev1 in exp_t. eapply IHev2 in exp_t.
    eapply is_expanded_aux_upwards; tea. lia.
Qed.

Lemma valid_case_masks_lift ind c brs n k :
  valid_case_masks ind c brs ->
  valid_case_masks ind c (map (fun br => (br.1, lift n (#|br.1| + k) br.2)) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  propify.
  split; [easy|].
  destruct valid as (_ & valid).
  apply alli_Alli.
  apply alli_Alli in valid.
  rewrite <- mapi_cst_map.
  apply Alli_mapi with (f := (fun (_ : nat) _ => (_,_))).
  eapply Alli_impl; [eassumption|].
  intros ? [] val_branch.
  cbn in *; propify.
  split; [easy|].
  apply valid_dearg_mask_branch_lift.
  now rewrite length_app,repeat_length,List.length_rev.
  easy.
Qed.

Lemma valid_dearg_branch_subst i mask s k k' t :
  i + #|mask| <= k' ->
  valid_dearg_mask_branch i mask t = true ->
  valid_dearg_mask_branch i mask (subst s (k' + k) t) = true.
Proof.
  intros Hik valid.
  induction mask in mask, i, k, k', Hik, valid |- *;cbn;auto.
  destruct a;cbn in *.
  - propify.
    split.
    * now rewrite is_dead_subst_other by lia.
    * easy.
  - easy.
Qed.

Lemma valid_case_masks_subst ind c brs s k :
  valid_case_masks ind c brs ->
  valid_case_masks ind c (map (fun br => (br.1, subst s (#|br.1| + k) br.2)) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  propify.
  split; [easy|].
  destruct valid as (_ & valid).
  apply alli_Alli.
  apply alli_Alli in valid.
  rewrite <- mapi_cst_map.
  apply Alli_mapi with (f := (fun (_ : nat) _ => (_,_))).
  eapply Alli_impl; [eassumption|].
  intros ? [] val_branch.
  cbn in *; propify.
  split; [easy|].
  apply valid_dearg_branch_subst.
  now rewrite length_app,repeat_length,List.length_rev.
  easy.
Qed.

Lemma valid_cases_lift t n k :
  valid_cases t ->
  valid_cases (lift n k t).
Proof.
  intros valid_t.
  induction t in t, k, valid_t |- * using term_forall_list_ind; cbn in *; propify; auto.
  - now destruct (_ <=? _).
  - induction X; [easy|].
    cbn in *.
    now propify.
  - easy.
  - easy.
  - now destruct args;try congruence.
  - destruct p.
    propify.
    split.
    * split; [easy|].
      destruct valid_t as [[valid valid_all]_].
      induction X in X, k, l, valid, valid_all |- *;cbn in *;auto.
    * now apply valid_case_masks_lift.
  - destruct s.
    now propify.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *.
    propify.
    now rewrite <- !Nat.add_succ_r.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *.
    propify.
    now rewrite <- !Nat.add_succ_r.
  - solve_all_k 6.
Qed.

Lemma valid_cases_subst s k t :
  valid_cases s ->
  valid_cases t ->
  valid_cases (subst [s] k t).
Proof.
  intros valid_s valid_t.
  induction t in k, t, valid_t |- * using term_forall_list_ind; cbn in *; propify; auto.
  - destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|easy].
    destruct (_ - _); cbn in *.
    + noconf nth.
      now apply valid_cases_lift.
    + now rewrite nth_error_nil in nth.
  - induction X; [easy|].
    now cbn in *; propify.
  - easy.
  - easy.
  - now destruct args;try congruence.
  - destruct p.
    cbn in *; propify.
    split.
    * split; [easy|].
      destruct valid_t as [[valid valid_all]_].
      induction X in X, k, l, valid, valid_all |- *;cbn in *;auto.
    * now apply valid_case_masks_subst.
  - destruct s0.
    now propify.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *; propify.
    now rewrite <- !Nat.add_succ_r.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *; propify.
    now rewrite <- !Nat.add_succ_r.
  - solve_all_k 6.
Qed.

Lemma closedn_dearg_single k t args mask :
  closedn k t ->
  Forall (closedn k) args ->
  closedn k (dearg_single mask t args).
Proof.
  intros clos_t clos_args.
  induction mask as [|[] mask IH] in k, t, args, mask, clos_t, clos_args |- *; cbn in *.
  - apply forallb_Forall in clos_args.
    now rewrite closedn_mkApps.
  - depelim clos_args; [|easy].
    cbn in *.
    apply IH; [|easy].
    pose proof (closedn_lift 1 k).
    now rewrite Nat.add_1_r in H.
  - depelim clos_args.
    + cbn.
      apply IH; [|easy].
      cbn.
      rewrite Bool.andb_true_r.
      pose proof (closedn_lift 1 k).
      now rewrite Nat.add_1_r in H.
    + apply IH; [|easy].
      cbn.
      now propify.
Qed.

Import EWellformed.

Lemma wellformed_dearg_single (efl := all_env_flags) Σ k t args mask :
  wellformed Σ k t ->
  Forall (wellformed Σ k) args ->
  wellformed Σ k (dearg_single mask t args).
Proof.
  intros clos_t clos_args.
  induction mask as [|[] mask IH] in k, t, args, mask, clos_t, clos_args |- *; cbn in *.
  - apply forallb_Forall in clos_args.
    now rewrite wellformed_mkApps.
  - depelim clos_args; [|easy].
    cbn in *. cbn.
    apply IH; [|easy].
    pose proof (wellformed_lift 1 k 0 _ clos_t).
    now rewrite Nat.add_1_r in H.
  - depelim clos_args.
    + cbn.
      apply IH; [|easy].
      cbn.
      rewrite Bool.andb_true_r.
      pose proof (wellformed_lift 1 k 0 _ clos_t).
      now rewrite Nat.add_1_r in H.
    + apply IH; [|easy].
      cbn.
      now propify.
Qed.
(* From Stdlib Require Import ssreflect.
Lemma wellformed_dearg_single' (efl := all_env_flags) Σ k t args mask :
  wellformed (trans_env (dearg_env Σ)) k t ->
  Forall (wellformed (trans_env (dearg_env Σ)) k) args ->
  wellformed (trans_env (dearg_env Σ)) k (dearg_single mask t args).
Proof.
  intros clos_t clos_args.
  induction mask as [|[] mask IH] in k, t, args, mask, clos_t, clos_args |- *; cbn in *.
  - eapply forallb_Forall in clos_args.
    now rewrite wellformed_mkApps //.
  - depelim clos_args; [|easy].
    cbn in *. cbn.
    apply IH; [|easy].
    pose proof (wellformed_lift 1 k 0 _ clos_t).
    now rewrite Nat.add_1_r in H.
  - depelim clos_args.
    + cbn.
      apply IH; [|easy].
      cbn.
      rewrite Bool.andb_true_r.
      pose proof (wellformed_lift 1 k 0 _ clos_t).
      now rewrite Nat.add_1_r in H.
    + apply IH; [|easy].
      cbn.
      now propify.
Qed. *)

Lemma closedn_dearg_lambdas k mask t :
  closedn k t ->
  closedn k (dearg_lambdas mask t).
Proof.
  intros clos.
  induction t in k, mask, t, clos |- *; auto; cbn in *.
  - destruct mask; [easy|].
    destruct b; [|easy].
    apply closedn_subst0; [easy|].
    now cbn; rewrite Nat.add_1_r.
  - now propify.
Qed.

Lemma wellformed_dearg_lambdas {efl : EEnvFlags} Σ k mask t :
  has_tBox ->
  wellformed Σ k t ->
  wellformed Σ k (dearg_lambdas mask t).
Proof.
  intros clos.
  induction t in k, mask, t, clos |- *; auto; cbn in *.
  - destruct mask; [easy|]. rtoProp; intuition auto.
    destruct b; eauto.
    apply wellformed_subst; eauto;
    cbn; rewrite ?Nat.add_1_r; eauto. cbn. rewrite H0. eauto.
  - now propify.
Qed.

(* NOTE: borrowed from MetaRocq (where it's commented out) and fixed *)
Lemma closedn_subst s k k' t :
  forallb (closedn k) s -> closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. solve_all. revert H.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    simpl closed in *; try change_Sk; repeat (rtoProp; solve_all);
    unfold Basics.compose, test_def, on_snd, test_snd in *; simpl in *; eauto with all.
  - elim (Nat.leb_spec k' n); intros. simpl.
    apply Nat.ltb_lt in H.
    destruct nth_error eqn:Heq.
    -- eapply closedn_lift.
       now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. lia.
    -- simpl. apply Nat.ltb_lt in H0.
       apply Nat.ltb_lt. apply Nat.ltb_lt in H0. lia.
  - rtoProp; solve_all.
    specialize (IHt (S k')).
    rewrite <- Nat.add_succ_comm in IHt. eauto.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - rtoProp; solve_all.
    specialize (IHt (S k')).
    specialize (a0 (#|x.1| + k')). unfold is_true. rewrite <- a0. f_equal. lia.
    now replace (k + (#|x.1| + k') + #|s|) with (#|x.1| + (k + k' + #|s|)) by lia.
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (a (#|m| + k')). unfold is_true. rewrite <- a. f_equal. lia.
    unfold is_true. rewrite <- b. f_equal. lia.
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (a (#|m| + k')). unfold is_true. rewrite <- a. f_equal. lia.
    unfold is_true. rewrite <- b. f_equal. lia.
  - solve_all_k 6.
Qed.

Lemma closedn_dearg_case_branch_body_rec i k mask t :
  closedn (i + #|mask| + k) t ->
  closedn (i + count_zeros mask + k) (dearg_branch_body_rec i mask t).2.
Proof.
  intros clos.
  induction mask in mask, i, k, t, clos |- *; cbn in *.
  - eapply closed_upwards;eauto.
  - destruct a.
    * cbn in *.
      eapply IHmask.
      unfold subst1.
      replace (i + #|mask| + k) with (k + #|mask| + i) by lia.
      apply closedn_subst;auto. cbn.
      now replace (k + #|mask| + i + 1) with (i + S #|mask| + k).
    * cbn.
      replace (i + S #|filter negb mask| + k) with (S i + #|filter negb mask| + k) by lia.
      replace (i + S #|mask| + k) with (S i + #|mask| + k) in * by lia.
      easy.
Qed.

Lemma wellformed_dearg_case_branch_body_rec (efl := all_env_flags) Σ i k mask t :
  wellformed Σ (i + #|mask| + k) t ->
  wellformed Σ (i + count_zeros mask + k) (dearg_branch_body_rec i mask t).2.
Proof.
  intros clos.
  induction mask in mask, i, k, t, clos |- *; cbn in *.
  - eauto.
  - destruct a.
    * cbn in *.
      eapply IHmask.
      unfold subst1.
      replace (i + #|mask| + k) with (k + #|mask| + i) by lia.
      eapply wellformed_subst_eq;eauto. cbn.
      now replace (k + #|mask| + i + 1) with (i + S #|mask| + k).
    * cbn.
      replace (i + S #|filter negb mask| + k) with (S i + #|filter negb mask| + k) by lia.
      replace (i + S #|mask| + k) with (S i + #|mask| + k) in * by lia.
      easy.
Qed.

Import EEtaExpandedFix.

Lemma isEtaExp_dearg_case_branch_body_rec (efl := all_env_flags) Σ i k mask t :
  isEtaExp Σ (repeat 0 i ++ repeat 0 #|mask| ++ k) t ->
  isEtaExp Σ (repeat 0 i ++ repeat 0 (count_zeros mask) ++ k) (dearg_branch_body_rec i mask t).2.
Proof.
  intros clos.
  induction mask in mask, i, k, t, clos |- *; cbn in *.
  - eauto.
  - destruct a.
    * cbn in *.
      eapply IHmask.
      unfold subst1.
      rewrite <- closed_subst; auto.
      eapply etaExp_csubst'. now len. now simp_eta. exact clos.
    * cbn. fold (dearg_branch_body_rec (S i) mask t).
      pose proof (repeat_app 0 i 1). cbn in H.
      replace (repeat 0 i ++ 0 :: repeat 0 #|filter negb mask| ++ k) with
        (repeat 0 (S i) ++ repeat 0 #|filter negb mask| ++ k).
        2:{ rewrite Nat.add_1_r in H. now rewrite H; cbn; rewrite <- app_assoc; cbn. }
        eapply IHmask. now rewrite <- Nat.add_1_r, repeat_app, <- app_assoc; cbn.
Qed.

Lemma closedn_dearg_aux k args t :
  closedn k t ->
  Forall (closedn k) args ->
  closedn k (dearg_aux args t).
Proof.
  intros clos_t clos_args.
  induction t in k, args, clos_t, clos_args |- * using term_forall_list_ind; cbn in *;
    try solve [apply forallb_Forall in clos_args;now rewrite closedn_mkApps].
  - apply forallb_Forall in clos_args;rewrite closedn_mkApps.
    propify. split;auto. cbn.
    induction X; [easy|].
    cbn in *.
    now propify.
  - rewrite closedn_mkApps.
    propify. split;[|now apply forallb_Forall in clos_args].
    cbn.
    now propify.
  - rewrite closedn_mkApps.
    propify. split;[|now apply forallb_Forall in clos_args].
    cbn.
    now propify.
  - propify;cbn.
    apply IHt1; [easy|].
    now constructor.
  - now apply closedn_dearg_single.
  - now apply closedn_dearg_single.
  - destruct p.
    apply forallb_Forall in clos_args;rewrite closedn_mkApps.
    unfold dearg_case. cbn.
    destruct (get_mib_masks _); cbn in *; propify; cycle 1.
    { split;[|easy].
      split; [now apply IHt|].
      rewrite forallb_map;cbn.
      destruct clos_t as (_ & clos_brs).
      induction X; [easy|].
      now cbn in *; propify. }

    split;[|easy].
    split; [now apply IHt|].
    destruct clos_t as (_ & clos_brs).
    unfold mapi.
    generalize 0.
    induction X; [easy|]; intros n'.
    cbn in *; propify.
    split.
    * unfold dearg_case_branch,dearg_branch_body.
      destruct (_ <=? _) eqn:Hmask;[|cbn;easy].
      remember (complete_ctx_mask _ _) as mm. cbn.
      assert (#|mm| = #|x.1|) by now subst;propify;apply complete_ctx_mask_length.
      rewrite masked_count_zeros by lia.
      specialize (closedn_dearg_case_branch_body_rec 0 ((#|x.1| - #|mm|) + k) mm ((dearg_aux [] x.2))) as b.
      cbn in b.
      replace (#|mm| + (#|x.1| - #|mm| + k)) with (#|x.1| + k) in * by lia.
      rewrite <- Nat.add_assoc.
      apply b.
      now apply p.
    * now apply IHX.
  - destruct s.
    apply forallb_Forall in clos_args;rewrite closedn_mkApps; propify;split;[|easy].
    unfold dearg_proj.
    now destruct (get_mib_masks _); apply IHt.
  - apply forallb_Forall in clos_args;rewrite closedn_mkApps; propify;split;[|easy].
    cbn.
    rewrite length_map.
    induction X in k, args, X, clos_t |- *; [easy|].
    cbn in *; propify.
    split; [easy|].
    rewrite <- !Nat.add_succ_r in *.
    now apply IHX.
  - apply forallb_Forall in clos_args;rewrite closedn_mkApps; propify;split;[|easy].
    cbn.
    rewrite length_map.
    induction X in k, args, X, clos_t |- *; [easy|].
    cbn in *; propify.
    split; [easy|].
    rewrite <- !Nat.add_succ_r in *.
    now apply IHX.
  - rewrite closedn_mkApps; cbn; rtoProp; intuition solve_all. solve_all_k 6.
  - rewrite closedn_mkApps; cbn; rtoProp; intuition solve_all.
  - rewrite closedn_mkApps; cbn; rtoProp; intuition solve_all.
Qed.

Lemma Alli_map {A B P n} {f : A -> B} l :
  Alli (fun n x => P n (f x)) n l ->
  Alli P n (map f l).
Proof.
  induction 1; constructor; eauto.
Qed.


Lemma lookup_env_dearg_env Σ kn :
  lookup_env (dearg_env Σ) kn = option_map (dearg_decl kn) (lookup_env Σ kn).
Proof.
  unfold lookup_env.
  induction Σ as [|((kn', has_deps), decl) Σ IH]; [easy|].
  cbn.
  unfold eq_kername.
  destruct Kername.reflect_kername as [eq Heq].
  destruct (Heq kn kn');subst;[easy| apply IH].
Qed.

Hint Resolve
     closedn_subst0 closed_mkApps closedn_dearg_aux closed_iota_red
     is_expanded_aux_subst is_expanded_aux_mkApps
     valid_cases_subst : dearg.
Hint Constructors Forall : dearg.

Lemma valid_cases_mkApps hd args :
  valid_cases hd ->
  Forall valid_cases args ->
  valid_cases (mkApps hd args).
Proof.
  intros valid_hd valid_args.
  induction args as [|a args IH] using List.rev_ind; [easy|].
  rewrite mkApps_app.
  cbn; propify.
  now apply Forall_snoc in valid_args.
Qed.

Lemma valid_cases_substl s t :
  Forall (fun s => closed s) s ->
  Forall valid_cases s ->
  valid_cases t ->
  valid_cases (substl s t).
Proof.
  intros clos_s valid_s valid_t.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_snoc in clos_s as (? & ?).
  apply Forall_snoc in valid_s as (? & ?).
  rewrite closed_subst by easy.
  now apply valid_cases_subst.
Qed.

Lemma valid_cases_iota_red pars args (br : (list BasicAst.name) × term) :
  Forall valid_cases args ->
  Forall (closedn 0) args ->
  valid_cases br.2 ->
  valid_cases (iota_red pars args br).
Proof.
  intros valid_args valid_brs.
  unfold iota_red.
  apply valid_cases_substl;eauto.
  - now apply Forall_rev, Forall_skipn.
  - now apply Forall_rev, Forall_skipn.
Qed.

Lemma Forall_closed_fix_subst defs :
  Forall (closedn #|defs| ∘ dbody) defs ->
  Forall (closedn 0) (fix_subst defs).
Proof.
  intros all.
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - apply forallb_Forall.
    eapply Forall_impl; [eassumption|].
    intros.
    now rewrite Nat.add_0_r.
  - now apply IHl.
Qed.

Lemma Forall_closed_cofix_subst defs :
  Forall (closedn #|defs| ∘ dbody) defs ->
  Forall (closedn 0) (cofix_subst defs).
Proof.
  intros all.
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - apply forallb_Forall.
    eapply Forall_impl; [eassumption|].
    intros.
    now rewrite Nat.add_0_r.
  - now apply IHl.
Qed.

Lemma Forall_valid_cases_fix_subst defs :
  Forall (valid_cases ∘ dbody) defs ->
  Forall valid_cases (fix_subst defs).
Proof.
  intros all.
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma Forall_valid_cases_cofix_subst defs :
  Forall (valid_cases ∘ dbody) defs ->
  Forall valid_cases (cofix_subst defs).
Proof.
  intros all.
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma valid_cases_cunfold_fix defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  closed (tFix defs i) ->
  valid_cases (tFix defs i) ->
  valid_cases f.
Proof.
  intros cuf clos_defs valid_defs.
  unfold cunfold_fix in *.
  cbn in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply (nth_error_forallb nth) in clos_defs as ?.
  eapply (nth_error_forallb nth) in valid_defs as ?.
  cbn in *.
  noconf cuf.
  apply valid_cases_substl.
  - apply Forall_closed_fix_subst.
    apply forallb_Forall.
    eapply forallb_impl; [|exact clos_defs].
    intros.
    now rewrite Nat.add_0_r in *.
  - apply Forall_valid_cases_fix_subst.
    now apply forallb_Forall.
  - easy.
Qed.

Lemma valid_cases_cunfold_cofix defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  closed (tCoFix defs i) ->
  valid_cases (tCoFix defs i) ->
  valid_cases f.
Proof.
  intros cuf clos_defs valid_defs.
  unfold cunfold_cofix in *.
  cbn in *. destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply (nth_error_forallb nth) in clos_defs as ?.
  eapply (nth_error_forallb nth) in valid_defs as ?.
  cbn in *.
  noconf cuf.
  apply valid_cases_substl.
  - apply Forall_closed_cofix_subst.
    apply forallb_Forall.
    eapply forallb_impl; [|exact clos_defs].
    intros.
    now rewrite Nat.add_0_r in *.
  - apply Forall_valid_cases_cofix_subst.
    now apply forallb_Forall.
  - easy.
Qed.

Lemma valid_cases_constant Σ kn cst body :
  valid_masks_env Σ ->
  EGlobalEnv.declared_constant (trans_env Σ) kn cst ->
  EAst.cst_body cst = Some body ->
  valid_cases body.
Proof.
  intros valid_env decl_const body_eq.
  eapply declared_constant_trans_env in decl_const as [(? & -> & look)|(? & -> & look)].
  - apply forallb_Forall in valid_env.
    eapply lookup_env_Forall in valid_env as (? & valid); eauto.
    destruct x.
    cbn in *.
    now rewrite body_eq in valid; propify.
  - destruct x; cbn in *; [|congruence].
    now replace body with tBox by congruence.
Qed.

Lemma valid_dearg_mask_constant Σ kn cst body :
  valid_masks_env Σ ->
  EGlobalEnv.declared_constant (trans_env Σ) kn cst ->
  EAst.cst_body cst = Some body ->
  valid_dearg_mask (get_const_mask kn) body.
Proof.
  intros valid_env decl_const body_eq.
  apply forallb_Forall in valid_env.
  eapply declared_constant_trans_env in decl_const as [(? & -> & look)|(? & -> & look)].
  - eapply lookup_env_Forall in valid_env as (? & valid); eauto.
    destruct x.
    cbn in *.
    now rewrite body_eq in valid; propify.
  - eapply lookup_env_Forall in valid_env as (? & valid); eauto.
    destruct x; cbn in *; [|congruence].
    replace body with tBox by congruence.
    cbn.
    now destruct get_const_mask.
Qed.

Definition check_oib_masks_trans masks i oib :=
  forallbi (fun c cb => #|get_branch_mask masks i c| == cb.(cstr_nargs)) 0 oib.(EAst.ind_ctors) &&
  match oib.(EAst.ind_projs) with
  | [] => true
  | _ :: _ =>
    let mask := get_branch_mask masks i 0 in
    #|mask| == #|oib.(EAst.ind_projs)|
  end.

Lemma forallbi_nth_error {A} n k {l : list A} p x : nth_error l n = Some x -> forallbi p k l -> p (n + k) x.
Proof.
  induction l in x, n, k |- *; cbn => //.
  - now rewrite nth_error_nil.
  - destruct n; cbn.
    + intros [= <-]. move/andP=> [ha hf]. exact ha.
    + intros hn. move/andP=> [hp hf].
      eapply IHl in hn; tea. now rewrite Nat.add_succ_r in hn.
Qed.

Import ssreflect.

Lemma forallbi_Alli {A} (f : nat -> A -> bool) n l :
  Alli f n l <~> forallbi f n l.
Proof.
  split.
  - induction 1; cbn; auto.
  - induction l in n |- *; cbn; auto.
    * constructor.
    * move/andP => [] hf hl. constructor; eauto.
Qed.


Lemma valid_ind_mask_inductive Σ ind mib oib :
  valid_masks_env Σ ->
  EGlobalEnv.declared_inductive (trans_env Σ) ind mib oib ->
  ∑ mask, get_mib_masks (inductive_mind ind) = Some mask /\
  (#|mask.(param_mask)| =? mib.(EAst.ind_npars)) /\ check_oib_masks_trans mask (inductive_ind ind) oib.
Proof.
  intros valid_env decl_ind.
  apply forallb_Forall in valid_env.
  unfold declared_inductive,declared_minductive in *.
  rewrite lookup_env_trans_env in decl_ind.
  destruct decl_ind as [decl_mind nth].
  destruct (lookup_env Σ _) as [cst|] eqn:Hm; cbn in *;try congruence.
  inversion decl_mind as [H0];subst;clear decl_mind.
  eapply lookup_env_Forall in valid_env as [b Hb];eauto.
  cbn in *.
  destruct cst;cbn in *;try congruence.
  inversion H0;subst;clear H0;cbn in *.
  destruct get_mib_masks;try congruence.
  eexists;eauto. split; eauto.
  move/andP: Hb => [] -> hf.
  rewrite nth_error_map in nth.
  destruct nth_error eqn:hnth => //. eapply forallbi_nth_error in hf; tea.
  rewrite Nat.add_0_r in hf. cbn in nth. noconf nth.
  destruct o; cbn. split => //. unfold check_oib_masks in hf; cbn in hf.
  move/andP: hf => [] oncs onps. apply/andP. split.
  - cbn. move/forallbi_Alli: oncs => oncs. eapply forallbi_Alli, Alli_map, Alli_impl; tea; cbn.
    now intros n [[kn tys] nargs]; cbn.
  - unfold check_oib_masks_trans. cbn in *. destruct ind_projs; cbn in * => //.
    now rewrite length_map.
Qed.

Ltac invert_facts :=
  unfold is_true in *;
  repeat match goal with
       | [ H : closed (mkApps _ _) = true |- _] =>
           apply closed_mkApps_inv in H as (? & ?)
      | [ H : valid_cases (mkApps _ _) = true |- _] =>
             apply valid_cases_mkApps_inv in H as (? & ?)
      | [ H : is_expanded (mkApps _ _) = true |- _] =>
          apply is_expanded_aux_mkApps_inv in H as (? & ?)
      end.

Lemma eval_valid_cases {wfl : WcbvFlags} Σ t v :
  with_constructor_as_block = false ->

  trans_env Σ e⊢ t ⇓ v ->

  env_closed (trans_env Σ) ->
  closed t ->

  valid_masks_env Σ ->
  valid_cases t ->

  valid_cases v.
Proof with auto with dearg.
  intros ? ev clos_env clos_t valid_env valid_t.
  induction ev in t, v, ev, clos_t, valid_t |- *; auto; cbn in *; propify;try congruence.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply eval_closed in ev2 as ?...
    rewrite closed_subst in * by easy.
    apply IHev3; [apply closedn_subst0|apply valid_cases_subst]...
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    rewrite closed_subst in * by easy.
    apply IHev2; [apply closedn_subst0|apply valid_cases_subst]...
  - destruct clos_t as [clos_discr clos_brs].
    destruct valid_t as [[val_discr val_brs] val_masks].
    specialize (IHev1 clos_discr val_discr) as val_cases.
    eapply eval_closed in ev1 as Happs...
    apply closed_mkApps_inv in Happs as (? & ?).
    assert (closed (iota_red pars args br)).
    { apply closed_iota_red; auto.
      eapply (nth_error_forallb e2) in clos_brs as ?.
      cbn in *.
      replace (#|br.1| + 0) with #|br.1| in * by lia.
      now rewrite e4. }
    eapply eval_closed in ev2 as ?...
    eapply valid_cases_mkApps_inv in val_cases as (? & ?).
    apply IHev2...
    apply valid_cases_iota_red...
    eapply (nth_error_forallb e2) in val_brs as ?...
  - subst brs.
    cbn in *.
    propify.
    intuition auto.
    apply IHev2.
    + apply closed_substl. induction n in n |- * ; easy.
      now rewrite repeat_length.
    + apply valid_cases_substl; try apply Forall_repeat;easy.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply eval_closed in ev2 as ?...
    apply closed_mkApps_inv in H7 as (? & ?).
    apply valid_cases_mkApps_inv in H6 as (? & ?).
    apply H5...
    + apply closed_mkApps...
      now eapply closed_cunfold_fix.
    + split; [|easy].
      apply valid_cases_mkApps...
      eapply valid_cases_cunfold_fix; [eassumption| |]...
  - easy.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply eval_closed in ev2 as ?...
    apply H5...
    + now eapply closed_cunfold_fix.
    + split; [|easy].
      eapply valid_cases_cunfold_fix;eauto.
  - destruct ip.
    propify.
    assert (Hcofix : closed (mkApps (tCoFix mfix idx) args)) by now eapply eval_closed.
    apply closed_mkApps_inv in Hcofix as (? & ?).
    assert (closed fn) by (now eapply closed_cunfold_cofix).
    assert (closed (mkApps fn args)) by (now apply closed_mkApps).
    intuition auto.
    invert_facts.
    assert (valid_cases (mkApps fn args)) by
      (apply valid_cases_mkApps;auto; eapply valid_cases_cunfold_cofix;eauto).
    easy.
  - destruct p.
    propify.
    assert (Hcofix : closed (mkApps (tCoFix mfix idx) args)) by now eapply eval_closed.
    apply closed_mkApps_inv in Hcofix as (? & ?).
    assert (closed fn) by (now eapply closed_cunfold_cofix).
    assert (closed (mkApps fn args)) by (now apply closed_mkApps).
    intuition auto.
    invert_facts.
    assert (valid_cases (mkApps fn args)) by
      (apply valid_cases_mkApps;auto; eapply valid_cases_cunfold_cofix;eauto).
    easy.
  - apply IHev.
    + now eapply closed_constant.
    + now eapply valid_cases_constant.
  - destruct p;cbn in *.
    propify.
    eapply eval_closed in ev1 as ?...
    intuition auto.
    invert_facts.
    assert (closed a) by
      (eapply @nth_error_forall with (x := a);eauto).
    assert (valid_cases a) by
      (eapply @nth_error_forall with (x := a);eauto).
    easy.
  - easy.
  - easy.
  - depelim X; auto.
    eapply All2_over_undep in a. eapply All2_Set_All2 in ev. subst a0 a'; cbn -[test_prim] in *.
    solve_all. depelim H0; constructor; cbn; intuition eauto. solve_all.
  - eapply IHev2. eapply eval_closed in ev1; tea. eapply IHev1; eauto.
Qed.

Lemma declared_constant_dearg Σ k cst :
  declared_constant (trans_env Σ) k cst ->
  ∑ cst',
    declared_constant (trans_env (dearg_env Σ)) k cst' ×
    EAst.cst_body cst' = option_map (dearg ∘ dearg_lambdas (get_const_mask k))
                                    (EAst.cst_body cst).
Proof.
  unfold declared_constant.
  rewrite !lookup_env_trans_env, lookup_env_dearg_env.
  intros typ.
  destruct lookup_env as [decl|]; cbn in *; [|congruence].
  destruct decl; cbn in *; [|congruence|]; noconf typ; eauto.
  cbn.
  eexists.
  split; [reflexivity|].
  cbn.
  now destruct o.
Qed.

Inductive dearg_spec : term -> term -> Type :=
| dearg_spec_const kn args :
    dearg_spec (mkApps (tConst kn) args)
               (dearg_single (get_const_mask kn) (tConst kn) (map dearg args))
| dearg_spec_ctor ind c args0 args :
    (* NOTE: args0 is not dearged, because we ignore constructors as blocks *)
    dearg_spec (mkApps (tConstruct ind c args0) args)
               (dearg_single (get_ctor_mask ind c) (tConstruct ind c args0) (map dearg args))
| dearg_spec_case ind npars discr brs args :
    dearg_spec (mkApps (tCase (ind, npars) discr brs) args)
               (mkApps (dearg (tCase (ind, npars) discr brs))
                       (map dearg args))
| dearg_spec_proj ind c npars t args :
    dearg_spec (mkApps (tProj (mkProjection ind c npars) t) args)
               (mkApps (dearg (tProj (mkProjection ind c npars) t)) (map dearg args))
| dearg_spec_other hd args :
    match hd with
    | tConst _
    | tConstruct _ _ _
    | tCase _ _ _
    | tProj _ _
    | tApp _ _ => False
    | _ => True
    end ->
    dearg_spec (mkApps hd args) (mkApps (dearg hd) (map dearg args)).

Lemma dearg_elim t :
  dearg_spec t (dearg t).
Proof.
  destruct (mkApps_elim t []).
  generalize (firstn n l) as args.
  clear n.
  intros args.
  rewrite dearg_mkApps.
  destruct f; try solve [now econstructor].
  - easy.
  - cbn in *.
    destruct indn.
    eapply dearg_spec_case.
  - cbn in *.
    destruct p.
    eapply dearg_spec_proj.
Qed.

Lemma valid_cases_dearg_lambdas mask t :
  valid_cases t ->
  valid_cases (dearg_lambdas mask t).
Proof.
  intros valid.
  induction t in mask, valid |- * using term_forall_list_ind; cbn in *; propify; try easy.
  destruct mask as [|[] mask]; try easy.
  now apply valid_cases_subst.
Qed.

Lemma isEtaExp_dearg_lambdas Σ Γ mask t :
  isEtaExp Σ Γ t ->
  isEtaExp Σ Γ (dearg_lambdas mask t).
Proof.
  intros valid.
  induction t in Γ, mask, valid |- * using term_forall_list_ind; cbn in *; try easy.
  - simp_eta in valid.
    destruct mask as [|[] mask]; try easy.
    + now simp_eta.
    + cbn. unfold subst1. rewrite <- closed_subst; try easy.
      eapply (isEtaExp_substl _ [0] _ [_]); easy.
    + simp_eta. now eapply IHt.
  - simp_eta. simp_eta in valid. rtoProp; intuition eauto.
Qed.

Lemma dearg_dearg_lambdas mask t :
  valid_dearg_mask mask t ->
  valid_cases t ->
  dearg (dearg_lambdas mask t) = dearg_lambdas mask (dearg t).
Proof.
  intros vm vc.
  induction t in mask, vm, vc |- * using term_forall_list_ind; cbn in *; propify; try easy;
    try solve [destruct mask; [|easy]; now rewrite dearg_lambdas_nil].
  - destruct mask as [|[] mask]; cbn in *; propify; try easy.
    + refold'.
      unfold subst1.
      rewrite dearg_subst; cbn in *.
      * now rewrite IHt.
      * now apply valid_cases_dearg_lambdas.
      * easy.
    + refold'; now rewrite IHt.
  - now refold'; rewrite IHt2.
Qed.

Lemma dearg_substl s t :
  Forall (closedn 0) s ->
  Forall valid_cases s ->
  Forall is_expanded s ->
  valid_cases t ->
  dearg (substl s t) = substl (map dearg s) (dearg t).
Proof.
  intros clos valid exp valid_t.
  induction s using List.rev_ind; [easy|].
  unfold substl.
  rewrite map_app, !fold_left_app.
  cbn.
  apply Forall_snoc in clos.
  apply Forall_snoc in valid.
  apply Forall_snoc in exp.
  rewrite closed_subst by easy.
  refold'.
  rewrite dearg_subst.
  - cbn.
    rewrite <- closed_subst by (now apply closedn_dearg_aux).
    f_equal.
    now apply IHs.
  - now apply valid_cases_substl.
  - easy.
Qed.

Lemma fix_subst_dearg defs :
  fix_subst (map (map_def dearg) defs) = map dearg (fix_subst defs).
Proof.
  unfold fix_subst.
  rewrite length_map.
  induction #|defs|; [easy|].
  cbn in *.
  f_equal.
  apply IHn.
Qed.

Lemma cofix_subst_dearg defs :
  cofix_subst (map (map_def dearg) defs) = map dearg (cofix_subst defs).
Proof.
  unfold cofix_subst.
  rewrite length_map.
  induction #|defs|; [easy|].
  cbn in *.
  f_equal.
  apply IHn.
Qed.

Lemma dearg_cunfold_fix defs i narg fn :
  cunfold_fix defs i = Some (narg, fn) ->
  closed (tFix defs i) ->
  valid_cases (tFix defs i) ->
  is_expanded (tFix defs i) ->
  cunfold_fix (map (map_def dearg) defs) i = Some (narg, dearg fn).
Proof.
  intros cuf clos_fix valid_fix exp_fix.
  cbn in *.
  unfold cunfold_fix in *.
  rewrite nth_error_map.
  destruct (nth_error _ _) eqn:nth; [|easy].
  cbn in *.
  noconf cuf.
  f_equal.
  f_equal.
  rewrite dearg_substl.
  - f_equal; apply fix_subst_dearg.
  - apply Forall_closed_fix_subst.
    setoid_rewrite Nat.add_0_r in clos_fix.
    now apply forallb_Forall.
  - apply Forall_valid_cases_fix_subst.
    now apply forallb_Forall.
  - apply Forall_is_expanded_fix_subst.
    now apply forallb_Forall.
  - now eapply nth_error_forallb in valid_fix.
Qed.

Lemma dearg_cunfold_cofix defs i narg fn :
  cunfold_cofix defs i = Some (narg, fn) ->
  closed (tCoFix defs i) ->
  valid_cases (tCoFix defs i) ->
  is_expanded (tCoFix defs i) ->
  cunfold_cofix (map (map_def dearg) defs) i = Some (narg, dearg fn).
Proof.
  intros cuf clos_fix valid_fix exp_fix.
  cbn in *.
  unfold cunfold_cofix in *.
  rewrite nth_error_map.
  destruct (nth_error _ _) eqn:nth; [|easy].
  cbn in *.
  noconf cuf.
  f_equal.
  f_equal.
  rewrite dearg_substl.
  - f_equal; apply cofix_subst_dearg.
  - apply Forall_closed_cofix_subst.
    setoid_rewrite Nat.add_0_r in clos_fix.
    now apply forallb_Forall.
  - apply Forall_valid_cases_cofix_subst.
    now apply forallb_Forall.
  - apply Forall_is_expanded_cofix_subst.
    now apply forallb_Forall.
  - now eapply nth_error_forallb in valid_fix.
Qed.

Lemma isBox_mkApps hd args :
  isBox (mkApps hd args) = isBox hd && (#|args| =? 0).
Proof.
  destruct args using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, length_app.
    cbn.
    rewrite Nat.add_comm.
    cbn.
    now rewrite Bool.andb_false_r.
Qed.

Lemma isLambda_mkApps hd args :
  isLambda (mkApps hd args) = isLambda hd && (#|args| =? 0).
Proof.
  destruct args using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, length_app.
    cbn.
    symmetry; propify.
    right; easy.
Qed.

Lemma eval_mkApps_tConstruct {wfl : WcbvFlags} Σ ind c args argsv mdecl idecl cdecl
      (a : All2 (eval Σ) args argsv) :
  with_constructor_as_block = false ->
  EGlobalEnv.lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  #|argsv| <= cstr_arity mdecl cdecl ->
  Σ e⊢ mkApps (tConstruct ind c []) args ⇓ mkApps (tConstruct ind c []) argsv.
Proof.
  revert argsv a.
  induction args using MRList.rev_ind; intros argsv all block ctor_look argsv_lt.
  - depelim all.
    cbn.
    constructor.
    cbn.
    unfold EGlobalEnv.lookup_constructor in *;cbn in *.
    destruct EGlobalEnv.lookup_env as [g|];try congruence.
    destruct g;cbn in *;try congruence.
    rewrite block.
    repeat destruct nth_error;cbn;try congruence.
  - destruct argsv as [|? ? _] using MRList.rev_ind.
    { apply All2_length in all as len.
      rewrite length_app in len; cbn in *; lia. }
    destruct (All2_eval_snoc_elim all).
    rewrite !mkApps_app.
    rewrite length_app in argsv_lt;cbn in argsv_lt.
    eapply eval_construct;eauto;try lia.
    apply IHargs;try lia;eauto.
Qed.

Ltac facts :=
  (repeat match goal with
   | H : ?Σ e⊢ ?t ⇓ ?v
     |- _ =>
         match goal with
         | H' : is_true (closed v) |- _ => fail 1
         | _ => idtac
         end; assert (closed v) by (unshelve eapply (eval_closed _ _ _ _ _ H); trivial)
   end);
  (repeat
     match goal with
     | [H : ?Σ e⊢ ?t ⇓ ?v |- _] =>
       match goal with
       | [H' : is_true (valid_cases v) |- _] =>
         fail 1
       | _ => idtac
       end;
       assert (valid_cases v) by (unshelve eapply (eval_valid_cases _ _ _ _ H); trivial)
     end);
  (repeat
     match goal with
     | [H : ?Σ e⊢ ?t ⇓ ?v |- _] =>
       match goal with
       | [H' : is_true (is_expanded v) |- _] =>
         fail 1
       | _ => idtac
       end;
       assert (is_expanded v) by (unshelve eapply (eval_is_expanded_aux _ _ _ 0 _ H); trivial)
     end).

Lemma count_zeros_le : forall mask, count_zeros mask <= #|mask|.
Proof.
  induction mask;cbn;auto. destruct a;cbn; unfold count_zeros in *; lia.
Qed.

Lemma count_zeros_rev : forall msk, count_zeros msk = count_zeros (List.rev msk).
Proof.
  intros. induction msk; unfold count_zeros;auto.
  destruct a;simpl;auto.
  - rewrite filter_app;cbn. now rewrite app_nil_r.
  - rewrite filter_app;cbn. rewrite length_app;cbn.
    unfold count_zeros in *;lia.
Qed.

Lemma count_zeros_repeat : forall n, count_zeros (repeat false n) = n.
Proof.
  intros n;induction n;unfold count_zeros in *;auto;cbn.
  lia.
Qed.

Lemma masked_len : forall {A} m (l : list A) , #|masked m l| <= #|l|.
Proof.
  induction m;cbn;auto.
  destruct l;cbn;auto.
  destruct a;cbn;auto.
  specialize (IHm l);lia.
Qed.

Lemma count_zeros_distr_app :
  forall (l1 l2 : bitmask), count_zeros (l1 ++ l2) = count_zeros l1 + count_zeros l2.
Proof.
  induction l1.
  - intro l2;destruct l2;try destruct a;cbn;auto.
  - intro l2;destruct l2.
    * destruct a;cbn;rewrite app_nil_r;lia.
    * destruct a;cbn;rewrite filter_app;cbn;
        destruct b;rewrite length_app;cbn; lia.
Qed.


Lemma masked_length {X} m (xs : list X) :
  #|m| <= #|xs| ->
  #|masked m xs| = count_zeros m + #|xs| - #|m|.
Proof.
  intros len.
  induction m in xs, len |- *; cbn in *.
  - now destruct xs.
  - destruct xs; cbn in *; [easy|].
    destruct a; cbn in *.
    + rewrite IHm by easy.
      now unfold count_zeros.
    + rewrite IHm by easy.
      now unfold count_zeros.
Qed.



Import EEtaExpandedFix.

Hint Resolve dearg_elim : core.

Lemma isEtaExp_dearg_single Σ Γ t m l :
  isEtaExp Σ Γ t ->
  forallb (isEtaExp Σ Γ) l ->
  isEtaExp Σ Γ (dearg_single m t l).
Proof.
  induction m in Γ, l, t |- *; intros etat etal.
  - cbn. eapply isEtaExp_mkApps_intro; solve_all.
  - cbn. destruct a; destruct l; simp_eta; eauto. eapply IHm; eauto.
    now eapply (isEtaExp_lift _ _ [_] []).
    eapply IHm; eauto. now move/andP: etal.
    eapply IHm. eapply (isEtaExp_mkApps_intro _ _ _ [_]).
    now eapply (isEtaExp_lift _ _ [_] []). constructor; eauto. now simp_eta.
    eapply IHm. eapply (isEtaExp_mkApps_intro _ _ _ [_]); eauto. constructor; eauto.
    all:now move/andP: etal.
Qed.

Unset Strict Universe Declaration.
Section dearg.
  Context {wfl : WcbvFlags}.
  Context (n : nat).
  Context (Σ : global_env).
  Context (clos_Σ : env_closed (trans_env Σ)).
  Context (valid_Σ : valid_masks_env Σ).
  Context (exp_Σ : is_expanded_env Σ).
  Context (IH : forall t v : term,
        closed t ->
        valid_cases t ->
        is_expanded t ->
        forall ev : trans_env Σ e⊢ t ⇓ v,
        deriv_length ev <= n ->
        trans_env (dearg_env Σ) e⊢ dearg t ⇓ dearg v).

  Lemma lookup_ctor_trans_env ind c Σ0 mdecl idecl cdecl :
    EGlobalEnv.lookup_constructor (trans_env Σ0) ind c = Some (mdecl, idecl, cdecl) ->
    ∑ mib oib ctor,
      lookup_constructor_full Σ0 ind c = Some (mib,oib,ctor) /\
        mdecl = trans_mib mib /\
        idecl = trans_oib oib /\
        cdecl = mkConstructor ctor.1.1 ctor.2.
  Proof.
    intros Hlook.
    unfold EGlobalEnv.lookup_constructor,lookup_constructor_full,lookup_minductive in *;cbn in *.
    rewrite lookup_env_trans_env in Hlook.
    destruct (lookup_env _ _);cbn in *;try congruence.
    destruct g;cbn in *;try congruence.
    rewrite nth_error_map in Hlook;cbn in *.
    destruct (nth_error _ _);cbn in *;try congruence.
    unfold trans_ctors in *.
    rewrite nth_error_map in Hlook.
    destruct (nth_error _ c) eqn:nth1;cbn in *;try congruence.
    cbn in *.
    destruct p as [p0 ?];cbn in *.
    destruct p0;cbn in *.
    inversion Hlook;subst.
    repeat eexists;eauto.
  Qed.

  Lemma lookup_ctor_trans_env_inv ind c Σ0 mib oib ctor :
    lookup_constructor_full Σ0 ind c = Some (mib,oib,ctor) ->
    EGlobalEnv.lookup_constructor (trans_env Σ0) ind c = Some (trans_mib mib, trans_oib oib, mkConstructor ctor.1.1 ctor.2).
  Proof.
    intros Hlook.
    unfold EGlobalEnv.lookup_constructor,lookup_constructor_full,lookup_minductive in *;cbn in *.
    rewrite lookup_env_trans_env.
    destruct (lookup_env _ _);try congruence.
    destruct g;try congruence;cbn in *.
    rewrite nth_error_map;cbn in *.
    destruct (nth_error _ _);try congruence;cbn in *.
    unfold trans_ctors in *.
    rewrite nth_error_map.
    destruct (nth_error _ c) eqn:nth1;try congruence.
    cbn in *.
    destruct p as [p0 ?];cbn in *.
    destruct p0;cbn in *.
    now inversion Hlook;subst.
  Qed.

  Lemma lookup_ctor_dearg :
          forall (ind : inductive) (c : nat) mmasks (mdecl : mutual_inductive_body)
                 (idecl : one_inductive_body) cdecl,
            lookup_constructor_full Σ ind c = Some (mdecl, idecl, cdecl) ->
            Optimize.get_mib_masks ind_masks (inductive_mind ind) = Some mmasks ->
            lookup_constructor_full (dearg_env Σ) ind c =
              Some (dearg_mib ind_masks (inductive_mind ind) mdecl, dearg_oib mmasks (inductive_ind ind) idecl, dearg_ctor (param_mask mmasks) (get_branch_mask mmasks (inductive_ind ind) c) cdecl).
  Proof.
    intros ind c mmasks mdecl idecl cdecl Hlook Hmasks.
    unfold lookup_constructor_full,lookup_minductive in *.
    rewrite lookup_env_dearg_env.
    destruct (lookup_env _ _) as [mdecl_e|] eqn:Henv;try congruence;cbn in *.
    destruct mdecl_e as [| mib |]eqn:Hgd;try congruence;cbn in *.
    unfold dearg_mib.
    rewrite Hmasks;cbn.
    rewrite nth_error_mapi.
    destruct (nth_error _ _) as [|]eqn:nth;try congruence;cbn in *.
    rewrite nth_error_mapi.
    destruct (nth_error _ c);try congruence;cbn.
    now inversion Hlook;subst.
  Qed.

  Lemma lookup_ctor_lookup_env :
    forall m i ctr Σ ind c,
      EGlobalEnv.lookup_constructor Σ ind c = Some (m,i,ctr) ->
      EGlobalEnv.lookup_env Σ (inductive_mind ind) = Some (EAst.InductiveDecl m) /\
        nth_error (EAst.ind_bodies m) (inductive_ind ind) = Some i.
  Proof.
    intros m i ctr Σ0 ind0 c0 Hc0. unfold EGlobalEnv.lookup_constructor in *;cbn in Hc0.
    destruct (EGlobalEnv.lookup_env Σ0 _);try congruence. destruct g;try congruence.
    destruct (nth_error _ _) eqn:Hi;try congruence. destruct (nth_error _ c0);try congruence.
    easy.
  Qed.

  Lemma count_ones_zeros m : count_zeros m + count_ones m = #|m|.
  Proof.
    clear -m.
    induction m;cbn;auto.
    destruct a;cbn; unfold count_zeros, count_ones in *;lia.
  Qed.


  Local Hint Resolve <- forallb_Forall : dearg.

  Lemma eval_tApp_dearg {hd arg v} :
    with_constructor_as_block = false ->
    closed hd ->
    valid_cases hd ->
    is_expanded hd ->

    closed arg ->
    valid_cases arg ->
    is_expanded arg ->
    forall (ev : trans_env Σ e⊢ tApp hd arg ⇓ v),
      deriv_length ev <= S n ->
      trans_env (dearg_env Σ) e⊢ tApp (dearg hd) (dearg arg) ⇓ dearg v.
  Proof with auto with dearg.
    intros ? clos_hd valid_hd exp_hd clos_arg valid_arg exp_arg ev ev_len.
    depind ev; cbn in *;try congruence.
    - apply eval_box with (dearg t').
      + now unshelve eapply (IH _ _ _ _ _ ev1).
      + now unshelve eapply (IH _ _ _ _ _ ev2).
    - apply (eval_beta _ _ na (dearg b) _ (dearg a')).
      + now unshelve eapply (IH _ _ _ _ _ ev1).
      + now unshelve eapply (IH _ _ _ _ _ ev2).
      + facts.
        clear IHev1 IHev2 IHev3.
        revert ev3 ev_len.
        cbn in *.
        rewrite !closed_subst; eauto. 2:now apply closedn_dearg_aux.
        intros.
        rewrite <- (dearg_subst [a']) by easy.
        unshelve eapply (IH _ _ _ _ _ ev3)...
        * now apply is_expanded_aux_subst.
        * lia.
    - facts.
      apply (eval_fix
                _ _
                (map (map_def dearg) mfix)
                idx
                (map dearg argsv)
                _
                (dearg av)
                (dearg fn)).
      + trivial.
      + unshelve epose proof (IH _ _ _ _ _ ev1 _) as ev; trivial.
        1: lia.
        rewrite dearg_mkApps in ev.
        apply ev.
      + now unshelve eapply (IH _ _ _ _ _ ev2).
      + invert_facts.
        rewrite length_map.
        now apply dearg_cunfold_fix.
      + invert_facts.
        apply closed_cunfold_fix in e1 as ?; auto.
        apply valid_cases_cunfold_fix in e1 as ?; auto.
        cbn in *.
        apply is_expanded_cunfold_fix in e1 as ?; eauto with dearg.
        rewrite <- dearg_expanded, <- dearg_mkApps by easy.
        apply IHev3 with (ev := ev3)...
        * apply closed_mkApps...
        * apply valid_cases_mkApps...
        * apply is_expanded_aux_mkApps...
          erewrite is_expanded_aux_upwards; [|eassumption|easy].
          cbn.
          easy.
        * lia.
    - facts.
      rewrite dearg_expanded by assumption.
      cbn.
      rewrite dearg_mkApps.
      cbn.
      apply (eval_fix_value _ _ _ _ _ _ _ narg (dearg fn)).
      + trivial.
      + unshelve epose proof (IH _ _ _ _ _ ev1 _) as ev; trivial.
        1: lia.
        rewrite dearg_mkApps in ev.
        apply ev.
      + now unshelve eapply (IH _ _ _ _ _ ev2).
      + invert_facts.
        now apply dearg_cunfold_fix.
      + rewrite length_map.
        lia.
    - facts.
      apply (eval_fix' _ _ (map (map_def (dearg_aux [])) mfix) idx _ (dearg av) (dearg fn) _ narg unguarded).
      + unshelve epose proof (IH _ _ _ _ _ ev1 _) as ev; trivial.
        1: lia.
      + now apply dearg_cunfold_fix.
      + unshelve epose proof (IH _ _ _ _ _ ev2 _) as ev; trivial.
        1: lia.
      + eapply IHev3;eauto;try lia.
        eapply closed_cunfold_fix in e0 as c_fn;auto.
        eapply valid_cases_cunfold_fix in e0 as vc_fn;auto.
        eapply is_expanded_cunfold_fix in e0 as ?;auto with dearg.
    - facts.
      apply lookup_ctor_trans_env in e0 as e0'.
      destruct e0' as (mib & oib & ctor & Hlook & Hmib & Hoib & Hctor).
      rewrite dearg_expanded by assumption.
      cbn.
      rewrite dearg_mkApps.
      cbn.
      invert_facts.
      cbn in *; propify.
      rewrite dearg_single_masked by now rewrite length_map.
      assert (decl_ind :declared_inductive (trans_env Σ) ind (trans_mib mib) (trans_oib oib)).
        { unfold declared_inductive,declared_minductive.
          split. subst.
          eapply lookup_ctor_lookup_env;eauto. apply e0.
          eapply lookup_ctor_lookup_env;eauto. subst; apply e0.
        }
      specialize (valid_ind_mask_inductive _ _ _ _ valid_Σ decl_ind) as [mask [Hmask [Hparams _]]].
      set (trans_mib (dearg_mib ind_masks (inductive_mind ind) mib)) as mib_dearg.
      set (trans_oib (dearg_oib mask (inductive_ind ind) oib)) as oib_dearg.
      set (dearg_ctor (param_mask mask) (get_branch_mask mask (inductive_ind ind) c) ctor) as ctor_dearg.
      unshelve eapply
               (eval_construct _ _ _
                               mib_dearg
                               oib_dearg (mkConstructor ctor_dearg.1.1 ctor_dearg.2) _ _ _ _ _);eauto.
      + cbn in e.
        subst.
        subst oib_dearg.
        apply lookup_ctor_trans_env_inv.
        now apply lookup_ctor_dearg.
      + rewrite <- dearg_single_masked.
        change (dearg_single (get_ctor_mask ind c) (tConstruct ind c []) (map dearg args)) with
          (dearg_aux (map dearg args) (tConstruct ind c [])).
        rewrite <- dearg_mkApps.
        now unshelve eapply (IH _ _ _ _ _ ev1 _).
        now rewrite length_map.
      + propify. cbn.
        unfold trans_mib,dearg_mib, cstr_arity in *;cbn.
        subst. cbn in *.
        rewrite <- Hparams in l.
        rewrite masked_count_zeros in * by (rewrite length_map;lia).
        rewrite length_map.
        specialize (count_zeros_le (param_mask mask)) as HH.
        unfold get_ctor_mask, dearg_ctor in *. rewrite Hmask in *. cbn.
        destruct ctor as [p0]. destruct p0;cbn in *.
        rewrite count_zeros_distr_app.
        rewrite length_app in *.
        remember (get_branch_mask _ _ _) as bm.
        assert (count_zeros bm <= #|bm|) by apply count_zeros_le.
        assert (count_zeros bm + count_ones bm = #|bm| ) by apply count_ones_zeros.
        lia.
      + now unshelve eapply (IH _ _ _ _ _ ev2 _).
    - facts.
      rewrite dearg_expanded by trivial.
      cbn.
      apply eval_app_cong.
      + now unshelve eapply (IH _ _ _ _ _ ev1 _).
      + destruct (dearg_elim f'); cbn.
        * invert_facts.
          cbn in *; propify.
          rewrite dearg_single_masked by (now rewrite length_map).
          rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps, isConstructApp_mkApps;cbn in *.
          rewrite isPrimApp_mkApps, isLazyApp_mkApps in *.
          destruct with_guarded_fix;cbn;intuition auto.
          now rewrite EOptimizePropDiscr.isFix_mkApps;cbn.
        * rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps, isConstructApp_mkApps in *;cbn in *.
          propify.
          destruct with_guarded_fix;cbn in *; intuition.
        * unfold dearg_case.
          destruct with_guarded_fix;cbn.
          now rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps, isConstructApp_mkApps, isPrimApp_mkApps, isLazyApp_mkApps;cbn.
          now rewrite isLambda_mkApps, isBox_mkApps, isConstructApp_mkApps, EOptimizePropDiscr.isFix_mkApps, isPrimApp_mkApps, isLazyApp_mkApps;cbn.
        * unfold dearg_proj.
          unfold dearg_case.
          destruct with_guarded_fix;cbn.
          ** now rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps, isConstructApp_mkApps, isPrimApp_mkApps, isLazyApp_mkApps;cbn.
          ** now rewrite isLambda_mkApps, isBox_mkApps, isConstructApp_mkApps, EOptimizePropDiscr.isFix_mkApps, isPrimApp_mkApps, isLazyApp_mkApps;cbn.
        * rewrite !isLambda_mkApps, !isFixApp_mkApps, !EOptimizePropDiscr.isFix_mkApps, !isBox_mkApps, isConstructApp_mkApps, isPrimApp_mkApps, isLazyApp_mkApps in *
            by now destruct hd.
          rewrite length_map.
          destruct with_guarded_fix;cbn;auto;
            destruct args;cbn;auto;destruct hd;try congruence;cbn;auto.
      + now unshelve eapply (IH _ _ _ _ _ ev2 _).
  Qed.

  Lemma eval_mkApps_dearg hd args v :
    with_constructor_as_block = false ->

    closed hd ->
    valid_cases hd ->
    is_expanded hd ->

    Forall (closedn 0) args ->
    Forall valid_cases args ->
    Forall is_expanded args ->
    forall (ev : trans_env Σ e⊢ mkApps hd args ⇓ v),
      deriv_length ev <= n ->
      trans_env (dearg_env Σ) e⊢ mkApps (dearg hd) (map dearg args) ⇓ dearg v.
  Proof.
    intros ? clos_hd valid_hd exp_hd clos_args valid_args exp_args ev ev_len.
    pose proof (eval_mkApps_deriv ev) as (hdv & ev_hd & argsv & ev_args & ev_args_len).
    induction ev_args using All2_rev_rect; cbn in *.
    - assert (hdv = v) as -> by (now eapply eval_deterministic).
      unshelve eapply (IH _ _ _ _ _ ev_hd _); auto.
      lia.
    - revert ev ev_len ev_args_len.
      rewrite map_app, !mkApps_app by easy.
      cbn.
      intros.
      rewrite <- dearg_expanded, <- dearg_mkApps by easy.
      unshelve eapply eval_tApp_dearg; auto.
      + apply closed_mkApps; auto.
        now apply Forall_snoc in clos_args.
      + apply valid_cases_mkApps; auto.
        now apply Forall_snoc in valid_args.
      + apply is_expanded_aux_mkApps; [now eapply is_expanded_aux_upwards|].
        now apply Forall_snoc in exp_args.
      + now apply Forall_snoc in clos_args.
      + now apply Forall_snoc in valid_args.
      + now apply Forall_snoc in exp_args.
  Qed.

  Lemma eval_mkApps_dearg_reduce {hd args v} :
    with_constructor_as_block = false ->

    closed hd ->
    valid_cases hd ->
    is_expanded hd ->

    Forall (closedn 0) args ->
    Forall valid_cases args ->
    Forall is_expanded args ->
    (args = [] -> trans_env (dearg_env Σ) e⊢ dearg hd ⇓ dearg v) ->
    forall (ev : trans_env Σ e⊢ mkApps hd args ⇓ v),
      deriv_length ev <= S n ->
      trans_env (dearg_env Σ) e⊢ mkApps (dearg hd) (map dearg args) ⇓ dearg v.
  Proof.
    intros ? clos_hd valid_hd exp_hd clos_args valid_args exp_args no_args ev ev_len.
    destruct args as [|? ? _] using MRList.rev_ind; cbn in *; [easy|].
    revert ev ev_len.
    rewrite map_app, !mkApps_app.
    cbn.
    intros.
    pose proof (eval_tApp_deriv ev) as (? & ? & ? & ? & ?).
    eapply eval_tApp_heads.
    2: { unshelve eapply eval_mkApps_dearg.
         2: eassumption.
         all: auto.
         - now apply Forall_snoc in clos_args.
         - now apply Forall_snoc in valid_args.
         - now apply Forall_snoc in exp_args.
         - lia. }
    1: { unshelve eapply IH.
         2: eassumption.
         - apply Forall_snoc in clos_args.
           now apply closed_mkApps.
         - apply Forall_snoc in valid_args.
           now apply valid_cases_mkApps.
         - apply is_expanded_aux_mkApps; [now eapply is_expanded_aux_upwards|].
           now apply Forall_snoc in exp_args.
         - lia. }
      unshelve eapply eval_tApp_dearg.
      all: auto.
    - apply Forall_snoc in clos_args.
      now apply closed_mkApps.
    - apply Forall_snoc in valid_args.
      now apply valid_cases_mkApps.
    - apply Forall_snoc in exp_args.
      apply is_expanded_aux_mkApps; [|easy].
      now eapply is_expanded_aux_upwards.
    - now apply Forall_snoc in clos_args.
    - now apply Forall_snoc in valid_args.
    - now apply Forall_snoc in exp_args.
  Qed.

  Set SsrRewrite.
  Lemma count_zeros_nth_error l :
    count_zeros l = 0 ->
    (forall n x, nth_error l n = Some x -> x = true).
  Proof using.
    clear.
    unfold count_zeros.
    induction l; cbn => //.
    - intros _ n x; rewrite nth_error_nil //.
    - destruct a => //=. intros hl n x.
      destruct n => //=.
      + intros [= <-] => //.
      + intros hnth. eapply IHl; eauto.
  Qed.

  Lemma wellformed_dearg_aux (efl := all_env_flags) k args t :
    valid_cases t ->
    wellformed (trans_env Σ) k t ->
    Forall (wellformed (trans_env (dearg_env Σ)) k) args ->
    wellformed (trans_env (dearg_env Σ)) k (dearg_aux args t).
  Proof.
    clear IH.
    intros valid_t clos_t clos_args.
    induction t in k, args, valid_t, clos_t, clos_args |- * using term_forall_list_ind;
      cbn -[EGlobalEnv.lookup_projection EGlobalEnv.lookup_inductive EGlobalEnv.lookup_constructor] in *; intros;
      try solve [intros; rewrite ?wellformed_mkApps; try easy; intros; repeat (rtoProp; cbn; intuition eauto; solve_all)];
      repeat (rtoProp; cbn; intuition eauto; solve_all).
    - intros. eapply wellformed_dearg_single; eauto. cbn.
      rewrite !lookup_env_trans_env in clos_t |- *.
      rewrite lookup_env_dearg_env. destruct lookup_env => //=. cbn in clos_t.
      destruct g => //.
    - intros. eapply wellformed_dearg_single; eauto.
      cbn -[EGlobalEnv.lookup_constructor]; eauto. move: H.
      destruct EGlobalEnv.lookup_constructor as [[[mib oib] cb]|] eqn:hc => //= _.
      eapply lookup_ctor_trans_env in hc as hc'; destruct hc' as [mib' [oib' [ctor' []]]]. intuition subst.
      assert (decl_ind :declared_inductive (trans_env Σ) i (trans_mib mib') (trans_oib oib')).
      { unfold declared_inductive,declared_minductive.
        eapply lookup_ctor_lookup_env;eauto. }
      specialize (valid_ind_mask_inductive _ _ _ _ valid_Σ decl_ind) as [mask [Hmask Hparams]].
      eapply lookup_ctor_dearg in H; tea.
      erewrite lookup_ctor_trans_env_inv; tea.
    - destruct p. rewrite wellformed_mkApps; try easy.
      unfold dearg_case.
      rewrite /wf_brs in H.
      destruct (EGlobalEnv.lookup_inductive _ _) as [[mib oib]|] eqn:hl => //.
      assert (decl_ind :declared_inductive (trans_env Σ) i mib oib).
      { move: hl. unfold EGlobalEnv.lookup_inductive. cbn.
        unfold declared_inductive,declared_minductive. destruct EGlobalEnv.lookup_env => //.
        destruct g => //. destruct nth_error eqn:hnth => //. intros [= <- <-]. split; eauto. }
      specialize (valid_ind_mask_inductive _ _ _ _ valid_Σ decl_ind) as [mask [Hmask Hparams]].
      rewrite Hmask.
      rtoProp; intuition eauto; solve_all.
      cbn [wellformed]. rtoProp; intuition eauto. len.
      rewrite mapi_length length_map. rewrite /wf_brs.
      { unfold EGlobalEnv.lookup_inductive. cbn.
        move: hl. cbn.
        rewrite !lookup_env_trans_env lookup_env_dearg_env.
        destruct lookup_env => //=. destruct g => //=.
        rewrite !nth_error_map. unfold dearg_mib. rewrite Hmask. cbn.
        rewrite nth_error_mapi. destruct nth_error => //=.
        intros [= <- <-].
        move: H; cbn. now rewrite /trans_ctors !length_map !mapi_length. }
      cbn.
      unfold mapi. clear clos_args IHt H.
      unfold valid_case_masks in H3. rewrite Hmask in H3.
      move/andP: H3 => [] _ hbrs.
      eapply alli_Alli in hbrs.
      eapply Alli_All_mix in hbrs; tea. clear H0.
      generalize 0.
      induction hbrs; [easy|]; intros n'.
      cbn in p.
      cbn [map mapi_rec forallb]. rtoProp.
      split.
      * unfold dearg_case_branch,dearg_branch_body.
        destruct (_ <=? _) eqn:Hmask';[|cbn;easy].
        remember (complete_ctx_mask _ _) as mm. cbn.
        assert (#|mm| = #|hd.1|) by now subst;propify;apply complete_ctx_mask_length.
        rewrite masked_count_zeros. lia.
        specialize (wellformed_dearg_case_branch_body_rec (trans_env (dearg_env Σ)) 0 ((#|hd.1| - #|mm|) + k) mm ((dearg_aux [] hd.2))) as b.
        cbn in b.
        replace (#|mm| + (#|hd.1| - #|mm| + k)) with (#|hd.1| + k) in * by lia.
        rewrite <- Nat.add_assoc.
        apply b.
        now apply p.
      * destruct p. eapply IHhbrs.
    - destruct s. rewrite wellformed_mkApps; rtoProp; intuition auto; solve_all.
      destruct lookup_projection as [[[[mib oib] cb] pb]|] eqn:hl => //.
      assert (decl_ind :declared_inductive (trans_env Σ) proj_ind mib oib).
      { move: hl. unfold EGlobalEnv.lookup_inductive. cbn.
        unfold declared_inductive,declared_minductive. destruct EGlobalEnv.lookup_env => //.
        destruct g => //. destruct nth_error eqn:hnth => //.
        destruct EAst.ind_ctors => //. destruct (nth_error _ proj_arg) => //. now intros [= <- <- <- <-]. }
      specialize (valid_ind_mask_inductive _ _ _ _ valid_Σ decl_ind) as [mask [Hmask [Hparams Hprojs]]].
      unfold dearg_proj. cbn -[lookup_projection] in *.
      rtoProp; intuition auto.
      revert hl; cbn.
      rewrite !lookup_env_trans_env !lookup_env_dearg_env.
      destruct lookup_env => //=.
      destruct g => //=. rewrite !nth_error_map /dearg_mib //=.
      destruct nth_error eqn:hi => //=; eauto.
      destruct o; cbn. destruct ind_ctors eqn:hcs => //=.
      rewrite nth_error_map. destruct (nth_error _ proj_arg) eqn:hp => //=.
      intros [= <- <- <- <-]. rewrite Hmask /=.
      rewrite nth_error_mapi hi //= /= nth_error_map.
      rewrite /check_oib_masks_trans /= in Hprojs.
      destruct ind_projs; [now rewrite nth_error_nil in hp|];
      rewrite /= length_map in Hprojs.
      move: H2. rewrite /valid_proj. rewrite Hmask.
      set (cm := get_branch_mask _ _ _) in *.
      move/andP=> [] _. rewrite nth_nth_error.
      eapply nth_error_Some_length in hp. clearbody cm.
      destruct (nth_error (masked _ _) _) eqn:h' => //=.
      eapply nth_error_None in h'.
      move: h'. move/andP: Hprojs => [] _ Hprojs.
      apply eqb_eq in Hprojs.
      destruct (nth_error cm proj_arg) eqn:hmp.
      2:{ cbn. eapply nth_error_None in hmp. cbn in hp. lia. }
      destruct b => //. intros hm _.
      move: hm.
      rewrite masked_count_zeros. cbn; lia. cbn.
      intros. assert (count_zeros cm + (S #|ind_projs| - #|cm|) = count_zeros cm) by lia.
      rewrite {}H2 in hm. cbn in hp. rewrite -Hprojs in hp.
      pose proof (count_ones_zeros (firstn proj_arg cm)).
      assert (count_ones (firstn proj_arg cm) = #|firstn proj_arg cm| - count_zeros (firstn proj_arg cm)). lia.
      rewrite {}H3 in hm.
      rewrite -{1}(firstn_skipn proj_arg cm) in hm.
      rewrite count_zeros_distr_app in hm.
      assert (#|firstn proj_arg cm| = proj_arg). rewrite length_firstn. lia.
      rewrite H3 in hm. move: hm.
      assert (proj_arg - (proj_arg - count_zeros (firstn proj_arg cm)) = proj_arg - proj_arg + count_zeros (firstn proj_arg cm)) as ->. lia.
      rewrite Nat.sub_diag /=. intros.
      assert (count_zeros (skipn proj_arg cm) = 0) by lia.
      have hc:= (count_zeros_nth_error _ H4 0 false) => //.
      forward hc.
      rewrite nth_error_skipn Nat.add_0_r //.
      by noconf hc.
    - rewrite wellformed_mkApps; cbn; rtoProp; intuition eauto; solve_all.
      destruct (dbody x); cbn in *; eauto; try congruence.
      revert H0. unfold wf_fix.
      rewrite length_map.
      rtoProp; intuition eauto. unfold test_def in *; solve_all.
    - rewrite wellformed_mkApps; cbn; rtoProp; intuition eauto; solve_all.
      revert clos_t. unfold wf_fix.
      rewrite length_map.
      rtoProp; intuition eauto. unfold test_def in *; solve_all.
    - rewrite wellformed_mkApps; cbn; rtoProp; intuition solve_all. solve_all_k 7.
  Qed.

  Lemma wellformed_dearg (efl := all_env_flags) k t :
    valid_cases t ->
    wellformed (trans_env Σ) k t ->
    wellformed (trans_env (dearg_env Σ)) k (dearg t).
  Proof.
    intros vt wf.
    eapply wellformed_dearg_aux; tea; constructor.
  Qed.

  Lemma All_masked {A} {P : A -> Type} m l : All P l -> All P (masked m l).
  Proof.
    induction 1 in m |- *; cbn; destruct m; try constructor; eauto.
    cbn. destruct b; eauto.
  Qed.

  Lemma isEtaExp_dearg_single_construct Γ ind i block_args l mib oib :
    is_nil block_args ->
    forall mask, get_mib_masks (inductive_mind ind) = Some mask ->
    declared_inductive (trans_env Σ) ind mib oib ->
    #|param_mask mask| = mib.(EAst.ind_npars) ->
    isEtaExp_app (trans_env Σ) ind i #|l| ->
    forallb (isEtaExp (trans_env (dearg_env Σ)) Γ) l ->
    #|get_ctor_mask ind i| <= #|l| ->
    isEtaExp (trans_env (dearg_env Σ)) Γ (dearg_single (get_ctor_mask ind i) (tConstruct ind i block_args) l).
  Proof.
    destruct block_args => //. intros _ mask getm decli hpars.
    intros etsal etak hml.
    rewrite dearg_single_masked; auto.
    rewrite isEtaExp_Constructor. rewrite masked_length; auto. bool.
    2:solve_all.
    move: etsal hml.
    unfold isEtaExp_app. rewrite /get_ctor_mask getm length_app.
    unfold lookup_constructor_pars_args.
    destruct EGlobalEnv.lookup_constructor as [[[mib' oib'] cb]|]eqn:hl => //=.
    assert (decl_ind :declared_inductive (trans_env Σ) ind mib' oib').
    { move: hl. unfold EGlobalEnv.lookup_inductive. cbn.
      unfold declared_inductive,declared_minductive. destruct EGlobalEnv.lookup_env => //.
      destruct g => //. destruct nth_error eqn:hnth => //.
      destruct (nth_error _ i) eqn:hnth' => //. now intros [= <- <- <-]. }
    specialize (valid_ind_mask_inductive _ _ _ _ valid_Σ decl_ind) as [mask' [Hmask [Hparams Hprojs]]].
    rewrite Hmask in getm. noconf getm.
    assert (oib = oib' /\ mib = mib').
    {move: decli decl_ind. rewrite /declared_inductive /declared_minductive. intuition congruence. }
    destruct H; subst oib' mib'.
    pose proof hl as hl'.
    eapply lookup_ctor_trans_env in hl as [mib' [oib' [ctor' []]]]. intuition subst.
    eapply lookup_ctor_dearg in H; tea. cbn in etsal.
    eapply lookup_ctor_trans_env_inv in H as ->. cbn.
    move/andP: Hprojs => [] Hcs _.
    destruct decli.
    destruct mib'; unfold dearg_mib. rewrite Hmask. cbn in *.
    apply Nat.leb_le in etsal. apply Nat.leb_le.
    unfold dearg_ctor. destruct ctor' as [[cna ctys] cnargs]. cbn in *.
    rewrite count_zeros_distr_app.
    move: hml.
    intros hl.
    assert (cnargs = #|get_branch_mask mask (inductive_ind ind) i|).
    { destruct decl_ind. red in H1. rewrite H1 H0 in hl'. destruct (nth_error _ i) eqn:hnth. noconf hl'.
      unfold trans_ctors in Hcs. destruct oib'; cbn in *.
      eapply forallbi_nth_error in hnth; tea. cbn in hnth. rewrite Nat.add_0_r in hnth. now apply eqb_eq in hnth. noconf hl'. }
    clear hl'. subst cnargs.
    set (bm := get_branch_mask _ _ _) in *.
    rewrite -{1}(count_ones_zeros bm).
    replace (count_zeros bm + count_ones bm - count_ones bm) with (count_zeros bm) by lia. lia.
    now eapply All_masked.
  Qed.

  Lemma expanded_dearg_aux (efl := all_env_flags) Γ t :
    valid_cases t ->
    isEtaExp (trans_env Σ) Γ t ->
    forall args, forallb (isEtaExp (trans_env (dearg_env Σ)) Γ) args ->
    isEtaExp (trans_env (dearg_env Σ)) Γ (dearg_aux args t).
  Proof.
    clear IH.
    apply_funelim (isEtaExp (trans_env Σ) Γ t); intros.
    all:match goal with H : is_true (valid_cases _) |- _ => cbn in H; bool end; intros; simp_eta.
    all:cbn; simp_eta; toAll; bool; try rewrite -> forallb_InP_spec in *.
    all:try solve [solve_all].
    all:try solve [eapply isEtaExp_mkApps_intro; simp_eta; eauto; bool; solve_all].
    - eapply isEtaExp_dearg_single; simp_eta.
    - eapply isEtaExp_dearg_single; simp_eta => //.
      unfold is_nil.
      rewrite H andb_true_r.
      move: H0. rewrite /isEtaExp_app.
      unfold lookup_constructor_pars_args.
      destruct EGlobalEnv.lookup_constructor as [[[mib oib] cb]|]eqn:hl => //=.
      assert (decl_ind :declared_inductive (trans_env Σ) ind mib oib).
      { move: hl. unfold EGlobalEnv.lookup_inductive. cbn.
        unfold declared_inductive,declared_minductive. destruct EGlobalEnv.lookup_env => //.
        destruct g => //. destruct nth_error eqn:hnth => //.
        destruct (nth_error _ i) eqn:hnth' => //. now intros [= <- <- <-]. }
      specialize (valid_ind_mask_inductive _ _ _ _ valid_Σ decl_ind) as [mask [Hmask [Hparams Hprojs]]].
      eapply lookup_ctor_trans_env in hl as [mib' [oib' [ctor' []]]]. intuition subst.
      eapply lookup_ctor_dearg in H0; tea.
      eapply lookup_ctor_trans_env_inv in H0; rewrite H0. clear H0. cbn in *.
      destruct mib'; cbn in *. unfold dearg_mib. rewrite Hmask /=.
      eapply Nat.leb_le in H4. assert (ind_npars = 0) by lia. subst ind_npars.
      apply Nat.eqb_eq in Hparams. destruct (param_mask) => //. cbn.
      unfold dearg_ctor. destruct ctor'; cbn in *. destruct p. cbn. assert (n0 = 0) by lia. apply Nat.leb_le. lia.
    - destruct ind. bool. eapply isEtaExp_mkApps_intro; simp_eta; eauto; bool; solve_all.
      unfold dearg_case. cbn. simp_eta. bool. solve_all.
      unfold valid_case_masks in H5. destruct get_mib_masks eqn:cm => //.
      unfold dearg_case_branches. simp_eta. eapply All_mapi, Alli_map.
      bool. eapply alli_Alli in H5. eapply Alli_All_mix in H5; tea.
      eapply Alli_impl; tea; cbn. intuition eauto. destruct x. bool. cbn in *.
      unfold dearg_case_branch. cbn. rewrite H6.
      unfold dearg_branch_body. cbn. apply Nat.leb_le in H6.
      rewrite masked_length. rewrite complete_ctx_mask_length //.
      replace (count_zeros (complete_ctx_mask (get_branch_mask m (inductive_ind i) n1) l) + #|l| - #|complete_ctx_mask (get_branch_mask m (inductive_ind i) n1) l|) with
        (count_zeros (complete_ctx_mask (get_branch_mask m (inductive_ind i) n1) l) + (#|l| - #|complete_ctx_mask (get_branch_mask m (inductive_ind i) n1) l|)).
      2:{ rewrite complete_ctx_mask_length; lia. }
      rewrite complete_ctx_mask_length //. rewrite Nat.sub_diag Nat.add_0_r.
      eapply (isEtaExp_dearg_case_branch_body_rec _ 0).
      rewrite complete_ctx_mask_length //.
      unfold dearg_case_branches. solve_all.
      unfold dearg_case_branches. solve_all.
    - destruct p. eapply isEtaExp_mkApps_intro; simp_eta; eauto; bool; solve_all.
      bool. unfold dearg_proj. now simp_eta.
    - rewrite test_primIn_spec in H1. eapply InPrim_primProp in H.
      eapply isEtaExp_mkApps_intro; simp_eta; eauto; bool; solve_all.
      solve_all.
      eapply primProp_map, primProp_impl; solve_all.
    - rewrite dearg_aux_mkApps. cbn.
      eapply valid_cases_mkApps_inv in H0 as [].
      move: H1. rewrite /isEtaExp_app /lookup_constructor_pars_args.
      destruct EGlobalEnv.lookup_constructor as [[[mib oib] cb]|]eqn:hl => //=.
      assert (decl_ind :declared_inductive (trans_env Σ) ind mib oib).
      { move: hl. unfold EGlobalEnv.lookup_inductive. cbn.
        unfold declared_inductive,declared_minductive. destruct EGlobalEnv.lookup_env => //.
        destruct g => //. destruct nth_error eqn:hnth => //.
        destruct (nth_error _ i) eqn:hnth' => //. now intros [= <- <- <-]. }
      specialize (valid_ind_mask_inductive _ _ _ _ valid_Σ decl_ind) as [mask [Hmask [Hparams Hprojs]]].
      pose proof hl as hl'.
      eapply lookup_ctor_trans_env in hl as [mib' [oib' [ctor' []]]]. intuition subst.
      eapply lookup_ctor_dearg in H1; tea.
      cbn.
      eapply Nat.eqb_eq in Hparams.
      eapply isEtaExp_dearg_single_construct; tea.
      + len. unfold isEtaExp_app.
        rewrite /lookup_constructor_pars_args hl' //=. eapply Nat.leb_le in H7. cbn in H7. apply Nat.leb_le. lia.
      + rewrite forallb_app; bool; solve_all.
      + len. rewrite /get_ctor_mask Hmask. len. rewrite Hparams.
        move/andP: Hprojs => [] hc _.
        destruct decl_ind. red in H6.
        unfold EGlobalEnv.lookup_constructor in hl'.
        rewrite /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive H6 //= H8 in hl'.
        destruct (nth_error _ i) eqn:nthc => //. noconf hl'.
        eapply forallbi_nth_error in hc; tea. rewrite Nat.add_0_r /= in hc. cbn in H7.
        apply Nat.eqb_eq in hc. apply Nat.leb_le in H7. rewrite -hc in H7. cbn. lia.
    - rewrite dearg_aux_mkApps. eapply valid_cases_mkApps_inv in H1 as[].
      cbn in H1. cbn.
      rewrite mkApps_app. eapply isEtaExp_mkApps_intro; solve_all.
      eapply isEtaExp_FixApp.
      + move: H2. unfold isEtaExp_fixapp. rewrite nth_error_map.
        destruct nth_error eqn:hnth => //=; now len.
      + rewrite forallb_InP_spec in H5.
        cbn. clear H6.
        replace (rev_map (fun d0 : def term => S (rarg d0)) (map (map_def (dearg_aux [])) mfix) ++ Γ0) with
          (rev_map (fun d0 : def term => S (rarg d0)) mfix ++ Γ0).
        2:{ f_equal. rewrite !rev_map_spec. f_equal. now rewrite map_map_compose /=. }
        set (rargs := rev_map _ _) in *. clearbody rargs. solve_all. bool. destruct (dbody x) => //.
      + solve_all.
    - rewrite dearg_aux_mkApps /=.
      destruct nth_error eqn:hnth => //=. cbn in H1.
      eapply expanded_isEtaExp. eapply expanded_tRel_app; tea. len. apply Nat.leb_le in H1. lia.
      eapply valid_cases_mkApps_inv in H0 as [].
      eapply All_Forall, All_app_inv. solve_all. eapply isEtaExp_expanded. eauto.
      solve_all. now eapply isEtaExp_expanded.

    - apply valid_cases_mkApps_inv in H1 as [].
      specialize (H H1 H2).
      rewrite dearg_aux_mkApps. eapply H. rewrite forallb_app. bool.
      solve_all.
  Qed.

  Lemma expanded_dearg (efl := all_env_flags) Γ t :
    valid_cases t ->
    isEtaExp (trans_env Σ) Γ t ->
    isEtaExp (trans_env (dearg_env Σ)) Γ (dearg t).
  Proof.
    intros vc ise. eapply expanded_dearg_aux; eauto.
  Qed.

End dearg.

Set SsrRewrite.

Lemma env_closed_dearg Σ :
  env_closed (trans_env Σ) ->
  env_closed (trans_env (dearg_env Σ)).
Proof.
  intros clos.
  induction Σ as [|((kn & has_deps) & decl) Σ IH]; [easy|].
  cbn in *.
  destruct decl; [|easy|].
  - cbn in *.
    propify; split; [|easy].
    destruct (cst_body c); [|easy].
    cbn in *.
    eapply closedn_dearg_aux; [|easy].
    now eapply closedn_dearg_lambdas.
  - cbn in *.
    now destruct o.
Qed.

Lemma wf_glob_dearg (efl := all_env_flags) Σ :
  valid_masks_env Σ ->
  wf_glob (trans_env Σ) ->
  wf_glob (trans_env (dearg_env Σ)).
Proof.
  intros val clos. revert val.
  induction Σ as [|((kn & has_deps) & decl) Σ IH]; [easy|].
  rewrite /valid_masks_env /=;  move/andP => [] hd he.
  depelim clos. cbn.
  constructor; eauto.
  destruct decl; cbn in *.
  - destruct c as [ty []]; [|easy].
    cbn in *. unfold dearg.
    move/andP: hd => [] vm vc.
    eapply wellformed_dearg_aux; auto.
    now eapply valid_cases_dearg_lambdas.
    eapply wellformed_dearg_lambdas; auto.
  - cbn in *.
    unfold dearg_mib.
    destruct get_mib_masks => //=.
    solve_all. eapply All_mapi.
    move/andP: hd => [] _ hf.
    eapply forallbi_Alli in hf.
    eapply Alli_All_mix in hf; tea. clear H.
    eapply Alli_impl; tea; cbn.
    intros n []; rewrite /trans_oib /dearg_oib //= /wf_inductive /wf_projections /=.
    rewrite /check_oib_masks /=.
    destruct ind_projs => //=; rewrite ?masked_nil //=.
    move=> [] /andP[] hcs /Nat.eqb_eq hps.
    destruct ind_ctors => //=. destruct ind_ctors => //=. len.
    intros h % eqb_eq.
    destruct map eqn:hm; destruct p0 as [[pn pars] k] => //=.
    cbn in h. subst k.
    rewrite masked_length. now (cbn; lia).
    cbn. rewrite hps.
    apply/Nat.eqb_spec.
    pose proof (count_ones_zeros (get_branch_mask m0 n 0)). lia.
  - now destruct o; cbn.
  - clear hd. clear -H0.
    move: H0; induction Σ; cbn; auto.
    intros h; depelim h; constructor; cbn; eauto.
    now destruct a as [[kn' b] d]; cbn in *.
    solve_all.
Qed.

Lemma trans_env_debox Σ : trans_env Σ = trans_env (debox_env_types Σ).
Proof.
  unfold debox_env_types.
  generalize Σ at 2.
  induction Σ; cbn; auto. intros Σ0.
  f_equal. f_equal.
  - destruct a as [[kn d] []]; cbn.
    * destruct c as [? []]; cbn => //.
    * destruct m. unfold trans_mib, debox_type_mib; cbn.
      f_equal. f_equal.
      rewrite map_map_compose. eapply map_ext.
      intros []; unfold trans_oib; cbn. f_equal.
      rewrite map_map_compose. eapply map_ext => //.
      intros [[] ?] => //.
      now rewrite map_map_compose.
    * destruct o => //=. destruct p => //.
  - apply IHΣ.
Qed.

Lemma wf_glob_debox (efl := all_env_flags) Σ :
  wf_glob (trans_env Σ) ->
  wf_glob (trans_env (debox_env_types Σ)).
Proof.
  now rewrite trans_env_debox.
Qed.

Section EtaFix.
  Import EEtaExpandedFix.
  Lemma expanded_dearg_env (efl := all_env_flags) Σ :
    valid_masks_env Σ ->
    expanded_global_env (trans_env Σ) ->
    expanded_global_env (trans_env (dearg_env Σ)).
  Proof.
    induction Σ; intros vm exp; depelim exp.
    - constructor.
    - cbn in *. constructor; eauto. move/andP: vm => [] va vΣ. now apply IHΣ.
      destruct a as [[kn ?] []]; cbn => //.
      + destruct c as [? []]; cbn => //.
        cbn in H.
        move/andP: vm => [] /andP[] vdm vc vΣ.
        eapply expanded_isEtaExp in H.
        eapply isEtaExp_expanded.
        eapply expanded_dearg; eauto.
        now eapply valid_cases_dearg_lambdas.
        now eapply isEtaExp_dearg_lambdas.
      + destruct o; cbn; constructor.
  Qed.
End EtaFix.

Unset SsrRewrite.

Lemma valid_dearg_mask_dearg_aux mask t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (dearg t).
Proof.
  intros valid.
  induction t in mask, t, valid |- *; auto; cbn in *;
    try (now destruct mask; [apply valid_dearg_mask_nil|]).
  destruct mask; [easy|].
  propify; split; [|easy].
  destruct b; [|easy].
  propify.
  now rewrite is_dead_dearg_aux.
Qed.

Lemma masked_app {X} m m' (xs : list X) :
  masked (m ++ m') xs = firstn (count_zeros m) (masked m xs) ++ masked m' (skipn #|m| xs).
Proof.
  induction m in m', xs |- *; cbn in *; [easy|].
  destruct xs.
  - destruct a; cbn.
    + now rewrite firstn_nil, skipn_nil, masked_nil.
    + now rewrite skipn_nil, masked_nil.
  - destruct a; cbn.
    + now rewrite IHm, skipn_S.
    + f_equal.
      apply IHm.
Qed.

Lemma masked_map {X Y} m (f : X -> Y) xs :
  masked m (map f xs) = map f (masked m xs).
Proof.
  induction m as [|[] m IH] in xs |- *; [easy| |]; cbn in *.
  - destruct xs; cbn in *; [easy|].
    apply IH.
  - destruct xs; cbn in *; [easy|].
    f_equal; apply IH.
Qed.

Lemma nth_error_masked {X} m (xs : list X) n :
  nth n m false = false ->
  nth_error (masked m xs) (n - count_ones (firstn n m)) =
  nth_error xs n.
Proof.
  intros not_removed.
  induction n in m, xs, not_removed |- *; cbn in *.
  - destruct xs; [now rewrite masked_nil|].
    destruct m; [easy|].
    now destruct b.
  - destruct m; cbn in *; [easy|].
    destruct xs; cbn in *.
    + now rewrite nth_error_nil.
    + destruct b; cbn in *.
      * now apply IHn.
      * rewrite Nat.sub_succ_l; [now apply IHn|].
        transitivity #|firstn n m|; [|now rewrite length_firstn].
        apply filter_length.
Qed.

Definition dearged_ctor_arity (mm : option mib_masks) (ind_index : nat) (ctor_index : nat) (ctor_body : constructor_body) : constructor_body :=
  match mm with
  | Some mm0 => mkConstructor (cstr_name ctor_body) (cstr_nargs ctor_body - count_ones (get_branch_mask mm0 ind_index ctor_index))
  | None => ctor_body
  end.


Lemma constructor_isprop_pars_decl_trans_env_dearg_env Σ ind c b cdecl pars :
  let mm := get_mib_masks (inductive_mind ind) in
  constructor_isprop_pars_decl (trans_env Σ) ind c = Some (b, pars, cdecl) ->
  constructor_isprop_pars_decl (trans_env (dearg_env Σ)) ind c = Some (b, dearged_npars mm pars, dearged_ctor_arity mm (inductive_ind ind) c cdecl).
Proof.
  intros ? Hc.
  unfold constructor_isprop_pars_decl,dearged_npars in *;cbn in *.
  rewrite !lookup_env_trans_env, lookup_env_dearg_env in *.
  destruct lookup_env; cbn in *;try congruence.
  destruct g; cbn in *; try congruence; auto.
  rewrite !nth_error_map in *.
  unfold dearg_mib.
  destruct get_mib_masks;cbn in *;try congruence;auto.
  cbn in *.
  rewrite nth_error_mapi.
  destruct nth_error;cbn in *;try congruence;auto.
  unfold trans_ctors in *.
  repeat rewrite nth_error_map in *.
  rewrite nth_error_mapi.
  destruct nth_error;cbn in *;try congruence;auto.
  destruct p;cbn in *.
  destruct p;cbn in *.
  now inversion Hc.
Qed.

Lemma inductive_isprop_and_pars_trans_env_dearg_env :
  forall (Σ : global_env) (ind : inductive) (pars : nat),
    inductive_isprop_and_pars (trans_env Σ) ind = Some (true, pars) ->
    inductive_isprop_and_pars (trans_env (dearg_env Σ)) ind =
      Some (true, dearged_npars (get_mib_masks (inductive_mind ind)) pars).
Proof.
  intros Σ ind pars e.
  unfold inductive_isprop_and_pars in *;cbn in *.
  rewrite !lookup_env_trans_env, lookup_env_dearg_env in *;cbn in *.
  destruct lookup_env; cbn in *;try congruence.
  destruct g; cbn in *; try congruence; auto.
  rewrite !nth_error_map in *.
  unfold dearg_mib.
  destruct get_mib_masks;cbn in *;try congruence;auto.
  cbn in *.
  rewrite nth_error_mapi.
  now destruct nth_error;cbn in *;try congruence;auto.
Qed.

(* NOTE: there is a similar lemma in MetaRocq, but it's missing
   the fact about arguments and the arity. *)
Lemma eval_mkApps_Construct_inv' {fl : WcbvFlags} Σ kn c args e :
  with_constructor_as_block = false ->
  eval Σ (mkApps (tConstruct kn c []) args) e ->
  ∑ args' mdecl idecl cdecl, [× EGlobalEnv.lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl), (#|args| <= cstr_arity mdecl cdecl), (e = mkApps (tConstruct kn c []) args') & All2 (eval Σ) args args'].
Proof.
  intros hblock.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. congruence.
    simpl in *.
    propify.
    unfold isSome in *.
    destruct (EGlobalEnv.lookup_constructor Σ kn c) as [[[mdecl idecl] cdecl] |] eqn:Hlook;
      intuition.
    repeat eexists;cbn;eauto. lia.
    reflexivity.
  - intros ev. rewrite mkApps_app in ev.
    depelim ev.
    all:try specialize (IHargs _ ev1) as [? [? [? [? [? ?]]]]];
    try solve_discr; try noconf H.
    * exists (x0 ++ [a']), x1, x2, x3.
      split;eauto.
      ** rewrite length_app;cbn.
         assert (H : #|args| = #|x0|) by now eapply All2_length.
         rewrite H in *.
         rewrite e in e1. inversion e1;subst. lia.
      ** now rewrite mkApps_app.
      ** eapply All2_app; eauto.
    * subst f'.
      rewrite isConstructApp_mkApps in *;cbn in i.
      now propify.
    * now cbn in i.
Qed.


Lemma dearg_branch_body_rec_dearg n mask t :
  valid_cases t ->
  (dearg_branch_body_rec n mask (dearg t)).2 = dearg (dearg_branch_body_rec n mask t).2.
Proof.
  revert n t.
  induction mask;cbn;intros;auto.
  destruct a;cbn in *.
  * unfold dearg_branch_body_rec in *.
    unfold subst1.
    change [tBox] with (map dearg [tBox]).
    rewrite <- dearg_subst;cbn;auto.
    apply IHmask. now apply valid_cases_subst.
  * now apply IHmask.
Qed.

Lemma valid_dearg_mask_branch_last_true :
  forall m t0 i, valid_dearg_mask_branch i (m ++ [true]) t0 = true ->
                 is_dead (#|m| + i) t0 /\ valid_dearg_mask_branch i m t0.
Proof.
  intros m. induction m;intros t2 i HH;cbn in *;propify;try easy.
  replace (S (#|m| + i)) with (#|m| + S i) by lia.
  destruct HH as [dead_t valid_t].
  destruct a;cbn in *;now specialize (IHm _ _ valid_t) as [??].
Qed.

Lemma valid_dearg_mask_branch_last_false :
  forall m t0 i, valid_dearg_mask_branch i (m ++ [false]) t0 = true ->
                 valid_dearg_mask_branch i m t0.
Proof.
  intros m. induction m;intros t2 i HH;cbn in *;propify;easy.
Qed.

Lemma dearg_branch_body_rec_all_zeros n t i :
  dearg_branch_body_rec i (repeat false n) t = (i + n,t).
Proof.
  revert i.
  induction n;intros i;cbn.
  - now rewrite Nat.add_0_r.
  - now replace (i + S n) with (S i + n) by lia.
Qed.

Lemma valid_dearg_mask_branch_all_zeros i n t :
  valid_dearg_mask_branch i (repeat false n) t.
Proof.
  revert i.
  induction n;cbn;intros;auto.
Qed.

Lemma valid_cases_dearg_branch_body_rec m i br0 :
  valid_cases br0 ->
  valid_cases (dearg_branch_body_rec i m br0).2.
Proof.
  revert i br0.
  induction m;cbn;intros i br0 Hvalid;auto.
  destruct a;cbn.
  + apply IHm;auto. now apply valid_cases_subst.
  + easy.
Qed.

Lemma Forall_masked {A} m (l : list A) (P : A -> Prop) :
  Forall P l -> Forall P (masked m l).
Proof.
  revert l.
  induction m;intros l H;cbn;auto.
  destruct l;cbn;auto.
  destruct a; now inversion H;subst.
Qed.

Lemma masked_all_zeros :
  forall {A} n (l : list A), masked (repeat false n) l = l.
Proof.
  intros A k.
  induction k;destruct l;cbn;auto.
  now rewrite IHk.
Qed.

Lemma mask_last : forall {A} msk b (l : list A) (a : A),
    #|msk| = #|l| ->
    masked (msk ++ [b]) (l ++ [a]) = masked msk l ++ if b then [] else [a].
Proof.
  induction msk;intros ??? H;cbn in *.
  - now destruct l;cbn;try congruence.
  - destruct l;cbn in *;try congruence.
    destruct a;cbn in *;auto.
    now f_equal.
Qed.

Lemma mask_rev : forall {A} msk (l0 : list A),
    #|msk| = #|l0| ->
    List.rev (masked msk l0) = masked (List.rev msk) (List.rev l0).
Proof.
  intros A msk. induction msk;intros l0 Hl0;cbn;auto.
  destruct l0;cbn.
  * now rewrite masked_nil.
  * cbn in *. rewrite mask_last by now repeat rewrite List.length_rev.
    destruct a;cbn. now rewrite app_nil_r.
    now f_equal.
Qed.

Lemma dearg_branch_body_rec_substl_correct : forall mm args0 t ctx0,
    forallb (closedn 0) args0 ->
    #|mm| <= #|args0| ->
    #|args0| = #|ctx0| ->
    valid_dearg_mask_branch 0 (complete_ctx_mask mm ctx0) t ->
    (substl (List.rev (masked mm args0))
            (dearg_branch_body_rec 0 (complete_ctx_mask mm ctx0) t).2)
    = substl (List.rev args0) t.
Proof.
  intros mm args0 t ctx0 Hc Hlen Hctx Hv.
  generalize dependent args0.
  generalize dependent t.
  revert ctx0.
  induction mm;simpl;intros ctx0 t Hv args0 Hc Hlen Hctx.
  - unfold complete_ctx_mask;cbn.
   rewrite app_nil_r. replace (#|ctx0| - 0) with #|ctx0| by lia.
   now rewrite dearg_branch_body_rec_all_zeros;cbn.
  - destruct args0.
   -- inversion Hlen.
   -- destruct a;simpl in *.
   * unfold complete_ctx_mask in Hv;cbn in Hv.
     rewrite app_assoc in Hv.
     apply valid_dearg_mask_branch_last_true in Hv as [??].
     destruct ctx0;simpl in *;try congruence.
     inversion Hctx as [Hctx0];clear Hctx.
     assert (Hmm : #|mm| <= #|args0|) by lia.
     clear Hlen.
     unfold substl,dearg_branch_body_rec.
     cbn.
     rewrite app_assoc.
     rewrite fold_left_app;cbn.
     change (repeat _ (#|?y| - _) ++ List.rev ?x) with (complete_ctx_mask x y) in *.
     destruct (fold_left _ _ (0,t)) as [n1 t1] eqn:Hfl;cbn.
     remember (complete_ctx_mask mm _) as ctx_mask.
     change (fold_left _ ?x (0,t)) with (dearg_branch_body_rec 0 x t) in *.
     rewrite fold_left_app;cbn.
     replace t1 with (dearg_branch_body_rec 0 ctx_mask t).2 by now rewrite Hfl.
     assert (Hn0 : n1 = count_zeros ctx_mask).
     { change n1 with (n1, t1).1. rewrite <- Hfl.
       replace (count_zeros _) with (count_zeros ctx_mask + 0) by lia.
       apply dearg_branch_body_rec_count_zeros. }
     replace n1 with (0 + n1 + 0) by lia.
     rewrite Hn0.
     unfold subst1.
     rewrite <- dearg_branch_body_rec_subst.
     propify.
     destruct Hc.
     unfold substl in IHmm.
     assert (Hctx_mask : #|ctx_mask| = #|ctx0|) by now subst;apply complete_ctx_mask_length.
     subst.
     rewrite Hctx_mask in *.
     rewrite IHmm; try easy.
     cbn.
     change (fold_left _ _ t) with (substl (List.rev args0) t).
     repeat rewrite EOptimizePropDiscr.substl_subst by (rewrite forallb_rev;assumption).
     rewrite <- subst_csubst_comm by (auto;rewrite forallb_rev;assumption).
     repeat rewrite List.length_rev in *.

     rewrite <- Hctx0 in *.
     f_equal.
     rewrite closed_subst by assumption.
     (** NOTE: here we use the fact that the the variable doesn't occur, that is [is_dead] *)
     now apply no_use_subst.
     apply valid_dearg_branch_subst. lia.
     easy.
   * unfold complete_ctx_mask in Hv;cbn in Hv.
     rewrite app_assoc in Hv.
     apply valid_dearg_mask_branch_last_false in Hv.
     destruct ctx0;simpl in *;try congruence.
     assert (Hmm : #|mm| <= #|args0|) by lia.
     clear Hlen.
     unfold complete_ctx_mask;cbn.
     unfold substl,dearg_branch_body_rec.
     rewrite app_assoc.
     remember (repeat _ _ ++ _) as ctx_mask.
     repeat rewrite fold_left_app;simpl.
     f_equal.
     destruct (fold_left _ _ (0,t)) as [n1 t1] eqn:Hfl;cbn.
     replace t1 with (dearg_branch_body_rec 0 ctx_mask t).2 by (unfold dearg_branch_body_rec;now rewrite Hfl).
     assert (Hn0 : n1 = count_zeros ctx_mask).
     { change n1 with (n1, t1).1. rewrite <- Hfl.
       replace (count_zeros _) with (count_zeros ctx_mask + 0) by lia.
       apply dearg_branch_body_rec_count_zeros. }
     unfold substl in IHmm.
     propify.
     subst.
     now apply IHmm.
Qed.

Lemma masked_weakening : forall {A} msk (l : list A) n,
    masked msk l = masked (msk ++ repeat false n) l.
Proof.
  intros ? msk.
  induction msk;cbn;intros.
  - now rewrite masked_all_zeros.
  - destruct l;cbn;auto.
    destruct a;cbn;auto.
    now f_equal.
Qed.

Lemma Forall_closed_repeat_tBox n k : Forall (closedn k) (repeat tBox n).
Proof.
  induction n;cbn;auto.
Qed.

Lemma dearg_repeat_tBox : forall n, map dearg (repeat tBox n) = repeat tBox n.
Proof.
  intros n1. induction n1;cbn;auto. now f_equal.
Qed.

Hint Resolve
     Forall_repeat
     Forall_forallb
     Forall_rev
     Forall_masked
     Forall_skipn
     valid_cases_dearg_branch_body_rec
     valid_dearg_mask_branch_dearg
     Forall_closed_repeat_tBox : dearg.

Ltac simpl_length :=
  repeat
    match goal with
    | |- context [ List.length (_ ++ _) ] => rewrite length_app
    | |- context [ List.length (repeat _ _) ] => rewrite repeat_length
    | |- context [ List.length (skipn _ _) ] => rewrite length_skipn
    | |- context [ List.length (rev _ _) ] => rewrite length_rev
    | |- context [ List.length (List.rev _ _) ] => rewrite List.length_rev
    | |- context [ List.length (map _ _) ] => rewrite length_map
    end.

Lemma dearg_correct {wfl : WcbvFlags} Σ t v :
  with_constructor_as_block = false ->

  env_closed (trans_env Σ) ->
  closed t ->

  valid_masks_env Σ ->
  valid_cases t ->

  is_expanded_env Σ ->
  is_expanded t ->

  trans_env Σ e⊢ t ⇓ v ->
  trans_env (dearg_env Σ) e⊢ dearg t ⇓ dearg v.
Proof.
  intros block clos_env clos_t valid_env valid_t exp_env exp_t.
  enough (forall n (ev : trans_env Σ e⊢ t ⇓ v),
             deriv_length ev <= n ->
             trans_env (dearg_env Σ) e⊢ dearg t ⇓ dearg v).
  { intros ev.
    eapply (H _ ev).
    apply Nat.le_refl. }
  induction n as [|n IH] in t, v, clos_t, valid_t, exp_t |- *; intros ev deriv_len.
  { now pose proof (deriv_length_min ev). }
  destruct (dearg_elim t).
  - apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    cbn in *; propify.
    rewrite dearg_single_masked by (now rewrite length_map).
    specialize (eval_mkApps_deriv ev) as (? & ev_const & argsv & ev_args & deriv).
    depelim ev_const; cbn in *; [|easy].
    eapply declared_constant_dearg in isdecl as isdecl_dearg.
    destruct isdecl_dearg as (cst_dearg & decl_dearg & body_dearg).
    rewrite e in body_dearg; cbn in *.

    enough (trans_env (dearg_env Σ)
            e⊢ mkApps (dearg (dearg_lambdas (get_const_mask kn) body))
                      (masked (get_const_mask kn) (map dearg args)) ⇓ dearg v) as ev'.
    { eapply eval_mkApps_head in ev' as ev_hd.
      destruct ev_hd as (hdv & ev_hd).
      eapply eval_mkApps_heads.
      3: eassumption.
      1: eassumption.
      econstructor; eassumption. }

    rewrite dearg_dearg_lambdas by
        eauto using valid_dearg_mask_constant, valid_cases_constant.
    assert (∑ ev' : trans_env Σ e⊢ mkApps body args ⇓ v,
               deriv_length ev' < deriv_length ev) as (ev_body & deriv_body).
    { unshelve epose proof (eval_mkApps_heads_deriv _ ev_const ev) as (ev' & ?).
      - now econstructor.
      - exists ev'.
        now cbn in *. }

    apply dearg_lambdas_correct.
    + now apply env_closed_dearg.
    + apply closedn_dearg_aux; [|easy].
      now eapply closed_constant.
    + apply Forall_map.
      apply closed_mkApps_inv in clos_t as (? & clos_args).
      eapply Forall_impl; [exact clos_args|].
      intros.
      now apply closedn_dearg_aux.
    + apply valid_dearg_mask_dearg_aux.
      now eapply valid_dearg_mask_constant.
    + now rewrite length_map.
    + unshelve eapply eval_mkApps_dearg.
      6: exact IH.
      all: auto.
      * now eapply closed_constant.
      * now eapply valid_cases_constant.
      * now eapply is_expanded_constant.
      * now apply closed_mkApps_inv in clos_t.
      * now apply valid_cases_mkApps_inv in valid_t.
      * lia.

  - specialize (eval_mkApps_deriv ev) as (? & ev_constr & argsv & ev_args & deriv).
    apply valid_cases_mkApps_inv in valid_t as (? & valid_apps).
    cbn in *.
    (* NOTE: we use validity of cases to ensure that the block constructor argument is an empty list *)
    destruct args0;try congruence.
    eapply eval_mkApps_Construct_inv' in ev as ev_c;eauto.
    destruct ev_c as (argsv' & mdecl & idecl & cdecl & [ctor_look Heq ev_args' a]).
    assert (argsv' = argsv) by now eapply eval_deterministic_all.
    subst.
    rewrite dearg_mkApps.
    cbn.
    apply All2_length in ev_args as ?.
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    cbn -[EGlobalEnv.lookup_constructor] in *; propify.
    rewrite !dearg_single_masked by (now rewrite length_map).
    assert (ev_args_dearg : All2 (eval (trans_env (dearg_env Σ))) (map dearg args) (map dearg argsv)).
    { assert (all_smaller : sum_deriv_lengths ev_args <= n).
      { pose proof (deriv_length_min ev_constr).
        lia. }
      apply closed_mkApps_inv in clos_t as (_ & clos_apps).
      clear -clos_apps valid_apps exp_args IH ev_args all_smaller.
      induction ev_args; cbn in *.
      - now constructor.
      - unshelve epose proof (IHev_args _ _ _ _) as ev_suf; auto.
        + now depelim clos_apps.
        + now depelim valid_apps.
        + now depelim exp_args.
        + lia.
        + unshelve epose proof (IH _ _ _ _ _ r _) as ev_dearg; auto.
          * now depelim clos_apps.
          * now depelim valid_apps.
          * now depelim exp_args.
          * lia. }
    apply lookup_ctor_trans_env in ctor_look as e0.
    destruct e0 as (mib & oib & ctor & Hc & Hmib & Hoib & Hctor).
    assert (decl_ind :declared_inductive (trans_env Σ) ind (trans_mib mib) (trans_oib oib)).
    { unfold declared_inductive,declared_minductive.
      split. subst.
      eapply lookup_ctor_lookup_env;eauto.
      eapply lookup_ctor_lookup_env;eauto. subst; apply ctor_look. }
    specialize (valid_ind_mask_inductive _ _ _ _ valid_env decl_ind) as [mask [Hmask [Hparams Hprojs]]].
    set (trans_mib (dearg_mib ind_masks (inductive_mind ind) mib)) as mib_dearg.
    set (trans_oib (dearg_oib mask (inductive_ind ind) oib)) as oib_dearg.
    set (dearg_ctor (param_mask mask) (get_branch_mask mask (inductive_ind ind) c) ctor) as ctor_dearg.

    eapply (eval_mkApps_tConstruct _ _ _ _ _ mib_dearg oib_dearg (mkConstructor ctor_dearg.1.1 ctor_dearg.2));eauto. now apply All2_masked.
    * apply lookup_ctor_trans_env_inv.
      now apply lookup_ctor_dearg.
    * propify.
      unfold trans_mib,dearg_mib, cstr_arity in *;cbn.
      subst. cbn in *.
      rewrite <- Hparams in *.
      rewrite masked_count_zeros in * by (rewrite length_map;lia).
      rewrite length_map.
      specialize (count_zeros_le (param_mask mask)) as HH.
      unfold get_ctor_mask, dearg_ctor in *. rewrite Hmask in *.
      destruct ctor as [p0]. destruct p0;cbn in *.
      rewrite count_zeros_distr_app.
      rewrite length_app in *.
      remember (get_branch_mask _ _ _) as bm.
      assert (count_zeros bm <= #|bm|) by apply count_zeros_le.
      assert (count_zeros bm + count_ones bm = #|bm| ) by apply count_ones_zeros.
      lia.
  - facts.
    apply closed_mkApps_inv in clos_t as (clos_t & clos_args).
    apply valid_cases_mkApps_inv in valid_t as (valid_t & valid_args).
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    unshelve eapply eval_mkApps_dearg_reduce.
    6: exact IH.
    all: auto.
    intros ->.
    cbn in *; propify; refold'.
    destruct clos_t as (clos_discr & clos_brs).
    destruct valid_t as ((valid_discr & valid_brs) & valid_brs_masks).
    destruct exp_hd as (exp_discr & exp_brs).
    unfold dearg_case.
    (* We need induction as casing on a cofix involves casing on whatever it evaluates to *)
    depind ev; cbn in *;try congruence.
    + (* Normal pattern match *)
      clear IHev1 IHev2.
      facts.
      clear clos_args valid_args exp_args.
      invert_facts.
      cbn in *; propify.
      pose proof e1 as ee.
      unfold constructor_isprop_pars_decl in e1;cbn in e1.
      rewrite lookup_env_trans_env in e1.
      destruct (lookup_env _ _) as [g|]eqn:Hg;cbn in *;try congruence.
      destruct g as [ | mib |] eqn:Hmib;cbn in *;try congruence.
      rewrite nth_error_map in e1.
      destruct nth_error as [oib|] eqn:Hoib;cbn in *;try congruence.
      cbn in *.
      destruct (nth_error _ c);cbn in *;try congruence.
      inversion e1;subst.
      assert (decl_ind :declared_inductive (trans_env Σ) ind (trans_mib mib) (trans_oib oib)).
        { unfold declared_inductive,declared_minductive.
          split. rewrite lookup_env_trans_env. now rewrite Hg.
          unfold trans_mib;cbn. rewrite nth_error_map. now rewrite Hoib. }
      specialize (valid_ind_mask_inductive _ _ _ _ valid_env decl_ind) as [mask [Hmask [Hparams Hprojs]]].

      set (dearg_case_branch mask ind c (on_snd dearg br)) as br_dearg.
      eapply (eval_iota _ _ _ _ _ c (masked (get_ctor_mask ind c) (map dearg args)) _ br_dearg);eauto.
      * unshelve epose proof (IH _ _ _ _ _ ev1 _); auto.
        1: lia.
        rewrite dearg_mkApps in *.
        cbn in *.
        now rewrite dearg_single_masked in * by (now rewrite length_map).
      * apply constructor_isprop_pars_decl_trans_env_dearg_env; eauto.
      * unfold dearg_case_branches,valid_case_masks in *.
        rewrite Hmask in *.
        unfold dearg_case_branch in *.
        rewrite nth_error_mapi, nth_error_map, e2;cbn. eauto.
      * propify.
        cbn in *.
        unfold trans_ctors in *.
        unfold dearged_npars.
        unfold get_ctor_mask.
        unfold valid_case_masks in *.
        rewrite Hmask in *.
        propify.
        destruct valid_brs_masks as [? Hall].
        apply alli_Alli in Hall.
        eapply (Alli_nth_error _ _ _ _ _ _ Hall) in e2;eauto.
        destruct br as [ctx br];cbn in *.
        propify.
        destruct e2 as [bm_ctx valid_bm].
        rewrite length_skipn in e4.
        rewrite masked_count_zeros by (simpl_length;lia).
        rewrite length_map. rewrite e3.
        unfold get_ctor_mask.
        rewrite count_zeros_distr_app. rewrite length_app.
        cbn.
        remember (get_branch_mask _ _ _) as bm.
        assert (count_zeros bm <= #|bm|) by apply count_zeros_le.
        assert (count_zeros bm + count_ones bm = #|bm| ) by apply count_ones_zeros.
        lia.
      * rewrite length_skipn.
        unfold valid_case_masks in *.
        rewrite Hmask in *.
        cbn in *.
        propify.
        destruct valid_brs_masks as [? Hall].
        apply alli_Alli in Hall.
        eapply (Alli_nth_error _ _ _ _ _ _ Hall) in e2;eauto.
        destruct br as [ctx br];cbn in *.
        unfold is_true in e2.
        rewrite andb_true_iff in e2.
        destruct e2 as [bm_ctx valid_bm].
        unfold dearg_case_branch in *;cbn in *.
        subst br_dearg.
        rewrite bm_ctx. cbn.
        unfold get_ctor_mask, dearg_ctor in *. rewrite Hmask in *.
        rewrite length_app in *.
        rewrite masked_count_zeros by (simpl_length;lia).
        remember (get_branch_mask _ _ _) as bm.
        rewrite count_zeros_distr_app.
        propify.
        remember (complete_ctx_mask _ _) as mm.
        assert (Hmm : #|mm| = #|ctx|) by now subst;propify;now apply complete_ctx_mask_length.
        rewrite masked_count_zeros by lia.
        subst mm. rewrite Hmm.
        unfold complete_ctx_mask.
        rewrite count_zeros_distr_app.
        rewrite <- count_zeros_rev.
        rewrite length_app, length_map.
        rewrite count_zeros_repeat.
        rewrite length_skipn in e4. lia.
        * cbn in *.
          unfold get_ctor_mask.
          rewrite Hmask.
          cbn.
          unfold iota_red in *.
          replace
          (skipn (count_zeros (param_mask mask))
                 (masked (param_mask mask ++ get_branch_mask mask (inductive_ind ind) c) (map dearg args)))
          with
            (masked (get_branch_mask mask (inductive_ind ind) c)
                             (skipn #|param_mask mask| (map dearg args))); cycle 1.
        { clear.
          generalize (get_branch_mask mask (inductive_ind ind) c) as m2.
          generalize (map dearg args) as ts.
          generalize (param_mask mask) as m1.
          intros m1 ts m2.
          induction m1 in ts, m2 |- *; intros.
          - cbn.
            now rewrite !skipn_0.
          - destruct a; cbn in *.
            + destruct ts; [now rewrite !skipn_nil, !masked_nil|].
              rewrite skipn_S.
              now apply IHm1.
            + destruct ts; [now rewrite !skipn_nil, !masked_nil|].
              rewrite !skipn_S.
              now apply IHm1. }
        rewrite skipn_map, masked_map, <- map_rev.
        subst br_dearg.
        unfold dearg_case_branch;cbn.
        unfold valid_case_masks in *.
        rewrite Hmask in*.
        propify.
        destruct valid_brs_masks as [? Hall].
        apply alli_Alli in Hall.
        eapply (Alli_nth_error _ _ _ _ _ _ Hall) in e2 as HH;eauto.
        destruct br as [ctx br];cbn in *.
        unfold is_true in HH.
        rewrite andb_true_iff in HH.
        destruct HH as [bm_ctx valid_bm].
        rewrite bm_ctx;cbn.
        change (dearg_aux []) with dearg.
        specialize (forallb_nth_error _ _ c valid_brs) as valid_br.
        rewrite e2 in valid_br;cbn in *.
        rewrite dearg_branch_body_rec_dearg by assumption.
        invert_facts.
        remember (ind_npars mib) as pars.
        assert (closed_args : forallb (closedn 0) args) by now apply forallb_Forall.
        assert (closed_args_skip : forallb (closedn 0) (skipn pars args))
          by now apply forallb_skipn.
        rewrite <- dearg_substl by eauto with dearg.
        rewrite Hparams.
        rewrite dearg_branch_body_rec_substl_correct;try easy.
        eapply IH with (ev := ev2);try lia;eauto with dearg.
          ** apply closed_substl.
             now rewrite forallb_rev.
             eapply nth_error_forallb in clos_brs;eauto;cbn in *.
             now rewrite List.length_rev,e4.
          ** eapply nth_error_forallb in valid_brs;eauto;cbn in *.
             apply valid_cases_substl; auto;now apply Forall_rev, Forall_skipn.
          ** eapply nth_error_forallb in exp_brs;eauto;cbn in *.
             apply is_expanded_substl;auto. now apply Forall_rev, Forall_skipn.
    + clear IHev1 IHev2.
      (* Singleton pattern match *)
      subst brs; cbn in *; propify.
      set (mm := match get_mib_masks (inductive_mind ind) with
                 | Some mm => mm
                 | None => Build_mib_masks [] []
                 end).
      set (ctx_mask := complete_ctx_mask (get_branch_mask mm (inductive_ind ind) 0) n).
      eapply (eval_iota_sing _ _ _ _ _
                             (if #|get_branch_mask mm (inductive_ind ind) 0| <=? #|n|
                              then masked ctx_mask n
                             else n)
                            (dearg_case_branch mm ind 0 (n,dearg f4)).2).
      * eauto.
      * unshelve eapply (IH _ tBox); eauto.
        lia.
      * apply inductive_isprop_and_pars_trans_env_dearg_env; eauto.
      * destruct (get_mib_masks _); unfold on_snd;cbn in *.
        ** f_equal.
           unfold dearg_case_branch,dearg_branch_body;cbn.
           destruct (_ <=? _);cbn; reflexivity.
        ** subst ctx_mask;cbn in *;f_equal.
           unfold complete_ctx_mask, dearg_case_branch, leb;cbn.
           rewrite app_nil_r. simpl.
           rewrite masked_all_zeros.
           change (fold_left _ ?m (?i,?x)) with (dearg_branch_body_rec i m x).
          unfold dearg_case_branch; cbn. unfold Nat.leb; cbn. f_equal.
          unfold complete_ctx_mask. cbn.
          now rewrite dearg_branch_body_rec_all_zeros.
      * unfold valid_case_masks in *. cbn in valid_brs_masks.
        remember (if #|get_branch_mask mm (inductive_ind ind) 0| <=? #|n| then masked ctx_mask n else n) as masked_n.
        replace (repeat tBox _) with (masked ctx_mask (repeat tBox #|n|)); cycle 1.
        { unfold valid_case_masks in valid_brs_masks.
          destruct (get_mib_masks _).
          - cbn in *; propify. subst mm.
            destruct valid_brs_masks as (_ & (bound & _) & _).
            assert (Hlen : #|ctx_mask| = #|n|) by (subst; now apply complete_ctx_mask_length).
            destruct (_ <=? _) eqn:Hbm;cbn;propify;try easy.
            * rewrite Heqmasked_n.
              rewrite masked_count_zeros by lia.
              replace (count_zeros ctx_mask + _) with (count_zeros ctx_mask ) by lia.
              rewrite <- Hlen.
              clear Heqmasked_n Hlen.
              induction ctx_mask; cbn in *;intros;auto.
              destruct a;cbn;auto.
              f_equal;auto.
          - subst mm ctx_mask;cbn in *.
            unfold complete_ctx_mask in *;cbn in *.
            rewrite app_nil_r in *.
            rewrite Heqmasked_n.
            now repeat rewrite masked_all_zeros.
        }
        unfold dearg_case_branch.
        destruct (get_mib_masks _).
        ** cbn in *.
           destruct (_ <=? _) eqn:Hbm;cbn;propify;try easy.
           assert (Hlen : #|ctx_mask| = #|n|) by (subst; now apply complete_ctx_mask_length).
           unfold complete_ctx_mask in ctx_mask.
           subst ctx_mask.
           rewrite <- rev_repeat, <- rev_app_distr.
           rewrite <- (rev_repeat _ tBox).
           subst mm.
           rewrite <- mask_rev by (simpl_length; lia).
           rewrite <- masked_weakening.
           rewrite dearg_branch_body_rec_substl_correct;cbn in *;
             try (simpl_length; lia);intuition;eauto with dearg.
           rewrite rev_repeat.
           rewrite <- dearg_repeat_tBox.
           rewrite <- dearg_substl by eauto with dearg.
           eapply IH with (ev := ev2).
           *** apply closed_substl;simpl_length;eauto with dearg.
           *** apply valid_cases_substl;eauto with dearg.
           *** apply is_expanded_substl;eauto with dearg.
           *** lia.
        ** subst mm. cbn -[dearg_branch_body_rec] in *.
           unfold leb, complete_ctx_mask; cbn.
           unfold leb, complete_ctx_mask; cbn.
           rewrite app_nil_r.
           rewrite dearg_branch_body_rec_all_zeros;cbn.
           subst ctx_mask. unfold complete_ctx_mask.
           rewrite <- rev_repeat, <- rev_app_distr.
           rewrite <- (rev_repeat _ tBox).
           rewrite <- mask_rev by (cbn;simpl_length; lia).
           rewrite <- masked_weakening;cbn -[substl].
           rewrite <- dearg_repeat_tBox.
           rewrite <- map_rev.
           rewrite <- dearg_substl;intuition; eauto with dearg.
           rewrite rev_repeat.
           apply IH with (ev := ev2).
           *** apply closed_substl;simpl_length;eauto with dearg.
           *** apply valid_cases_substl;eauto with dearg.
           *** apply is_expanded_substl;eauto with dearg.
           *** lia.
    + (* Unfold cofix *)
      clear clos_args valid_args exp_args.
      facts.
      invert_facts.
      cbn in *; propify.
      eapply (eval_cofix_case _ _ _ _ (map dearg args) _ narg (dearg fn)); [|eapply dearg_cunfold_cofix;eauto|].
      * assert (closed fn) by now eapply closed_cunfold_cofix.
        assert (valid_cases fn) by now eapply valid_cases_cunfold_cofix.
        assert (is_expanded fn).
        { eapply is_expanded_cunfold_cofix; [eassumption|].
          now apply forallb_Forall. }
        change (tCoFix (map (map_def dearg) mfix) idx) with
          (dearg (tCoFix mfix idx)).
        rewrite <- dearg_expanded, <- dearg_mkApps by auto.
        eapply IH with (ev := ev1);eauto with dearg;lia.
      * clear IHev1 IHev2.
        assert (is_expanded fn).
        { eapply is_expanded_cunfold_cofix; [eassumption|].
          now apply forallb_Forall. }
        set (dearg (tCase (ind, npars) (mkApps fn args) brs)) as b.
        cbn in b. unfold dearg_case in b.
        rewrite <- dearg_expanded, <- dearg_mkApps by eauto.
        change (tCase _ (dearg (mkApps fn args)) _)
          with (dearg (tCase (ind, npars) (mkApps fn args) brs)).
        assert (closed (mkApps fn args)) by
          (apply closed_mkApps;[eapply closed_cunfold_cofix;eauto|eauto]).
        assert (valid_cases (mkApps fn args)) by
          now (eapply valid_cases_mkApps;[eapply valid_cases_cunfold_cofix;eauto|eauto]).
        assert (is_expanded (mkApps fn args)) by
        (apply is_expanded_aux_mkApps;cbn;eauto with dearg;
         eapply is_expanded_aux_upwards;eauto;lia).
        eapply IH with (ev := ev2);cbn;propify;intuition;eauto with dearg.
  - facts.
    apply closed_mkApps_inv in clos_t as (clos_hd & clos_args).
    apply valid_cases_mkApps_inv in valid_t as (valid_hd & valid_args).
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    cbn in * |-.
    unshelve eapply eval_mkApps_dearg_reduce.
    6: exact IH.
    all: auto.
    intros ->.
    cbn in *; refold'.
    clear clos_args valid_args exp_args.
    depind ev; cbn in *.
    + (* Cofix projection *)
      propify.
      destruct valid_hd.
      facts.
      invert_facts.
      unshelve eapply (eval_cofix_proj _ _ ((map (map_def (dearg_aux [])) mfix)) idx (map dearg args) _ narg (dearg fn) _ _).
      * change (tCoFix (map _ _) _) with (dearg (tCoFix mfix idx)).
        rewrite <- dearg_expanded, <- dearg_mkApps by easy.
        eapply IH with (ev := ev1);now eauto with dearg.
      * now eapply dearg_cunfold_cofix.
      * assert (is_expanded fn).
        { eapply is_expanded_cunfold_cofix; [eassumption|].
          now apply forallb_Forall. }
        rewrite <- dearg_expanded, <- dearg_mkApps by easy.
        change (tProj _ _) with (dearg (tProj {| proj_ind := ind; proj_npars := c; proj_arg := npars |} (mkApps fn args))).
        assert (closed (mkApps fn args)) by
          (apply closed_mkApps;[eapply closed_cunfold_cofix;eauto|eauto]).
        assert (valid_cases (mkApps fn args)) by
          now (eapply valid_cases_mkApps;[eapply valid_cases_cunfold_cofix;eauto|eauto]).
        assert (is_expanded (mkApps fn args)) by
        (apply is_expanded_aux_mkApps;cbn;eauto with dearg;
         eapply is_expanded_aux_upwards;eauto; lia).

        apply IH with (ev := ev2);cbn;propify;now eauto with dearg.
    + (* Regular projection *)
      clear IHev1 IHev2.
      propify.
      destruct valid_hd as (valid_hd & valid_p).
      facts.
      invert_facts.
      cbn in *; propify.
      unfold dearg_proj.
      eapply (eval_proj _ _ _ _ (masked (get_ctor_mask ind 0) (map dearg args)) (dearg a));auto.
      * unshelve epose proof (IH _ _ _ _ _ ev1 _); eauto.
        1: lia.
        rewrite dearg_mkApps in *.
        cbn in *.
        now rewrite dearg_single_masked in * by (now rewrite length_map).
      * apply constructor_isprop_pars_decl_trans_env_dearg_env;eauto.
      * cbn in *.
        propify.
        unfold dearged_ctor_arity.
        unfold constructor_isprop_pars_decl in e1;cbn in e1.
        rewrite lookup_env_trans_env in e1.
        destruct (lookup_env _ _) as [g|]eqn:Hg;cbn in *;try congruence.
        destruct g as [ | mib |] eqn:Hmib;cbn in *;try congruence.
        rewrite nth_error_map in e1.
        destruct nth_error as [oib|] eqn:Hoib;cbn in *;try congruence.
        assert (decl_ind :declared_inductive (trans_env Σ) ind (trans_mib mib) (trans_oib oib)).
        { unfold declared_inductive,declared_minductive.
          split. rewrite lookup_env_trans_env. now rewrite Hg.
          unfold trans_mib;cbn. rewrite nth_error_map. now rewrite Hoib. }
        specialize (valid_ind_mask_inductive _ _ _ _ valid_env decl_ind) as [mask [Hmask [Hparams Hprojs]]].
        unfold get_ctor_mask,valid_proj in *.
        rewrite Hmask in *; cbn in *;propify.
        rewrite masked_count_zeros by (rewrite length_map;lia).
        rewrite length_map. rewrite e2.
        rewrite count_zeros_distr_app. rewrite length_app.
        cbn.
        remember (get_branch_mask _ _ _) as bm.
        assert (count_zeros bm <= #|bm|) by apply count_zeros_le.
        assert (count_zeros bm + count_ones bm = #|bm| ) by apply count_ones_zeros.
        rewrite length_app in *.
        cbn in *.
        lia.
      * unfold constructor_isprop_pars_decl in e1;cbn in e1.
        rewrite lookup_env_trans_env in e1.
        destruct (lookup_env _ _) as [g|]eqn:Hg;cbn in *;try congruence.
        destruct g as [ | mib |] eqn:Hmib;cbn in *;try congruence.
        rewrite nth_error_map in e1.
        destruct nth_error as [oib|] eqn:Hoib;cbn in *;try congruence.
        assert (decl_ind :declared_inductive (trans_env Σ) ind (trans_mib mib) (trans_oib oib)).
        { unfold declared_inductive,declared_minductive.
          split. rewrite lookup_env_trans_env. now rewrite Hg.
          unfold trans_mib;cbn. rewrite nth_error_map. now rewrite Hoib. }
        specialize (valid_ind_mask_inductive _ _ _ _ valid_env decl_ind) as [mask [Hmask [Hparams Hprojs]]].
        unfold get_ctor_mask, valid_proj in *.
        rewrite Hmask in *;cbn in *;propify.
        destruct (nth_error args _) eqn:nth; [|now depelim ev2].
        rewrite length_app in *.
        destruct valid_p as (<- & arg_unused).
        rewrite masked_map, nth_error_map, masked_app.
        rewrite nth_error_app2; cycle 1.
        { rewrite length_firstn.
          lia. }
        rewrite length_firstn.
        rewrite Nat.min_l; cycle 1.
        { rewrite masked_length by easy.
          lia. }
        replace (count_zeros (param_mask mask) + (npars - count_ones (firstn npars (get_branch_mask mask (inductive_ind ind) 0))) -
            count_zeros (param_mask mask)) with (npars - count_ones (firstn npars (get_branch_mask mask (inductive_ind ind) 0)))
          by lia.
        rewrite nth_error_masked by easy.
        rewrite nth_error_skipn, nth.
        cbn. congruence.
      * unshelve eapply (IH _ _ _ _ _ ev2 _).
        -- now eapply nth_error_forall in H5; [|eassumption].
        -- now eapply nth_error_forall in H6; [|eassumption].
        -- now eapply nth_error_forall in H7; [|eassumption].
        -- lia.
    + congruence.
    + (* Project out of box *)
      clear IHev.
      propify.
      destruct valid_hd as (valid_hd & valid_p).
      unfold dearg_proj.
      apply eval_proj_prop.
      * eauto.
      * unshelve eapply (IH _ _ _ _ _ ev _); auto.
        lia.
      * eapply inductive_isprop_and_pars_trans_env_dearg_env; eauto.
    + congruence.
  - facts.
    apply closed_mkApps_inv in clos_t as (clos_t & clos_args).
    apply valid_cases_mkApps_inv in valid_t as (valid_t & valid_args).
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_t & exp_args).
    unshelve eapply eval_mkApps_dearg_reduce.
    6: exact IH.
    all: auto.
    1: now destruct hd.
    intros ->.
    cbn in *.
    depelim ev; cbn in *; propify; try destruct y; refold'.
    + intuition auto.
      facts.
      econstructor.
      * now unshelve eapply (IH _ _ _ _ _ ev1 _).
      * revert ev2 deriv_len.
        rewrite !closed_subst by (auto; eapply eval_closed;eauto).
        intros.
        rewrite closed_subst.
        change (subst0 ?a ?t) with (subst0 (map dearg [b0']) t).
        rewrite <- dearg_subst by auto.
        unshelve eapply (IH _ _ _ _ _ ev2 _).
        -- apply closedn_subst0;cbn;eauto.
        -- now apply valid_cases_subst.
        -- now apply is_expanded_aux_subst.
        -- lia.
        -- eapply closedn_dearg_aux;eauto.
    + depelim e; repeat constructor.
      cbn in deriv_len. eapply All2_All2_Set, All2_map.
      solve_all. subst a' a; cbn in *.
      depelim H0; depelim H1. intuition auto; cbn in *.
      clear -b0 deriv_len IH.
      induction b0 in v', ev, deriv_len |- *; depelim ev; constructor; eauto.
      specialize (IHb0 _ ev). unshelve eapply IH; intuition eauto. cbn. cbn in deriv_len. lia.
      unshelve eapply IHb0; tea. cbn in deriv_len. lia.
      cbn in *; unfold test_array_model in *; subst a a'; cbn in *.
      unshelve eapply IH; tea; rtoProp; intuition eauto. lia.
    + facts. econstructor. specialize (IH _ _ clos_t valid_t exp_t ev1).
      cbn in IH. apply IH. lia.
      now forward (IH v _ H2 H4 H6 ev2).
    + destruct t; cbn in *; try destruct y; try congruence; now constructor.
Qed.
End dearg_correct.

Lemma lookup_env_debox_env_types Σ kn :
  lookup_env (debox_env_types Σ) kn = option_map (debox_type_decl Σ) (lookup_env Σ kn).
Proof.
  unfold debox_env_types, lookup_env.
  generalize Σ at 1 3.
  intros masks.
  induction Σ as [|((kn', has_deps), decl) Σ IH]; [easy|].
  cbn.
  unfold eq_kername.
    unfold eq_kername.
  destruct Kername.reflect_kername as [eq Heq].
  destruct (Heq kn kn'); [easy|].
  apply IH.
Qed.

Lemma constructor_isprop_pars_decl_trans_env_debox_types :
  forall (Σ : global_env) (ind : inductive) (c : nat) r,
    constructor_isprop_pars_decl (trans_env Σ) ind c = Some r ->
    constructor_isprop_pars_decl (trans_env (debox_env_types Σ)) ind c = Some r.
Proof.
  intros Σ ind pars c r.
  unfold constructor_isprop_pars_decl in *;cbn in *.
  rewrite !lookup_env_trans_env, lookup_env_debox_env_types in *.
  destruct lookup_env; cbn in *;try congruence.
  destruct g; cbn in *;try congruence.
  rewrite !nth_error_map in *. destruct nth_error;cbn in *;try congruence.
  unfold trans_ctors in *;cbn in *.
  repeat rewrite nth_error_map in *.
  destruct nth_error;cbn in *;try congruence.
  destruct p as [p0].
  now destruct p0.
Qed.

Lemma inductive_isprop_and_pars_trans_env_debox_types :
      forall (Σ : global_env) (ind : inductive) (r : bool * nat),
        inductive_isprop_and_pars (trans_env Σ) ind = Some r ->
        inductive_isprop_and_pars (trans_env (debox_env_types Σ)) ind = Some r.
Proof.
  intros Σ ind r H.
  unfold inductive_isprop_and_pars in *;cbn in *.
  rewrite !lookup_env_trans_env, lookup_env_debox_env_types in *.
  destruct lookup_env; cbn in *;try congruence.
  destruct g; cbn in *;try congruence.
  rewrite !nth_error_map in *.
  now destruct nth_error;cbn in *;try congruence.
Qed.

Lemma lookup_constructor_debox_types :
      forall (Σ : global_env) (ind : inductive) (c : nat) m o i n l
             (e : lookup_constructor_full Σ ind c = Some (m, o, (i,n,l))),
        lookup_constructor_full (debox_env_types Σ) ind c =
          Some (debox_type_mib Σ m,debox_type_oib Σ o,(i, map (on_snd (fun x : box_type => reindex (ind_type_vars o) (debox_box_type Σ x))) n, l)).
Proof.
  intros Σ ind c m o i n l H.
  unfold lookup_constructor_full in *;cbn in *.
  unfold lookup_constructor_full,lookup_minductive in *.
  rewrite lookup_env_debox_env_types.
  destruct (lookup_env _ _) as [mdecl_e|] eqn:Henv;try congruence;cbn in *.
  destruct mdecl_e as [| mib |]eqn:Hgd;try congruence;cbn in *.
  rewrite nth_error_map.
  destruct (nth_error _ _) as [|]eqn:nth;try congruence;cbn in *.
  rewrite nth_error_map.
  destruct (nth_error _ c);try congruence;cbn.
  destruct p as [p0]. destruct p0;cbn.
  now inversion H;subst.
Qed.

Lemma eval_debox_env_types {wfl : WcbvFlags} Σ t v :
  with_constructor_as_block = false ->
  trans_env Σ e⊢ t ⇓ v ->
  trans_env (debox_env_types Σ) e⊢ t ⇓ v.
Proof.
  intros wcab.
  induction 1; eauto;try congruence.
  - eapply eval_iota; eauto.
    now apply constructor_isprop_pars_decl_trans_env_debox_types.
  - eapply eval_iota_sing; eauto.
    now apply inductive_isprop_and_pars_trans_env_debox_types.
  - eapply eval_delta; eauto.
    unfold declared_constant in *.
    rewrite !lookup_env_trans_env, lookup_env_debox_env_types in *.
    destruct lookup_env; cbn in *; [|congruence].
    destruct g; cbn in *;auto.
    * congruence.
    * destruct o;auto. now destruct p.
  - eapply eval_proj; eauto.
    now apply constructor_isprop_pars_decl_trans_env_debox_types.
  - eapply eval_proj_prop; eauto.
    now apply inductive_isprop_and_pars_trans_env_debox_types.
  - apply lookup_ctor_trans_env in e0 as ee.
    destruct ee as (mib & oib & ctor & Hc & Hmib & Hoib & Hctor).
    subst.
    destruct ctor as [[i n] l0].
    eapply lookup_constructor_debox_types in Hc.
    eapply eval_construct.
    assumption.
    eapply lookup_ctor_trans_env_inv;eauto.
    all : eauto.
  - depelim X; repeat constructor.
    eapply All2_over_undep in a. eapply All2_All2_Set. eapply All2_Set_All2 in ev; solve_all. eauto.
  - eapply eval_atom.
    depelim t;auto.
    destruct args;simpl in *;try congruence.
    propify.
    destruct i.
    destruct (EGlobalEnv.lookup_constructor (trans_env Σ) _ _) as [p | ] eqn:He;simpl in *;try congruence.
    destruct p as [[??]?].
    apply lookup_ctor_trans_env in He as ee.
    destruct ee as (mib & oib & ctor & Hc & Hmib & Hoib & Hctor).
    subst.
    destruct ctor as [[? ?] ?].
    eapply lookup_constructor_debox_types in Hc.
    eapply lookup_ctor_trans_env_inv in Hc;eauto.
    now rewrite Hc.
Qed.

Lemma eval_const_construct_expanded {wfl : WcbvFlags} Σ kn ind c im cm :
  trans_env Σ e⊢ tConst kn ⇓ tConstruct ind c [] ->
  valid_masks_env im cm Σ ->
  is_expanded im cm (tConst kn).
Proof.
  intros ev valid.
  depelim ev.
  eapply valid_dearg_mask_constant in valid; eauto.
  cbn.
  apply valid_dearg_mask_spec in valid as (Γ & inner & <- & <-).
  clear -ev.
  induction #|Γ| as [|Γlen IH] eqn:eq in Γ, inner, ev |- *.
  - now destruct Γ.
  - destruct Γ as [|[na [body|]] Γ]; cbn in *.
    + easy.
    + depelim ev.
      refold.
      rewrite subst_it_mkLambda_or_LetIn in ev2.
      erewrite <- vasses_subst_context.
      eapply IH; [eassumption|].
      now rewrite length_subst_context.
    + depelim ev.
Qed.

Import MRMonadNotation ResultMonad.
From Stdlib Require Import String.
Definition compute_masks overridden_masks (do_trim_const_masks do_trim_ctor_masks : bool) Σ : result dearg_set bytestring.string :=
  let (const_masks, ind_masks) := Utils.timed "Dearg analysis" (fun _ => analyze_env overridden_masks Σ) in
  let const_masks := (if do_trim_const_masks then trim_const_masks else id) const_masks in
  let ind_masks := (if do_trim_ctor_masks then trim_ind_masks else id) ind_masks in
  throwIf (negb (is_expanded_env ind_masks const_masks Σ))
    "Erased environment is not expanded enough for dearging to be provably correct"%bs ;;
  throwIf (negb (valid_masks_env ind_masks const_masks Σ))
    "Analysis produced masks that ask to remove live arguments"%bs ;;
  Ok (Build_dearg_set const_masks ind_masks).

Definition dearg_env masks Σ :=
  debox_env_types (dearg_env masks.(ind_masks) masks.(const_masks) Σ).

Import PCUICWfEnvImpl PCUICWfEnv PCUICTyping.

Definition dearg_term masks t :=
  dearg masks.(ind_masks) masks.(const_masks) t.

Lemma dearg_transform_gen_correct {wfl : WcbvFlags} overridden_masks do_trim_const_masks do_trim_ctor_masks :
  forall (Σ Σopt : global_env) t v masks,
  with_constructor_as_block = false ->
  env_closed (trans_env Σ) ->
  compute_masks overridden_masks do_trim_const_masks do_trim_ctor_masks Σ = ResultMonad.Ok masks ->
  closed t ->
  valid_cases masks.(ind_masks) t ->
  is_expanded masks.(ind_masks) masks.(const_masks) t ->
  trans_env Σ e⊢ t ⇓ v -> trans_env (dearg_env masks Σ) e⊢ dearg_term masks t ⇓ dearg_term masks v.
Proof.
  intros Σ Σopt t v masks block cl opt clt vc expc ev.
  unfold compute_masks in opt. cbn in opt.
  destruct analyze_env; cbn in *.
  destruct is_expanded_env eqn:exp; cbn in *; [|congruence].
  destruct valid_masks_env eqn:valid; cbn in *; [|congruence].
  injection opt as <-.
  set (im := (if do_trim_ctor_masks then trim_ind_masks else id) ind_masks) in *; clearbody im.
  set (cm := (if do_trim_const_masks then trim_const_masks else id) const_masks) in *; clearbody cm.
  apply eval_debox_env_types;eauto.
  apply dearg_correct; eauto.
Qed.

Lemma dearg_transform_correct {wfl : WcbvFlags} overridden_masks do_trim_const_masks do_trim_ctor_masks :
  ExtractTransformCorrect (dearg_transform overridden_masks do_trim_const_masks do_trim_ctor_masks true true true).
Proof.
  red.
  intros Σ Σopt kn ind c block opt ev.
  cbn in opt.
  destruct env_closed eqn:clos; cbn in *; [|congruence].
  destruct analyze_env; cbn in *.
  destruct is_expanded_env eqn:exp; cbn in *; [|congruence].
  destruct valid_masks_env eqn:valid; cbn in *; [|congruence].
  injection opt as <-.
  set (im := (if do_trim_ctor_masks then trim_ind_masks else id) ind_masks) in *; clearbody im.
  set (cm := (if do_trim_const_masks then trim_const_masks else id) const_masks) in *; clearbody cm.
  apply eval_debox_env_types;eauto.
  eapply eval_const_construct_expanded in ev as expanded_const; eauto.
  eapply eval_is_expanded_aux in ev as empty_ctor_mask; eauto.
  cbn in *.
  replace (tConst kn) with (dearg im cm (tConst kn)).
  replace (tConstruct ind c []) with (dearg im cm (tConstruct ind c [])).
  2-3: now cbn; destruct get_const_mask, get_ctor_mask.
  apply dearg_correct; eauto.
Qed.
