(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Stdlib Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config Universes BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICOnOne PCUICCases
     PCUICContextReduction PCUICEquality PCUICLiftSubst PCUICTyping PCUICWeakeningEnvConv
     PCUICWeakeningEnvTyp PCUICReduction PCUICClosedTyp
     PCUICInduction PCUICRedTypeIrrelevance PCUICOnFreeVars PCUICEtaExpand.
From Stdlib Require Import ssreflect ssrbool.
Set Asymmetric Patterns.

(* Require Import Equations.Type.DepElim. *)

Module RedFlags.

  Record t := mk {
    beta   : bool ;
    iota   : bool ;
    zeta   : bool ;
    delta  : bool ;
    fix_   : bool ;
    cofix_ : bool
  }.

  Definition default := mk true true true true true true.
  Definition nodelta := mk true true true false true true.

End RedFlags.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Section Normal.

  Context (flags : RedFlags.t).
  Context (Σ : global_env).

  (* Relative to reduction flags *)
  Inductive whne (Γ : context) : term -> Type :=
  | whne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      whne Γ (tRel i)

  | whne_rel_nozeta i :
      RedFlags.zeta flags = false ->
      whne Γ (tRel i)

  | whne_lam_nobeta na A b :
      RedFlags.beta flags = false ->
      whne Γ (tLambda na A b)

  | whne_var v :
      whne Γ (tVar v)

  | whne_evar n l :
      whne Γ (tEvar n l)

  | whne_letin_nozeta na B b t :
      RedFlags.zeta flags = false ->
      whne Γ (tLetIn na B b t)

  | whne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      whne Γ (tConst c u)

  | whne_const_nodelta c u :
      RedFlags.delta flags = false ->
      whne Γ (tConst c u)

  | whne_app f v :
      whne Γ f ->
      whne Γ (tApp f v)

  (* Stuck fixpoints are neutrals *)
  | whne_fixapp mfix idx args d arg :
     nth_error mfix idx = Some d ->
     nth_error args (rarg d) = Some arg ->
     whne Γ arg ->
     whne Γ (mkApps (tFix mfix idx) args)

  | whne_fix_nofix defs i :
      RedFlags.fix_ flags = false ->
      whne Γ (tFix defs i)

  | whne_case i p c brs :
      whne Γ c ->
      whne Γ (tCase i p c brs)

  | whne_case_noiota i p c brs :
      RedFlags.iota flags = false ->
      whne Γ (tCase i p c brs)

  | whne_proj p c :
      whne Γ c ->
      whne Γ (tProj p c)

  | whne_proj_noiota p c :
      RedFlags.iota flags = false ->
      whne Γ (tProj p c).

  (* Relative to reduction flags *)
  Inductive whnf (Γ : context) : term -> Type :=
  | whnf_ne t : whne Γ t -> whnf Γ t
  | whnf_sort s : whnf Γ (tSort s)
  | whnf_prod na A B : whnf Γ (tProd na A B)
  | whnf_lam na A B : whnf Γ (tLambda na A B)
  | whnf_cstrapp i n u v : whnf Γ (mkApps (tConstruct i n u) v)
  | whnf_indapp i u v : whnf Γ (mkApps (tInd i u) v)
  | whnf_fixapp mfix idx args :
    (exists d, nth_error mfix idx = Some d /\ nth_error args (rarg d) = None)
      \/ (nth_error mfix idx = None) ->
    whnf Γ (mkApps (tFix mfix idx) args)
  | whnf_cofixapp mfix idx v : whnf Γ (mkApps (tCoFix mfix idx) v)
  | whnf_prim p : whnf Γ (tPrim p).

  Lemma whne_mkApps :
    forall Γ t args,
      whne Γ t ->
      whne Γ (mkApps t args).
  Proof using Type.
    intros Γ t args h.
    induction args in t, h |- *.
    - assumption.
    - simpl. eapply IHargs. econstructor. assumption.
  Qed.

  Lemma whnf_mkApps :
    forall Γ t args,
      whne Γ t ->
      whnf Γ (mkApps t args).
  Proof using Type.
    intros. econstructor. now eapply whne_mkApps.
  Qed.

  Lemma whne_mkApps_inv :
    forall Γ t l,
      negb (isApp t) ->
      whne Γ (mkApps t l) ->
      whne Γ t +
      ∑ mfix idx d a,
        t = tFix mfix idx ×
        nth_error mfix idx = Some d ×
        nth_error l (rarg d) = Some a ×
        whne Γ a.
  Proof using Type.
    intros Γ t l Ha h. revert t Ha h.
    induction l using rev_ind; intros.
    - eauto.
    - rewrite mkApps_snoc in h.
      depelim h.
      + edestruct IHl as [ | (? & ? & ? & ? & ? & ? & ? & ?)]; eauto. subst.
        right. exists x0, x1, x2, x3. repeat split; eauto. now eapply nth_error_app_left.
      + rewrite <- mkApps_snoc in x.
        eapply (f_equal decompose_app) in x;
          rewrite !decompose_app_mkApps in x; cbn in *; try intuition congruence.
        inversion x. subst.
        right. exists mfix, idx, d, arg. repeat split; eauto.
  Qed.

End Normal.

Derive Signature for whnf.
Derive Signature for whne.
Derive Signature for All.
#[global]
Hint Constructors whnf whne : core.
#[global]
Hint Constructors whnf whne : pcuic.

Local Ltac inv H := inversion H; subst; clear H.

Ltac help' := try repeat match goal with
| [ H0 : _ = mkApps _ _ |- _ ] =>
  eapply (f_equal decompose_app) in H0;
    rewrite !decompose_app_mkApps in H0; cbn in *; intuition congruence
| [ H1 : tApp _ _ = mkApps _ ?args |- _ ] =>
  destruct args using rev_ind; cbn in *; [ inv H1 |
                                           rewrite mkApps_app in H1; cbn in *; inv H1
                                  ]
        end.
Ltac help := help'; try match goal with | [ H0 : mkApps _ _ = _ |- _ ] => symmetry in H0 end; help'.

#[global]
Hint Resolve All_Forall : core.

Notation decision P := ({P} + {~P}).

Lemma dec_All X (L : list X) P : All (fun x => decision (P x)) L ->
                                 All P L + (All P L -> False).
Proof.
  intros. induction X0.
  - left. econstructor.
  - destruct p.
    + destruct IHX0. left; econstructor; eauto. right. inversion 1. subst. eauto.
    + right. inversion 1; subst; eauto.
Defined.

Lemma negb_is_true b :
 ~ is_true b -> is_true (negb b).
Proof.
  destruct b; pcuicfo. congruence.
Qed.
#[global]
Hint Resolve negb_is_true : core.

Lemma whnf_mkApps_inv flags :
  forall Σ Γ t l,
    whnf flags Σ Γ (mkApps t l) ->
    whnf flags Σ Γ t.
Proof.
  intros Σ Γ t l h.
  remember (mkApps t l) eqn:hdeq.
  revert hdeq.
  induction h in h, t, l, t0 |- *; intros eq; subst.
  - destruct (mkApps_elim t l).
    apply whne_mkApps_inv in w; auto.
    destruct w as [wh|(?&?&?&?&->&?&?&?)].
    + now apply whnf_mkApps.
    + destruct (leb_spec_Set n (rarg x1)).
      * eapply whnf_fixapp.
        rewrite e. left.
        apply nth_error_Some_length in e0. eexists.
        split; try reflexivity. apply nth_error_None.
        rewrite length_firstn.
        lia.
      * apply whnf_ne.
        eapply whne_fixapp; eauto.
        assert (rarg x1 < #|l|) by (now apply nth_error_Some_length in e0).
        rewrite <- (firstn_skipn n l) in e0.
        rewrite nth_error_app1 in e0; auto.
        rewrite length_firstn.
        lia.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
    eapply whnf_fixapp. destruct o; [| now right].
    left; try reflexivity. destruct H; eexists.
    destruct H. split; eauto. destruct nth_error as [?|]; [|easy].
    apply nth_error_None.
    apply nth_error_None in e0.
    rewrite length_firstn.
    lia.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
Qed.

Lemma whnf_fixapp' {flags} Σ Γ mfix idx narg v :
  nth_error mfix idx = Some narg ->
  nth_error v (rarg narg) = None ->
  whnf flags Σ Γ (mkApps (tFix mfix idx) v).
Proof.
 intros E1 H. eapply whnf_fixapp. now left.
Qed.
#[global]
Hint Resolve whnf_fixapp' : core.

Lemma whnf_whne_nodelta_upgrade Σ Γ t :
  whnf RedFlags.default Σ Γ t ->
  whne RedFlags.nodelta Σ Γ t ->
  whne RedFlags.default Σ Γ t.
Proof.
  intros whn whe.
  induction whe; cbn in *; try easy.
  - now inv whn; solve_discr.
  - inv whn.
    + easy.
    + destruct v0 as [|? ? _] using MRList.rev_ind; [discriminate|].
      rewrite mkApps_app in H0 *.
      cbn in *; inv H0.
      constructor.
      eapply IHwhe.
      apply whnf_cstrapp.
    + destruct v0 as [|? ? _] using MRList.rev_ind; [discriminate|].
      rewrite mkApps_app in H0 *.
      cbn in *; inv H0.
      constructor.
      eapply IHwhe.
      apply whnf_indapp.
    + destruct args as [|? ? _] using MRList.rev_ind; [discriminate|].
      rewrite mkApps_app in H H0 *.
      cbn in *; inv H.
      constructor.
      eapply IHwhe. eapply whnf_fixapp.
      destruct H0 as [H0 |]; [left; destruct H0 as [? [? ?]] | now right].
      eexists; split; eauto.
      apply nth_error_None.
      apply nth_error_None in H0.
      rewrite length_app in H0; cbn in *.
      lia.
    + destruct v0 as [|? ? _] using MRList.rev_ind; [discriminate|].
      rewrite mkApps_app in H0 *.
      cbn in *; inv H0.
      constructor.
      eapply IHwhe.
      apply whnf_cofixapp.
  - inv whn; solve_discr; try easy.
    rewrite e in H0. exfalso.
    destruct H0 as [[? H0]|H0] ; inversion H0. congruence.
  - inv whn; solve_discr; easy.
  - inv whn; solve_discr; easy.
Qed.

Definition whnf_whne_dec flags Σ Γ t :
  ({∥whnf flags Σ Γ t∥} + {~∥whnf flags Σ  Γ t∥}) *
  ({∥whne flags Σ Γ t∥} + {~∥whne flags Σ Γ t∥}).
Proof with eauto using sq with pcuic; try congruence.
  induction t using term_forall_mkApps_ind in Γ |- *; split...
  all: try now (right; intros [H]; depelim H;help).
  - destruct (RedFlags.zeta flags) eqn:Er.
    + destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E...
      * right. intros [H]. depelim H. depelim w. congruence. congruence. all:help.
      * right. intros [H]. depelim H. depelim w. congruence. congruence. all:help.
    + eauto using sq.
  - destruct (RedFlags.zeta flags) eqn:Er...
    destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E...
    + right. intros [H]. depelim H. congruence. congruence. help.
    + right. intros [H]. depelim H. congruence. congruence. help.
  - destruct (RedFlags.beta flags) eqn:Er...
    right. intros [H]. depelim H. congruence. help.
  - destruct (RedFlags.zeta flags) eqn:Er...
    right. intros [H]. depelim H. depelim w. all:help. congruence.
  - destruct (RedFlags.zeta flags) eqn:Er...
    right. intros [H]. depelim H. congruence. help.
  - destruct (IHt Γ) as [[] _].
    + destruct t. all:try now (left; eauto using whnf_mkApps, All_Forall).
      all: try now left; destruct s as [w]; constructor; eapply whnf_mkApps; depelim w; eauto; help.
      * destruct v as [ | ? v]...
        right. intros [w]. depelim w. depelim w. all:help. clear IHt.
        eapply whne_mkApps_inv in w as []...
        -- depelim w. help.
        -- destruct s0 as [? [? [? [? [? [? ?]]]]]]. congruence.
      * destruct v as [ | ? v]...
        right. intros [w]. depelim w. depelim w. all:help. clear IHt.
        eapply whne_mkApps_inv in w as []...
        -- depelim w. help.
        -- destruct s0 as (?&?&?&?&?&?&?); congruence.
      * destruct v as [ | ? v]...
        destruct (RedFlags.beta flags) eqn:?.
        -- right. intros [w]. depelim w. depelim w. all:help. clear IHl.
           eapply whne_mkApps_inv in w as []...
           ++ depelim w. congruence. help.
           ++ destruct s0 as (?&?&?&?&?&?&?); congruence.
        -- left; constructor.
           apply whnf_mkApps.
           constructor.
           assumption.
      * destruct (nth_error mfix idx) as [narg |] eqn:E1.
        -- destruct (nth_error v (rarg narg)) as [a  | ] eqn:E2...
           destruct (nth_error_all E2 X Γ) as [_ []].
           ++ left. destruct s0...
           ++ destruct (RedFlags.fix_ flags) eqn:?.
              ** right. intros [w]. depelim w. depelim w. all:help. clear IHv.
                 eapply whne_mkApps_inv in w as []; eauto.
                 --- depelim w; [|congruence]. help.
                     eapply (f_equal decompose_app) in x;
                       rewrite !decompose_app_mkApps in x; cbn in *; try intuition congruence.
                     inv x. destruct (rarg d); inv e0.
                 --- destruct s0 as (? & ? & ? & ? & ? & ? & ? & ?). inv e.
                     rewrite E1 in e0. inv e0.
                     eapply (nth_error_app_left v [x0]) in e1.
                     rewrite E2 in e1. inv e1...
                 --- solve_discr.
                     rewrite E1 in e. injection e as ->.
                     rewrite E2 in e0. injection e0 as ->.
                     apply n; sq; auto.
                 --- solve_discr.
                     rewrite E1 in o. destruct o. destruct H1. destruct H1.  congruence.
                     congruence.
            ** left.
                 constructor.
                 apply whnf_mkApps.
                 constructor.
                 assumption.
        -- left. constructor. eapply whnf_fixapp. rewrite E1. eauto.
      * destruct v as [ | ? v]...
        right. intros [w]. depelim w. depelim w. all:help. clear IHt.
        eapply whne_mkApps_inv in w as []...
        -- depelim w. help.
        -- destruct s0 as [? [? [? [? [? [? ?]]]]]]. congruence.
    + right. intros [w]. eapply n. constructor. now eapply whnf_mkApps_inv.
  - destruct (IHt Γ) as [_ []].
    + left. destruct s as [w]. constructor. now eapply whne_mkApps.
    + destruct t.
      all: try (right; intros [[ | (mfix & idx & narg & a & [=] & ? & ? & ?) ] % whne_mkApps_inv]; subst)...
      * destruct (nth_error mfix idx) as [narg |] eqn:E1.
      -- destruct (nth_error v (rarg narg)) as [a  | ] eqn:E2.
         ++ destruct (nth_error_all E2 X Γ) as [_ []].
            ** left. destruct s. constructor. eauto.
            ** destruct (RedFlags.fix_ flags) eqn:?.
               --- right. intros ?. depelim H1. depelim X0. all:help. clear IHv.
                   eapply whne_mkApps_inv in X0 as []...
                   destruct s as (? & ? & ? & ? & ? & ? & ? & ?). inv e.
                   rewrite E1 in e0. inv e0.
                   eapply (nth_error_app_left v [x0]) in e1.
                   rewrite E2 in e1. inv e1... solve_discr.
                   rewrite E1 in e. injection e as ->.
                   rewrite E2 in e0. injection e0 as ->.
                   apply n0; sq; auto.
               --- left. constructor. apply whne_mkApps. constructor. assumption.
         ++ right. intros [[ | (mfix' & idx' & narg' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv]; subst; cbn...
      -- right. intros [[ | (mfix' & idx' & narg' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv]; subst; cbn...
      * right. intros [[ | (mfix' & idx' & narg' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv]; subst; cbn...
  - destruct (RedFlags.delta flags) eqn:Er...
    destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2...
      right. intros [w]. depelim w. depelim w. congruence. congruence. all:help.
    + right. intros [w]. depelim w. depelim w. congruence. congruence. all:help.
    + right. intros [w]. depelim w. depelim w. congruence. congruence. all:help.
  - destruct (RedFlags.delta flags) eqn:Er...
    destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2...
      right. intros [w]. depelim w. congruence. congruence. help.
    + right. intros [w]. depelim w. congruence. congruence. help.
    + right. intros [w]. depelim w. congruence. congruence. help.
  - left. constructor. eapply whnf_indapp with (v := []).
  - left. constructor. eapply whnf_cstrapp with (v := []).
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s...
    + right. intros [w]. depelim w. depelim w. all:help...
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s...
    + right. intros [w]. depelim w. all:help...
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s0...
    + right. intros [w]. depelim w. depelim w. all:help...
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s0...
    + right. intros [w]. depelim w. all:help...
  - destruct (nth_error m n) as [narg |] eqn:E1.
    + left. constructor. eapply whnf_fixapp with (args := []). rewrite E1.
      left; eexists; split; eauto. now destruct (rarg narg).
    + left. constructor. eapply whnf_fixapp with (args := []). now right.
  - destruct (RedFlags.fix_ flags) eqn:?...
    right. intros [w]. depelim w; [|congruence].
    destruct args using rev_ind.
    + destruct rarg; inv e0.
    + rewrite mkApps_snoc in x. inv x.
  - left. constructor. eapply whnf_cofixapp with (v := []).
Defined.

Definition whnf_dec flags Σ Γ t := fst (whnf_whne_dec flags Σ Γ t).
Definition whne_dec flags Σ Γ t := snd (whnf_whne_dec flags Σ Γ t).

Lemma red1_mkApps_tConstruct_inv Σ Γ i n u v t' :
  red1 Σ Γ (mkApps (tConstruct i n u) v) t' ->
  ∑ v', (t' = mkApps (tConstruct i n u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X. help.
  - rewrite mkApps_snoc in X. depelim X.
    + help.
    + help.
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x]). rewrite mkApps_snoc. split; eauto.
      apply OnOne2_app_r. assumption.
    + exists (v ++ [N2]). rewrite mkApps_snoc. split; eauto.
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma red1_mkApps_tInd_inv Σ Γ i u v t' :
  red1 Σ Γ (mkApps (tInd i u) v) t' ->
  ∑ v', (t' = mkApps (tInd i u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X. help.
  - rewrite mkApps_snoc in X. depelim X.
    + help.
    + help.
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x]). rewrite mkApps_snoc. split; eauto.
      apply OnOne2_app_r. assumption.
    + exists (v ++ [N2]). rewrite mkApps_snoc. split; eauto.
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma is_constructor_app_false i x y :
  is_constructor i (x ++ y) = false ->
  is_constructor i x = false.
Proof.
  unfold is_constructor.
  destruct (nth_error (x ++ y) i) eqn:nth.
  - destruct nth_error eqn:nth' in |- *; [|easy].
    erewrite nth_error_app_left in nth by easy.
    intros; congruence.
  - apply nth_error_None in nth.
    rewrite (proj2 (nth_error_None _ _)); [|easy].
    rewrite length_app in nth.
    lia.
Qed.

Lemma red1_mkApps_tFix_inv Σ Γ mfix id v t' :
  match unfold_fix mfix id with
  | Some (rarg, body) => is_constructor rarg v = false
  | None => True
  end ->
  red1 Σ Γ (mkApps (tFix mfix id) v) t' ->
  (∑ v', (t' = mkApps (tFix mfix id) v') * (OnOne2 (red1 Σ Γ) v v'))
  + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x0 : def term => (dname x0, dbody x0, rarg x0))) mfix mfix'))
  + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody (fun x0 : def term => (dname x0, dtype x0, rarg x0))) mfix mfix')).
Proof.
  intros not_ctor. revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help; eauto.
    solve_discr.
    unfold is_constructor in e0.
    rewrite nth_error_nil in e0.
    congruence.
  - rewrite mkApps_snoc in X.
    depelim X; help; eauto.
    + solve_discr.
      rewrite e in not_ctor, IHv.
      congruence.
    + eapply IHv in X as [ [(? & ? & ?)|(?&?&?)] | (?&?&?)].
      * subst. left. left. exists (x0 ++ [x]). split. now rewrite mkApps_snoc.
        now apply OnOne2_app_r.
      * subst. left. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * subst. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * destruct unfold_fix as [(?&?)|]; [|easy].
        now eapply is_constructor_app_false.
    + left. left. exists (v ++ [N2]). split.
      now rewrite mkApps_snoc.
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma red1_mkApps_tCoFix_inv Σ Γ mfix id v t' :
  red1 Σ Γ (mkApps (tCoFix mfix id) v) t' ->
  (∑ v', (t' = mkApps (tCoFix mfix id) v') * (OnOne2 (red1 Σ Γ) v v'))
  + (∑ mfix', (t' = mkApps (tCoFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x0 : def term => (dname x0, dbody x0, rarg x0))) mfix mfix'))
  + (∑ mfix', (t' = mkApps (tCoFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody (fun x0 : def term => (dname x0, dtype x0, rarg x0))) mfix mfix')).
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help; eauto.
  - rewrite mkApps_snoc in X.
    depelim X; help; eauto.
    + eapply IHv in X as [ [(? & ? & ?)|(?&?&?)] | (?&?&?)].
      * subst. left. left. exists (x0 ++ [x]). split. now rewrite mkApps_snoc.
        now apply OnOne2_app_r.
      * subst. left. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * subst. right. exists x0. split. now rewrite mkApps_snoc. eauto.
    + left. left. exists (v ++ [N2]). split.
      now rewrite mkApps_snoc.
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma whne_isConstruct_app flags Σ Γ t :
  isConstruct_app t ->
  whne flags Σ Γ t ->
  False.
Proof.
  intros ctor wh.
  unfold isConstruct_app in *.
  destruct decompose_app eqn:decomp.
  destruct t0; try easy.
  apply decompose_app_notApp in decomp as notapp.
  apply decompose_app_inv in decomp as ->.
  cbn in *.
  apply whne_mkApps_inv in wh; [|easy].
  destruct wh as [wh|(?&?&?&?&?&?&?)]; [|easy].
  depelim wh.
  solve_discr.
Qed.

Lemma whnf_mkApps_tSort_inv f Σ Γ s args :
  whnf f Σ Γ (mkApps (tSort s) args) -> args = [].
Proof.
  intros wh.
  inversion wh; solve_discr.
  clear -X.
  remember (mkApps (tSort s) args) eqn:teq.
  exfalso.
  revert teq.
  induction X in args |- *; intros; solve_discr.
  destruct args as [|? ? _] using MRList.rev_ind; [easy|].
  rewrite mkApps_app in teq.
  cbn in teq.
  inv teq.
  eauto.
Qed.

Lemma whnf_mkApps_tProd_inv f Σ Γ na A B args :
  whnf f Σ Γ (mkApps (tProd na A B) args) -> args = [].
Proof.
  intros wh.
  inversion wh; solve_discr.
  clear -X.
  remember (mkApps (tProd na A B) args) eqn:teq.
  exfalso.
  revert teq.
  induction X in args |- *; intros; solve_discr.
  destruct args as [|? ? _] using List.rev_ind; [easy|].
  rewrite mkApps_app in teq.
  cbn in teq.
  inv teq.
  eauto.
Qed.

Lemma whnf_mkApps_tLambda_inv f Σ Γ na A b args :
  RedFlags.beta f = true ->
  whnf f Σ Γ (mkApps (tLambda na A b) args) -> args = [].
Proof.
  intros nobeta wh.
  inversion wh; solve_discr.
  clear -X nobeta.
  remember (mkApps (tLambda na A b) args) eqn:teq.
  exfalso.
  revert teq.
  induction X in args |- *; intros; solve_discr.
  destruct args as [|? ? _] using List.rev_ind; [easy|].
  rewrite mkApps_app in teq.
  cbn in teq.
  inv teq.
  eauto.
Qed.

Section whne_red1_ind.
Context (flags : RedFlags.t).
Context (Σ : global_env).
Context (Γ : context).
Context (P : term -> term -> Type).

Lemma whne_red1_ind {cf:checker_flags} {wfΣ : wf Σ}
      (Hrel : forall i body,
          RedFlags.zeta flags = false ->
          option_map decl_body (nth_error Γ i) = Some (Some body) ->
          P (tRel i) (lift0 (S i) body))
      (Hlam_nobeta_1 : forall na A b M',
          RedFlags.beta flags = false ->
          red1 Σ Γ A M' ->
          P (tLambda na A b) (tLambda na M' b))
      (Hlam_nobeta_2 : forall na A b M',
          RedFlags.beta flags = false ->
          red1 Σ (Γ,, vass na A) b M' ->
          P (tLambda na A b) (tLambda na A M'))
      (Hevar : forall n l l',
          OnOne2 (red1 Σ Γ) l l' ->
          P (tEvar n l) (tEvar n l'))
      (Hletin_nozeta_1 :
         forall t' na B b t,
           RedFlags.zeta flags = false ->
           red1 Σ Γ (tLetIn na B b t) t' ->
           P (tLetIn na B b t) t')
      (Hconst_nodelta : forall t' c u,
          RedFlags.delta flags = false ->
          red1 Σ Γ (tConst c u) t' ->
          P (tConst c u) t')
      (Hbeta_nobeta :
         forall na t b v,
           RedFlags.beta flags = false ->
           P (tApp (tLambda na t b) v) (b{0 := v}))
      (Hfix_nofix :
         forall v mfix idx args narg fn,
           RedFlags.fix_ flags = false ->
           nth_error mfix idx = Some narg ->
           is_constructor (rarg narg) (args ++ [v]) = true ->
           P (mkApps (tFix mfix idx) (args ++ [v])) (mkApps fn (args ++ [v])))
      (Happ_1 : forall f v N1,
          whne flags Σ Γ f ->
          red1 Σ Γ f N1 ->
          P f N1 ->
          P (tApp f v) (tApp N1 v))
      (Happ_2 : forall f v N2,
          whne flags Σ Γ f ->
          red1 Σ Γ v N2 ->
          P (tApp f v) (tApp f N2))
      (Hfix_red_arg : forall mfix idx args narg arg x,
          nth_error mfix idx = Some narg ->
          nth_error args (rarg narg) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2 (fun a a' => red1 Σ Γ a a') args x ->
          (forall t', red1 Σ Γ arg t' -> P arg t') ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix mfix idx) x))
      (Hfix_red_def_type : forall mfix idx args d arg x,
          nth_error mfix idx = Some d ->
          nth_error args (rarg d) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2
            (fun x y : def term =>
               red1 Σ Γ (dtype x) (dtype y) *
               ((dname x, dbody x, BasicAst.rarg x) =
                (dname y, dbody y, BasicAst.rarg y))) mfix x ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix x idx) args))
      (Hfix_red_def_body : forall mfix idx args narg arg x,
          nth_error mfix idx = Some narg ->
          nth_error args (rarg narg) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2
            (fun x y : def term =>
               red1 Σ (Γ ,,, fix_context mfix) (dbody x) (dbody y) *
               ((dname x, dtype x, BasicAst.rarg x) =
                (dname y, dtype y, BasicAst.rarg y))) mfix x ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix x idx) args))
      (Hfix_red_type_nofix : forall defs i mfix1,
          RedFlags.fix_ flags = false ->
          OnOne2
            (fun x y : def term =>
               red1 Σ Γ (dtype x) (dtype y) *
               ((dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)))
            defs mfix1 ->
          P (tFix defs i) (tFix mfix1 i))
      (Hfix_red_body_nofix : forall defs i mfix1,
          RedFlags.fix_ flags = false ->
          OnOne2
            (fun x y : def term =>
               red1 Σ (Γ ,,, fix_context defs) (dbody x) (dbody y) *
               ((dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)))
            defs mfix1 ->
          P (tFix defs i) (tFix mfix1 i))
      (Hcase_params : forall i p c brs params',
          whne flags Σ Γ c ->
          OnOne2 (red1 Σ Γ) p.(pparams) params' ->
          P (tCase i p c brs) (tCase i (set_pparams p params') c brs))
      (Hcase_motive : forall i  p c brs p',
          whne flags Σ Γ c ->
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) p' ->
          P (tCase i p c brs) (tCase i (set_preturn p p') c brs))
      (Hcase_discr : forall i p c brs c',
          whne flags Σ Γ c ->
          red1 Σ Γ c c' ->
          P c c' ->
          P (tCase i p c brs) (tCase i p c' brs))
      (Hcase_branch : forall i p c brs brs',
          whne flags Σ Γ c ->
          OnOne2 (fun br br' =>
            let ctx := inst_case_branch_context p br in
            (on_Trel_eq (red1 Σ (Γ ,,, ctx)) bbody bcontext br br')%type)
            brs brs' ->
          P (tCase i p c brs) (tCase i p c brs'))
      (Hcase_noiota : forall t' i p c brs,
          RedFlags.iota flags = false ->
          red1 Σ Γ (tCase i p c brs) t' ->
          P (tCase i p c brs) t')
      (Hproj : forall p c c',
          whne flags Σ Γ c ->
          red1 Σ Γ c c' ->
          P c c' ->
          P (tProj p c) (tProj p c'))
      (Hproj_cofix_noiota : forall p mfix idx args narg fn,
          RedFlags.iota flags = false ->
          unfold_cofix mfix idx = Some (narg, fn) ->
          P (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args)))
      (Hproj_noiota : forall p args u arg,
          RedFlags.iota flags = false ->
          nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
          P (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg)
      (Hproj_discr_noiota : forall p c c',
          RedFlags.iota flags = false ->
          red1 Σ Γ c c' ->
          P (tProj p c) (tProj p c')) :
  forall t t', whne flags Σ Γ t -> red1 Σ Γ t t' -> P t t'.
Proof using Type.
  intros t t' wh r.
  induction wh in t, t', wh, r |- *; cbn in *.
  - depelim r; [congruence|now solve_discr].
  - depelim r; [|solve_discr]; eauto.
  - depelim r; solve_discr; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; eauto.
  - eauto.
  - depelim r; solve_discr.
    unshelve eapply declared_constant_to_gen in isdecl; try exact wfΣ.
    unfold declared_constant, declared_constant_gen in isdecl.
    rewrite e in isdecl.
    inv isdecl.
    congruence.
  - eauto.
  - depelim r; eauto.
    + depelim wh; solve_discr.
      now apply Hbeta_nobeta.
    + unfold unfold_fix in *.
      destruct args as [|? ? _] using MRList.rev_ind; [now solve_discr|].
      rewrite mkApps_app in x.
      cbn in *.
      inv x.
      apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|].
      * depelim w.
        -- solve_discr.
           rewrite nth_error_nil in e0; congruence.
        -- rewrite <- mkApps_snoc.
           case_eq (nth_error mfix idx); intros.
           eapply Hfix_nofix; eauto. all: rewrite H in e0; congruence.
      * destruct s as (?&?&?&?&?&?&?&?).
        inv e1.
        rewrite e2 in e.
        inv e.
        unfold is_constructor in e0.
        erewrite nth_error_app_left in e0 by eassumption.
        now apply whne_isConstruct_app in w; auto.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { unfold unfold_fix. rewrite e.
         unfold is_constructor.
         rewrite e0.
         destruct isConstruct_app eqn:ctor; [|easy].
         now eapply whne_isConstruct_app in ctor. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)]; eauto.
  - depelim r; eauto.
    destruct args using MRList.rev_ind; [|rewrite mkApps_app in x; cbn in x; discriminate].
    cbn in *.
    unfold is_constructor in e1.
    rewrite nth_error_nil in e1; discriminate.
  - depelim r; eauto.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w.
      solve_discr.
    + solve_discr.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w.
      solve_discr.
  - eauto.
  - depelim r; eauto.
    + solve_discr.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w.
      solve_discr.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w.
      solve_discr.
  - depelim r; eauto.
    solve_discr.
Qed.
End whne_red1_ind.

Lemma whne_pres1 {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red1 Σ Γ t t' ->
  whne RedFlags.default Σ Γ t ->
  whne RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  apply (whne_red1_ind RedFlags.default Σ Γ (fun _ => whne RedFlags.default Σ Γ))
         with (t := t) (t' := t'); intros; try easy.
  - eapply OnOne2_nth_error in H0; eauto.
    destruct H0 as (?&?&[->|]).
    + eapply whne_fixapp; eauto.
    + apply X1 in r0.
      eapply whne_fixapp; eauto.
  - unfold unfold_fix in *.
    destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply OnOne2_nth_error in nth; eauto.
    inv H.
    destruct nth as (?&?&[->|(?&?)]).
    + eapply whne_fixapp; eauto.
    + eapply whne_fixapp; eauto.
      now inv e0.
  - destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply OnOne2_nth_error in nth; eauto.
    inv H.
    destruct nth as (?&?&[->|(?&?)]).
    + eapply whne_fixapp; eauto.
    + eapply whne_fixapp; eauto.
      now inv e0.
Qed.

Lemma whne_pres {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red Σ Γ t t' ->
  whne RedFlags.default Σ Γ t -> whne RedFlags.default Σ Γ t'.
Proof.
  induction 1 using red_rect_n1; eauto using whne_pres1.
Qed.

Lemma whnf_pres1 {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red1 Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t ->
  whnf RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  induction wh in wh, t, t', r |- *; cbn in *.
  - constructor.
    now eapply whne_pres1.
  - depelim r.
    solve_discr.
  - depelim r; try easy.
    solve_discr.
  - depelim r; try easy.
    solve_discr.
  - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
    apply whnf_cstrapp.
  - apply red1_mkApps_tInd_inv in r as (?&->&?).
    apply whnf_indapp.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { unfold unfold_fix. destruct o as [[? [-> ?]] | ];
        unfold is_constructor; now rewrite H. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_fixapp. destruct o as [[d [? ?]] | ]; [left ; exists d| easy].
      split; eauto.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H0.
      lia.
    + apply whnf_fixapp.
      destruct o as [[d [? ?]] | ]; [left| right].
      eapply OnOne2_sym in o0.
      eapply OnOne2_nth_error_r in o0; eauto.
      destruct o0 as [? [? ?]]. eexists; split; eauto.
      destruct s as [| [? ?]]. now subst. now inv e0.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H.
      lia.
    + apply whnf_fixapp.
      destruct o as [[d [? ?]] | ]; [left| right].
      eapply OnOne2_sym in o0.
      eapply OnOne2_nth_error_r in o0; eauto.
      destruct o0 as [? [? ?]]. eexists; split; eauto.
      destruct s as [| [? ?]]. now subst. now inv e0.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H.
      lia.
  - eapply red1_mkApps_tCoFix_inv in r as [[(?&->&?)|(?&->&?)]|(?&->&?)]; eauto.
  - depelim r; solve_discr; eapply whnf_prim.
Qed.

Lemma whnf_pres {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t -> whnf RedFlags.default Σ Γ t'.
Proof.
  induction 1 using red_rect_n1; eauto using whnf_pres1.
Qed.

#[global]
Hint Resolve All2_same All2_firstn All2_skipn OnOne2_All2 red_mkApps All2_app : pcuic.

(* For terms in whnf we have a very useful inversion lemma for reductions.
   This next relation is a subrelation of red that classifies how whnf terms reduce. *)
Inductive whnf_red Σ Γ : term -> term -> Type :=
| whnf_red_tRel i :
    option_map decl_body (nth_error Γ i) = Some None ->
    whnf_red Σ Γ (tRel i) (tRel i)
| whnf_red_tVar id : whnf_red Σ Γ (tVar id) (tVar id)
| whnf_red_tEvar n l l' :
    All2 (red Σ Γ) l l' ->
    whnf_red Σ Γ (tEvar n l) (tEvar n l')
| whnf_red_tConst kn u decl :
    lookup_env Σ kn = Some (ConstantDecl decl) ->
    cst_body decl = None ->
    whnf_red Σ Γ (tConst kn u) (tConst kn u)
| whnf_red_tApp hd hd' arg arg' :
    whnf_red Σ Γ hd hd' ->
    red Σ Γ arg arg' ->
    whnf_red Σ Γ (tApp hd arg) (tApp hd' arg')
| whnf_red_tFix mfix mfix' idx :
    All2 (fun d d' => dname d = dname d' ×
                      rarg d = rarg d' ×
                      red Σ Γ (dtype d) (dtype d') ×
                      red Σ (Γ,,, fix_context mfix) (dbody d) (dbody d'))
         mfix mfix' ->
    whnf_red Σ Γ (tFix mfix idx) (tFix mfix' idx)
| whnf_red_tCase ci motive motivepars motiveret discr discr' brs brs' :
    All2 (red Σ Γ) motive.(pparams) motivepars ->

    red Σ (Γ ,,, inst_case_predicate_context motive) motive.(preturn) motiveret ->
    red Σ Γ discr discr' ->
    All2 (fun br br' =>
      red Σ (Γ ,,, inst_case_branch_context motive br) br.(bbody) br'.(bbody) ×
      bcontext br = bcontext br') brs brs' ->
    whnf_red Σ Γ (tCase ci motive discr brs)
      (tCase ci {| pparams := motivepars;
                  puinst := motive.(puinst);
                  pcontext := motive.(pcontext);
                  preturn := motiveret |} discr' brs')
| whnf_red_tProj p c c' :
    red Σ Γ c c' ->
    whnf_red Σ Γ (tProj p c) (tProj p c')
| whnf_red_tSort s : whnf_red Σ Γ (tSort s) (tSort s)
| whnf_red_tProd na A A' B B' :
    red Σ Γ A A' ->
    red Σ (Γ,, vass na A) B B' ->
    whnf_red Σ Γ (tProd na A B) (tProd na A' B')
| whnf_red_tLambda na A A' B B' :
    red Σ Γ A A' ->
    red Σ (Γ,, vass na A) B B' ->
    whnf_red Σ Γ (tLambda na A B) (tLambda na A' B')
| whnf_red_tConstruct i n u :
    whnf_red Σ Γ (tConstruct i n u) (tConstruct i n u)
| whnf_red_tInd i u :
    whnf_red Σ Γ (tInd i u) (tInd i u)
| whnf_red_tCoFix mfix mfix' idx :
    All2 (fun d d' => dname d = dname d' ×
                      rarg d = rarg d' ×
                      red Σ Γ (dtype d) (dtype d') ×
                      red Σ (Γ,,, fix_context mfix) (dbody d) (dbody d'))
         mfix mfix' ->
    whnf_red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx)
| whnf_red_tPrim i i' :
  onPrims (red Σ Γ) eq i i' ->
  whnf_red Σ Γ (tPrim i) (tPrim i').

Derive Signature for whnf_red.

#[global]
Hint Constructors whnf_red : pcuic.

Lemma All3_impl {A B C} (P Q : A -> B -> C -> Type) {l l' l''}
  (a : All3 P l l' l'') :
  (forall x y z, P x y z -> Q x y z) ->
  All3 Q l l' l''.
Proof.
  intros HPQ; induction a; constructor; auto.
Qed.

Lemma whnf_red_red Σ Γ t t' :
  whnf_red Σ Γ t t' ->
  red Σ Γ t t'.
Proof.
  intros wh.
  induction wh; eauto with pcuic.
  - apply red_evar; auto.
  - apply red_app; auto.
  - apply red_fix_congr.
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&r1&r2).
    eauto.
  - eapply red_case; eauto.
  - apply red_proj_c; auto.
  - apply red_prod; auto.
  - apply red_abs; auto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; [|constructor].
    apply All2_fold_refl.
    reflexivity.
  - apply red_cofix_congr.
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&r1&r2).
    eauto.
  - depelim o. 1-3: reflexivity.
    eapply red_primArray_congr; eauto.
Qed.

#[global]
Hint Resolve whnf_red_red : pcuic.

Lemma whnf_red_mkApps Σ Γ hd hd' args args' :
  whnf_red Σ Γ hd hd' ->
  All2 (red Σ Γ) args args' ->
  whnf_red Σ Γ (mkApps hd args) (mkApps hd' args').
Proof.
  intros r ra.
  induction ra using All2_rect_rev; auto.
  rewrite !mkApps_app.
  cbn.
  constructor; auto.
Qed.

#[global]
Hint Resolve whnf_red_mkApps : pcuic.

Lemma whnf_red_mkApps_l_inv Σ Γ hd args t :
  whnf_red Σ Γ (mkApps hd args) t ->
  ∑ hd' args',
    t = mkApps hd' args' × whnf_red Σ Γ hd hd' × All2 (red Σ Γ) args args'.
Proof.
  intros r.
  revert hd t r.
  induction args using MRList.rev_ind; intros hd t r.
  - cbn in *.
    eexists _, []; split; [reflexivity|].
    eauto with pcuic.
  - rewrite mkApps_app in r.
    cbn in r.
    depelim r.
    apply IHargs in r as (?&?&->&?&?); auto.
    exists x0, (x1 ++ [arg']).
    rewrite mkApps_app.
    eauto with pcuic.
Qed.

Lemma whnf_red_mkApps_r_inv Σ Γ t hd' args' :
  whnf_red Σ Γ t (mkApps hd' args') ->
  ∑ hd args,
    t = mkApps hd args × whnf_red Σ Γ hd hd' × All2 (red Σ Γ) args args'.
Proof.
  intros r.
  revert hd' t r.
  induction args' using MRList.rev_ind; intros hd' t r.
  - cbn in *.
    eexists _, []; split; [reflexivity|].
    eauto with pcuic.
  - rewrite mkApps_app in r.
    cbn in r.
    depelim r.
    apply IHargs' in r as (?&?&->&?&?); auto.
    exists x0, (x1 ++ [arg]).
    rewrite mkApps_app.
    eauto with pcuic.
Qed.

Lemma whnf_red_mkApps_inv Σ Γ hd args hd' args' :
  whnf_red Σ Γ (mkApps hd args) (mkApps hd' args') ->
  isApp hd = false ->
  isApp hd' = false ->
  whnf_red Σ Γ hd hd' × All2 (red Σ Γ) args args'.
Proof.
  intros r notapp notapp'.
  apply whnf_red_mkApps_l_inv in r as (?&?&eq&?&?); auto.
  apply mkApps_notApp_inj in eq as (->&->); auto.
  now depelim w.
Qed.

Lemma whnf_red_refl_whne Σ Γ t :
  whne RedFlags.default Σ Γ t ->
  whnf_red Σ Γ t t.
Proof.
  intros wh.
  induction wh; cbn in *; try discriminate; eauto using whnf_red with pcuic.
  - apply whnf_red_mkApps; auto.
     2: apply All2_same; auto.
    constructor.
    apply All2_same; auto.
  - destruct p. econstructor; simpl; eauto.
    * eapply All2_same; auto.
    * eapply All2_same; intuition auto.
Qed.

Lemma whnf_red_refl Σ Γ t :
  whnf RedFlags.default Σ Γ t ->
  whnf_red Σ Γ t t.
Proof.
  intros wh.
  induction wh; cbn in *; try discriminate; eauto with pcuic.
  - eapply whnf_red_refl_whne; eauto.
  - apply whnf_red_mkApps; auto.
    2: apply All2_same; auto.
    constructor.
    apply All2_same; auto.
  - apply whnf_red_mkApps; auto.
    2: apply All2_same; auto.
    constructor.
    apply All2_same; auto.
  - constructor. destruct p as [? []]; constructor; eauto. eapply All2_same; auto.
Qed.

Ltac inv_on_free_vars :=
  match goal with
  | [ H : is_true (on_free_vars_decl _ _) |- _ ] => progress cbn in H
  | [ H : is_true (on_free_vars_decl _ (vdef _ _ _)) |- _ ] => unfold on_free_vars_decl, test_decl in H
  | [ H : is_true (_ && _) |- _ ] =>
    move/andP: H => []; intros
  | [ H : is_true (on_free_vars ?P ?t) |- _ ] =>
    progress (cbn in H || rewrite on_free_vars_mkApps in H);
    (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] ||
      eapply forallb_All in H); intros
  | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
    move/andP: H => []; rewrite ?shiftnP_xpredT; intros
  | [ H : is_true (test_context_k _ _ _ ) |- _ ] =>
    rewrite -> test_context_k_closed_on_free_vars_ctx in H
  end.

From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity PCUICOnFreeVars PCUICConfluence PCUICSR PCUICConversion PCUICSubstitution.

Lemma red_ctx_rel_subst {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} P Γ Γ' s s' Δ :
  All2 (red Σ Γ) s s' ->
  All (on_free_vars (shiftnP #|Γ| P)) s ->
  untyped_subslet Γ s Γ' ->
  on_free_vars_ctx P (Γ ,,, Γ' ,,, Δ) ->
  red_context_rel Σ Γ (subst_context s 0 Δ) (subst_context s' 0 Δ).
Proof.
  intros Hs ons subs onctx.
  induction Δ; cbn.
  * rewrite !subst_context_nil. constructor.
  * move: onctx => /=. rewrite on_free_vars_ctx_snoc => /andP[] onctx ona.
    rewrite !subst_context_snoc !Nat.add_0_r.
    constructor; eauto.
    now apply IHΔ.
    destruct a as [na [b|] ty]; constructor; cbn.
    relativize #|Δ|. eapply red_red; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
    relativize #|Δ|. eapply red_red; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
    relativize #|Δ|. eapply red_red; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
Qed.

Definition fake_params n : context :=
    unfold n (fun x => {| decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                          decl_body := None;
                          decl_type := tSort Sort.type0 |}).

Lemma fake_params_length n : #|fake_params n| = n.
Proof.
  induction n; simpl; auto. cbn.
  now rewrite length_app IHn /= Nat.add_1_r.
Qed.

Lemma params_subslet {cf:checker_flags} Γ pars :
  untyped_subslet Γ pars (List.rev (fake_params #|pars|)).
Proof.
  induction pars; cbn. constructor.
  rewrite List.rev_app_distr /=. constructor; auto.
Qed.

Lemma closed_fake_params n P :
  on_free_vars_ctx P (List.rev (fake_params n)).
Proof.
  unfold on_free_vars_ctx. generalize 0. rewrite List.rev_involutive.
  induction n; cbn => //.
  intros n'.
  rewrite alli_app IHn /= //.
Qed.

Lemma red_terms_on_free_vars {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ ts us}:
  is_closed_context Γ ->
  forallb (is_open_term Γ) ts ->
  All2 (red Σ Γ) ts us ->
  forallb (is_open_term Γ) us.
Proof.
  solve_all. eapply red_on_free_vars; tea.
  now rewrite on_free_vars_ctx_on_ctx_free_vars.
Qed.

Definition br_fvs (Γ : context) (motive : predicate term) br :=
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT))
    #|pparams motive| (bcontext br) &&
  on_free_vars (shiftnP #|bcontext br| (shiftnP #|Γ| xpred0)) (bbody br).

Lemma br_fvs_pres {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ motive brs brs' :
  is_closed_context Γ ->
  forallb (is_open_term Γ) (pparams motive) ->
  All (br_fvs Γ motive) brs ->
  All2
    (fun br br' : branch term =>
    red Σ (Γ,,, inst_case_branch_context motive br)
       (bbody br) (bbody br') * (bcontext br = bcontext br')) brs brs' ->
  All (br_fvs Γ motive) brs'.
Proof.
  intros clΓ clpars.
  unfold br_fvs; solve_all.
  now rewrite b0 in H.
  rewrite -b0. eapply red_on_free_vars; tea.
  rewrite shiftnP_add. relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
  2:len.
  rewrite on_free_vars_ctx_app clΓ /=.
  eapply on_free_vars_ctx_inst_case_context; trea. solve_all.
Qed.

Lemma whnf_red_trans {cf:checker_flags} {Σ : global_env_ext} Γ x y z : wf Σ ->
  is_closed_context Γ ->
  is_open_term Γ x ->
  whnf_red Σ Γ x y ->
  whnf_red Σ Γ y z ->
  whnf_red Σ Γ x z.
Proof.
  intros wf onΓ onx xy yz.
  revert onx z yz.
  induction xy; intros onx z yz; depelim yz; repeat inv_on_free_vars; eauto using whnf_red.
  - constructor.
    eapply All2_trans; eauto.
    typeclasses eauto.
  - constructor; eauto.
    all: try etransitivity; eauto.
  - constructor.
    eapply All2_trans; eauto.
    1: { intros ? ? ? (->&->&?&?) (->&->&?&?).
         do 2 (split; auto).
         split; etransitivity; eauto. }
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&?&?).
    do 3 (split; auto).
    eapply context_pres_let_bodies_red; eauto.
    apply fix_context_pres_let_bodies.
    now apply All2_length in a.
  - simpl in *.
    constructor; try solve [etransitivity; eauto].
    + eapply All2_trans; eauto.
      typeclasses eauto.
    + etransitivity; [eassumption|].
      have clp: on_ctx_free_vars (closedP #|Γ,,, inst_case_predicate_context motive| xpredT)
        (Γ,,, inst_case_predicate_context motive).
      { rewrite closedP_shiftnP_eq on_free_vars_ctx_on_ctx_free_vars.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
        rewrite test_context_k_closed_on_free_vars_ctx //. }
      eapply red_red_ctx. 5:tea. all:eauto; revgoals.
      apply red_context_app_right; eauto.
      * apply red_context_refl.
      * rewrite /inst_case_predicate_context /=.
        rewrite /inst_case_context.
        eapply (red_ctx_rel_subst (Σ := empty_ext Σ)).
        eapply All2_rev => //.
        eapply All_rev. solve_all.
        instantiate (1 := List.rev (fake_params #|pparams motive|)).
        rewrite -(List.length_rev (pparams motive)).
        eapply params_subslet.
        rewrite !on_free_vars_ctx_app onΓ /=. len.
        rewrite on_free_vars_ctx_subst_instance.
        rewrite closed_fake_params /=.
        setoid_rewrite closedP_shiftnP_eq in p1.
        eapply on_free_vars_ctx_impl; tea.
        rewrite /shiftnP. intros i. rewrite !orb_false_r.
        move/Nat.ltb_lt => ?. apply Nat.ltb_lt. lia.
      * eapply red_on_free_vars; tea.
        len. rewrite closedP_shiftnP_eq -shiftnP_add //.
      * rewrite closedP_shiftnP_eq.
        relativize #|Γ ,,, _|; [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //. cbn.
        eapply red_terms_on_free_vars; tea.
        rewrite test_context_k_closed_on_free_vars_ctx -(All2_length a) //.

    + eapply forallb_All in p3.
      epose proof (br_fvs_pres _ _ _ _ onΓ p p3 a0).
      eapply (All2_impl (P:=fun br br' => br_fvs Γ motive br ×
        red Σ (Γ,,, inst_case_branch_context motive br) (bbody br) (bbody br') *
            (bcontext br = bcontext br'))).
      2:intuition.
      eapply All2_trans with brs'.
      { clear -wf p.
        intros br br' br''. intuition auto. 2:congruence.
        etransitivity; tea. unfold inst_case_branch_context in *. now rewrite -b1 in a2. }
      1:solve_all.
      eapply All2_All_mix_left in a2; tea. eapply All2_impl; tea.
      intros br br'; cbn. intuition auto.
      unfold br_fvs in a3.
      move/andP: a3 => [] fvbctx fvbr.
      eapply red_red_ctx. 5:tea. all:eauto; revgoals.
      apply red_context_app_right; eauto.
      * rewrite closedP_shiftnP_eq on_free_vars_ctx_on_ctx_free_vars.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
      * apply red_context_refl.
      * rewrite /inst_case_branch_context /=.
        rewrite /inst_case_context.
        eapply (red_ctx_rel_subst (Σ := empty_ext Σ)).
        eapply All2_rev => //.
        eapply All_rev. solve_all.
        instantiate (1 := List.rev (fake_params #|pparams motive|)).
        rewrite -(List.length_rev (pparams motive)).
        eapply params_subslet.
        rewrite !on_free_vars_ctx_app onΓ /=. len.
        rewrite on_free_vars_ctx_subst_instance.
        rewrite closed_fake_params /=.
        move: fvbctx.
        rewrite test_context_k_closed_on_free_vars_ctx closedP_shiftnP_eq => H.
        eapply on_free_vars_ctx_impl; tea.
        rewrite /shiftnP. intros i. rewrite !orb_false_r.
        move/Nat.ltb_lt => ?. apply Nat.ltb_lt. lia.
      * rewrite shiftnP_add.
        relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
      * rewrite shiftnP_add.
        relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
        eapply red_terms_on_free_vars; tea.
        now rewrite -(All2_length a).
  - constructor.
    etransitivity; eauto.
  - constructor; etransitivity; eauto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; eauto; [|constructor].
    apply All2_fold_refl.
    intros _ ?. reflexivity.
  - constructor; etransitivity; eauto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; eauto; [|constructor].
    apply All2_fold_refl.
    intros _ ?; reflexivity.
  - constructor.
    eapply All2_trans; eauto.
    1: { intros ? ? ? (->&->&?&?) (->&->&?&?).
         do 2 (split; auto).
         split; etransitivity; eauto. }
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&?&?).
    do 3 (split; auto).
    eapply context_pres_let_bodies_red; eauto.
    apply fix_context_pres_let_bodies.
    now apply All2_length in a.
  - constructor. depelim o; depelim o0; constructor; eauto.
    * etransitivity; tea.
    * etransitivity; tea.
    * etransitivity; tea.
    * eapply All2_trans; eauto.
      tc.
Qed.

Lemma whne_red1_inv {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  whne RedFlags.default Σ Γ t ->
  red1 Σ Γ t t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wh r.
  apply (whne_red1_ind
           RedFlags.default Σ Γ
           (whnf_red Σ Γ)); intros; cbn in *; try easy; eauto using whnf_red.
  - constructor.
    eapply OnOne2_All2; eauto.
  - constructor; auto.
    now apply whnf_red_refl_whne.
  - apply whnf_red_mkApps; eauto.
    1: constructor; apply All2_same; auto.
    eapply OnOne2_All2; eauto.
  - apply whnf_red_mkApps; eauto.
    + constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply All2_same; auto.
  - apply whnf_red_mkApps; eauto.
    + constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply All2_same; auto.
  - constructor; auto.
    * eapply OnOne2_All2; eauto.
    * eapply All2_same; intuition auto.
  - econstructor; auto. apply All2_same; auto.
    eapply All2_same; intuition auto.
  - destruct p; econstructor; eauto; simpl.
    * eapply All2_same; auto.
    * eapply All2_same; intuition auto.
  - destruct p;  econstructor; eauto; simpl.
    * eapply All2_same; reflexivity.
    * eapply OnOne2_All2; eauto.
      cbn. intros ? ? [? <-].
      intuition eauto; try reflexivity.
Qed.

Lemma whnf_red1_inv {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wh r.
  destruct wh.
  - eapply whne_red1_inv; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; constructor; eauto using whnf_red.
  - depelim r; solve_discr; constructor; eauto using whnf_red.
  - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
    apply whnf_red_mkApps; eauto using whnf_red.
    eapply OnOne2_All2; eauto.
  - apply red1_mkApps_tInd_inv in r as (?&->&?).
    apply whnf_red_mkApps; eauto using whnf_red.
    eapply OnOne2_All2; eauto.
  - apply red1_mkApps_tFix_inv in r.
    2: { unfold unfold_fix. destruct o as [[? [-> ?]]|];
         now unfold is_constructor; rewrite H. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_red_mkApps; auto.
      2: eapply OnOne2_All2; eauto.
      constructor.
      apply All2_same; auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
  - apply red1_mkApps_tCoFix_inv in r.
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_red_mkApps; auto.
      2: eapply OnOne2_All2; eauto.
      constructor.
      apply All2_same; auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
  - depelim r; solve_discr; constructor; eauto.
    * constructor; eauto. eapply OnOne2_All2; eauto.
    * constructor; eauto. cbn. eapply All2_same; eauto.
    * constructor; eauto. cbn. eapply All2_same; eauto.
Qed.

Lemma whnf_red_inv {cf:checker_flags} {Σ : global_env_ext} Γ t t' :
  wf Σ ->
  whnf RedFlags.default Σ Γ t ->
  Σ ;;; Γ ⊢ t ⇝ t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wf wh [clΓ clt r].
  induction r using red_rect_n1.
  - apply whnf_red_refl; auto.
  - eapply whnf_red1_inv in X; eauto.
    + eapply whnf_red_trans; tea.
    + eapply whnf_pres; eauto.
Qed.

Lemma whnf_red_isApp Σ Γ t t' :
  whnf_red Σ Γ t t' ->
  isApp t' = isApp t.
Proof.
  intros r.
  now depelim r.
Qed.

Lemma whne_eq_term_upto_univ_napp f Σ Γ t cmp_universe cmp_sort pb napp t' :
  whne f Σ Γ t ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t' ->
  whne f Σ Γ t'.
Proof.
  intros wh eq.
  induction wh in pb, napp, t, t', eq, wh |- *; depelim eq;
    try solve [eauto using whne; depelim wh; solve_discr; eauto using whne].
  - destruct args as [|? ? _] using MRList.rev_ind; [discriminate x|].
    rewrite mkApps_app in x; cbn in x; inv x.
    apply eq_term_upto_univ_napp_mkApps_l_inv in eq1 as (?&?&(eq_hds&?)&->).
    depelim eq_hds.
    rewrite <- mkApps_snoc.
    assert (All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) (args ++ [x0]) (x1 ++ [u']))
           by (now apply All2_app).
    unfold unfold_fix in *.
    destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply All2_nth_error_Some in nth; eauto.
    destruct nth as (?&?&?&?).
    eapply All2_nth_error_Some in e0; eauto.
    inv e.
    destruct e0 as (?&?&?).
    eapply whne_fixapp.
    + unfold unfold_fix.
      rewrite e2.
      reflexivity.
    + rewrite <- e.
      destruct p as (?& eqrarg &?). rewrite eqrarg. reflexivity.
    + eapply IHwh; eauto.
  - destruct args using MRList.rev_ind; [|rewrite mkApps_app in x; discriminate x].
    now rewrite nth_error_nil in e0.
Qed.

Lemma whnf_eq_term_upto_univ_napp f Σ Γ t cmp_universe cmp_sort pb napp t' :
  whnf f Σ Γ t ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t' ->
  whnf f Σ Γ t'.
Proof.
  intros wh eq.
  depelim wh.
  - constructor.
    eapply whne_eq_term_upto_univ_napp; eauto.
  - depelim eq.
    apply whnf_sort.
  - depelim eq.
    apply whnf_prod.
  - depelim eq.
    apply whnf_lam.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_cstrapp.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_indapp.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_fixapp. destruct o as [[? [? ?]] |].
    eapply All2_nth_error_Some in e; eauto.
    destruct e as (? & e & ? & ? & e2 & ?).
    rewrite e. left; eexists; split; eauto. rewrite <- e2.
    eapply All2_nth_error_None; eauto.
    apply All2_length in e.
    right. apply nth_error_None.
    apply nth_error_None in H.
    lia.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_cofixapp.
  - depelim eq; auto.
Qed.

Lemma whnf_eq_term {cf:checker_flags} f Σ φ Γ t t' :
  whnf f Σ Γ t ->
  eq_term Σ φ t t' ->
  whnf f Σ Γ t'.
Proof.
  apply whnf_eq_term_upto_univ_napp.
Qed.


Section Normal.

  Context (flags : RedFlags.t).
  Context (Σ : global_env).

  (* Relative to reduction flags *)
  Inductive ne (Γ : context) : term -> Prop :=
  | ne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      ne Γ (tRel i)

  | ne_var v :
      ne Γ (tVar v)

  | ne_evar n l :
    All (ne Γ) l ->
    ne Γ (tEvar n l)

  | ne_app f a :
    ne Γ f ->
    nf Γ a ->
    ne Γ (tApp f a)

  (* | nf_letin_nozeta na B b t :
      RedFlags.zeta flags = false ->
      whne Γ (tLetIn na B b t) *)

  | ne_const c u decl :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    ne Γ (tConst c u)

  (* | whne_const_nodelta c u :
      RedFlags.delta flags = false ->
      whne Γ (tConst c u) *)

  (* Stuck fixpoints are neutrals *)
  | ne_fixapp mfix idx args d arg :
     nth_error mfix idx = Some d ->
     nth_error args (rarg d) = Some arg ->
     All (nf Γ) args ->
     ne Γ arg ->
     All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype)) mfix ->
     ne Γ (mkApps (tFix mfix idx) args)

  | ne_case i p c brs :
    ne Γ c ->
    All (fun br => nf (Γ ,,, inst_case_branch_context p br) br.(bbody)) brs ->
    All (nf Γ) (pparams p) ->
    onctx_rel nf Γ (inst_case_predicate_context p) ->
    nf (Γ,,, inst_case_context (pparams p) (puinst p) (pcontext p)) (preturn p) ->
    ne Γ (tCase i p c brs)

  | ne_proj p c :
    ne Γ c ->
    ne Γ (tProj p c)

  with nf (Γ : context) : term -> Prop :=
  | ne_nf t : ne Γ t -> nf Γ t

  | nf_lam na A b :
    nf Γ A ->
    nf (Γ ,, vass na A) b ->
    nf Γ (tLambda na A b)

  | nf_construct ind k u :
    nf Γ (tConstruct ind k u)

  | nf_cofix mfix idx args :
    All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype)) mfix ->
    All (nf Γ) args ->
    nf Γ (mkApps (tCoFix mfix idx) args)

  | nf_tind ind u : nf Γ (tInd ind u)
  | nf_tProd na dom codom : nf Γ dom -> nf (Γ ,, vass na dom) codom -> nf Γ (tProd na dom codom).

  Scheme nf_ne_ind := Minimality for ne Sort Prop
  with ne_nf_ind := Minimality for nf Sort Prop.

  Section nf_ne_ind.
    Context (P P0 : context -> term -> Prop).
    Context (hrel : (forall (Γ : context) (i : nat),
    option_map decl_body (nth_error Γ i) = Some None -> P Γ (tRel i)))
    (hvar : (forall (Γ : context) (v : ident), P Γ (tVar v)))
    (hevar : (forall (Γ : context) (n : nat) (l : list term),
    All (fun x => ne Γ x × P Γ x) l -> P Γ (tEvar n l)))
    (happ : (forall (Γ : context) (f2 a : term),
    ne Γ f2 -> P Γ f2 -> nf Γ a -> P0 Γ a -> P Γ (tApp f2 a)))
    (hcst : (forall (Γ : context) (c : kername) (u : Instance.t) (decl : constant_body),
    lookup_env Σ c = Some (ConstantDecl decl) ->
    cst_body decl = None -> P Γ (tConst c u)))
    (hfix :
    (forall (Γ : context) (mfix : list (def term)) (idx : nat)
      (args : list term) (d : def term) (arg : term),
    nth_error mfix idx = Some d ->
    nth_error args (rarg d) = Some arg ->
    All (fun x => nf Γ x /\ P0 Γ x) args -> ne Γ arg -> P Γ arg ->
    All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ P0 (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype) /\ P0 Γ d.(dtype)) mfix ->

    P Γ (mkApps (tFix mfix idx) args)))

    (hcase : (forall (Γ : context) (i : case_info) (p : predicate term)
      (c : term) (brs : list (branch term)),
    ne Γ c ->
    P Γ c ->
    All
      (fun br : branch term =>
      nf (Γ,,, inst_case_branch_context p br) (bbody br) /\ P0 (Γ ,,, inst_case_branch_context p br) (bbody br)) brs ->
    All (nf Γ) (pparams p) ->
    onctx_rel nf Γ (inst_case_predicate_context p) ->
    nf (Γ,,, inst_case_context (pparams p) (puinst p) (pcontext p)) (preturn p) ->
    All (P0 Γ) (pparams p) ->
    onctx_rel P0 Γ (inst_case_predicate_context p) ->
    P0 (Γ,,, inst_case_context (pparams p) (puinst p) (pcontext p)) (preturn p) ->
    P Γ (tCase i p c brs)))

    (hproj : (forall (Γ : context) (p : projection) (c : term),
    ne Γ c -> P Γ c -> P Γ (tProj p c)))
    (hne : (forall (Γ : context) (t : term), ne Γ t -> P Γ t -> P0 Γ t))
    (hlam : (forall (Γ : context) (na : aname) (A b : term),
    nf Γ A ->
    P0 Γ A ->
    nf (Γ,, vass na A) b -> P0 (Γ,, vass na A) b -> P0 Γ (tLambda na A b)))
    (hconstruct : (forall (Γ : context) (ind : inductive) (k : nat) (u : Instance.t),
    P0 Γ (tConstruct ind k u)))

    (hcofix : (forall (Γ : context) mfix idx args,

    All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ P0 (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype) /\ P0 Γ d.(dtype)) mfix ->
    All (fun t => nf Γ t /\ P0 Γ t) args ->
    P0 Γ (mkApps (tCoFix mfix idx) args)))

    (hind : (forall (Γ : context) (ind : inductive) (u : Instance.t), P0 Γ (tInd ind u)))

    (hprod : forall Γ na dom codom,
      nf Γ dom -> P0 Γ dom ->
      nf (Γ ,, vass na dom) codom ->
      P0 (Γ ,, vass na dom) codom ->
      P0 Γ (tProd na dom codom)).

    Lemma ne_ind_all : forall (Γ : context) (t : term), ne Γ t -> P Γ t
    with nf_ind_all : forall (Γ : context) (t : term), nf Γ t -> P0 Γ t.
    Proof.
      destruct 1; [eapply hrel|eapply hvar|eapply hevar|eapply happ|eapply hcst|eapply hfix|eapply hcase|eapply hproj]; eauto.
      * induction X; constructor; eauto.
      * clear -X nf_ind_all. induction X; constructor; eauto.
      * clear -X0 nf_ind_all; revert X0; generalize (fix_context mfix); induction 1; constructor; intuition eauto.
      * clear -X nf_ind_all; revert X; induction 1; constructor; intuition eauto.
      * clear -X0 nf_ind_all. revert X0; induction 1; constructor; intuition eauto.
      * clear -X1 nf_ind_all; revert X1; induction 1; constructor; unfold on_local_decl, lift_wf_term in *; cbn in *; intuition eauto.
      * destruct 1; [eapply hne|eapply hlam|eapply hconstruct|eapply hcofix|eapply hind|eapply hprod]; eauto.
        clear -X nf_ind_all. revert X; generalize (fix_context mfix); induction 1; constructor; intuition eauto.
        clear -X0 nf_ind_all. induction X0; constructor; eauto.
    Qed.

    Lemma ne_nf_ind_all : forall Γ t, (ne Γ t -> P Γ t) /\ (nf Γ t -> P0 Γ t).
    Proof.
      split; apply ne_ind_all || apply nf_ind_all.
    Qed.

  End nf_ne_ind.

  Lemma ne_mkApps_inv Γ f args :
    ~~ isApp f ->
    ne Γ (mkApps f args) ->
    (~~ isFix f /\ ne Γ f /\ Forall (nf Γ) args) \/
    (exists c u decl, f = tConst c u /\ lookup_env Σ c = Some (ConstantDecl decl) /\
      decl.(cst_body) = None) \/
    (exists mfix idx d arg, f = tFix mfix idx /\
      nth_error mfix idx = Some d /\
      nth_error args (rarg d) = Some arg /\
      Forall (nf Γ) args /\
      Forall (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype)) mfix /\
      ne Γ arg).
  Proof.
    revert f. induction args using rev_ind; cbn.
    - intros f napp. intros ne; depelim ne; try solve [left; split; [|split]; constructor; eauto; constructor].
      right. left. do 2 eexists; eauto.
      right; right. do 4 eexists. eapply nisApp_mkApps in napp as [? ->]. intuition eauto.

      - intros. specialize (IHargs f H).
        rewrite mkApps_app /= in H0.
        depelim H0. specialize (IHargs H0). intuition eauto.
        * left. intuition auto. eapply app_Forall; eauto.
        * right; right. destruct H3 as [mfix [idx [d [arg []]]]]. exists mfix, idx, d, arg. intuition eauto. erewrite nth_error_app_left; tea. reflexivity.
          eapply app_Forall; eauto.
        * destruct args0 using rev_case. cbn in x. noconf x. rewrite mkApps_app in x; noconf x.
          eapply mkApps_eq_inj in H3 => //. destruct H3; subst.
          right; right. exists mfix, idx, d, arg. intuition auto.
  Qed.

  Lemma OnOne2_nth_error {A} (l l' : list A) P :
    OnOne2 P l l' ->
    ∑ n t t', [× nth_error l n = Some t, nth_error l' n = Some t' & P t t'].
  Proof.
    induction 1 in |- *.
    - exists 0, hd, hd'; intuition auto.
    - destruct IHX as [n [t [t' []]]]. exists (S n), t, t'; intuition auto.
  Qed.

  Lemma ne_tConstruct_app Γ c k u args : ne Γ (mkApps (tConstruct c k u) args) -> False.
  Proof.
    induction args using rev_ind; cbn; intros hne; depelim hne; solve_discr.
    rewrite mkApps_app /= in x; noconf x; eauto.
  Qed.

  Lemma ne_tCoFix_app Γ mfix idx args : ne Γ (mkApps (tCoFix mfix idx) args) -> False.
  Proof.
    induction args using rev_ind; cbn; intros hne; depelim hne; solve_discr.
    rewrite mkApps_app /= in x; noconf x; eauto.
  Qed.

  Lemma isConstruct_app_ne Γ t : isConstruct_app t -> ne Γ t -> False.
  Proof.
    rewrite /isConstruct_app.
    destruct decompose_app eqn:ht. cbn.
    destruct t0 => //. eapply decompose_app_inv in ht; subst.
    intros _ hne. now apply ne_tConstruct_app in hne.
  Qed.

  Lemma ne_nisConstruct_app Γ t : ne Γ t -> ~~ isConstruct_app t.
  Proof.
    rewrite /isConstruct_app.
    destruct decompose_app eqn:ht. cbn.
    destruct t0 => //. eapply decompose_app_inv in ht; subst.
    intros hne. now apply ne_tConstruct_app in hne.
  Qed.

  Lemma nf_no_red {cf : checker_flags} Γ t : wf Σ ->
    (ne Γ t -> (forall u, red1 Σ Γ t u -> False)) /\
    (nf Γ t -> (forall u, red1 Σ Γ t u -> False)).
  Proof.
    intros wfΣ.
    refine (ne_nf_ind_all (fun Γ t => forall u, red1 Σ Γ t u -> False) (fun Γ t => forall u, red1 Σ Γ t u -> False) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros; try solve [depelim X; solve_discr; eauto].
    - depelim X. congruence.
      solve_discr.
    - depelim X0. solve_discr. induction o. depelim X. intuition eauto. apply IHo. now depelim X.
    - depelim X; solve_discr. depelim H; solve_discr.
      destruct args using rev_case; solve_discr. noconf x.
      rewrite mkApps_app in x; noconf x.
      eapply ne_mkApps_inv in H as [H|[H|H]]; intuition eauto.
      now destruct H as [? [? []]].
      destruct H as [mfix' [idx' [d [arg []]]]]. noconf H. intuition eauto.
      rewrite /unfold_fix in e. rewrite H in e. noconf e. rewrite /is_constructor in e0. erewrite nth_error_app_left in e0; tea.
      now eapply isConstruct_app_ne in e0.
      eauto. eauto.
    - depelim X; solve_discr. unshelve eapply declared_constant_to_gen in isdecl; tea. rewrite /declared_constant_gen H in isdecl.
      noconf isdecl. congruence.
    - eapply red1_mkApps_tFix_inv in X1 as [[Hr|Hr]|Hr].
      * destruct Hr as [v' [-> a]]. eapply OnOne2_nth_error in a as [n [? [? []]]].
        eapply nth_error_all in X; tea. cbn in X. intuition eauto.
      * destruct Hr as [mfix' []]. subst u.
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
      * destruct Hr as [mfix' []]. subst.
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
      * rewrite /unfold_fix H /is_constructor H0. eapply ne_nisConstruct_app in H1.
        now move/negPf: H1.
    - depelim X4; solve_discr.
      * eapply isConstruct_app_ne in H => //.
        rewrite /isConstruct_app decompose_app_mkApps //.
      * now eapply ne_tCoFix_app in H.
      * eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
      * eauto.
      * eauto.
      * eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
    - depelim X; solve_discr; eauto.
      * now eapply ne_tCoFix_app in H.
      * eapply isConstruct_app_ne in H => //.
        rewrite /isConstruct_app decompose_app_mkApps //.
    - eauto.
    - eapply red1_mkApps_tCoFix_inv in X1 as [[]|].
      * destruct s as [v' [-> ?]].
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]]. intuition eauto.
      * destruct s as [mfix' [-> o]].
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]]. intuition eauto.
      * destruct s as [mfix' [-> o]].
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]]. intuition eauto.
  Qed.

  Lemma nf_red {cf : checker_flags} Γ t : wf Σ ->
    (ne Γ t -> (forall u, red Σ Γ t u -> u = t))
   /\ (nf Γ t -> (forall u, red Σ Γ t u -> u = t)).
  Proof.
    intros wfΣ. split.
    - intros ne u hu.
      induction hu. eapply (proj1 (nf_no_red _ _ _)) in r; eauto. reflexivity.
      specialize (IHhu1 ne). subst.
      specialize (IHhu2 ne). subst. reflexivity.
    - intros ne u hu.
      induction hu.
      eapply (proj2 (nf_no_red _ _ _)) in r; eauto. reflexivity.
      specialize (IHhu1 ne). subst.
      specialize (IHhu2 ne). subst. reflexivity.
  Qed.

End Normal.
