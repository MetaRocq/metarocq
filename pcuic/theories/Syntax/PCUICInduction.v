(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect Program Lia BinPos Compare_dec Bool.
From MetaRocq.Utils Require Import utils LibHypsNaming.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICSize.
From Stdlib Require Import List.
From Equations Require Import Equations.
From Equations.Prop Require Import Subterm.

Set Asymmetric Patterns.
Import PCUICEnvTyping.

(** Derive the well-founded subterm relation for terms. Not so useful
  yet as it doesn't go throught lists.
  *)
(* Derive Subterm for term. *)

(** * Deriving a compact induction principle for terms

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t u : term, P t -> P u -> P (tApp t u)) ->
    (forall s (u : Instance.t), P (tConst s u)) ->
    (forall (i : inductive) (u : Instance.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : Instance.t), P (tConstruct i n u)) ->
    (forall (ind : case_info) (p : predicate term),
        tCasePredProp P P p -> forall c : term, P c -> forall l : list (branch term),
        tCaseBrsProp P l -> P (tCase ind p c l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall p, tPrimProp P p -> P (tPrim p)) ->
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  * revert l.
    fix auxl' 1.
    destruct l; constructor; [|apply auxl'].
    apply auxt.
  * split.
    generalize (pparams p).
    fix auxl' 1.
    destruct l; constructor; [|apply auxl']. apply auxt.
    split.
    + generalize (pcontext p).
      fix auxc 1.
      destruct l; constructor; [|apply auxc].
      destruct c. split. 2: apply auxt.
      simpl. destruct decl_body; simpl. apply auxt. constructor.
    + apply auxt.

  * revert brs.
    fix auxl' 1.
    destruct brs; constructor; [|apply auxl'].
    split.
    + generalize (bcontext b).
      fix auxc 1.
      destruct l; constructor; [|apply auxc].
      destruct c. split. 2: apply auxt.
      simpl. destruct decl_body; simpl. apply auxt. constructor.
    + apply auxt.

  * revert mfix.
    fix auxm 1.
    destruct mfix; constructor; [|apply auxm].
    split; apply auxt.
  * revert mfix.
    fix auxm 1.
    destruct mfix; constructor; [|apply auxm].
    split; apply auxt.

  * destruct prim. destruct p; cbn; intuition auto.
    destruct a. cbn.
    revert array_value.
    fix auxm 1; destruct array_value; constructor; [|apply auxm].
    apply auxt.
Defined.

Lemma size_decompose_app_rec t L :
  list_size size L + size t = size (decompose_app_rec t L).1 + list_size size (decompose_app_rec t L).2.
Proof.
  induction t in L |- *; cbn; try lia.
  rewrite <- IHt1. cbn. lia.
Qed.

Lemma size_decompose_app t :
  size t = size (decompose_app t).1 + list_size size (decompose_app t).2.
Proof.
  unfold decompose_app.
  eapply (size_decompose_app_rec t []).
Qed.

Lemma decompose_app_rec_length_mono t L1 L2 :
  length L1 <= length L2 ->
  length (decompose_app_rec t L1).2 <= length (decompose_app_rec t L2).2.
Proof.
  intros. induction t in L1, L2, H |- *; cbn; try lia.
  eapply IHt1. cbn. lia.
Qed.

Lemma decompose_app_rec_length t L :
  length (decompose_app_rec t L).2 >= length L.
Proof.
  induction t in L |- * ; cbn; try lia.
  unfold ge. etransitivity. eapply IHt1.
  eapply decompose_app_rec_length_mono. cbn. lia.
Qed.

Lemma decompose_app_size_tApp1 t1 t2 :
  size (decompose_app (tApp t1 t2)).1 < size (tApp t1 t2).
Proof.
  rewrite -> size_decompose_app with (t := tApp t1 t2). cbn.
  pose proof (decompose_app_rec_length t1 [t2]). cbn in H.
  pose proof (list_size_length size (decompose_app_rec t1 [t2]).2).
  lia.
Qed.

Lemma decompose_app_size_tApp2 t1 t2 :
  Forall (fun t => size t < size (tApp t1 t2)) (decompose_app (tApp t1 t2)).2.
Proof.
  destruct decompose_app eqn:da.
  eapply decompose_app_inv in da. rewrite da. simpl. clear da.
  induction l using rev_ind; try constructor.
  eapply app_Forall; [|constructor].
  eapply Forall_impl; eauto; simpl; intros.
  rewrite mkApps_app; simpl. lia.
  rewrite mkApps_app; simpl. lia.
  constructor.
Qed.

Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Defined.

Definition mkApps_decompose_app t :
  t = mkApps  (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].

  Section Reverse_Induction.

    Variable A : Type.
    Set Suggest Proof Using.

    Lemma rev_list_ind : forall P:list A-> Type,
      P [] ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
    Proof.
      induction l; auto.
    Defined.

    Let app_nil_r : forall l:list A, l ++ [] = l.
    Proof.
      induction l; simpl; f_equal; auto.
    Defined.

    Let app_assoc : forall l m n:list A, l ++ m ++ n = (l ++ m) ++ n.
    Proof.
      intros l m n; induction l; simpl; f_equal; auto.
    Defined.

    Let rev_app_distr : forall x y:list A, rev (x ++ y) = rev y ++ rev x.
    Proof.
      induction x as [| a l IHl].
      destruct y as [| a l].
      simpl.
      auto.

      simpl.
      rewrite app_nil_r; auto.

      intro y.
      simpl.
      rewrite -> (IHl y).
      rewrite app_assoc; trivial.
    Defined.

    Let rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
    Proof.
      intros.
      apply (rev_app_distr l [a]); simpl; auto.
    Defined.

    Let rev_involutive : forall l:list A, rev (rev l) = l.
    Proof.
      induction l as [| a l IHl].
      simpl; auto.

      simpl.
      rewrite (rev_unit (rev l) a).
      rewrite IHl; auto.
    Defined.

    Theorem rev_rec : forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros.
      generalize (rev_involutive l).
      intros E; rewrite <- E.
      apply (rev_list_ind P).
      - auto.
      - simpl.
        intros.
        apply (X0 a (rev l0)).
        auto.
    Defined.

  End Reverse_Induction.

From Equations Require Import Equations.

Lemma liftP_ctx_ind (P : term -> Type) (ctx : context) :
  (forall y, size y < context_size size ctx -> P y) ->
  All (ondecl P) ctx.
Proof.
  induction ctx; simpl; constructor; auto.
  * split.
    + destruct decl_body eqn:db; cbn. apply X; unfold decl_size.
      rewrite db; simpl; lia. exact tt.
    + apply X; cbn. unfold decl_size. simpl. lia.
  * apply IHctx; intros; apply X. lia.
Qed.

Lemma term_forall_mkApps_ind :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, forall v, ~ isApp t -> P t -> v <> [] -> All P v -> P (mkApps t v)) ->
    (forall (s : kername) (u : Instance.t), P (tConst s u)) ->
    (forall (i : inductive) (u : Instance.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : Instance.t), P (tConstruct i n u)) ->
    (forall (ind : case_info) (p : predicate term),
        tCasePredProp P P p ->
        forall c : term, P c -> forall l : list (branch term),
            tCaseBrsProp P l -> P (tCase ind p c l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall p, tPrimProp P p -> P (tPrim p)) ->
    forall t : term, P t.
Proof.
  intros until t.
  rename X14 into Pprim.
  assert (Acc (MR lt size) t) by eapply measure_wf, Wf_nat.lt_wf.
  induction H. rename X14 into auxt. clear H. rename x into t.
  move auxt at top.

  destruct t; try now repeat (match goal with
                 H : _ |- _ => apply H; try (hnf; cbn; lia)
              end).

  - eapply X1. revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. apply auxt. hnf; cbn; lia. apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. lia.

  - rewrite -> mkApps_decompose_app.
    destruct decompose_app eqn:E. cbn.
    eapply X6.
    + eapply decompose_app_notApp in E. eauto.
    + eapply auxt. cbn. hnf. pose proof (decompose_app_size_tApp1 t1 t2).
      rewrite E in H. hnf in *; cbn in *. lia.
    + intros ->.
      rewrite /decompose_app /= in E.
      pose proof (decompose_app_rec_notApp _ _ _ _ E).
      eapply decompose_app_rec_inv in E. simpl in *. subst t => //.
    + induction l using rev_rec in E, auxt, t1, t2, t |- *.
      * constructor.
      * eapply All_app_inv.
        2:{
        econstructor. eapply auxt. hnf; cbn.
        pose proof (decompose_app_size_tApp2 t1 t2). rewrite E in H. cbn in H. clear E.
        eapply Forall_All, All_app in H as [H H1]. inv H1. lia. econstructor. }
        destruct (isApp t1) eqn:Et1.
        -- destruct t1; try now inv Et1.
           pose proof E as E'.
           eapply IHl.
           2:{
           eapply decompose_app_inv in E. rewrite mkApps_app in E.
           cbn in E. noconf E. rewrite -> H.
           rewrite -> decompose_app_mkApps. reflexivity.
           eapply decompose_app_notApp in E'.
           now rewrite E'. }
           eapply decompose_app_inv in E. rewrite mkApps_app in E.
           cbn in E. noconf E.
           intros. eapply auxt.
           red. red in H0. cbn in *. lia.
        -- destruct l.
           econstructor.
           exfalso.
           pose proof (decompose_app_mkApps t1 [t2]). cbn in H.
           cbn in E. rewrite -> H in E.
           inversion E. destruct l; inv H3.
           now rewrite Et1.
  - eapply X10; [|apply auxt; hnf; cbn; lia.. | ].
    repeat split; [| |apply auxt; hnf; cbn; unfold predicate_size; lia].
    * unfold MR in auxt. simpl in auxt. revert auxt. unfold predicate_size.
      generalize (pparams p).
      fix auxt' 1.
      destruct l; constructor. apply auxt. hnf; cbn; lia. apply auxt'. intros. apply auxt.
      hnf in *; cbn in *. lia.
    * eapply liftP_ctx_ind. intros. apply auxt. red. simpl. unfold predicate_size. lia.
    * rename brs into l.
      revert l auxt. unfold MR; cbn. unfold branch_size. fix auxt' 1.
      destruct l; constructor. split; [|apply auxt; hnf; cbn; lia].
      + apply liftP_ctx_ind; intros. apply auxt; red; simpl; lia.
      + apply auxt'. intros. apply auxt.
      hnf in *; cbn in *. lia.
  - eapply X12; [apply auxt; hnf; cbn; lia.. | ]. rename mfix into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. split.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. unfold mfixpoint_size, def_size in *. lia.

  - eapply X13; [apply auxt; hnf; cbn; lia.. | ]. rename mfix into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. split.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. unfold mfixpoint_size, def_size in *. lia.

  - eapply Pprim.
    destruct prim. destruct p; cbn; intuition auto.
    * eapply auxt. red. cbn. lia.
    * eapply auxt. red. cbn. lia.
    * destruct a; cbn in *. unfold MR in auxt; cbn in auxt. clear -auxt array_value.
      revert array_value auxt.
      fix auxt' 1; destruct array_value; constructor => //.
      eapply auxt. cbn. lia. eapply auxt'. intros ? ?; eapply auxt. cbn; lia.
Defined.

Lemma liftP_ctx (P : term -> Type) :
  (forall t, P t) ->
  (forall ctx, All (ondecl P) ctx).
Proof.
  induction ctx; simpl; constructor; auto.
  split.
  + destruct decl_body eqn:db; cbn. apply X; unfold decl_size.
    exact tt.
  + apply X; cbn.
Qed.

Lemma ctx_length_ind (P : context -> Type) (p0 : P [])
  (pS : forall d Γ, (forall Γ', #|Γ'| <= #|Γ| -> P Γ') -> P (d :: Γ))
  Γ : P Γ.
Proof.
  generalize (le_n #|Γ|).
  generalize #|Γ| at 2.
  induction n in Γ |- *.
  destruct Γ; [|simpl; intros; exfalso; lia].
  intros. apply p0.
  intros.
  destruct Γ; simpl in *.
  apply p0. apply pS. intros. apply IHn. simpl. lia.
Qed.

Lemma ctx_length_rev_ind (P : context -> Type) (p0 : P [])
  (pS : forall d Γ, (forall Γ', #|Γ'| <= #|Γ|  -> P Γ') -> P (Γ ++ [d]))
  Γ : P Γ.
Proof.
  generalize (le_n #|Γ|).
  generalize #|Γ| at 2.
  induction n in Γ |- *.
  destruct Γ using MRList.rev_ind; [|simpl; rewrite length_app; simpl; intros; exfalso; try lia].
  intros. apply p0.
  destruct Γ using MRList.rev_ind; simpl in *; rewrite ?length_app; simpl; intros Hlen.
  intros. apply p0.
  apply pS. intros. apply IHn. simpl. lia.
Qed.

Lemma list_size_mapi_context_hom (size : context_decl -> nat) (l : context) (f : nat -> term -> term) :
  (forall k x, size (map_decl (f k) x) = size x) ->
  list_size size (mapi_context f l) = list_size size l.
Proof.
  intros.
  revert l.
  fix auxl' 1.
  destruct l; simpl. reflexivity.
  f_equal. f_equal. apply H. apply auxl'.
Defined.

Lemma decl_size_map_decl_hom (size : term -> nat) (d : context_decl) (f : term -> term) :
  (forall x, size (f x) = size x) ->
  decl_size size (map_decl f d) = decl_size size d.
Proof.
  intros.
  rewrite /map_decl /decl_size /=; destruct d as [na [b|] ty]; simpl;
  f_equal; auto.
Defined.

Lemma size_lift n k t : size (lift n k t) = size t.
Proof.
  revert n k t.
  fix size_lift 3.
  destruct t; simpl; rewrite ?list_size_map_hom; try lia.
  all:try now rewrite !size_lift.
  all:try intros; auto.
  - destruct x. simpl. unfold branch_size; cbn.
    f_equal.
    symmetry.
    apply size_lift.
  - f_equal. f_equal. f_equal.
    unfold predicate_size; cbn.
    2:apply size_lift.
    f_equal; [|apply size_lift].
    f_equal. cbn.
    apply list_size_map_hom. intros. symmetry; auto.
  - unfold mfixpoint_size.
    f_equal.
    apply list_size_map_hom. intros.
    simpl. destruct x. simpl. unfold def_size. simpl.
    f_equal; symmetry; apply size_lift.
  - unfold mfixpoint_size.
    f_equal.
    apply list_size_map_hom. intros.
    simpl. destruct x. simpl. unfold def_size. simpl.
    f_equal; symmetry; apply size_lift.
  - destruct prim. destruct p; cbn => //. unfold prim_size. simp map_prim => /=.
    rewrite !size_lift. rewrite list_size_map_hom; auto.
Qed.

Definition on_local_decl (P : context -> term -> Type) := lift_wf_term1 P.

(* TODO: remove List.rev *)
Lemma list_size_rev {A} size (l : list A)
  : list_size size (List.rev l) = list_size size l.
Proof.
  induction l; simpl. reflexivity.
  rewrite list_size_app IHl; cbn; lia.
Qed.

Definition onctx_rel (P : context -> term -> Type) (Γ Δ : context) :=
  All_local_env (on_local_decl (fun Δ => P (Γ ,,,  Δ))) Δ.

Definition CasePredProp (P : context -> term -> Type) Γ (p : predicate term) :=
  All (P Γ) p.(pparams) × onctx_rel P Γ (pcontext p) ×
  P (Γ ,,, inst_case_context p.(pparams) p.(puinst) p.(pcontext)) p.(preturn).

Definition CaseBrsProp p P Γ (brs : list (branch term)) :=
  All (fun x : branch term => onctx_rel P Γ (bcontext x) * P (Γ ,,, inst_case_context p.(pparams) p.(puinst)
    x.(bcontext)) (bbody x)) brs.

Lemma term_forall_ctx_list_ind :
  forall (P : context -> term -> Type),
    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : aname) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : aname) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : aname) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n t t0 :: Γ) t1 -> P Γ (tLetIn n t t0 t1)) ->
    (forall Γ (t u : term), P Γ t -> P Γ u -> P Γ (tApp t u)) ->
    (forall Γ s (u : Instance.t), P Γ (tConst s u)) ->
    (forall Γ (i : inductive) (u : Instance.t), P Γ (tInd i u)) ->
    (forall Γ (i : inductive) (n : nat) (u : Instance.t), P Γ (tConstruct i n u)) ->
    (forall Γ (ci : case_info) (p : predicate term) (t : term) (brs : list (branch term)),
        CasePredProp P Γ p ->
        P Γ t ->
        CaseBrsProp p P Γ brs ->
        P Γ (tCase ci p t brs)) ->
    (forall Γ (s : projection) (t : term), P Γ t -> P Γ (tProj s t)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
    (forall Γ p, tPrimProp (P Γ) p -> P Γ (tPrim p)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros ????????????????? Γ t.
  revert Γ t. set(foo:=CoreTactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size); unfold MR in *; simpl. clear H1.
  assert (auxl : forall Γ {A} (l : list A) (f : A -> term),
    list_size (fun x => size (f x)) l < size pr0 ->
    All (fun x => P Γ (f x)) l).
  { induction l; try solve [constructor].
    move=> f /= Hsize.
    constructor.
    * eapply aux => //. red. lia.
    * apply IHl => //. lia. }
  assert (forall mfix, context_size size (fix_context mfix) <= mfixpoint_size size mfix).
  { induction mfix. simpl. auto. simpl. unfold fix_context.
    unfold context_size.
    rewrite list_size_rev /=. cbn.
    rewrite size_lift. unfold context_size in IHmfix.
    epose (list_size_mapi_rec_le (def_size size) (decl_size size) mfix
                                 (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) 1).
    forward l. intros. destruct x; cbn; rewrite size_lift. lia.
    unfold def_size, mfixpoint_size. lia. }
  assert (auxΓ : forall Γ Δ,
             context_size size Δ < size pr0 ->
             onctx_rel P Γ Δ).
  { move=> Γ Δ.
    induction Δ; cbn.
    - constructor.
    - case: a => [na [b|] ty] /=;
      rewrite {1}/decl_size /context_size /= => Hlt; constructor; auto.
      + eapply IHΔ => //. unfold context_size. lia.
      + split.
        * apply aux => //. red. lia.
        * apply aux => //. cbn. lia.
      + apply IHΔ => //; unfold context_size; lia.
      + split => //. apply aux => //. cbn. lia. }
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top. move auxΓ at top.

  destruct pr0; eauto;
    (move: pr2=> /= /and3P [pr20 pr21 pr22] || move: pr2 => /= /andP [pr20 pr21] || idtac);
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); auto; red; simpl; try lia]
        end.

  - eapply X10; eauto.
    * red. split.
      + eapply auxl; auto. simpl. unfold predicate_size, branch_size.
        now change (fun x => size x) with size; lia.
      + split.
        ++ apply auxΓ. simpl. unfold predicate_size. lia.
        ++ eapply aux; auto. simpl. unfold predicate_size. lia.
    * eapply aux => //. simpl; lia.
    * red. simpl in aux.
      have auxbr := fun Γ t (H : size t <= list_size (branch_size size) brs) =>
        aux Γ t ltac:(lia).
      move: auxbr.
      clear -auxΓ.
      induction brs. simpl. constructor.
      constructor. simpl in auxbr.
      + split. eapply auxΓ. simpl. unfold branch_size. lia.
        eapply auxbr. unfold branch_size. lia.
      + eapply IHbrs. intros. apply auxΓ. simpl in *. lia.
        intros. apply auxbr. simpl. lia.
  - eapply X12; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X13; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X14.
    destruct prim. destruct p; cbn; intuition auto; destruct a; cbn in *.
    * eapply aux. cbn. lia.
    * eapply aux. cbn. lia.
    * eapply (auxl _ _ array_value id). unfold id.
      change (fun x => size x) with size. lia.
Defined.

(** This induction principle gives a general induction hypothesis for applications,
    allowing to apply the induction to their head or any smaller term. *)
Lemma term_ind_size_app :
  forall (P : term -> Type),
    (forall (n : nat), P (tRel n)) ->
    (forall (i : ident), P (tVar i)) ->
    (forall (n : nat) (l : list term), All (P) l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 ->
                                                   P (tLetIn n t t0 t1)) ->
    (forall (t u : term),
        (forall t', size t' < size (tApp t u) -> P t') ->
        P t -> P u -> P (tApp t u)) ->
    (forall s (u : Instance.t), P (tConst s u)) ->
    (forall (i : inductive) (u : Instance.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : Instance.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (p : PCUICAst.predicate term) (c : term) (brs : list (branch term)),
        tCasePredProp P P p -> P c ->
        tCaseBrsProp P brs -> P (tCase ci p c brs)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp (P) P m -> P (tCoFix m n)) ->
    (forall p, tPrimProp P p -> P (tPrim p)) ->
    forall (t : term), P t.
Proof.
  intros.
  revert t. set(foo:=CoreTactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size); unfold MR in *; simpl. clear H0.
  assert (auxl : forall {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr1 ->
                                                            All (fun x => P (f x)) l).
  { induction l; constructor. eapply aux. red. simpl in H. lia. apply IHl. simpl in H. lia. }
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top.

  !destruct pr1; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  * eapply X10. 2:{ apply aux; simpl. simpl; lia. }
    repeat split.
    + revert aux; simpl; unfold predicate_size.
      induction (pparams hh0); constructor; auto.
      apply aux. simpl. lia.
      apply IHl; intros. apply aux; simpl; lia.
    + revert aux; simpl; unfold predicate_size.
      induction (pcontext hh0); constructor; auto.
      destruct a as [na [b|] ty]; constructor; simpl;
      try (apply aux; cbn; lia). exact tt.
      apply IHl; intros. apply aux; simpl; lia.
    + apply aux; simpl. unfold predicate_size. lia.
    + red.
      revert aux; simpl.
      clear.
      induction hh1; simpl; constructor; auto.
      revert aux. unfold branch_size.
      induction (bcontext a); split; try constructor; auto.
      apply aux. lia.
      destruct a0 as [na [b|] ty]; constructor; simpl;
      try (apply aux; cbn; lia). exact tt.
      apply IHl; intros. apply aux; simpl; lia.
      apply aux. lia.
      apply IHhh1. intros. apply aux. lia.

  * eapply X12; try (apply aux; red; simpl; lia).
    red. apply All_pair. split; apply auxl; simpl; auto.

  * eapply X13; try (apply aux; red; simpl; lia).
    red. apply All_pair. split; apply auxl; simpl; auto.

  * eapply X14.
    destruct hh, p; cbn; intuition auto.
    1-2:(eapply aux; cbn; lia).
    eapply (auxl _ (array_value a) id).
    change (fun x => size (id x)) with size. cbn; lia.
Defined.
