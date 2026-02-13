(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect Program Lia BinPos Compare_dec Bool.
From MetaRocq.Utils Require Import utils LibHypsNaming.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICSize PCUICInduction.
From Stdlib Require Import List.
From Equations Require Import Equations.
From Equations.Prop Require Import Subterm.
Import PCUICEnvTyping.



Definition def_depth_gen (depth : term -> nat) (x : def term)
  := max (depth (dtype x)) (depth (dbody x)).

Definition list_depth_gen {A} (depth : A -> nat) :=
  fix list_depth (l : list A) : nat :=
    match l with
    | [] => 0
    | a :: v => (max (depth a) (list_depth v))
    end.

Definition mfixpoint_depth_gen (depth : term -> nat) (l : mfixpoint term) :=
  list_depth_gen (def_depth_gen depth) l.

Definition decl_depth_gen (depth : term -> nat) (x : context_decl) :=
  max (depth (decl_type x)) (option_default depth (decl_body x) 0).

Definition context_depth_gen (depth : term -> nat) (l : context) :=
  list_depth_gen (decl_depth_gen depth) l.

Definition branch_depth_gen (depth : term -> nat) p (br : branch term) :=
  let pard := list_depth_gen depth p.(pparams) in
  let bctxd := context_depth_gen depth br.(bcontext) in
  max (pard + bctxd) (depth br.(bbody)).

Definition predicate_depth_gen (depth : term -> nat) (p : PCUICAst.predicate term) :=
  let pard := list_depth_gen depth p.(pparams) in
  let pctxd := context_depth_gen depth p.(pcontext) in
    max (pard + pctxd) (depth p.(preturn)).

Definition prim_depth_gen (depth : term -> nat) (p : prim_val) :=
  match p.π2 with
  | primArrayModel arr =>
    let vald := list_depth_gen depth arr.(array_value) in
    max (depth arr.(array_default)) (max (depth arr.(array_type)) vald)
  | _ => 1
  end.

Fixpoint depth t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_depth_gen depth args)
  | tLambda na T M => S (max (depth T) (depth M))
  | tApp u v => S (max (depth u) (depth v))
  | tProd na A B => S (max (depth A) (depth B))
  | tLetIn na b t b' => S (max (depth b) (max (depth t) (depth b')))
  | tCase ind p c brs => S (max (predicate_depth_gen depth p)
    (max (depth c) (list_depth_gen (branch_depth_gen depth p) brs)))
  | tProj p c => S (depth c)
  | tFix mfix idx => S (mfixpoint_depth_gen depth mfix)
  | tCoFix mfix idx => S (mfixpoint_depth_gen depth mfix)
  | tPrim p => S (prim_depth_gen depth p)
  | _ => 1
  end.

Notation context_depth := (context_depth_gen depth).
Notation list_depth := (list_depth_gen depth).
Notation mfixpoint_depth := (mfixpoint_depth_gen depth).
Notation prim_depth := (prim_depth_gen depth).

Lemma depth_mkApps f l : max (depth f) (list_depth l) <= depth (mkApps f l).
Proof.
  induction l in f |- *; simpl; try lia.
  specialize (IHl (tApp f a)).
  cbn -[max] in IHl.
  etransitivity; tea.
  lia.
Qed.

Lemma mfixpoint_depth_In {mfix d} :
  In d mfix ->
  depth (dbody d) <= mfixpoint_depth mfix /\
  depth (dtype d) <= mfixpoint_depth mfix.
Proof.
  induction mfix in d |- *; simpl; auto.
  move=> [->|H]. unfold def_depth_gen. split; try lia.
  destruct (IHmfix d H). split; lia.
Qed.

Lemma mfixpoint_depth_nth_error {mfix i d} :
  nth_error mfix i = Some d ->
  depth (dbody d) <= mfixpoint_depth mfix.
Proof.
  induction mfix in i, d |- *; destruct i; simpl; try congruence.
  move=> [] ->. unfold def_depth_gen. lia.
  move/IHmfix. lia.
Qed.

Lemma nth_error_depth {A} (f : A -> nat) {l : list A} {n x} :
  nth_error l n = Some x ->
  f x <= list_depth_gen f l.
Proof.
  induction l in n |- *; destruct n; simpl => //; auto.
  - intros [= <-]. lia.
  - intros hnth. specialize (IHl _ hnth). lia.
Qed.

Lemma map_depth_hom {A} {depth : A -> nat} {l : list A} {f : A -> A} :
  (forall x : A, depth (f x) = depth x) ->
  list_depth_gen depth (map f l) = list_depth_gen depth l.
Proof.
  intros Hf.
  revert l.
  fix aux 1. destruct l. simpl; auto. simpl.
  f_equal. apply Hf. apply aux.
Defined.

Lemma depth_lift n k t : depth (lift n k t) = depth t.
Proof.
  revert n k t.
  fix aux 3.
  destruct t; simpl; try rewrite map_depth_hom; try lia.
  all:try now rewrite !aux.
  all:try intros; auto.
  - destruct x. simpl. unfold branch_depth_gen; cbn.
    f_equal. apply aux.
  - f_equal. f_equal.
    rewrite /predicate_depth_gen /=. f_equal.
    f_equal. exact (map_depth_hom (aux n k)).
    apply aux.
    f_equal. apply aux.
    revert brs.
    fix aux' 1. destruct brs; simpl; trivial.
    f_equal. 2:apply aux'.
    rewrite /branch_depth_gen /=.
    f_equal. f_equal. apply (map_depth_hom (aux n k)).
  - unfold mfixpoint_depth_gen.
    f_equal.
    apply map_depth_hom. intros.
    simpl. destruct x. simpl. unfold def_depth_gen. simpl.
    f_equal; apply aux.
  - unfold mfixpoint_depth_gen.
    f_equal.
    apply map_depth_hom. intros.
    simpl. destruct x. simpl. unfold def_depth_gen. simpl.
    f_equal; apply aux.
  - f_equal. destruct prim as [? []]; cbn; auto.
    rewrite !aux map_depth_hom //.
Qed.

Lemma All_depth {s l} k :
  All (fun x => forall k, depth (subst s k x) <= depth x + list_depth s) l ->
  list_depth (map (subst s k) l) <= list_depth l + list_depth s.
Proof.
  intros a. revert k. induction a; simpl; auto; intros; try lia.
  specialize (p k); specialize (IHa k). lia.
Qed.

Lemma depth_subst s k t : depth (subst s k t) <= depth t + list_depth s.
Proof.
  induction t in k |- * using term_forall_list_ind; simpl; auto; try lia.
  - destruct Nat.leb. destruct nth_error eqn:hnth.
    eapply (nth_error_depth depth) in hnth.
    rewrite depth_lift. lia. simpl. lia.
    simpl. lia.
  - eapply (All_depth k) in X. lia.
  - specialize (IHt1 k); specialize (IHt2 (S k)); lia.
  - specialize (IHt1 k); specialize (IHt2 (S k)); lia.
  - specialize (IHt1 k); specialize (IHt2 k); specialize (IHt3 (S k)); lia.
  - specialize (IHt1 k); specialize (IHt2 k); lia.
  - destruct X as [? [? ?]].
    rewrite /predicate_depth_gen /=.
    eapply (All_depth k) in a.
    assert ((list_depth (map (subst s k) (pparams p)) +
        context_depth (pcontext p)) <=
      (list_depth (pparams p) + context_depth (pcontext p) + list_depth s)) by lia.
    specialize (IHt k).
    assert (list_depth_gen (branch_depth_gen depth (map_predicate_k id (subst s) k p)) (map_branches_k (subst s) id k l) <=
        (list_depth_gen (branch_depth_gen depth p) l) + list_depth s).
    { clear -a X0 k. induction X0; simpl; auto; try lia.
      destruct p0. specialize (l0 (#|bcontext x| + k)).
      rewrite {1 3}/branch_depth_gen /= /id. rewrite /id in IHX0. lia. }
    specialize (l0 (#|pcontext p| + k)).
    assert ((list_depth (map (subst s k) (pparams p)) + context_depth (pcontext p)) <=
      (list_depth (pparams p) + context_depth (pcontext p) + list_depth s)) by lia.
    lia.
  - specialize (IHt k). lia.
  - rewrite /mfixpoint_depth_gen. generalize #|m|.
    induction X in k |- *; simpl; auto; try lia.
    destruct p. intros n'.
    rewrite {1 3}/def_depth_gen /=.
    specialize (l0 k).
    specialize (l1 (n' + k)). simpl in l1.
    specialize (IHX k n'). lia.
  - rewrite /mfixpoint_depth_gen. generalize #|m|.
    induction X in k |- *; simpl; auto; try lia.
    destruct p. intros n'.
    rewrite {1 3}/def_depth_gen /=.
    specialize (l0 k).
    specialize (l1 (n' + k)). simpl in l1.
    specialize (IHX k n'). lia.
  - destruct p as [? []]; cbn in X; cbn; eauto; try lia.
    destruct X as [? []]. specialize (l k); specialize (l0 k).
    eapply (All_depth k) in a0. lia.
Qed.

Lemma depth_subst_instance u t : depth (subst_instance u t) = depth t.
Proof.
  revert t.
  fix aux 1.
  destruct t; simpl; try rewrite map_depth_hom; try lia; tas.
  all:try rewrite !aux //.
  - destruct x. simpl. unfold branch_depth_gen; cbn.
    f_equal. apply aux.
  - f_equal. f_equal.
    rewrite /predicate_depth_gen /=. f_equal.
    f_equal. exact (map_depth_hom aux).
    apply aux.
    f_equal. rewrite /branch_depth_gen /=.
    revert brs.
    fix aux' 1. destruct brs; simpl; auto.
    f_equal; auto. f_equal. f_equal. exact (map_depth_hom aux).
  - unfold mfixpoint_depth_gen.
    f_equal.
    apply map_depth_hom. intros.
    simpl. destruct x. simpl. unfold def_depth_gen. simpl.
    f_equal; apply aux.
  - unfold mfixpoint_depth_gen.
    f_equal.
    apply map_depth_hom. intros.
    simpl. destruct x. simpl. unfold def_depth_gen. simpl.
    f_equal; apply aux.
  - f_equal. destruct prim as [? []]; cbn; auto.
    rewrite !map_depth_hom // !aux //.
Qed.

Lemma depth_subst_decl s k d :
  decl_depth_gen depth (subst_decl s k d) <= decl_depth_gen depth d + list_depth s.
Proof.
  destruct d as [na [b|] ty]; rewrite /decl_depth_gen /=.
  pose proof (depth_subst s k ty).
  pose proof (depth_subst s k b). lia.
  pose proof (depth_subst s k ty). lia.
Qed.

Lemma depth_subst_context s k ctx :
  context_depth (subst_context s k ctx) <= context_depth ctx + list_depth s.
Proof.
  induction ctx; simpl; try lia.
  rewrite subst_context_snoc /=.
  pose proof (depth_subst_decl s (#|ctx| + k) a). lia.
Qed.

Lemma depth_subst_instance_context u (ctx : context) : context_depth (subst_instance u ctx) = context_depth ctx.
Proof.
  induction ctx; simpl; auto.
  rewrite IHctx. f_equal.
  rewrite /decl_depth_gen /=.
  destruct decl_body; rewrite /= !depth_subst_instance //.
Qed.

(*Lemma list_depth_mapi_context_hom (depth : context_decl -> nat) (l : context) (f : nat -> term -> term) :
  (forall k x, depth (map_decl (f k) x) = depth x) ->
  list_depth_gen depth (mapi_context f l) = list_depth_gen depth l.
Proof.
  intros.
  revert l.
  fix auxl' 1.
  destruct l; simpl. reflexivity.
  f_equal. f_equal. apply H. apply auxl'.
Defined.*)

Definition onctx_rel (P : context -> term -> Type) (Γ Δ : context) :=
  All_local_env (PCUICInduction.on_local_decl (fun Δ => P (Γ ,,,  Δ))) Δ.

Definition CasePredProp (P : context -> term -> Type) Γ (p : predicate term) :=
  All (P Γ) p.(pparams) × onctx_rel P Γ (inst_case_context p.(pparams) p.(puinst) p.(pcontext)) ×
  P (Γ ,,, inst_case_context p.(pparams) p.(puinst) p.(pcontext)) p.(preturn).

Definition CaseBrsProp p P Γ (brs : list (branch term)) :=
  All (fun x : branch term => onctx_rel P Γ (inst_case_context p.(pparams) p.(puinst) x.(bcontext))
     * P (Γ ,,, inst_case_context p.(pparams) p.(puinst) x.(bcontext)) (bbody x)) brs.

Lemma list_depth_app {A} (depth : A -> nat) (l l' : list A) :
  list_depth_gen depth (l ++ l') = max (list_depth_gen depth l) (list_depth_gen depth l').
Proof.
  induction l; simpl; auto.
  rewrite IHl. lia.
Qed.

Lemma In_list_depth {A : Type} (f : A -> nat) :
  forall x xs, In x xs -> f x < S (list_depth_gen f xs).
Proof.
  intros. induction xs.
  destruct H.
  * destruct H. simpl; subst. lia.
    specialize (IHxs H). simpl. lia.
Qed.

Lemma list_depth_rev {A} (depth : A -> nat) (l : list A) :
  list_depth_gen depth (rev l) = list_depth_gen depth l.
Proof.
  induction l using rev_ind; simpl; auto; try lia.
  rewrite rev_app_distr /= list_depth_app /=. lia.
Qed.

Lemma list_depth_mapi_rec_le {A B} (l : list A) (f : nat -> A -> B) k
  (depthA : A -> nat) (depthB : B -> nat) :
  (forall i x, depthB (f i x) <= depthA x) ->
  list_depth_gen depthB (mapi_rec f l k) <= list_depth_gen depthA l.
Proof.
  intro H. induction l in k |- *. reflexivity.
  simpl. specialize (H k a). specialize (IHl (S k)). lia.
Qed.

Lemma context_depth_inst_case_context pars puinst pctx :
  context_depth (inst_case_context pars puinst pctx) <=
  context_depth pctx + list_depth pars.
Proof.
  rewrite /inst_case_context.
  rewrite -list_depth_rev.
  etransitivity; [eapply depth_subst_context|].
  now rewrite depth_subst_instance_context.
Qed.

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
    (forall Γ (t u : term),
      (forall t', depth t' < depth (tApp t u) -> P Γ t') ->
      P Γ t -> P Γ u -> P Γ (tApp t u)) ->
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
        All_local_env (PCUICInduction.on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (PCUICInduction.on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
    (forall Γ p, tPrimProp (P Γ) p -> P Γ (tPrim p)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros ????????????????? Γ t.
  revert Γ t. set(foo:=CoreTactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt depth); unfold MR in *; simpl. clear H1.
  assert (auxl : forall Γ {A} (l : list A) (f : A -> term),
    list_depth_gen (fun x => depth (f x)) l < depth pr0 ->
    All (fun x => P Γ (f x)) l).
  { induction l; try solve [constructor].
    move=> f /= Hdepth.
    constructor.
    * eapply aux => //. red. lia.
    * apply IHl => //. lia. }
  assert (forall mfix, context_depth (fix_context mfix) <= mfixpoint_depth_gen depth mfix).
  { induction mfix. simpl. auto. simpl. unfold fix_context.
    unfold context_depth.
    rewrite /context_depth list_depth_rev /=. cbn.
    rewrite depth_lift. unfold context_depth in IHmfix.
    epose (list_depth_mapi_rec_le mfix
                                 (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) 1
                                 (def_depth_gen depth) (decl_depth_gen depth)).
    forward l. intros. destruct x; cbn; rewrite depth_lift. lia.
    rewrite /mfixpoint_depth_gen {1}/def_depth_gen. lia. }
  assert (auxΓ : forall Γ Δ,
             context_depth Δ < depth pr0 ->
             onctx_rel P Γ Δ).
  { move=> Γ Δ.
    induction Δ; cbn.
    - constructor.
    - case: a => [na [b|] ty] /=;
      rewrite {1}/decl_depth_gen /context_depth_gen /= => Hlt; constructor; auto.
      + eapply IHΔ => //. unfold context_depth. lia.
      + split.
        * apply aux => //. red. lia.
        * apply aux => //. cbn. lia.
      + apply IHΔ => //; unfold context_depth; lia.
      + split => //. apply aux => //. cbn. lia. }
  assert (forall m, list_depth_gen (fun x : def term => depth (dtype x)) m < S (mfixpoint_depth_gen depth m)).
  { clear. unfold mfixpoint_depth_gen, def_depth_gen. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_depth_gen (fun x : def term => depth (dbody x)) m < S (mfixpoint_depth_gen depth m)).
  { clear. unfold mfixpoint_depth_gen, def_depth_gen. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top. move auxΓ at top.

  destruct pr0; eauto;
    (move: pr2=> /= /and3P [pr20 pr21 pr22] || move: pr2 => /= /andP [pr20 pr21] || idtac);
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); auto; red; simpl; try lia]
        end.

  - eapply X10; eauto.
    * red. split.
      + eapply auxl; auto. simpl. unfold predicate_depth_gen, branch_depth_gen.
        now change (fun x => depth x) with depth; lia.
      + split.
        ++ apply auxΓ. simpl. unfold predicate_depth_gen.
          pose proof (context_depth_inst_case_context p.(pparams) p.(puinst) p.(pcontext)). lia.
        ++ eapply aux; auto. simpl. unfold predicate_depth_gen. lia.
    * eapply aux => //. simpl; lia.
    * red. simpl in aux.
      have auxbr := fun Γ t (H : depth t <= list_depth_gen (branch_depth_gen depth p) brs) =>
        aux Γ t ltac:(lia).
      move: auxbr.
      clear -auxΓ.
      induction brs. simpl. constructor.
      constructor. simpl in auxbr.
      + split. eapply auxΓ. simpl.
        unfold branch_depth_gen at 1. rewrite /predicate_depth_gen /=.
        pose proof (context_depth_inst_case_context p.(pparams) p.(puinst) a.(bcontext)).
        lia.
        eapply auxbr. unfold branch_depth_gen. lia.
      + eapply IHbrs. intros. apply auxΓ. simpl in *. lia.
        intros. apply auxbr. simpl. lia.
  - eapply X12; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X13; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X14.
    destruct prim as [? []]; cbn => //.
    split; [apply aux; red; cbn; lia|].
    split; [apply aux; red; cbn; lia|].
    apply auxl; cbn. change (fun x => depth x) with depth; lia.
Defined.

Definition CasePredProp_depth (P : term -> Type) (p : predicate term) :=
  All P p.(pparams) × onctx P (inst_case_context p.(pparams) p.(puinst) p.(pcontext)) ×
  P p.(preturn).

Definition CaseBrsProp_depth p (P : term -> Type) (brs : list (branch term)) :=
  All (fun x : branch term => onctx P (inst_case_context p.(pparams) p.(puinst) x.(bcontext))
     * P (bbody x)) brs.

Lemma term_ind_depth_app :
  forall (P : term -> Type),
    (forall (n : nat), P (tRel n)) ->
    (forall (i : ident), P (tVar i)) ->
    (forall (n : nat) (l : list term), All (P) l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall (t u : term),
      (forall t', depth t' < depth (tApp t u) -> P t') ->
      P t -> P u -> P (tApp t u)) ->
    (forall s (u : Instance.t), P (tConst s u)) ->
    (forall (i : inductive) (u : Instance.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : Instance.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (p : predicate term) (t : term) (brs : list (branch term)),
        CasePredProp_depth P p ->
        P t ->
        CaseBrsProp_depth p P brs ->
        P (tCase ci p t brs)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat),
        onctx P (fix_context m) ->
        tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat),
        onctx P (fix_context m) ->
        tFixProp P P m -> P (tCoFix m n)) ->
    (forall p, tPrimProp P p -> P (tPrim p)) ->
    forall (t : term), P t.
Proof.
  intros ????????????????? t.
  revert t. set(foo:=CoreTactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt depth); unfold MR in *; simpl. clear H0.
  assert (auxl : forall {A} (l : list A) (f : A -> term),
    list_depth_gen (fun x => depth (f x)) l < depth pr1 ->
    All (fun x => P (f x)) l).
  { induction l; try solve [constructor].
    move=> f /= Hdepth.
    constructor.
    * eapply aux => //. red. lia.
    * apply IHl => //. lia. }
  assert (forall mfix, context_depth (fix_context mfix) <= mfixpoint_depth_gen depth mfix).
  { induction mfix. simpl. auto. simpl. unfold fix_context.
    unfold context_depth.
    rewrite /context_depth list_depth_rev /=. cbn.
    rewrite depth_lift. unfold context_depth in IHmfix.
    epose (list_depth_mapi_rec_le mfix
                                 (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) 1
                                 (def_depth_gen depth) (decl_depth_gen depth)).
    forward l. intros. destruct x; cbn; rewrite depth_lift. lia.
    rewrite /mfixpoint_depth_gen {1}/def_depth_gen. lia. }
  assert (auxΓ : forall Δ,
             context_depth Δ < depth pr1 ->
             onctx P Δ).
  { move=> Γ h.
    induction Γ; cbn.
    - constructor.
    - move: a h => [na bo ty] /=.
      rewrite {1}/decl_depth_gen /context_depth_gen /= => Hlt; constructor; auto.
      2: apply IHΓ => //; unfold context_depth; lia.
      split.
      + destruct bo => //. cbn in Hlt.
        apply aux => //. cbn. lia.
      + apply aux => //. cbn. lia. }
  assert (forall m, list_depth_gen (fun x : def term => depth (dtype x)) m < S (mfixpoint_depth_gen depth m)).
  { clear. unfold mfixpoint_depth_gen, def_depth_gen. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_depth_gen (fun x : def term => depth (dbody x)) m < S (mfixpoint_depth_gen depth m)).
  { clear. unfold mfixpoint_depth_gen, def_depth_gen. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top. move auxΓ at top.

  destruct pr1; eauto;
    (move: pr2=> /= /and3P [pr20 pr21 pr22] || move: pr2 => /= /andP [pr20 pr21] || idtac);
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); auto; red; simpl; try lia]
        end.

  - eapply X10; eauto.
    * red. split.
      + eapply auxl; auto. simpl. unfold predicate_depth_gen, branch_depth_gen.
        now change (fun x => depth x) with depth; lia.
      + split.
        ++ apply auxΓ. simpl. unfold predicate_depth_gen.
          pose proof (context_depth_inst_case_context p.(pparams) p.(puinst) p.(pcontext)). lia.
        ++ eapply aux; auto. simpl. unfold predicate_depth_gen. lia.
    * eapply aux => //. simpl; lia.
    * red. simpl in aux.
      have auxbr := fun t (H : depth t <= list_depth_gen (branch_depth_gen depth p) brs) =>
        aux t ltac:(lia).
      move: auxbr.
      clear -auxΓ.
      induction brs. simpl. constructor.
      constructor. simpl in auxbr.
      + split. eapply auxΓ. simpl.
        unfold branch_depth_gen at 1. rewrite /predicate_depth_gen /=.
        pose proof (context_depth_inst_case_context p.(pparams) p.(puinst) a.(bcontext)).
        lia.
        eapply auxbr. unfold branch_depth_gen. lia.
      + eapply IHbrs. intros. apply auxΓ. simpl in *. lia.
        intros. apply auxbr. simpl. lia.
  - eapply X12; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X13; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X14; cbn. destruct prim as [? []]; cbn => //.
    do 2 (split; [eapply aux; cbn; lia|]).
    eapply auxl. change (fun x => depth x) with depth. cbn. lia.
Defined.
