(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import Ast AstUtils Induction UnivSubst.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

(** * Well-formedness of terms and types in typing derivations

  The internal representation of terms is not canonical, so we show
  that only well-formed terms and types can appear in typing derivations
  and the global context.

  The invariants are:
  - Application nodes have always at least one argument, and they cannot
    be nested (keeping terms in "spine" representation).
  - Each `Case` refers to a declared inductive in the environment, and
    the predicate context and branches contexts have lengths that match
    the inductive declaration. This eases the proof of translation to PCUIC,
    in particular reduction on well-formed terms in Template translate to
    reductions in PCUIC, without further typing assumptions.
*)

(** Well-formed terms: invariants which are not ensured by the OCaml type system *)

Notation wf_nactx :=
  (All2 (fun x y => eq_binder_annot x (decl_name y))).

Inductive wf {Σ} : term -> Type :=
| wf_tRel n : wf (tRel n)
| wf_tVar id : wf (tVar id)
| wf_tEvar n l : All wf l -> wf (tEvar n l)
| wf_tSort u : wf (tSort u)
| wf_tCast t k t' : wf t -> wf t' -> wf (tCast t k t')
| wf_tProd na t b : wf t -> wf b -> wf (tProd na t b)
| wf_tLambda na t b : wf t -> wf b -> wf (tLambda na t b)
| wf_tLetIn na t b b' : wf t -> wf b -> wf b' -> wf (tLetIn na t b b')
| wf_tApp t u : isApp t = false -> u <> nil -> wf t -> All wf u -> wf (tApp t u)
| wf_tConst k u : wf (tConst k u)
| wf_tInd i u : wf (tInd i u)
| wf_tConstruct i k u : wf (tConstruct i k u)
| wf_tCase ci p c brs mdecl idecl :
    declared_inductive Σ ci.(ci_ind) mdecl idecl ->
    ci.(ci_npar) = mdecl.(ind_npars) ->
    wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
    #|pparams p| = context_assumptions (ind_params mdecl) ->
    All wf (pparams p) -> wf (preturn p) ->
    wf c ->
    All2 (fun cdecl br =>
      wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl) ×
      wf (bbody br)) idecl.(ind_ctors) brs ->
    wf (tCase ci p c brs)
| wf_tProj p t :
  wf t ->
  wf (tProj p t)
| wf_tFix mfix k : All (fun def => wf def.(dtype) × wf def.(dbody)) mfix ->
                   wf (tFix mfix k)
| wf_tCoFix mfix k : All (fun def => wf def.(dtype) × wf def.(dbody)) mfix -> wf (tCoFix mfix k)
| wf_tInt i : wf (tInt i)
| wf_tFloat f : wf (tFloat f)
| wf_tString s : wf (tString s)
| wf_tArray u arr def ty : All wf arr -> wf def -> wf ty -> wf (tArray u arr def ty).
Arguments wf : clear implicits.
Derive Signature for wf.

(** * Inversion lemmas for the well-formedness judgement *)

Definition wf_Inv Σ (t : term) : Type :=
  match t with
  | tRel _ | tVar _ | tSort _ => unit
  | tInt _ | tFloat _ | tString _ => unit
  | tArray u arr def ty => All (wf Σ) arr * wf Σ def * wf Σ ty
  | tEvar n l => All (wf Σ) l
  | tCast t k t' => wf Σ t * wf Σ t'
  | tProd na t b => wf Σ t * wf Σ b
  | tLambda na t b => wf Σ t * wf Σ b
  | tLetIn na t b b' => wf Σ t * wf Σ b * wf Σ b'
  | tApp t u => (isApp t = false) * (u <> nil) * wf Σ t * All (wf Σ) u
  | tConst c _ => unit
  | tInd ind _ => unit
  | tConstruct ind k _ => unit
  | tCase ci p c brs =>
    ∑ mdecl idecl,
    [× declared_inductive Σ ci.(ci_ind) mdecl idecl,
       ci.(ci_npar) = mdecl.(ind_npars),
       wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl),
       #|pparams p| = context_assumptions (ind_params mdecl),
       All (wf Σ) (pparams p),
       wf Σ (preturn p),
       wf Σ c &
       All2 (fun cdecl br =>
         wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl) ×
        wf Σ (bbody br)) idecl.(ind_ctors) brs]
  | tProj p t => wf Σ t
  | tFix mfix k => All (fun def => wf Σ def.(dtype) * wf Σ def.(dbody)) mfix
  | tCoFix mfix k => All (fun def => wf Σ def.(dtype) * wf Σ def.(dbody)) mfix
  end.

Lemma wf_inv {Σ t} (w : wf Σ t) : wf_Inv Σ t.
Proof.
  induction w; simpl; eauto; intuition eauto; try constructor.
Defined.

Lemma lift_to_list Σ (P : term -> Prop) : (forall t, wf Σ t -> P t) -> forall l, All (wf Σ) l -> Forall P l.
Proof.
  intros IH.
  fix lift_to_list 1.
  destruct l; constructor.
  apply IH. now inversion_clear X.
  apply lift_to_list. now inversion_clear X.
Defined.

Lemma lift_to_wf_list Σ (P : term -> Type) : forall l, All (fun t => wf Σ t -> P t) l ->
  All (wf Σ) l -> All P l.
Proof.
  induction 1. constructor.
  inversion_clear 1.
  constructor; auto.
Qed.

Ltac inv H := inversion_clear H.

Lemma term_wf_forall_list_ind Σ :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall t : term, P t -> forall (c : cast_kind) (t0 : term), P t0 -> P (tCast t c t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, isApp t = false -> wf Σ t -> P t ->
                      forall l : list term, l <> nil -> All (wf Σ) l -> All P l -> P (tApp t l)) ->
    (forall s (u : Instance.t), P (tConst s u)) ->
    (forall (i : inductive) (u : Instance.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : Instance.t),
      P (tConstruct i n u)) ->
    (forall (ci : case_info) (p : predicate term) mdecl idecl,
        declared_inductive Σ ci.(ci_ind) mdecl idecl ->
        ci.(ci_npar) = mdecl.(ind_npars) ->
        #|pparams p| = context_assumptions (ind_params mdecl) ->
        wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
        tCasePredProp P P p -> forall t : term, P t -> forall l : list (branch term),
        All2 (fun cdecl br =>
          wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl) ×
          P (bbody br)) idecl.(ind_ctors) l -> P (tCase ci p t l)) ->
    (forall (s : projection) (t : term),

      P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall i, P (tInt i)) ->
    (forall f, P (tFloat f)) ->
    (forall s, P (tString s)) ->
    (forall u arr def ty, All P arr -> P def -> P ty ->  P (tArray u arr def ty)) ->
    forall t : term, wf Σ t -> P t.
Proof.
  intros P H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 Harr.
  intros until t. revert t.
  apply (term_forall_list_rect (fun t => wf Σ t -> P t));
    intros; try solve [match goal with
                 H : _ |- _ => apply H
              end; auto].
  - apply H4. inv X0.
    eauto using lift_to_wf_list.

  - inv X1; auto.
  - inv X1; auto.
  - inv X1; auto.
  - inv X2; auto.
  - inv X1; auto.
    apply H10; auto.
    eauto using lift_to_wf_list.

  - destruct X.
    inv X2; eapply H14; eauto.
    + split; auto. solve_all.
    + red in X1. solve_all.

  - inv X0; auto.

  - inv X0; auto.
    apply H16. red. red in X. solve_all.
  - inv X0; auto.
    apply H17. red. red in X. solve_all.
  - inv X2; auto. eapply Harr; eauto using lift_to_wf_list.
Qed.

Definition wf_decl Σ d := option_default (wf Σ) (decl_body d) unit × wf Σ (decl_type d).

Definition wf_decl_pred Σ : context -> judgment -> Type :=
  (fun _ j => option_default (wf Σ) (j_term j) unit × wf Σ (j_typ j)).

Lemma wf_mkApp Σ u a : wf Σ u -> wf Σ a -> wf Σ (mkApp u a).
Proof.
  intros H H'.
  inversion_clear H; try constructor; simpl; auto; try congruence; try constructor; auto.
  solve_all.
  apply All_app_inv; auto. all:econstructor; eauto.
Qed.

Lemma wf_mkApps Σ u a : wf Σ u -> All (wf Σ) a -> wf Σ (mkApps u a).
Proof.
  intros H H'.
  induction a; simpl; auto.
  inversion_clear H; try constructor; simpl; auto; try congruence; try constructor; auto.
  intro. destruct u0; simpl in *; congruence.
  solve_all. apply All_app_inv; auto.
  all:econstructor; eauto.
Qed.

Lemma lift_isApp n k t : isApp t = false -> isApp (lift n k t) = false.
Proof.
  induction t; auto.
Qed.

#[export] Hint Resolve lift_isApp : all.

Lemma wf_lift Σ n k t : wf Σ t -> wf Σ (lift n k t).
Proof.
  intros wft; revert t wft k.
  apply (term_wf_forall_list_ind Σ (fun t => forall k, wf Σ (lift n k t)));
    intros; try cbn; econstructor; simpl; eauto; try solve [solve_all].
    destruct l; cbn in *. auto. discriminate. now rewrite length_map.
Qed.
From Stdlib Require Import PeanoNat.
Import Nat.

Lemma wf_subst Σ ts k u : All (wf Σ) ts -> wf Σ u -> wf Σ (subst ts k u).
Proof.
  intros wfts wfu.
  induction wfu in k using term_wf_forall_list_ind; simpl; intros; try econstructor; cbn in *; eauto;
    solve_all.

  - unfold subst. destruct (leb_spec_Set k n).
    destruct nth_error eqn:Heq. apply (nth_error_all Heq) in wfts.
    apply wf_lift; auto. constructor. constructor.
  - apply wf_mkApps; auto. solve_all.
  - now rewrite length_map.
Qed.

Lemma wf_subst1 Σ t k u : wf Σ t -> wf Σ u -> wf Σ (subst1 t k u).
Proof.
  intros wft wfu. apply wf_subst. constructor; auto. auto.
Qed.

#[export] Hint Resolve wf_mkApps wf_subst wf_subst1 wf_lift : wf.


Lemma wf_strip_outer_cast Σ t : WfAst.wf Σ t -> WfAst.wf Σ (strip_outer_cast t).
Proof.
  induction t; auto.
  simpl. intros H; now inv H.
Qed.

Lemma wf_mkApps_napp Σ t u : ~~ isApp t -> WfAst.wf Σ (mkApps t u) -> WfAst.wf Σ t * All (WfAst.wf Σ) u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros Happ H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t0 (u ++ [a]))).
    forward IHu.
    induction u; trivial. discriminate.
Qed.
#[export] Hint Resolve wf_mkApps_napp : wf.

Lemma wf_mkApps_inv Σ t u : WfAst.wf Σ (mkApps t u) -> All (WfAst.wf Σ) u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t0 (args ++ [a]))).
    forward IHu.
    induction u; trivial.
    simpl. rewrite <- app_assoc. simpl. apply H.
    intuition. inv H.
    now apply All_app in X0.
Qed.
#[export] Hint Resolve wf_mkApps_inv : wf.
#[export] Hint Constructors WfAst.wf : wf.

Lemma isLambda_isApp t : isLambda t = true -> ~~ isApp t.
Proof. destruct t; simpl; congruence. Qed.


Lemma wf_subst_instance Σ u c :
  wf Σ c -> wf Σ (subst_instance u c).
Proof.
  induction 1 using term_wf_forall_list_ind; simpl; try solve [ cbn; constructor; auto using All_map; solve_all ].
  - cbn. constructor; auto. destruct t0; simpl in *; try congruence.
    destruct l; simpl in *; congruence.
    now apply All_map.
  - cbn; econstructor; eauto; simpl; solve_all.
    now rewrite length_map.
Qed.

Lemma wf_nth Σ:
  forall (n : nat) (args : list term), All (wf Σ) args -> wf Σ (nth n args tDummy).
Proof.
  intros n args H. induction H in n; destruct n; simpl; try constructor; auto.
Qed.
#[export] Hint Resolve wf_nth : core.
