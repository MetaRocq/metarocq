(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils MRList.
From MetaRocq.Common Require Import config Environment Reflect.
From MetaRocq.Template Require Import Ast AstUtils LiftSubst UnivSubst WfAst TypingWf Typing.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Rocq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Rocq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)


Local Ltac inv H := inversion H; subst.

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction. *)

(** We use a different substitution function that requires no lifting as it assumes
  we are substituting closed terms. *)

Fixpoint csubst t k u :=
  match u with
  | tRel n =>
     match Nat.compare k n with
    | Datatypes.Eq => t
    | Gt => tRel n
    | Lt => tRel (Nat.pred n)
    end
  | tEvar ev args => tEvar ev (List.map (csubst t k) args)
  | tLambda na T M => tLambda na (csubst t k T) (csubst t (S k) M)
  | tApp u v => mkApps (csubst t k u) (map (csubst t k) v)
  | tProd na A B => tProd na (csubst t k A) (csubst t (S k) B)
  | tLetIn na b ty b' => tLetIn na (csubst t k b) (csubst t k ty) (csubst t (S k) b')
  | tCase ind p c brs =>
    let k' := #|pcontext p| + k in
    let brs' := map_branches_k (csubst t) k brs in
    tCase ind (map_predicate id (csubst t k) (csubst t k') p) (csubst t k c) brs'
  | tProj p c => tProj p (csubst t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k) (csubst t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k) (csubst t k')) mfix in
    tCoFix mfix' idx
  | tCast c kd c' => tCast (csubst t k c) kd (csubst t k c')
  | tArray l v d ty => tArray l (List.map (csubst t k) v) (csubst t k d) (csubst t k ty)
  | x => x
  end.

Definition substl defs body : term :=
  fold_left (fun bod term => csubst term 0 bod)
    defs body.

Definition cunfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cunfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    Some (d.(rarg), substl (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition atom t :=
  match t with
  | tInd _ _
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _
  | tLambda _ _ _
  | tSort _
  | tProd _ _ _
  | tInt _
  | tFloat _ => true
  | _ => false
  end.

Definition isArityHead t :=
  match t with
  | tSort _
  | tProd _ _ _ => true
  | _ => false
  end.

Definition isEvar t :=
  match t with
  | tEvar _ _ => true
  | _ => false
  end.

Definition isFix t :=
  match t with
  | tFix _ _ => true
  | _ => false
  end.

Definition isFixApp t :=
  match fst (decompose_app t) with
  | tFix _ _ => true
  | _ => false
  end.

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition isPrim t :=
  match t with
  | tInt _ | tFloat _ | tArray _ _ _ _ => true
  | _ => false
  end.

Definition isConstructApp t := isConstruct (decompose_app t).1.

Definition isAssRel (Γ : context) x :=
  match x with
  | tRel i =>
    match option_map decl_body (nth_error Γ i) with
    | Some None => true
    | _ => false
    end
  | _ => false
  end.

Definition isAxiom Σ x :=
  match x with
  | tConst c u =>
    match lookup_env Σ c with
    | Some (ConstantDecl {| cst_body := None |}) => true
    | _ => false
    end
  | _ => false
  end.

Definition isStuckFix t (args : list term) :=
  match t with
  | tFix mfix idx =>
    match cunfold_fix mfix idx with
    | Some (narg, fn) =>
      #|args| <? narg
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. rewrite -AstUtils.mkApp_mkApps in H.
  unfold mkApp in H. destruct (mkApps f l); discriminate.
Qed.

Definition cstr_arity mdecl cdecl :=
  (mdecl.(ind_npars) + context_assumptions cdecl.(cstr_args))%nat.

Section Wcbv.

  Context (Σ : global_env).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' l res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval (mkApps (csubst a' 0 b) l) res ->
      eval (tApp f (a :: l)) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 t b1) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance u body) res ->
      eval (tConst c u) res

  (** Case *)
  | eval_iota ci mdecl idecl cdecl discr c u args p brs br res :
      eval discr (mkApps (tConstruct ci.(ci_ind) c u) args) ->
      nth_error brs c = Some br ->
      declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
      let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
      #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
      eval (iota_red ci.(ci_npar) args bctx br) res ->
      eval (tCase ci p discr brs) res

  (** Proj *)
  | eval_proj proj discr args u a res mdecl idecl cdecl pdecl :
      declared_projection Σ proj mdecl idecl cdecl pdecl ->
      eval discr (mkApps (tConstruct proj.(proj_ind) 0 u) args) ->
      #|args| = cstr_arity mdecl cdecl ->
      nth_error args (proj.(proj_npars) + proj.(proj_arg)) = Some a ->
      eval a res ->
      eval (tProj proj discr) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx fixargsv args argsv narg fn res :
      ~~ isApp f ->
      eval f (mkApps (tFix mfix idx) fixargsv) ->
      All2 eval args argsv ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      #|fixargsv| < narg < #|fixargsv| + #|args| ->
      eval (mkApps fn (fixargsv ++ argsv)) res ->
      eval (mkApps f args) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx fixargsv args argsv narg fn :
      ~~ isApp f ->
      eval f (mkApps (tFix mfix idx) fixargsv) ->
      All2 eval args argsv ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      #|fixargsv ++ argsv| <= narg ->
      eval (mkApps f args) (mkApps (tFix mfix idx) (fixargsv ++ argsv))


  (** CoFix-case unfolding *)
  | eval_cofix_case ip mfix idx p discr args narg fn brs res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval discr (mkApps (tCoFix mfix idx) args) ->
      eval (tCase ip p (mkApps fn args) brs) res ->
      eval (tCase ip p discr brs) res

  (** CoFix-proj unfolding *)
  | eval_cofix_proj p mfix idx discr args narg fn res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval discr (mkApps (tCoFix mfix idx) args) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p discr) res

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct ind c u mdecl idecl cdecl f args args' :
    declared_constructor Σ (ind, c) mdecl idecl cdecl ->
    ~~ isApp f -> args <> [] ->
    eval f (tConstruct ind c u) ->
    #|args| <= cstr_arity mdecl cdecl ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tConstruct ind c u) args')

  (** Non redex-producing heads applied to values are values *)
  | eval_app_cong f f' a a' :
      ~~ isApp f -> a <> [] -> (* This ensures eval only applies to well-formed terms *)
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isArityHead f' || isConstructApp f' || isPrim f') ->
      All2 eval a a' ->
      eval (tApp f a) (mkApps f' a')

  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)

  | eval_tArray u v v' def def' ty :
    eval def def' ->
    All2 eval v v' ->
    eval (tArray u v def ty) (tArray u v' def' ty)

  (** Atoms are values (includes abstractions, cofixpoints and constructors
      along with type constructors) *)
  | eval_atom t : atom t -> eval t t.
  Derive Signature for eval.

  (* Scheme Minimality for eval Sort Type. *)
  Definition eval_evals_ind :
    forall P : term -> term -> Type,
      (forall (f : term) (na : aname) t b a a' l res,
          eval f (tLambda na t b) ->
          P f (tLambda na t b) -> eval a a' -> P a a' ->
          eval (mkApps (csubst a' 0 b) l) res -> P (mkApps (csubst a' 0 b) l) res ->
          P (tApp f (a :: l)) res) ->
      (forall (na : aname) (b0 b0' t b1 res : term),
          eval b0 b0' -> P b0 b0' ->
          eval (csubst b0' 0 b1) res ->
          P (csubst b0' 0 b1) res -> P (tLetIn na b0 t b1) res) ->
      (forall c (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall (u : Instance.t) (res : term),
            cst_body decl = Some body ->
            eval (subst_instance u body) res -> P (subst_instance u body) res -> P (tConst c u) res) ->
      (forall ci mdecl idecl cdecl (discr : term) (c : nat) (u : Instance.t)
              (args : list term) (p : predicate term) (brs : list (branch term)) br (res : term),
          let ind := ci.(ci_ind) in
          let npar := ci.(ci_npar) in
          eval discr (mkApps (tConstruct ind c u) args) ->
          P discr (mkApps (tConstruct ind c u) args) ->
          nth_error brs c = Some br ->
          declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
          let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
          #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
          eval (iota_red npar args bctx br) res -> P (iota_red npar args bctx br) res ->
          P (tCase ci p discr brs) res) ->
      (forall proj (discr : term) (args : list term) (u : Instance.t)
              a mdecl idecl cdecl pdecl res,
          declared_projection Σ proj mdecl idecl cdecl pdecl ->
          eval discr (mkApps (tConstruct proj.(proj_ind) 0 u) args) ->
          P discr (mkApps (tConstruct proj.(proj_ind) 0 u) args) ->
          #|args| = cstr_arity mdecl cdecl ->
          nth_error args (proj.(proj_npars) + proj.(proj_arg)) = Some a ->
          eval a res ->
          P a res ->
          P (tProj proj discr) res) ->
      (forall (f : term) (mfix : mfixpoint term) (idx : nat) (fixargsv args argsv : list term)
             (narg : nat) (fn res : term),
        ~~ isApp f ->
        eval f (mkApps (tFix mfix idx) fixargsv) ->
        P f (mkApps (tFix mfix idx) fixargsv) ->
        All2 eval args argsv ->
        All2 P args argsv ->
        cunfold_fix mfix idx = Some (narg, fn) ->
        #|fixargsv| < narg < #|fixargsv| + #|args| ->
        eval (mkApps fn (fixargsv ++ argsv)) res ->
        P (mkApps fn (fixargsv ++ argsv)) res ->
        P (mkApps f args) res) ->
      (forall (f : term) (mfix : mfixpoint term) (idx : nat) (fixargsv args argsv : list term)
              (narg : nat) (fn : term),
          ~~ isApp f ->
          eval f (mkApps (tFix mfix idx) fixargsv) ->
          P f (mkApps (tFix mfix idx) fixargsv) ->
          All2 eval args argsv ->
          All2 P args argsv ->
          cunfold_fix mfix idx = Some (narg, fn) ->
          #|fixargsv ++ argsv| <= narg ->
          P (mkApps f args) (mkApps (tFix mfix idx) (fixargsv ++ argsv))) ->
      (forall (ip : case_info) (mfix : mfixpoint term) (idx : nat)
        (p : predicate term) discr (args : list term)
        (narg : nat) (fn : term) (brs : list (branch term)) (res : term),
          cunfold_cofix mfix idx = Some (narg, fn) ->
          eval discr (mkApps (tCoFix mfix idx) args) ->
          P discr (mkApps (tCoFix mfix idx) args) ->
          eval (tCase ip p (mkApps fn args) brs) res ->
          P (tCase ip p (mkApps fn args) brs) res -> P (tCase ip p discr brs) res) ->
      (forall (p : projection) (mfix : mfixpoint term) (idx : nat) discr (args : list term) (narg : nat) (fn res : term),
          cunfold_cofix mfix idx = Some (narg, fn) ->
          eval discr (mkApps (tCoFix mfix idx) args) ->
          P discr (mkApps (tCoFix mfix idx) args) ->
          eval (tProj p (mkApps fn args)) res ->
          P (tProj p (mkApps fn args)) res -> P (tProj p discr) res) ->

      (forall ind c u mdecl idecl cdecl f args args',
          declared_constructor Σ (ind, c) mdecl idecl cdecl ->
          ~~ isApp f -> args <> [] ->
          eval f (tConstruct ind c u) ->
          P f (tConstruct ind c u) ->
          #|args| <= cstr_arity mdecl cdecl ->
          All2 eval args args' ->
          All2 P args args' ->
          P (mkApps f args) (mkApps (tConstruct ind c u) args')) ->

      (forall f f' a a',
          ~~ isApp f -> a <> [] ->
          eval f f' -> P f f' ->
          ~~ (isLambda f' || isFixApp f' || isArityHead f' || isConstructApp f' || isPrim f') ->
          All2 eval a a' -> All2 P a a' -> P (tApp f a) (mkApps f' a')) ->

      (forall u v v' def def' ty,
          eval def def' -> P def def' ->
          All2 eval v v' -> All2 P v v' ->
          P (tArray u v def ty) (tArray u v' def' ty)) ->
      (forall t : term, atom t -> P t t) ->

      forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbeta Hlet Hcst Hcase Hproj Hfix Hstuckfix Hcofixcase Hcofixproj Happcstr Happcong Harr Hatom.
    fix eval_evals_ind 3. destruct 1;
             try solve [match goal with [ H : _ |- _ ] =>
                             match type of H with
                               forall t t0, eval t t0 -> _ => fail 1
                             | _ => eapply H
                             end end; eauto].
    - eauto.
    - eauto.
    - eapply Hfix; eauto.
      clear -a eval_evals_ind.
      revert args argsv a.
      fix aux 3; destruct 1; constructor; auto.
    - eapply Hstuckfix; eauto.
      clear -a eval_evals_ind.
      revert args argsv a.
      fix aux 3; destruct 1; constructor; auto.
    - eapply Happcstr; eauto. clear l n.
      revert args args' a. fix aux 3; destruct 1; constructor; auto.
    - eapply Happcong; auto. clear i0 n.
      revert a a' a0. fix aux 3; destruct 1; constructor; auto.
    - eapply Harr; eauto.
      exact (map_All2 eval_evals_ind a).
  Defined.

  (** Characterization of values for this reduction relation.
      Only constructors, cofixpoints and stuck fixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments.

      This ensures that constructors cannot be overapplied.

   *)

  Variant value_head (nargs : nat) : term -> Type :=
  | value_head_cstr ind c u mdecl idecl cdecl :
    declared_constructor Σ (ind, c) mdecl idecl cdecl ->
    nargs <= cstr_arity mdecl cdecl ->
    value_head nargs (tConstruct ind c u)
  | value_head_cofix mfix idx : value_head nargs (tCoFix mfix idx)
  | value_head_ind ind u : value_head nargs (tInd ind u)
  | value_head_fix mfix idx rarg fn :
    cunfold_fix mfix idx = Some (rarg, fn) ->
    nargs <= rarg ->
    value_head nargs (tFix mfix idx).
  Derive Signature NoConfusion for value_head.

  Inductive atomic_value (value : term -> Type) : term -> Type :=
  | atomic_atom t : atom t -> atomic_value value t
  | atomic_array u v def ty : All value v -> value def -> atomic_value value (tArray u v def ty).
  Derive Signature NoConfusion for atomic_value.

  Inductive value : term -> Type :=
  | value_atom t : atomic_value value t -> value t
  | value_app f args : value_head #|args| f -> args <> [] -> All value args -> value (mkApps f args).
  Derive Signature for value.

  Abbreviation atomic := (atomic_value value).

  Lemma value_values_ind : forall P : term -> Type,
      (forall t, atom t -> P t) ->
      (forall u v def ty, All value v -> All P v -> value def -> P def -> P (tArray u v def ty)) ->
      (forall f args, value_head #|args| f -> args <> [] -> All value args -> All P args -> P (mkApps f args)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P ???.
    fix value_values_ind 2. destruct 1.
    - destruct a.
      * apply X; auto.
      * apply X0; eauto. eapply make_All_All; tea.
    - eapply X1; auto; tea. eapply make_All_All; tea.
  Defined.

  Lemma value_head_nApp {nargs t} : value_head nargs t -> ~~ isApp t.
  Proof using Type. destruct 1; auto. Qed.
  Hint Resolve value_head_nApp : core.

  Lemma isStuckfix_nApp {t args} : isStuckFix t args -> ~~ isApp t.
  Proof using Type. destruct t; auto. Qed.
  Hint Resolve isStuckfix_nApp : core.

  Lemma atom_nApp {t} : atom t -> ~~ isApp t.
  Proof using Type. destruct t; auto. Qed.
  Hint Resolve atom_nApp : core.

  Lemma value_mkApps_inv t l :
    ~~ isApp t ->
    value (mkApps t l) ->
    ((l = []) × atomic t) +
    ([× l <> [], value_head #|l| t & All value l]).
  Proof using Type.
    intros H H'. generalize_eq x (mkApps t l).
    revert t H. induction H' using value_values_ind.
    intros. subst.
    - eapply atom_mkApps in H.
      left. intuition auto. now constructor.
    - intros. left. destruct l using rev_case; cbn in H0. subst t.
      split => //. constructor 2; auto. solve_discr'. elim (app_tip_nil l x). congruence.
    - intros * isapp appeq. move: (value_head_nApp X) => Ht.
      right.
      apply mkApps_eq_inj in appeq => //. intuition subst; auto => //.
  Qed.

  Lemma value_mkApps_values t l :
    value (mkApps t l) ->
    ~~ isApp t ->
    All value l.
  Proof using Type.
    intros val not_app.
    now apply value_mkApps_inv in val as [(-> & ?)|[]].
  Qed.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma isFixApp_mkApps f args : ~~ isApp f -> isFixApp (mkApps f args) = isFixApp f.
  Proof using Type.
    move=> Hf.
    rewrite /isFixApp !decompose_app_mkApps // /=.
    change f with (mkApps f []) at 2.
    rewrite !decompose_app_mkApps // /=.
  Qed.

  Lemma isConstructApp_mkApps f args : ~~ isApp f -> isConstructApp (mkApps f args) = isConstructApp f.
  Proof using Type.
    move=> Hf.
    rewrite /isConstructApp !decompose_app_mkApps // /=.
    change f with (mkApps f []) at 2.
    rewrite !decompose_app_mkApps // /=.
  Qed.

  Lemma is_nil {A} (l : list A) : (l = []) + (l <> []).
  Proof using Type.
    destruct l; intuition congruence.
  Qed.

  Lemma All2_nil {A} {P} {l l' : list A} : All2 P l l' -> l <> [] -> l' <> [].
  Proof using Type.
    induction 1; congruence.
  Qed.

  Lemma All2_nil_rev {A} {P} {l l' : list A} : All2 P l l' -> l' <> [] -> l <> [].
  Proof using Type.
    induction 1; congruence.
  Qed.

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof using Type.
    intros eve. induction eve using eval_evals_ind; simpl; intros; auto using value.

    - apply All2_right in X0.
      destruct (is_nil (fixargsv ++ argsv)).
      { rewrite e /=. now apply value_atom; constructor. }
      eapply value_app => //.
      + econstructor; tea.
      + apply All_app_inv => //.
        now eapply value_mkApps_values.

    - apply All2_right in X0.
      eapply value_app; auto.
      econstructor; tea. rewrite -(All2_length X) //.
      now eapply All2_nil.

    - eapply All2_right in X0.
      depelim IHeve.
      destruct t; simpl in * |- *; try depelim a0; cbn in *; try congruence;
        try solve [eapply value_app => //; [now constructor|now eapply All2_nil]].
      rewrite -mkApps_app. eapply value_app.
      rewrite !negb_or in H1.
      pose proof (value_head_nApp v).
      rewrite isConstructApp_mkApps // isFixApp_mkApps // in H1.
      destruct v.
      * rewrite /isConstructApp /= in H1. rtoProp; intuition auto.
      * constructor.
      * constructor => //.
      * rewrite /isFixApp /= in H1. rtoProp; intuition auto.
      * eapply All2_nil in X; tea. destruct args; cbn; congruence.
      * eapply All_app_inv; tea.
    - eapply All2_right in X0. constructor. constructor 2; auto.
    - now do 2 constructor.
  Qed.

  Lemma value_head_spec n t :
    value_head n t -> (~~ (isLambda t || isArityHead t)).
  Proof using Type.
    now destruct 1; simpl.
  Qed.

  Lemma value_head_final n t :
    value_head n t -> eval t t.
  Proof using Type.
    destruct 1.
    - now constructor.
    - now eapply eval_atom.
    - now eapply eval_atom.
    - now eapply eval_atom.
  Qed.

  Lemma value_final e : value e -> eval e e.
  Proof using Type.
    induction 1 using value_values_ind; simpl; auto using value.
    - now constructor.
    - constructor; eauto. eapply All_All2; tea; eauto.
    - assert (All2 eval args args).
      { clear -X1; induction X1; constructor; auto. }
      destruct X.
      * eapply eval_construct; tea => //.
        now constructor.
      * rewrite -{1}mkApps_tApp => //. destruct args => //.
        eapply eval_app_cong => //.
        now constructor.
      * rewrite -{1}mkApps_tApp => //. destruct args => //.
        eapply eval_app_cong => //.
        now constructor.
      * eapply eval_fix_value with (fixargsv := []). 4:tea. auto.
        now constructor. exact X2. now cbn.
  Qed.

  Lemma eval_atom_inj t t' : atom t -> eval t t' -> t = t'.
  Proof using Type.
    intros Ha H; depind H; try solve_discr'; try now easy.
    - eapply atom_mkApps in Ha; intuition subst.
      depelim a.
      apply atom_mkApps in H2 as (-> & ?).
      cbn in *. lia.

    - eapply atom_mkApps in Ha; intuition subst.
      depelim a.
      apply atom_mkApps in H1 as (-> & ?).
      cbn in *. reflexivity.

    - eapply atom_mkApps in Ha as [-> ato].
      rewrite (IHeval ato).
      now depelim a.
  Qed.

  Lemma eval_to_stuck_fix_inv mfix idx narg fn t args :
    cunfold_fix mfix idx = Some (narg, fn) ->
    eval t (mkApps (tFix mfix idx) args) ->
    args = [] \/ #|args| <= narg.
  Proof using Type.
    intros uf ev.
    apply eval_to_value in ev.
    apply value_mkApps_inv in ev as [(-> & ?)|[eqargs vh eva]]; try easy.
    depelim vh. rewrite uf in e. noconf e. intuition auto.
  Qed.

  Lemma eval_LetIn {n b ty t v} :
    eval (tLetIn n b ty t) v ->
    ∑ b',
      eval b b' * eval (csubst b' 0 t) v.
  Proof using Type.
    intros H; depind H; try solve_discr'; try now easy.
    - depelim a.
      eapply eval_to_stuck_fix_inv in H; [|easy].
      exfalso. destruct H; subst; cbn in *; lia.

    - depelim a.
      now rewrite app_nil_r.
  Qed.

  Lemma eval_Const {c u v} :
    eval (tConst c u) v ->
    ∑ decl, declared_constant Σ c decl *
                 match cst_body decl with
                 | Some body => eval (subst_instance u body) v
                 | None => False
                 end.
  Proof using Type.
    intros H; depind H; try solve_discr'; try now easy.
    - exists decl. intuition auto. now rewrite e.
    - depelim a.
      eapply eval_to_stuck_fix_inv in H; [|easy].
      exfalso. destruct H; subst; cbn in *; lia.
    - depelim a.
      apply IHeval.
      now rewrite app_nil_r.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    ~~ isApp f ->
    eval f f' ->
    value_head #|l| f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof using Type.
    revert l'. induction l using rev_ind; intros l' appf evf vf' evl.
    depelim evl. intros. eapply evf.
    eapply All2_app_inv_l in evl as [? [? [? ?]]].
    intuition auto. subst. depelim b. depelim b.
    cbn in vf'; destruct vf'.
    - eapply eval_construct; tea. apply app_tip_nil. now eapply All2_app.
    - rewrite -mkApps_tApp => //. rewrite is_empty_app /= andb_false_r //.
      eapply eval_app_cong; auto.
      eapply All2_app; auto.
    - rewrite -mkApps_tApp => //. rewrite is_empty_app /= andb_false_r //.
      eapply eval_app_cong; auto.
      eapply All2_app; auto.
    - eapply eval_fix_value with (fixargsv := []) (argsv := x0 ++ [y]). 4:tea.
      all: move=> //.
      eapply All2_app; auto. cbn. len. len in l0. cbn in l0.
      now rewrite -(All2_length a).
  Qed.

End Wcbv.
