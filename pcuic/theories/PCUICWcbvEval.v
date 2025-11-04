(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses.
From MetaRocq.Common Require Import config.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICGlobalEnv PCUICReduction PCUICClosed PCUICCSubst
     PCUICClosedTyp PCUICEtaExpand. (* Due to reliance on wf Σ instead of closed_env Σ *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Rocq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction theorem that can be applied to Rocq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)


Local Ltac inv H := inversion H; subst.

Lemma nApp_mkApps t f args :
  t = mkApps f args -> ~~ isApp t -> t = f /\ args = [].
Proof.
  intros -> napp.
  destruct args using rev_case; cbn in *; solve_discr; try discriminate => //. split => //.
  now rewrite mkApps_app /= in napp.
Qed.

Ltac solve_discr :=
  try progress (prepare_discr; finish_discr; cbn[mkApps] in * );
  try match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  | H : ?t = mkApps ?f ?l |- _ =>
    (change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H) ||
    (eapply nApp_mkApps in H as [? ?]; [|easy]; subst)
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  end.

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Definition atom t :=
  match t with
  | tInd _ _
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _
  | tLambda _ _ _
  | tSort _
  | tProd _ _ _ => true
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

Definition isFixApp t := isFix (head t).

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isInd t :=
  match t with
  | tInd _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition isPrim t :=
  match t with
  | tPrim _ => true
  | _ => false
  end.

Definition isPrimApp t := isPrim (head t).

Definition isConstructApp t := isConstruct (head t).

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

Definition isStuckFix t (args : list term) :=
  match t with
  | tFix mfix idx =>
    match cunfold_fix mfix idx with
    | Some (narg, fn) => #|args| <=? narg
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite mkApps_app in H.
Qed.

Definition cstr_arity mdecl cdecl :=
  (mdecl.(ind_npars) + context_assumptions cdecl.(cstr_args))%nat.

Lemma nisLambda_mkApps f args : ~~ isLambda f -> ~~ isLambda (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.

Lemma nisArityHead_mkApps f args : ~~ isArityHead f -> ~~ isArityHead (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.

Lemma nisPrim_mkApps f args : ~~ isPrim f -> ~~ isPrim (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.

(* Lemma isLambda_mkApps f args : ~~ isApp f ->
  isLambda f = isLambda (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed. *)

Lemma head_mkApps f args : head (mkApps f args) = head f.
Proof.
  induction args in f |- *; cbn => //.
  now rewrite IHargs head_tapp.
Qed.

Lemma isFixApp_mkApps f args : isFixApp (mkApps f args) = isFixApp f.
Proof.
  now rewrite /isFixApp head_mkApps.
Qed.

Lemma isConstructApp_mkApps f args : isConstructApp (mkApps f args) = isConstructApp f.
Proof.
  now rewrite /isConstructApp head_mkApps.
Qed.

Lemma isPrimApp_mkApps f args : isPrimApp (mkApps f args) = isPrimApp f.
Proof. now rewrite /isPrimApp head_mkApps. Qed.

Section Wcbv.
  Context (Σ : global_env).

  (* The local context is empty: we are only doing weak reductions *)

  Variant eval_primitive (eval : term -> term -> Type) : prim_val -> prim_val -> Type :=
    | evalPrimInt i : eval_primitive eval (prim_int i) (prim_int i)
    | evalPrimFloat f : eval_primitive eval (prim_float f) (prim_float f)
    | evalPrimString s : eval_primitive eval (prim_string s) (prim_string s)
    | evalPrimArray  u v def ty v' def'
      (ev : All2 eval v v')
      (ed : eval def def') :
      let a := {| array_universe := u; array_default := def; array_value := v; array_type := ty |} in
      let a' := {| array_universe := u; array_default := def'; array_value := v'; array_type := ty |} in
      eval_primitive eval (prim_array a) (prim_array a').
  Derive Signature for eval_primitive.

  Variant eval_primitive_ind (eval : term -> term -> Type) (P : forall x y, eval x y -> Type) : forall x y, eval_primitive eval x y -> Type :=
  | evalPrimIntDep i : eval_primitive_ind eval P (prim_int i) (prim_int i) (evalPrimInt eval i)
  | evalPrimFloatDep f : eval_primitive_ind eval P (prim_float f) (prim_float f) (evalPrimFloat eval f)
  | evalPrimStringDep s : eval_primitive_ind eval P (prim_string s) (prim_string s) (evalPrimString eval s)
  | evalPrimArrayDep u v def ty v' def'
    (ev : All2 eval v v')
    (ed : eval def def') :
    All2_dep P ev -> P _ _ ed ->
    let a := {| array_universe := u; array_default := def; array_value := v; array_type := ty |} in
    let a' := {| array_universe := u; array_default := def'; array_value := v'; array_type := ty |} in
    eval_primitive_ind eval P (prim_array a) (prim_array a') (evalPrimArray eval u v def ty v' def' ev ed).
  Derive Signature for eval_primitive_ind.

  Unset Elimination Schemes.
  Inductive eval : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval (csubst a' 0 b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 t b1) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant_gen (lookup_env Σ) c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance u body) res ->
      eval (tConst c u) res

  (** Case *)
  | eval_iota ci discr c mdecl idecl cdecl u args p brs br res :
    eval discr (mkApps (tConstruct ci.(ci_ind) c u) args) ->
    nth_error brs c = Some br ->
    declared_constructor_gen (lookup_env Σ) (ci.(ci_ind), c) mdecl idecl cdecl ->
    #|args| = cstr_arity mdecl cdecl ->
    ci.(ci_npar) = mdecl.(ind_npars) ->
    context_assumptions cdecl.(cstr_args) = context_assumptions br.(bcontext) ->
    eval (iota_red ci.(ci_npar) p args br) res ->
    eval (tCase ci p discr brs) res

  (** Proj *)
  | eval_proj p discr args u a res mdecl idecl cdecl pdecl :
      declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl ->
      eval discr (mkApps (tConstruct p.(proj_ind) 0 u) args) ->
      #|args| = cstr_arity mdecl cdecl ->
      nth_error args (p.(proj_npars) + p.(proj_arg)) = Some a ->
      eval a res ->
      eval (tProj p discr) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx argsv a av fn res :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (#|argsv|, fn) ->
      eval (tApp (mkApps fn argsv) av) res ->
      eval (tApp f a) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx argsv a av narg fn :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      (#|argsv| < narg) ->
      eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

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
  | eval_construct ind c u mdecl idecl cdecl f args a a' :
    declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
    eval f (mkApps (tConstruct ind c u) args) ->
    #|args| < cstr_arity mdecl cdecl ->
    eval a a' ->
    eval (tApp f a) (mkApps (tConstruct ind c u) (args ++ [a']))

  (** Non redex-producing heads applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isArityHead f' || isConstructApp f' || isPrimApp f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')


  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)

  | eval_prim p p' :
    eval_primitive eval p p' ->
    eval (tPrim p) (tPrim p')


  (** Atoms are values (includes abstractions, cofixpoints and constructors
      along with type constructors) *)
  | eval_atom t : atom t -> eval t t.
  Derive Signature for eval.
  Set Elimination Schemes.

  Definition eval_rect :
  forall P : forall t t0 : term, eval t t0 -> Type,
  (forall (f : term) (na : aname) (t b a a' res : term)
     (e : eval f (tLambda na t b)),
   P f (tLambda na t b) e ->
   forall e0 : eval a a',
   P a a' e0 ->
   forall e1 : eval (csubst a' 0 b) res,
   P (csubst a' 0 b) res e1 ->
   P (tApp f a) res (eval_beta f na t b a a' res e e0 e1)) ->
  (forall (na : aname) (b0 b0' t b1 res : term) (e : eval b0 b0'),
   P b0 b0' e ->
   forall e0 : eval (csubst b0' 0 b1) res,
   P (csubst b0' 0 b1) res e0 ->
   P (tLetIn na b0 t b1) res (eval_zeta na b0 b0' t b1 res e e0)) ->
  (forall (c : kername) (decl : constant_body) (body : term)
     (isdecl : declared_constant_gen (lookup_env Σ) c decl)
     (u : Instance.t) (res : term) (e : cst_body decl = Some body)
     (e0 : eval body@[u] res),
   P body@[u] res e0 ->
   P (tConst c u) res (eval_delta c decl body isdecl u res e e0)) ->
  (forall (ci : case_info) (discr : term) (c : nat)
     (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
     (cdecl : constructor_body) (u : Instance.t) (args : list term)
     (p : predicate term) (brs : list (branch term))
     (br : branch term) (res : term)
     (e : eval discr (mkApps (tConstruct ci c u) args)),
   P discr (mkApps (tConstruct ci c u) args) e ->
   forall (e0 : nth_error brs c = Some br)
     (d : declared_constructor_gen (lookup_env Σ) (ci.(ci_ind), c) mdecl idecl cdecl)
     (e1 : #|args| = cstr_arity mdecl cdecl)
     (e2 : ci_npar ci = ind_npars mdecl)
     (e3 : context_assumptions (cstr_args cdecl) =
         context_assumptions (bcontext br))
     (e4 : eval (iota_red (ci_npar ci) p args br) res),
   P (iota_red (ci_npar ci) p args br) res e4 ->
   P (tCase ci p discr brs) res
     (eval_iota ci discr c mdecl idecl cdecl u args p brs br res e e0 d e1 e2
        e3 e4)) ->
  (forall (p : projection) (discr : term) (args : list term)
     (u : Instance.t) (a res : term) (mdecl : mutual_inductive_body)
     (idecl : one_inductive_body) (cdecl : constructor_body)
     (pdecl : projection_body)
     (d : declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl)
     (e : eval discr (mkApps (tConstruct (proj_ind p) 0 u) args)),
   P discr (mkApps (tConstruct (proj_ind p) 0 u) args) e ->
   forall (e0 : #|args| = cstr_arity mdecl cdecl)
     (e1 : nth_error args (proj_npars p + proj_arg p) = Some a)
     (e2 : eval a res),
   P a res e2 ->
   P (tProj p discr) res
     (eval_proj p discr args u a res mdecl idecl cdecl pdecl d e e0 e1 e2)) ->
  (forall (f4 : term) (mfix : mfixpoint term) (idx : nat)
     (argsv : list term) (a av fn res : term)
     (e : eval f4 (mkApps (tFix mfix idx) argsv)),
   P f4 (mkApps (tFix mfix idx) argsv) e ->
   forall e0 : eval a av,
   P a av e0 ->
   forall (e1 : cunfold_fix mfix idx = Some (#|argsv|, fn))
     (e2 : eval (tApp (mkApps fn argsv) av) res),
   P (tApp (mkApps fn argsv) av) res e2 ->
   P (tApp f4 a) res (eval_fix f4 mfix idx argsv a av fn res e e0 e1 e2)) ->
  (forall (f5 : term) (mfix : mfixpoint term) (idx : nat)
     (argsv : list term) (a av : term) (narg : nat)
     (fn : term) (e : eval f5 (mkApps (tFix mfix idx) argsv)),
   P f5 (mkApps (tFix mfix idx) argsv) e ->
   forall e0 : eval a av,
   P a av e0 ->
   forall (e1 : cunfold_fix mfix idx = Some (narg, fn)) (l : #|argsv| < narg),
   P (tApp f5 a) (tApp (mkApps (tFix mfix idx) argsv) av)
     (eval_fix_value f5 mfix idx argsv a av narg fn e e0 e1 l)) ->
  (forall (ip : case_info) (mfix : mfixpoint term) (idx : nat)
     (p : predicate term) (discr : term) (args : list term)
     (narg : nat) (fn : term) (brs : list (branch term))
     (res : term) (e : cunfold_cofix mfix idx = Some (narg, fn))
     (e0 : eval discr (mkApps (tCoFix mfix idx) args)),
   P discr (mkApps (tCoFix mfix idx) args) e0 ->
   forall e1 : eval (tCase ip p (mkApps fn args) brs) res,
   P (tCase ip p (mkApps fn args) brs) res e1 ->
   P (tCase ip p discr brs) res
     (eval_cofix_case ip mfix idx p discr args narg fn brs res e e0 e1)) ->
  (forall (p : projection) (mfix : mfixpoint term) (idx : nat)
     (discr : term) (args : list term) (narg : nat)
     (fn res : term) (e : cunfold_cofix mfix idx = Some (narg, fn))
     (e0 : eval discr (mkApps (tCoFix mfix idx) args)),
   P discr (mkApps (tCoFix mfix idx) args) e0 ->
   forall e1 : eval (tProj p (mkApps fn args)) res,
   P (tProj p (mkApps fn args)) res e1 ->
   P (tProj p discr) res
     (eval_cofix_proj p mfix idx discr args narg fn res e e0 e1)) ->
  (forall (ind : inductive) (c : nat) (u : Instance.t)
     (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
     (cdecl : constructor_body) (f8 : term) (args : list term)
     (a a' : term)
     (d : declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl)
     (e : eval f8 (mkApps (tConstruct ind c u) args)),
   P f8 (mkApps (tConstruct ind c u) args) e ->
   forall (l : #|args| < cstr_arity mdecl cdecl) (e0 : eval a a'),
   P a a' e0 ->
   P (tApp f8 a) (mkApps (tConstruct ind c u) (args ++ [a']))
     (eval_construct ind c u mdecl idecl cdecl f8 args a a' d e l e0)) ->
  (forall (f9 f' a a' : term) (e : eval f9 f'),
   P f9 f' e ->
   forall
     (i : ~~
          (isLambda f' || isFixApp f' || isArityHead f' || isConstructApp f'
           || isPrimApp f')) (e0 : eval a a'),
   P a a' e0 -> P (tApp f9 a) (tApp f' a') (eval_app_cong f9 f' a a' e i e0)) ->
  (forall (p p' : prim_val) (e : eval_primitive eval p p'),
   eval_primitive_ind eval P p p' e ->
   P (tPrim p) (tPrim p') (eval_prim p p' e)) ->
  (forall (t : term) (i : atom t), P t t (eval_atom t i)) ->
  forall (t t0 : term) (e : eval t t0), P t t0 e.
  Proof.
    intros.
    revert t t0 e.
    fix aux 3. destruct e.
    all:match reverse goal with
    [ H : _ |- _ ] => apply H; eauto
    end.
    induction e; constructor.
    induction ev; constructor. eapply aux. exact IHev.
    eapply aux.
  Qed.

  Definition eval_ind (P : forall t t0 : term, eval t t0 -> Prop) := eval_rect P.

  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

   Variant value_head (nargs : nat) : term -> Type :=
   | value_head_cstr ind c u mdecl idecl cdecl :
     declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
     nargs <= cstr_arity mdecl cdecl ->
     value_head nargs (tConstruct ind c u)
   | value_head_ind ind u : value_head nargs (tInd ind u)
   | value_head_cofix mfix idx : value_head nargs (tCoFix mfix idx)
   | value_head_fix mfix idx rarg fn :
     cunfold_fix mfix idx = Some (rarg, fn) ->
     nargs <= rarg ->
     value_head nargs (tFix mfix idx).
   Derive Signature NoConfusion for value_head.

   Variant primitive_value (value : term -> Type) : prim_val -> Type :=
    | primIntValue i : primitive_value value (prim_int i)
    | primFloatValue f : primitive_value value (prim_float f)
    | primStringValue s : primitive_value value (prim_string s)
    | primArrayValue a :
      All value a.(array_value) ->
      value a.(array_default) ->
      primitive_value value (prim_array a).
   Derive Signature NoConfusion for primitive_value.

  Variant atomic_value (value : term -> Type) : term -> Type :=
  | atomic_atom t : atom t -> atomic_value value t
  | atomic_primitive p : primitive_value value p -> atomic_value value (tPrim p).
  Derive Signature NoConfusion for atomic_value.
  Hint Constructors atomic_value : core.

   Inductive value : term -> Type :=
   | value_atomic t : atomic_value value t -> value t
   | value_app_nonnil f args : value_head #|args| f -> args <> [] -> All value args -> value (mkApps f args).
   Derive Signature for value.
   Lemma value_app f args : value_head #|args| f -> All value args -> value (mkApps f args).
   Proof using Type.
     destruct (args).
     - intros [] hv; now repeat constructor.
     - intros vh av. eapply value_app_nonnil => //.
   Qed.

   Lemma value_values_ind : forall P : term -> Type,
       (forall t, atom t -> P t) ->
       (forall p, primitive_value value p -> primitive_value P p -> P (tPrim p)) ->
       (forall f args, value_head #|args| f -> args <> [] -> All value args -> All P args -> P (mkApps f args)) ->
       forall t : term, value t -> P t.
   Proof.
     intros P ???.
     fix value_values_ind 2. destruct 1.
     - destruct a.
      * apply X; auto.
      * eapply X0; auto.
       depelim p0; constructor. exact (make_All_All value_values_ind a0). eauto.
     - eapply X1; auto; tea.
       eapply (make_All_All value_values_ind a).
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
     ((l = []) × atomic_value value t) + ([× l <> [], value_head #|l| t & All value l]).
   Proof using Type.
     intros H H'. generalize_eq x (mkApps t l).
     revert t H. induction H' using value_values_ind.
     intros. subst.
     - eapply atom_mkApps in H. intuition auto.
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

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof using Type.
    intros ev.
    induction ev; simpl; intros; auto using value.
    - change (tApp ?h ?a) with (mkApps h [a]).
      rewrite -mkApps_app.
      apply value_mkApps_inv in IHev1; [|easy].
      destruct IHev1 as [(-> & _)|[]].
      + apply value_app; auto. len.
        cbn in *. econstructor; tea. cbn; auto.
      + depelim v. rewrite e1 in e. noconf e.
        eapply value_app; auto. econstructor; tea.
          len; lia. apply All_app_inv; auto.

    - apply value_mkApps_inv in IHev1; [|easy].
      destruct IHev1 as [(-> & _)|[]].
      + eapply value_app; cbn; auto. econstructor; tea.
      + eapply value_app; cbn; auto. econstructor; tea. cbn; len.
        eapply All_app_inv; auto.

    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHev1 => //.
      destruct IHev1 as [?|[]]; intuition subst.
      * depelim b. rewrite a0 /=.
        rewrite a0 in i. simpl in *.
        apply (value_app t [a']).
        destruct t; simpl in * |- *; try congruence.
        all:try solve [repeat constructor; auto].
        auto.
        rewrite isPrimApp_mkApps /= /isPrimApp //= in i.
        rewrite !negb_or in i. rtoProp; intuition auto. cbn in H0. congruence.

      * rewrite -[tApp _ _](mkApps_app _ (firstn n l) [a']).
        eapply value_app; auto. len.
        rewrite isFixApp_mkApps // isConstructApp_mkApps // in i.
        rewrite !negb_or in i. rtoProp; intuition auto.
        destruct v; cbn in * => //.
        + constructor.
        + constructor.
        + apply All_app_inv; auto.
    - induction X.
      all:constructor; constructor 2; constructor; eauto.
      solve_all.
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

  Lemma eval_mkApps_Construct ind c u mdecl idecl cdecl f args args' :
    declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
    eval f (tConstruct ind c u) ->
    #|args| <= cstr_arity mdecl cdecl ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tConstruct ind c u) args').
  Proof using Type.
    intros hdecl evf hargs. revert args'.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. now cbn.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite mkApps_app /=. len in hargs. cbn in hargs.
      eapply eval_construct; tea.
      eapply IHargs => //. lia.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma eval_mkApps_CoFix f mfix idx args args' :
    eval f (tCoFix mfix idx) ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tCoFix mfix idx) args').
  Proof using Type.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_app_cong; tea.
      eapply IHargs => //.
      rewrite isFixApp_mkApps // /= isConstructApp_mkApps // !negb_or isPrimApp_mkApps.
      rtoProp; intuition auto.
      apply nisLambda_mkApps => //. apply nisArityHead_mkApps => //.
  Qed.

  Lemma eval_mkApps_tInd f ind u args args' :
    eval f (tInd ind u) ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tInd ind u) args').
  Proof using Type.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_app_cong; tea.
      eapply IHargs => //.
      rewrite isFixApp_mkApps // /= isConstructApp_mkApps // !negb_or isPrimApp_mkApps.
      rtoProp; intuition auto.
      apply nisLambda_mkApps => //. apply nisArityHead_mkApps => //.
  Qed.

  Lemma eval_stuck_Fix {f mfix idx args args'} :
    eval f (tFix mfix idx) ->
    All2 eval args args' ->
    isStuckFix (tFix mfix idx) args ->
    eval (mkApps f args) (mkApps (tFix mfix idx) args').
  Proof using Type.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      destruct cunfold_fix as [[rarg fn]|] eqn:eqc => //.
      len; cbn. move/Nat.leb_le => hrarg.
      eapply eval_fix_value.
      eapply IHargs => //. unfold isStuckFix. rewrite eqc. apply Nat.leb_le; lia. auto. tea.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma value_head_antimon {n n' f} : n' <= n -> value_head n f -> value_head n' f.
  Proof using Type.
    intros hn []; econstructor; tea. lia. lia.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    eval f f' ->
    value_head #|l| f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof using Type.
    revert l'. induction l using rev_ind; intros l' evf vf' evl.
    depelim evl. eapply evf.
    eapply All2_app_inv_l in evl as (?&?&?&?&?).
    intuition auto. subst. depelim a0. depelim a0.
    - destruct vf'.
      * eapply eval_mkApps_Construct; tea. eapply All2_app; auto.
      * eapply eval_mkApps_tInd; auto. eapply All2_app; auto.
      * eapply eval_mkApps_CoFix; auto. eapply All2_app; auto.
      * eapply eval_stuck_Fix; tea. eapply All2_app; auto.
        unfold isStuckFix; rewrite e0. now apply Nat.leb_le.
  Qed.

  Lemma value_final e : value e -> eval e e.
  Proof using Type.
    induction 1 using value_values_ind; simpl; auto using value.
    - now constructor.
    - constructor.
      destruct X0; try constructor; eauto.
      destruct a; cbn in *. constructor; solve_all.
    - assert (All2 eval args args).
      { clear -X1; induction X1; constructor; auto. }
      eapply eval_mkApps_cong => //. now eapply value_head_final.
  Qed.

  Lemma eval_stuck_fix args argsv mfix idx :
    All2 eval args argsv ->
    isStuckFix (tFix mfix idx) argsv ->
    eval (mkApps (tFix mfix idx) args) (mkApps (tFix mfix idx) argsv).
  Proof using Type.
    intros. eapply eval_stuck_Fix; eauto. now constructor.
    move: H. unfold isStuckFix. destruct cunfold_fix as [[rarg fn]|] => //.
    now rewrite (All2_length X).
  Qed.

  Lemma stuck_fix_value_inv argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    (All value argsv * isStuckFix (tFix mfix idx) argsv).
  Proof using Type.
    remember (mkApps (tFix mfix idx) argsv) as tfix.
    intros hv; revert Heqtfix.
    induction hv using value_values_ind; intros eq; subst.
    - unfold atom in H. destruct argsv using rev_case => //.
      split; auto. simpl. simpl in H. rewrite H0 //.
      rewrite mkApps_app /= // in H.
    - solve_discr => //.
    - solve_discr => //.
      depelim X. rewrite e. intros [= -> ->]. split => //.
      unfold isStuckFix. rewrite e. now apply Nat.leb_le.
  Qed.

  Lemma stuck_fix_value_args argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|argsv| <= narg.
  Proof using Type.
    intros val unf.
    eapply stuck_fix_value_inv in val; eauto.
    destruct val.
    simpl in i. rewrite unf in i.
    now eapply Nat.leb_le in i.
  Qed.

  Lemma closed_beta na t b u : closed (tLambda na t b) -> closed u -> closed (csubst u 0 b).
  Proof using Type. simpl; move/andP => [ct cb] cu. now eapply closed_csubst. Qed.

  Lemma closed_def `{checker_flags} c decl u b : wf Σ -> declared_constant Σ c decl ->
    cst_body decl = Some b ->
    closed (subst_instance u b).
  Proof using Type.
    move=> wfΣ Hc Hb. unshelve eapply declared_constant_to_gen in Hc; eauto.
    rewrite PCUICClosed.closedn_subst_instance.
    apply declared_decl_closed in Hc => //. simpl in Hc. red in Hc.
    rewrite Hb in Hc. simpl in Hc. now move/andP: Hc => [].
  Qed.

  Lemma closed_iota ci ind p c u args brs br :
    forallb (test_branch_k p closedn 0) brs ->
    forallb (closedn 0) p.(pparams) ->
    closed (mkApps (tConstruct ind c u) args) ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->    nth_error brs c = Some br ->
    closed (iota_red (ci_npar ci) p args br).
  Proof using Type.
    unfold iota_red => cbrs cpars cargs hass e.
    solve_all.
    eapply All_nth_error in e; eauto. simpl in e.
    rewrite closedn_mkApps in cargs.
    move/andP: cargs => [Hcons Hargs].
    eapply (closedn_subst _ 0 0).
    now rewrite forallb_rev forallb_skipn //.
    simpl. rewrite List.length_rev /expand_lets /expand_lets_k.
    rewrite -(Nat.add_0_r #|skipn (ci_npar ci) args|).
    rewrite length_skipn hass.
    replace (ci_npar ci + context_assumptions (bcontext br) - ci_npar ci)
    with (context_assumptions (bcontext br)) by lia.
    move/andP: e => [cltx clb].
    have hl : context_assumptions (inst_case_branch_context p br) = context_assumptions (bcontext br).
    { rewrite /inst_case_branch_context. now len. }
    eapply (closedn_subst _ _ 0).
    rewrite -hl.
    eapply closedn_extended_subst => //.
    { rewrite /inst_case_branch_context /inst_case_context.
      eapply (closedn_ctx_subst 0 0); cbn.
      rewrite closedn_subst_instance_context. now len.
      rewrite forallb_rev. solve_all. }
    rewrite extended_subst_length Nat.add_0_r /= Nat.add_comm -hl.
    eapply closedn_lift.
    rewrite inst_case_branch_context_length.
    now rewrite Nat.add_0_r in clb.
  Qed.

  Lemma closed_arg f args n a :
    closed (mkApps f args) ->
    nth_error args n = Some a -> closed a.
  Proof using Type.
    rewrite closedn_mkApps.
    move/andP => [cf cargs].
    solve_all. eapply All_nth_error in cargs; eauto.
  Qed.

  Lemma closed_unfold_fix mfix idx narg fn :
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = Some (narg, fn) -> closed fn.
  Proof using Type.
    unfold unfold_fix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold fix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto.
    simpl. rewrite fix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
  Qed.

  Lemma closed_fix_substl_subst_eq {mfix idx d} :
    closed (tFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (fix_subst mfix) (dbody d) = substl (fix_subst mfix) (dbody d).
  Proof using Type.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (fix_subst mfix).
    { clear idx.
      solve_all.
      unfold fix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (fix_subst mfix) (dbody d) clfix.
    clear; induction fix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; depelim Ha.
    simpl in *.
    intros hnth.
    rewrite -IHfix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_cofix_substl_subst_eq {mfix idx d} :
    closed (tCoFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (cofix_subst mfix) (dbody d) = substl (cofix_subst mfix) (dbody d).
  Proof using Type.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (cofix_subst mfix).
    { clear idx.
      solve_all.
      unfold cofix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (cofix_subst mfix) (dbody d) clfix.
    clear; induction cofix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; depelim Ha.
    simpl in *.
    intros hnth.
    rewrite -IHcofix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_fix_cunfold_eq mfix idx :
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = cunfold_fix mfix idx.
  Proof using Type.
    unfold unfold_fix, cunfold_fix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    intros cl; f_equal; f_equal.
    now rewrite (closed_fix_substl_subst_eq cl).
  Qed.

  Lemma closed_unfold_cofix_cunfold_eq mfix idx :
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = cunfold_cofix mfix idx.
  Proof using Type.
    unfold unfold_cofix, cunfold_cofix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (cofix_subst mfix).
    { clear Heq d idx.
      solve_all.
      unfold cofix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (cofix_subst mfix) (dbody d) clfix.
    clear; induction cofix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; dependent elimination Ha as [All_cons ca cf].
    simpl in *.
    rewrite -IHcofix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_cofix mfix idx narg fn :
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = Some (narg, fn) -> closed fn.
  Proof using Type.
    unfold unfold_cofix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold cofix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto.
    rewrite cofix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
  Qed.

  (** Evaluation preserves closedness: *)
  Lemma eval_closed `{checker_flags} {wfΣ : wf Σ} : forall t u, closed t -> eval t u -> closed u.
  Proof using Type.
    move=> t u Hc ev. move: Hc.
    induction ev; simpl in *; auto;
      (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
    - eapply IHev3. unshelve eapply closed_beta. 3:eauto. exact na. simpl. eauto.
    - eapply IHev2. now rewrite closed_csubst.
    - apply IHev. eapply closed_def; eauto.
      apply declared_constant_from_gen; eauto.
    - apply IHev2.
      eapply closed_iota; tea.
      move/andP: Hc => [] /andP [] //.
      now eapply IHev1. rewrite e1.
      now rewrite -e3 e2 /cstr_arity.
    - eapply IHev2.
      specialize (IHev1 Hc).
      rewrite closedn_mkApps in IHev1.
      move/andP: IHev1 => [Hcons Hargs]. solve_all.
      eapply All_nth_error in Hargs; eauto.
    - eapply IHev3.
      apply/andP.
      split; [|easy].
      specialize (IHev1 Hc).
      rewrite closedn_mkApps in IHev1.
      move/andP: IHev1 => [clfix clargs].
      rewrite closedn_mkApps clargs andb_true_r.
      eapply closed_unfold_fix; [easy|].
      now rewrite closed_unfold_fix_cunfold_eq.
    - apply andb_true_iff.
      split; [|easy].
      solve_all.
    - eapply IHev2. solve_all. rewrite !closedn_mkApps in H0 |- *. solve_all.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
    - eapply IHev2. solve_all. rewrite !closedn_mkApps in H0 |- *. solve_all.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
    - rewrite closedn_mkApps /=. specialize (IHev1 Hc). specialize (IHev2 Hc').
      move: IHev1. rewrite closedn_mkApps /= forallb_app => -> /=. now rewrite IHev2.
    - apply/andP; split; auto.
    - solve_all. depelim X; depelim Hc; constructor; intuition eauto; solve_all.
  Qed.

  (* TODO MOVE *)
  Lemma nApp_isApp_false :
    forall u,
      nApp u = 0 ->
      isApp u = false.
  Proof using Type.
    intros u e.
    destruct u. all: simpl. all: try reflexivity.
    discriminate.
  Qed.

  Lemma eval_tRel n t :
    eval (tRel n) t -> False.
  Proof using Type. now intros e; depelim e. Qed.

  Lemma eval_tVar i t : eval (tVar i) t -> False.
  Proof using Type. now intros e; depelim e. Qed.

  Lemma eval_tEvar n l t : eval (tEvar n l) t -> False.
  Proof using Type. now intros e; depelim e. Qed.

  Lemma eval_mkApps_tCoFix mfix idx args v :
    eval (mkApps (tCoFix mfix idx) args)  v ->
    exists args', v = mkApps (tCoFix mfix idx) args'.
  Proof using Type.
    revert v.
    induction args using List.rev_ind; intros v ev.
    + exists [].
      now depelim ev.
    + rewrite mkApps_app in ev.
      cbn in *.
      depelim ev;
        try solve [apply IHargs in ev1 as (? & ?); solve_discr].
      * apply IHargs in ev1 as (argsv & ->).
        exists (argsv ++ [a']).
        now rewrite mkApps_app.
      * easy.
  Qed.

  Set Equations With UIP.

  Scheme Induction for le Sort Prop.

  Lemma le_irrel n m (p q : n <= m) : p = q.
  Proof using Type.
    revert q.
    now induction p using le_ind_dep; intros q; depelim q.
  Qed.

  Instance branch_UIP : UIP (branch term).
  Proof using Type.
    eapply EqDec.eqdec_uip; tc.
  Qed.

  Instance option_UIP {A} (u : EqDec A) : UIP (option A).
  Proof using Type.
    eapply EqDec.eqdec_uip; tc.
    eqdec_proof.
  Qed.

  Lemma declared_constructor_unique {ind mdecl idecl cdecl} (d d' : declared_constructor_gen (lookup_env Σ) ind mdecl idecl cdecl) : d = d'.
  Proof using Type.
    destruct d, d'.
    destruct d, d0.
    assert (d0 = d) as -> by apply uip.
    assert (e1 = e2) as -> by now apply uip.
    assert (e = e0) as -> by now apply uip.
    reflexivity.
  Qed.

  Lemma declared_projection_unique {ind mdecl idecl cdecl pdecl}
     (d d' : declared_projection_gen (lookup_env Σ) ind mdecl idecl cdecl pdecl) : d = d'.
  Proof using Type.
    destruct d, d'.
    rewrite (declared_constructor_unique d d0).
    destruct a, a0.
    assert (e = e1) as -> by now apply uip.
    assert (e0 = e2) as -> by now apply uip.
    reflexivity.
  Qed.

  Unset SsrRewrite.
  Lemma eval_unique_sig {t v v'} :
    forall (ev1 : eval t v) (ev2 : eval t v'),
      {| pr1 := v; pr2 := ev1 |} = {| pr1 := v'; pr2 := ev2 |}.
  Proof using Type.
    Local Ltac go :=
      solve [
          repeat
            match goal with
            | [H: _, H' : _ |- _] =>
              specialize (H _ H');
              try solve [apply (f_equal pr1) in H; cbn in *; solve_discr];
              noconf H
            end; easy].
    intros ev.
    revert v'.
    induction ev; intros v' ev'.
    - depelim ev'; go.
    - depelim ev'; go.
    - depelim ev'; try go.
      pose proof (declared_constant_inj _ _ isdecl isdecl0) as <-.
      assert (body0 = body) as -> by congruence.
      assert (e0 = e) as -> by now apply uip.
      assert (isdecl0 = isdecl) as -> by now apply uip.
      now specialize (IHev _ ev'); noconf IHev.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        apply (f_equal pr1) in IHev1 as apps_eq; cbn in *.
        apply mkApps_eq_inj in apps_eq as (eq1 & eq2); try easy.
        noconf eq1. noconf eq2. noconf IHev1.
        epose proof (declared_constructor_inj d d0) as [-> [-> <-]].
        pose proof e0. rewrite e in H. noconf H.
        specialize (IHev2 _ ev'2). noconf IHev2.
        assert (e0 = e) as -> by now apply uip.
        assert (d = d0) as -> by apply declared_constructor_unique.
        assert (e1 = e4) as -> by now apply uip.
        assert (e2 = e5) as -> by now apply uip.
        assert (e3 = e6) as -> by now apply uip.
        reflexivity.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        apply (f_equal pr1) in IHev1 as apps_eq; cbn in *.
        apply mkApps_eq_inj in apps_eq as (eq1 & eq2); try easy.
        noconf eq1. noconf eq2. noconf IHev1.
        pose proof (declared_projection_inj d d0) as [? [? []]].
        subst mdecl0 idecl0 cdecl0 pdecl0.
        assert (d = d0) as -> by apply declared_projection_unique.
        pose proof e1. rewrite e2 in H. noconf H.
        specialize (IHev2 _ ev'2); noconf IHev2.
        assert (e0 = e) as -> by now apply uip.
        assert (e1 = e2) as -> by now apply uip.
        reflexivity.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        pose proof e.
        rewrite e1 in H. noconf H.
        assert (e1 = e) as -> by now apply uip.
        specialize (IHev3 _ ev'3).
        now noconf IHev3.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H. noconf IHev1.
        exfalso. rewrite e in e1. noconf e1. lia.
      + specialize (IHev1 _ ev'1). noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        exfalso; rewrite e1 in e.
        noconf e.
        lia.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        assert (narg0 = narg) as -> by congruence.
        assert (fn0 = fn) as -> by congruence.
        assert (e1 = e) as -> by now apply uip.
        now assert (l0 = l) as -> by now apply le_irrel.
      + specialize (IHev1 _ ev'1).
        noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1).
      pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
      noconf H. noconf IHev1.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      specialize (IHev2 _ ev'2); noconf IHev2.
      now assert (e0 = e) as -> by now apply uip.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1).
      pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
      noconf H. noconf IHev1.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      specialize (IHev2 _ ev'2); noconf IHev2.
      now assert (e0 = e) as -> by now apply uip.
    - depelim ev'; try go.
      * specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2). noconf IHev2.
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-). noconf H.
        noconf IHev1.
        epose proof (declared_constructor_inj d d0) as [-> [-> <-]].
        assert (d = d0) as -> by apply declared_constructor_unique.
        assert (l = l0) as -> by now apply le_irrel. reflexivity.
      * specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2). noconf IHev2.
        exfalso. rewrite isConstructApp_mkApps in i; auto.
        cbn in i. rewrite !negb_or in i; rtoProp; intuition auto.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        exfalso.
        rewrite isConstructApp_mkApps in i; auto.
        cbn in i. rewrite !negb_or in i; rtoProp; intuition auto.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        now assert (i0 = i) as -> by now apply uip.
    - depelim ev'; try go.
      depelim X; depelim e0; try constructor.
      subst a' a0 a1 a'0. cbn.
      specialize (e _ ed0). noconf e.
      assert (v' = v'0) as <-; auto.
      clear -ev0 a.
      induction a in v'0, ev0 |- *; depelim ev0; eauto. f_equal; eauto. specialize (r0 _ e). now noconf r0.
      assert (ev = ev0) as <-; auto.
      induction a in ev0 |- *; depelim ev0; eauto. f_equal; eauto. specialize (r0 _ e). now noconf r0.
    - depelim ev'; cbn in i; eauto.
      now assert (i0 = i) as -> by now apply uip.
  Qed.

  Lemma eval_deterministic {t v v'} :
    eval t v ->
    eval t v' ->
    v = v'.
  Proof using Type.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.

  Lemma eval_unique {t v} :
    forall (ev1 : eval t v) (ev2 : eval t v),
      ev1 = ev2.
  Proof using Type.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.

  Set SsrRewrite.

  Lemma eval_LetIn {n b ty t v} :
    eval (tLetIn n b ty t) v ->
    ∑ b',
      eval b b' * eval (csubst b' 0 t) v.
  Proof using Type. now intros H; depelim H. Qed.

  Lemma eval_Const {c u v} :
    eval (tConst c u) v ->
    ∑ decl, declared_constant Σ c decl *
                 match cst_body decl with
                 | Some body => eval (subst_instance u body) v
                 | None => False
                 end.
  Proof using Type.
    intros H; depelim H.
    - exists decl. apply declared_constant_from_gen in isdecl.
      split; [easy|].
      now rewrite e.
    - easy.
  Qed.

End Wcbv.

Arguments eval_unique_sig {_ _ _ _}.
Arguments eval_deterministic {_ _ _ _}.
Arguments eval_unique {_ _ _}.

Reserved Notation " Σ ⊢ t ⇝ᵥ u " (at level 50, t, u at next level).

Local Open Scope type_scope.

Inductive wcbv_red1 (Σ: global_env) : term -> term -> Type :=
| wcbv_red_app_left a a' b :
  Σ ⊢ a ⇝ᵥ a' -> Σ ⊢ tApp a b ⇝ᵥ tApp a' b
| wcbv_red_app_right a b b' :
  value Σ a -> Σ ⊢ b ⇝ᵥ b' -> Σ ⊢ tApp a b ⇝ᵥ tApp a b'
| wcbv_red_beta na t b a :
  value Σ a -> Σ ⊢ tApp (tLambda na t b) a ⇝ᵥ csubst a 0 b
| wcbv_red_let_in b0 b0' na t b1 :
  Σ ⊢ b0 ⇝ᵥ b0' -> Σ ⊢ tLetIn na b0 t b1 ⇝ᵥ tLetIn na b0' t b1
| wcbv_red_zeta b0 na t b1 :
  value Σ b0 -> Σ ⊢ tLetIn na b0 t b1 ⇝ᵥ csubst b0 0 b1
| wcbv_red_delta decl body c u (isdecl : declared_constant Σ c decl) :
   decl.(cst_body) = Some body ->
  Σ ⊢ tConst c u ⇝ᵥ subst_instance u body
| wcbv_red_case_in ci p discr discr' brs :
  Σ ⊢ discr ⇝ᵥ discr' -> Σ ⊢ tCase ci p discr brs ⇝ᵥ tCase ci p discr' brs
| wcbv_red_iota ci c mdecl idecl cdecl u args p brs br :
  nth_error brs c = Some br ->
  declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
  #|args| = cstr_arity mdecl cdecl ->
  ci.(ci_npar) = mdecl.(ind_npars) ->
  context_assumptions (cdecl.(cstr_args)) = context_assumptions br.(bcontext) ->
  All (value Σ) args ->
  Σ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs ⇝ᵥ iota_red ci.(ci_npar) p args br
| wcbv_red_proj_in discr discr' p :
  Σ ⊢ discr ⇝ᵥ discr' -> Σ ⊢ tProj p discr ⇝ᵥ tProj p discr'
| wcbv_red_proj p args u a mdecl idecl cdecl pdecl :
  declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl ->
  #|args| = cstr_arity mdecl cdecl ->
  nth_error args (p.(proj_npars) + p.(proj_arg)) = Some a ->
  All (value Σ) args ->
  Σ ⊢ tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ⇝ᵥ a
| wcbv_red_fix mfix idx argsv a fn :
  All (value Σ) argsv ->
  value Σ a ->
  unfold_fix mfix idx = Some (#|argsv|, fn) ->
  isConstruct_app a = true ->
  Σ ⊢ tApp ((mkApps (tFix mfix idx) argsv)) a ⇝ᵥ tApp (mkApps fn argsv) a
| wcbv_red_cofix_proj : forall (p : projection) (mfix : mfixpoint term)
                     (idx : nat) (args : list term)
                     (narg : nat) (fn : term),
                   cunfold_cofix mfix idx = Some (narg, fn) ->
                   All (value Σ) args ->
                   Σ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ⇝ᵥ tProj p (mkApps fn args)
| wcbv_red_cofix_case : forall (ip : case_info) (mfix : mfixpoint term)
                     (idx : nat) (p : predicate term)
                     (args : list term) (narg : nat)
                     (fn : term) (brs : list (branch term)),
                   cunfold_cofix mfix idx = Some (narg, fn) ->
                   All (value Σ) args ->
                   Σ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs ⇝ᵥ tCase ip p (mkApps fn args) brs
| wcbv_red_array_default : forall a d,
  Σ ⊢ a.(array_default) ⇝ᵥ d ->
  Σ ⊢ tPrim (prim_array a) ⇝ᵥ (tPrim (prim_array (set_array_default a d)))
| wcbv_red_array_value : forall a n val val',
  value Σ a.(array_default) ->
  nth_error a.(array_value) n = Some val ->
  All (value Σ) (firstn n a.(array_value)) ->
  Σ ⊢ val ⇝ᵥ val' ->
  let v' := firstn n a.(array_value) ++ (val' :: skipn (S n) a.(array_value)) in
  Σ ⊢ tPrim (prim_array a) ⇝ᵥ (tPrim (prim_array (set_array_value a v')))
where " Σ ⊢ t ⇝ᵥ u " := (wcbv_red1 Σ t u).

Lemma wcbv_red1_closed {cf : checker_flags} {Σ t t'} :
  wf Σ ->
  closed t -> Σ ⊢ t ⇝ᵥ t' -> closed t'.
Proof.
  intros Hwf Hcl Hred. induction Hred; cbn in *; solve_all.
  all: eauto using closed_csubst, closed_def.
  - eapply closed_iota; eauto. solve_all. unfold test_predicate_k in H. solve_all.
    now rewrite e0 /cstr_arity -e1 -e2.
  - eauto using closed_arg.
  - rewrite !closedn_mkApps in H |- *. solve_all.
    eapply closed_unfold_fix; tea.
  - rewrite !closedn_mkApps in Hcl |- *. solve_all.
    unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; inversion e.
    eapply closed_unfold_cofix with (narg := narg); eauto.
    unfold unfold_cofix. rewrite E. subst. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto.
  - rewrite !closedn_mkApps in H1 |- *. solve_all.
    unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; inversion e.
    eapply closed_unfold_cofix with (narg := narg); eauto.
    unfold unfold_cofix. rewrite E. subst. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto.
  - subst v'. eapply All_app_inv. now eapply All_firstn.
    constructor. 2:now eapply All_skipn.
    eapply All_nth_error in e; tea; eauto.
Qed.

Lemma wcbv_red1_red1 {cf : checker_flags} {Σ t t' } :
  closed t ->
  Σ ⊢ t ⇝ᵥ t' -> Σ ;;; [] |- t ⇝ t'.
Proof.
  intros Hcl Hred.
  induction Hred. all: cbn in *; solve_all.
  1-10: try econstructor; eauto using wcbv_red1_closed.
  1,2: now rewrite closed_subst; eauto; econstructor; eauto.
  - now rewrite e0 /cstr_arity -e1 -e2.
  - rewrite !tApp_mkApps -!mkApps_app. econstructor. eauto.
    unfold is_constructor. now rewrite nth_error_app2 // Nat.sub_diag.
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in Hcl. solve_all.
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in H1. solve_all.
  - now constructor.
  - constructor. subst v'.
    rewrite -{1}(firstn_skipn n (array_value a)).
    eapply OnOne2_app. move: (skipn_nth_error (array_value a) n).
    rewrite e. intros ->. constructor. eapply IHHred.
    eapply All_nth_error in e; tea; eauto.
Qed.


Global Hint Constructors value eval : wcbv.
Global Hint Resolve value_final : wcbv.

Lemma wcbv_red1_eval {cf : checker_flags} {Σ : global_env_ext } t t' v : wf Σ ->
  closed t ->
  Σ ⊢ t ⇝ᵥ t' -> eval Σ t' v -> eval Σ t v.
Proof.
  intros Hwf Hty Hred Heval.
  induction Hred in Heval, v, Hty |- *; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6:now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6: now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - unshelve eapply declared_constant_to_gen in isdecl; eauto.
    inversion Heval; subst. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv.
  - inversion Heval; subst. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv.
  - eapply eval_iota. eapply eval_mkApps_Construct; tea.
    unshelve eapply declared_constructor_to_gen; eauto.
    now econstructor. unfold cstr_arity. rewrite e0.
    rewrite (PCUICGlobalEnv.declared_minductive_ind_npars d).
    now rewrite -(declared_minductive_ind_npars d) /cstr_arity.
    all:tea. eapply All_All2_refl. solve_all. now eapply value_final.
    unshelve eapply declared_constructor_to_gen; eauto.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - all:cbn in Hty; solve_all. eapply eval_proj; tea.
    eapply value_final. eapply value_app; auto. econstructor; tea. eapply d.
    rewrite e; lia.
  - eapply eval_fix; eauto.
    + eapply value_final. eapply value_app; auto. econstructor.
      rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity. 2:eauto.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
    + eapply value_final; eauto.
    + rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
      Unshelve. all: now econstructor.
  - destruct p as [[] ?]. eapply eval_cofix_proj; tea.
    eapply value_final, value_app. now constructor. auto.
  - eapply eval_cofix_case; tea.
    eapply value_final, value_app. now constructor. auto.
  - cbn in Hty. rtoProp; intuition auto.
    depelim Heval; eapply eval_prim.
    depelim e.
    + subst a0 a'; cbn in *. destruct a; eapply evalPrimArray; cbn in *; eauto.
    + destruct a; eapply evalPrimArray; cbn in *; eauto.
  - cbn in Hty. rtoProp; intuition auto.
    depelim Heval; eapply eval_prim.
    depelim e0.
    + subst a1 a'; cbn in *. destruct a; eapply evalPrimArray; cbn in *; eauto.
      eapply All2_app_inv_l in ev as [r1 [r2 [? []]]]. subst v'0.
      depelim a1. specialize (IHHred y). forward IHHred. toAll. eapply All_nth_error in H; tea; eauto.
      rewrite -(firstn_skipn n array_value). eapply All2_app; eauto.
      move: (skipn_nth_error array_value n). rewrite e => ->.
      constructor; eauto.
    + now cbn in i.
Qed.
