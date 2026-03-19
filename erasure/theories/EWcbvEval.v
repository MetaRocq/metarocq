(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv
  EWellformed.

From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Set Default Proof Using "Type*".

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


(* Tells if the evaluation relation should include match-prop and proj-prop reduction rules.
  Also, are constructors represented as blocks or higher-order. *)
Class WcbvFlags := { with_prop_case : bool ; with_guarded_fix : bool ; with_constructor_as_block : bool }.

Definition atom `{wfl : WcbvFlags} Σ t :=
  match t with
  | tBox
  | tCoFix _ _
  | tLambda _ _
  | tLazy _
  | tFix _ _ => true
  | tConstruct ind c [] => negb with_constructor_as_block && isSome (lookup_constructor Σ ind c)
  | _ => false
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

Lemma atom_mkApps {wfl : WcbvFlags} Σ f l : atom Σ (mkApps f l) -> (l = []) /\ atom Σ f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite mkApps_app in H.
Qed.

Definition disable_prop_cases fl : WcbvFlags :=
  {| with_prop_case := false; with_guarded_fix := fl.(@with_guarded_fix) ; with_constructor_as_block := fl.(@with_constructor_as_block) |}.

Definition switch_unguarded_fix fl : WcbvFlags :=
  EWcbvEval.Build_WcbvFlags fl.(@with_prop_case) false fl.(@with_constructor_as_block).

Definition default_wcbv_flags := {| with_prop_case := true ; with_guarded_fix := true ; with_constructor_as_block := false |}.
Definition opt_wcbv_flags := {| with_prop_case := false ; with_guarded_fix := true ; with_constructor_as_block := false|}.
Definition target_wcbv_flags := {| with_prop_case := false ; with_guarded_fix := false ; with_constructor_as_block := false |}.

Section Wcbv.
  Context {wfl : WcbvFlags}.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

  Variant eval_primitive {term term' : Set} (eval : term -> term' -> Set) : prim_val term -> prim_val term' -> Set :=
    | evalPrimInt i : eval_primitive eval (prim_int i) (prim_int i)
    | evalPrimFloat f : eval_primitive eval (prim_float f) (prim_float f)
    | evalPrimString s : eval_primitive eval (prim_string s) (prim_string s)
    | evalPrimArray v def v' def'
      (ev : All2_Set eval v v')
      (ed : eval def def') :
      let a := {| array_default := def; array_value := v |} in
      let a' := {| array_default := def'; array_value := v' |} in
      eval_primitive eval (prim_array a) (prim_array a').
  Derive Signature for eval_primitive.

  Variant eval_primitive_ind {term term' : Set} (eval : term -> term' -> Set) (P : forall x y, eval x y -> Type) : forall x y, eval_primitive eval x y -> Type :=
  | evalPrimIntDep i : eval_primitive_ind eval P (prim_int i) (prim_int i) (evalPrimInt eval i)
  | evalPrimFloatDep f : eval_primitive_ind eval P (prim_float f) (prim_float f) (evalPrimFloat eval f)
  | evalPrimStringDep s : eval_primitive_ind eval P (prim_string s) (prim_string s) (evalPrimString eval s)
  | evalPrimArrayDep v def v' def'
    (ev : All2_Set eval v v')
    (ed : eval def def') :
    All2_over ev P -> P _ _ ed ->
    let a := {| array_default := def; array_value := v |} in
    let a' := {| array_default := def'; array_value := v' |} in
    eval_primitive_ind eval P (prim_array a) (prim_array a') (evalPrimArray eval v def v' def' ev ed).
  Derive Signature for eval_primitive_ind.

  Section map_eval_prim.
    Context {term term' : Set}.
    Context {eval : term -> term' -> Set}.
    Context {P : forall x y, eval x y -> Type}.
    Context (F : forall x y (e : eval x y), P x y e).

    Equations map_eval_primitive {p : prim_val term} {p' : prim_val term'} (ev : eval_primitive eval p p') : eval_primitive_ind eval P p p' ev :=
    | @evalPrimInt _ _ _ _ := evalPrimIntDep _ _ i;
    | @evalPrimFloat _ _ _ _ := evalPrimFloatDep _ _ f;
    | @evalPrimString _ _ _ _ := evalPrimStringDep _ _ s;
    | @evalPrimArray v def v' def'  ev ed :=
      evalPrimArrayDep _ _ v def v' def' ev ed (map_All2_dep _ F ev) (F _ _ ed).
  End map_eval_prim.

  Local Unset Elimination Schemes.

  Inductive eval : term -> term -> Set :=
  (** Reductions *)
  | eval_box a t t' :
      eval a tBox ->
      eval t t' ->
      eval (tApp a t) tBox

  (** Beta *)
  | eval_beta f na b a a' res :
      eval f (tLambda na b) ->
      eval a a' ->
      eval (csubst a' 0 b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 b1) res

  (** Case *)
  | eval_iota ind pars cdecl discr c args brs br res :
      with_constructor_as_block = false ->
      eval discr (mkApps (tConstruct ind c []) args) ->
      constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
      nth_error brs c = Some br ->
      #|args| = pars + cdecl.(cstr_nargs) ->
      #|skipn pars args| = #|br.1| ->
      eval (iota_red pars args br) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Case *)
  | eval_iota_block ind pars cdecl discr c args brs br res :
      with_constructor_as_block = true ->
      eval discr (tConstruct ind c args) ->
      constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
      nth_error brs c = Some br ->
      #|args| = pars + cdecl.(cstr_nargs) ->
      #|skipn pars args| = #|br.1| ->
      eval (iota_red pars args br) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Singleton case on a proof *)
  | eval_iota_sing ind pars discr brs n f res :
      with_prop_case ->
      eval discr tBox ->
      inductive_isprop_and_pars Σ ind = Some (true, pars) ->
      brs = [ (n,f) ] ->
      eval (substl (repeat tBox #|n|) f) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx argsv a av fn res :
      forall guarded : with_guarded_fix,
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (#|argsv|, fn) ->
      eval (tApp (mkApps fn argsv) av) res ->
      eval (tApp f a) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx argsv a av narg fn :
      forall guarded : with_guarded_fix,
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      (#|argsv| < narg) ->
      eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

  (** Fix unfolding, without guard *)
  | eval_fix' f mfix idx a av fn res narg :
    forall unguarded : with_guarded_fix = false,
    eval f (tFix mfix idx) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    eval a av ->
    eval (tApp fn av) res ->
    eval (tApp f a) res

  (** CoFix-case unfolding *)
  | eval_cofix_case ip mfix idx args discr narg fn brs res :
      eval discr (mkApps (tCoFix mfix idx) args) ->
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip (mkApps fn args) brs) res ->
      eval (tCase ip discr brs) res

  (** CoFix-proj unfolding *)
  | eval_cofix_proj p mfix idx args discr narg fn res :
      eval discr (mkApps (tCoFix mfix idx) args) ->
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p discr) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
      decl.(cst_body) = Some body ->
      eval body res ->
      eval (tConst c) res

  (** Proj *)
  | eval_proj p cdecl discr args a res :
      with_constructor_as_block = false ->
      eval discr (mkApps (tConstruct p.(proj_ind) 0 []) args) ->
      constructor_isprop_pars_decl Σ p.(proj_ind) 0 = Some (false, p.(proj_npars), cdecl) ->
      #|args| = p.(proj_npars) + cdecl.(cstr_nargs) ->
      nth_error args (p.(proj_npars) + p.(proj_arg)) = Some a ->
      eval a res ->
      eval (tProj p discr) res

  (** Proj *)
  | eval_proj_block p cdecl discr args a res :
      with_constructor_as_block = true ->
      eval discr (tConstruct p.(proj_ind) 0 args) ->
      constructor_isprop_pars_decl Σ p.(proj_ind) 0 = Some (false, p.(proj_npars), cdecl) ->
      #|args| = p.(proj_npars) + cdecl.(cstr_nargs) ->
      nth_error args (p.(proj_npars) + p.(proj_arg)) = Some a ->
      eval a res ->
      eval (tProj p discr) res

  (** Proj *)
  | eval_proj_prop p discr :
      with_prop_case ->
      eval discr tBox ->
      inductive_isprop_and_pars Σ p.(proj_ind) = Some (true, p.(proj_npars)) ->
      eval (tProj p discr) tBox

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct ind c mdecl idecl cdecl f args a a' :
    with_constructor_as_block = false ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    eval f (mkApps (tConstruct ind c []) args) ->
    #|args| < cstr_arity mdecl cdecl ->
    eval a a' ->
    eval (tApp f a) (tApp (mkApps (tConstruct ind c []) args) a')

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct_block ind c mdecl idecl cdecl args args' :
    with_constructor_as_block = true ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    #|args| = cstr_arity mdecl cdecl ->
    All2_Set eval args args' ->
    eval (tConstruct ind c args) (tConstruct ind c args')

  (** Atoms (non redex-producing heads) applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f' || isConstructApp f'
        || isPrimApp f' || isLazyApp f')  ->
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

  | eval_force t v v' :
    eval t (tLazy v) ->
    eval v v' ->
    eval (tForce t) v'

  (** Atoms are values (includes abstractions, cofixpoints, constructors and lazy) *)
  | eval_atom t : atom Σ t -> eval t t.

  Hint Constructors eval : core.
  Derive Signature for eval.
  Derive NoConfusionHom for term.

  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

   Variant value_head (nargs : nat) : term -> Type :=
   | value_head_cstr ind c mdecl idecl cdecl :
     with_constructor_as_block = false ->
     lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
     nargs <= cstr_arity mdecl cdecl ->
     value_head nargs (tConstruct ind c [])
   | value_head_cofix mfix idx : value_head nargs (tCoFix mfix idx)
   | value_head_fix mfix idx rarg fn :
     cunfold_fix mfix idx = Some (rarg, fn) ->
     (* If fixpoints are not guarded, we don't need to consider applied fixpoints
        as value heads*)
     (if with_guarded_fix then nargs <= rarg else False) ->
     value_head nargs (tFix mfix idx).
   Derive Signature NoConfusion for value_head.


   Variant primitive_value (value : term -> Type) : prim_val term -> Type :=
    | primIntValue i : primitive_value value (prim_int i)
    | primFloatValue f : primitive_value value (prim_float f)
    | primStringValue s : primitive_value value (prim_string s)
    | primArrayValue a :
      All value a.(array_value) ->
      value a.(array_default) ->
      primitive_value value (prim_array a).
   Derive Signature NoConfusion for primitive_value.

  Variant atomic_value (value : term -> Type) : term -> Type :=
  | atomic_atom t : atom Σ t -> atomic_value value t
  | atomic_primitive p : primitive_value value p -> atomic_value value (tPrim p).
  Derive Signature NoConfusion for atomic_value.
  Hint Constructors atomic_value : core.

   Inductive value : term -> Type :=
   | value_atom t : atomic_value value t -> value t
   | value_constructor ind c mdecl idecl cdecl args :
      with_constructor_as_block = true ->
      lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
      #|args| = cstr_arity mdecl cdecl ->
      All value args -> value (tConstruct ind c args)
   | value_app_nonnil f args : value_head #|args| f -> args <> [] -> All value args -> value (mkApps f args).
   Derive Signature for value.

End Wcbv.

Notation atomic Σ := (atomic_value Σ (value Σ)).

Definition eval_primitive_depth {eval : term -> term -> Set} (size : forall x y, eval x y -> nat) {p p'} (e : eval_primitive eval p p') : nat :=
  match e with
  | evalPrimInt _ => 0
  | evalPrimFloat _ => 0
  | evalPrimString _ => 0
  | evalPrimArray v d v' d' aev ed =>
    all2_size _ size aev + size _ _ ed
  end.

Fixpoint eval_depth {wfl : WcbvFlags} {Σ : EAst.global_declarations} {t1 t2 : EAst.term} (ev : eval Σ t1 t2) { struct ev } : nat.
Proof.
  rename eval_depth into aux.
  destruct ev.
  all:try match goal with
  | [ H : eval _ _ _, H' : eval _ _ _, H'' : eval _ _ _ |- _ ] =>
    apply aux in H; apply aux in H'; apply aux in H''; exact (S (Nat.max H (Nat.max H' H'')))
  | [ H : eval _ _ _, H' : eval _ _ _ |- _ ] =>
    apply aux in H; apply aux in H'; exact (S (Nat.max H H'))
  | [ H : eval _ _ _ |- _ ] => apply aux in H; exact (S H)
  end.
  exact (S (all2_size _ (fun x y ev => aux wfl Σ x y ev) a)).
  exact (S (eval_primitive_depth (aux wfl Σ) e)).
  exact 1.
Defined.

Set Equations Transparent.
Section eval_rect.

  Variables (wfl : WcbvFlags) (Σ : global_declarations) (P : forall x y, eval Σ x y → Type).

  Lemma eval_rect :
    (∀ (a t t' : term) (e : eval Σ a tBox),
     P a tBox e
     → ∀ e0 : eval Σ t t',
         P t t' e0 → P (tApp a t) tBox (eval_box Σ a t t' e e0))
  → (∀ (f0 : term) (na : name) (b a a' res : term)
       (e : eval Σ f0 (tLambda na b)),
       P f0 (tLambda na b) e
       → ∀ e0 : eval Σ a a',
           P a a' e0
           → ∀ e1 : eval Σ (csubst a' 0 b) res,
               P (csubst a' 0 b) res e1
               → P (tApp f0 a) res (eval_beta Σ f0 na b a a' res e e0 e1))
    → (∀ (na : name) (b0 b0' b1 res : term) (e : eval Σ b0 b0'),
         P b0 b0' e
         → ∀ e0 : eval Σ (csubst b0' 0 b1) res,
             P (csubst b0' 0 b1) res e0
             → P (tLetIn na b0 b1) res (eval_zeta Σ na b0 b0' b1 res e e0))
      → (∀ (ind : inductive) (pars : nat) (cdecl : constructor_body)
           (discr : term) (c : nat) (args : list term)
           (brs : list (list name × term)) (br : list name × term)
           (res : term) (e : with_constructor_as_block = false)
           (e0 : eval Σ discr (mkApps (tConstruct ind c []) args)),
           P discr (mkApps (tConstruct ind c []) args) e0
           → ∀ (e1 : constructor_isprop_pars_decl Σ ind c =
                     Some (false, pars, cdecl)) (e2 :
                                                 nth_error brs c =
                                                 Some br)
               (e3 : #|args| = pars + cstr_nargs cdecl)
               (e4 : #|skipn pars args| = #|br.1|)
               (e5 : eval Σ (iota_red pars args br) res),
               P (iota_red pars args br) res e5
               → P (tCase (ind, pars) discr brs) res
                   (eval_iota Σ ind pars cdecl discr c args brs br res e e0
                      e1 e2 e3 e4 e5))
        → (∀ (ind : inductive) (pars : nat) (cdecl : constructor_body)
             (discr : term) (c : nat) (args : list term)
             (brs : list (list name × term)) (br : list name × term)
             (res : term) (e : with_constructor_as_block = true)
             (e0 : eval Σ discr (tConstruct ind c args)),
             P discr (tConstruct ind c args) e0
             → ∀ (e1 : constructor_isprop_pars_decl Σ ind c =
                       Some (false, pars, cdecl))
                 (e2 : nth_error brs c = Some br)
                 (e3 : #|args| = pars + cstr_nargs cdecl)
                 (e4 : #|skipn pars args| = #|br.1|)
                 (e5 : eval Σ (iota_red pars args br) res),
                 P (iota_red pars args br) res e5
                 → P (tCase (ind, pars) discr brs) res
                     (eval_iota_block Σ ind pars cdecl discr c args brs br
                        res e e0 e1 e2 e3 e4 e5))
          → (∀ (ind : inductive) (pars : nat) (discr : term)
               (brs : list (list name × term)) (n : list name)
               (f4 res : term) (i : with_prop_case)
               (e : eval Σ discr tBox),
               P discr tBox e
               → ∀ (e0 : inductive_isprop_and_pars Σ ind = Some (true, pars))
                   (e1 : brs = [(n, f4)]) (e2 : eval Σ
                                                 (substl
                                                 (repeat tBox #|n|) f4) res),
                   P (substl (repeat tBox #|n|) f4) res e2
                   → P (tCase (ind, pars) discr brs) res
                       (eval_iota_sing Σ ind pars discr brs n f4 res i e e0
                          e1 e2))
            → (∀ (f5 : term) (mfix : mfixpoint term)
                 (idx : nat) (argsv : list term) (a av fn res : term)
                 (guarded : with_guarded_fix) (e :
                                               eval Σ f5
                                                 (mkApps
                                                 (tFix mfix idx) argsv)),
                 P f5 (mkApps (tFix mfix idx) argsv) e
                 → ∀ e0 : eval Σ a av,
                     P a av e0
                     → ∀ (e1 : cunfold_fix mfix idx = Some (#|argsv|, fn))
                         (e2 : eval Σ (tApp (mkApps fn argsv) av) res),
                         P (tApp (mkApps fn argsv) av) res e2
                         → P (tApp f5 a) res
                             (eval_fix Σ f5 mfix idx argsv a av fn res
                                guarded e e0 e1 e2))
              → (∀ (f6 : term) (mfix : mfixpoint term)
                   (idx : nat) (argsv : list term)
                   (a av : term) (narg : nat) (fn : term)
                   (guarded : with_guarded_fix) (e :
                                                 eval Σ f6
                                                 (mkApps
                                                 (tFix mfix idx) argsv)),
                   P f6 (mkApps (tFix mfix idx) argsv) e
                   → ∀ e0 : eval Σ a av,
                       P a av e0
                       → ∀ (e1 : cunfold_fix mfix idx = Some (narg, fn))
                           (l : #|argsv| < narg),
                           P (tApp f6 a)
                             (tApp (mkApps (tFix mfix idx) argsv) av)
                             (eval_fix_value Σ f6 mfix idx argsv a av narg fn
                                guarded e e0 e1 l))
                → (∀ (f7 : term) (mfix : mfixpoint term)
                     (idx : nat) (a av fn res : term)
                     (narg : nat) (unguarded : with_guarded_fix = false)
                     (e : eval Σ f7 (tFix mfix idx)),
                     P f7 (tFix mfix idx) e
                     → ∀ (e0 : cunfold_fix mfix idx = Some (narg, fn))
                         (e1 : eval Σ a av),
                         P a av e1
                         → ∀ e2 : eval Σ (tApp fn av) res,
                             P (tApp fn av) res e2
                             → P (tApp f7 a) res
                                 (eval_fix' Σ f7 mfix idx a av fn res narg
                                    unguarded e e0 e1 e2))
                  → (∀ (ip : inductive × nat) (mfix : mfixpoint term)
                       (idx : nat) (args : list term)
                       (discr : term) (narg : nat)
                       (fn : term) (brs : list (list name × term))
                       (res : term) (e : eval Σ discr
                                           (mkApps (tCoFix mfix idx) args)),
                       P discr (mkApps (tCoFix mfix idx) args) e
                       → ∀ (e0 : cunfold_cofix mfix idx = Some (narg, fn))
                           (e1 : eval Σ (tCase ip (mkApps fn args) brs) res),
                           P (tCase ip (mkApps fn args) brs) res e1
                           → P (tCase ip discr brs) res
                               (eval_cofix_case Σ ip mfix idx args discr narg
                                  fn brs res e e0 e1))
                    → (∀ (p : projection) (mfix : mfixpoint term)
                         (idx : nat) (args : list term)
                         (discr : term) (narg : nat)
                         (fn res : term) (e : eval Σ discr
                                                (mkApps
                                                 (tCoFix mfix idx) args)),
                         P discr (mkApps (tCoFix mfix idx) args) e
                         → ∀ (e0 : cunfold_cofix mfix idx = Some (narg, fn))
                             (e1 : eval Σ (tProj p (mkApps fn args)) res),
                             P (tProj p (mkApps fn args)) res e1
                             → P (tProj p discr) res
                                 (eval_cofix_proj Σ p mfix idx args discr
                                    narg fn res e e0 e1))
                      → (∀ (c : kername) (decl : constant_body)
                           (body : term) (isdecl :
                                          declared_constant Σ c decl)
                           (res : term) (e : cst_body decl = Some body)
                           (e0 : eval Σ body res),
                           P body res e0
                           → P (tConst c) res
                               (eval_delta Σ c decl body isdecl res e e0))
                        → (∀ (p : projection) (cdecl : constructor_body)
                             (discr : term) (args : list term)
                             (a res : term) (e : with_constructor_as_block =
                                                 false)
                             (e0 : eval Σ discr
                                     (mkApps (tConstruct (proj_ind p) 0 [])
                                        args)),
                             P discr
                               (mkApps (tConstruct (proj_ind p) 0 []) args)
                               e0
                             → ∀ (e1 : constructor_isprop_pars_decl Σ
                                         (proj_ind p) 0 =
                                       Some (false, proj_npars p, cdecl))
                                 (e2 : #|args| =
                                       proj_npars p + cstr_nargs cdecl)
                                 (e3 : nth_error args
                                         (proj_npars p + proj_arg p) =
                                       Some a) (e4 : eval Σ a res),
                                 P a res e4
                                 → P (tProj p discr) res
                                     (eval_proj Σ p cdecl discr args a res e
                                        e0 e1 e2 e3 e4))
                          → (∀ (p : projection) (cdecl : constructor_body)
                               (discr : term) (args : list term)
                               (a res : term) (e :
                                               with_constructor_as_block =
                                               true)
                               (e0 : eval Σ discr
                                       (tConstruct (proj_ind p) 0 args)),
                               P discr (tConstruct (proj_ind p) 0 args) e0
                               → ∀ (e1 : constructor_isprop_pars_decl Σ
                                           (proj_ind p) 0 =
                                         Some (false, proj_npars p, cdecl))
                                   (e2 : #|args| =
                                         proj_npars p + cstr_nargs cdecl)
                                   (e3 : nth_error args
                                           (proj_npars p + proj_arg p) =
                                         Some a) (e4 : eval Σ a res),
                                   P a res e4
                                   → P (tProj p discr) res
                                       (eval_proj_block Σ p cdecl discr args
                                          a res e e0 e1 e2 e3 e4))
                            → (∀ (p : projection)
                                 (discr : term) (i : with_prop_case)
                                 (e : eval Σ discr tBox),
                                 P discr tBox e
                                 → ∀ e0 : inductive_isprop_and_pars Σ
                                            (proj_ind p) =
                                          Some (true, proj_npars p),
                                     P (tProj p discr) tBox
                                       (eval_proj_prop Σ p discr i e e0))
                              → (∀ (ind : inductive)
                                   (c : nat) (mdecl : mutual_inductive_body)
                                   (idecl : one_inductive_body)
                                   (cdecl : constructor_body)
                                   (f14 : term) (args : list term)
                                   (a a' : term) (e :
                                                 with_constructor_as_block =
                                                 false)
                                   (e0 : lookup_constructor Σ ind c =
                                         Some (mdecl, idecl, cdecl))
                                   (e1 : eval Σ f14
                                           (mkApps (tConstruct ind c []) args)),
                                   P f14 (mkApps (tConstruct ind c []) args)
                                     e1
                                   → ∀ (l : #|args| < cstr_arity mdecl cdecl)
                                       (e2 : eval Σ a a'),
                                       P a a' e2
                                       → P (tApp f14 a)
                                           (tApp
                                              (mkApps
                                                 (tConstruct ind c []) args)
                                              a')
                                           (eval_construct Σ ind c mdecl
                                              idecl cdecl f14 args a a' e e0
                                              e1 l e2))
                                → (∀ (ind : inductive)
                                     (c : nat) (mdecl : mutual_inductive_body)
                                     (idecl : one_inductive_body)
                                     (cdecl : constructor_body)
                                     (args args' :
                                      list term) (e :
                                                 with_constructor_as_block =
                                                 true)
                                     (e0 : lookup_constructor Σ ind c =
                                           Some (mdecl, idecl, cdecl))
                                     (e1 : #|args| = cstr_arity mdecl cdecl)
                                     (a : All2_Set (eval Σ) args args')
                                     (iha : All2_over a P),
                                     P (tConstruct ind c args)
                                       (tConstruct ind c args')
                                       (eval_construct_block Σ ind c mdecl
                                          idecl cdecl args args' e e0 e1 a))
                                  → (∀ (f16 f' a a' : term)
                                       (e : eval Σ f16 f'),
                                       P f16 f' e
                                       → ∀ (i : ~~
                                                (isLambda f'
                                                 ||
                                                 (if with_guarded_fix
                                                 then isFixApp f'
                                                 else isFix f') ||
                                                 isBox f'
                                                 ||
                                                 isConstructApp f'
                                                 || isPrimApp f' || isLazyApp f'))
                                           (e0 : eval Σ a a'),
                                           P a a' e0
                                           → P (tApp f16 a)
                                               (tApp f' a')
                                               (eval_app_cong Σ f16 f' a a' e
                                                 i e0)) ->


    (forall p p' (ev : eval_primitive (eval Σ) p p'),
      eval_primitive_ind _ P _ _ ev ->
      P (tPrim p) (tPrim p') (eval_prim _ _ _ ev)) ->
    (forall t t' v (ev1 : eval Σ t (tLazy t')) (ev2 : eval Σ t' v),
      P _ _ ev1 -> P _ _ ev2 ->
      P (tForce t) v (eval_force _ t t' v ev1 ev2))

    → (∀ (t : term) (i : atom Σ t),
          P t t (eval_atom Σ t i))
      → ∀ (t t0 : term) (e : eval Σ t t0),
          P t t0 e.
  Proof using Type.
    intros ??????????????????????? H.
    revert t t0 H.
    fix aux 3.
    move aux at top.
    intros t t0 H.
    destruct H.
    all:try match goal with
    | [ H : _ |- _ ] =>
      eapply H; (unshelve eapply aux || tea); tea; cbn; try lia
    end.
    exact (map_All2_dep _ aux a).
    exact (map_eval_primitive aux e).
  Qed.

  Definition eval_rec := eval_rect.
  Definition eval_ind := eval_rect.

End eval_rect.

Global Hint Constructors value : value.

Section Wcbv.
  Context {wfl : WcbvFlags}.
  Context {Σ : global_declarations}.
  Abbreviation eval := (eval Σ).
  Abbreviation value_head := (value_head Σ).
  Abbreviation value := (value Σ).

  Lemma value_app f args : value_head #|args| f -> All value args -> value (mkApps f args).
  Proof.
    destruct args.
    - intros [] hv; do 2 constructor; try easy. cbn [atom mkApps]. now rewrite e e0.
    - intros vh av. eapply value_app_nonnil => //.
  Qed.

  Lemma value_values_ind : forall P : term -> Type,
  (forall t, atom Σ t -> P t) ->
  (forall p, primitive_value value p -> primitive_value P p -> P (tPrim p)) ->
       (forall (ind : inductive) (c : nat) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body)
         (args : list term) (e : with_constructor_as_block = true) (e0 : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl))
          (l : #|args| = cstr_arity mdecl cdecl) (a : All value args) , All P args ->
       P (tConstruct ind c args)) ->
      (forall f args, value_head #|args| f -> args <> [] -> All value args -> All P args -> P (mkApps f args)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P X X0 X1 X2.
    fix value_values_ind 2. destruct 1.
    - destruct a.
      + apply X; auto.
      + eapply X0; tea. destruct p0; constructor; eauto. exact (make_All_All value_values_ind a0).
    - eapply X1; auto; tea. clear -a value_values_ind. induction a; econstructor; auto.
    - eapply X2; auto; tea.
      clear v n. revert args a. fix aux 2. destruct 1. constructor; auto.
      constructor. now eapply value_values_ind. now apply aux.
  Defined.

  Lemma value_head_nApp {nargs t} : value_head nargs t -> ~~ isApp t.
  Proof. destruct 1; auto. Qed.
  Hint Resolve value_head_nApp : core.

  Lemma isStuckfix_nApp {t args} : isStuckFix t args -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve isStuckfix_nApp : core.

  Lemma atom_nApp {t} : atom Σ t -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve atom_nApp : core.

  Lemma value_mkApps_inv t l :
    ~~ isApp t ->
    value (mkApps t l) ->
    ((l = []) × atomic Σ t)
    + (l = [] × ∑ ind c mdecl idecl cdecl args, [ × with_constructor_as_block , lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl),    t = tConstruct ind c args, #|args| = cstr_arity mdecl cdecl & All value args])
    + ([× l <> [], value_head #|l| t & All value l]).
  Proof.
    intros H H'. generalize_eq x (mkApps t l).
    revert x H' t H. apply: value_values_ind.
    - intros. subst.
      eapply atom_mkApps in H as []. do 2 left. intuition eauto. now constructor.
    - intros. depelim X0; solve_discr; do 2 left; split => //; constructor 2; eauto.
    - intros * wcon lup len H IH t ht hcon.
      destruct l using rev_ind.
      + cbn in hcon. invs hcon. left. right.
        repeat eexists; eauto.
      + rewrite mkApps_app in hcon. invs hcon.
    - intros * vh nargs hargs ih t isapp appeq.
      move: (value_head_nApp vh) => Ht.
      right. apply mkApps_eq_inj in appeq => //. intuition subst; auto => //.
  Qed.

  Lemma value_mkApps_values t l :
    value (mkApps t l) ->
    ~~ isApp t ->
    All value l.
  Proof.
    intros val not_app.
    now apply value_mkApps_inv in val as [[(-> & ?) | [-> ] ] |[]].
  Qed.

  Lemma eval_Construct_inv ind c args e  :
     eval (tConstruct ind c args) e ->
     ∑ args', e = tConstruct ind c args' × All2 eval args args'.
  Proof.
    intros H. depind H.
    - repeat eexists; eauto.
    - invs i. destruct args; invs H0. exists []. repeat econstructor.
  Qed.

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    intros ev. induction ev; simpl; intros; eauto with value.

    - change (tApp ?h ?a) with (mkApps h [a]).
      rewrite -mkApps_app.
      apply value_mkApps_inv in IHev1; [|easy].
      destruct IHev1 as [[(-> & _) | [-> ] ] |[]].
      + apply value_app; auto. len.
        cbn in *. econstructor; tea.
        destruct with_guarded_fix => //. cbn; auto.
      + apply value_app; auto. len.
        cbn in *. econstructor; tea.
        destruct with_guarded_fix => //. cbn; auto.
      + depelim v. rewrite e1 in e. noconf e.
        eapply value_app; auto. econstructor; tea.
        destruct with_guarded_fix => //.
        len; lia. apply All_app_inv; auto.

    - apply value_mkApps_inv in IHev1; [|easy].
      destruct IHev1 as [[(-> & _)|[-> ]] | []].
      + cbn. eapply (value_app _ [a']); cbn; auto. econstructor; tea.
      + cbn. eapply (value_app _ [a']); cbn; auto. econstructor; tea.
      + rewrite -[tApp _ _](mkApps_app _ _ [a']).
        eapply value_app. cbn; auto. econstructor; tea. cbn; len.
        eapply All_app_inv; auto.

    - econstructor 2; tea. now rewrite -(All2_length a).
      clear -a iha. induction a. constructor.
      destruct iha as [va' ih].
      constructor. exact va'. now apply IHa.

    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHev1 => //.
      destruct IHev1 as [?|[]]; intuition subst.
      * rewrite a1 in i |- *. simpl in *.
        apply (value_app f [a']).
        depelim b. 2:{ cbn in i. rewrite !negb_or /= in i; rtoProp; intuition auto. }
        destruct t; simpl in * |- *; try congruence.
        + rewrite !negb_or /= in i1; rtoProp; intuition auto.
        + rewrite !negb_or /= in i1; rtoProp; intuition auto.
        + destruct with_guarded_fix.
          now cbn in i1. now cbn in i1.
        + constructor.
        + now destruct with_guarded_fix; cbn in i1.
        + cbn in i. destruct with_guarded_fix; cbn in i; rtoProp; intuition auto.
      * destruct b0 as (ind & c & mdecl & idecl & cdecl & args & [H1 H2 H3 H4]).
        rewrite -[tApp _ _](mkApps_app _ (firstn n l) [a']).
        rewrite a0 in i |- *. simpl in *.
        apply (value_app f [a']).
        destruct f; simpl in * |- *; try congruence.
        + rewrite !negb_or /= in i; rtoProp; intuition auto.
        + destruct with_guarded_fix. now cbn in i. now cbn in i.
      * rewrite -[tApp _ _](mkApps_app _ (firstn n l) [a']).
        eapply value_app; eauto with pcuic. 2:eapply All_app_inv; auto.
        len.
        rewrite isFixApp_mkApps isConstructApp_mkApps // in i.
        rewrite !negb_or in i. rtoProp; intuition auto.
        destruct with_guarded_fix eqn:gfix.
        { destruct v; cbn in * => //. constructor. }
      { destruct v; cbn in * => //; try now constructor.
        now rewrite gfix in y. }
    - depelim X; constructor; constructor 2; constructor; solve_all.
      clear -ev a. induction ev. constructor.
      destruct a as [va' ih].
      constructor. exact va'. now apply IHev.
    - now do 2 constructor.
  Qed.

  Lemma value_head_spec n t :
    value_head n t -> (~~ (isLambda t || isBox t)).
  Proof.
    destruct 1; simpl => //.
  Qed.

  Lemma value_head_final n t :
    value_head n t -> eval t t.
  Proof.
    destruct 1.
    - constructor; try easy. now cbn [atom]; rewrite e e0.
    - now eapply eval_atom.
    - now eapply eval_atom.
  Qed.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma value_head_spec' n t :
    value_head n t -> (~~ (isLambda t || isBox t)) && atom Σ t.
  Proof.
    induction 1; auto. cbn [atom]; rewrite e e0 //.
  Qed.


  Lemma closed_fix_substl_subst_eq {mfix idx d} :
    closed (tFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (fix_subst mfix) (dbody d) = substl (fix_subst mfix) (dbody d).
  Proof.
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

  Lemma closed_unfold_fix_cunfold_eq mfix idx :
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = cunfold_fix mfix idx.
  Proof.
    unfold unfold_fix, cunfold_fix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    intros cl; f_equal; f_equal.
    now rewrite (closed_fix_substl_subst_eq cl).
  Qed.

  Lemma closed_cofix_substl_subst_eq {mfix idx d} :
    closed (tCoFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (cofix_subst mfix) (dbody d) = substl (cofix_subst mfix) (dbody d).
  Proof.
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

  Lemma closed_unfold_cofix_cunfold_eq mfix idx :
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = cunfold_cofix mfix idx.
  Proof.
    unfold unfold_cofix, cunfold_cofix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    intros cl; f_equal; f_equal.
    now rewrite (closed_cofix_substl_subst_eq cl).
  Qed.

  Lemma eval_mkApps_tCoFix mfix idx args v :
    eval (mkApps (tCoFix mfix idx) args) v ->
    exists args', v = mkApps (tCoFix mfix idx) args'.
  Proof.
    revert v.
    induction args using List.rev_ind; intros v ev.
    + exists [].
      now depelim ev.
    + rewrite mkApps_app in ev.
      cbn in *.
      depelim ev;
        try (apply IHargs in ev1 as (? & ?); solve_discr).
      * apply IHargs in ev1 as (argsv & ->).
        exists (argsv ++ [a']).
        now rewrite mkApps_app.
      * easy.
  Qed.

  Lemma eval_mkApps_tFix_inv mfix idx args v :
   with_guarded_fix ->
    eval (mkApps (tFix mfix idx) args) v ->
    (exists args', v = mkApps (tFix mfix idx) args' /\ #|args| = #|args'|) \/
    (exists n b, cunfold_fix mfix idx = Some (n, b) /\ n < #|args|).
  Proof.
    revert v.
    induction args using List.rev_ind; intros wg v ev.
    + left. exists [].
      now depelim ev.
    + rewrite mkApps_app in ev.
      cbn in *.
      depelim ev.
      all: try (eapply IHargs in ev1 as [(? & ? & Heq) | (? & ? & ? & ?)]; eauto; rewrite ?Heq; try solve_discr;
        len; rewrite ?Heq; rewrite Nat.add_comm; eauto 7).
      * invs H. eauto 9.
      * invs H. left. exists (x0 ++ [av]). rewrite mkApps_app. cbn. split. eauto. len.
      * subst. rewrite isFixApp_mkApps in i => //. rewrite v in i. cbn in i.
        destruct isLambda; cbn in i; easy.
      * invs i.
  Qed.

  Lemma value_app_inv L : value (mkApps tBox L) -> L = nil.
  Proof.
    intro X. depelim X.
    - destruct L using rev_ind.
      reflexivity.
      rewrite mkApps_app in a. now inv a.
    - EAstUtils.solve_discr.
    - EAstUtils.solve_discr. depelim v.
  Qed.

  Lemma eval_to_mkApps_tBox_inv t argsv :
    eval t (mkApps tBox argsv) ->
    argsv = [].
  Proof.
    intros ev.
    apply eval_to_value in ev.
    now apply value_app_inv in ev.
  Qed.

  Lemma eval_stuck_Fix {f mfix idx args args'} :
    with_guarded_fix ->
    eval f (tFix mfix idx) ->
    All2 eval args args' ->
    isStuckFix (tFix mfix idx) args ->
    eval (mkApps f args) (mkApps (tFix mfix idx) args').
  Proof.
    intros wgf evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      destruct cunfold_fix as [[rarg fn]|] eqn:eqc => //.
      len; cbn. move/Nat.leb_le => hrarg.
      eapply eval_fix_value. auto.
      eapply IHargs => //. unfold isStuckFix. rewrite eqc. apply Nat.leb_le; lia. auto. tea.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma stuck_fix_value_inv argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    (All value argsv × isStuckFix (tFix mfix idx) argsv).
  Proof.
    remember (mkApps (tFix mfix idx) argsv) as tfix.
    intros hv; revert Heqtfix.
    move: tfix hv; apply: value_values_ind.
    - intros * isatom eq; subst.
      unfold atom in isatom. destruct argsv using rev_case => //.
      split; auto. simpl. simpl in isatom. rewrite H //.
      rewrite mkApps_app /= // in isatom.
    - intros; solve_discr.
    - intros. solve_discr.
    - intros * vf hargs vargs ihargs eq. solve_discr => //. depelim vf. rewrite e.
      intros [= <- <-]. destruct with_guarded_fix => //. split => //.
      unfold isStuckFix. rewrite e. now apply Nat.leb_le.
  Qed.

  Lemma stuck_fix_value_args argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|argsv| <= narg.
  Proof.
    intros val unf.
    eapply stuck_fix_value_inv in val; eauto.
    destruct val.
    simpl in i. rewrite unf in i.
    now eapply Nat.leb_le in i.
  Qed.

  Lemma eval_mkApps_Construct ind c mdecl idecl cdecl f args args' :
    with_constructor_as_block = false ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    eval f (tConstruct ind c []) ->
    #|args| <= cstr_arity mdecl cdecl ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tConstruct ind c []) args').
  Proof.
    intros hblock hdecl evf hargs. revert args'.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. now cbn.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite mkApps_app /=. len in hargs. cbn in hargs.
      rewrite mkApps_app.
      eapply eval_construct; tea.
      eapply IHargs => //. lia.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma eval_mkApps_Construct_block ind c mdecl idecl cdecl f args args' :
    with_constructor_as_block ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    eval f (tConstruct ind c []) ->
    #|args| = cstr_arity mdecl cdecl ->
    All2 eval args args' ->
    eval (tConstruct ind c args) (tConstruct ind c args').
  Proof.
    intros. econstructor; tea. auto.
  Qed.

  Lemma eval_mkApps_CoFix f mfix idx args args' :
    eval f (tCoFix mfix idx) ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tCoFix mfix idx) args').
  Proof.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_app_cong; tea.
      eapply IHargs => //.
      rewrite isFixApp_mkApps // /= isConstructApp_mkApps // !negb_or isPrimApp_mkApps isLazyApp_mkApps.
      rtoProp; intuition auto.
      apply nisLambda_mkApps => //.
      destruct with_guarded_fix => //; eapply nisFix_mkApps => //.
      apply nisBox_mkApps => //.
  Qed.

  Lemma eval_mkApps_tBox f args args' :
    eval f tBox ->
    All2 eval args args' ->
    eval (mkApps f args) tBox.
  Proof.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_box; tea.
      eapply IHargs => //. eapply evl.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    eval f f' ->
    value_head #|l| f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof.
    revert l'. induction l using rev_ind; intros l' evf vf' evl.
    depelim evl. eapply evf.
    eapply All2_app_inv_l in evl as (?&?&?&?&?).
    intuition auto. subst. depelim a0. depelim a0.
    - destruct vf'.
      * eapply eval_mkApps_Construct; tea. eapply All2_app; auto.
      * eapply eval_mkApps_CoFix; auto. eapply All2_app; auto.
      * destruct with_guarded_fix eqn:wgf => //.
        eapply eval_stuck_Fix; tea. eapply All2_app; auto.
        unfold isStuckFix; rewrite e0. now apply Nat.leb_le.
  Qed.

  Lemma value_final e : value e -> eval e e.
  Proof.
    move: e; eapply value_values_ind; simpl; intros; eauto with value.
    - now constructor.
    - depelim X0; constructor; try constructor.
      destruct a; constructor; cbn in *; eauto.
      assert (All2 eval array_value array_value) by solve_all; eauto.
    - assert (All2 eval args args).
      { clear -X; induction X; constructor; auto. }
      econstructor; tea; auto.
    - assert (All2 eval args args).
      { let X0 := match goal with H : All (fun t => eval t t) _ |- _ => H end in
        clear -X0; induction X0; constructor; auto. }
      eapply eval_mkApps_cong => //. now eapply value_head_final.
  Qed.

  Set Equations With UIP.

  Unset SsrRewrite.
  Lemma eval_unique_sig {t v v'} :
    forall (ev1 : eval t v) (ev2 : eval t v'),
      {| pr1 := v; pr2 := ev1 |} = {| pr1 := v'; pr2 := ev2 |}.
  Proof.
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
    depind ev; intros v' ev'.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1). noconf IHev1.
      specialize (IHev2 _ ev'2). noconf IHev2. cbn in i.
      exfalso. destruct (@with_guarded_fix wfl); easy.
    - depelim ev'; go.
    - depelim ev'; go.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        apply (f_equal pr1) in IHev1 as apps_eq. cbn in apps_eq.
        apply mkApps_eq_inj in apps_eq as (eq1 & eq2); try easy.
        noconf eq1. noconf eq2.
        noconf IHev1.
        assert (e = e0) by apply uip. subst e0.
        pose proof e1. rewrite e5 in H. noconf H.
        assert (e1 = e5) by apply uip. subst e5.
        assert (br0 = br) as -> by congruence.
        rewrite -> (uip e8 e4), (uip e2 e6), (uip e3 e7), (uip e4 e8).
        specialize (IHev2 _ ev'2); noconf IHev2.
        reflexivity.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        pose proof e1. rewrite e5 in H. noconf H.
        assert (br0 = br) as -> by congruence.
        rewrite -> (uip e e0), (uip e1 e5), (uip e8 e4), (uip e2 e6), (uip e3 e7), (uip e4 e8).
        specialize (IHev2 _ ev'2); noconf IHev2.
        reflexivity.
    - depelim ev'; try go.
      + subst.
        noconf e2.
        simpl.
        specialize (IHev1 _ ev'1); noconf IHev1. simpl.
        pose proof (uip e0 e). subst.
        pose proof (uip i i0). subst i0.
        now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        assert (fn0 = fn) as -> by congruence.
        assert (e1 = e) as -> by now apply uip.
        rewrite (uip guarded guarded0).
        now specialize (IHev3 _ ev'3); noconf IHev3.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        exfalso; rewrite e1 in e.
        noconf e.
        lia.
      + specialize (IHev1 _ ev'1).
        noconf IHev1.
        exfalso.
        rewrite guarded in i.
        rewrite isFixApp_mkApps in i; try easy.
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
        rewrite (uip guarded guarded0).
        now assert (l0 = l) as -> by now apply PCUICWcbvEval.le_irrel.
      + specialize (IHev1 _ ev'1).
        noconf IHev1.
        exfalso.  rewrite guarded in i.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
    - depelim ev'; try go.
      + move: (IHev1 _ ev'1).
        eapply DepElim.simplification_sigma1 => heq IHev1'.
        assert (narg0 = narg) as -> by congruence.
        assert (fn0 = fn) as -> by congruence.
        noconf IHev1'.
        assert (e0 = e) as -> by now apply uip.
        rewrite (uip unguarded unguarded0).
        cbn in *; subst.
        specialize (IHev2 _ ev'2). noconf IHev2.
        now specialize (IHev3 _ ev'3); noconf IHev3.
      + exfalso. rewrite unguarded in i.
        specialize (IHev1 _ ev'1). depelim IHev1. easy.
    - depelim ev'; try go.
      move: (IHev1 _ ev'1).
      eapply DepElim.simplification_sigma1 => heq IHev1'.
      apply mkApps_eq_inj in heq as H'; auto.
      destruct H' as (H' & <-). noconf H'.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      noconf IHev1'.
      assert (e0 = e) as -> by now apply uip.
      cbn in *; subst.
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      move: (IHev1 _ ev'1).
      eapply DepElim.simplification_sigma1 => heq IHev1'.
      apply mkApps_eq_inj in heq as H'; auto.
      destruct H' as (H' & <-). noconf H'.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      noconf IHev1'.
      assert (e0 = e) as -> by now apply uip.
      cbn in *; subst.
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      unfold EGlobalEnv.declared_constant in *.
      assert (decl0 = decl) as -> by congruence.
      assert (body0 = body) as -> by congruence.
      assert (e0 = e) as -> by now apply uip.
      assert (isdecl0 = isdecl) as -> by now apply uip.
      now specialize (IHev _ ev'); noconf IHev.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1).
      pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
      noconf H. noconf IHev1.
      assert (a0 = a) as -> by congruence.
      pose proof e1 as e'. rewrite e4 in e'; noconf e'.
      rewrite -> (uip e6 e3), (uip e1 e4), (uip e2 e5).
      rewrite -> (uip e e0).
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1); noconf IHev1.
      assert (a0 = a) as -> by congruence.
      pose proof e1 as e'. rewrite e4 in e'; noconf e'.
      rewrite -> (uip e e0), (uip e1 e4). cbn.
      rewrite -> (uip e3 e6), (uip e2 e5).
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      specialize (IHev _ ev'). noconf IHev.
      rewrite (uip e e0).
      now rewrite (uip i i0).
    - depelim ev'; try now go.
      + move: (IHev1 _ ev'1).
        eapply DepElim.simplification_sigma1 => heq IHev1'.
        apply mkApps_eq_inj in heq as H'; auto.
        destruct H' as (H' & <-). noconf H'.
        noconf IHev1'.
        pose proof e0 as e'. rewrite e2 in e'; noconf e'.
        specialize (IHev2 _ ev'2). noconf IHev2.
        now rewrite -> (uip e e1), (uip e0 e2), (PCUICWcbvEval.le_irrel _ _ l l0).
      + specialize (IHev1 _ ev'1). noconf IHev1.
        exfalso. rewrite isConstructApp_mkApps in i.
        cbn in i. rewrite !negb_or in i. rtoProp; intuition auto.
    - depelim ev'; try go.
      + pose proof e0. rewrite e3 in H; noconf H.
        rewrite -> (uip e0 e3); clear e0.
        rewrite -> (uip e1 e4); clear e1.
        rewrite -> (uip e e2); clear e.
        assert ({| pr1 := args'; pr2 := a |} = {| pr1 := args'0; pr2 := a0 |}). clear -iha.
        { induction a in iha, args'0, a0 |- *. cbn. depelim a0. reflexivity.
          destruct iha. depelim a0.
          specialize (IHa a1). specialize (IHa _ a0). noconf IHa.
          specialize (e _ e0). now noconf e. }
        now noconf H.
      + exfalso. invs i. destruct args; invs H0.
        rewrite e in H1; cbn in H1. discriminate.
    - depelim ev'; try go.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rtoProp; intuition auto.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rewrite guarded in i. rtoProp; intuition auto.
        rewrite isFixApp_mkApps in H4 => //.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rewrite guarded in i. rtoProp; intuition auto.
        rewrite isFixApp_mkApps in H4 => //.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rewrite unguarded in i. now cbn in i.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rtoProp; intuition auto.
        now rewrite isConstructApp_mkApps in H2.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        now assert (i0 = i) as -> by now apply uip.
    - depelim ev'; try go.
      depelim X; try depelim e; try constructor.
      depelim e0.
      subst a' a0 a1 a'0. cbn.
      specialize (e _ ed0). noconf e.
      assert (v' = v'0) as <-; auto.
      clear -ev0 a.
      induction ev in a, v'0, ev0 |- *; depelim ev0; eauto. f_equal; eauto. destruct a. specialize (e0 _ e). now noconf e0.
      destruct a. specialize (IHev a). eauto.
      assert (ev = ev0) as <-; auto.
      induction ev in a, ev0 |- *; depelim ev0; eauto.
      destruct a.
      f_equal; eauto. specialize (e0 _ e). now noconf e0.
    - depelim ev'; go.
    - depelim ev'; try go.
      2: now assert (i0 = i) as -> by now apply uip.
      exfalso. invs i. rewrite e in H0. destruct args; cbn in H0; invs H0.
  Qed.

  Lemma eval_unique {t v} :
    forall (ev1 : eval t v) (ev2 : eval t v),
      ev1 = ev2.
  Proof.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.

  Lemma eval_deterministic {t v v'} :
    eval t v ->
    eval t v' ->
    v = v'.
  Proof.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.

  Lemma eval_value v v' :
    value v -> eval v v' -> v = v'.
  Proof.
    intros isv ev.
    now pose proof (eval_deterministic ev (value_final _ isv)).
  Qed.

  Lemma eval_deterministic_all {t v v'} :
    All2 eval t v ->
    All2 eval t v' ->
    v = v'.
  Proof.
    induction 1 in v' |- *; intros H'; depelim H'; auto. f_equal; eauto.
    now eapply eval_deterministic.
  Qed.

  Lemma eval_trans' {e e' e''} :
    eval e e' -> eval e' e'' -> e' = e''.
  Proof.
    intros ev ev'.
    eapply eval_to_value in ev.
    eapply value_final in ev.
    eapply (eval_deterministic ev ev').
  Qed.

  Lemma eval_trans {e e' e''} :
    eval e e' -> eval e' e'' -> eval e e''.
  Proof.
    intros ev ev'.
    enough (e' = e'') by now subst.
    eapply eval_trans'; eauto.
  Qed.

  Set SsrRewrite.

  Lemma eval_mkApps_inv f args v :
    eval (mkApps f args) v ->
    ∑ f', eval f f' ×  eval (mkApps f' args) v.
  Proof.
    revert f v; induction args using rev_ind; cbn; intros f v.
    - intros ev. exists v. split => //. eapply eval_to_value in ev.
      now eapply value_final.
    - rewrite mkApps_app. intros ev.
      depelim ev.
      + specialize (IHargs _ _ ev1) as [f' [evf' evars]].
        exists f'. split => //.
        rewrite mkApps_app.
        econstructor; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' evars]].
        exists f'. split => //.
        rewrite mkApps_app.
        eapply eval_beta; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_fix; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_fix_value; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_fix'; eauto.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_construct; eauto.
      + specialize (IHargs _ _ ev1) as [f'' [evf' ev]].
        exists f''; split => //.
        rewrite mkApps_app.
        eapply eval_app_cong; tea.
      + cbn in i. discriminate.
  Qed.

End Wcbv.

(*
Lemma eval_mkApps_inv' Σ f args v :
  @eval target_wcbv_flags Σ (mkApps f args) v ->
  ∑ f', @eval target_wcbv_flags Σ f f' × ∑ args', All2 (@eval target_wcbv_flags  Σ) args args' × @eval target_wcbv_flags Σ (mkApps f' args') v.
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v. split => //. eapply eval_to_value in ev.
    exists []. split. econstructor. cbn.
    now eapply value_final.
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [evf' [args' [Hargs' evars]]]].
      exists f'. split => //.
      eexists. split. eapply All2_app; eauto.
      rewrite mkApps_app.
      econstructor; tea.
      eapply value_final; eapply eval_to_value; eauto.
    + specialize (IHargs _ _ ev1) as [f' [evf' [args' [Hargs' evars]]]].
      exists f'. split => //.
      eexists. split. eapply All2_app; eauto.
      rewrite mkApps_app.
      eapply eval_beta; tea.
      eapply value_final; eapply eval_to_value; eauto.
    + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
      exists f'; split => //. (*
      rewrite mkApps_app.
      eapply eval_fix; tea. *)
    + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
      exists f'; split => //.
      (* rewrite mkApps_app.
      eapply eval_fix_value; tea. *)
    + specialize (IHargs _ _ ev1) as [f' [evf' [args' [Hargs' evars]]]].
      exists f'. split => //.
      eexists. split. eapply All2_app; eauto.>
      rewrite mkApps_app.

    specialize (IHargs _ _ ev1) as [f' [evf' ev]].
      exists f'; split => //.
      rewrite mkApps_app.
      eapply eval_fix'; eauto.
    + specialize (IHargs _ _ ev1) as [f'' [evf' ev]].
      exists f''; split => //.
      rewrite mkApps_app.
      eapply eval_app_cong; tea.
    + cbn in i. discriminate.
Qed.*)

Arguments eval_unique_sig {_ _ _ _ _}.
Arguments eval_deterministic {_ _ _ _ _}.
Arguments eval_unique {_ _ _ _}.

Section WcbvEnv.
  Context {wfl : WcbvFlags} {efl : EEnvFlags}.

  Lemma weakening_eval_env {Σ Σ'} :
    wf_glob Σ' -> extends Σ Σ' ->
    forall v t, eval Σ v t -> eval Σ' v t.
  Proof.
    intros wf ex t v ev.
    induction ev; try solve [econstructor;
      eauto using (extends_lookup_constructor wf ex), (extends_constructor_isprop_pars_decl wf ex), (extends_is_propositional wf ex)].
    - econstructor; eauto.
      red in isdecl |- *. eauto using extends_lookup.
    - econstructor; tea.
      eauto using extends_lookup_constructor.
      clear -a iha. induction a; constructor; eauto. apply iha. apply IHa, iha.
    - constructor.
      depelim X; constructor; eauto.
      eapply All2_over_undep in a. now eapply All2_All2_Set.
    - constructor.
      destruct t => //. cbn [atom] in i. destruct args => //. destruct lookup_constructor eqn:hl => //.
      eapply (extends_lookup_constructor wf ex) in hl. now cbn [atom].
      cbn in i. now rewrite andb_false_r in i.
  Qed.

End WcbvEnv.

(* we could register but then some variable names change *)
#[register=no] Scheme eval_nondep := Minimality for eval Sort Prop.

Lemma isLambda_mkApps f l : ~~ isLambda f -> ~~ EAst.isLambda (mkApps f l).
Proof.
  induction l using rev_ind; simpl; auto => //.
  intros isf; specialize (IHl isf).
  now rewrite mkApps_app.
Qed.

Lemma isBox_mkApps f l : ~~ isBox f -> ~~ isBox (mkApps f l).
Proof.
  induction l using rev_ind; simpl; auto => //.
  intros isf; specialize (IHl isf).
  now rewrite mkApps_app.
Qed.


Lemma closedn_mkApps k f args : closedn k (mkApps f args) = closedn k f && forallb (closedn k) args.
Proof.
  induction args in f |- *; simpl; auto.
  ring. rewrite IHargs /=. ring.
Qed.

Lemma closed_fix_subst mfix :
  forallb (EAst.test_def (closedn (#|mfix| + 0))) mfix ->
  forallb (closedn 0) (fix_subst mfix).
Proof.
  solve_all.
  unfold fix_subst.
  move: #|mfix| => n.
  induction n. constructor.
  cbn. rewrite H IHn //.
Qed.

Lemma closed_cofix_subst mfix :
  forallb (EAst.test_def (closedn (#|mfix| + 0))) mfix ->
  forallb (closedn 0) (cofix_subst mfix).
Proof.
  solve_all.
  unfold cofix_subst.
  move: #|mfix| => n.
  induction n. constructor.
  cbn. rewrite H IHn //.
Qed.

Lemma closed_cunfold_fix mfix idx n f :
  closed (EAst.tFix mfix idx) ->
  cunfold_fix mfix idx = Some (n, f) ->
  closed f.
Proof.
  move=> cl.
  rewrite /cunfold_fix.
  destruct nth_error eqn:heq => //.
  cbn in cl.
  have := (nth_error_forallb heq cl) => cld.
  move=> [=] _ <-.
  eapply closed_substl. now eapply closed_fix_subst.
  rewrite fix_subst_length.
  apply cld.
Qed.

Lemma closed_cunfold_cofix mfix idx n f :
  closed (EAst.tCoFix mfix idx) ->
  cunfold_cofix mfix idx = Some (n, f) ->
  closed f.
Proof.
  move=> cl.
  rewrite /cunfold_cofix.
  destruct nth_error eqn:heq => //.
  cbn in cl.
  have := (nth_error_forallb heq cl) => cld.
  move=> [=] _ <-.
  eapply closed_substl. now eapply closed_cofix_subst.
  rewrite cofix_subst_length.
  apply cld.
Qed.

Lemma lookup_env_closed {Σ kn decl} : EGlobalEnv.closed_env Σ -> EGlobalEnv.lookup_env Σ kn = Some decl -> EGlobalEnv.closed_decl decl.
Proof.
  induction Σ; cbn => //.
  move/andP => [] cla cle.
  destruct (eqb_spec kn a.1).
  move=> [= <-]. apply cla.
  now eapply IHΣ.
Qed.

Lemma All2_over_impl {A : Set} (P : A -> A -> Set) l l' (a : All2_Set P l l') {Q R}
  (ha : All2_over a (fun t u _ => Q t u)) (arl : All R l) :
  (forall x y, Q x y -> R x -> R y) -> All R l'.
Proof.
  intros qr.
  induction a; constructor.
  - eapply qr. eapply ha. now depelim arl.
  - depelim arl. eapply IHa. apply ha. apply arl.
Qed.

(** Evaluation preserves closedness: *)
Lemma eval_closed {wfl : WcbvFlags} Σ :
  closed_env Σ ->
  forall t u, closed t -> eval Σ t u -> closed u.
Proof.
  move=> clΣ t u Hc ev. move: Hc.
  induction ev; simpl in *; auto;
    (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
  - eapply IHev3. rewrite ECSubst.closed_subst //. auto.
    eapply closedn_subst; tea. cbn. rewrite andb_true_r. auto. cbn. auto.
  - eapply IHev2.
    rewrite ECSubst.closed_subst; auto.
    eapply closedn_subst; tea. cbn. rewrite andb_true_r. auto.
  - specialize (IHev1 Hc).
    move: IHev1; rewrite closedn_mkApps => /andP[] _ clargs.
    apply IHev2. rewrite /iota_red.
    eapply closed_substl. now rewrite forallb_rev forallb_skipn.
    len. rewrite e4. eapply nth_error_forallb in Hc'; tea.
    now rewrite Nat.add_0_r in Hc'.
  - specialize (IHev1 Hc).
    apply IHev2. rewrite /iota_red.
    eapply closed_substl. now rewrite forallb_rev forallb_skipn.
    len. rewrite e4. eapply nth_error_forallb in Hc'; tea.
    now rewrite Nat.add_0_r in Hc'.
  - subst brs. cbn in Hc'. rewrite andb_true_r in Hc'.
    eapply IHev2. eapply closed_substl.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length.
  - eapply IHev3.
    apply/andP.
    split; [|easy].
    specialize (IHev1 Hc).
    rewrite closedn_mkApps in IHev1.
    move/andP: IHev1 => [clfix clargs].
    rewrite closedn_mkApps clargs andb_true_r.
    eapply closed_cunfold_fix; tea.
  - apply andb_true_iff.
    split; [|easy].
    solve_all.
  - eapply IHev3. rtoProp. split; eauto.
    eapply closed_cunfold_fix; tea. eauto.
  - eapply IHev2. rewrite closedn_mkApps.
    rewrite closedn_mkApps in IHev1.
    specialize (IHev1 Hc). move/andP: IHev1 => [Hfix Hargs].
    repeat (apply/andP; split; auto).
    eapply closed_cunfold_cofix; tea.
  - specialize (IHev1 Hc). eapply IHev2. rewrite closedn_mkApps in IHev1 *.
     move/andP: IHev1 => [Hfix Hargs].
    rewrite closedn_mkApps Hargs.
    rewrite andb_true_r.
    eapply closed_cunfold_cofix; tea.
  - apply IHev.
    move/(lookup_env_closed clΣ): isdecl.
    now rewrite /closed_decl e /=.
  - have := (IHev1 Hc).
    rewrite closedn_mkApps /= => clargs.
    eapply IHev2; eauto.
    eapply nth_error_forallb in clargs; tea.
  - have := (IHev1 Hc). intros clargs.
    eapply IHev2; eauto.
    eapply nth_error_forallb in clargs; tea.
  - have := (IHev1 Hc).
    rewrite closedn_mkApps /= => clargs.
    rewrite clargs IHev2 //.
  - eapply forallb_All in Hc. eapply All2_over_impl in iha; tea. solve_all.
    cbn; intros; intuition auto.
  - rtoProp; intuition auto.
  - depelim X; solve_all. eapply All2_over_undep in a. subst a' a0; cbn.
    depelim Hc; constructor; cbn in *; intuition eauto; solve_all.
Qed.

Ltac forward_keep H :=
  match type of H with
  ?X -> _ =>
    let H' := fresh in
    assert (H' : X) ; [|specialize (H H')]
  end.

Definition mk_env_flags has_ax has_pars tfl has_blocks :=
  {| has_axioms := has_ax;
     has_cstr_params := has_pars;
     term_switches := tfl ;
     cstr_as_blocks := has_blocks |}.

Global Hint Rewrite andb_true_r andb_false_r : simplifications.
Global Hint Rewrite orb_false_r orb_true_r : simplifications.

Tactic Notation "sim" "in" hyp(H) :=
  repeat (cbn in H; autorewrite with simplifications in H).
Ltac sim := repeat (cbn ; autorewrite with simplifications).

Lemma eval_wellformed {efl : EEnvFlags} {wfl : WcbvFlags} Σ :
  forall (has_app : has_tApp), (* necessary due to mkApps *)
  wf_glob Σ ->
  forall t u, wellformed Σ 0 t -> eval Σ t u -> wellformed Σ 0 u.
Proof.
  move=> has_app clΣ t u Hc ev. move: Hc.
  induction ev; simpl in *; auto;
    (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
  all:intros; intuition auto; rtoProp; intuition auto; rtoProp; eauto using wellformed_csubst.
  - eapply IHev2; eauto.
    eapply wellformed_iota_red_brs; tea => //.
    rewrite wellformed_mkApps // in H2. move/andP: H2 => [] //.
  - eapply IHev2; eauto.
    eapply wellformed_iota_red_brs; tea => //.
    destruct cstr_as_blocks; solve_all.
    destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all.
    destruct args; cbn in H3; eauto; econstructor.
  - subst brs. eapply IHev2. sim in H0.
    eapply wellformed_substl => //.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length.
  - eapply IHev3. apply/andP; split; [|easy].
    rewrite wellformed_mkApps // in H. rewrite Hc /=.
    move/andP: H => [clfix clargs].
    rewrite wellformed_mkApps // clargs andb_true_r.
    eapply wellformed_cunfold_fix; tea => //.
  - eapply IHev3 => //. rtoProp; intuition auto.
    eapply wellformed_cunfold_fix => //; tea. cbn. rewrite H H1 H2 //.
  - eapply IHev2. rewrite wellformed_mkApps //.
    rewrite wellformed_mkApps // in H2.
    move/andP: H2 => [Hfix Hargs].
    repeat (apply/andP; split; auto).
    eapply wellformed_cunfold_cofix => //; tea.
  - eapply IHev2. rewrite wellformed_mkApps // in H *.
    move/andP: H => [Hfix Hargs].
    rewrite wellformed_mkApps // Hargs andb_true_r Hc Hc' /=.
    eapply wellformed_cunfold_cofix; tea => //.
  - apply IHev.
    move/(lookup_env_wellformed clΣ): isdecl.
    now rewrite /wf_global_decl /= e /=.
  - move: H; rewrite wellformed_mkApps // /= => clargs.
    eapply IHev2; eauto.
    move/andP: clargs => [/andP[] hasc wfc wfargs].
    eapply nth_error_forallb in wfargs; tea.
  - eapply IHev2.
    eapply nth_error_forallb in e3; eauto.
    destruct cstr_as_blocks; eauto.
    destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all.
    destruct args; cbn in H0; eauto.
  - destruct cstr_as_blocks; try congruence.
    destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all.
    now rewrite (All2_length a) in H.
    eapply All2_over_impl in iha; tea.
    intuition auto.
    eapply All2_over_impl in iha; tea.
    intuition auto.
    depelim a => //.
  - depelim X; solve_all.
  - depelim X; solve_all.
    eapply All2_over_undep in a. subst a0 a'; depelim Hc'; constructor; cbn in *; solve_all.
    solve_all.
Qed.

Lemma remove_last_length {X} {l : list X} :
  #|remove_last l| = match l with nil => 0 | _ => #|l| - 1 end.
Proof.
  unfold remove_last. rewrite length_firstn.
  destruct l; cbn; lia.
Qed.

Lemma remove_last_length' {X} {l : list X} :
  l <> nil ->
  #|remove_last l| = #|l| - 1.
Proof.
  intros. rewrite remove_last_length. destruct l; try congruence; lia.
Qed.

Local Hint Rewrite @remove_last_length : len.

Lemma eval_mkApps_tFix_inv_size {wfl : WcbvFlags} Σ mfix idx args v :
  with_guarded_fix ->
  forall Heval : eval Σ (mkApps (tFix mfix idx) args) v,
  (∑ args', All2 (fun a a' => ∑ H : eval Σ a a', eval_depth H < eval_depth Heval) args args' ×
     v = mkApps (tFix mfix idx) (args')) +
  (∑ n b, args <> nil /\ cunfold_fix mfix idx = Some (n, b) /\ n < #|args|).
Proof.
 revert v.
 induction args using rev_ind; intros v wg ev.
 + left. exists []. split. repeat econstructor. now depelim ev.
 + rewrite mkApps_app in ev |- *.
   cbn in *.
   depelim ev.

   all: try(specialize (IHargs) with (Heval := ev1);
    destruct IHargs as [(args' & ? & Heq) | (? & ? & ? & ? & ?)];eauto;
      rewrite ?Heq; try solve_discr; try congruence; try noconf H;
     len; rewrite ?Heq; rewrite Nat.add_comm; eauto 9).
   * right. repeat eexists. destruct args; cbn; congruence. eauto.
     rewrite (All2_length a); lia.
   * left. eexists. split. sq. eapply All2_app. solve_all. destruct H. unshelve eexists. eauto. cbn. lia.
     econstructor. 2: econstructor.
     unshelve eexists. eauto. lia.
     now rewrite !mkApps_app.
   * subst f'. rewrite wg in i.
     rewrite isFixApp_mkApps /= /isFixApp /= in i.
     rewrite !negb_or in i; rtoProp; intuition auto. now cbn in H2.
   * now cbn in i.
Qed.

Lemma eval_to_values {wfl : WcbvFlags} Σ a a' : All2 (eval Σ) a a' -> All (value Σ) a'.
Proof.
  induction 1; constructor; eauto using eval_to_value.
Defined.

Lemma values_final {wfl : WcbvFlags} Σ a: All (value Σ) a -> All2 (eval Σ) a a.
Proof.
  induction 1; constructor; eauto using value_final.
Defined.

Lemma size_final {wfl : WcbvFlags} Σ t v :
  forall He : eval Σ t v, ∑ He' : eval Σ v v, eval_depth He' <= eval_depth He.
Proof.
  intros He. induction He.
  all: try now unshelve eexists; eauto; [ eapply IHHe | cbn; destruct IHHe; lia ].
  all: try now unshelve eexists; eauto; [ eapply IHHe2 | cbn; destruct IHHe2; lia ].
  all: try now unshelve eexists; eauto; [ eapply IHHe3 | cbn; destruct IHHe3; lia ].
  all: try now unshelve eexists; eauto; cbn; lia.
  - unshelve eexists. repeat econstructor. cbn; lia.
  - unshelve eexists; eauto. eapply eval_fix_value; eauto. eapply IHHe1. eapply IHHe2. cbn. destruct IHHe1, IHHe2. lia.
  - unshelve eexists. eapply eval_construct; eauto.
    eapply IHHe1. eapply IHHe2. cbn. destruct IHHe1, IHHe2. cbn. lia.
  - unshelve eexists. eapply eval_construct_block; eauto.
    now rewrite -(All2_length a).
    clear -a iha. induction a; constructor. destruct iha. apply s. apply IHa. apply iha.
    cbn.
    clear -a iha.
    { induction a; cbn; try lia.
      destruct iha. destruct s. cbn. specialize (IHa a0). lia. }
  - unshelve eexists. eapply eval_app_cong; eauto. eapply IHHe1. eapply IHHe2. cbn. destruct IHHe1, IHHe2. lia.
  - depelim X. 1-3:unshelve eexists; cbn; repeat constructor.
    destruct s as [hev evd].
    unshelve eexists. do 2 econstructor.
    clear -a. induction ev; constructor. apply a. apply IHev, a. tea.
    cbn.
    clear -a evd.
    { induction ev; cbn; try lia. cbn in *.
      destruct a. destruct s. cbn. specialize (IHev a). lia. }
Qed.

Lemma eval_mkApps_tFix_inv_size_unguarded {wfl : WcbvFlags} Σ mfix idx args v :
  with_guarded_fix = false ->
  forall Heval : eval Σ (mkApps (tFix mfix idx) args) v,
  (args = [] /\ v = tFix mfix idx)
  + ∑ a av args' argsv,
    (args = a :: args')%list ×
    All2 (fun a a' => (a = a') + (∑ H : eval Σ a a', eval_depth H < eval_depth Heval)) args' argsv ×
    ∑ n fn, cunfold_fix mfix idx = Some (n, fn) ×
    ∑ H : eval Σ a av, eval_depth H <= eval_depth Heval ×
    ∑ H : eval Σ (mkApps (tApp fn av) argsv) v, eval_depth H <= eval_depth Heval.
Proof.
 revert v.
 induction args using rev_ind; intros v wg ev.
 + left. now depelim ev.
 + rewrite mkApps_app in ev |- *.
   cbn in *.
   depelim ev; right.

   all: try(specialize (IHargs) with (Heval := ev1); destruct IHargs as [[-> Heq] | (a & aval & args' & argsv_ & Heqargs & Hall & n & fn_ & Hunf & Heva & Hevasz & Hev' & Hevsz')];eauto; try rewrite ?Heq; try solve_discr; try congruence;
     len; try rewrite ?Heq; rewrite ?Nat.add_comm; eauto 9).
   * subst. cbn. exists a, aval, (args' ++ [x])%list,(argsv_ ++ [t'])%list. split. reflexivity.
      repeat unshelve eexists; eauto. 3:{ rewrite mkApps_app. econstructor. eauto. eapply size_final. eauto. }
      eapply All2_app.
      solve_all. right. destruct b. unshelve eexists; eauto. lia.
      unshelve econstructor. right. unshelve eexists. eauto. lia. repeat econstructor.
      cbn in *; lia.
      cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [t']). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [t'])).
      cbn. intros. subst. cbn. destruct size_final. cbn in *. lia.
   * subst. cbn. exists a, aval, (args' ++ [x])%list,(argsv_ ++ [a'])%list. split. reflexivity.
     repeat unshelve eexists; eauto.
     eapply All2_app.
     solve_all. right. destruct b0. unshelve eexists; eauto. lia.
   unshelve econstructor. right. unshelve eexists. eauto. lia. repeat econstructor.
   cbn in *; lia.
   rewrite mkApps_app. cbn. econstructor; eauto. eapply size_final; eauto.
   cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [a']). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [a'])).
   intros. subst. cbn.
   destruct size_final. cbn in *. lia.

   * invs Heq. exists x, av, [], []. repeat split. econstructor. repeat unshelve eexists; eauto.
     all:cbn; lia.
   * subst. cbn. eexists _, _, _, (argsv_ ++ [_])%list. repeat eexists. 2: eauto.
    eapply All2_app.
     solve_all. right. destruct b. exists x1. cbn. lia. econstructor. now left. econstructor.
     Unshelve. 5:{ rewrite mkApps_app. eapply eval_fix'; eauto. }
     3:tea. cbn in *; lia.
     cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [x]). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [x])). intros. subst. cbn.
     cbn in *. lia.
   * subst. exists a, aval, (args' ++ [x]), (argsv_ ++ [a']).
     split => //. split.
     { eapply All2_app.
      - eapply All2_impl; tea; cbv beta.
        intros ?? [eq|[H IH]]; intuition auto. right; exists H. cbn. clear -IH. cbn in *. lia.
      - constructor; auto.
        right; exists ev2. cbn; lia. }
    exists n, fn_. split => //.
    exists Heva; cbn. split => //. cbn in *; lia.
    rewrite mkApps_app /=.
    unshelve eexists. eapply eval_construct; tea.
    exact (size_final _ _ _ ev2).π1.
    cbn. destruct size_final; cbn. cbn in *. lia.
   * subst. cbn in i. exfalso. destruct with_guarded_fix; easy.
   * subst.  cbn. eexists _, _, _, (argsv_ ++ [_])%list. repeat eexists. 2: eauto.
     eapply All2_app.
     solve_all. right. destruct b. exists x1. cbn. lia. econstructor. now left. econstructor.
     Unshelve. 4:tea. 3:{ rewrite mkApps_app. eapply eval_app_cong; eauto. }
     cbn in *; lia.
     cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [x]). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [x])). intros. subst. cbn.
     cbn in *. lia.
   * subst. cbn. invs i.
Qed.

Lemma eval_mkApps_inv' {wfl : WcbvFlags} Σ f args v :
  eval Σ (mkApps f args) v ->
  ∑ f' args', eval Σ f f' × All2 (eval Σ) args args' × eval Σ (mkApps f' args') v.
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v, []. split => //. eapply eval_to_value in ev.
    split => //. now eapply value_final.
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [t']). split => //.
      rewrite mkApps_app.
      econstructor; tea. eapply All2_app; auto.
      econstructor; tea. eapply value_final. now eapply eval_to_value in ev2.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [a']). split => //. split; auto.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_beta; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_fix; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_fix_value; tea. eapply value_final, eval_to_value; tea.
    + destruct (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_fix'; eauto. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evars res]]]].
      exists f'', (args' ++ [a']); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_construct; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evars res]]]].
      exists f'', (args' ++ [a']); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_app_cong; tea. eapply value_final, eval_to_value; tea.
    + cbn in i. discriminate.
Qed.

Lemma eval_mkApps_Construct_inv {fl : WcbvFlags} Σ kn c args e :
  with_constructor_as_block = false ->
  eval Σ (mkApps (tConstruct kn c []) args) e ->
  ∑ args', [× isSome (lookup_constructor Σ kn c), (e = mkApps (tConstruct kn c []) args') & All2 (eval Σ) args args'].
Proof.
  intros hblock.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. congruence. exists []=> //.
    split => //. cbn -[lookup_constructor] in i. now rewrite hblock /= in i.
  - intros ev. rewrite mkApps_app /= in ev.
    depelim ev; try solve_discr.
    destruct (IHargs _ ev1) as [? []]. solve_discr.
    all:try specialize (IHargs _ ev1) as [? []]; try solve_discr; try noconf H.
    * exists (x0 ++ [a']). split => //.
      rewrite mkApps_app /= //. eapply All2_app; eauto.
    * subst f'.
      exists (x0 ++ [a'])%list.
      rewrite mkApps_app /= //.
      cbn in i. split => //. eapply All2_app; eauto.
    * now cbn in i.
Qed.

Lemma eval_mkApps_Construct_block_inv {fl : WcbvFlags} Σ kn c args oargs e :
  with_constructor_as_block ->
  eval Σ (mkApps (tConstruct kn c args) oargs) e ->
  ∑ args', oargs = [] × (e = tConstruct kn c args') × All2 (eval Σ) args args'.
Proof.
  intros hblock.
  revert e; induction oargs using rev_ind; intros e.
  - intros ev. depelim ev.
    + eexists. split. reflexivity. split. reflexivity. auto.
    + invs i. destruct args; invs H0. exists []. repeat econstructor.
  - intros ev. rewrite mkApps_app /= in ev.
    depelim ev; try solve_discr.
    all: try specialize (IHoargs _ ev1) as (? & ? & E & ?); try congruence; try solve_discr; try noconf E.
    * subst. cbn in i. destruct with_guarded_fix; cbn in *; eauto.
    * invs i.
Qed.

Lemma eval_mkApps_inv_size {wfl : WcbvFlags} {Σ f args v} :
  forall ev : eval Σ (mkApps f args) v,
  ∑ f' args' (evf : eval Σ f f'),
    [× eval_depth evf <= eval_depth ev,
      All2 (fun a a' => ∑ eva : eval Σ a a', eval_depth eva < eval_depth ev) args args' &
      ∑ evres : eval Σ (mkApps f' args') v, eval_depth evres <= eval_depth ev].
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v, []. exists ev => //. split => //.
    exact (size_final _ _ _ ev).
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [t']). exists evf'.
      rewrite mkApps_app.
      split => //. cbn. lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      unshelve econstructor; tea.
      econstructor; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn. lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [a']). exists evf'. split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists.
      eapply eval_beta; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix_value; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + destruct (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix'; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evfs evars [evres res]]]]].
      exists f'', (args' ++ [a']); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_construct; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evfs evars [evres res]]]]].
      exists f'', (args' ++ [a']); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_app_cong; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + cbn in i. discriminate.
Qed.

Lemma eval_mkApps_Construct_size {wfl : WcbvFlags} {Σ ind c args v} :
  with_constructor_as_block = false ->
  forall ev : eval Σ (mkApps (tConstruct ind c []) args) v,
  ∑ args' (evf : eval Σ (tConstruct ind c []) (tConstruct ind c [])),
    [× eval_depth evf <= eval_depth ev,
      All2 (fun a a' => ∑ eva : eval Σ a a', eval_depth eva < eval_depth ev) args args' &
      v = mkApps (tConstruct ind c []) args'].
Proof.
  intros hblock ev.
  destruct (eval_mkApps_inv_size ev) as [f'' [args' [? []]]].
  exists args'.
  destruct (eval_mkApps_Construct_inv _ _ _ _ _ hblock ev) as [? []]. subst v.
  unshelve eexists (eval_atom _ (tConstruct ind c []) _).
  cbn -[lookup_constructor]. now rewrite hblock.
  cbn. split => //. destruct ev; cbn => //; auto with arith.
  clear l.
  eapply (eval_mkApps_Construct_inv _ _ _ [] _ hblock) in x as [? []]; auto. subst f''. depelim a1.
  f_equal.
  eapply eval_deterministic_all; tea.
  eapply All2_impl; tea; cbn; eauto. now intros x y [].
Qed.

Lemma eval_construct_size  {fl : WcbvFlags} [Σ kn c args e] :
  with_constructor_as_block = false ->
  forall (ev : eval Σ (mkApps (tConstruct kn c []) args) e),
  ∑ args', (e = mkApps (tConstruct kn c []) args') ×
  All2 (fun x y => ∑ ev' : eval Σ x y, eval_depth ev' < eval_depth ev) args args'.
Proof.
  intros hblock ev; destruct (eval_mkApps_Construct_size hblock ev) as [args'[evf [_ hargs hv]]].
  exists args'; intuition auto.
Qed.

Lemma eval_box_apps {wfl : WcbvFlags}:
  forall (Σ' : global_declarations) (e : term) (x x' : list term),
    All2 (eval Σ') x x' ->
    eval Σ' e tBox -> eval Σ' (mkApps e x) tBox.
Proof.
  intros Σ' e x H2.
  revert e H2; induction x using rev_ind; cbn; intros e ? X ?; eauto.
  eapply All2_app_inv_l in X as (l1' & l2' & -> & H' & H2).
  depelim H2.
  specialize (IHx e _ H'). simpl.
  rewrite mkApps_app. simpl. econstructor; eauto.
Qed.
