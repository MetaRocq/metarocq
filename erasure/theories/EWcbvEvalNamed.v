(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv
  EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From Stdlib Require Import BinaryString.
Import String.

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

(** ** Big step *named* version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Inductive value : Set :=
| vClos (na : ident) (b : term) (env : list (ident * value))
| vConstruct (ind : inductive) (c : nat) (args : list (value))
| vRecClos (b : list (ident * term)) (idx : nat) (env : list (ident * value))
| vPrim (p : EPrimitive.prim_val value)
| vLazy (p : term) (env : list (ident * value)).

Definition environment := list (ident * value).
Definition add : ident -> value -> environment -> environment := fun (x : ident) (v : value) env =>
                                                                (x, v) :: env.
Fixpoint add_multiple (xs : list ident) (vs : list value) (env : environment) {struct vs} : environment :=
  match xs, vs with
  | x :: xs, v :: vs => add x v (add_multiple xs vs env)
  | _, _ => env
  end.

Definition lookup (E : environment) x :=
  match find (fun '(s, v) => String.eqb x s) E with
    Some (_, v) => Some v
  | _ => None
  end.

Definition fix_env (l : list (ident * term)) Γ :=
  let fix aux (n : nat) : list value :=
    match n with
    | 0 => []
    | S n0 => vRecClos l n0 Γ :: aux n0
    end in
  aux #|l|.

(*
Definition cunfold_fix (mfix : list (ident * term)) (idx : nat) Γ :=
  match nth_error mfix idx with
  | Some d => match map_option_out (map (fun d => match fst d with nNamed a => Some a | nAnon => @None ident end) mfix), d.(dname) with
              | Some nms, nNamed nm  => Some (nm, d.(dbody), add_multiple nms (fix_env mfix Γ) Γ)
              | _, _ => None
              end
  | None => None
  end. *)

Unset Elimination Schemes.

Section Wcbv.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval (Γ : environment) : term -> value -> Set :=
  (** Reductions *)
  | eval_var na v :
    lookup Γ na = Some v ->
    eval Γ (tVar na) v

  (** Beta *)
  | eval_beta f na b a a' res Γ' :
    eval Γ f (vClos na b Γ') ->
    eval Γ a a' ->
    eval (add na a' Γ') b res ->
    eval Γ (tApp f a) res

  | eval_lambda na b :
    eval Γ (tLambda (nNamed na) b) (vClos na b Γ)

  (** Let *)
  | eval_zeta na b0 b0' b1 res :
    eval Γ b0 b0' ->
    eval (add na b0' Γ) b1 res ->
    eval Γ (tLetIn (nNamed na) b0 b1) res

  (** Case *)
  | eval_iota_block ind cdecl discr c args brs br res nms :
    eval Γ discr (vConstruct ind c args) ->
    constructor_isprop_pars_decl Σ ind c = Some (false, 0, cdecl) ->
    nth_error brs c = Some br ->
    #|args| = cdecl.(cstr_nargs) ->
    #|args| = #|br.1| ->
    Forall2 (fun x y => x = nNamed y) br.1 nms ->
    eval (add_multiple (List.rev nms) args Γ) br.2 res ->
    NoDup nms ->
    eval Γ (tCase (ind, 0) discr brs) res

  (** Fix unfolding, without guard *)
  | eval_fix_unfold f mfix idx a na na' av fn res Γ' :
    forallb (λ x, isLambda (snd x)) mfix ->
    ~ In na (map fst mfix) ->
    eval Γ f (vRecClos mfix idx Γ') ->
    NoDup (map fst mfix) ->
    nth_error mfix idx = Some (na', tLambda (nNamed na) fn) ->
    eval (add na av (add_multiple (List.rev (map fst mfix)) (fix_env mfix Γ') (Γ'))) fn res ->
    eval Γ a av ->
    eval Γ (tApp f a) res

  | eval_fix mfix idx nms :
    forall (Hlen : (idx < #|mfix|)),
    List.forallb (isLambda ∘ dbody) mfix ->
    NoDup nms ->
    Forall2 (fun d n => nNamed n = d.(dname)) mfix nms ->
    eval Γ (tFix mfix idx) (vRecClos (map2 (fun n d => (n, d.(dbody))) nms mfix) idx Γ)

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
    decl.(cst_body) = Some body ->
    eval [] body res ->
    eval Γ (tConst c) res

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct_block ind c mdecl idecl cdecl args args' :
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    #|args| <= cstr_nargs cdecl ->
    All2_Set (eval Γ) args args' ->
    eval Γ (tConstruct ind c args) (vConstruct ind c args')

  | eval_construct_block_empty ind c mdecl idecl cdecl :
     lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
     eval Γ (tConstruct ind c []) (vConstruct ind c [])

  | eval_prim p p' :
    eval_primitive (eval Γ) p p' ->
    eval Γ (tPrim p) (vPrim p')

  | eval_lazy t : eval Γ (tLazy t) (vLazy t Γ)
  | eval_force Γ' t t' v :
    eval Γ t (vLazy t' Γ') ->
    eval Γ' t' v ->
    eval Γ (tForce t) v
  .

  Program Definition eval_ind :=
    λ (P : ∀ (Γ : environment) (t : term) (v : value), eval Γ t v → Type) (f : ∀ (Γ : environment) (na : string) (v : value) (e : lookup Γ na = Some v),
          P Γ (tVar na) v (eval_var Γ na v e))

      (f1 : ∀ (Γ : environment) (f1 : term) (na : ident) (b a : term) (a' res : value) (Γ' : list (ident × value)) (e : eval Γ f1 (vClos na b Γ')),
          P Γ f1 (vClos na b Γ') e
          → ∀ e0 : eval Γ a a', P Γ a a' e0 → ∀ e1 : eval (add na a' Γ') b res, P (add na a' Γ') b res e1 → P Γ (tApp f1 a) res (eval_beta Γ f1 na b a a' res Γ' e e0 e1))
      (f2 : ∀ (Γ : environment) (na : ident) (b : term), P Γ (tLambda (nNamed na) b) (vClos na b Γ) (eval_lambda Γ na b)) (f3 : ∀ (Γ : environment)
                                                                                                                                  (na : ident) (b0 : term)
                                                                                                                                  (b0' : value) (b1 : term)
                                                                                                                                  (res : value) (e : eval Γ b0 b0'),
          P Γ b0 b0' e
          → ∀ e0 : eval (add na b0' Γ) b1 res,
            P (add na b0' Γ) b1 res e0
            → P Γ (tLetIn (nNamed na) b0 b1) res
                (eval_zeta Γ na b0 b0' b1 res e e0))
      (f4 : ∀ (Γ : environment) (ind : inductive) (cdecl : constructor_body) (discr : term) (c : nat) (args : list value) (brs : list (list name × term))
              (br : list name × term) (res : value) (nms : list ident) (e : eval Γ discr (vConstruct ind c args)),
          P Γ discr (vConstruct ind c args) e
          → ∀ (e0 : constructor_isprop_pars_decl Σ ind c = Some (false, 0, cdecl)) (e1 : nth_error brs c = Some br) (e2 : #|args| = cstr_nargs cdecl)
              (e3 : #|args| = #|br.1|) (f4 : Forall2 (λ (x : name) (y : ident), x = nNamed y) br.1 nms) (e4 : eval (add_multiple (List.rev nms) args Γ) br.2 res),
            P (add_multiple (List.rev nms) args Γ) br.2 res e4
            → ∀ n : NoDup nms, P Γ (tCase (ind, 0) discr brs) res (eval_iota_block Γ ind cdecl discr c args brs br res nms e e0 e1 e2 e3 f4 e4 n))
      (f5 :
            ∀ (Γ : environment)
             (f5 : term)
             (mfix :
             list (ident × term))
             (idx : nat)
             (a : term)
             (na na' : ident)
             (av : value)
             (fn : term)
             (res : value)
             (Γ' :
             list (ident × value))
             (Hbodies : forallb (λ x, isLambda (snd x)) mfix)
             (Hfresh : ~ In na (map fst mfix))
             (e :
             eval Γ f5
             (vRecClos mfix idx Γ')),
             P Γ f5
             (vRecClos mfix idx Γ') e
             →
             ∀ (n : NoDup (map fst mfix))
             (e0 :
             nth_error mfix idx =
             Some
             (na', tLambda (nNamed na) fn))
             (e1 :
             eval
             (add na av  (add_multiple
             (List.rev (map fst mfix))
             (fix_env mfix Γ') (Γ'))) fn
             res),
             P
             (add na av (add_multiple
             (List.rev (map fst mfix))
             (fix_env mfix Γ') (Γ'))) fn
             res e1
             →
             forall e2 : eval Γ a av,
             P Γ a av e2 ->
             P Γ
             (tApp f5 a) res
             (eval_fix_unfold Γ f5 mfix
             idx a na na' av fn res Γ' Hbodies Hfresh e
             n e0 e1 e2))
      (f6 : ∀ (Γ : environment) (mfix : list (def term)) (idx : nat) (nms : list ident) (Hlen : (idx < #|mfix|)) (Hbodies : List.forallb (isLambda ∘ dbody) mfix) (n : NoDup nms) (f6 : Forall2 (λ (d : def term) (n0 : ident), nNamed n0 = dname d) mfix
                                                                                                              nms),
          P Γ (tFix mfix idx) (vRecClos (map2 (λ (n0 : ident) (d : def term), (n0, dbody d)) nms mfix) idx Γ) (eval_fix Γ mfix idx nms Hlen Hbodies n f6)) (f7 :
        ∀ (Γ : environment)
          (c : kername)
          (decl : constant_body)
          (body : term)
          (isdecl :
            declared_constant Σ c decl)
          (res : value)
          (e :
            cst_body decl =
              Some body)
          (e0 :
            eval [] body res),
          P [] body res e0
          →
            P Γ
              (tConst c) res
              (eval_delta Γ c decl body
                 isdecl res e e0))
      (f8 : ∀ (Γ : environment) (ind : inductive) (c : nat) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body)
              (args : list term) (args' : list value) (e : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl)) (l : #|args| ≤ cstr_nargs cdecl)
              (a : All2_Set (eval Γ) args args') (IHa : All2_over a (P Γ)), P Γ (tConstruct ind c args) (vConstruct ind c args') (eval_construct_block Γ ind c mdecl idecl cdecl args args' e l a))
      (f9 : ∀ (Γ : environment) (ind : inductive) (c : nat) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body)
              (e : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl)),
          P Γ (tConstruct ind c []) (vConstruct ind c []) (eval_construct_block_empty Γ ind c mdecl idecl cdecl e))
      (f10 : ∀ (Γ : environment) (p : prim_val term) (p' : prim_val value) (ev : eval_primitive (eval Γ) p p')
        (evih : eval_primitive_ind (eval Γ) (P Γ) _ _ ev),
        P Γ (tPrim p) (vPrim p') (eval_prim _ _ _ ev))
      (f11 :∀ (Γ : environment) t, P Γ (tLazy t) (vLazy t Γ) (eval_lazy _ _))
      (f12 : ∀ Γ Γ' t t' v (ev0 : eval Γ t (vLazy t' Γ')) (ev1 : eval Γ' t' v),
        P _ _ _ ev0 -> P _ _ _ ev1 ->
        P _ _ _ (eval_force _ _ _ _ _ ev0 ev1)),
      fix F (Γ : environment) (t : term) (v : value) (e : eval Γ t v) {struct e} : P Γ t v e :=
      match e as e0 in (eval _ t0 v0) return (P Γ t0 v0 e0) with
      | @eval_var _ na v0 e0 => f Γ na v0 e0
      | @eval_beta _ f10 na b a a' res Γ' e0 e1 e2 => f1 Γ f10 na b a a' res Γ' e0 (F Γ f10 (vClos na b Γ') e0) e1 (F Γ a a' e1) e2 (F (add na a' Γ') b res e2)
      | @eval_lambda _ na b => f2 Γ na b
      | @eval_zeta _ na b0 b0' b1 res e0 e1 => f3 Γ na b0 b0' b1 res e0 (F Γ b0 b0' e0) e1 (F (add na b0' Γ) b1 res e1)
      | @eval_iota_block _ ind cdecl discr c args brs br res nms e0 e1 e2 e3 e4 f10 e5 n =>
          f4 Γ ind cdecl discr c args brs br res nms e0 (F Γ discr (vConstruct ind c args) e0) e1 e2 e3 e4 f10 e5 (F (add_multiple (List.rev nms) args Γ) br.2 res e5) n
      | @eval_fix_unfold _ f10 mfix idx a na na' av fn res Γ' Hbodies Hfresh e0 n e1 e2 e3 =>
          f5 Γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      | @eval_fix _ mfix idx nms Hlen Hbodies n f10 => f6 Γ mfix idx nms Hlen Hbodies n f10
      | @eval_delta _ c decl body isdecl res e0 e1 => f7 Γ c decl body isdecl res e0 e1 (F [] body res e1)
      | @eval_construct_block _ ind c mdecl idecl cdecl args args' e0 l a => f8 Γ ind c mdecl idecl cdecl args args' e0 l a (map_All2_dep _ (F Γ) a)
      | @eval_construct_block_empty _ ind c mdecl idecl cdecl e0 => f9 Γ ind c mdecl idecl cdecl e0
      | @eval_prim _ p p' ev => f10 Γ p p' ev (map_eval_primitive (P := P Γ) (F Γ) ev)
      | @eval_lazy _ t => f11 Γ t
      | @eval_force _ Γ' t t' v ev ev' => f12 _ _ _ _ _ ev ev' (F Γ _ _ ev) (F Γ' _ _ ev')
      end.

End Wcbv.

Definition ident_of_name (na : name) : ident :=
  match na with nAnon => "" | nNamed na => na end.

Reserved Notation "Γ ;;; E ⊩ s ~ t" (at level 50, E, s, t at next level).

Inductive represents : list ident -> environment -> term -> term -> Set :=
| represents_bound_tRel Γ n na E : nth_error Γ n = Some na -> Γ ;;; E ⊩ tVar na ~ tRel n
| represents_unbound_tRel E na v Γ s : lookup E na = Some v -> represents_value v s -> Γ ;;; E ⊩ tVar na ~ s
| represents_tLambda Γ E na na' b b' : (na :: Γ) ;;; E ⊩ b ~ b' -> Γ ;;; E ⊩ tLambda (nNamed na) b ~ tLambda na' b'
| represents_tLetIn Γ E na b0 b1 na' b0' b1' : Γ ;;; E ⊩ b0 ~ b0' -> (na :: Γ) ;;; E ⊩ b1 ~ b1' -> Γ ;;; E ⊩ tLetIn (nNamed na) b0 b1 ~ tLetIn na' b0' b1'
| represents_tApp Γ E s s' t t' : Γ ;;; E ⊩ s ~ s' -> Γ ;;; E ⊩ t ~ t' -> Γ ;;; E ⊩ tApp s t ~ tApp s' t'
| represents_tConst Γ E c : Γ ;;; E ⊩ tConst c ~ tConst c
| represents_tConstruct Γ E ind i args args' : All2_Set (represents Γ E) args args' -> Γ ;;; E ⊩ tConstruct ind i args ~ tConstruct ind i args'
| represents_tCase Γ E ind discr discr' brs brs' :
  Γ ;;; E ⊩ discr ~ discr' ->
  All2_Set (fun b b' => #|b.1| = #|b'.1|) brs brs' ->
  (All2_Set (fun b b' => {nms & (All2_Set (fun n n' => n = nNamed n') b.1 nms × ((nms ++ Γ) ;;; E ⊩ (b.2) ~ (b'.2)) × NoDup nms)}) brs brs') ->
  Γ ;;; E  ⊩ tCase ind discr brs ~ tCase ind discr' brs'
| represents_tFix Γ E mfix mfix' idx nms  :
  List.forallb (isLambda ∘ dbody) mfix ->
  NoDup nms ->
  All2_Set (fun d n => d.(dname) = nNamed n) mfix nms ->
  All2_Set (fun d d' => (List.rev nms ++ Γ) ;;; E ⊩ d.(dbody) ~ d'.(dbody)) mfix mfix' ->
  Γ ;;; E ⊩ tFix mfix idx ~ tFix mfix' idx
| represents_tPrim Γ E p p' :
  onPrims (represents Γ E) p p' ->
  Γ ;;; E ⊩ tPrim p ~ tPrim p'
| represents_tLazy Γ E t t' :
  Γ ;;; E ⊩ t ~ t' ->
  Γ ;;; E ⊩ tLazy t ~ tLazy t'
| represents_tForce Γ E t t' :
  Γ ;;; E ⊩ t ~ t' ->
  Γ ;;; E ⊩ tForce t ~ tForce t'

with represents_value : value -> term -> Set :=
| represents_value_tClos na E s t na' : [na] ;;; E ⊩ s ~ t -> represents_value (vClos na s E) (tLambda na' t)
| represents_value_tConstruct vs ts ind c : All2_Set represents_value vs ts -> represents_value (vConstruct ind c vs) (tConstruct ind c ts)
| represents_value_tFix vfix i E mfix :
  All2_Set (fun v d => isLambda (snd v) × (List.rev (map fst vfix) ;;; E ⊩ snd v ~ d.(dbody))) vfix mfix -> represents_value (vRecClos vfix i E) (tFix mfix i)
| represents_value_tPrim p p' : onPrims represents_value p p' -> represents_value (vPrim p) (tPrim p')
| represents_value_tLazy E t t' : [] ;;; E ⊩ t ~ t' -> represents_value (vLazy t E) (tLazy t')
where "Γ ;;; E ⊩ s ~ t" := (represents Γ E s t).
Derive Signature for represents represents_value.

Program Definition represents_ind :=
  (λ (P : ∀ (l : list ident) (e : environment) (t t0 : term),
         l;;; e ⊩ t ~ t0 → Type) (P0 : ∀ (v : value) (t : term),
         represents_value v t → Type)
     (f0 :
       ∀ (Γ : list ident)
         (n : nat)
         (na : ident)
         (E : environment)
         (e :
           nth_error Γ n = Some na),
         P Γ E
           (tVar na)
           (tRel n)
           (represents_bound_tRel Γ n
              na E e))
     (f1 : ∀ (E : environment) (na : string) (v : value)
             (Γ : list ident) (s : term) (e : lookup E na = Some v)
             (r : represents_value v s),
         P0 v s r
         → P Γ E (tVar na) s (represents_unbound_tRel E na v Γ s e r))
     (f2 : ∀ (Γ : list ident) (E : environment) (na : ident)
             (na' : name) (b b' : term) (r : (na :: Γ);;; E ⊩ b ~ b'),
         P (na :: Γ) E b b' r
         → P Γ E (tLambda (nNamed na) b) (tLambda na' b')
             (represents_tLambda Γ E na na' b b' r))
     (f3 : ∀ (Γ : list ident) (E : environment) (na : ident)
             (b0 b1 : term) (na' : name) (b0' b1' : term)
             (r : Γ;;; E ⊩ b0 ~ b0'),
         P Γ E b0 b0' r
         → ∀ r0 : (na :: Γ);;; E ⊩ b1 ~ b1',
           P (na :: Γ) E b1 b1' r0
           → P Γ E (tLetIn (nNamed na) b0 b1) (tLetIn na' b0' b1')
               (represents_tLetIn Γ E na b0 b1 na' b0' b1' r r0))
     (f4 : ∀ (Γ : list ident) (E : environment) (s s' t t' : term)
             (r : Γ;;; E ⊩ s ~ s'),
         P Γ E s s' r
         → ∀ r0 : Γ;;; E ⊩ t ~ t',
           P Γ E t t' r0
           → P Γ E (tApp s t) (tApp s' t')
               (represents_tApp Γ E s s' t t' r r0))
     (f5 : ∀ (Γ : list ident) (E : environment) (c : kername),
         P Γ E (tConst c) (tConst c) (represents_tConst Γ E c))
     (f6 : ∀ (Γ : list ident) (E : environment) (ind : inductive)
             (i : nat) (args args' : list term) (a : All2_Set (represents Γ E) args args') (IH : All2_over a (fun t t' => P Γ E t t')),
         P Γ E (tConstruct ind i args) (tConstruct ind i args')
           (represents_tConstruct Γ E ind i args args' a))
     (f7 : ∀ (Γ : list ident) (E : environment) (ind : inductive × nat)
             (discr discr' : term) (brs brs' : list (list name × term))
             (r : Γ;;; E ⊩ discr ~ discr'),
         P Γ E discr discr' r
         -> forall Heq : All2_Set (fun b b' => #|b.1| = #|b'.1|) brs brs',
         ∀ (a : All2_Set (λ b b' : list name × term, ∑ nms : list ident, All2_Set (λ (n : name) (n' : ident), n = nNamed n') b.1 nms × (nms ++ Γ);;; E ⊩ b.2 ~ b'.2 × NoDup nms) brs brs'),
         forall IH : All2_over a (fun b b' H => P (projT1 H ++ Γ) E b.2 b'.2 (fst (snd (projT2 H)))),
           P Γ E (tCase ind discr brs) (tCase ind discr' brs')
             (represents_tCase Γ E ind discr discr' brs brs' r Heq a))
     (f8 : ∀ (Γ : list ident) (E : environment) (mfix mfix' : list (def term))
             (idx : nat) (nms : list ident) (Hbodies : List.forallb (isLambda ∘ dbody) mfix) (Hnodup : NoDup nms) (a : All2_Set
                                                 (λ (d : def term) (n : ident),
                                                   dname d = nNamed n) mfix nms)
             (a0 : All2_Set
                     (λ d d' : def term, (List.rev nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                     mfix mfix')
             (IH : All2_over a0 (fun t t' : def term => P (List.rev nms ++ Γ) E (dbody t) (dbody t'))),
         P Γ E (tFix mfix idx) (tFix mfix' idx)
           (represents_tFix Γ E mfix mfix' idx nms Hbodies Hnodup a a0))
     (f9 : forall Γ E p p' (o : onPrims (represents Γ E) p p'), onPrims_dep _ (P Γ E) _ _ o ->
        P Γ E  (tPrim p) (tPrim p') (represents_tPrim Γ E p p' o))

     (flazy : forall Γ E t t'
      (he : Γ ;;; E ⊩ t ~ t'),
      P Γ E t t' he ->
      P Γ E _ _ (represents_tLazy Γ E t t' he))

    (fforce : forall Γ E t t'
      (he : Γ ;;; E ⊩ t ~ t'),
      P Γ E t t' he ->
      P Γ E _ _ (represents_tForce Γ E t t' he))

     (f10 :
       ∀ (na : ident)
         (E : environment)
         (s t : term)
         (na' : name)
         (r :
           [na];;; E ⊩ s ~ t),
         P [na] E s t r
         → P0
             (vClos na s E)
             (tLambda na' t)
             (represents_value_tClos na E
                s t na' r))
     (f11 : ∀ (vs : list value) (ts : list term) (ind : inductive)
              (c : nat) (a : All2_Set represents_value vs ts) (IH : All2_over a P0),
         P0 (vConstruct ind c vs) (tConstruct ind c ts)
           (represents_value_tConstruct vs ts ind c a))
     (f12 : ∀ (vfix : list (ident × term)) (i : nat)
              (E : list (ident × value)) (mfix : list (def term))
              (a : All2_Set (λ (v : ident × term) (d : def term), isLambda v.2 × List.rev (map fst vfix) ;;; E ⊩ v.2 ~ dbody d) vfix mfix)
              (IH : All2_over a (fun v d H => P (List.rev (map fst vfix)) E v.2 (dbody d) (snd H)  ) ),
         P0 (vRecClos vfix i E) (tFix mfix i)
           (represents_value_tFix vfix i E mfix a))
     (f13 : forall p p' (o : onPrims represents_value p p'), onPrims_dep _ P0 _ _ o ->
        P0 (vPrim p) (tPrim p') (represents_value_tPrim p p' o))
    (f14 : forall E t t' (r : represents [] E t t'), P [] E t t' r ->
      P0 (vLazy t E) (tLazy t') (represents_value_tLazy E t t' r)),
    fix F
      (l : list ident) (e : environment) (t t0 : term)
      (r : l;;; e ⊩ t ~ t0) {struct r} : P l e t t0 r :=
     match r as r0 in (l0;;; e0 ⊩ t1 ~ t2) return (P l0 e0 t1 t2 r0) with
     | represents_bound_tRel Γ n na E e0 => f0 Γ n na E e0
     | represents_unbound_tRel E na v Γ s e0 r0 =>
         f1 E na v Γ s e0 r0 (F0 v s r0)
     | represents_tLambda Γ E na na' b b' r0 =>
         f2 Γ E na na' b b' r0 (F (na :: Γ) E b b' r0)
     | represents_tLetIn Γ E na b0 b1 na' b0' b1' r0 r1 =>
         f3 Γ E na b0 b1 na' b0' b1' r0 (F Γ E b0 b0' r0) r1
           (F (na :: Γ) E b1 b1' r1)
     | represents_tApp Γ E s s' t1 t' r0 r1 =>
         f4 Γ E s s' t1 t' r0 (F Γ E s s' r0) r1 (F Γ E t1 t' r1)
     | represents_tConst Γ E c => f5 Γ E c
     | represents_tConstruct Γ E ind i args args' a =>
         f6 Γ E ind i args args' a _
     | represents_tCase Γ E ind discr discr' brs brs' r0 Heq a =>
         f7 Γ E ind discr discr' brs brs' r0 (F Γ E discr discr' r0) Heq a _
     | represents_tFix Γ E mfix mfix' idx nms Hbodies Hnodup a a0 =>
         f8 Γ E mfix mfix' idx nms Hbodies Hnodup a a0 _
     | represents_tPrim Γ E p p' r =>
         f9 Γ E p p' r (map_onPrims (F Γ E) r)
     | represents_tLazy Γ E t t' e =>
         flazy _ _ _ _ e (F Γ E _ _ e)
     | represents_tForce Γ E t t' e =>
         fforce _ _ _ _ e (F Γ E _ _ e)
      end
   with F0 (v : value) (t : term) (r : represents_value v t) {struct r} :
     P0 v t r :=
          match r as r0 in (represents_value v0 t0) return (P0 v0 t0 r0) with
          | represents_value_tClos na E s t0 na' r0 =>
              f10 na E s t0 na' r0 (F [na] E s t0 r0)
          | represents_value_tConstruct vs ts ind c a => f11 vs ts ind c a _
          | represents_value_tFix vfix i E mfix a => f12 vfix i E mfix a _
          | represents_value_tPrim p p' r => f13 p p' r (map_onPrims F0 r)
          | represents_value_tLazy E t t' r => f14 E t t' r (F [] E t t' r)
          end
            for
            F).
Obligation 1.
  clear - a F. induction a; econstructor. eapply F. apply IHa.
Defined.
Obligation 2.
  clear - a F. induction a; econstructor. eapply F. apply IHa.
Defined.
Obligation 3.
  clear - a0 F. induction a0; econstructor. eapply F. eapply IHa0.
Defined.
Obligation 4.
  clear - a F0. induction a; econstructor. eapply F0. eapply IHa.
Defined.
Obligation 5.
  clear - a F. induction a; econstructor. eapply F. eapply IHa.
Defined.

Program Definition represents_value_ind :=
  (λ (P : ∀ (l : list ident) (e : environment) (t t0 : term),
         l;;; e ⊩ t ~ t0 → Type) (P0 : ∀ (v : value) (t : term),
         represents_value v t → Type)
     (f0 :
       ∀ (Γ : list ident)
         (n : nat)
         (na : ident)
         (E : environment)
         (e :
           nth_error Γ n = Some na),
         P Γ E
           (tVar na)
           (tRel n)
           (represents_bound_tRel Γ n
              na E e))
     (f1 : ∀ (E : environment) (na : string) (v : value)
             (Γ : list ident) (s : term) (e : lookup E na = Some v)
             (r : represents_value v s),
         P0 v s r
         → P Γ E (tVar na) s (represents_unbound_tRel E na v Γ s e r))
     (f2 : ∀ (Γ : list ident) (E : environment) (na : ident)
             (na' : name) (b b' : term) (r : (na :: Γ);;; E ⊩ b ~ b'),
         P (na :: Γ) E b b' r
         → P Γ E (tLambda (nNamed na) b) (tLambda na' b')
             (represents_tLambda Γ E na na' b b' r))
     (f3 : ∀ (Γ : list ident) (E : environment) (na : ident)
             (b0 b1 : term) (na' : name) (b0' b1' : term)
             (r : Γ;;; E ⊩ b0 ~ b0'),
         P Γ E b0 b0' r
         → ∀ r0 : (na :: Γ);;; E ⊩ b1 ~ b1',
           P (na :: Γ) E b1 b1' r0
           → P Γ E (tLetIn (nNamed na) b0 b1) (tLetIn na' b0' b1')
               (represents_tLetIn Γ E na b0 b1 na' b0' b1' r r0))
     (f4 : ∀ (Γ : list ident) (E : environment) (s s' t t' : term)
             (r : Γ;;; E ⊩ s ~ s'),
         P Γ E s s' r
         → ∀ r0 : Γ;;; E ⊩ t ~ t',
           P Γ E t t' r0
           → P Γ E (tApp s t) (tApp s' t')
               (represents_tApp Γ E s s' t t' r r0))
     (f5 : ∀ (Γ : list ident) (E : environment) (c : kername),
         P Γ E (tConst c) (tConst c) (represents_tConst Γ E c))
     (f6 : ∀ (Γ : list ident) (E : environment) (ind : inductive)
             (i : nat) (args args' : list term) (a : All2_Set (represents Γ E) args args') (IH : All2_over a (fun t t' => P Γ E t t')),
         P Γ E (tConstruct ind i args) (tConstruct ind i args')
           (represents_tConstruct Γ E ind i args args' a))
     (f7 : ∀ (Γ : list ident) (E : environment) (ind : inductive × nat)
             (discr discr' : term) (brs brs' : list (list name × term))
             (r : Γ;;; E ⊩ discr ~ discr'),
         P Γ E discr discr' r
         → forall Heq : All2_Set (fun b b' => #|b.1| = #|b'.1|) brs brs',
          ∀ a : All2_Set
                   (λ b b' : list name × term,
                       ∑ nms : list ident,
                         All2_Set (λ (n : name) (n' : ident), n = nNamed n')
                           b.1 nms × (nms ++ Γ);;; E ⊩ b.2 ~ b'.2 × NoDup nms) brs brs',
            forall IH : All2_over a (fun b b' H => P (projT1 H ++ Γ) E b.2 b'.2 (fst (snd (projT2 H)))),
           P Γ E (tCase ind discr brs) (tCase ind discr' brs')
             (represents_tCase Γ E ind discr discr' brs brs' r Heq a))
     (f8 : ∀ (Γ : list ident) (E : environment) (mfix mfix' : list (def term))
             (idx : nat) (nms : list ident) (Hbodies : List.forallb (isLambda ∘ dbody) mfix) (Hnodup : NoDup nms) (a : All2_Set
                                                 (λ (d : def term) (n : ident),
                                                   dname d = nNamed n) mfix nms)
             (a0 : All2_Set
                     (λ d d' : def term, (List.rev nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                     mfix mfix')
             (IH : All2_over a0 (fun t t' : def term => P (List.rev nms ++ Γ) E (dbody t) (dbody t'))),
         P Γ E (tFix mfix idx) (tFix mfix' idx)
           (represents_tFix Γ E mfix mfix' idx nms Hbodies Hnodup a a0))
    (f9 : forall Γ E p p' (o : onPrims (represents Γ E) p p'), onPrims_dep _ (P Γ E) _ _ o ->
        P Γ E  (tPrim p) (tPrim p') (represents_tPrim Γ E p p' o))

    (flazy : forall Γ E t t'
    (he : Γ ;;; E ⊩ t ~ t'),
    P Γ E t t' he ->
    P Γ E _ _ (represents_tLazy Γ E t t' he))

  (fforce : forall Γ E t t'
    (he : Γ ;;; E ⊩ t ~ t'),
    P Γ E t t' he ->
    P Γ E _ _ (represents_tForce Γ E t t' he))

     (f10 :
       ∀ (na : ident)
         (E : environment)
         (s t : term)
         (na' : name)
         (r :
           [na];;; E ⊩ s ~ t),
         P [na] E s t r
         → P0
             (vClos na s E)
             (tLambda na' t)
             (represents_value_tClos na E
                s t na' r))
     (f11 : ∀ (vs : list value) (ts : list term) (ind : inductive)
              (c : nat) (a : All2_Set represents_value vs ts) (IH : All2_over a P0),
         P0 (vConstruct ind c vs) (tConstruct ind c ts)
           (represents_value_tConstruct vs ts ind c a))
     (f12 : ∀ (vfix : list (ident × term)) (i : nat)
              (E : list (ident × value)) (mfix : list (def term))
              (a : All2_Set
                     (λ (v : ident × term) (d : def term), isLambda v.2 ×
                     (List.rev (map fst vfix)) ;;; E ⊩ v.2 ~ d.(dbody)) vfix mfix)
              (IH : All2_over a (fun v d H => P (List.rev (map fst vfix)) E v.2 (dbody d) (snd H)  ) ),
         P0 (vRecClos vfix i E) (tFix mfix i)
           (represents_value_tFix vfix i E mfix a))
    (f13 : forall p p' (o : onPrims represents_value p p'), onPrims_dep _ P0 _ _ o ->
           P0 (vPrim p) (tPrim p') (represents_value_tPrim p p' o))
    (f14 : forall E t t' (r : represents [] E t t'), P [] E t t' r ->
        P0 (vLazy t E) (tLazy t') (represents_value_tLazy E t t' r)),

    fix F
      (l : list ident) (e : environment) (t t0 : term)
      (r : l;;; e ⊩ t ~ t0) {struct r} : P l e t t0 r :=
     match r as r0 in (l0;;; e0 ⊩ t1 ~ t2) return (P l0 e0 t1 t2 r0) with
     | represents_bound_tRel Γ n na E e0 => f0 Γ n na E e0
     | represents_unbound_tRel E na v Γ s e0 r0 =>
         f1 E na v Γ s e0 r0 (F0 v s r0)
     | represents_tLambda Γ E na na' b b' r0 =>
         f2 Γ E na na' b b' r0 (F (na :: Γ) E b b' r0)
     | represents_tLetIn Γ E na b0 b1 na' b0' b1' r0 r1 =>
         f3 Γ E na b0 b1 na' b0' b1' r0 (F Γ E b0 b0' r0) r1
           (F (na :: Γ) E b1 b1' r1)
     | represents_tApp Γ E s s' t1 t' r0 r1 =>
         f4 Γ E s s' t1 t' r0 (F Γ E s s' r0) r1 (F Γ E t1 t' r1)
     | represents_tConst Γ E c => f5 Γ E c
     | represents_tConstruct Γ E ind i args args' a =>
         f6 Γ E ind i args args' a _
     | represents_tCase Γ E ind discr discr' brs brs' r0 Heq a =>
         f7 Γ E ind discr discr' brs brs' r0 (F Γ E discr discr' r0) Heq a _
     | represents_tFix Γ E mfix mfix' idx nms Hbodies Hnodup a a0 =>
         f8 Γ E mfix mfix' idx nms Hbodies Hnodup a a0 _
    | represents_tPrim Γ E p p' r =>
         f9 Γ E p p' r (map_onPrims (F Γ E) r)
    | represents_tLazy Γ E t t' e =>
         flazy _ _ _ _ e (F Γ E _ _ e)
     | represents_tForce Γ E t t' e =>
         fforce _ _ _ _ e (F Γ E _ _ e)

     end
   with F0 (v : value) (t : term) (r : represents_value v t) {struct r} :
     P0 v t r :=
          match r as r0 in (represents_value v0 t0) return (P0 v0 t0 r0) with
          | represents_value_tClos na E s t0 na' r0 =>
              f10 na E s t0 na' r0 (F [na] E s t0 r0)
          | represents_value_tConstruct vs ts ind c a => f11 vs ts ind c a _
          | represents_value_tFix vfix i E mfix a => f12 vfix i E mfix a _
          | represents_value_tPrim p p' r => f13 p p' r (map_onPrims F0 r)
          | represents_value_tLazy E t t' r => f14 E t t' r (F [] E t t' r)
          end
            for
            F0).
Obligation 1.
  clear - a F. induction a; econstructor. eapply F. eassumption.
Defined.
Obligation 2.
  clear - a F. induction a; econstructor. eapply F. eassumption.
Defined.
Obligation 3.
  clear - a0 F. induction a0; econstructor. eapply F. eassumption.
Defined.
Obligation 4.
  clear - a F0. induction a; econstructor. eapply F0. eassumption.
Defined.
Obligation 5.
  clear - a F. induction a; econstructor. eapply F. eassumption.
Defined.

Definition rep_ind :=
  (λ (P : ∀ (l : list ident) (e : environment) (t t0 : term),
         l;;; e ⊩ t ~ t0 → Type) (P0 : ∀ (v : value) (t : term),
         represents_value v t → Type)
   (f0 :
       ∀ (Γ : list ident)
         (n : nat)
         (na : ident)
         (E : environment)
         (e :
           nth_error Γ n = Some na),
         P Γ E
           (tVar na)
           (tRel n)
           (represents_bound_tRel Γ n
              na E e))
     (f1 : ∀ (E : environment) (na : string) (v : value)
             (Γ : list ident) (s : term) (e : lookup E na = Some v)
             (r : represents_value v s),
         P0 v s r
         → P Γ E (tVar na) s (represents_unbound_tRel E na v Γ s e r))
     (f2 : ∀ (Γ : list ident) (E : environment) (na : ident)
             (na' : name) (b b' : term) (r : (na :: Γ);;; E ⊩ b ~ b'),
         P (na :: Γ) E b b' r
         → P Γ E (tLambda (nNamed na) b) (tLambda na' b')
             (represents_tLambda Γ E na na' b b' r))
     (f3 : ∀ (Γ : list ident) (E : environment) (na : ident)
             (b0 b1 : term) (na' : name) (b0' b1' : term)
             (r : Γ;;; E ⊩ b0 ~ b0'),
         P Γ E b0 b0' r
         → ∀ r0 : (na :: Γ);;; E ⊩ b1 ~ b1',
           P (na :: Γ) E b1 b1' r0
           → P Γ E (tLetIn (nNamed na) b0 b1) (tLetIn na' b0' b1')
               (represents_tLetIn Γ E na b0 b1 na' b0' b1' r r0))
     (f4 : ∀ (Γ : list ident) (E : environment) (s s' t t' : term)
             (r : Γ;;; E ⊩ s ~ s'),
         P Γ E s s' r
         → ∀ r0 : Γ;;; E ⊩ t ~ t',
           P Γ E t t' r0
           → P Γ E (tApp s t) (tApp s' t')
               (represents_tApp Γ E s s' t t' r r0))
     (f5 : ∀ (Γ : list ident) (E : environment) (c : kername),
         P Γ E (tConst c) (tConst c) (represents_tConst Γ E c))
     (f6 : ∀ (Γ : list ident) (E : environment) (ind : inductive)
             (i : nat) (args args' : list term) (a : All2_Set (represents Γ E) args args') (IH : All2_over a (fun t t' => P Γ E t t')),
         P Γ E (tConstruct ind i args) (tConstruct ind i args')
           (represents_tConstruct Γ E ind i args args' a))
     (f7 : ∀ (Γ : list ident) (E : environment) (ind : inductive × nat)
             (discr discr' : term) (brs brs' : list (list name × term))
             (r : Γ;;; E ⊩ discr ~ discr'),
         P Γ E discr discr' r
         → forall Heq : All2_Set (fun b b' => #|b.1| = #|b'.1|) brs brs',
         ∀ a : All2_Set
                   (λ b b' : list name × term,
                       ∑ nms : list ident,
                         All2_Set (λ (n : name) (n' : ident), n = nNamed n')
                           b.1 nms × (nms ++ Γ);;; E ⊩ b.2 ~ b'.2 × NoDup nms) brs brs',
          forall IH : All2_over a (fun b b' H => P (projT1 H ++ Γ) E b.2 b'.2 (fst (snd (projT2 H)))),
           P Γ E (tCase ind discr brs) (tCase ind discr' brs')
             (represents_tCase Γ E ind discr discr' brs brs' r Heq a))
     (f8 : ∀ (Γ : list ident) (E : environment) (mfix mfix' : list (def term))
             (idx : nat) (nms : list ident) (Hbodies : List.forallb (isLambda ∘ dbody) mfix) (Hnodup : NoDup nms) (a : All2_Set
                                                 (λ (d : def term) (n : ident),
                                                   dname d = nNamed n) mfix nms)
             (a0 : All2_Set
                     (λ d d' : def term, (List.rev nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                     mfix mfix')
             (IH : All2_over a0 (fun t t' : def term => P (List.rev nms ++ Γ) E (dbody t) (dbody t'))),
         P Γ E (tFix mfix idx) (tFix mfix' idx)
           (represents_tFix Γ E mfix mfix' idx nms Hbodies Hnodup a a0))
      (f9 : forall Γ E p p' (o : onPrims (represents Γ E) p p'), onPrims_dep _ (P Γ E) _ _ o ->
           P Γ E  (tPrim p) (tPrim p') (represents_tPrim Γ E p p' o))
      (flazy : forall Γ E t t'
        (he : Γ ;;; E ⊩ t ~ t'),
        P Γ E t t' he ->
        P Γ E _ _ (represents_tLazy Γ E t t' he))

      (fforce : forall Γ E t t'
        (he : Γ ;;; E ⊩ t ~ t'),
        P Γ E t t' he ->
        P Γ E _ _ (represents_tForce Γ E t t' he))
      (f10 :
       ∀ (na : ident)
         (E : environment)
         (s t : term)
         (na' : name)
         (r :
           [na];;; E ⊩ s ~ t),
         P [na] E s t r
         → P0
             (vClos na s E)
             (tLambda na' t)
             (represents_value_tClos na E
                s t na' r))
     (f11 : ∀ (vs : list value) (ts : list term) (ind : inductive)
              (c : nat) (a : All2_Set represents_value vs ts) (IH : All2_over a P0),
         P0 (vConstruct ind c vs) (tConstruct ind c ts)
           (represents_value_tConstruct vs ts ind c a))
     (f12 : ∀ (vfix : list (ident × term)) (i : nat)
              (E : list (ident × value)) (mfix : list (def term))
              (a : All2_Set
                     (λ (v : ident × term) (d : def term), isLambda v.2 ×
                     (List.rev (map fst vfix)) ;;;
                         E ⊩ v.2 ~
                         dbody d) vfix mfix)
              (IH : All2_over a (fun v d H => P (List.rev (map fst vfix)) E v.2 (dbody d) (snd H)  ) ),
         P0 (vRecClos vfix i E) (tFix mfix i)
           (represents_value_tFix vfix i E mfix a))
      (f13 : forall p p' (o : onPrims represents_value p p'), onPrims_dep _ P0 _ _ o ->
           P0 (vPrim p) (tPrim p') (represents_value_tPrim p p' o))
      f14
           ,
    (represents_ind P P0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 flazy fforce f10 f11 f12 f13 f14,
      represents_value_ind P P0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 flazy fforce f10 f11 f12 f13 f14)).

Local Notation "'⊩' v ~ s" := (represents_value v s) (at level 50).
Local Hint Constructors represents : core.
Local Hint Constructors represents_value : core.

Fixpoint gen_fresh_aux (na : ident) (Γ : list string) i :=
  match i with
  | 0 => na
  | S i' =>
      let na' := String.append na (string_of_nat ((List.length Γ) - i)) in
      if in_dec (ReflectEq_EqDec _) na' Γ then gen_fresh_aux na Γ i' else na'
  end.

Definition gen_fresh (na : string) (Γ : list string) :=
  gen_fresh_aux na Γ (List.length Γ).

Lemma gen_fresh_aux_spec na Γ i :
  i <= List.length Γ ->
  (exists j, j <= i /\
          let na' := append na (string_of_nat ((List.length Γ - j))) in
          gen_fresh_aux na Γ i = na' /\
            ~ In na' Γ /\
            forall k, j < k <= i -> In (append na (string_of_nat ((List.length Γ - k)))) Γ) \/
    (gen_fresh_aux na Γ i = na /\
       forall k, k < i -> In (append na (string_of_nat ((List.length Γ - S k)))) Γ).
Proof.
  induction i as [ | i IHi].
  - right. split. 1: reflexivity. intros. lia.
  - intros H. cbn.
    destruct IHi as [ (j & H1 & H2 & H3 &H4) | (H1 & H2)].
    + lia.
    + destruct in_dec.
      * left. exists j. repeat split; [ firstorder .. | ].
        intros k [].
        assert (k = S i \/ k <= i) as [-> | Ha] by lia; eauto.
      * left. exists (S i). firstorder. lia.
    + destruct in_dec.
      * right. split; [ firstorder | ].
        intros k Hk.
        assert (k = i \/ k < i) as [-> | Ha] by lia; eauto.
      * left. exists (S i). firstorder. lia.
Qed.

Lemma append_inv (s s1 s2 : string) :
  append s s1 = append s s2 ->
  s1 = s2.
Proof.
  induction s; cbn; eauto.
  inversion 1; eauto.
Qed.

Lemma append_Empty_r s :
  append s EmptyString = s.
Proof.
  induction s; cbn; congruence.
Qed.

Lemma NoDup_map {X Y} (f : X -> Y) l :
  (forall x1 x2, In x1 l -> In x2 l -> f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  induction 2; cbn; econstructor.
  1: intros (? & ? & ?) % in_map_iff.
  all: firstorder congruence.
Qed.

From Stdlib Require Import DecimalNat.

Lemma string_of_nat_empty n :
  string_of_nat n <> "".
Proof.
  unfold string_of_nat.
  enough (Nat.to_uint n <> Decimal.Nil).
  destruct (Nat.to_uint n); cbn; congruence.
  rewrite Unsigned.to_uint_alt.
  intros E % DecimalFacts.rev_nil_inv.
  destruct n; cbn in E; try congruence.
  destruct (Unsigned.to_lu n); cbn in *; congruence.
Qed.

Lemma string_of_uint_inj n1 n2 :
  string_of_uint n1 = string_of_uint n2 → n1 = n2.
Proof.
  revert n2.
  induction n1; intros []; cbn; intros Heq; f_equal; try congruence.
  all: inversion Heq; eauto.
Qed.

From Stdlib Require Import DecimalNat.

Lemma string_of_nat_inj n1 n2 :
  string_of_nat n1 = string_of_nat n2 -> n1 = n2.
Proof.
  intros H % string_of_uint_inj.
  eapply (f_equal (Nat.of_uint)) in H.
  now rewrite !DecimalNat.Unsigned.of_to in H.
Qed.

Lemma gen_fresh_fresh na Γ :
  ~ In (gen_fresh na Γ) Γ.
Proof.
  unfold gen_fresh.
  destruct (gen_fresh_aux_spec na Γ (List.length Γ)) as [ (j & Hle & Heq & Hin & Hl) | (Heq & Hl)].
  - lia.
  - rewrite Heq. eauto.
  - rewrite Heq. intros Hna.
    assert (NoDup (na :: map (fun k => na ++ string_of_nat (Datatypes.length Γ - S k))%bs (seq 0 (List.length Γ)))) as HN.
    { econstructor.
      - intros (? & Hla & [_ ? % Hl] % in_seq) % in_map_iff.
        rewrite <- (append_Empty_r na) in Hla at 2.
        now eapply append_inv, string_of_nat_empty in Hla.
      - eapply NoDup_map. 2: eapply seq_NoDup.
        clear. intros x1 x2 H1 % in_seq H2 % in_seq Heq % append_inv.
        eapply string_of_nat_inj in Heq.
        lia.
    }
    eapply NoDup_incl_length with (l' := Γ) in HN.
    { cbn in HN. rewrite length_map length_seq in HN. lia. }
    intros ? [ -> | (? & <- & [_ ? % Hl] % in_seq) % in_map_iff ]; eauto.
Qed.

Fixpoint gen_many_fresh Γ nms :=
  match nms with
  | [] => []
  | nAnon :: nms => let na' := gen_fresh "wildcard" Γ in
                    na' :: gen_many_fresh (na' :: Γ) nms
  | nNamed na :: nms => let na' := if in_dec (ReflectEq_EqDec _) na Γ then gen_fresh na Γ else na in
                        na' :: gen_many_fresh (na' :: Γ) nms
  end.

Lemma gen_many_fresh_length Γ nms : #|gen_many_fresh Γ nms| = #|nms|.
Proof.
  induction nms as [ | [] ] in Γ |- *; cbn; congruence.
Qed.

Definition map_def_name :=
  λ (term : Set) g (f : term → term) (d : def term),
    {| dname := g (dname d); dbody := f (dbody d); rarg := rarg d |}.


(* Section Map2. *)

(*   Context {A B C : Type}. *)
(*   Variable (f : A → B → C). *)
(*   Fixpoint map2 (l : list A) (l' : list B) {struct l} : *)
(*    list C := *)
(*     match l with *)
(*     | [] => [] *)
(*     | hd :: tl => *)
(*         match l' with *)
(*         | [] => [] *)
(*         | hd' :: tl' => f hd hd' :: map2 tl tl' *)
(*         end *)
(*     end. *)
(* End Map2. *)

Fixpoint annotate (s : list ident) (u : term) {struct u} : term :=
  match u with
  | tRel n => match nth_error s n with
              | Some na => tVar na
              | None => tRel n
              end
  | tEvar ev args => tEvar ev (map (annotate s) args)
  | tLambda na M => let na' := match na with
                               | nNamed na => if in_dec (ReflectEq_EqDec _) na s then gen_fresh na s else na
                               | nAnon => gen_fresh "wildcard" s
                               end in
                    tLambda (nNamed na') (annotate (na' :: s) M)
  | tLetIn na b b' =>
      let na' := match na with
                 | nNamed na => if in_dec (ReflectEq_EqDec _) na s then gen_fresh na s else na
                 | nAnon => gen_fresh "wildcard" s
                 end in
      tLetIn (nNamed na') (annotate s b) (annotate (na' :: s) b')
  | tApp u0 v => tApp (annotate s u0) (annotate s v)
  | tConstruct ind i args => tConstruct ind i (map (annotate s) args)
  | tCase ind c brs =>
      let brs' :=
        map (λ br : list name × term,
              let nms := gen_many_fresh s br.1 in
              (map nNamed nms, annotate (nms ++ s) br.2)) brs
      in
      tCase ind (annotate s c) brs'
  | tProj p c => tProj p (annotate s c)
  | tFix mfix idx =>
      let nms := gen_many_fresh s (map dname mfix) in
      let mfix' := map2 (fun d na => map_def_name _ (fun _ => nNamed na) (annotate (List.rev (gen_many_fresh s ((map dname mfix))) ++ s)) d) mfix nms in
      tFix mfix' idx
  | tCoFix mfix idx =>
    let nms := gen_many_fresh s (map dname mfix) in
    let mfix' := map2 (fun d na => map_def_name _ (fun _ => nNamed na) (annotate (List.rev (gen_many_fresh s ((map dname mfix))) ++ s)) d) mfix nms in
      tCoFix mfix' idx
  | tPrim p => tPrim (map_prim (annotate s) p)
  | tLazy t => tLazy (annotate s t)
  | tForce t => tForce (annotate s t)
  | _ => u
  end.

Fixpoint annotate_env Γ (Σ : global_declarations) :=
  match Σ with
  | (na, ConstantDecl (Build_constant_body (Some b))) :: Σ => (na, ConstantDecl (Build_constant_body (Some (annotate Γ b)))) :: annotate_env (Γ) Σ
  | d :: Σ => d :: annotate_env Γ Σ
  | nil => nil
  end.

Definition extraction_term_flags :=
  {| has_tBox := false
  ; has_tRel := true
  ; has_tVar := false
  ; has_tEvar := false
  ; has_tLambda := true
  ; has_tLetIn := true
  ; has_tApp := true
  ; has_tConst := true
  ; has_tConstruct := true
  ; has_tCase := true
  ; has_tProj := false
  ; has_tFix := true
  ; has_tCoFix := false
  ; has_tPrim := all_primitive_flags
  ; has_tLazy_Force := true
  |}.

Definition extraction_env_flags :=
  {| has_axioms := false;
    term_switches := extraction_term_flags;
    has_cstr_params := false ;
    cstr_as_blocks := true |}.

Local Existing Instance extraction_env_flags.

Lemma NoDup_gen_many_fresh Γ l :
  NoDup (gen_many_fresh Γ l) /\ forall x, In x (gen_many_fresh Γ l) -> ~ In x Γ.
Proof.
  induction l as [ | []] in Γ |- *; cbn.
  - split. econstructor. firstorder.
  - econstructor; eauto. econstructor.
    + intros H % IHl. eapply H. now left.
    + eapply IHl.
    + intros x [<- | ?]. 1: eapply gen_fresh_fresh. eapply IHl in H. firstorder.
  - destruct in_dec; cbn.
    + split. econstructor.
      * intros H % IHl. eapply H. now left.
      * eapply IHl.
      * intros x [<- | ?]. 1: eapply gen_fresh_fresh. eapply IHl in H. firstorder.
    + split. econstructor.
      * intros H % IHl. eapply H. now left.
      * eapply IHl.
      * intros x [<- | ?]. 1: eauto. eapply IHl in H. firstorder.
Qed.

Definition named_extraction_term_flags :=
  {| has_tBox := false
  ; has_tRel := false
  ; has_tVar := true
  ; has_tEvar := false
  ; has_tLambda := true
  ; has_tLetIn := true
  ; has_tApp := true
  ; has_tConst := true
  ; has_tConstruct := true
  ; has_tCase := true
  ; has_tProj := false
  ; has_tFix := true
  ; has_tCoFix := false
  ; has_tPrim := all_primitive_flags
  ; has_tLazy_Force := true
  |}.

Definition named_extraction_env_flags :=
  {| has_axioms := false;
    term_switches := named_extraction_term_flags;
    has_cstr_params := false ;
    cstr_as_blocks := true |}.

Lemma lookup_annotate_env Γ Σ i d :
  lookup_env Σ i = Some d ->
  lookup_env (annotate_env Γ Σ) i = Some
    match d with
    | ConstantDecl {| cst_body := b |} => ConstantDecl {| cst_body := option_map (annotate Γ) b |}
    | InductiveDecl m => InductiveDecl m
    end.
Proof.
  induction Σ in i |- *; cbn; try congruence.
  destruct a. cbn.
  destruct (eqb_spec i k).
  + subst. intros [= ->].
    destruct d as [ [ []] | ]; cbn; now rewrite eqb_refl.
  + intros Hi % IHΣ. destruct d as [ [] | ]; cbn in *;
    destruct g as [ [[]]| ]; cbn; destruct (eqb_spec i k); try congruence.
Qed.

Local Hint Resolve incl_tl incl_appr incl_appl : core.

Definition switch_term_flags_to_named (efl : ETermFlags) :=
  {|
    has_tBox := has_tBox;
    has_tRel := false;
    has_tVar := true;
    has_tEvar := has_tEvar;
    has_tLambda := has_tLambda;
    has_tLetIn := has_tLetIn;
    has_tApp := has_tApp;
    has_tConst := has_tConst;
    has_tConstruct := has_tConstruct;
    has_tCase := has_tCase;
    has_tProj := has_tProj;
    has_tFix := has_tFix;
    has_tCoFix := has_tCoFix;
    has_tPrim := has_tPrim;
    has_tLazy_Force := has_tLazy_Force
  |}.

Definition switch_env_flags_to_named (efl : EEnvFlags) :=
  {|
    has_axioms := has_axioms;
    has_cstr_params := has_cstr_params;
    term_switches := switch_term_flags_to_named efl.(term_switches);
    cstr_as_blocks := efl.(cstr_as_blocks) |}.

Lemma wellformed_annotate' efl Σ Γ Γ' s :
  incl Γ' Γ ->
  @wellformed efl Σ #|Γ| s ->
  @wellformed (switch_env_flags_to_named efl) (annotate_env Γ' Σ) #|Γ| (annotate Γ s).
Proof.
  intros Hincl Hwf.
  induction s in Γ, Hwf, Γ', Hincl |- * using EInduction.term_forall_list_ind; cbn in *; rtoProp; unshelve intuition eauto.
  - eapply Nat.ltb_lt in H0. destruct nth_error eqn:Eq; eauto.
    eapply nth_error_None in Eq. lia.
  - solve_all.
  - destruct n; cbn. 2: destruct in_dec.
    all: eapply (IHs (_ :: Γ)); cbn; eauto.
  - destruct n; cbn. 2: destruct in_dec; cbn.
    all: eapply (IHs2 (_ :: Γ)); cbn; eauto.
  - destruct lookup_env as [ [] | ] eqn:E; cbn in *; eauto.
    destruct c, cst_body; cbn in *; try congruence.
    erewrite lookup_annotate_env; eauto. cbn; eauto.
    now erewrite lookup_annotate_env; eauto.
  - destruct lookup_env as [ [] | ] eqn:E; cbn in *; eauto.
    erewrite lookup_annotate_env; eauto. cbn.
    destruct nth_error as [ [] | ]; cbn in *; eauto.
  - destruct lookup_env as [ [] | ] eqn:E; cbn in *; eauto.
    erewrite lookup_annotate_env; eauto. cbn.
    destruct nth_error as [ [] | ]; cbn in *; eauto.
    destruct nth_error as [ [] | ]; cbn in *; eauto.
    repeat split. len. solve_all.
    destruct cstr_as_blocks; eauto.
    rtoProp; intuition eauto. solve_all. destruct args => //.
  - move: H0; rewrite /wf_brs; cbn; destruct lookup_env as [ [] | ] eqn:E; cbn in *; eauto.
    erewrite lookup_annotate_env; eauto. cbn.
    destruct nth_error as [ [] | ]; cbn in *; eauto. len.
  - move: H0; rewrite /wf_brs; cbn; destruct lookup_env as [ [] | ] eqn:E; cbn in *; eauto.
    destruct nth_error as [ [] | ]; cbn in *; eauto. intros eq.
    solve_all. rewrite length_map. rewrite <- length_app.
    eapply a; eauto. len. rewrite gen_many_fresh_length. eauto.
  - destruct lookup_env as [ [] | ] eqn:E; cbn in *; eauto.
    erewrite lookup_annotate_env; eauto. cbn.
    destruct nth_error as [ [] | ]; cbn in *; eauto.

  - clear - H1. solve_all.
    generalize (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ).
    generalize (gen_many_fresh Γ (map dname m)).
    induction H1.
    + econstructor.
    + destruct x; cbn in *. destruct l0 => //=. cbn.
      constructor; cbn.
      destruct dbody; cbn in *; eauto.
      eapply IHAll.
  - solve_all. unfold wf_fix in *. rtoProp. split.
    rewrite map2_length gen_many_fresh_length length_map.
    { eapply Nat.ltb_lt in H0. eapply Nat.ltb_lt. lia. }
    solve_all. clear H0. unfold test_def in *. cbn in *.
    eapply All_impl in H2. 2:{ intros ? [[] ].
      specialize (i (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
      revert i. rewrite ?List.length_rev length_app ?List.length_rev gen_many_fresh_length ?List.length_rev length_map. intros r. eapply r in i1. exact i1.
      eapply incl_appr. eauto.
      }
      revert H2.
      generalize ((List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
      intros. rewrite map2_length gen_many_fresh_length length_map Nat.min_id.
      revert H2. generalize (#|m| + #|Γ|).
      intros.
      induction m in Γ, n, n0, l, H2 |- *.
      + econstructor.
      + invs H2. cbn. destruct a; cbn. destruct dname; cbn; econstructor; eauto.
  - solve_all. unfold wf_fix in *. rtoProp. split.
    rewrite map2_length gen_many_fresh_length length_map.
    { eapply Nat.ltb_lt in H0. eapply Nat.ltb_lt. lia. }
    solve_all. clear H0. unfold test_def in *. cbn in *.
    eapply All_impl in H1. 2:{ intros ? [i].
    specialize (i (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
      revert i. rewrite ?List.length_rev length_app ?List.length_rev gen_many_fresh_length ?List.length_rev length_map. intros r.
      eapply r in i0. exact i0.
      eapply incl_appr. eauto.
      }
    revert H1.
    generalize ((List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
    intros. rewrite map2_length gen_many_fresh_length length_map Nat.min_id.
    revert H1. generalize (#|m| + #|Γ|).
    intros.
    induction m in Γ, n, n0, l, H1 |- *.
    + econstructor.
    + invs H1. cbn. destruct a; cbn. destruct dname; cbn; econstructor; eauto.
  - repeat solve_all.
  - solve_all_k 6.
Qed.

Lemma wellformed_annotate Σ Γ s efl :
  wellformed (efl := efl) Σ #|Γ| s ->
  wellformed (efl := switch_env_flags_to_named efl) (annotate_env Γ Σ) #|Γ| (annotate Γ s).
Proof.
  eapply wellformed_annotate'. firstorder.
Qed.

Lemma nclosed_represents efl Σ Γ E s :
  ~~ has_tBox -> ~~ has_tVar -> ~~ has_tEvar -> ~~ has_tCoFix -> ~~ has_tProj ->
  wellformed (efl := efl) Σ #|Γ| s -> Γ ;;; E ⊩ annotate Γ s ~ s.
Proof.
  intros nb nv nev ncof nproj Hwf.
  induction s in Γ, Hwf |- * using EInduction.term_forall_list_ind;
    cbn -[lookup_constructor lookup_inductive] in *; rtoProp; unshelve eauto.
  - now rewrite Hwf in nb.
  - eapply Nat.ltb_lt in H0. destruct nth_error eqn:Eq; eauto.
    eapply nth_error_None in Eq. lia.
  - now rewrite Hwf in nv.
  - now rewrite H in nev.
  - econstructor. destruct cstr_as_blocks.
    destruct lookup_constructor as [[[mib oib] ctor]|] => //. cbn in *.
    rtoProp.
    { eapply All2_All2_Set. solve_all. }
    destruct args => //.
  - econstructor; eauto.
    eapply All2_All2_Set; solve_all.
    { eapply All_All2. eapply H1. cbn. intros [] []; cbn in *.
      len. now rewrite gen_many_fresh_length. }
    solve_all.
    clear - Γ H1. induction H1; econstructor; eauto.
    rename x into br. exists (gen_many_fresh Γ br.1). cbn. split.
    + eapply All2_All2_Set. solve_all. now eapply All2_refl.
    + split.
      * eapply p. rewrite length_app gen_many_fresh_length. eapply p.
      * eapply NoDup_gen_many_fresh.
  - now rewrite H in nproj.
  - eapply represents_tFix with (nms := gen_many_fresh Γ (map dname m)).
    1:{ solve_all. generalize (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ). clear - H1.
        induction H1 in Γ; cbn. econstructor. intros. destruct x, dname; cbn. all: econstructor.
        - cbn in *. destruct p, dbody; cbn in *; try congruence.
        - eapply IHAll.
        - cbn in *. destruct p, dbody; cbn in *; try congruence.
        - eapply IHAll.
    }
    1:{ eapply NoDup_gen_many_fresh. }
    { clear.  generalize ((List.rev (gen_many_fresh Γ ( (map dname m))) ++ Γ)).
      induction m in Γ |- *; cbn.
      - econstructor.
      - intros. destruct a; cbn. destruct dname; cbn; try econstructor; eauto.
    }
    { solve_all. unfold wf_fix in *. rtoProp. solve_all. clear H0. unfold test_def in *. cbn in *.
      eapply All_impl in H2. 2:{ intros ? [[] ].
      specialize (r (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
      revert r. rewrite ?List.length_rev length_app ?List.length_rev gen_many_fresh_length ?List.length_rev length_map. intros r. eapply r in i0. exact i0.
      }
      revert H2.
      generalize ((List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
      intros. induction H2 in Γ |- *.
      - econstructor.
      - cbn. destruct x; cbn. destruct dname; cbn; econstructor; eauto.
    }
  - now rewrite H in ncof.
  - constructor; solve_all. depelim H1; cbn; solve_all; try econstructor.
    destruct a; constructor; solve_all. eapply All2_All2_Set. solve_all.
Qed.

Lemma unfolds_bound :
  (forall Γ E s t, Γ ;;; E ⊩ s ~ t -> closedn #|Γ| t) ×
    (forall v s, ⊩ v ~ s -> closedn 0 s).
Proof.
  refine (rep_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros; cbn; rtoProp; eauto.
  - eapply Nat.ltb_lt, nth_error_Some. congruence.
  - eapply closed_upwards; eauto. lia.
  - solve_all. induction a; cbn in *; econstructor; firstorder.
  - split. eauto. solve_all. induction a; cbn in *; econstructor; firstorder.
    destruct r0 as (nms & Hl1 & Hl2). cbn in *.
    invs Heq. rewrite <- H3. revert a1. len.
    eapply All2_Set_All2, All2_length in Hl1 as ->. eauto.
    eapply IHa. now invs Heq. eauto.
  - solve_all. eapply All2_Set_All2 in a.
    enough (#|mfix'| = #|nms|) as ->.
    2:{ eapply All2_length in a. clear IH. eapply All2_Set_All2, All2_length in a0.
        len. }
    clear Hbodies a. induction a0; cbn in *; econstructor.
    rewrite length_app List.length_rev in IH. eapply IH.
    eapply IHa0. eapply IH.
  - depelim X; solve_all; try constructor; cbn; solve_all.
    eapply All2_over_undep in a. solve_all.
  - solve_all. induction a; cbn in *; rtoProp; eauto.
    econstructor. cbn in *. eapply IH. eapply IHa. eapply IH.
  - rewrite List.length_rev length_map in IH.
    assert (Hlen : #|vfix| = #|mfix|). { clear IH. eapply All2_Set_All2, All2_length in a. lia. }
    rewrite Hlen in IH. revert IH. generalize (#|mfix|).
    induction a; intros n H; cbn in *; rtoProp; split.
    + destruct H. revert i0. len.
    + eapply IHa. lia. eapply H.
  - depelim X; solve_all; try constructor; cbn; solve_all.
    eapply All2_over_undep in a. solve_all.
Qed.

Lemma represents_bound_head Γ E v s x :
  ⊩ v ~ s -> Γ ;;; add x v E ⊩ tVar x ~ s.
Proof.
  intros H. invs H; econstructor; unfold lookup, add.
  all: try now econstructor.
  all: cbn; change (eqb x x) with (x == x); now rewrite eqb_refl.
Qed.

Lemma represents_subst' Γ1 Γ2 E s s' t v na :
  ~ In na (map fst E) ->
  ⊩ v ~ t ->
  (Γ1 ++ na :: Γ2) ;;; E ⊩ s ~ s' ->
  (Γ1 ++ Γ2) ;;; add na v E ⊩ s ~ csubst t #|Γ1| s'.
Proof.
  intros Hna Hp Hs.
  remember (Γ1 ++ na :: Γ2) as Γ' eqn:eq__d.
  revert Γ1 Γ2 Hp eq__d Hna.
  eapply @represents_ind with (e := E) (l := Γ') (t := s) (t0 := s') (P0 := fun _ _ _ => True).

  all: intros; subst. all: cbn; eauto.
  - destruct (Nat.compare #|Γ1| n) eqn:Eq.
    + eapply Nat.compare_eq in Eq. subst.
      rewrite nth_error_app2 in e. 1: lia.
      rewrite Nat.sub_diag in e. invs e.
      econstructor; eauto. unfold lookup. cbn.
      change (eqb na0 na0) with (na0 == na0); now rewrite eqb_refl.
    + eapply Nat.compare_lt_iff in Eq.
      econstructor. destruct n; [lia | ].
      rewrite !nth_error_app2 in e |- *; cbn; [ lia .. | ].
      now replace (S n - #|Γ1|) with (S (n - #|Γ1|)) in * by lia.
    + eapply Nat.compare_gt_iff in Eq.
      econstructor. rewrite !nth_error_app1 in e |- *; eauto.
  - econstructor. instantiate (1 := v0).
    + unfold lookup in *. cbn. change (eqb na0 na) with (na0 == na) in *.
      destruct (eqb_spec na0 na); eauto.
      subst. destruct List.find as [ [] | ] eqn:Ef; invs e.
      eapply find_some in Ef as [H1 H2].
      change (eqb na t0) with (na == t0) in *.
      eapply eqb_eq in H2. subst.
      destruct Hna. eapply in_map_iff. exists (t0, v0); cbn; eauto.
    + rewrite csubst_closed; eauto.
      eapply closed_upwards.
      * now eapply unfolds_bound.
      * lia.
  - econstructor. eapply (H (na0 :: Γ1)); eauto.
  - econstructor. eapply H; eauto. eapply (H0 (na0 :: Γ1)); eauto.
  - econstructor. induction a; cbn.
    + econstructor.
    + cbn in *. econstructor. eapply IH; eauto.
      eapply IHa. eapply IH.
  - econstructor. eapply H; eauto.
    eapply All2_Set_All2 in Heq. eapply All2_All2_Set. solve_all.
    induction a; cbn.
    + econstructor.
    + cbn in *.
      destruct r0 as (nms & H1 & H2).
      destruct IH as [IH1 IH2].
      econstructor. 2: eapply IHa. 3: eapply IH2.
      2:{ now invs Heq. }
      exists nms. split. eauto.
      specialize (IH1 (nms ++ Γ1)).
      rewrite length_app in IH1.
      assert (#|y.1| = #|x.1|) as -> by now invs Heq.
      eapply All2_Set_All2 in H1 as HH. eapply All2_length in HH as ->.
      rewrite app_assoc. split.
      * eapply IH1. eauto. cbn. now rewrite <- app_assoc. eauto.
      * eapply H2.
  - econstructor; eauto.
    eapply All2_Set_All2, All2_length in a.
    assert (#|mfix'| = #|nms|) as ->.
    eapply All2_Set_All2 in a0 as Hlen.
    now eapply All2_length in Hlen.
    clear a.
    clear - Hp IH Hna. revert nms Γ1 mfix' a0 IH Hp Hna.
    induction mfix; intros.
    + inversion a0; subst. cbn. eauto.
    + cbn. depelim a0. cbn. invs IH. econstructor.
      * cbn.
        specialize (H (List.rev nms ++ Γ1) Γ2).
        rewrite length_app in H.
        rewrite <- !app_assoc in *. rewrite List.length_rev in H. eapply H; eauto.
      * eapply IHmfix; eauto.
  - econstructor; eauto.
    depelim X; solve_all; constructor; solve_all.
    eapply All2_over_undep in a. eapply All2_All2_Set; solve_all.
Qed.

Lemma represents_subst E s s' t v na :
  ~ In na (map fst E) ->
  ⊩ v ~ t ->
  [na] ;;; E ⊩ s ~ s' ->
  [] ;;; add na v E ⊩ s ~ csubst t 0 s'.
Proof.
  eapply represents_subst' with (Γ1 := []) (Γ2 := []).
Qed.

Lemma represents_subst_ctx Γ E s s' t v na :
  ~ In na (map fst E) ->
  ⊩ v ~ t ->
  (na :: Γ) ;;; E ⊩ s ~ s' ->
  Γ ;;; add na v E ⊩ s ~ csubst t 0 s'.
Proof.
  eapply represents_subst' with (Γ1 := []) (Γ2 := Γ).
Qed.

Lemma map_fst_add_multiple nms args Γ :
  #|nms| = #|args| ->
  map fst (add_multiple nms args Γ) = nms ++ map fst Γ.
Proof.
  induction nms in args |- *; intros Hlen; destruct args; cbn in *; try lia; eauto.
  now rewrite IHnms.
Qed.

Lemma represents_substl E s s' ts nms vs Γ :
  (forall na, In na nms -> ~ In na (map fst E)) ->
  NoDup nms ->
  #|nms| = #|vs| ->
  All2 represents_value vs ts ->
  (nms ++ Γ) ;;; E ⊩ s ~ s' ->
  Γ ;;; add_multiple (List.rev nms) (List.rev vs) E ⊩ s ~ substl ts s'.
Proof.
  revert ts vs s s' E Γ.
  induction nms using rev_ind; intros ts vs s s' E Γ Hna Hdup Hlen Hall Hrep.
  - destruct vs; cbn in *; try lia. invs Hall. eauto.
  - destruct vs using rev_ind; repeat rewrite length_app in Hlen; cbn in *; try lia.
    clear IHvs.
    eapply All2_app_inv_l in Hall as (vs' & ? & -> & H1 & H2). invs H2. invs X.
    unfold substl. rewrite fold_left_app. cbn.
    rewrite !rev_app_distr. cbn.
    eapply represents_subst_ctx.
    { apply NoDup_rev in Hdup. rewrite rev_app_distr in Hdup. cbn in Hdup. invs Hdup.
      rewrite <- in_rev in H2.
      rewrite map_fst_add_multiple. len. intros [ ? % in_rev | (? & <- & ?) % in_map_iff ] % in_app_iff; eauto.
      eapply Hna. rewrite in_app_iff. right. cbn. now left.
      eapply in_map_iff. exists x1. eauto.
    }
    eauto. eapply IHnms.
    { intros ? ? ?. eapply Hna; eauto. now rewrite in_app_iff. }
    { apply NoDup_rev in Hdup. rewrite rev_app_distr in Hdup. cbn in Hdup. invs Hdup.
      apply NoDup_rev in H3. now rewrite rev_involutive in H3. }
    lia. eauto. now rewrite <- app_assoc in Hrep.
Qed.

Lemma add_multiple_app nms1 nms2 vs1 vs2 E :
  #|nms1| = #|vs1| ->
  add_multiple (nms1 ++ nms2) (vs1 ++ vs2) E =
  add_multiple nms1 vs1 (add_multiple nms2 vs2 E).
Proof.
  induction nms1 in vs1 |- *; intros Hlen; cbn;
    destruct vs1; cbn in *; try congruence.
  f_equal. eapply IHnms1. lia.
Qed.

Lemma represents_substl_rev E s s' ts nms vs Γ :
  (forall na, In na nms -> ~ In na (map fst E)) ->
  NoDup nms ->
  #|nms| = #|vs| ->
  All2 represents_value vs ts ->
  (nms ++ Γ) ;;; E ⊩ s ~ s' ->
  Γ ;;; add_multiple nms vs E ⊩ s ~ substl ts s'.
Proof.
  revert ts vs s s' E Γ.
  induction nms using rev_ind; intros ts vs s s' E Γ Hna Hdup Hlen Hall Hrep.
  - destruct vs; cbn in *; try lia. invs Hall. eauto.
  - destruct vs using rev_ind; repeat rewrite length_app in Hlen; cbn in *; try lia.
    clear IHvs.
    eapply All2_app_inv_l in Hall as (vs' & ? & -> & H1 & H2). invs H2. invs X.
    unfold substl. rewrite fold_left_app. cbn.
    rewrite add_multiple_app. 1: lia. cbn.
    rewrite <- substl_csubst_comm.
    + eapply IHnms.
      * intros ? ? ?. cbn in H0. destruct H0 as [-> | H0].
        -- eapply NoDup_remove_2 in Hdup. now rewrite app_nil_r in Hdup.
        -- eapply Hna; eauto. now rewrite in_app_iff.
      * rewrite <- app_nil_r. eapply NoDup_remove_1; eauto.
      * lia.
      * eauto.
      * rewrite <- plus_n_O. assert (#|vs'| = #|nms|) as ->. { eapply All2_length in H1. lia. }
        eapply represents_subst'; eauto.
        2: now rewrite <- app_assoc in Hrep. eapply Hna, in_app_iff; cbn; eauto.
    + solve_all. now eapply unfolds_bound.
    + now eapply unfolds_bound.
Qed.

Definition extraction_wcbv_flags :=
  {| with_prop_case := false ; with_guarded_fix := false ; with_constructor_as_block := true |}.

Local Existing Instance extraction_wcbv_flags.

Lemma eval_represents_value Σ s t :
  EWcbvEval.eval Σ s t -> forall v, represents_value v s -> represents_value v t.
Proof.
  intros Heval v Hv.
  induction Heval in v, Hv |- *; inv Hv; eauto.
  econstructor. rename H1 into Hall.
  clear - a iha Hall.
  induction a in vs, Hall, iha |- *; cbn in *; invs Hall.
  - econstructor.
  - invs iha. econstructor; eauto.
  - econstructor. depelim H1; depelim X; solve_all; cbn; try constructor. eauto.
    eapply All2_over_undep in a. clear -a a2.
    induction a in v, a2 |- *; depelim a2; constructor; eauto.
Qed.

Definition fresh (na : ident) Γ := ~~ in_dec (ReflectEq_EqDec _) na Γ.

Lemma dupfree_dec_ident (Γ : list ident) :
  {NoDup Γ} + {~ NoDup Γ}.
Proof.
  induction Γ.
  - left. econstructor.
  - destruct in_dec with (a := a) (l := Γ).
    + change (Classes.EqDec ident). exact _.
    + right. abstract (intros H; invs H; auto).
    + destruct IHΓ.
      * left. abstract (econstructor; eauto).
      * right. abstract (intros H; invs H; auto).
Defined.

Definition dupfree (Γ : list ident) :=
  if dupfree_dec_ident Γ then true else false.

Fixpoint sunny Γ (t : term) : bool :=
  match t with
  | tBox => true
  | tRel _ => true
  | tVar na => true
  | tEvar ev args => List.forallb (sunny Γ) args
  | tLambda (nNamed na) M => fresh na Γ && sunny (na :: Γ) M
  | tApp u v => sunny Γ u && sunny Γ v
  | tLetIn (nNamed na) b b' => fresh na Γ && sunny Γ b && sunny (na :: Γ) b'
  | tCase ind c brs =>
      forallb (fun br => let names := flat_map (fun x => match x with nNamed na => [na] | _ => [] end) br.1 in
                         forallb (fun x => match x with nNamed na => fresh na Γ | _ => false end) br.1
                         && dupfree names
                         && sunny (List.rev names ++ Γ) br.2) brs
      && sunny Γ c
  | tProj p c => sunny Γ c
  | tFix mfix idx =>
      forallb (fun x => match x.(dname) with nNamed na => fresh na Γ | _ => false end) mfix
      && let names := flat_map (fun d => match d.(dname) with nNamed i => [i] | _ => [] end) mfix in
         dupfree names &&
           forallb (test_def (sunny (names ++ Γ))) mfix
  | tConstruct _ _ args => forallb (sunny Γ) args
  | tPrim p => test_prim (sunny Γ) p
  | tLazy t => sunny Γ t
  | tForce t => sunny Γ t
  | _ => true
  end.

Inductive wf : value -> Type :=
| wf_vClos na b E : ~ In na (map fst E) -> sunny (na :: map fst E) b -> All (fun v => wf (snd v)) E -> wf (vClos na b E)
| wf_vConstruct ind c args : All wf args -> wf (vConstruct ind c args)
| wf_vRecClos vfix idx E :
  NoDup (map fst vfix) ->
  (forall nm, In nm (map fst vfix) -> ~ In nm (map fst E)) ->
  All (fun t => sunny (map fst vfix ++ map fst E) (snd t)) vfix ->
  All (fun v => wf (snd v)) E ->
  wf (vRecClos vfix idx E)
| wf_vPrim p : primProp wf p -> wf (vPrim p)
| wf_vLazy E t : sunny (map fst E) t -> All (fun v => wf (snd v)) E -> wf (vLazy t E).
Derive Signature for wf.

Lemma declared_constant_Forall P Σ c decl :
  Forall (P ∘ snd) Σ ->
  declared_constant Σ c decl ->
  P (ConstantDecl decl).
Proof.
  induction 1; unfold declared_constant; cbn.
  - congruence.
  - destruct x as [kn decl']; cbn. destruct (eqb_spec c kn).
    + inversion 1; subst. eauto.
    + eauto.
Qed.

Lemma declared_constant_All P Σ c decl :
  All (P ∘ snd) Σ ->
  declared_constant Σ c decl ->
  P (ConstantDecl decl).
Proof.
  induction 1; unfold declared_constant; cbn.
  - congruence.
  - destruct x as [kn decl']; cbn.
    destruct (c == kn) eqn:E.
    + inversion 1; subst. eauto.
    + eauto.
Qed.

Local Hint Constructors All : core.

Lemma wf_add_multiple Γ args nms :
  All (fun x => wf x.2) Γ ->
  #|args| = #|nms| ->
  All wf args ->
  All (λ x : ident × value, wf x.2) (add_multiple nms args Γ).
Proof.
  intros H1 H2 H3.
  induction H3 in nms, H1, H2 |- *; destruct nms; cbn in *; try lia.
  - eauto.
  - econstructor; eauto.
Qed.

Lemma fix_env_length vfix E :
  #| fix_env vfix E | = #| vfix |.
Proof.
  unfold fix_env. induction #|vfix|; cbn; eauto. f_equal. eauto.
Qed.

Lemma wf_fix_env mfix Γ' :
  NoDup (map fst mfix) ->
  (∀ nm : ident, In nm (map fst mfix) → ¬ In nm (map fst Γ')) ->
  All (λ t0 : ident × term, sunny (map fst mfix ++ map fst Γ') t0.2) mfix ->
  All (λ v : ident × value, wf v.2) Γ' ->
  All wf (fix_env mfix Γ').
Proof.
  intros H.
  unfold fix_env. induction #|mfix|; econstructor.
  - econstructor; eauto.
  - eapply IHn; eauto.
Qed.

Lemma fresh_subset Γ1 Γ2 i :
  fresh i Γ1 -> incl Γ2 Γ1 -> fresh i Γ2.
Proof.
  unfold fresh. repeat destruct in_dec; eauto; cbn.
  intros. firstorder.
Qed.

Local Hint Resolve fresh_subset : core.

Lemma sunny_subset Γ1 Γ2 t :
  sunny Γ1 t -> incl Γ2 Γ1 -> sunny Γ2 t.
Proof.
  intros H Hincl.
  induction t using EInduction.term_forall_list_ind in Γ1, Γ2, H, Hincl |- * ; cbn in *; eauto.
  - cbn in H. solve_all.
  - destruct n; eauto. cbn in *. rtoProp. split. 1: eapply fresh_subset; eauto.
    eapply IHt; eauto. intros ? []; cbn; eauto.
  - destruct n; eauto. cbn in *. rtoProp. repeat split; eauto.
    eapply IHt2; eauto. eapply incl_cons; cbn; eauto.
  - rtoProp; split; eauto.
  - solve_all.
  - rtoProp; split; solve_all; rtoProp; eauto; repeat split; solve_all.
    + destruct x0; eauto.
    + eapply a0; eauto.
      intros ? ?. rewrite -> in_app_iff in *.
      destruct H3; eauto.
  - rtoProp; repeat split; solve_all. destruct x; cbn in *.
    { destruct dname; cbn in *; eauto. }
    eapply a; eauto.
    intros ? ?. rewrite -> in_app_iff in *.
    destruct H; eauto.
  - rtoProp; solve_all.
Qed.

Derive NoConfusion for value.

Lemma eval_wf Σ E s v :
  Forall (fun d => match d.2 with ConstantDecl (Build_constant_body (Some d)) => sunny [] d | _ => true end) Σ ->
  All (fun x => wf (snd x)) E ->
  sunny (map fst E) s ->
  eval Σ E s v ->
  wf v.
Proof.
  intros HΣ HE Hsunny.
  intros Heval.
  revert HE Hsunny. pattern E, s, v, Heval.
  revert E s v Heval.
  eapply eval_ind; intros; eauto; cbn in *; rtoProp; eauto using Forall.
  - induction HE.
    + cbn in *. congruence.
    + unfold lookup in e. cbn in e. destruct x.
      destruct eqb eqn:E.
      * invs e. cbn in *; eauto.
      * eapply IHHE. exact e.
  - let X := match reverse goal with H : All _ _ -> _ -> _ |- _ => H end in
    do 2 forward X; eauto; inv X.
    let X1 := multimatch goal with H : _ |- _ => H end in
    now eapply X1; eauto; econstructor; cbn; eauto.
  - econstructor; eauto. unfold fresh in H. destruct in_dec; cbn in *; congruence.
  - let X0 := multimatch goal with H : _ |- _ => H end in
    now eapply X0; [ econstructor; cbn; eauto | eauto ].
  - solve_all.
    let X := match goal with H : wf (vConstruct _ _ _) |- _ => H end in
    inv X.
    let X0 := match goal with H : All _ _ -> _ -> _ |- _ => H end in
    eapply X0. eapply wf_add_multiple; eauto.
    len. eapply All2_length in f4. lia.
    let H := match goal with H : All (fun x => is_true (_ && _ && _)) _ |- _ => H end in
    eapply All_nth_error in H. 2: eauto. rtoProp.
    solve_all.
    rewrite map_fst_add_multiple. len.
    eapply All2_length in f4; lia.
    enough (nms = flat_map (λ x : name, match x with
                 | nAnon => []
                 | nNamed na => [na]
                 end) br.1) as -> by eauto.
    clear - f4. induction f4; cbn; f_equal; destruct r, x; cbn; congruence.
  - let X := match goal with H : All _ _ -> _ -> wf (vRecClos _ _ _) |- _ => H end in
    do 2 forward X; eauto; invs X.
    let X0 := match goal with H : All _ (add _ _ _) -> _ -> wf _ |- _ => H end in
    eapply X0.
    + econstructor; cbn; eauto.
      eapply wf_add_multiple; eauto.
      now rewrite List.length_rev length_map fix_env_length.
      eapply wf_fix_env; eauto.
    + let X2 := multimatch goal with H : All _ _ |- _ => H end in
      eapply All_nth_error in X2; eauto; cbn in X2; rtoProp;
      rewrite map_fst_add_multiple; first [ now rewrite List.length_rev length_map fix_env_length | eauto ].
      eapply sunny_subset. eauto.
      intros ?. cbn. rewrite !in_app_iff. now rewrite <- in_rev.
  - assert (map fst (MRList.map2 (λ (n : ident) (d0 : def term), (n, EAst.dbody d0)) nms mfix) = nms) as EE. {
    clear - f6. induction f6; cbn; f_equal; eauto. }
    econstructor.
    + solve_all. clear H0.
      rewrite EE. clear EE.
      induction f6; cbn.
      * econstructor.
      * invs n.
        econstructor; eauto.
    + rewrite EE. solve_all.
      assert ((flat_map
      (λ d : def term,
         match dname d with
         | nAnon => []
         | nNamed i => [i]
         end) mfix = nms)).
      { clear - f6. induction f6; cbn; eauto.
        destruct r as [[? []]].
        destruct x; cbn in *; subst. cbn. f_equal.
      }
      rewrite -> H2 in *. clear H2 EE.
      revert f6. generalize nms at 1.
      clear - H H1.
      intros nms_. induction 1.
      * eauto.
      * cbn in *. destruct H as [-> | ]; eauto.
        solve_all. rewrite <- b in a.
        unfold fresh in a. destruct in_dec; cbn in *; eauto.
   + solve_all. rewrite EE.
     assert ((flat_map
      (λ d : def term,
         match dname d with
         | nAnon => []
         | nNamed i => [i]
         end) mfix = nms)).
      { clear - f6. induction f6; cbn; eauto.
        destruct r as [[? []]].
        destruct x; cbn in *; subst. cbn. f_equal.
      }
      rewrite -> H in *. clear H EE.
      revert f6. generalize nms at 1 3.
      clear. intros nms_ f6.
      induction f6; cbn; econstructor; eauto.
      destruct r as [[? []]].
      destruct x; cbn in *; subst; eauto.
   + eauto.
  - let X := match goal with H : All _ _ -> _ -> wf _ |- _ => H end in
    eapply X; eauto. eapply declared_constant_Forall in isdecl.
    2: eapply Forall_impl. 2: eauto.
    2: { cbn. intros [] ?. cbn in *. let H := match goal with H : match _ with ConstantDecl _ => _ | _ => _ end |- _ => H end in exact H. }
    cbn in *. destruct decl; cbn in *.
    subst. eauto.
  - solve_all. econstructor.
    clear - a IHa Hsunny HE.
    induction a; econstructor; cbn in *; eauto.
    + eapply IHa; eauto. now invs Hsunny.
    + eapply IHa0. eapply IHa. now invs Hsunny.
  - cbn. econstructor. econstructor.
  - econstructor. solve_all. depelim evih; depelim Hsunny; try subst a0 a'; cbn; constructor; cbn in *; intuition solve_all.
    eapply All2_over_undep in a. solve_all.
  - econstructor; eauto.
  - eapply X in HE; eauto. depelim HE. eapply X0; eauto.
Qed.

Lemma eval_construct_All2 Σ E ind c args vs mdecl idecl cdecl :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  #|args| <= cstr_nargs cdecl ->
  All2 (eval Σ E) args vs -> eval Σ E (tConstruct ind c args) (vConstruct ind c vs).
Proof.
  intros Hind.
  revert vs. induction args using rev_ind; intros vs Hlen Hvs.
  - invs Hvs. now econstructor.
  - eapply All2_app_inv_l in Hvs as (vs' & r2 & -> & H1 & H2).
    invs H2. invs X. revert Hlen; len; intros Hlen. econstructor.
    + eauto.
    + rewrite length_app; cbn. lia.
    + eapply All2_All2_Set, All2_app. eapply H1; eauto. econstructor; eauto.
Qed.

Lemma lookup_in_env Σ Σ' ind i :
  All2 (fun d d' => d.1 = d'.1 × match d.2 with ConstantDecl (Build_constant_body (Some body)) =>
    ∑ body', d'.2 = ConstantDecl (Build_constant_body (Some body')) × [] ;;; [] ⊩ body' ~ body
  | decl => d'.2 = decl
  end) Σ Σ' ->
  lookup_constructor Σ ind i = lookup_constructor Σ' ind i.
Proof.
  induction 1; cbn.
  - reflexivity.
  - destruct r as [-> ].
    destruct (eqb_spec (inductive_mind ind) y.1).
    + destruct x.2.
      * destruct c, cst_body.
        -- now destruct y0 as (? & -> & ?).
        -- now rewrite y0.
      * now rewrite y0.
    + eapply IHX.
Qed.

Lemma constructor_isprop_pars_decl_in_env Σ Σ' ind c :
  All2 (fun d d' => d.1 = d'.1 × match d.2 with ConstantDecl (Build_constant_body (Some body)) =>
    ∑ body', d'.2 = ConstantDecl (Build_constant_body (Some body')) × [] ;;; [] ⊩ body' ~ body
  | decl => d'.2 = decl
  end) Σ Σ' ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl Σ' ind c.
Proof.
  intros H.
  unfold constructor_isprop_pars_decl. erewrite lookup_in_env; eauto.
Qed.

(*
Lemma represents_value_fix_env vfix mfix E :
  All2 (λ (v : ident × term) (d : def term), map fst vfix;;; E ⊩ v.2 ~ dbody d) vfix mfix ->
  All2 represents_value (fix_env vfix E) (fix_subst mfix).
Proof.
Qed.
 *)

(*)

Lemma represents_add_fresh nms Γ E vs s t :
  Γ ;;; E ⊩ s ~ t ->
  sunny nms s ->
  Γ ;;; (add_multiple nms vs E) ⊩ s ~ t.
Proof.
  pattern Γ, E, s, t.
  revert Γ E s t.
  refine (@represents_ind _ (fun _ _ _ => True) _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: intros; cbn in *; rtoProp; eauto.
  - econstructor; eauto.
  - econstructor; eauto. eapply H; eauto.
    eapply sunny_subset; eauto. firstorder.
  - econstructor; eauto. eapply H0; eauto.
    eapply sunny_subset; eauto. firstorder.
  - econstructor; eauto. solve_all.
    induction a; invs IH; invs H; econstructor; eauto.
  - econstructor; eauto. solve_all.
    induction a; invs IH; invs H0; econstructor.
    + destruct r0 as (nms_ & ? & ? & ?).
      exists nms_. split. eauto. split; eauto.
      eapply H. rtoProp. eapply sunny_subset; eauto.
      eapply incl_appr, incl_refl.
    + eapply IHa; eauto. invs Heq; eauto.
  - econstructor; eauto. solve_all. clear - IH H1 a0.
    induction a0. econstructor. invs IH; invs H1; econstructor.
    + eapply H. destruct H2 as (? & ? & ?).
      destruct x; cbn in *.
      eapply sunny_subset; eauto.
      eapply incl_appr, incl_refl.
    + eapply IHa0; eauto. solve_all.
      destruct x0; cbn in *.
      eapply sunny_subset; eauto.
      rewrite <- app_assoc.
      eapply incl_appr, incl_refl.
Qed.

*)

Lemma NoDup_In_1 {A} (l1 l2 : list A) a :
    NoDup (l1 ++ l2) -> In a l1 -> ~ In a l2.
Proof.
  induction l1; cbn.
  - eauto.
  - inversion 1; subst. intros [-> | ?]; eauto.
    rewrite in_app_iff in H2; eauto.
Qed.

Lemma eval_to_eval_named (efl : EEnvFlags) (Σ Σ' : global_context) E s t u :
  ~~ has_cstr_params ->
  has_tApp ->
  ~~ has_tBox -> ~~ has_tVar -> ~~ has_tEvar -> ~~ has_tProj -> ~~ has_tCoFix ->
  wf_glob Σ ->
  Forall (fun d => match d.2 with ConstantDecl (Build_constant_body (Some d)) => sunny [] d | _ => true end) Σ' ->
  All2 (fun d d' => d.1 = d'.1 × match d.2 with ConstantDecl (Build_constant_body (Some body)) =>
    ∑ body', d'.2 = ConstantDecl (Build_constant_body (Some body')) × [] ;;; [] ⊩ body' ~ body
  | decl => d'.2 = decl
  end) Σ Σ' ->
  All (fun x => wf (snd x)) E ->
  sunny (map fst E) u ->
  EWcbvEval.eval Σ s t ->
  [] ;;; E ⊩ u ~ s ->
  wellformed Σ 0 s ->
  ∑ v, ⊩ v ~ t × eval Σ' E u v.
Proof.
  intros haspars hasapp nbox nvar nevar nproj ncof HwfΣ HΣ HΣind HE Hsunny Heval Hrep Hwell.
  revert u E Hrep Hsunny HE.
  pattern s, t.
  revert Heval.
  eapply eval_preserve_mkApps_ind with (Σ := Σ); cbn -[substl] in *; rtoProp.
  1: reflexivity.
  1: eapply Qpreserves_wellformed with (efl := efl).
  1: eauto.
  1:{ intros. cbn in *. eapply eval_wellformed; cbn; eauto. }
  1: eauto.
  1: eauto. 1:auto.
  all: try congruence.
  all: intros; rtoProp.
  all: repeat match reverse goal with  [H : MRProd.and3 _ _ _ |- _] => destruct H end.
  - cbn in i0 => //. now rewrite i0 in nbox.
  - invs Hrep.
    + invs H3.
    + cbn in Hsunny. rtoProp.
      edestruct s0 as (v1 & Hv1 & Hv2). 3: eauto. eauto. eauto.
      invs Hv1.
      edestruct s1 as (v2 & Hv1_ & Hv2_). 3: eauto. eauto. eauto.
      eapply eval_wf in Hv2 as Hwf; eauto. invs Hwf; eauto.
      edestruct s2 as (v3 & Hv1__ & Hv2__).
      1: eapply represents_subst; eauto.
      2:{ econstructor. eapply eval_wf in Hv2_; eauto. eauto. }
      { eauto. }
      eexists; split; eauto. econstructor; eauto.
  - invs Hrep.
    + invs H3.
    + cbn in Hsunny. rtoProp.
      edestruct s0 as (v1 & Hv1 & Hv2). 3: eauto. eauto. eauto.
      edestruct s1 as (v2 & Hv1_ & Hv2_).
      1: eapply represents_subst; eauto.
      3:{ econstructor. cbn in *. eapply eval_wf in Hv2; eauto. eauto. }
      2:{ eapply eval_wf in Hv2; eauto. }
      1:{ unfold fresh in *. destruct in_dec; cbn in *; congruence. }
      eexists; split; eauto. econstructor; eauto.
  - assert (pars = 0) as ->. {
      unfold constructor_isprop_pars_decl in *.
      destruct lookup_constructor as [[[[] [? ?]] ?] | ] eqn:EE; cbn in *; try congruence.
      invs H0.
      destruct lookup_env eqn:EEE; try congruence.
      eapply lookup_env_wellformed in EEE; eauto.
      destruct g; cbn in *; try congruence.
      red in EEE. unfold wf_minductive in EEE.
      rtoProp. eapply andb_true_iff in EEE as [Hpars _].
      cbn in Hpars. destruct has_cstr_params => //. eapply Nat.eqb_eq in Hpars.
      destruct nth_error eqn:EEE; cbn in *; try congruence.
      destruct (nth_error (EAst.ind_ctors o) c) eqn:EEEE; cbn in *; try congruence.
      now invs EE.
  }
   invs Hrep.
    + invs H7.
    + cbn in Hsunny. rtoProp.
      edestruct s0 as (v & Hv1 & Hv2). 3,1,2: eauto.
      eapply All2_Set_All2 in H14. eapply All2_nth_error_Some_right in H14 as He2. 2: eauto.
      destruct He2 as (br' & Hnth & nms & Hbrs & Hbr & Hnodup). invs Hv1.
      edestruct s1 as (v2 & Hv1_ & Hv2_).
      1: { eapply forallb_nth_error in H6. setoid_rewrite Hnth in H6. cbn in H6. rtoProp.
           assert (nms = flat_map (λ x : name, match x with
               | nAnon => []
               | nNamed na => [na]
               end) br'.1) as Heqnms. { clear - Hbrs. induction Hbrs; cbn; now subst. }
           unfold iota_red. eapply represents_substl. 5: eauto.
           { rewrite Heqnms flat_map_concat_map.
             intros ? (? & ([] & <- & ?) % in_map_iff & Hd) % in_concat; cbn in *; eauto.
            destruct Hd; subst; eauto.
            eapply forallb_forall in H6; eauto.
            cbn in H6. unfold fresh in H6. destruct in_dec; cbn in *; congruence. }
            { subst. unfold dupfree in H9. destruct dupfree_dec_ident; cbn in *; congruence. }
            2: eapply All2_rev. len.
            2:{ rewrite skipn_O. eauto. }
            eapply All2_Set_All2, All2_nth_error in H13; eauto.
            eapply All2_Set_All2, All2_length in H10; eauto.
            eapply All2_Set_All2, All2_length in Hbrs; eauto.
            rewrite -> !length_skipn in *. lia.
      }
      3: eexists; split; [ eauto | econstructor; eauto].
      * rewrite map_fst_add_multiple.
        -- len.
           eapply All2_Set_All2, All2_nth_error in H13; eauto.
           eapply All2_Set_All2, All2_length in H10; eauto.
           eapply All2_Set_All2, All2_length in Hbrs; eauto.
           rewrite -> !length_skipn in *. lia.
        -- eapply forallb_nth_error in H6. setoid_rewrite Hnth in H6. cbn in H6. rtoProp.
           enough (nms = flat_map (λ x : name, match x with
           | nAnon => []
           | nNamed na => [na]
           end) br'.1) as -> by eauto.
           clear - Hbrs. induction Hbrs; cbn; now subst.
      * rewrite rev_involutive.
        eapply eval_wf in Hv2; eauto.
        invs Hv2. eapply wf_add_multiple. eauto.
        -- len. eapply All2_Set_All2, All2_nth_error in H13; eauto.
           eapply All2_Set_All2, All2_length in H10; eauto.
           eapply All2_Set_All2, All2_length in Hbrs; eauto.
           rewrite -> !length_skipn in *. lia.
        -- eauto.
      * erewrite <- constructor_isprop_pars_decl_in_env. eauto. solve_all.
      * eapply All2_Set_All2, All2_length in H10. lia.
      * eapply All2_Set_All2, All2_length in H10.
        eapply All2_Set_All2, All2_nth_error in H13; eauto.
        eapply All2_Set_All2, All2_length in Hbrs; eauto.
        rewrite -> !length_skipn in *. lia.
      * solve_all.
      * now rewrite rev_involutive in Hv2_.
  - eapply X; eauto. (* artifact of the induction being weird and having a trivial assumption to not mess up proof script. FIXME! *)
  - invs Hrep.
    + let H5 := match goal with H : ⊩ _ ~ tApp _ _ |- _ => H end in
      invs H5.
    + cbn -[substl] in *. rtoProp.
      edestruct s0 as (v & IH1 & IH2). 3, 1, 2: eauto.
      invs IH1.
      edestruct s1 as (v' & IH1' & IH2'); eauto.

      destruct d; cbn -[substl] in *; subst.
      eapply All2_Set_All2 in H14.
      eapply All2_nth_error_Some_r in H14 as Hnth; eauto.
      destruct Hnth as ([na' b] & Hb1 & [Hlam Hb2]); cbn -[substl] in *.
      destruct b; invs Hlam.

      invs Hb2.
      eapply eval_wf in IH2 as Hwf; eauto.
      invs Hwf.

      let H12 := match goal with H : NoDup (map fst vfix) |- _ => H end in
      let H16 := match goal with H : forall nm, In nm (map fst vfix) -> ~In nm _ |- _ => H end in
      let X := match goal with H : All (fun t => is_true (sunny _ _)) vfix |- _ => H end in
      let X0 := match goal with H : All (fun v => wf _) _ |- _ => H end in
      rename H12 into dupfree_vfix, H16 into distinct_vfix_E0, X into sunny_in_vfix, X0 into wf_E0.

      edestruct s2 as (v'' & IH1'' & IH2'').

      eapply represents_substl_rev with (vs := _ :: fix_env vfix E0) (nms := na1 :: List.rev (map fst vfix)); eauto. (* having represents_substl_rev with nms ++ Gamma created an order problem here. changing it there fixes the problem here. but is this correct? *)
      8:{ eexists. split. eauto.
          eapply eval_fix_unfold; eauto.
          solve_all.
          eapply eval_wf in IH2; eauto.
          invs IH2.
          eapply All_nth_error in Hb1. 2: exact X. cbn in *.
          rtoProp.
          intros Hna.
          unfold fresh in H2.
          destruct in_dec; cbn in *; try congruence.
          eapply n. rewrite in_app_iff. eauto.
      }
      { intros ? [-> | ?].
        - eapply All_nth_error in sunny_in_vfix; eauto.
          cbn in sunny_in_vfix. rtoProp. unfold fresh in *.
          destruct in_dec; cbn in *; eauto.
          rewrite in_app_iff in n. eauto.
        - eapply distinct_vfix_E0; eauto. now eapply in_rev.
      }
      {
        econstructor.
        - eapply All_nth_error in sunny_in_vfix; eauto.
          cbn in *. rtoProp. unfold fresh in *.
          destruct in_dec; cbn in *; eauto.
          rewrite in_app_iff in n. rewrite <- in_rev. eauto.
        - eapply NoDup_rev. eauto.
      }
      { cbn. now rewrite List.length_rev length_map fix_env_length. }
      econstructor; eauto.
      { clear - H14. unfold fix_env, fix_subst.
        eapply All2_length in H14 as Hlen. rewrite Hlen. clear Hlen.
        generalize #|mfix|.
        induction n; econstructor; eauto.
      }
      now rewrite app_nil_r.
      { cbn. rewrite map_fst_add_multiple.
        now rewrite List.length_rev length_map fix_env_length.
        eapply All_nth_error in sunny_in_vfix; eauto. cbn in sunny_in_vfix.
        rtoProp.
        eapply sunny_subset; eauto.
        intros ?; cbn in *. rewrite !in_app_iff. rewrite <- !in_rev. eauto.
      }
      { econstructor.
        - cbn. eapply eval_wf. 4: eauto. all:eauto.
        - eapply wf_add_multiple.
          + eauto.
          + now rewrite List.length_rev length_map fix_env_length.
          + eapply eval_wf in IH2; eauto.
            eapply wf_fix_env; eauto.
      }
      (* besides the result, we believe that the exposition has several valuable contributions:
         - it discusses proofs techniques to get similar results
         - it gives an exposition how to extract from type theory to (cbv) programming languages in general, including the invariants
         - many of these things are known, but not in central places

      *)
  - invs Hrep.
    + invs H3.
    + cbn in *. rtoProp.
      edestruct s0 as (v1 & Hv1 & Hv2); eauto.
      invs Hv1; destruct args using rev_ind; cbn in *; try congruence.
      all: match goal with [H : _ = mkApps _ _ |- _ ] => now rewrite mkApps_app in H end.
  - now rewrite H in nproj.
  - invs Hrep.
    + invs H3.
    + assert (∑ decl' body', declared_constant Σ' c decl' × sunny [] body' × cst_body decl' = Some body' × [];;; [] ⊩ body' ~ body) as (decl' & Hdecl & body' & Hsunny' & e' & H').
      { rename H into isdecl. rename H0 into e. clear - HΣ HΣind isdecl e. unfold declared_constant in isdecl. solve_all.
        induction HΣind.
        - cbn in isdecl. congruence.
        - cbn in isdecl. destruct (c == x.1) eqn:E.
          + invs isdecl. eapply eqb_eq in E. subst.
            destruct r as ((H1 & H2) & H3). rewrite H0 in H2.
            destruct decl; cbn in *. subst. destruct H2 as (body' & H4 & H5).
            rewrite H4 in H3.
            eexists (Build_constant_body _). eexists.  repeat split. 2: exact H3.
            2: eauto. unfold declared_constant. cbn.
            destruct (eqb_spec x.1 y.1); congruence.
          + edestruct IHHΣind as (decl' & body' & H1 & H2 & H3 & H4); eauto.
            exists decl', body'. repeat split; eauto.
            unfold declared_constant. cbn.
            destruct (eqb_spec c y.1); try congruence.
            subst. destruct r as ([Eq ?] & ?).
            destruct (eqb_spec y.1 x.1); try congruence.
      }
      edestruct s0 as (v & Hv1 & Hv2). 1: eauto. eauto. econstructor.
      eexists. split. eauto. econstructor; eauto.
  - now rewrite H in nproj.
  - invs Hrep.
    + invs H2.
    + cbn in Hsunny. rtoProp.
      eapply eval_to_value in ev as Hval. invs Hval.
      * depelim X.
        ** destruct t1; cbn in *; try congruence. rtoProp. now rewrite H3 in ncof.
        ** now rewrite /= in H.
      * invs H4; cbn in *; eauto.
      * invs H1; cbn in *; eauto; try congruence.
        rtoProp. edestruct s0 as (v & Hv1 & Hv2). 3: eauto. eauto. eauto.
        invs Hv1; destruct args using rev_ind; cbn in *; try congruence.
        all: match goal with [H : _ = mkApps _ _ |- _ ] => now rewrite mkApps_app in H end.
  - invs Hrep.
    + let H2 := match goal with H : ⊩ _ ~ tConstruct _ _ _ |- _ => H end in
      invs H2. eexists. split. econstructor.  instantiate (1 := vs).
      * eapply All2_All2_Set.
        let H5 := multimatch goal with H : _ |- _ => H end in
        eapply All2_Set_All2 in H5.
        let X := match goal with H : All2 (EWcbvEval.eval _) _ _ |- _ => H end in
        eapply All2_All2_mix in X. 2: let X0 := match goal with H : All2 (fun _ _ => MRProd.and3 _ _ _) _ _ |- _ => H end in exact X0.
        solve_all. eapply All2_trans'. 2: eauto. 2: match goal with H : context[EWcbvEval.eval] |- _ => exact H end.
        intros x y z [? [? ?]]. rdest; destruct_head' MRProd.and3. eapply eval_represents_value; tea.
      * econstructor. eauto.
    + cbn in Hsunny.
      solve_all.
      let H5' := multimatch goal with H : _ |- _ => H end in
      rename H5' into H5.
      eapply All2_Set_All2 in H5.
      eapply All2_All_mix_left in H5; tea.
      toAll.
       cbn in *. match goal with H : All2 _ ?x ?y, H' : All2 _ ?y ?z |- _ => eapply All2_trans' in H'; [ | | exact H ]; cbv beta end.
       2:{ intros x y z ?; destruct_head'_prod; destruct_head' MRProd.and3.
           match goal with
           | [ H : context[y], H' : _ |- _ ] => eapply H' in H; [ | now eauto .. ]
           end.
           clear dependent y.
           repeat match goal with H : ?x, H' : ?x |- _ => clear H' end.
           repeat match goal with
                  | [ H : ?A, H' : ?B |- _ ]
                    => lazymatch A with context[x] => idtac | context[z] => idtac end;
                       lazymatch B with context[x] => idtac | context[z] => idtac end;
                       pose proof (pair H H'); clear H H'
                  end.
           generalize dependent x; intros x H'; exact H'. }
       assert ({ vs & All3 (fun v x z => ⊩ v ~ z × eval Σ' E x v) vs args0 args'}) as [vs Hvs]. { let X := match goal with H : All2 _ ?x ?y |- context[All3 _ _ ?x ?y] => H end in
         clear - X; induction X. eexists; econstructor. repeat (destruct_head'_sigT; destruct_head'_prod).
         eexists (_ :: _). econstructor; eauto.
       }
       eexists. split. econstructor.
       { instantiate (1 := vs). clear - Hvs; induction Hvs; econstructor; eauto. eapply r. }
       econstructor. erewrite <- lookup_in_env. 2: solve_all.
       eapply H. eapply All2_length in H5.
       destruct lookup_env as [ [] | ] eqn:Elo; try congruence.
       epose proof (@lookup_env_wellformed _ Σ (inductive_mind ind) _ HwfΣ Elo).
       cbn in H1. unfold wf_minductive in H1. rtoProp. cbn in *.
       destruct has_cstr_params => //. eapply Nat.eqb_eq in H1. unfold cstr_arity in *.
       destruct nth_error eqn:E1; cbn in *; try congruence.
       destruct (nth_error (ind_ctors o) i) eqn:E2; cbn in *; try congruence.
       unfold cstr_arity in *.  invs H. lia.
       clear - Hvs; induction Hvs; econstructor; eauto. eapply r.
  - invs Hrep.
    * exists v. depelim X; split; eauto; try now econstructor.
      eapply All2_over_undep in a. eapply All2_Set_All2 in ev.
      (* eapply eval_to_values in ev. solve_all. *)
      (* eapply eval_to_value in ed. subst a1 a'. *)
      depelim H0. depelim o. constructor. constructor. eapply All2_Set_All2 in a2. subst a1 a'.
      cbn in Hsunny. destruct a0. eapply eval_represents_value; tea.
      eapply All2_Set_All2 in a2. solve_all.
      eapply All2_trans' in a; tea. eapply All2_All2_Set; tea.
      { intros x y z [? []]. eapply eval_represents_value; tea. }
    * depelim X; depelim H3; try solve [eexists; split; repeat constructor].
      eapply All2_over_undep in a. eapply All2_Set_All2 in a2, ev. solve_all.
      destruct a0. specialize (s0 _ _ r). cbn in Hsunny. move/andP: Hsunny => [sd sv].
      solve_all. destruct H as [vdef []].
      eapply (All2_trans' _ _ (fun x z => ∑ v, ⊩ v ~ z × eval Σ' E x v)) in a; tea.
      2:{ intros x y z. cbn. intros [[] [ev []]].
          now specialize (s0 _ _ r1 i1 HE). }
      assert ({ vs & All3 (fun v x z => ⊩ v ~ z × eval Σ' E x v) vs v0 v'}) as [vs Hvs].
      { cbn in a. let X := match goal with H : All2 _ ?x ?y |- context[All3 _ _ ?x ?y] => H end in
          clear - X; induction X. eexists; econstructor. repeat (destruct_head'_sigT; destruct_head'_prod).
          eexists (_ :: _). econstructor; eauto.
        }
      exists (vPrim (prim_array {| array_default := vdef; array_value := vs |})).
      subst a1 a' a3 a'0; cbn in *.
      split; constructor.
      + constructor; eauto. eapply All2_All2_Set.
        { clear -Hvs; induction Hvs; constructor; intuition eauto. }
      + constructor; eauto. eapply All2_All2_Set.
        { clear -Hvs; induction Hvs; constructor; intuition eauto. }
  - invs Hrep; cbn in *; rtoProp. depelim H2.
    apply s0 in H5 as [v' [reprev t1v]]; eauto.
    depelim reprev.
    eapply eval_wf in HΣ; tea. depelim HΣ.
    eapply s1 in r as [v2 [reprv2 evv2]]; eauto.
    exists v2. split => //. econstructor; eauto.
  - invs Hrep; cbn in *; try congruence; rtoProp.
    + econstructor. split; eauto. econstructor. eauto.
    + econstructor. split; eauto. econstructor.
    + destruct args'; congruence.
    + solve_all. eexists. split. 2: econstructor; eauto. 4: solve_all.
      econstructor. 3:{ eapply All2_Set_All2 in H3. solve_all. }
      3:{ eapply All2_Set_All2 in H3. solve_all. }
      2:{ unfold wf_fix in H8. rtoProp. eapply Nat.ltb_lt in H5. eapply All2_Set_All2, All2_length in H4. lia. }
      eapply All2_Set_All2 in H3, H4. eapply All2_All2_Set. solve_all.
      assert (map fst (MRList.map2 (λ (n : ident) (d0 : def term), (n, dbody d0)) nms mfix) = nms) as ->. {
        clear - H3. induction H3; cbn; f_equal; eauto. }
      eapply All2_map2_left. eapply All2_swap; eauto. eauto.
      symmetry. eapply All2_length; eauto.
      intros.
      cbn in *. destruct H5 as (([? []] & ?) & ?).
      rewrite app_nil_r in r. all: eauto.
    + exists (vLazy t1 E). now split; econstructor.
  Unshelve. all: repeat econstructor.
Qed.

Lemma concat_sing {X} l :
  List.concat (map (fun x :X  => [x]) l) = l.
Proof.
  induction l; cbn in *; try congruence.
Qed.

Lemma sunny_annotate Γ s :
  sunny Γ (annotate Γ s).
Proof.
  induction s in Γ |- * using EInduction.term_forall_list_ind; cbn; eauto; rtoProp.
  - destruct nth_error; cbn; eauto.
  - solve_all.
  - split; eauto. destruct n; eauto.
    unfold fresh. destruct in_dec; cbn; eauto.
    eapply gen_fresh_fresh in i; eauto.
    destruct in_dec; cbn; eauto.
    unfold fresh. destruct in_dec; cbn; eauto.
    eapply gen_fresh_fresh in i1; eauto.
    unfold fresh. destruct in_dec; cbn; eauto. exfalso; eauto.
  - split; eauto. destruct n; eauto.
    unfold fresh. destruct in_dec; cbn; eauto.
    eapply gen_fresh_fresh in i; eauto.
    destruct in_dec; cbn; eauto.
    unfold fresh. destruct in_dec; cbn; eauto.
    eapply gen_fresh_fresh in i1; eauto.
    unfold fresh. destruct in_dec; cbn; eauto. exfalso; eauto.
  - split; eauto.
  - solve_all.
  - split; eauto. solve_all. rtoProp. repeat split; eauto.
    + solve_all. eapply In_All. intros.
      unfold fresh. destruct in_dec; cbn; eauto.
      exfalso. eapply NoDup_gen_many_fresh; eauto.
    + unfold dupfree. destruct dupfree_dec_ident; eauto.
      exfalso. eapply n.
      rewrite flat_map_concat_map. rewrite map_map.
      rewrite concat_sing.
      eapply NoDup_gen_many_fresh; eauto.
    + rewrite flat_map_concat_map map_map concat_sing.
      eapply sunny_subset. eapply H.
      intros ? ? %in_app_iff. eapply in_app_iff. rewrite <- in_rev in H0.
      eauto.
  - repeat split; eauto.
    1:{ unfold map_def_name.  generalize (annotate (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
        cbn. intros. solve_all.
        clear. induction m in Γ |- *.
        - cbn. econstructor.
        - cbn. destruct a; cbn. destruct dname; cbn.
          + econstructor; cbn.
            unfold fresh. destruct in_dec; eauto; cbn. exfalso.
            eapply gen_fresh_fresh; eauto.
            specialize (IHm (gen_fresh "wildcard" Γ :: Γ)).
            solve_all. destruct x, dname; cbn in *; try congruence.
            unfold fresh in *. repeat (destruct in_dec; cbn in *; try congruence).
            exfalso. eapply n. eauto.
          + econstructor; cbn.
            { destruct in_dec; cbn.
              + unfold fresh. destruct in_dec; eauto; cbn. exfalso.
                eapply gen_fresh_fresh; eauto.
              + unfold fresh. destruct in_dec; eauto; cbn. exfalso. eauto. }
            specialize (IHm ((if is_left (in_dec (ReflectEq_EqDec IdentOT.reflect_eq_string) i Γ) then gen_fresh i Γ else i) :: Γ)).
            solve_all. destruct x, dname; cbn in *; try congruence.
            destruct in_dec; cbn in *.
            * unfold fresh in *.
              repeat (destruct in_dec; cbn in *; try congruence).
              exfalso. eapply n. eauto.
            * unfold fresh in *.
              repeat (destruct in_dec; cbn in *; try congruence).
              exfalso. eapply n0. eauto.
    }
    { unfold map_def_name. generalize (annotate (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
      intros t0.
      assert ((flat_map (λ d : def term, match dname d with
      | nAnon => []
      | nNamed i => [i]
      end)
(map2 (λ (d : def term) (na : ident), {| dname := nNamed na; dbody := t0 (dbody d); rarg := rarg d |}) m (gen_many_fresh Γ (map dname m)))) = (gen_many_fresh Γ (map dname m))) as ->.
      { pose proof (gen_many_fresh_length Γ (map dname m)). rewrite length_map in H. revert H.
        generalize (gen_many_fresh Γ (map dname m)). clear. induction m; destruct l; cbn; try congruence.
        intros. f_equal. eapply IHm. lia. }

      unfold dupfree. intros. destruct dupfree_dec_ident; cbn; eauto.
      exfalso. apply n0.
      eapply NoDup_gen_many_fresh.
    }
    {
      unfold map_def_name.
      assert ((flat_map (λ d : def term, match dname d with
      | nAnon => []
      | nNamed i => [i]
      end)
(map2 (λ (d : def term) (na : ident), {| dname := nNamed na; dbody := annotate (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ) (dbody d); rarg := rarg d |}) m (gen_many_fresh Γ (map dname m)))) = (gen_many_fresh Γ (map dname m))) as ->.
      { generalize (annotate (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)).
         pose proof (gen_many_fresh_length Γ (map dname m)). rewrite length_map in H. revert H.
        generalize (gen_many_fresh Γ (map dname m)). clear. induction m; destruct l; cbn; try congruence.
        intros. f_equal. eapply IHm. lia. }

      solve_all.
      eapply (All_impl(P := (λ x : def term, test_def (sunny (List.rev (gen_many_fresh Γ (map dname m)) ++ Γ)) x))).
      2:{ intros x H. unfold test_def. eapply sunny_subset. eassumption.
          intros ? ? % in_app_iff. eapply in_app_iff. rewrite <- in_rev. eauto. }

      generalize (List.rev (gen_many_fresh Γ (map dname m))).
      pose proof (gen_many_fresh_length Γ (map dname m)). rewrite length_map in H. revert H.
      generalize (gen_many_fresh Γ (map dname m)). clear - X. induction X.
      + intros l. destruct l; cbn in *; try congruence. econstructor.
      + intros []; cbn in *; try congruence. intros. econstructor; eauto.
    }
  - solve_all.
Qed.

Lemma eval_to_eval_named_full (efl : EEnvFlags) (Σ Σ' : global_context) s t :
  ~~ has_cstr_params ->
  has_tApp ->
  ~~ has_tBox -> ~~ has_tVar -> ~~ has_tEvar -> ~~ has_tProj -> ~~ has_tCoFix ->
  wf_glob Σ ->
  Forall (fun d => match d.2 with ConstantDecl (Build_constant_body (Some d)) => sunny [] d | _ => true end) Σ' ->
  All2 (fun d d' => d.1 = d'.1 × match d.2 with ConstantDecl (Build_constant_body (Some body)) =>
    ∑ body', d'.2 = ConstantDecl (Build_constant_body (Some body')) × [] ;;; [] ⊩ body' ~ body
  | decl => d'.2 = decl
  end) Σ Σ' ->
  EWcbvEval.eval Σ s t ->
  wellformed Σ 0 s ->
  ∑ v, ⊩ v ~ t × eval Σ' [] (annotate [] s) v.
Proof.
  intros. eapply eval_to_eval_named; eauto.
  eapply sunny_annotate.
  eapply nclosed_represents; eauto.
Qed.
