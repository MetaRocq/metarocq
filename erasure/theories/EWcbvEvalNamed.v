(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils BasicAst.
From MetaCoq.PCUIC Require PCUICWcbvEval.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv
  EWellformed EWcbvEval.

From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Set Default Proof Using "Type*".

(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)


Local Ltac inv H := inversion H; subst.

(** ** Big step *named* version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Inductive value : Set :=
| vBox
| vClos (na : ident) (b : term) (env : list (ident * value))
| vConstruct (ind : inductive) (c : nat) (args : list (value))
| vRecClos (b : list (ident * term)) (idx : nat) (env : list (ident * value)).

Definition environment := list (ident * value).
Definition add : ident -> value -> environment -> environment := fun (x : ident) (v : value) env =>
                                                                (x, v) :: env.
Fixpoint add_multiple (xs : list ident) (vs : list value) (env : environment) : environment := 
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

Section Wcbv.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval (Γ : environment) : term -> value -> Type :=
  (** Reductions *)
  | eval_var na v :
    lookup Γ na = Some v ->
    eval Γ (tVar na) v

  | eval_box a t t' :
    eval Γ a vBox ->
    eval Γ t t' ->
    eval Γ (tApp a t) vBox

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
  | eval_iota_block ind pars cdecl discr c args brs br res nms :
    eval Γ discr (vConstruct ind c args) ->
    constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
    nth_error brs c = Some br ->
    #|args| = pars + cdecl.(cstr_nargs) ->
            #|skipn pars args| = #|br.1| ->
                                         Forall2 (fun x y => x = nNamed y) br.1 nms ->
                                         eval (add_multiple (List.rev nms) (skipn pars args) Γ) br.2 res ->
                                         eval Γ (tCase (ind, pars) discr brs) res

  (** Fix unfolding, without guard *)
  | eval_fix_unfold f mfix idx a av fn res Γ' Γ'' na na' b :
    eval Γ f (vRecClos mfix idx Γ') ->
    eval Γ a av ->
    eval (add_multiple (map fst mfix) (fix_env mfix Γ') Γ') fn (vClos na' b Γ'') ->
    eval (add na av Γ'') b res ->
    eval Γ (tApp f a) res

  | eval_fix mfix idx nms : 
    Forall2 (fun d n => nNamed n = d.(dname)) mfix nms ->
    eval Γ (tFix mfix idx) (vRecClos (map2 (fun n d => (n, d.(dbody))) nms mfix) idx Γ)

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
    decl.(cst_body) = Some body ->
    eval Γ body res ->
    eval Γ (tConst c) res

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct_block ind c mdecl idecl cdecl args args' a a' : 
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    #|args| < cstr_arity mdecl cdecl ->
            eval Γ (tConstruct ind c args) (vConstruct ind c args') ->
            eval Γ a a' ->
            eval Γ (tConstruct ind c (args ++ [a])) (vConstruct ind c (args' ++ [a']))
  
  | eval_construct_block_empty ind c mdecl idecl cdecl :
     lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
     eval Γ (tConstruct ind c []) (vConstruct ind c []).

End Wcbv.

Definition ident_of_name (na : name) : ident :=
  match na with nAnon => "" | nNamed na => na end.

Reserved Notation "Γ ;;; E ⊩ s ~ t" (at level 50, E, s, t at next level).

Unset Elimination Schemes.

Inductive represents : list ident -> environment -> term -> term -> Set :=
| represents_tBox Γ E : Γ ;;; E ⊩ tBox ~ tBox
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
  (All2_Set (fun b b' => {nms & (All2_Set (fun n n' => n = nNamed n') b.1 nms × ((nms ++ Γ) ;;; E ⊩ (b.2) ~ (b'.2)))}) brs brs') ->
  Γ ;;; E  ⊩ tCase ind discr brs ~ tCase ind discr' brs'
| represents_tFix Γ E mfix mfix' idx nms  :
  All2_Set (fun d n => d.(dname) = nNamed n) mfix nms ->
  All2_Set (fun d d' => (nms ++ Γ) ;;; E ⊩ d.(dbody) ~ d'.(dbody)) mfix mfix' ->
  Γ ;;; E ⊩ tFix mfix idx ~ tFix mfix' idx
with represents_value : value -> term -> Set :=
| represents_value_tBox : represents_value vBox tBox
| represents_value_tClos na E s t na' : [na] ;;; E ⊩ s ~ t -> represents_value (vClos na s E) (tLambda na' t)
| represents_value_tConstruct vs ts ind c : All2_Set represents_value vs ts -> represents_value (vConstruct ind c vs) (tConstruct ind c ts)
| represents_value_tFix vfix i E mfix :
  All2_Set (fun v d => map fst vfix ;;; (add_multiple (map fst vfix) (fix_env vfix E) E) ⊩ snd v ~ d.(dbody)) vfix mfix -> represents_value (vRecClos vfix i E) (tFix mfix i)
where "Γ ;;; E ⊩ s ~ t" := (represents Γ E s t).

Program Definition represents_ind :=
  (λ (P : ∀ (l : list ident) (e : environment) (t t0 : term),
	       l;;; e ⊩ t ~ t0 → Type) (P0 : ∀ (v : value) (t : term),
         represents_value v t → Type) 
     (f : ∀ (Γ : list ident) (E : environment),
         P Γ E tBox tBox (represents_tBox Γ E)) (f0 : 
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
         ∀ (a : All2_Set (λ b b' : list name × term, ∑ nms : list ident, All2_Set (λ (n : name) (n' : ident), n = nNamed n') b.1 nms × (nms ++ Γ);;; E ⊩ b.2 ~ b'.2) brs brs'),
         forall IH : All2_over a (fun b b' H => P (projT1 H ++ Γ) E b.2 b'.2 (snd (projT2 H))),
           P Γ E (tCase ind discr brs) (tCase ind discr' brs')
             (represents_tCase Γ E ind discr discr' brs brs' r Heq a)) 
     (f8 : ∀ (Γ : list ident) (E : environment) (mfix mfix' : list (def term)) 
             (idx : nat) (nms : list ident) (a : All2_Set
                                                 (λ (d : def term) (n : ident),
                                                   dname d = nNamed n) mfix nms) 
             (a0 : All2_Set
                     (λ d d' : def term, (nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                     mfix mfix')
             (IH : All2_over a0 (fun t t' : def term => P (nms ++ Γ) E (dbody t) (dbody t'))),
         P Γ E (tFix mfix idx) (tFix mfix' idx)
           (represents_tFix Γ E mfix mfix' idx nms a a0)) 
     (f9 : P0 vBox tBox represents_value_tBox) (f10 : 
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
              (a : All2_Set (λ (v : ident × term) (d : def term), map fst vfix;;; add_multiple (map fst vfix) (fix_env vfix E) E ⊩ v.2 ~ dbody d) vfix mfix)
              (IH : All2_over  a (fun v d => P (map fst vfix) (add_multiple (map fst vfix) (fix_env vfix E) E) v.2 (dbody d)  ) ),
         P0 (vRecClos vfix i E) (tFix mfix i)
           (represents_value_tFix vfix i E mfix a)),
    fix F
      (l : list ident) (e : environment) (t t0 : term) 
      (r : l;;; e ⊩ t ~ t0) {struct r} : P l e t t0 r :=
     match r as r0 in (l0;;; e0 ⊩ t1 ~ t2) return (P l0 e0 t1 t2 r0) with
     | represents_tBox Γ E => f Γ E
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
     | represents_tFix Γ E mfix mfix' idx nms a a0 =>
         f8 Γ E mfix mfix' idx nms a a0 _
     end
   with F0 (v : value) (t : term) (r : represents_value v t) {struct r} :
     P0 v t r :=
          match r as r0 in (represents_value v0 t0) return (P0 v0 t0 r0) with
          | represents_value_tBox => f9
          | represents_value_tClos na E s t0 na' r0 =>
              f10 na E s t0 na' r0 (F [na] E s t0 r0)
          | represents_value_tConstruct vs ts ind c a => f11 vs ts ind c a _
          | represents_value_tFix vfix i E mfix a => f12 vfix i E mfix a _
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
     (f : ∀ (Γ : list ident) (E : environment),
         P Γ E tBox tBox (represents_tBox Γ E)) (f0 : 
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
                           b.1 nms × (nms ++ Γ);;; E ⊩ b.2 ~ b'.2) brs brs',
            forall IH : All2_over a (fun b b' H => P (projT1 H ++ Γ) E b.2 b'.2 (snd (projT2 H))),
           P Γ E (tCase ind discr brs) (tCase ind discr' brs')
             (represents_tCase Γ E ind discr discr' brs brs' r Heq a)) 
     (f8 : ∀ (Γ : list ident) (E : environment) (mfix mfix' : list (def term)) 
             (idx : nat) (nms : list ident) (a : All2_Set
                                                 (λ (d : def term) (n : ident),
                                                   dname d = nNamed n) mfix nms) 
             (a0 : All2_Set
                     (λ d d' : def term, (nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                     mfix mfix')
             (IH : All2_over a0 (fun t t' : def term => P (nms ++ Γ) E (dbody t) (dbody t'))),
         P Γ E (tFix mfix idx) (tFix mfix' idx)
           (represents_tFix Γ E mfix mfix' idx nms a a0)) 
     (f9 : P0 vBox tBox represents_value_tBox) (f10 : 
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
                     (λ (v : ident × term) (d : def term),
                       map fst vfix;;;
                         add_multiple (map fst vfix) (fix_env vfix E) E ⊩ v.2 ~
                         dbody d) vfix mfix)
              (IH : All2_over  a (fun v d => P (map fst vfix) (add_multiple (map fst vfix) (fix_env vfix E) E) v.2 (dbody d)  ) ),
         P0 (vRecClos vfix i E) (tFix mfix i)
           (represents_value_tFix vfix i E mfix a)),
    fix F
      (l : list ident) (e : environment) (t t0 : term) 
      (r : l;;; e ⊩ t ~ t0) {struct r} : P l e t t0 r :=
     match r as r0 in (l0;;; e0 ⊩ t1 ~ t2) return (P l0 e0 t1 t2 r0) with
     | represents_tBox Γ E => f Γ E
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
     | represents_tFix Γ E mfix mfix' idx nms a a0 =>
         f8 Γ E mfix mfix' idx nms a a0 _
     end
   with F0 (v : value) (t : term) (r : represents_value v t) {struct r} :
     P0 v t r :=
          match r as r0 in (represents_value v0 t0) return (P0 v0 t0 r0) with
          | represents_value_tBox => f9
          | represents_value_tClos na E s t0 na' r0 =>
              f10 na E s t0 na' r0 (F [na] E s t0 r0)
          | represents_value_tConstruct vs ts ind c a => f11 vs ts ind c a _
          | represents_value_tFix vfix i E mfix a => f12 vfix i E mfix a _
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
     (f : ∀ (Γ : list ident) (E : environment),
         P Γ E tBox tBox (represents_tBox Γ E)) (f0 : 
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
                           b.1 nms × (nms ++ Γ);;; E ⊩ b.2 ~ b'.2) brs brs',
          forall IH : All2_over a (fun b b' H => P (projT1 H ++ Γ) E b.2 b'.2 (snd (projT2 H))),
           P Γ E (tCase ind discr brs) (tCase ind discr' brs')
             (represents_tCase Γ E ind discr discr' brs brs' r Heq a)) 
     (f8 : ∀ (Γ : list ident) (E : environment) (mfix mfix' : list (def term)) 
             (idx : nat) (nms : list ident) (a : All2_Set
                                                 (λ (d : def term) (n : ident),
                                                   dname d = nNamed n) mfix nms) 
             (a0 : All2_Set
                     (λ d d' : def term, (nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                     mfix mfix')
             (IH : All2_over a0 (fun t t' : def term => P (nms ++ Γ) E (dbody t) (dbody t'))),
         P Γ E (tFix mfix idx) (tFix mfix' idx)
           (represents_tFix Γ E mfix mfix' idx nms a a0)) 
     (f9 : P0 vBox tBox represents_value_tBox) (f10 : 
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
                     (λ (v : ident × term) (d : def term),
                       map fst vfix;;;
                         add_multiple (map fst vfix) (fix_env vfix E) E ⊩ v.2 ~
                         dbody d) vfix mfix)
              (IH : All2_over  a (fun v d => P (map fst vfix) (add_multiple (map fst vfix) (fix_env vfix E) E) v.2 (dbody d)  ) ),
         P0 (vRecClos vfix i E) (tFix mfix i)
           (represents_value_tFix vfix i E mfix a)),
    (represents_ind P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12,
      represents_value_ind P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12)).

Local Notation "'⊩' v ~ s" := (represents_value v s) (at level 50).
Local Hint Constructors represents : core.
Local Hint Constructors represents_value : core.

From MetaCoq Require Import bytestring MCString.
Require Import BinaryString.
Import String.

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

Lemma string_of_nat_empty n : 
  string_of_nat n <> "".
Proof.
Admitted.

Lemma string_of_nat_inj n1 n2 : 
  string_of_nat n1 = string_of_nat n2 -> n1 = n2.
Admitted.

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
    { cbn in HN. rewrite map_length seq_length in HN. lia. }
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


Section Map2.

  Context {A B C : Type}.
  Variable (f : A → B → C).
  Fixpoint map2 (l : list A) (l' : list B) {struct l} :
	  list C :=
    match l with
    | [] => []
    | hd :: tl =>
        match l' with
        | [] => []
        | hd' :: tl' => f hd hd' :: map2 tl tl'
        end
    end.
End Map2.

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
      let mfix' := map2 (fun d na => map_def_name _ (fun _ => nNamed na) (annotate (gen_many_fresh s (map dname mfix) ++ s)) d) mfix nms in
      tFix mfix' idx
  | _ => u
  end.


Definition extraction_term_flags := 
  {| has_tBox := true
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
  |}.

Definition extraction_env_flags := 
  {| has_axioms := false;
    term_switches := extraction_term_flags;
    has_cstr_params := false ;
    cstr_as_blocks := true |}.

Local Existing Instance extraction_env_flags.

Lemma nclosed_represents Σ Γ E s :
  wellformed Σ #|Γ| s -> Γ ;;; E ⊩ annotate Γ s ~ s.
Proof.
  intros Hwf.
  induction s in Γ, Hwf |- * using EInduction.term_forall_list_ind; cbn in *; rtoProp; eauto.
  - eapply Nat.ltb_lt in Hwf. destruct nth_error eqn:Eq; eauto.
    eapply nth_error_None in Eq. lia.
  - econstructor. solve_all. clear - H1. induction H1; econstructor; eauto. eapply p, p.
  - econstructor. eauto.
    { eapply All2_All2_Set. solve_all. eapply All_All2. eapply H0. intros [] []; cbn in *.
      len. now rewrite gen_many_fresh_length. }
    solve_all.
    clear - Γ H0. induction H0; econstructor; eauto.
    rename x into br. exists (gen_many_fresh Γ br.1). cbn. split.
    + eapply All2_All2_Set. solve_all. now eapply All2_refl.
    + eapply p. rewrite app_length gen_many_fresh_length. eapply p.
  - eapply represents_tFix with (nms := gen_many_fresh Γ (map dname m)).
    2:{ unfold wf_fix in Hwf. rtoProp. solve_all. eapply Nat.ltb_lt in H.
        generalize (map_length dname m).
        generalize (map dname m). intros nms Hnms. induction m in Γ, H0, n, H, nms, Hnms |- *.        
        + econstructor.
        + destruct nms; invs Hnms. invs H0.
          destruct n0; cbn in *; econstructor.
          * eapply H3. cbn. rewrite app_length gen_many_fresh_length H2. eapply H3.
          * specialize IHm with (nms := nAnon :: nms). cbn in IHm.
            todo "fix".
          * cbn. todo "fix".
          * todo "fix".
    }
    todo "fix".
Qed.

Lemma unfolds_bound : 
  (forall Γ E s t, Γ ;;; E ⊩ s ~ t -> closedn #|Γ| t) ×
    (forall v s, ⊩ v ~ s -> closedn 0 s).
Proof.
  refine (rep_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros; cbn; rtoProp; eauto.
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
    clear a. induction a0; cbn in *; econstructor.
    rewrite app_length in IH. eapply IH.
    eapply IHa0. eapply IH.
  - solve_all. induction a; cbn in *; rtoProp; eauto. 
    econstructor. cbn in *. eapply IH. eapply IHa. eapply IH.
  - induction a; cbn in *; rtoProp; split.
    + destruct IH. revert i0. len. eapply All2_Set_All2 in a as Haa. 
      eapply All2_length in Haa as ->. eauto.
    + todo "fix".
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
      rewrite app_length in IH1.
      assert (#|y.1| = #|x.1|) as -> by now invs Heq.
      eapply All2_Set_All2 in H1 as HH. eapply All2_length in HH as ->.
      rewrite app_assoc.
      eapply IH1. eauto. cbn. now rewrite <- app_assoc. eauto.
  - econstructor; eauto. todo "fix".
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
  - destruct vs using rev_ind; repeat rewrite app_length in Hlen; cbn in *; try lia.
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
  | tRel i => true
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
      forallb (fun x => match x.(dname) with nNamed _ => true | _ => false end) mfix
      && let names := flat_map (fun d => match d.(dname) with nNamed i => [i] | _ => [] end) mfix in
         dupfree names &&
           forallb (test_def (sunny (names ++ Γ))) mfix
  | tConstruct _ _ args => forallb (sunny Γ) args
  | tConst _ => true
  | _ => false
  end.

Inductive wf : value -> Type :=
| wf_vBox : wf vBox
| wf_vClos na b E : ~ In na (map fst E) -> sunny (na :: map fst E) b -> All (fun v => wf (snd v)) E -> wf (vClos na b E)
| wf_vConstruct ind c args : All wf args -> wf (vConstruct ind c args). (* 
| wf_vRecClos mfix idx E :  *)

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

Lemma eval_wf Σ E s v : 
  Forall (fun d => match d.2 with ConstantDecl (Build_constant_body (Some d)) => sunny [] d | _ => true end) Σ ->
  All (fun x => wf (snd x)) E ->
  sunny (map fst E) s -> 
  eval Σ E s v -> 
  wf v.
Proof.
  intros HΣ HE Hsunny.
  induction 1; eauto; cbn in *; rtoProp; eauto using Forall.
  - do 2 forward IHeval1; eauto. inv IHeval1.
    eapply IHeval3; eauto. econstructor; cbn; eauto.
  - econstructor; eauto. unfold fresh in H. destruct in_dec; cbn in *; congruence.
  - eapply IHeval2. econstructor; cbn; eauto. eauto.
  - solve_all. inv X0.
    eapply IHeval2. eapply wf_add_multiple; eauto.
    2: eapply All_skipn; eauto. len. eapply All2_length in f. lia.
    eapply All_nth_error in H1. 2: eauto. rtoProp.
    solve_all.
    rewrite map_fst_add_multiple. len.
    eapply All2_length in f; lia.
    enough (nms = flat_map (λ x : name, match x with
                 | nAnon => []
                 | nNamed na => [na]
                 end) br.1) as -> by eauto.
    clear - f. induction f; cbn; f_equal; destruct r, x; cbn; congruence. 
  - todo "fix".
  - todo "fix".
  - eapply IHeval; eauto. eapply declared_constant_Forall in isdecl.
    2: eapply Forall_impl. 2: eauto.
    2: { cbn. intros [] ?. cbn in *.  exact H0. }
    cbn in *. destruct decl; cbn in *.
    subst. todo "sunny constant".
  - solve_all. rename X into IHeval1, X0 into IHeval2. eapply All_app in Hsunny as [H1 H2].
    forward IHeval1; solve_all; eauto. invs IHeval1.
    econstructor. eapply All_app_inv; eauto.
    repeat econstructor. invs H2.
    eapply IHeval2; solve_all.
  - cbn. econstructor. econstructor.
Qed.

(* TODO
- red_iota
- fix
- sunny constants
- freshness in represents_subst
*)

Lemma eval_construct_All2 Σ E ind c args vs mdecl idecl cdecl :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  #|args| <= cstr_arity mdecl cdecl ->
  All2 (eval Σ E) args vs -> eval Σ E (tConstruct ind c args) (vConstruct ind c vs).
Proof.
  intros Hind.
  revert vs. induction args using rev_ind; intros vs Hlen Hvs.
  - invs Hvs. now econstructor.
  - eapply All2_app_inv_l in Hvs as (vs' & r2 & -> & H1 & H2).
    invs H2. invs X. revert Hlen; len; intros Hlen. econstructor.
    + eauto.
    + lia.
    + eapply IHargs; eauto. lia.
    + eauto.
Qed.
(* 
Local Hint Constructors eval : core.

Lemma eval_global_weaken Σ E t v E' : 
  eval Σ E t v -> ∑ v', eval Σ (E ++ E') t v' × (forall res, ⊩ v ~ res -> ⊩ v' ~ res).
Proof.
  intros H.
  induction H.
  - exists v. split. econstructor. admit. eauto.
  - edestruct IHeval1 as (? & ? & hres).
    edestruct IHeval2 as (? & ? & ?).
    specialize (hres tBox). forward hres. econstructor. invs hres.
    eauto.
  - edestruct IHeval1 as (? & ? & hres1). 
    edestruct IHeval2 as (? & ? & hres2).

    eexists. split.
    
  
  eexists. split. econstructor.
    eexists. split; eauto. econstructor.
    
    Admitted.     *)

Lemma implication (Σ Σ' : global_context) E s t u :
  Forall (fun d => match d.2 with ConstantDecl (Build_constant_body (Some d)) => sunny [] d | _ => true end) Σ' ->
  All2 (fun d d' => d.1 = d'.1 × match d.2 with ConstantDecl (Build_constant_body (Some body)) => 
    ∑ body', d'.2 = ConstantDecl (Build_constant_body (Some body')) × [] ;;; [] ⊩ body' ~ body
  | _ => True end) Σ Σ' -> 
  All (fun x => wf (snd x)) E ->
  sunny (map fst E) u -> 
  EWcbvEval.eval Σ s t ->
  [] ;;; E ⊩ u ~ s ->
  ∑ v, ⊩ v ~ t × eval Σ' E u v.
Proof.
  intros HΣ HΣind HE Hsunny Heval Hrep.
  induction Heval in u, E, Hrep, Hsunny, HE; cbn in *; rtoProp; eauto; try congruence.
  - invs Hrep.
    + invs H0.
    + cbn in Hsunny. rtoProp. edestruct IHHeval1 as (v & Hv1 & Hv2). 3: eauto. eauto. eauto. 
      edestruct IHHeval2 as (? & ? & ?); eauto.
      invs Hv1. eexists; split; eauto. econstructor; eauto.      
  - invs Hrep.
    + invs H0.
    + cbn in Hsunny. rtoProp.
      edestruct IHHeval1 as (v1 & Hv1 & Hv2). 3: eauto. eauto. eauto.
      invs Hv1.
      edestruct IHHeval2 as (v2 & Hv1_ & Hv2_). 3: eauto. eauto. eauto.
      eapply eval_wf in Hv2 as Hwf; eauto. invs Hwf; eauto. 
      edestruct IHHeval3 as (v3 & Hv1__ & Hv2__).
      3: eapply represents_subst; eauto.
      { econstructor. eapply eval_wf in Hv2_; eauto. eauto. }
      { eauto. }
      eexists; split; eauto. econstructor; eauto.
  - invs Hrep.
    + invs H0.
    + cbn in Hsunny. rtoProp. 
      edestruct IHHeval1 as (v1 & Hv1 & Hv2). 3: eauto. eauto. eauto.
      edestruct IHHeval2 as (v2 & Hv1_ & Hv2_).
      3: eapply represents_subst; eauto.
      { econstructor. cbn in *. eapply eval_wf in Hv2; eauto. eauto. }
      { eapply eval_wf in Hv2; eauto. }
      { unfold fresh in H. destruct in_dec; cbn in *; congruence. }
      eexists; split; eauto. econstructor; eauto.
  - invs Hrep.
    + invs H0.
    + cbn in Hsunny. rtoProp.
      edestruct IHHeval1 as (v & Hv1 & Hv2). 3,1,2: eauto.
      eapply All2_Set_All2 in H7. eapply All2_nth_error_Some_right in e2 as He2. 2: eauto.
      destruct He2 as (br' & Hnth & nms & Hbrs & Hbr). invs Hv1. 
      edestruct IHHeval2 as (v2 & Hv1_ & Hv2_).
      3: { eapply forallb_nth_error in H. setoid_rewrite Hnth in H. cbn in H. rtoProp.
           assert (nms = flat_map (λ x : name, match x with
               | nAnon => []
               | nNamed na => [na]
               end) br'.1) as Heqnms. { clear - Hbrs. induction Hbrs; cbn; now subst. }
           unfold iota_red. eapply represents_substl. 5: eauto.
           { rewrite Heqnms flat_map_concat_map. intros ? (? & ([] & <- & ?) % in_map_iff & Hd) % in_concat; cbn in *; eauto.
           destruct Hd; subst; eauto.
           eapply forallb_forall in H; eauto.
           cbn in H. unfold fresh in H. destruct in_dec; cbn in *; congruence. }
           { subst. unfold dupfree in H2. destruct dupfree_dec_ident; cbn in *; congruence. }
           2: eapply All2_rev. len.
           2:{ eapply All2_skipn. eauto. }
           eapply All2_Set_All2, All2_nth_error in H6; eauto.
           eapply All2_Set_All2, All2_length in H3; eauto.
           eapply All2_Set_All2, All2_length in Hbrs; eauto.
           rewrite !skipn_length in e4 |- *. lia.
      }
      3: eexists; split; [ eauto | econstructor; eauto].
      * rewrite rev_involutive.
        eapply eval_wf in Hv2; eauto.
        invs Hv2. eapply wf_add_multiple. eauto.
        -- len. eapply All2_Set_All2, All2_nth_error in H6; eauto.
           eapply All2_Set_All2, All2_length in H3; eauto.
           eapply All2_Set_All2, All2_length in Hbrs; eauto.
           rewrite !skipn_length in e4 |- *. lia.
        -- eapply All_skipn; eauto.
      * rewrite map_fst_add_multiple. 
        -- len.
           eapply All2_Set_All2, All2_nth_error in H6; eauto.
           eapply All2_Set_All2, All2_length in H3; eauto.
           eapply All2_Set_All2, All2_length in Hbrs; eauto.
           rewrite !skipn_length in e4 |- *. lia.
        -- eapply forallb_nth_error in H. setoid_rewrite Hnth in H. cbn in H. rtoProp.
           enough (nms = flat_map (λ x : name, match x with
           | nAnon => []
           | nNamed na => [na]
           end) br'.1) as -> by eauto.
           clear - Hbrs. induction Hbrs; cbn; now subst.
      * admit.
      * admit.
      * eapply All2_Set_All2, All2_length in H3.
        eapply All2_Set_All2, All2_nth_error in H6; eauto.
        eapply All2_Set_All2, All2_length in Hbrs; eauto.
        rewrite !skipn_length in e4 |- *. lia.
      * solve_all. 
      * now rewrite rev_involutive in Hv2_.
  - todo "fix".
  - invs Hrep. 
    + invs H0.
    + cbn in *. rtoProp.
      edestruct IHHeval1 as (v1 & Hv1 & Hv2); eauto.
      invs Hv1; destruct args using rev_ind; cbn in *; try congruence.
      all: match goal with [H : _ = mkApps _ _ |- _ ] => now rewrite mkApps_app in H end.
  - invs Hrep. invs H0.
  - invs Hrep.
    + invs H0.
    + assert (∑ decl' body', declared_constant Σ' c decl' × sunny [] body' × cst_body decl' = Some body' × [];;; [] ⊩ body' ~ body) as (decl' & Hdecl & body' & Hsunny' & e' & H').
      { clear - HΣ HΣind isdecl e. unfold declared_constant in isdecl. solve_all.
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
      edestruct IHHeval as (v & Hv1 & Hv2). 3: eauto. econstructor. cbn. eauto.
      eapply eval_global_weaken in Hv2 as (v' & H1' & H2'); eauto. cbn in H1'.
      eexists. split. eapply H2'. econstructor. eauto. eauto. eauto.
  - invs Hrep. invs H0.
  - invs Hrep.
    + invs H0. eexists. split. 2:{ econstructor. eauto. }
      econstructor. induction a in vs, H3 |- *.
      * invs H3. econstructor.
      * invs H3. econstructor. eapply eval_represents_value; eauto. eauto.
    + assert (∑ vs, All2 (fun v t => ⊩ v ~ t) vs args' × All2 (fun v u => eval Σ E u v) vs args0) as (vs & Hvs & Hvs').
      * cbn in Hsunny. rtoProp. induction a in iha, H3, args0, Hsunny |- *.
        -- invs H3. exists []. split; econstructor.
        -- invs H3. invs iha.
           edestruct IHa as (vs & Hv1 & Hv2). 2: eauto. 2: eauto.
           cbn in Hsunny; now rtoProp.
           edestruct X. 3: eauto. eauto. eauto. cbn in Hsunny; now rtoProp.
           eexists (_ :: _). destruct p. split. econstructor; eauto.
           econstructor; eauto. 
      * eexists. split. econstructor. eapply All2_All2_Set; eauto.
        eapply eval_construct_All2; eauto.
        2:{ solve_all. clear - Hvs'. induction Hvs'; econstructor; eauto. }
        eapply All2_length in Hvs'; eapply All2_length in Hvs.
        clear iha. eapply All2_Set_All2, All2_length in a. lia.
  - invs Hrep.
    + invs H0.
    + cbn in Hsunny. rtoProp.
      eapply eval_to_value in Heval1 as Hval. invs Hval.
      * destruct f'; cbn in *; try congruence.           
        edestruct IHHeval1 as (v & Hv1 & Hv2). 3: eauto. eauto. eauto. invs Hv1.
      * invs H4; cbn in *; eauto.
      * invs H1; cbn in *; eauto; try congruence.
        rtoProp. edestruct IHHeval1 as (v & Hv1 & Hv2). 3: eauto. eauto. eauto.
        invs Hv1; destruct args using rev_ind; cbn in *; try congruence.
        all: match goal with [H : _ = mkApps _ _ |- _ ] => now rewrite mkApps_app in H end.
  - invs Hrep; cbn in *; try congruence; rtoProp.
    + econstructor. split; eauto. econstructor.
    + destruct args'; congruence.
    + solve_all. eexists. split. 2: econstructor; solve_all.
      instantiate (1 := nms).
      econstructor. 2:{ eapply All2_Set_All2 in H. solve_all. }
      eapply All2_Set_All2 in H, H0. eapply All2_All2_Set. solve_all.
      clear - H H0. revert H. todo "fix".
      Unshelve. all: todo "evar".
Qed.