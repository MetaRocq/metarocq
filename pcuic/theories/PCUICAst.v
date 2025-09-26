(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Export Primitive Universes BasicAst Environment Reflect.
From MetaRocq.Common Require EnvironmentTyping.
From MetaRocq.PCUIC Require Export PCUICPrimitive.
From Equations Require Import Equations.
(** * AST of the Polymorphic Cumulative Calculus of Inductive Constructions

   This AST is a cleaned-up version of Rocq's internal AST better suited for
   reasoning.
   In particular, it has binary applications and all terms are well-formed.
   Casts are absent as well. *)

Declare Scope pcuic.
Delimit Scope pcuic with pcuic.
Open Scope pcuic.

(** DO NOT USE firstorder, since the introduction of Ints and Floats, it became unusuable. *)
Ltac pcuicfo_gen tac :=
  simpl in *; intuition (simpl; intuition tac).

Tactic Notation "pcuicfo" := pcuicfo_gen auto.
Tactic Notation "pcuicfo" tactic(tac) := pcuicfo_gen tac.

(* This allows not relying on lemma names getting a length ws_cumul_pb out of some type. *)
Class HasLen (A : Type) (x y : nat) := len : A -> x = y.

(** Note the use of a global reference to avoid capture. *)
Notation length_of t := ltac:(let lemma := constr:(PCUICAst.len t) in exact lemma) (only parsing).


(* Defined here since BasicAst does not have access to universe instances.
  Parameterized by term types as they are not yet defined. *)
Record predicate {term} := mk_predicate {
  pparams : list term; (* The parameters *)
  puinst : Instance.t; (* The universe instance *)
  pcontext : list (context_decl term);
    (* The predicate context,
    initially built from params and puinst *)
  preturn : term; (* The return type *) }.
Derive NoConfusion for predicate.
Arguments predicate : clear implicits.
Arguments mk_predicate {_}.

Section map_predicate.
  Context {term term' : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (paramf preturnf : term -> term').
  Context (pcontextf : list (context_decl term) -> list (context_decl term')).

  Definition map_predicate (p : predicate term) :=
    {| pparams := map paramf p.(pparams);
        puinst := uf p.(puinst);
        pcontext := pcontextf p.(pcontext);
        preturn := preturnf p.(preturn) |}.

  Lemma map_pparams (p : predicate term) :
    map paramf (pparams p) = pparams (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_preturn (p : predicate term) :
    preturnf (preturn p) = preturn (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_pcontext (p : predicate term) :
    pcontextf (pcontext p) = pcontext (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_puinst (p : predicate term) :
    uf (puinst p) = puinst (map_predicate p).
  Proof using Type. reflexivity. Qed.

End map_predicate.

Definition shiftf {A B} (f : nat -> A -> B) k := (fun k' => f (k' + k)).

Section map_predicate_k.
  Context {term : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (f : nat -> term -> term).

  Definition map_predicate_k k (p : predicate term) :=
    {| pparams := map (f k) p.(pparams);
        puinst := uf p.(puinst);
        pcontext := p.(pcontext);
        preturn := f (#|p.(pcontext)| + k) p.(preturn) |}.

  Lemma map_k_pparams k (p : predicate term) :
    map (f k) (pparams p) = pparams (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_preturn k (p : predicate term) :
    f (#|p.(pcontext)| + k) (preturn p) = preturn (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_pcontext k (p : predicate term) :
    (pcontext p) = pcontext (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_puinst k (p : predicate term) :
    uf (puinst p) = puinst (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Definition test_predicate (instp : Instance.t -> bool) (p : term -> bool)
    (pred : predicate term) :=
    instp pred.(puinst) && forallb p pred.(pparams) &&
    test_context p pred.(pcontext) && p pred.(preturn).

  Definition test_predicate_k (instp : Instance.t -> bool)
    (p : nat -> term -> bool) k (pred : predicate term) :=
    instp pred.(puinst) && forallb (p k) pred.(pparams) &&
    test_context_k p #|pred.(pparams)| pred.(pcontext) &&
    p (#|pred.(pcontext)| + k) pred.(preturn).

  Definition test_predicate_ku (instp : nat -> Instance.t -> bool)
    (p : nat -> term -> bool) k (pred : predicate term) :=
    instp k pred.(puinst) && forallb (p k) pred.(pparams) &&
    test_context (p #|pred.(puinst)|) pred.(pcontext) &&
    p k pred.(preturn).

End map_predicate_k.

Section Branch.
  Context {term : Type}.
  (* Parameterized by term types as they are not yet defined. *)
  Record branch := mk_branch {
    bcontext : list (context_decl term);
    (* Context of binders of the branch, including lets.
       This context is open w.r.t. to an instance of the parameters of the inductive type only,
       it is NOT subject to substitution/lifting
      *)
    bbody : term; (* The branch body *) }.
  Derive NoConfusion for branch.

  Definition string_of_branch (f : term -> string) (b : branch) :=
  "([" ^ String.concat "," (map (string_of_name ∘ binder_name ∘ decl_name) (bcontext b)) ^ "], "
  ^ f (bbody b) ^ ")".

  Definition pretty_string_of_branch (f : term -> string) (b : branch) :=
    String.concat " " (map (string_of_name ∘ binder_name ∘ decl_name) (bcontext b)) ^ " => " ^ f (bbody b).

  Definition test_branch (pctx : term -> bool) (p : term -> bool) (b : branch) :=
    test_context pctx b.(bcontext) && p b.(bbody).

  Definition test_branch_k (pred : predicate term) (p : nat -> term -> bool) k (b : branch) :=
    test_context_k p #|pred.(pparams)| b.(bcontext) && p (#|b.(bcontext)| + k) b.(bbody).

End Branch.
Arguments branch : clear implicits.

Section map_branch.
  Context {term term' : Type}.
  Context (f : term -> term').
  Context (g : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term')).

  Definition map_branch (b : branch term) :=
  {| bcontext := g b.(bcontext);
      bbody := f b.(bbody) |}.

  Lemma map_bbody (b : branch term) :
    f (bbody b) = bbody (map_branch b).
  Proof using Type. reflexivity. Qed.

  Lemma map_bcontext (b : branch term) :
    g (bcontext b) = bcontext (map_branch b).
  Proof using Type. reflexivity. Qed.
End map_branch.

Definition map_branches {term B} (f : term -> B) h l := List.map (map_branch f h) l.

Section map_branch_k.
  Context {term term' : Type}.
  Context (f : nat -> term -> term').
  Context (g : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term')).
  Definition map_branch_k k (b : branch term) :=
  {| bcontext := g b.(bcontext);
     bbody := f (#|b.(bcontext)| + k) b.(bbody) |}.

  Lemma map_k_bbody k (b : branch term) :
    f (#|b.(bcontext)| + k) (bbody b) = bbody (map_branch_k k b).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_bcontext k (b : branch term) :
    g (bcontext b) = bcontext (map_branch_k k b).
  Proof using Type. reflexivity. Qed.
End map_branch_k.

Notation map_branches_k f h k brs :=
  (List.map (map_branch_k f h k) brs).

Notation test_branches_k p test k brs :=
  (List.forallb (test_branch_k p test k) brs).

Inductive term :=
| tRel (n : nat)
| tVar (i : ident) (* For free variables (e.g. in a goal) *)
| tEvar (n : nat) (l : list term)
| tSort (u : sort)
| tProd (na : aname) (A B : term)
| tLambda (na : aname) (A t : term)
| tLetIn (na : aname) (b B t : term) (* let na := b : B in t *)
| tApp (u v : term)
| tConst (k : kername) (ui : Instance.t)
| tInd (ind : inductive) (ui : Instance.t)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase (indn : case_info) (p : predicate term) (c : term) (brs : list (branch term))
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term).

Derive NoConfusion for term.

Notation prim_val := (prim_val term).

Notation tInt i := (tPrim (_; primIntModel i)) (only parsing).
Notation tFloat f := (tPrim (_; primFloatModel f)) (only parsing).
Notation tString s := (tPrim (_; primStringModel s)) (only parsing).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (tApp t u) us
  end.

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

Lemma isLambda_inv t : isLambda t -> exists na ty bod, t = tLambda na ty bod.
Proof. destruct t => //; eauto. Qed.

(** Basic operations on the AST: lifting, substitution and tests for variable occurrences. *)

Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then (n + i) else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (lift n) k p in
    let brs' := map_branches_k (lift n) id k brs in
    tCase ind p' (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tCoFix mfix' idx
  | tPrim p => tPrim (map_prim (lift n k) p)
  | x => x
  end.

Notation lift0 n := (lift n 0).

(** Parallel substitution: it assumes that all terms in the substitution live in the
    same context *)

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (subst s) k p in
    let brs' := map_branches_k (subst s) id k brs in
    tCase ind p' (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tCoFix mfix' idx
  | tPrim p => tPrim (map_prim (subst s k) p)
  | x => x
  end.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation subst10 t := (subst1 t 0).
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ T M | tProd _ T M => closedn k T && closedn (S k) M
  | tApp u v => closedn k u && closedn k v
  | tLetIn na b t b' => closedn k b && closedn k t && closedn (S k) b'
  | tCase ind p c brs =>
    let p' := test_predicate_k (fun _ => true) closedn k p in
    let brs' := test_branches_k p closedn k brs in
    p' && closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tPrim p => test_prim (closedn k) p
  | _ => true
  end.

Section fix_test.

Variable test : term -> bool.

Fixpoint test_context_nlict (bcontext : list (context_decl term)) :=
  match bcontext with
  | nil => true
  | d :: bcontext => test_context_nlict bcontext &&
                     test (decl_type d) && match decl_body d with Some _ => false | None => true end
  end.

End fix_test.

Definition test_branch_nlict test b :=
  test_context_nlict test (bcontext b) && test (bbody b).

Definition test_branches_nlict test brs :=
  forallb (test_branch_nlict test) brs.

Fixpoint nlict (t : term) : bool :=
  match t with
  | tEvar ev args => List.forallb nlict args
  | tLambda _ T M | tProd _ T M => nlict T && nlict M
  | tApp u v => nlict u && nlict v
  | tLetIn na b t b' => nlict b && nlict t && nlict b'
  | tCase ind p c brs =>
    let p' := test_predicate_k (fun _ => true) (fun _ => nlict) 0 p in
    let brs' := test_branches_nlict nlict brs in
    p' && nlict c && brs'
  | tProj p c => nlict c
  | tFix mfix idx =>
    List.forallb (test_def nlict nlict) mfix
  | tCoFix mfix idx =>
    List.forallb (test_def nlict nlict) mfix
  | tPrim p => test_prim nlict p
  | _ => true
  end.

Notation closed t := (closedn 0 t).
Notation closed_decl n := (test_decl (closedn n)).
Notation closedn_ctx := (test_context_k closedn).
Notation closed_ctx := (closedn_ctx 0).

Fixpoint noccur_between k n (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k || Nat.leb (k + n) i
  | tEvar ev args => List.forallb (noccur_between k n) args
  | tLambda _ T M | tProd _ T M => noccur_between k n T && noccur_between (S k) n M
  | tApp u v => noccur_between k n u && noccur_between k n v
  | tLetIn na b t b' => noccur_between k n b && noccur_between k n t && noccur_between (S k) n b'
  | tCase ind p c brs =>
    let p' := test_predicate_k (fun _ => true) (fun k' => noccur_between k' n) k p in
    let brs' := test_branches_k p (fun k => noccur_between k n) k brs in
    p' && noccur_between k n c && brs'
  | tProj p c => noccur_between k n c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tPrim p => test_prim (noccur_between k n) p
  | _ => true
  end.

(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)

#[global]
Instance subst_instance_constr : UnivSubst term :=
  fix subst_instance_constr u c {struct c} : term :=
  match c with
  | tRel _ | tVar _ => c
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tSort s => tSort (subst_instance_sort u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tLambda na T M => tLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (subst_instance_constr u v)
  | tProd na A B => tProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | tLetIn na b ty b' => tLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind p c brs =>
    let p' := map_predicate (subst_instance_instance u) (subst_instance_constr u) (subst_instance_constr u) id p in
    let brs' := List.map (map_branch (subst_instance_constr u) id) brs in
    tCase ind p' (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  | tPrim p => tPrim (mapu_prim (subst_instance_level u) (subst_instance_constr u) p)
  end.

(** Tests that the term is closed over [k] universe variables *)
Fixpoint closedu (k : nat) (t : term) : bool :=
  match t with
  | tSort s => closedu_sort k s
  | tInd _ u => closedu_instance k u
  | tConstruct _ _ u => closedu_instance k u
  | tConst _ u => closedu_instance k u
  | tRel i => true
  | tEvar ev args => forallb (closedu k) args
  | tLambda _ T M | tProd _ T M => closedu k T && closedu k M
  | tApp u v => closedu k u && closedu k v
  | tLetIn na b t b' => closedu k b && closedu k t && closedu k b'
  | tCase ind p c brs =>
    let p' := test_predicate_ku closedu_instance closedu k p in
    let brs' := forallb (test_branch (closedu #|p.(puinst)|) (closedu k)) brs in
    p' && closedu k c && brs'
  | tProj p c => closedu k c
  | tFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | tCoFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | tPrim p => test_primu (closedu_level k) (closedu k) p
  | _ => true
  end.

Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.
  Definition tSort := tSort.
  Definition tProd := tProd.
  Definition tLambda := tLambda.
  Definition tLetIn := tLetIn.
  Definition tInd := tInd.
  Definition tProj := tProj.
  Definition mkApps := mkApps.

  Definition lift := lift.
  Definition subst := subst.
  Definition closedn := closedn.
  Definition noccur_between := noccur_between.
  Definition subst_instance_constr := subst_instance.
End PCUICTerm.

(* These functors derive the notion of local context and lift substitution, term lifting,
  the closed predicate to them. *)
Module PCUICEnvironment := Environment PCUICTerm.
Export PCUICEnvironment.
(* Do NOT `Include` this module, as this would sadly duplicate the rewrite database... *)


(** Decompose an arity into a context and a sort *)

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

(** Inductive substitution, to produce a constructors' type *)
Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Module PCUICTermUtils <: TermUtils PCUICTerm PCUICEnvironment.

Definition destArity := destArity.
Definition inds := inds.

End PCUICTermUtils.


Ltac unf_term := unfold PCUICTerm.term in *; unfold PCUICTerm.tRel in *;
                 unfold PCUICTerm.tSort in *; unfold PCUICTerm.tProd in *;
                 unfold PCUICTerm.tLambda in *; unfold PCUICTerm.tLetIn in *;
                 unfold PCUICTerm.tInd in *; unfold PCUICTerm.tProj in *;
                 unfold PCUICTerm.lift in *; unfold PCUICTerm.subst in *;
                 unfold PCUICTerm.closedn in *; unfold PCUICTerm.noccur_between in *;
                 unfold PCUICTerm.subst_instance_constr in *;
                 unfold PCUICTermUtils.destArity in *; unfold PCUICTermUtils.inds in *.


Lemma context_assumptions_mapi_context f (ctx : context) :
  context_assumptions (mapi_context f ctx) = context_assumptions ctx.
Proof.
  now rewrite mapi_context_fold; len.
Qed.
#[global]
Hint Rewrite context_assumptions_mapi_context : len.

Module PCUICEnvTyping := EnvironmentTyping.EnvTyping PCUICTerm PCUICEnvironment PCUICTermUtils.
(** Included in PCUICTyping only *)

Module PCUICConversion := EnvironmentTyping.Conversion PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.

Global Instance context_reflect`(ReflectEq term) :
  ReflectEq (list (BasicAst.context_decl term)) := _.

Local Ltac finish :=
  let h := fresh "h" in
  right ;
  match goal with
  | e : ?t <> ?u |- _ =>
    intro h ; apply e ; now inversion h
  end.

Local Ltac fcase c :=
  let e := fresh "e" in
  case c ; intro e ; [ subst ; try (left ; reflexivity) | finish ].

Definition string_of_predicate {term} (f : term -> string) (p : predicate term) :=
  "(" ^ "(" ^ String.concat "," (map f (pparams p)) ^ ")"
  ^ "," ^ string_of_universe_instance (puinst p)
  ^ ",(" ^ String.concat "," (map (string_of_name ∘ binder_name ∘ decl_name) (pcontext p)) ^ ")"
  ^ "," ^ f (preturn p) ^ ")".

Definition eqb_predicate_gen (eqb_univ_instance : Instance.t -> Instance.t -> bool)
  (eqdecl : context_decl -> context_decl -> bool)
  (eqterm : term -> term -> bool) (p p' : predicate term) :=
  forallb2 eqterm p.(pparams) p'.(pparams) &&
  eqb_univ_instance p.(puinst) p'.(puinst) &&
  forallb2 eqdecl p.(pcontext) p'.(pcontext) &&
  eqterm p.(preturn) p'.(preturn).

(** Syntactic ws_cumul_pb *)

Definition eqb_predicate (eqterm : term -> term -> bool) (p p' : predicate term) :=
  eqb_predicate_gen eqb (eqb_context_decl eqterm) eqterm p p'.

(** Theory of [map] variants on branches and predicates. *)

(* The [map] rewrite database gathers all the map composition rewrite lemmas
  on these types. *)
#[global]
Hint Rewrite map_map_compose @compose_map_def length_map : map.

#[global]
Hint Rewrite @forallb_map : map.

Lemma map_predicate_map_predicate
      {term term' term''}
      (finst finst' : Instance.t -> Instance.t)
      (f g : term' -> term'')
      (f' g' : term -> term')
      (h : list (BasicAst.context_decl term') -> list (BasicAst.context_decl term''))
      (h' : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term'))
      (p : predicate term) :
  map_predicate finst f g h (map_predicate finst' f' g' h' p) =
  map_predicate (finst ∘ finst') (f ∘ f') (g ∘ g') (h ∘ h') p.
Proof.
  unfold map_predicate. destruct p; cbn.
  f_equal.
  apply map_map.
Qed.

Lemma map_predicate_id x : map_predicate (@id _) (@id term) (@id term) (@id _) x = id x.
Proof.
  unfold map_predicate; destruct x; cbn; unfold id.
  f_equal. apply map_id.
Qed.
#[global]
Hint Rewrite @map_predicate_id : map.

Definition tCasePredProp_k
            (P : nat -> term -> Type)
            k (p : predicate term) :=
  All (P k) p.(pparams) × onctx_k P #|p.(pparams)| p.(pcontext) ×
  P (#|p.(pcontext)| + k) p.(preturn).

Definition tCasePredProp {term}
            (Pparams Preturn : term -> Type)
            (p : predicate term) :=
  All Pparams p.(pparams) ×
  onctx Pparams p.(pcontext) ×
  Preturn p.(preturn).

Lemma map_predicate_eq_spec {A B} (finst finst' : Instance.t -> Instance.t)
  (f f' g g' : A -> B) h h' (p : predicate A) :
  finst (puinst p) = finst' (puinst p) ->
  map f (pparams p) = map g (pparams p) ->
  h ≐1 h' ->
  f' (preturn p) = g' (preturn p) ->
  map_predicate finst f f' h p = map_predicate finst' g g' h' p.
Proof.
  intros. unfold map_predicate; f_equal; auto.
Qed.
#[global] Hint Resolve map_predicate_eq_spec : all.

Lemma map_predicate_k_eq_spec {A} (finst finst' : Instance.t -> Instance.t)
  (f g : nat -> A -> A) k k' (p : predicate A) :
  finst (puinst p) = finst' (puinst p) ->
  map (f k) (pparams p) = map (g k') (pparams p) ->
  shiftf f k #|pcontext p| (preturn p) = shiftf g k' #|pcontext p| (preturn p) ->
  map_predicate_k finst f k p = map_predicate_k finst' g k' p.
Proof.
  intros. unfold map_predicate_k; f_equal; auto.
Qed.
#[global] Hint Resolve map_predicate_k_eq_spec : all.

Lemma map_decl_id_spec P f d :
  ondecl P d ->
  (forall x : term, P x -> f x = x) ->
  map_decl f d = d.
Proof.
  intros Hc Hf.
  destruct Hc.
  unfold map_decl; destruct d; cbn in *. f_equal; eauto.
  destruct decl_body; simpl; eauto. f_equal.
  eauto.
Qed.

Lemma map_decl_id_spec_cond P p f d :
  ondecl P d ->
  test_decl p d ->
  (forall x : term, P x -> p x -> f x = x) ->
  map_decl f d = d.
Proof.
  intros [].
  unfold map_decl; destruct d; cbn in *.
  unfold test_decl; simpl.
  intros [pty pbody]%andb_and. intros Hx.
  f_equal; eauto.
  destruct decl_body; simpl; eauto. f_equal.
  eauto.
Qed.

Lemma map_context_id_spec P f ctx :
  onctx P ctx ->
  (forall x : term, P x -> f x = x) ->
  map_context f ctx = ctx.
Proof.
  intros Hc Hf. induction Hc; simpl; auto.
  rewrite IHHc. f_equal; eapply map_decl_id_spec; eauto.
Qed.
#[global] Hint Resolve map_context_id_spec : all.

Lemma map_context_id_spec_cond P p f ctx :
  onctx P ctx ->
  test_context p ctx ->
  (forall x : term, P x -> p x -> f x = x) ->
  map_context f ctx = ctx.
Proof.
  intros Hc Hc' Hf. induction Hc in Hc' |- *; simpl; auto.
  revert Hc'; simpl; intros [hx hl]%andb_and.
  rewrite IHHc; auto. f_equal. eapply map_decl_id_spec_cond; eauto.
Qed.
#[global] Hint Resolve map_context_id_spec_cond : all.

Lemma map_predicate_id_spec {A} finst (f f' : A -> A) h (p : predicate A) :
  finst (puinst p) = puinst p ->
  map f (pparams p) = pparams p ->
  h (pcontext p) = pcontext p ->
  f' (preturn p) = preturn p ->
  map_predicate finst f f' h p = p.
Proof.
  unfold map_predicate.
  intros -> -> -> ->; destruct p; auto.
Qed.
#[global] Hint Resolve map_predicate_id_spec : all.

Lemma map_predicate_k_id_spec {A} finst (f : nat -> A -> A) k (p : predicate A) :
  finst (puinst p) = puinst p ->
  map (f k) (pparams p) = pparams p ->
  shiftf f k #|p.(pcontext)| (preturn p) = preturn p ->
  map_predicate_k finst f k p = p.
Proof.
  unfold map_predicate_k, shiftf.
  intros -> -> ->; destruct p; auto.
Qed.
#[global] Hint Resolve map_predicate_k_id_spec : all.

#[global]
Instance map_predicate_proper {term} :
  Proper (`≐1` ==> `≐1` ==> `≐1` ==> Logic.eq ==> Logic.eq)%signature (@map_predicate term term id).
Proof.
  intros eqf0 eqf1 eqf.
  intros eqf'0 eqf'1 eqf' h h' eqh'.
  intros x y ->.
  apply map_predicate_eq_spec; auto.
  now apply map_ext => x.
Qed.

#[global]
Instance map_predicate_proper' {term} f : Proper (`≐1` ==> `≐1` ==> Logic.eq ==> Logic.eq)
  (@map_predicate term term id f).
Proof.
  intros eqf0 eqf1 eqf h h' eqh'.
  intros x y ->.
  apply map_predicate_eq_spec; auto.
Qed.

Lemma shiftf0 {A B} (f : nat -> A -> B) : shiftf f 0 ≐2 f.
Proof. intros x. unfold shiftf. now rewrite Nat.add_0_r. Qed.

#[global]
Hint Rewrite @shiftf0 : map.

Lemma map_predicate_k_map_predicate_k
  (finst finst' : Instance.t -> Instance.t)
  (f f' : nat -> term -> term)
  k k' (p : predicate term) :
  map_predicate_k finst f k (map_predicate_k finst' f' k' p) =
  map_predicate_k (finst ∘ finst') (fun i => f (i + k) ∘ f' (i + k')) 0 p.
Proof.
  unfold map_predicate, map_predicate_k. destruct p; cbn.
  f_equal.
  now rewrite map_map.
  now len.
Qed.
#[global]
Hint Rewrite map_predicate_k_map_predicate_k : map.

Lemma map_predicate_map_predicate_k
  (finst finst' : Instance.t -> Instance.t)
  (f : term -> term) (f' : nat -> term -> term)
  k (p : predicate term) :
  map_predicate finst f f id (map_predicate_k finst' f' k p) =
  map_predicate_k (finst ∘ finst') (fun k => f ∘ f' k) k p.
Proof.
  unfold map_predicate, map_predicate_k. destruct p; cbn.
  f_equal.
  apply map_map.
Qed.
#[global]
Hint Rewrite map_predicate_map_predicate_k : map.

Lemma map_predicate_k_map_predicate
  (finst finst' : Instance.t -> Instance.t)
  (f' : term -> term) (f : nat -> term -> term)
  k (p : predicate term) :
  map_predicate_k finst f k (map_predicate finst' f' f' id p) =
  map_predicate_k (finst ∘ finst') (fun k => (f k) ∘ f') k p.
Proof.
  unfold map_predicate, map_predicate_k. destruct p; cbn.
  f_equal; len; auto.
  * apply map_map.
Qed.
#[global]
Hint Rewrite map_predicate_k_map_predicate : map.

Lemma map_branch_map_branch
      {term term' term''}
      (f : term' -> term'')
      (f' : term -> term')
      h h'
      (b : branch term) :
  map_branch f h (map_branch f' h' b) =
  map_branch (f ∘ f') (h ∘ h') b.
Proof.
  unfold map_branch; destruct b; cbn.
  f_equal.
Qed.
#[global]
Hint Rewrite @map_branch_map_branch : map.

Lemma map_branch_k_map_branch_k (f f' : nat -> term -> term) h h' k k' (b : branch term) :
  #|h' b.(bcontext)| = #|b.(bcontext)| ->
  map_branch_k f h k (map_branch_k f' h' k' b) =
  map_branch_k (fun i => f (i + k) ∘ f' (i + k')) (h ∘ h') 0 b.
Proof.
  unfold map_branch, map_branch_k; destruct b; cbn. len.
  intros ->.
  f_equal.
Qed.

Lemma map_branch_k_map_branch_k_id (f f' : nat -> term -> term) k k' (b : branch term) :
  map_branch_k f id k (map_branch_k f' id k' b) =
  map_branch_k (fun i => f (i + k) ∘ f' (i + k')) id 0 b.
Proof.
  unfold map_branch, map_branch_k; destruct b; cbn. len.
  f_equal.
Qed.
#[global]
Hint Rewrite map_branch_k_map_branch_k_id : map.

Lemma map_branch_map_branch_k
      (f : term -> term)
      (f' : nat -> term -> term) k
      (b : branch term) :
  map_branch f id (map_branch_k f' id k b) =
  map_branch_k (fun k => f ∘ (f' k)) id k b.
Proof.
  unfold map_branch, map_branch_k; destruct b; cbn.
  f_equal.
Qed.

#[global]
Hint Rewrite map_branch_map_branch_k : map.
Lemma map_branch_k_map_branch
      (f' : term -> term)
      (f : nat -> term -> term) k
      (b : branch term) :
  map_branch_k f id k (map_branch f' id b) =
  map_branch_k (fun k => f k ∘ f') id k b.
Proof.
  unfold map_branch, map_branch_k; destruct b; cbn. len.
  f_equal.
Qed.

#[global]
Hint Rewrite map_branch_k_map_branch : map.

Lemma map_branch_id x : map_branch (@id term) id x = id x.
Proof.
  unfold map_branch, id; destruct x; cbn.
  f_equal.
Qed.
#[global]
Hint Rewrite @map_branch_id : map.

Lemma map_decl_eq_spec {A B} {P : A -> Type} {d} {f g : A -> B} :
  ondecl P d ->
  (forall x, P x -> f x = g x) ->
  map_decl f d = map_decl g d.
Proof.
  destruct d; cbn; intros [Pty Pbod] Hfg.
  unfold map_decl; cbn in *; f_equal.
  * destruct decl_body; cbn in *; eauto. f_equal.
    eauto.
  * eauto.
Qed.

Lemma map_context_eq_spec {A B} P (f g : A -> B) ctx :
  onctx P ctx ->
  (forall x, P x -> f x = g x) ->
  map_context f ctx = map_context g ctx.
Proof.
  intros onc Hfg.
  induction onc; simpl; auto.
  rewrite IHonc. f_equal.
  eapply map_decl_eq_spec; eauto.
Qed.

Lemma map_branch_eq_spec {A B} (f g : A -> B) h h' (x : branch A) :
  f (bbody x) = g (bbody x) ->
  h ≐1 h' ->
  map_branch f h x = map_branch g h' x.
Proof.
  intros. unfold map_branch; f_equal; auto.
Qed.
#[global] Hint Resolve map_branch_eq_spec : all.

Lemma map_branch_k_eq_spec {A B} (f g : nat -> A -> B) h h' k k' (x : branch A) :
  shiftf f k #|x.(bcontext)| (bbody x) = shiftf g k' #|x.(bcontext)| (bbody x) ->
  h ≐1 h' ->
  map_branch_k f h k x = map_branch_k g h' k' x.
Proof.
  intros. unfold map_branch_k; f_equal; auto.
Qed.
#[global] Hint Resolve map_branch_eq_spec : all.

#[global]
Instance map_branch_proper {term} : Proper (`≐1` ==> `≐1` ==> Logic.eq ==> Logic.eq)
  (@map_branch term term).
Proof.
  intros eqf0 eqf1 eqf h h' eqh'.
  intros x y ->.
  apply map_branch_eq_spec; auto.
Qed.

Lemma id_id {A} : @id A ≐1 id.
Proof. now intros x. Qed.
#[global] Hint Resolve id_id : core.

Lemma map_branch_id_spec (f : term -> term) (x : branch term) :
  f (bbody x) = (bbody x) ->
  map_branch f id x = x.
Proof.
  intros. rewrite (map_branch_eq_spec _ id id id); auto.
  now rewrite map_branch_id.
Qed.
#[global] Hint Resolve map_branch_id_spec : all.

Lemma map_branch_k_id_spec (f : nat -> term -> term) h k (x : branch term) :
  h (bcontext x) = bcontext x ->
  shiftf f k #|x.(bcontext)| (bbody x) = (bbody x) ->
  map_branch_k f h k x = x.
Proof.
  intros. unfold map_branch_k.
  destruct x; simpl in *; f_equal; eauto.
Qed.
#[global] Hint Resolve map_branch_k_id_spec : all.

Lemma map_branches_map_branches
      {term term' term''}
      (f : term' -> term'')
      (f' : term -> term')
      h h'
      (l : list (branch term)) :
  map (fun b => map_branch f h (map_branch f' h' b)) l =
  map (map_branch (f ∘ f') (h ∘ h')) l.
Proof.
  eapply map_ext => b. apply map_branch_map_branch.
Qed.

Lemma mapu_prim_compose {term term' term''}
  f (g : term' -> term'') f' (g' : term -> term') : mapu_prim f g ∘ mapu_prim f' g' ≐1 mapu_prim (f ∘ f') (g ∘ g').
Proof.
  intros [? []]; cbn => //. do 3 f_equal.
  unfold mapu_array_model; destruct a => //=. now rewrite map_map_compose.
Qed.

Lemma mapu_prim_compose_rew {term term' term''}
  f (g : term' -> term'') f' (g' : term -> term') :
  forall x, mapu_prim f g (mapu_prim f' g' x) = mapu_prim (f ∘ f') (g ∘ g') x.
Proof. intros x. now rewrite (mapu_prim_compose _ _ _ _ x). Qed.

#[global] Hint Rewrite @mapu_prim_compose_rew : map.

Lemma prim_val_tag_map {term term'} (p : PCUICPrimitive.prim_val term) fu (ft : term -> term') :
  prim_val_tag (mapu_prim fu ft p) = prim_val_tag p.
Proof.
  destruct p as [? []] => //.
Qed.

Lemma mapu_array_model_proper {term term'} (l l' : Level.t -> Level.t) (f g : term -> term') a :
  l ≐1 l' -> f ≐1 g ->
  mapu_array_model l f a = mapu_array_model l' g a.
Proof.
  destruct a; cbn ; rewrite /mapu_array_model /=. intros; f_equal; eauto. now eapply map_ext.
Qed.

Lemma mapu_array_model_proper_cond {term term'} (P : term -> Type) (l l' : Level.t -> Level.t) (f g : term -> term') a :
  l ≐1 l' -> (forall x, P x -> f x = g x) ->
  P a.(array_type) × P a.(array_default) × All P a.(array_value) ->
  mapu_array_model l f a = mapu_array_model l' g a.
Proof.
  destruct a; cbn ; rewrite /mapu_array_model /=. intros hl hf [? []]; f_equal; eauto.
  induction a; cbn => //. rewrite IHa. rewrite hf //.
Qed.

Lemma primProp_map_eq {term term'} P p l l' (f g : term -> term') :
  tPrimProp P p ->
  l ≐1 l' ->
  (forall x, P x -> f x = g x) ->
  mapu_prim l f p = mapu_prim l' g p.
Proof.
  destruct p as [? []]; cbn => //.
  intros [? []] hl hp. do 2 f_equal.
  eapply mapu_array_model_proper_cond; tea. intuition auto.
Qed.

Lemma primProp_map_id {term} P p (f : term -> term) :
  tPrimProp P p ->
  (forall x, P x -> f x = x) ->
  map_prim f p = p.
Proof.
  intros hp hf.
  rewrite (primProp_map_eq P p id id f id) //.
  destruct p as [? []]; cbn => //.
  destruct a => //=. rewrite /mapu_array_model /=. rewrite map_id //.
Qed.

Lemma test_prim_primProp {term} {P p} : @test_prim term P p -> tPrimProp P p.
Proof.
  destruct p as [? []]; cbn => //.
  move/andP => [] /andP[]. intuition auto.
  now eapply forallb_All in a0.
Qed.

Lemma primProp_test_prim {P : term -> bool} {p} : tPrimProp P p -> test_prim P p.
Proof.
  destruct p as [? []]; cbn => //. intros. rtoProp.
  intuition auto.
  now eapply All_forallb.
Qed.

Lemma tPrimProp_impl {term} {P Q : term -> Type} {p} : tPrimProp P p -> (forall x, P x -> Q x) -> tPrimProp Q p.
Proof.
  intros hp hpq; destruct p as [? []]; cbn in * => //. intuition auto.
  eapply All_impl; tea.
Qed.

Lemma tPrimProp_prod {term} {P Q : term -> Type} {p} : tPrimProp P p -> tPrimProp Q p -> tPrimProp (fun x => P x × Q x) p.
Proof.
  destruct p as [? []]; cbn => //. intuition auto.
  now eapply All_prod.
Qed.

Lemma primProp_map {term} (P : term -> Type) f (p : PCUICPrimitive.prim_val term) :
  tPrimProp (fun x => P (f x)) p ->
  tPrimProp P (map_prim f p).
Proof.
  destruct p as [? []]; cbn => //. intuition eauto. now eapply All_map.
Qed.

Lemma primProp_map_inv {term} (P : term -> Type) f (p : PCUICPrimitive.prim_val term) :
  tPrimProp P (map_prim f p) ->
  tPrimProp (fun x => P (f x)) p.
Proof.
  destruct p as [? []]; cbn => //. intuition eauto; now eapply All_map_inv.
Qed.

Lemma primProp_mapu_id {P : term -> Type} {pu put} p f g :
  tPrimProp P p -> test_primu pu put p ->
  (forall u, pu u -> f u = u) ->
  (forall t, P t -> put t -> g t = t) ->
  mapu_prim f g p = p.
Proof.
  intros hp ht hf hg.
  destruct p as [? []]; cbn => //. f_equal. f_equal.
  destruct a; destruct hp; cbn in *. unfold mapu_array_model; cbn.
  rtoProp. destruct p0. f_equal; intuition eauto.
  eapply forallb_All in H2. eapply All_prod in a; tea.
  eapply All_map_id, All_impl; tea. intuition eauto. apply hg; intuition auto.
Qed.

Lemma test_primu_test_primu_tPrimProp {P : term -> Type} {pu put} {pu' : Level.t -> bool} {put' : term -> bool} p f g :
  tPrimProp P p -> test_primu pu put p ->
  (forall u, pu u -> pu' (f u)) ->
  (forall t, P t -> put t -> put' (g t)) ->
  test_primu pu' put' (mapu_prim f g p).
Proof.
  intros hp ht hf hg.
  destruct p as [? []]; cbn => //.
  destruct a; destruct hp; cbn in *.
  rtoProp. destruct p0. intuition eauto.
  eapply forallb_All in H2. eapply All_prod in a; tea.
  eapply All_forallb, All_map, All_impl; tea. intuition eauto. apply hg; intuition auto.
Qed.

Lemma test_prim_mapu {term term'} {put : term' -> bool} {l} {f : term -> term'} {p} :
  test_prim put (mapu_prim l f p) = test_prim (fun x => put (f x)) p.
Proof.
  destruct p as [? []]; cbn; eauto.
  now rewrite forallb_map.
Qed.
#[global] Hint Rewrite @test_prim_mapu : map.

Lemma test_prim_eq_spec {P : term -> Type} {put} {put' : term -> bool} p :
  tPrimProp P p ->
  (forall t, P t -> put t = put' t) ->
  test_prim put p = test_prim put' p.
Proof.
  destruct p as [? []]; cbn => //. intuition eauto.
  f_equal; eauto. f_equal; eauto.
  eapply All_forallb_eq_forallb; tea.
Qed.

Definition tCaseBrsProp {A} (P : A -> Type) (l : list (branch A)) :=
  All (fun x => onctx P (bcontext x) × P (bbody x)) l.

Definition tCaseBrsProp_k (P : nat -> term -> Type) (p : predicate term) k (l : list (branch term)) :=
  All (fun x => onctx_k P (#|p.(pparams)|) (bcontext x) × P (#|x.(bcontext)| + k) (bbody x)) l.

Lemma map_branches_k_map_branches_k
      {term term' term''}
      (f : nat -> term' -> term'')
      (g : term -> term')
      (f' : nat -> term -> term')
      h h' k
      (l : list (branch term)) :
  (forall ctx, #|h' ctx| = #|ctx|) ->
  map (fun b => map_branch (f #|bcontext (map_branch g h' b)|) h (map_branch (f' k) h' b)) l =
  map (fun b => map_branch (f #|bcontext b|) h (map_branch (f' k) h' b)) l.
Proof.
  intros Hh.
  eapply map_ext => b. rewrite map_branch_map_branch.
  rewrite map_branch_map_branch.
  simpl; autorewrite with len. now rewrite Hh.
Qed.

Lemma case_brs_map_spec {A B} {P : A -> Type} {l} {f g : A -> B}
  {h h' : list (BasicAst.context_decl A) -> list (BasicAst.context_decl B)} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) -> h ≐1 h' ->
  map_branches f h l = map_branches g h' l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  destruct X0.
  apply map_branch_eq_spec; eauto.
Qed.

Lemma map_decl_eqP_spec {A B} {P : A -> Type} {p : A -> bool}
   {d} {f g : A -> B} :
  ondecl P d ->
  test_decl p d ->
  (forall x, P x -> p x -> f x = g x) ->
  map_decl f d = map_decl g d.
Proof.
  destruct d; cbn; intros [Pty Pbod] [pty pbody]%andb_and Hfg.
  unfold map_decl; cbn in *; f_equal.
  * destruct decl_body; cbn in *; eauto. f_equal.
    eauto.
  * eauto.
Qed.

Lemma map_context_eqP_spec {A B} {P : A -> Type} {p : A -> bool}
   {ctx} {f g : A -> B} :
  All (ondecl P) ctx ->
  test_context p ctx ->
  (forall x, P x -> p x -> f x = g x) ->
  map_context f ctx = map_context g ctx.
Proof.
  intros Ha Hctx Hfg. induction Ha; simpl; auto.
  revert Hctx; simpl; intros [Hx Hl]%andb_and.
  rewrite IHHa; f_equal; auto.
  eapply map_decl_eqP_spec; eauto.
Qed.

Lemma mapi_context_eqP_spec {A B} {P : A -> Type} {ctx} {f g : nat -> A -> B} :
  All (ondecl P) ctx ->
  (forall k x, P x -> f k x = g k x) ->
  mapi_context f ctx = mapi_context g ctx.
Proof.
  intros Ha Hfg. induction Ha; simpl; auto.
  rewrite IHHa; f_equal.
  destruct p as [Hty Hbody].
  unfold map_decl; destruct x ; cbn in *; f_equal.
  * destruct decl_body; cbn in *; auto.
    f_equal. eauto.
  * eauto.
Qed.

Lemma mapi_context_eqP_id_spec {A} {P : A -> Type} {ctx} {f : nat -> A -> A} :
  All (ondecl P) ctx ->
  (forall k x, P x -> f k x = x) ->
  mapi_context f ctx = ctx.
Proof.
  intros Ha Hfg. induction Ha; simpl; auto.
  rewrite IHHa; f_equal.
  destruct p as [Hty Hbody].
  unfold map_decl; destruct x ; cbn in *; f_equal.
  * destruct decl_body; cbn in *; auto.
    f_equal. eauto.
  * eauto.
Qed.

Lemma mapi_context_eqP_test_id_spec {A} {P : A -> Type} (p : nat -> A -> bool)
  k {ctx} {f : nat -> A -> A} :
  All (ondecl P) ctx ->
  test_context_k p k ctx ->
  (forall k (x : A), P x -> p k x -> f k x = x) ->
  mapi_context (shiftf f k) ctx = ctx.
Proof.
  intros Ha ht Hfg. revert ht.
  induction Ha; simpl; auto.
  intros [hl [hty hbod]%andb_and]%andb_and.
  rewrite IHHa; auto; f_equal.
  destruct p0 as [Hty Hbody].
  unfold map_decl; destruct x ; cbn in *; f_equal; eauto.
  destruct decl_body; cbn in *; auto.
  f_equal. unfold shiftf. eapply Hfg; auto.
Qed.

Lemma test_context_k_eqP_id_spec {A} {P : A -> Type} (p q : nat -> A -> bool) k k' {ctx} :
  All (ondecl P) ctx ->
  test_context_k p k ctx ->
  (forall i (x : A), P x -> p (i + k) x -> q (i + k') x) ->
  test_context_k q k' ctx.
Proof.
  intros Ha ht Hfg. revert ht.
  induction Ha; simpl; auto.
  intros [hl [hty hbod]%andb_and]%andb_and.
  rewrite IHHa; simpl; auto.
  destruct p0 as [Hty Hbody].
  unfold test_decl; destruct x ; cbn in *; eauto.
  destruct decl_body; cbn in *; auto.
  rewrite !Hfg; auto.
Qed.

Lemma test_context_k_eqP_eq_spec {A} {P : A -> Type} (p q : nat -> A -> bool) k k' {ctx} :
  All (ondecl P) ctx ->
  (forall i (x : A), P x -> p (i + k) x = q (i + k') x) ->
  test_context_k p k ctx = test_context_k q k' ctx.
Proof.
  intros Ha Hfg.
  induction Ha; simpl; auto.
  rewrite IHHa; auto; f_equal.
  destruct p0 as [Hty Hbody].
  unfold test_decl; destruct x ; cbn in *; f_equal; eauto.
  destruct decl_body; cbn in *; auto;
  rewrite !Hfg; auto.
Qed.

Lemma test_context_k_eq_spec (p q : nat -> term -> bool) k k' {ctx} :
  (p ≐2 q) ->
  k = k' ->
  test_context_k p k ctx = test_context_k q k' ctx.
Proof.
  intros Hfg <-.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; now rewrite IHctx Hfg.
Qed.

Lemma test_context_k_eq (p : nat -> term -> bool) n ctx :
  test_context_k p n ctx = alli (fun k d => test_decl (p (n + k)) d) 0 (List.rev ctx).
Proof.
  induction ctx; simpl; auto.
  rewrite IHctx alli_app /= andb_comm andb_true_r andb_comm. f_equal.
  len. now rewrite Nat.add_comm.
Qed.

#[global]
Instance test_context_k_Proper : Proper (`≐2` ==> Logic.eq ==> `≐1`) (@test_context_k term).
Proof.
  intros f g Hfg k k' <- ctx.
  now apply test_context_k_eq_spec.
Qed.

#[global]
Instance test_predicate_k_Proper : Proper (`≐1` ==> `≐2` ==> Logic.eq ==> `≐1`) (@test_predicate_k term).
Proof.
  intros hi hi' eqhi f g Hfg k k' <- ctx.
  unfold test_predicate_k. rewrite eqhi.
  now setoid_rewrite Hfg.
Qed.

#[global]
Instance test_predicate_ku_Proper : Proper (`≐2` ==> `≐2` ==> Logic.eq ==> `≐1`) (@test_predicate_ku term).
Proof.
  intros hi hi' eqhi f g Hfg k k' <- ctx.
  unfold test_predicate_ku. rewrite eqhi.
  now setoid_rewrite Hfg.
Qed.

#[global]
Instance test_branch_k_Proper p : Proper (`≐2` ==> Logic.eq ==> `≐1`) (@test_branch_k term p).
Proof.
  intros f g Hfg k k' <- ctx.
  unfold test_branch_k.
  now setoid_rewrite Hfg.
Qed.

Lemma case_brs_map_spec_cond {A B} {P : A -> Type} pctx p {l} {f g : A -> B} {h h'}:
  tCaseBrsProp P l ->
  forallb (test_branch pctx p) l ->
  (forall x, P x -> p x -> f x = g x) ->
  (* (forall ctx, onctx P ctx -> test_context pctx ctx -> h ctx = h' ctx) -> *)
  h ≐1 h' ->
  map_branches f h l = map_branches g h' l.
Proof.
  intros. red in X.
  eapply forallb_All in H.
  eapply All_map_eq.
  eapply All_prod in X; tea. clear H.
  eapply All_impl; eauto. simpl; intros br [[]%andb_and []].
  apply map_branch_eq_spec; eauto.
  (*eapply map_context_eqP_spec; eauto.*)
Qed.

Lemma case_brs_map_k_spec {A B} {P : A -> Type} {k l} {f g : nat -> A -> B} {h h'} :
  tCaseBrsProp P l ->
  (forall k x, P x -> f k x = g k x) ->
  h ≐1 h' ->
  map_branches_k f h k l = map_branches_k g h' k l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  apply map_branch_k_eq_spec; eauto.
  unfold shiftf. now apply H.
Qed.

Lemma case_brs_forallb_map_spec {A B} {P : A -> Type} {pctx p : A -> bool}
      {l} {f g : A -> B} {h h'} :
  tCaseBrsProp P l ->
  forallb (test_branch pctx p) l ->
  (forall x, P x -> p x -> f x = g x) ->
  h ≐1 h' ->
  map (map_branch f h) l = map (map_branch g h') l.
Proof.
  intros.
  eapply All_map_eq. red in X. apply forallb_All in H.
  eapply All_impl. eapply All_prod. exact X. exact H. simpl.
  intros [bctx bbod] [Hbr hb]. cbn in *.
  unfold map_branch; cbn. f_equal.
  - apply H1.
  - eapply H0; eauto. apply Hbr.
    now move/andb_and: hb => [].
Qed.

Lemma test_context_map (p : term -> bool) f (ctx : context) :
  test_context p (map_context f ctx) = test_context (p ∘ f) ctx.
Proof.
  induction ctx; simpl; auto.
  rewrite IHctx. f_equal.
  now rewrite test_decl_map_decl.
Qed.
#[global]
Hint Rewrite test_context_map : map.

Lemma test_context_app (p : term -> bool) Γ Δ :
  test_context p (Γ ,,, Δ) = test_context p Γ && test_context p Δ.
Proof using Type.
  induction Δ; simpl; auto.
  - now rewrite andb_true_r.
  - now rewrite IHΔ andb_assoc.
Qed.

Lemma onctx_test P (p q : term -> bool) ctx :
  onctx P ctx ->
  test_context p ctx ->
  (forall t, P t -> p t -> q t) ->
  test_context q ctx.
Proof.
  intros Hc tc HP. revert tc.
  induction Hc; simpl; auto.
  destruct p0.
  intros [pl [pbod pty]%andb_and]%andb_and.
  rewrite (IHHc pl); simpl.
  unfold test_decl.
  rewrite (HP _ p0 pty) andb_true_r; simpl.
  destruct (decl_body x); simpl in *; eauto.
Qed.

(** Useful for inductions *)
Lemma onctx_k_rev {P : nat -> term -> Type} {k} {ctx} :
  onctx_k P k ctx <~>
  Alli (fun i => ondecl (P (i + k))) 0 (List.rev ctx).
Proof.
  split.
  - unfold onctx_k.
    intros Hi.
    eapply forall_nth_error_Alli => i x hx.
    pose proof (nth_error_Some_length hx).
    rewrite nth_error_rev // in hx.
    rewrite List.rev_involutive in hx.
    len in hx.
    eapply Alli_nth_error in Hi; tea.
    simpl in Hi. simpl.
    replace (Nat.pred #|ctx| - (#|ctx| - S i) + k) with (i + k) in Hi => //.
    len in H; by lia.
  - intros Hi.
    eapply forall_nth_error_Alli => i x hx.
    eapply Alli_rev_nth_error in Hi; tea.
    simpl.
    replace (#|ctx| - S i + k) with (Nat.pred #|ctx| - i + k) in Hi => //.
    lia.
Qed.

Lemma onctx_k_shift {P : nat -> term -> Type} {k} {ctx} :
  onctx_k P k ctx ->
  onctx_k (fun k' => P (k' + k)) 0 ctx.
Proof.
  intros Hi%onctx_k_rev.
  eapply onctx_k_rev.
  eapply Alli_impl; tea => /= n x.
  now rewrite Nat.add_0_r.
Qed.

Lemma onctx_k_P {P : nat -> term -> Type} {p : nat -> term -> bool} {k} {ctx : context} :
  (forall x y, reflectT (P x y) (p x y)) ->
  reflectT (onctx_k P k ctx) (test_context_k p k ctx).
Proof.
  intros HP.
  eapply equiv_reflectT.
  - intros Hi%onctx_k_rev.
    rewrite test_context_k_eq.
    induction Hi; simpl; auto.
    rewrite Nat.add_comm.
    rewrite IHHi /= //.
    now move/(ondeclP (HP _)): p0 => ->.
  - intros Hi. eapply onctx_k_rev.
    move: ctx Hi. induction ctx.
    * constructor.
    * move => /= /andb_and [Hctx Hd].
      eapply Alli_app_inv; eauto. constructor.
      + move/(ondeclP (HP _)): Hd. now len.
      + constructor.
Qed.

Module PCUICLookup := EnvironmentTyping.Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.

Derive NoConfusion for global_decl.

Module PCUICGlobalMaps := EnvironmentTyping.GlobalMaps
  PCUICTerm
  PCUICEnvironment
  PCUICTermUtils
  PCUICEnvTyping
  PCUICConversion
  PCUICLookup
.
Include PCUICGlobalMaps.

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universes_decl }.

Record definition_entry := {
  definition_entry_type      : term;
  definition_entry_body      : term;
  definition_entry_universes : universes_decl;
  definition_entry_opaque    : bool }.

Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

Derive NoConfusion for parameter_entry definition_entry constant_entry.

(** *** Inductive entries *)

(** This is the representation of mutual inductives.
    nearly copied from [kernel/entries.mli]

  Assume the following definition in concrete syntax:

[[
  Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
  ...
  with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1  ... | cpnp : Tpnp.
]]

  then, in [i]th block, [mind_entry_params] is [xn:Xn;...;x1:X1];
  [mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
  [mind_entry_lc] is [Ti1;...;Tini], defined in context
  [A'1;...;A'p;x1:X1;...;xn:Xn] where [A'i] is [Ai] generalized over
  [x1:X1;...;xn:Xn].
*)

Inductive local_entry :=
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.

Record one_inductive_entry := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term (* constructor list *) }.

Record mutual_inductive_entry := {
  mind_entry_record    : option (option ident);
  (* Is this mutual inductive defined as a record?
     If so, is it primitive, using binder name [ident]
     for the record in primitive projections ? *)
  mind_entry_finite    : recursivity_kind;
  mind_entry_params    : context;
  mind_entry_inds      : list one_inductive_entry;
  mind_entry_universes : universes_decl;
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by.Common Rocq yet. *) }.

Derive NoConfusion for local_entry one_inductive_entry mutual_inductive_entry.
