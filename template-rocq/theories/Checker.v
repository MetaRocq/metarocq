(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Environment uGraph.
From MetaRocq.Template Require Import Ast AstUtils LiftSubst UnivSubst Typing.
Import MRMonadNotation.

(** * Rocq type-checker for kernel terms

  Implemets [typecheck_program] which returns an error and
  on success should guarantee that the term has the given type.
  Currently uses fuel to implement reduction and is unverified.

  This file implements reduction with a stack machine [reduce_stack],
  conversion/cumulativity with the first-order fast-path heuristic [isconv]
  that are used to type-check terms in reasonable time. *)


Local Notation " () " := Datatypes.unit : type_scope.
Local Notation " () " := tt.

Module RedFlags.

  Record t := mk
    { beta : bool;
      iota : bool;
      zeta : bool;
      delta : bool;
      fix_ : bool;
      cofix_ : bool }.

  Definition default := mk true true true true true true.
End RedFlags.


Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundMeta (m : nat)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : kername)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotConvertible (Γ : context) (t u t' u' : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| UnsatisfiableConstraints (c : ConstraintSet.t)
| NotEnoughFuel (n : nat)
| NotSupported (s : string).

Definition string_of_type_error (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unboound rel " ^ string_of_nat n
  | UnboundVar id => "Unbound var " ^ id
  | UnboundMeta m => "Unbound meta " ^ string_of_nat m
  | UnboundEvar ev => "Unbound evar " ^ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ^ string_of_kername c
  | UndeclaredInductive c => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | NotConvertible Γ t u t' u' => "Terms are not convertible: " ^
      string_of_term t ^ " " ^ string_of_term u ^ " after reduction: " ^
      string_of_term t' ^ " " ^ string_of_term u'
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | UnsatisfiableConstraints c => "Unsatisfiable constraints"
  | NotEnoughFuel n => "Not enough fuel"
  | NotSupported s => s ^ " are not supported"
  end.

Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Global Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

Global Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.

Section Lookups.
  Context (Σ : global_env).

  Definition polymorphic_constraints u :=
    match u with
    | Monomorphic_ctx => ConstraintSet.empty
    | Polymorphic_ctx ctx => (AUContext.repr ctx).2.2
    end.

  Definition lookup_constant_type cst u :=
    match lookup_env Σ cst with
    | Some (ConstantDecl {| cst_type := ty; cst_universes := uctx |}) =>
      ret (subst_instance u ty)
    |  _ => raise (UndeclaredConstant cst)
    end.

  Definition lookup_constant_type_cstrs cst u :=
    match lookup_env Σ cst with
    | Some (ConstantDecl {| cst_type := ty; cst_universes := uctx |}) =>
      let cstrs := polymorphic_constraints uctx in
      ret (subst_instance u ty, subst_instance_cstrs u cstrs)
      |  _ => raise (UndeclaredConstant cst)
    end.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl mdecl) =>
      match nth_error mdecl.(ind_bodies) i with
      | Some body => ret (mdecl, body)
      | None => raise (UndeclaredInductive (mkInd ind i))
      end
    | _ => raise (UndeclaredInductive (mkInd ind i))
    end.

  Definition lookup_ind_type ind i (u : list Level.t) :=
    res <- lookup_ind_decl ind i ;;
    ret (subst_instance u (snd res).(ind_type)).

  Definition lookup_ind_type_cstrs ind i (u : list Level.t) :=
    res <- lookup_ind_decl ind i ;;
    let '(mib, body) := res in
    let uctx := mib.(ind_universes) in
    let cstrs := polymorphic_constraints uctx in
    ret (subst_instance u body.(ind_type), subst_instance_cstrs u cstrs).

  Definition lookup_constructor_decl ind i k :=
    res <- lookup_ind_decl ind i;;
    let '(mib, body) := res in
    match nth_error body.(ind_ctors) k with
    | Some cdecl => ret (mib, cdecl)
    | None => raise (UndeclaredConstructor (mkInd ind i) k)
    end.

  Definition lookup_constructor_type ind i k u :=
    res <- lookup_constructor_decl ind i k ;;
    let '(mib, cdecl) := res in
    ret (subst0 (inds ind u mib.(ind_bodies)) (subst_instance u cdecl.(cstr_type))).

  Definition lookup_constructor_type_cstrs ind i k u :=
    res <- lookup_constructor_decl ind i k ;;
    let '(mib, cdecl) := res in
    let cstrs := polymorphic_constraints mib.(ind_universes) in
    ret (subst0 (inds ind u mib.(ind_bodies)) (subst_instance u cdecl.(cstr_type)),
        subst_instance_cstrs u cstrs).
End Lookups.

Section Reduce.
  Context (flags : RedFlags.t) (Σ : global_env).

  Definition zip (t : term * list term) := mkApps (fst t) (snd t).

  Fixpoint reduce_stack (Γ : context) (n : nat) (t : term) (stack : list term)
    : option (term * list term) :=
  match n with 0 => None | S n =>
  match t with

  | tRel c =>
    if RedFlags.zeta flags then
      d <- nth_error Γ c ;;
      match d.(decl_body) with
      | None => ret (t, stack)
      | Some b => reduce_stack Γ n (lift0 (S c) b) stack
      end
    else ret (t, stack)

  | tLetIn _ b _ c =>
    if RedFlags.zeta flags then
      reduce_stack Γ n (subst10 b c) stack
    else ret (t, stack)

  | tConst c u =>
    if RedFlags.delta flags then
      match lookup_env Σ c with
      | Some (ConstantDecl {| cst_body := Some body |}) =>
        let body' := subst_instance u body in
        reduce_stack Γ n body' stack
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  | tApp f args => reduce_stack Γ n f (args ++ stack)

  | tLambda na ty b =>
    if RedFlags.beta flags then
      match stack with
      | a :: args' =>
        (** CBN reduction: we do not reduce arguments before substitution *)
        (* a' <- reduce_stack Γ n a [] ;; *)
        reduce_stack Γ n (subst10 a b) args'
      | _ => ret (t, stack)
               (*  b' <- reduce_stack (Γ ,, vass na ty) n b stack ;; *)
               (* ret (tLambda na ty (zip b'), stack) *)
      end
    else ret (t, stack)

  | tFix mfix idx =>
    if RedFlags.fix_ flags then
      nf <- unfold_fix mfix idx ;;
      let '(narg, fn) := nf in
      match  List.nth_error stack narg with
      | Some c =>
        c' <- reduce_stack Γ n c [] ;;
        match fst c' with
        | tConstruct _ _ _ => reduce_stack Γ n fn stack
        | _ => ret (t, stack)
        end
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  | tProd _ _ _ => ret (t, stack)

    (* b' <- reduce_stack Γ n b [] ;; *)
    (* t' <- reduce_stack (Γ ,, vass na (zip b')) n t [] ;; *)
    (* ret (tProd na (zip b') (zip t'), stack) *)

  | tCast c _ _ => reduce_stack Γ n c stack

  | tCase ci p c brs =>
    if RedFlags.iota flags then
      c' <- reduce_stack Γ n c [] ;;
      match c' with
      | (tConstruct ind c _, args) =>
        match nth_error brs c with
        | Some br =>
          match lookup_constructor_decl Σ (inductive_mind ind) (inductive_ind ind) c with
          | Checked (mdecl, cdecl) =>
            let bctx := case_branch_context ind mdecl cdecl p br in
              reduce_stack Γ n (iota_red ci.(ci_npar) args bctx br) stack
          | TypeError e => ret (t, stack)
          end
        | None => ret (tCase ci p (zip c') brs, stack)
        end
      | _ => ret (tCase ci p (zip c') brs, stack)
      end
    else ret (t, stack)

  | _ => ret (t, stack)

  end
  end.

  Definition reduce_stack_term Γ n c :=
    res <- reduce_stack Γ n c [] ;;
    ret (zip res).

  Definition fix_decls (l : mfixpoint term) :=
    let fix aux acc ds :=
        match ds with
        | nil => acc
        | d :: ds => aux (vass d.(dname) d.(dtype) :: acc) ds
        end
    in aux [] l.

  Definition rebuild_case_predicate_ctx ind (p : predicate term) : context :=
    match lookup_ind_decl Σ (inductive_mind ind) (inductive_ind ind) with
    | TypeError _ => []
    | Checked (mib, oib) => case_predicate_context ind mib oib p
    end.

  Definition map_context_with_binders (f : context -> term -> term) (c : context) Γ : context :=
    fold_left (fun acc decl => map_decl (f (Γ ,,, acc)) decl :: acc) (List.rev c) [].

  Definition map_predicate_with_binders (f : context -> term -> term) Γ ind (p : predicate term) :=
    let pctx := rebuild_case_predicate_ctx ind p in
    let Γparams := map_context_with_binders f pctx Γ in
    {| pparams := map (f Γ) p.(pparams);
       puinst := p.(puinst);
       pcontext := p.(pcontext);
       preturn := f (Γparams  ++ Γ) (preturn p) |}.

  Definition rebuild_case_branch_ctx ind i p br :=
    match lookup_constructor_decl Σ (inductive_mind ind) (inductive_ind ind) i with
    | TypeError _ => []
    | Checked (mib, cdecl) => case_branch_context ind mib cdecl p br
    end.

  Definition map_case_branch_with_binders ind i (f : context -> term -> term) Γ p br :=
    let ctx := rebuild_case_branch_ctx ind i p br in
    map_branch (f (Γ ,,, ctx)) br.
  
  Definition map_constr_with_binders (f : context -> term -> term) Γ (t : term) : term :=
    match t with
    | tRel i => t
    | tEvar ev args => tEvar ev (List.map (f Γ) args)
    | tLambda na T M =>
        let T' := f Γ T in
        tLambda na T' (f (Γ,, vass na T') M)
    | tApp u v => tApp (f Γ u) (List.map (f Γ) v)
    | tProd na A B =>
      let A' := f Γ A in
      tProd na A' (f (Γ ,, vass na A') B)
    | tCast c kind t => tCast (f Γ c) kind (f Γ t)
    | tLetIn na b t c =>
      let b' := f Γ b in
      let t' := f Γ t in
      tLetIn na b' t' (f (Γ ,, vdef na b' t') c)
    | tCase ci p c brs =>
      let p' := map_predicate_with_binders f Γ ci.(ci_ind) p in
      let brs' := mapi (fun i x => map_case_branch_with_binders ci.(ci_ind) i f Γ p' x) brs in
      tCase ci p' (f Γ c) brs'
    | tProj p c => tProj p (f Γ c)
    | tFix mfix idx =>
      let Γ' := fix_decls mfix ++ Γ in
      let mfix' := List.map (map_def (f Γ) (f Γ')) mfix in
      tFix mfix' idx
    | tCoFix mfix k =>
      let Γ' := fix_decls mfix ++ Γ in
      let mfix' := List.map (map_def (f Γ) (f Γ')) mfix in
      tCoFix mfix' k
    | x => x
    end.

  Fixpoint reduce_opt Γ n c :=
    match n with
    | 0 => None
    | S n =>
      match reduce_stack_term Γ n c with
      | Some c' =>
        Some (map_constr_with_binders
                (fun Γ t => match reduce_opt Γ n t with
                            | Some t => t
                            | None => t end) Γ c')
      | None => None
      end
    end.

End Reduce.

Definition isConstruct c :=
  match c with
  | tConstruct _ _ _ => true
  | tApp (tConstruct _ _ _) _ => true
  | _ => false
  end.

Definition isCoFix c :=
  match c with
  | tCoFix _ _ => true
  | _ => false
  end.

Inductive conv_pb :=
| Conv
| Cumul.

Definition eq_case_info (ci ci' : case_info) :=
  eq_inductive ci.(ci_ind) ci'.(ci_ind) && Nat.eqb ci.(ci_npar) ci'.(ci_npar). (* FIXME relevance check *)

Fixpoint eq_term `{checker_flags} (φ : universes_graph) (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => Nat.eqb n n'
  | tEvar ev args, tEvar ev' args' => Nat.eqb ev ev' && forallb2 (eq_term φ) args args'
  | tVar id, tVar id' => eqb id id'
  | tSort s, tSort s' => check_eqb_sort φ s s'
  | tCast f k T, tCast f' k' T' => eq_term φ f f' && eq_term φ T T'
  | tApp f args, tApp f' args' => eq_term φ f f' && forallb2 (eq_term φ) args args'
  | tConst c u, tConst c' u' => eq_constant c c' && eqb_univ_instance φ u u'
  | tInd i u, tInd i' u' => eq_inductive i i' && eqb_univ_instance φ u u'
  | tConstruct i k u, tConstruct i' k' u' => eq_inductive i i' && Nat.eqb k k'
                                                    && eqb_univ_instance φ u u'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term φ b b' && eq_term φ t t' && eq_term φ c c'
  | tCase ci p c brs,
    tCase ci' p' c' brs' =>
    eq_case_info ci ci' &&
    eqb_predicate (eqb_univ_instance φ) (eq_term φ) p p' && eq_term φ c c' && forallb2 (fun br br' => eq_term φ br.(bbody) br'.(bbody)) brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term φ c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | _, _ => false
  end.


Fixpoint leq_term `{checker_flags} (φ : universes_graph) (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => Nat.eqb n n'
  | tEvar ev args, tEvar ev' args' => Nat.eqb ev ev' && forallb2 (eq_term φ) args args'
  | tVar id, tVar id' => eqb id id'
  | tSort s, tSort s' => check_leqb_sort φ s s'
  | tApp f args, tApp f' args' => eq_term φ f f' && forallb2 (eq_term φ) args args'
  | tCast f k T, tCast f' k' T' => eq_term φ f f' && eq_term φ T T'
  | tConst c u, tConst c' u' => eq_constant c c' && eqb_univ_instance φ u u'
  | tInd i u, tInd i' u' => eq_inductive i i' && eqb_univ_instance φ u u'
  | tConstruct i k u, tConstruct i' k' u' => eq_inductive i i' && Nat.eqb k k' &&
                                                    eqb_univ_instance φ u u'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && leq_term φ t t'
  | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term φ b b' && eq_term φ t t' && leq_term φ c c'
  | tCase ci p c brs, tCase ci' p' c' brs' =>
    eq_case_info ci ci' &&
    eqb_predicate (eqb_univ_instance φ) (eq_term φ) p p' && eq_term φ c c' && forallb2 (fun br br' => eq_term φ br.(bbody) br'.(bbody)) brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term φ c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | _, _ => false
  end.

Section Conversion.

  Context `{checker_flags} (flags : RedFlags.t).
  Context (Σ : global_env) (G : universes_graph).

  Definition nodelta_flags := RedFlags.mk true true true false true true.

  Definition unfold_one_fix n Γ mfix idx l :=
    unf <- unfold_fix mfix idx ;;
    let '(arg, fn) := unf in
    c <- nth_error l arg ;;
    cred <- reduce_stack RedFlags.default Σ Γ n c [] ;;
    let '(cred, _) := cred in
    if negb (isConstruct cred) then None
    else Some fn.

  Definition unfold_one_case n Γ c :=
    cred <- reduce_stack_term RedFlags.default Σ Γ n c ;;
    if negb (isConstruct cred || isCoFix cred) then None
    else Some cred.

  Definition reducible_head n Γ c l :=
    match c with
    | tFix mfix idx => unfold_one_fix n Γ mfix idx l
    | tCase ind' p' c' brs =>
      match unfold_one_case n Γ c' with
      | None => None
      | Some c' => Some (tCase ind' p' c' brs)
      end
    | tProj p c =>
      match unfold_one_case n Γ c with
      | None => None
      | Some c' => Some (tProj p c')
      end
    | tConst c _ => (* TODO Universes *)
      match lookup_env Σ c with
      | Some (ConstantDecl {| cst_body := Some body |}) => Some body
      | _ => None
      end
    | _ => None
    end.

  Definition lookup_env c := lookup_env Σ c.

  Definition opt_bool_to_bool (x : option bool) : bool :=
    match x with
    | Some b => b
    | None => false
    end.


  Fixpoint isconv (n : nat) (leq : conv_pb) (Γ : context)
           (t1 : term) (l1 : list term) (t2 : term) (l2 : list term) {struct n} : option bool :=
    match n with 0 => None | S n =>
    red1 <- reduce_stack nodelta_flags Σ Γ n t1 l1 ;;
    red2 <- reduce_stack nodelta_flags Σ Γ n t2 l2 ;;
    let '(t1,l1) := red1 in
    let '(t2,l2) := red2 in
    isconv_prog n leq Γ t1 l1 t2 l2
    end
  with isconv_prog (n : nat) (leq : conv_pb) (Γ : context)
                   (t1 : term) (l1 : list term) (t2 : term) (l2 : list term)
                   {struct n} : option bool :=
    match n with 0 => None | S n =>
    let isconv_stacks l1 l2 :=
        ret (forallb2 (fun x y => opt_bool_to_bool (isconv n Conv Γ x [] y [])) l1 l2)
    in
    let on_cond (b : bool) := if b then isconv_stacks l1 l2 else ret false in
    (** Test equality at each step ?? *)
    (* if eq_term t1 t2 && (match isconv_stacks l1 l2 with Some true => true | _ => false) *)
    (* then ret true else *)
    let fallback (x : unit) :=
      match reducible_head n Γ t1 l1 with
      | Some t1 =>
        redt <- reduce_stack nodelta_flags Σ Γ n t1 l1 ;;
        let '(t1, l1) := redt in
        isconv_prog n leq Γ t1 l1 t2 l2
      | None =>
        match reducible_head n Γ t2 l2 with
        | Some t2 =>
          redt <- reduce_stack nodelta_flags Σ Γ n t2 l2 ;;
          let '(t2, l2) := redt in
          isconv_prog n leq Γ t1 l1 t2 l2
        | None =>
          on_cond (match leq with
                   | Conv => eq_term G t1 t2
                   | Cumul => leq_term G t1 t2 end)
        end
      end
    in
    match t1, t2 with
    | tApp f args, tApp f' args' =>
      None (* Impossible *)

    | tCast t _ v, tCast u _ v' => None (* Impossible *)

    | tConst c u, tConst c' u' => (* TODO Universes *)
      if eq_constant c c' then
        b <- isconv_stacks l1 l2 ;;
        if b then ret true (* FO optim *)
        else
          match lookup_env c with (* Unfold both bodies at once *)
          | Some (ConstantDecl {| cst_body := Some body |}) =>
            isconv n leq Γ body l1 body l2
          | _ => ret false
          end
      else
        match lookup_env c' with
        | Some (ConstantDecl {| cst_body := Some body |}) =>
          isconv n leq Γ t1 l1 body l2
        | _ =>
          match lookup_env c with
          | Some (ConstantDecl {| cst_body := Some body |}) =>
            isconv n leq Γ body l1 t2 l2
          | _ => ret false
          end
        end

    | tLambda na b t, tLambda _ b' t' =>
      cnv <- isconv n Conv Γ b [] b' [] ;;
      if (cnv : bool) then
        isconv n Conv (Γ ,, vass na b) t [] t' []
      else ret false

    | tProd na b t, tProd _ b' t' =>
      cnv <- isconv n Conv Γ b [] b' [] ;;
      if (cnv : bool) then
        isconv n leq (Γ ,, vass na b) t [] t' []
      else ret false

    | tCase ci p c brs,
      tCase ci' p' c' brs' => (* Hnf did not reduce, maybe delta needed in c *)
      if eq_case_info ci ci' && eqb_predicate (eqb_univ_instance G) (eq_term G) p p' && eq_term G c c'
      && forallb2 (fun br br' => eq_term G br.(bbody) br'.(bbody)) brs brs' then
        ret true
      else
        cred <- reduce_stack_term RedFlags.default Σ Γ n c ;;
        c'red <- reduce_stack_term RedFlags.default Σ Γ n c' ;;
        if eq_term G cred c && eq_term G c'red c' then ret true
        else
          isconv n leq Γ (tCase ci p cred brs) l1 (tCase ci' p c'red brs') l2

    | tProj p c, tProj p' c' => on_cond (eq_projection p p' && eq_term G c c')

    | tFix mfix idx, tFix mfix' idx' =>
      (* Hnf did not reduce, maybe delta needed *)
      if eq_term G t1 t2 && opt_bool_to_bool (isconv_stacks l1 l2) then ret true
      else
        match unfold_one_fix n Γ mfix idx l1 with
        | Some t1 =>
          redt <- reduce_stack nodelta_flags Σ Γ n t1 l1 ;;
          let '(t1, l1) := redt in
          isconv_prog n leq Γ t1 l1 t2 l2
        | None =>
          match unfold_one_fix n Γ mfix' idx' l2 with
          | Some t2 =>
            redt <- reduce_stack nodelta_flags Σ Γ n t2 l2 ;;
            let '(t2, l2) := redt in
            isconv_prog n leq Γ t1 l1 t2 l2
          | None => ret false
          end
        end

    | tCoFix mfix idx, tCoFix mfix' idx' =>
      on_cond (eq_term G t1 t2)

    | _, _ => fallback ()
    end
    end.
End Conversion.

Definition try_reduce Σ Γ n t :=
  match reduce_opt RedFlags.default Σ Γ n t with
  | Some t' => t'
  | None => t
  end.

Definition check_conv_gen `{checker_flags} {F:Fuel} conv_pb Σ G Γ t u :=
  match isconv Σ G fuel conv_pb Γ t [] u [] with
  | Some b => if b then ret () else raise (NotConvertible Γ t u t u)
  | None => raise (NotEnoughFuel fuel)
  end.

Definition check_conv_leq `{checker_flags} {F:Fuel} := check_conv_gen Cumul.
Definition check_conv `{checker_flags} {F:Fuel} := check_conv_gen Conv.


Definition is_graph_of_global_env_ext `{checker_flags} Σ G :=
  is_graph_of_uctx G (global_ext_uctx Σ).

Section Typecheck.
  Context {F : Fuel}.
  Context (Σ : global_env).

  Definition hnf_stack Γ t :=
    match reduce_stack RedFlags.default Σ Γ fuel t [] with
    | Some t' => ret t'
    | None => raise (NotEnoughFuel fuel)
    end.

  Definition reduce Γ t :=
    match reduce_opt RedFlags.default Σ Γ fuel t with
    | Some t' => ret t'
    | None => raise (NotEnoughFuel fuel)
    end.

  Definition reduce_to_sort Γ (t : term) : typing_result sort :=
    match t with
    | tSort s => ret s
    | _ =>
      t' <- hnf_stack Γ t ;;
      match t' with
      | (tSort s, []) => ret s
      | _ => raise (NotASort t)
      end
    end.

  Definition reduce_to_prod Γ (t : term) : typing_result (term * term) :=
    match t with
    | tProd _ a b => ret (a, b)
    | _ =>
      t' <- hnf_stack Γ t ;;
      match t' with
      | (tProd _ a b,[]) => ret (a, b)
      | _ => raise (NotAProduct t (zip t'))
      end
    end.

  Definition reduce_to_ind Γ (t : term) :
    typing_result (inductive * list Level.t * list term) :=
    match decompose_app t with
    | (tInd i u, l) => ret (i, u, l)
    | _ => t' <- hnf_stack Γ t ;;
           match t' with
           | (tInd i u, l) => ret (i, u, l)
           | _ => raise (NotAnInductive t)
           end
    end.
End Typecheck.

Section Typecheck.
  Context {cf : checker_flags} {F : Fuel}.
  Context (Σ : global_env) (G : universes_graph).

  Definition convert_leq Γ (t u : term) : typing_result unit :=
    if eq_term G t u then ret ()
    else
      match isconv Σ G fuel Cumul Γ t [] u [] with
      | Some b =>
        if b then ret ()
        else raise (NotConvertible Γ t u t u)
      | None => (* fallback *)
        t' <- reduce Σ Γ t ;;
        u' <- reduce Σ Γ u ;;
        if leq_term G t' u' then ret ()
        else raise (NotConvertible Γ t u t' u')
      end.

  Section InferAux.
    Variable (infer : context -> term -> typing_result term).

    Fixpoint infer_spine (Γ : context) (ty : term) (l : list term)
             {struct l} : typing_result term :=
    match l with
    | nil => ret ty
    | cons x xs =>
       pi <- reduce_to_prod Σ Γ ty ;;
       let '(a1, b1) := pi in
       tx <- infer Γ x ;;
       convert_leq Γ tx a1 ;;
       infer_spine Γ (subst10 x b1) xs
    end.

    Definition infer_type Γ t :=
      tx <- infer Γ t ;;
      reduce_to_sort Σ Γ tx.

    Definition infer_cumul Γ t t' :=
      tx <- infer Γ t ;;
      convert_leq Γ tx t'.

  End InferAux.

  Definition check_consistent_constraints cstrs :=
    if check_constraints G cstrs then ret tt
    else raise (UnsatisfiedConstraints cstrs).

  Fixpoint infer (Γ : context) (t : term) : typing_result term :=
    match t with
    | tRel n =>
      match nth_error Γ n with
      | Some d => ret (lift0 (S n) d.(decl_type))
      | None => raise (UnboundRel n)
      end

    | tVar n => raise (UnboundVar n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort s => ret (tSort (Sort.super s))

    | tCast c k t =>
      infer_type infer Γ t ;;
      infer_cumul infer Γ c t ;;
      ret t

    | tProd n t b =>
      s1 <- infer_type infer Γ t ;;
      s2 <- infer_type infer (Γ ,, vass n t) b ;;
      ret (tSort (Sort.sort_of_product s1 s2))

    | tLambda n t b =>
      infer_type infer Γ t ;;
      t2 <- infer (Γ ,, vass n t) b ;;
      ret (tProd n t t2)

    | tLetIn n b b_ty b' =>
      infer_type infer Γ b_ty ;;
       infer_cumul infer Γ b b_ty ;;
       b'_ty <- infer (Γ ,, vdef n b b_ty) b' ;;
       ret (tLetIn n b b_ty b'_ty)

    | tApp t l =>
      t_ty <- infer Γ t ;;
      infer_spine infer Γ t_ty l

    | tConst cst u =>
      tycstrs <- lookup_constant_type_cstrs Σ cst u ;;
      let '(ty, cstrs) := tycstrs in
      check_consistent_constraints cstrs;;
      ret ty

    | tInd (mkInd ind i) u =>
      tycstrs <- lookup_ind_type_cstrs Σ ind i u;;
      let '(ty, cstrs) := tycstrs in
      check_consistent_constraints cstrs;;
      ret ty

    | tConstruct (mkInd ind i) k u =>
      tycstrs <- lookup_constructor_type_cstrs Σ ind i k u ;;
      let '(ty, cstrs) := tycstrs in
      check_consistent_constraints cstrs;;
      ret ty

    | tCase ci p c brs =>
      ty <- infer Γ c ;;
      indargs <- reduce_to_ind Σ Γ ty ;;
      (** TODO check branches *)
      let '(ind, u, args) := indargs in
      if eq_inductive ind ci.(ci_ind) then
        let pctx := rebuild_case_predicate_ctx Σ ind p in
        let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in
        ret (tApp ptm (List.skipn ci.(ci_npar) args ++ [c]))
      else
        let ind1 := tInd ind u in
        let ind2 := tInd ci.(ci_ind) u in
        raise (NotConvertible Γ ind1 ind2 ind1 ind2)

    | tProj p c =>
      ty <- infer Γ c ;;
      indargs <- reduce_to_ind Σ Γ ty ;;
      (* FIXME *)
      ret ty

    | tFix mfix n =>
      match nth_error mfix n with
      | Some f => ret f.(dtype)
      | None => raise (IllFormedFix mfix n)
      end

    | tCoFix mfix n =>
      match nth_error mfix n with
      | Some f => ret f.(dtype)
      | None => raise (IllFormedFix mfix n)
      end

    | tInt _ | tFloat _ | tString _ | tArray _ _ _ _ => raise (NotSupported "primitive types")
    end.

  Definition check (Γ : context) (t : term) (ty : term) : typing_result unit :=
    infer Γ ty ;;
    infer_cumul infer Γ t ty ;;
    ret ().

  Definition typechecking (Γ : context) (t ty : term) :=
    match check Γ t ty with
    | Checked _ => true
    | TypeError _ => false
    end.

End Typecheck.

Arguments bind _ _ _ _ ! _.
Open Scope monad.

Definition default_fuel : Fuel := Nat.pow 2 14.

Fixpoint fresh id (env : global_declarations) : bool :=
  match env with
  | nil => true
  | cons g env => negb (eq_constant g.1 id) && fresh id env
  end.

Section Checker.

  Context {cf : checker_flags} {F : Fuel}.

  Inductive env_error :=
  | IllFormedDecl (e : string) (e : type_error)
  | AlreadyDeclared (id : string).

  Inductive EnvCheck (A : Type) :=
  | CorrectDecl (a : A)
  | EnvError (e : env_error).
  Global Arguments EnvError {A} e.
  Global Arguments CorrectDecl {A} a.

  Instance envcheck_monad : Monad EnvCheck :=
    {| ret A a := CorrectDecl a ;
       bind A B m f :=
         match m with
         | CorrectDecl a => f a
         | EnvError e => EnvError e
         end
    |}.

  Definition wrap_error {A} (id : string) (check : typing_result A) : EnvCheck A :=
    match check with
    | Checked a => CorrectDecl a
    | TypeError e => EnvError (IllFormedDecl id e)
    end.

  Definition check_wf_type id Σ G t :=
    wrap_error id (infer_type Σ (infer Σ G) [] t) ;; ret ().

  Definition check_wf_judgement id Σ G t ty :=
    wrap_error id (check Σ G [] t ty) ;; ret ().

  Definition infer_term Σ G t :=
    wrap_error "" (infer Σ G [] t).

  Definition check_wf_decl Σ G kn (g : global_decl) : EnvCheck () :=
    match g with
    | ConstantDecl cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement (string_of_kername kn) Σ G term cst.(cst_type)
      | None => check_wf_type (string_of_kername kn) Σ G cst.(cst_type)
      end
    | InductiveDecl inds =>
      List.fold_left (fun acc body =>
                        acc ;; check_wf_type body.(ind_name) Σ G body.(ind_type))
                     inds.(ind_bodies) (ret ())
    end.

  Fixpoint check_fresh id (env : global_declarations) : EnvCheck () :=
    match env with
    | [] => ret ()
    | g :: env =>
      check_fresh id env;;
      if eq_constant id g.1 then
        EnvError (AlreadyDeclared (string_of_kername id))
      else ret ()
    end.

  Definition add_gc_constraints ctrs  (G : universes_graph) : universes_graph
    := (G.1.1,  GoodConstraintSet.fold
                  (fun ctr => wGraph.EdgeSet.add (edge_of_constraint ctr)) ctrs G.1.2,
        G.2).

  Fixpoint check_wf_declarations (univs : ContextSet.t) (retro : Retroknowledge.t) (G : universes_graph) (g : global_declarations)
    : EnvCheck () :=
    match g with
    | [] => ret tt
    | g :: env =>
      check_wf_declarations univs retro G env ;;
      check_wf_decl {| universes := univs; declarations := env; retroknowledge := retro |} G g.1 g.2 ;;
      check_fresh g.1 env ;;
      ret tt
    end.

  Definition typecheck_program (p : program) : EnvCheck term :=
    let Σ := fst p in
    let '(univs, decls, retro) := (Σ.(universes), Σ.(declarations), Σ.(retroknowledge)) in
    match gc_of_constraints (snd univs) with
    | None => EnvError (IllFormedDecl "toplevel"
        (UnsatisfiableConstraints univs.2))
    | Some ctrs =>
      let G := add_gc_constraints ctrs init_graph in
      if wGraph.is_acyclic G then
        check_wf_declarations univs retro G decls ;;
        infer_term Σ G (snd p)
      else EnvError (IllFormedDecl "toplevel"
        (UnsatisfiableConstraints univs.2))
    end.

End Checker.

(* for compatibility, will go away *)
Definition infer' `{checker_flags} `{Fuel} (Σ : global_env_ext) Γ t
  := let uctx := (global_ext_uctx Σ) in
    match gc_of_uctx uctx with
     | None => raise (UnsatisfiableConstraints uctx.2)
     | Some uctx => infer (fst Σ) (make_graph uctx) Γ t
     end.

