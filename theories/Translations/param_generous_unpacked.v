(* Distributed under the terms of the MIT license. *)
From MetaRocq.Template Require Import utils All.
From MetaRocq.Translations Require Import translation_utils.
From Stdlib Require Import ssreflect.
(* Import BasicAst. *)

Reserved Notation "'tsl_ty_param'".

Definition tsl_name n :=
  match n with
  | nAnon => nAnon
  | nNamed n => nNamed (tsl_ident n)
  end.

(* Definition mkApps t us := *)
(*   match t with *)
(*   | tApp f args => tApp f (args ++ us) *)
(*   | _ => tApp t us *)
(*   end. *)
Definition mkApps t us := tApp t us. (* meanwhile *)
Definition mkApp t u := mkApps t [u].

Definition default_term := tRel 0.

Definition up := lift 1 0.

Fixpoint tsl_rec0 (E : tsl_table) (t : term) {struct t} : term :=
  match t with
  | tRel k => tRel (2*k+1)
  | tEvar k ts => tEvar k (map (tsl_rec0 E) ts)
  | tCast t c a => tCast (tsl_rec0 E t) c (tsl_rec0 E a)
  | tProd na A B => tProd na (tsl_rec0 E A)
                  (tProd (tsl_name na) (mkApp (up (tsl_rec1 E A)) (tRel 0))
                         (tsl_rec0 E B))
  | tLambda na A t => tLambda na (tsl_rec0 E A)
                    (tLambda (tsl_name na) (mkApp (up (tsl_rec1 E A)) (tRel 0))
                             (tsl_rec0 E t))
  | tLetIn na A t u => tLetIn na (tsl_rec0 E A) (tsl_rec0 E t)
                     (tLetIn (tsl_name na) (mkApp (up (tsl_rec1 E A)) (tRel 0)) (up (tsl_rec1 E t))
                             (tsl_rec0 E u))

  | tApp t us => let u' := List.fold_right (fun v l => tsl_rec0 E v :: tsl_rec1 E v :: l) [] us in
                mkApps (tsl_rec0 E t) u'

  | tCase ik t u br => tCase ik (tsl_rec0 E t) (tsl_rec0 E u)
                            (map (fun x => (fst x, tsl_rec0 E (snd x))) br)
  | tProj p t => tProj p (tsl_rec0 E t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end
with tsl_rec1 (E : tsl_table) (t : term) {struct t} : term :=
  match t with
  | tRel k => tRel (2 * k)
  | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))

  | tProd na A B => let A0 := tsl_rec0 E A in
                   let A1 := tsl_rec1 E A in
                   let B0 := tsl_rec0 E B in
                   let B1 := tsl_rec1 E B in
                   let ΠAB0 := tProd na A0 (tProd (tsl_name na) (mkApp (up A1) (tRel 0)) B0) in
                   tLambda (nNamed "f") ΠAB0
                           (tProd na (up A0) (tProd (tsl_name na) (subst_app (lift0 2 A1) [tRel 0])
                                                    (subst_app (lift 1 2 B1)
                                                               [tApp (tRel 2) [tRel 1; tRel 0]])))

  | tLambda na A t => let A0 := tsl_rec0 E A in
                     let A1 := tsl_rec1 E A in
                     tLambda na A0 (tLambda (tsl_name na) (subst_app (up A1) [tRel 0]) (tsl_rec1 E t))

  | tApp t us => let u' := List.fold_right (fun v l => tsl_rec0 E v :: tsl_rec1 E v :: l) [] us in
                mkApps (tsl_rec1 E t) u'

  | tLetIn na t A u => let t0 := tsl_rec0 E t in
                      let t1 := tsl_rec1 E t in
                      let A0 := tsl_rec0 E A in
                      let A1 := tsl_rec1 E A in
                      let u0 := tsl_rec0 E u in
                      let u1 := tsl_rec1 E u in
                      tLetIn na t0 A0 (tLetIn (tsl_name na) (up t1) (subst_app (up A1) [tRel 0]) u1)

  | tCast t c A => let t0 := tsl_rec0 E t in
                  let t1 := tsl_rec1 E t in
                  let A0 := tsl_rec0 E A in
                  let A1 := tsl_rec1 E A in
                  tCast t1 c (mkApps A1 [tCast t0 c A0]) (* apply_subst ? *)

  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => t
    | None => default_term
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => t
    | None => default_term
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => t
    | None => default_term
    end

  | _ => todo ""
  end.



MetaRocq Run (tm <- tmQuote (forall A, A -> A) ;;
                     let tm' := tsl_rec1 [] tm in
                     tmUnquote tm' >>= tmPrint).

MetaRocq Run (tm <- tmQuote (fun A (x : A) => x) ;;
                     let tm' := tsl_rec0 [] tm in
                     tmUnquote tm' >>= tmPrint).

MetaRocq Run (tm <- tmQuote (fun A (x : A) => x) ;;
                     let tm' := tsl_rec1 [] tm in
                     tmUnquote tm' >>= tmPrint).

Goal ((fun f : forall (A : Type) (Aᵗ : A -> Type) (H : A), Aᵗ H -> A =>
    forall (A : Type) (Aᵗ : A -> Type) (H : A) (H0 : Aᵗ H), Aᵗ (f A Aᵗ H H0)) (fun (A : Type) (Aᵗ : A -> Type) (x : A) (_ : Aᵗ x) => x)
       = (forall (A : Type) (Aᵗ : A -> Type) (x : A), Aᵗ x -> Aᵗ x)).
reflexivity.
Defined.

MetaRocq Quote Definition tm := ((fun A (x:A) => x) (Type -> Type) (fun x => x)).

Unset MetaRocq Strict Unquote Universe Mode.

MetaRocq Run (let tm' := tsl_rec1 [] tm in
                     print_nf tm' ;;
                     tmUnquote tm' >>= tmPrint).


Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.

Fixpoint monad_map_i_aux {M} {H : Monad M} {A B} (f : nat -> A -> M B) (n0 : nat) (l : list A) : M (list B)
  := match l with
     | [] => ret []
     | x :: l => x' <- (f n0 x) ;;
                l' <- (monad_map_i_aux f (S n0) l) ;;
                ret (x' :: l')
     end.

Definition monad_map_i {M H A B} f := @monad_map_i_aux M H A B f 0.

(* could be defined with Id monad *)
Fixpoint map_i_aux {A B} (f : nat -> A -> B) (n0 : nat) (l : list A) : list B
  := match l with
     | [] => []
     | x :: l => (f n0 x) :: (map_i_aux f (S n0) l)
     end.

Definition map_i {A B} f := @map_i_aux A B f 0.


Definition tsl_mind_body (E : tsl_table)
           (id : ident) (mind : mutual_inductive_body)
  : tsl_table * list mutual_inductive_body.
  refine (_, [{| ind_npars := 2 * mind.(ind_npars);
                 ind_bodies := _ |}]).
  - refine (let id' := tsl_ident id in (* should be kn ? *)
            fold_left_i (fun E i ind => _ :: _ ++ E) mind.(ind_bodies) []).
    + (* ind *)
      exact (IndRef (mkInd id i), tInd (mkInd id' i) []).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd id i) k, tConstruct (mkInd id' i) k []).
  - refine (map_i _ mind.(ind_bodies)).
    intros i ind.
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}. (* todo *)
    + (* arity  *)
      refine (let ar := subst_app (tsl_rec1 E ind.(ind_type))
                             [tInd (mkInd id i) []] in
              ar).
    + (* constructors *)
      refine (map_i _ ind.(ind_ctors)).
      intros k ((name, typ), nargs).
      refine (tsl_ident name, _, 2 * nargs).
      refine (subst_app _ [tConstruct (mkInd id i) k []]).
      refine (fold_left_i (fun t0 i u  => t0 {S i := u}) _ (tsl_rec1 E typ)).
      (* [I_n-1; ... I_0] *)
      refine (List.rev (map_i (fun i _ => tInd (mkInd id i) [])
                              mind.(ind_bodies))).
Defined.


(* Instance param3 : Translation *)
(*   := {| tsl_id := tsl_ident ; *)
(*         tsl_tm := fun ΣE => tsl_term fuel (fst ΣE) (snd ΣE) [] ; *)
(*         tsl_ty := fun ΣE => tsl_ty_param fuel (fst ΣE) (snd ΣE) [] ; *)
(*         tsl_ind := todo |}. *)




Definition tTranslate (ΣE : tsl_context) (id : ident)
  : TemplateMonad (option tsl_context) :=
  gr <- tmLocate id ;;
  id' <- tmEval all (tsl_ident id) ;;
  let E := snd ΣE in
  match gr with
  | ConstructRef ind _ => tmPrint "todo tTranslate" ;; ret None
  | IndRef (mkInd kn n) =>
      d <- tmQuoteInductive id ;;
      let d' := tsl_mind_body E id d in
      d' <- tmEval lazy d' ;;
      tmPrint d' ;;
      let entries := map mind_body_to_entry (snd d') in
      (* print_nf entries ;; *)
      monad_fold_left (fun _ e => tmMkInductive true e) entries tt ;;
      let decl := InductiveDecl kn d in
      print_nf  (id ^ " has been translated as " ^ id') ;;
      ret (Some (decl :: fst ΣE, E ++ snd ΣE))

  | ConstRef kn =>
    e <- tmQuoteConstant kn true ;;
    print_nf ("toto1" ^ id) ;;
    match e with
    | ParameterEntry _ => print_nf (id ^ "is an axiom, not a definition") ;;
                         ret None
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_body := t |} =>
      print_nf ("toto2 " ^ id) ;;
      (* tmPrint t ;; *)
      t0 <- tmEval lazy (tsl_rec0 E t) ;;
      t1 <- tmEval lazy (tsl_rec1 E t) ;;
      A1 <- tmEval lazy (tsl_rec1 E A) ;;
      print_nf ("toto4 " ^ id) ;;
      tmMkDefinition id' t1 ;;
      print_nf ("toto5 " ^ id) ;;
      let decl := {| cst_universes := [];
                     cst_type := A; cst_body := Some t |} in
      let Σ' := ConstantDecl kn decl :: (fst ΣE) in
      let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
      print_nf  (id ^ " has been translated as " ^ id') ;;
      tmEval all (Some (Σ', E'))
    end
  end.


Definition Ty := Type.
Definition TyTy := Ty -> Type.
MetaRocq Run (ΣE <- tTranslate ([],[]) "Ty" ;;
                     let ΣE := option_get todo ΣE in
                        (* print_nf ΣE). *)
                     tTranslate ΣE "TyTy" >>= tmPrint).

(* MetaRocq Run (ΣE <- tTranslate ([],[]) "nat" ;; *)
(*                      let ΣE := option_get todo ΣE in *)
(*                         (* print_nf ΣE). *) *)
(*                      tTranslate ΣE "t" >>= tmPrint). *)

Fail MetaRocq Run (tTranslate ([],[]) "nat").



Definition map_context_decl (f : term -> term) (decl : context_decl): context_decl
  := {| decl_name := decl.(decl_name);
        decl_body := option_map f decl.(decl_body); decl_type := f decl.(decl_type) |}.


Notation " Γ ,, d " := (d :: Γ) (at level 20, d at next level, only parsing).

Fixpoint tsl_ctx (E : tsl_table) (Γ : context) : context :=
  match Γ with
  | [] => []
  (* | Γ ,, {| decl_name := n; decl_body := None; decl_type := A |} => *)
  (*   tsl_ctx E Γ ,, vass n (tsl_rec0 0 A) ,, vass (tsl_name n) (mkApp (lift0 1 (tsl_rec1 E 0 A)) (tRel 0)) *)
  | Γ ,, decl => let n := decl.(decl_name) in
                let x := decl.(decl_body) in
                let A := decl.(decl_type) in
    tsl_ctx E Γ ,, Build_context_decl n (omap (tsl_rec0 0) x) (tsl_rec0 0 A)
                ,, Build_context_decl (tsl_name n) (omap (lift 1 0 \o tsl_rec1 E 0) x) (mkApps (lift0 1 (tsl_rec1 E 0 A)) [tRel 0])
  end.

Delimit Scope term_scope with term.

Notation "#| Γ |" := (List.length Γ) (at level 0, Γ at level 99, format "#| Γ |") : term_scope.


Lemma tsl_ctx_length E (Γ : context) : #|tsl_ctx E Γ| = 2 * #|Γ|%term.
Proof.
  induction Γ.
  reflexivity.
  destruct a, decl_body; simpl;
  by rewrite IHΓ mulnS.
Qed.

(* Fixpoint removefirst_n {A} (n : nat) (l : list A) : list A := *)
(*   match n with *)
(*   | O => l *)
(*   | S n => match l with *)
(*           | [] => [] *)
(*           | a :: l => removefirst_n n l *)
(*           end *)
(*   end. *)

Notation "( x ; y )" := (exist _ x y).

(* Lemma tsl_ctx_safe_nth fuel Σ E Γ *)
(*   : forall Γ', tsl_ctx fuel Σ E Γ = Success Γ' -> forall n p, exists p', *)
(*         map_context_decl (tsl_ty fuel Σ E (removefirst_n (S n) Γ)) *)
(*                          (safe_nth Γ (n; p)) *)
(*         = Success (safe_nth Γ' (n; p')). *)
(*   intros Γ' H n p. cbn beta in *. *)
(*   revert Γ Γ' H p. *)
(*   induction n; intros Γ Γ' H p; *)
(*     (destruct Γ as [|A Γ]; [inversion p|]). *)
(*   - cbn -[map_context_decl]. *)
(*     rewrite tsl_ctx_cons in H. *)
(*     remember (map_context_decl (tsl_term fuel Σ E Γ) A).  *)
(*     destruct t; [|discriminate]. *)
(*     remember (tsl_ctx fuel Σ E Γ).  *)
(*     destruct t; [|discriminate]. *)
(*     cbn in H. inversion H; clear H. *)
(*     clear p H1. *)
(*     unshelve econstructor. apply le_n_S, le_0_n. *)
(*     reflexivity. *)
(*   - cbn -[map_context_decl]. *)
(*     rewrite tsl_ctx_cons in H. *)
(*     remember (map_context_decl (tsl_term fuel Σ E Γ) A).  *)
(*     destruct t; [|discriminate]. *)
(*     remember (tsl_ctx fuel Σ E Γ).  *)
(*     destruct t; [|discriminate]. *)
(*     cbn in H. inversion H; clear H. *)
(*     symmetry in Heqt0. *)
(*     set (Typing.safe_nth_obligation_2 context_decl (A :: Γ) (S n; p) A Γ eq_refl n eq_refl). *)
(*     specialize (IHn Γ c0 Heqt0 l). *)
(*     destruct IHn. *)

(*     unshelve econstructor. *)
(*     cbn. rewrite <- (tsl_ctx_length fuel Σ E Γ _ Heqt0). exact p. *)
(*     etransitivity. exact π2. cbn. *)
(*     apply f_equal, f_equal, f_equal. *)
(*     apply le_irr. *)
(* Defined. *)
(* Admitted. *)

(* (* todo inductives *) *)
(* Definition global_ctx_correct (Σ : global_context) (E : tsl_context) *)
(*   := forall id T, lookup_constant_type Σ id = Checked T *)
(*                 -> exists fuel t' T', lookup_tsl_ctx E (ConstRef id) = Some t' /\ *)
(*                            tsl_term fuel Σ E [] T = Success _ T' /\ *)
(*                            squash (Σ ;;; [] |-- t' : T'). *)


Definition tsl_table_correct (Σ : global_context) (E : tsl_table) : Type := todo.
(*   := forall id t' T, *)
(*     lookup_tsl_table E (ConstRef id) = Some t' -> *)
(*     lookup_constant_type Σ id = Checked T -> *)
(*     exists fuel T', ((tsl_ty fuel Σ E [] T = Success T') *)
(*       * (Σ ;;; [] |--  t' : T'))%type. *)

Lemma LmapE : @List.map = @seq.map.
reflexivity.
Qed.

Lemma lebE (m n : nat) : (Nat.leb m n) = (m <= n).
Admitted.

Lemma term_eqP : Equality.axiom eq_term.
Admitted.

Definition term_eqMixin := EqMixin term_eqP.
Canonical termT_eqype := EqType term term_eqMixin.

Lemma tsl_rec0_lift m n t :
  tsl_rec0 m (lift n m t) = lift (2 * n) m (tsl_rec0 m t).
Proof.
elim/term_forall_list_ind : t m n => //=; rewrite ?plusE.
- move=> n m k.
  rewrite lebE.
  case: leqP => /= mn; rewrite lebE plusE.
  rewrite !ifT ?mulnDr ?addnA //.
    admit.
    admit.
  by rewrite leqNgt mn.
- admit.
- by move=> t IHt c t0 IHt0 m n; rewrite IHt IHt0.
- by move=> n0 t -IHt t0 IHt0 m n /=; rewrite IHt addn1 IHt0.
- by move=> n t IHt t0 IHt0 m n0; rewrite IHt addn1 IHt0.
- by move=> n t IHt t0 IHt0 t1 IHt1 m n0; rewrite !addn1 IHt IHt0 IHt1.
- move=> t IHt l IHl m n; rewrite IHt.
  rewrite LmapE.
  rewrite -!map_comp.
  congr (tApp _ _).
  apply/eq_in_map => i /=.
  admit.
- move=> p t IHt t0 IHt0 l IHl m n.
  rewrite IHt IHt0.
  admit.
- by move=> s t IHt m n; rewrite IHt.
- admit.
- admit.
Admitted.


Lemma lift_mkApps n k t us
  : lift n k (mkApps t us) = mkApps (lift n k t) (map (lift n k) us).
Proof.
  (* destruct t; try reflexivity. *)
  (* cbn. destruct (Nat.leb k n0); try reflexivity. *)
  (* cbn. by rewrite -map_cat.  *)
done.
Qed.

Arguments subst_app : simpl nomatch.

Lemma tsl_rec1_lift E n t :
  (* tsl_rec1 E 0 (lift n m t) = lift (2 * n) (2 * m) (tsl_rec1 E 0 t). *)
  tsl_rec1 E 0 (lift0 n t) = lift0 (2 * n) (tsl_rec1 E 0 t).
Proof.
elim/term_forall_list_ind : t n => //; rewrite ?plusE.
- move=> n k.
  (* rewrite !lebE fun_if /= leq_mul2l /=. *)
  (* by have [] := leqP m n => //=; *) by rewrite /= mulnDr.
- admit.
- admit.
- admit.
- move=> t IHt c t0 IHt0 n /=; rewrite IHt IHt0 ?lift_mkApps.
  congr (tCast _ _ (mkApps _ _)).
  by rewrite !tsl_rec0_lift.
- move=> n t IHt t0 IHt0 n0.
  rewrite /=.
  rewrite !IHt.
  rewrite !tsl_rec0_lift.
(*   rewrite lift_simpl. *)
(*   rewrite IHt addn1 IHt0. *)
(* - by move=> n t IHt t0 IHt0 m n0; rewrite IHt addn1 IHt0. *)
(* - by move=> n t IHt t0 IHt0 t1 IHt1 m n0; rewrite !addn1 IHt IHt0 IHt1. *)
(* - move=> t IHt l IHl m n; rewrite IHt. *)
(*   rewrite LmapE. *)
(*   rewrite -!map_comp. *)
(*   congr (tApp _ _). *)
(*   apply/eq_in_map => i /=. *)
(*   admit. *)
(* - move=> p t IHt t0 IHt0 l IHl m n. *)
(*   rewrite IHt IHt0. *)
(*   admit. *)
(* - by move=> s t IHt m n; rewrite IHt. *)
(* - admit. *)
(* - admit. *)
Admitted.





(* Admitted. *)

(* Lemma tsl_rec0_lift n t *)
(*   : tsl_rec0 0 (lift0 n t) = lift0 n (tsl_rec0 0 t). *)
(* Admitted. *)

(* Lemma tsl_ty_lift fuel Σ E Γ n (p : n <= #|Γ|) t *)
(*   : tsl_ty fuel Σ E Γ (lift0 n t) = *)
(*     (t' <- tsl_ty fuel Σ E (removefirst_n n Γ) t ;; ret (lift0 n t')). *)
(* Admitted. *)

(* Lemma tsl_S_fuel {fuel Σ E Γ t t'} *)
(*   : tsl_term fuel Σ E Γ t = Success t' -> tsl_term (S fuel) Σ E Γ t = Success t'. *)
(* Admitted. *)


Record hidden T := Hidden {show : T}.
Arguments show : simpl never.
Notation "'hidden" := (show _ (Hidden _ _)).
Lemma hide T (t : T) : t = show T (Hidden T t).
Proof. by []. Qed.

(* From mathcomp Require Import ssrnat. *)

Arguments safe_nth : simpl nomatch.

Lemma eq_safe_nth T (l : list T) n n' p p' : n = n' ->
  safe_nth l (n; p) = safe_nth l (n'; p') :> T.
Proof.
move=> eq_n; case: _ / eq_n in p p' *.
elim: l => [|x l IHl] in n p p' *.
  by inversion p.
by case: n => [//|n] in p p' *; apply: IHl.
Qed.

    Lemma tsl_rec0_decl_type (Γ : context) (n : nat) (isdecl : (n < #|Γ|%term)%coq_nat) (E : tsl_table) (isdecl' : (2 * n + 1 < #|tsl_ctx E Γ|%term)%coq_nat)
      : tsl_rec0 0 (decl_type (safe_nth Γ (n; isdecl))) =
        decl_type (safe_nth (tsl_ctx E Γ) (2 * n + 1; isdecl')).
    Proof.
      elim: Γ => [|a Γ IHΓ] in n isdecl isdecl' *.
        by inversion isdecl.
      simpl.
      case: n => [//|n] in isdecl isdecl' *.
      rewrite addn1 /= in isdecl' *.
      rewrite IHΓ addn1 //.
        apply/leP; move/leP : isdecl'.
        by rewrite !mul2n doubleS.
      move=> isdecl''.
      congr (decl_type _); apply: eq_safe_nth.
      by rewrite plusE addn0 mul2n -addnn addnS.
    Qed.


Lemma tsl_rec1_decl_type (Γ : context) (n : nat) (E : tsl_table) p p'
  (Γ' := tsl_ctx E Γ) :
  mkApps (lift0 1 (decl_type (safe_nth Γ' ((2 * n); p)))) [tRel 0] =
  decl_type (safe_nth Γ' (2 * n; p')).
Proof.
subst Γ'; elim: Γ => [|a Γ IHΓ] in n p p' *.
  by inversion p.
(* simpl. *)
(* case: n => [|n] //= in p p' *. *)

(* rewrite /=. *)
(* rewrite addn1 /= in p' *. *)
(* rewrite IHΓ addn1 //. *)
(*   apply/leP; move/leP : p'. *)
(*   by rewrite !mul2n doubleS. *)
(* move=> p''. *)
(* congr (decl_type _); apply: eq_safe_nth. *)
(* by rewrite plusE addn0 mul2n -addnn addnS. *)
(*     Qed. *)


Admitted.

    (* Lemma tsl_rec1_decl_type (Γ : context) (n : nat) (isdecl : (n < #|Γ|%term)%coq_nat) (E : tsl_table) (isdecl' : (2 * n + 1 < #|tsl_ctx E Γ|%term)%coq_nat) *)
    (*   : tsl_rec1 E (decl_type (safe_nth Γ (n; isdecl))) = *)
    (*     decl_type (safe_nth (tsl_ctx E Γ) (2 * n + 1; isdecl')). *)

Lemma tsl_correct Σ Γ t T (H : Σ ;;; Γ |-- t : T)
  : forall E, tsl_table_correct Σ E ->
    let Γ' := tsl_ctx E Γ in
    let t0 := tsl_rec0 0 t in
    let t1 := tsl_rec1 E 0 t in
    let T0 := tsl_rec0 0 T in
    let T1 := tsl_rec1 E 0 T in
    Σ ;;; Γ' |-- t0 : T0 /\ Σ ;;; Γ' |-- t1 : mkApps T1 [t0].
Proof.
elim/typing_ind: H => {Γ t T} Γ.
- move=> n isdecl E X Γ' /=.
  rewrite tsl_rec0_lift mulnS add2n (tsl_rec0_decl_type _ _ _ E).
  rewrite tsl_ctx_length.
     apply/leP.
       by rewrite addn1 mul2n -doubleS -mul2n leq_mul2l; apply/leP.
  rewrite !addn1; move=> isdecl'.
  split; first exact: type_Rel.
  have := type_Rel Σ Γ' (2 * n) _.

  evar (l : (2 * n < #|Γ'|%term)%coq_nat).
  move=> /(_ l).
  rewrite -tsl_rec1_decl_type /=.
  admit.
  (* rewrite simpl_lift_rec; do ?easy. *)
  (* by rewrite plusE addn0 addn1. *)




- admit.
- admit.
- admit.
- admit.
- admit.
- rewrite /= => t l t' t'' tt' IHt' spine E ΣE_correct; rewrite /mkApps; split.
    apply: type_App.
      have [] := IHt' _ ΣE_correct.
        by move=> t0_ty ?; exact: t0_ty.
    admit.
  apply: type_App.
    have [] := IHt' _ ΣE_correct.
    by move=> ? t1_ty; exact: t1_ty.
  admit.






    rewrite /Γ' => isdecl'; clear.
    case: Γ isdecl isdecl'.





From Stdlib Require Import Vector.
(* MetaRocq Run (ΣE <- tTranslate ([],[]) "nat" ;; *)
