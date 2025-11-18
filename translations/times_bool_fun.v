(* Distributed under the terms of the MIT license. *)
Set Warnings "-notation-overridden".

From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All Checker.
From MetaRocq.Translations Require Import translation_utils MiniHoTT.
Import MRMonadNotation.

Unset MetaRocq Strict Unquote Universe Mode.

Local Set Primitive Projections.
Record prod A B := pair { π1 : A ; π2 : B }.

Arguments π1 {_ _} _.
Arguments π2 {_ _} _.
Arguments pair {_ _} _ _.

Declare Scope prod_scope.
Notation "( x ; y )" := (pair x y) : prod_scope.
Notation " A × B " := (prod A B) : type_scope.
Open Scope prod_scope.

MetaRocq Quote Definition tprod := prod.
MetaRocq Quote Definition tpair := @pair.
MetaRocq Run (t <- tmQuote prod ;;
            match t with
            | tInd i _ => tmDefinition "prod_ind" i
            | _ => tmFail "bug"
            end).
Definition proj1 (t : term) : term
  := tProj (mkProjection prod_ind 2 0) t.
Definition proj2 (t : term) : term
  := tProj (mkProjection prod_ind 2 (S 0)) t.

MetaRocq Quote Definition tbool := bool.
MetaRocq Quote Definition ttrue := true.
Definition timesBool (A : term) := tApp tprod [A; tbool].
Definition pairTrue typ tm := tApp tpair [typ; tbool; tm; ttrue].




Local Instance tit : config.checker_flags := config.type_in_type.
Local Existing Instance Checker.default_fuel.

Fixpoint tsl_rec (fuel : nat) (Σ : global_env_ext) (E : tsl_table) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel  n => ret (tRel n)
  | tSort s => ret (tSort s)

  | tCast t c A => t' <- tsl_rec fuel Σ E Γ t ;;
                  A' <- tsl_rec fuel Σ E Γ A ;;
                  ret (tCast t' c A')

  | tProd n A B => A' <- tsl_rec fuel Σ E Γ A ;;
                  B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;
                  ret (timesBool (tProd n A' B'))

  | tLambda n A t => A' <- tsl_rec fuel Σ E Γ A ;;
                    t' <- tsl_rec fuel Σ E (Γ ,, vass n A) t ;;
                    match infer' Σ (Γ ,, vass n A) t with
                    | Checked B =>
                      B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;
                      ret (pairTrue (tProd n A' B') (tLambda n A' t'))
                    | TypeError t => raise (TypingError t)
                    end

  | tLetIn n t A u => t' <- tsl_rec fuel Σ E Γ t ;;
                     A' <- tsl_rec fuel Σ E Γ A ;;
                     u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) u ;;
                     ret (tLetIn n t' A' u')

  | tApp t us => t' <- tsl_rec fuel Σ E Γ t ;;
                monad_fold_left (fun t u => u' <- tsl_rec fuel Σ E Γ u ;;
                                         ret (tApp (proj1 t) [u'])) us t'

  | tConst s univs => lookup_tsl_table' E (ConstRef s)
  | tInd i univs => lookup_tsl_table' E (IndRef i)
  | tConstruct i n univs => lookup_tsl_table' E (ConstructRef i n)
  | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;;
                ret (tProj p t')

  | tFix bodies n =>
    Γ' <- monad_map (fun '{| dname := na; dtype := ty; dbody := b; rarg := r |} =>
                      ty' <- tsl_rec fuel Σ E Γ ty ;;
                      ret {| decl_name := na; decl_body := None; decl_type := ty'|})
                   bodies;;
    bodies' <- monad_map (fun '{| dname := na; dtype := ty; dbody := b; rarg := r |} =>
                           ty' <- tsl_rec fuel Σ E Γ ty ;;
                           b'  <- tsl_rec fuel Σ E (Γ ++ Γ') b ;;
                           ret {| dname := na; dtype := ty';
                                  dbody := b'; rarg := r |})
                        bodies ;;
    ret (tFix bodies' n)
  | _ => raise TranslationNotHandeled (* var evar meta case cofix *)
  end
  end.


(* Definition recompose_prod (nas : list name) (ts : list term) (u : term) *)
(*   : term *)
(*   := let nats := List.combine nas ts in *)
(*      List.fold_right (fun t u => tProd (fst t) (snd t) u) u nats. *)

Definition combine' {A B} (p : list A * list B) : list (A * B)
  := List.combine  (fst p) (snd p).


Fixpoint replace pat u t {struct t} :=
  if eq_term uGraph.init_model t pat then u else
    match t with
    | tCast t c A => tCast (replace pat u t) c (replace pat u A)
    | tProd n A B => tProd n (replace pat u A) (replace (up pat) (up u) B)
    | tLambda n A t => tLambda n (replace pat u A) (replace (up pat) (up u) t)
    | tLetIn n t A B => tLetIn n (replace pat u t) (replace pat u A)
                              (replace (up pat) (up u) B)
    | tApp t us => tApp (replace pat u t) (List.map (replace pat u) us)
    | tProj p t => tProj p (replace pat u t)
    | _ => t (* todo *)
    end.

Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.

(* If tm of type typ = Π [A0] [A1] ... . [B], returns *)
(* a term of type [Π A0 A1 ... . B] *)
Definition pouet (tm typ : term) : term.
  simple refine (let '((names, types), last) := decompose_prod typ in
                 let L' := List.fold_left _ (List.combine names types) [] in _).
  exact (fun Γ' A => Γ' ,, vass (fst A) (snd A)).
  refine (let args := fold_left_i (fun l i _ => tRel i :: l) L' [] in _).
  refine (fst (List.fold_left _ L' (subst_app tm args, last))).
  refine (fun '(tm, typ) decl =>
            let A := tProd decl.(decl_name) decl.(decl_type) typ in
            (pairTrue A (tLambda decl.(decl_name) decl.(decl_type) tm),
             timesBool A)).
Defined.



Definition tsl_mind_body (ΣE : tsl_context) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body)
  : tsl_result (tsl_table * list mutual_inductive_body).
  refine (let tsl := fun Γ t => match tsl_rec fuel (fst ΣE) (snd ΣE) Γ t with
                             | Success x => x
                             | Error _ => todo "tsl"
                             end in
          let kn' := (mp, tsl_ident (snd kn)) in _).
  unshelve refine (let LI := List.split (mapi _ mind.(ind_bodies)) in
          ret (List.concat (fst LI),
               [{| ind_npars := mind.(ind_npars);
                   ind_params := _;
                   ind_bodies := snd LI;
                   ind_universes := mind.(ind_universes);
                   ind_variance := mind.(ind_variance)|}])). (* FIXME always ok? *)
  intros i ind.
  simple refine (let ind_type' := _ in
                 let ctors' := List.split (mapi _ ind.(ind_ctors)) in
                 (_ :: fst ctors',
                  {| ind_name := tsl_ident ind.(ind_name);
                     ind_sort := ind.(ind_sort);
                     ind_indices := ind.(ind_indices);
                     ind_type := ind_type';
                     ind_kelim := ind.(ind_kelim);
                     ind_ctors := snd ctors';
                     ind_projs := [];
                     ind_relevance := ind.(ind_relevance) |})).
  + (* arity *)
    refine (let L := decompose_prod ind.(ind_type) in _).
    simple refine (let L' := List.fold_left _ (combine' (fst L)) [] in _).
    exact (fun Γ' A => Γ' ,, vass (fst A) (tsl Γ' (snd A))).
    refine (List.fold_left _ L' (snd L)).
    exact (fun t decl => tProd decl.(decl_name) decl.(decl_type) t).
  + (* constructors *)
    intros k [name argctx indices typ nargs].
    simple refine (let ctor_type' := _ in
                   ((ConstructRef (mkInd kn i) k,
                     pouet (tConstruct (mkInd kn' i) k []) _),
                    (Build_constructor_body (tsl_ident name) argctx indices ctor_type' nargs))).
    * refine (fold_left_i (fun t i _ => replace (proj1 (tRel i)) (tRel i) t)
                          mind.(ind_bodies) _).
      refine (let L := decompose_prod typ in _).
      simple refine (let L' := List.fold_left _ (combine' (fst L))
                                              [] in _).
      exact (fun Γ' A => Γ' ,, vass (fst A) (tsl Γ' (snd A))).
      refine (List.fold_left _ L' _).
      exact (fun t decl => tProd decl.(decl_name) decl.(decl_type) t).
      exact (match snd L with
             | tApp t us => tApp t (List.map (tsl L') us)
             | _ as t => t
             end).
    * refine (fold_left_i (fun t l _ => replace (tRel l) (tInd (mkInd kn' i) []) t)
                          mind.(ind_bodies) ctor_type').
  + (* table *)
    refine (IndRef (mkInd kn i), pouet (tInd (mkInd kn' i) []) ind_type').
  + exact mind.(ind_finite).
  + (* parameters *)
    simple refine (List.fold_right _ [] (mind.(ind_params))).
    exact (fun A Γ' => Γ' ,, vass (decl_name A) (tsl Γ' (decl_type A))).
Defined.

Definition refresh_universe u :=
  if Universe.is_level u then u else fresh_universe.

Definition refresh_sort_universe := Sort.map refresh_universe.

Fixpoint refresh_universes (t : term) {struct t} :=
  match t with
  | tSort s => tSort (refresh_sort_universe s)
  | tProd na b t => tProd na b (refresh_universes t)
  | tLetIn na b t' t => tLetIn na b t' (refresh_universes t)
  | tCast x x0 x1 => tCast (refresh_universes x) x0 (refresh_universes x1)
  | tLambda x x0 x1 => tLambda x (refresh_universes x0) (refresh_universes x1)
  | tApp x x0 => tApp (refresh_universes x) (List.map refresh_universes x0)
  | tProj x x0 => tProj x (refresh_universes x0)
  | _ => t
  end.

Global Instance tsl_fun : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE t => t' <- tsl_rec fuel (fst ΣE) (snd ΣE) [] t ;;
                           ret (refresh_universes t');
        tsl_ty := Some (fun ΣE t => t' <- tsl_rec fuel (fst ΣE) (snd ΣE) [] t ;;
                                 ret (refresh_universes t')) ;
        tsl_ind := tsl_mind_body |}.


Tactic Notation "tSpecialize" ident(H) uconstr(t)
  := apply π1 in H; specialize (H t).
Tactic Notation "tIntro" ident(H)
  := refine (fun H => _; true).

Definition NotFunext :=
  ((forall (A B : Set) (f g : A -> B), (forall x:A, f x = g x) -> f = g) -> False).

Unset Universe Checking.

MetaRocq Run (TC <- TranslateRec emptyTC NotFunext ;;
                     tmDefinition "TC" TC ;;
                     Implement TC "notFunext" NotFunext).
Next Obligation.
  unfold NotFunextᵗ; cbn in *.
  tIntro H.
  tSpecialize H unit. tSpecialize H unit.
  tSpecialize H (fun x => x; true). tSpecialize H (fun x => x; false).
  tSpecialize H (fun x => eq_reflᵗ _ _; true).
  inversion H.
Defined.

MetaRocq Run (Implement TC "notη" ((forall (A B : Set) (f : A -> B), f = fun x => f x) -> False)).

Next Obligation.
  tIntro H.
  tSpecialize H unit. tSpecialize H unit.
  tSpecialize H (fun x => x; false). cbn in H.
  inversion H.
Defined.

(* Require Import Vector Even. *)
(* Definition SS := S. *)
(* MetaRocq Run (TC <- Translate emptyTC "nat" ;; *)
(*                      TC <- Translate TC "even" ;; *)
(*                      tmDefinition "TC2" TC). *)

(* Inductive foo := *)
(* | bar : (nat -> foo) -> foo. *)
(* Definition bar' := bar. *)
(* MetaRocq Run (TranslateRec TC2 bar'). *)


Definition UIP := forall A (x y : A) (p q : x = y), p = q.


MetaRocq Run (TC <- TranslateRec TC UIP ;;
                     tmDefinition "eqTC" TC).

Definition eqᵗ_eq {A} x y
  : eqᵗ A x y -> x = y.
Proof.
  destruct 1; reflexivity.
Defined.

Definition eq_eqᵗ {A} x y
  : x = y -> eqᵗ A x y.
Proof.
  destruct 1; reflexivity.
Defined.

Definition isequiv_eqᵗ_eq {A} x y
  : IsEquiv (@eqᵗ_eq A x y).
Proof.
  unshelve eapply isequiv_adjointify.
  apply eq_eqᵗ.
  all: intros []; reflexivity.
Defined.

Theorem preserves_UIP : UIP -> UIPᵗ.
Proof.
  unfold UIP, UIPᵗ.
  intros H.
  tIntro A. tIntro x. tIntro y. tIntro p. tIntro q.
  cbn in *.
  apply eq_eqᵗ. refine (equiv_inj _ (H := isequiv_eqᵗ_eq _ _) _).
  apply H.
Defined.


Definition wFunext
  := forall A (B : A -> Type) (f g : forall x, B x), (forall x, f x = g x) -> f = g.


MetaRocq Run (TC <- TranslateRec eqTC (wFunext -> False) ;;
                     tmDefinition "eqTC'" TC ;;
                     Implement TC "notwFunext" (wFunext -> False)).
Next Obligation.
  tIntro H.
  tSpecialize H unit. tSpecialize H (fun _ => unit; true).
  tSpecialize H (fun x => x; true). tSpecialize H (fun x => x; false).
  tSpecialize H (fun x => eq_reflᵗ _ _; true).
  inversion H.
Defined.

Definition wUnivalence
  := forall A B, Equiv A B -> A = B.

MetaRocq Run (TC <- Translate eqTC' "idpath" ;;
                     TC <- ImplementExisting TC "paths_ind" ;;
                     tmDefinition "eqTC''" TC).
Next Obligation.
  tIntro A. tIntro a. tIntro P. tIntro t.
  tIntro y. tIntro p. destruct p. exact t.
Defined.

MetaRocq Run (TC <- TranslateRec eqTC'' wUnivalence ;;
                     tmDefinition "eqTC3" TC).

Theorem preserves_wUnivalence : wUnivalence -> wUnivalenceᵗ.
Proof.
  unfold wUnivalence, wUnivalenceᵗ.
  intros H.
  tIntro A. tIntro B. tIntro H.
  cbn in *.
  apply eq_eqᵗ. apply H0. destruct H as [[f bf] Hf]; cbn in *.
  exists f. destruct Hf as [[g bg] [s _] [r _] _]; cbn in *.
  unshelve eapply isequiv_adjointify. assumption.
  all: intro; apply eqᵗ_eq; auto.
Defined.






Definition bool_of_Equivᵗ {A B} (e : Equivᵗ A B) : bool.
  now destruct e as [[_ b] _].
Defined.

Definition UA := forall A B, IsEquiv (paths_ind A (fun B _ => Equiv A B) (equiv_idmap A) B).

MetaRocq Run (TC <- Translate eqTC3 "isequiv_idmap" ;;
                     TC <- Translate TC "equiv_idmap" ;;
                     TC <- Translate TC "UA" ;;
                     tmDefinition "eqTC4" TC).

Axiom fx : Funext.
Axiom ua : UA.


Lemma eqᵗ_unit_unit (e e' : eqᵗ Type unit unit) : e = e'.
  refine (equiv_inj (eqᵗ_eq _ _) _).
  - apply isequiv_eqᵗ_eq.
  - refine (equiv_inj _ (H:=ua _ _) _).
    apply path_equiv; cbn. apply fx.
    apply fx. intro; apply path_unit.
Defined.


MetaRocq Run (Implement eqTC4 "notUA" (UA -> False)).
Next Obligation.
  unfold UAᵗ; tIntro ua.
  tSpecialize ua unit.
  tSpecialize ua unit.
  destruct ua as [[g bg] H1 H2 _]; cbn -[paths_indᵗ] in *.
  simple refine (let e1 := BuildEquivᵗ unit unit (idmap; true) _ in _); cbn. {
    unshelve econstructor; cbn. exact (idmap; true).
    all: tIntro x; reflexivity. }
  simple refine (let e2 := BuildEquivᵗ unit unit (idmap; false) _ in _); cbn. {
    unshelve econstructor; cbn. exact (idmap; true).
    all: tIntro x; reflexivity. }
  assert (e1 = e2). {
    etransitivity. symmetry. eapply eqᵗ_eq.
    exact (π1 H1 e1).
    etransitivity. 2: eapply eqᵗ_eq; exact (π1 H1 e2).
    clearbody e1 e2; clear.
    assert (g e1 = g e2). apply eqᵗ_unit_unit.
    now rewrite X. }
  apply (f_equal bool_of_Equivᵗ) in X. cbn in X.
  inversion X.
Defined.
