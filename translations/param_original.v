(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Translations Require Import translation_utils.
Import MonadNotation.

Local Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ^ msg).

Fixpoint tsl_rec0 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if n <= k then tRel (2*k-n+1) else t
  | tEvar k ts => tEvar k (map (tsl_rec0 n) ts)
  | tCast t c a => tCast (tsl_rec0 n t) c (tsl_rec0 n a)
  | tProd na A B => tProd na (tsl_rec0 n A) (tsl_rec0 (n+1) B)
  | tLambda na A t => tLambda na (tsl_rec0 n A) (tsl_rec0 (n+1) t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n t) (tsl_rec0 n A) (tsl_rec0 (n+1) u)
  | tApp t lu => tApp (tsl_rec0 n t) (map (tsl_rec0 n) lu)
  | tCase ik t u br => tCase ik (map_predicate_k id tsl_rec0 n t) (tsl_rec0 n u)
                            (map_branches_k tsl_rec0 n br)
  | tProj p t => tProj p (tsl_rec0 n t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Fixpoint tsl_rec1_app (app : option term) (E : tsl_table) (t : term) : term :=
  let tsl_rec1 := tsl_rec1_app None in
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  | tLambda na A t =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1_app None E A in
    tLambda na A0 (tLambda (tsl_name tsl_ident na)
                           (subst_app (lift0 1 A1) [tRel 0])
                           (tsl_rec1_app (option_map (lift 2 2) app) E t))
  | t => let t1 :=
  match t with
  | tRel k => tRel (2 * k)
  | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))

  | tProd na A B =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let B0 := tsl_rec0 1 B in
    let B1 := tsl_rec1 E B in
    let ΠAB0 := tProd na A0 B0 in
    tLambda (nNamed "f") ΠAB0
      (tProd na (lift0 1 A0)
             (tProd (tsl_name tsl_ident na)
                    (subst_app (lift0 2 A1) [tRel 0])
                    (subst_app (lift 1 2 B1)
                               [tApp (tRel 2) [tRel 1]])))
  | tApp t us =>
    let us' := concat (map (fun v => [tsl_rec0 0 v; tsl_rec1 E v]) us) in
    mkApps (tsl_rec1 E t) us'

  | tLetIn na t A u =>
    let t0 := tsl_rec0 0 t in
    let t1 := tsl_rec1 E t in
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let u0 := tsl_rec0 0 u in
    let u1 := tsl_rec1 E u in
    tLetIn na t0 A0 (tLetIn (tsl_name tsl_ident na) (lift0 1 t1)
                            (subst_app (lift0 1 A1) [tRel 0]) u1)

  | tCast t c A => let t0 := tsl_rec0 0 t in
                  let t1 := tsl_rec1 E t in
                  let A0 := tsl_rec0 0 A in
                  let A1 := tsl_rec1 E A in
                  tCast t1 c (mkApps A1 [tCast t0 c A0]) (* apply_subst ? *)

  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => t
    | None => debug "tConst" (string_of_kername s)
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => t
    | None => debug "tInd" (match i with mkInd s _ => string_of_kername s end)
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => t
    | None => debug "tConstruct" (match i with mkInd s _ => string_of_kername s end)
    end
  | tCase ik t u brs as case =>
    let t' := map_predicate_k id (fun x => lift x 0) 1 t in
    let brs' := map_branches_k (fun x => lift x 0) 1 brs in
    let case1 := tCase ik t' (tRel 0) brs' in
    match lookup_tsl_table E (IndRef ik.(ci_ind)) with
    | Some (tInd i _univ) =>
      let ci' := {| ci_ind := ik.(ci_ind); ci_npar := ik.(ci_npar) * 2; ci_relevance := ik.(ci_relevance) |} in
      tCase ci'
            (map_predicate_k id (fun k => tsl_rec1_app (Some (tsl_rec0 0 case1)) E) 0 t)
            (tsl_rec1 E u)
            (map_branches_k (fun k => tsl_rec1 E) 0 brs)
    | _ => debug "tCase" (match ik.(ci_ind) with mkInd s _ => string_of_kername s end)
    end
  | tProj _ _ => todo "tsl"
  | tFix _ _ | tCoFix _ _ => todo "tsl"
  | tVar _ | tEvar _ _ => todo "tsl"
  | tLambda _ _ _ => tVar "impossible"
  | tInt _ | tFloat _ | tArray _ _ _ _ | tString _ => todo "tsl"
  end in
  match app with Some t' => mkApp t1 (t' {3 := tRel 1} {2 := tRel 0})
               | None => t1 end
  end.
Definition tsl_rec1 := tsl_rec1_app None.

Definition tsl_mind_body (E : tsl_table) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  refine (_, [{| ind_npars := 2 * mind.(ind_npars);
                 ind_params := _;
                 ind_bodies := _;
                 ind_universes := mind.(ind_universes);
                 ind_variance := mind.(ind_variance)|}]).  (* FIXME always ok? *)
  - refine (let kn' : kername := (mp, tsl_ident kn.2) in
            fold_left_i (fun E i ind => _ :: _ ++ E) mind.(ind_bodies) []).
    + (* ind *)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
  - exact mind.(ind_finite).
  - (* params: 2 times the same parameters? Probably wrong *)
    refine (mind.(ind_params) ++ mind.(ind_params)).
  - refine (mapi _ mind.(ind_bodies)).
    intros i ind.
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_indices := ind.(ind_indices);
              ind_sort := ind.(ind_sort);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [];
              ind_relevance := ind.(ind_relevance) |}. (* UGLY HACK!!! todo *)
    + (* arity  *)
      refine (let ar := subst_app (tsl_rec1 E ind.(ind_type))
                                  [tInd (mkInd kn i) []] in
              ar).
    + (* constructors *)
      refine (mapi _ ind.(ind_ctors)).
      intros k c.
      refine {| cstr_name := tsl_ident c.(cstr_name); cstr_arity := 2 * c.(cstr_arity) |}%nat.
      exact c.(cstr_args). (* wrong probably *)
      exact c.(cstr_indices).
      refine (subst_app _ [tConstruct (mkInd kn i) k []]).
      refine (fold_left_i (fun t0 i u  => t0 {S i := u}) _ (tsl_rec1 E c.(cstr_type))).
      (* [I_n-1; ... I_0] *)
      refine (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies))).
Defined.


MetaRocq Run (typ <- tmQuote (forall A, A -> A) ;;
                     typ' <- tmEval all (tsl_rec1 [] typ) ;;
                     tm <- tmQuote (fun A (x : A) => x) ;;
                     tm' <- tmEval all (tsl_rec1 [] tm) ;;
                     tmUnquote (tApp typ' [tm]) >>= tmDebug).



#[export] Instance param : Translation :=
  {| tsl_id := tsl_ident ;
     tsl_tm := fun ΣE t => ret (tsl_rec1 (snd ΣE) t) ;
     (* Implement and Implement Existing cannot be used with this translation *)
     tsl_ty := None ;
     tsl_ind := fun ΣE mp kn mind =>
     ret (tsl_mind_body (snd ΣE) mp kn mind) |}.






Definition T := forall A, A -> A.
MetaRocq Run (Translate emptyTC "T").


Definition tm := ((fun A (x:A) => x) (Type -> Type) (fun x => x)).
MetaRocq Run (Translate emptyTC "tm").

MetaRocq Run (TC <- Translate emptyTC "nat" ;;
                     tmDefinition "nat_TC" TC ).

MetaRocq Run (TC <- Translate nat_TC "bool" ;;
                     tmDefinition "bool_TC" TC ).
Import Init.Nat.
(* todo "case" *)
(*
MetaRocq Run (Translate bool_TC "pred").


Module Id1.
  Definition ID := forall A, A -> A.

  MetaRocq Run (Translate emptyTC "ID").

  Lemma param_ID_identity (f : ID)
    : IDᵗ f -> forall A x, f A x = x.
  Proof.
    compute. intros H A x.
    exact (H A (fun y => y = x) x eq_refl).
  Qed.

  Definition toto := fun n : nat => (fun y => 0) (fun _ : Type =>  n).
  MetaRocq Run (Translate nat_TC "toto").


  Definition my_id : ID :=
    let n := 12 in (fun (_ : nat) y => y) 4 (fun A x => (fun _ : nat => x) n).

  MetaRocq Run (Translate nat_TC "my_id").


  Definition free_thm_my_id : forall A x, my_id A x = x
    := param_ID_identity my_id my_idᵗ.
End Id1.

Module Id2.
  Definition ID := forall A x y (p : x = y :> A), x = y.

  MetaRocq Run (TC <- TranslateRec emptyTC ID ;;
                       tmDefinition "TC" TC).


  Lemma param_ID_identity (f : ID)
    : IDᵗ f -> forall A x y p, f A x y p = p.
  Proof.
    compute. intros H A x y p.
    destruct p.
    specialize (H A (fun y => x = y) x eq_refl x eq_refl eq_refl
                  (eq_reflᵗ _ _ _ _)).
    destruct H. reflexivity.
  Qed.

  Definition myf : ID
    := fun A x y p => eq_trans (eq_trans p (eq_sym p)) p.

  MetaRocq Run (TranslateRec TC myf).

  Definition free_thm_myf : forall A x y p, myf A x y p = p
    := param_ID_identity myf myfᵗ.
End Id2.




Module Vectors.
  Import Vector.
  MetaRocq Run (Translate nat_TC "t").
End Vectors.

From Stdlib Require Import Even.
MetaRocq Run (Translate nat_TC "even").

Definition rev_type := forall A, list A -> list A.
MetaRocq Run (TC <- Translate emptyTC "list" ;;
                     TC <- Translate TC "rev_type" ;;
                     tmDefinition "list_TC" TC ).



From Stdlib Require Import MiniHoTT.
Module Axioms.

  Definition UIP := forall A (x y : A) (p q : x = y), p = q.

  MetaRocq Run (TC <- TranslateRec emptyTC UIP ;;
                       tmDefinition "eqTC" TC).

  Definition eqᵗ_eq {A Aᵗ x xᵗ y yᵗ p}
    : eqᵗ A Aᵗ x xᵗ y yᵗ p -> p # xᵗ = yᵗ.
  Proof.
    destruct 1; reflexivity.
  Defined.

  Definition eq_eqᵗ {A Aᵗ x xᵗ y yᵗ p}
    : p # xᵗ = yᵗ -> eqᵗ A Aᵗ x xᵗ y yᵗ p.
  Proof.
    destruct p, 1; reflexivity.
  Defined.

  Definition eqᵗ_eq_equiv A Aᵗ x xᵗ y yᵗ p
    : eqᵗ A Aᵗ x xᵗ y yᵗ p <~> p # xᵗ = yᵗ.
  Proof.
    unshelve eapply equiv_adjointify.
    - apply eqᵗ_eq.
    - apply eq_eqᵗ.
    - destruct p; intros []; reflexivity.
    - intros []; reflexivity.
  Defined.

  Theorem UIP_provably_parametric : forall h : UIP, UIPᵗ h.
  Proof.
    unfold UIP, UIPᵗ.
    intros h A Aᵗ x xᵗ y yᵗ p pᵗ q qᵗ.
    apply eq_eqᵗ.
    refine (equiv_inj _ (H := equiv_isequiv (eqᵗ_eq_equiv _ _ _ _ _ _ _)) _).
    apply h.
  Defined.


  Definition wFunext
    := forall A (B : A -> Type) (f g : forall x, B x), (forall x, f x = g x) -> f = g.


  MetaRocq Run (Translate eqTC "wFunext").

  Theorem wFunext_provably_parametric : forall h : wFunext, wFunextᵗ h.
  Proof.
    unfold wFunext, wFunextᵗ.
    intros h A Aᵗ B Bᵗ f fᵗ g gᵗ X H.
    apply eq_eqᵗ.
    apply h; intro x.
    apply h; intro xᵗ.
    specialize (H x xᵗ).
    apply eqᵗ_eq in H.
    refine (_ @ H).
    rewrite !transport_forall_constant.
    epose proof (transport_compose (Bᵗ x xᵗ) (fun x0 => x0 x) (h A B f g X) (fᵗ x xᵗ)).
    symmetry in X0.
    destruct X0.
    eapply ap10. eapply ap.
    (* rewrite ap_apply_lD. *)
  Abort.

  (* Definition Funext *)
  (*   := forall A B (f g : forall x : A, B x), IsEquiv (@apD10 A B f g). *)

  (* MetaRocq Run (TC <- TranslateRec eqTC Funext ;; *)
  (*                  tmDefinition "eqTC'" TC). *)


  (* Theorem Funext_provably_parametric : forall h : Funext, Funextᵗ h. *)
  (* Proof. *)
  (*   unfold Funext, Funextᵗ. *)
  (*   intros h A Aᵗ B Bᵗ f fᵗ g gᵗ. *)
  (*   (* unshelve eapply isequiv_adjointify. *) *)
  (*   (* apply eq_eqᵗ. *) *)
  (*   (* apply h; intro x. *) *)
  (*   (* apply h; intro xᵗ. *) *)
  (*   (* specialize (H x xᵗ). *) *)
  (*   (* apply eqᵗ_eq in H. *) *)
  (*   (* refine (_ @ H). *) *)
  (*   (* rewrite !transport_forall_constant. *) *)
  (*   (* rewrite transport_compose. *) *)
  (*   (* eapply ap10. eapply ap. *) *)
  (*   (* rewrite ap_apply_lD. *) *)
  (* Abort. *)

  Definition wUnivalence := forall A B, A <~> B -> A = B.

  MetaRocq Run (TC <- TranslateRec eqTC wUnivalence ;;
                          tmDefinition "eqTC1" TC).

  Theorem wUnivalence_provably_parametric : forall h, wUnivalenceᵗ h.
  Proof.
    intros H A A' B B' e e'.
    apply eq_eqᵗ.
  Abort.



  Definition equiv_paths {A B} (p : A = B) : A <~> B
    := transport (Equiv A) p equiv_idmap.

  Definition Univalence := forall A B (p : A = B), IsEquiv (equiv_paths p).

  Definition coe {A B} (p : A = B) : A -> B := transport idmap p.

  Definition Univalence' := forall A B (p : A = B), IsEquiv (coe p).

  MetaRocq Run (TC <- TranslateRec eqTC1 Univalence' ;;
                          tmDefinition "eqTC'" TC).


  Definition UU' : Univalence' -> Univalence.
    intros H A B []; exact (H A A 1).
  Defined.

  MetaRocq Run (TC <- TranslateRec eqTC' UU' ;;
                          tmDefinition "eqTC''" TC).

  (* Goal (Univalence -> Univalence') * (Univalence' -> Univalence). *)
  (*   split; intros H A B []; exact (H A A 1). *)
  (* Defined. *)

  Lemma pathsᵗ_ok {A} {Aᵗ : A -> Type} {x y} {xᵗ : Aᵗ y} (p : x = y)
    : pathsᵗ A Aᵗ x (transport Aᵗ p^ xᵗ) y xᵗ p.
  Proof.
    destruct p; reflexivity.
  Defined.

  Lemma pathsᵗ_ok2 {A} {Aᵗ : A -> Type} {x y} {xᵗ : Aᵗ y} (p q : x = y) e r
        (Hr : e # (pathsᵗ_ok p) = r)
    : pathsᵗ (x = y) (pathsᵗ A Aᵗ x (transport Aᵗ p^ xᵗ) y xᵗ) p (pathsᵗ_ok p) q r e.
    destruct e, p, Hr; reflexivity.
  Defined.

  Definition apᵗ_idmap  {A} {Aᵗ : A -> Type} {x y xᵗ yᵗ} (p : x = y)
             (pᵗ : pathsᵗ A Aᵗ x xᵗ y yᵗ p)
    : apᵗ A Aᵗ A Aᵗ idmap (fun u => idmap) x xᵗ y yᵗ p pᵗ = (ap_idmap p)^ # pᵗ.
  Proof.
    destruct pᵗ; reflexivity.
  Defined.

  Definition U'U : Univalence -> Univalence'.
    intros H A B []; exact (H A A 1).
  Defined.

  (* The import of CRelationClasses breaks rewrite *)
  Set Typeclasses Depth 4.

  Theorem Univalence'_provably_parametric : forall h : Univalence', Univalence'ᵗ h.
  Proof.
    unfold Univalence', Univalence'ᵗ.
    intros h A Aᵗ B Bᵗ p pᵗ.
    set (h A B p).
    destruct i as [g q1 q2 coh].
    destruct pᵗ; cbn in *.
    unshelve econstructor.
    intros. refine ((q1 _)^ # _); assumption.
    intros x xᵗ; cbn. apply pathsᵗ_ok.
    intros x xᵗ; cbn. refine ((coh x @ ap_idmap _) # pathsᵗ_ok (q1 x)).
    intros x xᵗ; cbn. eapply pathsᵗ_ok2.
    set (coh x). set (q1 x) in *. set (q2 x) in *.
    clearbody p p1 p0; clear; cbn in *.
    set (g x) in *. clearbody a. simpl.
    rewrite transport_pp.
    destruct p1. cbn in *.
    match goal with
    | |- ?XX = ?AA _ => set XX
    end.
    clearbody p1.
    assert (1 = p0^) by (rewrite p; reflexivity).
    destruct X; clear.
    change (p1 = apᵗ A Aᵗ A Aᵗ idmap (fun u => idmap) a xᵗ a xᵗ eq_refl p1).
    rewrite apᵗ_idmap. reflexivity.
  Defined.

  Definition Univalence_wFunext : Univalence -> wFunext.
  Admitted.

  Theorem Univalence_provably_parametric : forall h : Univalence, Univalenceᵗ h.
    intro h. pose proof (Univalence'_provably_parametric (U'U h)).
    apply UU'ᵗ in X. cbn in *.
    refine (_ # X). clear.
    pose proof (Univalence_wFunext h).
    apply X; intro A.
    apply X; intro B.
    apply X; intros []. reflexivity.
  Defined.
End Axioms.

*)



(* Record IsEquiv' {A B} (f : A -> B) := BuildIsEquiv' *)
(*   { equiv_inv' : B -> A; *)
(*     eisretr' : Sect equiv_inv' f; *)
(*     eissect' : Sect f equiv_inv'}. *)

(* Definition IsEquiv_IsEquiv' {A B} (f : A -> B) *)
(*   : IsEquiv' f -> IsEquiv f. *)
(* Proof. *)
(*   intros [g H1 H2]. unshelve eapply isequiv_adjointify; eassumption. *)
(* Defined. *)

(* Definition IsEquiv'_IsEquiv {A B} (f : A -> B) *)
(*   : IsEquiv f -> IsEquiv' f. *)
(* Proof. *)
(*   intros [g H1 H2 _]; econstructor; eassumption. *)
(* Defined. *)

(* Record Equiv' A B := *)
(*   { equiv_fun' : A -> B ; *)
(*     equiv_isequiv' : IsEquiv' equiv_fun' }. *)

(* Definition equiv_idmap' (A : Type) : Equiv' A A. *)
(*   refine (Build_Equiv' A A idmap _). *)
(*   unshelve econstructor. exact idmap. *)
(*   all: intro; reflexivity. *)
(* Defined. *)

(* Arguments equiv_idmap' {A} , A. *)
