(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Translations Require Import translation_utils.
Import MonadNotation.

Local Infix "<=" := Nat.leb.

Definition default_term   := tVar "constant_not_found".
Definition debug_term msg := tVar ("debug: " ^ msg).

Fixpoint tsl_rec0 (n : nat) (o : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if n <= k then (* global variable *) tRel (3 * (k - n) + n + o)
                        else (* local  variable *) t
  | tEvar k ts   => tEvar k (map (tsl_rec0 n o) ts)
  | tCast t c a  => tCast (tsl_rec0 n o t) c (tsl_rec0 n o a)
  | tProd na A B => tProd na (tsl_rec0 n o A) (tsl_rec0 (n+1) o B)
  | tLambda na A t  => tLambda na (tsl_rec0 n o A) (tsl_rec0 (n+1) o t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n o t) (tsl_rec0 n o A) (tsl_rec0 (n+1) o u)
  | tApp t lu       => tApp (tsl_rec0 n o t) (map (tsl_rec0 n o) lu)
  | tCase ik t u br => tCase ik (map_predicate_k id (fun k => tsl_rec0 n k) o t) (tsl_rec0 n o u)
                            (map_branches_k (fun x => tsl_rec0 n x) o br)
  | tProj p t => tProj p (tsl_rec0 n o t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.


Definition suffix0 (n : name) s : name :=
  match n with
  | BasicAst.nAnon     => BasicAst.nAnon
  | BasicAst.nNamed id => BasicAst.nNamed (id ^ s)
  end.

Definition nAnon := {| binder_name := BasicAst.nAnon; binder_relevance := Relevant |}.
Definition nNamed n := {| binder_name := BasicAst.nNamed n; binder_relevance := Relevant |}.

Definition suffix na n := map_binder_annot (fun na => suffix0 na n) na.


Fixpoint apply (app : list term) (t : term) :=
  match app with
  | t' :: app =>  apply app (mkApp t (t' {3 := tRel 1} {2 := tRel 0}))
  | [] => t
  end.

Fixpoint tsl_rec1_app (app : list term) (E : tsl_table) (t : term) : term :=
  let tsl_rec1 := tsl_rec1_app [] in
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  | tLambda na A t =>
      let A0 := tsl_rec0 0 2 A in
      let A1 := tsl_rec1 E A in

      tLambda (suffix na "₁") A0
        (tLambda (suffix na "₂") A0
          (tLambda (tsl_name tsl_ident na)
            (subst_app (lift0 2 A1) [tRel 1; tRel 0])
            (tsl_rec1_app (map (lift 3 3) app) E t)))

  | _ => let t1 :=
  match t with
  | tSort s =>
      tLambda (nNamed "x₁") (tSort s)
        (tLambda (nNamed "x₂") (tSort s)
          (tProd nAnon (tRel 1) (tProd nAnon (tRel 1) (tSort s))))

  | tRel k => tRel (3 * k)

  | tProd na A B =>
      let A0 := tsl_rec0 0 2 A in
      let B0 := tsl_rec0 1 2 B in
      let A1 := tsl_rec1 E A in
      let B1 := tsl_rec1 E B in
      let ΠAB0 := tProd na A0 B0 in

      tLambda (nNamed "f₁") ΠAB0
        (tLambda (nNamed "f₂") ΠAB0
          (tProd (suffix na "₁") (lift0 2 A0)
            (tProd (suffix na "₂") (lift0 2 A0)
              (tProd (tsl_name tsl_ident na)
                (subst_app (lift0 4 A1) [tRel 1; tRel 0])
                (subst_app (lift 2 3 B1) [tApp (tRel 4) [tRel 2]; tApp (tRel 3) [tRel 1]])))))

  | tApp t us =>
      let us' := concat (map (fun v => [tsl_rec0 0 2 v; tsl_rec0 0 1 v; tsl_rec1 E v]) us) in
      mkApps (tsl_rec1 E t) us'

  | tCast t c A =>
      let t0 := tsl_rec0 0 2 t in
      let t1 := tsl_rec1 E t in
      let A0 := tsl_rec0 0 2 A in
      let A1 := tsl_rec1 E A in
      tCast t1 c (mkApps A1 [tCast t0 c A0])

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
    case
    (* todo "case", but probably already wrong before
      let brs' := (map_branches_k (fun x => lift x 0) 1 brs) in
    let case1 := tCase ik (map_predicate_k id (fun x => lift x 0) 3 t) (tRel 2) brs' in
    let case2 := tCase ik (map_predicate_k id (fun x => lift x 0) 3 t) (tRel 1) brs' in
       match lookup_tsl_table E (IndRef ik.(ci_ind)) with
      | Some (tInd i _univ) =>
        let ci' := {| ci_ind := i; ci_npar := 3 * ci.(ci_npar); ci_relevance := ci.(ci_relevance) |} in
        tCase ci'
              (tsl_rec1_app [tsl_rec0 0 2 case1; tsl_rec0 0 1 case2] E t)
              (tsl_rec1 E u)
              (map (on_snd (tsl_rec1 E)) brs)
      | _ => debug "tCase" (match ik.(ci_ind) with mkInd s _ => string_of_kername s end)
      end*)

  | tLetIn na t A u =>
    let t0 := tsl_rec0 0 2 t in
    let A0 := tsl_rec0 0 2 A in
    let t1 := tsl_rec1 E t in
    let A1 := tsl_rec1 E A in
    let u1 := tsl_rec1 E u in
    tLetIn (suffix na "₁") t0 A0 (
      tLetIn (suffix na "₂") (lift0 1 t0) (lift0 1 A0) (
        tLetIn (tsl_name tsl_ident na) (lift0 2 t1)
          (subst_app (lift0 2 A1) [tRel 1; tRel 0]) u1))

  | tProj _ _ => todo "tsl"
  | tFix _ _ | tCoFix _ _ => todo "tsl"
  | tVar _ | tEvar _ _ => todo "tsl"
  | tLambda _ _ _ => tVar "impossible"
  | tInt _ | tFloat _ | tArray _ _ _ _ | tString _ => todo "tsl"
  end
  in apply app t1
  end.

Definition tsl_rec1 := tsl_rec1_app [].

Definition tsl_mind_body (E : tsl_table) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  refine (_, [{| ind_npars := 3 * mind.(ind_npars);
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
    refine (mind.(ind_params) ++ mind.(ind_params) ++ mind.(ind_params)).
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
                                  [tInd (mkInd kn i) []; tInd (mkInd kn i) []] in
              ar).
    + (* constructors *)
      refine (mapi _ ind.(ind_ctors)).
      intros k [name args indices type arity].
      econstructor.
      refine (tsl_ident name).
      refine args.
      refine indices.
      refine (subst_app _ [tConstruct (mkInd kn i) k []; tConstruct (mkInd kn i) k []]).
      refine (fold_left_i (fun t0 i u => t0 {S i := u} {S i := u}) _ (tsl_rec1 E type)).
      (* [I_0; ... I_(n-1)] *)

      refine (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies))).
      refine (3 * arity)%nat.

Defined.

#[global]
Instance param : Translation :=
  {| tsl_id := tsl_ident ;
     tsl_tm := fun ΣE t => ret (tsl_rec1 (snd ΣE) t) ;
     (* Implement and Implement Existing cannot be used with this translation *)
     tsl_ty  := None ;
     tsl_ind := fun ΣE mp kn mind => ret (tsl_mind_body (snd ΣE) mp kn mind) |}.

(* EXAMPLES *)

MetaRocq Run (
  typ <- tmQuote (forall A, A -> A) ;;
  typ' <- tmEval all (tsl_rec1 [] typ) ;;
  tm <- tmQuote (fun A (x : A) => x) ;;
  tm' <- tmEval all (tsl_rec1 [] tm) ;;
  tmUnquote (tApp typ' [tm; tm]) >>= tmDebug ;;
  tmUnquote tm' >>= tmDebug
).

Set Warnings "-unexpected-implicit-declaration".
MetaRocq Run (
  typ <- tmQuote (forall A B, B -> (A -> B -> B) -> B) ;;
  typ' <- tmEval all (tsl_rec1 [] typ) ;;
  t   <- tmQuote (fun {A B} (x:B) (f : A -> B -> B) => x) ;;
  t'  <- tmEval all (tsl_rec1 [] t) ;;
  tmUnquote (tApp typ' [t; t]) >>= tmDebug
).

MetaRocq Run (TC <- Translate emptyTC "nat" ;;
                     tmDefinition "nat_TC" TC).

MetaRocq Run (TC <- Translate nat_TC "bool" ;;
                     tmDefinition "bool_TC" TC).

MetaRocq Run (TC <- Translate bool_TC "list" ;;
                     tmDefinition "list_TC" TC).

Module FreeTheorems.

  Definition HD := forall X, list X -> X.
  MetaRocq Run (Translate list_TC "HD").

  Definition MAP := forall X, list X -> list X.
  MetaRocq Run (Translate list_TC "MAP").

  (* taken from coq-community/paramcoq *)
  Definition graph {A B} (f : A -> B) := fun x y => f x = y.
  Definition map_rel {A B} (f : A -> B) := listᵗ A B (graph f).

  Definition map_rel_map A B (f : A -> B) :
    forall (l : list A), map_rel f l (map f l).
  induction l; constructor; compute; auto.
  Defined.

  Lemma rel_map_map A B (f : A -> B) :
    forall (l : list A) fl, map_rel f l fl -> fl = map f l.
  intros l fl H. induction H; unfold graph in *; subst; auto.
  Defined.

  Definition FREE_THEOREM (F : MAP) :=
    forall A B (f : A -> B) l,
      F B (map f l) = map f (F A l).

  Lemma param_map :
    forall F (H : MAPᵗ F F), FREE_THEOREM F.
  Proof.
    repeat intro.
    apply rel_map_map.
    apply H.
    apply map_rel_map.
  Qed.

End FreeTheorems.
