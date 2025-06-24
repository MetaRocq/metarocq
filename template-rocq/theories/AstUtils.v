(* For primitive integers and floats  *)
From Stdlib Require Numbers.Cyclic.Int63.Uint63 Floats.PrimFloat.
(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import BasicAst Primitive Environment.
From MetaRocq.Template Require Import Ast.
From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import ZArith.

#[local] Set Universe Polymorphism.

(** Raw term printing *)

Module string_of_term_tree.
  Import bytestring.Tree.
  Infix "^" := append.

  Definition string_of_predicate {term} (f : term -> t) (p : predicate term) :=
    "(" ^ "(" ^ concat "," (map f (pparams p)) ^ ")"
    ^ "," ^ string_of_universe_instance (puinst p)
    ^ ",(" ^ String.concat "," (map (string_of_name ∘ binder_name) (pcontext p)) ^ ")"
    ^ "," ^ f (preturn p) ^ ")".

  Definition string_of_branch (f : term -> t) (b : branch term) :=
    "([" ^ String.concat "," (map (string_of_name ∘ binder_name) (bcontext b)) ^ "], "
    ^ f (bbody b) ^ ")".

  Definition string_of_def {A} (f : A -> t) (def : def A) :=
    "(" ^ string_of_name (binder_name (dname def))
      ^ "," ^ string_of_relevance (binder_relevance (dname def))
      ^ "," ^ f (dtype def)
      ^ "," ^ f (dbody def)
      ^ "," ^ string_of_nat (rarg def) ^ ")".

  Fixpoint string_of_term (t : term) : Tree.t :=
  match t with
  | tRel n => "Rel(" ^ string_of_nat n ^ ")"
  | tVar n => "Var(" ^ n ^ ")"
  | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "," ^ string_of_list string_of_term args ^ ")"
  | tSort s => "Sort(" ^ string_of_sort s ^ ")"
  | tCast c k t => "Cast(" ^ string_of_term c ^ (* TODO *) ","
                           ^ string_of_term t ^ ")"
  | tProd na b t => "Prod(" ^ string_of_name na.(binder_name) ^ ","
                            ^ string_of_relevance na.(binder_relevance) ^ ","
                            ^ string_of_term b ^ ","
                            ^ string_of_term t ^ ")"
  | tLambda na b t => "Lambda(" ^ string_of_name na.(binder_name) ^ ","
                                ^ string_of_term b ^ ","
                                ^ string_of_relevance na.(binder_relevance) ^ ","
                                ^ string_of_term t ^ ")"
  | tLetIn na b t' t => "LetIn(" ^ string_of_name na.(binder_name) ^ ","
                                 ^ string_of_relevance na.(binder_relevance) ^ ","
                                 ^ string_of_term b ^ ","
                                 ^ string_of_term t' ^ ","
                                 ^ string_of_term t ^ ")"
  | tApp f l => "App(" ^ string_of_term f ^ "," ^ string_of_list string_of_term l ^ ")"
  | tConst c u => "Const(" ^ string_of_kername c ^ "," ^ string_of_universe_instance u ^ ")"
  | tInd i u => "Ind(" ^ string_of_inductive i ^ "," ^ string_of_universe_instance u ^ ")"
  | tConstruct i n u => "Construct(" ^ string_of_inductive i ^ "," ^ string_of_nat n ^ ","
                                    ^ string_of_universe_instance u ^ ")"
  | tCase ci p t brs =>
    "Case(" ^ string_of_case_info ci ^ ","
            ^ string_of_predicate string_of_term p ^ ","
            ^ string_of_term t ^ ","
            ^ string_of_list (string_of_branch string_of_term) brs ^ ")"
  | tProj p c =>
    "Proj(" ^ string_of_inductive p.(proj_ind) ^ "," ^ string_of_nat p.(proj_npars) ^ "," ^ string_of_nat p.(proj_arg) ^ ","
            ^ string_of_term c ^ ")"
  | tFix l n => "Fix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tCoFix l n => "CoFix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tInt i => "Int(" ^ string_of_prim_int i ^ ")"
  | tFloat f => "Float(" ^ string_of_float f ^ ")"
  | tString s => "String(" ^ string_of_pstring s ^ ")"
  | tArray u arr def ty => "Array(" ^ string_of_level u ^ "," ^
    string_of_list string_of_term arr ^ "," ^ string_of_term def ^ "," ^ string_of_term ty ^ ")"
  end.
End string_of_term_tree.

Definition string_of_term := Tree.to_string ∘ string_of_term_tree.string_of_term.

Definition decompose_app (t : term) :=
  match t with
  | tApp f l => (f, l)
  | _ => (t, [])
  end.

Lemma decompose_app_mkApps f l :
  ~~ isApp f -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. rewrite /decompose_app.
  destruct l. simpl. destruct f; try discriminate; auto.
  remember (mkApps f (t :: l)) eqn:Heq. simpl in Heq.
  destruct f; simpl in *; subst; auto.
Qed.

Lemma atom_decompose_app t : ~~ isApp t -> decompose_app t = (t, []).
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_mkApp u a v : mkApps (mkApp u a) v = mkApps u (a :: v).
Proof.
  induction v. simpl.
  destruct u; simpl; try reflexivity.
  intros. simpl.
  destruct u; simpl; try reflexivity.
  now rewrite <- app_assoc.
Qed.

Lemma mkApps_eq_inj {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  ~~ isApp t -> ~~ isApp t' -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ.
  rewrite !decompose_app_mkApps in Happ => //. intuition congruence.
Qed.

Inductive mkApps_spec : term -> list term -> term -> list term -> term -> Type :=
| mkApps_intro f l n :
    ~~ isApp f ->
    mkApps_spec f l (mkApps f (firstn n l)) (skipn n l) (mkApps f l).

Definition is_empty {A} (l : list A) :=
  if l is nil then true else false.

Lemma is_empty_app {A} (l l' : list A) : is_empty (l ++ l') = is_empty l && is_empty l'.
Proof.
  induction l; simpl; auto.
Qed.

Lemma mkApps_tApp f args :
  ~~ isApp f ->
  ~~ is_empty args ->
  tApp f args = mkApps f args.
Proof.
  intros.
  destruct args, f; try discriminate; auto.
Qed.

Lemma nApp_mkApps {t l} : ~~ isApp (mkApps t l) -> ~~ isApp t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (isApp t) eqn:Heq. destruct t; try discriminate.
  destruct t; try discriminate.
Qed.

Lemma mkApps_nisApp {t t' l} : mkApps t l = t' -> ~~ isApp t' -> t = t' /\ l = [].
Proof.
  intros <-. intros. eapply nApp_mkApps in H. intuition auto.
  now subst.
Qed.

Ltac solve_discr' :=
  match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : ?t = mkApps ?f ?l |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  end.

Lemma mkApps_app f l l' : mkApps f (l ++ l') = mkApps (mkApps f l) l'.
Proof.
  induction l; destruct f; destruct l'; simpl; rewrite ?app_nil_r; auto.
  f_equal. now rewrite <- app_assoc.
Qed.

Lemma mkApp_mkApps f a l : mkApp (mkApps f l) a = mkApps f (l ++ [a]).
Proof.
  destruct l. simpl. reflexivity.
  rewrite mkApps_app //.
Qed.

Lemma mkAppMkApps s t:
  mkApp s t = mkApps s [t].
Proof. reflexivity. Qed.

Lemma mkApp_tApp f u : isApp f = false -> mkApp f u = tApp f [u].
Proof. intros. destruct f; (discriminate || reflexivity). Qed.

Fixpoint decompose_prod (t : term) : (list aname) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* TODO *)
          end
  end.

Fixpoint lookup_mind_decl (id : kername) (decls : global_declarations)
 := match decls with
    | nil => None
    | (kn, InductiveDecl d) :: tl =>
      if kn == id then Some d else lookup_mind_decl id tl
    | _ :: tl => lookup_mind_decl id tl
    end.

(* TODO factorize in Environment *)
(* was mind_decl_to_entry *)
Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _ (* Should be ind_params, but translations are broken: for Simon decl.(ind_params) *);
            mind_entry_inds := _;
            mind_entry_universes := universes_entry_of_decl decl.(ind_universes);
            mind_entry_template := false;
            mind_entry_variance := option_map (map Some) decl.(ind_variance);
            mind_entry_private := None |}.
  - (* FIXME: this is wrong, the info should be in ind_params *)
   refine (match List.hd_error decl.(ind_bodies) with
  | Some i0 => List.rev _
  | None => nil (* assert false: at least one inductive in a mutual block *)
  end).
  pose (typ := decompose_prod i0.(ind_type)).
destruct typ as [[names types] _].
apply (List.firstn decl.(ind_npars)) in names.
apply (List.firstn decl.(ind_npars)) in types.
  refine (map (fun '(x, ty) => vass x ty) (combine names types)).
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name0;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type0;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => cstr_name x) ind_ctors0).
    refine (List.map (fun x => remove_arity decl.(ind_npars) (cstr_type x)) ind_ctors0).
Defined.

Fixpoint strip_casts t :=
  match t with
  | tEvar ev args => tEvar ev (List.map strip_casts args)
  | tLambda na T M => tLambda na (strip_casts T) (strip_casts M)
  | tApp u v => mkApps (strip_casts u) (List.map (strip_casts) v)
  | tProd na A B => tProd na (strip_casts A) (strip_casts B)
  | tCast c kind t => strip_casts c
  | tLetIn na b t b' => tLetIn na (strip_casts b) (strip_casts t) (strip_casts b')
  | tCase ind p c brs =>
    let p' := map_predicate id strip_casts strip_casts p in
    let brs' := List.map (map_branch strip_casts) brs in
    tCase ind p' (strip_casts c) brs'
  | tProj p c => tProj p (strip_casts c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tCoFix mfix' idx
  | tArray u arr def ty =>
    tArray u (List.map strip_casts arr) (strip_casts def) (strip_casts ty)
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => t
  | tInt _ | tFloat _ | tString _ => t
  end.

Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | _ => (Γ, t)
  end.

Fixpoint strip_outer_cast t :=
  match t with
  | tCast t _ _ => strip_outer_cast t
  | _ => t
  end.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match strip_outer_cast t with
    | tProd na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Fixpoint decompose_lam_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match strip_outer_cast t with
    | tLambda na A B => decompose_lam_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_lam_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite length_app /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  match t with
  | tInd _ _ => true
  | tApp (tInd _ _) _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof. now destruct l; simpl. Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition lookup_minductive Σ mind :=
  match lookup_env Σ mind with
  | Some (InductiveDecl decl) => Some decl
  | _ => None
  end.

Definition lookup_inductive Σ ind :=
  match lookup_minductive Σ (inductive_mind ind) with
  | Some mdecl =>
    match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
    | Some idecl => Some (mdecl, idecl)
    | None => None
    end
  | None => None
  end.

Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Definition forget_types {term} (c : list (BasicAst.context_decl term)) : list aname :=
  map decl_name c.

Import MRMonadNotation.

Definition mkCase_old (Σ : global_env) (ci : case_info) (p : term) (c : term) (brs : list (nat × term)) : option term :=
  '(mib, oib) <- lookup_inductive Σ ci.(ci_ind) ;;
  '(pctx, preturn) <- decompose_lam_n_assum [] (S #|oib.(ind_indices)|) p ;;
  '(puinst, pparams, pctx) <-
    match pctx with
    | {| decl_name := na; decl_type := tind; decl_body := Datatypes.None |} :: indices =>
      let (hd, args) := decompose_app tind in
      match destInd hd with
      | Datatypes.Some (ind, u) => ret (u, firstn mib.(ind_npars) args, forget_types indices)
      | Datatypes.None => raise tt
      end
    | _ => raise tt
    end ;;
  let p' :=
    {| puinst := puinst; pparams := pparams; pcontext := pctx; preturn := preturn |}
  in
  brs' <-
    monad_map2 (E:=unit) (ME:=option_monad_exc) (fun cdecl br =>
      '(bctx, bbody) <- decompose_lam_n_assum [] #|cdecl.(cstr_args)| br.2 ;;
      ret {| bcontext := forget_types bctx; bbody := bbody |})
      tt oib.(ind_ctors) brs ;;
  ret (tCase ci p' c brs').

Definition default_sort_quality_or_set (s : sort) : allowed_eliminations :=
  match s with
  | sSProp => IntoSProp
  | sProp => IntoPropSProp
  | _ => IntoAny
  end.

(** Convenience functions for building constructors and inductive declarations *)

(** The [indrel] argument represents the de Bruijn associated to the inductive in the mutual block.
    index 0 represents the LAST inductive in the block.
    The [params] is the context of parameters of the whole inductive block.
    The [args] context represents the argument types of the constructor (the last argument
    of the constructor is the first item in this list, as contexts are represented as snoc lists). *)
Definition make_constructor_body (id : ident) (indrel : nat)
  (params : context) (args : context) (index_terms : list term)
  : constructor_body :=
  {| cstr_name := id;
     cstr_args := args;
     cstr_indices := index_terms;
     cstr_type := it_mkProd_or_LetIn (params ,,, args)
      (mkApps (tRel (#|args| + #|params| + indrel))
        (to_extended_list_k params #|args| ++ index_terms));
     cstr_arity := context_assumptions args |}.

(** Makes a simple inductive body with no projections, and "standard" universe and elimination rules
  derived from the universe (i.e. does not handle inductives with singleton elimination, or impredicate set
  eliminations). *)
Definition make_inductive_body (id : ident) (params : context) (indices : context)
   (s : sort) (ind_ctors : list constructor_body) : one_inductive_body :=
  {| ind_name := id;
     ind_indices := indices;
     ind_sort := s;
     ind_type := it_mkProd_or_LetIn (params ,,, indices) (tSort s);
     ind_kelim := default_sort_quality_or_set s;
     ind_ctors := ind_ctors;
     ind_projs := [];
     ind_relevance := relevance_of_sort s |}.

Ltac change_Sk :=
  repeat match goal with
    | |- context [S (?x + ?y)] => progress change (S (x + y)) with (S x + y)
    | |- context [#|?l| + (?x + ?y)] => progress replace (#|l| + (x + y)) with ((#|l| + x) + y) by now rewrite Nat.add_assoc
  end.

#[global] Hint Extern 10 => progress unfold map_branches_k : all.
#[global] Hint Extern 10 => rewrite !map_branch_map_branch : all.

Definition tCaseBrsType {A} (P : A -> Type) (l : list (branch A)) :=
  All (fun x => P (bbody x)) l.

Definition tFixType {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Ltac solve_all_one :=
  try lazymatch goal with
  | H: tCasePredProp _ _ _ |- _ => destruct H
  end;
  unfold tCaseBrsProp, tFixProp, tCaseBrsType, tFixType in *;
  try apply map_predicate_eq_spec;
  try apply map_predicate_id_spec;
  repeat toAll; try All_map; try close_Forall;
  change_Sk; auto with all;
  intuition eauto 4 with all.

Ltac solve_all := repeat (progress solve_all_one).

Ltac nth_leb_simpl :=
  match goal with
    |- context [leb ?k ?n] => elim (leb_spec_Set k n); try lia; simpl
  | |- context [nth_error ?l ?n] => elim (nth_error_spec l n); rewrite -> ?length_app, ?length_map;
                                    try lia; intros; simpl
  | H : context[nth_error (?l ++ ?l') ?n] |- _ =>
    (rewrite -> (nth_error_app_ge l l' n) in H by lia) ||
    (rewrite -> (nth_error_app_lt l l' n) in H by lia)
  | H : nth_error ?l ?n = Some _, H' : nth_error ?l ?n' = Some _ |- _ =>
    replace n' with n in H' by lia; rewrite -> H in H'; injection H'; intros; subst
  | _ => lia || congruence || solve [repeat (f_equal; try lia)]
  end.

(** * Traversal functions. *)

Section TraverseWithBinders.
Context {Acc : Type} {A : Type} (a : A) (lift : aname -> A -> A).

Definition lift_names : list aname -> A -> A :=
  fun names a => List.fold_right lift a names.

Definition map_predicate_with_binders (f : A -> term -> term) (p : predicate term) : predicate term :=
  let a_return := lift_names p.(pcontext) a in
  {| puinst := p.(puinst)
  ;  pparams := List.map (f a) p.(pparams)
  ;  pcontext := p.(pcontext)
  ;  preturn := f a_return p.(preturn) |}.

Definition map_branch_with_binders (f : A -> term -> term) (b : branch term) : branch term :=
  let a_body := lift_names b.(bcontext) a in
  {| bcontext := b.(bcontext) ; bbody := f a_body b.(bbody) |}.

(** [map_term_with_binders a lift f t] maps [f] on the immediate subterms of [t].
    It carries an extra data [a] (typically a lift index) which is processed by [lift]
    (which typically add 1 to [a]) at each binder traversal.
    It is not recursive and the order in which subterms are processed is not specified. *)
Definition map_term_with_binders (f : A -> term -> term) (t : term) : term :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map (f a) ts)
  | tCast b k t => tCast (f a b) k (f a t)
  | tProd name ty body => tProd name (f a ty) (f (lift name a) body)
  | tLambda name ty body => tLambda name (f a ty) (f (lift name a) body)
  | tLetIn name def ty body => tLetIn name (f a def) (f a ty) (f (lift name a) body)
  | tApp func args => tApp (f a func) (List.map (f a) args)
  | tProj proj t => tProj proj (f a t)
  (* For [tFix] and [tCoFix] we have to take care to lift [a]
     only when processing the body of the (co)fixpoint. *)
  | tFix defs i =>
    let a_body := lift_names (List.map dname defs) a in
    let on_def := map_def (f a) (f a_body) in
    tFix (List.map on_def defs) i
  | tCoFix defs i =>
    let a_body := lift_names (List.map dname defs) a in
    let on_def := map_def (f a) (f a_body) in
    tCoFix (List.map on_def defs) i
  | tCase ci pred x branches =>
    tCase ci (map_predicate_with_binders f pred) (f a x) (List.map (map_branch_with_binders f) branches)
  | tArray l t def ty => tArray l (List.map (f a) t) (f a def) (f a ty)
  end.

Definition fold_predicate_with_binders (f : A -> Acc -> term -> Acc) (acc : Acc) (p : predicate term) : Acc :=
  let a_return := lift_names p.(pcontext) a in
  let acc := List.fold_left (f a) p.(pparams) acc in
  f a_return acc p.(preturn).

Definition fold_branch_with_binders (f : A -> Acc -> term -> Acc) (acc : Acc) (b : branch term) : Acc :=
  let a_body := lift_names b.(bcontext) a in
  f a_body acc b.(bbody).

(** Fold version of [map_term_with_binders]. *)
Definition fold_term_with_binders (f : A -> Acc -> term -> Acc) (acc : Acc) (t : term) : Acc :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _
  | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => acc
  | tEvar n ts => List.fold_left (f a) ts acc
  | tCast b k t => let acc := f a acc b in f a acc t
  | tProd name ty body => let acc := f a acc ty in f (lift name a) acc body
  | tLambda name ty body => let acc := f a acc ty in f (lift name a) acc body
  | tLetIn name def ty body =>
    let acc := f a acc def in
    let acc := f a acc ty in
    f (lift name a) acc body
  | tApp func args => List.fold_left (f a) (func :: args) acc
  | tProj proj t => f a acc t
  | tFix defs i =>
    let a_body := lift_names (List.map dname defs) a in
    let acc := List.fold_left (f a) (List.map dtype defs) acc in
    List.fold_left (f a_body) (List.map dbody defs) acc
  | tCoFix defs i =>
    let a_body := lift_names (List.map dname defs) a in
    let acc := List.fold_left (f a) (List.map dtype defs) acc in
    List.fold_left (f a_body) (List.map dbody defs) acc
  | tCase ci pred x branches =>
    let acc := fold_predicate_with_binders f acc pred in
    let acc := f a acc x in
    List.fold_left (fold_branch_with_binders f) branches acc
  | tArray l t def ty =>
    let acc := List.fold_left (f a) t acc in
    let acc := f a acc def in
    f a acc ty
  end.

End TraverseWithBinders.

Section TraverseWithBindersM.
Import MRMonadNotation.

Context {M : Type -> Type} `{Monad M} {Acc : Type} {A : Type} {a : A} {liftM : aname -> A -> M A}.

Definition lift_namesM (names : list aname) (a : A) : M A :=
  let fix loop names a :=
    match names with
    | [] => ret a
    | n :: names => loop names =<< liftM n a
    end
  in
  loop (List.rev names) a.

Definition map_defM {A B} (tyf bodyf : A -> M B) (d : def A) : M (def B) :=
  mlet dtype <- tyf d.(dtype) ;;
  mlet dbody <- bodyf d.(dbody) ;;
  ret (mkdef _ d.(dname) dtype dbody d.(rarg)).

Definition map_predicate_with_bindersM (f : A -> term -> M term) (p : predicate term) : M (predicate term) :=
  mlet a_return <- lift_namesM p.(pcontext) a ;;
  mlet pparams <- monad_map (f a) p.(pparams) ;;
  mlet preturn <- f a_return p.(preturn) ;;
  ret (mk_predicate p.(puinst) pparams p.(pcontext) preturn).

Definition map_branch_with_bindersM (f : A -> term -> M term) (b : branch term) : M (branch term) :=
  mlet a_body <- lift_namesM b.(bcontext) a ;;
  mlet bbody <- f a_body b.(bbody) ;;
  ret (mk_branch b.(bcontext) bbody).

(** Monadic variant of [map_term_with_binders]. *)
Definition map_term_with_bindersM (f : A -> term -> M term) (t : term) : M term :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _
  | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => ret t
  | tEvar n ts =>
    mlet ts <- monad_map (f a) ts ;;
    ret (tEvar n ts)
  | tCast b k t =>
    mlet b <- f a b ;;
    mlet t <- f a t ;;
    ret (tCast b k t)
  | tProd name ty body =>
    mlet ty <- f a ty ;;
    mlet a_body <- liftM name a ;;
    mlet body <- f a_body body ;;
    ret (tProd name ty body)
  | tLambda name ty body =>
    mlet ty <- f a ty ;;
    mlet a_body <- liftM name a ;;
    mlet body <- f a_body body ;;
    ret (tLambda name ty body)
  | tLetIn name def ty body =>
    mlet def <- f a def ;;
    mlet ty <- f a ty ;;
    mlet a_body <- liftM name a ;;
    mlet body <- f a_body body ;;
    ret (tLetIn name def ty body)
  | tApp func args =>
    mlet func <- f a func ;;
    mlet args <- monad_map (f a) args ;;
    ret (tApp func args)
  | tProj proj t =>
    mlet t <- f a t ;;
    ret (tProj proj t)
  (* For [tFix] and [tCoFix] we have to take care to lift [a]
     only when processing the body of the (co)fixpoint. *)
  | tFix defs i =>
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    let on_def := map_defM (f a) (f a_body) in
    mlet defs <- monad_map on_def defs ;;
    ret (tFix defs i)
  | tCoFix defs i =>
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    let on_def := map_defM (f a) (f a_body) in
    mlet defs <- monad_map on_def defs ;;
    ret (tCoFix defs i)
  | tCase ci pred x branches =>
    mlet pred <- map_predicate_with_bindersM f pred ;;
    mlet x <- f a x ;;
    mlet branches <- monad_map (map_branch_with_bindersM f) branches ;;
    ret (tCase ci pred x branches)
  | tArray l t def ty =>
    mlet t <- monad_map (f a) t ;;
    mlet def <- f a def ;;
    mlet ty <- f a ty ;;
    ret (tArray l t def ty)
  end.

Definition fold_predicate_with_bindersM (f : A -> Acc -> term -> M Acc) (acc : Acc) (p : predicate term) : M Acc :=
  mlet a_return <- lift_namesM p.(pcontext) a ;;
  mlet acc <- monad_fold_left (f a) p.(pparams) acc ;;
  f a_return acc p.(preturn).

Definition fold_branch_with_bindersM (f : A -> Acc -> term -> M Acc) (acc : Acc) (b : branch term) : M Acc :=
  mlet a_body <- lift_namesM b.(bcontext) a ;;
  f a_body acc b.(bbody).

(** Monadic variant of [fold_term_with_binders]. *)
Definition fold_term_with_bindersM (f : A -> Acc -> term -> M Acc) (acc : Acc) (t : term) : M Acc :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _
  | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => ret acc
  | tEvar n ts => monad_fold_left (f a) ts acc
  | tCast b k t => mlet acc <- f a acc b ;; f a acc t
  | tProd name ty body =>
    mlet a_body <- liftM name a ;;
    mlet acc <- f a acc ty ;;
    f a_body acc body
  | tLambda name ty body =>
    mlet a_body <- liftM name a ;;
    mlet acc <- f a acc ty ;;
    f a_body acc body
  | tLetIn name def ty body =>
    mlet a_body <- liftM name a ;;
    mlet def <- f a acc def ;;
    mlet acc <- f a acc ty ;;
    f a_body acc body
  | tApp func args => monad_fold_left (f a) (func :: args) acc
  | tProj proj t => f a acc t
  | tFix defs i =>
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    mlet acc <- monad_fold_left (f a) (List.map dtype defs) acc ;;
    monad_fold_left (f a_body) (List.map dbody defs) acc
  | tCoFix defs i =>
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    mlet acc <- monad_fold_left (f a) (List.map dtype defs) acc ;;
    monad_fold_left (f a_body) (List.map dbody defs) acc
  | tCase ci pred x branches =>
    mlet acc <- fold_predicate_with_bindersM f acc pred ;;
    mlet acc <- f a acc x ;;
    monad_fold_left (fold_branch_with_bindersM f) branches acc
  | tArray l t def ty =>
    mlet acc <- monad_fold_left (f a) t acc ;;
    mlet acc <- f a acc def ;;
    f a acc ty
  end.

End TraverseWithBindersM.


(** [map_term f t] maps [f] on the immediate subterms of [t].
    It is not recursive and the order in which subterms are processed is not specified. *)
Definition map_term (f : term -> term) (t : term) : term :=
  @map_term_with_binders unit tt (fun _ _ => tt) (fun _ => f) t.

(** Monadic variant of [map_term]. *)
Definition map_termM {M} `{Monad M} (f : term -> M term) (t : term) : M term :=
  @map_term_with_bindersM M _ unit tt (fun _ _ => ret tt) (fun _ => f) t.

(** [fold_term f acc t] folds [f] on the immediate subterms of [t].
    It is not recursive and the order in which subterms are processed is not specified. *)
Definition fold_term {Acc} (f : Acc -> term -> Acc) (acc : Acc) (t : term) : Acc :=
  @fold_term_with_binders Acc unit tt (fun _ _ => tt) (fun _ => f) acc t.

(** Monadic variant of [fold_term]. *)
Definition fold_termM {M} `{Monad M} {Acc} (f : Acc -> term -> M Acc) (acc : Acc) (t : term) : M Acc :=
  @fold_term_with_bindersM M _ Acc unit tt (fun _ _ => ret tt) (fun _ => f) acc t.


(** * Traversal functions with a context*)
Definition rebuild_case_predicate_ctx_with_context (Σ : global_env) ind (p : predicate term) : context :=
  match lookup_ind_decl Σ (inductive_mind ind) (inductive_ind ind) with
  | TypeError _ => []
  | Checked (mib, oib) => case_predicate_context ind mib oib p
  end.

Definition map_context_with_context (f : context -> term -> term) (c : context) Γ : context :=
  fold_left (fun acc decl => map_decl (f (Γ ,,, acc)) decl :: acc) (List.rev c) [].

Definition map_predicate_with_context (Σ : global_env) (f : context -> term -> term) Γ ind (p : predicate term) :=
  let pctx := rebuild_case_predicate_ctx_with_context Σ ind p in
  let Γparams := map_context_with_context f pctx Γ in
  {| pparams := map (f Γ) p.(pparams);
    puinst := p.(puinst);
    pcontext := p.(pcontext);
    preturn := f (Γparams  ++ Γ) (preturn p) |}.

Definition rebuild_case_branch_ctx_with_context Σ ind i p br :=
  match lookup_constructor_decl Σ (inductive_mind ind) (inductive_ind ind) i with
  | TypeError _ => []
  | Checked (mib, cdecl) => case_branch_context ind mib cdecl p br
  end.

Definition map_case_branch_with_context Σ ind i (f : context -> term -> term) Γ p br :=
  let ctx := rebuild_case_branch_ctx_with_context Σ ind i p br in
  map_branch (f (Γ ,,, ctx)) br.

Definition map_term_with_context Σ (f : context -> term -> term) Γ (t : term) : term :=
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
      let p' := map_predicate_with_context Σ f Γ ci.(ci_ind) p in
      let brs' := mapi (fun i x => map_case_branch_with_context Σ ci.(ci_ind) i f Γ p' x) brs in
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
