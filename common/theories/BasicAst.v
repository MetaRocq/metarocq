(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect Morphisms Orders Setoid.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Export Kernames.
From Stdlib Require Floats.SpecFloat.
From Equations Require Import Equations.

(** Identifiers that are allowed to be anonymous (i.e. "_" in concrete syntax). *)
Inductive name : Set :=
| nAnon
| nNamed (_ : ident).
Derive NoConfusion EqDec for name.

Inductive relevance : Set := Relevant | Irrelevant.
Derive NoConfusion EqDec for relevance.

(** Binders annotated with relevance *)
Record binder_annot (A : Type) := mkBindAnn { binder_name : A; binder_relevance : relevance }.

Arguments mkBindAnn {_}.
Arguments binder_name {_}.
Arguments binder_relevance {_}.

Derive NoConfusion for binder_annot.

#[global] Instance eqdec_binder_annot (A : Type) (e : Classes.EqDec A) : Classes.EqDec (binder_annot A).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition map_binder_annot {A B} (f : A -> B) (b : binder_annot A) : binder_annot B :=
  {| binder_name := f b.(binder_name); binder_relevance := b.(binder_relevance) |}.

Definition eq_binder_annot {A B} (b : binder_annot A) (b' : binder_annot B) : Prop :=
  b.(binder_relevance) = b'.(binder_relevance).

(** Type of annotated names *)
Definition aname := binder_annot name.
#[global] Instance anqme_eqdec : Classes.EqDec aname := _.

Definition eqb_binder_annot {A} (b b' : binder_annot A) : bool :=
  match Classes.eq_dec b.(binder_relevance) b'.(binder_relevance) with
  | left _ => true
  | right _ => false
  end.

Definition string_of_name (na : name) :=
  match na with
  | nAnon => "_"
  | nNamed n => n
  end.

Definition string_of_relevance (r : relevance) :=
  match r with
  | Relevant => "Relevant"
  | Irrelevant => "Irrelevant"
  end.

(** The kind of a cast *)
Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast.
Derive NoConfusion EqDec for cast_kind.

Record case_info := mk_case_info {
  ci_ind : inductive;
  ci_npar : nat;
  (* Not implemented yet, as the representation in PCUIC doesn't need this cached information.
     ci_cstr_nargs : list nat; (* The number of REAL arguments of each constructor (no params, no lets) *)
     ci_cstr_ndecls : list nat; (* The number of arguments of each constructor (no params but lets included) *)   *)
  ci_relevance : relevance }.
Derive NoConfusion EqDec for case_info.

Definition string_of_case_info ci :=
  "(" ^ string_of_inductive ci.(ci_ind) ^ "," ^
  string_of_nat ci.(ci_npar) ^ "," ^
  (* string_of_list string_of_nat ci.(ci_cstr_nargs) ^ "," ^
  string_of_list string_of_nat ci.(ci_cstr_ndecls) ^ "," ^ *)
  string_of_relevance ci.(ci_relevance) ^ ")".

Inductive recursivity_kind :=
  | Finite (* = inductive *)
  | CoFinite (* = coinductive *)
  | BiFinite (* = non-recursive, like in "Record" definitions *).
Derive NoConfusion EqDec for recursivity_kind.

(* The kind of a conversion problem *)
Inductive conv_pb :=
  | Conv
  | Cumul.
Derive NoConfusion EqDec for conv_pb.

Definition conv_pb_leqb (pb1 pb2 : conv_pb) : bool
  := match pb1, pb2 with
     | Cumul, Conv => false
     | _, _ => true
     end.

(* This opaque natural number is a hack to inform unquoting to generate
  a fresh evar when encountering it. *)
Definition fresh_evar_id : nat. exact 0. Qed.

(* Parametrized by term because term is not yet defined *)
Record def term := mkdef {
  dname : aname; (* the name, annotated with relevance **)
  dtype : term;
  dbody : term; (* the body (a lambda term). Note, this may mention other (mutually-defined) names **)
  rarg  : nat  (* the index of the recursive argument, 0 for cofixpoints **) }.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Derive NoConfusion for def.
#[global] Instance def_eq_dec {A} : Classes.EqDec A -> Classes.EqDec (def A).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition string_of_def {A} (f : A -> string) (def : def A) :=
  "(" ^ string_of_name (binder_name (dname def))
      ^ "," ^ string_of_relevance (binder_relevance (dname def))
      ^ "," ^ f (dtype def)
      ^ "," ^ f (dbody def)
      ^ "," ^ string_of_nat (rarg def) ^ ")".

Definition print_def {A} (f : A -> string) (g : A -> string) (def : def A) :=
  string_of_name (binder_name (dname def)) ^ " { struct " ^ string_of_nat (rarg def) ^ " }" ^
                 " : " ^ f (dtype def) ^ " := " ^ nl ^ g (dbody def).


Definition map_def {A B} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Lemma map_dtype {A B} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dbody {A B} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dname {A B} (f : A -> B) (g : A -> B) (d : def A) :
  dname d = dname (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Definition mfixpoint term := list (def term).

Definition test_def {A} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tFixProp {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma map_def_map_def {A B C} (f f' : B -> C) (g g' : A -> B) (d : def A) :
  map_def f f' (map_def g g' d) = map_def (f ∘ g) (f' ∘ g') d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {A B C} (f f' : B -> C) (g g' : A -> B) :
  (map_def f f') ∘ (map_def g g') = map_def (f ∘ g) (f' ∘ g').
Proof. reflexivity. Qed.

Lemma map_def_id {t} x : map_def (@id t) (@id t) x = id x.
Proof. now destruct x. Qed.
#[global] Hint Rewrite @map_def_id @map_id : map.

Lemma map_def_spec {A B} (P P' : A -> Type) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  now rewrite !H // !H0.
Qed.

#[global] Hint Extern 10 (_ < _)%nat => lia : all.
#[global] Hint Extern 10 (_ <= _)%nat => lia : all.
#[global] Hint Extern 10 (@eq nat _ _) => lia : all.
#[global] Hint Extern 0 (_ = _) => progress f_equal : all.
#[global] Hint Unfold on_snd snd : all.

Lemma on_snd_eq_id_spec {A B} (f : B -> B) (x : A * B) :
  f (snd x) = snd x <->
  on_snd f x = x.
Proof.
  destruct x; simpl; unfold on_snd; simpl. split; congruence.
Qed.
#[global] Hint Resolve -> on_snd_eq_id_spec : all.
#[global] Hint Resolve -> on_snd_eq_spec : all.

Lemma map_def_eq_spec {A B} (f f' g g' : A -> B) (x : def A) :
  f (dtype x) = g (dtype x) ->
  f' (dbody x) = g' (dbody x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. unfold map_def; f_equal; auto.
Qed.
#[global] Hint Resolve map_def_eq_spec : all.

Lemma map_def_id_spec {A} (f f' : A -> A) (x : def A) :
  f (dtype x) = (dtype x) ->
  f' (dbody x) = (dbody x) ->
  map_def f f' x = x.
Proof.
  intros. rewrite (map_def_eq_spec _ _ id id); auto. destruct x; auto.
Qed.
#[global] Hint Resolve map_def_id_spec : all.

Lemma tfix_map_spec {A B} {P P' : A -> Type} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq. red in X. eapply All_impl; eauto. simpl.
  intros. destruct X0;
  eapply map_def_spec; eauto.
Qed.

Record judgment_ {universe Term} := Judge {
  j_term : option Term;
  j_typ : Term;
  j_univ : option universe;
  j_rel : option relevance;
}.
Arguments judgment_ : clear implicits.
Arguments Judge {universe Term} _ _ _.

Definition judgment_map {univ T A} (f: T -> A) (j : judgment_ univ T) :=
  Judge (option_map f (j_term j)) (f (j_typ j)) (j_univ j) (j_rel j).

Section Contexts.
  Context {term : Type}.
  (** *** The context of De Bruijn indices *)

  Record context_decl := mkdecl {
    decl_name : aname ;
    decl_body : option term ;
    decl_type : term
  }.
  Derive NoConfusion for context_decl.
End Contexts.

Arguments context_decl : clear implicits.

Notation Typ typ := (Judge None typ None None).
Notation TypRel typ rel := (Judge None typ None (Some rel)).
Notation TermTyp tm ty := (Judge (Some tm) ty None None).
Notation TermTypRel tm ty rel := (Judge (Some tm) ty None (Some rel)).
Notation TermoptTyp tm typ := (Judge tm typ None None).
Notation TermoptTypRel tm typ rel := (Judge tm typ None (Some rel)).
Notation TypUniv ty u := (Judge None ty (Some u) None).
Notation TypUnivRel ty u rel := (Judge None ty (Some u) (Some rel)).
Notation TermTypUniv tm ty u := (Judge (Some tm) ty (Some u) None).

Notation j_vass na ty := (TypRel ty na.(binder_relevance)).
Notation j_vass_s na ty s := (TypUnivRel ty s na.(binder_relevance)).
Notation j_vdef na b ty := (TermTypRel b ty na.(binder_relevance)).
Notation j_decl d := (TermoptTypRel (decl_body d) (decl_type d) (decl_name d).(binder_relevance)).
Notation j_decl_s d s := (Judge (decl_body d) (decl_type d) s (Some (decl_name d).(binder_relevance))).

Definition map_decl {term term'} (f : term -> term') (d : context_decl term) : context_decl term' :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}.

Lemma compose_map_decl {term term' term''} (g : term -> term') (f : term' -> term'') x :
  map_decl f (map_decl g x) = map_decl (f ∘ g) x.
Proof.
  destruct x as [? [?|] ?]; reflexivity.
Qed.

Lemma map_decl_ext {term term'} (f g : term -> term') x : (forall x, f x = g x) -> map_decl f x = map_decl g x.
Proof.
  intros H; destruct x as [? [?|] ?]; rewrite /map_decl /=; f_equal; auto.
  now rewrite (H t).
Qed.

#[global] Instance map_decl_proper {term term'} : Proper (`≐1` ==> Logic.eq ==> Logic.eq) (@map_decl term term').
Proof.
  intros f g Hfg x y ->. now apply map_decl_ext.
Qed.

#[global] Instance map_decl_pointwise {term term'} : Proper (`≐1` ==> `≐1`) (@map_decl term term').
Proof. intros f g Hfg x. rewrite /map_decl.
  destruct x => /=. f_equal.
  - now rewrite Hfg.
  - apply Hfg.
Qed.
(*

#[global] Instance pointwise_subrelation {A B} : subrelation (`≐1`) (@Logic.eq A ==> @Logic.eq B)%signature.
Proof.
  intros f g Hfg x y ->. now rewrite Hfg.
Qed.

#[global] Instance pointwise_subrelation_inv {A B} : subrelation (@Logic.eq A ==> @Logic.eq B)%signature  (`≐1`).
Proof.
  intros f g Hfg x. now specialize (Hfg x x eq_refl).
Qed.*)

Definition map_context {term term'} (f : term -> term') (c : list (context_decl term)) :=
  List.map (map_decl f) c.

#[global] Instance map_context_proper {term term'} : Proper (`≐1` ==> Logic.eq ==> Logic.eq) (@map_context term term').
Proof.
  intros f g Hfg x y ->.
  now rewrite /map_context Hfg.
Qed.

Lemma map_context_length {term term'} (f : term -> term') l : #|map_context f l| = #|l|.
Proof. now unfold map_context; rewrite length_map. Qed.
#[global] Hint Rewrite @map_context_length : len.

Definition test_decl {term} (f : term -> bool) (d : context_decl term) : bool :=
  option_default f d.(decl_body) true && f d.(decl_type).

#[global] Instance test_decl_proper {term} : Proper (`≐1` ==> Logic.eq ==> Logic.eq) (@test_decl term).
Proof.
  intros f g Hfg [na [b|] ty] ? <- => /=; rewrite /test_decl /=;
  now rewrite Hfg.
Qed.

Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

Definition app_context {A} (Γ Γ': list A) := Γ' ++ Γ.

Notation "Γ ,,, Γ'" := (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

Lemma app_context_nil_l {T} Γ : [] ,,, Γ = Γ :> list T.
Proof.
  unfold app_context. rewrite app_nil_r. reflexivity.
Qed.

Lemma app_context_assoc {T} Γ Γ' Γ'' : Γ ,,, (Γ' ,,, Γ'') = Γ ,,, Γ' ,,, Γ'' :> list T.
Proof. unfold app_context; now rewrite app_assoc. Qed.

Lemma app_context_cons {T} Γ Γ' A : Γ ,,, (Γ' ,, A) = (Γ ,,, Γ') ,, A :> list T.
Proof. exact (app_context_assoc _ _ [A]). Qed.

Lemma app_context_push {T} Γ Δ Δ' d : (Γ ,,, Δ ,,, Δ') ,, d = (Γ ,,, Δ ,,, (Δ' ,, d)) :> list T.
Proof using Type.
  reflexivity.
Qed.

Lemma snoc_app_context {T Γ Δ d} : (Γ ,,, (d :: Δ)) =  (Γ ,,, Δ) ,,, [d] :> list T.
Proof using Type.
  reflexivity.
Qed.

Lemma app_context_length {T} (Γ Γ' : list T) : #|Γ ,,, Γ'| = #|Γ'| + #|Γ|.
Proof. unfold app_context. now rewrite length_app. Qed.
#[global] Hint Rewrite @app_context_length : len.

Lemma nth_error_app_context_ge {T} v Γ Γ' :
  #|Γ'| <= v -> nth_error (Γ ,,, Γ') v = nth_error Γ (v - #|Γ'|) :> option T.
Proof. apply nth_error_app_ge. Qed.

Lemma nth_error_app_context_lt {T} v Γ Γ' :
  v < #|Γ'| -> nth_error (Γ ,,, Γ') v = nth_error Γ' v :> option T.
Proof. apply nth_error_app_lt. Qed.


Definition ondecl {A} (P : A -> Type) (d : context_decl A) :=
  option_default P d.(decl_body) unit × P d.(decl_type).

Notation onctx P := (All (ondecl P)).

Section ContextMap.
  Context {term term' : Type} (f : nat -> term -> term').

  Fixpoint mapi_context (c : list (context_decl term)) : list (context_decl term') :=
    match c with
    | d :: Γ => map_decl (f #|Γ|) d :: mapi_context Γ
    | [] => []
  end.
End ContextMap.

#[global] Instance mapi_context_proper {term term'} : Proper (`≐2` ==> Logic.eq ==> Logic.eq) (@mapi_context term term').
Proof.
  intros f g Hfg Γ ? <-.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; f_equal; auto; now rewrite Hfg.
Qed.

Lemma mapi_context_length {term} (f : nat -> term -> term) l : #|mapi_context f l| = #|l|.
Proof.
  induction l; simpl; auto.
Qed.
#[global] Hint Rewrite @mapi_context_length : len.

Section ContextTest.
  Context {term : Type} (f : term -> bool).

  Fixpoint test_context (c : list (context_decl term)) : bool :=
    match c with
    | d :: Γ => test_context Γ && test_decl f d
    | [] => true
    end.
End ContextTest.

#[global] Instance test_context_proper {term} : Proper (`≐1` ==> Logic.eq ==> Logic.eq) (@test_context term).
Proof.
  intros f g Hfg Γ ? <-.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; f_equal; auto; now rewrite Hfg.
Qed.

Section ContextTestK.
  Context {term : Type} (f : nat -> term -> bool) (k : nat).

  Fixpoint test_context_k (c : list (context_decl term)) : bool :=
    match c with
    | d :: Γ => test_context_k Γ && test_decl (f (#|Γ| + k)) d
    | [] => true
    end.
End ContextTestK.

#[global] Instance test_context_k_proper {term} : Proper (`≐1` ==> Logic.eq ==> Logic.eq ==> Logic.eq) (@test_context_k term).
Proof.
  intros f g Hfg k ? <- Γ ? <-.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; f_equal; auto; now rewrite Hfg.
Qed.

Section Contexts.
  Context {term term' term'' : Type}.
  Notation context term := (list (context_decl term)).

  Lemma test_decl_impl (f g : term -> bool) x : (forall x, f x -> g x) ->
    test_decl f x -> test_decl g x.
  Proof using Type.
    intros Hf; rewrite /test_decl.
    move/andb_and=> [Hd Hb].
    apply/andb_and; split; eauto.
    destruct (decl_body x); simpl in *; eauto.
  Qed.

  Definition onctx_k (P : nat -> term -> Type) k (ctx : context term) :=
    Alli (fun i d => ondecl (P (Nat.pred #|ctx| - i + k)) d) 0 ctx.

  Lemma ondeclP {P : term -> Type} {p : term -> bool} {d : context_decl term} :
    (forall x, reflectT (P x) (p x)) ->
    reflectT (ondecl P d) (test_decl p d).
  Proof using Type.
    intros hr.
    rewrite /ondecl /test_decl; destruct d as [decl_name decl_body decl_type]; cbn.
    destruct (hr decl_type) => //;
    destruct (reflect_option_default hr decl_body) => /= //; now constructor.
  Qed.

  Lemma onctxP {p : term -> bool} {ctx : context term} :
    reflectT (onctx p ctx) (test_context p ctx).
  Proof using Type.
    eapply equiv_reflectT.
    - induction 1; simpl; auto. rewrite IHX /= //.
      now move/(ondeclP reflectT_pred): p0.
    - induction ctx.
      * constructor.
      * move => /= /andb_and [Hctx Hd]; constructor; eauto.
        now move/(ondeclP reflectT_pred): Hd.
  Qed.

  Lemma map_decl_type (f : term -> term') decl : f (decl_type decl) = decl_type (map_decl f decl).
  Proof using Type. destruct decl; reflexivity. Qed.

  Lemma map_decl_body (f : term -> term') decl : option_map f (decl_body decl) = decl_body (map_decl f decl).
  Proof using Type. destruct decl; reflexivity. Qed.

  Lemma map_decl_id : @map_decl term term id ≐1 id.
  Proof using Type. intros d; now destruct d as [? [] ?]. Qed.

  Lemma option_map_decl_body_map_decl (f : term -> term') x :
    option_map decl_body (option_map (map_decl f) x) =
    option_map (option_map f) (option_map decl_body x).
  Proof using Type. destruct x; reflexivity. Qed.

  Lemma option_map_decl_type_map_decl (f : term -> term') x :
    option_map decl_type (option_map (map_decl f) x) =
    option_map f (option_map decl_type x).
  Proof using Type. destruct x; reflexivity. Qed.

  Definition fold_context_k (f : nat -> term -> term') Γ :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

  Arguments fold_context_k f Γ%_list_scope.

  Lemma fold_context_k_alt f Γ :
    fold_context_k f Γ =
    mapi (fun k' d => map_decl (f (Nat.pred (length Γ) - k')) d) Γ.
  Proof using Type.
    unfold fold_context_k. rewrite rev_mapi. rewrite List.rev_involutive.
    apply mapi_ext. intros. f_equal. now rewrite List.length_rev.
  Qed.

  Lemma mapi_context_fold f Γ :
    mapi_context f Γ = fold_context_k f Γ.
  Proof using Type.
    setoid_replace f with (fun k => f (k - 0)) using relation
      (pointwise_relation nat (pointwise_relation term (@Logic.eq term')))%signature at 1.
    rewrite fold_context_k_alt. unfold mapi.
    generalize 0.
    induction Γ as [|d Γ]; intros n; simpl; auto. f_equal.
    rewrite IHΓ. rewrite mapi_rec_Sk.
    apply mapi_rec_ext => k x. intros.
    apply map_decl_ext => t. lia_f_equal.
    intros k. now rewrite Nat.sub_0_r.
  Qed.

  Lemma fold_context_k_tip f d : fold_context_k f [d] = [map_decl (f 0) d].
  Proof using Type. reflexivity. Qed.

  Lemma fold_context_k_length f Γ : length (fold_context_k f Γ) = length Γ.
  Proof using Type.
    unfold fold_context_k. now rewrite !List.length_rev mapi_length List.length_rev.
  Qed.

  Lemma fold_context_k_snoc0 f Γ d :
    fold_context_k f (d :: Γ) = fold_context_k f Γ ,, map_decl (f (length Γ)) d.
  Proof using Type.
    unfold fold_context_k.
    rewrite !rev_mapi !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
    unfold snoc. f_equal. now rewrite Nat.sub_0_r List.length_rev.
    rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
    rewrite length_app !List.length_rev. simpl. f_equal. f_equal. lia.
  Qed.

  Lemma fold_context_k_app f Γ Δ :
    fold_context_k f (Δ ++ Γ)
    = fold_context_k (fun k => f (length Γ + k)) Δ ++ fold_context_k f Γ.
  Proof using Type.
    unfold fold_context_k.
    rewrite List.rev_app_distr.
    rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
    apply mapi_ext. intros. f_equal. rewrite List.length_rev. f_equal.
  Qed.

  Local Set Keyed Unification.

  Equations mapi_context_In (ctx : context term) (f : nat -> forall (x : context_decl term), In x ctx -> context_decl term) : context term :=
  mapi_context_In nil _ := nil;
  mapi_context_In (cons x xs) f := cons (f #|xs| x _) (mapi_context_In xs (fun n x H => f n x _)).

  Lemma mapi_context_In_spec (f : nat -> term -> term) (ctx : context term) :
    mapi_context_In ctx (fun n (x : context_decl term) (_ : In x ctx) => map_decl (f n) x) =
    mapi_context f ctx.
  Proof using Type.
    remember (fun n (x : context_decl term) (_ : In x ctx) => map_decl (f n) x) as g.
    funelim (mapi_context_In ctx g) => //=; rewrite (H f0) ; trivial.
  Qed.

  Equations fold_context_In (ctx : context term) (f : context term -> forall (x : context_decl term), In x ctx -> context_decl term) : context term :=
  fold_context_In nil _ := nil;
  fold_context_In (cons x xs) f :=
    let xs' := fold_context_In xs (fun n x H => f n x _) in
    cons (f xs' x _) xs'.

  Equations fold_context (f : context term -> context_decl term -> context_decl term) (ctx : context term) : context term :=
    fold_context f nil := nil;
    fold_context f (cons x xs) :=
      let xs' := fold_context f xs in
      cons (f xs' x ) xs'.

  Lemma fold_context_length f Γ : #|fold_context f Γ| = #|Γ|.
  Proof using Type.
    now apply_funelim (fold_context f Γ); intros; simpl; auto; f_equal.
  Qed.


  Lemma fold_context_In_spec (f : context term -> context_decl term -> context_decl term) (ctx : context term) :
    fold_context_In ctx (fun n (x : context_decl term) (_ : In x ctx) => f n x) =
    fold_context f ctx.
  Proof using Type.
    remember (fun n (x : context_decl term) (_ : In x ctx) => f n x) as g.
    funelim (fold_context_In ctx g) => //=; rewrite (H f0); trivial.
  Qed.

  #[global]
  Instance fold_context_Proper : Proper (`≐2` ==> `≐1`) fold_context.
  Proof using Type.
    intros f f' Hff' x.
    funelim (fold_context f x); simpl; auto. simp fold_context.
    now rewrite (H f' Hff').
  Qed.

  (** This function allows to forget type annotations on a binding context.
  Useful to relate the "compact" case representation in terms, with
  its typing relation, where the context has types *)
  Definition forget_types (c : list (BasicAst.context_decl term)) : list aname :=
    map decl_name c.

End Contexts.
#[global] Hint Rewrite @fold_context_length @fold_context_k_length : len.

Section Contexts.
  Context {term term' term'' : Type}.
  Notation context term := (list (context_decl term)).

  Lemma fold_context_k_id (x : context term) : fold_context_k (fun i x => x) x = x.
  Proof using Type.
    rewrite fold_context_k_alt.
    rewrite /mapi. generalize 0.
    induction x; simpl; auto.
    intros n.
    f_equal; auto.
    now rewrite map_decl_id.
  Qed.

  Lemma fold_context_k_compose (f : nat -> term' -> term) (g : nat -> term'' -> term') Γ :
    fold_context_k f (fold_context_k g Γ) =
    fold_context_k (fun i => f i ∘ g i) Γ.
  Proof using Type.
    rewrite !fold_context_k_alt mapi_mapi.
    apply mapi_ext => i d.
    rewrite compose_map_decl. apply map_decl_ext => t.
    now len.
  Qed.

  Lemma fold_context_k_ext (f g : nat -> term' -> term) Γ :
    f ≐2 g ->
    fold_context_k f Γ = fold_context_k g Γ.
  Proof using Type.
    intros hfg.
    induction Γ; simpl; auto; rewrite !fold_context_k_snoc0.
    simpl. rewrite IHΓ. f_equal. apply map_decl_ext.
    intros. now apply hfg.
  Qed.

  #[global] Instance fold_context_k_proper : Proper (pointwise_relation nat (pointwise_relation _ Logic.eq) ==> Logic.eq ==> Logic.eq)
    (@fold_context_k term' term).
  Proof using Type.
    intros f g Hfg x y <-. now apply fold_context_k_ext.
  Qed.

  Lemma alli_fold_context_k_prop (f : nat -> context_decl term -> bool) (g : nat -> term' -> term) ctx :
    alli f 0 (fold_context_k g ctx) =
    alli (fun i x => f i (map_decl (g (Nat.pred #|ctx| - i)) x)) 0 ctx.
  Proof using Type.
    now rewrite fold_context_k_alt /mapi alli_mapi.
  Qed.

  Lemma test_decl_map_decl f g x : (@test_decl term) f (map_decl g x) = @test_decl term (f ∘ g) x.
  Proof using Type.
    rewrite /test_decl /map_decl /=.
    f_equal. rewrite /option_default.
    destruct (decl_body x) => //.
  Qed.

  Lemma map_fold_context_k (f : term' -> term) (g : nat -> term'' -> term') ctx :
    map (map_decl f) (fold_context_k g ctx) = fold_context_k (fun i => f ∘ g i) ctx.
  Proof using Type.
    rewrite !fold_context_k_alt map_mapi.
    apply mapi_ext => i d. now rewrite compose_map_decl.
  Qed.

  Lemma map_context_mapi_context (f : term' -> term) (g : nat -> term'' -> term') (ctx : list (BasicAst.context_decl term'')) :
    map_context f (mapi_context g ctx) =
    mapi_context (fun i => f ∘ g i) ctx.
  Proof using Type.
    rewrite !mapi_context_fold. now unfold map_context; rewrite map_fold_context_k.
  Qed.

  Lemma mapi_context_map (f : nat -> term' -> term) (g : context_decl term'' -> context_decl term') ctx :
    mapi_context f (map g ctx) = mapi (fun i => map_decl (f (Nat.pred #|ctx| - i)) ∘ g) ctx.
  Proof using Type.
    rewrite mapi_context_fold fold_context_k_alt mapi_map. now len.
  Qed.

  Lemma map_context_map (f : term' -> term) (g : context_decl term'' -> context_decl term') ctx :
    map_context f (map g ctx) = map (map_decl f ∘ g) ctx.
  Proof using Type.
    induction ctx; simpl; f_equal; auto.
  Qed.

  Lemma map_map_context (f : context_decl term' -> term) (g : term'' -> term') ctx :
    map f (map_context g ctx) = map (f ∘ map_decl g) ctx.
  Proof using Type.
    now rewrite /map_context map_map_compose.
  Qed.

  Lemma fold_context_k_map (f : nat -> term' -> term) (g : term'' -> term') Γ :
    fold_context_k f (map_context g Γ) =
    fold_context_k (fun k => f k ∘ g) Γ.
  Proof using Type.
    rewrite !fold_context_k_alt mapi_map.
    apply mapi_ext => n d //. len.
    now rewrite compose_map_decl.
  Qed.

  Lemma fold_context_k_map_comm (f : nat -> term -> term) (g : term -> term) Γ :
    (forall i x, f i (g x) = g (f i x)) ->
    fold_context_k f (map_context g Γ) = map_context g (fold_context_k f Γ).
  Proof using Type.
    intros Hfg.
    rewrite !fold_context_k_alt mapi_map.
    rewrite /map_context map_mapi.
    apply mapi_ext => i x.
    rewrite !compose_map_decl.
    apply map_decl_ext => t.
    rewrite Hfg.
    now len.
  Qed.

  Lemma mapi_context_map_context (f : nat -> term' -> term) (g : term'' -> term') ctx :
    mapi_context f (map_context g ctx) =
    mapi_context (fun i => f i ∘ g) ctx.
  Proof using Type.
    now rewrite !mapi_context_fold fold_context_k_map.
  Qed.

  Lemma map_mapi_context (f : context_decl term' -> term) (g : nat -> term'' -> term') ctx :
    map f (mapi_context g ctx) = mapi (fun i => f ∘ map_decl (g (Nat.pred #|ctx| - i))) ctx.
  Proof using Type.
    now rewrite mapi_context_fold fold_context_k_alt map_mapi.
  Qed.

  Lemma map_context_id (ctx : context term) : map_context id ctx = ctx.
  Proof using Type.
    unfold map_context.
    now rewrite map_decl_id map_id.
  Qed.

  Lemma forget_types_length (ctx : list (context_decl term)) :
    #|forget_types ctx| = #|ctx|.
  Proof using Type.
    now rewrite /forget_types length_map.
  Qed.

  Lemma map_decl_name_fold_context_k (f : nat -> term' -> term) ctx :
    map decl_name (fold_context_k f ctx) = map decl_name ctx.
  Proof using Type.
    now rewrite fold_context_k_alt map_mapi /= mapi_cst_map.
  Qed.

  Lemma forget_types_fold_context_k (f : nat -> term' -> term) ctx :
    forget_types (fold_context_k f ctx) = forget_types ctx.
  Proof using Type.
    now rewrite /forget_types map_decl_name_fold_context_k.
  Qed.

  Lemma All2_fold_impl_onctx (P : context term -> context term -> context_decl term -> context_decl term -> Type) P' Γ Δ Q :
    onctx Q Γ ->
    All2_fold P Γ Δ ->
    (forall Γ Δ d d',
      All2_fold P Γ Δ ->
      P Γ Δ d d' ->
      ondecl Q d ->
      P' Γ Δ d d') ->
    All2_fold P' Γ Δ.
  Proof using Type.
    intros onc cr Hcr.
    induction cr; depelim onc; constructor; intuition eauto.
  Qed.

  Lemma All2_fold_mapi (P : context term -> context term -> context_decl term -> context_decl term -> Type) (Γ Δ : context term) f g :
    All2_fold (fun Γ Δ d d' =>
      P (mapi_context f Γ) (mapi_context g Δ) (map_decl (f #|Γ|) d) (map_decl (g #|Γ|) d')) Γ Δ
    <~> All2_fold P (mapi_context f Γ) (mapi_context g Δ).
  Proof using Type.
    split.
    - induction 1; simpl; constructor; intuition auto;
      now rewrite <-(All2_fold_length X).
    - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
      depelim H; constructor; simpl in *; auto.
      pose proof (All2_fold_length H). len in H0.
      now rewrite <- H0 in p.
  Qed.

  Lemma All2_fold_map {P : context term -> context term -> context_decl term -> context_decl term -> Type} {Γ Δ : context term} f g :
    All2_fold (fun Γ Δ d d' =>
      P (map_context f Γ) (map_context g Δ) (map_decl f d) (map_decl g d')) Γ Δ <~>
    All2_fold P (map_context f Γ) (map_context g Δ).
  Proof using Type.
    split.
    - induction 1; simpl; constructor; intuition auto;
      now rewrite <-(All2_fold_length X).
    - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
        depelim H; constructor; auto.
  Qed.

  Lemma All2_fold_cst_map {P : context_decl term -> context_decl term -> Type} {Γ Δ : context term} {f g} :
    All2_fold (fun _ _ d d' => P (f d) (g d')) Γ Δ <~>
    All2_fold (fun _ _ => P) (map f Γ) (map g Δ).
  Proof using Type.
    split.
    - induction 1; simpl; constructor; intuition auto;
      now rewrite <-(All2_fold_length X).
    - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
        depelim H; constructor; auto.
  Qed.


End Contexts.

#[global] Hint Rewrite @map_mapi_context
  @map_fold_context_k @mapi_context_map @map_context_map @map_map_context
  @mapi_context_map_context @map_context_mapi_context : map.
#[global] Hint Rewrite @forget_types_length : len.

(** Primitive types models (axiom free) *)

(** Model of unsigned integers *)
Definition uint_size := 63.
Definition uint_wB := (2 ^ (Z.of_nat uint_size))%Z.
Definition uint63_model := { z : Z | ((0 <=? z) && (z <? uint_wB))%Z }.

Definition string_of_uint63_model (i : uint63_model) := string_of_Z (proj1_sig i).

(** Model of floats *)
Definition prec := 53%Z.
Definition emax := 1024%Z.
(** We consider valid binary encordings of floats as our model *)
Definition float64_model := sig (SpecFloat.valid_binary prec emax).
