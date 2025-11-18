(* Distributed under the terms of the MIT license. *)
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Export Environment EnvironmentTyping Universes BasicAst.
(* For primitive integers and floats  *)
From Stdlib Require Uint63 Floats.PrimFloat Floats.SpecFloat PArray PrimString.
From Stdlib Require Import ssreflect Morphisms.

(** * AST of Rocq kernel terms and kernel data structures

    ** Basic data-types:

      We reflect identifiers [ident], sort families [sort_family], names
    [name], cast kinds [cast_kind], inductives [inductive] and primitive
    projections [projection] and (co)-fixpoint blocks [mfixpoint] and
    [def]. These are defined in the [BasicAst] file.

    ** Terms:

      The AST is [term : Set]

      Smart constructors [mkApp], [mkApps] maintain the invariant
    of no nested or empty n-ary applications.
      List in fixpoints and cofixpoint should be non-empty.

    ** Kernel interface: entries and declarations

      Kernel input declarations for constants [constant_entry] and mutual
    inductives [mutual_inductive_entry]. Kernel safe declarations for
    constants [constand_decl] and inductives [minductive_decl].

    ** Environments of declarations

      The global environment [global_env_ext]: a list of [global_decl] and
    a universe graph [constraints].  *)

(* Defined here since BasicAst does not have access to universe instances.
  Parameterized by term types as they are not yet defined. *)
Record predicate {term} := mk_predicate {
  puinst : Instance.t; (* The universe instance *)
  pparams : list term; (* The parameters *)
  pcontext : list aname; (* Names of binders of indices and inductive application,
                          in same order as context (i.e. name of "inductive application"
                          binder is first). Types are obtained from inductive declaration.
                          Also used for lifting/substitution for the return type. *)
  preturn : term; (* The return type *) }.

Arguments predicate : clear implicits.
Arguments mk_predicate {_}.

Derive NoConfusion for predicate.
Global Instance predicate_eq_dec term :
  Classes.EqDec term ->
  Classes.EqDec (predicate term).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition string_of_predicate {term} (f : term -> string) (p : predicate term) :=
  "(" ^ "(" ^ String.concat "," (map f (pparams p)) ^ ")"
  ^ "," ^ string_of_universe_instance (puinst p)
  ^ ",(" ^ String.concat "," (map (string_of_name ∘ binder_name) (pcontext p)) ^ ")"
  ^ "," ^ f (preturn p) ^ ")".

Definition test_predicate {term}
            (instf : Instance.t -> bool) (paramf preturnf : term -> bool) (p : predicate term) :=
  instf p.(puinst) && forallb paramf p.(pparams) && preturnf p.(preturn).

Definition eqb_predicate {term} (eqb_univ_instance : Instance.t -> Instance.t -> bool) (eqterm : term -> term -> bool) (p p' : predicate term) :=
  forallb2 eqterm p.(pparams) p'.(pparams) &&
  eqb_univ_instance p.(puinst) p'.(puinst) &&
  forallb2 eqb_binder_annot p.(pcontext) p'.(pcontext) &&
  eqterm p.(preturn) p'.(preturn).

Section map_predicate.
  Context {term term' : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (paramf preturnf : term -> term').

  Definition map_predicate (p : predicate term) :=
    {| pparams := map paramf p.(pparams);
        puinst := uf p.(puinst);
        pcontext := p.(pcontext);
        preturn := preturnf p.(preturn) |}.

  Lemma map_pparams (p : predicate term) :
    map paramf (pparams p) = pparams (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_preturn (p : predicate term) :
    preturnf (preturn p) = preturn (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_puints (p : predicate term) :
    uf (puinst p) = puinst (map_predicate p).
  Proof using Type. reflexivity. Qed.

End map_predicate.

Lemma map_predicate_map_predicate
      {term term' term''}
      (finst finst' : Instance.t -> Instance.t)
      (f g : term' -> term'')
      (f' g' : term -> term')
      (p : predicate term) :
  map_predicate finst f g (map_predicate finst' f' g' p) =
  map_predicate (finst ∘ finst') (f ∘ f') (g ∘ g') p.
Proof.
  destruct p; cbv.
  f_equal.
  apply map_map.
Qed.

Lemma map_predicate_id {t} x : map_predicate (@id _) (@id t) (@id t) x = id x.
Proof.
  destruct x; cbv.
  f_equal.
  apply map_id.
Qed.
#[global] Hint Rewrite @map_predicate_id : map.

Definition tCasePredProp {term}
            (Pparams Preturn : term -> Type)
            (p : predicate term) :=
  All Pparams p.(pparams) × Preturn p.(preturn).

Lemma map_predicate_eq_spec {A B} (finst finst' : Instance.t -> Instance.t) (f f' g g' : A -> B) (p : predicate A) :
  finst (puinst p) = finst' (puinst p) ->
  map f (pparams p) = map g (pparams p) ->
  f' (preturn p) = g' (preturn p) ->
  map_predicate finst f f' p = map_predicate finst' g g' p.
Proof.
  intros. unfold map_predicate; f_equal; auto.
Qed.
#[global] Hint Resolve map_predicate_eq_spec : all.

Lemma map_predicate_id_spec {A} finst (f f' : A -> A) (p : predicate A) :
  finst (puinst p) = puinst p ->
  map f (pparams p) = pparams p ->
  f' (preturn p) = preturn p ->
  map_predicate finst f f' p = p.
Proof.
  unfold map_predicate.
  intros -> -> ->; destruct p; auto.
Qed.
#[global] Hint Resolve map_predicate_id_spec : all.

#[global] Instance map_predicate_proper {term} : Proper (`≐1` ==> `≐1` ==> Logic.eq ==> Logic.eq)%signature (@map_predicate term term id).
Proof.
  intros eqf0 eqf1 eqf.
  intros eqf'0 eqf'1 eqf'.
  intros x y ->.
  apply map_predicate_eq_spec; auto.
  now apply map_ext => x.
Qed.

#[global] Instance map_predicate_proper' {term} f : Proper (`≐1` ==> Logic.eq ==> Logic.eq) (@map_predicate term term id f).
Proof.
  intros eqf0 eqf1 eqf.
  intros x y ->.
  apply map_predicate_eq_spec; auto.
Qed.

Notation shiftf f k := (fun k' => f (k' + k)).

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
    pcontext p = pcontext (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_puinst k (p : predicate term) :
    uf (puinst p) = puinst (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Definition test_predicate_k (instp : Instance.t -> bool)
    (p : nat -> term -> bool) k (pred : predicate term) :=
    instp pred.(puinst) && forallb (p k) pred.(pparams) &&
    p (#|pred.(pcontext)| + k) pred.(preturn).

End map_predicate_k.

Section Branch.
  Context {term : Type}.
  (* Parameterized by term types as they are not yet defined. *)
  Record branch := mk_branch {
    bcontext : list aname; (* Names of binders of the branch, in "context" order.
                          Also used for lifting/substitution for the branch body. *)
    bbody : term; (* The branch body *) }.

  Derive NoConfusion for branch.
  Global Instance branch_eq_dec :
    Classes.EqDec term ->
    Classes.EqDec branch.
  Proof using Type. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

  Definition string_of_branch (f : term -> string) (b : branch) :=
  "([" ^ String.concat "," (map (string_of_name ∘ binder_name) (bcontext b)) ^ "], "
  ^ f (bbody b) ^ ")".

  Definition pretty_string_of_branch (f : term -> string) (b : branch) :=
    String.concat " " (map (string_of_name ∘ binder_name) (bcontext b)) ^ " => " ^ f (bbody b).

  Definition test_branch (bodyf : term -> bool) (b : branch) :=
    bodyf b.(bbody).
End Branch.
Arguments branch : clear implicits.

Section map_branch.
  Context {term term' : Type}.
  Context (bbodyf : term -> term').

    Definition map_branch (b : branch term) :=
    {| bcontext := b.(bcontext);
      bbody := bbodyf b.(bbody) |}.

    Lemma map_bbody (b : branch term) :
      bbodyf (bbody b) = bbody (map_branch b).
    Proof using Type. destruct b; auto. Qed.
End map_branch.

Lemma map_branch_map_branch
      {term term' term''}
      (f : term' -> term'')
      (f' : term -> term')
      (b : branch term) :
  map_branch f (map_branch f' b) =
  map_branch (f ∘ f') b.
Proof.
  destruct b; cbv.
  f_equal.
Qed.

Lemma map_branch_id {t} x : map_branch (@id t) x = id x.
Proof.
  destruct x; cbv.
  f_equal.
Qed.
#[global] Hint Rewrite @map_branch_id : map.

Lemma map_branch_eq_spec {A B} (f g : A -> B) (x : branch A) :
  f (bbody x) = g (bbody x) ->
  map_branch f x = map_branch g x.
Proof.
  intros. unfold map_branch; f_equal; auto.
Qed.
#[global] Hint Resolve map_branch_eq_spec : all.

#[global] Instance map_branch_proper {term} : Proper (`≐1` ==> Logic.eq ==> Logic.eq) (@map_branch term term).
Proof.
  intros eqf0 eqf1 eqf.
  intros x y ->.
  apply map_branch_eq_spec; auto.
Qed.

Lemma map_branch_id_spec {A} (f : A -> A) (x : branch A) :
  f (bbody x) = (bbody x) ->
  map_branch f x = x.
Proof.
  intros. rewrite (map_branch_eq_spec _ id); auto. destruct x; auto.
Qed.
#[global] Hint Resolve map_branch_id_spec : all.

Lemma map_branches_map_branches
      {term term' term''}
      (f : term' -> term'')
      (f' : term -> term')
      (l : list (branch term)) :
  map (fun b => map_branch f (map_branch f' b)) l =
  map (map_branch (f ∘ f')) l.
Proof.
  eapply map_ext => b. apply map_branch_map_branch.
Qed.

Definition map_branches {term B} (f : term -> B) l := List.map (map_branch f) l.

Definition tCaseBrsProp {A} (P : A -> Type) (l : list (branch A)) :=
  All (fun x => P (bbody x)) l.

Notation map_branches_k f k brs :=
  (List.map (fun b => map_branch (f (#|b.(bcontext)| + k)) b) brs).

Notation test_branches_k test k brs :=
  (List.forallb (fun b => test_branch (test (#|b.(bcontext)| + k)) b) brs).

Lemma map_branches_k_map_branches_k
      {term term' term''}
      (f : nat -> term' -> term'')
      (g : term -> term')
      (f' : nat -> term -> term') k
      (l : list (branch term)) :
  map (fun b => map_branch (f #|bcontext (map_branch g b)|) (map_branch (f' k) b)) l =
  map (fun b => map_branch (f #|bcontext b|) (map_branch (f' k) b)) l.
Proof.
  eapply map_ext => b. now rewrite map_branch_map_branch.
Qed.

Lemma case_brs_map_spec {A B} {P : A -> Type} {l} {f g : A -> B} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
  map_branches f l = map_branches g l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  apply map_branch_eq_spec; eauto.
Qed.

Lemma case_brs_map_k_spec {A B} {P : A -> Type} {k l} {f g : nat -> A -> B} :
  tCaseBrsProp P l -> (forall k x, P x -> f k x = g k x) ->
  map_branches_k f k l = map_branches_k g k l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  apply map_branch_eq_spec; eauto.
Qed.

Lemma case_brs_forallb_map_spec {A B} {P : A -> Type} {p : A -> bool}
      {l} {f g : A -> B} :
  tCaseBrsProp P l ->
  forallb (test_branch p) l ->
  (forall x, P x -> p x -> f x = g x) ->
  map (map_branch f) l = map (map_branch g) l.
Proof.
  intros.
  eapply All_map_eq. red in X. apply forallb_All in H.
  eapply All_impl. eapply All_prod. exact X. exact H.
  intros [] []; unfold map_branch; cbn. f_equal. now apply H0.
Qed.

Lemma tfix_forallb_map_spec {A B} {P P' : A -> Prop} {p p'} {l} {f f' g g' : A -> B} :
  tFixProp P P' l ->
  forallb (test_def p p') l ->
  (forall x, P x -> p x -> f x = g x) ->
  (forall x, P' x -> p' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq; red in X. apply forallb_All in H.
  eapply All_impl. eapply All_prod. exact X. exact H.
  intros [] [[] ?]; unfold map_def, test_def in *; cbn in *. rtoProp.
  f_equal; eauto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : All _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : forallb _ _ = _ |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : All _ _ |- map _ _ = map _ _ =>
    eapply (All_map_eq H)
  | H : All _ _ |- map _ _ = _ =>
    eapply (All_map_id H)
  | H : All _ _ |- is_true (forallb _ _) =>
    eapply (All_forallb _ _ H); clear H
  end.

Ltac close_All :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : Forall2 _ _ _ |- Forall2 _ _ _ => apply (Forall2_impl H); clear H; simpl
  | H : All _ _ |- All2 _ _ _ =>
    apply (All_All2 H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  end.

Inductive term : Type :=
| tRel (n : nat)
| tVar (id : ident) (* For free variables (e.g. in a goal) *)
| tEvar (ev : nat) (args : list term)
| tSort (s : sort)
| tCast (t : term) (kind : cast_kind) (v : term)
| tProd (na : aname) (ty : term) (body : term)
| tLambda (na : aname) (ty : term) (body : term)
| tLetIn (na : aname) (def : term) (def_ty : term) (body : term)
| tApp (f : term) (args : list term)
| tConst (c : kername) (u : Instance.t)
| tInd (ind : inductive) (u : Instance.t)
| tConstruct (ind : inductive) (idx : nat) (u : Instance.t)
| tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term))
| tProj (proj : projection) (t : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tInt (i : PrimInt63.int)
| tFloat (f : PrimFloat.float)
| tString (s : PrimString.string)
| tArray (u : Universe.t) (arr : list term) (default : term) (type : term).

(** This can be used to represent holes, that, when unquoted, turn into fresh existential variables.
    The fresh evar will depend on the whole context at this point in the term, despite the empty instance.
    Denotation will call Rocq's Typing.solve_evars to try and fill these holes using typing information.
*)
Definition hole := tEvar fresh_evar_id [].

Definition mkApps t us :=
  match us with
  | nil => t
  | _ => match t with
        | tApp f args => tApp f (args ++ us)
        | _ => tApp t us
        end
  end.

(** Term lifting / weakening *)

Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then n + i else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (List.map (lift n k) v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tCast c kind t => tCast (lift n k c) kind (lift n k t)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (lift n k) (lift n k') p in
    let brs' := map_branches_k (lift n) k brs in
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
  | tArray u arr def ty =>
    tArray u (List.map (lift n k) arr) (lift n k def) (lift n k ty)
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
  | tApp u v => mkApps (subst s k u) (List.map (subst s k) v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tCast c kind ty => tCast (subst s k c) kind (subst s k ty)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (subst s k) (subst s k') p in
    let brs' := map_branches_k (subst s) k brs in
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
  | tArray u arr def ty =>
    tArray u (List.map (subst s k) arr) (subst s k def) (subst s k ty)
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
  | tApp u v => closedn k u && List.forallb (closedn k) v
  | tCast c kind t => closedn k c && closedn k t
  | tLetIn na b t b' => closedn k b && closedn k t && closedn (S k) b'
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := test_predicate (fun _ => true) (closedn k) (closedn k') p in
    let brs' := test_branches_k closedn k brs in
    p' && closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tArray u arr def ty =>
    List.forallb (closedn k) arr && closedn k def && closedn k ty
  | _ => true
  end.

Notation closed t := (closedn 0 t).

Fixpoint noccur_between k n (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k || Nat.leb (k + n) i
  | tEvar ev args => List.forallb (noccur_between k n) args
  | tLambda _ T M | tProd _ T M => noccur_between k n T && noccur_between (S k) n M
  | tApp u v => noccur_between k n u && List.forallb (noccur_between k n) v
  | tCast c kind t => noccur_between k n c && noccur_between k n t
  | tLetIn na b t b' => noccur_between k n b && noccur_between k n t && noccur_between (S k) n b'
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := test_predicate (fun _ => true) (noccur_between k n) (noccur_between k' n) p in
    let brs' := test_branches_k (fun k => noccur_between k n) k brs in
    p' && noccur_between k n c && brs'
  | tProj p c => noccur_between k n c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tArray u arr def ty =>
    List.forallb (noccur_between k n) arr &&
    noccur_between k n def && noccur_between k n ty
  | _ => true
  end.

#[global] Instance subst_instance_constr : UnivSubst term :=
  fix subst_instance_constr u c {struct c} : term :=
  match c with
  | tRel _ | tVar _ => c
  | tInt _ | tFloat _ | tString _ => c
  | tArray u' arr def ty => tArray (subst_instance_universe u u') (List.map (subst_instance_constr u) arr)
    (subst_instance_constr u def) (subst_instance_constr u ty)
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tSort s => tSort (subst_instance_sort u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tLambda na T M => tLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (List.map (subst_instance_constr u) v)
  | tProd na A B => tProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | tCast c kind ty => tCast (subst_instance_constr u c) kind (subst_instance_constr u ty)
  | tLetIn na b ty b' => tLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind p c brs =>
    let p' := map_predicate (subst_instance_instance u) (subst_instance_constr u) (subst_instance_constr u) p in
    let brs' := List.map (map_branch (subst_instance_constr u)) brs in
    tCase ind p' (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  end.

(** Tests that the term is closed over [k] universe variables *)
Fixpoint closedu (k : nat) (t : term) : bool :=
  match t with
  | tSort univ => closedu_sort k univ
  | tInd _ u => closedu_instance k u
  | tConstruct _ _ u => closedu_instance k u
  | tConst _ u => closedu_instance k u
  | tRel i => true
  | tEvar ev args => forallb (closedu k) args
  | tLambda _ T M | tProd _ T M => closedu k T && closedu k M
  | tApp u v => closedu k u && forallb (closedu k) v
  | tCast c kind t => closedu k c && closedu k t
  | tLetIn na b t b' => closedu k b && closedu k t && closedu k b'
  | tCase ind p c brs =>
    let p' := test_predicate (closedu_instance k) (closedu k) (closedu k) p in
    let brs' := forallb (test_branch (closedu k)) brs in
    p' && closedu k c && brs'
  | tProj p c => closedu k c
  | tFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | tCoFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | tArray u arr def ty =>
    closedu_universe k u && forallb (closedu k) arr && closedu k def && closedu k ty
  | _ => true
  end.

Module TemplateTerm <: Term.

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

End TemplateTerm.

Module Env := Environment TemplateTerm.
Export Env.
(* Do NOT `Include` this module, as this would sadly duplicate the rewrite database... *)


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

Module TemplateTermUtils <: TermUtils TemplateTerm Env.

Definition destArity := destArity.
Definition inds := inds.

End TemplateTermUtils.

Ltac unf_term := unfold TemplateTerm.term in *; unfold TemplateTerm.tRel in *;
                  unfold TemplateTerm.tSort in *; unfold TemplateTerm.tProd in *;
                  unfold TemplateTerm.tLambda in *; unfold TemplateTerm.tLetIn in *;
                  unfold TemplateTerm.tInd in *; unfold TemplateTerm.tProj in *;
                  unfold TemplateTerm.lift in *; unfold TemplateTerm.subst in *;
                  unfold TemplateTerm.closedn in *; unfold TemplateTerm.noccur_between in *;
                  unfold TemplateTerm.subst_instance_constr in *;
                  unfold TemplateTermUtils.destArity; unfold TemplateTermUtils.inds.

Module TemplateLookup := EnvironmentTyping.Lookup TemplateTerm Env.
Include TemplateLookup.

Definition tDummy := tVar "".

Definition mkApp t u := Eval cbn in mkApps t [u].

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

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universes_entry }.

Record definition_entry := {
  definition_entry_type      : option term;
  definition_entry_body      : term;
  definition_entry_universes : universes_entry;
  definition_entry_opaque    : bool }.


Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

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

Record one_inductive_entry := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
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
  mind_entry_universes : universes_entry;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_variance  : option (list (option Universes.Variance.t));
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by Template Rocq yet. *) }.

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
Qed.

Lemma inds_spec ind u l :
  inds ind u l = List.rev (mapi (fun i _ => tInd {| inductive_mind := ind; inductive_ind := i |} u) l).
Proof.
  unfold inds, mapi. induction l using rev_ind. simpl. reflexivity.
  now rewrite length_app /= Nat.add_1_r IHl mapi_rec_app /= rev_app_distr /= Nat.add_0_r.
Qed.

(** Helpers for "compact" case representation, reconstructing predicate and
  branch contexts. *)

Definition ind_predicate_context ind mdecl idecl : context :=
  let ictx := (expand_lets_ctx mdecl.(ind_params) idecl.(ind_indices)) in
  let indty := mkApps (tInd ind (Instance.of_level_instance (abstract_instance mdecl.(ind_universes))))
    (to_extended_list (smash_context [] mdecl.(ind_params) ,,, ictx)) in
  let inddecl :=
    {| decl_name :=
      {| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |};
        decl_body := None;
        decl_type := indty |}
  in (inddecl :: ictx).

Definition inst_case_context params puinst (pctx : context) :=
  subst_context (List.rev params) 0 (subst_instance puinst pctx).

Definition pre_case_predicate_context_gen ind mdecl idecl params puinst : context :=
  inst_case_context params puinst (ind_predicate_context ind mdecl idecl).

Definition case_predicate_context_gen ind mdecl idecl params puinst pctx :=
  map2 set_binder_name pctx (pre_case_predicate_context_gen ind mdecl idecl params puinst).

Definition case_predicate_context ind mdecl idecl p : context :=
  case_predicate_context_gen ind mdecl idecl p.(pparams) p.(puinst) p.(pcontext).

Definition cstr_branch_context ind mdecl cdecl : context :=
  expand_lets_ctx mdecl.(ind_params)
    (subst_context (inds (inductive_mind ind) (abstract_instance mdecl.(ind_universes))
        mdecl.(ind_bodies)) #|mdecl.(ind_params)|
      cdecl.(cstr_args)).

Definition case_branch_context_gen ind mdecl params puinst bctx cdecl : context :=
  map2 set_binder_name bctx
    (inst_case_context params puinst (cstr_branch_context ind mdecl cdecl)).

Definition case_branch_context ind mdecl cdecl p (br : branch term) : context :=
  case_branch_context_gen ind mdecl p.(pparams) p.(puinst) br.(bcontext) cdecl.

Definition case_branches_contexts_gen ind mdecl idecl params puinst (brs : list (branch term)) : list context :=
  map2 (fun br cdecl => case_branch_context_gen ind mdecl params puinst br.(bcontext) cdecl) brs idecl.(ind_ctors).

Definition case_branches_contexts ind mdecl idecl p (brs : list (branch term)) : list context :=
  map2 (fun br => case_branch_context_gen ind mdecl p.(pparams) p.(puinst) br.(bcontext)) brs idecl.(ind_ctors).

Definition case_branch_type_gen ind mdecl params puinst ptm i cdecl (br : branch term) : context * term :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list cdecl.(cstr_args) in
  let cstrapp := mkApps cstr (map (lift0 #|cdecl.(cstr_args)|) params ++ args) in
  let brctx := case_branch_context_gen ind mdecl params puinst br.(bcontext) cdecl in
  let upars := subst_instance puinst mdecl.(ind_params) in
  let indices :=
    (map (subst (List.rev params) #|cdecl.(cstr_args)|)
      (map (expand_lets_k upars #|cdecl.(cstr_args)|)
        (map (subst (inds (inductive_mind ind) puinst mdecl.(ind_bodies))
                    (#|mdecl.(ind_params)| + #|cdecl.(cstr_args)|))
          (map (subst_instance puinst) cdecl.(cstr_indices))))) in
  let ty := mkApps (lift0 #|cdecl.(cstr_args)| ptm) (indices ++ [cstrapp]) in
  (brctx, ty).

Definition case_branch_type ind mdecl p ptm i cdecl br : context * term :=
  case_branch_type_gen ind mdecl p.(pparams) p.(puinst) ptm i cdecl br.
