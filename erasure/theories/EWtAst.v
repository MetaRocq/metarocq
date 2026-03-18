(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Template Require Import utils BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICPrimitive.
From MetaRocq.Erasure Require Import EAst EAstUtils EInduction ECSubst ELiftSubst EGlobalEnv.
(* EEtaExpanded.*)
From Equations Require Import Equations.
Set Equations Transparent.

Import MonadNotation.

(** * Well-scoped and well-formed extracted terms *)

Definition isSome {A} (o : option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Section WellScoped.
  Context (Σ : global_context).

  Definition lookup_constant kn : option constant_body :=
    decl <- EGlobalEnv.lookup_env Σ kn;;
    match decl with
    | ConstantDecl decl => Some decl
    | InductiveDecl mdecl => None
    end.

  Definition lookup_minductive kn : option mutual_inductive_body :=
    decl <- EGlobalEnv.lookup_env Σ kn;;
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).

  Definition lookup_constructor kn c : option (mutual_inductive_body * one_inductive_body * (ident × nat)) :=
    '(mdecl, idecl) <- lookup_inductive kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl, idecl, cdecl).

  Definition lookup_projection (proj : projection) :=
    '(mdecl, idecl) <- lookup_inductive (fst (fst proj)) ;;
    pdecl <- List.nth_error idecl.(ind_projs) (snd proj) ;;
    ret (mdecl, idecl, pdecl).

  Definition declared_constant id : bool :=
    isSome (lookup_constant id).

  Definition declared_minductive mind :=
    isSome (lookup_minductive mind).

  Definition declared_inductive ind :=
    isSome (lookup_inductive ind).

  Definition declared_constructor kn c :=
    isSome (lookup_constructor kn c).

  Definition declared_projection kn :=
    isSome (lookup_projection kn).

  Equations well_scoped (n : nat) (t : EAst.term) : bool :=
  { | n, tBox => true
    | n, tRel i := i <? n
    | n, tVar _ := false
    | n, tEvar m l := well_scoped_terms n l
    | _, tConst kn := declared_constant kn
    | _, tConstruct kn k := declared_constructor kn k
    | n, tLambda na b := well_scoped (S n) b
    | n, tLetIn na b b' := well_scoped n b && well_scoped (S n) b'
    | n, tApp f u := well_scoped n f && well_scoped n u
    | n, tCase (ind, pars) c brs :=
      declared_inductive ind && well_scoped n c && well_scoped_brs n brs
    | n, tProj p c :=
      declared_projection p && well_scoped n c
    | n, tFix mfix idx :=
      well_scoped_mfix (#|mfix| + n) mfix
    | n, tCoFix mfix idx :=
      well_scoped_mfix (#|mfix| + n) mfix }
  where well_scoped_terms (n : nat) (l : list term) : bool :=
  { | n, [] := true;
    | n, (t :: ts) := well_scoped n t && well_scoped_terms n ts }
  where well_scoped_brs (n : nat) (brs : list (list name × term)) : bool :=
  { | n, [] := true;
    | n, (br :: brs) := well_scoped (#|br.1| + n) br.2 && well_scoped_brs n brs }
  where well_scoped_mfix (n : nat) (mfix : mfixpoint term) : bool :=
  { | n, [] := true;
    | n, (d :: defs) := well_scoped n d.(dbody) && well_scoped_mfix n defs }.

  Lemma well_scoped_closed n t : well_scoped n t -> closedn n t.
  Proof.
    revert n t.
    apply (well_scoped_elim
      (fun n t e => e -> closedn n t)
      (fun n l e => e -> forallb (closedn n) l)
      (fun n l e => e -> forallb (fun br => closedn (#|br.1| + n) (snd br)) l)
      (fun n l e => e -> forallb (closedn n ∘ dbody) l)); cbn => //.
    all:intros *; intros; simp well_scoped.
    all:rtoProp; intuition eauto.
  Qed.

  Definition eterm n := { t : EAst.term | well_scoped n t }.
  Definition eterm_term {n} (e : eterm n) := proj1_sig e.
  Definition well_scoped_eterm {n} (e : eterm n) : well_scoped n (eterm_term e) := proj2_sig e.
End WellScoped.

Arguments eterm_term {Σ n}.

Coercion eterm_term : eterm >-> term.
Coercion well_scoped_eterm : eterm >-> is_true.

Module Constructors.
  Section Constructors.
  Context {Σ : global_context} {n : nat}.

  Obligation Tactic := idtac.
  Program Definition tBox : eterm Σ n := tBox.
  Next Obligation. cbn. exact eq_refl. Defined.


  Program Definition tRel (i : nat) (Hi : i < n) : eterm Σ n := tRel i.
  Next Obligation. cbn; intros. eapply Nat.leb_le, Hi. Defined.

  Lemma andP (a b : bool) : a -> b -> a && b.
  Proof. destruct a, b; cbn; intros; try exact eq_refl; try discriminate. Defined.

  Program Definition tEvar k (l : list (eterm Σ n)) : eterm Σ n := tEvar k (map eterm_term l).
  Next Obligation.
    cbn; intros.
    induction l; cbn. exact eq_refl.
    apply andP. exact a. exact IHl.
  Defined.

  Program Definition tLambda na (b : eterm Σ (S n)) : eterm Σ n := tLambda na b.
  Next Obligation.
    intros. exact b.
  Defined.

  Program Definition tLetIn na (b : eterm Σ n) (b' : eterm Σ (S n)) : eterm Σ n := tLetIn na b b'.
  Next Obligation.
    intros. cbn. apply andP. exact b. exact b'.
  Defined.

  Lemma ap {A B : Type} (f : A -> B) (x y : A) : x = y -> f x = f y.
  Proof. destruct 1. exact eq_refl. Defined.

  Lemma map_app {A B : Type} (f : A -> B) (l l' : list A) : map f (l ++ l') = map f l ++ map f l'.
  Proof.
    induction l; cbn. exact eq_refl.
    now apply ap.
  Defined.

  Program Definition tApp (f : eterm Σ n) (l : list (eterm Σ n)) (napp : ~~ isApp f) (nnil : l <> nil) : eterm Σ n :=
    mkApps f (map eterm_term l).
  Next Obligation.
    induction l using rev_ind => //.
    intros Hf Hl.
    specialize (IHl Hf).
    rewrite map_app EAstUtils.mkApps_app /=.
    apply andP.
    - destruct l; cbn; [exact f|].
      apply IHl. intros Heq. congruence.
    - exact x.
  Defined.

  Program Definition tConst kn (isdecl : declared_constant Σ kn) : eterm Σ n := tConst kn.

  Program Definition tConstruct ind k (isdecl : declared_constructor Σ ind k) : eterm Σ n := tConstruct ind k.

  Program Definition tCase ci (c : eterm Σ n) (brs : list (∑ args : list name, eterm Σ (#|args| + n)))
    (isdecl : declared_inductive Σ ci.1) : eterm Σ n :=
    tCase ci c (map (fun br : ∑ args, eterm Σ (#|args| + n) => (br.π1, proj1_sig br.π2)) brs).
  Next Obligation.
    intros. cbn.
    destruct ci. apply andP.
    - apply andP => //. exact c.
    - induction brs; simp well_scoped => //.
      cbn. rewrite IHbrs andb_true_r. exact a.π2.
  Qed.

  Program Definition tProj p (c : eterm Σ n) (isdecl : declared_projection Σ p) : eterm Σ n :=
    tProj p c.
  Next Obligation.
    now cbn; intros.
  Defined.
  Next Obligation.
    now cbn.
  Defined.
  Next Obligation.
    cbn.
    intros. apply andP => //. exact c.
  Defined.

  Definition edefs := ∑ mfix : mfixpoint term, well_scoped_mfix Σ (#|mfix| + n) mfix.

  Program Definition tFix (mfix : edefs) idx : eterm Σ n := (tFix mfix.π1 idx).
  Next Obligation.
    cbn; intros. exact mfix.π2.
  Defined.

  Program Definition tCoFix (mfix : edefs) idx : eterm Σ n := (tCoFix mfix.π1 idx).
  Next Obligation.
    cbn; intros; exact mfix.π2.
  Defined.
  End Constructors.
End Constructors.

Definition ebr_br Σ n := (fun br : ∑ args : list name, eterm Σ (#|args| + n) => (br.π1, proj1_sig br.π2)).

Module View.
  Section view.
    Context {Σ : global_context} {n : nat}.

    Inductive t : eterm Σ n -> Set :=
    | tBox       : t Constructors.tBox
    | tRel (i : nat) (le : i < n) : t (Constructors.tRel i le)
    | tEvar (k : nat) l : t (Constructors.tEvar k l)
    | tLambda na b : t (Constructors.tLambda na b)
    | tLetIn na b b' : t (Constructors.tLetIn na b b')
    | tApp (f : eterm Σ n) l (napp : ~~ isApp f) (nnil : l <> nil) : t (Constructors.tApp f l napp nnil)
    | tConst kn (isdecl : declared_constant Σ kn): t (Constructors.tConst kn isdecl)
    | tConstruct i k isdecl : t (Constructors.tConstruct i k isdecl)
    | tCase ci c brs isdecl : t (Constructors.tCase ci c brs isdecl)
    | tProj p c isdecl : t (Constructors.tProj p c isdecl)
    | tFix mfix idx : t (Constructors.tFix mfix idx)
    | tCoFix mfix idx : t (Constructors.tCoFix mfix idx).
    Derive Signature for t.

    Equations view_term {e} (v : t e) : term :=
    | tBox => EAst.tBox
    | tRel i le => EAst.tRel i
    | tEvar k l => EAst.tEvar k (map eterm_term l)
    | tLambda na b => EAst.tLambda na b
    | tLetIn na b b' => EAst.tLetIn na b b'
    | tApp f l napp nnil => EAst.mkApps f (map eterm_term l)
    | tConst kn isdecl => EAst.tConst kn
    | tConstruct i k isdecl => EAst.tConstruct i k
    | tCase ci c brs isdecl => EAst.tCase ci c (map (ebr_br Σ n) brs)
    | tProj p c isdecl => EAst.tProj p c
    | tFix mfix idx => EAst.tFix mfix.π1 idx
    | tCoFix mfix idx => EAst.tCoFix mfix.π1 idx.

  End view.

  Section ViewSizes.
    Context {Σ : global_context} {n : nat}.

    Lemma view_size_let_def {na} {b : eterm Σ n} {b' : eterm Σ (S n)} : size b < size (Constructors.tLetIn na b b').
    Proof. cbn. lia. Qed.

    Lemma view_size_let_body {na} {b : eterm Σ n} {b' : eterm Σ (S n)} : size b' < size (Constructors.tLetIn na b b').
    Proof. cbn. lia. Qed.

    Lemma view_size_lambda {na} {b : eterm Σ (S n)} : size b < size (Constructors.tLambda na b).
    Proof. cbn. lia. Qed.

  End ViewSizes.

End View.


Lemma well_scoped_irr {Σ n t} (ws ws' : well_scoped Σ n t) : ws = ws'.
Proof. apply uip. Defined.

Section view.
  Context {Σ : global_context} {n : nat}.

  Equations? ws_list (l : list term) (ws : well_scoped_terms Σ n l) : list (eterm Σ n) :=
    | [], _ => []
    | t :: ts, ws => (exist _ t _) :: ws_list ts _.
  Proof.
    all:move/andP: ws => [] //.
  Qed.

  Lemma ws_list_eq l ws : map eterm_term (ws_list l ws) = l.
  Proof. funelim (ws_list l ws); cbn; auto. now rewrite H. Qed.

  Equations? ws_brs (l : list (list name × term)) (ws : well_scoped_brs Σ n l) : list (∑ args, eterm Σ (#|args| + n)) :=
    | [], _ => []
    | t :: ts, ws => (t.1; exist _ t.2 _) :: ws_brs ts _.
  Proof.
    all:move/andP: ws => [] //.
  Qed.

  Lemma ws_brs_eq l ws : map (ebr_br Σ n) (ws_brs l ws) = l.
  Proof. funelim (ws_brs l ws); cbn; auto. rewrite H. destruct t => //. Qed.

  Lemma andb_left {a b} : a && b -> a.
  Proof.
    move/andP=>[] //.
  Qed.

  Lemma andb_right {a b} : a && b -> b.
  Proof.
    move/andP=>[] //.
  Qed.

  Lemma well_scoped_terms_forallb {l} : well_scoped_terms Σ n l = forallb (well_scoped Σ n) l.
  Proof.
    induction l; simp well_scoped; auto.
    now rewrite IHl.
  Qed.

  Lemma well_scoped_mkApps {f l} : well_scoped Σ n (mkApps f l) -> well_scoped Σ n f && well_scoped_terms Σ n l.
  Proof.
    induction l using rev_ind; cbn; auto.
    - now intros ->.
    - rewrite mkApps_app /=.
      move/andP=> [] wfl wx.
      move/andP: (IHl wfl) => [] => -> wfnl /=.
      now rewrite well_scoped_terms_forallb forallb_app -well_scoped_terms_forallb /= wfnl wx.
  Qed.

  Notation " ( x ⧆ y ) " := (exist _ x y).

  Definition view (x : eterm Σ n) : View.t x.
  Proof.
    destruct x as [t ws].
    set (t' := t).
    destruct t;
    try solve [evar (ws' : well_scoped Σ n    t' = true); rewrite (well_scoped_irr ws ws'); subst ws' t';
      unshelve econstructor; eauto].
    - evar (ws' : well_scoped Σ n t' = true); rewrite (well_scoped_irr ws ws'); subst ws' t'.
      unshelve econstructor. now eapply Nat.leb_le.
    - cbn in ws; discriminate.
    - pose proof (ws_list_eq l ws). set(l' := ws_list l ws) in *. clearbody l'.
      subst t'.
      revert ws. destruct H.
      intros ws. set (t' := tEvar _ _).
      evar (ws' : well_scoped Σ n t' = true); rewrite (well_scoped_irr ws ws'); subst ws' t'.
      econstructor.
    - cbn in ws.
      change t with (eterm_term (exist _ t ws)) in t'.
      evar (ws' : well_scoped Σ n t' = true); rewrite (well_scoped_irr ws ws'); subst ws' t'.
      econstructor.
    - change t2 with (eterm_term (t2 ⧆ andb_right ws)) in t'.
      change t1 with (eterm_term (t1 ⧆ andb_left ws)) in t'.
      revert t'.
      set (prf := andb_left ws).
      set (prf' := andb_right _). clearbody prf prf'.
      intros t'.
      evar (ws' : well_scoped Σ n t' = true).
      rewrite (well_scoped_irr ws ws'); subst ws' t'.
      econstructor.
    - destruct (decompose_app (tApp t1 t2)) eqn:da.
      move: ws. revert t'.
      rewrite (decompose_app_inv da).
      intros t' ws.
      move: (decompose_app_notApp _ _ _ da).
      move: (EInduction.decompose_app_app _ _ _ _ da).
      clear da t1 t2.
      pose proof (wfa := well_scoped_mkApps ws).
      pose proof (ws_list_eq l (andb_right wfa)).
      set(l'' := ws_list l _) in *. clearbody l''.
      move: ws. revert t'.
      destruct H.
      intros t'.
      change t with (eterm_term (t ⧆ andb_left wfa)) in t'.
      set (prfa := andb_left wfa) in *. clearbody prfa.
      intros ws hl ht.
      evar (ws' : well_scoped Σ n t' = true).
      rewrite (well_scoped_irr ws ws'); subst ws' t'.
      unshelve econstructor. exact ht.
      intros hl'. subst l''. cbn in hl. congruence.

    - destruct p as [ind k].
      change t with (eterm_term (t ⧆ andb_right (andb_left ws))) in t'.
      set (prf1 := andb_right _) in t'. clearbody prf1.
      pose proof (ws_brs_eq _ (andb_right ws)).
      set (prf2 := andb_right _) in *. clearbody prf2.
      revert t' ws. destruct H.
      intros t' ws.
      evar (ws' : well_scoped Σ n t' = true).
      rewrite (well_scoped_irr ws ws'); subst ws' t'.
      unshelve econstructor.
      cbn. apply (andb_left (andb_left ws)).

    - change t with (eterm_term (t ⧆ andb_right ws)) in t'.
      set (prf := andb_right ws) in *. clearbody prf.
      evar (ws' : well_scoped Σ n t' = true).
      rewrite (well_scoped_irr ws ws'); subst ws' t'.
      unshelve econstructor. apply (andb_left ws).
    - change m with (((m; ws) : Constructors.edefs).π1) in t'.
      evar (ws' : well_scoped Σ n t' = true).
      rewrite (well_scoped_irr ws ws'); subst ws' t'.
      econstructor.
    - change m with (((m; ws) : Constructors.edefs).π1) in t'.
      evar (ws' : well_scoped Σ n t' = true).
      rewrite (well_scoped_irr ws ws'); subst ws' t'.
      econstructor.
  Defined.

  Lemma view_term (t : eterm Σ n) (v : View.t t) : View.view_term v = t.
  Proof.
    induction v; cbn; reflexivity.
  Qed.

  Lemma view_view_term (t : eterm Σ n) : View.view_term (view t) = t.
  Proof. apply view_term. Qed.

  Lemma view_view_size (t : eterm Σ n) : size (View.view_term (view t)) = size t.
  Proof. now rewrite view_view_term. Qed.

End view.

From Stdlib Require Import Relation_Definitions.

Section test_view.
  Context (Σ : global_context).
  Import View.

  Definition eterm_size : relation (∑ n, eterm Σ n) :=
    MR lt (fun x : ∑ n, eterm Σ n => size x.π2).

  Instance wf_size : WellFounded eterm_size.
  Proof. unfold eterm_size. tc. Defined.
  Obligation Tactic := idtac.

  #[derive(eliminator=no)]
  Equations? test_view (n : nat) (t : eterm Σ n) : bool
    by wf (n; t) eterm_size :=
    test_view n t with view t := {
      | tBox => true
      | tRel i lei => false
      | tApp f args notapp notnil => test_view n f
      | _ => false
    }.
  Proof.
    do 2 red. cbn. rewrite size_mkApps.
    destruct args; cbn; try congruence. lia.
  Qed.

End test_view.
