(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICTyping
     PCUICElimination PCUICWcbvEval PCUICFirstorder
     PCUICWellScopedCumulativity PCUICFirstorder PCUICNormalization PCUICReduction
     PCUICConversion PCUICPrincipality PCUICNormal.
From MetaRocq.Erasure Require EPrimitive EAst EGlobalEnv.
Import EPrimitive.
Module E := EAst.

Local Existing Instance extraction_checker_flags.

(* A term is erasable if it has _a_ type which either:
  - is a syntactic arity
  - is of propositional type *)
Definition isErasable Σ Γ t :=
  ∑ T, Σ ;;; Γ |- t : T ×
  (isArity T + (∑ u, (Σ ;;; Γ |- T : tSort u) * Sort.is_propositional u))%type.

(* A more positive notion of relevant terms.
  Showing that a term is not erasable requires quantification over all its possible typings.
  We give a more positive characterization of relevant terms. A term is not erasable if
  it has _a_ type in normal form which is not an arity and whose sort is not propositional.
*)
Definition nisErasable Σ Γ t :=
  ∑ T u,
    [× Σ;;; Γ |- t : T,
      nf Σ Γ T,
    ~ isArity T,
    Σ;;; Γ |- T : tSort u &
    ~ Sort.is_propositional u].

Lemma nisErasable_spec Σ Γ t :
  wf_ext Σ -> wf_local Σ Γ ->
  nisErasable Σ Γ t -> ~ ∥ isErasable Σ Γ t ∥.
Proof.
  intros wf wf' [T [u []]].
  intros []. destruct X as [T' []].
  destruct s.
  * destruct (common_typing _ _ t0 t2) as (? & e & ? & ?).
    eapply PCUICClassification.invert_cumul_arity_l_gen in e. destruct e as [s [[hr] ha]].
    eapply (proj2 (nf_red _ _ _ _)) in n. 2:eapply hr. subst. contradiction.
    eapply PCUICClassification.invert_cumul_arity_r_gen. 2:exact w.
    exists T'. split; auto. sq.
    eapply PCUICValidity.validity in t2 as (_ & s & Hs & _).
    eapply PCUICClassification.wt_closed_red_refl; eauto.
  * destruct (principal_type _ _ t0) as [princ hprinc].
    destruct s as [u' [hs isp]].
    pose proof (hprinc _ t2) as [].
    destruct (PCUICValidity.validity t3) as (_ & s & Hs & _).
    eapply PCUICElimination.unique_sorting_equality_propositional in hs; tea; eauto.
    pose proof (hprinc _ t0) as [].
    eapply PCUICElimination.unique_sorting_equality_propositional in t1; tea; eauto.
    congruence.
Qed.

Fixpoint mkAppBox c n :=
  match n with
  | 0 => c
  | S n => mkAppBox (E.tApp c E.tBox) n
  end.

Reserved Notation "Σ ;;; Γ |- s ⇝ℇ t" (at level 50, Γ, s, t at next level).

Definition erase_context (Γ : context) : list name :=
  map (fun d => d.(decl_name).(binder_name)) Γ.

Inductive erase_prim_model (erase : term -> E.term -> Prop) : forall {t : prim_tag},
  @PCUICPrimitive.prim_model term t -> @prim_model E.term t -> Type :=
| erase_primInt i : @erase_prim_model erase primInt (PCUICPrimitive.primIntModel i) (primIntModel i)
| erase_primFloat f : @erase_prim_model erase primFloat (PCUICPrimitive.primFloatModel f) (primFloatModel f)
| erase_primString s : @erase_prim_model erase primString (PCUICPrimitive.primStringModel s) (primStringModel s)
| erase_primArray a ed ev :
    erase a.(PCUICPrimitive.array_default) ed ->
    All2 erase a.(PCUICPrimitive.array_value) ev ->
    @erase_prim_model erase primArray
      (PCUICPrimitive.primArrayModel a) (primArrayModel {| array_default := ed; array_value := ev |}).
Derive Signature NoConfusion for erase_prim_model.

Inductive erase_prim_val (erase : term -> E.term -> Prop) :
  PCUICPrimitive.prim_val term -> prim_val E.term -> Prop :=
| erase_prim t m m' : @erase_prim_model erase t m m' ->
  erase_prim_val erase (t; m) (t; m').
Derive Signature for erase_prim_val.

Inductive erases (Σ : global_env_ext) (Γ : context) : term -> E.term -> Prop :=
    erases_tRel : forall i : nat, Σ;;; Γ |- tRel i ⇝ℇ E.tRel i
  | erases_tVar : forall n : ident, Σ;;; Γ |- tVar n ⇝ℇ E.tVar n
  | erases_tEvar : forall (m m' : nat) (l : list term) (l' : list E.term),
                   All2 (erases Σ Γ) l l' -> Σ;;; Γ |- tEvar m l ⇝ℇ E.tEvar m' l'
  | erases_tLambda : forall (na : aname) (b t : term) (t' : E.term),
                     Σ;;; (vass na b :: Γ) |- t ⇝ℇ t' ->
                     Σ;;; Γ |- tLambda na b t ⇝ℇ E.tLambda na.(binder_name) t'
  | erases_tLetIn : forall (na : aname) (t1 : term) (t1' : E.term)
                      (T t2 : term) (t2' : E.term),
                    Σ;;; Γ |- t1 ⇝ℇ t1' ->
                    Σ;;; (vdef na t1 T :: Γ) |- t2 ⇝ℇ t2' ->
                    Σ;;; Γ |- tLetIn na t1 T t2 ⇝ℇ E.tLetIn na.(binder_name) t1' t2'
  | erases_tApp : forall (f u : term) (f' u' : E.term),
                  Σ;;; Γ |- f ⇝ℇ f' ->
                  Σ;;; Γ |- u ⇝ℇ u' -> Σ;;; Γ |- tApp f u ⇝ℇ E.tApp f' u'
  | erases_tConst : forall (kn : kername) (u : Instance.t),
                    Σ;;; Γ |- tConst kn u ⇝ℇ E.tConst kn
  | erases_tConstruct : forall (kn : inductive) (k : nat) (n : Instance.t),
        ~~ isPropositional Σ kn ->
        Σ;;; Γ |- tConstruct kn k n ⇝ℇ E.tConstruct kn k []
  | erases_tCase (ci : case_info) (p : predicate term) (c : term)
        (brs : list (branch term)) (c' : E.term)
        (brs' : list (list name × E.term)) :
        Subsingleton Σ ci.(ci_ind) ->
        Σ;;; Γ |- c ⇝ℇ c' ->
        All2
          (fun (x : branch term) (x' : list name × E.term) =>
          Σ;;; Γ ,,, inst_case_branch_context p x |- bbody x ⇝ℇ snd x' × erase_context (bcontext x) = fst x') brs brs' ->
        Σ;;; Γ |- tCase ci p c brs ⇝ℇ E.tCase (ci.(ci_ind), ci.(ci_npar)) c' brs'
  | erases_tProj : forall p (c : term) (c' : E.term),
                   let ind := p.(proj_ind) in
                   Subsingleton Σ ind ->
                   Σ;;; Γ |- c ⇝ℇ c' -> Σ;;; Γ |- tProj p c ⇝ℇ E.tProj p c'
  | erases_tFix : forall (mfix : mfixpoint term) (n : nat) (mfix' : list (E.def E.term)),
                  All2
                    (fun (d : def term) (d' : E.def E.term) =>
                     [× d.(dname).(binder_name) = E.dname d', rarg d = E.rarg d',
                      isLambda (dbody d), E.isLambda (E.dbody d') &
                      Σ;;; Γ ,,, fix_context mfix |- dbody d ⇝ℇ E.dbody d']) mfix mfix' ->
                  Σ;;; Γ |- tFix mfix n ⇝ℇ E.tFix mfix' n
  | erases_tCoFix : forall (mfix : mfixpoint term) (n : nat) (mfix' : list (E.def E.term)),
                    All2
                      (fun (d : def term) (d' : E.def E.term) =>
                      d.(dname).(binder_name) = E.dname d'
                       × rarg d = E.rarg d'
                         × Σ;;; Γ ,,, fix_context mfix |-
                           dbody d ⇝ℇ E.dbody d') mfix mfix' ->
                    Σ;;; Γ |- tCoFix mfix n ⇝ℇ E.tCoFix mfix' n
  | erases_tPrim : forall p p',
    erase_prim_val (erases Σ Γ) p p' ->
    Σ;;; Γ |- tPrim p ⇝ℇ E.tPrim p'
  | erases_box : forall t : term, isErasable Σ Γ t -> Σ;;; Γ |- t ⇝ℇ E.tBox
  where "Σ ;;; Γ |- s ⇝ℇ t" := (erases Σ Γ s t).

Lemma erases_forall_list_ind
      Σ (P : context -> term -> E.term -> Prop)
      (Hrel : forall Γ i, P Γ (tRel i) (E.tRel i))
      (Hvar : forall Γ n, P Γ (tVar n) (E.tVar n))
      (Hevar : forall Γ m m' l l',
          All2 (erases Σ Γ) l l' ->
          Forall2 (P Γ) l l' ->
          P Γ (tEvar m l) (E.tEvar m' l'))
      (Hlam : forall Γ na b t t',
          Σ;;; (vass na b :: Γ) |- t ⇝ℇ t' ->
          P (vass na b :: Γ) t t' ->
          P Γ (tLambda na b t) (E.tLambda na.(binder_name) t'))
      (Hletin : forall Γ na t1 t1' T t2 t2',
          Σ;;; Γ |- t1 ⇝ℇ t1' ->
          P Γ t1 t1' ->
          Σ;;; (vdef na t1 T :: Γ) |- t2 ⇝ℇ t2' ->
          P (vdef na t1 T :: Γ) t2 t2' ->
          P Γ (tLetIn na t1 T t2) (E.tLetIn na.(binder_name) t1' t2'))
      (Happ : forall Γ f4 u f' u',
          Σ;;; Γ |- f4 ⇝ℇ f' ->
          P Γ f4 f' -> Σ;;; Γ |- u ⇝ℇ u' ->
          P Γ u u' ->
          P Γ (tApp f4 u) (E.tApp f' u'))
      (Hconst : forall Γ kn u,
          P Γ (tConst kn u) (E.tConst kn))
      (Hconstruct : forall Γ kn k n,
          ~~ isPropositional Σ kn ->
          P Γ (tConstruct kn k n) (E.tConstruct kn k []))
      (Hcase : forall Γ ci p c brs c' brs',
          PCUICElimination.Subsingleton Σ ci.(ci_ind) ->
          Σ;;; Γ |- c ⇝ℇ c' ->
          P Γ c c' ->
          All2 (fun x x' => Σ;;; Γ ,,, inst_case_branch_context p x |- bbody x ⇝ℇ x'.2 ×
            erase_context (bcontext x) = x'.1) brs brs' ->
          Forall2 (fun br br' => P (Γ ,,, inst_case_branch_context p br) (bbody br) br'.2) brs brs' ->
          P Γ (tCase ci p c brs) (E.tCase (ci.(ci_ind), ci.(ci_npar)) c' brs'))
      (Hproj : forall Γ p c c',
          let ind := p.(proj_ind) in
          PCUICElimination.Subsingleton Σ ind ->
          Σ;;; Γ |- c ⇝ℇ c' ->
          P Γ c c' ->
          P Γ (tProj p c) (E.tProj p c'))
      (Hfix : forall Γ mfix n mfix',
          All2
            (fun d d' =>
               [× (dname d).(binder_name) = E.dname d',
                  rarg d = E.rarg d',
                  isLambda (dbody d), E.isLambda (E.dbody d') &
               Σ;;; app_context Γ (fix_context mfix) |- dbody d ⇝ℇ E.dbody d'])
            mfix mfix' ->
          Forall2 (fun d d' =>
                     P (app_context Γ (fix_context mfix))
                       (dbody d)
                       (EAst.dbody d') ) mfix mfix' ->
          P Γ (tFix mfix n) (E.tFix mfix' n))
      (Hcofix : forall Γ mfix n mfix',
          All2
            (fun d d' =>
               (dname d).(binder_name) = E.dname d' ×
               rarg d = E.rarg d' ×
               Σ;;; app_context Γ (fix_context mfix) |- dbody d ⇝ℇ E.dbody d')
            mfix mfix' ->
          Forall2 (fun d d' =>
                     P (app_context Γ (fix_context mfix))
                       (dbody d)
                       (EAst.dbody d') ) mfix mfix' ->
          P Γ (tCoFix mfix n) (E.tCoFix mfix' n))
      (Hprim : forall Γ p p',
        erase_prim_val (erases Σ Γ) p p' ->
        erase_prim_val (P Γ) p p' ->
        P Γ (tPrim p) (E.tPrim p'))
      (Hbox : forall Γ t, isErasable Σ Γ t -> P Γ t E.tBox) :
  forall Γ t t0,
    Σ;;; Γ |- t ⇝ℇ t0 ->
    P Γ t t0.
Proof.
  fix f 4.
  intros Γ t et er.
  move f at top.
  destruct er;
    try solve [match goal with
    | [H: _ |- _] => apply H
    end; auto].
  - apply Hevar; [assumption|].
    revert l l' X.
    fix f' 3.
    intros l l' [].
    + now constructor.
    + constructor; [now apply f|now apply f'].
  - apply Hcase; try assumption.
    + now apply f.
    + revert brs brs' X.
      fix f' 3.
      intros brs brs' []; [now constructor|].
      constructor; [now apply f|now apply f'].
  - apply Hfix; try assumption.
    revert X.
    generalize mfix at 1 3.
    intros mfix_gen.
    revert mfix mfix'.
    fix f' 3.
    intros mfix mfix' []; [now constructor|].
    destruct a. constructor; [now apply f|now apply f'].
  - apply Hcofix; try assumption.
    revert X.
    generalize mfix at 1 3.
    intros mfix_gen.
    revert mfix mfix'.
    fix f' 3.
    intros mfix mfix' []; [now constructor|].
    constructor; [now apply f|now apply f'].
  - eapply Hprim; tea.
    induction H. constructor.
    induction X; constructor.
    * now eapply f.
    * destruct a; cbn in *.
      revert array_value ev a0.
      fix f' 3; intros mfix mfix' []; [now constructor|].
      constructor; [now apply f|now apply f'].
Defined.

Definition erases_constant_body (Σ : global_env_ext) (cb : constant_body) (cb' : E.constant_body) :=
  match cst_body cb, E.cst_body cb' with
  | Some b, Some b' => erases Σ [] b b'
  | None, None => True
  | _, _ => False
  end.

Definition erases_one_inductive_body (oib : one_inductive_body) (oib' : E.one_inductive_body) :=
  Forall2 (fun cdecl cstr => cdecl.(PCUICEnvironment.cstr_arity) = cstr.(E.cstr_nargs) /\ cdecl.(cstr_name) = cstr.(E.cstr_name)) oib.(ind_ctors) oib'.(E.ind_ctors) /\
  Forall2 (fun 'i i' => i.(PCUICEnvironment.proj_name) = i'.(E.proj_name)) oib.(ind_projs) oib'.(E.ind_projs) /\
  oib'.(E.ind_name) = oib.(ind_name) /\
  oib'.(E.ind_kelim) = oib.(ind_kelim) /\
  isPropositionalArity oib.(ind_type) = oib'.(E.ind_propositional).

Definition erases_mutual_inductive_body (mib : mutual_inductive_body) (mib' : E.mutual_inductive_body) :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  Forall2 erases_one_inductive_body bds (mib'.(E.ind_bodies)) /\
  mib.(ind_npars) = mib'.(E.ind_npars).

Inductive erases_global_decls (univs : ContextSet.t) retro : global_declarations -> E.global_declarations -> Prop :=
| erases_global_nil : erases_global_decls univs retro [] []
| erases_global_cnst Σ cb cb' kn Σ' :
    erases_constant_body ({| universes := univs; declarations := Σ; retroknowledge := retro |}, cst_universes cb) cb cb' ->
    erases_global_decls univs retro Σ Σ' ->
    erases_global_decls univs retro ((kn, ConstantDecl cb) :: Σ) ((kn, E.ConstantDecl cb') :: Σ')
| erases_global_ind Σ mib mib' kn Σ' :
    erases_mutual_inductive_body mib mib' ->
    erases_global_decls univs retro Σ Σ' ->
    erases_global_decls univs retro ((kn, InductiveDecl mib) :: Σ) ((kn, E.InductiveDecl mib') :: Σ').

Definition erases_global Σ Σ' := erases_global_decls Σ.(universes) Σ.(retroknowledge) Σ.(declarations) Σ'.

Definition inductive_arity (t : term) :=
  match fst (decompose_app t) with
  | tInd ind u => Some ind
  | _ => None
  end.

(* For erasure evaluation correctness we do not need the full global
   environment to be erased, rather only (constant) dependencies of
   terms need to be there along with the inductive types that are used. *)
Inductive erases_deps (Σ : global_env) (Σ' : E.global_declarations) : E.term -> Prop :=
| erases_deps_tBox : erases_deps Σ Σ' E.tBox
| erases_deps_tRel i : erases_deps Σ Σ' (E.tRel i)
| erases_deps_tVar n : erases_deps Σ Σ' (E.tVar n)
| erases_deps_tEvar m l :
    Forall (erases_deps Σ Σ') l ->
    erases_deps Σ Σ' (E.tEvar m l)
| erases_deps_tLambda na body :
    erases_deps Σ Σ' body ->
    erases_deps Σ Σ' (E.tLambda na body)
| erases_deps_tLetIn na val body :
    erases_deps Σ Σ' val ->
    erases_deps Σ Σ' body ->
    erases_deps Σ Σ' (E.tLetIn na val body)
| erases_deps_tApp hd arg :
    erases_deps Σ Σ' hd ->
    erases_deps Σ Σ' arg ->
    erases_deps Σ Σ' (E.tApp hd arg)
| erases_deps_tConst kn cb cb' :
    declared_constant Σ kn cb ->
    EGlobalEnv.declared_constant Σ' kn cb' ->
    erases_constant_body (Σ, cst_universes cb) cb cb' ->
    (forall body, E.cst_body cb' = Some body -> erases_deps Σ Σ' body) ->
    erases_deps Σ Σ' (E.tConst kn)
| erases_deps_tConstruct ind c mdecl idecl cdecl mdecl' idecl' cdecl' :
    PCUICAst.declared_constructor Σ (ind, c) mdecl idecl cdecl ->
    EGlobalEnv.declared_constructor Σ' (ind, c) mdecl' idecl' cdecl' ->
    erases_mutual_inductive_body mdecl mdecl' ->
    erases_one_inductive_body idecl idecl' ->
    erases_deps Σ Σ' (E.tConstruct ind c [])
| erases_deps_tCase p mdecl idecl mdecl' idecl' discr brs :
    declared_inductive Σ (fst p) mdecl idecl ->
    EGlobalEnv.declared_inductive Σ' (fst p) mdecl' idecl' ->
    erases_mutual_inductive_body mdecl mdecl' ->
    erases_one_inductive_body idecl idecl' ->
    erases_deps Σ Σ' discr ->
    #|EAst.ind_ctors idecl'| = #|brs| ->
    Forall (fun br => erases_deps Σ Σ' br.2) brs ->
    erases_deps Σ Σ' (E.tCase p discr brs)
| erases_deps_tProj p mdecl idecl cdecl pdecl mdecl' idecl' cdecl' pdecl' t :
    declared_projection Σ p mdecl idecl cdecl pdecl ->
    EGlobalEnv.declared_projection Σ' p mdecl' idecl' cdecl' pdecl' ->
    erases_mutual_inductive_body mdecl mdecl' ->
    erases_one_inductive_body idecl idecl' ->
    erases_deps Σ Σ' t ->
    erases_deps Σ Σ' (E.tProj p t)
| erases_deps_tFix defs i :
    Forall (fun d => erases_deps Σ Σ' (E.dbody d)) defs ->
    erases_deps Σ Σ' (E.tFix defs i)
| erases_deps_tCoFix defs i :
    Forall (fun d => erases_deps Σ Σ' (E.dbody d)) defs ->
    erases_deps Σ Σ' (E.tCoFix defs i)
| erases_deps_tPrimInt i :
    erases_deps Σ Σ' (E.tPrim (primInt; primIntModel i))
| erases_deps_tPrimFloat f :
    erases_deps Σ Σ' (E.tPrim (primFloat; primFloatModel f))
| erases_deps_tPrimString s :
    erases_deps Σ Σ' (E.tPrim (primString; primStringModel s))
| erases_deps_tPrimArray a :
    erases_deps Σ Σ' a.(array_default) ->
    Forall (erases_deps Σ Σ') a.(array_value) ->
    erases_deps Σ Σ' (E.tPrim (primArray; primArrayModel a)).

Definition option_is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition is_axiom_decl g :=
  match g with
  | ConstantDecl cb => option_is_none cb.(cst_body)
  | InductiveDecl ind => false
  end.

Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.
  (* List.forallb (fun g => negb (is_axiom_decl g)) Σ. *)

Definition computational_ind Σ ind :=
  let 'mkInd mind n := ind in
  let mib := lookup_env Σ mind in
  match mib with
  | Some (InductiveDecl decl) =>
    match List.nth_error decl.(ind_bodies) n with
    | Some body =>
      match destArity [] body.(ind_type) with
      | Some arity => negb (Sort.is_prop (snd arity))
      | None => false
      end
    | None => false
    end
  | _ => false
  end.

Definition computational_type Σ T :=
  exists ind, inductive_arity T = Some ind /\ computational_ind Σ ind.


