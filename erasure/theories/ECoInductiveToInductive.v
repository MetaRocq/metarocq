(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EExtends
    ELiftSubst ECSubst EGlobalEnv EInduction EWellformed EWcbvEval
    EEnvMap EProgram EFirstorder.

Import MRList (map_InP, map_InP_elim, map_InP_spec).

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

#[global]
Hint Constructors eval : core.

(** * Translation of coinductive types to lazy inductive types

  Coinductive constructors are thunked, matches and projections on
  coinductive types force their scrutinee, and a cofixpoint
  [cofix f (x1 .. xn) := b], where [n] is its arity ([rarg]), becomes the
  fixpoint [fix f (x1 .. xn) := tLazy (tForce b')]. *)

(** [wrap_lazy n t] goes under the [n] leading lambdas of [t] and thunks the
    body. On a term with fewer lambdas the wrapper is put where they stop:
    this does not happen on wellformed cofixpoints. *)
Fixpoint wrap_lazy (n : nat) (t : term) : term :=
  match n, t with
  | S n, tLambda na b => tLambda na (wrap_lazy n b)
  | _, _ => tLazy (tForce t)
  end.

Definition wrap_def (d : def term) : def term :=
  {| dname := dname d; dbody := wrap_lazy (rarg d) (dbody d);
     rarg := rarg d |}.

(** [beta_apps t args]: the result of the beta-reductions of
    [mkApps t args] when [t] starts with [#|args|] lambdas. *)
Fixpoint beta_apps (t : term) (args : list term) : term :=
  match args with
  | [] => t
  | a :: args =>
    match t with
    | tLambda _ b => beta_apps (ECSubst.csubst a 0 b) args
    | _ => t
    end
  end.

Section trans.
  Context (Σ : GlobalContextMap.t).

  Fixpoint trans (t : term) : term :=
    match t with
    | tRel i => tRel i
    | tEvar ev args => tEvar ev (List.map trans args)
    | tLambda na M => tLambda na (trans M)
    | tApp u v => tApp (trans u) (trans v)
    | tLetIn na b b' => tLetIn na (trans b) (trans b')
    | tCase ind c brs =>
      let brs' := List.map (on_snd trans) brs in
      if GlobalContextMap.is_coind Σ (fst ind).(inductive_mind)
      then tCase ind (tForce (trans c)) brs'
      else tCase ind (trans c) brs'
    | tProj p c =>
      if GlobalContextMap.is_coind Σ p.(proj_ind).(inductive_mind)
      then tProj p (tForce (trans c))
      else tProj p (trans c)
    | tFix mfix idx =>
      let mfix' := List.map (map_def trans) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := List.map (map_def trans) mfix in
      tFix (List.map wrap_def mfix') idx
    | tBox => t
    | tVar _ => t
    | tConst _ => t
    | tConstruct ind i args =>
      if GlobalContextMap.is_coind Σ ind.(inductive_mind)
      then tLazy (tConstruct ind i (map trans args))
      else tConstruct ind i (map trans args)
    | tPrim p => tPrim (map_prim trans p)
    | tLazy t => tLazy (trans t)
    | tForce t => tForce (trans t)
    end.

  (* cofix succ x := match x with Stream x xs => Stream (x + 1) (succ xs) ->

    fix succ x := lazy (force (match force x with
      Stream x xs => lazy (Stream (x + 1) (succ xs))))

    cofix ones := Stream 1 ones ->
    fix ones := lazy (force (lazy (Stream 1 ones)))
  *)

  Lemma trans_mkApps f l : trans (mkApps f l) = mkApps (trans f) (map trans l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.


  Import ECSubst.


  Lemma csubst_closed t k x : closedn k x -> csubst t k x = x.
  Proof using Type.
    induction x in k |- * using EInduction.term_forall_list_ind; simpl; auto.
    all:try solve [intros; f_equal; solve_all; eauto].
    intros Hn. eapply Nat.ltb_lt in Hn.
    - destruct (Nat.compare_spec k n); try lia. reflexivity.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
  Qed.

  Lemma closedn_wrap_lazy n k t : closedn k (wrap_lazy n t) = closedn k t.
  Proof using Type.
    induction n in k, t |- *; destruct t; cbn; auto.
  Qed.

  Lemma closed_trans t k : closedn k t -> closedn k (trans t).
  Proof using Type.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct GlobalContextMap.is_coind => /= //; solve_all.
    - move/andP: H => [] clt clargs.
      destruct GlobalContextMap.is_coind => /= //; rtoProp; solve_all;
        solve_all.
    - destruct GlobalContextMap.is_coind => /= //; rtoProp; solve_all;
        solve_all.
    - solve_all. rewrite closedn_wrap_lazy. eauto.
    - primProp. solve_all_k 6.
  Qed.


  Lemma isLambdas_trans n t : isLambdas n t -> isLambdas n (trans t).
  Proof using Type.
    induction n in t |- *; destruct t => //=. apply IHn.
  Qed.

End trans.

(** ** Properties of [wrap_lazy] and [beta_apps] *)

Lemma isLambdas_substl n s t :
  isLambdas n t -> isLambdas n (ECSubst.substl s t).
Proof.
  induction s in t |- *; cbn; auto.
  intros h. now apply IHs, ECSubst.isLambdas_csubst.
Qed.

Lemma wrap_lazy_csubst n a k t :
  isLambdas n t ->
  ECSubst.csubst a k (wrap_lazy n t) = wrap_lazy n (ECSubst.csubst a k t).
Proof.
  induction n in k, t |- *; destruct t; cbn; auto; try discriminate.
  intros h. now rewrite IHn.
Qed.

Lemma wrap_lazy_substl n s t :
  isLambdas n t ->
  ECSubst.substl s (wrap_lazy n t) = wrap_lazy n (ECSubst.substl s t).
Proof.
  induction s in t |- *; cbn; auto.
  intros h. rewrite wrap_lazy_csubst //.
  now apply IHs, ECSubst.isLambdas_csubst.
Qed.

Lemma wrap_def_csubst a k d :
  isLambdas (rarg d) (dbody d) ->
  map_def (ECSubst.csubst a k) (wrap_def d) =
  wrap_def (map_def (ECSubst.csubst a k) d).
Proof.
  intros h. rewrite /wrap_def /map_def /=. f_equal.
  now apply wrap_lazy_csubst.
Qed.

Lemma beta_apps_app t l l' :
  beta_apps t (l ++ l') = beta_apps (beta_apps t l) l'.
Proof.
  induction l in t |- *; cbn; auto.
  destruct t; auto; now destruct l'.
Qed.

Lemma isLambdas_beta_apps n t vs :
  isLambdas n t -> #|vs| <= n -> isLambdas (n - #|vs|) (beta_apps t vs).
Proof.
  induction vs in n, t |- *; cbn.
  - now rewrite Nat.sub_0_r.
  - destruct n; [lia|]. destruct t => //=.
    intros h hl. apply IHvs; [|lia].
    now apply ECSubst.isLambdas_csubst.
Qed.


Lemma closed_beta_apps t vs :
  closed t -> forallb (closedn 0) vs -> closed (beta_apps t vs).
Proof.
  induction vs in t |- *; cbn; auto.
  move=> clt /andP[] cla clvs.
  destruct t => //. apply IHvs => //.
  now apply ECSubst.closed_csubst.
Qed.

Lemma isLambdas_S_inv n t :
  isLambdas (S n) t -> ∑ na b, t = tLambda na b /\ isLambdas n b.
Proof.
  destruct t => //=. intros h. now do 2 eexists.
Qed.


Lemma cunfold_fix_wrap_def mfix idx d :
  nth_error mfix idx = Some d ->
  isLambdas (rarg d) (dbody d) ->
  EGlobalEnv.cunfold_fix (map wrap_def mfix) idx =
  Some (rarg d, wrap_lazy (rarg d)
    (ECSubst.substl (EGlobalEnv.fix_subst (map wrap_def mfix)) (dbody d))).
Proof.
  intros hnth hl. rewrite /EGlobalEnv.cunfold_fix nth_error_map hnth /=.
  now rewrite wrap_lazy_substl.
Qed.


Import EWcbvEval.

Notation "Σ ⊢ s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.


Definition trans_constant_decl Σ cb :=
  {| cst_body := option_map (trans Σ) cb.(cst_body) |}.

(** Coinductive types become inductive types: their values are thunks of
    constructor applications. *)
Definition trans_inductive_decl (mib : mutual_inductive_body) :=
  {| ind_finite :=
       match mib.(ind_finite) with
       | CoFinite => Finite
       | k => k
       end;
     ind_npars := mib.(ind_npars);
     ind_bodies := mib.(ind_bodies) |}.

Definition trans_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (trans_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl (trans_inductive_decl idecl)
  end.

Definition trans_env Σ :=
  map (on_snd (trans_decl Σ)) Σ.(GlobalContextMap.global_decls).

Import EnvMap.

Program Fixpoint trans_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
    on_snd (trans_decl Σg) hd :: trans_env' tl (fresh_globals_cons_inv HΣ)
  end.

Import EGlobalEnv EExtends.


Lemma extends_lookup_inductive_kind {efl : EEnvFlags} {Σ Σ' ind} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_minductive Σ ind) ->
  lookup_inductive_kind Σ ind = lookup_inductive_kind Σ' ind.
Proof.
  intros ext wf.
  unfold lookup_inductive_kind. cbn.
  destruct lookup_env as [[]|] eqn:hl => //.
  now rewrite (extends_lookup wf ext hl).
Qed.

Lemma wellformed_trans_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  forall n, EWellformed.wellformed Σ n t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  trans Σ t = trans Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive
    lookup_projection
    lookup_constructor
    GlobalContextMap.lookup_inductive_kind]; intros => //.
  all:unfold wf_fix_gen in *; rtoProp; intuition auto.
  all:try now f_equal; eauto; solve_all.
  - rewrite /GlobalContextMap.is_coind
      !GlobalContextMap.lookup_inductive_kind_spec.
    destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
    destruct cstr_as_blocks.
    { move/andP: H2 => [] hpars hargs.
      assert (map (trans Σ) args = map (trans Σ') args) as -> by solve_all.
      rewrite (extends_lookup_inductive_kind H0 H1) //.
      apply lookup_constructor_lookup_inductive in hl.
      unfold lookup_inductive in hl.
      destruct lookup_minductive => //. }
    { destruct args => // /=.
      rewrite (extends_lookup_inductive_kind H0 H1) //.
      apply lookup_constructor_lookup_inductive in hl.
      unfold lookup_inductive in hl.
      destruct lookup_minductive => //. }
  - rewrite /GlobalContextMap.is_coind
      !GlobalContextMap.lookup_inductive_kind_spec.
    move: H2; rewrite /wf_brs.
    destruct lookup_inductive as [[mdecl idecl]|] eqn:hl => //.
    assert (map (on_snd (trans Σ)) l = map (on_snd (trans Σ')) l) as -> by solve_all.
    rewrite (extends_lookup_inductive_kind H0 H1) //.
    unfold lookup_inductive in hl.
    destruct lookup_minductive => //.
    rewrite (IHt _ H4 _ H0 H1) //.
  - rewrite /GlobalContextMap.is_coind
      !GlobalContextMap.lookup_inductive_kind_spec.
    destruct (lookup_projection) as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => //.
    eapply lookup_projection_lookup_constructor in hl.
    eapply lookup_constructor_lookup_inductive in hl.
    rewrite (extends_lookup_inductive_kind H0 H1) //.
    unfold lookup_inductive in hl.
    destruct lookup_minductive => //.
    rewrite (IHt _ H2 _ H0 H1) //.
Qed.

Lemma wellformed_trans_decl_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_global_decl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  trans_decl Σ t = trans_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold trans_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_trans_extends.
Qed.

Lemma lookup_env_trans_env_Some {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn d :
  wf_glob Σ ->
  GlobalContextMap.lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t,
    [× extends_prefix Σ' Σ, wf_global_decl Σ' d &
      lookup_env (trans_env Σ) kn = Some (trans_decl Σ' d)].
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  induction Σ in map, repr, wf |- *; simpl; auto => //.
  intros wfg.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-].
    exists (GlobalContextMap.make Σ (fresh_globals_cons_inv wf)). split.
    cbn. now exists [a]. now depelim wfg.
    depelim wfg; eauto.
    f_equal. symmetry. eapply wellformed_trans_decl_extends. cbn; auto. cbn.
    now eapply extends_fresh. cbn. now constructor.
  - intros _.
    set (Σ' := GlobalContextMap.make Σ (fresh_globals_cons_inv wf)).
    specialize (IHΣ (GlobalContextMap.map Σ') (GlobalContextMap.repr Σ') (GlobalContextMap.wf Σ')).
    cbn in IHΣ. forward IHΣ. now depelim wfg.
    intros hl. specialize (IHΣ hl) as [Σ'' [ext wfgd hl']].
    exists Σ''. split => //.
    * destruct ext as [? ->].
      now exists (a :: x).
    * rewrite -hl'. f_equal.
      clear -wfg.
      eapply map_ext_in => kn hin. unfold on_snd. f_equal.
      symmetry. eapply wellformed_trans_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      cbn. destruct a. eapply extends_fresh. now depelim wfg.
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_env_trans_env_None {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  GlobalContextMap.lookup_env Σ kn = None ->
  lookup_env (trans_env Σ) kn = None.
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_trans {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  wf_glob Σ ->
  lookup_env (trans_env Σ) kn = option_map (trans_decl Σ) (lookup_env Σ kn).
Proof.
  intros wf.
  rewrite -GlobalContextMap.lookup_env_spec.
  destruct (GlobalContextMap.lookup_env Σ kn) eqn:hl.
  - eapply lookup_env_trans_env_Some in hl as [Σ' [ext wf' hl']] => /= //.
    rewrite hl'. f_equal.
    eapply wellformed_trans_decl_extends; eauto.
    now eapply extends_prefix_extends.
  - cbn. now eapply lookup_env_trans_env_None in hl.
Qed.

Lemma is_propositional_trans {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (trans_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_trans (inductive_mind ind) wf) //.
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //=.
  repeat (destruct nth_error => //=).
Qed.

Lemma is_propositional_cstr_trans {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind c :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (trans_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_trans (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //=.
  repeat (destruct nth_error => //=).
Qed.


Lemma lookup_constructor_trans {efl : EEnvFlags}
  {Σ : GlobalContextMap.t} {ind c} :
  wf_glob Σ ->
  lookup_constructor (trans_env Σ) ind c =
  option_map (fun '(mdecl, idecl, cdecl) =>
    (trans_inductive_decl mdecl, idecl, cdecl)) (lookup_constructor Σ ind c).
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_trans // /=. destruct lookup_env as [[]|] => // /=.
  destruct nth_error => //=. destruct nth_error => //.
Qed.

(** No coinductive type is left in the translated environment. *)
Lemma is_coind_trans_env {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  wf_glob Σ -> EGlobalEnv.is_coind (trans_env Σ) kn = false.
Proof.
  intros wfΣ.
  rewrite /EGlobalEnv.is_coind /lookup_inductive_kind /lookup_minductive.
  rewrite lookup_env_trans // /=. destruct lookup_env as [[]|] => // /=.
  now destruct (ind_finite m).
Qed.


Lemma value_constructor_as_block {wfl : WcbvFlags} {Σ ind c args} : value Σ (tConstruct ind c args) ->
  All (value Σ) args.
Proof.
  intros h; depelim h.
  - depelim a. cbn in i. destruct args => //.
  - eauto.
  - depelim v; solve_discr.
Qed.


(** ** The relation between source and target terms

  A source value which is an applied cofixpoint or a coinductive
  constructor with evaluated arguments is not the translation of a term: the
  target computes an unevaluated thunk instead. Correctness is hence stated
  using a relation between source and target terms which contains the graph
  of the translation, is closed under substitution of related closed terms,
  and relates the values computed on both sides. *)

(** Related definitions of a cofixpoint block: the target definition [d0] is
    the one before thunking of its body by [wrap_def]. *)
Definition def_rel (R : term -> term -> Type) (d d0 : def term) :=
  [× dname d = dname d0, rarg d = rarg d0,
    isLambdas (rarg d0) (dbody d0) & R (dbody d) (dbody d0)].

(** The value computed in the target by a cofixpoint applied to arguments
    [args'], up to its arity. *)
Definition cofix_app_target (mfix0 : mfixpoint term) (d0 : def term)
  (nargs : nat) (args' : list term) :=
  wrap_lazy (rarg d0 - nargs)
    (beta_apps
      (ECSubst.substl (fix_subst (map wrap_def mfix0)) (dbody d0)) args').

Declare Scope coind_scope.
Delimit Scope coind_scope with coind.
Reserved Notation "t ≈ t'" (at level 70).
Local Open Scope coind_scope.

Section Rel.
  Context {wfl : WcbvFlags}.
  (** Source and target environments *)
  Context (Σ Σ' : global_declarations).
  Notation is_coind := (EGlobalEnv.is_coind Σ).

  (** Applied cofixpoint values: the arguments are related values and the
      target is the value computed by the translated fixpoint applied to
      them. *)
  Variant cofix_app_rel (R : term -> term -> Type) (t t' : term) : Type :=
  | cofix_app_intro mfix mfix0 idx d0 args args' :
    t = mkApps (tCoFix mfix idx) args ->
    t' = cofix_app_target mfix0 d0 #|args| args' ->
    All2 (def_rel R) mfix mfix0 ->
    nth_error mfix0 idx = Some d0 ->
    args <> [] ->
    #|args| <= rarg d0 ->
    closed (tCoFix mfix idx) ->
    forallb (closedn 0) args ->
    All (value Σ) args ->
    All (value Σ') args' ->
    All2 R args args' ->
    cofix_app_rel R t t'.

  (** The nested recursion calls for a hand-written eliminator, [crel_rect]
      below. *)
  Unset Elimination Schemes.
  Inductive crel : term -> term -> Type :=
  | crel_box : tBox ≈ tBox
  | crel_rel i : tRel i ≈ tRel i
  | crel_var id : tVar id ≈ tVar id
  | crel_evar ev args args' :
    All2 crel args args' -> tEvar ev args ≈ tEvar ev args'
  | crel_lambda na b b' : b ≈ b' -> tLambda na b ≈ tLambda na b'
  | crel_letin na b b' c c' :
    b ≈ b' -> c ≈ c' -> tLetIn na b c ≈ tLetIn na b' c'
  | crel_app f f' a a' :
    f ≈ f' -> a ≈ a' -> tApp f a ≈ tApp f' a'
  | crel_const kn : tConst kn ≈ tConst kn
  (** Constructors of inductive types *)
  | crel_construct ind c args args' :
    is_coind (inductive_mind ind) = false ->
    All2 crel args args' ->
    tConstruct ind c args ≈ tConstruct ind c args'
  (** Constructors of coinductive types are thunked *)
  | crel_construct_lazy ind c args args' :
    is_coind (inductive_mind ind) = true ->
    All2 crel args args' ->
    tConstruct ind c args ≈ tLazy (tConstruct ind c args')
  (** Coinductive values: the thunk evaluates to related arguments *)
  | crel_construct_eval ind c args t' args' :
    is_coind (inductive_mind ind) = true ->
    forallb (closedn 0) args ->
    closed t' ->
    Σ' ⊢ t' ⇓ tConstruct ind c args' ->
    All2 crel args args' ->
    tConstruct ind c args ≈ tLazy t'
  | crel_case ip discr discr' brs brs' :
    is_coind (inductive_mind ip.1) = false ->
    discr ≈ discr' ->
    All2 (fun br br' => (br.1 = br'.1) × br.2 ≈ br'.2) brs brs' ->
    tCase ip discr brs ≈ tCase ip discr' brs'
  | crel_case_force ip discr discr' brs brs' :
    is_coind (inductive_mind ip.1) = true ->
    discr ≈ discr' ->
    All2 (fun br br' => (br.1 = br'.1) × br.2 ≈ br'.2) brs brs' ->
    tCase ip discr brs ≈ tCase ip (tForce discr') brs'
  | crel_proj p c c' :
    is_coind (inductive_mind (proj_ind p)) = false ->
    c ≈ c' -> tProj p c ≈ tProj p c'
  | crel_proj_force p c c' :
    is_coind (inductive_mind (proj_ind p)) = true ->
    c ≈ c' -> tProj p c ≈ tProj p (tForce c')
  | crel_fix mfix mfix' idx :
    All2 (fun d d' => [× dname d = dname d', rarg d = rarg d' &
      dbody d ≈ dbody d']) mfix mfix' ->
    tFix mfix idx ≈ tFix mfix' idx
  (** Cofixpoints become fixpoints with thunked bodies *)
  | crel_cofix mfix mfix0 idx :
    All2 (def_rel crel) mfix mfix0 ->
    tCoFix mfix idx ≈ tFix (map wrap_def mfix0) idx
  | crel_prim p p' : prim_rel crel p p' -> tPrim p ≈ tPrim p'
  | crel_lazy t t' : t ≈ t' -> tLazy t ≈ tLazy t'
  | crel_force t t' : t ≈ t' -> tForce t ≈ tForce t'
  (** Applied cofixpoint values *)
  | crel_cofix_app t t' : cofix_app_rel crel t t' -> t ≈ t'
  where "t ≈ t'" := (crel t t') : coind_scope.
  Set Elimination Schemes.
  Derive Signature for crel.

End Rel.

Section RelInd.
  Context {wfl : WcbvFlags}.
  Context (Σ Σ' : global_declarations).
  Notation crel := (crel Σ Σ').
  Notation "t ≈ t'" := (crel t t') (at level 70) : coind_scope.
  Notation is_coind := (EGlobalEnv.is_coind Σ).
  Context (P : term -> term -> Type).
  Context (Pbox : P tBox tBox)
    (Prel : forall i, P (tRel i) (tRel i))
    (Pvar : forall id, P (tVar id) (tVar id))
    (Pevar : forall ev args args', All2 crel args args' ->
      All2 P args args' -> P (tEvar ev args) (tEvar ev args'))
    (Plambda : forall na b b', b ≈ b' -> P b b' ->
      P (tLambda na b) (tLambda na b'))
    (Pletin : forall na b b' c c', b ≈ b' -> P b b' ->
      c ≈ c' -> P c c' -> P (tLetIn na b c) (tLetIn na b' c'))
    (Papp : forall f f' a a', f ≈ f' -> P f f' -> a ≈ a' -> P a a' ->
      P (tApp f a) (tApp f' a'))
    (Pconst : forall kn, P (tConst kn) (tConst kn))
    (Pconstruct : forall ind c args args',
      is_coind (inductive_mind ind) = false ->
      All2 crel args args' -> All2 P args args' ->
      P (tConstruct ind c args) (tConstruct ind c args'))
    (Pconstruct_lazy : forall ind c args args',
      is_coind (inductive_mind ind) = true ->
      All2 crel args args' -> All2 P args args' ->
      P (tConstruct ind c args) (tLazy (tConstruct ind c args')))
    (Pconstruct_eval : forall ind c args t' args',
      is_coind (inductive_mind ind) = true ->
      forallb (closedn 0) args ->
      closed t' ->
      Σ' ⊢ t' ⇓ tConstruct ind c args' ->
      All2 crel args args' -> All2 P args args' ->
      P (tConstruct ind c args) (tLazy t'))
    (Pcase : forall ip discr discr' brs brs',
      is_coind (inductive_mind ip.1) = false ->
      discr ≈ discr' -> P discr discr' ->
      All2 (fun br br' => (br.1 = br'.1) × br.2 ≈ br'.2) brs brs' ->
      All2 (fun br br' => (br.1 = br'.1) × P br.2 br'.2) brs brs' ->
      P (tCase ip discr brs) (tCase ip discr' brs'))
    (Pcase_force : forall ip discr discr' brs brs',
      is_coind (inductive_mind ip.1) = true ->
      discr ≈ discr' -> P discr discr' ->
      All2 (fun br br' => (br.1 = br'.1) × br.2 ≈ br'.2) brs brs' ->
      All2 (fun br br' => (br.1 = br'.1) × P br.2 br'.2) brs brs' ->
      P (tCase ip discr brs) (tCase ip (tForce discr') brs'))
    (Pproj : forall p c c',
      is_coind (inductive_mind (proj_ind p)) = false ->
      c ≈ c' -> P c c' -> P (tProj p c) (tProj p c'))
    (Pproj_force : forall p c c',
      is_coind (inductive_mind (proj_ind p)) = true ->
      c ≈ c' -> P c c' -> P (tProj p c) (tProj p (tForce c')))
    (Pfix : forall mfix mfix' idx,
      All2 (fun d d' => [× dname d = dname d', rarg d = rarg d' &
        dbody d ≈ dbody d']) mfix mfix' ->
      All2 (fun d d' => [× dname d = dname d', rarg d = rarg d' &
        P (dbody d) (dbody d')]) mfix mfix' ->
      P (tFix mfix idx) (tFix mfix' idx))
    (Pcofix : forall mfix mfix0 idx,
      All2 (def_rel crel) mfix mfix0 ->
      All2 (def_rel P) mfix mfix0 ->
      P (tCoFix mfix idx) (tFix (map wrap_def mfix0) idx))
    (Pcofix_app : forall t t', cofix_app_rel Σ Σ' crel t t' ->
      cofix_app_rel Σ Σ' P t t' -> P t t')
    (Pprim : forall p p', prim_rel crel p p' -> prim_rel P p p' ->
      P (tPrim p) (tPrim p'))
    (Plazy : forall t t', t ≈ t' -> P t t' -> P (tLazy t) (tLazy t'))
    (Pforce : forall t t', t ≈ t' -> P t t' -> P (tForce t) (tForce t')).

  Lemma crel_rect : forall t t', crel t t' -> P t t'.
  Proof using Pbox Prel Pvar Pevar Plambda Pletin Papp Pconst Pconstruct
    Pconstruct_lazy Pconstruct_eval Pcase Pcase_force Pproj Pproj_force Pfix
    Pcofix Pcofix_app Pprim Plazy Pforce.
    fix aux 3. intros t t' r.
    assert (auxl : forall l l', All2 crel l l' -> All2 P l l').
    { fix auxl 3. intros l l' []; constructor;
      [apply aux; assumption|apply auxl; assumption]. }
    assert (auxbr : forall l l' : list (list name × term),
      All2 (fun br br' => (br.1 = br'.1) × crel br.2 br'.2) l l' ->
      All2 (fun br br' => (br.1 = br'.1) × P br.2 br'.2) l l').
    { fix auxl' 3. intros l l' [|? ? ? ? [e r'] rs]; constructor;
      [split; [exact e|apply aux; exact r']|apply auxl'; exact rs]. }
    assert (auxd : forall l l', All2 (def_rel crel) l l' ->
      All2 (def_rel P) l l').
    { fix auxl' 3. intros l l' [|? ? ? ? [e e' i r'] rs]; constructor;
      [split; [exact e|exact e'|exact i|apply aux; exact r']
      |apply auxl'; exact rs]. }
    destruct r.
    - apply Pbox.
    - apply Prel.
    - apply Pvar.
    - apply Pevar; auto.
    - apply Plambda; auto.
    - apply Pletin; auto.
    - apply Papp; auto.
    - apply Pconst.
    - apply Pconstruct; auto.
    - apply Pconstruct_lazy; auto.
    - eapply Pconstruct_eval; eauto.
    - apply Pcase; auto.
    - apply Pcase_force; auto.
    - apply Pproj; auto.
    - apply Pproj_force; auto.
    - apply Pfix; auto.
      revert mfix mfix' a. clear -aux.
      fix auxl' 3. intros l l' [|? ? ? ? [e e' r'] rs]; constructor;
      [split; [exact e|exact e'|apply aux; exact r']|apply auxl'; exact rs].
    - apply Pcofix; auto.
    - apply Pprim; auto.
      destruct p0; constructor; auto.
    - apply Plazy; auto.
    - apply Pforce; auto.
    - apply Pcofix_app; auto.
      destruct c. econstructor; tea; auto.
  Qed.
End RelInd.

Section RelFacts.
  Context {wfl : WcbvFlags}.
  Context (Σ Σ' : global_declarations).
  Notation crel := (crel Σ Σ').
  Notation "t ≈ t'" := (crel t t') (at level 70) : coind_scope.
  Notation is_coind := (EGlobalEnv.is_coind Σ).
  Import ECSubst.

  Lemma cofix_app_rel_isApp R t t' : cofix_app_rel Σ Σ' R t t' -> isApp t.
  Proof using Type.
    intros []. subst. destruct args using rev_case => //.
    now rewrite mkApps_app.
  Qed.

  Lemma closed_cofix_app_target mfix0 d0 idx n args' :
    closed (tFix (map wrap_def mfix0) idx) ->
    nth_error mfix0 idx = Some d0 ->
    isLambdas (rarg d0) (dbody d0) ->
    forallb (closedn 0) args' ->
    closed (cofix_app_target mfix0 d0 n args').
  Proof using Type.
    intros clf hnth hl cla. rewrite /cofix_app_target closedn_wrap_lazy.
    apply closed_beta_apps => //.
    pose proof (cunfold_fix_wrap_def _ _ _ hnth hl) as hc.
    eapply closed_cunfold_fix in hc; tea.
    now rewrite closedn_wrap_lazy in hc.
  Qed.

  Lemma closed_cofix_block mfix mfix0 k :
    All2 (def_rel (fun t t' => forall k, closedn k t -> closedn k t'))
      mfix mfix0 ->
    forallb (test_def (closedn (#|mfix| + k))) mfix ->
    forallb (test_def (closedn (#|map wrap_def mfix0| + k)))
      (map wrap_def mfix0).
  Proof using Type.
    intros a. rewrite length_map -(All2_length a) forallb_map.
    generalize (#|mfix| + k). clear k.
    induction a; cbn; auto.
    intros k => /andP[] hx hl. rewrite IHa // andb_true_r.
    destruct r as [_ _ _ hr]. rewrite /test_def /= closedn_wrap_lazy.
    now apply hr.
  Qed.

  Lemma closed_crel t t' : t ≈ t' -> forall k, closedn k t -> closedn k t'.
  Proof using Type.
    revert t t'. apply: crel_rect => /=.
    all:try solve [intros; rtoProp; intuition eauto; solve_all].
    - intros. eapply closed_upwards; tea. lia.
    - intros * hc r IH a IHa k => /andP[] cld clbrs.
      rewrite IH //=. solve_all. destruct y; cbn in *; subst; eauto.
    - intros * hc r IH a IHa k => /andP[] cld clbrs.
      rewrite IH //=. solve_all. destruct y; cbn in *; subst; eauto.
    - intros mfix mfix' idx a IHa k. rewrite -(All2_length a).
      generalize (#|mfix| + k). clear -IHa.
      induction IHa; cbn; auto.
      intros n => /andP[] hx hl. rewrite IHIHa // andb_true_r.
      destruct r as [_ _ hr]. now apply hr.
    - intros mfix mfix' idx a IHa k. now apply closed_cofix_block.
    - intros t t' _ [mfix mfix0 idx d0 args args' -> -> hd hnth hne hlen
        clf cla va va' ha] k hk.
      eapply (closed_upwards (k := 0)); [|lia].
      eapply closed_cofix_app_target; tea.
      + cbn. eapply (closed_cofix_block _ _ 0); tea.
      + eapply All2_nth_error_Some_r in hd as [d [hnth' []]]; tea.
      + solve_all.
    - intros * a []; cbn; auto.
      intros k => /andP[] hd ha. rewrite /test_array_model.
      rtoProp. split; eauto. solve_all.
  Qed.

  Lemma cofix_app_rel_closed t t' :
    cofix_app_rel Σ Σ' crel t t' -> closed t /\ closed t'.
  Proof using Type.
    intros hr.
    assert (closed t).
    { destruct hr; subst. rewrite closedn_mkApps. now apply/andP. }
    split => //. eapply closed_crel; tea. now constructor.
  Qed.

  Lemma crel_csubst a a' :
    a ≈ a' -> closed a -> closed a' ->
    forall t t', t ≈ t' ->
    forall k, csubst a k t ≈ csubst a' k t'.
  Proof using Type.
    intros ha cla cla'. apply: crel_rect => /=.
    all:try solve [intros; constructor; auto].
    - intros i k. destruct (k ?= i) => //; constructor.
    - intros. constructor. solve_all.
    - intros. constructor => //. solve_all.
    - intros. constructor => //. solve_all.
    - intros ind c args t' args' hc clargs clt' ev a0 IH k.
      rewrite (csubst_closed _ _ t').
      { eapply (closed_upwards (k := 0)); tea; lia. }
      assert (map (csubst a k) args = args) as ->.
      { solve_all. apply csubst_closed.
        eapply (closed_upwards (k := 0)); tea; lia. }
      eapply crel_construct_eval; tea.
    - intros. constructor; auto. solve_all.
      destruct y; cbn in *; subst; eauto.
    - intros. eapply crel_case_force; auto. solve_all.
      destruct y; cbn in *; subst; eauto.
    - intros mfix mfix' idx a0 IH k. constructor.
      rewrite -(All2_length a0). solve_all.
      destruct b as [? ? hb]. split; cbn; auto.
    - intros mfix mfix0 idx a0 IH k.
      assert (map (map_def (csubst a' (#|map wrap_def mfix0| + k)))
        (map wrap_def mfix0) =
        map wrap_def (map (map_def (csubst a' (#|mfix0| + k))) mfix0)) as ->.
      { rewrite length_map !map_map.
        eapply (All2_All_right
          (Q := fun d0 => isLambdas (rarg d0) (dbody d0))) in a0;
          [|now intros x y []].
        solve_all. now apply wrap_def_csubst. }
      constructor. rewrite -(All2_length a0). solve_all.
      destruct b as [? ? ? hb]. split; cbn; auto.
      now apply isLambdas_csubst.
    - intros t t' hr _ k.
      destruct (cofix_app_rel_closed _ _ hr) as [clt clt'].
      rewrite !csubst_closed.
      1-2:eapply (closed_upwards (k := 0)); tea; lia.
      now constructor.
    - intros p p' hp []; intros k; cbn; apply crel_prim; constructor;
        cbn; auto.
      solve_all.
  Qed.

  Lemma crel_substl s s' :
    All2 crel s s' -> forallb (closedn 0) s -> forallb (closedn 0) s' ->
    forall t t', t ≈ t' -> substl s t ≈ substl s' t'.
  Proof using Type.
    induction 1; cbn; auto.
    move=> /andP[] clx cll /andP[] cly cll' t t' h.
    apply IHX => //. now apply crel_csubst.
  Qed.

  Lemma crel_mkApps f f' args args' :
    f ≈ f' -> All2 crel args args' ->
    mkApps f args ≈ mkApps f' args'.
  Proof using Type.
    intros hf ha; induction ha in f, f', hf |- *; cbn; auto.
    apply IHha. now constructor.
  Qed.

  Lemma crel_iota_red pars args args' br br' :
    All2 crel args args' ->
    forallb (closedn 0) args -> forallb (closedn 0) args' ->
    br.2 ≈ br'.2 ->
    iota_red pars args br ≈ iota_red pars args' br'.
  Proof using Type.
    intros ha cl cl' hbr. rewrite /iota_red. apply crel_substl => //.
    - now apply All2_rev, All2_skipn.
    - now rewrite forallb_rev forallb_skipn.
    - now rewrite forallb_rev forallb_skipn.
  Qed.

  Lemma crel_fix_subst mfix mfix' :
    All2 (fun d d' => [× dname d = dname d', rarg d = rarg d' &
      dbody d ≈ dbody d']) mfix mfix' ->
    All2 crel (fix_subst mfix) (fix_subst mfix').
  Proof using Type.
    intros a. rewrite /fix_subst -(All2_length a).
    induction #|mfix|; constructor; auto. now constructor.
  Qed.

  Lemma crel_cofix_subst mfix mfix0 :
    All2 (def_rel crel) mfix mfix0 ->
    All2 crel (cofix_subst mfix) (fix_subst (map wrap_def mfix0)).
  Proof using Type.
    intros a. rewrite /fix_subst /cofix_subst length_map -(All2_length a).
    induction #|mfix|; constructor; auto. now constructor.
  Qed.

  Lemma crel_cunfold_fix mfix mfix' idx narg fn :
    All2 (fun d d' => [× dname d = dname d', rarg d = rarg d' &
      dbody d ≈ dbody d']) mfix mfix' ->
    closed (tFix mfix idx) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    ∑ fn', cunfold_fix mfix' idx = Some (narg, fn') × fn ≈ fn'.
  Proof using Type.
    intros a cl. rewrite /cunfold_fix.
    destruct nth_error eqn:hnth => //. intros [= <- <-].
    eapply All2_nth_error_Some in a as hd; tea.
    destruct hd as [d' [-> [_ -> hb]]].
    eexists; split; [reflexivity|].
    apply crel_substl => //.
    - now apply crel_fix_subst.
    - now apply closed_fix_subst.
    - apply closed_fix_subst.
      apply (closed_crel _ _ (crel_fix _ _ _ _ idx a) 0 cl).
  Qed.

  (** The fixpoint body without its thunk is related to the unfolding of
      the cofixpoint. *)
  Lemma crel_cunfold_cofix mfix mfix0 idx narg fn :
    All2 (def_rel crel) mfix mfix0 ->
    closed (tCoFix mfix idx) ->
    cunfold_cofix mfix idx = Some (narg, fn) ->
    ∑ d0, [× nth_error mfix0 idx = Some d0, rarg d0 = narg,
      isLambdas (rarg d0) (dbody d0) &
      fn ≈ substl (fix_subst (map wrap_def mfix0)) (dbody d0)].
  Proof using Type.
    intros a cl. rewrite /cunfold_cofix.
    destruct nth_error eqn:hnth => //. intros [= <- <-].
    eapply All2_nth_error_Some in a as hd; tea.
    destruct hd as [d' [hnth' [_ e hl hb]]].
    exists d'; split => //.
    apply crel_substl => //.
    - now apply crel_cofix_subst.
    - now apply closed_cofix_subst.
    - apply closed_fix_subst.
      apply (closed_crel _ _ (crel_cofix _ _ _ _ idx a) 0 cl).
  Qed.

  Fixpoint hd_cofix (t : term) : bool :=
    match t with
    | tApp f _ => hd_cofix f
    | tCoFix _ _ => true
    | _ => false
    end.

  Lemma hd_cofix_mkApps f l : hd_cofix (mkApps f l) = hd_cofix f.
  Proof using Type.
    induction l in f |- *; cbn; auto. now rewrite IHl.
  Qed.

  Lemma hd_cofix_wrap_lazy n t : hd_cofix (wrap_lazy n t) = false.
  Proof using Type. destruct n, t => //. Qed.

  Lemma crel_hd_cofix t t' : t ≈ t' -> hd_cofix t' = false.
  Proof using Type.
    revert t t'. apply: crel_rect => /=; auto.
    intros t t' [] _; subst. apply hd_cofix_wrap_lazy.
  Qed.

End RelFacts.

(** ** Generic evaluation lemmas *)

Section EvalFacts.
  Context {wfl : WcbvFlags} (Σ : global_declarations).
  Import ECSubst.

  Lemma eval_lambda_inv na b v : Σ ⊢ tLambda na b ⇓ v -> v = tLambda na b.
  Proof using Type.
    intros ev. eapply eval_deterministic; tea. now constructor.
  Qed.

  Lemma atom_wrap_lazy n t : isLambdas n t -> atom Σ (wrap_lazy n t).
  Proof using Type. destruct n, t => //. Qed.


  Lemma eval_mkApps_beta_apps_inv t vs v :
    All (value Σ) vs -> isLambdas #|vs| t ->
    Σ ⊢ mkApps t vs ⇓ v -> Σ ⊢ beta_apps t vs ⇓ v.
  Proof using Type.
    revert v; induction vs using rev_ind; intros v; cbn; auto.
    intros hv hl. rewrite beta_apps_app mkApps_app /=.
    eapply All_app in hv as [hvs hx]. depelim hx.
    rewrite length_app /= in hl.
    pose proof (isLambdas_beta_apps _ _ vs hl ltac:(lia)) as hl'.
    replace (#|vs| + 1 - #|vs|) with 1 in hl' by lia.
    destruct (isLambdas_S_inv _ _ hl') as [na [b [eq _]]].
    rewrite eq /=. intros ev.
    assert (hX : forall X, Σ ⊢ mkApps t vs ⇓ X -> X = tLambda na b).
    { intros X evX. eapply IHvs in evX; tea.
      - rewrite eq in evX. now eapply eval_lambda_inv in evX.
      - eapply isLambdas_le; tea. lia. }
    depelim ev;
      try match goal with
      | H : _ ⊢ mkApps t vs ⇓ _ |- _ => apply hX in H
      end; try solve_discr; try discriminate.
    noconf ev1. eapply eval_value in ev2; tea. now subst.
  Qed.

  Lemma eval_tForce_value t w v :
    Σ ⊢ t ⇓ w -> Σ ⊢ tForce w ⇓ v -> Σ ⊢ tForce t ⇓ v.
  Proof using Type.
    intros ev evf.
    eapply eval_tForce_inv in evf
      as [[b [evw evb]]|[mfix [idx [narg [b [evw hc evb]]]]]].
    - eapply eval_force; tea. eapply eval_trans; tea.
    - eapply eval_force_fix; tea. eapply eval_trans; tea.
  Qed.

  Lemma eval_case_discr ip d1 d2 brs r :
    (forall X, Σ ⊢ d1 ⇓ X -> Σ ⊢ d2 ⇓ X) ->
    Σ ⊢ tCase ip d1 brs ⇓ r -> Σ ⊢ tCase ip d2 brs ⇓ r.
  Proof using Type.
    intros H ev; depelim ev.
    - eapply eval_iota; eauto.
    - eapply eval_iota_block; eauto.
    - eapply eval_iota_sing; eauto.
    - eapply eval_cofix_case; eauto.
    - now cbn in i.
  Qed.

  Lemma eval_proj_discr p d1 d2 r :
    (forall X, Σ ⊢ d1 ⇓ X -> Σ ⊢ d2 ⇓ X) ->
    Σ ⊢ tProj p d1 ⇓ r -> Σ ⊢ tProj p d2 ⇓ r.
  Proof using Type.
    intros H ev; depelim ev.
    - eapply eval_cofix_proj; eauto.
    - eapply eval_proj; eauto.
    - eapply eval_proj_block; eauto.
    - eapply eval_proj_prop; eauto.
    - now cbn in i.
  Qed.

  Lemma eval_case_lambda ip na b brs r :
    Σ ⊢ tCase ip (tLambda na b) brs ⇓ r -> False.
  Proof using Type.
    intros ev; depelim ev;
      try match goal with
      | H : _ ⊢ tLambda _ _ ⇓ _ |- _ => apply eval_lambda_inv in H
      end; try solve_discr; try discriminate.
  Qed.

  Lemma eval_proj_lambda p na b r :
    Σ ⊢ tProj p (tLambda na b) ⇓ r -> False.
  Proof using Type.
    intros ev; depelim ev;
      try match goal with
      | H : _ ⊢ tLambda _ _ ⇓ _ |- _ => apply eval_lambda_inv in H
      end; try solve_discr; try discriminate.
  Qed.

  Lemma eval_wrap_lazy_beta m G f a av :
    isLambdas (S m) G -> Σ ⊢ f ⇓ wrap_lazy (S m) G -> Σ ⊢ a ⇓ av ->
    Σ ⊢ tApp f a ⇓ wrap_lazy m (beta_apps G [av]).
  Proof using Type.
    intros hl evf eva.
    destruct (isLambdas_S_inv _ _ hl) as [na [b [-> hb]]]. cbn in *.
    eapply eval_beta; tea. rewrite wrap_lazy_csubst //.
    apply eval_atom, atom_wrap_lazy. now apply isLambdas_csubst.
  Qed.

  Lemma value_app_hd_cofix f a :
    with_constructor_as_block = true -> with_guarded_fix = false ->
    value Σ (tApp f a) -> hd_cofix (tApp f a).
  Proof using Type.
    intros wcon wgf hv.
    destruct (decompose_app (tApp f a)) as [h l] eqn:da.
    pose proof (decompose_app_notApp _ _ _ da) as hna.
    apply decompose_app_inv in da. rewrite da in hv |- *.
    rewrite hd_cofix_mkApps.
    apply value_mkApps_inv in hv => //.
    destruct hv as [[[-> _]|[-> _]]|[hnil vh hall]].
    - cbn in da. subst h. discriminate.
    - cbn in da. subst h. discriminate.
    - destruct vh => //.
      + congruence.
      + now rewrite wgf in y.
  Qed.

End EvalFacts.

(** ** Related values *)

Section RelValues.
  Context {wfl : WcbvFlags}.
  Context (Σ Σ' : global_declarations).
  Context (wcon : with_constructor_as_block = true).
  Context (wgf : with_guarded_fix = false).
  Notation crel := (crel Σ Σ').
  Notation "t ≈ t'" := (crel t t') (at level 70) : coind_scope.
  Notation is_coind := (EGlobalEnv.is_coind Σ).
  Import ECSubst.

  Lemma cofix_app_rel_inv mfix idx args w' :
    cofix_app_rel Σ Σ' crel (mkApps (tCoFix mfix idx) args) w' ->
    ∑ mfix0 d0 args',
      [× w' = cofix_app_target mfix0 d0 #|args| args',
         All2 (def_rel crel) mfix mfix0,
         nth_error mfix0 idx = Some d0,
         args <> [],
         #|args| <= rarg d0,
         closed (tCoFix mfix idx),
         forallb (closedn 0) args,
         All (value Σ) args,
         All (value Σ') args' &
         All2 crel args args'].
  Proof using Type.
    intros [mfix1 mfix0 idx1 d0 args1 args' eq -> hd hnth hne hlen
      clf cla va va' ha].
    apply mkApps_eq_inj in eq as [[= <- <-] <-] => //.
    exists mfix0, d0, args'. split => //.
  Qed.

  (** A target value related to an applied cofixpoint is either the
      translated fixpoint or the result of its application. *)
  Lemma crel_cofix_app_inv mfix idx args w' :
    mkApps (tCoFix mfix idx) args ≈ w' -> value Σ' w' ->
    (args = [] × ∑ mfix0, All2 (def_rel crel) mfix mfix0 ×
      w' = tFix (map wrap_def mfix0) idx) +
    cofix_app_rel Σ Σ' crel (mkApps (tCoFix mfix idx) args) w'.
  Proof using wcon wgf.
    destruct args using rev_case.
    - cbn. intros h _. depelim h.
      + left. split => //. now eexists.
      + now right.
    - rewrite mkApps_app /=. intros h hv. depelim h.
      + exfalso. eapply value_app_hd_cofix in hv; tea.
        cbn in hv. apply crel_hd_cofix in h1. congruence.
      + now right.
  Qed.

  Lemma cofix_app_rel_value t t' :
    cofix_app_rel Σ Σ' crel t t' -> value Σ t × atom Σ' t'.
  Proof using Type.
    intros [mfix mfix0 idx d0 args args' -> -> hd hnth hne hlen
      clf cla va va' ha].
    eapply All2_nth_error_Some_r in hd as hd'; tea.
    destruct hd' as [d [hnth' [_ hr hl _]]].
    split.
    - apply value_app => //.
      eapply (value_head_cofix _ _ _ _ (rarg d)).
      + now rewrite /cofix_arity hnth'.
      + lia.
    - apply atom_wrap_lazy.
      rewrite (All2_length ha). apply isLambdas_beta_apps.
      + now apply isLambdas_substl.
      + rewrite -(All2_length ha). lia.
  Qed.

  Lemma cofix_app_rel_eval t t' v :
    cofix_app_rel Σ Σ' crel t t' -> Σ ⊢ t ⇓ v ->
    ∑ v', Σ' ⊢ t' ⇓ v' × v ≈ v'.
  Proof using Type.
    intros hr ev. destruct (cofix_app_rel_value _ _ hr) as [hv hat].
    eapply eval_value in ev; tea. subst v.
    exists t'; split; [now apply eval_atom|now constructor].
  Qed.

  (** Applying a cofixpoint value to one more argument, below its arity *)
  Lemma cofix_app_step mfix idx args a narg f' a' fv' av' :
    mkApps (tCoFix mfix idx) args ≈ fv' ->
    Σ' ⊢ f' ⇓ fv' ->
    a ≈ av' -> Σ' ⊢ a' ⇓ av' ->
    cofix_arity mfix idx = Some narg -> #|args| < narg ->
    closed (tCoFix mfix idx) -> forallb (closedn 0) args -> closed a ->
    All (value Σ) args -> value Σ a ->
    ∑ v', Σ' ⊢ tApp f' a' ⇓ v' ×
      mkApps (tCoFix mfix idx) (args ++ [a]) ≈ v'.
  Proof using wcon wgf.
    intros hr evf ha eva hcof hlt clf cla cla' vargs va.
    pose proof (eval_to_value _ _ evf) as vfv.
    pose proof (eval_to_value _ _ eva) as vav.
    move: hcof. rewrite /cofix_arity.
    destruct (nth_error mfix idx) as [d|] eqn:hnth => //=. intros [= <-].
    destruct (crel_cofix_app_inv _ _ _ _ hr vfv)
      as [[-> [mfix0 [hd ->]]]|hrel].
    - eapply All2_nth_error_Some in hd as hd'; tea.
      destruct hd' as [d0 [hnth0 [_ hrarg hlam hbody]]].
      exists (cofix_app_target mfix0 d0 1 [av']). split.
      + eapply eval_fix'; tea.
        { now apply cunfold_fix_wrap_def. }
        cbn in hlt. rewrite /cofix_app_target.
        destruct (rarg d0) as [|m] eqn:hm; [lia|].
        replace (S m - 1) with m by lia.
        apply eval_wrap_lazy_beta.
        * rewrite -hm. now apply isLambdas_substl.
        * apply eval_atom, atom_wrap_lazy.
          rewrite -hm. now apply isLambdas_substl.
        * now apply value_final.
      + apply crel_cofix_app.
        eapply (cofix_app_intro _ _ _ _ _ mfix mfix0 idx d0 [a] [av']);
          tea; cbn; auto; try congruence.
        cbn in hlt. lia.
    - eapply cofix_app_rel_inv in hrel
        as [mfix0 [d0 [args' [-> hd hnth0 hne hlen _ _ _ va' ha']]]].
      eapply All2_nth_error in hd as hd'; tea.
      destruct hd' as [_ hrarg hlam hbody].
      exists (cofix_app_target mfix0 d0 (S #|args|) (args' ++ [av'])). split.
      + rewrite /cofix_app_target beta_apps_app.
        set (F := substl _ _).
        pose proof (isLambdas_beta_apps (rarg d0) F args') as hl.
        forward hl. { now apply isLambdas_substl. }
        forward hl. { rewrite -(All2_length ha'). lia. }
        rewrite -(All2_length ha') in hl.
        destruct (rarg d0 - #|args|) as [|m] eqn:hm; [lia|].
        replace (rarg d0 - S #|args|) with m by lia.
        rewrite /cofix_app_target -/F hm in evf.
        now apply eval_wrap_lazy_beta.
      + apply crel_cofix_app.
        eapply (cofix_app_intro _ _ _ _ _ mfix mfix0 idx d0
          (args ++ [a]) (args' ++ [av'])); tea;
          rewrite ?length_app ?forallb_app /= ?Nat.add_1_r ?cla ?cla' //;
          try lia; try (now destruct args);
          try (eapply All_app_inv => //; now constructor);
          try (eapply All2_app => //; now constructor).
  Qed.

  (** Related target terms of a cofixpoint applied to values evaluate *)
  Lemma crel_cofix_apps_eval mfix idx narg args :
    cofix_arity mfix idx = Some narg -> #|args| <= narg ->
    closed (tCoFix mfix idx) -> forallb (closedn 0) args ->
    All (value Σ) args ->
    All (fun a => forall t', a ≈ t' ->
      ∑ v', Σ' ⊢ t' ⇓ v' × a ≈ v') args ->
    forall t', mkApps (tCoFix mfix idx) args ≈ t' ->
    ∑ v', Σ' ⊢ t' ⇓ v' × mkApps (tCoFix mfix idx) args ≈ v'.
  Proof using wcon wgf.
    intros hcof.
    induction args using rev_ind; intros hlen clf cla va IH t'.
    - cbn. intros h. depelim h.
      + eexists; split; [now apply eval_atom|now constructor].
      + apply cofix_app_rel_isApp in c. discriminate.
    - rewrite mkApps_app /=. intros h.
      rewrite length_app /= in hlen.
      rewrite forallb_app /= andb_true_r in cla.
      move/andP: cla => [] cla clx.
      eapply All_app in va as [va vx]. depelim vx.
      eapply All_app in IH as [IH IHx]. depelim IHx.
      depelim h.
      + destruct (IHargs ltac:(lia) clf cla va IH _ h1) as [fv' [evf hf]].
        destruct (s _ h2) as [av' [eva hav]].
        destruct (cofix_app_step _ _ _ _ _ _ _ _ _ hf evf hav eva hcof
          ltac:(lia) clf cla clx va v) as [v' [ev' hv']].
        exists v'. split => //. now rewrite mkApps_app in hv'.
      + destruct (cofix_app_rel_value _ _ c) as [_ hat].
        exists t'; split; [now apply eval_atom|now constructor].
  Qed.

  (** Constructors are declared in the target, with the same arity *)
  Context (Hcstr : forall ind c mdecl idecl cdecl,
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    ∑ mdecl', lookup_constructor Σ' ind c = Some (mdecl', idecl, cdecl) ×
      cstr_arity mdecl' cdecl = cstr_arity mdecl cdecl).

  Lemma crel_values_eval args args' :
    All (fun a => closed a -> forall t', a ≈ t' ->
      ∑ v', Σ' ⊢ t' ⇓ v' × a ≈ v') args ->
    forallb (closedn 0) args ->
    All2 crel args args' ->
    ∑ vs', All2 (eval Σ') args' vs' × All2 crel args vs'.
  Proof using Type.
    intros IH cl a. induction a in IH, cl |- *.
    - exists []. split; constructor.
    - depelim IH. move/andP: cl => [] clx cll.
      destruct (s clx _ r) as [v' [ev hv]].
      destruct (IHa IH cll) as [vs' [evs hvs]].
      exists (v' :: vs'). split; constructor; auto.
  Qed.

  (** Catching up: a target term related to a source value evaluates to a
      related value. *)
  Lemma crel_value_eval v :
    value Σ v -> closed v -> forall t', v ≈ t' ->
    ∑ v', Σ' ⊢ t' ⇓ v' × v ≈ v'.
  Proof using wcon wgf Hcstr.
    revert v. apply: value_values_ind.
    - intros t hat clt t' h.
      destruct t => //; depelim h;
        try (apply cofix_app_rel_isApp in c; discriminate).
      all:try solve [eexists; split; [now apply eval_atom|now constructor]].
      all:cbn in hat; rewrite wcon in hat; destruct args => //.
    - intros p pv IH clp t' h. depelim h.
      2:{ apply cofix_app_rel_isApp in c. discriminate. }
      match goal with H : prim_rel _ _ _ |- _ => rename H into hp end.
      depelim hp; depelim pv; depelim IH.
      1-3:eexists; split; [eapply eval_prim; constructor|
        apply crel_prim; constructor].
      cbn in clp. move/andP: clp => [] cld clv.
      destruct (crel_values_eval _ _ a2 clv a0) as [vs' [evs hvs]].
      destruct (s cld _ c) as [d' [evd hd]].
      exists (tPrim (prim_array
        {| array_default := d'; array_value := vs' |})).
      split.
      + eapply eval_prim.
        destruct a'; cbn in *.
        eapply (evalPrimArray (eval Σ') _ _ vs' d'); tea.
        now apply All2_All2_Set.
      + apply crel_prim. constructor; cbn; auto.
    - intros ind c mdecl idecl cdecl args e hl hlen va IH cl t' h.
      cbn in cl. depelim h.
      + destruct (crel_values_eval _ _ IH cl a) as [vs' [evs hvs]].
        destruct (Hcstr _ _ _ _ _ hl) as [mdecl' [hl' har]].
        exists (tConstruct ind c vs'). split.
        * eapply eval_construct_block; [tea|exact hl'| |].
          { now rewrite har -(All2_length a). }
          now apply All2_All2_Set.
        * now constructor.
      + eexists; split; [now apply eval_atom|].
        now eapply crel_construct_lazy.
      + eexists; split; [now apply eval_atom|].
        now eapply crel_construct_eval.
      + apply cofix_app_rel_isApp in c0. discriminate.
    - intros f args vh hne va IH cl t' h.
      rewrite closedn_mkApps in cl. move/andP: cl => [] clf cla.
      destruct vh.
      + congruence.
      + eapply crel_cofix_apps_eval; tea. solve_all.
      + now rewrite wgf in y.
  Qed.

End RelValues.

(** ** The translation is in the relation *)

Section TransRel.
  Context {efl : EEnvFlags} {wfl : WcbvFlags} (Σ : GlobalContextMap.t).
  Notation "t ≈ t'" := (crel Σ (trans_env Σ) t t') (at level 70) : coind_scope.

  Lemma crel_trans k t : wellformed Σ k t -> t ≈ trans Σ t.
  Proof using Type.
    induction t in k |- * using EInduction.term_forall_list_ind;
      cbn -[lookup_constructor lookup_constructor_pars_args
        lookup_projection];
      intros wf; rtoProp; intuition eauto; try solve [constructor; eauto].
    - constructor. solve_all.
    - assert (ha : All2 (crel Σ (trans_env Σ)) args (map (trans Σ) args)).
      { destruct cstr_as_blocks; rtoProp; [solve_all|].
        destruct args => //. }
      rewrite GlobalContextMap.is_coind_spec.
      destruct EGlobalEnv.is_coind eqn:hc;
        solve [now eapply crel_construct|now eapply crel_construct_lazy].
    - assert (hb : All2 (fun br br' => (br.1 = br'.1) ×
        crel Σ (trans_env Σ) br.2 br'.2) l (map (on_snd (trans Σ)) l)).
      { solve_all. eapply All_All2; tea. cbn. intros x []; split; eauto. }
      rewrite GlobalContextMap.is_coind_spec.
      destruct EGlobalEnv.is_coind eqn:hc;
        solve [eapply crel_case; eauto|eapply crel_case_force; eauto].
    - rewrite GlobalContextMap.is_coind_spec.
      destruct EGlobalEnv.is_coind eqn:hc;
        solve [eapply crel_proj; eauto|eapply crel_proj_force; eauto].
    - move/andP: H0 => [] _ hb. constructor. solve_all.
      eapply All_All2; tea. cbn. intros x [? []]; split; eauto.
    - move/andP: H0 => [] _ hb. constructor. solve_all.
      eapply All_All2; tea. cbn. intros x [? []]; split; cbn; eauto.
      now apply isLambdas_trans.
    - constructor. solve_all.
      depelim H1; cbn; try constructor; cbn.
      all:destruct p as [[] ?]; cbn in *; eauto.
      solve_all.
  Qed.

End TransRel.

(** ** First-order values

  Values built only from constructors of inductive (not coinductive) types
  ([EFirstorder.firstorder_ind_value]) are related to themselves only: the
  translation preserves the observation of such values. *)

Section FirstOrder.
  Context {wfl : WcbvFlags} (Σ Σ' : global_declarations).

  Notation "t ≈ t'" := (crel Σ Σ' t t') (at level 70) : coind_scope.

  Lemma crel_firstorder_ind_value v :
    firstorder_ind_value Σ v -> forall v', v ≈ v' -> v' = v.
  Proof using Type.
    revert v. apply: firstorder_ind_value_rect.
    intros ind c args hco hargs IH v' h. depelim h.
    - f_equal. clear -IH a. induction a; depelim IH; f_equal; eauto.
    - congruence.
    - congruence.
    - apply cofix_app_rel_isApp in c0. discriminate.
  Qed.
End FirstOrder.

(** ** Correctness of the translation *)

From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksInd.

Ltac destruct_times :=
  match goal with
  | [ H : pair _ _ |- _ ] => destruct H
  | [ H : MRProd.and3 _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and4 _ _ _ _ |- _ ] => destruct H
  | [ H : MRProd.and5 _ _ _ _ _ |- _ ] => destruct H
  end.

Section Correctness.
  Context {efl : EEnvFlags} {wfl : WcbvFlags} (Σ : GlobalContextMap.t).
  Context (wcon : with_constructor_as_block = true).
  Context (wcb : cstr_as_blocks = true).
  Context (wpc : with_prop_case = false).
  Context (wgf : with_guarded_fix = false).
  Context (hasapp : has_tApp) (wfΣ : wf_glob Σ).
  Notation Σ' := (trans_env Σ).
  Notation "t ≈ t'" := (crel Σ Σ' t t') (at level 70) : coind_scope.

  Lemma lookup_constructor_trans_env ind c mdecl idecl cdecl :
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    ∑ mdecl', lookup_constructor Σ' ind c = Some (mdecl', idecl, cdecl) ×
      cstr_arity mdecl' cdecl = cstr_arity mdecl cdecl.
  Proof using wfΣ.
    intros hl. rewrite lookup_constructor_trans // hl /=.
    eexists; split; reflexivity.
  Qed.

  (** Forcing the target value related to an evaluated coinductive
      constructor gives a block of related values. *)
  Lemma crel_force_construct ind c mdecl idecl cdecl vs w' :
    is_coind Σ (inductive_mind ind) ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    #|vs| = cstr_arity mdecl cdecl ->
    All (value Σ) vs -> forallb (closedn 0) vs ->
    tConstruct ind c vs ≈ w' ->
    ∑ vs', All2 (crel Σ Σ') vs vs' ×
      forall t', Σ' ⊢ t' ⇓ w' -> Σ' ⊢ tForce t' ⇓ tConstruct ind c vs'.
  Proof using wcon wgf wfΣ.
    intros hco hl hlen hv hcl h. depelim h.
    - now rewrite e in hco.
    - destruct (crel_values_eval Σ Σ' vs args') as [vs' [evs hvs]]; tea.
      { solve_all. eapply crel_value_eval; tea.
        apply lookup_constructor_trans_env. }
      exists vs'. split => //. intros t' ev.
      eapply eval_force; tea.
      destruct (lookup_constructor_trans_env _ _ _ _ _ hl)
        as [mdecl' [hl' har]].
      eapply eval_construct_block; [tea|exact hl'| |].
      + now rewrite har -(All2_length a).
      + now apply All2_All2_Set.
    - exists args'. split => //. intros t0 ev.
      eapply eval_force; tea.
    - apply cofix_app_rel_isApp in c0. discriminate.
  Qed.

  (** A cofixpoint whose unfolding does not evaluate to an abstraction is
      applied to as many arguments as its arity. *)
  Lemma cofix_forced_saturated mfix idx narg fn args bv :
    wellformed Σ 0 (mkApps (tCoFix mfix idx) args) ->
    value Σ (mkApps (tCoFix mfix idx) args) ->
    cunfold_cofix mfix idx = Some (narg, fn) ->
    Σ ⊢ mkApps fn args ⇓ bv -> ~~ isLambda bv -> #|args| = narg.
  Proof using hasapp.
    intros wf hv hunf ev hnl.
    pose proof (cunfold_cofix_arity _ _ _ _ hunf) as har.
    destruct (cofix_value_args _ _ _ _ _ hv har) as [hvs hle].
    destruct (Nat.eq_dec #|args| narg) => //. exfalso.
    assert (hl : isLambdas narg fn).
    { move: wf; rewrite wellformed_mkApps // => /andP[] wfc _.
      move: wfc => /= /andP[] /andP[] _ hlam _.
      move: hunf; rewrite /cunfold_cofix.
      destruct nth_error eqn:hnth => //. intros [= <- <-].
      apply isLambdas_substl.
      eapply forallb_nth_error in hlam. erewrite hnth in hlam. exact hlam. }
    eapply eval_mkApps_beta_apps_inv in ev; tea.
    2:{ eapply isLambdas_le; tea. }
    pose proof (isLambdas_beta_apps narg fn args hl ltac:(lia)) as hl'.
    destruct (narg - #|args|) eqn:hd; [lia|].
    destruct (isLambdas_S_inv _ _ hl') as [na [b [eq _]]]. rewrite eq in ev.
    eapply eval_lambda_inv in ev. subst bv. discriminate.
  Qed.

  (** Forcing a saturated cofixpoint value. The value [bv] of its unfolding
      is related to some [bv'], and forcing a term which evaluates to the
      target value [w'] of the cofixpoint behaves as forcing [bv']:
      - a nullary cofixpoint is a recursive lazy value, forced by
        [eval_force_fix];
      - an applied one is the thunk of the forced unfolded body. *)
  Lemma cofix_force mfix idx narg fn args w' bv :
    wellformed Σ 0 (mkApps (tCoFix mfix idx) args) ->
    cunfold_cofix mfix idx = Some (narg, fn) -> #|args| = narg ->
    mkApps (tCoFix mfix idx) args ≈ w' -> value Σ' w' ->
    (forall t', mkApps fn args ≈ t' -> ∑ v', Σ' ⊢ t' ⇓ v' × bv ≈ v') ->
    ∑ bv', bv ≈ bv' ×
      forall t' X, Σ' ⊢ t' ⇓ w' -> Σ' ⊢ tForce bv' ⇓ X ->
        Σ' ⊢ tForce t' ⇓ X.
  Proof using wcon wgf hasapp.
    intros wf hunf hsat hr hv IH.
    move: (wf); rewrite wellformed_mkApps // => /andP[] wfc wfargs.
    have clf : closed (tCoFix mfix idx) by now eapply wellformed_closed.
    destruct (crel_cofix_app_inv _ _ wcon wgf _ _ _ _ hr hv)
      as [[-> [mfix0 [hd ->]]]|hrel].
    - destruct (crel_cunfold_cofix _ _ _ _ _ _ _ hd clf hunf)
        as [d0 [hnth hrarg hlam hfn]].
      destruct (IH _ hfn) as [bv' [evb hb]].
      exists bv'. split => //. intros t' X evt evf.
      set (F0 := substl _ _) in *.
      eapply (eval_force_fix _ t' (map wrap_def mfix0) idx _ (tForce F0) X
        evt).
      + rewrite (cunfold_fix_wrap_def _ _ _ hnth hlam).
        cbn in hsat. rewrite hrarg -hsat /=. reflexivity.
      + eapply eval_tForce_value; tea.
    - eapply cofix_app_rel_inv in hrel
        as [mfix0 [d0 [args' [-> hd hnth0 hne hlen _ _ va va' ha']]]].
      destruct (crel_cunfold_cofix _ _ _ _ _ _ _ hd clf hunf)
        as [d1 [hnth hrarg hlam hfn]].
      rewrite hnth0 in hnth. noconf hnth.
      set (F0 := substl _ _) in *.
      destruct (IH (mkApps F0 args')) as [bv' [evb hb]].
      { now eapply crel_mkApps. }
      exists bv'; split => //. intros t' X evt evf.
      rewrite /cofix_app_target -/F0 in evt.
      replace (rarg d0 - #|args|) with 0 in evt by lia. cbn in evt.
      eapply eval_force; tea. eapply eval_tForce_value; tea.
      eapply eval_mkApps_beta_apps_inv; tea.
      rewrite -(All2_length ha') hsat -hrarg.
      now apply isLambdas_substl.
  Qed.

  (** The translation simulates evaluation, up to the relation. *)
  Lemma trans_rel_correct t v :
    wellformed Σ 0 t -> Σ ⊢ t ⇓ v ->
    forall t', t ≈ t' -> ∑ v', Σ' ⊢ t' ⇓ v' × v ≈ v'.
  Proof using wcon wcb wpc wgf hasapp wfΣ.
    intros wf ev. revert t v wf ev.
    eapply (eval_preserve_mkApps_ind wfl wcon
      (efl:=efl) Σ
      (fun t v => forall t', t ≈ t' -> ∑ v', Σ' ⊢ t' ⇓ v' × v ≈ v')
      (wellformed Σ)
      (Qpres := Qpreserves_wellformed efl _ wfΣ))
      => //.
    all:intros; repeat destruct_times.
    - eapply eval_wellformed; tea.
    - (* Application of a box *)
      depelim X1.
      + destruct (s0 _ X1_1) as [fv' [evf hf]].
        depelim hf; [|apply cofix_app_rel_isApp in c; discriminate].
        destruct (s _ X1_2) as [av' [eva ha]].
        exists tBox; split; [eapply eval_box; tea|constructor].
      + eapply cofix_app_rel_eval; tea. eapply eval_box; tea.
    - (* Beta *)
      depelim X2.
      + destruct (s1 _ X2_1) as [fv' [evf hf]].
        depelim hf; [|apply cofix_app_rel_isApp in c; discriminate].
        destruct (s0 _ X2_2) as [av' [eva ha]].
        destruct (s (csubst av' 0 b')) as [v' [ev hv]].
        { eapply crel_csubst; tea. now eapply wellformed_closed.
          eapply closed_crel; tea; now eapply wellformed_closed. }
        exists v'; split => //. eapply eval_beta; tea.
      + eapply cofix_app_rel_eval; tea. eapply eval_beta; tea.
    - (* Let *)
      depelim X1; [|apply cofix_app_rel_isApp in c; discriminate].
      destruct (s0 _ X1_1) as [bv' [evb hb]].
      destruct (s (csubst bv' 0 c')) as [v' [ev hv]].
      { eapply crel_csubst; tea. now eapply wellformed_closed.
        eapply closed_crel; tea; now eapply wellformed_closed. }
      exists v'; split => //. eapply eval_zeta; tea.
    - (* Iota *)
      assert (hcl : forallb (closedn 0) args).
      { move: i2; cbn -[lookup_constructor_pars_args]; rewrite wcb.
        move/and3P => [] _ _ hargs. solve_all.
        now eapply wellformed_closed. }
      assert (hcont : forall d' args' brs',
        All2 (crel Σ Σ') args args' ->
        Σ' ⊢ d' ⇓ tConstruct ind c args' ->
        All2 (fun br br' => (br.1 = br'.1) × crel Σ Σ' br.2 br'.2)
          brs brs' ->
        ∑ v', Σ' ⊢ tCase (ind, pars) d' brs' ⇓ v' × crel Σ Σ' res v').
      { intros d' args' brs' hargs evd hbrs.
        eapply All2_nth_error_Some in hbrs as [br' [hnth [hn hbr]]]; tea.
        destruct (s (iota_red pars args' br')) as [v' [ev hv]].
        { eapply crel_iota_red; tea. solve_all.
          eapply closed_crel; tea. }
        exists v'; split => //.
        eapply eval_iota_block; tea.
        - now rewrite -is_propositional_cstr_trans.
        - now rewrite -(All2_length hargs).
        - rewrite -hn -H3 !length_skipn (All2_length hargs) //. }
      depelim X1.
      + destruct (s0 _ X1) as [dv' [evd hd]]. depelim hd.
        * eapply hcont; tea.
        * cbn in e. congruence.
        * cbn in e. congruence.
        * apply cofix_app_rel_isApp in c0; discriminate.
      + (* Coinductive type: the scrutinee is forced *)
        destruct (s0 _ X1) as [dv' [evd hd]].
        pose proof (eval_to_value _ _ H) as hval.
        depelim hval.
        * exfalso. depelim a0. cbn in i3. rewrite wcon in i3.
          now destruct args.
        * destruct (crel_force_construct _ _ _ _ _ _ _ e e1 e2 a0 hcl hd)
            as [vs' [hvs hforce]].
          eapply hcont; tea. now apply hforce.
        * exfalso. destruct args0 using rev_case => //.
          rewrite mkApps_app in H6. discriminate.
      + apply cofix_app_rel_isApp in c0; discriminate.
    - now rewrite wpc in H.
    - now rewrite wgf in H.
    - now rewrite wgf in H.
    - (* Unguarded fixpoint unfolding *)
      depelim X2.
      + destruct (s1 _ X2_1) as [fv' [evf hf]].
        depelim hf; [|apply cofix_app_rel_isApp in c; discriminate].
        eapply crel_cunfold_fix in H1 as [fn' [hunf hfn]]; tea;
          [|now eapply wellformed_closed].
        destruct (s0 _ X2_2) as [av' [eva ha]].
        destruct (s (tApp fn' av')) as [v' [ev hv]]. { now constructor. }
        exists v'; split => //. eapply eval_fix'; tea.
      + eapply cofix_app_rel_eval; tea. eapply eval_fix'; tea.
    - (* Cofixpoint unfolding under a match: the type is coinductive, the
         target forces its scrutinee *)
      depelim X2;
        [now rewrite e in H0| |apply cofix_app_rel_isApp in c; discriminate].
      destruct (s1 _ X2) as [w' [evd hw]].
      assert (hsat : #|args| = narg).
      { eapply cofix_forced_saturated; tea. now eapply eval_to_value in H1.
        destruct bv => //. exfalso. eapply eval_case_lambda; tea. }
      destruct (cofix_force _ _ _ _ _ _ _ i4 H hsat hw
        (eval_to_value _ _ evd) s0) as [bv' [hb hforce]].
      destruct (s (tCase ip (tForce bv') brs')) as [v' [ev hv]].
      { now eapply crel_case_force. }
      exists v'; split => //.
      eapply eval_case_discr; tea. intros X evX. eapply hforce; tea.
    - (* Cofixpoint unfolding under a projection *)
      match goal with X : crel _ _ (tProj _ _) _ |- _ => depelim X end.
      + now rewrite e in H1.
      + destruct (s1 _ X2) as [w' [evd hw]].
        assert (hsat : #|args| = narg).
        { eapply cofix_forced_saturated; tea. now eapply eval_to_value in H2.
          destruct bv => //. exfalso. eapply eval_proj_lambda; tea. }
        destruct (cofix_force _ _ _ _ _ _ _ i4 H0 hsat hw
          (eval_to_value _ _ evd) s0) as [bv' [hb hforce]].
        destruct (s (tProj p (tForce bv'))) as [v' [ev hv]].
        { now eapply crel_proj_force. }
        exists v'; split => //.
        eapply eval_proj_discr; tea. intros X evX. eapply hforce; tea.
      + apply cofix_app_rel_isApp in c; discriminate.
    - (* Cofixpoint applied below its arity *)
      match goal with X : crel _ _ (tApp _ _) _ |- _ => depelim X end.
      2:{ eapply cofix_app_rel_eval; tea. eapply eval_cofix_value; tea. }
      destruct (s0 _ X1_1) as [fv' [evf hf]].
      destruct (s _ X1_2) as [av' [eva ha]].
      move: (i2); rewrite wellformed_mkApps // => /andP[] wfc wfargs.
      pose proof (eval_to_value _ _ H) as hval.
      destruct (cofix_value_args _ _ _ _ _ hval H1) as [hvs _].
      destruct (cofix_app_step Σ Σ' wcon wgf mfix idx argsv av narg f' a'
        fv' av') as [v' [ev hv]]; tea.
      { now eapply wellformed_closed. }
      { solve_all. now eapply wellformed_closed. }
      { now eapply wellformed_closed. }
      { now eapply eval_to_value in H0. }
      exists v'; split => //. now rewrite mkApps_app in hv.
    - (* Constants *)
      match goal with X : crel _ _ (tConst _) _ |- _ => depelim X end.
      2:{ apply cofix_app_rel_isApp in c0; discriminate. }
      destruct (s (trans Σ body)) as [v' [ev hv]].
      { eapply crel_trans; tea. }
      exists v'; split => //.
      eapply (eval_delta _ _ (trans_constant_decl Σ decl)); tea.
      + red. rewrite lookup_env_trans // H /= //.
      + cbn. now rewrite H0.
    - (* Projection of a constructor *)
      match goal with X : crel _ _ (tProj _ _) _ |- _ => rename X into hr end.
      assert (hcl : forallb (closedn 0) args).
      { move: i2; cbn -[lookup_constructor_pars_args]; rewrite wcb.
        move/and3P => [] _ _ hargs. solve_all.
        now eapply wellformed_closed. }
      assert (hcont : forall d' args',
        All2 (crel Σ Σ') args args' ->
        Σ' ⊢ d' ⇓ tConstruct (proj_ind p) 0 args' ->
        ∑ v', Σ' ⊢ tProj p d' ⇓ v' × crel Σ Σ' res v').
      { intros d' args' hargs evd.
        eapply All2_nth_error_Some in hargs as hn; tea.
        destruct hn as [a' [hnth ha]].
        destruct (s _ ha) as [v' [ev hv]]. exists v'; split => //.
        eapply eval_proj_block; tea.
        - now rewrite -is_propositional_cstr_trans.
        - now rewrite -(All2_length hargs). }
      depelim hr.
      + destruct (s0 _ hr) as [dv' [evd hd]]. depelim hd.
        * eapply hcont; tea.
        * congruence.
        * congruence.
        * apply cofix_app_rel_isApp in c; discriminate.
      + destruct (s0 _ hr) as [dv' [evd hd]].
        pose proof (eval_to_value _ _ H0) as hval.
        depelim hval.
        * exfalso. depelim a0. cbn in i3. rewrite wcon in i3.
          now destruct args.
        * destruct (crel_force_construct _ _ _ _ _ _ _ e e1 e2 a0 hcl hd)
            as [vs' [hvs hforce]].
          eapply hcont; tea. now apply hforce.
        * exfalso. destruct args0 using rev_case => //.
          match goal with
            H : tConstruct _ _ _ = mkApps _ _ |- _ =>
              rewrite mkApps_app in H; discriminate
          end.
      + apply cofix_app_rel_isApp in c; discriminate.
    - match goal with
        H : is_true with_prop_case |- _ => now rewrite wpc in H
      end.
    - (* Constructor blocks *)
      match goal with
        X : crel _ _ (tConstruct _ _ _) _ |- _ => rename X into hr
      end.
      assert (hargs : forall targs, All2 (crel Σ Σ') args targs ->
        ∑ vs', All2 (eval Σ') targs vs' × All2 (crel Σ Σ') args' vs').
      { intros targs h. induction X0 in targs, h, X |- *; depelim h.
        - exists []; split; constructor.
        - depelim X. destruct r as [ih _ _].
          destruct (ih _ c) as [v' [ev hv]].
          destruct (IHX0 X _ h) as [vs' [evs hvs]].
          exists (v' :: vs'); split; constructor; auto. }
      assert (hcl : forallb (closedn 0) args × forallb (closedn 0) args').
      { split.
        - eapply All2_All_left in X0; [|intros x y [_ wfx _]; exact wfx].
          solve_all. now eapply wellformed_closed.
        - eapply All2_All_right in X0; [|intros x y [_ _ wfy]; exact wfy].
          solve_all. now eapply wellformed_closed. }
      destruct hcl as [hcl hcl'].
      depelim hr.
      + destruct (hargs _ a) as [vs' [evs hvs]].
        exists (tConstruct ind i vs'). split; [|now constructor].
        destruct (lookup_constructor_trans_env _ _ _ _ _ H)
          as [mdecl' [hl' har]].
        eapply eval_construct_block; [tea|exact hl'| |].
        * now rewrite har -(All2_length a).
        * now apply All2_All2_Set.
      + (* The thunk is a value: its body evaluates to related values *)
        destruct (hargs _ a) as [vs' [evs hvs]].
        eexists; split; [now apply eval_atom|].
        eapply crel_construct_eval; tea.
        * cbn. clear -a hcl. induction a; cbn in * => //.
          move/andP: hcl => [] cx cl. apply/andP; split; eauto.
          eapply closed_crel; tea.
        * destruct (lookup_constructor_trans_env _ _ _ _ _ H)
            as [mdecl' [hl' har]].
          eapply eval_construct_block; [tea|exact hl'| |].
          { now rewrite har -(All2_length a). }
          now apply All2_All2_Set.
      + destruct (hargs _ a) as [vs' [evs hvs]].
        pose proof (value_constructor_as_block (eval_to_value _ _ e0)) as hv.
        assert (vs' = args'0) as ->.
        { clear -evs hv. induction evs; depelim hv; f_equal; eauto.
          eapply eval_deterministic; tea. now apply value_final. }
        eexists; split; [now apply eval_atom|].
        eapply crel_construct_eval; tea.
      + apply cofix_app_rel_isApp in c; discriminate.
    - (* Primitives *)
      match goal with X : crel _ _ (tPrim _) _ |- _ => depelim X end.
      2:{ apply cofix_app_rel_isApp in c; discriminate. }
      depelim X; depelim p1.
      1-3:eexists; split; [eapply eval_prim; constructor|
        apply crel_prim; constructor].
      eapply All2_over_undep in a.
      destruct a0 as [ihd _ _]. destruct (ihd _ c) as [d' [evd hd]].
      destruct a'0 as [d0 vs0]; cbn in *.
      assert (hargs : ∑ vs', All2 (eval Σ') vs0 vs' ×
        All2 (crel Σ Σ') v' vs').
      { clear -a a3. induction a in vs0, a3 |- *; depelim a3.
        - exists []; split; constructor.
        - destruct r as [ih _ _]. destruct (ih _ c) as [w [ev hv]].
          destruct (IHa _ a3) as [vs' [evs hvs]].
          exists (w :: vs'); split; constructor; auto. }
      destruct hargs as [vs' [evs hvs]].
      exists (tPrim (prim_array
        {| array_default := d'; array_value := vs' |})). split.
      + eapply eval_prim.
        eapply (evalPrimArray (eval Σ') _ _ vs' d'); tea.
        now apply All2_All2_Set.
      + apply crel_prim. constructor; cbn; auto.
    - (* Forcing a thunk *)
      match goal with X : crel _ _ (tForce _) _ |- _ => depelim X end.
      2:{ apply cofix_app_rel_isApp in c; discriminate. }
      destruct (s0 _ X1) as [w' [evw hw]].
      depelim hw; [|apply cofix_app_rel_isApp in c; discriminate].
      destruct (s _ hw) as [v' [ev hv]].
      exists v'; split => //. eapply eval_force; tea.
    - (* Forcing a recursive lazy value *)
      match goal with X : crel _ _ (tForce _) _ |- _ => depelim X end.
      2:{ apply cofix_app_rel_isApp in c; discriminate. }
      destruct (s0 _ X1) as [w' [evw hw]].
      depelim hw; [|apply cofix_app_rel_isApp in c; discriminate].
      eapply crel_cunfold_fix in H0 as [fn' [hunf hfn]]; tea;
        [|now eapply wellformed_closed].
      depelim hfn; [|apply cofix_app_rel_isApp in c; discriminate].
      destruct (s _ hfn) as [v' [ev hv]].
      exists v'; split => //. eapply eval_force_fix; tea.
    - (* Atoms *)
      match goal with X : crel _ _ _ _ |- _ => rename X into hr end.
      eapply crel_value_eval; tea.
      + apply lookup_constructor_trans_env.
      + eapply eval_to_value, eval_atom; tea.
      + now eapply wellformed_closed.
  Qed.

  (** Correctness of the translation: the translated term evaluates to a
      value related to the source value. *)
  Theorem trans_correct t v :
    wellformed Σ 0 t -> Σ ⊢ t ⇓ v ->
    ∑ v', Σ' ⊢ trans Σ t ⇓ v' × v ≈ v'.
  Proof using wcon wcb wpc wgf hasapp wfΣ.
    intros wf ev. eapply trans_rel_correct; tea. eapply crel_trans; tea.
  Qed.

  (** First-order values of inductive types are observed unchanged. *)
  Corollary trans_correct_firstorder t v :
    wellformed Σ 0 t -> Σ ⊢ t ⇓ v -> firstorder_ind_value Σ v ->
    Σ' ⊢ trans Σ t ⇓ v.
  Proof using wcon wcb wpc wgf hasapp wfΣ.
    intros wf ev fo.
    destruct (trans_correct _ _ wf ev) as [v' [ev' hv]].
    eapply crel_firstorder_ind_value in hv; tea. now subst.
  Qed.

End Correctness.

(** ** Wellformedness of the translation

  The translated program has no cofixpoints left: it is wellformed for the
  flags where they are switched off. *)

Definition disable_cofix_term_flags (et : ETermFlags) :=
  {| has_tBox := has_tBox
    ; has_tRel := has_tRel
    ; has_tVar := has_tVar
    ; has_tEvar := has_tEvar
    ; has_tLambda := has_tLambda
    ; has_tLetIn := has_tLetIn
    ; has_tApp := has_tApp
    ; has_tConst := has_tConst
    ; has_tConstruct := has_tConstruct
    ; has_tCase := has_tCase
    ; has_tProj := has_tProj
    ; has_tFix := has_tFix
    ; has_tCoFix := false
    ; has_tPrim := has_tPrim
    ; has_tLazy_Force := has_tLazy_Force
  |}.

Definition switch_off_cofix (efl : EEnvFlags) :=
  {| has_axioms := efl.(has_axioms);
     has_cstr_params := efl.(has_cstr_params);
     term_switches := disable_cofix_term_flags efl.(term_switches);
     cstr_as_blocks := efl.(cstr_as_blocks) |}.

Lemma isLambda_wrap_lazy n t :
  isLambdas n t -> isLambda (wrap_lazy n t) || isLazy (wrap_lazy n t).
Proof. destruct n, t => //. Qed.

Lemma wellformed_wrap_lazy {efl : EEnvFlags} Σ n k t :
  has_tLazy_Force ->
  wellformed Σ k t -> wellformed Σ k (wrap_lazy n t).
Proof.
  intros hl. induction n in k, t |- *; cbn.
  - now rewrite hl.
  - destruct t; cbn; rewrite ?hl //.
    move/andP => [] -> /=. apply IHn.
Qed.

Lemma trans_wellformed {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tLazy_Force -> has_tFix ->
  @wellformed efl Σ n t ->
  @wellformed (switch_off_cofix efl) Σ n (trans Σ t).
Proof.
  intros hlf hfix.
  induction t in n |- * using EInduction.term_forall_list_ind => //.
  all:try solve [cbn -[lookup_constructor lookup_constructor_pars_args
    lookup_projection]; rtoProp; intuition auto; solve_all].
  - cbn -[lookup_constructor lookup_constructor_pars_args].
    intros wf.
    assert (wf' : @wellformed (switch_off_cofix efl) Σ n
      (tConstruct i n0 (map (trans Σ) args))).
    { move: wf; cbn -[lookup_constructor lookup_constructor_pars_args].
      rtoProp; intuition auto.
      destruct cstr_as_blocks; rtoProp; intuition auto; len; solve_all.
      now destruct args. }
    destruct GlobalContextMap.is_coind => //.
    cbn -[wellformed]. cbn. now rewrite hlf.
  - cbn -[lookup_inductive]. intros wf.
    destruct GlobalContextMap.is_coind; cbn -[lookup_inductive];
      rewrite ?hlf /=; move: wf; rewrite /wf_brs; len;
      rtoProp; intuition auto; solve_all.
  - cbn -[lookup_projection]. intros wf.
    destruct GlobalContextMap.is_coind; cbn -[lookup_projection];
      rewrite ?hlf /=; move: wf; rtoProp; intuition auto.
  - cbn. unfold wf_fix_gen, test_def; len. intros wf.
    rtoProp; intuition auto; solve_all.
    destruct (dbody x) => //.
    all:now rewrite /= andb_false_r in a0.
  - (* A cofixpoint becomes a fixpoint whose bodies are abstractions or,
       for a nullary one, a thunk *)
    cbn. unfold wf_fix_gen, test_def; len. intros wf.
    rtoProp; intuition auto; solve_all.
    + rewrite hlf /=. apply isLambda_wrap_lazy. now apply isLambdas_trans.
    + apply (wellformed_wrap_lazy (efl := switch_off_cofix efl)) => //.
      now apply a.
  - cbn. intros wf; rtoProp; intuition auto. solve_all_k 6.
    depelim X; cbn in *; rtoProp; intuition auto; solve_all.
    move: H0; rewrite /test_array_model /=. rtoProp; intuition auto.
    solve_all.
Qed.

Lemma trans_env_extends' {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  extends_prefix Σ Σ' ->
  wf_glob Σ' ->
  List.map (on_snd (trans_decl Σ)) Σ.(GlobalContextMap.global_decls) =
  List.map (on_snd (trans_decl Σ')) Σ.(GlobalContextMap.global_decls).
Proof.
  intros ext.
  destruct Σ as [Σ map repr wf]; cbn in *.
  move=> wfΣ.
  assert (extends_prefix Σ Σ); auto. now exists [].
  assert (wf_glob Σ).
  { eapply extends_wf_glob. exact ext. tea. }
  revert H H0.
  generalize Σ at 1 3 5 6. intros Σ''.
  induction Σ'' => //. cbn.
  intros hin wfg. depelim wfg.
  f_equal.
  2:{ eapply IHΣ'' => //. destruct hin. exists (x ++ [(kn, d)]).
      rewrite -app_assoc /= //. }
  unfold on_snd. cbn. f_equal.
  eapply wellformed_trans_decl_extends => //. cbn.
  eapply extends_wf_global_decl. 3:tea.
  eapply extends_wf_glob; tea. eapply extends_prefix_extends; tea.
  2:{ eapply extends_wf_glob; tea. }
  destruct hin. exists (x ++ [(kn, d)]). rewrite -app_assoc /= //.
  cbn. eapply extends_prefix_extends; tea.
Qed.

Lemma trans_env_eq {efl : EEnvFlags} (Σ : GlobalContextMap.t) :
  wf_glob Σ ->
  trans_env Σ =
  trans_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  unfold trans_env.
  destruct Σ; cbn. cbn in wf.
  induction global_decls in map, repr, wf0, wf |- * => //.
  cbn. f_equal.
  destruct a as [kn d]; unfold on_snd; cbn. f_equal. symmetry.
  eapply wellformed_trans_decl_extends => //. cbn. now depelim wf. cbn.
  eapply extends_prefix_extends; tea. now exists [(kn, d)]. cbn.
  set (Σg' := GlobalContextMap.make global_decls
    (fresh_globals_cons_inv wf0)).
  erewrite <- (IHglobal_decls (GlobalContextMap.map Σg')
    (GlobalContextMap.repr Σg')).
  2:now depelim wf.
  set (Σg := {| GlobalContextMap.global_decls := _ :: _ |}).
  symmetry. eapply (trans_env_extends' (Σ := Σg') (Σ' := Σg)) => //.
  cbn. now exists [a].
Qed.

Lemma trans_wellformed_irrel {efl efl' : EEnvFlags}
  {Σ : GlobalContextMap.t} t :
  @wf_glob efl Σ ->
  forall n, @wellformed efl' Σ n t -> @wellformed efl' (trans_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto;
    solve_all].
  - rewrite (lookup_env_trans (efl := efl)) //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct (cst_body c) => //.
  - rewrite (lookup_env_trans (efl := efl)) //.
    destruct lookup_env as [[|m]|] eqn:hl => /=; rewrite ?andb_false_r //.
    destruct (nth_error (ind_bodies m) _) => /=; rewrite ?andb_false_r //.
    destruct (nth_error (ind_ctors _) _) => /=; rewrite ?andb_false_r //.
    intros; rtoProp; intuition auto.
    destruct cstr_as_blocks; rtoProp; intuition auto. solve_all.
  - rewrite /wf_brs; cbn; rewrite (lookup_env_trans (efl := efl)) //.
    destruct lookup_env as [[|m]|] eqn:hl => /=; rewrite ?andb_false_r //.
    destruct nth_error => /=; rewrite ?andb_false_r //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite (lookup_env_trans (efl := efl)) //.
    destruct lookup_env as [[|m]|] eqn:hl => /=; rewrite ?andb_false_r //.
    destruct nth_error => /=; rewrite ?andb_false_r //.
    all:intros; rtoProp; intuition auto; solve_all.
    move: H1. destruct (ind_ctors o) => //=.
    now destruct nth_error.
Qed.

Lemma trans_wellformed_decl_irrel {efl efl' : EEnvFlags}
  {Σ : GlobalContextMap.t} d :
  @wf_glob efl Σ ->
  @wf_global_decl efl' Σ d -> @wf_global_decl efl' (trans_env Σ) d.
Proof.
  intros wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply (trans_wellformed_irrel (efl := efl)).
Qed.

Lemma trans_decl_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tLazy_Force -> has_tFix -> wf_glob Σ ->
  forall d, wf_global_decl Σ d ->
  @wf_global_decl (switch_off_cofix efl) (trans_env Σ) (trans_decl Σ d).
Proof.
  intros hlf hfix wf d hd.
  eapply (trans_wellformed_decl_irrel (efl := efl)); tea.
  move: hd.
  destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply trans_wellformed.
Qed.

Lemma fresh_global_trans_env {Σ : GlobalContextMap.t} kn :
  fresh_global kn Σ ->
  fresh_global kn (trans_env Σ).
Proof.
  destruct Σ as [Σ map repr wf]; cbn in *.
  induction 1; cbn; constructor; auto.
  now eapply Forall_map; cbn.
Qed.

Lemma trans_env_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tLazy_Force -> has_tFix ->
  wf_glob Σ -> @wf_glob (switch_off_cofix efl) (trans_env Σ).
Proof.
  intros hlf hfix wfg. rewrite trans_env_eq //.
  destruct Σ as [Σ map repr wf]; cbn in *.
  clear map repr.
  induction wfg; cbn; constructor; auto.
  - rewrite /= -(trans_env_eq (GlobalContextMap.make Σ
      (fresh_globals_cons_inv wf))) //.
    eapply trans_decl_wf => //.
  - rewrite /= -(trans_env_eq (GlobalContextMap.make Σ
      (fresh_globals_cons_inv wf))) //.
    now eapply fresh_global_trans_env.
Qed.

Definition trans_program (p : eprogram_env) :=
  (trans_env p.1, trans p.1 p.2).

Definition trans_program_wf {efl} (p : eprogram_env)
  {haslf : has_tLazy_Force} {hasfix : has_tFix} :
  wf_eprogram_env efl p ->
  wf_eprogram (switch_off_cofix efl) (trans_program p).
Proof.
  intros []; split.
  now eapply trans_env_wf.
  cbn. eapply (trans_wellformed_irrel (efl := efl)); tea.
  now eapply trans_wellformed.
Qed.

(** The translation is stable under extension of the environment *)
Lemma trans_env_extends {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  extends Σ Σ' -> wf_glob Σ -> wf_glob Σ' ->
  extends (trans_env Σ) (trans_env Σ').
Proof.
  intros ext wf wf' kn d.
  rewrite !lookup_env_trans //.
  destruct (lookup_env Σ kn) as [d0|] eqn:hl => //=. intros [= <-].
  rewrite (ext _ _ hl) /=. f_equal. symmetry.
  eapply wellformed_trans_decl_extends; tea.
  eapply lookup_env_wellformed; tea.
Qed.
