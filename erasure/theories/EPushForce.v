(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils
    ELiftSubst ECSubst EGlobalEnv EInduction EWellformed EWcbvEval
    EProgram EFirstorder.

Local Open Scope string_scope.
Set Asymmetric Patterns.

From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

(** * Pushing [tForce] inside terms

  The translation of cofixpoints to lazy fixpoints
  ([ECoInductiveToInductive]) produces forces applied to terms whose head
  is not a variable, in particular [tForce (tLazy t)] when the body of a
  cofixpoint is directly a constructor. This pass pushes forces towards the
  leaves of the term they apply to and cancels them against thunks:

  - [tForce (tLazy t)] becomes [t];
  - [tForce (tCase ind c brs)] becomes [tCase ind c brs'], where the force
    is pushed in each branch;
  - [tForce (tLetIn na b c)] becomes [tLetIn na b c'], where the force is
    pushed in [c]. *)

(** [push_force t] is [tForce t] with the force pushed inside [t]. *)
Fixpoint push_force (t : term) : term :=
  match t with
  | tLazy t => t
  | tCase ind c brs => tCase ind c (map (on_snd push_force) brs)
  | tLetIn na b c => tLetIn na b (push_force c)
  | _ => tForce t
  end.

Fixpoint force_opt (t : term) : term :=
  match t with
  | tRel i => tRel i
  | tEvar ev args => tEvar ev (map force_opt args)
  | tLambda na M => tLambda na (force_opt M)
  | tApp u v => tApp (force_opt u) (force_opt v)
  | tLetIn na b b' => tLetIn na (force_opt b) (force_opt b')
  | tCase ind c brs => tCase ind (force_opt c) (map (on_snd force_opt) brs)
  | tProj p c => tProj p (force_opt c)
  | tFix mfix idx => tFix (map (map_def force_opt) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def force_opt) mfix) idx
  | tBox => t
  | tVar _ => t
  | tConst _ => t
  | tConstruct ind i args => tConstruct ind i (map force_opt args)
  | tPrim p => tPrim (map_prim force_opt p)
  | tLazy t => tLazy (force_opt t)
  | tForce t => push_force (force_opt t)
  end.

(** ** Pushed forces

  [pushed t r]: [r] is [tForce t] where the force has been pushed inside
  [t], to any depth. Unlike [push_force], this relation is closed under
  substitution: substituting a thunk for a variable creates new occasions
  of pushing a force, which need not be taken. *)

Unset Elimination Schemes.
Inductive pushed : term -> term -> Type :=
| pushed_refl t : pushed t (tForce t)
| pushed_lazy t : pushed (tLazy t) t
| pushed_case ind c brs brs' :
  All2 (fun br br' => (br.1 = br'.1) × pushed br.2 br'.2) brs brs' ->
  pushed (tCase ind c brs) (tCase ind c brs')
| pushed_let na b c c' :
  pushed c c' -> pushed (tLetIn na b c) (tLetIn na b c').
Set Elimination Schemes.
Derive Signature for pushed.

Lemma pushed_rect (P : term -> term -> Type) :
  (forall t, P t (tForce t)) ->
  (forall t, P (tLazy t) t) ->
  (forall ind c brs brs',
    All2 (fun br br' => (br.1 = br'.1) × pushed br.2 br'.2) brs brs' ->
    All2 (fun br br' => (br.1 = br'.1) × P br.2 br'.2) brs brs' ->
    P (tCase ind c brs) (tCase ind c brs')) ->
  (forall na b c c', pushed c c' -> P c c' ->
    P (tLetIn na b c) (tLetIn na b c')) ->
  forall t r, pushed t r -> P t r.
Proof.
  intros Hrefl Hlazy Hcase Hlet. fix aux 3. intros t r [].
  - apply Hrefl.
  - apply Hlazy.
  - apply Hcase => //.
    clear -aux a. induction a; constructor; auto.
    destruct r as [e p]. split => //. now apply aux.
  - apply Hlet => //. now apply aux.
Qed.

Lemma pushed_push_force t : pushed t (push_force t).
Proof.
  induction t using EInduction.term_forall_list_ind; cbn;
    try solve [constructor].
  - constructor. assumption.
  - constructor. solve_all.
Qed.

Lemma pushed_csubst a k t r :
  pushed t r -> pushed (csubst a k t) (csubst a k r).
Proof.
  intros h; revert t r h k. apply: pushed_rect; cbn; intros.
  - constructor.
  - constructor.
  - constructor. solve_all. rewrite -a2. apply b3.
  - constructor. auto.
Qed.

Lemma pushed_substl s t r :
  pushed t r -> pushed (substl s t) (substl s r).
Proof.
  induction s in t, r |- *; cbn; auto.
  intros h. apply IHs. now apply pushed_csubst.
Qed.

(** ** Pushing a force preserves evaluation *)

Section Eval.
  Context {wfl : WcbvFlags} (Σ : global_declarations).

  Notation "Σ ⊢ s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level).

  Lemma eval_force_value t lv x :
    Σ ⊢ t ⇓ lv -> Σ ⊢ tForce lv ⇓ x -> Σ ⊢ tForce t ⇓ x.
  Proof using Type.
    intros ev evf.
    eapply eval_tForce_inv in evf
      as [[b [evw evb]]|[mfix [idx [narg [b [evw hc evb]]]]]].
    - eapply eval_force; tea. eapply eval_trans; tea.
    - eapply eval_force_fix; tea. eapply eval_trans; tea.
  Qed.

  (** If [t] evaluates to a value [lv] which is forced to [x], then [t]
      with the force pushed inside evaluates to [x]. The value [lv] of a
      match or of a let-binding is the value of the branch or body that is
      taken, so the induction goes through with [lv] and [x] fixed. *)
  Lemma eval_pushed t lv x :
    Σ ⊢ t ⇓ lv -> Σ ⊢ tForce lv ⇓ x ->
    forall r, pushed t r -> Σ ⊢ r ⇓ x.
  Proof using Type.
    intros ev evf. induction ev; intros r hp; depelim hp.
    (* The force is not pushed *)
    all:try solve [eapply eval_force_value; [|eassumption];
      econstructor; eauto].
    - eapply eval_zeta; tea. apply IHev2 => //. now apply pushed_csubst.
    - eapply All2_nth_error_Some in a as [br' [hnth [hn hbr]]]; tea.
      eapply eval_iota; tea.
      + now rewrite -hn.
      + apply IHev2 => //. rewrite /iota_red. now apply pushed_substl.
    - eapply All2_nth_error_Some in a as [br' [hnth [hn hbr]]]; tea.
      eapply eval_iota_block; tea.
      + now rewrite -hn.
      + apply IHev2 => //. rewrite /iota_red. now apply pushed_substl.
    - subst brs. depelim a. depelim a. destruct y as [n' f']; cbn in *.
      destruct p as [<- hf].
      eapply eval_iota_sing; tea; [reflexivity|].
      apply IHev2 => //. now apply pushed_substl.
    - eapply eval_cofix_case; tea. apply IHev3 => //. now constructor.
    - (* A thunk: the force is cancelled *)
      eapply eval_tForce_inv in evf
        as [[b [evw evb]]|[mfix [idx [narg [b [evw hc evb]]]]]].
      + eapply eval_deterministic in evw; [|now apply eval_atom].
        now noconf evw.
      + eapply eval_deterministic in evw; [|now apply eval_atom].
        discriminate.
    - now cbn in i.
    - now cbn in i.
  Qed.

  Corollary eval_push_force t x :
    Σ ⊢ tForce t ⇓ x -> Σ ⊢ push_force t ⇓ x.
  Proof using Type.
    intros ev.
    eapply eval_tForce_inv in ev
      as [[b [evw evb]]|[mfix [idx [narg [b [evw hc evb]]]]]].
    - eapply eval_pushed; [exact evw| |apply pushed_push_force].
      eapply eval_force; [now apply eval_atom|exact evb].
    - eapply eval_pushed; [exact evw| |apply pushed_push_force].
      eapply eval_force_fix; [now apply eval_atom|exact hc|exact evb].
  Qed.
End Eval.

(** ** The optimization relation

  [force_opt] does not commute with substitution: substituting a thunk for a
  variable under a force creates a redex the function would have
  simplified. Correctness is hence proved for the relation [t ⇝ t'], the
  congruence closure of [pushed]: any force in [t] may be pushed, to any
  depth. It contains the graph of [force_opt] and is closed under
  substitution. *)

Declare Scope force_scope.
Delimit Scope force_scope with force.
Reserved Notation "t ⇝ t'" (at level 70).
Local Open Scope force_scope.

Definition def_rel (R : term -> term -> Type) (d d' : def term) :=
  [× dname d = dname d', rarg d = rarg d' & R (dbody d) (dbody d')].

Unset Elimination Schemes.
Inductive frel : term -> term -> Type :=
| frel_box : tBox ⇝ tBox
| frel_rel i : tRel i ⇝ tRel i
| frel_var id : tVar id ⇝ tVar id
| frel_evar ev args args' :
  All2 frel args args' -> tEvar ev args ⇝ tEvar ev args'
| frel_lambda na b b' : b ⇝ b' -> tLambda na b ⇝ tLambda na b'
| frel_letin na b b' c c' :
  b ⇝ b' -> c ⇝ c' -> tLetIn na b c ⇝ tLetIn na b' c'
| frel_app f f' a a' : f ⇝ f' -> a ⇝ a' -> tApp f a ⇝ tApp f' a'
| frel_const kn : tConst kn ⇝ tConst kn
| frel_construct ind c args args' :
  All2 frel args args' -> tConstruct ind c args ⇝ tConstruct ind c args'
| frel_case ip discr discr' brs brs' :
  discr ⇝ discr' ->
  All2 (fun br br' => (br.1 = br'.1) × br.2 ⇝ br'.2) brs brs' ->
  tCase ip discr brs ⇝ tCase ip discr' brs'
| frel_proj p c c' : c ⇝ c' -> tProj p c ⇝ tProj p c'
| frel_fix mfix mfix' idx :
  All2 (def_rel frel) mfix mfix' -> tFix mfix idx ⇝ tFix mfix' idx
| frel_cofix mfix mfix' idx :
  All2 (def_rel frel) mfix mfix' -> tCoFix mfix idx ⇝ tCoFix mfix' idx
| frel_prim p p' : prim_rel frel p p' -> tPrim p ⇝ tPrim p'
| frel_lazy t t' : t ⇝ t' -> tLazy t ⇝ tLazy t'
(** A force may be pushed inside the term it applies to *)
| frel_force t t' r : t ⇝ t' -> pushed t' r -> tForce t ⇝ r
where "t ⇝ t'" := (frel t t') : force_scope.
Set Elimination Schemes.
Derive Signature for frel.

Section FrelInd.
  Context (P : term -> term -> Type).
  Context (Pbox : P tBox tBox)
    (Prel : forall i, P (tRel i) (tRel i))
    (Pvar : forall id, P (tVar id) (tVar id))
    (Pevar : forall ev args args', All2 frel args args' ->
      All2 P args args' -> P (tEvar ev args) (tEvar ev args'))
    (Plambda : forall na b b', b ⇝ b' -> P b b' ->
      P (tLambda na b) (tLambda na b'))
    (Pletin : forall na b b' c c', b ⇝ b' -> P b b' -> c ⇝ c' -> P c c' ->
      P (tLetIn na b c) (tLetIn na b' c'))
    (Papp : forall f f' a a', f ⇝ f' -> P f f' -> a ⇝ a' -> P a a' ->
      P (tApp f a) (tApp f' a'))
    (Pconst : forall kn, P (tConst kn) (tConst kn))
    (Pconstruct : forall ind c args args', All2 frel args args' ->
      All2 P args args' ->
      P (tConstruct ind c args) (tConstruct ind c args'))
    (Pcase : forall ip discr discr' brs brs',
      discr ⇝ discr' -> P discr discr' ->
      All2 (fun br br' => (br.1 = br'.1) × br.2 ⇝ br'.2) brs brs' ->
      All2 (fun br br' => (br.1 = br'.1) × P br.2 br'.2) brs brs' ->
      P (tCase ip discr brs) (tCase ip discr' brs'))
    (Pproj : forall p c c', c ⇝ c' -> P c c' -> P (tProj p c) (tProj p c'))
    (Pfix : forall mfix mfix' idx, All2 (def_rel frel) mfix mfix' ->
      All2 (def_rel P) mfix mfix' -> P (tFix mfix idx) (tFix mfix' idx))
    (Pcofix : forall mfix mfix' idx, All2 (def_rel frel) mfix mfix' ->
      All2 (def_rel P) mfix mfix' -> P (tCoFix mfix idx) (tCoFix mfix' idx))
    (Pprim : forall p p', prim_rel frel p p' -> prim_rel P p p' ->
      P (tPrim p) (tPrim p'))
    (Plazy : forall t t', t ⇝ t' -> P t t' -> P (tLazy t) (tLazy t'))
    (Pforce : forall t t' r, t ⇝ t' -> P t t' -> pushed t' r ->
      P (tForce t) r).

  Lemma frel_rect : forall t t', t ⇝ t' -> P t t'.
  Proof using Pbox Prel Pvar Pevar Plambda Pletin Papp Pconst Pconstruct
    Pcase Pproj Pfix Pcofix Pprim Plazy Pforce.
    fix aux 3. intros t t' r.
    assert (auxl : forall l l', All2 frel l l' -> All2 P l l').
    { fix auxl 3. intros l l' []; constructor;
      [apply aux; assumption|apply auxl; assumption]. }
    assert (auxbr : forall l l' : list (list name × term),
      All2 (fun br br' => (br.1 = br'.1) × br.2 ⇝ br'.2) l l' ->
      All2 (fun br br' => (br.1 = br'.1) × P br.2 br'.2) l l').
    { fix auxl' 3. intros l l' [|? ? ? ? [e r'] rs]; constructor;
      [split; [exact e|apply aux; exact r']|apply auxl'; exact rs]. }
    assert (auxd : forall l l', All2 (def_rel frel) l l' ->
      All2 (def_rel P) l l').
    { fix auxl' 3. intros l l' [|? ? ? ? [e e' r'] rs]; constructor;
      [split; [exact e|exact e'|apply aux; exact r']|apply auxl'; exact rs]. }
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
    - apply Pcase; auto.
    - apply Pproj; auto.
    - apply Pfix; auto.
    - apply Pcofix; auto.
    - apply Pprim; auto.
      destruct p0; constructor; auto.
    - apply Plazy; auto.
    - eapply Pforce; eauto.
  Qed.
End FrelInd.

Lemma frel_force_opt t : t ⇝ force_opt t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn;
    try solve [constructor; eauto].
  - constructor. solve_all.
  - constructor. solve_all.
  - constructor; auto. solve_all.
  - constructor. eapply All2_map_right, All_All2; tea. cbn.
    intros x hx; split; cbn; auto.
  - constructor. eapply All2_map_right, All_All2; tea. cbn.
    intros x hx; split; cbn; auto.
  - constructor. destruct p as [? []]; cbn in *; try constructor; cbn.
    all:depelim X; cbn; auto. destruct p; cbn in *. solve_all.
    exact p.1.
  - eapply frel_force; tea. apply pushed_push_force.
Qed.

Lemma frel_csubst a a' :
  a ⇝ a' -> forall t t', t ⇝ t' ->
  forall k, csubst a k t ⇝ csubst a' k t'.
Proof.
  intros ha. apply: frel_rect => /=.
  all:try solve [intros; constructor; auto].
  - intros i k. destruct (k ?= i) => //; constructor.
  - intros. constructor. solve_all.
  - intros. constructor. solve_all.
  - intros. constructor; auto. solve_all.
    destruct y; cbn in *; subst; eauto.
  - intros mfix mfix' idx a0 IH k. constructor.
    rewrite -(All2_length a0). solve_all.
    destruct b as [? ? hb]. split; cbn; auto.
  - intros mfix mfix' idx a0 IH k. constructor.
    rewrite -(All2_length a0). solve_all.
    destruct b as [? ? hb]. split; cbn; auto.
  - intros p p' hp []; intros k; cbn; apply frel_prim; constructor;
      cbn; auto.
    solve_all.
  - intros t t' r ht IH hp k. eapply frel_force; [apply IH|].
    now apply pushed_csubst.
Qed.

Lemma frel_substl s s' :
  All2 frel s s' -> forall t t', t ⇝ t' -> substl s t ⇝ substl s' t'.
Proof.
  induction 1; cbn; auto. intros t t' h. apply IHX. now apply frel_csubst.
Qed.

Lemma frel_mkApps f f' args args' :
  f ⇝ f' -> All2 frel args args' -> mkApps f args ⇝ mkApps f' args'.
Proof.
  intros hf ha. induction ha in f, f', hf |- *; cbn; auto.
  apply IHha. now constructor.
Qed.

Lemma frel_iota_red pars args args' br br' :
  All2 frel args args' -> br.2 ⇝ br'.2 ->
  iota_red pars args br ⇝ iota_red pars args' br'.
Proof.
  intros ha hbr. rewrite /iota_red. apply frel_substl => //.
  now apply All2_rev, All2_skipn.
Qed.

Lemma frel_fix_subst mfix mfix' :
  All2 (def_rel frel) mfix mfix' ->
  All2 frel (fix_subst mfix) (fix_subst mfix').
Proof.
  intros a. rewrite /fix_subst -(All2_length a).
  induction #|mfix|; constructor; auto. now constructor.
Qed.

Lemma frel_cofix_subst mfix mfix' :
  All2 (def_rel frel) mfix mfix' ->
  All2 frel (cofix_subst mfix) (cofix_subst mfix').
Proof.
  intros a. rewrite /cofix_subst -(All2_length a).
  induction #|mfix|; constructor; auto. now constructor.
Qed.

Lemma frel_cunfold_fix mfix mfix' idx narg fn :
  All2 (def_rel frel) mfix mfix' ->
  cunfold_fix mfix idx = Some (narg, fn) ->
  ∑ fn', cunfold_fix mfix' idx = Some (narg, fn') × fn ⇝ fn'.
Proof.
  intros a. rewrite /cunfold_fix.
  destruct (nth_error mfix idx) as [d|] eqn:hnth => //. intros [= <- <-].
  eapply All2_nth_error_Some in a as a'; tea.
  destruct a' as [d' [hnth' [_ hr hb]]]. rewrite hnth' -hr.
  eexists; split; [reflexivity|].
  apply frel_substl => //. now apply frel_fix_subst.
Qed.

Lemma frel_cunfold_cofix mfix mfix' idx narg fn :
  All2 (def_rel frel) mfix mfix' ->
  cunfold_cofix mfix idx = Some (narg, fn) ->
  ∑ fn', cunfold_cofix mfix' idx = Some (narg, fn') × fn ⇝ fn'.
Proof.
  intros a. rewrite /cunfold_cofix.
  destruct (nth_error mfix idx) as [d|] eqn:hnth => //. intros [= <- <-].
  eapply All2_nth_error_Some in a as a'; tea.
  destruct a' as [d' [hnth' [_ hr hb]]]. rewrite hnth' -hr.
  eexists; split; [reflexivity|].
  apply frel_substl => //. now apply frel_cofix_subst.
Qed.

(** ** Translation of environments *)

Definition force_opt_constant_decl cb :=
  {| cst_body := option_map force_opt cb.(cst_body) |}.

Definition force_opt_decl d :=
  match d with
  | ConstantDecl cb => ConstantDecl (force_opt_constant_decl cb)
  | InductiveDecl idecl => d
  end.

Definition force_opt_env (Σ : global_declarations) :=
  map (on_snd force_opt_decl) Σ.

Lemma lookup_env_force_opt Σ kn :
  lookup_env (force_opt_env Σ) kn =
  option_map force_opt_decl (lookup_env Σ kn).
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn => //.
  destruct (eqb_spec kn kn') => //.
Qed.

Lemma lookup_constructor_force_opt Σ ind c :
  lookup_constructor (force_opt_env Σ) ind c = lookup_constructor Σ ind c.
Proof.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_force_opt. destruct lookup_env as [[]|] => //.
Qed.

Lemma constructor_isprop_pars_decl_force_opt Σ ind c :
  constructor_isprop_pars_decl (force_opt_env Σ) ind c =
  constructor_isprop_pars_decl Σ ind c.
Proof.
  rewrite /constructor_isprop_pars_decl lookup_constructor_force_opt //.
Qed.

Lemma inductive_isprop_and_pars_force_opt Σ ind :
  inductive_isprop_and_pars (force_opt_env Σ) ind =
  inductive_isprop_and_pars Σ ind.
Proof.
  rewrite /inductive_isprop_and_pars /lookup_inductive /lookup_minductive.
  rewrite lookup_env_force_opt. destruct lookup_env as [[]|] => //.
Qed.

Lemma is_coind_force_opt Σ kn :
  is_coind (force_opt_env Σ) kn = is_coind Σ kn.
Proof.
  rewrite /is_coind /lookup_inductive_kind /lookup_minductive.
  rewrite lookup_env_force_opt. destruct lookup_env as [[]|] => //.
Qed.

(** ** Correctness *)

Lemma frel_mkApps_inv f args t' :
  mkApps f args ⇝ t' ->
  ∑ f' args', [× t' = mkApps f' args', f ⇝ f' & All2 frel args args'].
Proof.
  revert t'. induction args using rev_ind; cbn; intros t'.
  - intros h. exists t', []. split => //.
  - rewrite mkApps_app /=. intros h. depelim h.
    destruct (IHargs _ h1) as [f0 [args0 [-> hf ha]]].
    exists f0, (args0 ++ [a']). split => //.
    + now rewrite mkApps_app.
    + eapply All2_app => //. now constructor.
Qed.

Lemma frel_repeat_box n : All2 frel (repeat tBox n) (repeat tBox n).
Proof. induction n; constructor; auto. constructor. Qed.

Section Correctness.
  Context {wfl : WcbvFlags} (Σ : global_declarations).
  Notation Σ' := (force_opt_env Σ).
  Notation "Σ ⊢ s ⇓ t" := (eval Σ s t) (at level 50, s, t at next level).

  (** Simulation: related terms evaluate to related values. Every rule is a
      congruence, except for the two forcing rules where [eval_pushed] shows
      that the pushed force computes the same value. *)
  Lemma force_opt_rel_correct t v :
    Σ ⊢ t ⇓ v -> forall t', t ⇝ t' -> ∑ v', Σ' ⊢ t' ⇓ v' × v ⇝ v'.
  Proof using Type.
    intros ev. induction ev; intros t0 h.
    1-21:depelim h.
    - (* box *)
      destruct (IHev1 _ h1) as [fv' [evf hf]]. depelim hf.
      destruct (IHev2 _ h2) as [av' [eva ha]].
      exists tBox; split; [eapply eval_box; tea|constructor].
    - (* beta *)
      destruct (IHev1 _ h1) as [fv' [evf hf]]. depelim hf.
      destruct (IHev2 _ h2) as [av' [eva ha]].
      destruct (IHev3 (csubst av' 0 b')) as [v' [ev hv]].
      { now apply frel_csubst. }
      exists v'; split => //. eapply eval_beta; tea.
    - (* zeta *)
      destruct (IHev1 _ h1) as [bv' [evb hb]].
      destruct (IHev2 (csubst bv' 0 c')) as [v' [ev hv]].
      { now apply frel_csubst. }
      exists v'; split => //. eapply eval_zeta; tea.
    - (* iota *)
      destruct (IHev1 _ h) as [dv' [evd hd]].
      eapply frel_mkApps_inv in hd as [f' [args' [-> hf ha]]].
      depelim hf.
      match goal with H : All2 frel [] _ |- _ => depelim H end.
      eapply All2_nth_error_Some in a as [br' [hnth [hn hbr]]]; tea.
      destruct (IHev2 (iota_red pars args' br')) as [v' [ev hv]].
      { now apply frel_iota_red. }
      exists v'; split => //. eapply eval_iota; tea.
      + now rewrite constructor_isprop_pars_decl_force_opt.
      + now rewrite -(All2_length ha).
      + now rewrite -hn -e4 !length_skipn (All2_length ha).
    - (* iota, constructors as blocks *)
      destruct (IHev1 _ h) as [dv' [evd hd]]. depelim hd.
      eapply All2_nth_error_Some in a as [br' [hnth [hn hbr]]]; tea.
      destruct (IHev2 (iota_red pars args' br')) as [v' [ev hv]].
      { now apply frel_iota_red. }
      exists v'; split => //. eapply eval_iota_block; tea.
      + now rewrite constructor_isprop_pars_decl_force_opt.
      + now rewrite -(All2_length a0).
      + now rewrite -hn -e4 !length_skipn (All2_length a0).
    - (* match on a proof *)
      destruct (IHev1 _ h) as [dv' [evd hd]]. depelim hd.
      subst brs. depelim a. depelim a. destruct y as [n' f']; cbn in *.
      destruct p as [<- hf].
      destruct (IHev2 (substl (repeat tBox #|n|) f')) as [v' [ev hv]].
      { apply frel_substl => //. apply frel_repeat_box. }
      exists v'; split => //. eapply eval_iota_sing; tea.
      + now rewrite inductive_isprop_and_pars_force_opt.
      + reflexivity.
    - (* guarded fixpoint unfolding *)
      destruct (IHev1 _ h1) as [fv' [evf hf]].
      eapply frel_mkApps_inv in hf as [g [argsv' [-> hg ha]]]. depelim hg.
      destruct (IHev2 _ h2) as [av' [eva hav]].
      match goal with
        H : cunfold_fix _ _ = _ |- _ =>
          eapply frel_cunfold_fix in H as [fn' [hunf hfn]]; tea
      end.
      destruct (IHev3 (tApp (mkApps fn' argsv') av')) as [v' [ev hv]].
      { constructor => //. now apply frel_mkApps. }
      exists v'; split => //. eapply eval_fix; tea.
      now rewrite -(All2_length ha).
    - (* stuck guarded fixpoint *)
      destruct (IHev1 _ h1) as [fv' [evf hf]].
      eapply frel_mkApps_inv in hf as [g [argsv' [-> hg ha]]]. depelim hg.
      destruct (IHev2 _ h2) as [av' [eva hav]].
      match goal with
        H : cunfold_fix _ _ = _ |- _ =>
          eapply frel_cunfold_fix in H as [fn' [hunf hfn]]; tea
      end.
      eexists; split.
      + eapply eval_fix_value; tea. now rewrite -(All2_length ha).
      + constructor => //. apply frel_mkApps => //. now constructor.
    - (* unguarded fixpoint unfolding *)
      destruct (IHev1 _ h1) as [fv' [evf hf]]. depelim hf.
      match goal with
        H : cunfold_fix _ _ = _ |- _ =>
          eapply frel_cunfold_fix in H as [fn' [hunf hfn]]; tea
      end.
      destruct (IHev2 _ h2) as [av' [eva hav]].
      destruct (IHev3 (tApp fn' av')) as [v' [ev hv]].
      { now constructor. }
      exists v'; split => //. eapply eval_fix'; tea.
    - (* cofixpoint unfolding under a match *)
      destruct (IHev1 _ h) as [dv' [evd hd]].
      eapply frel_mkApps_inv in hd as [g [args' [-> hg ha]]]. depelim hg.
      match goal with
        H : cunfold_cofix _ _ = _ |- _ =>
          eapply frel_cunfold_cofix in H as [fn' [hunf hfn]]; tea
      end.
      destruct (IHev2 (mkApps fn' args')) as [bv' [evb hb]].
      { now apply frel_mkApps. }
      destruct (IHev3 (tCase ip bv' brs')) as [v' [ev hv]].
      { now constructor. }
      exists v'; split => //. eapply eval_cofix_case; tea.
      now rewrite is_coind_force_opt.
    - (* cofixpoint unfolding under a projection *)
      destruct (IHev1 _ h) as [dv' [evd hd]].
      eapply frel_mkApps_inv in hd as [g [args' [-> hg ha]]]. depelim hg.
      match goal with
        H : cunfold_cofix _ _ = _ |- _ =>
          eapply frel_cunfold_cofix in H as [fn' [hunf hfn]]; tea
      end.
      destruct (IHev2 (mkApps fn' args')) as [bv' [evb hb]].
      { now apply frel_mkApps. }
      destruct (IHev3 (tProj p bv')) as [v' [ev hv]].
      { now constructor. }
      exists v'; split => //. eapply eval_cofix_proj; tea.
      now rewrite is_coind_force_opt.
    - (* cofixpoint applied below its arity *)
      destruct (IHev1 _ h1) as [fv' [evf hf]].
      eapply frel_mkApps_inv in hf as [g [argsv' [-> hg ha]]]. depelim hg.
      destruct (IHev2 _ h2) as [av' [eva hav]].
      assert (har : cofix_arity mfix' idx = Some narg).
      { match goal with H : cofix_arity _ _ = _ |- _ => move: H end.
        rewrite /cofix_arity.
        destruct (nth_error mfix idx) as [d|] eqn:hnth => //=. intros [= <-].
        match goal with
          H : All2 (def_rel frel) _ _ |- _ =>
            eapply All2_nth_error_Some in H as [d' [-> [_ hr _]]]; tea
        end.
        now rewrite /= hr. }
      eexists; split.
      + eapply eval_cofix_value; tea. now rewrite -(All2_length ha).
      + constructor => //. apply frel_mkApps => //. now constructor.
    - (* constants *)
      destruct (IHev (force_opt body)) as [v' [ev' hv]].
      { apply frel_force_opt. }
      exists v'; split => //.
      eapply (eval_delta _ _ (force_opt_constant_decl decl)); tea.
      + red. rewrite lookup_env_force_opt isdecl //.
      + cbn. now rewrite e.
    - (* projection *)
      destruct (IHev1 _ h) as [dv' [evd hd]].
      eapply frel_mkApps_inv in hd as [g [args' [-> hg ha]]]. depelim hg.
      match goal with H : All2 frel [] _ |- _ => depelim H end.
      eapply All2_nth_error_Some in ha as hn; tea.
      destruct hn as [a' [hnth ha']].
      destruct (IHev2 _ ha') as [v' [ev hv]].
      exists v'; split => //. eapply eval_proj; tea.
      + now rewrite constructor_isprop_pars_decl_force_opt.
      + now rewrite -(All2_length ha).
    - (* projection, constructors as blocks *)
      destruct (IHev1 _ h) as [dv' [evd hd]]. depelim hd.
      eapply All2_nth_error_Some in a0 as hn; tea.
      destruct hn as [a' [hnth ha']].
      destruct (IHev2 _ ha') as [v' [ev hv]].
      exists v'; split => //. eapply eval_proj_block; tea.
      + now rewrite constructor_isprop_pars_decl_force_opt.
      + now rewrite -(All2_length a0).
    - (* projection of a proof *)
      destruct (IHev _ h) as [dv' [evd hd]]. depelim hd.
      exists tBox; split; [|constructor]. eapply eval_proj_prop; tea.
      now rewrite inductive_isprop_and_pars_force_opt.
    - (* constructor application *)
      destruct (IHev1 _ h1) as [fv' [evf hf]].
      eapply frel_mkApps_inv in hf as [g [args' [-> hg ha]]]. depelim hg.
      match goal with H : All2 frel [] _ |- _ => depelim H end.
      destruct (IHev2 _ h2) as [av' [eva hav]].
      eexists; split.
      + eapply eval_construct; tea.
        * now rewrite lookup_constructor_force_opt.
        * now rewrite -(All2_length ha).
      + constructor => //. apply frel_mkApps => //. repeat constructor.
    - (* constructor blocks *)
      assert (hargs : ∑ vs', All2 (eval Σ') args'0 vs' × All2 frel args' vs').
      { eapply All2_over_undep in iha.
        clear -iha a0. induction iha in args'0, a0 |- *; depelim a0.
        - exists []; split; constructor.
        - destruct (r _ f) as [w [ev hv]].
          destruct (IHiha _ a0) as [vs' [evs hvs]].
          exists (w :: vs'); split; constructor; auto. }
      destruct hargs as [vs' [evs hvs]].
      exists (tConstruct ind c vs'). split; [|now constructor].
      eapply eval_construct_block; tea.
      + now rewrite lookup_constructor_force_opt.
      + now rewrite -(All2_length a0).
      + now apply All2_All2_Set.
    - (* primitives *)
      depelim X; depelim p1.
      1-3:eexists; split; [eapply eval_prim; constructor|
        apply frel_prim; constructor].
      eapply All2_over_undep in a.
      destruct (s _ f) as [d' [evd hd]].
      destruct a'0 as [d0 vs0]; cbn in *.
      assert (hargs : ∑ vs', All2 (eval Σ') vs0 vs' × All2 frel v' vs').
      { clear -a a2. induction a in vs0, a2 |- *; depelim a2.
        - exists []; split; constructor.
        - destruct (r _ f) as [w [ev hv]].
          destruct (IHa _ a2) as [vs' [evs hvs]].
          exists (w :: vs'); split; constructor; auto. }
      destruct hargs as [vs' [evs hvs]].
      exists (tPrim (prim_array
        {| array_default := d'; array_value := vs' |})). split.
      + eapply eval_prim.
        eapply (evalPrimArray (eval Σ') _ _ vs' d'); tea.
        now apply All2_All2_Set.
      + apply frel_prim. constructor; cbn; auto.
    - (* forcing a thunk: the target may have pushed the force *)
      destruct (IHev1 _ h) as [lv' [evl hl]]. depelim hl.
      destruct (IHev2 _ hl) as [v' [ev hv]].
      exists v'; split => //.
      eapply eval_pushed; [exact evl| |exact p].
      eapply eval_force; [now apply eval_atom|exact ev].
    - (* forcing a recursive lazy value *)
      destruct (IHev1 _ h) as [lv' [evl hl]]. depelim hl.
      match goal with
        H : cunfold_fix _ _ = _ |- _ =>
          eapply frel_cunfold_fix in H as [fn' [hunf hfn]]; tea
      end.
      depelim hfn.
      destruct (IHev2 _ hfn) as [v' [ev hv]].
      exists v'; split => //.
      eapply eval_pushed; [exact evl| |exact p].
      eapply eval_force_fix; [now apply eval_atom|exact hunf|exact ev].
    - (* atoms *)
      destruct t => //; depelim h.
      all:try solve [eexists; split; [now apply eval_atom|now constructor]].
      destruct args; [|now cbn in i]. depelim a.
      eexists; split; [|now repeat constructor].
      apply eval_atom. move: i. cbn -[lookup_constructor].
      now rewrite lookup_constructor_force_opt.
  Qed.

  (** Correctness of the optimization *)
  Theorem force_opt_correct t v :
    Σ ⊢ t ⇓ v -> ∑ v', Σ' ⊢ force_opt t ⇓ v' × v ⇝ v'.
  Proof using Type.
    intros ev. eapply force_opt_rel_correct; tea. apply frel_force_opt.
  Qed.
End Correctness.

(** ** Observations

  The relation only changes terms under a force: constructor applications
  are related to constructor applications. *)

Lemma frel_construct_inv ind c args t' :
  tConstruct ind c args ⇝ t' ->
  ∑ args', t' = tConstruct ind c args' × All2 frel args args'.
Proof. intros h; depelim h. now eexists. Qed.

(** First-order values are related to themselves only. *)
Lemma frel_firstorder_evalue_block Σ v :
  firstorder_evalue_block Σ v -> forall v', v ⇝ v' -> v' = v.
Proof.
  revert v. apply: firstorder_evalue_block_elim.
  intros ind c args hl hargs IH v' h.
  eapply frel_construct_inv in h as [args' [-> ha]]. f_equal.
  clear -IH ha. induction ha; depelim IH; f_equal; eauto.
Qed.

(** The optimization preserves the observation of first-order values. *)
Corollary force_opt_correct_firstorder {wfl : WcbvFlags} Σ t v :
  eval Σ t v -> firstorder_evalue_block Σ v ->
  eval (force_opt_env Σ) (force_opt t) v.
Proof.
  intros ev fo. destruct (force_opt_correct Σ t v ev) as [v' [ev' hv]].
  eapply frel_firstorder_evalue_block in hv; tea. now subst.
Qed.

(** ** Wellformedness *)

Lemma isLambda_force_opt t : isLambda t -> isLambda (force_opt t).
Proof. now destruct t. Qed.

Lemma isLazy_force_opt t : isLazy t -> isLazy (force_opt t).
Proof. now destruct t. Qed.

Lemma isLambdas_force_opt n t : isLambdas n t -> isLambdas n (force_opt t).
Proof. induction n in t |- *; cbn; auto. destruct t => //=. apply IHn. Qed.

Lemma wellformed_push_force {efl : EEnvFlags} Σ k t :
  wellformed Σ k (tForce t) -> wellformed Σ k (push_force t).
Proof.
  induction t in k |- * using EInduction.term_forall_list_ind;
    try solve [cbn; auto].
  - cbn. intros wf; rtoProp; intuition auto. apply IHt2. cbn. now rtoProp.
  - cbn. intros wf; rtoProp; intuition auto.
    + now len.
    + solve_all.
Qed.

Lemma wellformed_force_opt {efl : EEnvFlags} Σ k t :
  wellformed Σ k t -> wellformed Σ k (force_opt t).
Proof.
  induction t in k |- * using EInduction.term_forall_list_ind;
    cbn -[lookup_constructor lookup_constructor_pars_args
      lookup_projection]; intros wf; rtoProp; intuition eauto.
  all:try solve [solve_all].
  - destruct cstr_as_blocks; rtoProp; intuition auto; len; solve_all.
    now destruct args.
  - solve_all. move/orP: b => [h|/andP[-> h]].
    + now rewrite isLambda_force_opt.
    + now rewrite isLazy_force_opt // orb_true_r.
  - move: H0. unfold wf_fix_gen, test_def; len. rtoProp; intuition auto.
    solve_all.
  - solve_all. now apply isLambdas_force_opt.
  - move: H0. unfold wf_fix_gen, test_def; len. rtoProp; intuition auto.
    solve_all.
  - depelim X; cbn in *; rtoProp; intuition auto; solve_all.
    move: H0; rewrite /test_array_model /=. rtoProp; intuition auto.
    solve_all.
  - apply wellformed_push_force. cbn. rewrite H /=. now apply IHt.
Qed.

Lemma wellformed_force_opt_env {efl : EEnvFlags} Σ k t :
  wellformed Σ k t -> wellformed (force_opt_env Σ) k t.
Proof.
  induction t in k |- * using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto;
    solve_all].
  - rewrite lookup_env_force_opt.
    destruct lookup_env as [[]|] => //=. now destruct (cst_body c).
  - rewrite lookup_env_force_opt.
    destruct lookup_env as [[|m]|] => /=; rewrite ?andb_false_r //.
    destruct (nth_error (ind_bodies m) _) => /=; rewrite ?andb_false_r //.
    destruct (nth_error (ind_ctors _) _) => /=; rewrite ?andb_false_r //.
    intros; rtoProp; intuition auto.
    destruct cstr_as_blocks; rtoProp; intuition auto. solve_all.
  - rewrite /wf_brs; cbn; rewrite lookup_env_force_opt.
    destruct lookup_env as [[|m]|] => /=; rewrite ?andb_false_r //.
    destruct nth_error => /=; rewrite ?andb_false_r //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_force_opt.
    destruct lookup_env as [[|m]|] => /=; rewrite ?andb_false_r //.
    destruct nth_error => /=; rewrite ?andb_false_r //.
    all:intros; rtoProp; intuition auto; solve_all.
Qed.

Lemma force_opt_decl_wf {efl : EEnvFlags} Σ d :
  wf_global_decl Σ d -> wf_global_decl (force_opt_env Σ) (force_opt_decl d).
Proof.
  destruct d => //=. destruct (cst_body c) => //=. intros wf.
  now apply wellformed_force_opt_env, wellformed_force_opt.
Qed.

Lemma fresh_global_force_opt_env Σ kn :
  fresh_global kn Σ -> fresh_global kn (force_opt_env Σ).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma force_opt_env_wf {efl : EEnvFlags} Σ :
  wf_glob Σ -> wf_glob (force_opt_env Σ).
Proof.
  induction 1; cbn; constructor; auto.
  - now apply force_opt_decl_wf.
  - now apply fresh_global_force_opt_env.
Qed.

Lemma force_opt_env_extends Σ Σ' :
  extends Σ Σ' -> extends (force_opt_env Σ) (force_opt_env Σ').
Proof.
  intros ext kn d. rewrite !lookup_env_force_opt.
  destruct (lookup_env Σ kn) as [d0|] eqn:hl => //=. intros [= <-].
  now rewrite (ext _ _ hl).
Qed.

(** ** Programs *)

Definition force_opt_program (p : eprogram) : eprogram :=
  (force_opt_env p.1, force_opt p.2).

Lemma force_opt_program_wf {efl : EEnvFlags} (p : eprogram) :
  wf_eprogram efl p -> wf_eprogram efl (force_opt_program p).
Proof.
  intros []; split.
  - now apply force_opt_env_wf.
  - cbn. now apply wellformed_force_opt_env, wellformed_force_opt.
Qed.
