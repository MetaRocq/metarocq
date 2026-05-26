(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program ssreflect ssrbool btauto.Algebra.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst EnvMap.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction EWcbvEval EGlobalEnv
  EWellformed ECSubst EInduction EWcbvEvalInd EEtaExpanded.

Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.
From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.

#[export]
Hint Constructors eval : core.

Definition atomic_term (t : term) :=
  match t with
  | tBox | tConstruct _ _ _ | tConst _ | tRel _ | tVar _ | tPrim _ => true
  | _ => false
  end.

Definition has_atom {etfl : ETermFlags} (t : term) :=
  match t with
  | tBox => has_tBox
  | tConstruct _ _ _ => has_tConstruct
  | tConst _ => has_tConst
  | tRel _ => has_tRel
  | tVar _ => has_tVar
  | _ => false
  end.

Section OnSubterm.
  Context {etfl : ETermFlags}.
  Inductive on_subterms (Q : nat -> term -> Type) (n : nat) : term -> Type :=
  | on_atom t : has_atom t -> atomic_term t -> on_subterms Q n t
  | on_evar k l : has_tEvar -> All (Q n) l -> on_subterms Q n (tEvar k l)
  | on_lambda na t : has_tLambda -> Q (S n) t -> on_subterms Q n (tLambda na t)
  | on_letin na t u : has_tLetIn -> Q n t -> Q (S n) u -> on_subterms Q n (tLetIn na t u)
  | on_app f u : has_tApp -> Q n f -> Q n u -> on_subterms Q n (tApp f u)
  | on_case ci discr brs : has_tCase -> Q n discr ->
    All (fun br => Q (#|br.1| + n) br.2) brs -> on_subterms Q n (tCase ci discr brs)
  | on_proj p c : has_tProj -> Q n c -> on_subterms Q n (tProj p c)
  | on_fix mfix idx : has_tFix -> All (fun d => Q (#|mfix| + n) d.(dbody)) mfix -> on_subterms Q n (tFix mfix idx)
  | on_cofix mfix idx : has_tCoFix -> All (fun d => Q (#|mfix| + n) d.(dbody)) mfix -> on_subterms Q n (tCoFix mfix idx)
  | on_prim p : has_prim p -> primProp (Q n) p -> on_subterms Q n (tPrim p)
  | on_lazy t : has_tLazy_Force -> Q n t -> on_subterms Q n (tLazy t)
  | on_force t : has_tLazy_Force -> Q n t -> on_subterms Q n (tForce t).
  Derive Signature for on_subterms.
End OnSubterm.

Class Qpres {etfl : ETermFlags} (Q : nat -> term -> Type) := qpres : forall n t, Q n t -> on_subterms Q n t.
#[export] Hint Mode Qpres - ! : typeclass_instances.

Class Qapp {etfl : ETermFlags} (Q : nat -> term -> Type) := qapp : has_tApp -> forall n f args, Q n (mkApps f args) <~> Q n f × All (Q n) args.
#[export] Hint Mode Qapp - ! : typeclass_instances.

Class Qcase {etfl : ETermFlags} (Q : nat -> term -> Type) := qcase : has_tCase ->
  forall n ci discr brs, Q n (tCase ci discr brs) -> forall discr', Q n discr' -> Q n (tCase ci discr' brs).
#[export] Hint Mode Qcase - ! : typeclass_instances.

Class Qproj {etfl : ETermFlags} (Q : nat -> term -> Type) := qproj : has_tProj -> forall n p discr, Q n (tProj p discr) -> forall discr', Q n discr' -> Q n (tProj p discr').
#[export] Hint Mode Qproj - ! : typeclass_instances.

Class Qfix {etfl : ETermFlags} (Q : nat -> term -> Type) := qfix : has_tFix -> forall n mfix idx, idx < #|mfix| -> Q n (tFix mfix idx) -> forall idx', idx' < #|mfix| -> Q n (tFix mfix idx').
#[export] Hint Mode Qfix - ! : typeclass_instances.
Class Qcofix {etfl : ETermFlags} (Q : nat -> term -> Type) := qcofix : has_tCoFix -> forall n mfix idx, idx < #|mfix| -> Q n (tCoFix mfix idx) -> forall idx', idx' < #|mfix| -> Q n (tCoFix mfix idx').
#[export] Hint Mode Qcofix - ! : typeclass_instances.
Class Qsubst (Q : nat -> term -> Type) := qsubst : forall t l, Q (#|l|) t -> All (Q 0) l -> Q 0 (substl l t).
#[export] Hint Mode Qsubst ! : typeclass_instances.
Class Qfixs (Q : nat -> term -> Type) := qfixs : forall mfix idx, Q 0 (tFix mfix idx) ->
    forall args fn, cunfold_fix mfix idx = Some (args, fn) ->
    Q 0 fn.
#[export] Hint Mode Qfixs ! : typeclass_instances.
Class Qcofixs (Q : nat -> term -> Type) := qcofixs : forall mfix idx, Q 0 (tCoFix mfix idx) ->
  forall args fn, cunfold_cofix mfix idx = Some (args, fn) ->
  Q 0 fn.
#[export] Hint Mode Qcofixs ! : typeclass_instances.

Lemma Qfix_subst {etfl : ETermFlags} mfix Q : has_tFix -> Qfix Q -> Qpres Q -> forall idx, idx < #|mfix| -> Q 0 (tFix mfix idx) -> All (Q 0) (fix_subst mfix).
Proof.
  intros hasfix qfix qpre; unfold fix_subst.
  generalize (Nat.le_refl #|mfix|).
  generalize #|mfix| at 1 4.
  induction n. intros. constructor; auto.
  intros. constructor. eapply qfix => //. 2:tea. tea.
  eapply IHn. lia. 2:tea. assumption.
Qed.

Lemma Qcofix_subst {etfl : ETermFlags} mfix Q : has_tCoFix -> Qcofix Q -> Qpres Q -> forall idx, idx < #|mfix| -> Q 0 (tCoFix mfix idx) -> All (Q 0) (cofix_subst mfix).
Proof.
  intros hascofix qcofix qpre; unfold cofix_subst.
  generalize (Nat.le_refl #|mfix|).
  generalize #|mfix| at 1 4.
  induction n. intros. constructor; auto.
  intros. constructor. eapply qcofix => //. 2:tea. tea.
  eapply IHn. lia. 2:tea. assumption.
Qed.

#[export] Instance Qsubst_Qfixs {etfl : ETermFlags} Q : Qpres Q -> Qfix Q -> Qsubst Q -> Qfixs Q.
Proof.
  move=> qpres qfix; rewrite /Qsubst /Qfixs.
  intros Hs mfix idx hfix args fn.
  assert (hasfix : has_tFix).
  { eapply qpres in hfix. now depelim hfix. }
  rewrite /cunfold_fix.
  destruct nth_error eqn:hnth => //.
  pose proof (nth_error_Some_length hnth).
  epose proof (Qfix_subst _ _ hasfix qfix qpres idx H hfix).
  intros [= <-]. subst fn.
  eapply Hs. rewrite fix_subst_length //.
  eapply qpres in hfix. depelim hfix. depelim i0. eapply nth_error_all in a; tea. now rewrite Nat.add_0_r in a.
  assumption.
Qed.

#[export] Instance Qsubst_Qcofixs {etfl : ETermFlags} Q : Qpres Q -> Qcofix Q -> Qsubst Q -> Qcofixs Q.
Proof.
  move=> qpres qfix; rewrite /Qsubst /Qfixs.
  intros Hs mfix idx hfix args fn.
  assert (hasfix : has_tCoFix).
  { eapply qpres in hfix. now depelim hfix. }
  rewrite /cunfold_cofix.
  destruct nth_error eqn:hnth => //.
  pose proof (nth_error_Some_length hnth).
  epose proof (Qcofix_subst _ _ hasfix qfix qpres idx H hfix).
  intros [= <-]. subst fn.
  eapply Hs. rewrite cofix_subst_length //.
  eapply qpres in hfix. depelim hfix. depelim i0. eapply nth_error_all in a; tea. now rewrite Nat.add_0_r in a.
  assumption.
Qed.

Class Qconst Σ (Q : nat -> term -> Type) := qconst :
  ∀ kn decl, declared_constant Σ kn decl →
    match cst_body decl with
    | None => unit
    | Some b => Q 0 b
    end.
#[export] Hint Mode Qconst - ! : typeclass_instances.

Class Qpreserves {etfl : ETermFlags} (Q : nat -> term -> Type) Σ :=
  { qpres_qpres :: Qpres Q;
    qpres_qcons :: Qconst Σ Q;
    qpres_qapp :: Qapp Q;
    qpres_qcase :: Qcase Q;
    qpres_qproj :: Qproj Q;
    qpres_qsubst :: Qsubst Q;
    qpres_qfix :: Qfix Q;
    qpres_qcofix :: Qcofix Q }.

Lemma eval_preserve_mkApps_ind :
∀ (wfl : WcbvFlags), with_constructor_as_block = false -> forall  {efl : EEnvFlags} (Σ : global_declarations)
  (P' : term → term → Type)
  (Q : nat -> term -> Type)
  {Qpres : Qpreserves Q Σ}
  (P := (fun x y => [× P' x y, Q 0 x, Q 0 y, isEtaExp Σ x & isEtaExp Σ y])%type)
  (HPQ : ∀ t u, eval Σ t u -> Q 0 t -> P' t u -> Q 0 u),
  isEtaExp_env Σ ->
  wf_glob Σ ->
  has_tApp ->
  (∀ (a t t' : term),
	 eval Σ a tBox ->
     P a tBox →
     eval Σ t t' → P t t' → P' (tApp a t) tBox) →
  (∀ (f0 : term) (na : name) (b a a' res : term),
      eval Σ f0 (tLambda na b) →
      P f0 (tLambda na b)
         → eval Σ a a'
           → P a a'
             → eval Σ (ECSubst.csubst a' 0 b) res
          → P (ECSubst.csubst a' 0 b) res → P' (tApp f0 a) res)
    → (∀ (na : name) (b0 b0' b1 res : term),
         eval Σ b0 b0'
         → P b0 b0'
         -> isEtaExp Σ b1
         -> Q 1 b1
           → eval Σ (ECSubst.csubst b0' 0 b1) res
             → P (ECSubst.csubst b0' 0 b1) res →
             P' (tLetIn na b0 b1) res)
      → (∀ (ind : inductive) (pars : nat) cdecl (discr : term)
           (c : nat) (args : list term) (brs :
                                              list
                                                (list name × term))
           (br : list name × term) (res : term),
           forallb (λ x : list name × term, isEtaExp Σ x.2) brs ->
           eval Σ discr (mkApps (tConstruct ind c []) args)
           → P discr (mkApps (tConstruct ind c []) args)
           → constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl)
               → nth_error brs c = Some br
               → #|args| = pars + cdecl.(cstr_nargs)
                 → #|skipn pars args| = #|br.1|
                 -> Q #|br.1| br.2
                   → eval Σ (iota_red pars args br) res
                     → P (iota_red pars args br) res
                       → P' (tCase (ind, pars) discr brs) res)
        → (∀ (ind : inductive) (pars : nat) (discr : term)
             (brs : list (list name × term))
             (n : list name) (f3 res : term),
             with_prop_case
             → eval Σ discr tBox
               → P discr tBox
                 → inductive_isprop_and_pars Σ ind = Some (true, pars)
                   → brs = [(n, f3)]
                   -> forallb (isEtaExp Σ ∘ snd) brs
                   -> Q #|n| f3
                     → eval Σ (ECSubst.substl (repeat tBox #|n|) f3)
                         res
                       → P (ECSubst.substl (repeat tBox #|n|) f3) res
                         → P' (tCase (ind, pars) discr brs) res)
          → (∀ (f4 : term) (mfix : mfixpoint term)
               (idx : nat) (argsv : list term)
               (a av fn res : term),
               with_guarded_fix ->
               eval Σ f4 (mkApps (tFix mfix idx) argsv)
               → P f4 (mkApps (tFix mfix idx) argsv)
                 → eval Σ a av
                   → P a av
                     → cunfold_fix mfix idx = Some (#|argsv|, fn)
                     -> isEtaExp Σ fn
                     -> Q 0 fn
                      → eval Σ (tApp (mkApps fn argsv) av) res
                         → P (tApp (mkApps fn argsv) av) res
                           → P' (tApp f4 a) res)
            → (∀ (f5 : term) (mfix : mfixpoint term)
                 (idx : nat) (argsv : list term)
                 (a av : term) (narg : nat) (fn : term),
                 with_guarded_fix ->
                 eval Σ f5 (mkApps (tFix mfix idx) argsv)
                 → P f5 (mkApps (tFix mfix idx) argsv)
                   → eval Σ a av
                     → P a av
                       → cunfold_fix mfix idx = Some (narg, fn)
                         → #|argsv| < narg
                         -> isEtaExp Σ (tApp (mkApps (tFix mfix idx) argsv) av)
                           → P' (tApp f5 a)
                               (tApp
                                  (mkApps (tFix mfix idx) argsv) av))
            → (∀ (f5 : term) (mfix : mfixpoint term)
            (idx : nat) (a av : term) (narg : nat) (fn : term) res,
            with_guarded_fix = false ->
            eval Σ f5 (tFix mfix idx)
            → P f5 (tFix mfix idx)
              → cunfold_fix mfix idx = Some (narg, fn)
              -> isEtaExp Σ fn
              -> eval Σ a av -> P a av
              → eval Σ (tApp fn av) res
              → P (tApp fn av) res
              -> isEtaExp Σ (tApp f5 a)
              → P' (tApp f5 a) res) →

              (∀ (ip : inductive × nat) (mfix : mfixpoint term)
                   (idx : nat) (args : list term)
                   (narg : nat) discr (fn : term) (brs :
                                                 list
                                                 (list name × term))
                   (res : term),
                   cunfold_cofix mfix idx = Some (narg, fn)
                   -> isEtaExp Σ fn
                   -> forallb (isEtaExp Σ) args
                   -> eval Σ discr (mkApps (tCoFix mfix idx) args)
                   -> P discr (mkApps (tCoFix mfix idx) args)
                   -> forallb (isEtaExp Σ ∘ snd) brs
                   → eval Σ (tCase ip (mkApps fn args) brs) res
                     → P (tCase ip (mkApps fn args) brs) res
                       → P'
                           (tCase ip discr brs)
                           res)
                → (∀ (p : projection) (mfix : mfixpoint term)
                     (idx : nat) (args : list term)
                     (narg : nat) discr (fn res : term),
                     has_tProj ->
                     cunfold_cofix mfix idx = Some (narg, fn)
                     -> isEtaExp Σ fn
                     -> forallb (isEtaExp Σ) args
                     -> eval Σ discr (mkApps (tCoFix mfix idx) args)
                     -> P discr (mkApps (tCoFix mfix idx) args)
                     → eval Σ (tProj p (mkApps fn args)) res
                       → P (tProj p (mkApps fn args)) res
                         → P'
                             (tProj p discr) res)
                  → (∀ (c : kername) (decl : constant_body)
                       (body : term),
                       declared_constant Σ c decl
                       → ∀ res : term,
                           cst_body decl = Some body
                           → eval Σ body res
                             → P body res → P' (tConst c) res)
                    → (∀ p cdecl (discr : term) (args : list term) a (res : term),
                         has_tProj ->
                         eval Σ discr
                           (mkApps (tConstruct p.(proj_ind) 0 []) args)
                         → P discr (mkApps (tConstruct p.(proj_ind) 0 []) args)
                         → constructor_isprop_pars_decl Σ p.(proj_ind) 0 = Some (false, p.(proj_npars), cdecl)
                         → #|args| = p.(proj_npars) + cdecl.(cstr_nargs)
                         -> nth_error args (p.(proj_npars) + p.(proj_arg)) = Some a
                         -> eval Σ a res
                         → P a res
                         → P' (tProj p discr) res)
                      → (∀ p (discr : term),
                           has_tProj ->
                           with_prop_case
                           → eval Σ discr tBox
                             → P discr tBox
                               → inductive_isprop_and_pars Σ p.(proj_ind) = Some (true, p.(proj_npars))
                                 → P' (tProj p discr) tBox) →
  (∀ (f11 f' : term) a a',
     forall (ev : eval Σ f11 f'),
     P f11 f' ->
     (forall t u (ev' : eval Σ t u), eval_depth ev' <= eval_depth ev -> Q 0 t -> isEtaExp Σ t -> P t u) →
     ~~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f' || isConstructApp f' ||
      isPrimApp f' || isLazyApp f') →
     eval Σ a a' → P a a' →
     isEtaExp Σ (tApp f' a') ->
     P' (tApp f11 a) (tApp f' a')) →
  (∀ ind i mdecl idecl cdecl args args',
    lookup_constructor Σ ind i = Some (mdecl, idecl, cdecl) ->
    #|args| = cstr_arity mdecl cdecl ->
    All2 (eval Σ) args args' ->
    isEtaExp_app Σ ind i #|args| ->
    Q 0 (mkApps (tConstruct ind i []) args) ->
    Q 0 (mkApps (tConstruct ind i []) args') ->
    All2 P args args' ->
    P' (mkApps (tConstruct ind i []) args) (mkApps (tConstruct ind i []) args')) →

  (forall p p' (ev : eval_primitive (eval Σ) p p'),
    eval_primitive_ind _ (fun x y _ => P x y) _ _ ev ->
    P' (tPrim p) (tPrim p')) ->

  (forall t t' v, eval Σ t (tLazy t') -> eval Σ t' v ->
    P t (tLazy t') ->
    P t' v ->
    P' (tForce t) v) ->

  (∀ t : term, atom Σ t → Q 0 t -> isEtaExp Σ t -> P' t t) ->
  ∀ (t t0 : term), Q 0 t -> isEtaExp Σ t -> eval Σ t t0 → P' t t0.
Proof.
  intros wfl hcon. intros * Qpres P P'Q etaΣ wfΣ hasapp.
  assert (qfixs: Qfixs Q) by tc.
  assert (qcofixs: Qcofixs Q) by tc.
  intros.
  enough (P' t t0 × isEtaExp Σ t0). apply X18.
  pose proof (p := @Fix_F { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  specialize (p (MR lt (fun x => eval_depth x.π2.π2.π2))).
  set(foo := existT _ t (existT _ t0 (existT _ X17 H0)) :  { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  move: H.
  change t with (projT1 foo).
  change t0 with (projT1 (projT2 foo)).
  change H0 with (projT2 (projT2 foo)).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p.
  2:{ apply p. apply measure_wf, lt_wf. }
  clear p.
  rename X17 into qt. rename X13 into Xcappexp.
  rename X14 into Qprim. rename X15 into Qforce.
  rename X16 into Qatom.
  clear t t0 qt H0.
  intros (t & t0 & qt & ev).
  intros IH.
  set (IH' t t0 q H := IH (t; t0; q; H)). clearbody IH'; clear IH; rename IH' into IH.
  Opaque isEtaExp.
  cbn in IH. unfold MR in IH; cbn in IH. cbn.
  Ltac ih :=
    match goal with
    [ IH : forall x y, ?Q 0 x -> _ |- _ ] => unshelve eapply IH; tea; cbn; try lia
    end.
  Ltac iheta e :=
    match goal with
    [ IH : forall x y, ?Q 0 x -> _ |- _ ] => unshelve eapply (IH _ _ e); tea; cbn; try lia
    end.
  Ltac hp' P'Q := intros [hp' heta]; repeat split => //; try eapply P'Q; tea.
  assert (and_assum : forall x y, (P' x y × isEtaExp Σ y) ->
    ((P' x y × isEtaExp Σ y) -> Q 0 x × Q 0 y × isEtaExp Σ x) ->
    P x y).
  { intuition auto. red. intuition auto. }
  Ltac ih' P'Q :=
    match goal with
    | [ H : _, IH : forall x y, ?Q 0 x -> _ |- _ ] =>
      eapply H; tea; (apply and_assum; [ih|hp' P'Q])
    end.
  destruct ev.
  1-19:eapply qpres in qt as qt'; depelim qt' => //.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] /andP[] etaind etaargs bargs. destruct block_args; inv bargs.
      clear IH; rewrite ha in ev1. exfalso.
      eapply eval_mkApps_Construct_inv in ev1 as [ex []]. solve_discr. auto.
    * move=> /and4P [] etat0 etaargs etaa etat.
      split. eapply X; tea; (apply and_assum; [ih|hp' P'Q]).
      iheta q.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] /andP[] etaind etaargs bargs. destruct block_args; inv bargs.
      clear IH; rewrite ha in ev1. exfalso.
      eapply eval_mkApps_Construct_inv in ev1 as [ex []]. solve_discr. auto.
    * move=> /and4P [] etat0 etaargs etaa etat.
      assert (ql : Q 0 (tLambda na b)).
      { eapply P'Q; tea. ih. }
       assert (qs: Q 0 (csubst a' 0 b)).
      { eapply qpres in ql. depelim ql => //.
        eapply (qsubst b [a']) in q1. now cbn in q1.
        repeat constructor.
        eapply P'Q; tea; ih. }
      assert (isEtaExp Σ (csubst a' 0 b)).
      { eapply etaExp_csubst; tea. cbn in IH. specialize (IH _ _ q0 ev2). apply IH; [lia|auto].
        specialize (IH _ _ q ev1). forward IH by cbn; lia.
        forward IH by auto. destruct IH as [_ eta]. now simp_eta in eta. }
      split. eapply X0; tea. 1-3:(apply and_assum; [ih|hp' P'Q]).
      iheta qs.
  - simp_eta. move=> /andP[etab0 etab1].
    assert (qs : Q 0 (csubst b0' 0 b1)).
    { eapply (qsubst b1 [b0']) in q0. now cbn in q0.
      repeat constructor.
      eapply P'Q; tea; ih. }
    assert (isEtaExp Σ (csubst b0' 0 b1)).
    { eapply etaExp_csubst; tea. iheta q. }
    split; [eapply X1; tea|]. 1-2:(apply and_assum; [ih|hp' P'Q]).
    iheta qs.
  - simp_eta. move=> /andP[etad etabrs].
    assert (isEtaExp Σ (iota_red pars args br)).
    { eapply isEtaExp_iota_red.
      assert (isEtaExp Σ (mkApps (tConstruct ind c []) args)) by iheta q.
      rewrite isEtaExp_mkApps_napp /= // in H. rewrite andb_true_r in H.
      now move/andP: H => [].
      now clear IH; eapply nth_error_forallb in e1; tea. }
    assert (Q 0 (iota_red pars args br)).
    { unfold iota_red.
      eapply nth_error_all in a; tea. cbn in a.
      rewrite -e3 in a.
      rewrite -(List.length_rev (skipn pars args)) in a.
      rewrite Nat.add_0_r in a.
      eapply (qsubst _ (List.rev (skipn pars args))) in a.
      2:{ eapply All_rev, All_skipn.
        assert (Q 0 (mkApps (tConstruct ind c []) args)).
        eapply P'Q; tea; ih.
        eapply qapp in X13; tea. eapply X13. }
      exact a. }
    split. eapply X2; tea. 1,3:(apply and_assum; [ih|hp' P'Q]).
    eapply nth_error_all in a; tea; cbn. now rewrite Nat.add_0_r in a.
    iheta X13.
  - congruence.
  - simp_eta; move=> /andP[etad etabrs].
    assert (isEtaExp Σ (substl (repeat tBox #|n|) f)).
    { eapply isEtaExp_substl => //. rewrite forallb_repeat //.
      rewrite e0 /= in etabrs. now move/andP: etabrs. }
    assert (Q 0 (substl (repeat tBox #|n|) f)).
    { subst brs. eapply All_tip in a. cbn in a.
      rewrite -(repeat_length tBox #|n|) Nat.add_0_r in a.
      eapply (qsubst _ (repeat tBox #|n|)) in a => //.
      eapply All_repeat. eapply P'Q; tea; ih. }
   split. eapply X3; tea. 1,3:(apply and_assum; [ih|hp' P'Q]).
   subst brs.  depelim a. now rewrite Nat.add_0_r in q0.
   iheta X13.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] /andP[] etaind etaargs bargs. destruct block_args; inv bargs.
      clear IH; rewrite ha in ev1. exfalso.
      eapply eval_mkApps_Construct_inv in ev1 as [ex []]. solve_discr. auto.
    * move=> /and4P [] etat0 etaargs etaa etat.
      pose proof (ev1' := ev1). eapply P'Q in ev1' => //. 2:{ clear ev1'; ih. }
      eapply qapp in ev1' as [hfix qargs] => //.
      assert (hastfix : has_tFix).
      { eapply qpres in hfix. now depelim hfix. }
      assert (qf : Q 0 fn).
      { eapply (qfixs mfix idx) in hfix; tea. }
      assert (qa : Q 0 (tApp (mkApps fn argsv) av)).
      { rewrite -[tApp _ _](mkApps_app _ _ [av]).
        unshelve eapply (qapp _ _ _ _).2; auto.
        split => //.
        eapply (qfixs mfix idx) in hfix; tea.
        eapply All_app_inv => //. eapply All_tip.1.
        eapply P'Q; tea; ih. }
      assert (etaapp : isEtaExp Σ fn × isEtaExp Σ (tApp (mkApps fn argsv) av)).
      { rewrite -[tApp _ _](mkApps_app _ _ [av]).
        assert (efix : isEtaExp Σ (mkApps (tFix mfix idx) argsv)) by iheta q.
        rewrite isEtaExp_mkApps_napp /= // in efix.
        move/andP: efix => [efix hargs].
        apply MRProd.and_assum.
        eapply isEtaExp_cunfold_fix. now simp_eta in efix. exact e.
        intros hfn.
        eapply isEtaExp_mkApps_intro => //.
        eapply All_app_inv. now eapply forallb_All in hargs. eapply (fst All_tip).
        iheta q0. }
      destruct etaapp as [etafn etafnapp].
      split. eapply X4; tea. 1-3:(apply and_assum; [ih|hp' P'Q]).
      iheta qa.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] /andP[] etaind etaargs bargs. destruct block_args; inv bargs.
      clear IH; rewrite ha in ev1. exfalso.
      eapply eval_mkApps_Construct_inv in ev1 as [ex []]. solve_discr. auto.
    * move=> /and4P [] etat0 etaargs etaa etat.
      assert (isEtaExp Σ (tApp (mkApps (tFix mfix idx) argsv) av)).
      { rewrite -[tApp _ _](mkApps_app _ _ [av]).
        rewrite isEtaExp_mkApps_napp // /=.
        assert (isEtaExp Σ (mkApps (tFix mfix idx) argsv)) by iheta q.
        assert (isEtaExp Σ av) by iheta q0.
        rewrite isEtaExp_mkApps_napp // /= in H.
        move/andP: H => [] -> /=.
        rewrite forallb_app /= H0 => -> /= //. }
      split => //. eapply X5; tea; (apply and_assum; [ih|hp' P'Q]).
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] /andP[] etaind etaargs bargs. destruct block_args; inv bargs.
      clear IH; rewrite ha in ev1. exfalso.
      eapply eval_mkApps_Construct_inv in ev1 as [ex []]. solve_discr. auto.
    * move=> /and4P [] etat0 etaargs etaa etat.
      assert (qav : Q 0 av).
      { eapply P'Q; tea; ih. }
      assert (qa : Q 0 (tApp fn av)).
      { pose proof (ev1' := ev1). eapply P'Q in ev1' => //. 2:clear ev1'; ih.
        eapply qfixs in ev1'. cbn in IH. eapply ev1' in e.
        unshelve eapply (qapp _ _ _ [av]); tea; split => //. now eapply All_tip.1. }
      assert (etafn : isEtaExp Σ fn).
      { assert (hfix : isEtaExp Σ (tFix mfix idx)) by iheta q.
        eapply isEtaExp_cunfold_fix. now simp_eta in hfix. exact e. }
      assert (etaav : isEtaExp Σ av).
      { iheta q0. }
      assert (etaapp : isEtaExp Σ (tApp fn av)).
      { change (isEtaExp Σ (mkApps fn [av])).
        eapply isEtaExp_mkApps_intro => //.
        now eapply All_tip.1. }
      split. eapply X6; tea. 1-3:(apply and_assum; [ih|hp' P'Q]).
      rewrite (decompose_app_inv da). eapply isEtaExp_mkApps_intro => //.
      now eapply forallb_All in etaargs.
      iheta qa.
  - simp_eta. move=> /andP[etad etabrs].
    assert (qa : Q 0 (tCase ip (mkApps fn args) brs)).
    { eapply qcase; tea => //.
      pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [hfix qargs] => //.
      eapply qapp => //. split => //.
      eapply (qcofixs mfix idx) in hfix; tea.
      clear ev1'; ih. }
    assert (etafn : isEtaExp Σ fn && forallb (isEtaExp Σ) args).
    { assert (hfix : isEtaExp Σ (mkApps (tCoFix mfix idx) args)) by iheta q.
      rewrite isEtaExp_mkApps_napp /= // in hfix.
      move/andP: hfix => [hfix hargs].
      apply/andP; split => //.
      eapply isEtaExp_cunfold_cofix. now simp_eta in hfix. exact e. }
    move/andP: etafn => [] etaf etaargs.
    assert (etac : isEtaExp Σ (tCase ip (mkApps fn args) brs)).
    { simp_eta. rewrite etabrs andb_true_r.
      eapply isEtaExp_mkApps_intro => //.
      now eapply forallb_All in etaargs. }
    split. eapply X7; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta qa.
  - simp_eta. move=> etad.
    cbn in IH.
    assert (qa : Q 0 (tProj p (mkApps fn args))).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [hfix ?] => //.
      eapply qproj; tea => //. eapply qapp => //. split => //.
      eapply (qcofixs mfix idx) in hfix; tea.
      clear ev1'; ih. }
    assert (etafn : isEtaExp Σ fn && forallb (isEtaExp Σ) args).
    { assert (hfix : isEtaExp Σ (mkApps (tCoFix mfix idx) args)) by iheta q.
      rewrite isEtaExp_mkApps_napp /= // in hfix.
      move/andP: hfix => [hfix hargs].
      apply/andP; split => //.
      eapply isEtaExp_cunfold_cofix. now simp_eta in hfix. exact e. }
    move/andP: etafn => [] etaf etaargs.
    assert (etaa : isEtaExp Σ (tProj p (mkApps fn args))).
    { simp_eta.
      eapply isEtaExp_mkApps_intro => //.
      now eapply forallb_All in etaargs. }
    split. eapply X8; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta qa.
  - move => _.
    assert (Q 0 body).
    { cbn in IH; eapply (qconst (Q:=Q)) in isdecl. now rewrite e in isdecl. }
    assert (isEtaExp Σ body).
    { eapply isEtaExp_lookup in etaΣ as etad; tea.
      unfold isEtaExp_decl, isEtaExp_constant_decl in etad.
      now rewrite e /= in etad. }
    split. eapply X9; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta X13.
  - simp_eta => etadiscr.
    assert (Q 0 a).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [_ qargs] => //.
      { eapply nth_error_all in qargs; tea. }
      clear ev1'; ih. }
    assert (isEtaExp Σ a).
    { assert (isEtaExp Σ (mkApps (tConstruct p.(proj_ind) 0 []) args)) by iheta q.
      move: H; simp_eta.
      rewrite isEtaExp_mkApps_napp // /=.
      move=> /andP[] /andP[] etaapp etaargs.
      eapply nth_error_forallb in etaargs; tea. eauto. }
    split. eapply X10; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta X13.
  - congruence.
  - simp_eta => etadiscr.
    split. unshelve eapply X11; tea; try (intros; apply and_assum; [ih|hp' P'Q]).
    now idtac.
  - move/isEtaExp_tApp.
    rename args into cargs.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] /andP[] etaind etaargs bargs. destruct block_args; inv bargs.
      assert (eval_depth ev1 = eval_depth ev1) by reflexivity.
      set (ev1' := ev1). change ev1 with ev1' in H at 1. clearbody ev1'. move: H.
      subst f.
      pose proof (eval_construct_size hcon ev1') as [ex []].
      cbn in IH. intros eq.
      assert (All2 (λ x y : term, ∑ ev' : eval Σ x y, eval_depth ev' < S (Nat.max (eval_depth ev1) (eval_depth ev2)))
        (remove_last args ++ [a]) (ex ++ [a'])).
      { eapply All2_app. eapply All2_impl; tea; cbn. intros ?? []. exists x0. lia.
        constructor; [|constructor]. exists ev2. lia. }
      assert (All (Q 0) (remove_last args ++ [a])).
      { eapply All_app_inv. eapply qapp in q as []; auto.
        now eapply All_tip.1. }
      assert (All (isEtaExp Σ) (remove_last args ++ [a])).
      { rewrite ht -(remove_last_last args a argsn). now eapply forallb_All. }
      eapply All2_All_mix_left in X15; tea.
      assert (All2 (fun x y => P' x y × isEtaExp Σ y) (remove_last args ++ [a]) (ex ++ [a'])).
      { clear X13. eapply All2_All_mix_left in X15; tea.
        eapply All2_impl; tea. cbn. intros ? ? [? [? [ev ?]]].
        eapply (IH _ _ q1 ev). lia. auto. }
      rewrite (remove_last_last args a argsn) in etaargs.
      rewrite -[tApp _ _](mkApps_app _ _ [a]).
      rewrite -[tApp _ _](mkApps_app _ _ [a']).
      assert (All (fun x => Q 0 x × isEtaExp Σ x) (ex ++ [a'])).
      { eapply All2_mix in X15; tea. cbn in X15.
        eapply All2_All_mix_left in X15. 2:exact X14.
        eapply All2_All_right; tea; cbn.
        intros ? ? [? [? [? []]]]. split. eapply P'Q; tea. apply p. apply p. }
      eapply mkApps_eq_inj in e1 as [] => //. subst ex. noconf H.
      split.
      unshelve eapply Xcappexp; tea.
      + rewrite ht -remove_last_last //.
        move: etaind; rewrite /isEtaExp_app.
        rewrite (lookup_constructor_pars_args_cstr_arity _ _ _ _ _ _ e0).
        move/Nat.leb_le. move: l. rewrite /cstr_arity.
        eapply All2_length in X13. move: X13.
        rewrite ht /= -remove_last_last //. len.
      + eapply All2_app. eapply All2_impl; tea. cbn. now intros ? ? [].
        constructor; [|constructor]. apply ev2.
      + rewrite ht. rewrite -remove_last_last //.
      + eapply qapp in q as []; auto.
        eapply qapp => //.
      + eapply qapp in q as [] => //. eapply qapp; auto. split => //.
        eapply All_impl; tea; cbn; intuition auto.
      + eapply All2_All_mix_left in X16; [|exact X14].
        eapply All2_All_mix_right in X16; [|exact X17].
        cbn in X16.
        eapply All2_mix in X16; [|exact X15].
        eapply All2_impl; tea; cbn.
        intros x y [? [[] ?]].
        red. intuition auto.
      + rewrite isEtaExp_Constructor.
        apply/andP. split. rewrite -(All2_length X16).
        rewrite ht -remove_last_last //.
        rtoProp. split. eauto.
        eapply All_forallb. eapply All_impl; tea. cbn; intuition auto. auto.
    * move=> /and4P [] etat0 etaargs etaa etat.
      rewrite -[tApp _ a'](mkApps_app _ _ [a']).
      assert (P' f (mkApps (tConstruct ind c []) cargs) × isEtaExp Σ (mkApps (tConstruct ind c []) cargs)).
      { unshelve eapply IH; tea. cbn. lia. }
      exfalso.
      destruct X13 as [p'f etac].
      move: etac. rewrite isEtaExp_Constructor.
      move/andP => []. rewrite /isEtaExp_app.
      rewrite /lookup_constructor_pars_args e0 /=.
      move => /andP[] /Nat.leb_le. clear IH. move: l; rewrite /cstr_arity. lia.
  - congruence.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] /andP[] etaind etaargs bargs. destruct block_args; inv bargs.
      assert (eval_depth ev1 = eval_depth ev1) by reflexivity.
      set (ev1' := ev1). change ev1 with ev1' in H at 1. clearbody ev1'. move: H.
      subst f. exfalso.
      eapply eval_mkApps_Construct_inv in ev1' as [? [hf' hargs']]. subst f'.
      clear IH; move: i; rewrite !negb_or isConstructApp_mkApps /= !andb_false_r //.  auto.
    * move=> /and4P [] etat0 etaargs etaa etat.
      split. eapply (X12 _ _ _ _ ev1); tea.
      1,3:(apply and_assum; [ih|hp' P'Q]).
      intros. apply and_assum; [ih|hp' P'Q].
      pose proof (decompose_app_inv da). clear cv.
      eapply (isEtaExp_mkApps_intro _ _ [a']) => //.
      iheta q.
      eapply All_tip.1. iheta q0.
      eapply (isEtaExp_mkApps_intro _ _ [a']) => //. iheta q.
      eapply All_tip.1. iheta q0.
  - intros ise. simp_eta in ise.
    depelim e.
    * split; simp_eta. unshelve eapply Qprim. constructor. constructor.
    * split; simp_eta. unshelve eapply Qprim. constructor. constructor.
    * split; simp_eta. unshelve eapply Qprim. constructor. constructor.
    * eapply Qpres in qt. depelim qt. now cbn in i.
      split; simp_eta. unshelve eapply Qprim. constructor; eauto. constructor.
      + apply All2_over_undep. cbn in IH.
        ELiftSubst.solve_all.
        depelim H0. destruct p as [[] a0].
        clear -ev IH a0 P'Q and_assum. cbn in a0. subst a; cbn in *.
        induction ev; constructor; eauto.
        ** depelim a0. destruct p as [? []].
           eapply and_assum. unshelve eapply IH; tea. cbn. lia.
           intros []. split => //. split => //. eapply P'Q; tea.
        ** depelim a0. intuition eauto. eapply IHev; intros. 2:eauto.
           unshelve eapply IH; tea. cbn; lia.
      + ELiftSubst.solve_all. depelim H0. destruct p as [[? []] ?].
        eapply and_assum. unshelve eapply IH; tea. cbn; lia.
        intros []; split => //; split => //. eapply P'Q; tea.
      + ELiftSubst.solve_all. subst a a'; cbn in *.
        depelim H0; constructor; cbn in *; intuition eauto.
        unshelve eapply IH. 2:tea. all:eauto. cbn; lia.
        clear -ev IH b P'Q and_assum. cbn in b.
        induction ev; constructor; eauto.
        ** depelim b. destruct p as [? []]. unshelve eapply IH. 2:tea. all:eauto. cbn. lia.
        ** depelim b. intuition eauto. eapply IHev; intros. 2:eauto.
           unshelve eapply IH; tea. cbn; lia.
  - simp_eta => ise.
    eapply Qpres in qt. depelim qt => //.
    assert (Q 0 (tLazy v)).
    { eapply P'Q; tea. eapply (IH _ _ q ev1); tea. now cbn; lia. }
    eapply qpres in X13. depelim X13 => //.
    assert (isEtaExp Σ (tLazy v)) as etav.
    { eapply (IH _ _ q ev1); tea. now cbn; lia. }
    simp_eta in etav.
    split.
    + unshelve eapply Qforce. 2:tea. auto.
      eapply and_assum. eapply (IH _ _ q ev1); tea. now cbn; lia.
      intros []. split => //. split => //. eapply P'Q; tea.
      pose proof (IH _ _ q ev1). forward X13. cbn; lia. specialize (X13 ise) as [].
      eapply and_assum. eapply (IH _ _ q0 ev2); tea. now cbn; lia.
      now simp_eta in i1.
    + eapply (IH _ _ q0 ev2) => //. now cbn; lia.
  - intros ise. split => //. eapply Qatom; tea.
Qed.

From MetaRocq.Erasure Require Import ELiftSubst.
Lemma Qpreserves_wellformed (efl : EEnvFlags) Σ :
  cstr_as_blocks = false ->
  wf_glob Σ -> Qpreserves (fun n x => wellformed Σ n x) Σ.
Proof.
  intros cstbl clΣ.
  split.
  - red. move=> n t.
    destruct t; cbn [wellformed]; rtoProp; intuition auto; try solve [constructor; auto].
    all:cbn; rtoProp; intuition auto.
    constructor; cbn => //.
    eapply on_evar; auto. solve_all.
    eapply on_lambda; auto.
    eapply on_letin; rtoProp; intuition auto.
    eapply on_app; rtoProp; intuition auto.
    constructor; cbn; auto. rewrite cstbl in H0.
    destruct args => //. constructor => //.
    eapply on_case; rtoProp; intuition auto. ELiftSubst.solve_all.
    eapply on_proj; auto.
    eapply on_fix; eauto. move/andP: H0 => [] _ wf. solve_all.
    eapply on_cofix; eauto. move/andP: H0 => [] _ wf. solve_all.
    eapply on_prim; eauto. solve_all.
    eapply on_lazy; eauto.
    eapply on_force; eauto.
  - red. intros kn decl.
    move/(lookup_env_wellformed clΣ).
    unfold wf_global_decl. destruct cst_body => //.
  - red. move=> hasapp n t args. rewrite wellformed_mkApps //.
    split; intros; rtoProp; intuition auto; solve_all.
  - red. intros. simpl in H0. simpl. rtoProp; intuition auto.
  - red. move=> hasproj n p discr. simpl; rtoProp; intuition auto.
  - red. move=> t args clt cll.
    eapply wellformed_substl. solve_all. now rewrite Nat.add_0_r.
  - red. move=> n mfix idx. cbn. unfold EWellformed.wf_fix.
    intros; rtoProp; intuition auto; solve_all. now apply Nat.ltb_lt.
  - red. move=> n mfix idx. cbn. unfold EWellformed.wf_fix.
    intros; rtoProp; intuition auto; solve_all. now apply Nat.ltb_lt.
Qed.

Ltac destruct_nary_times :=
  match goal with
  | [ H : _ × _ |- _ ] => destruct H
  | [ H : [× _, _ & _] |- _ ] => destruct H
  | [ H : [× _, _, _ & _] |- _ ] => destruct H
  | [ H : [× _, _, _, _ & _] |- _ ] => destruct H
  end.

Definition term_flags :=
  {|
    has_tBox := true;
    has_tRel := true;
    has_tVar := false;
    has_tEvar := false;
    has_tLambda := true;
    has_tLetIn := true;
    has_tApp := true;
    has_tConst := true;
    has_tConstruct := true;
    has_tCase := true;
    has_tProj := false;
    has_tFix := true;
    has_tCoFix := false;
    has_tPrim := all_primitive_flags;
    has_tLazy_Force := false;
  |}.

Definition env_flags :=
    {| has_axioms := false;
        has_cstr_params := false;
        term_switches := term_flags ;
        cstr_as_blocks := false
  |}.

Lemma eval_etaexp {fl : WcbvFlags} (efl := env_flags) {Σ a a'} :
  with_constructor_as_block = false ->
  isEtaExp_env Σ ->
  wf_glob Σ ->
  wellformed Σ 0 a ->
  eval Σ a a' -> isEtaExp Σ a -> isEtaExp Σ a'.
Proof.
  intros hcon etaΣ wfΣ wf ev eta.
  revert a a' wf eta ev.
  eapply (eval_preserve_mkApps_ind (efl:=env_flags) fl hcon Σ (fun _ x => isEtaExp Σ x) (fun n t => wellformed Σ n t)
    (Qpres := Qpreserves_wellformed env_flags Σ eq_refl wfΣ)) => //.
  all:intros; repeat destruct_nary_times.
  all:intuition auto.
  - eapply eval_wellformed; tea => //.
  - rewrite isEtaExp_Constructor => //.
    let X0 := multimatch goal with H : All2 _ _ _ |- _ => H end in
    let H1 := multimatch goal with H : _ = _ |- _ => H end in
    rewrite -(All2_length X0) H1. cbn. rtoProp; intuition eauto.
    match goal with H : ?f ?n |- ?f ?n' => replace n' with n by congruence; exact H end.
    cbn; eapply All_forallb. eapply All2_All_right; tea.
    cbn. intros x y []; auto.
  - depelim X;try constructor. destruct a0. simp_eta. subst a'. cbn.
    apply All2_over_undep in a.
    rewrite /test_array_model /=. rtoProp; intuition eauto. solve_all; now destruct H.
Qed.
