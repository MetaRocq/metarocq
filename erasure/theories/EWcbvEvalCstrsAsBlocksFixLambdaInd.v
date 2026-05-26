(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst EnvMap.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst EWcbvEval EGlobalEnv
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
  | tBox | tConst _ | tRel _ | tVar _ => true
  | _ => false
  end.

Definition has_atom {etfl : ETermFlags} (t : term) :=
  match t with
  | tBox => has_tBox
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
  | on_cstr i k args : has_tConstruct -> All (Q n) args -> on_subterms Q n (tConstruct i k args)
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

(* Class Qcstr {etfl : ETermFlags} (Q : nat -> term -> Type) := *)
  (* qcstr : has_tConstruct -> forall i n args, Q n (tConstruct i n args)   Q n discr × All (fun br => Q (#|br.1| + n) br.2) brs. *)
(* #[export] Hint Mode Qcase - ! : typeclass_instances. *)

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

Lemma eval_beta_inv {wfl : WcbvFlags} Σ t a v :
  isLambda t ->
  forall ev : eval Σ (tApp t a) v,
  match ev with
  | eval_beta _ _ _ _ _ _ ev' _ _ => match ev' with
                                     | eval_atom _ _ => True
                                     | _ => False
                                     end
  | _ => False
  end.
Proof.
  intros H; destruct t; invs H.
  intros ev. depelim ev.
  - depelim ev1.
  - depelim ev1; eauto.
  - depelim ev1;
    eapply (f_equal head) in H; rewrite head_mkApps in H; cbn in H;
    congruence.
  - depelim ev1;
    eapply (f_equal head) in H; rewrite head_mkApps in H; cbn in H;
    congruence.
  - depelim ev1;
    eapply (f_equal head) in H; rewrite head_mkApps in H; cbn in H;
    congruence.
  - depelim ev1;
    eapply (f_equal head) in H; rewrite head_mkApps in H; cbn in H;
    congruence.
  - depelim ev1. cbn in *. eauto.
  - invs i.
Qed.

Lemma eval_preserve_mkApps_ind :
∀ (wfl : WcbvFlags), with_constructor_as_block = true -> forall  {efl : EEnvFlags} (Σ : global_declarations)
  (P' : term → term → Type)
  (Q : nat -> term -> Type)
  {Qpres : Qpreserves Q Σ}
  (P := (fun x y => [× P' x y, Q 0 x & Q 0 y])%type)
  (HPQ : ∀ t u, eval Σ t u -> Q 0 t -> P' t u -> Q 0 u)
  (Qwf : forall n t, Q n t -> wellformed Σ n t),
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
         -> Q 1 b1
           → eval Σ (ECSubst.csubst b0' 0 b1) res
             → P (ECSubst.csubst b0' 0 b1) res →
             P' (tLetIn na b0 b1) res)
      → (∀ (ind : inductive) (pars : nat) cdecl (discr : term)
           (c : nat) (args : list term) (brs :
                                              list
                                                (list name × term))
           (br : list name × term) (res : term),
           eval Σ discr (tConstruct ind c args)
           → P discr (tConstruct ind c args)
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
                   -> Q #|n| f3
                     → eval Σ (ECSubst.substl (repeat tBox #|n|) f3)
                         res
                       → P (ECSubst.substl (repeat tBox #|n|) f3) res
                         → P' (tCase (ind, pars) discr brs) res)
          → (∀ (f4 : term) (mfix : mfixpoint term)
               (idx : nat) (argsv : list term)
               (a av fn res : term),
               with_guarded_fix = true ->
               eval Σ f4 (mkApps (tFix mfix idx) argsv)
               → P f4 (mkApps (tFix mfix idx) argsv)
                 → eval Σ a av
                   → P a av
                     → cunfold_fix mfix idx = Some (#|argsv|, fn)
                     -> Q 0 fn
                      → eval Σ (tApp (mkApps fn argsv) av) res
                         → P (tApp (mkApps fn argsv) av) res
                           → P' (tApp f4 a) res)
            → (∀ (f5 : term) (mfix : mfixpoint term)
                 (idx : nat) (argsv : list term)
                 (a av : term) (narg : nat) (fn : term),
                 with_guarded_fix = true ->
                 eval Σ f5 (mkApps (tFix mfix idx) argsv)
                 → P f5 (mkApps (tFix mfix idx) argsv)
                   → eval Σ a av
                     → P a av
                       → cunfold_fix mfix idx = Some (narg, fn)
                         → #|argsv| < narg
                           → P' (tApp f5 a)
                               (tApp
                                  (mkApps (tFix mfix idx) argsv) av))
            → (forall t, P' t t -> P' t t) ->

          (∀ (f5 : term) (mfix : mfixpoint term)
            (idx : nat) (a av : term) (narg : nat) (fn : term) na d res,
            with_guarded_fix = false ->
            eval Σ f5 (tFix mfix idx)
            → P f5 (tFix mfix idx)
              → nth_error mfix idx = Some d
              -> d.(dbody) = tLambda na fn
              -> eval Σ a av -> P a av
              → eval Σ (substl (av :: fix_subst mfix) fn) res
              → P (substl (av :: fix_subst mfix) fn) res
              → P' (tApp f5 a) res) →

              (∀ (ip : inductive × nat) (mfix : mfixpoint term)
                   (idx : nat) (args : list term)
                   (narg : nat) discr (fn : term) (brs :
                                                 list
                                                 (list name × term))
                   (res : term),
                   cunfold_cofix mfix idx = Some (narg, fn)
                   -> eval Σ discr (mkApps (tCoFix mfix idx) args)
                   -> P discr (mkApps (tCoFix mfix idx) args)
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
                         eval Σ discr (tConstruct p.(proj_ind) 0 args)
                         → P discr (tConstruct p.(proj_ind) 0 args)
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
     (forall t u (ev' : eval Σ t u), eval_depth ev' <= eval_depth ev -> Q 0 t -> P t u) →
     ~~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f'
      || isConstructApp f' || isPrimApp f' || isLazyApp f') →
     eval Σ a a' → P a a' →
     P' (tApp f11 a) (tApp f' a')) →
  (∀ ind i mdecl idecl cdecl args args',
    lookup_constructor Σ ind i = Some (mdecl, idecl, cdecl) ->
    #|args| = cstr_arity mdecl cdecl ->
    All2 (eval Σ) args args' ->
    All2 P args args' ->
    P' (tConstruct ind i args) (tConstruct ind i args')) →


  (forall p p' (ev : eval_primitive (eval Σ) p p'),
    eval_primitive_ind _ (fun x y _ => P x y) _ _ ev ->
    P' (tPrim p) (tPrim p')) ->

  (forall t t' v, eval Σ t (tLazy t') -> eval Σ t' v ->
    P t (tLazy t') ->
    P t' v ->
    P' (tForce t) v) ->

  (∀ t : term, atom Σ t → Q 0 t -> P' t t) ->
  ∀ (t t0 : term), Q 0 t -> eval Σ t t0 → P' t t0.
Proof.
  Arguments substl : simpl never.
  intros wfl hcon. intros * Qpres P P'Q Qwf wfΣ hasapp.
  assert (qfixs: Qfixs Q) by tc.
  assert (qcofixs: Qcofixs Q) by tc.
  intros.
  pose proof (p := @Fix_F { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  specialize (p (MR lt (fun x => eval_depth x.π2.π2.π2))).
  set(foo := existT _ t (existT _ t0 (existT _ X18 H)) :  { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  change t with (projT1 foo).
  change t0 with (projT1 (projT2 foo)).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p.
  2:{ apply p. apply measure_wf, lt_wf. }
  clear p.
  rename X18 into qt. rename X14 into Xcappexp.
  rename X15 into Qprim, X16 into Qforce, X17 into Qatom.
  clear t t0 qt H.
  intros (t & t0 & qt & ev).
  intros IH.
  set (IH' t t0 q H := IH (t; t0; q; H)). clearbody IH'; clear IH; rename IH' into IH.
  cbn in IH. unfold MR in IH; cbn in IH. cbn.
  Ltac ih :=
    match goal with
    [ IH : forall x y, ?Q 0 x -> _ |- _ ] => unshelve eapply IH; tea; cbn; try lia
    end.
  Ltac hp' P'Q := intros ?; repeat split => //; try eapply P'Q; tea.
  assert (and_assum : forall x y, P' x y ->
    ((P' x y) -> Q 0 x × Q 0 y) ->
    P x y).
  { intuition auto. red. intuition auto. }
  Ltac ih' P'Q :=
    match goal with
    | [ H : _, IH : forall x y, ?Q 0 x -> _ |- _ ] =>
      eapply H; tea; (apply and_assum; [ih|hp' P'Q])
    end.
  Ltac myt hyp anda P'Q := eapply hyp; tea; (apply and_assum; [ih|hp' P'Q]).

  destruct ev.
  1-19:eapply qpres in qt as qt'; depelim qt' => //.
  all:try now (cbn in *; congruence).
  - eapply X; tea; (apply and_assum; [ih|hp' P'Q]).
  - assert (ql : Q 0 (tLambda na b)).
    { eapply P'Q; tea. ih. }
    assert (qs: Q 0 (csubst a' 0 b)).
    { eapply qpres in ql. depelim ql => //.
      eapply (qsubst b [a']) in q1. now cbn in q1.
      repeat constructor.
      eapply P'Q; tea; ih. }
    eapply X0; tea; (apply and_assum; [ih|hp' P'Q]).
  - assert (qs : Q 0 (csubst b0' 0 b1)).
    { eapply (qsubst b1 [b0']) in q0. now cbn in q0.
      repeat constructor.
      eapply P'Q; tea; ih. }
    eapply X1; tea; (apply and_assum; [ih|hp' P'Q]).
  - assert (Q 0 (iota_red pars args br)).
    { unfold iota_red.
      eapply nth_error_all in a; tea. cbn in a.
      rewrite -e3 in a.
      rewrite -(List.length_rev (skipn pars args)) in a.
      rewrite Nat.add_0_r in a.
      eapply (qsubst _ (List.rev (skipn pars args))) in a.
      2:{ eapply All_rev, All_skipn.
        assert (Q 0 (tConstruct ind c args)).
        eapply P'Q; tea; ih. eapply qpres in X14.
        depelim X14 => //. }
      exact a. }
    eapply nth_error_all in a; tea; cbn. rewrite Nat.add_0_r in a.
    eapply X2; tea; (apply and_assum; [ih|hp' P'Q]).
  - assert (Q 0 (substl (repeat tBox #|n|) f)).
    { subst brs. eapply All_tip in a. cbn in a.
      rewrite -(repeat_length tBox #|n|) Nat.add_0_r in a.
      eapply (qsubst _ (repeat tBox #|n|)) in a => //.
      eapply All_repeat. eapply P'Q; tea; ih. }
   eapply X3; tea. 1,3:(apply and_assum; [ih|hp' P'Q]).
   subst brs. depelim a. now rewrite Nat.add_0_r in q0.
  - pose proof (ev1' := ev1). eapply P'Q in ev1' => //. 2:{ clear ev1'; ih. }
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
    eapply X4; tea. 1-3:(apply and_assum; [ih|hp' P'Q]).
  - eapply X5; tea; (apply and_assum; [ih|hp' P'Q]).
  - clear X6. assert (qav : Q 0 av).
    { eapply P'Q; tea; ih. }
    assert (qa : Q 0 (tApp fn av)).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //. 2:clear ev1'; ih.
      eapply qfixs in ev1'. cbn in IH. eapply ev1' in e.
      unshelve eapply (qapp _ _ _ [av]); tea; split => //. now eapply All_tip.1. }
    assert (qf : Q 0 (tFix mfix idx)).
    { pose (ev1' := ev1). unshelve eapply P'Q in ev1' => //.
      ih. unfold ev1'. lia. }

      (*
         - we use a fix rule which knows that bodies of fixpoints are lambdas and intermediately substitutes
         - named fix rule does the same
         - if we keep the tApp, the argument is in the wrong environment. that's not a problem per se, but because Malfunction dumps the full env (and not only the bound variables from the env) into closures, this is a problem: we get only related, not the same closures
         - like this, the proof to named is easy
         - we need to prove the transformation here though: here we have a strong induction lemma which allows us to get an IH after inverting the beta rule used
         - in the step to malfunction, we need two malfunction rules to simulate: first beta, and then the let rec rule for the left side.
           the IH with the substituted thing is then exactly what is needed
         - we need to assume here that Q on tFix implies that the bodies are lambdas - just in this file
         - instantiating Q with wellformed will enforce that
      *)

    pose proof e as e'. unfold cunfold_fix in e'.
    destruct (nth_error mfix idx) eqn:E; invs e'.


    eapply Qwf in qf as wfix.
    cbn in wfix. rtoProp.
    unfold wf_fix in H0. rtoProp.
    solve_all.

    eapply All_nth_error in H2 as Hnth. 2: exact E.
    destruct Hnth as [H1 Hnth].
    destruct d; cbn in *; destruct dbody; invs H1.

    unshelve epose proof (eval_beta_inv _ _ _ _ _ ev3).
    { rewrite substl_subst.
      eapply closed_fix_subst; solve_all; destruct x; cbn; eapply wellformed_closed; eauto.
      cbn; eauto.
    }
    depelim ev3; try now tauto. clear H1.
    assert (qsubstl : Q 0 (substl (av :: fix_subst mfix) dbody)).
    { eapply qsubst. 2:{ econstructor. eauto. eapply Qfix_subst; tea. eapply qpres_qfix. eapply qpres_qpres. eapply nth_error_Some_length; eauto. }
      eapply qpres in qf. depelim qf. cbn in *. eauto.
      eapply All_nth_error in a0; eauto.
      cbn in a0. eapply qpres  in a0. depelim a0. cbn in *. eauto. cbn. rewrite Nat.add_0_r in q1. now rewrite fix_subst_length.
    }

    cbn in IH.

    revert IH.
    revert ev3_1.
    rewrite substl_subst. { eapply Qwf, wellformed_closed in qf as Hwf. cbn in Hwf. now eapply closed_fix_subst. }
    intros ev3_1 IH. depelim ev3_1.

    assert (a' = av) as ->. { eapply eval_deterministic; eauto. eapply value_final. eapply eval_to_value; eauto. }
    revert ev3_3 IH.
    rewrite closed_subst. now eapply Qwf, wellformed_closed in qav.
    rewrite -(subst_app_simpl [_]).
    rewrite -(substl_subst). cbn. rtoProp. split. now eapply Qwf, wellformed_closed in qav. eapply Qwf, wellformed_closed in qf as Hwf. cbn in Hwf. now eapply closed_fix_subst.

    intros ev3_3 IH.


    eapply X7; tea.
    2: cbn; reflexivity.
    { apply and_assum; [ ih | hp' P'Q]. }
    { apply and_assum; [ ih | hp' P'Q]. }

    apply and_assum; [ | hp' P'Q].
    unshelve eapply IH. eassumption. eassumption. cbn -[Nat.max]. lia.
  - assert (qa : Q 0 (tCase ip (mkApps fn args) brs)).
    { eapply qcase; tea => //.
      pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [hfix qargs] => //.
      eapply qapp => //. split => //.
      eapply (qcofixs mfix idx) in hfix; tea.
      clear ev1'; ih. }
    eapply X8; tea; (apply and_assum; [ih|hp' P'Q]).
  - cbn in IH.
    assert (qa : Q 0 (tProj p (mkApps fn args))).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [hfix ?] => //.
      eapply qproj; tea => //. eapply qapp => //. split => //.
      eapply (qcofixs mfix idx) in hfix; tea.
      clear ev1'; ih. }
    eapply X9; tea; (apply and_assum; [ih|hp' P'Q]).
  - assert (Q 0 body).
    { cbn in IH; eapply (qconst (Q:=Q)) in isdecl. now rewrite e in isdecl. }
    eapply X10; tea; (apply and_assum; [ih|hp' P'Q]).
  - assert (Q 0 a).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qpres in ev1'; depelim ev1' => //.
      { eapply nth_error_all in a0; tea. }
      clear ev1'; ih. }
    eapply X11; tea; (apply and_assum; [ih|hp' P'Q]).
  - unshelve eapply X12; tea; try (intros; apply and_assum; [ih|hp' P'Q]).
  - rename args into cargs.
    eapply Xcappexp; tea. eauto.
    cbn in IH.
    clear -P'Q IH a a0 and_assum.
    revert a0; induction a; constructor; auto. depelim a0.
    apply and_assum; [ih|hp' P'Q].
    eapply IHa. cbn. intros. eapply (IH _ _ q H). cbn. lia.
    now depelim a0.
  - eapply (X13 _ _ _ _ ev1); tea.
    1,3:(apply and_assum; [ih|hp' P'Q]).
    intros. apply and_assum; [ih|hp' P'Q].
  - unshelve eapply Qprim; tea. depelim e.
    * constructor.
    * constructor.
    * constructor.
    * eapply Qpres in qt. depelim qt. now cbn in i. constructor; eauto.
      + apply All2_over_undep. cbn in IH.
        depelim p0. destruct p.
        clear -ev IH a0 P'Q and_assum. cbn in a0. subst a; cbn in *.
        induction ev; constructor; eauto.
        ** depelim a0.
          eapply and_assum. unshelve eapply IH; tea. cbn. lia.
          intros. split => //. eapply P'Q; tea.
        ** depelim a0. intuition eauto. eapply X; intros.
          unshelve eapply IH; tea. cbn; lia.
      + depelim p0. destruct p.
        eapply and_assum. unshelve eapply IH; tea. cbn; lia.
        intros; split => //; eapply P'Q; tea.
  - eapply qpres in qt; depelim qt => //.
    assert (Q 0 (tLazy v)).
    { eapply P'Q; tea. eapply (IH _ _ q ev1); tea. now cbn; lia. }
    eapply qpres in X14. depelim X14 => //.
    eapply Qforce; tea.
    + eapply and_assum. eapply (IH _ _ q ev1); eauto; cbn; lia.
      intros hp'. split => //. eapply P'Q; tea.
    + eapply and_assum. eapply (IH _ _ q0 ev2); eauto; cbn; lia.
      intros hp'. split => //. eapply P'Q; tea.
  - eapply Qatom; tea.
Qed.

Lemma Qpreserves_wellformed (efl : EEnvFlags) Σ : wf_glob Σ -> Qpreserves (fun n x => wellformed Σ n x) Σ.
Proof.
  intros clΣ.
  split.
  - red. move=> n t.
    destruct t; cbn -[lookup_constructor lookup_constructor_pars_args]; intuition auto; try solve [constructor; auto].
    rtoProp; intuition auto.
    constructor => //.
    eapply on_evar; rtoProp; intuition auto. solve_all.
    eapply on_lambda;rtoProp;  intuition auto.
    eapply on_letin; rtoProp; intuition auto.
    eapply on_app; rtoProp; intuition auto.
    constructor => //; rtoProp; intuition auto.
    move/andP: H => [] /andP[] has isl hf => //.
    eapply on_cstr => //. destruct cstr_as_blocks.
    rtoProp; intuition auto. solve_all. destruct args => //.
    eapply on_case; rtoProp; intuition auto. solve_all.
    eapply on_proj; rtoProp; intuition auto.
    rtoProp; intuition auto.
    eapply on_fix => //. move/andP: H0 => [] _ ha. solve_all.
    rtoProp; intuition auto.
    eapply on_cofix => //. move/andP: H0 => [] _ ha. solve_all.
    move/andP: H => [] hp ha. eapply on_prim => //. solve_all.
    eapply on_lazy; rtoProp; intuition auto.
    eapply on_force; rtoProp; intuition auto.
 - red. intros kn decl.
    move/(lookup_env_wellformed clΣ).
    unfold wf_global_decl. destruct cst_body => //.
  - red. move=> hasapp n t args. rewrite wellformed_mkApps //.
    split; intros; rtoProp; intuition auto; solve_all.
  - red.
    move=> hascase n ci discr brs. simpl.
    intros; rtoProp; intuition auto; solve_all.
  - red. simpl. move=> hasproj n p discr wf discr' wf'.
    simpl. rtoProp; intuition auto.
  - red. move=> t args clt cll.
    eapply wellformed_substl. solve_all. now rewrite Nat.add_0_r.
  - red. move=> n mfix idx. cbn. unfold EWellformed.wf_fix.
    intros; rtoProp; intuition auto; solve_all. now apply Nat.ltb_lt.
  - red. move=> n mfix idx. cbn. unfold EWellformed.wf_fix.
    intros; rtoProp; intuition auto; solve_all. now apply Nat.ltb_lt.
Qed.
