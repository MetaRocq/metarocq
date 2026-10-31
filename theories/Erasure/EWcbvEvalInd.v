(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst EnvMap.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction EWcbvEval EGlobalEnv ECSubst EInduction.

Set Asymmetric Patterns.
From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.

#[global]
Hint Constructors eval : core.

Section eval_mkApps_rect.

  Variables (wfl : WcbvFlags) (Σ : global_declarations) (P : term → term → Type).

  Let IH x y (ev : eval Σ x y) :=
    forall t u (ev' : eval Σ t u), eval_depth ev' <= eval_depth ev -> P t u.

  Lemma eval_mkApps_rect :
    (∀ a t t' : term,
	    forall ev : eval Σ a tBox, P a tBox →
                            IH _ _ ev ->
                            eval Σ t t' → P t t' → P (tApp a t) tBox)
    → (∀ (f0 : term) (na : BasicAst.name) (b a a' res : term),
        forall ev : eval Σ f0 (tLambda na b),
          P f0 (tLambda na b)
          → IH _ _ ev
          → eval Σ a a' →
          P a a'
          → eval Σ (ECSubst.csubst a' 0 b) res
          → P (ECSubst.csubst a' 0 b) res → P (tApp f0 a) res)
    → (∀ (na : BasicAst.name) (b0 b0' b1 res : term),
          eval Σ b0 b0'
          → P b0 b0'
          → eval Σ (ECSubst.csubst b0' 0 b1) res
          → P (ECSubst.csubst b0' 0 b1) res →
          P (tLetIn na b0 b1) res)
          → (∀ (ind : inductive) (pars : nat) (cdecl : constructor_body)
          (discr : term) (c : nat) (args : list term)
          (brs : list (list name × term)) (br : list name × term)
          (res : term) (e : with_constructor_as_block = false)
          (e0 : eval Σ discr (mkApps (tConstruct ind c []) args)),
          P discr (mkApps (tConstruct ind c []) args)
          → ∀ (e1 : constructor_isprop_pars_decl Σ ind c =
                    Some (false, pars, cdecl)) (e2 :
                                                nth_error brs c =
                                                Some br)
              (e3 : #|args| = pars + cstr_nargs cdecl)
              (e4 : #|skipn pars args| = #|br.1|)
              (e5 : eval Σ (iota_red pars args br) res),
              P (iota_red pars args br) res
              → P (tCase (ind, pars) discr brs) res)
       → (∀ (ind : inductive) (pars : nat) (cdecl : constructor_body)
            (discr : term) (c : nat) (args : list term)
            (brs : list (list name × term)) (br : list name × term)
            (res : term) (e : with_constructor_as_block = true)
            (e0 : eval Σ discr (tConstruct ind c args)),
            P discr (tConstruct ind c args)
            → ∀ (e1 : constructor_isprop_pars_decl Σ ind c =
                      Some (false, pars, cdecl))
                (e2 : nth_error brs c = Some br)
                (e3 : #|args| = pars + cstr_nargs cdecl)
                (e4 : #|skipn pars args| = #|br.1|)
                (e5 : eval Σ (iota_red pars args br) res),
                P (iota_red pars args br) res
                → P (tCase (ind, pars) discr brs) res)

    → (∀ (ind : Kernames.inductive) (pars : nat) (discr : term)
         (brs : list (list BasicAst.name × term))
         (n : list BasicAst.name) (f3 res : term),
          with_prop_case
          → eval Σ discr tBox
          → P discr tBox
          → inductive_isprop_and_pars Σ ind = Some (true, pars)
          → brs = [(n, f3)]
          → eval Σ (ECSubst.substl (repeat tBox #|n|) f3) res
          → P (ECSubst.substl (repeat tBox #|n|) f3) res
          → P (tCase (ind, pars) discr brs) res)

    → (∀ (f4 : term) (mfix : mfixpoint term)
         (idx : nat) (argsv : list term)
         (a av fn res : term),
        forall guarded : with_guarded_fix,
        forall ev : eval Σ f4 (mkApps (tFix mfix idx) argsv),
          P f4 (mkApps (tFix mfix idx) argsv)
          → IH _ _ ev
          → eval Σ a av
          → P a av
          → cunfold_fix mfix idx = Some (#|argsv|, fn)
          → eval Σ (tApp (mkApps fn argsv) av) res
          → P (tApp (mkApps fn argsv) av) res
          → P (tApp f4 a) res)
    → (∀ (f5 : term) (mfix : mfixpoint term)
         (idx : nat) (argsv : list term)
         (a av : term) (narg : nat) (fn : term),
        forall guarded : with_guarded_fix,
        forall ev : eval Σ f5 (mkApps (tFix mfix idx) argsv),
          P f5 (mkApps (tFix mfix idx) argsv)
          → IH _ _ ev
          → eval Σ a av
          → P a av
          → cunfold_fix mfix idx = Some (narg, fn)
          → #|argsv| < narg
          → P (tApp f5 a) (tApp (mkApps (tFix mfix idx) argsv) av))
    → (∀ (f6 : term) (mfix : mfixpoint term)
         (idx : nat) (a av fn res : term) (narg : nat)
         (unguarded : with_guarded_fix = false)
         (ev : eval Σ f6 (tFix mfix idx)),
          P f6 (tFix mfix idx)
          → IH _ _ ev
          → forall (ev' : eval Σ a av), IH _ _ ev'
          → cunfold_fix mfix idx = Some (narg, fn)
          → eval Σ (tApp fn av) res
          → P (tApp fn av) res
          → P (tApp f6 a) res)
    → (∀ (ip : Kernames.inductive × nat) (mfix : mfixpoint term)
         (idx : nat) (args : list term)
         (narg : nat) discr (fn : term) (brs : list (list BasicAst.name × term))
         (res : term),
          cunfold_cofix mfix idx = Some (narg, fn)
          -> eval Σ discr (mkApps (tCoFix mfix idx) args)
          -> P discr (mkApps (tCoFix mfix idx) args)
          → eval Σ (tCase ip (mkApps fn args) brs) res
          → P (tCase ip (mkApps fn args) brs) res
          → P (tCase ip discr brs) res)
    → (∀ (p : Kernames.projection) (mfix : mfixpoint term)
         (idx : nat) (args : list term)
         (narg : nat) discr (fn res : term),
          cunfold_cofix mfix idx = Some (narg, fn)
          -> eval Σ discr (mkApps (tCoFix mfix idx) args)
          -> P discr (mkApps (tCoFix mfix idx) args)
          → eval Σ (tProj p (mkApps fn args)) res
          → P (tProj p (mkApps fn args)) res
          → P (tProj p discr) res)
    → (∀ (c : Kernames.kername) (decl : constant_body) (body : term),
          declared_constant Σ c decl
          → ∀ res : term,
          cst_body decl = Some body
          → eval Σ body res
          → P body res → P (tConst c) res)

    → (∀ (p : projection) (cdecl : constructor_body)
                             (discr : term) (args : list term)
                             (a res : term) (e : with_constructor_as_block =
                                                 false)
                             (e0 : eval Σ discr
                                     (mkApps
                                        (tConstruct
                                           (proj_ind p) 0 []) args)),
                             P discr
                               (mkApps
                                  (tConstruct (proj_ind p) 0 [])
                                  args)
                             → ∀ (e1 : constructor_isprop_pars_decl Σ
                                         (proj_ind p) 0 =
                                       Some (false, proj_npars p, cdecl))
                                 (e2 : #|args| =
                                       proj_npars p + cstr_nargs cdecl)
                                 (e3 : nth_error args
                                         (proj_npars p + proj_arg p) =
                                       Some a) (e4 : eval Σ a res),
                                 P a res
                                 → P (tProj p discr) res)
                          → (∀ (p : projection) (cdecl : constructor_body)
                               (discr : term) (args : list term)
                               (a res : term) (e :
                                               with_constructor_as_block =
                                               true)
                               (e0 : eval Σ discr
                                       (tConstruct (proj_ind p) 0 args)),
                               P discr (tConstruct (proj_ind p) 0 args)
                               → ∀ (e1 : constructor_isprop_pars_decl Σ
                                           (proj_ind p) 0 =
                                         Some (false, proj_npars p, cdecl))
                                   (e2 : #|args| =
                                         proj_npars p + cstr_nargs cdecl)
                                   (e3 : nth_error args
                                           (proj_npars p + proj_arg p) =
                                         Some a) (e4 : eval Σ a res),
                                   P a res
                                   → P (tProj p discr) res)

    → (∀ p (discr : term),
          with_prop_case
          → eval Σ discr tBox
          → P discr tBox
          → inductive_isprop_and_pars Σ p.(proj_ind) = Some (true, p.(proj_npars))
          → P (tProj p discr) tBox)

          → (∀ (ind : inductive)
          (c : nat) (mdecl : mutual_inductive_body)
          (idecl : one_inductive_body)
          (cdecl : constructor_body)
          (f14 : term) (args : list term)
          (a a' : term)
          (e : with_constructor_as_block = false)
          (e0 : lookup_constructor Σ ind c =
                Some (mdecl, idecl, cdecl))
          (e1 : eval Σ f14
                  (mkApps
                     (tConstruct ind c [])
                     args)),
                IH _ _ e1 ->
          P f14
            (mkApps (tConstruct ind c [])
               args)
          → ∀ (l : #|args| < cstr_arity mdecl cdecl)
              (e2 : eval Σ a a'),
              P a a'
              → P (tApp f14 a)
                  (tApp
                     (mkApps
                        (tConstruct ind c
                        []) args) a'))

      → (∀ (ind : inductive)
                   (c : nat) (mdecl : mutual_inductive_body)
                   (idecl : one_inductive_body)
                   (cdecl : constructor_body)
                   (args args' : list term)
                   (e : with_constructor_as_block = true)
                   (e0 : lookup_constructor Σ ind c =
                         Some (mdecl, idecl, cdecl))
                   (l : #|args| = cstr_arity mdecl cdecl)
                   (e1 : All2 (eval Σ) args args'),
                   All2 P args args'
            → P (tConstruct ind c args) (tConstruct ind c args'))

      → (∀ (f15 f' a a' : term) (e : eval Σ f15 f'),
      P f15 f' -> IH _ _ e
      → ∀ (i : ~~
               (isLambda f'
                ||
                (if with_guarded_fix
                 then isFixApp f'
                 else isFix f') ||
                isBox f' ||
                isConstructApp f' || isPrimApp f' || isLazyApp f'))
          (e0 : eval Σ a a'),
          P a a'
          → P (tApp f15 a)
              (tApp f' a')) ->

   (forall p p' (ev : eval_primitive (eval Σ) p p'),
      eval_primitive_ind _ (fun x y _ => P x y) _ _ ev ->
      P (tPrim p) (tPrim p')) ->

   (forall t t' v (ev1 : eval Σ t (tLazy t')) (ev2 : eval Σ t' v),
      P t (tLazy t') -> P t' v ->
      P (tForce t) v)
    → (∀ t : term, atom Σ t → P t t)
    → ∀ t t0 : term, eval Σ t t0 → P t t0.
Proof using Type.
  intros ??????????????????????? H.
  pose proof (p := @Fix_F { t : _ & { t0 : _ & eval Σ t t0 }}).
  specialize (p (MR lt (fun x => eval_depth x.π2.π2))).
  set(foo := existT _ t (existT _ t0 H) :  { t : _ & { t0 : _ & eval Σ t t0 }}).
  change t with (projT1 foo).
  change t0 with (projT1 (projT2 foo)).
  change H with (projT2 (projT2 foo)).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p.
  2:{ apply p. apply measure_wf, lt_wf. }
  clear p.
  clear t t0 H.
  intros (t & t0 & ev).
  intros IH'.
  set (IH'' t t0 H := IH' (t; t0; H)). clearbody IH''; clear IH'; rename IH'' into IH'.
  cbn in IH'. unfold MR in IH'; cbn in IH'. cbn.
  destruct ev; cbn in IH'.
  all:try match goal with
  | [ H : _ |- _ ] =>
    eapply H; tea; unshelve eapply IH'; tea; cbn; try lia
  end.
  all:try solve[match goal with
  | [ H : _ |- _ ] =>
    unshelve eapply H; try match goal with |- eval _ _ _ => tea end; tea; unfold IH; intros; unshelve eapply IH'; tea; cbn; try lia
  end].
  - eapply X15; tea; auto.
    clear -a IH'. induction a; constructor; eauto.
    eapply (IH' _ _ r). cbn. lia. apply IHa.
    intros. eapply (IH' _ _ H). cbn. lia.
  - unshelve eapply X17; tea.
    clear -e IH'.
    induction e; constructor; eauto. subst a a'.
    2:{ unshelve eapply IH'; tea; cbn; lia. }
      eapply All2_over_undep.
      induction ev; constructor; eauto.
      unshelve eapply IH'; tea; cbn; lia.
      eapply IHev. cbn. intros. unshelve eapply IH'; tea; cbn; lia.
Qed.

End eval_mkApps_rect.
