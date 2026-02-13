From Stdlib Require Import Program ssreflect ssrbool List.
From MetaRocq.Utils Require Import utils MRRelations.
From MetaRocq.Common Require Import config Kernames.


From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction
  PCUICReflect PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp
  PCUICContextConversionTyp
  PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion
  PCUICUnivSubstitutionTyp
  PCUICCumulativity PCUICSR PCUICSafeLemmata
  PCUICValidity PCUICPrincipality PCUICElimination
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICClassification.

From MetaRocq.PCUIC Require Import PCUICArities PCUICSpine.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.PCUIC Require Import PCUICEquality PCUICAlpha.

Section firstorder.

  Context {Σ : global_env_ext}.
  Context {Σb : list (kername × bool)}.

  Fixpoint plookup_env {A} (Σ : list (kername × A)) (kn : kername) {struct Σ} : option A :=
  match Σ with
  | [] => None
  | d :: tl => if eq_kername kn d.1 then Some d.2 else plookup_env tl kn
  end.
  (*
  Definition zo_type (t : term) :=
    match (PCUICAstUtils.decompose_app t).1 with
    | tProd _ _ _ => false
    | tSort _ => false
    | tInd (mkInd nm i) _ => match (plookup_env Σb nm) with
                             | Some l => nth i l false | None => false
                             end
    | _ => true
    end. *)

  Definition firstorder_type (n k : nat) (t : term) :=
    match (PCUICAstUtils.decompose_app t).1, (PCUICAstUtils.decompose_app t).2 with
    | tInd (mkInd nm i) u , [] => match (plookup_env Σb nm) with
                             | Some b => b | None => false
                             end
    | tRel i , [] => (k <=? i) && (i <? n + k)
    | _ , _ => false
    end.

  Definition firstorder_con mind (c : constructor_body) :=
    let inds := #|mind.(ind_bodies)| in
    alli (fun k '({| decl_body := b ; decl_type := t ; decl_name := n|}) =>
      firstorder_type inds k t) 0
      (List.rev (c.(cstr_args) ++ mind.(ind_params)))%list.

  Definition firstorder_oneind mind (ind : one_inductive_body) :=
    forallb (firstorder_con mind) ind.(ind_ctors) && negb (Sort.is_level (ind_sort ind)).

  Definition firstorder_mutind (mind : mutual_inductive_body) :=
    (* if forallb (fun decl => firstorder_type decl.(decl_type)) mind.(ind_params) then *)
    ~~ (mind.(ind_finite) == CoFinite) &&
    forallb (firstorder_oneind mind) mind.(ind_bodies)
    (* else repeat false (length mind.(ind_bodies)). *).

  Definition firstorder_ind (i : inductive) :=
    match lookup_env Σ.1 (inductive_mind i) with
    | Some (InductiveDecl mind) => firstorder_mutind mind
    | _ => false
    end.

End firstorder.

Arguments firstorder_ind : clear implicits.

Fixpoint firstorder_env' (Σ : global_declarations) :=
  match Σ with
  | nil => []
  | (nm, ConstantDecl _) :: Σ' =>
    let Σb := firstorder_env' Σ' in
    ((nm, false) :: Σb)
  | (nm, InductiveDecl mind) :: Σ' =>
    let Σb := firstorder_env' Σ' in
    ((nm, @firstorder_mutind Σb mind) :: Σb)
  end.

Definition firstorder_env (Σ : global_env_ext) :=
  firstorder_env' Σ.1.(declarations).

Lemma firstorder_lookup_inv {Σ i} :
  firstorder_ind Σ (firstorder_env Σ) i ->
  {mind & lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind)}.
Proof.
  unfold firstorder_ind. destruct lookup_env. 2:auto.
  destruct g; auto with core; eauto.
Defined.

Section cf.

Context {cf : config.checker_flags}.

Definition isPropositionalArity ar :=
  match destArity [] ar with
  | Some (_, s) => Sort.is_propositional s
  | None => false
  end.

Definition isPropositional Σ ind :=
  match lookup_inductive Σ ind with
  | Some (mdecl, idecl) => isPropositionalArity idecl.(ind_type)
  | _ => false
  end.

Inductive firstorder_value Σ Γ : term -> Prop :=
| firstorder_value_C i n ui u args pandi :
   Σ ;;; Γ |- mkApps (tConstruct i n ui) args :
   mkApps (tInd i u) pandi ->
   Forall (firstorder_value Σ Γ) args ->
   ~~ isPropositional Σ i ->
   firstorder_value Σ Γ (mkApps (tConstruct i n ui) args).

Lemma firstorder_value_inds :
 forall (Σ : global_env_ext) (Γ : context) (P : term -> Prop),
(forall (i : inductive) (n : nat) (ui u : Instance.t)
   (args pandi : list term),
 Σ;;; Γ |- mkApps (tConstruct i n ui) args : mkApps (tInd i u) pandi ->
 Forall (firstorder_value Σ Γ) args ->
 Forall P args ->
 ~~ isPropositional (PCUICEnvironment.fst_ctx Σ) i ->
 P (mkApps (tConstruct i n ui) args)) ->
forall t : term, firstorder_value Σ Γ t -> P t.
Proof using Type.
  intros ? ? ? ?. fix rec 2. intros t [ ]. eapply H; eauto.
  clear - H0 rec.
  induction H0; econstructor; eauto.
Qed.

Lemma firstorder_ind_propositional {Σ : global_env_ext} {wfΣ:wf Σ} i mind oind :
  declared_inductive Σ i mind oind ->
  firstorder_ind Σ (firstorder_env Σ) i ->
  ~~ isPropositional Σ i.
Proof using Type.
  intros d. unshelve epose proof (d_ := declared_inductive_to_gen d); eauto.
  pose proof d_ as [d1 d2]. intros H. red in d1. unfold firstorder_ind in H.
  unfold isPropositional.
  unfold PCUICEnvironment.fst_ctx in *. rewrite d1 in H |- *.
  unfold firstorder_mutind in H.
  rewrite /lookup_inductive /lookup_inductive_gen /lookup_minductive_gen /= d1 d2.
  move/andP: H => [ind H0].
  eapply forallb_nth_error in H0; tea.
  erewrite d2 in H0. cbn in H0.
  unfold firstorder_oneind in H0. solve_all.
  destruct (ind_sort oind) eqn:E2; inv H0.
  eapply PCUICInductives.declared_inductive_type in d.
  rewrite d. rewrite E2. unfold isPropositionalArity.
  now rewrite destArity_it_mkProd_or_LetIn.
Qed.

Inductive firstorder_spine Σ (Γ : context) : term -> list term -> term -> Type :=
| firstorder_spine_nil ty ty' :
    isType Σ Γ ty ->
    isType Σ Γ ty' ->
    Σ ;;; Γ ⊢ ty ≤ ty' ->
    firstorder_spine Σ Γ ty [] ty'

| firstorder_spine_cons ty hd tl na i u args B B' mind oind :
    isType Σ Γ ty ->
    isType Σ Γ (tProd na (mkApps (tInd i u) args) B) ->
    Σ ;;; Γ ⊢ ty ≤ tProd na (mkApps (tInd i u) args) B ->
    declared_inductive Σ i mind oind ->
    Σ ;;; Γ |- hd : (mkApps (tInd i u) args) ->
    firstorder_ind Σ (@firstorder_env Σ) i ->
    firstorder_spine Σ Γ (subst10 hd B) tl B' ->
    firstorder_spine Σ Γ ty (hd :: tl) B'.

Inductive instantiated {Σ} (Γ : context) : term -> Type :=
| instantiated_mkApps i u args : instantiated Γ (mkApps (tInd i u) args)
| instantiated_LetIn na d b ty :
  instantiated Γ (ty {0 := d}) ->
  instantiated Γ (tLetIn na d b ty)
| instantiated_tProd na B i u args :
  firstorder_ind Σ (@firstorder_env Σ) i ->
    (forall x,
       (* Σ ;;; Γ |- x : mkApps (tInd i u) args ->  *)
      instantiated Γ (subst10 x B)) ->
    instantiated Γ (tProd na (mkApps (tInd i u) args) B).

Import PCUICLiftSubst.
Lemma isType_context_conversion {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ} {T} :
  isType Σ Γ T ->
  Σ ⊢ Γ = Δ ->
  wf_local Σ Δ ->
  isType Σ Δ T.
Proof using Type.
  intros HT ??.
  apply lift_typing_impl with (1 := HT); intros ?? H.
  eapply context_conversion; tea. now eapply ws_cumul_ctx_pb_forget.
Qed.

Lemma typing_spine_arity_spine {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ args T' i u pars :
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd i u) pars)) args T' ->
  arity_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd i u) pars)) args T'.
Proof using Type.
  intros H. revert args pars T' H.
  induction Δ using PCUICInduction.ctx_length_rev_ind; intros args pars T' H.
  - cbn. depelim H.
    + econstructor; eauto.
    + eapply invert_cumul_ind_prod in w. eauto.
  - cbn. depelim H.
    + econstructor; eauto.
    + rewrite it_mkProd_or_LetIn_app in w, i0 |- *. cbn. destruct d as [name [body |] type]; cbn in *.
      -- constructor. rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps. eapply X. now len.
         econstructor; tea. eapply isType_tLetIn_red in i0.
         rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r in i0. now rewrite Nat.add_0_r. pcuic.
         etransitivity; tea. eapply into_ws_cumul_pb. 2,4:fvs.
         econstructor 3. 2:{ econstructor. }
         rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps //. constructor 1. reflexivity.
         eapply isType_tLetIn_red in i0. 2:pcuic.
         rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps in i0.
         now eapply PCUICClosedTyp.isType_is_open_term.
      -- eapply cumul_Prod_inv in w as []. econstructor.
         ++ eapply type_ws_cumul_pb. 3: eapply PCUICContextConversion.ws_cumul_pb_eq_le; symmetry. all:eauto.
            eapply isType_tProd in i0. eapply isTypeRel_isType, i0.
         ++ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. autorewrite with subst.
            cbn. eapply X. len.
            eapply typing_spine_strengthen. eauto.
            2:{ replace (it_mkProd_or_LetIn (subst_context [hd] 0 Γ0)
            (mkApps (tInd i u) (map (subst [hd] (#|Γ0| + 0)) pars))) with ((PCUICAst.subst10 hd (it_mkProd_or_LetIn Γ0 (mkApps (tInd i u) pars)))).
            2:{ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. now autorewrite with subst. }
            eapply substitution0_ws_cumul_pb. eauto. eauto.
            }
            replace (it_mkProd_or_LetIn (subst_context [hd] 0 Γ0)
            (mkApps (tInd i u) (map (subst [hd] (#|Γ0| + 0)) pars))) with ((PCUICAst.subst10 hd (it_mkProd_or_LetIn Γ0 (mkApps (tInd i u) pars)))).
            2:{ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. now autorewrite with subst. }
            eapply PCUICSubstitution.isType_subst. eapply PCUICSubstitution.subslet_ass_tip. eauto.
            eapply isType_tProd in i0 as [_ tprod].
            eapply isType_context_conversion; tea. constructor. eapply ws_cumul_ctx_pb_refl. now eapply typing_wf_local, PCUICClosedTyp.wf_local_closed_context in t.
            constructor; tea. constructor. pcuic. now eapply isType_tProd in i1 as [].
Qed.

Lemma leb_spect : forall x y : nat, BoolSpecSet (x <= y) (y < x) (x <=? y).
Proof using Type.
  intros x y. destruct (x <=? y) eqn:E;
  econstructor; destruct (Nat.leb_spec x y); lia.
Qed.

Lemma nth_error_inds {ind u mind n} : n < #|ind_bodies mind| ->
  nth_error (inds ind u mind.(ind_bodies)) n = Some (tInd (mkInd ind (#|mind.(ind_bodies)| - S n)) u).
Proof using Type.
  unfold inds.
  induction #|ind_bodies mind| in n |- *.
  - intros hm. inv hm.
  - intros hn. destruct n => /=. lia_f_equal.
    eapply IHn0. lia.
Qed.

Lemma alli_subst_instance (Γ : context) u p :
  (forall k t, p k t = p k t@[u]) ->
  forall n,
    alli (fun (k : nat) '{| decl_type := t |} => p k t) n Γ =
    alli (fun (k : nat) '{| decl_type := t |} => p k t) n Γ@[u].
Proof using Type.
  intros hp.
  induction Γ; cbn => //.
  move=> n. destruct a; cbn. f_equal. apply hp. apply IHΓ.
Qed.

Arguments firstorder_mutind : clear implicits.

Lemma plookup_env_lookup_env {Σ : global_env_ext} kn b :
  plookup_env (firstorder_env Σ) kn = Some b ->
  ∑ Σ' decl, lookup_env Σ kn = Some decl ×
    strictly_extends_decls Σ' Σ ×
    match decl with
    | ConstantDecl _ => b = false
    | InductiveDecl mind =>
      b = firstorder_mutind (firstorder_env' (declarations Σ')) mind
    end.
Proof using.
  destruct Σ as [[univs Σ retro] ext].
  induction Σ; cbn => //.
  destruct a as [kn' d] => //. cbn.
  case: eqb_specT.
  * intros ->.
    destruct d => //; cbn; rewrite eqb_refl => [=] <-;
    exists {| universes := univs; declarations := Σ; retroknowledge := retro |}.
    eexists; split => //. cbn. split => //.
    red. split => //. eexists (_ :: []); cbn; trea.
    eexists; split => //. cbn; split => //.
    red. split => //. eexists (_ :: []); cbn; trea.
  * intros neq h.
    destruct d => //. cbn in h.
    move: h. case: eqb_specT=> // _ h'.
    unfold firstorder_env in IHΣ. cbn in IHΣ.
    specialize (IHΣ h') as [Σ' [decl [Hdecl [ext' ?]]]].
    exists Σ', decl; split => //. split => //.
    destruct ext' as [equ [Σ'' eq]]. split => //.
    eexists (_ :: Σ''). cbn in *. rewrite eq. trea.
    move: h. cbn. apply neqb in neq. rewrite (negbTE neq).
    intros h'; specialize (IHΣ h') as [Σ' [decl [Hdecl [ext' ?]]]].
    exists Σ', decl; split => //. split => //.
    destruct ext' as [equ [Σ'' eq]]. split => //.
    eexists (_ :: Σ''). cbn in *. rewrite eq. trea.
Qed.

Lemma firstorder_spine_let {Σ : global_env_ext} {wfΣ : wf Σ} {Γ na a A B args T'} :
  firstorder_spine Σ Γ (B {0 := a}) args T' ->
  isType Σ Γ (tLetIn na a A B) ->
  firstorder_spine Σ Γ (tLetIn na a A B) args T'.
Proof using Type.
  intros H; depind H.
  - constructor; auto.
    etransitivity; tea. eapply cumulSpec_cumulAlgo_curry; tea; fvs.
    eapply cumul_zeta.
  - intros. econstructor. tea.
    2:{ etransitivity; tea.
        eapply cumulSpec_cumulAlgo_curry; tea; fvs.
        eapply cumul_zeta. }
    all:tea.
Qed.

Lemma instantiated_typing_spine_firstorder_spine {Σ : global_env_ext} {wfΣ : wf Σ} Γ T args T' :
  instantiated (Σ := Σ) Γ T ->
  arity_spine Σ Γ T args T' ->
  isType Σ Γ T ->
  firstorder_spine Σ Γ T args T'.
Proof using Type.
  intros hi hsp.
  revert hi; induction hsp; intros hi isty.
  - constructor => //. now eapply isType_ws_cumul_pb_refl.
  - econstructor; eauto.
  - depelim hi. solve_discr. eapply firstorder_spine_let; eauto. eapply IHhsp => //.
    now eapply isType_tLetIn_red in isty; pcuic.
  - depelim hi. solve_discr.
    specialize (i1 hd). specialize (IHhsp i1).
    destruct (validity t) as (_ & s & Hs & _). eapply inversion_mkApps in Hs as [? [hi _]].
    eapply inversion_Ind in hi as [mdecl [idecl [decli [? ?]]]].
    econstructor; tea. 2:{ eapply IHhsp. eapply isType_apply in isty; tea. }
    now eapply isType_ws_cumul_pb_refl. eauto.
Qed.

Arguments firstorder_type : clear implicits.

(* Lemma firstorder_env'_app x y :
  firstorder_env' (x ++ y) = firstorder_env' x ++ firstorder_env' y.
Proof.
  induction x in y |- *; cbn => //.
  destruct a => //. destruct g => //. cbn. f_equal; eauto.
  cbn; f_equal; eauto.
  f_equal. f_equal. eauto. *)

Import PCUICGlobalMaps.

Lemma fresh_global_app decls decls' kn :
  fresh_global kn (decls ++ decls') ->
  fresh_global kn decls /\ fresh_global kn decls'.
Proof using Type.
  induction decls => /= //.
  - intros f; split => //.
  - intros f; depelim f.
    specialize (IHdecls f) as [].
    split; eauto. constructor => //.
Qed.

Lemma plookup_env_Some_not_fresh g kn b :
  plookup_env (firstorder_env' g) kn = Some b ->
  ~ PCUICGlobalMaps.fresh_global kn g.
Proof using Type.
  induction g; cbn => //.
  destruct a => //. destruct g0 => //.
  - cbn.
    case: eqb_spec.
    + move=> -> [=].
      intros neq hf. depelim hf. now cbn in H.
    + move=> neq hl hf.
      apply IHg => //. now depelim hf.
  - cbn.
    case: eqb_spec.
    + move=> -> [=].
      intros neq hf. depelim hf. now cbn in H.
    + move=> neq hl hf.
      apply IHg => //. now depelim hf.
Qed.

Lemma plookup_env_extends {Σ Σ' : global_env} kn b :
  strictly_extends_decls Σ' Σ ->
  wf Σ ->
  plookup_env (firstorder_env' (declarations Σ')) kn = Some b ->
  plookup_env (firstorder_env' (declarations Σ)) kn = Some b.
Proof using Type.
  intros [equ [Σ'' eq] eqr]. rewrite eq.
  clear equ eqr. intros []. clear o.
  rewrite eq in o0. clear eq. move: o0.
  generalize (declarations Σ'). clear Σ'.
  induction Σ''.
  - cbn => //.
  - cbn. destruct a => //. intros gs ong.
    depelim ong. specialize (IHΣ'' _ ong).
    destruct o as [f ? ? ?].
    destruct g => //.
    * intros hl. specialize (IHΣ'' hl).
      eapply plookup_env_Some_not_fresh in hl.
      cbn. case: eqb_spec.
      + intros <-.  apply fresh_global_app in f as [].
        contradiction.
      + now intros neq.
    * intros hl. specialize (IHΣ'' hl).
      eapply plookup_env_Some_not_fresh in hl.
      cbn. case: eqb_spec.
      + intros <-. apply fresh_global_app in f as [].
        contradiction.
      + now intros neq.
Qed.

Lemma firstorder_mutind_ext {Σ Σ' : global_env_ext} m :
  strictly_extends_decls Σ' Σ ->
  wf Σ ->
  firstorder_mutind (firstorder_env' (declarations Σ')) m ->
  firstorder_mutind (firstorder_env Σ) m.
Proof using Type.
  intros [equ [Σ'' eq]] wf.
  unfold firstorder_env. rewrite eq.
  unfold firstorder_mutind.
  move/andP => [] -> /=. apply forallb_impl => x _.
  unfold firstorder_oneind.
  move/andP => [] h -> /=; rewrite andb_true_r.
  eapply forallb_impl; tea => c _.
  unfold firstorder_con.
  eapply alli_impl => i [] _ _ ty.
  unfold firstorder_type.
  destruct decompose_app => // /=.
  destruct t => //. destruct ind => //.
  destruct plookup_env eqn:hl => //. destruct b => //.
  eapply (plookup_env_extends (Σ:=Σ)) in hl. 2:split; eauto.
  rewrite eq in hl. rewrite hl //. apply wf.
  all: destruct l; eauto.
Qed.

Arguments Nat.leb : simpl never.
Arguments Nat.ltb : simpl never.

Lemma firstorder_args {Σ : global_env_ext} {wfΣ : wf Σ} { mind cbody i n ui args u pandi oind} :
  declared_constructor Σ (i, n) mind oind cbody ->
  PCUICArities.typing_spine Σ [] (type_of_constructor mind cbody (i, n) ui) args (mkApps (tInd i u) pandi) ->
  firstorder_ind Σ (@firstorder_env Σ) i ->
  firstorder_spine Σ [] (type_of_constructor mind cbody (i, n) ui) args (mkApps (tInd i u) pandi).
Proof using Type.
  intros Hdecl Hspine Hind. revert Hspine.
  unshelve edestruct @declared_constructor_inv with (Hdecl := Hdecl); eauto. exact weaken_env_prop_typing.

  (* revert Hspine. *) unfold type_of_constructor.
  erewrite cstr_eq. 2: eapply p.
  rewrite <- it_mkProd_or_LetIn_app.
  rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
  rewrite PCUICSpine.subst0_it_mkProd_or_LetIn. intros Hspine.

  match goal with
   | [ |- firstorder_spine _ _ ?T _ _ ] =>
  assert (@instantiated Σ [] T) as Hi end.
  { clear Hspine. destruct Hdecl as [[d1 d3] d2]. pose proof d3 as Hdecl.
    unfold firstorder_ind in Hind.
    unshelve epose proof (d1_ := declared_minductive_to_gen d1); eauto.
    rewrite d1_ in Hind. solve_all. clear a.
    move/andP: Hind => [indf H0].
    eapply forallb_nth_error in H0 as H'.
    erewrite d3 in H'.
    unfold firstorder_oneind in H'. cbn in H'.
    rtoProp.
    eapply nth_error_forallb in H. 2: eauto.
    unfold firstorder_con in H.
    revert H. cbn.
    unfold cstr_concl.
    rewrite PCUICUnivSubst.subst_instance_mkApps subst_mkApps.
    rewrite subst_instance_length length_app.
    unfold cstr_concl_head. rewrite PCUICInductives.subst_inds_concl_head. now eapply nth_error_Some_length in Hdecl.
    rewrite -length_app.
    generalize (cstr_args cbody ++ ind_params mind)%list.
    clear -wfΣ d1 indf H1 H0 Hdecl.
    (* generalize conclusion to mkApps tInd args *)
    intros c.
    change (list context_decl) with context in c.
    move: (map (subst (inds _ _ _) _) _).
    intros args.
    rewrite (alli_subst_instance _ ui (fun k t => firstorder_type _ #|ind_bodies mind| k t)).
    { intros k t.
      rewrite /firstorder_type.
      rewrite -PCUICUnivSubstitutionConv.subst_instance_decompose_app /=.
      destruct (decompose_app) => //=. destruct t0 => //; destruct l; eauto. }
    replace (List.rev c)@[ui] with (List.rev c@[ui]).
    2:{ rewrite /subst_instance /subst_instance_context /map_context map_rev //. }
    revert args.
    induction (c@[ui]) using PCUICInduction.ctx_length_rev_ind => args.
    - unfold cstr_concl, cstr_concl_head. cbn.
      autorewrite with substu subst.
      rewrite subst_context_nil. cbn -[subst0].
      econstructor.
    - rewrite rev_app_distr /=. destruct d as [na [b|] t].
      + move=> /andP[] fot foΓ.
        rewrite subst_context_app /=.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        constructor.
        rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps /=. len.
        rewrite -subst_app_context' // PCUICSigmaCalculus.subst_context_decompo.
        cbn. len. eapply X. now len.
        rewrite -subst_telescope_subst_context. clear -foΓ.
        revert foΓ. move: (lift0 #|ind_bodies mind| _).
        generalize 0.
        induction (List.rev Γ) => //.
        cbn -[subst_telescope]. intros n t.
        destruct a; cbn -[subst_telescope].
        move/andP => [] fo fol.
        rewrite PCUICContextSubst.subst_telescope_cons /=.
        apply/andP; split; eauto.
        clear -fo.
        move: fo.
        unfold firstorder_type; cbn.
        destruct (decompose_app decl_type) eqn:da.
        rewrite (decompose_app_inv da) subst_mkApps /=.
        destruct t0 => //=; destruct l; eauto.
        { move/andP => [/Nat.leb_le hn /Nat.ltb_lt hn'].
          destruct (Nat.leb_spec n n0).
          destruct (n0 - n) eqn:E. lia.
          cbn. rewrite nth_error_nil /=.
          apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
          rewrite decompose_app_mkApps //=.
          apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
        { destruct ind => //. }
      + move=> /andP[] fot foΓ.
        rewrite subst_context_app /=.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        unfold firstorder_type in fot.
        destruct ((PCUICAstUtils.decompose_app t)) eqn:E.
        cbn in fot. destruct t0; try solve [inv fot].
        * rewrite (decompose_app_inv E) /= subst_mkApps.
          rewrite Nat.add_0_r in fot. destruct l; try solve [inversion fot].
          eapply Nat.ltb_lt in fot.
          cbn. rewrite nth_error_inds. lia. cbn.
          eapply instantiated_tProd with (args := []).
          unshelve epose proof (d1_ := declared_minductive_to_gen d1); eauto.
          { rewrite /firstorder_ind d1_ /= /firstorder_mutind indf H0 //. }
          intros x.
          rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps /=. len.
          rewrite -subst_app_context' // PCUICSigmaCalculus.subst_context_decompo.
          cbn. len. eapply X. now len.
          rewrite -subst_telescope_subst_context. clear -foΓ.
          revert foΓ. generalize (lift0 #|ind_bodies mind| x).
          generalize 0.
          induction (List.rev Γ) => //.
          cbn -[subst_telescope]. intros n t.
          destruct a; cbn -[subst_telescope].
          move/andP => [] fo fol.
          rewrite PCUICContextSubst.subst_telescope_cons /=.
          apply/andP; split; eauto.
          clear -fo.
          move: fo.
          unfold firstorder_type; cbn.
          destruct (decompose_app decl_type) eqn:da.
          rewrite (decompose_app_inv da) subst_mkApps /=.
          destruct t0 => //=; destruct l; eauto.
          { move/andP => [/Nat.leb_le hn /Nat.ltb_lt hn'].
            destruct (Nat.leb_spec n n0).
            destruct (n0 - n) eqn:E. lia.
            cbn. rewrite nth_error_nil /=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
            rewrite decompose_app_mkApps //=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
          { destruct ind => //. }
        * rewrite (decompose_app_inv E) subst_mkApps //=.
          constructor. {
             unfold firstorder_ind. destruct ind. cbn in *.
             destruct l; [|inversion fot].
             destruct plookup_env eqn:hp => //.
             eapply plookup_env_lookup_env in hp as [Σ' [decl [eq [ext he]]]].
             rewrite eq. destruct decl; subst b => //.
             eapply (firstorder_mutind_ext (Σ' := (empty_ext Σ'))); tea. }
          intros x. rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps /=; len.
          rewrite -subst_app_context' // PCUICSigmaCalculus.subst_context_decompo.
          eapply X. now len. len.
          rewrite -subst_telescope_subst_context. clear -foΓ.
          revert foΓ. generalize (lift0 #|ind_bodies mind| x).
          generalize 0.
          induction (List.rev Γ) => //.
          cbn -[subst_telescope]. intros n t.
          destruct a; cbn -[subst_telescope].
          move/andP => [] fo fol.
          rewrite PCUICContextSubst.subst_telescope_cons /=.
          apply/andP; split; eauto.
          clear -fo.
          move: fo.
          unfold firstorder_type; cbn.
          destruct (decompose_app decl_type) eqn:da.
          rewrite (decompose_app_inv da) subst_mkApps /=.
          destruct t0 => //=; destruct l; eauto.
          { move/andP => [/Nat.leb_le hn /Nat.ltb_lt hn'].
            destruct (Nat.leb_spec n n0).
            destruct (n0 - n) eqn:E. lia.
            cbn. rewrite nth_error_nil /=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
            rewrite decompose_app_mkApps //=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
          { destruct ind => //. }
  }
  cbn in Hi |- *.
  revert Hi Hspine. cbn.
  unfold cstr_concl, cstr_concl_head.
  autorewrite with substu subst.
  rewrite subst_instance_length length_app.
  rewrite PCUICInductives.subst_inds_concl_head. { cbn. destruct Hdecl as [[d1 d2] d3]. eapply nth_error_Some. rewrite d2. congruence. }
  match goal with [ |- context[mkApps _ ?args]] => generalize args end.
  intros args' Hi Spine.
  eapply instantiated_typing_spine_firstorder_spine; tea.
  now eapply typing_spine_arity_spine in Spine.
  now eapply typing_spine_isType_dom in Spine.
Qed.

Lemma invert_cumul_it_mkProd_or_LetIn_Sort_Ind {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ s i u args} :
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ (tSort s) ≤ mkApps (tInd i u) args -> False.
Proof using Type.
  induction Δ using PCUICInduction.ctx_length_rev_ind; cbn.
  - eapply invert_cumul_sort_ind.
  - rewrite it_mkProd_or_LetIn_app; destruct d as [na [b|] ty]; cbn.
    * intros hl.
      eapply ws_cumul_pb_LetIn_l_inv in hl.
      rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn in hl.
      eapply H, hl. now len.
    * intros hl. now eapply invert_cumul_prod_ind in hl.
Qed.

Lemma firstorder_value_spec (Σ:global_env_ext) t i u args :
  wf Σ -> wf_local Σ [] ->
   Σ ;;; [] |- t : mkApps (tInd i u) args ->
  PCUICWcbvEval.value Σ t ->
  firstorder_ind Σ (firstorder_env Σ) i ->
  firstorder_value Σ [] t.
Proof using Type.
  intros Hwf Hwfl Hty Hvalue.
  revert i u args Hty.

  induction Hvalue as [ t Hvalue | p pv ih | t args' Hhead Hargs IH ] using PCUICWcbvEval.value_values_ind;
   intros i u args Hty Hfo.
  - destruct t; inversion_clear Hvalue.
    + exfalso. eapply inversion_Sort in Hty as (? & ? & Hcumul); eauto.
      now eapply invert_cumul_sort_ind in Hcumul.
    + exfalso. eapply inversion_Prod in Hty as (? & ? & ? & ? & Hcumul); eauto.
      now eapply invert_cumul_sort_ind in Hcumul.
    + exfalso. eapply inversion_Lambda in Hty as (? & ? & ? & Hcumul); eauto.
      now eapply invert_cumul_prod_ind in Hcumul.
    + exfalso. eapply inversion_Ind in Hty as (? & ? & ? & ? & ? & ?); eauto.
      eapply PCUICInductives.declared_inductive_type in d.
      rewrite d in w.
      destruct (ind_params x ,,, ind_indices x0) as [ | [? [] ?] ? _] using rev_ind.
      * cbn in w. now eapply invert_cumul_sort_ind in w.
      * rewrite it_mkProd_or_LetIn_app in w. cbn in w.
        eapply ws_cumul_pb_LetIn_l_inv in w.
        rewrite /subst1 PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn PCUICLiftSubst.subst_it_mkProd_or_LetIn in w.
        now eapply invert_cumul_it_mkProd_or_LetIn_Sort_Ind in w.
      * rewrite it_mkProd_or_LetIn_app in w. cbn in w.
        now eapply invert_cumul_prod_ind in w.
    + eapply inversion_Construct in Hty as Hty'; eauto.
      destruct Hty' as (? & ? & ? & ? & ? & ? & ?).
      assert (ind = i) as ->. {
         eapply PCUICInductiveInversion.Construct_Ind_ind_eq with (args := []); eauto.
      }
      eapply firstorder_value_C with (args := []); eauto.
      eapply firstorder_ind_propositional; eauto. sq. eauto.
      apply declared_inductive_from_gen.
      eapply (declared_constructor_inductive (ind := (i, _))).
      unshelve eapply declared_constructor_to_gen; eauto.
    + exfalso. eapply invert_fix_ind with (args := []) in Hty as [].
      destruct unfold_fix as [ [] | ]; auto. eapply nth_error_nil.
    + exfalso. eapply (typing_cofix_coind (args := [])) in Hty. red in Hty.
      red in Hfo. unfold firstorder_ind in Hfo.
      destruct lookup_env eqn:E; try congruence.
      destruct g; try congruence.
      eapply andb_true_iff in Hfo as [Hfo _].
      rewrite /check_recursivity_kind E in Hty.
      now eapply (negb_False _ Hfo).
  - eapply inversion_Prim in Hty as [prim_ty [cdecl [wf hp hdecl inv ty cum]]]; eauto.
      now eapply invert_cumul_prim_type_ind in cum; tea.
  - destruct t; inv Hhead.
    + exfalso. now eapply invert_ind_ind in Hty.
    + apply inversion_mkApps in Hty as Hcon; auto.
      destruct Hcon as (?&typ_ctor& spine).
      apply inversion_Construct in typ_ctor as (?&?&?&?&?&?&?); auto.
      pose proof d as [[d' _] _]. red in d'. cbn in *. unfold PCUICEnvironment.fst_ctx in *.
      eapply @PCUICInductiveInversion.Construct_Ind_ind_eq with (mdecl := x0) in Hty as Hty'; eauto.
      destruct Hty' as (([[[]]] & ?)  & ? & ? & ? & ? & _). subst.
      econstructor; eauto.
      2:{ eapply firstorder_ind_propositional; sq; eauto.
          unshelve eapply declared_constructor_to_gen in d; eauto.
          eapply declared_constructor_inductive in d.
          apply declared_inductive_from_gen; eauto. }
      eapply PCUICSpine.typing_spine_strengthen in spine. 3: eauto.
      2: eapply PCUICInductiveInversion.declared_constructor_valid_ty; eauto.

      eapply firstorder_args in spine; eauto.
      clear c0 c1 e0 w Hty H0 Hargs.
      induction spine.
      * econstructor.
      * destruct d as [d1 d2]. inv IH.
        econstructor. inv X.
        eapply H0. tea.
        unshelve eapply declared_inductive_to_gen in d0; eauto.
        inv X. eapply IHspine; eauto.
     + exfalso.
       destruct PCUICWcbvEval.cunfold_fix as [[] | ] eqn:E; inversion H.
       eapply invert_fix_ind in Hty. auto.
       unfold unfold_fix. unfold PCUICWcbvEval.cunfold_fix in E.
       destruct (nth_error mfix idx); auto.
       inversion E; subst; clear E.
       eapply nth_error_None. lia.
    + exfalso. eapply (typing_cofix_coind (args := args')) in Hty.
      red in Hfo. unfold firstorder_ind in Hfo.
      destruct lookup_env eqn:E; try congruence.
      destruct g; try congruence.
      eapply andb_true_iff in Hfo as [Hfo _].
      rewrite /check_recursivity_kind E in Hty.
      now eapply (negb_False _ Hfo).
Qed.

Lemma firstorder_value_alpha Σ t t' :
  t ≡α t' ->
  firstorder_value Σ [] t ->
  t = t'.
Proof.
  intros Ha H. induction H in t', Ha |- using firstorder_value_inds.
  eapply eq_term_upto_univ_napp_mkApps_l_inv in Ha as (? & ? & [] & ->).
  invs e. repeat f_equal.
  - now eapply cmp_universe_instance_eq.
  - revert x0 a. clear - H0. induction H0; intros; invs a; f_equal; eauto.
Qed.

End cf.
