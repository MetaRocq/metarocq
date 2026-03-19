From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
  PCUICReduction PCUICProgram PCUICLiftSubst PCUICCSubst PCUICUnivSubst.

(* move *)
Lemma nApp_mkApps t f args :
  t = mkApps f args -> ~~ isApp t -> t = f /\ args = [].
Proof.
  intros -> napp.
  destruct args using rev_case; cbn in *; solve_discr; try discriminate => //. split => //.
  now rewrite mkApps_app /= in napp.
Qed.

Ltac solve_discr :=
  try progress (prepare_discr; finish_discr; cbn[mkApps] in * );
  try match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  | H : ?t = mkApps ?f ?l |- _ =>
    (change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H) ||
    (eapply nApp_mkApps in H as [? ?]; [|easy]; subst)
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  end.

(* end move *)

Definition isConstruct t :=
   match t with tConstruct _ _ _ => true | _ => false end.

 Definition isFix t :=
  match t with tFix _ _ => true | _ => false end.

Definition isRel t :=
    match t with tRel _ => true | _ => false end.

Section map_All.
  Context (P P' : term -> Type).
  Context (ont : forall x, P x -> P' x).

  Fixpoint map_All {x} (a : All P x) : All P' x :=
    match a with
    | All_nil => All_nil
    | All_cons _ _ p a => All_cons (ont _ p) (map_All a)
    end.
End map_All.

Section map_onPrim.
  Context (P P' : term -> Prop).
  Context (ont : forall x, P x -> P' x).

  Definition map_onPrim {x} (o : onPrim P x) : onPrim P' x :=
    match o with
    | onPrimInt i => onPrimInt _ i
    | onPrimFloat f => onPrimFloat _ f
    | onPrimString s => onPrimString _ s
    | onPrimArray a def ty v =>
      onPrimArray _ _ (ont _ def) (ont _ ty) (map_All _ _ ont v)
    end.
End map_onPrim.

Section expanded.

Variable Σ : global_env.

Local Unset Elimination Schemes.

Inductive expanded (Γ : list nat) : term -> Prop :=
| expanded_tRel (n : nat) m args : nth_error Γ n = Some m -> forall Hle : m <= #|args|, Forall (expanded Γ) args -> expanded Γ (mkApps (tRel n) args)
| expanded_tVar (id : ident) : expanded Γ (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall (expanded Γ) args -> expanded Γ (tEvar ev args)
| expanded_tSort (s : sort) : expanded Γ (tSort s)
| expanded_tProd (na : aname) (ty : term) (body : term) : expanded Γ (tProd na ty body)
| expanded_tLambda (na : aname) (ty : term) (body : term) : expanded (0 :: Γ) body -> expanded Γ (tLambda na ty body)
| expanded_tLetIn (na : aname) (def : term) (def_ty : term) (body : term) : expanded Γ def -> expanded (0 :: Γ) body -> expanded Γ (tLetIn na def def_ty body)
| expanded_mkApps (f : term) (args : list term) : ~ (isConstruct f || isFix f || isRel f) -> expanded Γ f -> Forall (expanded Γ) args -> expanded Γ (mkApps f args)
| expanded_tConst (c : kername) (u : Instance.t) : expanded Γ (tConst c u)
| expanded_tInd (ind : inductive) (u : Instance.t) : expanded Γ (tInd ind u)
| expanded_tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term)) : expanded Γ discr ->
        Forall (expanded Γ) type_info.(pparams) ->
        Forall (fun br =>
          ∥ All_fold (fun Δ d => ForOption (fun b => expanded (repeat 0 #|Δ| ++ repeat 0 #|type_info.(pparams)|) b) d.(decl_body)) br.(bcontext) ∥ /\
          expanded (repeat 0 #|br.(bcontext)| ++ Γ) br.(bbody)) branches ->
        expanded Γ (tCase ci type_info discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded Γ t -> expanded Γ (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) args d :
  Forall (fun d => isLambda d.(dbody) /\ let ctx := rev_map (fun  d => 1 + d.(rarg)) mfix in expanded (ctx ++ Γ) d.(dbody)) mfix ->
  Forall (expanded Γ) args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > d.(rarg) ->
  expanded Γ (mkApps (tFix mfix idx) args)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) :   Forall (fun d => expanded (repeat 0 #|mfix| ++ Γ) d.(dbody)) mfix -> expanded Γ (tCoFix mfix idx)
| expanded_tConstruct_app ind c u mind idecl cdecl args :
    declared_constructor Σ (ind, c) mind idecl cdecl ->
    #|args| >= (ind_npars mind + context_assumptions (cstr_args cdecl)) ->
    Forall (expanded Γ) args ->
    expanded Γ (mkApps (tConstruct ind c u) args)
| expanded_tPrim p : onPrim (expanded Γ) p -> expanded Γ (tPrim p).

End expanded.
Derive Signature for expanded.

Definition expanded_context Σ Γ ctx :=
  ∥ All_fold (fun Δ d => ForOption (expanded Σ (repeat 0 #|Δ| ++ Γ)) d.(decl_body)) ctx ∥.

Lemma expanded_ind :
  forall (Σ : global_env) (P : list nat -> term -> Prop),
  (forall (Γ : list nat) (n m : nat) (args : list term),
  nth_error Γ n = Some m ->
  m <= #|args| -> Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (mkApps (tRel n) args)) ->
  (forall (Γ : list nat) (id : ident), P Γ (tVar id)) ->
  (forall (Γ : list nat) (ev : nat) (args : list term),
  Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (tEvar ev args)) ->
  (forall (Γ : list nat) (s : sort), P Γ (tSort s)) ->
  (forall (Γ : list nat) (na : aname) (ty body : term), P Γ (tProd na ty body)) ->
  (forall (Γ : list nat) (na : aname) (ty body : term),
  expanded Σ (0 :: Γ) body -> P (0 :: Γ) body -> P Γ (tLambda na ty body)) ->
  (forall (Γ : list nat) (na : aname) (def def_ty body : term),
  expanded Σ Γ def ->
  P Γ def ->
  expanded Σ (0 :: Γ) body ->
  P (0 :: Γ) body -> P Γ (tLetIn na def def_ty body)) ->
  (forall (Γ : list nat) (f6 : term) (args : list term),
  ~ (isConstruct f6 || isFix f6 || isRel f6) ->
  expanded Σ Γ f6 ->
  P Γ f6 -> Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (mkApps f6 args)) ->
  (forall (Γ : list nat) (c : kername) (u : Instance.t), P Γ (tConst c u)) ->
  (forall (Γ : list nat) (ind : inductive) (u : Instance.t), P Γ (tInd ind u)) ->
  (forall (Γ : list nat) (ci : case_info) (type_info : predicate term)
    (discr : term) (branches : list (branch term)),
  expanded Σ Γ discr ->
  P Γ discr ->
  Forall (expanded Σ Γ) type_info.(pparams) ->
  Forall (P Γ) type_info.(pparams) ->
  Forall
    (fun br : branch term =>
    expanded_context Σ (repeat 0 #|type_info.(pparams)|)  br.(bcontext) /\
    expanded Σ (repeat 0 #|bcontext br| ++ Γ) (bbody br)) branches ->
    Forall
    (fun br : branch term =>
      ∥ All_fold (fun Δ d => ForOption (fun b => P (repeat 0 (#|Δ| + #|type_info.(pparams)|)) b) d.(decl_body)) br.(bcontext) ∥ /\
      P (repeat 0 #|bcontext br| ++ Γ) (bbody br)) branches ->
      P Γ (tCase ci type_info discr branches)) ->
  (forall (Γ : list nat) (proj : projection) (t : term),
  expanded Σ Γ t -> P Γ t -> P Γ (tProj proj t)) ->
  (forall (Γ : list nat) (mfix : mfixpoint term) (idx : nat)
    (args : list term) (d : def term),
  Forall
    (fun d0 : def term =>
      isLambda d0.(dbody) /\ let ctx := rev_map (fun d1 : def term => 1 + rarg d1) mfix in
      expanded Σ (ctx ++ Γ) (dbody d0)) mfix ->
  Forall
      (fun d0 : def term =>
      let ctx := rev_map (fun d1 : def term => 1 + rarg d1) mfix in
      P (ctx ++ Γ) (dbody d0)) mfix ->
  Forall (expanded Σ Γ) args -> Forall (P Γ) args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > rarg d -> P Γ (mkApps (tFix mfix idx) args)) ->
  (forall (Γ : list nat) (mfix : mfixpoint term) (idx : nat),
  Forall (fun d : def term => expanded Σ (repeat 0 #|mfix| ++ Γ) (dbody d))
    mfix ->  Forall (fun d : def term => P (repeat 0 #|mfix| ++ Γ) (dbody d))
    mfix  -> P Γ (tCoFix mfix idx)) ->
  (forall (Γ : list nat) (ind : inductive) (c : nat)
    (u : Instance.t) (mind : mutual_inductive_body)
    (idecl : one_inductive_body) (cdecl : constructor_body)
    (args : list term),
  declared_constructor Σ (ind, c) mind idecl cdecl ->
  #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl) ->
  Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (mkApps (tConstruct ind c u) args)) ->
  (forall Γ p, onPrim (expanded Σ Γ) p -> onPrim (P Γ) p -> P Γ (tPrim p)) ->
  forall (Γ : list nat) (t : term), expanded Σ Γ t -> P Γ t.
Proof.
  intros Σ P HRel HVar HEvar HSort HProd HLamdba HLetIn HApp HConst HInd HCase HProj HFix HCoFix HConstruct HPrim.
  fix f 3.
  intros Γ t Hexp.  destruct Hexp; eauto.
  - eapply HRel; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HEvar; eauto. clear - f H. induction H; econstructor; eauto.
  - eapply HApp; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HCase; eauto. induction H; econstructor; eauto.
    clear -H1 f. induction H1; constructor; auto.
    clear -H0 f.
    revert H0. induction 1; constructor; auto.
    split. destruct H as [[] ?]; constructor; auto.
    clear -X f. induction X; constructor; auto. destruct p; constructor; auto.
    apply f. rewrite repeat_app. exact H.
    eapply f, H.
  - assert (Forall (P Γ) args). { clear - H0 f. induction H0; econstructor; eauto. }
    eapply HFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H. induction H; econstructor; cbn in *; intuition eauto; split.
  - eapply HCoFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HConstruct; eauto.
    clear - H1 f. induction H1; econstructor; eauto.
  - eapply HPrim; eauto. now eapply (map_onPrim _ _ (f Γ)).
Qed.
Register Scheme expanded_ind as ind_nodep for expanded.

From MetaRocq.PCUIC Require Import PCUICInductiveInversion PCUICLiftSubst PCUICSigmaCalculus.

Record expanded_constant_decl Σ (cb : constant_body) : Prop :=
  { expanded_body : on_Some_or_None (expanded Σ []) cb.(cst_body); }.
    (* expanded_type : expanded Σ [] cb.(Ast.Env.cst_type) }. *)

Record expanded_constructor_decl Σ mdecl cdecl :=
  { expanded_cstr_args : expanded_context Σ (repeat 0 (#|mdecl.(ind_params)| + #|mdecl.(ind_bodies)|)) cdecl.(cstr_args) }.
    (* expanded_cstr_indices : All (expanded Σ []) cdecl.(cstr_indices); *)
    (* expanded_cstr_type : expanded Σ (repeat 0 #|mdecl.(ind_bodies)|) cdecl.(cstr_type) }. *)

Record expanded_inductive_decl Σ mdecl idecl :=
  { (* expanded_ind_type : expanded Σ [] idecl.(ind_type); *)
    expanded_ind_ctors : Forall (expanded_constructor_decl Σ mdecl) idecl.(ind_ctors) }.

Record expanded_minductive_decl Σ mdecl :=
  { expanded_params : expanded_context Σ [] mdecl.(ind_params);
    expanded_ind_bodies : Forall (expanded_inductive_decl Σ mdecl) mdecl.(ind_bodies) }.

Definition expanded_decl Σ d :=
  match d with
  | ConstantDecl cb => expanded_constant_decl Σ cb
  | InductiveDecl idecl => expanded_minductive_decl Σ idecl
  end.

Inductive expanded_global_declarations (univs : ContextSet.t) retro : forall (Σ : global_declarations), Prop :=
| expanded_global_nil : expanded_global_declarations univs retro []
| expanded_global_cons decl Σ : expanded_global_declarations univs retro Σ ->
  expanded_decl {| universes := univs; declarations := Σ; retroknowledge := retro |} decl.2 ->
  expanded_global_declarations univs retro (decl :: Σ).
Derive Signature for expanded_global_declarations.

Definition expanded_global_env (g : global_env) :=
  expanded_global_declarations g.(universes) g.(retroknowledge) g.(declarations).

Definition expanded_pcuic_program (p : pcuic_program) :=
  expanded_global_env p.1 /\ expanded p.1 [] p.2.

Lemma expanded_mkApps_expanded {Σ Γ f args} :
  expanded Σ Γ f -> All (expanded Σ Γ) args ->
  expanded Σ Γ (mkApps f args).
Proof.
  intros.
  destruct (isConstruct f || isFix f || isRel f) eqn:eqc.
  destruct f => //.
  - depelim H; solve_discr. eapply expanded_tRel; tea. cbn in Hle. lia. solve_all.
    now rewrite eqc in H.
  - depelim H; solve_discr.
    now rewrite eqc in H.
    eapply expanded_tConstruct_app; tea. cbn in H0. lia. solve_all.
  - depelim H; solve_discr. now rewrite eqc in H.
  - eapply expanded_mkApps. now rewrite eqc. auto. solve_all.
Qed.

Lemma expanded_lift Σ n k b Γ Δ Δ' :
  #|Γ| = k ->
  #|Δ'| = n ->
  expanded Σ (Γ ++ Δ) b ->
  expanded Σ (Γ ++ Δ' ++ Δ) (lift n k b).
Proof.
  intros Hk Hn.
  remember (Γ ++ Δ)%list as Γ_.
  intros exp; revert Γ n k Hn Hk HeqΓ_.
  induction exp using expanded_ind; intros Γ' n' k Hn Hk ->.
  all:try solve[ cbn; econstructor => // ].
  2,7:try solve [cbn; econstructor => //; solve_all ].
  - subst n'. rewrite lift_mkApps /=.
    destruct (Nat.leb_spec k n).
    * rewrite nth_error_app_ge in H. lia.
      eapply expanded_tRel.
      rewrite nth_error_app_ge; [lia|].
      rewrite nth_error_app_ge; [lia|]. erewrite <- H. lia_f_equal.
      now len. solve_all.
    * eapply expanded_tRel.
      rewrite nth_error_app_lt in H; [lia|].
      rewrite nth_error_app_lt; [lia|]. tea. now len. solve_all.
  - cbn. econstructor.
    eapply (IHexp (0 :: Γ') n' (S k)); cbn; auto; lia.
  - cbn. econstructor. apply IHexp1; auto.
    eapply (IHexp2 (0 :: Γ') n' (S k)); cbn; auto; lia.
  - rewrite lift_mkApps.
    destruct (isConstruct (lift n' k f6) || isFix (lift n' k f6) || isRel (lift n' k f6)) eqn:eqc.
    specialize (IHexp  _ _ _ Hn Hk eq_refl).
    eapply expanded_mkApps_expanded => //. solve_all.
    eapply expanded_mkApps => //. now rewrite eqc. now eapply IHexp. solve_all.
  - cbn. econstructor. eauto. solve_all. cbn. solve_all.
    solve_all.
    specialize (H1 (repeat 0 #|bcontext x| ++ Γ') n' (#|bcontext x| + k) Hn).
    forward H1. len.
    forward H1. now rewrite app_assoc.
    rewrite /id. rewrite app_assoc. apply H1.
  - rewrite lift_mkApps. cbn.
    eapply expanded_tFix.
    + solve_all.
      specialize (a
      (rev_map (fun d0 : def term => S (rarg d0))
      (map (map_def (lift n' k) (lift n' (#|mfix| + k))) mfix) ++ Γ') n' (#|mfix| + k) Hn).
      forward a. { rewrite rev_map_spec; len. }
      forward a. { rewrite app_assoc. f_equal. f_equal.
        rewrite !rev_map_spec. f_equal. now rewrite map_map_compose /=. }
      rewrite app_assoc. eapply a.
    + solve_all.
    + destruct args => //.
    + rewrite nth_error_map /= H4 //.
    + len.
  - cbn. constructor.
    solve_all.
    specialize (a (repeat 0 #|mfix| ++ Γ') n' (#|mfix| + k) Hn).
    forward a. { len. }
    forward a. { rewrite app_assoc //. }
    rewrite app_assoc. eapply a.
  - rewrite lift_mkApps. cbn.
    eapply expanded_tConstruct_app; tea. now len.
    solve_all.
  - cbn; constructor. depelim H0; constructor; cbn; eauto. solve_all.
Qed.

Lemma expanded_subst Σ a k b Γ Δ :
    #|Γ| = k ->
  Forall (expanded Σ Δ) a ->
  expanded Σ (Γ ++ repeat 0 #|a| ++ Δ) b ->
  expanded Σ (Γ ++ Δ) (subst a k b).
Proof.
  intros Hk H.
  remember (Γ ++ _ ++ Δ)%list as Γ_.
  intros exp; revert Γ k Hk HeqΓ_.
  induction exp using expanded_ind; intros Γ' k Hk ->.
  all:try solve[ cbn; econstructor => // ].
  2,7:solve[ cbn; econstructor => //; solve_all ].
  - rewrite subst_mkApps /=.
    destruct (Nat.leb_spec k n).
    destruct (nth_error a _) eqn:hnth.
    * eapply expanded_mkApps_expanded.
      eapply nth_error_forall in H; tea.
      eapply (expanded_lift Σ k 0 _ [] Δ Γ'); auto.
      solve_all.
    * rewrite nth_error_app_ge in H0. lia.
      eapply nth_error_None in hnth.
      rewrite nth_error_app_ge in H0. rewrite repeat_length. lia.
      rewrite repeat_length in H0.
      eapply expanded_tRel. rewrite nth_error_app_ge. lia. erewrite <- H0.
      lia_f_equal. len. solve_all.
    * rewrite nth_error_app_lt in H0. lia.
      eapply expanded_tRel. rewrite nth_error_app_lt. lia. tea. now len.
      solve_all.
  - cbn. econstructor.
    eapply (IHexp (0 :: Γ') (S k)); cbn; auto; lia.
  - cbn. econstructor. apply IHexp1; auto.
    eapply (IHexp2 (0 :: Γ') (S k)); cbn; auto; lia.
  - rewrite subst_mkApps.
    destruct (isConstruct (subst a k f6) || isFix (subst a k f6) || isRel (subst a k f6)) eqn:eqc.
    specialize (IHexp  _ _ Hk eq_refl).
    eapply expanded_mkApps_expanded => //. solve_all.
    eapply expanded_mkApps => //. now rewrite eqc. now eapply IHexp. solve_all.
  - cbn. econstructor. eauto. cbn. solve_all. solve_all.
    specialize (H2 (repeat 0 #|bcontext x| ++ Γ') (#|bcontext x| + k)).
    forward H2 by len.
    forward H2. now rewrite app_assoc.
    rewrite /id. rewrite app_assoc. apply H2.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tFix.
    + solve_all. now eapply isLambda_subst.
      specialize (a0
      (rev_map (fun d0 : def term => S (rarg d0))
      (map (map_def (subst a k) (subst a (#|mfix| + k))) mfix) ++ Γ') (#|mfix| + k)).
      forward a0 by len.
      forward a0. { rewrite app_assoc. f_equal. f_equal.
        rewrite !rev_map_spec. f_equal. now rewrite map_map_compose /=. }
      rewrite app_assoc. eapply a0.
    + solve_all.
    + now destruct args.
    + rewrite nth_error_map /= H5 //.
    + len.
  - cbn. constructor.
    solve_all.
    specialize (a0 (repeat 0 #|mfix| ++ Γ') (#|mfix| + k)).
    forward a0 by len.
    forward a0. { rewrite app_assoc //. }
    rewrite app_assoc. eapply a0.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tConstruct_app; tea. now len.
    solve_all.
  - cbn; constructor; eauto.
    depelim H1; constructor; cbn; eauto; solve_all.
Qed.

Lemma expanded_let_expansion Σ (Δ : context) Γ t :
  expanded_context Σ Γ Δ ->
  expanded Σ (repeat 0 #|Δ| ++ Γ) t ->
  expanded Σ (repeat 0 (context_assumptions Δ) ++ Γ) (expand_lets Δ t).
Proof.
  intros [ha].
  revert Γ t ha.
  induction Δ using PCUICInduction.ctx_length_rev_ind.
  - cbn; intros. now rewrite expand_lets_nil.
  - intros Γ' t ha; destruct d as [na [b|] ty]; cbn; len; cbn.
    * rewrite expand_lets_vdef /= //.
      intros exp. relativize (context_assumptions Γ).
      eapply H. now len.
      { eapply All_fold_app_inv in ha as [].
        depelim a. depelim a. cbn in *.
        rewrite /subst_context.
        eapply PCUICParallelReduction.All_fold_fold_context_k.
        eapply All_fold_impl; tea. cbn; intros.
        depelim f.
        destruct decl_body => //; constructor. depelim H1.
        len in H1. cbn in H1.
        cbn. len. eapply expanded_subst. now rewrite repeat_length. eauto.
        auto. cbn. now rewrite repeat_app /= -app_assoc /= in H1. }
      len.
      rewrite repeat_app -app_assoc /= in exp.
      eapply All_fold_app_inv in ha as []. eapply All_fold_tip in a. cbn in a. depelim a.
      eapply expanded_subst. rewrite repeat_length //. constructor; auto.
      cbn. exact exp. now len.
    * rewrite expand_lets_vass /= //.
      rewrite !repeat_app -!app_assoc.
      intros exp. relativize (context_assumptions Γ).
      eapply H. lia.
      { eapply All_fold_app_inv in ha as [].
        depelim a. cbn in f. depelim a.
        eapply All_fold_impl; tea. cbn; intros.
        destruct decl_body => //; constructor. depelim H0. len in H0. cbn in H0.
        now rewrite repeat_app /= -app_assoc /= in H0. }
      exact exp. lia.
Qed.

Lemma subst_instance_isConstruct t u : isConstruct t@[u] = isConstruct t.
Proof. destruct t => //. Qed.
Lemma subst_instance_isRel t u : isRel t@[u] = isRel t.
Proof. destruct t => //. Qed.
Lemma subst_instance_isFix t u : isFix t@[u] = isFix t.
Proof. destruct t => //. Qed.
Lemma subst_instance_isLambda t u : isLambda t@[u] = isLambda t.
Proof. destruct t => //. Qed.

Lemma expanded_subst_instance Σ Γ t u : expanded Σ Γ t -> expanded Σ Γ t@[u].
Proof.
  induction 1 using PCUICEtaExpand.expanded_ind; cbn.
  all:intros; rewrite ?subst_instance_mkApps.
  all:try solve [econstructor; eauto 1].
  - econstructor; eauto. now rewrite length_map. solve_all.
  - econstructor; eauto. solve_all.
  - econstructor; eauto. 2:solve_all.
    rewrite subst_instance_isConstruct subst_instance_isFix subst_instance_isRel //.
  - econstructor; eauto. cbn. solve_all.
    solve_all.
  - cbn; eapply expanded_tFix. solve_all. rewrite subst_instance_isLambda //.
    rewrite rev_map_spec map_map_compose -rev_map_spec //.
    solve_all. now destruct args => //.
    rewrite nth_error_map H4 //.
    now len.
  - econstructor; eauto. solve_all.
  - eapply expanded_tConstruct_app; tea. now len. solve_all.
  - constructor. depelim H0; constructor; cbn; eauto; solve_all.
Qed.

Lemma expanded_weakening Σ Γ t : expanded Σ Γ t -> forall Γ', expanded Σ (Γ ++ Γ') t.
Proof.
  induction 1 using PCUICEtaExpand.expanded_ind; cbn.
  1:{ intros. eapply expanded_tRel; tea. rewrite nth_error_app_lt.
     now eapply nth_error_Some_length in H. assumption.
    solve_all. }
  all:intros; try solve [econstructor; cbn; eauto 1; solve_all; try now rewrite app_assoc].
  constructor. depelim H0; constructor; cbn; eauto; solve_all.
Qed.


Lemma expanded_tApp (Σ : global_env) (Γ : list nat) (f : term) a :
  expanded Σ Γ f -> expanded Σ Γ a ->
  expanded Σ Γ (tApp f a).
Proof.
  induction 1 using expanded_ind; intros expa.
  all:rewrite -?[tApp _ a](mkApps_app _ _ [a]).
  all:try (eapply (expanded_mkApps _ _ _ [a]) => //; econstructor; eauto).

  - econstructor; tea. rewrite length_app. lia. eapply app_Forall;eauto.
  - econstructor; tea. eapply app_Forall; eauto.
  - eapply expanded_tFix; tea. eapply app_Forall; eauto. eauto. rewrite length_app; cbn; eauto. lia.
  - eapply expanded_tConstruct_app; tea. rewrite length_app ; lia. eapply app_Forall; eauto.
Qed.

Lemma expanded_tApp_inv Σ Γ f a :
  ~ isConstruct (head f) || isFix (head f) || isRel (head f) ->
  expanded Σ Γ (tApp f a) ->
  expanded Σ Γ f /\ expanded Σ Γ a.
Proof.
  intros hf exp; depind exp.
  - destruct args using rev_case; solve_discr; try discriminate.
    rewrite mkApps_app in H3; noconf H3.
    eapply Forall_app in H1 as [? ha]. depelim ha.
    destruct args using rev_case; cbn in hf => //.
    now rewrite !head_mkApps /= in hf.
  - destruct args using rev_case; solve_discr. subst f6.
    eapply IHexp => //.
    rewrite mkApps_app in H2; noconf H2.
    eapply Forall_app in H0 as [? H0]. depelim H0. split => //.
    rewrite !head_mkApps in hf.
    eapply expanded_mkApps => //.
  - destruct args using rev_case; solve_discr. discriminate.
    rewrite mkApps_app in H6; noconf H6.
    eapply Forall_app in H1 as [? h]. depelim h. split => //.
    now rewrite !head_mkApps /= in hf.
  - destruct args using rev_case; solve_discr. discriminate.
    rewrite mkApps_app in H3; noconf H3.
    now rewrite !head_mkApps /= in hf.
Qed.

Lemma expanded_tLambda_inv Σ Γ na t b :
  expanded Σ Γ (tLambda na t b) ->
  expanded Σ (0 :: Γ) b.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tLetIn_inv Σ Γ na t t' b :
  expanded Σ Γ (tLetIn na t t' b) ->
  expanded Σ Γ t /\ expanded Σ (0 :: Γ) b.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tEvar_inv Σ Γ ev l:
  expanded Σ Γ (tEvar ev l) ->
  Forall (expanded Σ Γ) l.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tCase_inv Σ Γ ci p c brs :
  expanded Σ Γ (tCase ci p c brs) ->
  Forall (expanded Σ Γ) (pparams p) /\
  Forall
    (fun br : branch term =>
     ∥ All_fold
         (fun (Δ : list context_decl) (d : context_decl)
          =>
          ForOption
            (fun b : term =>
             expanded Σ
               (repeat 0 #|Δ| ++
                repeat 0 #|pparams p|) b)
            (decl_body d)) (bcontext br) ∥ /\
     expanded Σ (repeat 0 #|bcontext br| ++ Γ) (bbody br))
    brs /\
  expanded Σ Γ c.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tProj_inv Σ Γ p c :
  expanded Σ Γ (tProj p c) ->
  expanded Σ Γ c.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tCoFix_inv Σ Γ mfix idx :
 expanded Σ Γ (tCoFix mfix idx) ->
 Forall (fun d : def term => expanded Σ (repeat 0 #|mfix| ++ Γ) (dbody d)) mfix.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tPrim_inv Σ Γ p :
  expanded Σ Γ (tPrim p) -> onPrim (expanded Σ Γ) p.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.
Import PCUICOnOne.

Module Red1Apps.

  Set Warnings "-notation-overridden".

  Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | red_beta na t b a ts :
    Σ ;;; Γ |- mkApps (tLambda na t b) (a :: ts) ⇝ mkApps (b {0 := a}) ts

  (** Let *)
  | red_zeta na b t b' :
    Σ ;;; Γ |- tLetIn na b t b' ⇝ b' {0 := b}

  | red_rel i body :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      Σ ;;; Γ |- tRel i ⇝ lift0 (S i) body

  (** Case *)
  | red_iota ci c u args p brs br :
      nth_error brs c = Some br ->
      #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
      Σ ;;; Γ |- tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs
          ⇝ iota_red ci.(ci_npar) p args br

  (** Fix unfolding, with guard *)
  | red_fix mfix idx args narg fn :
      unfold_fix mfix idx = Some (narg, fn) ->
      is_constructor narg args = true ->
      Σ ;;; Γ |- mkApps (tFix mfix idx) args ⇝ mkApps fn args

  (** CoFix-case unfolding *)
  | red_cofix_case ip p mfix idx args narg fn brs :
      unfold_cofix mfix idx = Some (narg, fn) ->
      Σ ;;; Γ |- tCase ip p (mkApps (tCoFix mfix idx) args) brs ⇝
          tCase ip p (mkApps fn args) brs

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn :
      unfold_cofix mfix idx = Some (narg, fn) ->
      Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args) ⇝ tProj p (mkApps fn args)

  (** Constant unfolding *)
  | red_delta c decl body (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = Some body ->
      Σ ;;; Γ |- tConst c u ⇝ subst_instance u body

  (** Proj *)
  | red_proj p args u arg:
      nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
      Σ ;;; Γ |- tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ⇝ arg


  | abs_red_l na M M' N : Σ ;;; Γ |- M ⇝ M' -> Σ ;;; Γ |- tLambda na M N ⇝ tLambda na M' N
  | abs_red_r na M M' N : Σ ;;; Γ ,, vass na N |- M ⇝ M' -> Σ ;;; Γ |- tLambda na N M ⇝ tLambda na N M'

  | letin_red_def na b t b' r : Σ ;;; Γ |- b ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na r t b'
  | letin_red_ty na b t b' r : Σ ;;; Γ |- t ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b r b'
  | letin_red_body na b t b' r : Σ ;;; Γ ,, vdef na b t |- b' ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b t r

  | case_red_param ci p params' c brs :
      OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) p.(pparams) params' ->
      Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_pparams p params') c brs

  | case_red_return ci p preturn' c brs :
    Σ ;;; Γ ,,, inst_case_predicate_context p |- p.(preturn) ⇝ preturn' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_preturn p preturn') c brs

  | case_red_discr ci p c c' brs :
    Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c' brs

  | case_red_brs ci p c brs brs' :
      OnOne2 (fun br br' =>
        on_Trel_eq (fun t u => Σ ;;; Γ ,,, inst_case_branch_context p br |- t ⇝ u) bbody bcontext br br')
        brs brs' ->
      Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c brs'

  | proj_red p c c' : Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tProj p c ⇝ tProj p c'

  | app_red_l M1 N1 M2 : Σ ;;; Γ |- M1 ⇝ N1 -> ~~ isApp M1 -> ~~ isFix M1 -> M2 <> nil ->
    Σ ;;; Γ |- mkApps M1 M2 ⇝ mkApps N1 M2

  | app_red_r M2 N2 M1 : ~~ isApp M1 -> OnOne2 (fun M2 N2 => Σ ;;; Γ |- M2 ⇝ N2) M2 N2 -> Σ ;;; Γ |- mkApps M1 M2 ⇝ mkApps M1 N2

  | app_fix_red_ty mfix0 mfix1 idx M2 :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- mkApps (tFix mfix0 idx) M2 ⇝ mkApps (tFix mfix1 idx) M2

  | app_fix_red_body mfix0 mfix1 idx M2 :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- mkApps (tFix mfix0 idx) M2 ⇝ mkApps (tFix mfix1 idx) M2

  | prod_red_l na M1 M2 N1 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na N1 M2
  | prod_red_r na M2 N2 M1 : Σ ;;; Γ ,, vass na M1 |- M2 ⇝ N2 ->
                            Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na M1 N2

  | evar_red ev l l' : OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) l l' -> Σ ;;; Γ |- tEvar ev l ⇝ tEvar ev l'

  | fix_red_ty mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
      Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

  | fix_red_body mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x)))
            mfix0 mfix1 ->
      Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

  | cofix_red_ty mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
      Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx

  | cofix_red_body mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
      Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx

  | array_red_val arr value :
      OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) arr.(array_value) value ->
      Σ ;;; Γ |- tPrim (primArray; primArrayModel arr) ⇝
                 tPrim (primArray; primArrayModel (set_array_value arr value))

  | array_red_def arr def :
      Σ ;;; Γ |- arr.(array_default) ⇝ def ->
      Σ ;;; Γ |- tPrim (primArray; primArrayModel arr) ⇝
                 tPrim (primArray; primArrayModel (set_array_default arr def))

  | array_red_type arr ty :
      Σ ;;; Γ |- arr.(array_type) ⇝ ty ->
      Σ ;;; Γ |- tPrim (primArray; primArrayModel arr) ⇝
            tPrim (primArray; primArrayModel (set_array_type arr ty))

  where " Σ ;;; Γ |- t ⇝ u " := (red1 Σ Γ t u).

  Derive Signature for red1.

  Lemma red1_ind_all :
    forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : aname) (t b a : term) ts,
        P Γ (mkApps (tLambda na t b) (a :: ts)) (mkApps (b {0 := a}) ts)) ->

       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

       (forall (Γ : context) p (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ci : case_info) p params' c brs,
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) p.(pparams) params' ->
           P Γ (tCase ci p c brs)
               (tCase ci (set_pparams p params') c brs)) ->

       (forall (Γ : context) (ci : case_info) p preturn' c brs,
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_preturn p preturn') c brs)) ->

       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ci p c brs brs',
          OnOne2 (fun br br' =>
          (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, inst_case_branch_context p br))
            (P (Γ ,,, inst_case_branch_context p br)))
            bbody bcontext br br')) brs brs' ->
          P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) M1 N1 M2, red1 Σ Γ M1 N1 -> P Γ M1 N1 -> ~~ isApp M1 -> ~~ isFix M1 -> M2 <> [] ->
                                                         P Γ (mkApps M1 M2) (mkApps N1 M2)) ->

       (forall (Γ : context) M1 N2 M2, ~~ isApp M1 ->
        OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) M2 N2 ->
        P Γ (mkApps M1 M2) (mkApps M1 N2)) ->

      (forall (Γ : context) mfix0 mfix1 idx M2,
        OnOne2 (on_Trel_eq (Trel_conj (fun t u => Σ ;;; Γ |- t ⇝ u) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (mkApps (tFix mfix0 idx) M2) (mkApps (tFix mfix1 idx) M2)) ->

      (forall (Γ : context) mfix0 mfix1 idx M2,
        OnOne2 (on_Trel_eq (Trel_conj (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) (P (Γ ,,, fix_context mfix0))) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (mkApps (tFix mfix0 idx) M2) (mkApps (tFix mfix1 idx) M2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

        (forall (Γ : context) (arr : array_model term)
          (value : list term),
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) (array_value arr) value ->
          P Γ (tPrim (primArray; primArrayModel arr))
            (tPrim (primArray; primArrayModel (set_array_value arr value)))) ->

        (forall (Γ : context) (arr : array_model term)
          (def : term), Σ;;; Γ |- array_default arr ⇝ def ->
        P Γ (array_default arr) def ->
        P Γ (tPrim (primArray; primArrayModel arr))
          (tPrim (primArray; primArrayModel (set_array_default arr def)))) ->

       (forall (Γ : context) (arr : array_model term)
          (ty : term), Σ;;; Γ |- array_type arr ⇝ ty ->
        P Γ (array_type arr) ty ->
        P Γ (tPrim (primArray; primArrayModel arr))
          (tPrim (primArray; primArrayModel (set_array_type arr ty)))) ->


       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
  Proof.
    intros. rename X32 into Xlast. revert Γ t t0 Xlast.
    fix aux 4. intros Γ t T.
    move aux at top.
    destruct 1; match goal with
                | |- P _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - eapply X3; eauto.
    - eapply X4; eauto.
    - eapply X5; eauto.

    - revert params' o.
      generalize (pparams p).
      fix auxl 3.
      intros params params' [].
      + constructor. split; auto.
      + constructor. auto.

    - revert brs' o.
      revert brs.
      fix auxl 3.
      intros l l' Hl. destruct Hl.
      + simpl in *. constructor; intros; intuition auto.
      + constructor. eapply auxl. apply Hl.

    - revert M2 N2 o.
      fix auxl 3.
      intros l l' Hl. destruct Hl.
      + constructor. split; auto.
      + constructor. auto.

    - eapply X20.
      revert mfix0 mfix1 o.
      fix auxl 3.
      intros l l' Hl. destruct Hl.
      + constructor; split; auto; intuition.
      + constructor; try split; auto; intuition.

    - eapply X21. revert o.
      generalize (fix_context mfix0).
      intros c o. revert mfix0 mfix1 o.
      fix auxl 3.
      intros l l' Hl. destruct Hl.
      + constructor. split; auto; intuition.
      + constructor; try split; auto; intuition.

    - revert l l' o.
      fix auxl 3.
      intros l l' Hl. destruct Hl.
      + constructor. split; auto.
      + constructor. auto.

    - eapply X25.
      revert mfix0 mfix1 o; fix auxl 3.
      intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

    - eapply X26.
      revert o. generalize (fix_context mfix0). intros c Xnew.
      revert mfix0 mfix1 Xnew; fix auxl 3; intros l l' Hl;
      destruct Hl; constructor; try split; auto; intuition.

    - eapply X27.
      revert mfix0 mfix1 o.
      fix auxl 3; intros l l' Hl; destruct Hl;
        constructor; try split; auto; intuition.

    - eapply X28.
      revert o. generalize (fix_context mfix0). intros c new.
      revert mfix0 mfix1 new; fix auxl 3; intros l l' Hl; destruct Hl;
        constructor; try split; auto; intuition.

    - revert value o. generalize (array_value arr).
        fix auxl 3; intros l l' Hl; destruct Hl;
       constructor; try split; auto; intuition.
  Defined.

  Lemma red_tApp Σ Γ t v u :
    red1 Σ Γ t v ->
    red1 Σ Γ (tApp t u) (tApp v u).
  Proof.
    induction 1.
    all:try solve [eapply (app_red_l _ _ _ _ [u]) => //; econstructor; eauto].
    - rewrite -![tApp _ u](mkApps_app _ _ [u]).
      eapply red_beta.
    - rewrite -![tApp _ u](mkApps_app _ _ [u]). econstructor; eauto.
      now apply is_constructor_app_ge.
    - rewrite -![tApp _ u](mkApps_app _ _ [u]). econstructor; eauto.
    - rewrite -![tApp _ u](mkApps_app _ _ [u]). econstructor; eauto.
      now eapply OnOne2_app_r.
    - rewrite -![tApp _ u](mkApps_app _ _ [u]). now eapply app_fix_red_ty.
    - rewrite -![tApp _ u](mkApps_app _ _ [u]). now eapply app_fix_red_body.
    - now eapply (app_fix_red_ty _ _ _ _ _ [_]).
    - now eapply (app_fix_red_body _ _ _ _ _ [_]).
  Qed.

  Lemma isLambda_red1 Σ Γ b b' : isLambda b -> red1 Σ Γ b b' -> isLambda b'.
  Proof.
    destruct b; simpl; try discriminate.
    intros _ red.
    depelim red; solve_discr; eauto. depelim o.
  Qed.

End Red1Apps.

Lemma red1_red1apps Σ Γ t v :
  red1 Σ Γ t v -> Red1Apps.red1 Σ Γ t v.
Proof.
  intros red; induction red using red1_ind_all in |- *.
  all:try solve [econstructor; eauto; solve_all; eauto].
  - eapply (Red1Apps.red_beta _ _ _ _ _ _ []).
  - now eapply Red1Apps.red_tApp.
  - remember (decompose_app (tApp M1 M2)).
    destruct p as [hd args].
    edestruct (decompose_app_rec_inv' M1 [M2]). rewrite /decompose_app in Heqp.
    cbn in Heqp. rewrite -Heqp. reflexivity.
    destruct a as [napp [hm2 hm1]].
    symmetry in Heqp; eapply decompose_app_inv in Heqp. rewrite Heqp.
    assert (tApp M1 N2 = mkApps hd (firstn x args ++ [N2])) as ->.
    { now rewrite mkApps_app -hm1. }
    rewrite -{1}(firstn_skipn x args) -hm2. eapply Red1Apps.app_red_r => //.
    eapply OnOne2_app. now constructor.
Qed.

Lemma head_nApp f :
  ~~ isApp f -> head f = f.
Proof.
  induction f => //.
Qed.

Lemma expanded_mkApps_inv Σ Γ f v :
  ~~ isApp f ->
  ~~ (isConstruct f || isFix f || isRel f) ->
  expanded Σ Γ (mkApps f v) ->
  expanded Σ Γ f /\ Forall (expanded Σ Γ) v.
Proof.
  intros happ hc.
  induction v using rev_ind; cbn.
  - intros exp; split => //.
  - rewrite mkApps_app /=.
    move/expanded_tApp_inv => e.
    forward e. rewrite head_mkApps.
    rewrite head_nApp //. now move/negbTE: hc ->.
    intuition auto. eapply app_Forall; eauto.
Qed.

Lemma expanded_mkApps_inv' Σ Γ f :
  expanded Σ Γ f ->
  let args := arguments f in
  Forall (expanded Σ Γ) args /\
    match head f with
    | tRel n => exists m, nth_error Γ n = Some m /\ m <= #|args|
    | tConstruct ind c u => exists mind idecl cdecl,
      declared_constructor Σ (ind, c) mind idecl cdecl /\ #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl)
    | tFix mfix idx => exists d,
      Forall
        (fun d0 : def term =>
        isLambda (dbody d0) /\
        (let ctx :=
            rev_map (fun d1 : def term => (1 + rarg d1)%nat)
              mfix in
          expanded Σ (ctx ++ Γ) (dbody d0))) mfix /\
      args <> [] /\
      nth_error mfix idx = Some d /\ #|args| > rarg d
    | _ => expanded Σ Γ (head f)
    end.
Proof.
  induction 1 using expanded_ind; cbn.
  all: try solve [split; econstructor; eauto].
  all:rewrite head_mkApps /=.
  - rewrite arguments_mkApps_nApp //. split => //. now exists m.
  - destruct IHexpanded. rewrite arguments_mkApps. split.
    eapply app_Forall => //.
    rewrite length_app.
    destruct (head f6) => //; firstorder (eauto; try lia).
    exists x. split => //. firstorder (eauto; try lia).
    intros heq; apply H5. now eapply app_eq_nil in heq.
  - rewrite arguments_mkApps_nApp //. split => //. now exists d.
  - rewrite arguments_mkApps_nApp //. split => //.
    firstorder.
Qed.

Lemma All_fold_map_context (P : context -> context_decl -> Type) (f : term -> term) ctx :
  All_fold P (map_context f ctx) <~> All_fold (fun Γ d => P (map_context f Γ) (map_decl f d)) ctx.
Proof.
  induction ctx.
  - split; constructor.
  - cbn. split; intros H; depelim H; constructor; auto; now apply IHctx.
Qed.

Lemma expanded_fix_subst Σ a k b Γ Γs Δ :
  #|Γ| = k ->
  Forall2 (fun n arg => forall args Γ' k',
    Forall (expanded Σ (Γ' ++ Δ)) args ->
    n <= #|args| ->
    #|Γ'| = k' ->
    expanded Σ (Γ' ++ Δ) (mkApps (lift0 k' arg) args)) Γs a ->
  expanded Σ (Γ ++ Γs ++ Δ) b ->
  expanded Σ (Γ ++ Δ) (subst a k b).
Proof.
  intros Hk Hs.
  remember (Γ ++ _ ++ Δ)%list as Γ_.
  intros exp; revert Γ k Hk HeqΓ_.
  induction exp using expanded_ind; intros Γ' k Hk ->.
  all:try solve[ cbn; econstructor => // ].
  2,7:solve[ cbn; econstructor => //; solve_all ].
  - rewrite subst_mkApps /=.
    destruct (Nat.leb_spec k n).
    destruct (nth_error a _) eqn:hnth.
    * pose proof (Forall2_length Hs).
      pose proof (Forall2_nth_error_Some_r _ _ _ _ _ _ _ hnth Hs) as [t' [hnth' hargs]].
      eapply hargs => //.
      eapply Forall_map.
      2:{ len. rewrite nth_error_app_ge in H. lia. subst k.
        rewrite nth_error_app_lt in H.
        eapply nth_error_Some_length in hnth'. lia. rewrite hnth' in H. noconf H. exact H0. }
      solve_all.
    * rewrite nth_error_app_ge in H. lia.
      eapply nth_error_None in hnth.
      pose proof (Forall2_length Hs).
      rewrite nth_error_app_ge in H. lia.
      eapply expanded_tRel. rewrite nth_error_app_ge. lia. erewrite <- H.
      lia_f_equal. len. solve_all.
    * rewrite nth_error_app_lt in H. lia.
      eapply expanded_tRel. rewrite nth_error_app_lt. lia. tea. now len.
      solve_all.
  - cbn. econstructor.
    eapply (IHexp (0 :: Γ') (S k)); cbn; auto; try lia.
  - cbn. econstructor. apply IHexp1; auto.
    eapply (IHexp2 (0 :: Γ') (S k)); cbn; auto; lia.
  - rewrite subst_mkApps.
    destruct (isConstruct (subst a k f6) || isFix (subst a k f6) || isRel (subst a k f6)) eqn:eqc.
    specialize (IHexp  _ _ Hk eq_refl).
    eapply expanded_mkApps_expanded => //. solve_all.
    eapply expanded_mkApps => //. rewrite eqc //. now eapply IHexp. solve_all.
  - cbn. econstructor. eauto. cbn. solve_all. solve_all.
    specialize (H1 (repeat 0 #|bcontext x| ++ Γ') (#|bcontext x| + k)%nat).
    forward H1 by len.
    forward H1. now rewrite app_assoc.
    rewrite /id. rewrite app_assoc. apply H1.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tFix.
    + solve_all. now eapply isLambda_subst.
      specialize (a0
      (rev_map (fun d0 : def term => S (rarg d0))
      (map (map_def (subst a k) (subst a (#|mfix| + k))) mfix) ++ Γ') (#|mfix| + k)%nat).
      forward a0 by len.
      forward a0. { rewrite app_assoc. f_equal. f_equal.
        rewrite !rev_map_spec. f_equal. now rewrite map_map_compose /=. }
      rewrite app_assoc. eapply a0.
    + solve_all.
    + now destruct args.
    + rewrite nth_error_map /= H4 //.
    + len.
  - cbn. constructor.
    solve_all.
    specialize (a0 (repeat 0 #|mfix| ++ Γ') (#|mfix| + k)%nat).
    forward a0 by len.
    forward a0. { rewrite app_assoc //. }
    rewrite app_assoc. eapply a0.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tConstruct_app; tea. now len.
    solve_all.
  - cbn; econstructor; eauto.
    depelim H0; constructor; cbn; eauto; solve_all.
Qed.

Lemma expanded_unfold_fix Σ Γ' mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  All (fun d0 : def term => isLambda (dbody d0) /\ expanded Σ (rev_map (fun d1 : def term => S (rarg d1)) mfix ++ Γ') (dbody d0)) mfix ->
  expanded Σ Γ' fn.
Proof.
  unfold unfold_fix.
  destruct nth_error eqn:e => //.
  intros [= <- <-] hf.
  pose proof (nth_error_all e hf) as [hl hf'].
  eapply (expanded_fix_subst _ _ _ _ []) => //; tea.
  rewrite rev_map_spec.
  eapply Forall2_from_nth_error. len.
  intros n rarg f. len. intros hn hrarg hnthf args Γ'' k' hargs hrarg' <-.
  eapply PCUICParallelReductionConfluence.nth_error_fix_subst in hnthf. subst f.
  move: hrarg.
  rewrite nth_error_rev; len. rewrite List.rev_involutive nth_error_map.
  intros hrarg.
  destruct (nth_error mfix (_ - _)) eqn:e'. cbn in hrarg. noconf hrarg.
  eapply expanded_tFix => //. solve_all.
  eapply expanded_lift; len. rewrite !rev_map_spec in H1 *.
  rewrite map_map => //. destruct args => //. cbn in hrarg'. lia.
  rewrite nth_error_map /= e' /= //. cbn. lia.
  eapply nth_error_None in e'. lia.
Qed.

Lemma expanded_unfold_cofix Σ Γ' mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  All (fun d0 : def term => expanded Σ (repeat 0 #|mfix| ++ Γ') (dbody d0)) mfix ->
  expanded Σ Γ' fn.
Proof.
  unfold unfold_cofix.
  destruct nth_error eqn:e => //.
  intros [= <- <-] hf.
  pose proof (nth_error_all e hf) as hf'.
  eapply (expanded_subst _ _ _ _ []) => //; tea.
  rewrite /cofix_subst.
  generalize #|mfix|.
  induction n; repeat constructor; eauto. solve_all.
  len.
Qed.

Lemma expanded_weakening_env {cf : checker_flags} Σ Σ' Γ t :
  wf Σ' ->
  extends Σ Σ' ->
  expanded Σ Γ t -> expanded Σ' Γ t.
Proof.
  intros w s.
  eapply expanded_ind; intros.
  all:try solve [econstructor; eauto].
  - econstructor; eauto. solve_all. sq. eapply All_fold_impl; tea. cbn.
    intros. now rewrite repeat_app in H6.
  - eapply expanded_tFix; eauto. solve_all.
  - eapply expanded_tConstruct_app; eauto.
    eapply PCUICWeakeningEnv.weakening_env_declared_constructor; tea.
Qed.

Lemma expanded_global_env_constant {cf : checker_flags} Σ c decl :
  wf Σ ->
  expanded_global_env Σ ->
  declared_constant Σ c decl ->
  ForOption (expanded Σ []) (cst_body decl).
Proof.
  intros wf; destruct Σ as [Σ univs] => /=. cbn.
  unfold expanded_global_env. cbn.
  induction 1; cbn => //.
  intros [->|H'].
  - depelim H0.
    destruct decl as [? [] ?]; cbn in *.
    constructor. cbn.
    eapply expanded_weakening_env; tea.
    eapply extends_strictly_on_decls_extends.
    split => //=. eapply incl_cs_refl. 2:eapply Retroknowledge.extends_refl.
    set (cb := ConstantDecl _). now exists [(c, cb)].
    constructor.
  - forward IHexpanded_global_declarations.
    destruct wf. cbn in *. split => //.
    cbn. now depelim o0.
    eapply IHexpanded_global_declarations in H'.
    destruct decl as [? [] ?]; cbn in * => //. 2:constructor.
    depelim H'. constructor.
    eapply expanded_weakening_env; tea.
    eapply extends_strictly_on_decls_extends.
    split => //=. eapply incl_cs_refl. 2:eapply Retroknowledge.extends_refl.
    now exists [decl0].
Qed.

Lemma All_fold_nth_error P (ctx : context) n b :
  All_fold P ctx -> nth_error ctx n = Some b ->
  P (skipn (S n) ctx) b.
Proof.
  induction 1 in n, b |- *.
  - rewrite nth_error_nil //.
  - destruct n => //=.
    * intros [= <-]. now rewrite skipn_S skipn_0.
    * intros hnth. now rewrite skipn_S.
Qed.

Lemma skipn_repeat {A} k n (a : A) :
  skipn n (repeat a k) = repeat a (k - n).
Proof.
  induction n in k |- *.
  - rewrite skipn_0. lia_f_equal.
  - destruct k => //=.
    rewrite skipn_S IHn. lia_f_equal.
Qed.

Lemma expanded_red1 {cf : checker_flags} {Σ : global_env_ext} Γ Γ' t v : wf Σ ->
  expanded_global_env Σ ->
  (forall n body, option_map decl_body (nth_error Γ n) = Some (Some body) -> expanded Σ (skipn (S n) Γ') body) ->
  red1 Σ Γ t v ->
  expanded Σ Γ' t ->
  expanded Σ Γ' v.
Proof.
  move=> wf expΣ wfΓ /red1_red1apps red.
  induction red using Red1Apps.red1_ind_all in wfΓ, Γ' |- *;  intros exp.
  - eapply expanded_mkApps_inv in exp as [] => //.
    eapply expanded_tLambda_inv in H.
    depelim H0.
    eapply expanded_mkApps_expanded => //.
    eapply (expanded_subst _ _ _ _ [] Γ') => //. now constructor. solve_all.
  - eapply expanded_tLetIn_inv in exp as [].
    eapply (expanded_subst _ _ _ _ [] Γ') => //. now constructor.
  - rewrite -(firstn_skipn (S i) Γ').
    eapply expanded_mkApps_inv' in exp; cbn in exp.
    destruct exp as [_ [m []]]. eapply nth_error_Some_length in H0.
    eapply (expanded_lift _ _ _ _ []) => //.
    rewrite firstn_length_le; try lia.
    now eapply wfΓ.
  - eapply expanded_tCase_inv in exp as [? []].
    unfold iota_red.
    move/expanded_mkApps_inv': H3 => /=.
    rewrite arguments_mkApps_nApp // head_mkApps //=.
    intros [hargs [mind [idecl [cdecl [declc hargs']]]]].
    eapply nth_error_forall in H2; tea.
    destruct H2 as [[hbctx] hbod].
    eapply (expanded_subst _ _ _ _ [] _) => //.
    + eapply Forall_rev, Forall_skipn => //.
    + len. replace #|skipn (ci_npar ci) args| with (context_assumptions (inst_case_branch_context p br)).
      eapply expanded_let_expansion; len. red.
      sq. rewrite /inst_case_branch_context /inst_case_context /subst_context.
      eapply PCUICParallelReduction.All_fold_fold_context_k.
      eapply All_fold_map_context, All_fold_impl; tea; cbn.
      intros ? ? fo. len. destruct x as [? [] ?] => //; constructor.
      cbn in fo. depelim fo. eapply (expanded_subst _ _ _ _ (repeat 0 #|Γ0|) _); len.
      eapply Forall_rev; eauto.
      eapply expanded_subst_instance. rewrite app_assoc. now eapply expanded_weakening.
      rewrite length_skipn. len.
  - move/expanded_mkApps_inv': exp. cbn.
    rewrite arguments_mkApps_nApp // head_mkApps //=.
    move=> [hargs [d [hf [hargs' []]]]] hnth hrarg.
    eapply expanded_mkApps_expanded => //; solve_all.
    eapply expanded_unfold_fix in H; tea.
  - eapply expanded_tCase_inv in exp as [? []].
    constructor => //.
    eapply expanded_mkApps_inv' in H2. move: H2; rewrite arguments_mkApps_nApp // head_mkApps //=.
    intros [hargs' hcof]. cbn in hcof. eapply expanded_tCoFix_inv in hcof.
    eapply expanded_unfold_cofix in H; tea. eapply expanded_mkApps_expanded; tea => //; solve_all. solve_all.
  - eapply expanded_tProj_inv in exp. econstructor.
    eapply expanded_mkApps_inv' in exp. move: exp; rewrite arguments_mkApps_nApp // head_mkApps //=.
    intros [hargs' hcof]. cbn in hcof. eapply expanded_tCoFix_inv in hcof.
    eapply expanded_mkApps_expanded => //; solve_all.
    eapply expanded_unfold_cofix in H; tea.
  - eapply expanded_subst_instance.
    eapply expanded_global_env_constant in expΣ; tea.
    eapply (expanded_weakening _ []). rewrite H0 in expΣ. now depelim expΣ.
  - eapply expanded_tProj_inv in exp.
    move/expanded_mkApps_inv': exp. rewrite arguments_mkApps_nApp // head_mkApps //=.
    intros [].
    eapply nth_error_forall in H0; tea.
  - constructor. now eapply expanded_tLambda_inv in exp.
  - constructor. eapply expanded_tLambda_inv in exp.
    eapply IHred => //.
    { intros [] body; cbn => //. rewrite skipn_S. eapply wfΓ. }
  - eapply expanded_tLetIn_inv in exp; now constructor.
  - eapply expanded_tLetIn_inv in exp. now constructor.
  - eapply expanded_tLetIn_inv in exp. constructor; intuition eauto.
    eapply IHred => //.
    { intros [] ? => //=. intros [=]. subst b. now rewrite skipn_S skipn_0.
      rewrite skipn_S. eapply wfΓ. }
  - eapply expanded_tCase_inv in exp as [? []].
    constructor; eauto. cbn.
    solve_all. eapply OnOne2_impl_All_r; tea. intuition eauto. now apply X0.
    now rewrite /PCUICOnOne.set_pparams /= -(OnOne2_length X).
  - eapply expanded_tCase_inv in exp as [? []].
    constructor; eauto.
  - eapply expanded_tCase_inv in exp as [? []].
    econstructor; eauto.
  - eapply expanded_tCase_inv in exp as [? []].
    econstructor; eauto. solve_all.
    eapply OnOne2_impl_All_r; tea.
    intros x y [? ?]. intros [[] ?]. rewrite -e0.
    solve_all. eapply e => //.
    intros n b.
    clear -H H2 wfΓ.
    destruct nth_error eqn:e' => //.
    cbn. intros [=]. destruct c as [? [] ?]. cbn in *. noconf H1.
    eapply nth_error_app_inv in e' as [[]|[]].
    { rewrite inst_case_branch_context_length in H0. destruct H2.
      rewrite /inst_case_branch_context /inst_case_context in H1.
      destruct (nth_error (bcontext x) n) eqn:e.
      2:{ eapply nth_error_None in e. rewrite skipn_app skipn_all2. len. cbn. len. }
      rewrite /subst_context in H1.
      erewrite nth_error_fold_context_k in H1. 4:{ rewrite nth_error_map e //. } 3:len. 2:exact [].
      len in H1. noconf H1. destruct c as [? [] ?]; noconf H1.
      rewrite skipn_app. len. eapply All_fold_nth_error in X; tea. cbn in X. depelim X.
      rewrite length_skipn in H1.
      eapply expanded_subst. rewrite length_skipn. len.
      replace (S n - #|bcontext x|) with 0. 2:{ lia. } rewrite skipn_0. eapply Forall_rev. solve_all.
      len. rewrite app_assoc. eapply expanded_weakening. eapply expanded_subst_instance.
      now rewrite skipn_repeat. }
    { rewrite inst_case_branch_context_length in H0, H1.
      rewrite skipn_app skipn_all2 /=; len.
      replace (S n - #|bcontext x|) with (S (n - #|bcontext x|)). 2:lia.
      eapply wfΓ. rewrite H1 //. }
    noconf H1.
  - eapply expanded_tProj_inv in exp. now econstructor.
  - eapply expanded_mkApps_inv' in exp.
    rewrite head_mkApps head_nApp in exp => //.
    rewrite arguments_mkApps_nApp // in exp. destruct exp as [].
    specialize (IHred Γ' wfΓ).
    destruct M1; try solve [eapply expanded_mkApps_expanded => //; eauto; solve_all].
    * depelim red; solve_discr. eapply wfΓ in e.
      eapply expanded_mkApps_expanded => //; solve_all.
      rewrite -(firstn_skipn (S n) Γ'). eapply (expanded_lift _ _ _ _ []) => //.
      destruct H3 as [m [hn ha]].
      rewrite firstn_length_le //. now eapply nth_error_Some_length in hn.
      depelim o.
    * depelim red; solve_discr. depelim o.

  - eapply expanded_mkApps_inv' in exp.
    move: exp.
    rewrite head_mkApps head_nApp // arguments_mkApps_nApp //.
    intros [].
    assert(Forall (expanded Σ Γ') N2).
    { clear H1. solve_all. eapply OnOne2_impl_All_r; tea. cbn. intuition auto. }
    destruct M1; try solve [eapply expanded_mkApps => //; eauto].
    + rewrite (OnOne2_length X) in H1. destruct H1 as [m []]; eapply expanded_tRel; tea.
    + rewrite (OnOne2_length X) in H1. destruct H1 as [m [? [? []]]]; eapply expanded_tConstruct_app; tea.
    + rewrite (OnOne2_length X) in H1.
      destruct H1 as [d [? [? []]]]; eapply expanded_tFix; tea.
      destruct N2; cbn in *; eauto. lia. intros eq; discriminate.

  - move/expanded_mkApps_inv': exp.
    rewrite head_mkApps head_nApp // arguments_mkApps_nApp // => [] [] hargs [d [hf [hm2 [hnth harg]]]].
    eapply OnOne2_nth_error in hnth as [t' [hnth hor]]; tea.
    eapply expanded_tFix; tea.
    { clear hor. solve_all. eapply OnOne2_impl_All_r; tea.
      intros ? ? [] []. noconf e. rewrite -H2. split => //. solve_all.
      clear -X H1.
      enough (rev_map (fun d1 : def term => S (rarg d1)) mfix0 = (rev_map (fun d1 : def term => S (rarg d1)) mfix1)) as <- => //.
      clear -X. rewrite !rev_map_spec. f_equal. induction X. destruct p as []. cbn in *. congruence. cbn. congruence. }
    { destruct hor; subst => //. destruct p as [? e]; noconf e. now congruence. }

  - move/expanded_mkApps_inv': exp.
    rewrite head_mkApps head_nApp // arguments_mkApps_nApp // => [] [] hargs [d [hf [hm2 [hnth harg]]]].
    eapply OnOne2_nth_error in hnth as [t' [hnth hor]]; tea.
    eapply expanded_tFix; tea.
    { clear hor. solve_all.
      assert (rev_map (fun d1 : def term => S (rarg d1)) mfix0 = (rev_map (fun d1 : def term => S (rarg d1)) mfix1)).
      { clear -X. rewrite !rev_map_spec. f_equal. induction X. destruct p as []. cbn in *. congruence. cbn. congruence. }
      rewrite -H.
      eapply OnOne2_impl_All_r; tea.
      intros ? ? [] []. noconf e. destruct p.
      eapply Red1Apps.isLambda_red1 in r; tea. split => //.
      set(Γ'' := rev_map (fun d1 : def term => S (rarg d1)) mfix0).
      eapply e => //.
      { intros n b hnth'.
        destruct (nth_error (fix_context mfix0) n) eqn:e'.
        rewrite nth_error_app_lt in hnth'. now eapply nth_error_Some_length in e'.
        rewrite e' in hnth'. noconf hnth'.
        pose proof (PCUICParallelReductionConfluence.fix_context_assumption_context mfix0).
        eapply PCUICParallelReductionConfluence.nth_error_assumption_context in H6; tea. congruence.
        rewrite /Γ''.
        eapply nth_error_None in e'. len in e'.
        rewrite nth_error_app_ge in hnth' => //. now len.
        rewrite skipn_app skipn_all2. len.
        cbn. len. replace (S n - #|mfix0|) with (S (n - #|mfix0|)). 2:{ lia. }
        eapply wfΓ. now len in hnth'. } }
    { destruct hor; subst => //. destruct p as [? e]; noconf e. now congruence. }
  - eapply expanded_tProd.
  - constructor.
  - constructor.
    eapply expanded_tEvar_inv in exp.
    solve_all; eapply OnOne2_impl_All_r; tea. intuition eauto.
    now eapply X0.
  - depelim exp; solve_discr. now cbn in H.
  - depelim exp; solve_discr. now cbn in H.
  - eapply expanded_tCoFix_inv in exp. econstructor.
    rewrite -(OnOne2_length X). solve_all; eapply OnOne2_impl_All_r; tea; intuition eauto.
    destruct X0. noconf e. now rewrite -H1.
  - eapply expanded_tCoFix_inv in exp. econstructor.
    rewrite -(OnOne2_length X). solve_all; eapply OnOne2_impl_All_r; tea; intuition eauto.
    destruct X0. destruct p. noconf e. eapply e0 => //.
    intros n b.
    destruct nth_error eqn:e' => //.
    cbn. intros [=]. destruct c as [? [] ?]. cbn in *. noconf H4.
    eapply nth_error_app_inv in e' as [[]|[]].
    { pose proof (PCUICParallelReductionConfluence.fix_context_assumption_context mfix0).
      eapply PCUICParallelReductionConfluence.nth_error_assumption_context in H5; tea. cbn in H5. congruence. }
    len in H3. len in H4.
    rewrite skipn_app skipn_all2; len.
    replace (S n - #|mfix0|) with (S (n - #|mfix0|)) by lia. eapply wfΓ. rewrite H4 /= //.
    noconf H4.
  - constructor. eapply expanded_tPrim_inv in exp.
    depelim exp; eauto. constructor; cbn; eauto.
    eapply OnOne2_impl_All_r; tea; cbn; intuition eauto.
  - constructor. eapply expanded_tPrim_inv in exp.
    depelim exp; eauto. constructor; cbn; eauto.
  - constructor. eapply expanded_tPrim_inv in exp.
    depelim exp; eauto. constructor; cbn; eauto.
Qed.

Lemma expanded_red {cf : checker_flags} {Σ : global_env_ext} Γ Γ' t v : wf Σ ->
  expanded_global_env Σ ->
  (forall n body, option_map decl_body (nth_error Γ n) = Some (Some body) -> expanded Σ (skipn (S n) Γ') body) ->
  red Σ Γ t v ->
  expanded Σ Γ' t ->
  expanded Σ Γ' v.
Proof.
  intros.
  induction X0. now eapply expanded_red1. auto.
  eapply IHX0_2. now eapply IHX0_1.
Qed.

Lemma expanded_tApp_arg Σ Γ t u : expanded Σ Γ (tApp t u) -> expanded Σ Γ u.
Proof.
  move/expanded_mkApps_inv' => [expa _].
  move: expa; rewrite (arguments_mkApps t [u]).
  move/Forall_app => [] _ hu; now depelim hu.
Qed.
