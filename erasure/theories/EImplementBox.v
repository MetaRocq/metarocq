(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst EnvMap.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction EArities
    ELiftSubst ESpineView EGlobalEnv EWellformed EEnvMap
    EWcbvEval EEtaExpanded ECSubst EWcbvEvalEtaInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

(** We assume [Prop </= Type] and universes are checked correctly in the following. *)
(* Local Existing Instance extraction_checker_flags. *)
Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors eval : core.

Import MRList (map_InP, map_InP_elim, map_InP_spec).

Section implement_box.
  Context (Σ : global_declarations).

  Section Def.

  Definition iBox :=
   tFix [ {| dname := nNamed "reccall" ; dbody := tLambda nAnon (tRel 1) ; rarg := 0 |} ] 0.

  Equations? implement_box (t : term) : term
    by wf t (fun x y : EAst.term => size x < size y) :=
    | tRel i => EAst.tRel i
    | tEvar ev args => EAst.tEvar ev (map_InP args (fun x H => implement_box x))
    | tLambda na M => EAst.tLambda na (implement_box M)
    | tApp u v := tApp (implement_box u) (implement_box v)
    | tLetIn na b b' => EAst.tLetIn na (implement_box b) (implement_box b')
    | tCase ind c brs =>
      let brs' := map_InP brs (fun x H => (x.1, lift 1 #|x.1| (implement_box x.2))) in
      EAst.tLetIn (nNamed "discr") (implement_box c)
      (EAst.tCase (ind.1, 0) (tRel 0) brs')
    | tProj p c => EAst.tProj {| proj_ind := p.(proj_ind); proj_npars := 0; proj_arg := p.(proj_arg) |} (implement_box c)
    | tFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := implement_box d.(dbody); rarg := d.(rarg) |}) in
      EAst.tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := implement_box d.(dbody); rarg := d.(rarg) |}) in
      EAst.tCoFix mfix' idx
    | tBox => iBox
    | tVar n => EAst.tVar n
    | tConst n => EAst.tConst n
    | tConstruct ind i block_args => EAst.tConstruct ind i (map_InP block_args (fun d H => implement_box d))
    | tPrim p => EAst.tPrim (map_primIn p (fun x H => implement_box x))
    | tLazy t => EAst.tLazy (implement_box t)
    | tForce t => EAst.tForce (implement_box t).
  Proof.
    all:try lia.
    all:try apply (In_size); tea.
    all:try lia.
    - setoid_rewrite <- (In_size id size H); unfold id; lia.
    - setoid_rewrite <- (In_size id size H); unfold id; lia.
    - setoid_rewrite <- (In_size snd size H); cbn; lia.
    - setoid_rewrite <- (In_size dbody size H); cbn; lia.
    - setoid_rewrite <- (In_size dbody size H); cbn; lia.
    - now eapply InPrim_size in H.
  Qed.

  End Def.

  #[universes(polymorphic)]
  Hint Rewrite @map_primIn_spec @map_InP_spec : implement_box.

  Arguments eqb : simpl never.

  Opaque implement_box.
  Opaque isEtaExp.
  Opaque isEtaExp_unfold_clause_1.

  Lemma chop_firstn_skipn {A} n (l : list A) : chop n l = (firstn n l, skipn n l).
  Proof using Type.
    induction n in l |- *; destruct l; simpl; auto.
    now rewrite IHn skipn_S.
  Qed.

  Lemma chop_eq {A} n (l : list A) l1 l2 : chop n l = (l1, l2) -> l = l1 ++ l2.
  Proof using Type.
    rewrite chop_firstn_skipn. intros [= <- <-].
    now rewrite firstn_skipn.
  Qed.

  Lemma closed_implement_box t k : closedn k t -> closedn k (implement_box t).
  Proof using Type.
    funelim (implement_box t); simp implement_box; rewrite <-?implement_box_equation_1; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *;
    try solve [simpl; subst; simpl closed; f_equal; auto; rtoProp; solve_all; solve_all]; try easy.
    rtoProp. split. eauto.
    solve_all.
    replace (#|x.1| + S k) with (#|x.1| + k + 1) by lia.
    eapply closedn_lift. eauto.
    try solve [simpl; subst; simpl closed; f_equal; auto; rtoProp; solve_all; solve_all_k 6]; try easy.
  Qed.

  Hint Rewrite @forallb_InP_spec : isEtaExp.
  Transparent isEtaExp_unfold_clause_1.

  Lemma implement_box_lift a k b :
    implement_box (lift a k b) = lift a k (implement_box b).
  Proof.
    revert k.
    funelim (implement_box b); intros k; cbn; simp implement_box; try easy.
    - destruct (Nat.leb_spec k i); reflexivity.
    - f_equal. rewrite !map_map_compose. solve_all.
      eapply In_All. eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros. eapply H; eauto.
    - cbn. do 2 f_equal. 1: eauto.
      rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal.
      replace (#|x.1| + S k) with (S (#|x.1| + k)) by lia.
      erewrite H; eauto.
      rewrite permute_lift. lia.
      f_equal. lia.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. erewrite H; eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. erewrite H; eauto.
    - solve_all_k 6.
  Qed.

  (* Lemma implement_box_subst a k b : *)
  (*   implement_box (subst a k b) = subst (map implement_box a) k (implement_box b). *)
  (* Proof using Type. *)
  (*   revert k. *)
  (*   funelim (implement_box b); intros k; cbn; simp implement_box; try easy. *)
  (*   all: try now (cbn; f_equal; eauto). *)
  (*   - destruct (Nat.leb_spec k i). *)
  (*     + erewrite nth_error_map. *)
  (*       destruct nth_error; cbn. *)
  (*       * now rewrite implement_box_lift. *)
  (*       * len. *)
  (*     + reflexivity. *)
  (*   - f_equal. rewrite !map_map_compose. solve_all. *)
  (*     eapply In_All. eauto. *)
  (*   - cbn. f_equal. rewrite !map_map. solve_all. *)
  (*     eapply In_All. intros. eapply H; eauto. *)
  (*   - cbn. do 2 f_equal. 1: eauto. *)
  (*     rewrite !map_map. solve_all. *)
  (*     eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. *)
  (*     replace (#|x.1| + S k) with (S (#|x.1| + k)) by lia. *)
  (*     rewrite commut_lift_subst. *)
  (*     f_equal. *)
  (*     eapply H; eauto. *)
  (*   - cbn. f_equal. rewrite !map_map. solve_all. *)
  (*     eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. erewrite H; eauto. *)
  (*     f_equal. now rewrite length_map. *)
  (*   - cbn. f_equal. rewrite !map_map. solve_all. *)
  (*     eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. erewrite H; eauto. *)
  (*     f_equal. now rewrite length_map. *)
  (* Qed. *)

  Lemma implement_box_csubst a k b :
    closed a ->
    implement_box (ECSubst.csubst a k b) = ECSubst.csubst (implement_box a) k (implement_box b).
  Proof using Type.
    intros Ha.
    revert k.
    funelim (implement_box b); intros k; cbn; simp implement_box; try easy.
    all: try now (cbn; f_equal; eauto).
    - destruct Nat.compare => //.
    - f_equal. rewrite !map_map_compose. solve_all.
      eapply In_All. eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros. eapply H; eauto.
    - cbn. do 2 f_equal. 1: eauto.
      rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal.
      setoid_rewrite -> closed_subst at 2.
      replace (#|x.1| + S k) with ((#|x.1| + k) + 1) by lia.
      rewrite <- commut_lift_subst_rec. 2: lia.
      rewrite <- closed_subst.
      2, 3: eapply closed_implement_box; eauto.
      f_equal.
      eapply H; eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. solve_all.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. solve_all.
    - cbn. solve_all.
  Qed.

  Lemma implement_box_substl s t :
    All (fun x => closed x) s ->
    implement_box (substl s t) = substl (map implement_box s) (implement_box t).
  Proof using Type.
    induction s in t |- *; simpl; auto; intros Hall.
    inversion Hall.
    rewrite IHs //.
    now rewrite implement_box_csubst.
  Qed.

  Lemma implement_box_iota_red pars args br :
    All (fun x => closed x) args ->
    implement_box (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map implement_box args) (on_snd implement_box br).
  Proof using Type.
    intros Hall.
    unfold EGlobalEnv.iota_red.
    rewrite implement_box_substl //.
    solve_all. now eapply All_skipn.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma implement_box_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def implement_box) mfix) = map implement_box (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp implement_box.
  Qed.

  Lemma implement_box_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def implement_box) mfix) = map implement_box (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp implement_box.
  Qed.

  Lemma implement_box_cunfold_fix mfix idx n f :
    All (λ x : term, closed x) (fix_subst mfix) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def implement_box) mfix) idx = Some (n, implement_box f).
  Proof using Type.
    intros Hcl.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal. f_equal.
    rewrite implement_box_substl //. 2:congruence.
    f_equal. f_equal. apply implement_box_fix_subst.
  Qed.

  Lemma implement_box_cunfold_cofix mfix idx n f :
    All (λ x : term, closed x) (cofix_subst mfix) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def implement_box) mfix) idx = Some (n, implement_box f).
  Proof using Type.
    intros Hcl.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal.
    rewrite implement_box_substl //. 2:congruence.
    f_equal. f_equal. apply implement_box_cofix_subst.
  Qed.

  Lemma implement_box_nth {n l d} :
    implement_box (nth n l d) = nth n (map implement_box l) (implement_box d).
  Proof using Type.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End implement_box.

#[universes(polymorphic)]
Global Hint Rewrite @map_primIn_spec @map_InP_spec : implement_box.

Definition implement_box_constant_decl cb :=
  {| cst_body := option_map implement_box cb.(cst_body) |}.

Definition implement_box_decl d :=
  match d with
  | ConstantDecl cb => ConstantDecl (implement_box_constant_decl cb)
  | InductiveDecl idecl => InductiveDecl idecl
  end.

Definition implement_box_env (Σ : global_declarations) :=
  map (on_snd (implement_box_decl)) Σ.

Definition implement_box_program (p : eprogram) :=
  (implement_box_env p.1, implement_box p.2).

Definition block_wcbv_flags :=
  {| with_prop_case := false ; with_guarded_fix := false ; with_constructor_as_block := true |}.

Local Hint Resolve wellformed_closed : core.

Lemma wellformed_lookup_inductive_pars {efl : EEnvFlags} Σ kn mdecl :
  has_cstr_params = false ->
  wf_glob Σ ->
  lookup_minductive Σ kn = Some mdecl -> mdecl.(ind_npars) = 0.
Proof.
  intros hasp.
  induction 1; cbn => //.
  case: eqb_spec => [|].
  - intros ->. destruct d => //. intros [= <-].
    cbn in H0. unfold wf_minductive in H0.
    rtoProp. cbn in H0. rewrite hasp in H0; now eapply eqb_eq in H0.
  - intros _. eapply IHwf_glob.
Qed.

Lemma wellformed_lookup_constructor_pars {efl : EEnvFlags} {Σ kn c mdecl idecl cdecl} :
  has_cstr_params = false ->
  wf_glob Σ ->
  lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl) -> mdecl.(ind_npars) = 0.
Proof.
  intros hasp wf. cbn -[lookup_minductive].
  destruct lookup_minductive eqn:hl => //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma lookup_constructor_pars_args_spec {efl : EEnvFlags} {Σ ind n mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  lookup_constructor_pars_args Σ ind n = Some (mdecl.(ind_npars), cdecl.(cstr_nargs)).
Proof.
  cbn -[lookup_constructor] => wfΣ.
  destruct lookup_constructor as [[[mdecl' idecl'] [pars args]]|] eqn:hl => //.
  intros [= -> -> <-]. cbn. f_equal.
Qed.

Lemma wellformed_lookup_constructor_pars_args {efl : EEnvFlags} {Σ ind k n block_args} :
  wf_glob Σ ->
  has_cstr_params = false ->
  wellformed Σ k (EAst.tConstruct ind n block_args) ->
  ∑ args, lookup_constructor_pars_args Σ ind n = Some (0, args).
Proof.
  intros wfΣ hasp wf. cbn -[lookup_constructor] in wf.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  exists cdecl.(cstr_nargs).
  pose proof (wellformed_lookup_constructor_pars hasp wfΣ hl).
  eapply lookup_constructor_pars_args_spec in hl => //. congruence.
  destruct has_tConstruct => //.
Qed.

Lemma constructor_isprop_pars_decl_params {efl : EEnvFlags} {Σ ind c b pars cdecl} :
  has_cstr_params = false -> wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.
Proof.
  intros hasp hwf.
  rewrite /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive.
  destruct lookup_minductive as [mdecl|] eqn:hl => /= //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma skipn_ge m {A} (l : list A) :
  m >= length l -> skipn m l = [].
Proof.
  induction l in m |- *.
  - destruct m; reflexivity.
  - cbn. destruct m; try lia. intros H.
    eapply IHl. lia.
Qed.

Lemma chop_all {A} (l : list A) m :
  m >= length l -> chop m l = (l, nil).
Proof.
  intros Hl. rewrite chop_firstn_skipn.
  rewrite firstn_ge; try lia. rewrite skipn_ge; try lia.
  eauto.
Qed.

Lemma implement_box_isConstructApp {efl : EEnvFlags} {Σ : global_declarations} t :
  isConstructApp (implement_box t) = isConstructApp t.
Proof.
  induction t; try now cbn; eauto.
  simp implement_box.
  rewrite (isConstructApp_mkApps _ [t2]).
  rewrite (isConstructApp_mkApps _ [_]). eauto.
Qed.

Lemma implement_box_isPrimApp {efl : EEnvFlags} {Σ : global_declarations} t :
  isPrimApp (implement_box t) = isPrimApp t.
Proof.
  induction t; try now cbn; eauto.
  simp implement_box.
  rewrite (isPrimApp_mkApps _ [t2]).
  rewrite (isPrimApp_mkApps _ [_]). eauto.
Qed.

Lemma implement_box_isLazyApp {efl : EEnvFlags} {Σ : global_declarations} t :
  isLazyApp (implement_box t) = isLazyApp t.
Proof.
  induction t; try now cbn; eauto.
  simp implement_box.
  rewrite (isLazyApp_mkApps _ [t2]).
  rewrite (isLazyApp_mkApps _ [_]). eauto.
Qed.

Lemma lookup_env_implement_box {Σ : global_declarations} kn :
  lookup_env (implement_box_env Σ) kn =
  option_map (implement_box_decl) (lookup_env Σ kn).
Proof.
  unfold implement_box_env.
  induction Σ at 1 2; simpl; auto.
  case: eqb_spec => //.
Qed.

Lemma implement_box_declared_constant {Σ : global_declarations} c decl :
   declared_constant Σ c decl ->
   declared_constant (implement_box_env Σ) c (implement_box_constant_decl decl).
Proof.
  intros H. red in H; red.
  rewrite lookup_env_implement_box H //.
Qed.

Lemma lookup_constructor_implement_box Σ ind c :
  lookup_constructor (implement_box_env Σ) ind c =
  lookup_constructor Σ ind c.
Proof.
  unfold lookup_constructor, lookup_inductive, lookup_minductive in *.
  rewrite lookup_env_implement_box.
  destruct lookup_env as [ [] | ]; cbn; congruence.
Qed.

Lemma lookup_inductive_implement_box Σ ind :
  lookup_inductive (implement_box_env Σ) ind =
  lookup_inductive Σ ind.
Proof.
  unfold lookup_constructor, lookup_inductive, lookup_minductive in *.
  rewrite lookup_env_implement_box.
  destruct lookup_env as [ [] | ]; cbn; congruence.
Qed.

Lemma lookup_constructor_pars_args_implement_box {efl : EEnvFlags} {Σ ind n} :
  lookup_constructor_pars_args (implement_box_env Σ) ind n = lookup_constructor_pars_args Σ ind n.
Proof.
  cbn -[lookup_constructor]. now rewrite lookup_constructor_implement_box.
Qed.

Lemma isLambda_implement_box c : isLambda c -> isLambda (implement_box c).
Proof. destruct c => //. Qed.

Definition disable_box_term_flags (et : ETermFlags) :=
  {| has_tBox := false
    ; has_tRel := true
    ; has_tVar := has_tVar
    ; has_tEvar := has_tEvar
    ; has_tLambda := true
    ; has_tLetIn := has_tLetIn
    ; has_tApp := has_tApp
    ; has_tConst := has_tConst
    ; has_tConstruct := has_tConstruct
    ; has_tCase := has_tCase
    ; has_tProj := has_tProj
    ; has_tFix := true
    ; has_tCoFix := has_tCoFix
    ; has_tPrim := has_tPrim
    ; has_tLazy_Force := has_tLazy_Force
  |}.

Definition switch_off_box (efl : EEnvFlags) :=
  {|  has_axioms := efl.(has_axioms) ; has_cstr_params := efl.(has_cstr_params) ; term_switches := disable_box_term_flags efl.(term_switches) ; cstr_as_blocks := efl.(cstr_as_blocks) |}.

Lemma transform_wellformed' {efl : EEnvFlags} {Σ : list (kername × global_decl)} n t :
  has_tApp -> has_tLetIn ->
  wf_glob Σ ->
  @wellformed efl Σ n t ->
  @wellformed (switch_off_box efl) (implement_box_env Σ) n (implement_box t).
Proof.
  intros hasa hasl.
  revert n. funelim (implement_box t); simp_eta; cbn -[implement_box
    lookup_inductive lookup_constructor lookup_constructor_pars_args
    GlobalContextMap.lookup_constructor_pars_args isEtaExp]; intros m Hwf Hw; rtoProp; try split; eauto.
  all: rewrite ?map_InP_spec; toAll; eauto; try now solve_all.
  - rewrite lookup_env_implement_box. destruct (lookup_env Σ n) => //. destruct g => //=.
    destruct (cst_body c) => //=.
  - unfold lookup_constructor_pars_args in *.
    rewrite lookup_constructor_implement_box. rewrite H2. intuition auto.
  - rewrite lookup_constructor_pars_args_implement_box. len.
    all: destruct cstr_as_blocks; rtoProp; try split; eauto.
    + solve_all.
    + destruct block_args; cbn in *; eauto.
  - rewrite /wf_brs; cbn -[lookup_inductive implement_box].
    rewrite lookup_inductive_implement_box. intuition auto. solve_all. solve_all.
    replace (#|x.1| + S m) with ((#|x.1| + m) + 1) by lia.
    eapply wellformed_lift. eauto.
  - rewrite lookup_constructor_implement_box. intuition auto.
  - unfold wf_fix in *. rtoProp. solve_all. solve_all. now eapply isLambda_implement_box.
  - unfold wf_fix in *. rtoProp. solve_all. len. solve_all.
  - unfold wf_fix in *. len. solve_all. rtoProp; intuition auto.
    solve_all.
  - solve_all_k 6.
Qed.

Lemma transform_wellformed_decl' {efl : EEnvFlags} {Σ : global_declarations} d :
  has_tApp -> has_tLetIn ->
  wf_glob Σ ->
  @wf_global_decl efl Σ d ->
  @wf_global_decl (switch_off_box efl) (implement_box_env Σ) (implement_box_decl d).
Proof.
  intros.
  destruct d => //=. cbn.
  destruct c as [[]] => //=.
  eapply transform_wellformed'; tea.
Qed.

Lemma fresh_global_map_on_snd {Σ : global_context} f kn :
  fresh_global kn Σ ->
  fresh_global kn (map (on_snd f) Σ).
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma implement_box_env_wf_glob {efl : EEnvFlags} {Σ : global_declarations} :
  has_tApp -> has_tLetIn ->
  wf_glob (efl := efl) Σ -> wf_glob (efl := switch_off_box efl) (implement_box_env Σ).
Proof.
  intros hasapp haslet wfg.
  assert (extends_prefix Σ Σ). now exists [].
  revert H wfg. generalize Σ at 2 3.
  induction Σ; cbn; constructor; auto.
  - eapply IHΣ; rtoProp; intuition eauto.
    destruct H. subst Σ0. exists (x ++ [a]). now rewrite -app_assoc.
  - epose proof (EExtends.extends_wf_glob _ H wfg); tea.
    depelim H0. cbn.
    now eapply transform_wellformed_decl'.
  - eapply fresh_global_map_on_snd.
    eapply EExtends.extends_wf_glob in wfg; tea. now depelim wfg.
Qed.

From MetaRocq.Erasure Require Import EGenericGlobalMap.

Lemma implement_box_env_extends {efl : EEnvFlags} {Σ Σ' : global_declarations} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (implement_box_env Σ) (implement_box_env Σ').
Proof.
  intros hast ext wf wf'.
  intros kn d.
  rewrite !lookup_env_map_snd.
  specialize (ext kn). destruct (lookup_env) eqn:E => //=.
  intros [= <-].
  rewrite (ext g) => //.
Qed.

Transparent implement_box.

Lemma fst_decompose_app_rec t l : fst (decompose_app_rec t l) = fst (decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

Lemma head_tapp t1 t2 : head (tApp t1 t2) = head t1.
Proof. rewrite /head /decompose_app /= fst_decompose_app_rec //. Qed.
Lemma tApp_mkApps f a : tApp f a = mkApps f [a].
Proof. reflexivity. Qed.

From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksInd.

Lemma implement_box_mkApps f args :
  implement_box (mkApps f args) = mkApps (implement_box f) (map implement_box args).
Proof.
  induction args in f |- *; simp implement_box.
  - reflexivity.
  - rewrite IHargs. now simp implement_box.
Qed.

Lemma implement_box_eval {efl : EEnvFlags} (fl := block_wcbv_flags) :
  with_constructor_as_block = true ->
  has_cstr_params = false ->
  has_tApp ->
  has_tCoFix = false ->
  forall (Σ : global_declarations), @wf_glob efl Σ ->
  forall t t',
  @wellformed efl Σ 0 t ->
  EWcbvEval.eval Σ t t' ->
  @EWcbvEval.eval block_wcbv_flags (implement_box_env Σ) (implement_box t) (implement_box t').
Proof.
  intros cstrbl prms hasapp hascofix Σ wfΣ.
  eapply
  (EWcbvEvalCstrsAsBlocksInd.eval_preserve_mkApps_ind fl cstrbl (efl := efl) Σ _
    (wellformed Σ) (Qpres := Qpreserves_wellformed efl _ wfΣ)) => //.
  { intros. eapply EWcbvEval.eval_wellformed => //; tea. }
  all:intros *.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    eapply eval_fix' => //.
    + eauto.
    + cbn. reflexivity.
    + eauto.
    + econstructor. econstructor => //.
      eapply value_final. eapply eval_to_value; eauto.
      unfold iBox. cbn -[implement_box]. unfold map_def. cbn -[implement_box].
      econstructor. cbn. eauto.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    econstructor; eauto.
    now rewrite -implement_box_csubst.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    econstructor; eauto.
    now rewrite -implement_box_csubst.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    assert (pars = 0) as -> by now (eapply constructor_isprop_pars_decl_params; eauto).
    pose proof (Hcon := H1).
    rewrite /constructor_isprop_pars_decl in H1.
    destruct lookup_constructor as [[[]] | ] eqn:eqc; cbn in H1; invs H1.
    eapply eval_zeta => //.
    1: eauto. rewrite H8.
    cbn [csubst Nat.compare].
    eapply eval_iota_block => //.
    + eapply value_final. eapply eval_to_value; eauto.
    + unfold constructor_isprop_pars_decl.
      rewrite lookup_constructor_implement_box. cbn [fst].
      rewrite eqc //= H7 //. rewrite H8.
      reflexivity.
    + rewrite map_map.
      rewrite nth_error_map H2; eauto.
      reflexivity.
    + len.
    + len.
    +
      cbn [csubst].
      cbn [fst snd].
      rewrite closed_subst.
      { eapply wellformed_closed in i2.
        cbn in i2 |- *. solve_all.
        now eapply closed_implement_box.
      }
      rewrite Nat.add_0_r.
      rewrite simpl_subst_k. reflexivity.
      rewrite -implement_box_iota_red.
      2: eauto.
      eapply wellformed_closed in i2.
      cbn in i2.
      solve_all.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    eapply eval_fix' => //; eauto.
    eapply implement_box_cunfold_fix.
    eapply forallb_All. eapply closed_fix_subst.
    eapply wellformed_closed in i4.
    now cbn in i4. eauto.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    rewrite wellformed_mkApps in i2. eauto.
    cbn in i2. rtoProp. congruence.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    rewrite wellformed_mkApps in i2. eauto.
    cbn in i2. rtoProp. congruence.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    econstructor.
    eapply implement_box_declared_constant; eauto.
    destruct decl. cbn in *. now rewrite H0.
    eauto.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    unfold constructor_isprop_pars_decl in *.
    destruct lookup_constructor as [[[mdecl idecl] cdecl']|] eqn:hc => //.
    noconf H2.
    pose proof (lookup_constructor_pars_args_cstr_arity _ _ _ _ _ _ hc).
    assert (ind_npars mdecl = 0).
    { eapply wellformed_lookup_constructor_pars; tea. }
    eapply eval_proj_block => //; tea. cbn.
    + unfold constructor_isprop_pars_decl.
      rewrite lookup_constructor_implement_box. cbn [fst].
      rewrite hc //= H1 H7. reflexivity.
    + len.
    + rewrite nth_error_map /=. rewrite H7 in H2; rewrite -H2 in H4; rewrite H4; eauto.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    eapply eval_app_cong; eauto.
    revert H1.
    destruct f'; try now cbn; tauto.
    intros H. cbn in H.
    rewrite implement_box_isConstructApp; eauto.
    rewrite implement_box_isPrimApp; eauto.
    rewrite implement_box_isLazyApp; eauto.
  - intros; repeat match goal with [H : MRProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_box in *.
    eapply eval_construct_block; tea. eauto.
    2: len; eassumption.
    rewrite lookup_constructor_implement_box; eauto.
    eapply All2_All2_Set.
    solve_all. now destruct b.
  - intros wf H; depelim H; simp implement_box; repeat constructor.
    destruct a0. eapply All2_over_undep in a. eapply All2_All2_Set, All2_map.
    cbn -[implement_box]. solve_all. now destruct H. now destruct a0.
  - intros evt evt' [] [].
    simp implement_box. simp implement_box in e.
    econstructor; eauto.
  - intros. destruct t; try solve [constructor; cbn in H, H0 |- *; try congruence].
    cbn -[lookup_constructor] in H |- *. destruct args => //.
Qed.
