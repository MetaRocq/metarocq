(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config Kernames BasicAst EnvMap.
From MetaCoq.Erasure Require Import EPrimitive EAst EAstUtils EInduction EArities
    ELiftSubst ESpineView EGlobalEnv EWellformed EEnvMap
    EWcbvEval EEtaExpanded ECSubst EWcbvEvalEtaInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Coq Require Import ssreflect ssrbool.

(** We assume [Prop </= Type] and universes are checked correctly in the following. *)
(* Local Existing Instance extraction_checker_flags. *)
Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors eval : core.

Import MCList (map_InP, map_InP_elim, map_InP_spec).

Section implement_lazy_force.
  Context (Σ : global_declarations).

  Section Def.

  Equations? implement_lazy_force (t : term) : term
    by wf t (fun x y : EAst.term => size x < size y) :=
    | tRel i => EAst.tRel i
    | tEvar ev args => EAst.tEvar ev (map_InP args (fun x H => implement_lazy_force x))
    | tLambda na M => EAst.tLambda na (implement_lazy_force M)
    | tApp u v := tApp (implement_lazy_force u) (implement_lazy_force v)
    | tLetIn na b b' => EAst.tLetIn na (implement_lazy_force b) (implement_lazy_force b')
    | tCase ind c brs =>
      let brs' := map_InP brs (fun x H => (x.1, (implement_lazy_force x.2))) in
      (EAst.tCase (ind.1, 0) (implement_lazy_force c) brs')
    | tProj p c => EAst.tProj {| proj_ind := p.(proj_ind); proj_npars := 0; proj_arg := p.(proj_arg) |} (implement_lazy_force c)
    | tFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := implement_lazy_force d.(dbody); rarg := d.(rarg) |}) in
      EAst.tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := implement_lazy_force d.(dbody); rarg := d.(rarg) |}) in
      EAst.tCoFix mfix' idx
    | tBox => tBox
    | tVar n => EAst.tVar n
    | tConst n => EAst.tConst n
    | tConstruct ind i block_args => EAst.tConstruct ind i (map_InP block_args (fun d H => implement_lazy_force d))
    | tPrim p => EAst.tPrim (map_primIn p (fun x H => implement_lazy_force x))
    | tLazy t => EAst.tLambda nAnon (lift 1 0 (implement_lazy_force t))
    | tForce t => EAst.tApp (implement_lazy_force t) tBox.
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
  Hint Rewrite @map_primIn_spec @map_InP_spec : implement_lazy_force.

  Arguments eqb : simpl never.

  Opaque implement_lazy_force.
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

  Lemma closed_implement_lazy_force t k : closedn k t -> closedn k (implement_lazy_force t).
  Proof using Type.
    funelim (implement_lazy_force t); simp implement_lazy_force; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold test_def in *;
    simpl closed in *;
      try solve [simpl; subst; simpl closed; f_equal; auto; rtoProp; solve_all; solve_all]; try easy.
    - solve [simpl; subst; simpl closed; f_equal; auto; rtoProp; solve_all; solve_all_k 6]; try easy.
    - replace (S k) with (k + 1) by lia.
      eapply closedn_lift. eauto.
  Qed.

  Hint Rewrite @forallb_InP_spec : isEtaExp.
  Transparent isEtaExp_unfold_clause_1.

  Lemma implement_lazy_force_lift a k b :
    implement_lazy_force (lift a k b) = lift a k (implement_lazy_force b).
  Proof.
    revert k.
    funelim (implement_lazy_force b); intros k; cbn; simp implement_lazy_force; try easy.
    - destruct (Nat.leb_spec k i); reflexivity.
    - f_equal. rewrite !map_map_compose. solve_all.
      eapply In_All. eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros. eapply H; eauto.
    - cbn. do 1 f_equal. 1: eauto.
      rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal.
      replace (#|x.1| + S k) with (S (#|x.1| + k)) by lia.
      erewrite H; eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. erewrite H; eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. erewrite H; eauto.
    - solve_all_k 6.
    - replace (S k) with (k + 1) by lia. now rewrite <- permute_lift. 
  Qed.

  (* Lemma implement_lazy_force_subst a k b : *)
  (*   implement_lazy_force (subst a k b) = subst (map implement_lazy_force a) k (implement_lazy_force b). *)
  (* Proof using Type. *)
  (*   revert k. *)
  (*   funelim (implement_lazy_force b); intros k; cbn; simp implement_lazy_force; try easy. *)
  (*   all: try now (cbn; f_equal; eauto). *)
  (*   - destruct (Nat.leb_spec k i). *)
  (*     + erewrite nth_error_map. *)
  (*       destruct nth_error; cbn. *)
  (*       * now rewrite implement_lazy_force_lift. *)
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

  Lemma implement_lazy_force_csubst a k b :
    closed a ->
    implement_lazy_force (ECSubst.csubst a k b) = ECSubst.csubst (implement_lazy_force a) k (implement_lazy_force b).
  Proof using Type.
    intros Ha.
    revert k.
    funelim (implement_lazy_force b); intros k; cbn; simp implement_lazy_force; try easy.
    all: try now (cbn; f_equal; eauto).
    - destruct Nat.compare => //.
    - f_equal. rewrite !map_map_compose. solve_all.
      eapply In_All. eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros. eapply H; eauto.
    - cbn. do 1 f_equal. 1: eauto.
      rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal.
      setoid_rewrite -> closed_subst at 2.
      rewrite <- closed_subst.
      2, 3: eapply closed_implement_lazy_force; eauto.
      f_equal.
      eapply H; eauto.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. solve_all.
    - cbn. f_equal. rewrite !map_map. solve_all.
      eapply In_All. intros ? ?. unfold map_def. cbn. f_equal. solve_all.
    - cbn. solve_all.
    - setoid_rewrite closed_subst at 2.
      replace (S k) with (k + 1) by lia.
      rewrite <- commut_lift_subst_rec. 2: lia.
      rewrite <- closed_subst.
      2, 3: eapply closed_implement_lazy_force; eauto.
      f_equal.
      now rewrite H.
  Qed.

  Lemma implement_lazy_force_substl s t :
    All (fun x => closed x) s ->
    implement_lazy_force (substl s t) = substl (map implement_lazy_force s) (implement_lazy_force t).
  Proof using Type.
    induction s in t |- *; simpl; auto; intros Hall.
    inversion Hall.
    rewrite IHs //.
    now rewrite implement_lazy_force_csubst.
  Qed.

  Lemma implement_lazy_force_iota_red pars args br :
    All (fun x => closed x) args ->
    implement_lazy_force (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map implement_lazy_force args) (on_snd implement_lazy_force br).
  Proof using Type.
    intros Hall.
    unfold EGlobalEnv.iota_red.
    rewrite implement_lazy_force_substl //.
    solve_all. now eapply All_skipn.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma implement_lazy_force_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def implement_lazy_force) mfix) = map implement_lazy_force (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp implement_lazy_force.
  Qed.

  Lemma implement_lazy_force_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def implement_lazy_force) mfix) = map implement_lazy_force (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp implement_lazy_force.
  Qed.

  Lemma implement_lazy_force_cunfold_fix mfix idx n f :
    All (λ x : term, closed x) (fix_subst mfix) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def implement_lazy_force) mfix) idx = Some (n, implement_lazy_force f).
  Proof using Type.
    intros Hcl.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal. f_equal.
    rewrite implement_lazy_force_substl //. 2:congruence.
    f_equal. f_equal. apply implement_lazy_force_fix_subst.
  Qed.

  Lemma implement_lazy_force_cunfold_cofix mfix idx n f :
    All (λ x : term, closed x) (cofix_subst mfix) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def implement_lazy_force) mfix) idx = Some (n, implement_lazy_force f).
  Proof using Type.
    intros Hcl.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal.
    rewrite implement_lazy_force_substl //. 2:congruence.
    f_equal. f_equal. apply implement_lazy_force_cofix_subst.
  Qed.

  Lemma implement_lazy_force_nth {n l d} :
    implement_lazy_force (nth n l d) = nth n (map implement_lazy_force l) (implement_lazy_force d).
  Proof using Type.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End implement_lazy_force.

#[universes(polymorphic)]
Global Hint Rewrite @map_primIn_spec @map_InP_spec : implement_lazy_force.

Definition implement_lazy_force_constant_decl cb :=
  {| cst_body := option_map implement_lazy_force cb.(cst_body) |}.

Definition implement_lazy_force_decl d :=
  match d with
  | ConstantDecl cb => ConstantDecl (implement_lazy_force_constant_decl cb)
  | InductiveDecl idecl => InductiveDecl idecl
  end.

Definition implement_lazy_force_env (Σ : global_declarations) :=
  map (on_snd (implement_lazy_force_decl)) Σ.

Definition implement_lazy_force_program (p : eprogram) :=
  (implement_lazy_force_env p.1, implement_lazy_force p.2).

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

Lemma implement_lazy_force_isConstructApp {efl : EEnvFlags} t :
  ~ (exists t', head t = tForce t') ->
  isConstructApp (implement_lazy_force t) -> isConstructApp t.
Proof.
  intros Ht. 
  induction t; try now cbn; eauto.
  + simp implement_lazy_force. rewrite !(isConstructApp_mkApps _ [_]).
    intros. eapply IHt1; eauto. rewrite head_tApp in Ht.
    firstorder.
  + simp implement_lazy_force. rewrite !(isConstructApp_mkApps _ [_]).
    intros. destruct Ht. eexists t. cbn. reflexivity.
Qed.

Lemma implement_lazy_force_isPrimApp {efl : EEnvFlags} t :
  ~ (exists t', head t = tForce t') ->
  isPrimApp (implement_lazy_force t) -> isPrimApp t.
Proof.
  intros Ht. 
  induction t; try now cbn; eauto.
  + simp implement_lazy_force. rewrite !(isPrimApp_mkApps _ [_]).
    intros. eapply IHt1; eauto. rewrite head_tApp in Ht.
    firstorder.
  + simp implement_lazy_force. rewrite !(isPrimApp_mkApps _ [_]).
    intros. destruct Ht. eexists t. cbn. reflexivity.
Qed.

(* Lemma implement_lazy_force_isPrimApp {efl : EEnvFlags} {Σ : global_declarations} t : *)
(*   isPrimAppd (implement_lazy_force t) = isPrimApp t. *)
(* Proof. *)
(*   induction t; try now cbn; eauto. *)
(*   simp implement_lazy_force. *)
(*   rewrite (isPrimApp_mkApps _ [t2]). *)
(*   rewrite (isPrimApp_mkApps _ [_]). eauto. *)
(* Qed. *)

(* Lemma implement_lazy_force_isLazyApp {efl : EEnvFlags} {Σ : global_declarations} t : *)
(*   isLazyApp (implement_lazy_force t) = isLazyApp t. *)
(* Proof. *)
(*   induction t; try now cbn; eauto. *)
(*   simp implement_lazy_force. *)
(*   rewrite (isLazyApp_mkApps _ [t2]). *)
(*   rewrite (isLazyApp_mkApps _ [_]). eauto. *)
(* Qed. *)

Lemma lookup_env_implement_lazy_force {Σ : global_declarations} kn :
  lookup_env (implement_lazy_force_env Σ) kn =
  option_map (implement_lazy_force_decl) (lookup_env Σ kn).
Proof.
  unfold implement_lazy_force_env.
  induction Σ at 1 2; simpl; auto.
  case: eqb_spec => //.
Qed.

Lemma implement_lazy_force_declared_constant {Σ : global_declarations} c decl :
   declared_constant Σ c decl ->
   declared_constant (implement_lazy_force_env Σ) c (implement_lazy_force_constant_decl decl).
Proof.
  intros H. red in H; red.
  rewrite lookup_env_implement_lazy_force H //.
Qed.

Lemma lookup_constructor_implement_lazy_force Σ ind c :
  lookup_constructor (implement_lazy_force_env Σ) ind c =
  lookup_constructor Σ ind c.
Proof.
  unfold lookup_constructor, lookup_inductive, lookup_minductive in *.
  rewrite lookup_env_implement_lazy_force.
  destruct lookup_env as [ [] | ]; cbn; congruence.
Qed.

Lemma lookup_inductive_implement_lazy_force Σ ind :
  lookup_inductive (implement_lazy_force_env Σ) ind =
  lookup_inductive Σ ind.
Proof.
  unfold lookup_constructor, lookup_inductive, lookup_minductive in *.
  rewrite lookup_env_implement_lazy_force.
  destruct lookup_env as [ [] | ]; cbn; congruence.
Qed.

Lemma lookup_constructor_pars_args_implement_lazy_force {efl : EEnvFlags} {Σ ind n} :
  lookup_constructor_pars_args (implement_lazy_force_env Σ) ind n = lookup_constructor_pars_args Σ ind n.
Proof.
  cbn -[lookup_constructor]. now rewrite lookup_constructor_implement_lazy_force.
Qed.

Lemma isLambda_implement_lazy_force c : isLambda c -> isLambda (implement_lazy_force c).
Proof. destruct c => //. Qed.

Definition disable_thunk_term_flags (et : ETermFlags) :=
  {| has_tBox := has_tBox
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
    ; has_tLazy_Force := false
  |}.

Definition switch_off_thunk (efl : EEnvFlags) :=
  {|  has_axioms := efl.(has_axioms) ; has_cstr_params := efl.(has_cstr_params) ; term_switches := disable_thunk_term_flags efl.(term_switches) ; cstr_as_blocks := efl.(cstr_as_blocks) |}.

Lemma transform_wellformed' {efl : EEnvFlags} {Σ : list (kername × global_decl)} n t :
  has_tApp -> has_tBox ->
  wf_glob Σ ->
  @wellformed efl Σ n t ->
  @wellformed (switch_off_thunk efl) (implement_lazy_force_env Σ) n (implement_lazy_force t).
Proof.
  intros hasa hasbox.
  revert n. funelim (implement_lazy_force t); simp_eta; cbn -[implement_lazy_force
    lookup_inductive lookup_constructor lookup_constructor_pars_args
    GlobalContextMap.lookup_constructor_pars_args isEtaExp]; intros m Hwf Hw; rtoProp; try split; eauto.
  all: rewrite ?map_InP_spec; toAll; eauto; try now solve_all.
  - rewrite lookup_env_implement_lazy_force. destruct (lookup_env Σ n) => //. destruct g => //=.
    destruct (cst_body c) => //=.
  - unfold lookup_constructor_pars_args in *.
    rewrite lookup_constructor_implement_lazy_force. rewrite H2. intuition auto.
  - rewrite lookup_constructor_pars_args_implement_lazy_force. len.
    all: destruct cstr_as_blocks; rtoProp; try split; eauto.
    + solve_all.
    + destruct block_args; cbn in *; eauto.
  - rewrite /wf_brs; cbn -[lookup_inductive implement_lazy_force].
    rewrite lookup_inductive_implement_lazy_force. intuition auto. solve_all. solve_all.
  - rewrite lookup_constructor_implement_lazy_force. intuition auto.
  - unfold wf_fix in *. rtoProp. solve_all. solve_all. now eapply isLambda_implement_lazy_force.
  - unfold wf_fix in *. rtoProp. solve_all. len. solve_all.
  - unfold wf_fix in *. len. solve_all. rtoProp; intuition auto.
    solve_all.
  - solve_all_k 6.
  - replace (S m) with (m + 1) by lia.
    eapply wellformed_lift. eauto.
Qed.

Lemma transform_wellformed_decl' {efl : EEnvFlags} {Σ : global_declarations} d :
  has_tApp -> has_tBox ->
  wf_glob Σ ->
  @wf_global_decl efl Σ d ->
  @wf_global_decl (switch_off_thunk efl) (implement_lazy_force_env Σ) (implement_lazy_force_decl d).
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

Lemma implement_lazy_force_env_wf_glob {efl : EEnvFlags} {Σ : global_declarations} :
  has_tApp -> has_tBox ->
  wf_glob (efl := efl) Σ -> wf_glob (efl := switch_off_thunk efl) (implement_lazy_force_env Σ).
Proof.
  intros hasapp hasbox wfg.
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

From MetaCoq.Erasure Require Import EGenericGlobalMap.

Lemma implement_lazy_force_env_extends {efl : EEnvFlags} {Σ Σ' : global_declarations} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (implement_lazy_force_env Σ) (implement_lazy_force_env Σ').
Proof.
  intros hast ext wf wf'.
  intros kn d.
  rewrite !lookup_env_map_snd.
  specialize (ext kn). destruct (lookup_env) eqn:E => //=.
  intros [= <-].
  rewrite (ext g) => //.
Qed.

Transparent implement_lazy_force.

Lemma fst_decompose_app_rec t l : fst (decompose_app_rec t l) = fst (decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

Lemma head_tapp t1 t2 : head (tApp t1 t2) = head t1.
Proof. rewrite /head /decompose_app /= fst_decompose_app_rec //. Qed.
Lemma tApp_mkApps f a : tApp f a = mkApps f [a].
Proof. reflexivity. Qed.

Require Import EWcbvEvalCstrsAsBlocksInd.

Lemma implement_lazy_force_mkApps f args :
  implement_lazy_force (mkApps f args) = mkApps (implement_lazy_force f) (map implement_lazy_force args).
Proof.
  induction args in f |- *; simp implement_lazy_force.
  - reflexivity.
  - rewrite IHargs. now simp implement_lazy_force.
Qed.

Lemma eval_app_cong_tApp (fl := block_wcbv_flags) Σ t v args res :
  eval Σ t v ->
  eval Σ (tApp v args) res ->
  eval Σ (tApp t args) res.
Proof.
  intros. depind H0.
  - econstructor; eauto. eapply eval_trans; eauto.
  - econstructor; eauto. eapply eval_trans; eauto.
  - eapply eval_fix; eauto. eapply eval_trans; eauto.
  - eapply eval_fix_value; eauto. eapply eval_trans; eauto.
  - eapply eval_fix'; eauto. eapply eval_trans; eauto.
  - eapply eval_construct; eauto. eapply eval_trans; eauto.
  - eapply eval_app_cong; eauto. eapply eval_trans; eauto.
  - cbn in i. easy.
Qed.

Lemma eval_app_cong_tApp' (fl := block_wcbv_flags) Σ t arg arg' res :
  value Σ t ->
  eval Σ arg arg' ->
  eval Σ (tApp t arg') res ->
  eval Σ (tApp t arg) res.
Proof.
  intros X H H0. depind H0.
  - eapply eval_app_cong_tApp; tea. econstructor. constructor. constructor. exact H.
  - pose proof (eval_trans' H H0_0). subst a'. econstructor; tea.
  - pose proof (eval_trans' H H0_0). subst av. eapply eval_fix; tea.
  - pose proof (eval_trans' H H0_0). subst av. eapply eval_fix_value; tea.
  - eapply value_final in X. pose proof (eval_trans' X H0_). subst f7.
    pose proof (eval_trans' H H0_0). subst av.
    eapply eval_fix'; tea.
  - eapply eval_construct; tea.
    eapply eval_trans; tea.
  - eapply eval_app_cong; tea.
    eapply eval_trans; tea.
  - now cbn in i.
Qed.

Lemma implement_lazy_force_eval {efl : EEnvFlags} (fl := block_wcbv_flags) :
  with_constructor_as_block = true ->
  has_cstr_params = false ->
  has_tApp ->
  has_tBox ->
  has_tCoFix = false ->
  forall (Σ : global_declarations), @wf_glob efl Σ ->
  forall t t',
  @wellformed efl Σ 0 t ->
  EWcbvEval.eval Σ t t' ->
  @EWcbvEval.eval block_wcbv_flags (implement_lazy_force_env Σ) (implement_lazy_force t) (implement_lazy_force t').
Proof.
  intros cstrbl prms hasapp hasbox hascofix Σ wfΣ.
  eapply
  (EWcbvEvalCstrsAsBlocksInd.eval_preserve_mkApps_ind fl cstrbl (efl := efl) Σ _
    (wellformed Σ) (Qpres := Qpreserves_wellformed efl _ wfΣ)) => //.
  { intros. eapply EWcbvEval.eval_wellformed => //; tea. }
  all:intros *.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    econstructor; eauto.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    econstructor; eauto.
    now rewrite -implement_lazy_force_csubst.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    econstructor; eauto.
    now rewrite -implement_lazy_force_csubst.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    assert (pars = 0) as -> by now (eapply constructor_isprop_pars_decl_params; eauto).
    pose proof (Hcon := H1).
    rewrite /constructor_isprop_pars_decl in H1.
    destruct lookup_constructor as [[[]] | ] eqn:eqc; cbn in H1; invs H1.
    eapply eval_iota_block => //.
    + eauto. 
    + unfold constructor_isprop_pars_decl.
      rewrite lookup_constructor_implement_lazy_force. cbn [fst].
      rewrite eqc //= H7 //. 
    + rewrite nth_error_map H2; eauto.
      reflexivity.
    + len.
    + rewrite H8. len.
    + rewrite -implement_lazy_force_iota_red.
      eapply wellformed_closed in i2.
      cbn in i2.
      solve_all.
      rewrite H8. eauto.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    eapply eval_fix' => //; eauto.
    eapply implement_lazy_force_cunfold_fix.
    eapply forallb_All. eapply closed_fix_subst.
    eapply wellformed_closed in i4.
    now cbn in i4. eauto.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    rewrite wellformed_mkApps in i2. eauto.
    cbn in i2. rtoProp. congruence.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    rewrite wellformed_mkApps in i2. eauto.
    cbn in i2. rtoProp. congruence.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    econstructor.
    eapply implement_lazy_force_declared_constant; eauto.
    destruct decl. cbn in *. now rewrite H0.
    eauto.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    unfold constructor_isprop_pars_decl in *.
    destruct lookup_constructor as [[[mdecl idecl] cdecl']|] eqn:hc => //.
    noconf H2.
    pose proof (lookup_constructor_pars_args_cstr_arity _ _ _ _ _ _ hc).
    assert (ind_npars mdecl = 0).
    { eapply wellformed_lookup_constructor_pars; tea. }
    eapply eval_proj_block => //; tea. cbn.
    + unfold constructor_isprop_pars_decl.
      rewrite lookup_constructor_implement_lazy_force. cbn [fst].
      rewrite hc //= H1 H7. reflexivity.
    + len.
    + rewrite nth_error_map /=. rewrite H7 in H2; rewrite -H2 in H4; rewrite H4; eauto.
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    eapply eval_app_cong; eauto.
    revert H1.
    destruct f'; try now cbn; tauto.
    { intros H. cbn in H. simp implement_lazy_force.
      cbn -[implement_lazy_force].
      rewrite !(isConstructApp_mkApps _ [_]) in H |- *.
      rewrite !negb_orb in H |- *.
      rtoProp.
      assert (¬ ∃ t' : term, head f'1 = tForce t').
      { eapply eval_to_value in ev as ev'.
        invs ev'.
        + inv X. cbn in H4. congruence.
        + eapply (f_equal head) in H4.
          rewrite head_mkApps in H4.
          rewrite (head_mkApps _ [_] )in H4.
          rewrite <- H4.
          inv H5.
          * cbn. congruence. 
          * cbn. intros []. congruence.
          * cbn in *. tauto. }
      repeat split.
      + eapply PCUICNormal.negb_is_true.
        intros HH. eapply implement_lazy_force_isConstructApp in HH.
        apply negbTE in H. congruence.
        eauto.
      + rewrite !(isPrimApp_mkApps _ [_]) in H3 |- *.
        eapply PCUICNormal.negb_is_true.
        intros HH. eapply implement_lazy_force_isPrimApp in HH.
        apply negbTE in H3. congruence.
        eauto.
      + rewrite (isLazyApp_mkApps _ [_]).
        clear. induction f'1; simp implement_lazy_force; cbn -[implement_lazy_force]; auto.
        rewrite (isLazyApp_mkApps _ [_]). eauto.
        rewrite (isLazyApp_mkApps _ [_]). eauto.
    }
    { exfalso.
      eapply eval_to_value in ev as ev'. cbn in ev'.
      depelim ev'. inv a0. cbn in H. congruence.
      destruct args using rev_ind. cbn in H. congruence.
      rewrite mkApps_app in H. inv H.
    }
  - intros; repeat match goal with [H : MCProd.and3 _ _ _ |- _] => destruct H end.
    simp implement_lazy_force in *.
    eapply eval_construct_block; tea. eauto.
    2: len; eassumption.
    rewrite lookup_constructor_implement_lazy_force; eauto.
    eapply All2_All2_Set.
    solve_all. now destruct b.
  - intros wf H; depelim H; simp implement_lazy_force; repeat constructor.
    destruct a0. eapply All2_over_undep in a. eapply All2_All2_Set, All2_map.
    cbn -[implement_lazy_force]. solve_all. now destruct H. now destruct a0.
  - intros evt evt' [] [].
    simp implement_lazy_force. simp implement_lazy_force in e.
    econstructor; eauto.
    setoid_rewrite closed_subst. 2: cbn; auto.
    rewrite simpl_subst_k. reflexivity. auto.
  - intros. destruct t; try solve [constructor; cbn in H, H0 |- *; try congruence].
    cbn -[lookup_constructor] in H |- *. destruct args => //.
Qed.
