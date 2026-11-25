(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames Primitive BasicAst EnvMap.
From MetaRocq.SafeChecker Require Import PCUICSafeReduce (inspect).

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
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

Section unbox.

Section Def.
  Context (Σ : GlobalContextMap.t).
  Definition unboxable (idecl : one_inductive_body) (cdecl : constructor_body) :=
    (#|idecl.(ind_ctors)| == 1) && (cdecl.(cstr_nargs) == 1).

  Equations is_unboxable (kn : inductive) (c : nat) : bool :=
    | kn | 0 with GlobalContextMap.lookup_constructor Σ kn 0 := {
      | Some (mdecl, idecl, cdecl) := unboxable idecl cdecl
      | None := false }
    | kn | S _ := false.
    

  Notation " t 'eqn:' h " := (exist t h) (only parsing, at level 12).

  Opaque is_unboxable.

  Equations get_unboxable_case_branch (ind : inductive) (brs : list (list name * term)) : option (name * term) :=
  get_unboxable_case_branch ind [([brna], bbody)] := Some (brna, bbody);
  get_unboxable_case_branch ind _ := None.

  Equations unbox (t : term) : term :=
  | tRel i => EAst.tRel i
  | tEvar ev args => EAst.tEvar ev (map unbox args)
  | tLambda na M => EAst.tLambda na (unbox M)
  | tApp u v => EAst.tApp (unbox u) (unbox v)
  | tLetIn na b b' => EAst.tLetIn na (unbox b) (unbox b')
  | tCase ind c brs with inspect (is_unboxable ind.1 0) =>
    { | true eqn:unb with inspect (get_unboxable_case_branch ind.1 (map (on_snd unbox) brs)) := {
        | Some (brna, bbody) eqn:heqbr => EAst.tLetIn brna (unbox c) bbody
        | None eqn:heqbr := EAst.tCase ind (unbox c) (map (on_snd unbox) brs) }
      | false eqn:unb := EAst.tCase ind (unbox c) (map (on_snd unbox) brs) }
  | tProj p c with inspect (is_unboxable p.(proj_ind) 0) := {
      | true eqn:unb => unbox c
      | false eqn:unb => EAst.tProj p (unbox c) }
  | tConstruct ind n args with inspect (is_unboxable ind n) => {
      unbox (tConstruct ind n [a]) (true eqn:unb) => unbox a ;
      unbox (tConstruct ind n args) isunb => tConstruct ind n (map unbox args) }
  | tFix mfix idx =>
    let mfix' := map (map_def unbox) mfix in
    EAst.tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := map (map_def unbox) mfix in
    EAst.tCoFix mfix' idx
  | tBox => EAst.tBox
  | tVar n => EAst.tVar n
  | tConst n => EAst.tConst n
  | tPrim p => EAst.tPrim (map_prim unbox p)
  | tLazy t => EAst.tLazy (unbox t)
  | tForce t => EAst.tForce (unbox t).

End Def.

Definition unbox_constant_decl Σ cb :=
  {| cst_body := option_map (unbox Σ) cb.(cst_body) |}.

Definition unbox_inductive_decl idecl :=
  {| ind_finite := idecl.(ind_finite); ind_npars := idecl.(ind_npars); ind_bodies := idecl.(ind_bodies) |}.
  (* 
  ind_npars was initially set to 0,
  At this point it is forced to be the case as far as I understand, changed it to simplify proof but should be equivalent *)

Definition unbox_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (unbox_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl (unbox_inductive_decl idecl)
  end.

Definition unbox_env Σ :=
  map (on_snd (unbox_decl Σ)) Σ.(GlobalContextMap.global_decls).

Definition unbox_program (p : eprogram_env) : eprogram :=
  (unbox_env p.1, unbox p.1 p.2).

Create HintDb unboxing_rw_hints.
Ltac simple := repeat (
    assumption ||
    match goal with
    | |- All _ _ => apply Forall_All 
    | H : All _ _ |- _ => apply All_Forall in H
    | h : ?e = Some _ |-
        context[option_map _ ?e] =>
          rewrite h
    end ||
    autorewrite with unboxing_rw_hints in * || 
    simpl in *
  ).

Hint Rewrite @Forall_All : unboxing_rw_hints.
Hint Rewrite <-@forallb_Forall : unboxing_rw_hints.
Hint Rewrite <-@forallb_Forall : unboxing_rw_hints.
Hint Rewrite Forall_forall : unboxing_rw_hints.
Hint Rewrite @forallb_map : unboxing_rw_hints.
Hint Rewrite andb_and : unboxing_rw_hints.
Hint Rewrite length_map : unboxing_rw_hints.
Hint Rewrite length_map : unboxing_rw_hints.
Hint Rewrite <- @map_skipn : unboxing_rw_hints.
Hint Rewrite @nth_error_map : unboxing_rw_hints.
Hint Rewrite @map_repeat : unboxing_rw_hints.
Hint Rewrite andb_and : unboxing_rw_hints.
Hint Rewrite repeat_length : unboxing_rw_hints.
Hint Rewrite if_same : unboxing_rw_hints.
Hint Rewrite map_map_compose : unboxing_rw_hints.
Hint Rewrite GlobalContextMap.lookup_constructor_spec : unboxing_rw_hints.
Hint Rewrite @skipn_nil : unboxing_rw_hints.
Hint Rewrite negb_orb : unboxing_rw_hints.
Hint Rewrite <- map_rev : unboxing_rw_hints.
Hint Rewrite @nth_error_nil : unboxing_rw_hints.

Lemma lookup_env_map_snd Σ f kn : lookup_env (map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.
Hint Rewrite lookup_env_map_snd : unboxing_rw_hints.

Lemma lookup_env_unbox Σ name :
  lookup_env (unbox_env Σ) name =
    option_map (unbox_decl Σ) (lookup_env Σ name).
Proof.
  unfold unbox_env.
  apply lookup_env_map_snd.
Qed.
Hint Rewrite lookup_env_unbox : unboxing_rw_hints.

Lemma lookup_constant_unbox Σ name :
  lookup_constant (unbox_env Σ) name =
    option_map (unbox_constant_decl Σ) (lookup_constant Σ name).
Proof.
  unfold lookup_constant. simple.
  now destruct (lookup_env Σ name) as [[]|].
Qed.
Hint Rewrite lookup_constant_unbox : unboxing_rw_hints.

Lemma lookup_minductive_unbox Σ name :
  lookup_minductive (unbox_env Σ) name =
    option_map (unbox_inductive_decl) (lookup_minductive Σ name).
Proof.
  unfold lookup_minductive. simple.
  now destruct (lookup_env Σ name) as [[]|].
Qed.
Hint Rewrite lookup_minductive_unbox : unboxing_rw_hints.

Definition on_fst {A B C : Type} (f : A -> B) (p : A * C) : B * C :=
  (f p.1, p.2).

Lemma lookup_inductive_unbox Σ name :
  lookup_inductive (unbox_env Σ) name =
    option_map (on_fst (unbox_inductive_decl)) (lookup_inductive Σ name).
Proof.
  unfold lookup_inductive. simple.
  destruct (lookup_minductive Σ (inductive_mind name)); last easy.
  simple.
  now destruct (nth_error (ind_bodies m) (inductive_ind name)).
Qed.
Hint Rewrite lookup_inductive_unbox : unboxing_rw_hints.

Lemma lookup_constructor_unbox Σ name k :
  lookup_constructor (unbox_env Σ) name k =
    option_map (on_fst (on_fst unbox_inductive_decl)) (lookup_constructor Σ name k).
Proof.
  unfold lookup_constructor.
  simple.
  destruct (lookup_inductive Σ name) as [[[? ?] ?]|]; simple; last easy.
  now destruct (nth_error (ind_ctors _) k).
Qed.
Hint Rewrite lookup_constructor_unbox : unboxing_rw_hints.

Lemma lookup_constructor_pars_args_unbox Σ name k :
  lookup_constructor_pars_args (unbox_env Σ) name k = lookup_constructor_pars_args Σ name k.
Proof.
  unfold lookup_constructor_pars_args.
  simple.
  now destruct (lookup_constructor Σ name k) as [[[? ?] ?]|].
Qed.
Hint Rewrite lookup_constructor_pars_args_unbox : unboxing_rw_hints.

Lemma lookup_projection_unbox Σ name:
  lookup_projection (unbox_env Σ) name =
    option_map (on_fst (on_fst (on_fst unbox_inductive_decl))) (lookup_projection Σ name).
Proof.
  unfold lookup_projection.
  simple.
  destruct (lookup_constructor Σ (proj_ind name)) as [[[? ?] ?]|]; simple; last easy.
  now destruct (nth_error (ind_projs _) (proj_arg name)).
Qed.
Hint Rewrite lookup_projection_unbox : unboxing_rw_hints.

Lemma isSome_map {A B : Type} (f : A -> B) o :
  isSome (option_map f o) =
  isSome o.
Proof.
  now destruct o.
Qed.
Hint Rewrite @isSome_map : unboxing_rw_hints.

Lemma isSome_map' {A B : Type} (f : A -> B) o :
  EWellformed.isSome (option_map f o) =
  EWellformed.isSome o.
Proof.
  now destruct o.
Qed.
Hint Rewrite @isSome_map' : unboxing_rw_hints.

Ltac invert_primProp :=
  lazymatch goal with
  | X : primProp _ _ |- _ =>
      inversion X as [| | | ? [? ?]]; clear X
  end.

Lemma wf_unbox_env_map_ctx 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (t : term) (k : nat) (Σ : GlobalContextMap.t) ctx :
  wellformed ctx k t -> 
  wellformed (map (on_snd (unbox_decl Σ)) ctx) k t.
Proof.
  induction t using term_forall_list_ind in k |- *; simple;
  try invert_primProp;
  unfold 
    wf_brs, wf_fix, 
    test_def, 
    map_prim, test_prim, test_array_model 
    in *; 
    repeat split; intros; simple; try easy.
  - unfold lookup_constant in *. simple.
    now destruct (lookup_env ctx s) as [[?|?]|]; simple.
  - unfold lookup_constructor, lookup_inductive, lookup_minductive
      in *. simple.
    destruct (lookup_env ctx (inductive_mind i)) as [[?|?]|]; simple;
    try easy.
    now destruct (nth_error (ind_bodies m) (inductive_ind i)); simple.
  - destruct cstr_as_blocks; try easy.
    simple.
    split; last easy.
    unfold lookup_constructor_pars_args, lookup_constructor, lookup_inductive, lookup_minductive in *.
    simple.
    destruct (lookup_env ctx (inductive_mind i)) as [[?|?]|]; simple; try easy.
    destruct (nth_error (ind_bodies m) (inductive_ind i)); simple; last easy.
    destruct (nth_error (ind_ctors o) n); simple; easy.
  - unfold lookup_inductive, lookup_minductive in *; simple.
    destruct (lookup_env ctx (inductive_mind p.1)) as [[? | ?]|]; simple; try easy.
    now destruct (nth_error (ind_bodies m) (inductive_ind p.1) ).
  - unfold lookup_projection, lookup_constructor, lookup_inductive, lookup_minductive in *; simple.
    destruct (lookup_env ctx (inductive_mind (proj_ind s))) as [[? | ?]|]; simple; try easy.
    destruct (nth_error (ind_bodies m) (inductive_ind (proj_ind s))); simple; try easy.
    now destruct (ind_ctors o); simple.
Qed.

Lemma get_unboxable_case_branch_spec {ind : inductive} {brs : list (list name * term)} {brna bbody} :
  get_unboxable_case_branch ind brs = Some (brna, bbody) <->
  brs = [([brna], bbody)].
Proof.
  now funelim (get_unboxable_case_branch ind brs).
Qed.
Hint Rewrite @get_unboxable_case_branch_spec : unboxing_rw_hints.

Lemma get_unboxable_case_branch_map_on_snd {ind : inductive} {brs : list (list name * term)} f :
  get_unboxable_case_branch ind (map (on_snd f) brs) = option_map (on_snd f) (get_unboxable_case_branch ind brs).
Proof.
  destruct brs as [| [ [|brna [|?]] bbody] [|?]]; easy.
Qed.
Hint Rewrite @get_unboxable_case_branch_map_on_snd : unboxing_rw_hints.

Lemma unbox_isLambda Σ f :
  isLambda f -> isLambda (unbox Σ f).
Proof.
  now induction f.
Qed.

Lemma fresh_global_map_on_snd ctx f kn :
  fresh_global kn (map (on_snd f) ctx) <->
  fresh_global kn ctx.
Proof.
  unfold fresh_global. cbn. unfold unbox_env.
  induction ctx as [| [name decl] ctx [IH1 IH2]]; simple; first easy; split; now intros h [? ?] [[= ? ?] | hin]; subst; eauto.
Qed.
Hint Rewrite @fresh_global_map_on_snd : unboxing_rw_hints.

Lemma wf_unbox_expr
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (t : term) (k : nat) (Σ : GlobalContextMap.t) ctx :
  has_tLetIn ->
  wellformed ctx k t -> 
  wellformed ctx k (unbox Σ t).
Proof.
  induction t using term_forall_list_ind in k |- *; simple;
  try invert_primProp;
  unfold 
    wf_brs, wf_fix, 
    test_def, 
    map_prim, test_prim, test_array_model 
    in *; 
  repeat split; intros; simple; try easy.
  - destruct cstr_as_blocks eqn:has_cstr_blocks; last first.
    + destruct (is_unboxable Σ i n); last first.
      { simple. rewrite has_cstr_blocks. now destruct args. }
      destruct args; last easy.
      simple. now rewrite has_cstr_blocks.
    + destruct (is_unboxable Σ i n); simple; last first.
      { rewrite has_cstr_blocks. now simple. }
      destruct args as [|arg1[|arg2 args]]; simple; rewrite ?has_cstr_blocks; simple; try easy.
      * now apply X.
      * repeat split; try easy.
        { now apply X. }  
        { apply X; try easy. now apply H0. }
        { intros. apply X; try easy. now apply H0. }
  - unfold is_unboxable_clause_1, lookup_constructor.
    destruct (lookup_inductive Σ p.1) as [[mind_body ind_body]|] eqn:heq;
      simple; last easy.
    destruct (ind_ctors ind_body) as [|cstr cstrs] eqn:heq'; simple.
    { repeat split; try easy.  }
    destruct (unboxable ind_body cstr) eqn:heq''; simple; last easy.
    destruct (
      get_unboxable_case_branch p.1 l
    ) as [[? ?]|] eqn:heq'''; 
      simple; last easy.
    
    repeat split; try easy.
    subst.
    assert (In ([n], t0) [([n], t0)]) by now left.
    eapply (X ([_], _)); try easy.
    now change (S k) with (#|([n], t0).1| + k).
  - unfold is_unboxable_clause_1, lookup_constructor.
    destruct (lookup_inductive Σ (proj_ind s)) as [[mind_body ind_body]|] eqn:heq;
      simple; last easy.
    destruct (ind_ctors ind_body) as [|cstr cstrs] eqn:heq'; simple.
    { repeat split; try easy. }
    destruct (unboxable ind_body cstr) eqn:heq''; now simple.
  - now apply unbox_isLambda.
Qed.

Lemma wf_glob_map_unbox 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (Σ : GlobalContextMap.t) ctx :
  has_tLetIn ->
  wf_glob ctx ->
  wf_glob (map (on_snd (unbox_decl Σ)) ctx).
Proof.
  induction ctx as [| [name decl] ctx]; first easy.
  intros ? h; inversion h as [|? ? ? wf_ctx wf_decl fresh_name]; subst; clear h; simple.
  constructor; simple; try easy.
  unfold wf_global_decl.
  destruct decl as [[[?|]]|?]; simple.
  now apply wf_unbox_env_map_ctx, wf_unbox_expr.
Qed.

Theorem wf_unboxing
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (input : eprogram_env) :
  has_tLetIn ->
  wf_eprogram_env efl input ->
  wf_eprogram efl (unbox_program input).
Proof.
  destruct input as [ctx t].
  intros ? [wf_ctx wf_t]; simple.
  pose proof wf_glob_map_unbox.
  pose proof wf_unbox_env_map_ctx.
  pose proof wf_unbox_expr.
  unfold wf_eprogram; simple.
  easy.
Qed.

Lemma unbox_csubst Σ e1 e2 k :
  unbox Σ (ECSubst.csubst e1 k e2) =
  ECSubst.csubst (unbox Σ e1) k (unbox Σ e2).
Proof.
  induction e2 
    using term_forall_list_ind
    in k  |- *;
      simple; try solve[
        now f_equal |
        simple; f_equal;
        unfold map_def;
        apply All_map_eq;
        simple; intros; f_equal;
        easy
      ].
  - simple. destruct (k ?= n); reflexivity.
  - destruct (is_unboxable Σ i n) eqn:heq; simple; last first.
    { f_equal.
      apply All_map_eq.
      now simple. }
    destruct args as [|? [|? ?]]; simple; try easy.
    do 3 f_equal; eauto.
    apply All_map_eq.
    simple. eauto.
  - unfold is_unboxable_clause_1.
    destruct (lookup_constructor Σ p.1 0) 
    as [[[mind_body ind_body] constr_body]|]
    eqn:heq; simple; last first.
    { f_equal; first easy.
      apply All_map_eq.
      unfold on_snd. simple. 
      intros; f_equal. easy. } 
    destruct (unboxable ind_body constr_body) eqn:heq';
    simple; last first.
    { f_equal; first easy.
      apply All_map_eq.
      unfold on_snd. simple. 
      intros; f_equal. easy. }
    destruct l as [| [ [|brna [|?]] bbody] [|?]]; simple; unfold on_snd; simple; try easy.
    + f_equal; try easy. do 2 f_equal.
      now apply (X ([], bbody)).
    + f_equal; try easy. do 2 f_equal; try easy.
      * now apply (X ([], bbody)).
      * f_equal; now apply (X p0).
      * apply All_map_eq; simple.
        intros; f_equal.
        now apply X.
    + f_equal; try easy.
      now apply (X (([brna], bbody))).
    + do 3 f_equal; try easy.
      * now apply (X ([brna], bbody)).
      * f_equal; now apply (X p0).
      * apply All_map_eq; simple.
        intros; f_equal.
        now apply X.
    + do 3 f_equal; try easy.
      now eapply (X (_, bbody)).
    + do 3 f_equal; try easy.
      * now eapply (X (_, bbody)).
      * f_equal; now eapply X.
      * apply All_map_eq; simple.
        intros; f_equal; now apply X.
  - unfold is_unboxable_clause_1.
    destruct (lookup_constructor Σ (proj_ind s) 0) 
    as [[[mind_body ind_body] constr_body]|]
    eqn:heq; simple; last easy.
    destruct (unboxable ind_body constr_body) eqn:heq';
    simple; easy.
  - inversion X as [| | | ? [? ?]]; 
    unfold map_prim, map_array_model; 
    simple; try easy.
    do 4 f_equal; first easy.
    apply All_map_eq.
    now simple.
Qed.
Hint Rewrite unbox_csubst : unboxing_rw_hints.

Lemma unbox_substl Σ l e :
  unbox Σ (ECSubst.substl l e) =
  substl (map (unbox Σ) l) (unbox Σ e).
Proof.
  unfold ECSubst.substl.
  intros.
  induction l as [| ? ? IH] 
    using list_ind_rev; simpl; first reflexivity.
  rewrite map_app !fold_left_app -IH.
  now simple.
Qed.
Hint Rewrite <- unbox_substl : unboxing_rw_hints.

Lemma unbox_map_fix_subst Σ mfix  :
  map (unbox Σ) (fix_subst mfix) = fix_subst (map (map_def ((unbox Σ))) mfix).
Proof.
  unfold fix_subst.
  induction mfix as [|? ? IH] at 2 4; first reflexivity.
  now simple.
Qed.
Hint Rewrite unbox_map_fix_subst : unboxing_rw_hints.

Lemma unbox_cunfold_fix mfix idx ctx :
  cunfold_fix (map (map_def (unbox ctx)) mfix) idx =
  option_map (on_snd (unbox ctx)) (cunfold_fix mfix idx).
Proof.
  intros.
  unfold cunfold_fix.
  simple.
  destruct (nth_error mfix idx); unfold on_snd; simpl; last reflexivity.
  now rewrite unbox_substl unbox_map_fix_subst.
Qed.
Hint Rewrite unbox_cunfold_fix : unboxing_rw_hints.

Lemma unbox_map_cofix_subst Σ mfix  :
  map (unbox Σ) (cofix_subst mfix) = cofix_subst (map (map_def ((unbox Σ))) mfix).
Proof.
  unfold cofix_subst.
  induction mfix as [|? ? IH] at 2 4; first reflexivity.
  now simple.
Qed.
Hint Rewrite unbox_map_cofix_subst : unboxing_rw_hints.

Lemma unbox_cunfold_cofix mfix idx ctx :
  cunfold_cofix (map (map_def (unbox ctx)) mfix) idx =
  option_map (on_snd (unbox ctx)) (cunfold_cofix mfix idx).
Proof.
  intros.
  unfold cunfold_cofix.
  simple.
  destruct (nth_error mfix idx); unfold on_snd; simpl; last reflexivity.
  now rewrite unbox_substl unbox_map_cofix_subst.
Qed.
Hint Rewrite unbox_cunfold_cofix : unboxing_rw_hints.

Lemma unbox_mkApps Σ e l :
  unbox Σ (mkApps e l) =
  mkApps (unbox Σ e) (map (unbox Σ) l).
Proof.
  now induction l in e |- *.
Qed.
Hint Rewrite unbox_mkApps : unboxing_rw_hints.

Lemma tCase_not_val (efl : EEnvFlags) (wfl : WcbvFlags)
  ctx indn t brs :
  value ctx (tCase indn t brs) -> False.
Proof.
  repeat (
    easy ||
    rewrite ->mkApps_app in * ||
    match goal with 
    | |- _ -> _ => intros ?
    | h : value _ _ |- _ => inversion h; clear h; subst
    | h : atomic _ _ |- _ => inversion h; clear h; subst
    | h : value_head _ _ _ |- _ => inversion h; clear h; subst
    | h : ?args ≠ [] |- _ =>
        induction args as [|? ? _] using rev_ind; 
        first easy; clear h
    end
  ).
Qed.

Lemma tProj_not_val (efl : EEnvFlags) (wfl : WcbvFlags)
  ctx p t :
  value ctx (tProj p t) -> False.
Proof.
  repeat (
    easy ||
    rewrite ->mkApps_app in * ||
    match goal with 
    | |- _ -> _ => intros ?
    | h : value _ _ |- _ => inversion h; clear h; subst
    | h : atomic _ _ |- _ => inversion h; clear h; subst
    | h : value_head _ _ _ |- _ => inversion h; clear h; subst
    | h : ?args ≠ [] |- _ =>
        induction args as [|? ? _] using rev_ind; 
        first easy; clear h
    end
  ).
Qed.

#[local] Ltac destruct_IHs :=
    repeat match goal with 
    | IH : _ ->
      eval (unbox_env _) _ _
        |- _ =>
        unshelve epose proof IH _; first try easy;
        clear IH
    end
    ; [
      try solve[
        repeat (
          easy || simple || 
          lazymatch goal with
          | h : is_true (wellformed _ _ (mkApps _ _)) |- _ =>
              rewrite wellformed_mkApps /= in h
          | |- is_true (wellformed _ _ (mkApps _ _)) =>
              rewrite wellformed_mkApps /=
          | h : _ /\ _ |- _ => destruct h
          | h : cunfold_fix _ _ = Some (_, ?e) |-
              is_true (wellformed _ _ ?e) => 
              eapply wellformed_cunfold_fix; simpl
          | h : cunfold_cofix _ _ = Some (_, ?e) |-
              is_true (wellformed _ _ ?e) => 
              eapply wellformed_cunfold_cofix; simpl
          | h : nth_error _ _ = Some ?a |-
                is_true (wellformed _ _ ?a) => eapply nth_error_forallb
          | |- is_true (wellformed _ _ (iota_red _ _ _)) => 
              eapply wellformed_iota_red_brs
          | |- is_true (wellformed _ _ (ECSubst.csubst _ _ _)) => 
              eapply wellformed_csubst
          | |- is_true (wellformed _ _ (ECSubst.substl _ _)) => 
              eapply wellformed_substl
          | |- _ /\ _ => split
          | h : context[if ?c then _ else _] |- _ => 
              destruct c eqn:?
          | h : is_true (is_nil ?l) |- _ => 
              destruct l; last (simpl in h; easy); clear h
          end ||
          match goal with
          | h : eval _ _ _ |- _ => 
              apply eval_wellformed in h; [|easy..]; simpl in h
          end 
        )
      ]..
    |].

#[local]
Ltac crush lem := solve[
    simple; eapply lem; repeat (easy || simple)
  ].

Lemma lookup_wf_minductive 
  (efl : EEnvFlags) ctx name m :
  wf_glob ctx ->
  lookup_minductive ctx name = Some m ->
  wf_minductive m.
Proof.
  unfold lookup_minductive; simple.
  intros hwf hlookup.
  induction hwf as [|name' decl ctx IH wf_ctx wf_decl fresh_name']; simple; first easy.
  destruct (eqb_spec name name') as [? | hneq]; subst; last easy.
  destruct decl; first easy.
  injection hlookup as ?; subst; simple.
Qed.

Lemma wf_inductive_no_cstr_params (efl : EEnvFlags) m :
  ~~has_cstr_params ->
  wf_minductive m ->
  m.(ind_npars) = 0.
Proof.
  unfold wf_minductive; simple.
  intros no_cstr_params [h _].
  destruct (eqb_spec (ind_npars m) 0); simple.
  rewrite /is_true orb_false_r -no_cstr_params in h.
  now destruct has_cstr_params.
Qed.

Lemma value_value_head {efl : EEnvFlags} {wfl : WcbvFlags} ctx t :
  value ctx t -> value ctx (head t).
Proof.
  unfold head, decompose_app.
  generalize (@nil term).
  induction t; simple; try easy.
  inversion 1; subst; first now inversion X0.
  inversion H0; subst.
  - apply mkApps_eq in H as (? & ? & ?); last easy; subst.
    rewrite decompose_app_rec_mkApps; simple.
    do 2 constructor.
    simple; split.
    + now rewrite H2.
    + now rewrite H3.
  - apply mkApps_eq in H as (? & ? & ?); last easy; subst.
    rewrite decompose_app_rec_mkApps; simple.
    do 3 constructor.
  - apply mkApps_eq in H as (? & ? & ?); last easy; subst.
    rewrite decompose_app_rec_mkApps; simple.
    do 3 constructor.
Qed.

Lemma value_tApp_first_value {efl : EEnvFlags} {wfl : WcbvFlags} ctx t1 t2 :
  value ctx (tApp t1 t2) ->
  value ctx t1.
Proof.
  intros h.
  set P := fun t =>
    match t with
    | tApp t1 t2 => value ctx t1
    | _ => forall A, A -> A
    end.
  change (P (tApp t1 t2)).
  move: h.
  eapply value_values_ind; simple; try easy.
  - intros t h.
    now destruct t.
  - intros f args value_head_f args_nnil args_vals IH.
    induction args as [|? [|? ?] _] using rev_ind;
    simple; first easy.
    + inversion value_head_f; subst; simple; try easy.
      * now do 2 constructor; simple; rewrite H H0.
      * now do 3 constructor.
      * now do 3 constructor.
    + rewrite mkApps_app; simple.
      change (mkApps (tApp f t) l) with (mkApps f (t :: l)).
      apply value_app_nonnil; simple; try easy.
      * inversion value_head_f; try solve[constructor].
        { rewrite length_app in H1.
          now econstructor. }
        { econstructor; first eassumption.
          destruct with_guarded_fix; last easy.
          now rewrite length_app in H0. }
      * change (t :: l ++ [x])
        with ((t :: l) ++ [x])
        in args_vals.
        now apply All_app in args_vals as [? _].
Qed.

Ltac find_value_contra := solve[
  exfalso;
  try match goal with
  | h : value _ ?t, h' : head ?t = _
    |- _ =>
      apply value_value_head in h;
      rewrite h' in h
  end;
  eauto using tCase_not_val, tProj_not_val
].

Theorem unbox_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : eprogram_env)
  (v : term),
  has_tApp ->
  has_tBox || ~~ with_prop_case -> 
  ~~has_tCoFix ->
  ~~has_cstr_params ->
  with_constructor_as_block ->
  wf_eprogram_env efl p ->
  eval_eprogram_env wfl p v ->
  let ip := unbox_program p in
  eval_eprogram wfl ip (unbox p.1 v).
Proof.
  intros ? ? [ctx e] ? ? htBox nhtCofix nhCstrPms hCstrsAsBlcks [wf_ctx wf_e] [eval_e]; constructor; simple.
  induction eval_e; simple; subst.
  - destruct_IHs. crush eval_box.
  - destruct_IHs. crush eval_beta.
  - destruct_IHs. crush eval_zeta.
  - easy. 
  - destruct_IHs.
    { eapply wellformed_iota_red; try easy.
      - apply eval_wellformed in eval_e1; simple; last easy.
        destruct cstr_as_blocks; simple; try easy.
        destruct args; simple; easy.
      - destruct wf_e as (_ & _ & wf_e).
        rewrite -(Nat.add_0_r #|br.1|).
        now eapply wf_e, nth_error_In. }
    unfold is_unboxable, is_unboxable_clause_1, get_unboxable_case_branch in *; simple.
    destruct 
      (lookup_constructor ctx ind 0) 
      as [
        [
          [[ind_finite ind_npars ind_bodies] ind_body] 
          cstr_body
        ]
      |] eqn:heq; simple; try easy; last first.
    { eapply eval_iota_block.
      - assumption.
      - destruct c; easy.
      - unfold constructor_isprop_pars_decl in *; simple.
        now destruct (lookup_constructor ctx ind c) as [[[? ?]]|].
      - now simple.
      - now simple.
      - now simple.
      - unfold iota_red in *; simple. }
    assert (ind_npars = 0); subst.
    { unfold lookup_constructor, lookup_inductive in heq.
      destruct (lookup_minductive ctx (inductive_mind ind)) eqn:heq''; simple; try easy.
      unshelve eapply lookup_wf_minductive in heq''; try easy.
      destruct (nth_error (EAst.ind_bodies m) (inductive_ind ind)); simple; try easy.
      destruct (ind_ctors o); simple; try easy.
      injection heq as ? ? ?; subst; simple.
      unfold wf_minductive in heq''.
      simple.
      destruct heq'' as [h _].
      destruct has_cstr_params; try easy.
      destruct ind_npars; easy. }
      destruct (unboxable ind_body cstr_body) eqn:heq'; last first.
      { eapply eval_iota_block.
        - assumption.
        - destruct c; easy.
        - unfold constructor_isprop_pars_decl in *; simple.
          now destruct (lookup_constructor ctx ind c) as [[[? ?]]|].
        - now simple.
        - now simple.
        - now simple.
        - unfold iota_red in *; simple. }
      unfold unboxable in heq'.
      destruct ind_body as [ind_name ind_propositional ind_kelim [|ind_ctor [|??]] ind_projs], cstr_body as [cstr_name [|[|?]]]; simple; try easy.
      assert (1 == #|brs|). { 
        unfold wf_brs in wf_e.
        unfold lookup_constructor in *; simple.
        destruct (lookup_inductive ctx ind)
        as [[? [? ? ? [] ?]]|] eqn:heq''; simple; try easy.
        injection heq as ? ? ?; repeat (easy || simple || subst). }
      destruct
        brs as [|[[|? [|? ?]] ?] [| ? ?]],
        c as [|[|?]]; simple; try easy;
      rewrite /constructor_isprop_pars_decl heq in e1; simple;
      injection e1 as ? ? ?; subst; simple;
      injection e2 as ?; subst; simple;
      destruct args as [|arg [|? ?]]; simple; easy.
  - destruct_IHs; simpl in *.
    { assert (has_tBox) as htBox'.
      { destruct has_tBox, with_prop_case; simple; easy. }
      assert (
        forallb (wellformed ctx 0) (repeat tBox #|n|)
      ).
      { move: htBox'; clear. induction n; simpl; now simple. }
      apply wellformed_substl; simple.
      destruct wf_e as (? & ? & wf_e).
      now eapply (wf_e (_, _)). }
    unfold is_unboxable_clause_1, unboxable, lookup_constructor, inductive_isprop_and_pars in *.
    destruct (lookup_inductive ctx ind)
    as [
      [
        [ind_finite ind_npars ind_bodies] 
        [
          ind_name ind_propositional 
          ind_kelim ind_ctors ind_projs
        ]
      ]
    |] eqn:heq; simple; last easy.
    destruct (#|ind_ctors| == 1) eqn:heq'; last first.
    { destruct (ind_ctors) as [|? [|? ?]]; try easy.
      - eapply eval_iota_sing; simple; try easy.
        + unfold inductive_isprop_and_pars in *; simple.
        + simple.
          replace (repeat tBox #|n|) 
          with (map (unbox ctx) (repeat tBox #|n|));
          now simple.
      - eapply eval_iota_sing; simple; try easy.
        + unfold inductive_isprop_and_pars in *; simple.
        + simple.
          replace (repeat tBox #|n|) 
          with (map (unbox ctx) (repeat tBox #|n|));
          now simple. }
    destruct ind_ctors as [|ind_ctor [|? ?]]; try easy.
    simple.
    destruct (cstr_nargs ind_ctor == 1) eqn:heq''; last first.
    { eapply eval_iota_sing; simple; try easy.
      - unfold inductive_isprop_and_pars in *; simple.
      - simple.
        replace (repeat tBox #|n|) 
        with (map (unbox ctx) (repeat tBox #|n|));
        now simple. }
    unfold get_unboxable_case_branch; simple.
    destruct n as [|n [|n' ns]]; simple.
    + eapply eval_iota_sing; simple; try easy.
      unfold inductive_isprop_and_pars in *; simple.
    + crush eval_zeta.
    + eapply eval_iota_sing; simple; try easy.
      * unfold inductive_isprop_and_pars in *; simple.
      * rewrite unbox_substl unbox_csubst in H0; simple.
  - destruct_IHs. crush eval_fix.
  - destruct_IHs. crush eval_fix_value.
  - destruct_IHs. crush eval_fix'.
  - exfalso.
    clear IHeval_e1 IHeval_e2.
    apply eval_wellformed in eval_e1; try easy.
    rewrite wellformed_mkApps in eval_e1; simple.
    now apply (no_fixpoint_negb has_tCoFix).
  - exfalso.
    clear IHeval_e1 IHeval_e2.
    apply eval_wellformed in eval_e1; try easy.
    rewrite wellformed_mkApps in eval_e1; simple.
    now apply (no_fixpoint_negb has_tCoFix).
  - destruct_IHs.
    { rewrite /lookup_constant isdecl /= in wf_e.
      apply lookup_env_wellformed in isdecl; last assumption.
      rewrite /wf_global_decl e //= in isdecl. }
    econstructor; last easy.
    + unfold declared_constant in *. now simple.
    + now simple.
  - easy.
  - destruct_IHs.
    { apply eval_wellformed in eval_e1; simple; last easy.
      destruct cstr_as_blocks; simple.
      - assert (In a args); simple; try easy.
        now eapply nth_error_In.
      - destruct args; simple; easy. }
    unfold is_unboxable_clause_1, unboxable, constructor_isprop_pars_decl in *.
    destruct p as [proj_ind proj_npars proj_args]; simple.
    destruct (lookup_constructor ctx proj_ind 0) 
    as [
      [
        [
          [ind_finite ind_npars ind_bodies] 
          [
            ind_name ind_propositional 
            ind_kelim ind_ctors ind_projs 
            ]
        ] 
        [cstr_name cstr_nargs]
      ]
    |] eqn:heq; simple; last easy.
    injection e1 as ? ? ?; subst; simple.
    assert (proj_npars = 0); subst.
    { clear htBox nhtCofix wf_e H0 H1 eval_e2 e2 e3 hCstrsAsBlcks.
      unfold lookup_constructor, lookup_inductive in heq.
      destruct (lookup_minductive ctx (inductive_mind proj_ind)) eqn:heq'''; simple; try easy.
      unshelve eapply lookup_wf_minductive in heq'''; try assumption.
      destruct (nth_error (EAst.ind_bodies m) (inductive_ind proj_ind)); simple; try easy.
      destruct (EAst.ind_ctors o); simple; try easy.
      injection heq as ? ? ?; subst; simple.
      unfold wf_minductive in heq'''.
      simple.
      destruct heq''' as [h _].
      destruct has_cstr_params; try easy.
      destruct proj_npars; try easy. }
    destruct 
      ind_ctors as [|ind_ctor [| ? ?]],
      cstr_nargs as [|[|?]]; simple;
    try solve[
      eapply eval_proj_block; 
      repeat (
        unfold constructor_isprop_pars_decl || 
        rewrite heq ||
        simple ||
        easy
      )
    ].
    destruct args as [|? [|? ?]], proj_args as [|[|?]];
    simple; try easy.
    now eapply eval_trans.
  - destruct_IHs.
    unfold lookup_projection, is_unboxable_clause_1, inductive_isprop_and_pars, lookup_constructor in *.
    destruct p as [proj_ind proj_npars proj_arg]; simple.
    destruct (lookup_inductive ctx proj_ind) 
    as [[
        mdecl 
        [
          ind_name ind_propositional 
          ind_kelim [|[cstr_name [|[|?]]] [|? ?]] ind_projs
        ]
      ]|] eqn:heq; simple; try easy;
    eapply eval_proj_prop; repeat (
      easy ||
      unfold inductive_isprop_and_pars ||
      simple ||
      rewrite heq
    ).
  - easy.
  - unfold is_unboxable, is_unboxable_clause_1, lookup_constructor_pars_args in *; simple.
    destruct c as [|c]; simple; last first.
    { destruct cstr_as_blocks; last first.
      { destruct args, args'; simple; try solve[inversion a | easy].
        now eapply eval_construct_block; simple. }
      eapply eval_construct_block; simple; try easy.
      apply All2_All2_Set, All2_map.
      apply All2_over_undep in iha.
      unshelve eapply (All2_apply_dep_arrow _ iha).
      now simple. }
    rewrite ->e0 in *.
    destruct (unboxable idecl cdecl) eqn:heq; last first.
    { destruct cstr_as_blocks; last first.
      { destruct args, args'; simple; try solve[inversion a | easy].
        now eapply eval_construct_block; simple. }
      eapply eval_construct_block; simple; try easy.
      apply All2_All2_Set, All2_map.
      apply All2_over_undep in iha.
      unshelve eapply (All2_apply_dep_arrow _ iha).
      now simple. }
    unfold unboxable in heq; simple.
    destruct idecl 
    as [ind_name ind_propositional 
      ind_kelim [|ind_ctor [|??]] ind_projs]; simple; try easy.
    destruct cdecl as [cstr_name [|[|]]]; simple; try easy.
    unfold cstr_arity in *; simple.
    destruct mdecl as [ind_finite ind_npars ind_bodies].
    assert (ind_npars = 0); subst.
    { unfold lookup_constructor, lookup_inductive in e0.
      destruct (lookup_minductive ctx (inductive_mind ind)) eqn:heq''; simple; try easy.
      unshelve eapply lookup_wf_minductive in heq''; try easy.
      destruct (nth_error (EAst.ind_bodies m) (inductive_ind ind)); simple; try easy.
      destruct (EAst.ind_ctors o); simple; try easy.
      injection e0 as ? ? ?; subst; simple.
      unfold wf_minductive in heq''.
      simple.
      destruct heq'' as [h _].
      destruct has_cstr_params; try easy.
      destruct ind_npars; easy. }
    destruct args as [|arg [|? ?]]; simple; try easy. 
    inversion a; subst.
    inversion H4; subst.
    apply All2_over_undep in iha.
    unshelve epose proof (All2_apply_dep_arrow _ iha).
    + simple. intros ? [<- | []].
      now destruct cstr_as_blocks; simple.
    + now inversion X.
  - destruct_IHs.
    apply eval_to_value in eval_e1.
    apply eval_app_cong; try easy.
    simple. clear H0 H1.
    unfold isFixApp, isConstructApp, isPrimApp, isLazyApp in *.
    repeat split;
    repeat match goal with
    | |- context[with_guarded_fix] => destruct with_guarded_fix
    | |- context[head (unbox ctx ?f)] => 
        destruct (head f) eqn:heq; simple; try easy; try find_value_contra; solve[
          move:heq; clear;
          induction f'; simple; try easy;
          now rewrite !head_tApp
        ]
    | |- context[unbox ctx ?f] =>
        destruct f'; simple; try easy; find_value_contra
    end.
  - inversion X; subst; try solve[repeat constructor]; simple.
    rewrite /test_prim /= /test_array_model /= in wf_e.
    simple.
    destruct_IHs.
    unfold map_prim; simpl.
    do 2 constructor; last assumption.
    subst a a'; simpl in *.
    apply All2_All2_Set, All2_map.
    apply All2_over_undep in X0.
    unshelve eapply (All2_apply_dep_arrow _ X0).
    now simple.
  - destruct_IHs. crush eval_force.
  - apply eval_atom.
    destruct t; simple; try easy.
    destruct args; simple; try easy.
    now destruct (is_unboxable ctx ind n); simple.
Qed.

Lemma unbox_extends_eq (efl : EEnvFlags) (wfl : WcbvFlags) 
  (ctx ctx' : GlobalContextMap.t) k (e : term) :
  wf_glob ctx ->
  wf_glob ctx' ->
  wellformed ctx k e ->
  extends ctx ctx' ->
  unbox ctx' e = unbox ctx e.
Proof.
  induction e in k |- * using term_forall_list_ind; intros; simple; try solve[easy | now simple; f_equal].
  - simple; f_equal.
    apply All_map_eq; simple.
    intros; now eapply X.
  - destruct n; simple; last first.
    { simple; f_equal.
      apply All_map_eq; simple.
      intros; eapply X; try easy.
      destruct cstr_as_blocks; simple; first easy.
      destruct args; easy. }
    assert (lookup_constructor ctx' i 0 = lookup_constructor ctx i 0). 
    { destruct (lookup_constructor ctx i 0) eqn:heq; try easy.
      now eapply extends_lookup_constructor. }
    rewrite ->H3 in *.
    destruct (is_unboxable_clause_1 i (lookup_constructor ctx i 0)) eqn:heq; last first.
    { simple; f_equal.
      apply All_map_eq; simple.
      intros; eapply X; try easy.
      destruct cstr_as_blocks; simple; first easy.
      destruct args; easy. }
    destruct args as [|? [|? ?]]; simple; try easy.
    + eapply X; try easy.
      destruct cstr_as_blocks; now simple.
    + do 2 f_equal.
      { eapply X; try easy.
        destruct cstr_as_blocks; now simple. }
      f_equal.
      { eapply X; try easy.
        destruct cstr_as_blocks; now simple. }
      apply All_map_eq; simple.
      intros; eapply X; try easy.
      destruct cstr_as_blocks; simple; easy.
  - assert (lookup_constructor ctx' p.1 0 = lookup_constructor ctx p.1 0). 
    { unfold wf_brs, lookup_constructor in *.
      destruct (lookup_inductive ctx p.1) as [[[? ? ?] [? ? ? ?]]|] eqn:heq; simple; last easy.
      eapply extends_lookup_inductive in heq as heq'; try easy.
      now rewrite heq'. }
    rewrite ->H3 in *.
    destruct (is_unboxable_clause_1 p.1 (lookup_constructor ctx p.1 0)) eqn:heq; last first.
    { simple; f_equal; first easy.
      apply All_map_eq; simple.
      intros; unfold on_snd.
      f_equal. now eapply X. }
    assert (map (on_snd (unbox ctx')) l = map (on_snd (unbox ctx)) l).
    { apply All_map_eq; simple.
      intros; unfold on_snd.
      f_equal. now eapply X. }
    unfold get_unboxable_case_branch.
    rewrite H4.
    destruct (map (on_snd (unbox ctx)) l) as [|[[|? [|? ?]] ?] [|? ?]] eqn:heq'; try now f_equal.
  - assert (lookup_constructor ctx' (proj_ind s) 0 = lookup_constructor ctx (proj_ind s) 0). 
    { unfold wf_brs, lookup_projection, lookup_constructor in *.
      destruct (lookup_inductive ctx (proj_ind s)) as [[[? ? ?] [? ? ? ?]]|] eqn:heq; simple; last easy.
      eapply extends_lookup_inductive in heq as heq'; try easy.
      now rewrite heq'. }
    rewrite ->H3 in *.
    destruct (is_unboxable_clause_1 (proj_ind s) (lookup_constructor ctx (proj_ind s) 0)) eqn:heq; last now f_equal.
    easy.
  - simple; f_equal.
    apply All_map_eq; simple.
    unfold map_def.
    intros ? ?; unfold map_def; simple; f_equal.
    unfold wf_fix, test_def in H1; simple.
    now eapply X.
  - simple; f_equal.
    apply All_map_eq; simple.
    unfold map_def.
    intros ? ?; unfold map_def; simple; f_equal.
    unfold wf_fix, test_def in H1; simple.
    now eapply X.
  - simple; f_equal.
    inversion X as [| | | ? [? ?]]; subst; simple; try easy.
    unfold map_prim, map_array_model, test_prim, test_array_model in *; simple.
    do 3 f_equal; first easy.
    now apply All_map_eq; simple.
Qed.

Lemma unbox_extends (efl : EEnvFlags) (wfl : WcbvFlags) 
  (ctx ctx' : GlobalContextMap.t) :
  wf_glob ctx ->
  wf_glob ctx' ->
  extends ctx ctx' ->
  extends (unbox_env ctx) (unbox_env ctx').
Proof.
  intros wf_ctx wf_ctx' h_extends.
  intros name d.
  simple.
  destruct (lookup_env ctx name) as [[[[e|]]|]|]eqn:heq'; simple;
    try easy; last first.
  { unfold unbox_inductive_decl.
    intros [=<-].
    erewrite h_extends; last eassumption.
    simple; f_equal. }
  { unfold unbox_constant_decl; intros [=<-].
    erewrite h_extends; last eassumption.
    simple; f_equal. }
  unfold unbox_constant_decl; simple.
  intros [=<-].
  erewrite h_extends; last eassumption.
  simple; unfold unbox_constant_decl; simple; do 4 f_equal.
  eapply unbox_extends_eq; try easy.
  Search lookup_env wf_glob wellformed.
  apply (lookup_env_wellformed wf_ctx heq').
Qed.

End unbox.

(* Import MRList (map_InP, map_InP_spec). *)
(* Equations safe_hd {A} (l : list A) (nnil : l <> nil) : A :=
| [] | nnil := False_rect _ (nnil eq_refl)
| hd :: _ | _nnil := hd. *)
