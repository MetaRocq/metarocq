(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames Primitive BasicAst EnvMap.
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

#[global]
Hint Constructors eval : core.

Import MRList (map_InP, map_InP_spec).

Equations safe_hd {A} (l : list A) (nnil : l <> nil) : A :=
| [] | nnil := False_rect _ (nnil eq_refl)
| hd :: _ | _nnil := hd.

Definition inspect {A : Type} (x : A) : {y : A | x = y} :=
  @exist _ (fun y => x = y) x eq_refl.

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
        option_map _ ?e = Some _ =>
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


Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
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
  now destruct (nth_error (ind_ctors o) k).
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
  now destruct (nth_error (ind_projs o) (proj_arg name)).
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
  (* ~~cstr_as_blocks -> *)
  has_tLetIn ->
  wellformed ctx k t -> 
  wellformed ctx k (unbox Σ t).
Proof.
  (* destruct cstr_as_blocks eqn:has_cstr_blocks; first easy. *)
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
    rewrite get_unboxable_case_branch_spec in heq'''.
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
      simple; try now f_equal.
  - simple. destruct (k ?= n); reflexivity.
  - simple.
    f_equal.
    apply All_map_eq.
    now simple.
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
  - simple; f_equal.
    unfold map_def.
    apply All_map_eq.
    simple. intros. f_equal.
    easy.
  - simple; f_equal.
    unfold map_def.
    apply All_map_eq.
    simple. intros. f_equal.
    easy.
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
  simple.
  remember #|mfix| as n eqn:heq.
  clear heq.
  induction n as [|? IH]; first reflexivity.
  rewrite map_cons /=; f_equal.
  now rewrite IH.
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
  simple.
  remember #|mfix| as n eqn:heq.
  clear heq.
  induction n as [|? IH]; first reflexivity.
  rewrite map_cons /=; f_equal.
  now rewrite IH.
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

(* Lemma unbox_env_declared_constant ctx c decl :
  declared_constant ctx c decl ->
  declared_constant (unbox_env ctx) c (unbox_decl decl). *)

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
  eapply value_values_ind.
  - intros t h.
    now destruct t.
  - now simple.
  - now simple.
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
  has_tApp -> (* Needed for eval_wellformed *)
  has_tBox || ~~ with_prop_case -> 
  ~~has_tCoFix ->
  ~~has_cstr_params ->
  with_constructor_as_block ->
  wf_eprogram_env efl p ->
  eval_eprogram_env wfl p v ->
  let ip := unbox_program p in
  eval_eprogram wfl ip (unbox p.1 v).
Proof.
  intros ? ? [ctx e] ? ? htBox nhtCofix nhCstrPms hCstrsAsBlcks [wf_ctx wf_e] [eval_e]; simpl in *.
  constructor; simpl.
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
      |] eqn:heq; simple; try easy.
    + assert (ind_npars = 0); subst.
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
    + eapply eval_iota_block.
      * assumption.
      * destruct c; easy.
      * unfold constructor_isprop_pars_decl in *; simple.
        now destruct (lookup_constructor ctx ind c) as [[[? ?]]|].
      * now simple.
      * now simple.
      * now simple.
      * unfold iota_red in *; simple.
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
          now rewrite heq.
        + simple.
          replace (repeat tBox #|n|) 
          with (map (unbox ctx) (repeat tBox #|n|));
          now simple.
      - eapply eval_iota_sing; simple; try easy.
        + unfold inductive_isprop_and_pars in *; simple.
          now rewrite heq.
        + simple.
          replace (repeat tBox #|n|) 
          with (map (unbox ctx) (repeat tBox #|n|));
          now simple. }
    destruct ind_ctors as [|ind_ctor [|? ?]]; try easy.
    simple.
    destruct (cstr_nargs ind_ctor == 1) eqn:heq''; last first.
    { eapply eval_iota_sing; simple; try easy.
      - unfold inductive_isprop_and_pars in *; simple.
        now rewrite heq.
      - simple.
        replace (repeat tBox #|n|) 
        with (map (unbox ctx) (repeat tBox #|n|));
        now simple. }
    unfold get_unboxable_case_branch; simple.
    destruct n as [|n [|n' ns]]; simple.
    + eapply eval_iota_sing; simple; try easy.
      unfold inductive_isprop_and_pars in *; simple.
      now rewrite heq.
    + crush eval_zeta.
    + eapply eval_iota_sing; simple; try easy.
      * unfold inductive_isprop_and_pars in *; simple.
        now rewrite heq.
      * rewrite unbox_substl unbox_csubst in H0.
        simple.
  - destruct_IHs. crush eval_fix.
  - destruct_IHs. crush eval_fix_value.
  - destruct_IHs. crush eval_fix'.
  - exfalso.
    clear IHeval_e1 IHeval_e2.
    apply eval_wellformed in eval_e1; try easy.
    rewrite wellformed_mkApps in eval_e1; simple.
    destruct eval_e1 as [[? ?] ?].
    now apply (no_fixpoint_negb has_tCoFix).
  - exfalso.
    clear IHeval_e1 IHeval_e2.
    apply eval_wellformed in eval_e1; try easy.
    rewrite wellformed_mkApps in eval_e1; simple.
    destruct eval_e1 as [[? ?] ?].
    now apply (no_fixpoint_negb has_tCoFix).
  - destruct_IHs.
    { rewrite /lookup_constant isdecl /= in wf_e.
      apply lookup_env_wellformed in isdecl; last assumption.
      rewrite /wf_global_decl e //= in isdecl. }
    econstructor; last easy.
    + unfold declared_constant. simple.
      now rewrite isdecl.
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
  - destruct_IHs; simple.
    unfold is_unboxable, is_unboxable_clause_1, lookup_constructor_pars_args in *; simple.
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

(* 

Lemma map_unbox_repeat_box Σ n : 
  map (unbox Σ) (repeat tBox n) = repeat tBox n.
Proof.
  now simple.
Qed.

Arguments eqb : simpl never.


Lemma closed_unbox Σ t k : closedn k t -> closedn k (unbox Σ t).
Proof.
  induction t using term_forall_list_ind in k |- *;
  repeat (
    easy ||
    unfold test_def in * ||
    unfold test_prim in * ||
    unfold test_array_model in * ||
    invert_primProp ||
    simple
  ).
  - intros args_closed.
    destruct (is_unboxable Σ i n) eqn:i_unboxable; simple; last easy.
    assert (forall x, In x args -> closedn k (unbox Σ x)) by easy.
    destruct args as [|? [|? ?]]; simple; repeat split; auto.
  - unfold is_unboxable_clause_1.
    destruct (lookup_constructor Σ p.1 0)
      as [[[mind_body ind_body] constr_body] |] eqn:heq; simple; last easy.
    destruct (unboxable ind_body constr_body); simple; last easy.
    destruct (get_unboxable_case_branch p.1 l) as [[? ?]| ] eqn:heq'; simple; last easy.
    rewrite get_unboxable_case_branch_spec in heq'.
    destruct l as [|[? ?] [|? ?]]; try easy.
    unfold on_snd in heq'.
    simple.
    injection heq' as ? ?; subst.
    intros [? H].
    split; try easy.
    eapply (X (_, _)); simple; first easy.
    now eapply (H ([_], _)).
  - unfold is_unboxable_clause_1.
    destruct (lookup_constructor Σ (proj_ind s) 0) 
      as [[[mind_body ind_body] constr_body] |] eqn:heq; simple; last easy.
    destruct (unboxable ind_body constr_body); simple; easy.
Qed.    
(* 
Hint Rewrite @forallb_InP_spec : isEtaExp.
Transparent isEtaExp_unfold_clause_1. *)

  Local Lemma unbox_mkApps_nonnil Σ f v (nnil : v <> []):
    ~~ isApp f ->
    unbox Σ (mkApps f v) = match construct_viewc f with
      | view_construct kn c block_args =>
         if is_unboxable Σ kn c then unbox Σ (safe_hd v nnil)
         else mkApps (EAst.tConstruct kn c block_args) (map (unbox Σ) v)
      | view_other u nconstr => mkApps (unbox Σ f) (map (unbox Σ) v)
    end.
  Proof using Type.
  Admitted.
    (* intros napp.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp nnil) as [hna [hv' ->]].
    simp unbox; rewrite -unbox_equation_1.
    destruct (construct_viewc f).
    2:cbn; simp unbox => //.
    simp unbox.
    destruct (is_unboxable ind n) => //=. simp unbox.
    replace (safe_hd v hv') with (safe_hd v nnil) => //.
    destruct v; cbn => //.
    f_equal. now simp unbox.
  Qed. *)

  (* Lemma unbox_mkApps Σ f v : ~~ isApp f ->
    unbox Σ (mkApps f v) = match construct_viewc f with
      | view_construct kn c block_args =>
        if is_unboxable Σ kn c then
          match v with
          | hd :: _ => unbox Σ hd
          | _ => mkApps (EAst.tConstruct kn c block_args) (map (unbox Σ) v)
          end
        else mkApps (EAst.tConstruct kn c block_args) (map (unbox Σ) v)
      | view_other u nconstr => mkApps (unbox Σ f) (map (unbox Σ) v)
    end.
  Proof using Type.
  Admitted. *)
    (* intros napp.
    destruct v using rev_case; simpl.
    - destruct construct_viewc => //. simp unbox.
      destruct is_unboxable => //.
    - rewrite (unbox_mkApps_nonnil f (v ++ [x])) => //.
      destruct construct_viewc => //.
      destruct is_unboxable eqn:unb => //.
      destruct v eqn:hc => //=.
  Qed. *)

  Lemma lookup_inductive_pars_constructor_pars_args Σ {ind n pars args} :
    lookup_constructor_pars_args Σ ind n = Some (pars, args) ->
    lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
  Proof using Type.
    rewrite /lookup_constructor_pars_args /lookup_inductive_pars.
    rewrite /lookup_constructor /lookup_inductive. destruct lookup_minductive => //.
    cbn. do 2 destruct nth_error => //. congruence.
  Qed.
  
  

  Lemma unbox_iota_red Σ pars args br :
    unbox Σ (iota_red pars args br) = iota_red pars (map (unbox Σ) args) (on_snd (unbox Σ) br).
  Proof using Type.
    unfold iota_red.
    simple.
    rewrite unbox_substl //.
  Qed. *)

  (* Lemma unbox_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def unbox) mfix) = map unbox (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma unbox_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def unbox) mfix) = map unbox (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma unbox_cunfold_fix mfix idx n f :
    forallb (closedn 0) (fix_subst mfix) ->
    forallb (fun d =>  isLambda (dbody d) && isEtaExp Σ (dbody d)) mfix ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def unbox) mfix) idx = Some (n, unbox f).
  Proof using Type.
    intros hfix heta.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal. f_equal.
    rewrite unbox_substl //.
    now apply isEtaExp_fix_subst.
    solve_all. eapply nth_error_all in heta; tea. cbn in heta.
    rtoProp; intuition auto.
    f_equal. f_equal. apply unbox_fix_subst.
    discriminate.
  Qed.


  Lemma unbox_cunfold_cofix mfix idx n f :
    forallb (closedn 0) (cofix_subst mfix) ->
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def unbox) mfix) idx = Some (n, unbox f).
  Proof using Type.
    intros hcofix heta.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal.
    rewrite unbox_substl //.
    now apply isEtaExp_cofix_subst.
    solve_all. now eapply nth_error_all in heta; tea.
    f_equal. f_equal. apply unbox_cofix_subst.
    discriminate.
  Qed.

  Lemma unbox_nth {n l d} :
    unbox (nth n l d) = nth n (map unbox l) (unbox d).
  Proof using Type.
    induction l in n |- *; destruct n; simpl; auto.
  Qed. *)


End unbox.

(* #[universes(polymorphic)] Global Hint Rewrite @map_primIn_spec @map_InP_spec : unbox.
Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.
Tactic Notation "simp_unbox" "in" hyp(H) := simp unbox in H; rewrite -?unbox_equation_1 in H.
Ltac simp_unbox := simp unbox; rewrite -?unbox_equation_1.

Definition unbox_constant_decl Σ cb :=
  {| cst_body := option_map (unbox Σ) cb.(cst_body) |}.

Definition unbox_inductive_decl idecl :=
  {| ind_finite := idecl.(ind_finite); ind_npars := 0; ind_bodies := idecl.(ind_bodies) |}.

Definition unbox_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (unbox_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl (unbox_inductive_decl idecl)
  end.

Definition unbox_env Σ :=
  map (on_snd (unbox_decl Σ)) Σ.(GlobalContextMap.global_decls).

Import EGlobalEnv.

Lemma lookup_env_unbox Σ kn :
  lookup_env (unbox_env Σ) kn =
  option_map (unbox_decl Σ) (lookup_env Σ.(GlobalContextMap.global_decls) kn).
Proof.
  unfold unbox_env.
  destruct Σ as [Σ map repr wf]; cbn.
  induction Σ at 2 4; simpl; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_constructor_unbox {Σ kn c} :
  lookup_constructor (unbox_env Σ) kn c =
  match lookup_constructor Σ.(GlobalContextMap.global_decls) kn c with
  | Some (mdecl, idecl, cdecl) => Some (unbox_inductive_decl mdecl, idecl, cdecl)
  | None => None
  end.
Proof.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_unbox.
  destruct lookup_env as [[]|] => /= //.
  do 2 destruct nth_error => //.
Qed.

Lemma lookup_constructor_pars_args_unbox (Σ : GlobalContextMap.t) i n npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  EGlobalEnv.lookup_constructor_pars_args (unbox_env Σ) i n = Some (0, nargs).
Proof.
  rewrite /EGlobalEnv.lookup_constructor_pars_args. rewrite lookup_constructor_unbox //=.
  destruct EGlobalEnv.lookup_constructor => //. destruct p as [[] ?] => //=. now intros [= <- <-].
Qed.

Lemma is_propositional_unbox (Σ : GlobalContextMap.t) ind :
  match inductive_isprop_and_pars Σ.(GlobalContextMap.global_decls) ind with
  | Some (prop, npars) =>
    inductive_isprop_and_pars (unbox_env Σ) ind = Some (prop, 0)
  | None =>
    inductive_isprop_and_pars (unbox_env Σ) ind = None
  end.
Proof.
  rewrite /inductive_isprop_and_pars /lookup_inductive /lookup_minductive.
  rewrite lookup_env_unbox.
  destruct lookup_env; simpl; auto.
  destruct g; simpl; auto. destruct nth_error => //.
Qed.

Lemma is_propositional_cstr_unbox {Σ : GlobalContextMap.t} {ind c} :
  match constructor_isprop_pars_decl Σ.(GlobalContextMap.global_decls) ind c with
  | Some (prop, npars, cdecl) =>
    constructor_isprop_pars_decl (unbox_env Σ) ind c = Some (prop, 0, cdecl)
  | None =>
  constructor_isprop_pars_decl (unbox_env Σ) ind c = None
  end.
Proof.
  rewrite /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_unbox.
  destruct lookup_env; simpl; auto.
  destruct g; simpl; auto. do 2 destruct nth_error => //.
Qed.

Lemma lookup_inductive_pars_unbox {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  forall pars, lookup_inductive_pars Σ ind = Some pars ->
  EGlobalEnv.lookup_inductive_pars (unbox_env Σ) ind = Some 0.
Proof.
  rewrite /lookup_inductive_pars => wf pars.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_unbox _ ind).
  destruct lookup_env as [[decl|]|] => //=.
Qed.

Arguments eval {wfl}.

Arguments isEtaExp : simpl never.

Lemma isEtaExp_mkApps {Σ} {f u} : isEtaExp Σ (tApp f u) ->
  let (hd, args) := decompose_app (tApp f u) in
  match construct_viewc hd with
  | view_construct kn c block_args =>
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\
    isEtaExp_app Σ kn c #|args| && forallb (isEtaExp Σ) args && is_nil block_args
  | view_other _ discr =>
    [&& isEtaExp Σ hd, forallb (isEtaExp Σ) args, isEtaExp Σ f & isEtaExp Σ u]
  end.
Proof.
  move/(isEtaExp_mkApps Σ f [u]).
  cbn -[decompose_app]. destruct decompose_app eqn:da.
  destruct construct_viewc eqn:cv => //.
  intros ->.
  pose proof (decompose_app_inv da).
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H.
  rewrite mkApps_app in H. noconf H.
  rewrite remove_last_app last_last. intuition auto.
  destruct l; cbn in *; congruence.
  pose proof (decompose_app_inv da).
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l using rev_case. cbn. intuition auto. destruct t => //.
  rewrite mkApps_app in H. noconf H.
  move=> /andP[] etat. rewrite forallb_app => /andP[] etal /=.
  rewrite andb_true_r => etaa. rewrite etaa andb_true_r.
  rewrite etat etal. cbn. rewrite andb_true_r.
  eapply isEtaExp_mkApps_intro; auto; solve_all.
Qed.

Lemma decompose_app_tApp_split f a hd args :
  decompose_app (tApp f a) = (hd, args) -> f = mkApps hd (remove_last args) /\ a = last args a.
Proof.
  unfold decompose_app. cbn.
  move/decompose_app_rec_inv' => [n [napp [hskip heq]]].
  rewrite -(firstn_skipn n args).
  rewrite -hskip. rewrite last_last; split => //.
  rewrite heq. f_equal.
  now rewrite remove_last_app.
Qed.

Arguments lookup_inductive_pars_constructor_pars_args {Σ ind n pars args}.

Lemma unbox_tApp {Σ : GlobalContextMap.t} f a : isEtaExp Σ f -> isEtaExp Σ a -> unbox Σ (EAst.tApp f a) = EAst.tApp (unbox Σ f) (unbox Σ a).
Proof.
  move=> etaf etaa.
  pose proof (isEtaExp_mkApps_intro _ _ [a] etaf).
  forward H by eauto.
  move/isEtaExp_mkApps: H.
  destruct decompose_app eqn:da.
  destruct construct_viewc eqn:cv => //. *)
  (* { intros [? [? []]]. rewrite H0 /=.
    rewrite -[EAst.tApp _ _ ](mkApps_app _ _ [a]).
    move/andP: H2 => []. rewrite /isEtaExp_app.
    rewrite !unbox_mkApps // cv.
    destruct lookup_constructor_pars_args as [[pars args]|] eqn:hl => //.
    rewrite (lookup_inductive_pars_constructor_pars_args hl).
    intros hpars etal.
    rewrite -[EAst.tApp _ _ ](mkApps_app _ _ [unbox Σ a]).
    f_equal. rewrite !skipn_map !skipn_app map_app. f_equal.
    assert (pars - #|remove_last l| = 0) as ->.
    2:{ rewrite skipn_0 //. }
    rewrite H0 in etaf.
    rewrite isEtaExp_mkApps_napp // in etaf.
    simp construct_viewc in etaf.
    move/andP: etaf => []. rewrite /isEtaExp_app hl.
    move => /andP[] /Nat.leb_le. lia. }
  { move/and4P=> [] iset isel _ _. rewrite (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    rewrite unbox_mkApps //.
    destruct (decompose_app_tApp_split _ _ _ _ da).
    rewrite cv. rewrite H0.
    rewrite unbox_mkApps // cv.
    rewrite -[EAst.tApp _ _ ](mkApps_app _ _ [unbox Σ a]). f_equal.
    rewrite -[(_ ++ _)%list](map_app (unbox Σ) _ [a]).
    f_equal.
    assert (l <> []).
    { destruct l; try congruence. eapply decompose_app_inv in da. cbn in *. now subst t. }
    rewrite H1.
    now apply remove_last_last. } 
Qed.*)
(*
Module Fast.
  Section fastunbox.
    Context (Σ : GlobalContextMap.t).

    Equations unbox (app : list term) (t : term) : term := {
    | app, tEvar ev args => mkApps (EAst.tEvar ev (unbox_args args)) app
    | app, tLambda na M => mkApps (EAst.tLambda na (unbox [] M)) app
    | app, tApp u v => unbox (unbox [] v :: app) u
    | app, tLetIn na b b' => mkApps (EAst.tLetIn na (unbox [] b) (unbox [] b')) app
    | app, tCase ind c brs =>
        let brs' := unbox_brs brs in
        mkApps (EAst.tCase (ind.1, 0) (unbox [] c) brs') app
    | app, tProj p c => mkApps (EAst.tProj {| proj_ind := p.(proj_ind); proj_npars := 0; proj_arg := p.(proj_arg) |} (unbox [] c)) app
    | app, tFix mfix idx =>
        let mfix' := unbox_defs mfix in
        mkApps (EAst.tFix mfix' idx) app
    | app, tCoFix mfix idx =>
        let mfix' := unbox_defs mfix in
        mkApps (EAst.tCoFix mfix' idx) app
    | app, tConstruct kn c block_args with GlobalContextMap.lookup_inductive_pars Σ (inductive_mind kn) := {
        | Some npars => mkApps (EAst.tConstruct kn c block_args) (List.skipn npars app)
        | None => mkApps (EAst.tConstruct kn c block_args) app }
    | app, tPrim (primInt; primIntModel i) => mkApps (tPrim (primInt; primIntModel i)) app
    | app, tPrim (primFloat; primFloatModel f) => mkApps (tPrim (primFloat; primFloatModel f)) app
    | app, tPrim (primArray; primArrayModel a) =>
      mkApps (tPrim (primArray; primArrayModel {| array_default := unbox [] a.(array_default); array_value := unbox_args a.(array_value) |})) app
    | app, x => mkApps x app }

    where unbox_args (t : list term) : list term :=
    { | [] := []
      | a :: args := (unbox [] a) :: unbox_args args
    }

    where unbox_brs (t : list (list BasicAst.name × term)) : list (list BasicAst.name × term) :=
    { | [] := []
      | a :: args := (a.1, (unbox [] a.2)) :: unbox_brs args }

    where unbox_defs (t : mfixpoint term) : mfixpoint term :=
    { | [] := []
      | d :: defs := {| dname := dname d; dbody := unbox [] d.(dbody); rarg := d.(rarg) |} :: unbox_defs defs
    }.

    Local Ltac specIH :=
          match goal with
          | [ H : (forall args : list term, _) |- _ ] => specialize (H [] eq_refl)
          end.

    Lemma unbox_acc_opt t :
      forall args, ERemoveParams.unbox Σ (mkApps t args) = unbox (map (ERemoveParams.unbox Σ) args) t.
    Proof using Type.
      intros args.
      remember (map (ERemoveParams.unbox Σ) args) as args'.
      revert args Heqargs'.
      set (P:= fun args' t fs => forall args, args' = map (ERemoveParams.unbox Σ) args -> ERemoveParams.unbox Σ (mkApps t args) = fs).
      apply (unbox_elim P
        (fun l l' => map (ERemoveParams.unbox Σ) l = l')
        (fun l l' => map (on_snd (ERemoveParams.unbox Σ)) l = l')
        (fun l l' => map (map_def (ERemoveParams.unbox Σ)) l = l')); subst P; cbn -[GlobalContextMap.lookup_inductive_pars isEtaExp ERemoveParams.unbox]; clear.
      all: try reflexivity.
      all: intros *; simp_eta; simp_unbox.
      all: try solve [intros; subst; rtoProp; rewrite unbox_mkApps // /=; simp_unbox; repeat specIH; repeat (f_equal; intuition eauto)].
      all: try solve [rewrite unbox_mkApps //].
      - intros IHv IHu.
        specialize (IHv [] eq_refl). simpl in IHv.
        intros args ->. specialize (IHu (v :: args)).
        forward IHu. now rewrite -IHv. exact IHu.
      - intros Hl hargs args ->.
        rewrite unbox_mkApps //=. simp_unbox.
        f_equal. f_equal. cbn.
        do 2 f_equal. rewrite /map_array_model.
        specialize (Hl [] eq_refl). f_equal; eauto.
      - intros Hl args ->.
        rewrite unbox_mkApps // /=.
        rewrite GlobalContextMap.lookup_inductive_pars_spec in Hl. now rewrite Hl.
      - intros Hl args ->.
        rewrite GlobalContextMap.lookup_inductive_pars_spec in Hl.
        now rewrite unbox_mkApps // /= Hl.
      - intros IHa heq.
        specIH. now rewrite IHa.
      - intros IHa heq; specIH. f_equal; eauto. unfold on_snd. now rewrite IHa.
      - intros IHa heq; specIH. unfold map_def. f_equal; eauto. now rewrite IHa.
    Qed.

    Lemma unbox_fast t : ERemoveParams.unbox Σ t = unbox [] t.
    Proof using Type. now apply (unbox_acc_opt t []). Qed.

  End fastunbox.

  Notation unbox' Σ := (unbox Σ []).

  Definition unbox_constant_decl Σ cb :=
    {| cst_body := option_map (unbox' Σ) cb.(cst_body) |}.

  Definition unbox_inductive_decl idecl :=
    {| ind_finite := idecl.(ind_finite); ind_npars := 0; ind_bodies := idecl.(ind_bodies) |}.

  Definition unbox_decl Σ d :=
    match d with
    | ConstantDecl cb => ConstantDecl (unbox_constant_decl Σ cb)
    | InductiveDecl idecl => InductiveDecl (unbox_inductive_decl idecl)
    end.

  Definition unbox_env Σ :=
    map (on_snd (unbox_decl Σ)) Σ.(GlobalContextMap.global_decls).

  Lemma unbox_env_fast Σ : ERemoveParams.unbox_env Σ = unbox_env Σ.
  Proof.
    unfold ERemoveParams.unbox_env, unbox_env.
    destruct Σ as [Σ map repr wf]. cbn.
    induction Σ at 2 4; cbn; auto.
    f_equal; eauto.
    destruct a as [kn []]; cbn; auto.
    destruct c as [[b|]]; cbn; auto. unfold on_snd; cbn.
    do 2 f_equal. unfold ERemoveParams.unbox_constant_decl, unbox_constant_decl.
    simpl. f_equal. f_equal. apply unbox_fast.
  Qed.

End Fast.

Lemma isLambda_mkApps' f l :
  l <> nil ->
  ~~ EAst.isLambda (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isBox_mkApps' f l :
  l <> nil ->
  ~~ isBox (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isFix_mkApps' f l :
  l <> nil ->
  ~~ isFix (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isLambda_mkApps_Construct ind n block_args l :
  ~~ EAst.isLambda (EAst.mkApps (EAst.tConstruct ind n block_args) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isBox_mkApps_Construct ind n block_args l :
  ~~ isBox (EAst.mkApps (EAst.tConstruct ind n block_args) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isFix_mkApps_Construct ind n block_args l :
  ~~ isFix (EAst.mkApps (EAst.tConstruct ind n block_args) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma unbox_isLambda Σ f :
  EAst.isLambda f = EAst.isLambda (unbox Σ f).
Proof.
  funelim (unbox Σ f); cbn -[unbox]; (try simp_unbox) => //.
  rewrite (negbTE (isLambda_mkApps' _ _ _)) //.
  rewrite (negbTE (isLambda_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rewrite !(negbTE (isLambda_mkApps_Construct _ _ _ _)) //.
Qed.

Lemma unbox_isBox Σ f :
  isBox f = isBox (unbox Σ f).
Proof.
  funelim (unbox Σ f); cbn -[unbox] => //.
  all:rewrite map_InP_spec.
  rewrite (negbTE (isBox_mkApps' _ _ _)) //.
  rewrite (negbTE (isBox_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rewrite !(negbTE (isBox_mkApps_Construct _ _ _ _)) //.
Qed.

Lemma isApp_mkApps u v : v <> nil -> isApp (mkApps u v).
Proof.
  destruct v using rev_case; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma unbox_isApp Σ f :
  ~~ EAst.isApp f ->
  ~~ EAst.isApp (unbox Σ f).
Proof.
  funelim (unbox Σ f); cbn -[unbox] => //.
  all:rewrite map_InP_spec.
  all:rewrite isApp_mkApps //.
Qed.

Lemma unbox_isFix Σ f :
  isFix f = isFix (unbox Σ f).
Proof.
  funelim (unbox Σ f); cbn -[unbox] => //.
  all:rewrite map_InP_spec.
  rewrite (negbTE (isFix_mkApps' _ _ _)) //.
  rewrite (negbTE (isFix_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rewrite !(negbTE (isFix_mkApps_Construct _ _ _ _)) //.
Qed.

Lemma unbox_isFixApp Σ f :
  isFixApp f = isFixApp (unbox Σ f).
Proof.
  funelim (unbox Σ f); cbn -[unbox] => //.
  all:rewrite map_InP_spec.
  all:rewrite isFixApp_mkApps isFixApp_mkApps //.
Qed.

Lemma unbox_isConstructApp Σ f :
  isConstructApp f = isConstructApp (unbox Σ f).
Proof.
  funelim (unbox Σ f); cbn -[unbox] => //.
  all:rewrite map_InP_spec.
  all:rewrite isConstructApp_mkApps isConstructApp_mkApps //.
Qed.

Lemma unbox_isPrimApp Σ f :
  isPrimApp f = isPrimApp (unbox Σ f).
Proof.
  funelim (unbox Σ f); cbn -[unbox] => //.
  all:rewrite map_InP_spec.
  all:rewrite !isPrimApp_mkApps //.
Qed.

Lemma lookup_inductive_pars_is_prop_and_pars {Σ ind b pars} :
  inductive_isprop_and_pars Σ ind = Some (b, pars) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
Proof.
  rewrite /inductive_isprop_and_pars /lookup_inductive_pars /lookup_inductive /lookup_minductive.
  destruct lookup_env => //.
  destruct g => /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_lookup {Σ ind c b pars decl} :
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, decl) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
Proof.
  rewrite /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive_pars /lookup_inductive /lookup_minductive.
  destruct lookup_env => //.
  destruct g => /= //.
  destruct nth_error => //. destruct nth_error => //. congruence.
Qed.

Lemma constructor_isprop_pars_inductive_pars {Σ ind c b pars decl} :
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, decl) ->
  inductive_isprop_and_pars Σ ind = Some (b, pars).
Proof.
  rewrite /constructor_isprop_pars_decl /inductive_isprop_and_pars /lookup_constructor.
  destruct lookup_inductive as [[mdecl idecl]|] => /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma lookup_constructor_lookup_inductive_pars {Σ ind c mdecl idecl cdecl} :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some mdecl.(ind_npars).
Proof.
  rewrite /lookup_constructor /lookup_inductive_pars /lookup_inductive /lookup_minductive.
  destruct lookup_env => //.
  destruct g => /= //.
  destruct nth_error => //. destruct nth_error => //. congruence.
Qed.

Lemma unbox_mkApps_etaexp {Σ : GlobalContextMap.t} fn args :
  isEtaExp Σ fn ->
  unbox Σ (EAst.mkApps fn args) = EAst.mkApps (unbox Σ fn) (map (unbox Σ) args).
Proof.
  destruct (decompose_app fn) eqn:da.
  rewrite (decompose_app_inv da).
  rewrite isEtaExp_mkApps_napp. now eapply decompose_app_notApp.
  destruct construct_viewc eqn:vc.
  + move=> /andP[] hl0 etal0.
    rewrite -mkApps_app.
    rewrite (unbox_mkApps Σ (tConstruct ind n block_args)) // /=.
    rewrite unbox_mkApps // /=.
    unfold isEtaExp_app in hl0.
    destruct lookup_constructor_pars_args as [[pars args']|] eqn:hl => //.
    rtoProp.
    eapply Nat.leb_le in H.
    rewrite (lookup_inductive_pars_constructor_pars_args hl).
    rewrite -mkApps_app. f_equal. rewrite map_app.
    rewrite skipn_app. len. assert (pars - #|l| = 0) by lia.
    now rewrite H1 skipn_0.
  + move=> /andP[] etat0 etal0.
    rewrite -mkApps_app !unbox_mkApps; try now eapply decompose_app_notApp.
    rewrite vc. rewrite -mkApps_app !map_app //.
Qed.

 #[export] Instance Qpreserves_closedn (efl := all_env_flags) Σ : closed_env Σ ->
  Qpreserves (fun n x => closedn n x) Σ.
Proof.
  intros clΣ.
  split.
  - red. move=> n t.
    destruct t; cbn; intuition auto; try solve [constructor; auto].
    eapply on_evar; solve_all.
    eapply on_letin; rtoProp; intuition auto.
    eapply on_app; rtoProp; intuition auto.
    eapply on_case; rtoProp; intuition auto. solve_all.
    eapply on_fix. solve_all. solve_all.
    eapply on_cofix; solve_all.
    eapply on_prim; solve_all.
  - red. intros kn decl.
    move/(lookup_env_closed clΣ).
    unfold closed_decl. destruct EAst.cst_body => //.
  - red. move=> hasapp n t args. rewrite closedn_mkApps.
    split; intros; rtoProp; intuition auto; solve_all.
  - red. move=> hascase n ci discr brs. simpl.
    intros; rtoProp; intuition auto; solve_all.
  - red. move=> hasproj n p discr. simpl.
    intros; rtoProp; intuition auto; solve_all.
  - red. move=> t args clt cll.
    eapply closed_substl. solve_all. now rewrite Nat.add_0_r.
  - red. move=> n mfix idx. cbn.
    intros; rtoProp; intuition auto; solve_all.
  - red. move=> n mfix idx. cbn.
    intros; rtoProp; intuition auto; solve_all.
Qed.

Lemma unbox_eval (efl := all_env_flags) {wfl:WcbvFlags} {wcon : with_constructor_as_block = false} {Σ : GlobalContextMap.t} t v :
  isEtaExp_env Σ ->
  closed_env Σ ->
  wf_glob Σ ->
  closedn 0 t ->
  isEtaExp Σ t ->
  eval Σ t v ->
  eval (unbox_env Σ) (unbox Σ t) (unbox Σ v).
Proof.
  intros etaΣ clΣ wfΣ.
  revert t v.
  unshelve eapply (eval_preserve_mkApps_ind wfl wcon Σ (fun x y => eval (unbox_env Σ) (unbox Σ x) (unbox Σ y))
    (fun n x => closedn n x) (Qpres := Qpreserves_closedn Σ clΣ)) => //.
  { intros. eapply eval_closed; tea. }
  all:intros; simpl in *.
  all:repeat destruct_nary_times => //.
  - rewrite unbox_tApp //.
    econstructor; eauto.

  - rewrite unbox_tApp //. simp_unbox in e1.
    econstructor; eauto.
    rewrite unbox_csubst // in e. now simp_eta in i10.

  - simp_unbox.
    rewrite unbox_csubst // in e.
    econstructor; eauto.

  - simp_unbox.
    set (brs' := map _ brs). cbn -[unbox].
    cbn in H3.
    rewrite unbox_mkApps // /= in e0.
    apply constructor_isprop_pars_decl_lookup in H2 as H1'.
    rewrite H1' in e0.
    pose proof (@is_propositional_cstr_unbox Σ ind c).
    rewrite H2 in H1.
    econstructor; eauto.
    * rewrite nth_error_map H3 //.
    * len. cbn in H4, H5. rewrite length_skipn. lia.
    * cbn -[unbox]. rewrite skipn_0. len.
    * cbn -[unbox].
      have etaargs : forallb (isEtaExp Σ) args.
      { rewrite isEtaExp_Constructor in i6.
        now move/andP: i6 => [] /andP[]. }
      rewrite unbox_iota_red // in e.
      rewrite closedn_mkApps in i4. now move/andP: i4.
      cbn. now eapply nth_error_forallb in H; tea.

  - subst brs. cbn in H4.
    rewrite andb_true_r in H4.
    rewrite unbox_substl // in e.
    eapply All_forallb, All_repeat => //.
    eapply All_forallb, All_repeat => //.
    rewrite map_unbox_repeat_box in e.
    simp_unbox. set (brs' := map _ _).
    cbn -[unbox]. eapply eval_iota_sing => //.
    now move: (is_propositional_unbox Σ ind); rewrite H2.

  - rewrite unbox_tApp //.
    rewrite unbox_mkApps // /= in e1.
    simp_unbox in e1.
    eapply eval_fix; tea.
    * rewrite length_map.
      eapply unbox_cunfold_fix; tea.
      eapply closed_fix_subst. tea.
      move: i8; rewrite closedn_mkApps => /andP[] //.
      move: i10; rewrite isEtaExp_mkApps_napp // /= => /andP[] //. simp_eta.
    * move: e.
      rewrite -[tApp _ _](mkApps_app _ _ [av]).
      rewrite -[tApp _ _](mkApps_app _ _ [unbox _ av]).
      rewrite unbox_mkApps_etaexp // map_app //.

  - rewrite unbox_tApp //.
    rewrite unbox_tApp //.
    rewrite unbox_mkApps //. simpl.
    simp_unbox. set (mfix' := map _ _). simpl.
    rewrite unbox_mkApps // /= in e0. simp_unbox in e0.
    eapply eval_fix_value; tea.
    eapply unbox_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    { move: i4.
      rewrite closedn_mkApps. now move/andP => []. }
    { move: i6. rewrite isEtaExp_mkApps_napp // /= => /andP[] //. now simp isEtaExp. }
    now rewrite length_map.

  - rewrite unbox_tApp //. simp_unbox in e0.
    simp_unbox in e1.
    eapply eval_fix'; tea.
    eapply unbox_cunfold_fix; tea.
    { eapply closed_fix_subst => //. }
    { simp isEtaExp in i10. }
    rewrite unbox_tApp // in e.

  - simp_unbox.
    rewrite unbox_mkApps // /= in e0.
    simp_unbox in e.
    simp_unbox in e0.
    set (brs' := map _ _) in *; simpl.
    eapply eval_cofix_case; tea.
    eapply unbox_cunfold_cofix; tea => //.
    { eapply closed_cofix_subst; tea.
      move: i5; rewrite closedn_mkApps => /andP[] //. }
    { move: i7. rewrite isEtaExp_mkApps_napp // /= => /andP[] //. now simp isEtaExp. }
    rewrite unbox_mkApps_etaexp // in e.

  - destruct p as [[ind pars] arg].
    simp_unbox.
    simp_unbox in e.
    rewrite unbox_mkApps // /= in e0.
    simp_unbox in e0.
    rewrite unbox_mkApps_etaexp // in e.
    simp_unbox in e0.
    eapply eval_cofix_proj; tea.
    eapply unbox_cunfold_cofix; tea.
    { eapply closed_cofix_subst; tea.
      move: i4; rewrite closedn_mkApps => /andP[] //. }
    { move: i6. rewrite isEtaExp_mkApps_napp // /= => /andP[] //. now simp isEtaExp. }

  - econstructor. red in H |- *.
    rewrite lookup_env_unbox H //.
    now rewrite /unbox_constant_decl H0.
    exact e.

  - simp_unbox.
    rewrite unbox_mkApps // /= in e0.
    rewrite (constructor_isprop_pars_decl_lookup H2) in e0.
    eapply eval_proj; eauto.
    move: (@is_propositional_cstr_unbox Σ p.(proj_ind) 0). now rewrite H2. simpl.
    len. rewrite length_skipn. cbn in H3. lia.
    rewrite nth_error_skipn nth_error_map /= H4 //.

  - simp_unbox. eapply eval_proj_prop => //.
    move: (is_propositional_unbox Σ p.(proj_ind)); now rewrite H3.

  - rewrite !unbox_tApp //.
    eapply eval_app_cong; tea.
    move: H1. eapply contraNN.
    rewrite -unbox_isLambda -unbox_isConstructApp -unbox_isFixApp -unbox_isBox -unbox_isPrimApp //.
    rewrite -unbox_isFix //.

  - rewrite !unbox_mkApps // /=.
    rewrite (lookup_constructor_lookup_inductive_pars H).
    eapply eval_mkApps_Construct; tea.
    + rewrite lookup_constructor_unbox H //.
    + constructor. cbn [atom]. rewrite wcon lookup_constructor_unbox H //.
    + rewrite /cstr_arity /=.
      move: H0; rewrite /cstr_arity /=.
      rewrite length_skipn length_map => ->. lia.
    + cbn in H0. eapply All2_skipn, All2_map.
      eapply All2_impl; tea; cbn -[unbox].
      intros x y []; auto.

  - depelim X; simp unbox; repeat constructor.
    eapply All2_over_undep in a. eapply All2_Set_All2 in ev. eapply All2_All2_Set. solve_all. now destruct b.
    now destruct a0.

  - destruct t => //.
    all:constructor; eauto. simp unbox.
    cbn [atom unbox] in H |- *.
    rewrite lookup_constructor_unbox.
    destruct lookup_constructor eqn:hl => //. destruct p as [[] ?] => //.
Qed.

From MetaRocq.Erasure Require Import EEtaExpanded.

Lemma unbox_declared_constructor {Σ : GlobalContextMap.t} {k mdecl idecl cdecl} :
  declared_constructor Σ.(GlobalContextMap.global_decls)  k mdecl idecl cdecl ->
  declared_constructor (unbox_env Σ) k (unbox_inductive_decl mdecl) idecl cdecl.
Proof.
  intros [[] ?]; do 2 split => //.
  red in H; red.
  rewrite lookup_env_unbox H //.
Qed.

Lemma lookup_inductive_pars_spec {Σ} {mind} {mdecl} :
  declared_minductive Σ mind mdecl ->
  lookup_inductive_pars Σ mind = Some (ind_npars mdecl).
Proof.
  rewrite /declared_minductive /lookup_inductive_pars /lookup_minductive.
  now intros -> => /=.
Qed.

Definition switch_no_params (efl : EEnvFlags) :=
  {| has_axioms := has_axioms;
     has_cstr_params := false;
     term_switches := term_switches ;
     cstr_as_blocks := cstr_as_blocks
     |}.

(* Stripping preserves well-formedness directly, not caring about eta-expansion *)
Lemma unbox_wellformed {efl} {Σ : GlobalContextMap.t} n t :
  cstr_as_blocks = false ->
  has_tApp ->
  @wf_glob efl Σ ->
  @wellformed efl Σ n t ->
  @wellformed (switch_no_params efl) (unbox_env Σ) n (unbox Σ t).
Proof.
  intros cab hasapp wfΣ.
  revert n.
  funelim (unbox Σ t); try intros n.
  all:cbn -[unbox lookup_constructor lookup_inductive]; simp_unbox; intros.
  all:try solve[unfold wf_fix_gen in *; rtoProp; intuition auto; toAll; solve_all].
  - cbn -[unbox]; simp_unbox. intros; rtoProp; intuition auto.
    rewrite lookup_env_unbox. destruct lookup_env eqn:hl => // /=.
    destruct g => /= //. destruct (cst_body c) => //.
  - rewrite cab in H |- *. cbn -[unbox] in *.
    rewrite lookup_env_unbox. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. destruct nth_error => //.
  - cbn -[unbox].
    rewrite lookup_env_unbox. cbn in H1. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. rtoProp; intuition auto.
    simp_unbox. toAll; solve_all.
    toAll. solve_all.
  - cbn -[unbox] in H0 |- *.
    rewrite lookup_env_unbox. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g. cbn in H0. now rtoProp.
    destruct nth_error => //. all:rtoProp; intuition auto.
    destruct EAst.ind_ctors => //.
    destruct nth_error => //.
    all: eapply H; auto.
  - unfold wf_fix_gen in *. rewrite length_map. rtoProp; intuition auto. toAll; solve_all.
    now rewrite -unbox_isLambda. toAll; solve_all.
  - primProp. rtoProp; intuition eauto; solve_all_k 6.
  - move:H1; rewrite !wellformed_mkApps //. rtoProp; intuition auto.
    toAll; solve_all. toAll; solve_all.
  - move:H0; rewrite !wellformed_mkApps //. rtoProp; intuition auto.
    move: H1. cbn. rewrite cab.
    rewrite lookup_env_unbox. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. destruct nth_error => //.
    toAll; solve_all. eapply All_skipn. solve_all.
  - move:H0; rewrite !wellformed_mkApps //. rtoProp; intuition auto.
    move: H1. cbn. rewrite cab.
    rewrite lookup_env_unbox. destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => //. destruct nth_error => //.
    toAll; solve_all.
Qed.

Lemma unbox_wellformed_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t :
  cstr_as_blocks = false ->
  wf_glob Σ ->
  forall n, wellformed Σ n t -> wellformed (unbox_env Σ) n t.
Proof.
  intros hcstrs wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_unbox //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct (cst_body c) => //.
  - rewrite lookup_env_unbox //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    destruct cstr_as_blocks => //; repeat split; eauto.
    destruct nth_error => /= //.
    destruct nth_error => /= //.
  - rewrite lookup_env_unbox //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_unbox //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    rewrite andb_false_r => //.
    destruct nth_error => /= //.
    destruct EAst.ind_ctors => /= //.
    all:intros; rtoProp; intuition auto; solve_all.
    destruct nth_error => //.
Qed.

Lemma unbox_wellformed_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} d :
  cstr_as_blocks = false ->
  wf_glob Σ ->
  wf_global_decl Σ d -> wf_global_decl (unbox_env Σ) d.
Proof.
  intros hcstrs wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply unbox_wellformed_irrel.
Qed.

Lemma unbox_decl_wf (efl := all_env_flags) {Σ : GlobalContextMap.t} :
  wf_glob Σ ->
  forall d, wf_global_decl Σ d ->
  wf_global_decl (efl := switch_no_params efl) (unbox_env Σ) (unbox_decl Σ d).
Proof.
  intros wf d.
  destruct d => /= //.
  destruct (cst_body c) => /= //.
  now apply (unbox_wellformed (Σ := Σ) 0 t).
Qed.

Lemma fresh_global_unbox_env {Σ : GlobalContextMap.t} kn :
  fresh_global kn Σ ->
  fresh_global kn (unbox_env Σ).
Proof.
  unfold fresh_global. cbn. unfold unbox_env.
  induction (GlobalContextMap.global_decls Σ); cbn; constructor; auto. cbn.
  now depelim H. depelim H. eauto.
Qed.

From MetaRocq.Erasure Require Import EProgram.

Program Fixpoint unbox_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
    on_snd (unbox_decl Σg) hd :: unbox_env' tl (fresh_globals_cons_inv HΣ)
  end.

Lemma lookup_minductive_declared_minductive Σ ind mdecl :
  lookup_minductive Σ ind = Some mdecl <-> declared_minductive Σ ind mdecl.
Proof.
  unfold declared_minductive, lookup_minductive.
  destruct lookup_env => /= //. destruct g => /= //; split => //; congruence.
Qed.

Lemma lookup_minductive_declared_inductive Σ ind mdecl idecl :
  lookup_inductive Σ ind = Some (mdecl, idecl) <-> declared_inductive Σ ind mdecl idecl.
Proof.
  unfold declared_inductive, lookup_inductive.
  rewrite <- lookup_minductive_declared_minductive.
  destruct lookup_minductive => /= //.
  destruct nth_error eqn:hnth => //.
  split. intros [=]. subst. split => //.
  intros [[=] hnth']. subst. congruence.
  split => //. intros [[=] hnth']. congruence.
  split => //. intros [[=] hnth'].
Qed.

Lemma extends_lookup_inductive_pars {efl : EEnvFlags} {Σ Σ'} :
  extends Σ Σ' -> wf_glob Σ' ->
  forall ind t, lookup_inductive_pars Σ ind = Some t ->
    lookup_inductive_pars Σ' ind = Some t.
Proof.
  intros ext wf ind t.
  rewrite /lookup_inductive_pars.
  destruct (lookup_minductive Σ ind) eqn:hl => /= //.
  intros [= <-].
  apply lookup_minductive_declared_minductive in hl.
  eapply EExtends.weakening_env_declared_minductive in hl; tea.
  apply lookup_minductive_declared_minductive in hl. now rewrite hl.
Qed.

Lemma unbox_extends {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' -> wf_glob Σ' ->
  forall n t, wellformed Σ n t -> unbox Σ t = unbox Σ' t.
Proof.
  intros hasapp hext hwf n t. revert n.
  funelim (unbox Σ t); intros ?n; simp_unbox  => /= //.
  all:try solve [intros; unfold wf_fix in *; rtoProp; intuition auto; f_equal; auto; toAll; solve_all].
  - intros; rtoProp; intuition auto.
    move: H1; rewrite wellformed_mkApps // => /andP[] wfu wfargs.
    rewrite unbox_mkApps // Heq /=. f_equal; eauto. toAll; solve_all.
  - rewrite wellformed_mkApps // => /andP[] wfc wfv.
    rewrite unbox_mkApps // /=.
    rewrite GlobalContextMap.lookup_inductive_pars_spec in Heq.
    eapply (extends_lookup_inductive_pars hext hwf) in Heq.
    rewrite Heq. f_equal. f_equal.
    toAll; solve_all.
  - rewrite wellformed_mkApps // => /andP[] wfc wfv.
    rewrite unbox_mkApps // /=.
    move: Heq.
    rewrite GlobalContextMap.lookup_inductive_pars_spec.
    unfold wellformed in wfc. move/andP: wfc => [] /andP[] hacc hc bargs.
    unfold lookup_inductive_pars. destruct lookup_minductive eqn:heq => //.
    unfold lookup_constructor, lookup_inductive in hc. rewrite heq /= // in hc.
Qed.

Lemma unbox_decl_extends {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' -> wf_glob Σ' ->
  forall d, wf_global_decl Σ d -> unbox_decl Σ d = unbox_decl Σ' d.
Proof.
  intros hast ext wf []; cbn.
  unfold unbox_constant_decl.
  destruct (EAst.cst_body c) eqn:hc => /= //.
  intros hwf. f_equal. f_equal. f_equal.
  eapply unbox_extends => //. exact hwf.
  intros _ => //.
Qed.

From MetaRocq.Erasure Require Import EGenericGlobalMap.

#[local]
Instance GT : GenTransform := { gen_transform := unbox; gen_transform_inductive_decl := unbox_inductive_decl }.
#[local]
Instance GTExt efl : has_tApp -> GenTransformExtends efl efl GT.
Proof.
  intros hasapp Σ t n wfΣ Σ' ext wf wf'.
  unfold gen_transform, GT.
  eapply unbox_extends; tea.
Qed.
#[local]
Instance GTWf efl : GenTransformWf efl (switch_no_params efl) GT.
Proof.
  refine {| gen_transform_pre := fun _ _ => has_tApp /\ cstr_as_blocks = false |}; auto.
  - unfold wf_minductive; intros []. cbn. repeat rtoProp. intuition auto.
  - intros Σ n t [? ?] wfΣ wft. unfold gen_transform_env, gen_transform. simpl.
    eapply unbox_wellformed => //.
Defined.

Lemma unbox_extends' {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  List.map (on_snd (unbox_decl Σ)) Σ.(GlobalContextMap.global_decls) =
  List.map (on_snd (unbox_decl Σ')) Σ.(GlobalContextMap.global_decls).
Proof.
  intros hast ext wf.
  now apply (gen_transform_env_extends' (gt := GTExt efl hast) ext).
Qed.

Lemma unbox_extends_env {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (unbox_env Σ) (unbox_env Σ').
Proof.
  intros hast ext wf.
  now apply (gen_transform_extends (gt := GTExt efl hast) ext).
Qed.

Lemma unbox_env_eq (efl := all_env_flags) (Σ : GlobalContextMap.t) : wf_glob Σ -> unbox_env Σ = unbox_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  unfold unbox_env.
  destruct Σ; cbn. cbn in wf.
  induction global_decls in map, repr, wf0, wf |- * => //.
  cbn. f_equal.
  destruct a as [kn d]; unfold on_snd; cbn. f_equal. symmetry.
  eapply unbox_decl_extends => //. cbn. cbn. eapply EExtends.extends_prefix_extends. now exists [(kn, d)]. auto. cbn. now depelim wf.
  set (Σg' := GlobalContextMap.make global_decls (fresh_globals_cons_inv wf0)).
  erewrite <- (IHglobal_decls (GlobalContextMap.map Σg') (GlobalContextMap.repr Σg')).
  2:now depelim wf.
  set (Σg := {| GlobalContextMap.global_decls := _ :: _ |}).
  symmetry. eapply (unbox_extends' (Σ := Σg') (Σ' := Σg)) => //.
  cbn. eapply EExtends.extends_prefix_extends => //. now exists [a].
  cbn. now depelim wf.
Qed.

Lemma unbox_env_wf (efl := all_env_flags) {Σ : GlobalContextMap.t} :
  wf_glob Σ -> wf_glob (efl := switch_no_params efl) (unbox_env Σ).
Proof.
  intros wf.
  rewrite (unbox_env_eq _ wf).
  destruct Σ as [Σ map repr fr]; cbn in *.
  induction Σ in map, repr, fr, wf |- *.
  - cbn. constructor.
  - cbn.
    set (Σg := GlobalContextMap.make Σ (fresh_globals_cons_inv fr)).
    constructor; eauto.
    eapply (IHΣ (GlobalContextMap.map Σg) (GlobalContextMap.repr Σg)). now depelim wf.
    depelim wf. cbn.
    rewrite -(unbox_env_eq Σg). now cbn. cbn.
    now eapply (unbox_decl_wf (Σ:=Σg)).
    rewrite -(unbox_env_eq Σg). now depelim wf.
    eapply fresh_global_unbox_env. now depelim fr.
Qed.

Lemma unbox_program_wf (efl := all_env_flags) (p : eprogram_env) :
  wf_eprogram_env efl p ->
  wf_eprogram (switch_no_params efl) (unbox_program p).
Proof.
  intros []; split => //.
  eapply (unbox_env_wf H).
  now eapply unbox_wellformed.
Qed.

Lemma unbox_expanded {Σ : GlobalContextMap.t} {t} : expanded Σ t -> expanded (unbox_env Σ) (unbox Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[simp_unbox; constructor; eauto; solve_all].
  - rewrite unbox_mkApps_etaexp. now eapply expanded_isEtaExp.
    eapply expanded_mkApps_expanded => //. solve_all.
  - simp_unbox; constructor; eauto. solve_all.
    rewrite -unbox_isLambda //.
  - rewrite unbox_mkApps // /=.
    rewrite (lookup_inductive_pars_spec (proj1 (proj1 H))).
    eapply expanded_tConstruct_app.
    eapply unbox_declared_constructor; tea.
    len. rewrite length_skipn /= /EAst.cstr_arity /=.
    rewrite /EAst.cstr_arity in H0. lia.
    solve_all. eapply All_skipn. solve_all.
Qed.

Lemma unbox_expanded_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded Σ t -> expanded (unbox_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rewrite lookup_env_unbox // /= H //. 1-2:eauto.
  cbn. rewrite /EAst.cstr_arity in H0. lia. solve_all.
Qed.

Lemma unbox_expanded_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl (unbox_env Σ) (unbox_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply unbox_expanded.
Qed.

Lemma unbox_env_expanded (efl := all_env_flags) {Σ : GlobalContextMap.t} :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (unbox_env Σ).
Proof.
  unfold expanded_global_env.
  intros wf. rewrite unbox_env_eq //.
  destruct Σ as [Σ map repr wf']; cbn in *.
  intros exp; induction exp in map, repr, wf', wf |- *; cbn.
  - constructor; auto.
  - set (Σ' := GlobalContextMap.make Σ (fresh_globals_cons_inv wf')).
    constructor; auto.
    eapply IHexp. eapply Σ'. now depelim wf. cbn.
    eapply (unbox_expanded_decl (Σ := Σ')) in H.
    rewrite -(unbox_env_eq Σ'). cbn. now depelim wf.
    exact H.
Qed.

Import EProgram.

Lemma unbox_program_expanded (efl := all_env_flags) (p : eprogram_env) :
  wf_eprogram_env efl p ->
  expanded_eprogram_env_cstrs p ->
  expanded_eprogram_cstrs (unbox_program p).
Proof.
  unfold expanded_eprogram_env_cstrs, expanded_eprogram_cstrs.
  move=> [] wfe wft. move/andP => [] etaenv etap.
  apply/andP; split.
  eapply expanded_global_env_isEtaExp_env, unbox_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  now eapply expanded_isEtaExp, unbox_expanded, isEtaExp_expanded.
Qed.


        tConstruct ind n (map unbox args)
    | tPrim p => tPrim (map_prim unbox p)
    end.

  Lemma unbox_mkApps f l : unbox (mkApps f l) = mkApps (unbox f) (map unbox l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_unbox_repeat_box n : map unbox (repeat tBox n) = repeat tBox n.
  Proof using Type. by rewrite map_repeat. Qed.

  (* move to globalenv *)

  Lemma isLambda_unbox t : isLambda t -> isLambda (unbox t).
  Proof. destruct t => //. Qed.
  Lemma isBox_unbox t : isBox t -> isBox (unbox t).
  Proof. destruct t => //. Qed.

  Lemma wf_unbox t k :
    wf_glob Σ ->
    wellformed Σ k t -> wellformed Σ k (unbox t).
  Proof using Type.
    intros wfΣ.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold wf_fix_gen, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - rtoProp. split; eauto. destruct args; eauto.
    - move/andP: H => [] /andP[] -> clt cll /=.
      rewrite IHt //=. solve_all.
    - rewrite GlobalContextMap.lookup_projection_spec.
      destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl; auto => //.
      simpl.
      have arglen := wellformed_projection_args wfΣ hl.
      apply lookup_projection_lookup_constructor, lookup_constructor_lookup_inductive in hl.
      rewrite hl /= andb_true_r.
      rewrite IHt //=; len. apply Nat.ltb_lt.
      lia.
    - len. rtoProp; solve_all. solve_all.
      now eapply isLambda_unbox. solve_all.
    - len. rtoProp; repeat solve_all.
    - rewrite test_prim_map. rtoProp; intuition eauto; solve_all.
  Qed.

  Lemma unbox_csubst {a k b} n :
    wf_glob Σ ->
    wellformed Σ (k + n) b ->
    unbox (ECSubst.csubst a k b) = ECSubst.csubst (unbox a) k (unbox b).
  Proof using Type.
    intros wfΣ.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros wft; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
    unfold wf_fix, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n0)%nat; auto.
    - f_equal. rtoProp. now destruct args; inv H0.
    - move/andP: wft => [] /andP[] hi hb hl. rewrite IHb. f_equal. unfold on_snd; solve_all.
      repeat toAll. f_equal. solve_all. unfold on_snd; cbn. f_equal.
      rewrite a0 //. now rewrite -Nat.add_assoc.
    - move/andP: wft => [] hp hb.
      rewrite GlobalContextMap.lookup_projection_spec.
      destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => /= //.
      f_equal; eauto. f_equal. len. f_equal.
      have arglen := wellformed_projection_args wfΣ hl.
      case: Nat.compare_spec. lia. lia.
      auto.
    - f_equal. move/andP: wft => [hlam /andP[] hidx hb].
      solve_all. unfold map_def. f_equal.
      eapply a0. now rewrite -Nat.add_assoc.
    - f_equal. move/andP: wft => [hidx hb].
      solve_all. unfold map_def. f_equal.
      eapply a0. now rewrite -Nat.add_assoc.
  Qed.

  Lemma unbox_substl s t :
    wf_glob Σ ->
    forallb (wellformed Σ 0) s ->
    wellformed Σ #|s| t ->
    unbox (substl s t) = substl (map unbox s) (unbox t).
  Proof using Type.
    intros wfΣ. induction s in t |- *; simpl; auto.
    move/andP => [] cla cls wft.
    rewrite IHs //. eapply wellformed_csubst => //.
    f_equal. rewrite (unbox_csubst (S #|s|)) //.
  Qed.

  Lemma unbox_iota_red pars args br :
    wf_glob Σ ->
    forallb (wellformed Σ 0) args ->
    wellformed Σ #|skipn pars args| br.2 ->
    unbox (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map unbox args) (on_snd unbox br).
  Proof using Type.
    intros wfΣ wfa wfbr.
    unfold EGlobalEnv.iota_red.
    rewrite unbox_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite List.length_rev.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma unbox_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def unbox) mfix) = map unbox (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma unbox_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def unbox) mfix) = map unbox (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite length_map.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma unbox_cunfold_fix mfix idx n f :
    wf_glob Σ ->
    wellformed Σ 0 (tFix mfix idx) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def unbox) mfix) idx = Some (n, unbox f).
  Proof using Type.
    intros wfΣ hfix.
    unfold cunfold_fix.
    rewrite nth_error_map.
    cbn in hfix. move/andP: hfix => [] hlam /andP[] hidx hfix.
    destruct nth_error eqn:hnth => //.
    intros [= <- <-] => /=. f_equal.
    rewrite unbox_substl //. eapply wellformed_fix_subst => //.
    rewrite fix_subst_length.
    eapply nth_error_forallb in hfix; tea. now rewrite Nat.add_0_r in hfix.
    now rewrite unbox_fix_subst.
  Qed.

  Lemma unbox_cunfold_cofix mfix idx n f :
    wf_glob Σ ->
    wellformed Σ 0 (tCoFix mfix idx) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def unbox) mfix) idx = Some (n, unbox f).
  Proof using Type.
    intros wfΣ hfix.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    cbn in hfix. move/andP: hfix => [] hidx hfix.
    destruct nth_error eqn:hnth => //.
    intros [= <- <-] => /=. f_equal.
    rewrite unbox_substl //. eapply wellformed_cofix_subst => //.
    rewrite cofix_subst_length.
    eapply nth_error_forallb in hfix; tea. now rewrite Nat.add_0_r in hfix.
    now rewrite unbox_cofix_subst.
  Qed.

End unbox.

Definition unbox_constant_decl Σ cb :=
  {| cst_body := option_map (unbox Σ) cb.(cst_body) |}.

Definition unbox_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (unbox_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl idecl
  end.

Definition unbox_env Σ :=
  map (on_snd (unbox_decl Σ)) Σ.(GlobalContextMap.global_decls).

Import EnvMap.

Program Fixpoint unbox_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in
    on_snd (unbox_decl Σg) hd :: unbox_env' tl (fresh_globals_cons_inv HΣ)
  end.

Import EGlobalEnv EExtends.

Lemma extends_lookup_projection {efl : EEnvFlags} {Σ Σ' p} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_projection Σ p) ->
  lookup_projection Σ p = lookup_projection Σ' p.
Proof.
  intros ext wf; cbn.
  unfold lookup_projection.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  simpl.
  rewrite (extends_lookup_constructor wf ext _ _ _ hl) //.
Qed.

Lemma wellformed_unbox_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  forall n, EWellformed.wellformed Σ n t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  unbox Σ t = unbox Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive
    GlobalContextMap.lookup_projection]; intros => //.
  all:unfold wf_fix_gen in *; rtoProp; intuition auto.
  5:{ destruct cstr_as_blocks; rtoProp. f_equal; eauto; solve_all. destruct args; cbn in *; eauto. }
  all:f_equal; eauto; solve_all.
  - rewrite !GlobalContextMap.lookup_projection_spec.
    rewrite -(extends_lookup_projection H0 H1 H3).
    destruct lookup_projection as [[[[]]]|]. f_equal; eauto.
    now cbn in H3.
Qed.

Lemma wellformed_unbox_decl_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_global_decl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  unbox_decl Σ t = unbox_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold unbox_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_unbox_extends.
Qed.

Lemma lookup_env_unbox_env_Some {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn d :
  wf_glob Σ ->
  GlobalContextMap.lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t,
    [× extends_prefix Σ' Σ, wf_global_decl Σ' d &
      lookup_env (unbox_env Σ) kn = Some (unbox_decl Σ' d)].
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  induction Σ in map, repr, wf |- *; simpl; auto => //.
  intros wfg.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-].
    exists (GlobalContextMap.make Σ (fresh_globals_cons_inv wf)). split.
    now eexists [_].
    cbn. now depelim wfg.
    f_equal. symmetry. eapply wellformed_unbox_decl_extends. cbn. now depelim wfg.
    eapply extends_prefix_extends.
    cbn. now exists [a]. now cbn. now cbn.
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
      symmetry. eapply wellformed_unbox_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      eapply extends_prefix_extends.
      cbn. now exists [a]. now cbn.
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_env_unbox_env_None {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  GlobalContextMap.lookup_env Σ kn = None ->
  lookup_env (unbox_env Σ) kn = None.
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_unbox {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn :
  wf_glob Σ ->
  lookup_env (unbox_env Σ) kn = option_map (unbox_decl Σ) (lookup_env Σ kn).
Proof.
  intros wf.
  rewrite -GlobalContextMap.lookup_env_spec.
  destruct (GlobalContextMap.lookup_env Σ kn) eqn:hl.
  - eapply lookup_env_unbox_env_Some in hl as [Σ' [ext wf' hl']] => /=.
    rewrite hl'. f_equal.
    eapply wellformed_unbox_decl_extends; eauto.
    now eapply extends_prefix_extends. auto.

  - cbn. now eapply lookup_env_unbox_env_None in hl.
Qed.

Lemma is_propositional_unbox {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (unbox_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_unbox (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma lookup_inductive_pars_unbox {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind :
  wf_glob Σ ->
  EGlobalEnv.lookup_inductive_pars Σ ind = EGlobalEnv.lookup_inductive_pars (unbox_env Σ) ind.
Proof.
  rewrite /lookup_inductive_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_unbox ind wf).
  rewrite /GlobalContextMap.lookup_inductive /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma is_propositional_cstr_unbox {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind c :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (unbox_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_unbox (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.
  destruct lookup_env as [[decl|]|] => //.
Qed.


Lemma closed_iota_red pars c args brs br :
  forallb (closedn 0) args ->
  nth_error brs c = Some br ->
  #|skipn pars args| = #|br.1| ->
  closedn #|br.1| br.2 ->
  closed (iota_red pars args br).
Proof.
  intros clargs hnth hskip clbr.
  rewrite /iota_red.
  eapply ECSubst.closed_substl => //.
  now rewrite forallb_rev forallb_skipn.
  now rewrite List.length_rev hskip Nat.add_0_r.
Qed.

Definition disable_prop_cases fl := {| with_prop_case := false; with_guarded_fix := fl.(@with_guarded_fix) ; with_constructor_as_block := false |}.

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma lookup_constructor_unbox {efl : EEnvFlags} {Σ : GlobalContextMap.t} {ind c} :
  wf_glob Σ ->
  lookup_constructor Σ ind c = lookup_constructor (unbox_env Σ) ind c.
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_unbox // /=. destruct lookup_env => // /=.
  destruct g => //.
Qed.

Lemma lookup_projection_unbox {efl : EEnvFlags} {Σ : GlobalContextMap.t} {p} :
  wf_glob Σ ->
  lookup_projection Σ p = lookup_projection (unbox_env Σ) p.
Proof.
  intros wfΣ. rewrite /lookup_projection.
  rewrite -lookup_constructor_unbox //.
Qed.

Lemma constructor_isprop_pars_decl_inductive {Σ ind c} {prop pars cdecl} :
  constructor_isprop_pars_decl Σ ind c = Some (prop, pars, cdecl)  ->
  inductive_isprop_and_pars Σ ind = Some (prop, pars).
Proof.
  rewrite /constructor_isprop_pars_decl /inductive_isprop_and_pars /lookup_constructor.
  destruct lookup_inductive as [[mdecl idecl]|]=> /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_constructor {Σ ind c} {mdecl idecl cdecl} :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  constructor_isprop_pars_decl Σ ind c = Some (ind_propositional idecl, ind_npars mdecl, cdecl).
Proof.
  rewrite /constructor_isprop_pars_decl. intros -> => /= //.
Qed.

Lemma wf_mkApps Σ k f args : reflect (wellformed Σ k f /\ forallb (wellformed Σ k) args) (wellformed Σ k (mkApps f args)).
Proof.
  rewrite wellformed_mkApps //. eapply andP.
Qed.

Lemma substl_closed s t : closed t -> substl s t = t.
Proof.
  induction s in t |- *; cbn => //.
  intros clt. rewrite csubst_closed //. now apply IHs.
Qed.

Lemma substl_rel s k a :
  closed a ->
  nth_error s k = Some a ->
  substl s (tRel k) = a.
Proof.
  intros cla.
  induction s in k |- *.
  - rewrite nth_error_nil //.
  - destruct k => //=.
    * intros [= ->]. rewrite substl_closed //.
    * intros hnth. now apply IHs.
Qed.


Lemma unbox_correct {fl} {wcon : with_constructor_as_block = false} { Σ : GlobalContextMap.t} t v :
  wf_glob Σ ->
  @eval fl Σ t v ->
  wellformed Σ 0 t ->
  @eval fl (unbox_env Σ) (unbox Σ t) (unbox Σ v).
Proof.
  intros wfΣ ev.
  induction ev; simpl in *.

  - move/andP => [] cla clt. econstructor; eauto.
  - move/andP => [] clf cla.
    eapply eval_wellformed in ev2; tea => //.
    eapply eval_wellformed in ev1; tea => //.
    econstructor; eauto.
    rewrite -(unbox_csubst _ 1) //.
    apply IHev3. eapply wellformed_csubst => //.

  - move/andP => [] clb0 clb1.
    intuition auto.
    eapply eval_wellformed in ev1; tea => //.
    forward IHev2 by eapply wellformed_csubst => //.
    econstructor; eauto. rewrite -(unbox_csubst _ 1) //.

  - move/andP => [] /andP[] hl wfd wfbrs. rewrite unbox_mkApps in IHev1.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] wfc' wfargs.
    eapply nth_error_forallb in wfbrs; tea.
    rewrite Nat.add_0_r in wfbrs.
    forward IHev2. eapply wellformed_iota_red; tea => //.
    rewrite unbox_iota_red in IHev2 => //. now rewrite e4.
    econstructor; eauto.
    rewrite -is_propositional_cstr_unbox //. tea.
    rewrite nth_error_map e2 //. len. len.

  - congruence.

  - move/andP => [] /andP[] hl wfd wfbrs.
    forward IHev2. eapply wellformed_substl; tea => //.
    rewrite forallb_repeat //. len.
    rewrite e1 /= Nat.add_0_r in wfbrs. now move/andP: wfbrs.
    rewrite unbox_substl in IHev2 => //.
    rewrite forallb_repeat //. len.
    rewrite e1 /= Nat.add_0_r in wfbrs. now move/andP: wfbrs.
    eapply eval_iota_sing => //; eauto.
    rewrite -is_propositional_unbox //.
    rewrite e1 //. simpl.
    rewrite map_repeat in IHev2 => //.

  - move/andP => [] clf cla. rewrite unbox_mkApps in IHev1.
    simpl in *.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] wff wfargs.
    eapply eval_fix; eauto.
    rewrite length_map.
    eapply unbox_cunfold_fix; tea.
    rewrite unbox_mkApps in IHev3. apply IHev3.
    rewrite wellformed_mkApps // wfargs.
    eapply eval_wellformed in ev2; tas => //. rewrite ev2 /= !andb_true_r.
    eapply wellformed_cunfold_fix; tea.

  - move/andP => [] clf cla.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] clfix clargs.
    eapply eval_wellformed in ev2; tas => //.
    rewrite unbox_mkApps in IHev1 |- *.
    simpl in *. eapply eval_fix_value. auto. auto. auto.
    eapply unbox_cunfold_fix; eauto.
    now rewrite length_map.

  - move/andP => [] clf cla.
    eapply eval_wellformed in ev1 => //.
    eapply eval_wellformed in ev2; tas => //.
    simpl in *. eapply eval_fix'. auto. auto.
    eapply unbox_cunfold_fix; eauto.
    eapply IHev2; tea. eapply IHev3.
    apply/andP; split => //.
    eapply wellformed_cunfold_fix; tea. now cbn.

  - move/andP => [] /andP[] hl cd clbrs. specialize (IHev1 cd).
    eapply eval_wellformed in ev1; tea => //.
    move/wf_mkApps: ev1 => [] wfcof wfargs.
    forward IHev2.
    rewrite hl wellformed_mkApps // /= wfargs clbrs !andb_true_r.
    eapply wellformed_cunfold_cofix; tea => //.
    rewrite !unbox_mkApps /= in IHev1, IHev2.
    eapply eval_cofix_case. tea.
    eapply unbox_cunfold_cofix; tea.
    exact IHev2.

  - move/andP => [] hl hd.
    rewrite GlobalContextMap.lookup_projection_spec in IHev2 |- *.
    destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl' => //.
    eapply eval_wellformed in ev1 => //.
    move/wf_mkApps: ev1 => [] wfcof wfargs.
    forward IHev2.
    { rewrite /= wellformed_mkApps // wfargs andb_true_r.
      eapply wellformed_cunfold_cofix; tea. }
    rewrite unbox_mkApps /= in IHev1.
    eapply eval_cofix_case. eauto.
    eapply unbox_cunfold_cofix; tea.
    rewrite unbox_mkApps in IHev2 => //.

  - rewrite /declared_constant in isdecl.
    move: (lookup_env_unbox c wfΣ).
    rewrite isdecl /= //.
    intros hl.
    econstructor; tea. cbn. rewrite e //.
    apply IHev.
    eapply lookup_env_wellformed in wfΣ; tea.
    move: wfΣ. rewrite /wf_global_decl /= e //.

  - move=> /andP[] iss cld.
    rewrite GlobalContextMap.lookup_projection_spec.
    eapply eval_wellformed in ev1; tea => //.
    move/wf_mkApps: ev1 => [] wfc wfargs.
    destruct lookup_projection as [[[[mdecl idecl] cdecl'] pdecl]|] eqn:hl' => //.
    pose proof (lookup_projection_lookup_constructor hl').
    rewrite (constructor_isprop_pars_decl_constructor H) in e1. noconf e1.
    forward IHev1 by auto.
    forward IHev2. eapply nth_error_forallb in wfargs; tea.
    rewrite unbox_mkApps /= in IHev1.
    eapply eval_iota; tea.
    rewrite /constructor_isprop_pars_decl -lookup_constructor_unbox // H //= //.
    rewrite H0 H1; reflexivity. cbn. reflexivity. len. len.
    rewrite length_skipn. lia.
    unfold iota_red. cbn.
    rewrite (substl_rel _ _ (unbox Σ a)) => //.
    { eapply nth_error_forallb in wfargs; tea.
      eapply wf_unbox in wfargs => //.
      now eapply wellformed_closed in wfargs. }
    pose proof (wellformed_projection_args wfΣ hl'). cbn in H1.
    rewrite nth_error_rev. len. rewrite length_skipn. lia.
    rewrite List.rev_involutive. len. rewrite length_skipn.
    rewrite nth_error_skipn nth_error_map.
    rewrite e2 -H1.
    assert((ind_npars mdecl + cstr_nargs cdecl - ind_npars mdecl) = cstr_nargs cdecl) by lia.
    rewrite H3.
    eapply (f_equal (option_map (unbox Σ))) in e3.
    cbn in e3. rewrite -e3. f_equal. f_equal. lia.

  - congruence.

  - move=> /andP[] iss cld.
    rewrite GlobalContextMap.lookup_projection_spec.
    destruct lookup_projection as [[[[mdecl idecl] cdecl'] pdecl]|] eqn:hl' => //.
    pose proof (lookup_projection_lookup_constructor hl').
    simpl in H.
    move: e0. rewrite /inductive_isprop_and_pars.
    rewrite (lookup_constructor_lookup_inductive H) /=.
    intros [= eq <-].
    eapply eval_iota_sing => //; eauto.
    rewrite -is_propositional_unbox // /inductive_isprop_and_pars
      (lookup_constructor_lookup_inductive H) //=. congruence.
    have lenarg := wellformed_projection_args wfΣ hl'.
    rewrite (substl_rel _ _ tBox) => //.
    { rewrite nth_error_repeat //. len. }
    now constructor.

  - move/andP=> [] clf cla.
    rewrite unbox_mkApps.
    eapply eval_construct; tea.
    rewrite -lookup_constructor_unbox //. exact e0.
    rewrite unbox_mkApps in IHev1. now eapply IHev1.
    now len.
    now eapply IHev2.

  - congruence.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply eval_app_cong; eauto.
    eapply eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * depelim a0.
      + destruct t => //; rewrite unbox_mkApps /=.
      + now rewrite /= !orb_false_r orb_true_r in i.
    * destruct with_guarded_fix.
      + move: i.
        rewrite !negb_or.
        rewrite unbox_mkApps !isFixApp_mkApps !isConstructApp_mkApps !isPrimApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        rewrite !andb_true_r.
        rtoProp; intuition auto;  destruct v => /= //.
      + move: i.
        rewrite !negb_or.
        rewrite unbox_mkApps !isConstructApp_mkApps !isPrimApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        destruct v => /= //.
  - intros; rtoProp; intuition eauto.
    depelim X; repeat constructor.
    eapply All2_over_undep in a.
    eapply All2_Set_All2 in ev. eapply All2_All2_Set. primProp.
    subst a0 a'; cbn in *. depelim H0; cbn in *. intuition auto; solve_all.
    primProp; depelim H0; intuition eauto.
  - destruct t => //.
    all:constructor; eauto.
    cbn [atom unbox] in i |- *.
    rewrite -lookup_constructor_unbox //.
    destruct args; cbn in *; eauto.
Qed.

From MetaRocq.Erasure Require Import EEtaExpanded.

Lemma unbox_expanded {Σ : GlobalContextMap.t} t : expanded Σ t -> expanded Σ (unbox Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?unbox_mkApps.
  - eapply expanded_mkApps_expanded => //. solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars].
    rewrite GlobalContextMap.lookup_projection_spec.
    destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] => /= //.
    2:constructor; eauto; solve_all.
    destruct proj as [[ind npars] arg].
    econstructor; eauto. repeat constructor.
  - cbn. eapply expanded_tFix. solve_all.
    rewrite isLambda_unbox //.
  - eapply expanded_tConstruct_app; tea.
    now len. solve_all.
Qed.

Lemma unbox_expanded_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded Σ t -> expanded (unbox_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rewrite lookup_env_unbox // /= H //. 1-2:eauto. auto. solve_all.
Qed.

Lemma unbox_expanded_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl Σ (unbox_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply unbox_expanded.
Qed.

Lemma unbox_expanded_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded_decl Σ t -> expanded_decl (unbox_env Σ) t.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply unbox_expanded_irrel.
Qed.

Lemma unbox_wellformed_term {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t ->
  EWellformed.wellformed (efl := disable_projections_env_flag efl) Σ n (unbox Σ t).
Proof.
  intros hbox hrel wfΣ.
  induction t in n |- * using EInduction.term_forall_list_ind => //.
  all:try solve [cbn; rtoProp; intuition auto; solve_all].
  - cbn -[lookup_constructor_pars_args]. intros. rtoProp. repeat split; eauto.
    destruct cstr_as_blocks; rtoProp; eauto.
    destruct lookup_constructor_pars_args as [ [] | ]; eauto. split; len.  solve_all. split; eauto.
    solve_all. now destruct args; invs H0.
  - cbn. move/andP => [] /andP[] hast hl wft.
    rewrite GlobalContextMap.lookup_projection_spec.
    destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl'; auto => //.
    simpl.
    rewrite (lookup_constructor_lookup_inductive (lookup_projection_lookup_constructor hl')) /=.
    rewrite hrel IHt //= andb_true_r.
    have hargs' := wellformed_projection_args wfΣ hl'.
    apply Nat.ltb_lt. len.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all. now eapply isLambda_unbox.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all.
  - cbn. rtoProp; intuition eauto; solve_all_k 6.
Qed.

Import EWellformed.

Lemma unbox_wellformed_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_glob Σ ->
  forall n, wellformed (efl := disable_projections_env_flag efl) Σ n t ->
  wellformed (efl := disable_projections_env_flag efl) (unbox_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_unbox //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    repeat (rtoProp; intuition auto).
    destruct has_axioms => //. cbn in *.
    destruct (cst_body c) => //.
  - rewrite lookup_env_unbox //.
    destruct lookup_env eqn:hl => // /=; intros; rtoProp; eauto.
    destruct g eqn:hg => /= //; intros; rtoProp; eauto.
    repeat split; eauto. destruct cstr_as_blocks; rtoProp; repeat split; eauto. solve_all.
  - rewrite lookup_env_unbox //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
Qed.

Lemma unbox_wellformed {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t ->
  EWellformed.wellformed (efl := disable_projections_env_flag efl) (unbox_env Σ) n (unbox Σ t).
Proof.
  intros. apply unbox_wellformed_irrel => //.
  now apply unbox_wellformed_term.
Qed.

From MetaRocq.Erasure Require Import EGenericGlobalMap.

#[local]
Instance GT : GenTransform := { gen_transform := unbox; gen_transform_inductive_decl := id }.
#[local]
Instance GTID : GenTransformId GT.
Proof.
  red. reflexivity.
Qed.
#[local]
Instance GTExt efl : GenTransformExtends efl (disable_projections_env_flag efl) GT.
Proof.
  intros Σ t n wfΣ Σ' ext wf wf'.
  unfold gen_transform, GT.
  eapply wellformed_unbox_extends; tea.
Qed.
#[local]
Instance GTWf efl : GenTransformWf efl (disable_projections_env_flag efl) GT.
Proof.
  refine {| gen_transform_pre := fun _ _ => has_tBox /\ has_tRel |}; auto.
  intros Σ n t [] wfΣ wft.
  now apply unbox_wellformed.
Defined.

Lemma unbox_extends_env {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} :
  has_tApp ->
  extends Σ Σ' ->
  wf_glob Σ ->
  wf_glob Σ' ->
  extends (unbox_env Σ) (unbox_env Σ').
Proof.
  intros hast ext wf.
  now apply (gen_transform_extends (gt := GTExt efl) ext).
Qed.

Lemma unbox_env_eq {efl : EEnvFlags} (Σ : GlobalContextMap.t) : wf_glob Σ -> unbox_env Σ = unbox_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  now apply (gen_transform_env_eq (gt := GTExt efl)).
Qed.

Lemma unbox_env_expanded {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (unbox_env Σ).
Proof.
  unfold expanded_global_env; move=> wfg.
  rewrite unbox_env_eq //.
  destruct Σ as [Σ map repr wf]. cbn in *.
  clear map repr.
  induction 1; cbn; constructor; auto.
  cbn in IHexpanded_global_declarations.
  unshelve eapply IHexpanded_global_declarations. now depelim wfg. cbn.
  set (Σ' := GlobalContextMap.make _ _).
  rewrite -(unbox_env_eq Σ'). cbn. now depelim wfg.
  eapply (unbox_expanded_decl_irrel (Σ := Σ')). now depelim wfg.
  now unshelve eapply (unbox_expanded_decl (Σ:=Σ')).
Qed.

Lemma Pre_glob efl Σ wf :
  has_tBox -> has_tRel -> Pre_glob (GTWF:=GTWf efl) Σ wf.
Proof.
  intros hasb hasr.
  induction Σ => //. destruct a as [kn d]; cbn.
  split => //. destruct d as [[[|]]|] => //=.
Qed.

Lemma unbox_env_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel ->
  wf_glob Σ -> wf_glob (efl := disable_projections_env_flag efl) (unbox_env Σ).
Proof.
  intros hasb hasre wfg.
  eapply (gen_transform_env_wf (gt := GTExt efl)) => //.
  now apply Pre_glob.
Qed.

Definition unbox_program (p : eprogram_env) :=
  (unbox_env p.1, unbox p.1 p.2).

Definition unbox_program_wf {efl : EEnvFlags} (p : eprogram_env) {hastbox : has_tBox} {hastrel : has_tRel} :
  wf_eprogram_env efl p -> wf_eprogram (disable_projections_env_flag efl) (unbox_program p).
Proof.
  intros []; split.
  now eapply unbox_env_wf.
  cbn. now eapply unbox_wellformed.
Qed.

Definition unbox_program_expanded {efl} (p : eprogram_env) :
  wf_eprogram_env efl p ->
  expanded_eprogram_env_cstrs p -> expanded_eprogram_cstrs (unbox_program p).
Proof.
  unfold expanded_eprogram_env_cstrs.
  move=> [wfe wft] /andP[] etae etat.
  apply/andP; split.
  cbn. eapply expanded_global_env_isEtaExp_env, unbox_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  eapply expanded_isEtaExp.
  eapply unbox_expanded_irrel => //.
  now apply unbox_expanded, isEtaExp_expanded.
Qed.
*)