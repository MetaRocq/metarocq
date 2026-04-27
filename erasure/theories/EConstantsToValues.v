From Stdlib Require Import List String Arith Lia ssreflect ssrbool.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring utils monad_utils.
From MetaRocq.Erasure Require Import EPrimitive EAst EEnvMap EInduction EGlobalEnv.

#[local] Set Default Goal Selector "!".
Import Kernames.
Import MonadNotation.

(** We transform a program by transforming each constant into a value by thunking them, and forcing their evaluation when needed *)
(* 
  TODO:
  Thunk only when the constant is not already a value
*)
Fixpoint consts_to_values (t : term) : term :=
  match t with
  | tVar na => tVar na
  | tLambda nm bod => tLambda nm (consts_to_values bod)
  | tLetIn nm dfn bod => 
      tLetIn nm (consts_to_values dfn) (consts_to_values bod)
  | tApp fn arg => 
      tApp (consts_to_values fn) (consts_to_values arg)
  | tConst nm => tForce (tConst nm) 
  | tConstruct i m args => tConstruct i m (map consts_to_values args)
  | tCase i mch brs =>
      tCase i (consts_to_values mch) (map (on_snd consts_to_values) brs)
  | tFix mfix idx => 
      tFix (map (map_def consts_to_values) mfix) idx
  | tCoFix mfix idx => 
      tCoFix (map (map_def consts_to_values) mfix) idx
  | tProj p bod => tProj p (consts_to_values bod)
  | tPrim p => tPrim (map_prim consts_to_values p)
  | tLazy t => tLazy (consts_to_values t)
  | tForce t => tForce (consts_to_values t)
  | tRel n => tRel n
  | tBox => tBox
  | tEvar ev args => tEvar ev (map consts_to_values args)
  end
.

Definition consts_to_values_constant_decl (cb : constant_body) : constant_body := 
  {| cst_body := option_map (tLazy ∘ consts_to_values) cb.(cst_body)|}.


Definition consts_to_values_global_decl (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cb => 
      ConstantDecl (consts_to_values_constant_decl cb)
  | InductiveDecl idecl => d
  end.
Definition consts_to_values_decl (d : kername * global_decl) : kername * global_decl := on_snd consts_to_values_global_decl d.


Definition consts_to_values_env Σ : global_context := 
  List.map consts_to_values_decl Σ.


Definition consts_to_values_program (p : program) : program :=
  (consts_to_values_env p.1, consts_to_values p.2).


From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.


Create HintDb consts_to_values_rw_hints.
Ltac simple := repeat (
    assumption ||
    match goal with
    | |- All _ _ => apply Forall_All 
    | H : All _ _ |- _ => apply All_Forall in H
    | h : ?e = Some _ |- _ =>
          rewrite ->h in *
    end ||
    autorewrite with consts_to_values_rw_hints in * || 
    simpl in *
  ).

Hint Rewrite @Forall_All : consts_to_values_rw_hints.
Hint Rewrite <-@forallb_Forall : consts_to_values_rw_hints.
Hint Rewrite <-@forallb_Forall : consts_to_values_rw_hints.
Hint Rewrite Forall_forall : consts_to_values_rw_hints.
Hint Rewrite @forallb_map : consts_to_values_rw_hints.
Hint Rewrite andb_and : consts_to_values_rw_hints.
Hint Rewrite length_map : consts_to_values_rw_hints.
Hint Rewrite length_map : consts_to_values_rw_hints.
Hint Rewrite <- @map_skipn : consts_to_values_rw_hints.
Hint Rewrite @nth_error_map : consts_to_values_rw_hints.
Hint Rewrite @map_repeat : consts_to_values_rw_hints.
Hint Rewrite andb_and : consts_to_values_rw_hints.
Hint Rewrite repeat_length : consts_to_values_rw_hints.


Lemma is_nil_map {A B} (f : A -> B) l :
  is_nil (map f l) = is_nil l.
Proof.
  now destruct l.
Qed.
Hint Rewrite @is_nil_map : consts_to_values_rw_hints.


Lemma isLambda_consts_to_values (d : def term) :
  isLambda (consts_to_values (dbody d)) = isLambda (dbody d).
Proof.
  by destruct d as [? [] ?].
Qed.
Hint Rewrite @isLambda_consts_to_values : consts_to_values_rw_hints.

Lemma lookup_env_consts_to_values ctx name :
  lookup_env (consts_to_values_env ctx) name = option_map (consts_to_values_global_decl) (lookup_env ctx name).
Proof.
  induction ctx as [|[? [|]] ? ?]; simpl; first easy;
  repeat (
    match goal with
    | H : context[if ?p then _ else _] |- _ =>
        destruct p eqn:?
    | |- context[if ?p then _ else _] =>
        destruct p eqn:?
    | H : context[if ?p then _ else _] |- _ =>
        destruct p eqn:?
    | H : context[match ?p with _ => _ end] |- _ =>
        destruct p eqn:?
    | |- context[match ?p with _ => _ end] =>
        destruct p eqn:?
    end; easy
  ).
Qed.
Hint Rewrite lookup_env_consts_to_values : consts_to_values_rw_hints.


Lemma lookup_inductive_consts_to_values ctx i :
  lookup_inductive (consts_to_values_env ctx) i = lookup_inductive ctx i.
Proof. 
  unfold lookup_inductive, lookup_minductive; simple.
  destruct (lookup_env ctx (inductive_mind i)) as [[? | ?]|]; reflexivity.
Qed.
Hint Rewrite lookup_inductive_consts_to_values : consts_to_values_rw_hints.


Lemma lookup_constructor_consts_to_values ctx i n :
  lookup_constructor (consts_to_values_env ctx) i n = lookup_constructor ctx i n.
Proof.
  unfold consts_to_values_decl, lookup_constructor.
  now simple.
Qed.
Hint Rewrite lookup_constructor_consts_to_values : consts_to_values_rw_hints.


Lemma lookup_constructor_pars_args_consts_to_values ctx i n :
  lookup_constructor_pars_args (consts_to_values_env ctx) i n = lookup_constructor_pars_args ctx i n.
Proof.
  unfold lookup_constructor_pars_args.
  now simple.
Qed.
Hint Rewrite lookup_constructor_pars_args_consts_to_values : consts_to_values_rw_hints.


Lemma wf_brs_consts_to_values ctx i n :
  wf_brs (consts_to_values_env ctx) i n = wf_brs ctx i n.
Proof.
  unfold wf_brs.
  now simple.
Qed.
Hint Rewrite wf_brs_consts_to_values : consts_to_values_rw_hints.


Lemma lookup_projection_consts_to_values ctx i :
  lookup_projection (consts_to_values_env ctx) i = lookup_projection ctx i.
Proof.
  unfold lookup_projection.
  now simple.
Qed.
Hint Rewrite lookup_projection_consts_to_values : consts_to_values_rw_hints.


Lemma lookup_constant_consts_to_values ctx s :
  lookup_constant (consts_to_values_env ctx) s = 
  option_map consts_to_values_constant_decl (lookup_constant ctx s).
Proof.
  unfold lookup_constant.
  simple.
  now destruct (lookup_env ctx s) as [[]|].
Qed.
Hint Rewrite lookup_constant_consts_to_values : consts_to_values_rw_hints.


Lemma fresh_consts_to_values name ctx :
  fresh_global name (consts_to_values_env ctx) <-> fresh_global name ctx.
Proof.
  split; 
    [intros H%Forall_map_inv | intros H; apply Forall_map];
    simple.
Qed.
Hint Rewrite fresh_consts_to_values : consts_to_values_rw_hints.


Lemma consts_to_values_atom (wfl : WcbvFlags) ctx e :
  atom (consts_to_values_env ctx) (consts_to_values e) = atom ctx e.
Proof.
  destruct e; try (discriminate || easy); simpl.
  destruct args; simpl; last easy.
  now simple.
Qed.
Hint Rewrite -> consts_to_values_atom : consts_to_values_rw_hints.


Lemma consts_to_values_mkApps (e : term) (args : list term) :
  consts_to_values (mkApps e args) = mkApps (consts_to_values e) (map consts_to_values args).
Proof.
  now induction args in e |- *.
Qed.
Hint Rewrite consts_to_values_mkApps : consts_to_values_rw_hints.


Lemma consts_to_values_csubst e1 n e2 :
  consts_to_values (ECSubst.csubst e1 n e2) =
  ECSubst.csubst (consts_to_values e1) n (consts_to_values e2).
Proof.
  induction e2 using term_forall_list_ind in n, e1 |- *; simple; try easy.
  - destruct (n ?= n0); reflexivity.
  - f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    now simple.
  - f_equal.  
    rewrite !map_map_compose.
    apply All_map_eq.
    now simple.
  - f_equal; try easy.
    rewrite !map_map_compose.
    apply All_map_eq.
    simple.
    intros [names t] hIn; unfold on_snd; simpl in *.
    now rewrite (X (names, t)).
  - f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    simple.
    intros [dname body rarg] hIn; unfold map_def; simpl in *.
    now rewrite (X _ hIn).
  - f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    simple.
    intros [dname body rarg] hIn.
    now rewrite /map_def (X _ hIn).
  - f_equal.
    inversion X as [| | | ? [heq eq_All]]; subst; try reflexivity.
    rewrite /map_prim /= /map_array_model /= heq.
    do 3 f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    now simple.
Qed.
Hint Rewrite consts_to_values_csubst : consts_to_values_rw_hints.


Lemma consts_to_values_substl l e :
  consts_to_values (ECSubst.substl l e) =
  ECSubst.substl (map consts_to_values l) (consts_to_values e).
Proof.
  unfold ECSubst.substl.
  induction l as [| ? ? IH] 
    using list_ind_rev; simpl; first reflexivity.
  rewrite map_app !fold_left_app.
  now simple.
Qed. 
Hint Rewrite consts_to_values_substl : consts_to_values_rw_hints.


Lemma map_fix_subst mfix :
  map consts_to_values (fix_subst mfix) = fix_subst (map (map_def consts_to_values) mfix).
Proof.
  unfold fix_subst.
  induction mfix as [|? ? IH] at 2 4; first reflexivity.
  now simple.
Qed.
Hint Rewrite map_fix_subst : consts_to_values_rw_hints.


Lemma consts_to_values_cunfold_fix mfix idx :
  cunfold_fix (map (map_def consts_to_values) mfix) idx =
  option_map (on_snd consts_to_values) (cunfold_fix mfix idx).
Proof.
  unfold cunfold_fix; simple.
  now destruct (nth_error mfix idx); unfold on_snd; simple.
Qed.
Hint Rewrite consts_to_values_cunfold_fix : consts_to_values_rw_hints.


Lemma map_cofix_subst mfix :
  map consts_to_values (cofix_subst mfix) = cofix_subst (map (map_def consts_to_values) mfix).
Proof.
  unfold cofix_subst.
  induction mfix as [|? ? IH] at 2 4; first reflexivity.
  now simple.
Qed.
Hint Rewrite map_cofix_subst : consts_to_values_rw_hints.


Lemma consts_to_values_cunfold_cofix mfix idx :
  cunfold_cofix (map (map_def consts_to_values) mfix) idx =
  option_map (on_snd consts_to_values) (cunfold_cofix mfix idx).
Proof.
  unfold cunfold_cofix; simple.
  now destruct (nth_error mfix idx); unfold on_snd; simple.
Qed.
Hint Rewrite consts_to_values_cunfold_cofix : consts_to_values_rw_hints.


Lemma consts_to_values_ind_isprop_and_pars ctx ind :
  inductive_isprop_and_pars (consts_to_values_env ctx) ind =
  inductive_isprop_and_pars ctx ind.
Proof.
  unfold inductive_isprop_and_pars.
  now simple.
Qed.
Hint Rewrite consts_to_values_ind_isprop_and_pars : consts_to_values_rw_hints.

Lemma consts_to_values_constr_isprop_pars_decl ctx ind n :
  constructor_isprop_pars_decl (consts_to_values_env ctx) ind n =
  constructor_isprop_pars_decl ctx ind n.
Proof.
  unfold constructor_isprop_pars_decl.
  now simple. 
Qed.  
Hint Rewrite consts_to_values_constr_isprop_pars_decl : consts_to_values_rw_hints.



Lemma consts_to_values_declared_constant ctx c decl :
  declared_constant ctx c decl ->
  declared_constant (consts_to_values_env ctx) c (consts_to_values_constant_decl decl).
Proof.
  unfold declared_constant. simple.
  now intros ->.
Qed.

Lemma consts_to_values_cst_body  decl :
  cst_body (consts_to_values_constant_decl decl) = option_map (tLazy ∘ consts_to_values) (cst_body decl). 
Proof.
  reflexivity.
Qed.
Hint Rewrite consts_to_values_cst_body : consts_to_values_rw_hints.


Lemma consts_to_values_head e :
  EAstUtils.head (consts_to_values e) = consts_to_values (EAstUtils.head e).
Proof.
  now induction e; simpl; rewrite ?EAstUtils.head_tApp.
Qed.  
Hint Rewrite consts_to_values_head : consts_to_values_rw_hints.

Lemma consts_to_values_isLambda e : 
  isLambda (consts_to_values e) = isLambda e.
Proof.
  now destruct e.
Qed.
Hint Rewrite consts_to_values_isLambda : consts_to_values_rw_hints.

Lemma consts_to_values_isFixApp e : EAstUtils.isFixApp (consts_to_values e) = EAstUtils.isFixApp e.
Proof.
  unfold EAstUtils.isFixApp; simple.
  now destruct (EAstUtils.head e).
Qed.
Hint Rewrite consts_to_values_isFixApp : consts_to_values_rw_hints.

Lemma consts_to_values_isFix e : 
  EAstUtils.isFix (consts_to_values e) = EAstUtils.isFix e.
Proof.
  now destruct e.
Qed.
Hint Rewrite consts_to_values_isFix : consts_to_values_rw_hints.

Lemma consts_to_values_isBox e : EAstUtils.isBox (consts_to_values e) = EAstUtils.isBox e.
Proof.
  now destruct e.
Qed.
Hint Rewrite consts_to_values_isBox : consts_to_values_rw_hints.

Lemma consts_to_values_isConstructApp e :
  EAstUtils.isConstructApp (consts_to_values e) = EAstUtils.isConstructApp e.
Proof.
  unfold EAstUtils.isConstructApp; simple.
  now destruct (EAstUtils.head e).
Qed.
Hint Rewrite consts_to_values_isConstructApp : consts_to_values_rw_hints.

Lemma consts_to_values_isPrimApp e : EAstUtils.isPrimApp (consts_to_values e) = EAstUtils.isPrimApp e.
Proof.
  unfold EAstUtils.isPrimApp; simple.
  now destruct (EAstUtils.head e).
Qed.
Hint Rewrite consts_to_values_isPrimApp : consts_to_values_rw_hints.

Lemma consts_to_values_isLazyApp e : EAstUtils.isLazyApp (consts_to_values e) = EAstUtils.isLazyApp e.
Proof.
  unfold EAstUtils.isLazyApp; simple.
  now destruct (EAstUtils.head e).
Qed.
Hint Rewrite consts_to_values_isLazyApp : consts_to_values_rw_hints.

Lemma consts_to_values_iota pars args br :
  consts_to_values (iota_red pars args br) = 
  iota_red 
    pars 
    (map consts_to_values args) 
    (on_snd consts_to_values br).
Proof.
  unfold iota_red. simple.
  now rewrite map_rev.
Qed.
Hint Rewrite consts_to_values_iota : consts_to_values_rw_hints.


Lemma wf_consts_to_values_same_ctx 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (t : term) (k : nat) (ctx : global_context) :
  has_tLazy_Force ->
  wellformed ctx k t -> 
  wellformed ctx k (consts_to_values t).
Proof.
  induction t using term_forall_list_ind in k |- *;
  simple; unfold wf_fix, test_def, map_prim, test_prim, test_array_model in *;
  repeat split; intros; simple; try easy.
  - now destruct cstr_as_blocks; simple.
  - now inversion X; subst.
  - now inversion X as [| | | ? [? ?]]; subst; simple.
Qed.


Lemma wf_consts_to_values_env_map_ctx 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (t : term) (k : nat) (ctx : global_context) :
  has_tLazy_Force ->
  wellformed ctx k t -> 
  wellformed (consts_to_values_env ctx) k t.
Proof.
  induction t using term_forall_list_ind in k |- *; simple;
  unfold wf_fix, test_def, map_prim, test_prim, test_array_model 
  in *; repeat split; intros; simple; try easy.
  - now destruct (lookup_constant ctx s) as [[[|]]|].
  - now destruct cstr_as_blocks; simple.
  - inversion X as [| | | ? [? ?]]; subst; now simple.
Qed.


Lemma wf_glob_consts_to_values
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (ctx : global_context) :
  has_tLazy_Force ->
  wf_glob ctx ->
  wf_glob (consts_to_values_env ctx).
Proof.
  induction ctx as [|[? [[[|]]|?]] ? ?];
  inversion 2; subst; constructor; now rewrite /= ?wf_consts_to_values_env_map_ctx ?wf_consts_to_values_same_ctx ?fresh_consts_to_values.
Qed.

Theorem wf_consts_to_values
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (input : eprogram) :
  has_tLazy_Force ->
  wf_eprogram efl input ->
  wf_eprogram efl (consts_to_values_program input).
Proof.
  destruct input as [ctx t].
  intros ? [wf_ctx wf_t].
  pose proof wf_glob_consts_to_values.
  pose proof wf_consts_to_values_same_ctx.
  pose proof wf_consts_to_values_env_map_ctx.
  unfold wf_eprogram; simple.
  easy.
Qed.

#[local] Ltac destruct_IHs :=
    repeat match goal with 
    | IH : _ -> 
      eval (consts_to_values_env _) _ _
        |- _ =>
        unshelve epose proof IH _; first try easy;
        clear IH
    end
    ; [
      try solve[
        repeat (
          simpl in * || easy || simple ||  intros ||
          lazymatch goal with
          | hdec : declared_constant _ ?c _ |- _ =>
              unfold lookup_constant, declared_constant in *;
              apply lookup_env_wellformed in hdec as ?
          | heq: ?a = _, 
                h: context[match ?a with _ => _ end] |- _ =>
                  rewrite heq in h
          | h: In _ (repeat _ _) |- _ =>
                apply repeat_spec in h; subst
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
Ltac crush := solve[
    simple; econstructor; try now simple
  ].

Theorem consts_to_values_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : eprogram)
  (v : term),
  has_tApp -> (* Needed for eval_wellformed *)
  has_tBox || ~~ with_prop_case -> (* Needed for wellformedness in the case eval_iota_sing *)
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  let ip := consts_to_values_program p in
  eval_eprogram wfl ip (consts_to_values v).
Proof.
  intros ? ? [ctx e] ? ? htBox [wf_ctx wf_e] [eval_e]; simpl in *.
  constructor; simpl.
  induction eval_e; simpl in *; subst.
  all: destruct_IHs. (* Takes a bit of time, proves the premises of most of the induction hypotheses  *)
  all: try crush.  (* Solves automatically most of the goals *)
  - eapply eval_force; try now simple.
    econstructor.
    + now apply consts_to_values_declared_constant.
    + now simple.
    + do 2 constructor.
  - simple.
    eapply eval_construct_block; try now simple.
    destruct cstr_as_blocks; last first.
    { destruct args; last easy.
      inversion a; subst.
      constructor. }
    rewrite /lookup_constructor_pars_args e0 /= in wf_e.
    destruct wf_e as [[? ?] [? ?]%andb_andI].
    apply All2_All2_Set, All2_map.
    apply All2_over_undep in iha.
    unshelve eapply (All2_apply_dep_arrow _ iha).
    now simple.
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
Qed.



Lemma consts_to_values_extends ctx ctx' :
  extends ctx ctx' ->
  extends (consts_to_values_env ctx) (consts_to_values_env ctx').
Proof.
  intros h_extends name decl heq.
  simple.
  apply option_map_Some in heq as [decl' [heq%h_extends ?]]; subst.
  now simple.
Qed.




Theorem consts_to_values_env_values {wfl : WcbvFlags} (Σ : global_context) :
  values_glob (consts_to_values_env Σ).
Proof.
  induction Σ as [|[kn [[[v|]]|?]] Σ IH]; simpl; 
    repeat constructor; assumption.
Qed.