From Stdlib Require Import List String Arith Lia ssreflect ssrbool.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring utils monad_utils.
From MetaRocq.Erasure Require Import EPrimitive EAst EEnvMap EInduction EGlobalEnv.


Import Kernames.
Import MonadNotation.


Fixpoint consts_to_values (t : term) : term :=
  match t with
  | tVar na => tVar na
  | tLambda nm bod => tLambda nm (consts_to_values bod)
  | tLetIn nm dfn bod => 
      tLetIn nm (consts_to_values dfn) (consts_to_values bod)
  | tApp fn arg => 
      tApp (consts_to_values fn) (consts_to_values arg)
  | tConst nm => tForce (tConst nm) 
    (* For now we apply lazy on all constants, wether they already are a value or not *)
  | tConstruct i m args => tConstruct i m (map consts_to_values args)
  | tCase i mch brs =>
      tCase i mch (map (on_snd consts_to_values) brs)
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
  {| cst_body := option_map tLazy cb.(cst_body)|}.

Definition consts_to_values_decl (d : kername * global_decl) : kername * global_decl :=
  match d.2 with
  | ConstantDecl cb => 
      (d.1, ConstantDecl (consts_to_values_constant_decl cb))
  | InductiveDecl idecl => d
  end.

Definition consts_to_values_env Σ : global_context := 
  List.map consts_to_values_decl Σ.

Definition consts_to_values_program (p : program) : program :=
  (consts_to_values_env p.1, consts_to_values p.2).

(* TODO: see to add new types to differentiate, even if equal  *)

From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.



Lemma is_lambda_consts_to_values (d : def term) :
  isLambda (dbody d) -> isLambda (dbody (map_def consts_to_values d)).
Proof.
  by destruct d as [? [] ?].
Qed.

Ltac convert_foralls :=
  repeat match goal with
  | H : All _ _ |- _ => apply All_Forall in H
  | H : context[is_true (forallb _ _)] |- _ =>
      rewrite <-forallb_Forall in H
  | H : context[Forall _ _] |- _ => rewrite Forall_forall in H
  | |- context[forallb _ (map _ _)] => rewrite forallb_map
  | |- context[is_true (forallb _ _)] =>
      rewrite <-forallb_Forall
  | |- context[Forall _ _] => rewrite Forall_forall
  end.

Theorem wf_consts_to_values_same_ctx 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (t : term) (k : nat) (ctx : global_context) :
  has_tLazy_Force ->
  wellformed ctx k t -> 
  wellformed ctx k (consts_to_values t).
Proof.
  induction t using term_forall_list_ind in k |- *; simpl in *; try easy;
  repeat rewrite ->andb_and in *;
  try solve[
    repeat match goal with
    | |- _ -> _ => intro
    | h : _ /\ _ |- _ => destruct h
    | |- _ /\ _ => split
    end; easy
  ].
  - intros ? [? all_wf]. split; first easy.
    now convert_foralls.
  - intros ? [[? ?] all_wf].
     destruct cstr_as_blocks; repeat rewrite ->andb_and in *; simpl in *.
    + repeat split; try easy.
      * rewrite length_map.
        now destruct (lookup_constructor_pars_args ctx i n) 
        as [[]|].
      * destruct all_wf as [? ?].
        now convert_foralls.
    + now destruct args.
  - intros ? (? & (wf_brs_p & wf_t) &  wf_all);
    rewrite length_map; repeat split; try easy.
    now convert_foralls; simpl.
  - intros ? [[? is_lambda_all] wf_fix_m]; repeat split.
    + assumption.
    + convert_foralls.
      auto using is_lambda_consts_to_values. 
    + unfold wf_fix in *.
      rewrite ->andb_and in *.
      destruct wf_fix_m as [? all_wf].
      rewrite length_map; split; first easy.
      unfold test_def in *.
      now convert_foralls; simpl.
  - intros ? [? wf_fix_m]; repeat split; first easy.
    unfold wf_fix in *.
    rewrite ->andb_and in *.
    destruct wf_fix_m as [? all_wf].
    rewrite length_map; split; first easy.
    unfold test_def in *.
    now convert_foralls; simpl.
  - intros ? [? h].
    split.
    + destruct p as [? []]; unfold map_prim; simpl; easy.
    + destruct p as [? []]; unfold map_prim; simpl; [easy..|].
      inversion X as [| | | ? [h1 h2]]; subst.
      unfold test_prim, test_array_model in *; simpl in *.
      rewrite ->andb_and in *.
      now convert_foralls.
Qed.


Lemma lookup_inductive_consts_to_values ctx i :
  lookup_inductive (consts_to_values_env ctx) i = lookup_inductive ctx i.
Proof.
  induction ctx as [|[? [|]] ? ?]; simpl; first easy;
  unfold lookup_inductive, lookup_minductive; simpl;
  repeat (
    match goal with
    | H : context[if ?p then _ else _] |- _ =>
        let hp := fresh "h" in
        destruct p eqn:hp
    | |- context[if ?p then _ else _] =>
        let hp := fresh "h" in
        destruct p eqn:hp
    | H : context[if ?p then _ else _] |- _ =>
        let hp := fresh "h" in
        destruct p eqn:hp
    | H : context[match ?p with _ => _ end] |- _ =>
        let hp := fresh "h" in
        destruct p eqn:hp
    | |- context[match ?p with _ => _ end] =>
        let hp := fresh "h" in
        destruct p eqn:hp
    end; try easy
  ).
Qed.

Lemma lookup_constructor_consts_to_values ctx i n :
  lookup_constructor (consts_to_values_env ctx) i n = lookup_constructor ctx i n.
Proof.
  rewrite
    /consts_to_values_decl
    /lookup_constructor
    lookup_inductive_consts_to_values //.
Qed.

Lemma lookup_constructor_pars_args_consts_to_values ctx i n :
  lookup_constructor_pars_args (consts_to_values_env ctx) i n = lookup_constructor_pars_args ctx i n.
Proof.
  rewrite 
    /lookup_constructor_pars_args
    lookup_constructor_consts_to_values //.
Qed.

Lemma wf_brs_consts_to_values ctx i n :
  wf_brs (consts_to_values_env ctx) i n = wf_brs ctx i n.
Proof.
  rewrite 
    /wf_brs
    lookup_inductive_consts_to_values //.
Qed.

Lemma lookup_projection_consts_to_values ctx i :
  lookup_projection (consts_to_values_env ctx) i = lookup_projection ctx i.
Proof.
  rewrite /lookup_projection lookup_constructor_consts_to_values //.
Qed.

Lemma lookup_constant_consts_to_values ctx s :
  lookup_constant (consts_to_values_env ctx) s = 
  option_map consts_to_values_constant_decl (lookup_constant ctx s).
Proof.
  induction ctx as [|[name [|]]? ?]; first easy; simpl.
  - rewrite /lookup_constant /=.
    now destruct (s == name).
  - rewrite /lookup_constant /=.
    now destruct (s == name).
Qed.



Theorem wf_consts_to_values_env_map_ctx 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (t : term) (k : nat) (ctx : global_context) :
  has_tLazy_Force ->
  wellformed ctx k t -> 
  wellformed (consts_to_values_env ctx) k t.
Proof.
  induction t using term_forall_list_ind in k |- *; simpl in *; try easy;
  repeat rewrite ->andb_and in *;
  try solve[
    repeat match goal with
    | |- _ -> _ => intro
    | h : _ /\ _ |- _ => destruct h
    | |- _ /\ _ => split
    end; easy
  ].
  - intros ? [? all_wf]. split; first easy.
    now convert_foralls.
  - intros ? [? ?]; split; first easy.
    rewrite lookup_constant_consts_to_values.
    now destruct (lookup_constant ctx s) as [[[|]]|].
  - intros ? [[? ?] all_wf].
     destruct cstr_as_blocks; repeat rewrite ->andb_and in *; simpl in *.
    + repeat split. 
      * assumption.
      * now rewrite lookup_constructor_consts_to_values.
      * now rewrite lookup_constructor_pars_args_consts_to_values.
      * destruct all_wf as [? ?].
        now convert_foralls.
    + rewrite lookup_constructor_consts_to_values.
      now destruct args.
  - intros ? (? & (wf_brs_p & wf_t) &  wf_all); 
    repeat split; try easy.
    + now rewrite wf_brs_consts_to_values.
    + now convert_foralls; simpl.
  - rewrite lookup_projection_consts_to_values.
    now intros ? [[? ?] wf_t]; repeat split.
  - intros ? [[? is_lambda_all] wf_fix_m]; 
    repeat split; try assumption.
    unfold wf_fix in *.
    rewrite ->andb_and in *.
    destruct wf_fix_m as [? all_wf].
    split; first easy.
    unfold test_def in *.
    now convert_foralls; simpl.
  - intros ? [? wf_fix_m]; repeat split; first easy.
    unfold wf_fix in *.
    rewrite ->andb_and in *.
    destruct wf_fix_m as [? all_wf].
    split; first easy.
    unfold test_def in *.
    now convert_foralls; simpl.
  - intros ? [? h].
    split.
    + destruct p as [? []]; unfold map_prim; simpl; easy.
    + destruct p as [? []]; unfold map_prim; simpl; [easy..|].
      inversion X as [| | | ? [h1 h2]]; subst.
      unfold test_prim, test_array_model in *; simpl in *.
      rewrite ->andb_and in *.
      now convert_foralls.
Qed.


Lemma fresh_consts_to_values name ctx :
  fresh_global name (consts_to_values_env ctx) <-> fresh_global name ctx.
Proof.
  unfold fresh_global.
  split; 
    [intros H%Forall_map_inv | intros H; apply Forall_map];
    convert_foralls;
    now intros [? [|]]; simpl.
Qed.

Theorem wf_glob_consts_to_values
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (ctx : global_context) :
  has_tLazy_Force ->
  wf_glob ctx ->
  wf_glob (consts_to_values_env ctx).
Proof.
  induction ctx as [|[? [[[|]]|?]] ? ?];
  inversion 2; subst; constructor; now rewrite /= ?wf_consts_to_values_env_map_ctx ?fresh_consts_to_values.
Qed.    

Theorem wf_consts_to_values 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (input : Transform.program _ term) :
  has_tLazy_Force ->
  wf_eprogram efl input ->
  wf_eprogram efl (consts_to_values_program input).
Proof.
  destruct input as [ctx t].
  intros ? [wf_ctx wf_t].
  split; simpl in *.
  - now apply wf_glob_consts_to_values.
  - now apply 
      wf_consts_to_values_same_ctx,
      wf_consts_to_values_env_map_ctx.
Qed.

