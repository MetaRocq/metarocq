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
  {| cst_body := option_map tLazy (option_map consts_to_values cb.(cst_body))|}.


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

(* TODO: see to add new types to differentiate, even if equal  *)

From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.



Lemma isLambda_consts_to_values (d : def term) :
  isLambda (dbody d) -> isLambda (dbody (map_def consts_to_values d)).
Proof.
  by destruct d as [? [] ?].
Qed.

Ltac convert_foralls :=
  repeat match goal with
  | |- All _ _ => apply Forall_All 
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
  - intros ? [[? isLambda_all] wf_fix_m]; repeat split.
    + assumption.
    + convert_foralls.
      auto using isLambda_consts_to_values. 
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
    + inversion X as [| | | ? [h1 h2]]; subst; try easy.
      unfold test_prim, test_array_model in *; simpl in *.
      rewrite ->andb_and in *.
      now convert_foralls.
Qed.

Lemma lookup_env_consts_to_values ctx name :
  lookup_env (consts_to_values_env ctx) name = option_map (consts_to_values_global_decl) (lookup_env ctx name).
Proof.
  induction ctx as [|[? [|]] ? ?]; simpl; first easy;
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


Lemma lookup_inductive_consts_to_values ctx i :
  lookup_inductive (consts_to_values_env ctx) i = lookup_inductive ctx i.
Proof. 
  unfold lookup_inductive, lookup_minductive; simpl.
  rewrite lookup_env_consts_to_values.
  destruct (lookup_env ctx (inductive_mind i)) as [[? | ibody]|]; simpl; reflexivity.
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
  - intros ? [[? isLambda_all] wf_fix_m]; 
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
  inversion 2; subst; constructor; now rewrite /= ?wf_consts_to_values_env_map_ctx ?wf_consts_to_values_same_ctx ?fresh_consts_to_values.
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


Lemma consts_to_values_atom (wfl : WcbvFlags) ctx e :
  atom (consts_to_values_env ctx) (consts_to_values e) = atom ctx e.
Proof.
  destruct e; try (discriminate || easy); simpl.
  destruct args; simpl; last easy.
  now rewrite lookup_constructor_consts_to_values.
Qed.

Lemma consts_to_values_mkApps (e : term) (args : list term) :
  consts_to_values (mkApps e args) = mkApps (consts_to_values e) (map consts_to_values args).
Proof.
  induction args as [| ? ? IH] in e |- *; first reflexivity.
  rewrite /= IH //.
Qed.

Lemma mkApps_snoc e args a :
  tApp (mkApps e args) a = mkApps e (args ++ [a]).
Proof.
  induction args in e |- *; easy.
Qed.


Lemma consts_to_values_csubst e1 n e2 :
  consts_to_values (ECSubst.csubst e1 n e2) =
  ECSubst.csubst (consts_to_values e1) n (consts_to_values e2).
Proof.
  induction e2 using term_forall_list_ind in n, e1 |- *; simpl; try (reflexivity || now f_equal).
  - destruct (n ?= n0); reflexivity.
  - f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    now convert_foralls.
  - f_equal.  
    rewrite !map_map_compose.
    apply All_map_eq.
    now convert_foralls.
  - f_equal; try easy.
    rewrite !map_map_compose.
    apply All_map_eq.
    convert_foralls.
    intros [names t] hIn; unfold on_snd; simpl in *.
    now rewrite (X (names, t)).
  - f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    convert_foralls.
    intros [dname body rarg] hIn; unfold map_def; simpl in *.
    now rewrite length_map (X _ hIn).
  - f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    convert_foralls.
    intros [dname body rarg] hIn; unfold map_def; simpl in *.
    now rewrite length_map (X _ hIn).
  - f_equal.
    inversion X as [| | | ? [heq eq_All]]; subst; try reflexivity.
    rewrite /map_prim /= /map_array_model /= heq.
    do 3 f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    now convert_foralls.
Qed.

Lemma consts_to_values_substl l e :
  consts_to_values (ECSubst.substl l e) =
  ECSubst.substl (map consts_to_values l) (consts_to_values e).
Proof.
  induction l as [| ? ? IH] 
    using list_ind_rev; simpl; first reflexivity.
  rewrite /ECSubst.substl map_app !fold_left_app.
  fold (ECSubst.substl l e); simpl.
  fold (ECSubst.substl (map consts_to_values l) (consts_to_values e)); simpl.
  now rewrite consts_to_values_csubst IH.
Qed. 

Lemma map_fix_subst mfix :
  map consts_to_values (fix_subst mfix) = fix_subst (map (map_def consts_to_values) mfix).
Proof.
  unfold fix_subst.
  rewrite length_map.
  remember #|mfix| as n eqn:heq.
  clear heq.
  induction n as [|? IH]; first reflexivity.
  rewrite map_cons /=; f_equal.
  now rewrite IH.
Qed.

Lemma consts_to_values_cunfold_fix mfix idx :
  cunfold_fix (map (map_def consts_to_values) mfix) idx =
  option_map (on_snd consts_to_values) (cunfold_fix mfix idx).
Proof.
  unfold cunfold_fix.
  rewrite nth_error_map.
  destruct (nth_error mfix idx); unfold on_snd; simpl; last reflexivity.
  now rewrite consts_to_values_substl map_fix_subst.
Qed.

Lemma map_cofix_subst mfix :
  map consts_to_values (cofix_subst mfix) = cofix_subst (map (map_def consts_to_values) mfix).
Proof.
  unfold cofix_subst.
  rewrite length_map.
  remember #|mfix| as n eqn:heq.
  clear heq.
  induction n as [|? IH]; first reflexivity.
  rewrite map_cons /=; f_equal.
  now rewrite IH.
Qed.

Lemma consts_to_values_cunfold_cofix mfix idx :
  cunfold_cofix (map (map_def consts_to_values) mfix) idx =
  option_map (on_snd consts_to_values) (cunfold_cofix mfix idx).
Proof.
  unfold cunfold_cofix.
  rewrite nth_error_map.
  destruct (nth_error mfix idx); unfold on_snd; simpl; last reflexivity.
  now rewrite consts_to_values_substl map_cofix_subst.
Qed.




Lemma consts_to_values_ind_isprop_and_pars ctx ind :
  inductive_isprop_and_pars (consts_to_values_env ctx) ind =
  inductive_isprop_and_pars ctx ind.
Proof.
  rewrite
    /inductive_isprop_and_pars 
    lookup_inductive_consts_to_values //.
Qed.
Lemma consts_to_values_constr_isprop_pars_decl ctx ind n :
  constructor_isprop_pars_decl (consts_to_values_env ctx) ind n =
  constructor_isprop_pars_decl ctx ind n.
Proof.
  rewrite
    /constructor_isprop_pars_decl 
    lookup_constructor_consts_to_values //.
Qed.  


Lemma consts_to_values_declared_constant ctx c decl :
  declared_constant ctx c decl ->
  declared_constant (consts_to_values_env ctx) c (consts_to_values_constant_decl decl).
Proof.
  unfold declared_constant.
  rewrite lookup_env_consts_to_values.
  destruct (lookup_env ctx c); intros [=->].
  reflexivity.
Qed.

Lemma consts_to_values_cst_body  decl :
  cst_body (consts_to_values_constant_decl decl) = option_map (fun t => tLazy (consts_to_values t)) (cst_body decl). 
Proof.
  destruct decl as [[?|]]; reflexivity.
Qed.

Lemma consts_to_values_head e :
  EAstUtils.head (consts_to_values e) = consts_to_values (EAstUtils.head e).
Proof.
  induction e; simpl; try reflexivity.
  now rewrite !EAstUtils.head_tApp.
Qed.  

Lemma consts_to_values_isLambda e : 
  isLambda (consts_to_values e) = isLambda e.
Proof.
  destruct e; reflexivity.
Qed.
Lemma consts_to_values_isFixApp e : EAstUtils.isFixApp (consts_to_values e) = EAstUtils.isFixApp e.
Proof.
  unfold EAstUtils.isFixApp.
  rewrite consts_to_values_head.
  destruct (EAstUtils.head e); reflexivity.
Qed.

Lemma consts_to_values_isFix e : 
  EAstUtils.isFix (consts_to_values e) = EAstUtils.isFix e.
Proof.
  destruct e; reflexivity.
Qed.

Lemma consts_to_values_isBox e : EAstUtils.isBox (consts_to_values e) = EAstUtils.isBox e.
Proof.
  destruct e; reflexivity.
Qed.

Lemma consts_to_values_isConstructApp e :
  EAstUtils.isConstructApp (consts_to_values e) = EAstUtils.isConstructApp e.
Proof.
  unfold EAstUtils.isConstructApp.
  rewrite consts_to_values_head.
  destruct (EAstUtils.head e); reflexivity.
Qed.

Lemma consts_to_values_isPrimApp e : EAstUtils.isPrimApp (consts_to_values e) = EAstUtils.isPrimApp e.
Proof.
  unfold EAstUtils.isPrimApp.
  rewrite consts_to_values_head.
  destruct (EAstUtils.head e); reflexivity.
Qed.

Lemma consts_to_values_isLazyApp e : EAstUtils.isLazyApp (consts_to_values e) = EAstUtils.isLazyApp e.
Proof.
  unfold EAstUtils.isLazyApp.
  rewrite consts_to_values_head.
  destruct (EAstUtils.head e); reflexivity.
Qed.

Lemma consts_to_values_iota pars args br :
  consts_to_values (iota_red pars args br) = 
  iota_red 
    pars 
    (map consts_to_values args) 
    (on_snd consts_to_values br).
Proof.
  rewrite /iota_red consts_to_values_substl -map_skipn map_rev //.
Qed.



#[local] Ltac destruct_IHs :=
    repeat match goal with 
    | IH : _ -> 
      eval (consts_to_values_env _) _ _
        |- _ =>
        unshelve epose proof IH _; first try easy;
        clear IH
    end;[
      try solve[
        repeat match goal with
        | h : is_true (is_nil ?l) |- _ => 
            destruct l; last (simpl in h; easy); clear h
        | h : _ /\ _ |- _ => destruct h
        | h : is_true (_ && _) |- _ => apply andb_andI in h
        | h : eval _ _ _ |- _ => 
            apply eval_wellformed in h; [|easy..]; simpl in h
        | h : is_true (wellformed _ _ (mkApps _ _)) |- _ =>
            rewrite wellformed_mkApps /= in h
        | |- is_true (wellformed _ _ (iota_red _ _ _)) => 
            eapply wellformed_iota_red_brs
        | |- is_true (wellformed _ _ (ECSubst.csubst _ _ _)) => 
            eapply wellformed_csubst
        | |- context[is_true (_ && _)] => rewrite andb_and
        | |- _ /\ _ => split; try easy
        | h : ?P |- ?P => assumption
        | |- is_true (wellformed _ _ (mkApps _ _)) =>
            rewrite wellformed_mkApps /=
        | h : cunfold_fix _ _ = Some (_, ?e) |-
            is_true (wellformed _ _ ?e) => 
            eapply wellformed_cunfold_fix; simpl
        | h : cunfold_cofix _ _ = Some (_, ?e) |-
            is_true (wellformed _ _ ?e) => 
            eapply wellformed_cunfold_cofix; simpl
        | h : nth_error _ _ = Some ?a |-
              is_true (wellformed _ _ ?a) => eapply nth_error_forallb
        | h : context[if ?c then _ else _] |- _ => 
            destruct c eqn:?
        end; easy
      ]..
    |].

Ltac my_simpl :=
  repeat match goal with
  | h : nth_error ?l ?n = Some ?r |-
      nth_error (map _ ?l) ?n = Some _ =>
        rewrite nth_error_map h //=
  | |- context[#|map _ _|] => rewrite length_map //
  | |- context[#|skipn _ (map _ _)|] => rewrite -map_skipn /=
  end.


Theorem trust_consts_to_values_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ term)
  (v : term),
  has_tApp -> (* Needed for eval_wellformed *)
  has_tBox -> (*  *)
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  let ip := consts_to_values_program p in
  eval_eprogram wfl ip (consts_to_values v).
Proof.
  intros ? ? [ctx e] ? ? htBox [wf_ctx wf_e] [eval_e]; simpl in *.
  constructor; simpl.
  induction eval_e; simpl in *; try rewrite ->!andb_and in *.
  - destruct_IHs. econstructor; eassumption.
  - destruct_IHs.
    econstructor; try eassumption.
    now rewrite -consts_to_values_csubst.
  - destruct_IHs.
    econstructor; first eassumption.
    now rewrite -consts_to_values_csubst.
  - destruct_IHs.
    econstructor.
    + assumption.
    + now rewrite consts_to_values_mkApps in H1.
    + rewrite consts_to_values_constr_isprop_pars_decl e1 //.
    + erewrite nth_error_map, e2; simpl.
      reflexivity.
    + rewrite length_map. eassumption. 
    + rewrite -map_skipn length_map. 
      destruct br; simpl in *. assumption.
    + rewrite -consts_to_values_iota //.
  - destruct_IHs.
    eapply eval_iota_block.
    + assumption.
    + eassumption.
    + rewrite consts_to_values_constr_isprop_pars_decl e1 //.
    + my_simpl.
    + my_simpl.
    + my_simpl.
    + rewrite -consts_to_values_iota //.
  - destruct_IHs.
    { subst brs. simpl in *.
      rewrite ->andb_and in *.
      destruct wf_e as (_ & _ & wf_f4 & _).
      apply wellformed_substl; last rewrite repeat_length //.
      remember #|n| as len.
      move:htBox.
      clear.
      induction len; simpl; first easy.
      rewrite andb_and; split; easy. }
    eapply eval_iota_sing.
    + assumption.
    + assumption.
    + rewrite consts_to_values_ind_isprop_and_pars //.
    + subst; reflexivity.
    + change tBox with (consts_to_values tBox).
      rewrite -map_repeat -consts_to_values_substl.
      assumption.
  - destruct_IHs.
    eapply eval_fix; simpl in *.
    + assumption.
    + now rewrite consts_to_values_mkApps /= in H2.
    + eassumption.
    + rewrite consts_to_values_cunfold_fix e1 length_map //.
    + rewrite -consts_to_values_mkApps //.
  - destruct_IHs.
    rewrite consts_to_values_mkApps /=.
    eapply eval_fix_value.
    + assumption.
    + now rewrite consts_to_values_mkApps /= in H1.
    + eassumption.
    + rewrite consts_to_values_cunfold_fix e1.
      reflexivity.
    + my_simpl.
  - destruct_IHs.
    eapply eval_fix'; try eassumption.
    rewrite consts_to_values_cunfold_fix e0; reflexivity.
  - destruct_IHs.
    eapply eval_cofix_case.
    + rewrite consts_to_values_mkApps /= in H1.
      eassumption.
    + rewrite consts_to_values_cunfold_cofix e0 /on_snd //.
    + rewrite consts_to_values_mkApps // in H0.
  - destruct_IHs.
    eapply eval_cofix_proj.
    + rewrite consts_to_values_mkApps /= in H1.
      eassumption.
    + rewrite consts_to_values_cunfold_cofix e0 /on_snd //.
    + rewrite consts_to_values_mkApps // in H0.
  - destruct_IHs.
    { rewrite /lookup_constant isdecl /= in wf_e.
      apply lookup_env_wellformed in isdecl; last assumption.
      rewrite /wf_global_decl e //= in isdecl. }
    eapply eval_force.
    + econstructor.
      * now apply consts_to_values_declared_constant. 
      * rewrite consts_to_values_cst_body e //.
      * do 2 constructor.
    + assumption.
  - destruct_IHs.
    eapply eval_proj.
    + assumption.
    + now rewrite consts_to_values_mkApps in H1.
    + now rewrite consts_to_values_constr_isprop_pars_decl.
    + my_simpl.
    + my_simpl.
    + assumption. 
  - destruct_IHs.
    eapply eval_proj_block.
    + assumption.
    + eassumption.
    + now rewrite consts_to_values_constr_isprop_pars_decl.
    + my_simpl.
    + my_simpl.
    + assumption.
  - destruct_IHs.
    apply eval_proj_prop; try assumption.
    now rewrite consts_to_values_ind_isprop_and_pars.
  - destruct_IHs.
    rewrite consts_to_values_mkApps /=.
    eapply eval_construct.
    + assumption.
    + now rewrite lookup_constructor_consts_to_values.
    + now rewrite consts_to_values_mkApps in H1.
    + my_simpl.
    + assumption.
  - destruct_IHs.
    eapply eval_construct_block.
    + assumption.
    + now rewrite lookup_constructor_consts_to_values.
    + my_simpl.
    + destruct cstr_as_blocks; last first.
      { destruct args; last easy. 
        inversion a; subst.
        constructor. }
      rewrite /lookup_constructor_pars_args e0 /= in wf_e.
      destruct wf_e as [[? ?] [? ?]%andb_andI].
      apply All2_All2_Set, All2_map.
      apply All2_over_undep in iha.
      unshelve eapply (All2_apply_dep_arrow _ iha).
      now convert_foralls.
  - destruct_IHs.
    apply eval_app_cong; try assumption.
    rewrite 
      consts_to_values_isLambda
      consts_to_values_isFixApp
      consts_to_values_isFix
      consts_to_values_isBox
      consts_to_values_isConstructApp
      consts_to_values_isPrimApp
      consts_to_values_isLazyApp
      //.
  - inversion X; subst; try solve[repeat constructor].
    rewrite /test_prim /= /test_array_model /= in wf_e.
    destruct wf_e as [? [? ?]%andb_andI].
    destruct_IHs.
    unfold map_prim; simpl.
    do 2 constructor; last assumption.
    subst a a'; simpl in *.
    apply All2_All2_Set, All2_map.
    apply All2_over_undep in X0.
    unshelve eapply (All2_apply_dep_arrow _ X0).
    now convert_foralls.
  - destruct_IHs.
    econstructor; eassumption.
  - apply eval_atom.
    now rewrite consts_to_values_atom.
Qed.