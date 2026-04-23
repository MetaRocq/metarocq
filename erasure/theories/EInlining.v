From Stdlib Require Import List String Arith Lia ssreflect ssrbool.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring utils monad_utils.
From MetaRocq.Erasure Require Import EPrimitive EAst EEnvMap EInduction EGlobalEnv.

Import Kernames.
Import MonadNotation.

(* Inlining hints *)
Definition inlining := KernameSet.t.
(* Fast maps for actual inlinings *)
Definition constants_inlining := KernameMap.t term.

Section Inline.
  Context (inlining : constants_inlining).

  Equations inline (t : term) : term :=
    | tVar na => tVar na
    | tLambda nm bod => tLambda nm (inline bod)
    | tLetIn nm dfn bod => tLetIn nm (inline dfn) (inline bod)
    | tApp fn arg => tApp (inline fn) (inline arg)
    | tConst nm with KernameMap.find nm inlining :=
      { | Some body := (* Already inlined body *) body
        | None := tConst nm }
    | tConstruct i m args => tConstruct i m (map inline args)
    | tCase i mch brs => tCase i (inline mch) (map (on_snd inline) brs)
    (* TODO: See if we inline the machee, it wasn't the case initially *)

    | tFix mfix idx => tFix (map (map_def inline) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def inline) mfix) idx
    | tProj p bod => tProj p (inline bod)
    | tPrim p => tPrim (map_prim inline p)
    | tLazy t => tLazy (inline t)
    | tForce t => tForce (inline t)
    | tRel n => tRel n
    | tBox => tBox
    | tEvar ev args => tEvar ev (map inline args).
End Inline.

Definition inline_constant_decl inlining cb :=
  {| cst_body := option_map (inline inlining) cb.(cst_body) |}.


Definition inline_global_decl inlining (d : global_decl) :=
  match d with
  | ConstantDecl cb => ConstantDecl (inline_constant_decl inlining cb)
  | InductiveDecl idecl => d
  end.
Definition inline_decl inlining d : (kername * global_decl) :=
  (d.1, inline_global_decl inlining d.2).

Definition inline_add (inlining : inlining) (acc : global_context × constants_inlining) decl :=
  let '(Σ, inls) := acc in
  if KernameSet.mem decl.1 inlining then
    match decl.2 with
    | ConstantDecl {| cst_body := Some body |} => KernameMap.add decl.1 body inls
    | _ => inls
    end
  else inls.

Definition inline_env (inlining : KernameSet.t) Σ : global_context × constants_inlining :=
  let inline_decl '(Σ, inls) decl :=
    let inldecl := inline_decl inls decl in
    (inldecl :: Σ, inline_add inlining (Σ, inls) inldecl)
  in
  fold_left (inline_decl) (rev Σ) ([], KernameMap.empty _).



Definition inlined_program :=
  (global_context × constants_inlining) × term.

Definition inlined_program_inlinings (pr : inlined_program) : constants_inlining :=
  pr.1.2.

Coercion inlined_program_inlinings : inlined_program >-> constants_inlining.

Definition inline_program inlining (p : program) : inlined_program :=
  let '(Σ', inls) := inline_env inlining p.1 in
  (Σ', inls, inline inls p.2).

(* Maybe a good idea to have something like 
  inline_program (ctx, p) = inline_program (inline_env ctx.1, p)
*)

From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.

Definition forget_inlining_info (pr : inlined_program) : eprogram :=
  let '((Σ', inls), p) := pr in
  (Σ', p).

Coercion forget_inlining_info : inlined_program >-> eprogram.

Definition eval_inlined_program wfl (pr : inlined_program) := eval_eprogram wfl pr.


Ltac destruct_inline_env :=
  let destr inlining ctx := 
    replace (inline_env inlining ctx) with ((inline_env inlining ctx).1, (inline_env inlining ctx).2) in *;
    last (destruct (inline_env inlining ctx); reflexivity)
  in
  match goal with
  | h : context[let (_, _) := inline_env ?inlining ?ctx in _] |- _ =>
    destr inlining ctx
  | |- context[let (_, _) := inline_env ?inlining ?ctx in _] =>
      destr inlining ctx
  end.


Create HintDb inlining_rw_hints.
Ltac simple := repeat (
    assumption ||
    match goal with
    | |- All _ _ => apply Forall_All 
    | H : All _ _ |- _ => apply All_Forall in H
    | h : ?e = Some _ |-
        option_map _ ?e = Some _ =>
          rewrite h
    end ||
    autorewrite with inlining_rw_hints in * || 
    destruct_inline_env ||
    simpl in *
  ).

Hint Rewrite @Forall_All : inlining_rw_hints.
Hint Rewrite <-@forallb_Forall : inlining_rw_hints.
Hint Rewrite <-@forallb_Forall : inlining_rw_hints.
Hint Rewrite Forall_forall : inlining_rw_hints.
Hint Rewrite @forallb_map : inlining_rw_hints.
Hint Rewrite andb_and : inlining_rw_hints.
Hint Rewrite length_map : inlining_rw_hints.
Hint Rewrite length_map : inlining_rw_hints.
Hint Rewrite <- @map_skipn : inlining_rw_hints.
Hint Rewrite @nth_error_map : inlining_rw_hints.
Hint Rewrite <-@map_repeat : inlining_rw_hints.
Hint Rewrite andb_and : inlining_rw_hints.
Hint Rewrite repeat_length : inlining_rw_hints.
Hint Rewrite if_same : inlining_rw_hints.

Lemma inline_env_nil_1
  (efl : EEnvFlags) (flags : WcbvFlags) inlining :
  (inline_env inlining []).1 = [].
Proof.
  reflexivity.
Qed.
Hint Rewrite inline_env_nil_1 : inlining_rw_hints.


Lemma inline_env_cons_1
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) d :
  (inline_env inlining (d :: ctx)).1 = inline_decl (inline_env inlining ctx).2 d :: (inline_env inlining ctx).1.
Proof.
  induction ctx as [|d' ctx IH]; first reflexivity.
  rewrite /inline_env rev_cons fold_left_app.
  fold (inline_env inlining (d'::ctx)).
  now simple.
Qed.
Hint Rewrite inline_env_cons_1 : inlining_rw_hints.


Lemma inline_env_nil_2
  (efl : EEnvFlags) (flags : WcbvFlags) inlining :
  (inline_env inlining []).2 = KernameMap.empty term.
Proof.
  reflexivity.
Qed.
Hint Rewrite inline_env_nil_2 : inlining_rw_hints.


Lemma inline_env_cons_2
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) d :
  (inline_env inlining (d :: ctx)).2 = 
  inline_add
    inlining 
    (inline_env inlining ctx)
    (inline_decl (inline_env inlining ctx).2 d).
Proof.
  induction ctx as [|d' ctx IH]; first reflexivity.
  rewrite /inline_env rev_cons fold_left_app.
  fold (inline_env inlining (d'::ctx)).
  now simple.
Qed.
Hint Rewrite inline_env_cons_2 : inlining_rw_hints.


Lemma fresh_inline 
  (efl : EEnvFlags) (flags : WcbvFlags) 
  (inlining : inlining) (glob_ctx : global_context)
  (name : kername) :
  fresh_global name (inline_env inlining glob_ctx).1 <-> fresh_global name glob_ctx.
Proof.
  induction glob_ctx as [| [? decl] ? ?]; first reflexivity.
  rewrite inline_env_cons_1 /inline_decl /= /fresh_global !Forall_cons_iff.
  apply ZifyClasses.and_morph; last assumption.
  now destruct decl.
Qed.
Hint Rewrite fresh_inline : inlining_rw_hints.


Lemma isLambda_inline (t : term) inlining :
  isLambda t ->
  isLambda (inline inlining t).
Proof.
  now destruct t.
Qed.

Lemma is_nil_map {A B : Type} (f : A -> B) l :
  is_nil (map f l) = is_nil l.
Proof.
  now destruct l.
Qed.
Hint Rewrite @is_nil_map : inlining_rw_hints.


Lemma wellformed_monotone 
  {efl : EEnvFlags} (ctx : global_context) (k k': nat) e :
  k <= k' ->
  wellformed ctx k e ->
  wellformed ctx k' e.
Proof.
  induction e using term_forall_list_ind in k, k' |- *;
  repeat (
      easy ||
      simple ||
      unfold wf_fix in * ||
      unfold test_def in * ||
      unfold test_prim in * ||
      unfold test_array_model in * ||
      match goal with
      | X : primProp _ _ |- _ =>
          inversion X as [| | | ? [? ?]]; subst; clear X
      | |- context[if ?p then _ else _] => destruct p
      | |- context[match ?p with _ => _ end] => destruct p
      | |- _ -> _ => intro
      | h : _ /\ _ |- _ => destruct h
      | |- _ /\ _ => split
      | |- context[is_nil (map _ _)] => rewrite is_nil_map
      | h: is_true (_ <? _) |- _ => unfold is_true in h; rewrite ->Nat.ltb_lt in h
      | |- is_true (_ <? _) => unfold is_true; rewrite ->Nat.ltb_lt
      end ||
      eauto with arith
    ).
Qed.


Definition wf_inlining {efl : EEnvFlags} (ctx : global_context) (k : nat) (inlining : constants_inlining) :=
  forall key (e : term), KernameMap.find (elt := term) key inlining = Some e ->
  wellformed ctx k e.


Lemma wf_inlining_monotone {efl : EEnvFlags} (ctx : global_context) (k k' : nat) (inlining : constants_inlining) :
  k <= k' ->
  wf_inlining ctx k inlining ->
  wf_inlining ctx k' inlining.
Proof.
  intros k_le_k' wf_in key e heq.
  eapply wellformed_monotone; first eassumption.
  eapply wf_in, heq.
Qed.

Ltac wf_mon_inlining :=
  solve[
    eapply wf_inlining_monotone; last eassumption;
    auto with arith
  ].



Lemma lookup_env_fresh_None ctx name :
  fresh_global name ctx ->
  lookup_env ctx name = None.
Proof.
  destruct (lookup_env ctx name) eqn:heq; last reflexivity.
  now apply lookup_env_Some_fresh in heq.
Qed.


Lemma lookup_constant_fresh_None ctx name :
  fresh_global name ctx ->
  lookup_constant ctx name = None.
Proof.
  intros.
  unfold lookup_constant.
  now rewrite lookup_env_fresh_None.
Qed.

Lemma inline_decl_1 inlining d :
  (inline_decl inlining d).1 = d.1.
Proof.
  destruct d as [? [|]]; reflexivity.
Qed.
Hint Rewrite inline_decl_1 : inlining_rw_hints.

Lemma inline_env_lookup (efl : EEnvFlags) (flags : WcbvFlags) inlining ctx name t :
  KernameSet.mem name inlining ->
  wf_glob ctx ->
  KernameMap.find name (inline_env inlining ctx).2 = Some t <->
  lookup_env (inline_env inlining ctx).1 name = 
    Some (ConstantDecl {|cst_body := Some t|}).
Proof.
  intros h_in h_wf_ctx.
  induction ctx
    as [|[name' [[[body|]] | B]] ctx IH]
    in h_in, h_wf_ctx, t |- *; simple.
  - now rewrite KernameMapFact.F.empty_o.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    simple.
    destruct (name == name') eqn:heq'; rewrite heq'.
    + apply eqb_eq in heq'; subst.
      rewrite h_in.
      rewrite KernameMapFact.F.add_eq_o.
      { apply KernameMap.E.eq_refl. }
      easy.
    + destruct (KernameSet.mem name' inlining) eqn:heq''.
      * rewrite KernameMapFact.F.add_neq_o.
        { unfold 
            eqb, 
            Kername.reflect_kername, Kername.eqb, Kername.compare 
            in *.
          destruct name as [n1 n2], name' as [n1' n2'].
          rewrite 
            (StringOT.compare_sym n2' n2)
            (ModPathComp.compare_sym n1 n1')
            -compare_cont_CompOpp.
          destruct (compare_cont (ModPathComp.compare n1 n1') (string_compare n2 n2')); easy. }
        rewrite IH //.
      * now apply IH.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    simple.
    destruct (name == name') eqn:heq'; rewrite heq'; rewrite IH //.
    split; last easy.
    apply eqb_eq in heq'; subst.
    rewrite lookup_env_fresh_None //.
    now rewrite fresh_inline.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    simple.
    destruct (name == name') eqn:heq'; rewrite heq'; rewrite IH //.
    split; last easy.
    apply eqb_eq in heq'; subst.
    rewrite lookup_env_fresh_None //.
    now rewrite fresh_inline.
Qed.

Lemma inline_env_lookup_no_inline_None (efl : EEnvFlags) (flags : WcbvFlags) inlining ctx name :
  ~~ KernameSet.mem name inlining ->
  wf_glob ctx ->
  KernameMap.find name (inline_env inlining ctx).2 = None.
Proof.
  intros h_nin%negbTE h_wf_ctx.
  induction ctx
    as [|[name' [[[body|]] | B]] ctx IH]; simple.
  - now rewrite KernameMapFact.F.empty_o.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    simple.
    destruct (name == name') eqn:cmp_name_name'.
    + apply eqb_eq in cmp_name_name'; subst.
      now rewrite h_nin.
    + destruct (KernameSet.mem name' inlining) eqn:heq''.
      * rewrite KernameMapFact.F.add_neq_o.
        { unfold 
            eqb, 
            Kername.reflect_kername, Kername.eqb, Kername.compare 
            in *.
          destruct name as [n1 n2], name' as [n1' n2'].
          rewrite 
            (StringOT.compare_sym n2' n2)
            (ModPathComp.compare_sym n1 n1')
            -compare_cont_CompOpp.
          destruct (compare_cont (ModPathComp.compare n1 n1') (string_compare n2 n2')); easy. }
        rewrite IH //.
      * now apply IH.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    now simple.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    now simple.
Qed.


Lemma inline_add_fresh 
  (efl : EEnvFlags) (flags : WcbvFlags) name k ctx t t' inls :
  fresh_global name ctx ->
  wellformed ctx k t ->
  inline (KernameMap.add name t' inls) t = inline inls t.
Proof.
  intros name_fresh t_wf.
  induction t using term_forall_list_ind 
  in name_fresh, t_wf, k |- *; simple; try now f_equal.
  - f_equal. apply All_map_eq.
    now simple.
  - unfold inline_clause_5.
    destruct (eqb_spec name s) as [heq | hneq].
    + subst.
      unfold lookup_constant in t_wf.
      destruct (lookup_env ctx s) as [[|]|] eqn:heq; 
      simple; try easy.
      now apply lookup_env_Some_fresh in heq.
    + rewrite -Kername.compare_eq in hneq.
      now rewrite KernameMapFact.F.add_neq_o.
  - destruct cstr_as_blocks; f_equal; apply All_map_eq.
    + now simple.
    + now destruct args.
  - f_equal; first easy.
    unfold on_snd.
    apply All_map_eq.
    simple.
    intros; now f_equal.
  - f_equal. 
    unfold map_def, wf_fix in *.
    apply All_map_eq.
    simple.
    intros; now f_equal.
  - f_equal. 
    unfold map_def, wf_fix in *.
    apply All_map_eq.
    simple.
    intros; now f_equal.
  - f_equal.
    unfold map_prim, map_array_model, test_prim, test_array_model in *;
    inversion X as [| | |? [? ?]]; subst;
    simple; try easy.
    do 3 f_equal; first easy.
    apply All_map_eq.
    simple.
    intros; easy.
Qed.

Lemma wf_cons (efl : EEnvFlags) k d ctx t :
  wf_glob (d :: ctx) ->
  wellformed ctx k t -> 
  wellformed (d::ctx) k t.
Proof.
  induction t using term_forall_list_ind in k |- *; simple; try easy.
  - inversion 1; subst; split; first easy.
    unfold lookup_constant, lookup_env in *; fold lookup_env in *.
    simple; destruct (eqb_spec s kn); try easy.
    subst. 
    destruct (lookup_env ctx kn) as [[]|] eqn:heq; try easy.
    exfalso.
    now eapply lookup_env_Some_fresh.
  - inversion 1; subst; repeat split; first easy.
    + destruct H0 as [[_ H'] _].
      unfold
        lookup_constructor,
        lookup_inductive,
        lookup_minductive,
        lookup_env in *.
      fold lookup_env in *.
      simple.
      destruct (lookup_env ctx (inductive_mind i)) as [[|]|] eqn:heq; try easy.
      destruct (eqb_spec (inductive_mind i) kn); subst.
      { exfalso. now eapply lookup_env_Some_fresh. }
      easy.
    + destruct cstr_as_blocks; simple; last now destruct args.
      unfold
        lookup_constructor_pars_args,
        lookup_constructor,
        lookup_inductive,
        lookup_minductive,
        lookup_env in *.
      fold lookup_env in *.
      simple.
      destruct (eqb_spec (inductive_mind i) kn); subst.
      { now rewrite lookup_env_fresh_None in H0. }
      easy.
  - inversion 1; subst.
    repeat split; try easy.
    unfold 
      wf_brs,
      lookup_inductive,
      lookup_minductive,
      lookup_env in *.
      fold lookup_env in *.
      destruct (eqb_spec (inductive_mind p.1) kn); subst; simple.
      { now rewrite lookup_env_fresh_None in H0. }
      rewrite ifF.
      { now destruct (eqb_spec (inductive_mind p.1) kn). }
      easy.
  - inversion 1; subst.
    repeat split; try easy.
    unfold 
      lookup_projection,
      lookup_constructor,
      lookup_inductive,
      lookup_minductive,
      lookup_env in *;
      fold lookup_env in *.
      simple.
      destruct (eqb_spec (inductive_mind (proj_ind s)) kn); subst; simple.
      { now rewrite lookup_env_fresh_None in H0. }
      easy.
  - unfold wf_fix; now simple.
  - unfold wf_fix; now simple.
  - inversion 1; subst.
    unfold test_prim, test_array_model in *.
    inversion X as [| | | ? [? ?]]; subst; now simple.
Qed.

Lemma lookup_env_wf (efl : EEnvFlags) ctx name t :
  wf_glob ctx ->
  lookup_env ctx name = Some (ConstantDecl {| cst_body := Some t |}) ->
  wellformed ctx 0 t.
Proof.
  pose proof wf_cons.
  induction ctx as [| [name' d] ctx IH ]; first easy.
  inversion 1; subst.
  simple.
  destruct (eqb_spec name name'); last easy.
  destruct d as [[[t'|]]|]; try easy.
  intros [=[=[=[= ?]]]]; subst; easy.
Qed.

Lemma lookup_env_inline (efl : EEnvFlags) (flags : WcbvFlags) inlining ctx name :
  wf_glob ctx ->
  lookup_env (inline_env inlining ctx).1 name =
  option_map
    (inline_global_decl (inline_env inlining ctx).2)
    (lookup_env ctx name).
Proof.
  intros h_wf_ctx.
  induction ctx
    as [|[name' [[[body|]] | B]] ctx IH]; simple.
  - reflexivity.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    simple.
    destruct (name == name') eqn:cmp_name_name'.
    + apply eqb_eq in cmp_name_name'; subst.
      rewrite /inline_global_decl /inline_constant_decl; simple.
      do 4 f_equal.
      destruct (KernameSet.mem name' inlining); last reflexivity.
      now erewrite inline_add_fresh.
    + destruct (KernameSet.mem name' inlining) eqn:heq'; 
        last easy.
      rewrite IH //.
      destruct (lookup_env ctx name) as [[[[|]]|]|] eqn:heq''; try reflexivity.
      unfold inline_global_decl, inline_constant_decl.
      simple.
      erewrite inline_add_fresh; try easy.
      now eapply lookup_env_wf.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    simple.
    rewrite 
      (fun_if (option_map _)) /= 
      /inline_constant_decl /= IH //.
  - inversion h_wf_ctx; subst.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    simple.
    rewrite 
      (fun_if (option_map _)) /= 
      /inline_constant_decl /= IH //.
Qed.
Hint Rewrite lookup_env_inline : inlining_rw_hints.


Lemma lookup_constant_inlining
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) name d :
  wf_glob ctx ->
  let ctx' := (inline_env inlining ctx).1 in
  lookup_constant ctx name = Some d ->
  lookup_constant ctx' name = Some (inline_constant_decl (inline_env inlining ctx).2 d).
Proof.
  intros wf_ctx. simple.
  rewrite /lookup_constant lookup_env_inline //.
  destruct (lookup_env ctx name) as [[|]|]; simple; easy.
Qed.

Lemma lookup_mind_inlining
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) name :
  let ctx' := (inline_env inlining ctx).1 in
  lookup_minductive ctx' name = lookup_minductive ctx name.
Proof.
  unfold lookup_minductive; simple.
  induction ctx as [|[name' [?|?]] ? IH]; simpl in *; first easy;
  simple; destruct (name == name'); eauto.
Qed. 

Hint Rewrite lookup_mind_inlining : inlining_rw_hints.


Lemma lookup_ind_inlining
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) name :
  let ctx' := (inline_env inlining ctx).1 in
  lookup_inductive ctx' name = lookup_inductive ctx name.
Proof.
  unfold lookup_inductive.
  now simple.
Qed.
Hint Rewrite lookup_ind_inlining : inlining_rw_hints.

Lemma lookup_constr_inlining
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) name n :
  let ctx' := (inline_env inlining ctx).1 in
  lookup_constructor ctx' name n = lookup_constructor ctx name n.
Proof.
  unfold lookup_constructor.
  now simple.
Qed.
Hint Rewrite lookup_constr_inlining : inlining_rw_hints.

Lemma lookup_constr_pars_args_inlining
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) name n :
  let ctx' := (inline_env inlining ctx).1 in
  lookup_constructor_pars_args ctx' name n = 
  lookup_constructor_pars_args ctx name n.
Proof.
  unfold lookup_constructor_pars_args.
  now simple.
Qed.
Hint Rewrite lookup_constr_pars_args_inlining : inlining_rw_hints.


Lemma lookup_proj_inlining
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) name :
  let ctx' := (inline_env inlining ctx).1 in
  lookup_projection ctx' name = 
  lookup_projection ctx name.
Proof.
  unfold lookup_projection.
  now simple.
Qed.
Hint Rewrite lookup_proj_inlining : inlining_rw_hints.

Theorem wf_inlining_same_ctx 
  (efl : EEnvFlags) (flags : WcbvFlags)  inlining
  (t : term) (k : nat) (ctx : global_context) :
  wf_inlining ctx k inlining ->
  wellformed ctx k t -> 
  wellformed ctx k (inline inlining t).
Proof.
  induction t using term_forall_list_ind in k |- *;
  simple; unfold wf_fix, test_def in *; simple; try easy.
  - intros ? h; split; first easy.
    apply (IHt (S k)); last easy.
    wf_mon_inlining.
  - intros ? h; split; first easy.
    apply (IHt2 (S k)); last easy.
    wf_mon_inlining.
  - intros ? ?.
    unfold inline_clause_5.
    destruct 
      (lookup_constant ctx s) as [[[|]]|] eqn:heq, 
      (KernameMap.find (elt:=term) s inlining) eqn:heq'; 
      simple; rewrite ?heq; easy.
  - intros. destruct cstr_as_blocks; now simple.
  - repeat split; try easy.
    intros. apply X; try easy.
    wf_mon_inlining.
  - repeat split; try easy.
    + intros. now apply isLambda_inline.
    + intros. apply X; try easy.
      wf_mon_inlining.
  - repeat split; try easy.
    intros. apply X; try easy.
    wf_mon_inlining.
  - intros.
    unfold map_prim, test_prim, test_array_model in *.
    simple.
    inversion X as [| | | ? [? ?]]; subst; split; simple; try easy.
Qed.

Theorem wf_inlining_ctx 
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (k : nat) (ctx : global_context) e :
  wf_glob ctx ->
  wellformed ctx k e ->
  let ctx' := (inline_env inlining ctx).1 in
  wellformed ctx' k e.
Proof.
  induction e using term_forall_list_ind in k |- *;
  simpl in *; unfold wf_fix, wf_brs, test_prim, test_array_model; 
  simple; try easy.
  - destruct (lookup_constant ctx s) as [[[|]]|] eqn:heq'; 
    simple; try easy.
    + intros; split; first easy.
      erewrite lookup_constant_inlining; now simple; try easy.
    + intros; split; first easy.
      erewrite lookup_constant_inlining; now simple; try easy.
  - intros; repeat split; try easy.
    destruct cstr_as_blocks; try easy.
    simple.
    now destruct (lookup_constructor_pars_args ctx i n).
  - intros. split; first easy.
    now inversion X as [| | | ? [? ?]]; subst; simple. 
Qed.
  

Lemma wf_glob_inlining 
  (efl : EEnvFlags) (flags : WcbvFlags) inlining
  (ctx : global_context) :
  wf_glob ctx ->
  let Σ := (inline_env inlining ctx).1 in
  let inls := (inline_env inlining ctx).2 in
  wf_glob Σ /\ wf_inlining Σ 0 inls.
Proof.
  induction ctx; first easy.
  rewrite inline_env_cons_1; simpl.
  intros h; inversion h as [| name [[[?|]]|] ? wf_ctx wf_d fresh_name]; clear h; subst.
  - split.
    { constructor; simple; try easy.
      apply wf_inlining_same_ctx; try easy.
      now apply wf_inlining_ctx. }
    simpl in *.
    intros name' e heq.
    unfold inline_add in heq.
    simple.
    destruct (KernameSet.mem name inlining) eqn:h_in; last first.
    { apply wf_cons.
      - constructor.
        + easy.
        + now apply wf_inlining_same_ctx, wf_inlining_ctx.
        + now apply fresh_inline.
      - now rewrite /inline_add h_in /= in heq. }
    rewrite /inline_add h_in  /= in heq.
    simple.
    destruct (name == name') eqn:comp_name_name'.
    + apply eqb_eq in comp_name_name'; subst.
      rewrite KernameMapFact.F.add_eq_o in heq.
      { apply KernameMap.E.eq_refl. }
      injection heq as heq; subst.
      apply wf_cons.
      { constructor.
        - easy.
        - now apply wf_inlining_same_ctx, wf_inlining_ctx.
        - now apply fresh_inline. }
      now apply wf_inlining_same_ctx, wf_inlining_ctx; try easy.
    + rewrite KernameMapFact.F.add_neq_o in heq.
      { unfold 
          eqb, 
          Kername.reflect_kername, Kername.eqb, Kername.compare 
          in *.
        destruct name as [n1 n2], name' as [n1' n2'].
        destruct (compare_cont (ModPathComp.compare n1 n1') (string_compare n2 n2')); easy. }
      apply wf_cons.
      { constructor.
        - easy.
        - now apply wf_inlining_same_ctx, wf_inlining_ctx.
        - now apply fresh_inline. }
    assert (KernameSet.mem name' inlining).
    { destruct (KernameSet.mem name' inlining) eqn:h_in';
      first easy.
      rewrite inline_env_lookup_no_inline_None // in heq.
      now rewrite h_in'. }
    rewrite inline_env_lookup // lookup_env_inline // in heq.
    destruct (lookup_env ctx name') as [[[[e'|]]|]|] eqn:h_lookup_name'; try easy.
    injection heq as heq; subst.
    now eapply 
      wf_inlining_same_ctx,
      wf_inlining_ctx,
      lookup_env_wf.

  - split; first now constructor; simple.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    intros name' e heq.
    unfold inline_add in heq.
    simple.
    destruct (KernameSet.mem name inlining) eqn:h_in; last first.
    {apply wf_cons.
      - constructor; try easy.
        now apply fresh_inline.
      - now rewrite /inline_add h_in /= in heq. }
    rewrite /inline_add h_in  /= in heq.
    apply wf_cons.
    { constructor; try easy.
      now apply fresh_inline. }
    assert (KernameSet.mem name' inlining).
    { destruct (KernameSet.mem name' inlining) eqn:h_in';
      first easy.
      rewrite inline_env_lookup_no_inline_None // in heq.
      now rewrite h_in'. }
    rewrite inline_env_lookup // lookup_env_inline // in heq.
    destruct (lookup_env ctx name') as [[[[e'|]]|]|] eqn:h_lookup_name'; try easy.
    injection heq as heq; subst.
    now eapply 
      wf_inlining_same_ctx,
      wf_inlining_ctx,
      lookup_env_wf.
  - split; first now constructor; simple.
    rewrite /inline_decl /= /inline_constant_decl /= /inline_add.
    intros name' e heq.
    unfold inline_add in heq.
    simple.
    destruct (KernameSet.mem name inlining) eqn:h_in; last first.
    { apply wf_cons.
      - constructor; try easy.
        now apply fresh_inline.
      - now rewrite /inline_add h_in /= in heq. }
    apply wf_cons.
    { constructor; try easy.
      now apply fresh_inline. }
    rewrite /inline_add h_in  /= in heq.
    simple.
    assert (KernameSet.mem name' inlining).
    { destruct (KernameSet.mem name' inlining) eqn:h_in';
      first easy.
      rewrite inline_env_lookup_no_inline_None // in heq.
      now rewrite h_in'. }
    rewrite inline_env_lookup // lookup_env_inline // in heq.
    destruct (lookup_env ctx name') as [[[[e'|]]|]|] eqn:h_lookup_name'; try easy.
    injection heq as heq; subst.
    now eapply 
      wf_inlining_same_ctx,
      wf_inlining_ctx,
      lookup_env_wf.
Qed.
     

Theorem inlining_wf :
  forall (efl : EEnvFlags)
  (wfl : WcbvFlags) inlining 
  (input : Transform.program _ term),
  wf_eprogram efl input -> 
  wf_eprogram efl (inline_program inlining input).
Proof.
  intros ? ? inlining [ctx e] [? ?]; unfold wf_eprogram, inline_program; split; simple; first now apply wf_glob_inlining.
  pose proof wf_glob_inlining efl wfl inlining ctx.
  pose proof wf_inlining_ctx efl wfl inlining 0 ctx e.
  pose proof wf_inlining_same_ctx.
  now simple.
Qed.



#[local] Ltac destruct_IHs :=
    repeat match goal with 
    | Σ' := (inline_env _ _).1,
      IH : _ -> 
      eval ?Σ' _ _
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

Lemma wf_inlining_closed 
  (efl : EEnvFlags)
  inlining ctx k name t :
  wf_inlining ctx k inlining ->
  KernameMap.find name inlining = Some t ->
  ELiftSubst.closedn k t.
Proof.
  intros h_wf_inl heq.
  unfold wf_inlining in *.
  now eapply wellformed_closed.
Qed.


Lemma inline_csubst (efl : EEnvFlags) inlining ctx e1 e2 k :
  wf_inlining ctx k inlining ->
  inline inlining (ECSubst.csubst e1 k e2) =
  ECSubst.csubst (inline inlining e1) k (inline inlining e2).
Proof.
  intros h_wf_inlining.
  assert (wf_inlining ctx (S k) inlining) 
    as h_wf_inlining' 
    by wf_mon_inlining.
  induction e2 
    using term_forall_list_ind
    in k, h_wf_inlining  |- *;
    assert (wf_inlining ctx (S k) inlining) 
      as h_wf_inlining' 
      by wf_mon_inlining;
      simple; try now f_equal.
  - simple. destruct (k ?= n); reflexivity.
  - simple.
    f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    now simple.
  - unfold inline_clause_5.
    destruct (KernameMap.find (elt:=term) s inlining) eqn:heq; last reflexivity.
    rewrite ECSubst.csubst_closed; last easy.
    now eapply wf_inlining_closed.
  - simple; f_equal.
    rewrite !map_map_compose.
    apply All_map_eq.
    now simple.
  - f_equal; first easy.
    rewrite !map_map_compose.
    apply All_map_eq.
    unfold on_snd.
    simple.
    intros.
    f_equal.
    apply X; try easy.
    now apply wf_inlining_monotone with (k := k).
  - simple; f_equal.
    unfold map_def.
    rewrite !map_map_compose.
    apply All_map_eq.
    simple. intros. f_equal.
    apply X; first easy.
    now apply wf_inlining_monotone with (k := k).
  - simple; f_equal.
    unfold map_def.
    rewrite !map_map_compose.
    apply All_map_eq.
    simple. intros. f_equal.
    apply X; first easy.
    now apply wf_inlining_monotone with (k := k).
  - inversion X as [| | | ? [? ?]]; 
    unfold map_prim, map_array_model; 
    simple; try easy.
    do 4 f_equal; first easy.
    rewrite !map_map_compose.
    apply All_map_eq.
    now simple.
Qed.
Hint Rewrite inline_csubst : inlining_rw_hints.


Lemma inline_substl (efl : EEnvFlags) inlining ctx l e :
  wf_inlining ctx 0 inlining ->
  inline inlining (ECSubst.substl l e) =
  ECSubst.substl (map (inline inlining) l) (inline inlining e).
Proof.
  unfold ECSubst.substl.
  intros.
  induction l as [| ? ? IH] 
    using list_ind_rev; simpl; first reflexivity.
  rewrite map_app !fold_left_app -IH.
  simple.
  now erewrite inline_csubst.
Qed.
Hint Rewrite <- inline_substl : inlining_rw_hints.

Lemma inline_mkApps inlining e l :
  inline inlining (mkApps e l) =
  mkApps (inline inlining e) (map (inline inlining) l).
Proof.
  now induction l in e |- *.
Qed.
Hint Rewrite inline_mkApps : inlining_rw_hints.




Lemma inline_ind_isprop_and_pars
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining ctx ind :
  inductive_isprop_and_pars (inline_env inlining ctx).1 ind =
  inductive_isprop_and_pars ctx ind.
Proof.
  unfold inductive_isprop_and_pars.
  now simple.
Qed.
Hint Rewrite inline_ind_isprop_and_pars : inlining_rw_hints.

Lemma inline_constr_isprop_pars_decl 
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining ctx ind n :
  constructor_isprop_pars_decl (inline_env inlining ctx).1 ind n =
  constructor_isprop_pars_decl ctx ind n.
Proof.
  unfold constructor_isprop_pars_decl.
  now simple. 
Qed.  
Hint Rewrite inline_constr_isprop_pars_decl : inlining_rw_hints.


Lemma inline_iota 
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining pars args br ctx :
  wf_inlining ctx 0 inlining ->
  inline inlining (iota_red pars args br) = 
  iota_red 
    pars 
    (map (inline inlining) args) 
    (on_snd (inline inlining) br).
Proof.
  intros.
  unfold iota_red.
  erewrite inline_substl; last eassumption.
  rewrite -map_skipn map_rev //.
Qed.
Hint Rewrite inline_iota : inlining_rw_hints.



Lemma inline_map_fix_subst 
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining mfix :
  map (inline inlining) (fix_subst mfix) = fix_subst (map (map_def (inline inlining)) mfix).
Proof.
  unfold fix_subst.
  simple.
  remember #|mfix| as n eqn:heq.
  clear heq.
  induction n as [|? IH]; first reflexivity.
  rewrite map_cons /=; f_equal.
  now rewrite IH.
Qed.
Hint Rewrite inline_map_fix_subst : inlining_rw_hints.




Lemma inline_map_cofix_subst 
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining mfix :
  map (inline inlining) (cofix_subst mfix) = cofix_subst (map (map_def (inline inlining)) mfix).
Proof.
  unfold cofix_subst.
  simple.
  remember #|mfix| as n eqn:heq.
  clear heq.
  induction n as [|? IH]; first reflexivity.
  rewrite map_cons /=; f_equal.
  now rewrite IH.
Qed.
Hint Rewrite inline_map_cofix_subst : inlining_rw_hints.



Lemma inline_cunfold_fix
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining ctx mfix idx :
  wf_inlining ctx 0 inlining ->
  cunfold_fix (map (map_def (inline inlining)) mfix) idx =
  option_map (on_snd (inline inlining)) (cunfold_fix mfix idx).
Proof.
  intros.
  unfold cunfold_fix.
  rewrite nth_error_map.
  destruct (nth_error mfix idx); unfold on_snd; simpl; last reflexivity.
  erewrite inline_substl, inline_map_fix_subst; try easy.
Qed.
Hint Rewrite inline_cunfold_fix : inlining_rw_hints.


Lemma inline_cunfold_cofix
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining ctx mfix idx :
  wf_inlining ctx 0 inlining ->
  cunfold_cofix (map (map_def (inline inlining)) mfix) idx =
  option_map (on_snd (inline inlining)) (cunfold_cofix mfix idx).
Proof.
  intros.
  unfold cunfold_cofix.
  rewrite nth_error_map.
  destruct (nth_error mfix idx); unfold on_snd; simpl; last reflexivity.
  erewrite inline_substl, inline_map_cofix_subst; try easy.
Qed.
Hint Rewrite inline_cunfold_cofix : inlining_rw_hints.

Lemma inline_atom 
  (efl : EEnvFlags) (wfl : WcbvFlags) 
  inlining ctx e :
  atom ctx e ->
  atom 
    (inline_env inlining ctx).1
    (inline (inline_env inlining ctx).2 e).
Proof.
  destruct e; try (discriminate || easy); simpl.
  destruct args; now simple.
Qed.

Lemma inline_isLambda (wfl : WcbvFlags) inlining ctx v :
  value ctx v ->
  isLambda (inline (inline_env inlining ctx).2 v) = isLambda v.
Proof.
  move: v.
  apply value_values_ind; try easy.
  - intros [] atom_v; easy.
  - intros f [|? ?] ? ? ? ?; simple; try easy.
    rewrite 
      (negb_involutive_reverse (isLambda _))
      isLambda_mkApps //
      (negb_involutive_reverse (isLambda _))
      isLambda_mkApps //
      .
Qed.
Hint Rewrite inline_isLambda : inlining_rw_hints.



Lemma inline_isFix (wfl : WcbvFlags) inlining ctx v :
  value ctx v ->
  EAstUtils.isFix (inline (inline_env inlining ctx).2 v) =
  EAstUtils.isFix v.
Proof.
  move: v.
  apply value_values_ind; try easy.
  - intros [] atom_v; easy.
  - intros f [|? ?] ? ? ? ?; simple; try easy.
    rewrite 
      (negb_involutive_reverse (EAstUtils.isFix _))
      EAstUtils.nisFix_mkApps //
      (negb_involutive_reverse (EAstUtils.isFix _))
      EAstUtils.nisFix_mkApps //
    .
Qed.

Lemma inline_isFixApp (wfl : WcbvFlags) inlining ctx v :
  value ctx v ->
  EAstUtils.isFixApp (inline (inline_env inlining ctx).2 v) =
  EAstUtils.isFixApp v.
Proof.
  move: v.
  apply value_values_ind; try easy.
  - intros [] atom_v; easy.
  - intros f [|? ?] ? ? ? ?; simple; try easy.
    rewrite 
      !EAstUtils.isFixApp_mkApps 
      /EAstUtils.isFixApp
      !EAstUtils.head_tApp.
    inversion H; reflexivity.
Qed.

Lemma inline_isBox (wfl : WcbvFlags) inlining ctx v :
  value ctx v ->
  EAstUtils.isBox (inline (inline_env inlining ctx).2 v) =
  EAstUtils.isBox v.
Proof.
  move: v.
  apply value_values_ind; try easy.
  - intros [] atom_v; easy.
  - intros f [|? ?] ? ? ? ?; simple; try easy.
    rewrite 
      (negb_involutive_reverse (EAstUtils.isBox _))
      isBox_mkApps //
      (negb_involutive_reverse (EAstUtils.isBox _))
      isBox_mkApps //
    .
Qed.


Lemma inline_isConstructApp (wfl : WcbvFlags) inlining ctx v :
  value ctx v ->
  EAstUtils.isConstructApp (inline (inline_env inlining ctx).2 v) =
  EAstUtils.isConstructApp v.
Proof.
  move: v.
  apply value_values_ind; try easy.
  - intros [] atom_v; easy.
  - intros f [|? ?] ? ? ? ?; simple; try easy.
    rewrite 
      !EAstUtils.isConstructApp_mkApps 
      /EAstUtils.isConstructApp
      !EAstUtils.head_tApp.
    inversion H; reflexivity.
Qed.


Lemma inline_isPrimApp (wfl : WcbvFlags) inlining ctx v :
  value ctx v ->
  EAstUtils.isPrimApp (inline (inline_env inlining ctx).2 v) =
  EAstUtils.isPrimApp v.
Proof.
  move: v.
  apply value_values_ind; try easy.
  - intros [] atom_v; easy.
  - intros f [|? ?] ? ? ? ?; simple; try easy.
    rewrite 
      !EAstUtils.isPrimApp_mkApps 
      /EAstUtils.isPrimApp
      !EAstUtils.head_tApp.
    inversion H; reflexivity.
Qed.


Lemma inline_isLazyApp (wfl : WcbvFlags) inlining ctx v :
  value ctx v ->
  EAstUtils.isLazyApp (inline (inline_env inlining ctx).2 v) =
  EAstUtils.isLazyApp v.
Proof.
  move: v.
  apply value_values_ind; try easy.
  - intros [] atom_v; easy.
  - intros f [|? ?] ? ? ? ?; simple; try easy.
    rewrite 
      !EAstUtils.isLazyApp_mkApps 
      /EAstUtils.isLazyApp
      !EAstUtils.head_tApp.
    inversion H; reflexivity.
Qed.



Theorem inlining_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inlining (p : Transform.program _ term)
  (v : term),
  has_tApp ->
  has_tBox || ~~with_prop_case ->
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  let ip := inline_program inlining p in
  eval_eprogram wfl ip v' /\ v' = inline ip v.
Proof.
  intros efl wfl inlining [glob_ctx e] v htApp htBox [wf_glob_ctx wf_e] [eval_e];
  simpl in *; eexists; split; last reflexivity.
  constructor.
  unfold inline_program; simple.
  unfold inlined_program_inlinings; simple.
  set Σ' := (inline_env inlining glob_ctx).1.
  set inls := (inline_env inlining glob_ctx).2.
  assert (wf_inlining Σ' 0 inls) 
    by now apply wf_glob_inlining.
  induction eval_e; simple.
  - eapply eval_box; easy.
  - destruct_IHs. eapply eval_beta; try easy.
    now erewrite <-inline_csubst.
  - destruct_IHs.
    eapply eval_zeta; simple; try easy.
    erewrite <-inline_csubst; first assumption.
    now apply wf_glob_inlining.
  - destruct_IHs; simple.
    eapply eval_iota; subst Σ'; simple; try easy.
    + now rewrite e2.
    + now simple.
    + simple.
    + now erewrite inline_iota in *.
  - destruct_IHs; simple.
    eapply eval_iota_block; try easy; subst Σ'; try now simple.
    now erewrite inline_iota in *.
  - destruct_IHs; simpl in *.
    { assert (has_tBox) as htBox'.
      { destruct has_tBox, with_prop_case; simple; easy. }
      assert (
        forallb (wellformed glob_ctx 0) (repeat tBox #|n|)
      ).
      { move: htBox'; clear. induction n; simpl; now simple. }
      apply wellformed_substl; simple.
      subst.
      change n with (n, f4).1.
      change f4 with (n, f4).2 at 2.
      apply wf_e. now simple. }
    eapply eval_iota_sing; subst Σ'; subst; simple; try easy.
    change tBox with (inline inls tBox). simple.
    now erewrite <-inline_substl.
  - destruct_IHs; simple.
    eapply eval_fix; subst Σ'; simple; try easy.
    erewrite inline_cunfold_fix; now simple.
  - destruct_IHs; simple.
    eapply eval_fix_value; subst Σ'; simple; try easy.
    erewrite inline_cunfold_fix; now simple.
  - destruct_IHs; simple.
    eapply eval_fix'; subst Σ'; simple; try easy.
    erewrite inline_cunfold_fix; now simple.
  - destruct_IHs; simple.
    eapply eval_cofix_case; subst Σ'; simple; try easy.
    erewrite inline_cunfold_cofix; now simple.
  - destruct_IHs; simple.
    eapply eval_cofix_proj; subst Σ'; simple; try easy.
    erewrite inline_cunfold_cofix; now simple.
  - destruct_IHs.
    { rewrite /lookup_constant isdecl /= in wf_e.
      apply lookup_env_wellformed in isdecl; last assumption.
      rewrite /wf_global_decl e //= in isdecl. }
    unfold inline_clause_5.
    destruct (KernameMap.find (elt:=term) c inls) eqn:heq.
    + unfold inls in *.
      eapply inline_env_lookup in heq; try easy; last first.
      { destruct (KernameSet.mem c inlining) eqn:heq'; first easy.
        unshelve epose proof inline_env_lookup_no_inline_None _ _ _ _ _ _ wf_glob_ctx; try easy.
        now rewrite heq'. }
      rewrite 
        lookup_env_inline // isdecl 
        /inline_constant_decl /inline_global_decl
        /inline_constant_decl 
        /= e /=
        in heq.
      injection heq as heq; subst.
      easy.
    + econstructor; last eassumption.
      * unfold declared_constant. subst Σ'.
        rewrite lookup_env_inline // isdecl /= /inline_constant_decl e /=.
        reflexivity.
      * reflexivity.
  - destruct_IHs; simple.
    eapply eval_proj; subst Σ'; simple; try easy; now simple.
  - destruct_IHs; simple.
    eapply eval_proj_block; subst Σ'; simple; try easy; now simple.
  - destruct_IHs; simple.
    eapply eval_proj_prop; subst Σ'; now simple.
  - destruct_IHs; simple.
    eapply eval_construct; subst Σ'; now simple.
  - destruct_IHs; simple.
    eapply eval_construct_block; subst Σ'; simple; try easy.
    destruct cstr_as_blocks; last first.
    { destruct args; last easy. 
      inversion a; subst.
      constructor. }
    apply All2_All2_Set, All2_map.
    apply All2_over_undep in iha.
    unshelve eapply (All2_apply_dep_arrow _ iha).
    now simple.
  - destruct_IHs; simple.
    apply eval_app_cong; try easy.
    apply eval_to_value in eval_e1.
    unfold inls.
    rewrite 
      inline_isLambda //
      inline_isFixApp //
      inline_isFix //
      inline_isBox //
      inline_isConstructApp //
      inline_isPrimApp //
      inline_isLazyApp //
    .
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
  - destruct_IHs; simple.
    eapply eval_force; subst Σ'; now simple.
  - destruct_IHs; simple.
    eapply eval_atom; subst Σ'; simple.
    now apply inline_atom.
Qed.

Lemma find_inlining_not_declared 
  (efl : EEnvFlags) (wfl : WcbvFlags) inlining ctx name :
  wf_glob ctx ->
  (~ exists t, lookup_env ctx name = Some (ConstantDecl {|cst_body := Some t|})) ->
  KernameMap.find name (inline_env inlining ctx).2 = None.
Proof.
  induction ctx as [|[name' decl] ctx IH]; first easy.
  intros h; inversion h as [ | ? d ? wf_ctx wf_d fresh_name]; clear h; subst.
  intros h_nexists.
  simple.
  unfold inline_add.
  simple.
  destruct (KernameSet.mem name' inlining); simple; last first.
  { apply IH; first assumption.
    intros [t h].
    apply h_nexists.
    exists t.
    destruct (eqb_spec name name'); subst.
    { now apply lookup_env_Some_fresh in h. }
    assumption. }
  destruct decl as [[[?|]]|]; simple.
  - destruct (eqb_spec name name'); subst.
    + rewrite KernameMapFact.F.add_eq_o.
      { apply KernameMap.E.eq_refl. }
      exfalso. easy.
    + rewrite KernameMapFact.F.add_neq_o.
      { now rewrite Kername.compare_eq. }
      easy.
  - apply IH; first assumption.
    intros [t h].
    apply h_nexists.
    exists t.
    destruct (eqb_spec name name'); subst.
    { now apply lookup_env_Some_fresh in h. }
    assumption.
  - apply IH; first assumption.
    intros [t h].
    apply h_nexists.
    exists t.
    destruct (eqb_spec name name'); subst.
    { now apply lookup_env_Some_fresh in h. }
    assumption.
Qed.

Lemma find_inlining_fresh 
  (efl : EEnvFlags) (wfl : WcbvFlags) inlining ctx name :
  fresh_global name ctx ->
  KernameMap.find name (inline_env inlining ctx).2 = None.
Proof.
  induction ctx as [|[name' d] ctx IH]; first easy.
  simple.
  unfold fresh_global.
  rewrite Forall_cons_iff.
  fold (fresh_global name ctx).
  intros [h_diff h_fresh].
  simple.
  unfold inline_add.
  simple.
  destruct (KernameSet.mem name' inlining) eqn:heq; last easy.
  destruct d as [[[?|]]| ?]; simple; intros; try easy.
  rewrite KernameMapFact.F.add_neq_o; last easy.
  now rewrite Kername.compare_eq.
Qed.


Lemma inline_find_extends (efl : EEnvFlags) (wfl : WcbvFlags) inlining ctx ctx' (t : option term) :
  wf_glob ctx ->
  wf_glob ctx' ->
  extends ctx ctx' ->
  (forall p : {t' | t = Some t'},
  forall k, wellformed ctx k (proj1_sig p) ->
  inline (inline_env inlining ctx).2 (proj1_sig p) = 
  inline (inline_env inlining ctx').2 (proj1_sig p)) /\ 
  (forall name, isSome (lookup_env ctx name) ->
  KernameMap.find name (inline_env inlining ctx).2 = 
  KernameMap.find name (inline_env inlining ctx').2).
Proof.
  set decl_size := fun (d : global_decl) =>
    match d with
    | ConstantDecl {|cst_body := Some t|} => size t
    | _ => 1
    end.
  set my_size := 
    fun (p : (option term) * global_context) =>
    let s1 :=
      match p.1 with
      | None => 0
      | Some t => size t
      end
    in
    (s1 + list_size (decl_size ∘ snd) p.2).
  assert (well_founded (fun p1 p2 => my_size p1 < my_size p2))
  as wf_mysize_lt
  by now apply (well_founded_lt_compat _ my_size).
  move: t ctx ctx'.
  match goal with
  | |- forall (t : option term) (ctx : global_context), ?P => 
      pose myP := fun (t : option term) (ctx : global_context) => P
  end.
  apply (well_founded_induction_type_2 myP wf_mysize_lt).
  intros t ctx IH ctx' wf_ctx wf_ctx' ctx'_extends_ctx.
  split.
  { intros [t' ?] k wf_t; subst.
    destruct t'; unfold my_size in *; simple; try easy;
    try solve[
      f_equal;
      match goal with
      | |- inline _ ?t = inline _ ?t =>
        let H := fresh in 
        unshelve epose proof IH (Some t) ctx (ltac:(easy)) _ wf_ctx wf_ctx' ctx'_extends_ctx as [H _];
        epose proof H (exist _ eq_refl) _; easy
      end
    ].
    - simple. f_equal. 
      apply All_map_eq.
      simple.
      intros x h_in.
      unshelve epose proof IH (Some x) ctx _ _ wf_ctx wf_ctx' ctx'_extends_ctx as [? _].
      { assert (size x < (list_size size l)) 
        by now apply (In_size id).
        lia. }
      now eapply (H (exist x eq_refl)).
    - unfold inline_clause_5.
      unshelve epose proof IH None _ _ _ wf_ctx wf_ctx' ctx'_extends_ctx as [_ ->]; try easy.
      unfold lookup_constant in wf_t.
      now destruct (lookup_env ctx k0).
    - f_equal.
      apply All_map_eq.
      destruct cstr_as_blocks; simple; last now destruct args.
      simple.
      intros x h_in.
      unshelve epose proof IH (Some x) ctx _ _ wf_ctx wf_ctx' ctx'_extends_ctx as [? _].
      { assert (size x < (list_size size args)) 
        by now apply (In_size id).
        lia. }
      now eapply (H (exist x eq_refl)).
    - f_equal.
      { match goal with
        | |- inline _ ?t = inline _ ?t =>
          let H := fresh in 
          unshelve epose proof IH (Some t) ctx (ltac:(easy)) _ wf_ctx wf_ctx' ctx'_extends_ctx as [H _];
          epose proof H (exist _ eq_refl) _; easy
        end. }
      unfold on_snd.
      apply All_map_eq.
      simple.
      intros x h_in.
      f_equal.
      unshelve epose proof IH (Some x.2) ctx _ _ wf_ctx wf_ctx' ctx'_extends_ctx as [H _].
      { assert (size x.2 < (list_size (size ∘ snd) brs)) 
        by now apply (In_size snd).
        lia. }
      now eapply (H (exist x.2 eq_refl)).
    - unfold map_def, wf_fix in *.
      simple.
      f_equal.
      apply All_map_eq.
      simple.
      intros x h_in.
      f_equal.
      unshelve epose proof IH (Some (dbody x)) ctx _ _ wf_ctx wf_ctx' ctx'_extends_ctx as [H _].
      { assert (size (dbody x) < (list_size (size ∘ dbody) mfix)) 
        by now apply (In_size dbody).
        lia. }
      now eapply (H (exist (dbody x) eq_refl)).
    - unfold map_def, wf_fix in *.
      simple.
      f_equal.
      apply All_map_eq.
      simple.
      intros x h_in.
      f_equal.
      unshelve epose proof IH (Some (dbody x)) ctx _ _ wf_ctx wf_ctx' ctx'_extends_ctx as [H _].
      { assert (size (dbody x) < (list_size (size ∘ dbody) mfix)) 
        by now apply (In_size dbody).
        lia. }
      now eapply (H (exist (dbody x) eq_refl)).
    - unfold 
        test_prim, map_prim, 
        test_array_model, map_array_model in *; simple.
      destruct prim as [? [| | |]]; simple; try easy.
      do 4 f_equal.
      { assert (
          size (array_default a) <= 
          prim_size size (Primitive.primArray; primArrayModel a)
        ) by now destruct a; unfold prim_size; simple.
        match goal with
        | |- inline _ ?t = inline _ ?t =>
          let H := fresh in 
          unshelve epose proof IH (Some t) ctx (ltac:(easy)) _ wf_ctx wf_ctx' ctx'_extends_ctx as [H _];
          epose proof H (exist _ eq_refl) _; easy
        end. }
      apply All_map_eq.
      simple.
      intros x' h_in.
      unshelve epose proof IH (Some x') ctx _ _ wf_ctx wf_ctx' ctx'_extends_ctx as [? _].
      { unfold prim_size; simple.
        assert (size x' < (list_size size (array_value a))) 
        by now apply (In_size id).
        lia. }
      now eapply (H (exist x' eq_refl)). }
  { intros name h_lookup.
    destruct ctx as [|[name' decl] ctx]; first easy.
    move: wf_ctx.
    intros h; inversion h as [ | ? d ? wf_ctx wf_d fresh_name]; clear h; subst.
    simple.
    unfold inline_add.
    simple.
    assert (extends ctx ctx').
    { intros n ? h_lookup_n.
      apply ctx'_extends_ctx.
      simple.
      destruct (eqb_spec n name'); subst; last easy.
      now rewrite lookup_env_fresh_None in h_lookup_n. }
    destruct (eqb_spec name name'); subst.
    - simple.
      destruct (KernameSet.mem name' inlining) eqn:heq.
      + simple.
        destruct decl as [[[t'|]]|]; simple.
        * rewrite KernameMapFact.F.add_eq_o.
          { apply KernameMap.E.eq_refl. }
          assert (lookup_env ctx' name' = Some (ConstantDecl {| cst_body := Some t' |})).
          { apply ctx'_extends_ctx. simple.
            now rewrite eq_kername_refl. }
          symmetry.
          rewrite
            inline_env_lookup // 
            lookup_env_inline // H0 /= 
            /inline_constant_decl //=.
          do 3 f_equal.
          symmetry.
          unfold my_size in IH; simple.
          unshelve epose proof IH (Some t') ctx _ ctx' wf_ctx wf_ctx' _ as [H' _]; try easy.
          f_equal.
          eapply (H' (exist t' eq_refl)); easy.
        * rewrite find_inlining_fresh //.
          rewrite find_inlining_not_declared //.
          intros [t' h].
          assert (lookup_env ctx' name' = Some (ConstantDecl {| cst_body := None|})); last easy.
          apply ctx'_extends_ctx.
          now rewrite /= eq_kername_refl.
        * assert (lookup_env ctx' name' = Some (InductiveDecl m)).
          { apply ctx'_extends_ctx.
            now rewrite /= eq_kername_refl. }
          rewrite find_inlining_fresh // find_inlining_not_declared //.
          now intros [??].
      + intros.
        assert (~~ KernameSet.mem name' inlining)
        by rewrite heq //.
        rewrite !inline_env_lookup_no_inline_None //.
    - unfold my_size, myP in *.
      unshelve epose proof IH None ctx _ _ _ _ _ as [? ?]; simple; first easy.
      destruct (KernameSet.mem name' inlining) eqn:heq; last easy.
      destruct decl as [[[|]]|]; simple; try easy.
      rewrite KernameMapFact.F.add_neq_o; last easy.
      now rewrite Kername.compare_eq.
  }
Qed.


Lemma find_extends (efl : EEnvFlags) (wfl : WcbvFlags) inlining ctx ctx' name :
  wf_glob ctx ->
  wf_glob ctx' ->
  extends ctx ctx' ->
  isSome (lookup_env ctx name) ->
  KernameMap.find name (inline_env inlining ctx).2 = 
  KernameMap.find name (inline_env inlining ctx').2.
Proof.
  intros.
  eapply inline_find_extends; try easy.
  exact None.
Qed.

Lemma inline_extends (efl : EEnvFlags) (wfl : WcbvFlags) inlining ctx ctx' k t :
  wf_glob ctx ->
  wf_glob ctx' ->
  extends ctx ctx' ->
  wellformed ctx k t ->
  inline (inline_env inlining ctx).2 t = 
  inline (inline_env inlining ctx').2 t.
Proof.
  intros.
  unshelve epose proof inline_find_extends efl wfl inlining ctx ctx' (Some t) _ _ _ as [H' _]; try assumption.
  now eapply (H' (exist t eq_refl)).
Qed. 

Lemma extends_inline_env (efl : EEnvFlags) (wfl : WcbvFlags) inlining ctx ctx' :
  wf_glob ctx ->
  wf_glob ctx' ->
  extends ctx ctx' ->
  extends (inline_env inlining ctx).1 (inline_env inlining ctx').1.
Proof.
  intros ? ? ? name decl heq.
  rewrite lookup_env_inline // in heq.
  destruct (lookup_env ctx name) as [d|]eqn:heq';
  last easy.
  simpl in heq.
  injection heq as <-.
  rewrite lookup_env_inline // (H1 _ _ heq') /inline_global_decl.
  destruct d as [[[t|]]|]; [|easy..].
  simple.
  rewrite /inline_constant_decl /= (inline_extends _ _ _ ctx ctx' 0) //.
  now eapply lookup_env_wf.
Qed.

Definition extends_inlined_eprogram (p q : inlined_program) :=
  extends p.1.1 q.1.1 /\ p.2 = q.2.
