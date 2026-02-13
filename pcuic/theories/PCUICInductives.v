(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSigmaCalculus PCUICInstDef PCUICInstConv PCUICContextSubst
     PCUICRenameDef PCUICRenameConv PCUICRenameTyp
     PCUICSubstitution PCUICOnFreeVars PCUICClosed PCUICClosedConv PCUICClosedTyp
     PCUICCumulativity PCUICGeneration PCUICReduction PCUICWellScopedCumulativity
     PCUICEquality PCUICConfluence PCUICParallelReductionConfluence
     PCUICContextConversion PCUICUnivSubstitutionConv
     PCUICUnivSubstitutionTyp
     PCUICConversion PCUICGlobalEnv PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICWfUniverses PCUICSpine.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Arguments subst_context !s _ !Γ.
Arguments it_mkProd_or_LetIn !l _.

Lemma nth_error_rev_map {A B} (f : A -> B) l i :
  i < #|l| ->
  nth_error (rev_map f l) (#|l| - S i) =
  option_map f (nth_error l i).
Proof.
  move=> Hi.
  rewrite rev_map_spec. rewrite -(length_map f l) -nth_error_rev ?length_map //.
  now rewrite nth_error_map.
Qed.

#[global]
Hint Resolve conv_ctx_refl : pcuic.

(* Definition branch_type ind mdecl (idecl : one_inductive_body) params u p i (br : constructor_body) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let '(id, t, ar) := br in
  let ty := subst0 inds (subst_instance u t) in
  match instantiate_params (subst_instance u mdecl.(ind_params)) params ty with
  | Some ty =>
  let '(sign, ccl) := decompose_prod_assum [] ty in
  let nargs := List.length sign in
  let allargs := snd (decompose_app ccl) in
  let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
  let cstr := tConstruct ind i u in
  let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
  Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
| None => None
end.

Lemma nth_branches_type ind mdecl idecl args u p i t btys : map_option_out (build_branches_type ind mdecl idecl args u p) = Some btys ->
  nth_error btys i = Some t ->
  (∑ br, (nth_error idecl.(ind_ctors) i = Some br) /\
    (branch_type ind mdecl idecl args u p i br = Some t)).
Proof.
  intros Htys Hnth.
  eapply nth_map_option_out in Htys; eauto.
Qed.

Lemma build_branches_type_lookup {cf:checker_flags} Σ Γ ind mdecl idecl cdecl pars u p (brs :  list (nat * term)) btys :
  declared_inductive Σ.1 ind mdecl idecl ->
  map_option_out (build_branches_type ind mdecl idecl pars u p) = Some btys ->
  All2 (fun br bty => (br.1 = bty.1) * (Σ ;;; Γ |- br.2 : bty.2))%type brs btys ->
  forall c, nth_error (ind_ctors idecl) c = Some cdecl ->
  ∑ nargs br bty,
    (nth_error brs c = Some (nargs, br)) *
    (nth_error btys c = Some (nargs, bty)) *
    (Σ ;;; Γ |- br : bty) * (branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty)).
Proof.
  intros decli Hbrs Hbrtys c Hc.
  destruct decli as [declmi decli].
  pose proof (map_option_out_length _ _ Hbrs) as hlen.
  rewrite mapi_length in hlen.
  assert (H:∑ t', nth_error btys c = Some t').
  pose proof (All2_length _ _ Hbrtys) as e. eapply nth_error_Some_length in Hc.
  destruct (nth_error_spec btys c). eexists; eauto. exfalso; lia.
  destruct H as [[argty bty] Hbty].
  assert (H:∑ t', nth_error brs c = Some t').
  pose proof (All2_length _ _ Hbrtys) as e. eapply nth_error_Some_length in Hc.
  destruct (nth_error_spec brs c). eexists; eauto. exfalso; lia.
  destruct H as [[argbr br] Hbr].
  eapply All2_nth_error in Hbrtys; eauto.
  destruct Hbrtys as [Harg tybr]. simpl in *. subst.
  eapply nth_branches_type in Hbrs; eauto.
  destruct Hbrs as [[[id brty] nargs] [Hnth' Hbrty]].
  exists argty, br, bty.
  intuition auto. rewrite -Hbrty. f_equal.
  congruence.
Qed.

Import PCUICEnvironment.

Lemma branch_type_spec {cf:checker_flags} Σ ind mdecl idecl cdecl pars u p c nargs bty :
  declared_inductive Σ ind mdecl idecl ->
  forall (omib : on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl),
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  forall cdecl (cs : on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind ind) idecl (ind_indices idecl) cdecl cdecl),
  branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty) ->
  nargs = context_assumptions cdecl.(cstr_args) /\
  forall parsubst,
  context_subst (subst_instance u (PCUICAst.ind_params mdecl)) pars parsubst ->
  let indsubst := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  let nargs' := #|cdecl.(cstr_args)| in
  let npars := #|ind_params mdecl| in
  let substargs := (subst_context parsubst 0
    (subst_context indsubst npars (map_context (subst_instance u) cdecl.(cstr_args)))) in
  bty =
  it_mkProd_or_LetIn substargs
    (mkApps (lift0 nargs' p)
      (map (subst parsubst nargs' ∘ subst indsubst (nargs' + npars) ∘ subst_instance u) cdecl.(cstr_indices) ++
       [mkApps (tConstruct ind c u)
         (map (lift0 nargs') pars ++
          to_extended_list substargs)])).
Proof.
  move=> decli onmib [] indices ps aeq onAr indsorts onC onP inds onIndices.
  intros cs onc brty. simpl in *.
  simpl in onc.
  clear onP.
  assert(lenbodies: inductive_ind ind < #|ind_bodies mdecl|).
  { destruct decli as [_ Hnth]. now apply nth_error_Some_length in Hnth. }
  clear decli.
  destruct onc. simpl in *.
  destruct cs as [args indi csort] => /=. simpl in *.
  rewrite cstr_eq in on_ctype.
  unfold branch_type in brty.
  destruct cdecl as [[id ty] nargs'']. simpl in * |-.
  destruct instantiate_params eqn:Heq => //.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [? [? ?]]]]].
  subst t. move: H.
  rewrite {1}cstr_eq subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
  rewrite -(subst_context_length (PCUICTyping.inds (inductive_mind ind) u (ind_bodies mdecl)) 0).
  rewrite decompose_prod_n_assum_it_mkProd.
  move=> H;noconf H.
  move: brty.

  rewrite !subst_context_length !subst_instance_length
    subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite subst_context_length subst_instance_length Nat.add_0_r.
  rewrite subst_instance_mkApps !subst_mkApps.
  rewrite Nat.add_0_r.
  assert((subst s' #|args|
  (subst
     (PCUICTyping.inds (inductive_mind ind) u
        (PCUICAst.ind_bodies mdecl))
     (#|args| + #|PCUICAst.ind_params mdecl|)
     (subst_instance u cstr_concl_head))) = tInd ind u).
  rewrite /head. simpl subst_instance.
  erewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| -  S (inductive_ind ind))); try lia.
  2:{ rewrite inds_spec nth_error_rev.
      rewrite List.length_rev mapi_length; try lia.
      rewrite List.rev_involutive List.length_rev mapi_length; try lia.
      rewrite nth_error_mapi. simpl.
      elim: (nth_error_spec _ _). simpl. reflexivity.
      lia. }
  simpl. f_equal. destruct ind as [mind k]=> /=.
  f_equal. simpl in lenbodies. lia.
  rewrite H.
  rewrite decompose_prod_assum_it_mkProd ?is_ind_app_head_mkApps //.
  rewrite decompose_app_mkApps //.
  move=> Heq; simpl in Heq; move: Heq.
  rewrite !map_map_compose map_app.
  rewrite chop_n_app.
  rewrite length_map to_extended_list_k_length.
  by rewrite (onmib.(onNpars)).

  move=> [=] Hargs Hbty. subst nargs. split;auto. rewrite -Hbty.
  clear Hbty bty.
  rewrite app_nil_r.
  move=>parsubst Hpars.
  pose proof (make_context_subst_spec _ _ _ H0) as csubst.
  rewrite rev_involutive in csubst.
  pose proof (context_subst_fun csubst Hpars). subst s'. clear csubst.
  f_equal.
  rewrite !subst_context_length subst_instance_length.
  f_equal. f_equal. f_equal. f_equal.
  f_equal. rewrite -(map_map_compose _ _ _ _ (subst _ _ ∘ subst _ _)).
  rewrite subst_instance_to_extended_list_k.
  rewrite -map_map_compose.
  rewrite -to_extended_list_k_map_subst. rewrite subst_instance_length; lia.
  now rewrite (subst_to_extended_list_k _ _ pars).
Qed. *)

Lemma wf_arities_context_inst {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {mind mdecl u} :
  declared_minductive Σ mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (arities_context mdecl.(ind_bodies))@[u].
Proof.
  intros decli cu.
  unshelve eapply declared_minductive_to_gen in decli; eauto.
  eapply wf_local_instantiate; tea. cbn.
  eapply wf_arities_context; tea.
  unshelve eapply declared_minductive_from_gen; eauto.
Qed.


Lemma instantiate_inds {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} {u mind mdecl} :
  declared_minductive Σ.1 mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subst_instance u
     (inds mind (abstract_instance (PCUICEnvironment.ind_universes mdecl))
        (ind_bodies mdecl)) =
  inds mind u (ind_bodies mdecl).
Proof.
  intros declm cu.
  rewrite subst_instance_inds.
  f_equal. eapply subst_instance_id_mdecl; eauto.
Qed.

Lemma subst_inds_concl_head ind u mdecl (arity : context) :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance u head)
  = tInd ind u.
Proof.
  intros.
  subst head. simpl subst_instance.
  rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
  subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
  elim nth_error_spec.
  + intros. simpl.
    f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
  + rewrite List.length_rev. lia.
Qed.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).

  Lemma on_minductive_wf_params_indices : wf_local (Σ, ind_universes mdecl) (ind_params mdecl ,,, ind_indices idecl).
  Proof using decli wfΣ.
    eapply on_declared_inductive in decli as [onmind oib].
    pose proof (oib.(onArity)).
    rewrite oib.(ind_arity_eq) in X.
    destruct X as (_ & s & Hs & _).
    rewrite -it_mkProd_or_LetIn_app in Hs.
    eapply it_mkProd_or_LetIn_wf_local in Hs.
    now rewrite app_context_nil_l in Hs.
  Qed.

  Lemma declared_inductive_type :
    ind_type idecl = it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl)).
  Proof using decli wfΣ.
    eapply on_declared_inductive in decli as [onmind oib].
    rewrite oib.(ind_arity_eq).
    now rewrite -it_mkProd_or_LetIn_app.
  Qed.

End OnInductives.

Lemma isType_intro {cf:checker_flags} {Σ Γ T s} : Σ ;;; Γ |- T : tSort s -> isType Σ Γ T.
Proof.
  eapply has_sort_isType.
Qed.
#[global]
Hint Resolve isType_intro : pcuic.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).

  Lemma on_minductive_wf_params_indices_inst (u : Instance.t) :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ (subst_instance u (ind_params mdecl ,,, ind_indices idecl)).
  Proof using decli wfΣ.
    intros.
    unshelve eapply declared_inductive_to_gen in decli; eauto.
    eapply (wf_local_instantiate _ (proj1 decli)); eauto.
    eapply on_minductive_wf_params_indices.
    unshelve eapply declared_inductive_from_gen; eauto.
  Qed.

  Lemma on_inductive_inst Γ u :
    wf_local Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isTypeRel Σ Γ (it_mkProd_or_LetIn (subst_instance u (ind_params mdecl ,,, idecl.(ind_indices)))
          (tSort (subst_instance_sort u idecl.(ind_sort)))) rel_of_Type.
  Proof using decli wfΣ.
    move=> wfΓ cext.
    destruct (on_declared_inductive decli) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    rewrite oib.(ind_arity_eq) in ar.
    eapply lift_typing_weaken_ctx with (Γ := []) => //.
    rewrite -(subst_instance_it_mkProd_or_LetIn u _ (tSort _)).
    rewrite -it_mkProd_or_LetIn_app in ar.
    eapply (lift_typing_subst_instance_decl Σ [] _ _ (InductiveDecl mdecl) u wfΣ) in ar; cbn in ar; tas.
    unshelve eapply declared_inductive_to_gen in decli; eauto.
  Qed.

  Lemma declared_inductive_valid_type Γ u :
    wf_local Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isTypeRel Σ Γ (subst_instance u idecl.(ind_type)) rel_of_Type.
  Proof using decli wfΣ.
    move=> wfΓ cext.
    destruct (on_declared_inductive decli) as [onmind oib].
    rewrite oib.(ind_arity_eq).
    rewrite -it_mkProd_or_LetIn_app subst_instance_it_mkProd_or_LetIn /=.
    now apply on_inductive_inst.
  Qed.

  Local Definition oi := (on_declared_inductive decli).1.
  Local Definition oib := (on_declared_inductive decli).2.

  Lemma on_inductive_sort : wf_sort (Σ.1, ind_universes mdecl) (ind_sort idecl).
  Proof using decli wfΣ.
    pose proof (oib.(onArity)) as ar.
    rewrite oib.(ind_arity_eq) in ar.
    destruct ar as (_ & s & ar & _).
    eapply typing_wf_universes in ar; auto.
    move/andP: ar => [].
    rewrite wf_universes_it_mkProd_or_LetIn => /andP [] _.
    now rewrite wf_universes_it_mkProd_or_LetIn => /andP [] _ /= /wf_sort_reflect.
  Qed.

  Lemma on_inductive_sort_inst u :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_sort Σ (subst_instance u (ind_sort idecl)).
  Proof using decli wfΣ.
    generalize on_inductive_sort => wf.
    destruct Σ. intros cu.
    eapply wf_sort_instantiate; eauto.
    now eapply consistent_instance_ext_wf.
  Qed.

  Lemma nth_errror_arities_context decl :
    nth_error (arities_context (ind_bodies mdecl)) (#|ind_bodies mdecl| - S (inductive_ind ind)) = Some decl ->
    decl.(decl_type) = idecl.(ind_type).
  Proof using decli.
    unfold arities_context.
    rewrite nth_error_rev_map.
    destruct decli as [declm decli'].
    now apply nth_error_Some_length in decli'.
    destruct nth_error eqn:Heq; try discriminate.
    destruct decli. rewrite H0 in Heq. noconf Heq.
    simpl. move=> [] <-. now simpl.
  Qed.

  Lemma isType_mkApps_Ind {Γ puinst args inst} :
    consistent_instance_ext Σ (ind_universes mdecl) puinst ->
    spine_subst Σ Γ args inst (subst_instance puinst (ind_params mdecl ,,, ind_indices idecl)) ->
    Σ ;;; Γ |- mkApps (tInd ind puinst) args : tSort (subst_instance puinst (ind_sort idecl)).
  Proof using decli wfΣ.
    intros cu sp.
    eapply type_mkApps; tea.
    econstructor; eauto. apply sp.
    rewrite (declared_inductive_type decli).
    rewrite subst_instance_it_mkProd_or_LetIn.
    eapply wf_arity_spine_typing_spine; tea.
    split.
    rewrite -subst_instance_it_mkProd_or_LetIn.
    rewrite -(declared_inductive_type decli).
    eapply isTypeRel_isType, declared_inductive_valid_type; tea.
    apply sp.
    eapply arity_spine_it_mkProd_or_LetIn_Sort.
    2:reflexivity. 2:exact sp.
    now eapply on_inductive_sort_inst.
  Qed.
End OnInductives.

(** * Projections *)

Fixpoint projs_inst ind npars k x : list term :=
  match k with
  | 0 => []
  | S k' => tProj (mkProjection ind npars k') x :: projs_inst ind npars k' x
  end.

Lemma subst_instance_projs u i p n :
  map (subst_instance u) (projs i p n) = projs i p n.
Proof.
  induction n; simpl; auto. f_equal; auto.
Qed.

Lemma projs_inst_subst s k ind pars arg t :
  map (subst s k) (projs_inst ind pars arg t)  =
  projs_inst ind pars arg (subst s k t).
Proof.
  induction arg; simpl; auto.
  f_equal; auto.
Qed.

Lemma projs_inst_skipn {ind pars arg t} n :
  skipn n (projs_inst ind pars arg t) = projs_inst ind pars (arg - n) t.
Proof.
  induction arg in n |- *; simpl; auto.
  - now rewrite skipn_nil.
  - destruct n as [|n']; [rewrite skipn_0|rewrite skipn_S]; [done|].
    rewrite IHarg /= //.
Qed.

Lemma untyped_subslet_projs {cf:checker_flags} (Σ : global_env_ext) i mdecl idecl :
  forall (wfΣ : wf Σ.1)
  (Hdecl : declared_inductive Σ.1 i mdecl idecl),
  match ind_ctors idecl return Type with
  | [cs] =>
    on_projections mdecl (inductive_mind i) (inductive_ind i)
     idecl (ind_indices idecl) cs ->
     forall Γ t u,
     let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
     untyped_subslet Γ
     (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cs)) t)
     (smash_context []
        (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
           #|ind_params mdecl| (subst_instance u (cstr_args cs))))
  | _ => True
  end.
Proof.
  intros wfΣ Hdecl.
  destruct ind_ctors as [|cs []] eqn:Heq; trivial.
  intros onp. simpl. intros Γ t u.
  rewrite (smash_context_subst []).
  destruct onp.
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cstr_args cs)). lia.
  clear on_projs_all.
  induction (cstr_args cs) as [|[? [] ?] ?].
  - simpl. constructor.
  - simpl. apply IHc. now simpl in H.
  - simpl. rewrite smash_context_acc /=.
    rewrite subst_context_snoc.
    rewrite /subst_decl {2}/map_decl /=.
    simpl in H. constructor. apply IHc. lia.
Qed.


Lemma skipn_projs n i npars k :
  skipn n (projs i npars k) = projs i npars (k - n).
Proof.
  induction k in n |- *; simpl.
  - now rewrite skipn_nil.
  - destruct n. now rewrite skipn_0.
    now  rewrite skipn_S.
Qed.

Lemma subst_projs_inst ind npars k x : map (subst0 [x]) (projs ind npars k) = projs_inst ind npars k x.
Proof.
  induction k; simpl; auto. unfold Nat.sub. simpl.
  rewrite lift0_id. f_equal; auto.
Qed.

Lemma projs_inst_length ind npars k x : #|projs_inst ind npars k x| = k.
Proof. induction k; simpl; auto. lia. Qed.

#[global]
Hint Rewrite projs_inst_length : len.

Lemma projs_inst_lift ind npars k x n :
  projs_inst ind npars k (lift0 n x) =
  map (lift0 n) (projs_inst ind npars k x).
Proof.
  induction k; simpl; auto.
  f_equal; auto.
Qed.

Lemma projs_subst_instance u ind npars k :
  map (subst_instance u) (projs ind npars k) = projs ind npars k.
Proof.
  induction k; simpl; auto. f_equal; auto.
Qed.

Lemma projs_subst_above s (n : nat) ind npars k : n > 0 ->
  map (subst s n) (projs ind npars k) = projs ind npars k.
Proof.
  induction k; simpl; auto. intros.
  f_equal; auto. elim: Nat.leb_spec => //; lia.
Qed.

Lemma nth_error_projs_inst ind npars k x n :
  n < k ->
  nth_error (projs_inst ind npars k x) n = Some (tProj (mkProjection ind npars (k - S n)) x).
Proof.
  induction k in n |- *; simpl; auto. lia.
  destruct n.
  + simpl. now rewrite Nat.sub_0_r.
  + intros Hlt. simpl. apply IHk; lia.
Qed.


(* k is the projection number: 0 is the first argument *)
Definition projection_type mdecl ind k ty :=
  let u := abstract_instance (PCUICEnvironment.ind_universes mdecl) in
  let indsubst := inds (inductive_mind ind) u (ind_bodies mdecl) in
  let projsubst := projs ind (ind_npars mdecl) k in
  subst indsubst (S (ind_npars mdecl))
      (subst0 projsubst (lift 1 k
        (subst (extended_subst (ind_params mdecl) 0) k
          (lift (context_assumptions (ind_params mdecl)) (k + #|ind_params mdecl|)
          ty)))).

Definition projection_type' mdecl ind k ty :=
  let u := abstract_instance (PCUICEnvironment.ind_universes mdecl) in
  let indsubst := inds (inductive_mind ind) u (ind_bodies mdecl) in
  let projsubst := projs ind (ind_npars mdecl) k in
  (subst0 projsubst
    (subst (extended_subst (ind_params mdecl) 0) (S k)
    (lift 1 k (subst indsubst (k + #|ind_params mdecl|) ty)))).

Definition projection_decls_type mdecl ind k ty :=
  let u := abstract_instance (PCUICEnvironment.ind_universes mdecl) in
  let indsubst := inds (inductive_mind ind) u (ind_bodies mdecl) in
  let projsubst := projs ind (ind_npars mdecl) k in
  subst indsubst (S (ind_npars mdecl))
      (subst0 projsubst (lift 1 k ty)).

Lemma on_projections_decl {cf:checker_flags} {mdecl ind idecl cs} :
  let u := abstract_instance (ind_universes mdecl) in
  on_projections mdecl (inductive_mind ind) (inductive_ind ind) idecl (idecl.(ind_indices)) cs ->
  Alli (fun i decl =>
    ∑ pdecl,
      (nth_error (ind_projs idecl) (context_assumptions (cstr_args cs) - S i) = Some pdecl))
    0 (smash_context [] cs.(cstr_args)).
Proof.
  intros.
  destruct X as [_ _ _ on_projs_all on_projs].
  eapply forall_nth_error_Alli.
  intros.
  pose proof (snd (nth_error_Some' (ind_projs idecl) (context_assumptions (cstr_args cs) - S i))).
  apply X. eapply nth_error_Some_length in H.
    autorewrite with len in H. simpl in H; lia.
Qed.

Record wf_subslet {cf} Σ Γ s Δ :=
  { wf_subslet_ctx : wf_local Σ (Γ ,,, Δ);
    wf_subslet_subslet :> subslet Σ Γ s Δ }.

Lemma wf_subslet_dom {cf} {Σ Γ s Δ} :
  wf_subslet Σ Γ s Δ -> wf_local Σ Γ.
Proof.
  intros [wf _]. now eapply All_local_env_app_inv in wf.
Qed.

Lemma subst_id s Γ t :
  closedn #|s| t ->
  assumption_context Γ ->
  s = List.rev (to_extended_list Γ) ->
  subst s 0 t = t.
Proof.
  intros cl ass eq.
  autorewrite with sigma.
  rewrite -{2}(subst_ids t).
  eapply inst_ext_closed; eauto.
  intros.
  unfold ids, subst_consn. simpl.
  destruct (snd (nth_error_Some' s x) H). rewrite e.
  subst s.
  rewrite /to_extended_list /to_extended_list_k in e.
  rewrite List.length_rev in cl, H. autorewrite with len in *.
  rewrite reln_alt_eq in e.
  rewrite app_nil_r List.rev_involutive in e.
  clear -ass e. revert e.
  rewrite -{2}(Nat.add_0_r x).
  generalize 0.
  induction Γ in x, ass, x0 |- * => n.
  - simpl in *. rewrite nth_error_nil => //.
  - depelim ass; simpl.
    destruct x; simpl in *; try congruence.
    move=> e; specialize (IHΓ ass); simpl in e.
    specialize (IHΓ _ _ _ e). subst x0. f_equal. lia.
Qed.

Lemma isType_it_mkProd_or_LetIn_inv {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ T} :
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  isType Σ (Γ ,,, Δ) T.
Proof.
  intros HT; apply lift_sorting_it_impl_gen with HT => // Hs.
  now eapply inversion_it_mkProd_or_LetIn in Hs.
Qed.

Lemma isType_it_mkProd_or_LetIn_subst {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ args inst T} :
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  spine_subst Σ Γ args inst Δ ->
  isType Σ Γ (subst0 inst T).
Proof.
  intros isty sp.
  eapply isType_subst. exact sp.
  now eapply isType_it_mkProd_or_LetIn_inv in isty.
Qed.

Definition projection_context_gen ind mdecl idecl :=
  let u := abstract_instance (ind_universes mdecl) in
  smash_context [] (ind_params mdecl),,
  vass ({| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |})
      (mkApps (tInd ind u) (to_extended_list (smash_context [] (ind_params mdecl)))).

Definition projection_arg_ctx ind mdecl cdecl p :=
  let indsubst := inds (inductive_mind ind) (abstract_instance (ind_universes mdecl)) mdecl.(ind_bodies) in
  subst_context (extended_subst (ind_params mdecl) 0) 1
    (lift_context 1 0
        (subst_context indsubst #|ind_params mdecl|
          (skipn (context_assumptions (cstr_args cdecl) - p)
              (smash_context [] (cstr_args cdecl))))).

Definition projection_context ind mdecl idecl u :=
  smash_context [] (subst_instance u (ind_params mdecl)),,
  vass ({| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |})
      (mkApps (tInd ind u) (to_extended_list (smash_context [] (subst_instance u (ind_params mdecl))))).

Lemma IHup {P : nat -> Type} i (H : forall i', i' < i -> P i') :
  forall i', S i' < S i -> P i'.
Proof.
  intros. apply H. lia.
Qed.

Lemma subslet_extended_subst {cf:checker_flags} Σ Δ :
  wf Σ.1 ->
  wf_local Σ Δ ->
  subslet Σ (smash_context [] Δ) (extended_subst Δ 0) Δ.
Proof.
  move=> wfΣ wfΔ.
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; auto; depelim wfΔ.
  * constructor.
  * apply unlift_TermTyp in l.
    rewrite extended_subst_length. rewrite lift_closed. fvs.
    constructor. auto. specialize (IHΔ wfΔ).
    eapply weaken_ctx in l. 3:eapply wf_local_smash_context; eauto. 2:auto.
    eapply (substitution (Δ := [])) in l. eapply l. all:auto.
  * rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    eassert (isTypeRel Σ (smash_context [] Δ) (subst0 (extended_subst Δ 0) decl_type) _).
    { apply lift_sorting_it_impl_gen with l => // Hs.
      eapply weaken_ctx in Hs. 3:eapply wf_local_smash_context; eauto. 2:auto.
      eapply (substitution (Δ := [])) in Hs. eapply Hs. all:auto. }
    rewrite lift_closed. fvs.
    rewrite (lift_extended_subst _ 1).
    rewrite -{4}(closed_ctx_lift 1 0 Δ); fvs.
    constructor.
    { eapply (subslet_lift _ [_]); eauto.
      constructor; tas. eapply wf_local_smash_context; auto. }
    { eapply refine_type.
      econstructor.
      rewrite smash_context_acc /=. constructor; tas.
      apply wf_local_smash_context; auto.
      reflexivity.
      simpl.
      rewrite distr_lift_subst. f_equal.
      rewrite lift_closed //. autorewrite with len; fvs. }
Qed.

Lemma context_subst_to_extended_list_k {cf:checker_flags} Σ Δ :
  wf Σ.1 ->
  wf_local Σ Δ ->
  context_subst Δ
    (map (subst0 (extended_subst Δ 0)) (to_extended_list_k Δ 0))
      (extended_subst Δ 0).
Proof.
  move=> wfΣ wfΔ.
  generalize 0 at 1 4.
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; auto;
  depelim wfΔ.
  * apply unlift_TermTyp in l.
    intros n. rewrite extended_subst_length. rewrite lift_closed. fvs.
    rewrite (reln_lift 1 0).
    rewrite map_map_compose map_subst_lift1.
    autorewrite with len.
    constructor. apply IHΔ; auto.
  * intros n. rewrite reln_acc.
    simpl.
    rewrite reln_acc /= map_app app_nil_r.
    rewrite (reln_lift 1 0).
    rewrite map_map_compose map_subst_lift1.
    simpl. constructor. now apply IHΔ.
Qed.

Lemma spine_subst_smash_inv {cf : checker_flags} {Σ : global_env_ext} (Δ : context) :
  wf Σ.1 ->
  wf_local Σ Δ ->
  spine_subst Σ (smash_context [] Δ)
    (to_extended_list (smash_context [] Δ)) (extended_subst Δ 0) Δ.
Proof.
  move=> wfΣ wfΔ.
  split; auto.
  - eapply wf_local_smash_context; auto.
  - eapply weaken_wf_local; auto. apply wf_local_smash_context; auto.
  - remember #|Δ| as n.
    rewrite /to_extended_list.
    rewrite -extended_subst_to_extended_list_k.
    eapply context_subst_to_extended_list_k; eauto.
  - now apply subslet_extended_subst.
Qed.

Lemma wf_projection_context_gen {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl cdecl} :
  wf Σ.1 ->
  declared_inductive Σ ind mdecl idecl ->
  on_projections mdecl (inductive_mind ind) (inductive_ind ind)
    idecl (ind_indices idecl) cdecl ->
  wf_local (Σ.1, ind_universes mdecl) (projection_context_gen ind mdecl idecl).
Proof.
  intros wfΣ hdecl onps.
  pose proof (on_declared_inductive hdecl) as [onmib oib]; auto.
  have wfpars : wf_local (Σ.1, ind_universes mdecl) (ind_params mdecl).
  { now apply onParams in onmib. }
  have wfsmpars : wf_local (Σ.1, ind_universes mdecl) (smash_context [] (ind_params mdecl)).
  { now apply wf_local_smash_context. }
  constructor => //.
  eapply has_sort_isTypeRel. 1: apply oib.(ind_relevance_compat).
  eapply type_mkApps. econstructor; eauto.
  eapply consistent_instance_ext_abstract_instance; eauto with pcuic.
  eapply declared_inductive_wf_global_ext; eauto with pcuic.
  set (u := abstract_instance (ind_universes mdecl)).
  destruct hdecl; eauto.
  assert (isType (Σ.1, ind_universes mdecl) [] (ind_type idecl)).
  { eapply isTypeRel_isType. pose proof (onArity oib). exact X. }
  rewrite (subst_instance_ind_type_id _ _ _ _ _ hdecl).
  rewrite (ind_arity_eq oib).
  rewrite -(app_nil_r (to_extended_list _)).
  eapply typing_spine_it_mkProd_or_LetIn'; auto.
  eapply spine_subst_smash_inv; tea.
  destruct onps. destruct (ind_indices idecl). cbn.
  eapply typing_spine_refl. eapply isType_Sort; tea.
  now eapply on_inductive_sort.
  now cbn in *.
  eapply isType_weaken; auto.
  now rewrite (oib.(ind_arity_eq)) in X.
Qed.

Lemma subst_context_extended_subst_expand Γ Δ :
  closedn_ctx #|Γ| Δ ->
  subst_context (extended_subst Γ 0) 0 Δ =
  expand_lets_ctx Γ Δ.
Proof.
  intros.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite closed_ctx_lift //.
Qed.

Lemma declared_constructor_wf_pars_args
  {cf:checker_flags} {Σ : global_env_ext} {ind i mdecl idecl cdecl} {wfΣ : wf Σ.1} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  wf_local (Σ.1, ind_universes mdecl)
    (ind_params mdecl ,,, subst_context
    (inds (inductive_mind ind) (abstract_instance (ind_universes mdecl))
       (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)).
Proof.
  intros onc.
  epose proof (on_declared_constructor onc) as [[onmib oib] [cs []]].
  eapply on_cargs in o.
  eapply sorts_local_ctx_wf_local in o.
  2:{ eapply weaken_wf_local => //.
      now eapply wf_arities_context'.
      now eapply onParams in onmib. }
  rewrite -app_context_assoc -[_ ,,, _]app_context_nil_l app_context_assoc in o.
  eapply (substitution_wf_local (Γ := [])) in o.
  2:eapply subslet_inds_gen, onc.
  rewrite app_context_nil_l in o.
  rewrite subst_context_app in o.
  rewrite closed_ctx_subst in o.
  eapply declared_inductive_closed_params, onc.
  now rewrite Nat.add_0_r in o.
Qed.

Lemma to_extended_list_k_map_lift:
  forall (n k : nat) (c : context),
  to_extended_list_k c k = map (lift n (#|c| + k)) (to_extended_list_k c k).
Proof.
  intros n k c.
  pose proof (to_extended_list_k_spec c k). unf_term.
  symmetry. solve_all.
  destruct H as [x' [-> Hx]]. simpl.
  destruct (leb_spec_Set (#|c| + k) x').
  - f_equal. lia.
  - reflexivity.
Qed.

Lemma all_rels_smash Γ n k :
  assumption_context Γ ->
  all_rels Γ n k = List.rev (to_extended_list_k Γ n).
Proof.
  induction 1 in n, k |- *; cbn; auto.
  rewrite reln_acc rev_app_distr /=.
  f_equal. rewrite IHassumption_context Nat.add_1_r //.
Qed.

Lemma to_extended_list_k_expand_lets Γ n Δ i :
  to_extended_list_k (expand_lets_k_ctx Γ n Δ) i = to_extended_list_k Δ i.
Proof.
  rewrite /expand_lets_k_ctx.
  now rewrite to_extended_list_k_subst to_extended_list_k_lift_context.
Qed.


Lemma extended_subst_lift_context n (Γ : context) (k k' : nat) :
  extended_subst (lift_context n k Γ) k' =
  map (lift n (k + context_assumptions Γ + k')) (extended_subst Γ k').
Proof.
  pose proof (rename_extended_subst).
  rewrite -rename_context_lift_context.
  rewrite lift_extended_subst -H.
  rewrite (lift_extended_subst _ k').
  rewrite !map_map_compose. apply map_ext => t.
  rewrite shiftn_lift_renaming; sigma.
  apply inst_ext.
  rewrite - !Upn_Upn (Nat.add_comm _ k') !Upn_Upn shiftn_Upn - !Upn_Upn.
  move=> i; lia_f_equal.
Qed.

Lemma subst_context_lift_context (n : nat) (Γ Δ : context) :
  subst_context (extended_subst (lift_context n 0 Γ) 0) 0 (lift_context n (#|Γ| + context_assumptions Γ) Δ) =
  lift_context n (context_assumptions Γ) (subst_context (extended_subst Γ 0) 0 Δ).
Proof.
  rewrite {1}extended_subst_lift_context /= Nat.add_0_r.
  now rewrite distr_lift_subst_context; len.
Qed.

Lemma lift_context_lift_context n k k' Γ :
  lift_context n (k + k') (lift_context k' k Γ) = lift_context (n + k') k Γ.
Proof.
  rewrite - !rename_context_lift_context.
  rewrite /rename_context fold_context_k_compose.
  apply fold_context_k_ext => i x.
  rewrite !rename_inst !shiftn_lift_renaming !ren_lift_renaming.
  sigma. apply inst_ext.
  now rewrite Upn_compose Upn_compose shiftn_Upn shiftk_compose.
Qed.

Lemma lift_context_subst_context_let_expand n s Γ Δ :
  #|s| = context_assumptions Γ ->
  lift_context n 0 (subst_context_let_expand s Γ Δ) =
  subst_context_let_expand (map (lift0 n) s) (lift_context n 0 Γ) (lift_context n #|Γ| Δ).
Proof.
  intros hlen.
  rewrite /subst_context_let_expand.
  rewrite distr_lift_subst_context. f_equal.
  rewrite Nat.add_0_r hlen.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=; autorewrite with len.
  rewrite -lift_context_add Nat.add_comm lift_context_add.
  rewrite -subst_context_lift_context.
  rewrite -lift_context_add.
  now rewrite lift_context_lift_context.
Qed.


Lemma expand_lets_lift n k Γ t :
  expand_lets (lift_context n k Γ) (lift n (#|Γ| + k) t) =
  lift n (k + context_assumptions Γ) (expand_lets Γ t).
Proof.
  rewrite /expand_lets /expand_lets_k /=.
  rewrite extended_subst_lift_context Nat.add_0_r.
  epose proof (distr_lift_subst_rec _ _ _ 0 (k + context_assumptions Γ)).
  len. rewrite permute_lift. lia. rewrite !Nat.add_assoc /= in H.
  relativize #|Γ|. erewrite <- H. 2:now len.
  now len.
Qed.

Lemma expand_lets_ctx_lift n k' Γ Δ :
  k' = #|Γ| ->
  expand_lets_ctx (lift_context n 0 Γ) (lift_context n k' Δ) =
  lift_context n (context_assumptions Γ) (expand_lets_ctx Γ Δ).
Proof.
  intros ->.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  len.
  rewrite distr_lift_subst_context. len.
  rewrite -lift_context_add Nat.add_comm.
  rewrite lift_context_lift_context.
  now rewrite extended_subst_lift_context.
Qed.

Lemma lift_context_expand_lets_ctx n Γ Δ :
  lift_context n 0 (expand_lets_ctx Γ Δ) =
  expand_lets_k_ctx Γ n (lift_context n 0 Δ).
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite lift_context_subst_context. f_equal.
  rewrite - !rename_context_lift_context /rename_context !fold_context_k_compose.
  apply fold_context_k_ext => i t.
  rewrite !shiftn_lift_renaming; sigma.
  apply inst_ext. now rewrite !Upn_compose shiftn_Upn.
Qed.

Lemma skipn_lift_context (m n : nat) (k : nat) (Γ : context) :
  skipn m (lift_context n k Γ) = lift_context n k (skipn m Γ).
Proof.
  rewrite !lift_context_alt.
  rewrite skipn_mapi_rec. rewrite mapi_rec_add /mapi.
  apply mapi_rec_ext. intros.
  f_equal. rewrite List.length_skipn. lia.
Qed.

Lemma skipn_subst_instance {n u Γ} :
  skipn n Γ@[u] = (skipn n Γ)@[u].
Proof.
  now rewrite /subst_instance /= /subst_instance_context /map_context map_skipn.
Qed.

Lemma skipn_expand_lets_ctx {n Γ Δ} :
  skipn n (expand_lets_ctx Γ Δ) = expand_lets_ctx Γ (skipn n Δ).
Proof.
  now rewrite /expand_lets_ctx /expand_lets_k_ctx skipn_subst_context skipn_lift_context.
Qed.

Lemma expand_lets_k_ctx_snoc Γ Δ k d :
  expand_lets_k_ctx Γ k (Δ ,, d) =
  expand_lets_k_ctx Γ k Δ ,, map_decl (expand_lets_k Γ (#|Δ| + k)) d.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx lift_context_snoc subst_context_snoc /=.
  f_equal. len. rewrite /subst_decl /lift_decl compose_map_decl //.
  rewrite Nat.add_assoc //.
Qed.

Lemma expand_lets_ctx_snoc Γ Δ d :
  expand_lets_ctx Γ (Δ ,, d) =
  expand_lets_ctx Γ Δ ,, map_decl (expand_lets_k Γ #|Δ|) d.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx lift_context_snoc subst_context_snoc /=.
  f_equal. len. rewrite /subst_decl /lift_decl compose_map_decl //.
Qed.

Lemma expand_lets_ctx_tip Γ d : expand_lets_ctx Γ [d] = [map_decl (expand_lets Γ) d].
Proof. rewrite /expand_lets_ctx /expand_lets_k_ctx /expand_lets /expand_lets_k.
  simpl. rewrite (lift_context_app _ _ [] [_]) /= (subst_context_app _ _ [] [_]) /=.
  f_equal.
  now rewrite compose_map_decl.
Qed.

Lemma subst_context_lift_context_cancel s k n Γ :
  n = #|s| ->
  subst_context s k (lift_context n k Γ) = Γ.
Proof.
  intros ->.
  induction Γ as [|[na [b|] ty] Γ']; auto;
    rewrite !lift_context_snoc !subst_context_snoc /= /subst_decl /map_decl /snoc /=; simpl; f_equal;
    auto; f_equal; len;
    rewrite -(Nat.add_0_r #|s|) simpl_subst_rec /= // ?lift0_id //; lia.
Qed.

Lemma wf_projection_arg_ctx {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl cdecl} :
  wf Σ.1 ->
  declared_constructor Σ (ind, 0) mdecl idecl cdecl ->
  on_projections mdecl (inductive_mind ind) (inductive_ind ind)
    idecl (ind_indices idecl) cdecl ->
  forall k,
  wf_local (Σ.1, ind_universes mdecl)
    (projection_context_gen ind mdecl idecl ,,, projection_arg_ctx ind mdecl cdecl k).
Proof.
  intros wfΣ decli onps k.
  rewrite /projection_arg_ctx.
  rewrite subst_context_lift_context_comm //.
  rewrite /projection_context_gen.
  eapply (weakening_wf_local (Γ'' := [_])).
  2:eapply wf_projection_context_gen; tea. 2:apply decli.
  rewrite - !skipn_subst_context.
  eapply All_local_env_app_skipn.
  rewrite -(smash_context_subst []) /=.
  rewrite -(smash_context_subst []) /=.
  rewrite subst_context_nil.
  rewrite subst_context_extended_subst_expand.
  { eapply declared_constructor_wf_pars_args in decli.
    eapply closed_wf_local in decli => //.
    rewrite closedn_ctx_app in decli.
    now move/andP: decli => []. }
  rewrite -(expand_lets_smash_context _ []).
  rewrite -smash_context_app_expand. eapply wf_local_smash_context.
  destruct onps.
  pose proof (on_declared_inductive decli) as [onmib oib]; auto.
  have onpars := onParams onmib.
  have oncstr := onConstructors oib.
  destruct (ind_ctors idecl) as [|? []] eqn:hctors; try discriminate.
  red in oncstr. depelim oncstr.
  depelim oncstr.
  now eapply declared_constructor_wf_pars_args.
Qed.

Lemma declared_projections_subslet_ind {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} :
  forall (wfΣ : wf Σ.1) (Hdecl : declared_inductive Σ ind mdecl idecl),
  let u := abstract_instance (ind_universes mdecl) in
  let indb:= {|
          binder_name := nNamed (ind_name idecl);
          binder_relevance := ind_relevance idecl |} in
  forall c, ind_ctors idecl = [c] ->
  Alli (fun (i : nat) (_ : context_decl) =>
     ∑ pdecl, nth_error (ind_projs idecl) (context_assumptions (cstr_args c) - S i) =
            Some pdecl) 0 (smash_context [] (cstr_args c)) ->
  forall i: nat,
  let indsubst:= inds (inductive_mind ind)
                (abstract_instance (ind_universes mdecl))
                (ind_bodies mdecl) in
  forall (IH: forall i0 : nat,
       i0 < i ->
       forall x,
       nth_error (ind_projs idecl) i0 = Some x ->
      isType (Σ.1, ind_universes mdecl)
           (smash_context [] (ind_params mdecl),,
            vass indb
              (mkApps (tInd ind (abstract_instance (ind_universes mdecl)))
                 (to_extended_list (smash_context [] (ind_params mdecl))))) x.(proj_type)
         × (∑ decl : context_decl,
              [× nth_error (smash_context [] (cstr_args c))
                  (context_assumptions (cstr_args c) - S i0) = Some decl,
                isType (Σ.1, ind_universes mdecl)
                (arities_context (ind_bodies mdecl),,, ind_params mdecl,,,
                 skipn (context_assumptions (cstr_args c) - i0)
                   (smash_context [] (cstr_args c))) (decl_type decl),
                wf_local (Σ.1, ind_universes mdecl)
                  (arities_context (ind_bodies mdecl),,, ind_params mdecl,,,
                   smash_context [] (cstr_args c)),
               projection_type mdecl ind i0 (decl_type decl) = x.(proj_type) &
               projection_type mdecl ind i0 (decl_type decl) =
               projection_type' mdecl ind i0 (decl_type decl)])),
  on_projections mdecl (inductive_mind ind) (inductive_ind ind)
    idecl (ind_indices idecl) c ->
  i <= context_assumptions (cstr_args c) ->
  context_assumptions (ind_params mdecl) = ind_npars mdecl ->
  #|ind_projs idecl| = context_assumptions (cstr_args c) ->
  wf_subslet (Σ.1, ind_universes mdecl)
  (projection_context_gen ind mdecl idecl)
  (projs ind (ind_npars mdecl) i)
  (subst_context (extended_subst (ind_params mdecl) 0) 1
     (lift_context 1 0
        (subst_context indsubst #|ind_params mdecl|
           (skipn (context_assumptions (cstr_args c) - i)
              (smash_context [] (cstr_args c)))))).
Proof.
  intros.
  split.
  { eapply wf_projection_arg_ctx; tea. split => //.
    now rewrite H. }
  induction i as [|i IHi].
  - rewrite Nat.sub_0_r.
    rewrite skipn_all2.
    autorewrite with len; simpl; auto.
    constructor.
  - forward IHi.
    intros. eapply IH. lia. auto.
    forward IHi by lia. simpl in IHi.
    destruct (skipn (context_assumptions (cstr_args c) - S i)
      (smash_context [] (cstr_args c))) eqn:eqargs.
    apply (f_equal (@length _)) in eqargs.
    autorewrite with len in eqargs.
    rewrite length_skipn in eqargs.
    autorewrite with len in eqargs. simpl in eqargs. lia.
    rewrite subst_context_snoc lift_context_snoc subst_context_snoc.
    simpl.
    destruct c0 as [? [] ?].
    * simpl in eqargs.
      pose proof (@smash_context_assumption_context [] (cstr_args c)).
      forward H3 by constructor.
      eapply assumption_context_skipn in H3.
      rewrite -> eqargs in H3. exfalso; inv H3.
    * apply skipn_eq_cons in eqargs as [Hnth eqargs].
      constructor.
      + replace (S (context_assumptions (cstr_args c) - (S i)))
          with (context_assumptions (cstr_args c) - i) in eqargs by lia.
        rewrite eqargs in IHi. cbn.
        apply IHi.
      + rewrite /lift_decl /=; len.
        specialize (IH i).
        forward IH by lia; len.
        eapply (f_equal (@length _)) in eqargs.
        rewrite length_skipn in eqargs.
        autorewrite with len in eqargs. simpl in eqargs.
        eapply nth_error_alli in X; eauto. simpl in X.
        destruct X as [pdecl Hnth'].
        replace ((context_assumptions (cstr_args c) -
          (S (context_assumptions (cstr_args c) - (S i)))))
          with i in eqargs, Hnth' by lia. rewrite -eqargs.
        rewrite /lift_decl /subst_decl. simpl; len.
        erewrite (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i).
        2:lia.
        specialize (IH _ Hnth').
        eapply meta_conv. econstructor.
        split; eauto. split; eauto. simpl.
        rewrite H //. split => //.
        apply Hnth'.
        eapply meta_conv. econstructor.
        destruct IH as [(_ & s & isTy & _) _].
        now eapply typing_wf_local in isTy.
        simpl. reflexivity. simpl.
        rewrite lift_mkApps. simpl. destruct ind; simpl.
        reflexivity. autorewrite with len.
        simpl.
        rewrite context_assumptions_smash_context /= //.
        assert(subst_instance (abstract_instance (ind_universes mdecl)) pdecl.(proj_type) = pdecl.(proj_type)) as ->.
        { eapply (isType_subst_instance_id (Σ.1, ind_universes mdecl)); eauto with pcuic.
          eapply declared_inductive_wf_ext_wk; eauto with pcuic.
          destruct Hdecl; eauto. eapply IH.    }
        destruct IH as [isTy [decl [nthdecl _ _ eqpdecl ptyeq]]].
        move ptyeq at bottom.
        rewrite nthdecl in Hnth. noconf Hnth. simpl in ptyeq.
        rewrite -eqpdecl. simpl.
        rewrite ptyeq. unfold projection_type'.
        fold indsubst. destruct ind as [mind ind]; simpl in *.
        set (projsubst := projs {| inductive_mind := mind; inductive_ind := ind |} (ind_npars mdecl) i) in *.
        rewrite -eqpdecl in isTy.
        eapply isType_closed in isTy.
        simpl in isTy. autorewrite with len in isTy. simpl in isTy.
        rewrite ptyeq in isTy.
        unfold projection_type' in isTy.
        erewrite (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i) in isTy by lia.
        erewrite (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i) by lia.
        rewrite (subst_id _ (({|
          decl_name := indb;
          decl_body := None;
          decl_type := mkApps
                        (tInd
                            {| inductive_mind := mind; inductive_ind := ind |}
                            u)
                        (to_extended_list
                            (smash_context [] (ind_params mdecl))) |}
          :: smash_context [] (ind_params mdecl)))).
        ++ simpl. autorewrite with len.
          rewrite context_assumptions_smash_context //.
        ++ constructor. apply smash_context_assumption_context; constructor.
        ++ unfold to_extended_list, to_extended_list_k.  simpl.
          rewrite -reln_lift /= (reln_acc [_]) rev_app_distr /= //.
        ++ now rewrite (Nat.add_1_r i).
Qed.

Lemma map_expand_lets_to_extended_list_k Γ :
  map (expand_lets Γ) (to_extended_list Γ) = to_extended_list (smash_context [] Γ).
Proof.
  rewrite -map_subst_extended_subst_lift_to_extended_list_k map_map_compose //.
Qed.

Lemma declared_projections {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} :
  forall (wfΣ : wf Σ.1) (Hdecl : declared_inductive Σ ind mdecl idecl),
  let u := abstract_instance (ind_universes mdecl) in
  match ind_ctors idecl return Type with
  | [cs] =>
    on_projections mdecl (inductive_mind ind) (inductive_ind ind)
      idecl (ind_indices idecl) cs ->
    Alli (fun i pdecl =>
    isType (Σ.1, ind_universes mdecl) (projection_context_gen ind mdecl idecl) pdecl.(proj_type) *
      ∑ decl,
        [× nth_error (smash_context [] (cstr_args cs))
          (context_assumptions (cstr_args cs) - S i) = Some decl,
        isType (Σ.1, ind_universes mdecl)
         (arities_context (ind_bodies mdecl),,, ind_params mdecl,,,
          skipn (context_assumptions (cstr_args cs) - i)
            (smash_context [] (cstr_args cs))) (decl_type decl),
        wf_local (Σ.1, ind_universes mdecl)
          (arities_context (ind_bodies mdecl) ,,,
            ind_params mdecl ,,, smash_context [] (cstr_args cs)),
        (projection_type mdecl ind i decl.(decl_type) = pdecl.(proj_type)) &
        (projection_type mdecl ind i decl.(decl_type) =
            projection_type' mdecl ind  i decl.(decl_type))])%type
      0 (ind_projs idecl)
  | _ => True
  end.
Proof.
  intros wfΣ decli u.
  set oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ decli.
  unfold projection_context_gen.
  set indb := {| binder_name := _ |}.
  destruct (ind_ctors idecl) as [|? []] eqn:Heq; try contradiction; auto.
  intros onps.
  eapply forall_nth_error_Alli.
  set (eos := CoreTactics.the_end_of_the_section).
  intros i. Subterm.rec_wf_rel IH i lt. clear eos.
  rename pr1 into i. simpl; clear H0.
  set (p := mkProjection ind (ind_npars mdecl) i).
  intros pdecl Hp. simpl.
  assert (hnth': nth_error (ind_ctors idecl) 0 = Some c) by
    (rewrite Heq //).
  set(isdecl := (conj (conj decli hnth') (conj Hp eq_refl)) :
      declared_projection Σ.1 p mdecl idecl c pdecl).
  destruct (on_declared_projection isdecl) as [oni onp].
  set (declared_inductive_inv _ _ _ _) as oib' in onp.
  change oib' with oib in *. clear oib'.
  simpl in onp.
  have onpars := onParams (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ decli.p1).
  have parslen := onNpars (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ decli.p1).
  simpl in onp.
  destruct onp as [[[wfargs onProjs] Hp2] onp].
  red in onp.
  destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
  destruct onp as [onna onp].
  rewrite {}onp.
  apply on_projections_decl in onps.
  assert(projslen : #|ind_projs idecl| = (context_assumptions (cstr_args c))).
  { now destruct onProjs. }
  assert (some_proj :#|ind_projs idecl| > 0).
  { destruct isdecl as [ [] []]. now apply nth_error_Some_length in H1. }
  simpl.
  assert (wfarities : wf_local (Σ.1, ind_universes mdecl)
      (arities_context (ind_bodies mdecl))).
  { eapply wf_arities_context; eauto.
    destruct isdecl as [[[] ?] ?]; eauto. }
  destruct (ind_cunivs oib) as [|? []] eqn:hequ => //.
  eapply PCUICClosedConv.sorts_local_ctx_All_local_env in wfargs.
  2:{ eapply All_local_env_app; auto.
      red in onpars. eapply (All_local_env_impl _ _ _ onpars).
      intros. apply lift_typing_impl with (1 := X); intros ? Hs.
      eapply weaken_ctx; auto. }
  pose proof wfargs as X.
  rewrite -(app_context_nil_l (arities_context _)) in X.
  rewrite -app_context_assoc in X.
  eapply (substitution_wf_local (Γ := [])) in X; auto.
  2:{ eapply subslet_inds_gen; eauto. }
  rewrite app_context_nil_l in X.
  move: X.
  rewrite subst_context_app.
  rewrite (closed_ctx_subst _ _ (ind_params mdecl)).
  red in onpars. eapply closed_wf_local; [|eauto]. auto.
  assert (parsu : subst_instance u (ind_params mdecl) = ind_params mdecl).
  { red in onpars. eapply (subst_instance_id (Σ.1, ind_universes mdecl)). eauto.
    eapply declared_inductive_wf_ext_wk; eauto with pcuic.
    destruct decli; eauto. auto. }
  assert (typeu : subst_instance u (ind_type idecl) = ind_type idecl).
  { eapply (subst_instance_ind_type_id Σ.1); eauto. }
  assert (sortu : subst_instance u (ind_sort idecl) = ind_sort idecl).
  { apply (subst_instance_ind_sort_id Σ mdecl ind idecl); eauto. }
  pose proof (spine_subst_to_extended_list_k (Σ := (Σ.1, ind_universes mdecl))
    (Δ := ind_params mdecl) (Γ := [])).
  assert (wf_local (Σ.1, ind_universes mdecl) (ind_params mdecl)). auto.
  forward X. rewrite app_context_nil_l; auto.
  rewrite app_context_nil_l in X.
  rewrite closed_ctx_lift in X.
  red in onpars. eapply closed_wf_local; [|eauto]. auto.
  assert(wf_local (Σ.1, ind_universes mdecl) (ind_params mdecl ,,
      vass {| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |}
      (mkApps (tInd ind u) (to_extended_list (ind_params mdecl))))).
  { constructor. auto. eapply has_sort_isTypeRel.
    1: apply oib.(ind_relevance_compat).
    eapply type_mkApps. econstructor; eauto.
    destruct isdecl as []; eauto. subst u.
    eapply consistent_instance_ext_abstract_instance; eauto with pcuic.
    eapply declared_inductive_wf_global_ext; eauto with pcuic.
    destruct decli; eauto.
    assert (isType (Σ.1, ind_universes mdecl) [] (ind_type idecl)@[u]).
    { eapply isTypeRel_isType. rewrite typeu. pose proof (onArity oib). exact X1. }
    rewrite (ind_arity_eq oib).
    rewrite subst_instance_it_mkProd_or_LetIn.
    rewrite -(app_nil_r (to_extended_list _)).
    eapply typing_spine_it_mkProd_or_LetIn' ; auto.
    rewrite parsu. eapply X.
    constructor.
    cbn.
    rewrite (oib.(ind_arity_eq)) in X1.
    eapply isType_it_mkProd_or_LetIn_subst.
    2:eapply X. eapply isType_weaken => //.
    rewrite -parsu - !subst_instance_it_mkProd_or_LetIn /= //.
    eapply isType_Sort. 2:pcuic.
    eapply on_inductive_sort; eauto.
    simpl in oib.
    pose proof (onProjs.(on_projs_noidx _ _ _ _ _ _)).
    destruct (ind_indices idecl); simpl in H; try discriminate.
    simpl. rewrite [subst_instance_sort _ _]sortu.
    eapply ws_cumul_pb_compare => //.
    now eapply wf_local_closed_context in X0.
    constructor. reflexivity.
    rewrite -subst_instance_it_mkProd_or_LetIn.
    pose proof (onArity oib). rewrite -(oib.(ind_arity_eq)).
    apply lift_typing_impl with (1 := X1) => t T HT.
    eapply (weaken_ctx (Γ:=[])); auto. }
  intros wf.
  generalize (weakening_wf_local (Γ'':=[_]) wf X1).
  simpl; clear X1 wf.
  move/wf_local_smash_context => /=.
  rewrite smash_context_app /= smash_context_acc.

  set(indsubst := (inds (inductive_mind ind)
    (abstract_instance (PCUICEnvironment.ind_universes mdecl))
    (PCUICEnvironment.ind_bodies mdecl))) in *.
  set (projsubst :=  (projs {| inductive_mind := inductive_mind ind;
      inductive_ind := inductive_ind ind |}
    (PCUICEnvironment.ind_npars mdecl) i)) in *.
  rewrite lift_context_app. simpl.
  rewrite [subst_context _ _ (_ ++ _)]subst_context_app.
  rewrite lift_context_length /=.
  simpl. unfold app_context. simpl.
  rewrite lift_context_snoc /= /lift_decl /map_decl /=.
  simpl. rewrite lift_mkApps. simpl.
  rewrite {3}/subst_context /fold_context_k /= /map_decl /= subst_mkApps /=.
  rewrite /to_extended_list lift_to_extended_list_k.
  rewrite extended_subst_to_extended_list_k.
  fold (to_extended_list (smash_context [] (ind_params mdecl))).
  intros wfl.
  rewrite PCUICClosed.closed_ctx_lift in wfl.
  { eapply closedn_smash_context.
    eapply closed_wf_local in wfargs; auto.
    rewrite closedn_ctx_app in wfargs.
    simpl in wfargs; autorewrite with len in wfargs.
    move/andP: wfargs => [_ clargs].
    clear -isdecl wfΣ clargs.
    eapply (closedn_ctx_lift 1).
    rewrite Nat.add_0_r.
    eapply (closedn_ctx_subst 0 #|ind_params mdecl|).
    now unfold indsubst; rewrite inds_length.
    unfold indsubst.
    eapply declared_minductive_closed_inds. eauto.
    destruct isdecl as [[[] ?] ?]; eauto.  }
  rewrite -app_assoc in wfl.
  apply All_local_env_app_inv in wfl as [wfctx wfsargs].
  rewrite smash_context_app in Heq'.
  rewrite smash_context_acc in Heq'.
  rewrite nth_error_app_lt in Heq'.
  autorewrite with len. lia.
  set (idx := context_assumptions (cstr_args c) - S i) in *.
  unshelve epose proof ((nth_error_Some' _ idx).2 _) as (c2 & hidx); cycle -1.
  eapply @All_local_env_nth_error with (n := idx) (2 := hidx) in wfsargs as onnth.
  2: autorewrite with len; simpl. 2: lia.
  simpl in onnth. red in onnth. cbn in onnth.
  assert(decl_body c2 = None).
  { apply nth_error_assumption_context in hidx; auto.
    rewrite /subst_context /lift_context.
    apply assumption_context_fold, smash_context_assumption_context. constructor. }
  rewrite H in onnth.
  destruct onnth as (_ & s & Hs & _).
  Ltac havefst H :=
    match goal with
    |- ?T × _ => have H : T; [|split => //]
    end.
  eapply (substitution (Σ := (Σ.1, ind_universes mdecl)) (Γ := _ :: _) (Γ' := skipn _ _) (s := projsubst) (Δ := []))
    in Hs; auto.
  2:{ subst projsubst.
    rewrite (smash_context_lift []).
    rewrite (smash_context_subst []).
    rewrite -(firstn_skipn (S idx) (smash_context [] (cstr_args c))).
    rewrite subst_context_app lift_context_app subst_context_app.
    len.
    rewrite skipn_all_app_eq.
    len.
    rewrite firstn_length_le; auto. rewrite smash_context_length.
    simpl. lia. destruct ind; cbn in *.
    replace (S idx) with (context_assumptions (cstr_args c) - i); try lia.
    eapply (declared_projections_subslet_ind wfΣ decli _ Heq onps i IH); tas. lia. }
  simpl in Hs.
  rewrite nth_error_subst_context in Heq'.
  autorewrite with len in Heq'. simpl in Heq'.
  epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))).
  autorewrite with len in H0.
  erewrite H0 in Heq'. simpl in Heq'. clear H0.
  rewrite !option_map_two in Heq'.
  apply option_map_Some in Heq' as [arg [nthidx eq]].
  rewrite nth_error_subst_context in hidx.
  autorewrite with len in hidx. simpl in hidx.
  rewrite (smash_context_lift []) in hidx.
  rewrite (smash_context_subst []) in hidx.
  rewrite (nth_error_lift_context_eq _ [vass indb (mkApps (tInd ind u) [])]) in hidx.
  simpl in hidx. autorewrite with len in hidx.
  rewrite nth_error_subst_context in hidx. autorewrite with len in hidx.
  simpl in hidx.
  rewrite !option_map_two in hidx.
  assert(clarg : closedn (i + #|ind_params mdecl| + #|ind_bodies mdecl|) (decl_type arg)).
  { assert(wfargs' : wf_local (Σ.1, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
      smash_context [] (cstr_args c))).
    { apply All_local_env_app; auto.
      now apply All_local_env_app_inv in wfargs as [wfindpars wfargs].
      apply wf_local_rel_smash_context; auto. }
    eapply closed_wf_local in wfargs'; auto.
    eapply (closedn_ctx_decl (n:=idx)) in wfargs'; eauto.
    2:{ rewrite nth_error_app_lt. autorewrite with len. simpl; lia.
        now eapply nthidx. }
    move/andP: wfargs' => [_ clty].
    eapply closed_upwards; eauto.
    autorewrite with len; simpl. simpl in idx. lia. }
  rewrite nthidx in hidx. simpl in hidx. noconf hidx. simpl in *.
  subst c0.
  destruct ind as [mind ind]; simpl in *.
  autorewrite with len. simpl.
  revert Hs.
  assert(context_assumptions (cstr_args c) - S idx = i) as -> by lia.
  intros Hs.
  assert (projection_type mdecl {| inductive_mind := mind; inductive_ind := ind |}
      i (decl_type arg) =
    projection_type' mdecl {| inductive_mind := mind; inductive_ind := ind |} i
        (decl_type arg)).
  { eapply nth_error_Some_length in nthidx.
    autorewrite with len in nthidx. simpl in nthidx.
    unfold projection_type, projection_type'. simpl.
    fold indsubst projsubst.
    rewrite distr_subst.
    f_equal.
    { clear. subst projsubst. induction i; simpl; auto.
      f_equal. auto. }
    rewrite /projsubst projs_length.
    replace (context_assumptions (cstr_args c) - S idx + 1) with
    (context_assumptions (cstr_args c) - idx) by lia.
    simpl in idx.
    epose proof (commut_lift_subst_rec _ _ 1 (i + ind_npars mdecl) i).
    rewrite -Nat.add_1_r Nat.add_assoc. erewrite <-H0. 2:lia.
    clear H0.
    epose proof (commut_lift_subst_rec _ _ 1 i i) as hs.
    rewrite Nat.add_1_r in hs. rewrite <- hs; try lia. clear hs. f_equal.
    rewrite distr_subst_rec.
    clear H.
    rewrite map_subst_closedn.
    rewrite -parslen.
    eapply closedn_extended_subst. eapply closed_wf_local. 2:eauto. auto.
    f_equal. autorewrite with len.
    epose proof (commut_lift_subst_rec _ _ (ind_npars mdecl) (i + #|ind_params mdecl|)
      (i + #|ind_params mdecl|)) as hs.
    rewrite parslen. erewrite <-hs. 2:lia.
    rewrite lift_closed; auto.
    apply (closedn_subst _ 0).
    unfold indsubst.
    eapply (declared_minductive_closed_inds decli).
    simpl. eapply subject_closed in Hs.
    now rewrite /indsubst inds_length. }
  split.
  unfold projection_type in H0.
  rewrite H0. eapply has_sort_isType; eauto.
  rewrite -/indb in Hs.
  rewrite /projection_type' -/indb -/indsubst -/projsubst.
  rewrite Nat.add_1_r in Hs. exact Hs.
  exists arg. split; auto.
  2:{ apply wf_local_smash_end; auto. }
  eapply wf_local_smash_end in wfargs.
  eapply All_local_env_app_skipn with (n:=context_assumptions (cstr_args c) - S i) in wfargs.
  epose proof (wf_local_nth_isTypeRel (d:=arg) (n:=0) wfargs).
  rewrite skipn_app in X1.
  rewrite length_skipn in X1. len.
  rewrite nth_error_app_lt // in X1. rewrite length_skipn. len. len.
  rewrite nth_error_skipn Nat.add_0_r nthidx in X1.
  forward X1 by reflexivity.
  len in X1. rewrite /idx in X1.
  rewrite skipn_skipn in X1.
  assert (context_assumptions (cstr_args c) - S i + 1 =
    context_assumptions (cstr_args c) - i) by lia.
  rewrite H1 in X1.
  rewrite [skipn _ (_ ,,, _)]skipn_0_eq in X1.
  assert (context_assumptions (cstr_args c) > 0). lia. lia.
  apply isTypeRel_isType in X1.
  apply X1.
Qed.

Lemma declared_projections_subslet {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} :
  forall (wfΣ : wf Σ.1) (Hdecl : declared_inductive Σ ind mdecl idecl),
  let u := abstract_instance (ind_universes mdecl) in
  let indsubst:= inds (inductive_mind ind)
          (abstract_instance (ind_universes mdecl))
          (ind_bodies mdecl) in
  forall c, ind_ctors idecl = [c] ->
  on_projections mdecl (inductive_mind ind) (inductive_ind ind) idecl (ind_indices idecl) c ->
  forall i, i <= context_assumptions (cstr_args c) ->
  wf_subslet (Σ.1, ind_universes mdecl)
    (projection_context_gen ind mdecl idecl)
    (projs ind (ind_npars mdecl) i)
    (subst_context (extended_subst (ind_params mdecl) 0) 1
      (lift_context 1 0
          (subst_context indsubst #|ind_params mdecl|
             (skipn (context_assumptions (cstr_args c) - i)
                (smash_context [] (cstr_args c)))))).
Proof.
  intros wfΣ decli u indsubst c hctors onps i hi.
  eapply declared_projections_subslet_ind; tea.
  now apply on_projections_decl in onps.
  intros.
  move: (declared_projections wfΣ decli).
  rewrite hctors. intros IH. cbn in IH.
  forward IH by tas. eapply nth_error_alli in IH; tea.
  now cbn in IH.
  now rewrite (declared_minductive_ind_npars decli).
  eapply onps.
Qed.

Lemma declared_projection_type {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p cdecl pdecl} :
  wf Σ.1 ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  let u := abstract_instance (ind_universes mdecl) in
  isType (Σ.1, ind_universes mdecl)
    ((vass {| binder_name := nNamed idecl.(ind_name); binder_relevance := idecl.(ind_relevance) |} (mkApps (tInd p.(proj_ind) u)
          (to_extended_list (smash_context [] (ind_params mdecl)))))::
        smash_context [] (ind_params mdecl)) pdecl.(proj_type).
Proof.
  intros wfΣ declp.
  destruct (on_declared_projection declp) as [oni onp].
  specialize (declared_projections wfΣ (let (x , _) := declp in x.p1)).
  set(oib := declared_inductive_inv _ _ _ _) in *.
  intros onprojs u.
  clearbody oib.
  simpl in *.
  destruct oni.
  destruct (ind_ctors idecl) as [|? []] => //.
  destruct onp as [[[? ?] ?] ?].
  destruct (ind_cunivs oib) as [|? []] => //.
  forward onprojs. noconf e. intuition auto.
  destruct declp as [decli [Hnth Hpars]].
  eapply nth_error_alli in onprojs; eauto.
  simpl in onprojs. intuition auto.
Qed.

Lemma declared_projection_type_and_eq {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p cdecl pdecl} :
  forall (wfΣ : wf Σ.1) (Hdecl : declared_projection Σ p mdecl idecl cdecl pdecl),
  let u := abstract_instance (ind_universes mdecl) in
  (ind_ctors idecl = [cdecl]) *
  isType (Σ.1, ind_universes mdecl)
    ((vass {| binder_name := nNamed idecl.(ind_name); binder_relevance := idecl.(ind_relevance) |}
      (mkApps (tInd p.(proj_ind) u)
          (to_extended_list (smash_context [] (ind_params mdecl)))))::
      smash_context [] (ind_params mdecl)) pdecl.(proj_type) *
  ∑ decl,
    [× nth_error (smash_context [] (cstr_args cdecl))
      (context_assumptions (cstr_args cdecl) - S p.(proj_arg)) = Some decl,
      isType (Σ.1, ind_universes mdecl)
        (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
          skipn (context_assumptions (cstr_args cdecl) - p.(proj_arg))
            (smash_context [] (cstr_args cdecl))) decl.(decl_type),
      (wf_local (Σ.1, ind_universes mdecl)
        (arities_context (ind_bodies mdecl) ,,,
          ind_params mdecl ,,, smash_context [] (cstr_args cdecl))),
      (projection_type mdecl p.(proj_ind) p.(proj_arg) decl.(decl_type) = pdecl.(proj_type)) &
      (projection_type mdecl p.(proj_ind) p.(proj_arg) decl.(decl_type) =
        projection_type' mdecl p.(proj_ind) p.(proj_arg) decl.(decl_type))%type].
Proof.
  intros wfΣ declp.
  destruct (on_declared_projection declp) as [oni onp].
  specialize (declared_projections wfΣ (let (x, _) := declp in x.p1)).
  set(oib := declared_inductive_inv _ _ _ _) in *.
  intros onprojs u.
  clearbody oib.
  destruct oni.
  destruct (ind_ctors idecl) as [|? []] => //. noconf e.
  destruct onp as [[[? ?] ?] ?].
  set (cu := ind_cunivs _) in y.
  destruct cu as [|? []] in y => //. simpl in *.
  forward onprojs. intuition auto.
  destruct declp as [decli [Hnth Hpars]].
  eapply nth_error_alli in onprojs; eauto.
  simpl in onprojs. intuition auto.
Qed.

Lemma type_local_ctx_cum {cf:checker_flags} {Σ Γ Δ s s'} :
  wf Σ.1 -> wf_sort Σ s' ->
  leq_sort (global_ext_constraints Σ) s s' ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s'.
Proof.
  intros wfΣ wfs leqs.
  induction Δ as [|[na [b|] ty] Δ]; simpl; auto;
  intros []; split; auto.
  destruct l as (_ & ss & Hs & <- & Her).
  split; cbn; eexists; split; [|split; eauto using leq_relevance].
  eapply type_Cumul; eauto.
  econstructor; pcuic.
  now eapply cumul_Sort.
Qed.

Lemma type_local_ctx_wf {cf:checker_flags} {Σ Γ Δ s} :
  wf Σ.1 ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s ->
  wf_sort Σ s.
Proof.
  intros wfΣ.
  induction Δ as [|[na [b|] ty] Δ]; simpl; intuition auto.
Qed.

Lemma isType_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ s s':
  wf Σ.1 ->
  wf_local Σ Γ ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s ->
  wf_sort Σ s' ->
  isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s')).
Proof.
  move=> wfΣ wfΓ wfΔ wfs.
  eapply isType_intro.
  eapply type_it_mkProd_or_LetIn. 2:tea.
  eapply type_local_ctx_wf; eauto.
  econstructor; pcuic.
  eapply type_local_ctx_All_local_env; eauto.
Qed.

Lemma isType_it_mkProd_or_LetIn_smash {cf:checker_flags} Σ Γ Δ s :
  wf Σ.1 ->
  isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) ->
  isType Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (tSort s)).
Proof.
  intros wfΣ HT.
  apply lift_sorting_it_impl_gen with HT => // Hu. set (u := HT.2.π1) in *; clearbody u. clear HT.
  revert Γ u Hu.
  induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; simpl in *; auto;
  rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=; rewrite smash_context_app; intros Γ u Hu.
  - simpl.
    assert (wfu := typing_wf_sort wfΣ Hu).
    eapply inversion_LetIn in Hu as (T & wfty & HT & hlt); auto.
    eapply substitution_let in HT; auto.
    rewrite /subst1 subst_it_mkProd_or_LetIn /= in HT.
    specialize (X (subst_context [b] 0 Δ) ltac:(autorewrite with len; lia)).
    eapply ws_cumul_pb_LetIn_l_inv in hlt; eauto.
    eapply type_ws_cumul_pb in HT. 3:eauto.
    2:{ eapply isType_Sort. all: pcuic. }
    specialize (X _ _ HT).
    now rewrite -smash_context_subst /= subst_context_nil.
  - simpl. rewrite it_mkProd_or_LetIn_app. simpl.
    assert (wfu := typing_wf_sort wfΣ Hu).
    eapply inversion_Prod in Hu as (s1 & s2 & wfty & Ht & hlt); auto.
    specialize (X Δ ltac:(reflexivity)).
    specialize (X _ _ Ht).
    eapply type_ws_cumul_pb; eauto.
    econstructor; tas. apply unlift_TypUniv in wfty.
    eapply isType_intro. econstructor; pcuic.
Qed.


Lemma typing_spine_to_extended_list {cf:checker_flags} Σ Δ u s :
  wf Σ.1 ->
  isType Σ [] (subst_instance u (it_mkProd_or_LetIn Δ (tSort s))) ->
  typing_spine Σ (smash_context [] (subst_instance u Δ))
    (subst_instance u (it_mkProd_or_LetIn Δ (tSort s)))
    (to_extended_list (smash_context [] (subst_instance u Δ)))
    (tSort (subst_instance_sort u s)).
Proof.
  move=> wfΣ wfΔ.
  apply wf_arity_spine_typing_spine; auto.
  rewrite subst_instance_it_mkProd_or_LetIn in wfΔ |- *.
  split.
  eapply isType_weaken; auto.
  eapply wf_local_smash_context; pcuic.
  now eapply isType_it_mkProd_or_LetIn_wf_local in wfΔ; auto; rewrite app_context_nil_l in wfΔ.
  rewrite -(app_nil_r (to_extended_list (smash_context [] (subst_instance u Δ)))).
  eapply arity_spine_it_mkProd_or_LetIn; auto.
  2:{ constructor. }
  eapply spine_subst_smash_inv; eauto.
  eapply isType_it_mkProd_or_LetIn_inv in wfΔ; pcuic.
  rewrite app_context_nil_l in wfΔ.
  now eapply isType_wf_local.
Qed.

Lemma wf_projection_context {cf:checker_flags} (Σ : global_env_ext) {mdecl idecl p cdecl pdecl u} :
  wf Σ.1 ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (projection_context p.(proj_ind) mdecl idecl u).
Proof.
  move=> wfΣ decli.
  pose proof (on_declared_projection decli) as [[onmind eqctr] onind].
  set (oib := declared_inductive_inv _ _ _ _) in *. clearbody oib.
  simpl in onind; destruct ind_ctors as [|? []] => //. noconf eqctr.
  destruct onind as [[[_ onps] Hpe] onp].
  move=> cu.
  assert(wfparams : wf_local Σ (subst_instance u (ind_params mdecl))).
  { eapply on_minductive_wf_params; eauto. eapply decli. }
  assert(wfsmash : wf_local Σ (smash_context [] (subst_instance u (ind_params mdecl)))).
  { eapply wf_local_smash_context; auto. }
  constructor; auto. red.
  eapply has_sort_isTypeRel with (s := subst_instance_sort u (ind_sort idecl)).
  1: rewrite relevance_subst_eq; apply oib0.(ind_relevance_compat).
  eapply type_mkApps. econstructor; eauto. eapply decli.p1.
  rewrite (ind_arity_eq oib0).
  pose proof (on_projs_noidx _ _ _ _ _ _ onps).
  destruct (ind_indices idecl) eqn:eqind; try discriminate.
  simpl.
  eapply typing_spine_to_extended_list; eauto.
  pose proof (on_inductive_inst decli _ u localenv_nil).
  rewrite eqind in X. simpl in X.
  eapply isTypeRel_isType.
  now rewrite subst_instance_it_mkProd_or_LetIn.
Qed.

Lemma invert_type_mkApps_ind {cf:checker_flags} Σ Γ ind u args T mdecl idecl :
  wf Σ.1 ->
  declared_inductive Σ.1 ind mdecl idecl ->
  Σ ;;; Γ |- mkApps (tInd ind u) args : T ->
  (typing_spine Σ Γ (subst_instance u (ind_type idecl)) args T)
  * consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  intros wfΣ decli.
  intros H; dependent induction H; solve_discr.
  - destruct args using rev_case; solve_discr. noconf H2.
    rewrite mkApps_app in H2. simpl in H2.
    noconf H2. clear IHtyping1 IHtyping3.
    specialize (IHtyping2 _ _ _ _ _ _ _ wfΣ decli eq_refl) as [IH cu];
      split; auto.
    destruct (on_declared_inductive decli) as [onmind oib].
    eapply typing_spine_app; eauto.
  - invs H0.
    unshelve epose proof (d' := declared_inductive_to_gen d);
    unshelve epose proof (decli' := declared_inductive_to_gen decli); eauto.
    destruct (declared_inductive_inj d' decli') as [-> ->].
    clear decli. split; auto.
    destruct (on_declared_inductive d) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    apply typing_spine_refl.
    exact (declared_inductive_valid_type d _ _ a c).
  - specialize (IHtyping1 _ _ wfΣ decli) as [IH cu]; split; auto.
    eapply typing_spine_weaken_concl; pcuic.
Qed.

Lemma isType_mkApps_Ind_inv {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wf Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 ind mdecl idecl) :
  wf_local Σ Γ ->
  isType Σ Γ (mkApps (tInd ind u) args) ->
  ∑ parsubst argsubst,
    let parctx := (subst_instance u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0 (subst_instance u (idecl.(ind_indices)))) in
    [× spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx,
      spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx,
      #|firstn (ind_npars mdecl) args| = ind_npars mdecl,
      #|skipn (ind_npars mdecl) args| = context_assumptions idecl.(ind_indices) &
      consistent_instance_ext Σ (ind_universes mdecl) u].
Proof.
  move=> wfΓ isType.
  destruct isType as (_ & s & Hs & _).
  eapply invert_type_mkApps_ind in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductive declm).
  rename declm into decli.
  destruct decli' as [declm decli'].
  pose proof (decli'.(onArity)) as ar.
  rewrite decli'.(ind_arity_eq) in tyargs, ar.
  destruct ar as (_ & s' & ar & _). cbn in ar.
  rewrite !subst_instance_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spine in tyargs as [argslen leqs [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [argsubst parsubst].
  eexists _, _. move=> parctx argctx.
  rewrite context_assumptions_subst_instance in argsubst, parsubst.
  rewrite declm.(onNpars) in argsubst, parsubst.
  eapply subslet_app_inv in subs as [subp suba].
  rewrite subst_instance_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_length => //.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app_inv in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc in wfcodom.
  rewrite !lengths in argslen.
  move: (context_subst_length2 parsubst).
  now rewrite !lengths (declared_minductive_ind_npars decli).
  move: (context_subst_length2 argsubst).
  now rewrite !lengths.
Qed.

Lemma isType_mkApps_Ind_inv' {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wf Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 ind mdecl idecl) :
  wf_local Σ Γ ->
  isType Σ Γ (mkApps (tInd ind u) args) ->
  ∑ pars indices parsubst argsubst,
    let parctx := (subst_instance u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0 (subst_instance u (idecl.(ind_indices)))) in
    [× args = pars ++ indices,
      spine_subst Σ Γ pars parsubst parctx,
      spine_subst Σ Γ indices argsubst argctx,
      #|pars| = ind_npars mdecl,
      #|indices| = context_assumptions idecl.(ind_indices) &
      consistent_instance_ext Σ (ind_universes mdecl) u].
Proof.
  move=> wfΓ isType.
  destruct isType as (_ & s & Hs & _).
  eapply invert_type_mkApps_ind in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductive declm).
  rename declm into decli.
  destruct decli' as [declm decli'].
  pose proof (decli'.(onArity)) as ar.
  rewrite decli'.(ind_arity_eq) in tyargs, ar.
  destruct ar as (_ & s' & ar & _). cbn in ar.
  rewrite !subst_instance_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spine in tyargs as [argslen leqs [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [argsubst parsubst].
  eexists (firstn (ind_npars mdecl) args), (skipn (ind_npars mdecl) args), _, _.
  move=> parctx argctx.
  rewrite context_assumptions_subst_instance in argsubst, parsubst.
  rewrite declm.(onNpars) in argsubst, parsubst.
  eapply subslet_app_inv in subs as [subp suba].
  rewrite subst_instance_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_length => //.
  now rewrite firstn_skipn.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app_inv in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc in wfcodom.
  rewrite !lengths in argslen.
  move: (context_subst_length2 parsubst).
  now rewrite !lengths (declared_minductive_ind_npars decli).
  move: (context_subst_length2 argsubst).
  now rewrite !lengths.
Qed.

Lemma projection_subslet {cf:checker_flags} Σ Γ mdecl idecl u c p cdecl pdecl args :
  declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  wf Σ.1 ->
  Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
  isType Σ Γ (mkApps (tInd p.(proj_ind) u) args) ->
  subslet Σ Γ (c :: List.rev args) (projection_context p.(proj_ind) mdecl idecl u).
Proof.
  intros declp wfΣ Hc Ha.
  destruct (on_declared_projection declp) as [[onind eqctr] y].
  destruct (isType_mkApps_Ind_inv wfΣ (let (x, _) := declp in x.p1) (typing_wf_local Hc) Ha) as
    [parsubst [argsubst [sppars spargs cu]]].
  unfold projection_context.
  set (oib := declared_inductive_inv _ _ _ _) in *. clearbody oib.
  simpl in y.
  destruct (ind_ctors idecl) as [|ctors []] => //. noconf eqctr.
  destruct y as [[[_ onps] ?] ?].
  pose proof (on_projs_noidx _ _ _ _ _ _ onps).
  pose proof (onNpars onind).
  pose proof (context_subst_length2 spargs).
  rewrite context_assumptions_fold in H1.
  autorewrite with len in H1.
  destruct (ind_indices idecl); try discriminate.
  simpl in H1. rewrite List.length_skipn in H1.
  assert(#|args| = ind_npars mdecl).
  { pose proof (context_subst_length2 sppars).
    autorewrite with len in H2.
    rewrite H0 in H2.
    apply firstn_length_le_inv in H2. lia. }
  rewrite -H2 in sppars.
  rewrite firstn_all in sppars.
  eapply spine_subst_smash in sppars; auto.
  constructor. apply sppars.
  rewrite subst_mkApps /=.
  rewrite /argsubst in H1.
  now rewrite (spine_subst_subst_to_extended_list_k sppars).
Qed.

Lemma invert_red1_letin {cf:checker_flags} (Σ : global_env_ext) Γ C na d ty b :
  red1 Σ.1 Γ (tLetIn na d ty b) C ->
  (∑ d', (C = tLetIn na d' ty b) *
    red1 Σ.1 Γ d d') +
  (∑ ty', (C = tLetIn na d ty' b) *
    red1 Σ.1 Γ ty ty') +
  (∑ b', (C = tLetIn na d ty b') *
    red1 Σ.1 (Γ ,, vdef na d ty) b b') +
  (C = subst10 d b)%type.
Proof.
  intros H; depelim H; try solve_discr; pcuicfo auto.
  - left. left. left. eexists; eauto.
  - left. left. right. eexists; eauto.
  - left. right. eexists; eauto.
Qed.

Lemma decompose_prod_assum_it_mkProd_or_LetIn' ctx Γ t :
  decompose_prod_assum ctx (it_mkProd_or_LetIn Γ t) =
  let (ctx', t') := decompose_prod_assum [] t in
  (ctx ,,, Γ ,,, ctx', t').
Proof.
  generalize ctx.
  induction Γ using rev_ind; simpl; intros.
  - now rewrite decompose_prod_assum_ctx.
  - rewrite it_mkProd_or_LetIn_app.
    destruct x as [na [b|] ty]; simpl.
    rewrite IHΓ.
    destruct (decompose_prod_assum [] t).
    now rewrite app_context_assoc.
    rewrite IHΓ.
    destruct (decompose_prod_assum [] t).
    now rewrite app_context_assoc.
Qed.

Lemma destInd_head_subst s k t f : destInd (head (subst s k t)) = Some f ->
  (destInd (head t) = Some f) +
  (∑ n u, (head t = tRel n) /\ k <= n /\ (nth_error s (n - k) = Some u /\ destInd (head  (lift0 k u)) = Some f)).
Proof.
  induction t in s, k, f |- *; simpl; try solve [pcuicfo auto].
  elim: leb_spec_Set => le; intros destI.
   right.
  destruct nth_error eqn:Heq.
  - exists n, t; intuition auto.
  - simpl in destI => //.
  - simpl => //.
  - intros destI. rewrite head_tapp in destI.
    rewrite head_tapp.
    specialize (IHt1 _ _ _ destI).
    destruct IHt1 as [?|[n [u [headt1 [hnth hind]]]]].
    * left; auto.
    * right. exists n, u; intuition auto.
Qed.

Lemma destInd_head_lift n b ind u : destInd (head (lift0 n b)) = Some (ind, u) ->
  destInd (head b) = Some (ind, u).
Proof.
  induction b; simpl; try discriminate.
  rewrite !head_tapp. apply IHb1.
  congruence.
Qed.

Lemma destInd_head_lift_inv n b ind u : destInd (head b) = Some (ind, u) ->
  destInd (head (lift0 n b)) = Some (ind, u).
Proof.
  induction b; simpl; try discriminate.
  rewrite !head_tapp. apply IHb1.
  congruence.
Qed.

Lemma head_subst s k t : head (subst s k t) = head (subst s k (head t)).
Proof.
  induction t; simpl; auto.
  now rewrite !head_tapp.
Qed.

#[global]
Hint Rewrite context_assumptions_app @context_assumptions_subst : len.

Lemma red1_destInd (Σ : global_env_ext) Γ t t' ind u :
  red1 Σ.1 Γ t t' -> destInd (head t) = Some (ind, u) ->
  destInd (head t') = Some (ind, u).
Proof.
  induction 1; simpl in *; try discriminate.
  unfold head.
  remember (mkApps (tFix mfix idx) args) eqn:decapp.
  symmetry in decapp. pose proof (mkApps_Fix_spec _ _ _ _ decapp).
  destruct (decompose_app t); simpl in *; try discriminate.
  destruct t0; try discriminate.
  elim H.
  rewrite !head_tapp. auto.
  rewrite !head_tapp. auto.
Qed.

Lemma red_destInd (Σ : global_env_ext) Γ t t' ind u :
  red Σ.1 Γ t t' -> destInd (head t) = Some (ind, u) ->
  destInd (head t') = Some (ind, u).
Proof.
  intros r%Relation_Properties.clos_rt_rt1n_iff.
  induction r.
  auto.
  intros.
  eapply red1_destInd in H. apply IHr. eauto.
  eauto.
Qed.

Lemma destInd_Some_eq t ind u : destInd t = Some (ind, u) -> t = tInd ind u.
Proof.
  destruct t; simpl; congruence.
Qed.

Lemma is_closed_context_expand_let Γ na b ty Δ :
  is_closed_context (Γ ,, vdef na b ty ,,, Δ) ->
  is_closed_context (Γ ,,, subst_context [b] 0 Δ).
Proof.
  intros iscl.
  eapply (is_closed_subst_context _ ([vdef na b ty])); cbn; tea => //.
  move: iscl. rewrite on_free_vars_ctx_app on_free_vars_ctx_snoc => /andP[] /andP[] _ /andP[] isb.
  rewrite andb_true_r => //.
Qed.

Lemma red_it_mkProd_or_LetIn_smash {cf} {Σ} {wfΣ : wf Σ} Γ ctx t u n c :
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  ∑ ctx' t' d,
    [× (decompose_prod_assum [] u = (ctx', t')),
       (nth_error (List.rev (smash_context [] ctx')) n = Some d) &
        Σ ;;; Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d ].
Proof.
  rename Γ into Δ.
  revert Δ t u n c.
  induction ctx using ctx_length_rev_ind; simpl; intros Δ t u n c r.
  rewrite nth_error_nil => //.
  destruct d as [na [b|] ty].
  rewrite it_mkProd_or_LetIn_app in r.
  simpl in *.
  eapply invert_red_letin in r as [[d' [ty' [b' [-> redb redty redbody]]]]|]; auto.
  - intros Hnth.
    rewrite !smash_context_app smash_context_acc in Hnth |- *; simpl in *.
    pose proof (nth_error_Some_length Hnth).
    autorewrite with len in H. simpl in H.
    rewrite nth_error_rev_inv in Hnth.
    now autorewrite with len.
    autorewrite with len in Hnth. simpl in Hnth.
    rewrite subst_empty lift0_id lift0_context in Hnth.
    rewrite app_nil_r in Hnth.
    rewrite nth_error_subst_context in Hnth.
    unfold snoc; simpl.
    rewrite decompose_prod_assum_ctx.
    specialize (X Γ ltac:(lia)).
    destruct nth_error eqn:hnth.
    specialize (X _ _ _ n c0 redbody).
    rewrite nth_error_rev_inv in X; autorewrite with len. auto.
    autorewrite with len in X |- *. simpl in *.
    specialize (X hnth).
    destruct X as [ctx' [t' [d [decompb hnth' hred]]]].
    rewrite decompb. eexists _, _, _. split; eauto.
    have hlen := nth_error_Some_length hnth'.
    autorewrite with len in hlen.
    rewrite nth_error_rev_inv in hnth'; autorewrite with len. auto.
    rewrite nth_error_rev_inv; autorewrite with len. cbn.
    rewrite context_assumptions_app /=. simpl in hlen. lia.
    rewrite smash_context_app smash_context_acc /= app_nil_r.
    rewrite subst_empty lift0_id lift0_context.
    rewrite nth_error_subst_context /=.
    autorewrite with len. simpl in *.
    rewrite context_assumptions_app /=. simpl.
    rewrite Nat.add_0_r. autorewrite with len in hnth'. rewrite hnth'.
    simpl. reflexivity. simpl.
    autorewrite with len in Hnth. simpl in Hnth. move: Hnth.
    intros [= <-]. cbn.
    assert (context_assumptions Γ -
    S (context_assumptions Γ - S n) = n) as -> by lia.
    pose proof (nth_error_Some_length hnth'). len in H0.
    assert (context_assumptions ctx' -
    S (context_assumptions ctx'  - S n) = n) as -> by lia.
    simpl.
    rewrite app_nil_r.
    transitivity (subst [b] n (decl_type d)).
    rewrite subst_empty lift0_id lift0_context.
    epose proof (@closed_red_untyped_substitution _ _ _ Δ [vdef na b ty] (skipn (context_assumptions Γ - n) (smash_context [] Γ)) [b]
      (decl_type c0) (decl_type d)).
    forward X. rewrite -{1}(subst_empty 0 b). repeat constructor.
    forward X. cbn. rewrite andb_true_r. eapply redb.
    forward X. eapply hred.
    rewrite skipn_subst_context.
    rewrite !length_skipn in X.
    len in X. simpl in X.
    assert(context_assumptions Γ - (context_assumptions Γ - n) = n) by lia.
    rewrite H1 in X. apply X.
    epose proof (@closed_red_red_subst _ _ _ Δ [vdef na b ty]
       (skipn (context_assumptions Γ - n) (smash_context [] Γ)) _ _ _).
    rewrite subst_empty lift0_id lift0_context.
    rewrite !length_skipn in X; autorewrite with len.
    autorewrite with len in X. simpl in X.
    assert(context_assumptions Γ - (context_assumptions Γ - n) = n) by lia.
    rewrite H1 in X. rewrite skipn_subst_context.
    eapply X; auto. 2:rewrite -{1}(subst_empty 0 b); repeat constructor.
    3:simpl in Hnth; discriminate.
    clear X.
    apply hred. clear X.
    apply closed_red_open_right in hred.
    len in hred.

  - rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in c0.
    intros hnth.
    rewrite smash_context_app smash_context_acc /= app_nil_r in hnth.
    rewrite subst_empty lift0_id lift0_context in hnth.
    specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; lia)).
    specialize (X _ _ _ n c c0).
    rewrite (smash_context_subst []) in X.
    specialize (X hnth). len.
    len in X. simpl in X.
    rewrite smash_context_app smash_context_acc /=.
    rewrite subst_empty lift0_id lift0_context app_nil_r.
    apply X.

  - rewrite smash_context_app /= List.rev_app_distr /=.
    move=> hnth.
    rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in r.
    eapply invert_red_prod in r as [A' [B' [-> redty redB']]]; auto.
    simpl. rewrite decompose_prod_assum_ctx.
    destruct n.
    * simpl in hnth. noconf hnth; simpl in *.
      destruct (decompose_prod_assum [] B') eqn:decomp.
      eexists _, _, _; split; eauto.
      unfold snoc; simpl. rewrite smash_context_app /= List.rev_app_distr /= //.
      len. simpl.
      rewrite skipn_all2. len. simpl => //.
    * simpl in hnth.
      specialize (X Γ ltac:(lia) (vass na ty :: Δ) t B' n c redB' hnth).
      destruct X as [ctx' [t' [decomp [d hnth' red]]]].
      rewrite d. simpl. eexists _, _, _; split; eauto.
      unfold snoc; simpl. rewrite smash_context_app /= List.rev_app_distr /= hnth' //.
      rewrite length_app. simpl. len.
      assert (context_assumptions Γ + 1 - S n = context_assumptions Γ - n) by lia.
      rewrite H. rewrite skipn_app. len.
      rewrite [skipn _ [_]]skipn_0_eq. lia.
      rewrite app_context_assoc. unfold app_context in red |- *.
      simpl. len in red.
Qed.

Lemma red1_it_mkProd_or_LetIn_smash {cf} {Σ} {wfΣ : wf Σ} {Γ ctx t u n c} :
  closed_red1 Σ Γ (it_mkProd_or_LetIn ctx t) u ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  ∑ ctx' t',
    (decompose_prod_assum [] u = (ctx', t')) *
    ∑ d, (nth_error (List.rev (smash_context [] ctx')) n = Some d) *
      (match destInd (head (decl_type c)) with
      | Some ind => destInd (head (decl_type d)) = Some ind
      | None => True
      end).
Proof.
  intros r nth.
  eapply red_it_mkProd_or_LetIn_smash in nth; eauto.
  destruct nth as [ctx' [t' [d [decomp hnth r']]]].
  exists ctx', t'. split; eauto.
  exists d; intuition auto.
  destruct destInd as [[ind u']|] eqn:di; auto.
  now eapply (red_destInd _ _ _ _ _ _ r').
  destruct r. eapply into_closed_red.
  eapply red1_red; tea. all:auto.
Qed.

Lemma red_it_mkProd_or_LetIn_mkApps_Ind {cf} {Σ} {wfΣ : wf Σ} {Γ ctx ind u args v} :
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args) ⇝ v ->
  ∑ ctx' args', v = it_mkProd_or_LetIn ctx' (mkApps (tInd ind u) args').
Proof.
  rename Γ into Δ.
  revert Δ v args.
  induction ctx using ctx_length_rev_ind; simpl; intros Δ v args r.
  - eapply invert_red_mkApps_tInd in r as [args' [-> conv]];  auto.
    now exists [], args'.
  - rewrite it_mkProd_or_LetIn_app in r.
    destruct d as [na [b|] ty].
    simpl in *.
    eapply invert_red_letin in r as [[d' [ty' [b' [-> redb redty redbody]]]]|]; auto.
    * specialize (X Γ ltac:(lia) _ _ _ redbody).
      destruct X as [ctx' [args' ->]].
      exists (ctx' ++ [vdef na d' ty']).
      exists args'. now rewrite it_mkProd_or_LetIn_app /=.
    * rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps /= in c.
      specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; lia) _ _ _ c).
      apply X.
    * simpl in r.
      eapply invert_red_prod in r as [A' [B' [-> redty redB']]]; auto.
      specialize (X Γ ltac:(lia) _ _ _ redB') as [ctx' [args' ->]].
      exists (ctx' ++ [vass na A']), args'.
      rewrite it_mkProd_or_LetIn_app /= //.
Qed.

Lemma wf_local_expand_lets {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Γ'} :
  wf_local Σ (Γ ,,, Δ ,,, Γ') ->
  wf_local Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ').
Proof.
  intros hwf.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  destruct (All_local_env_app_inv hwf) as [wfΓΔ _].
  rewrite -app_context_assoc in hwf.
  eapply (weakening_wf_local (Γ'' := smash_context [] Δ)) in hwf.
  len in hwf. simpl in hwf. simpl.
  2:{ eapply wf_local_smash_end; pcuic. }
  rewrite lift_context_app app_context_assoc Nat.add_0_r in hwf.
  eapply substitution_wf_local in hwf; tea.
  now eapply PCUICContexts.subslet_extended_subst.
Qed.


Lemma typing_expand_lets_gen {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Γ' t T} :
  Σ ;;; Γ ,,, Δ ,,, Γ' |- t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' |-
    expand_lets_k Δ #|Γ'| t : expand_lets_k Δ #|Γ'| T.
Proof.
  intros Ht.
  rewrite /expand_lets /expand_lets_k.
  pose proof (typing_wf_local Ht).
  rewrite -app_context_assoc in Ht.
  eapply (weakening_typing (Γ'' := smash_context [] Δ)) in Ht.
  len in Ht. simpl in Ht. simpl.
  2:{ eapply wf_local_smash_end; pcuic. now apply All_local_env_app_inv in X. }
  rewrite lift_context_app app_context_assoc Nat.add_0_r in Ht.
  eapply substitution in Ht; tea.
  2:{ eapply PCUICContexts.subslet_extended_subst. now apply All_local_env_app_inv in X. }
  now len in Ht.
Qed.

Lemma expand_lets_k_subst_comm Δ k s T :
  expand_lets_k Δ k (subst0 s T) =
  subst0 (map (expand_lets_k Δ k) s) (expand_lets_k Δ (#|s| + k) T).
Proof.
  rewrite /expand_lets_k.
  now rewrite distr_lift_subst distr_subst Nat.add_assoc map_map_compose; len.
Qed.

Definition subst_let_expand_k args Δ k T :=
  (subst args k (expand_lets_k Δ k T)).

Lemma map_subst_let_expand_k args Δ k l :
  map (subst args k) (map (expand_lets_k Δ k) l) =
  map (subst_let_expand_k args Δ k) l.
Proof.
  now rewrite map_map_compose.
Qed.

Lemma subst_let_expand_k_0 s Γ :
  subst_let_expand_k s Γ 0 ≐1 subst_let_expand s Γ.
Proof. reflexivity. Qed.



Lemma subst_let_expand_it_mkProd_or_LetIn s Γ Δ T :
  subst_let_expand s Γ (it_mkProd_or_LetIn Δ T) =
  it_mkProd_or_LetIn (subst_context_let_expand s Γ Δ) (subst_let_expand_k s Γ #|Δ| T).
Proof.
  rewrite /subst_let_expand /expand_lets.
  rewrite expand_lets_it_mkProd_or_LetIn /= subst_it_mkProd_or_LetIn /=.
  len.
Qed.

Lemma subst_let_expand_k_mkApps s Γ k f args :
  subst_let_expand_k s Γ k (mkApps f args) =
  mkApps (subst_let_expand_k s Γ k f) (map (subst_let_expand_k s Γ k) args).
Proof.
  rewrite /subst_let_expand_k.
  now rewrite expand_lets_k_mkApps subst_mkApps map_map_compose.
Qed.

Lemma expand_lets_k_to_extended_list_k Γ k :
  map (expand_lets_k Γ k) (to_extended_list_k Γ k) = to_extended_list_k (smash_context [] Γ) k.
Proof.
  rewrite /expand_lets_k -map_map_compose.
  rewrite -extended_subst_to_extended_list_k.
  f_equal. now rewrite Nat.add_comm -to_extended_list_k_map_lift.
Qed.

Lemma map_subst_let_expand_k_to_extended_list_lift {cf} {Σ s Γ Δ k} :
  spine_subst Σ Γ s (List.rev s) (smash_context [] Δ) ->
  map (subst_let_expand_k (List.rev s) Δ k) (to_extended_list_k Δ k) = map (lift0 k) s.
Proof.
  intros sp.
  eapply spine_subst_subst_to_extended_list_k in sp.
  rewrite /subst_let_expand_k.
  rewrite -map_map_compose.
  rewrite expand_lets_k_to_extended_list_k.
  rewrite -{2}(Nat.add_0_r k).
  rewrite PCUICLiftSubst.lift_to_extended_list_k -{2}sp !map_map_compose.
  apply map_ext. intros x.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma map_subst_let_expand_to_extended_list {cf} {Σ s Γ Δ} :
  spine_subst Σ Γ s (List.rev s) (smash_context [] Δ) ->
  map (subst_let_expand (List.rev s) Δ) (to_extended_list Δ) = s.
Proof.
  intros sp.
  specialize (map_subst_let_expand_k_to_extended_list_lift (k:=0) sp).
  now rewrite map_lift0.
Qed.

Lemma map_subst_let_expand_lift {s Γ k s'} :
  #|s| = context_assumptions Γ -> k = #|Γ| ->
  map (subst_let_expand s Γ) (map (lift0 k) s') = s'.
Proof.
  intros hs hlen.
  rewrite /subst_let_expand map_map_compose.
  rewrite -{2}(map_id s'). apply map_ext => t.
  rewrite /expand_lets /expand_lets_k /=.
  sigma. rewrite hlen.
  rewrite -subst_compose_assoc.
  rewrite shiftn_Upn. sigma.
  (rewrite subst_consn_shiftn; try now len); [].
  now rewrite subst_consn_shiftn; sigma.
Qed.

Lemma subst_let_expand_k_lift s Γ n k t :
  n = #|Γ| -> #|s| = context_assumptions Γ ->
  subst_let_expand_k s Γ 0 (lift0 (n + k) t) = lift0 k t.
Proof.
  intros.
  rewrite -(simpl_lift _ _ _ _ 0); try lia.
  rewrite subst_let_expand_k_0.
  rewrite subst_let_expand_lift_id //.
Qed.

Lemma expand_lets_k_0 Γ t : expand_lets_k Γ 0 t = expand_lets Γ t.
Proof. reflexivity. Qed.


Lemma smash_context_app_expand_acc Γ Δ :
  smash_context [] Γ ,,, expand_lets_ctx Γ Δ =
  smash_context Δ Γ.
Proof.
  rewrite (smash_context_acc Γ Δ). reflexivity.
Qed.

Lemma expand_lets_ctx_app Δ Γ Γ' :
  expand_lets_ctx Δ (Γ ,,, Γ') = expand_lets_ctx Δ Γ ,,, expand_lets_k_ctx Δ #|Γ| Γ'.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx lift_context_app subst_context_app; len => //.
Qed.

Lemma lift_context_subst Γ p s n k :
  context_subst Γ p s ->
  context_subst (lift_context n k Γ) (map (lift n k) p) (map (lift n k) s).
Proof.
  induction 1 in |- *; try constructor.
  rewrite lift_context_snoc map_app /=; constructor; auto.
  rewrite lift_context_snoc /= /lift_decl /map_decl /=.
  rewrite (context_subst_length X).
  rewrite distr_lift_subst.
  now constructor.
Qed.

Lemma subst_context_subst Γ p s sub k :
  context_subst Γ p s ->
  context_subst (subst_context sub k Γ) (map (subst sub k) p) (map (subst sub k) s).
Proof.
  induction 1 in |- *; try constructor.
  rewrite subst_context_snoc map_app /=; constructor; auto.
  rewrite subst_context_snoc /= /subst_decl /map_decl /=.
  rewrite (context_subst_length X).
  rewrite distr_subst.
  now constructor.
Qed.

Lemma subslet_smash_context {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Γ' Δ' s} :
  subslet Σ (Γ ,,, Δ ,,, Γ') s Δ' ->
  subslet Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ')
    (map (expand_lets_k Δ #|Γ'|) s) (expand_lets_k_ctx Δ #|Γ'| Δ').
Proof.
  induction 1.
  * simpl. constructor.
  * simpl. rewrite /expand_lets_k_ctx lift_context_snoc subst_context_snoc.
    constructor. apply IHX. len.
    rewrite Nat.add_assoc. fold (expand_lets_k Δ (#|Δ0| + #|Γ'|) T).
    eapply typing_expand_lets_gen in t0.
    rewrite expand_lets_k_subst_comm in t0.
    now rewrite -(subslet_length X).
  * simpl. rewrite /expand_lets_k_ctx lift_context_snoc subst_context_snoc.
    len. rewrite /subst_decl /lift_decl /map_decl /=.
    eapply subslet_def. apply IHX. len.
    rewrite !Nat.add_assoc.
    fold (expand_lets_k Δ (#|Δ0| + #|Γ'|) t).
    fold (expand_lets_k Δ (#|Δ0| + #|Γ'|) T).
    eapply typing_expand_lets_gen in t0.
    rewrite !expand_lets_k_subst_comm in t0.
    now rewrite -(subslet_length X).
    now rewrite expand_lets_k_subst_comm -(subslet_length X) Nat.add_assoc.
Qed.

Lemma spine_subst_expand_lets {cf Σ} {wfΣ : wf Σ} {Γ Δ Γ'} {inst s Δ'} :
  spine_subst Σ (Γ ,,, Δ ,,, Γ') inst s Δ' ->
  spine_subst Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ')
    (map (expand_lets_k Δ #|Γ'|) inst) (map (expand_lets_k Δ #|Γ'|) s)
    (expand_lets_k_ctx Δ #|Γ'| Δ').
Proof.
  intros [].
  split.
  * rewrite -app_context_assoc.
    rewrite smash_context_app_expand_acc.
    eapply All_local_env_app_inv in spine_dom_wf as [wfΔ wfΓ'].
    eapply All_local_env_app. now apply All_local_env_app_inv in wfΔ.
    eapply wf_local_rel_smash_context_gen; tea.
  * eapply All_local_env_app_inv in spine_codom_wf as [wfΔ wfΓ'].
    rewrite - !app_context_assoc -expand_lets_ctx_app.
    apply All_local_env_app_inv in wfΔ as [].
    eapply All_local_env_app.
    now apply All_local_env_app_inv in a as [].
    rewrite smash_context_app_expand_acc.
    apply wf_local_rel_smash_context_gen; tea.
    eapply All_local_rel_app; tea.
  * rewrite /expand_lets_k_ctx /expand_lets_k -map_map_compose -[map (fun t => _) s]map_map_compose.
    eapply subst_context_subst.
    now eapply lift_context_subst.
  * now eapply subslet_smash_context.
Qed.

Lemma subst_lift_subst s k t : subst s k (lift0 k t) = lift0 k (subst s 0 t).
Proof.
  replace k with (0 + k) by lia.
  rewrite -commut_lift_subst_rec. lia. simpl. reflexivity.
Qed.

(* We show that the derived predicate of a case is always well-typed, for *any*
  instance of the parameters (not just the ones from a well-formed predicate). *)
Lemma wf_ind_predicate {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} u :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (Γ ,,, smash_context [] (ind_params mdecl)@[u] ,,, (ind_predicate_context ci mdecl idecl)@[u]).
Proof.
  move=> wfΓ isdecl cu.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  set (iass := {| decl_name := _ |}).
  cbn.
  rewrite [subst_instance_context _ _]subst_instance_expand_lets_ctx.
  unshelve epose proof (on_inductive_inst isdecl _ _ _ cu); tea.
  rewrite -/(subst_context_let_expand _ _ _).
  rewrite subst_instance_app_ctx in X.
  destruct X as (_ & s & Hs & _ & Her).
  eapply type_it_mkProd_or_LetIn_inv in Hs as (idxs & inds & [sortsidx sortind leq]).
  set (idxctx := smash_context [] (ind_params mdecl)@[u] ,,, expand_lets_ctx (ind_params mdecl)@[u] (ind_indices idecl)@[u]) in *.
  have tyass : Σ ;;; Γ ,,, idxctx |- (decl_type iass)@[u] : tSort (ind_sort idecl)@[u].
  { pose proof (on_inductive_sort_inst isdecl _ cu).
    rewrite /iass /=.
    have wfidxctx : wf_local Σ (Γ ,,, idxctx).
    { rewrite /idxctx. rewrite app_context_assoc.
      apply wf_local_expand_lets. rewrite -app_context_assoc.
      eapply weaken_wf_local => //. rewrite -subst_instance_app_ctx.
      eapply on_minductive_wf_params_indices_inst; tea.
    }
    generalize wfidxctx. rewrite {1}/idxctx {1}app_context_assoc => wfidxctx'.
    rewrite subst_instance_mkApps /=; cbn.
    erewrite subst_instance_id_mdecl; tea.
    eapply pre_type_mkApps_arity. econstructor; tea.
    eapply isTypeRel_isType, declared_inductive_valid_type; tea.
    pose proof (on_declared_inductive isdecl) as [onmind oib].
    rewrite oib.(ind_arity_eq) !subst_instance_it_mkProd_or_LetIn
      subst_instance_to_extended_list subst_instance_app_ctx
      subst_instance_smash.
    rewrite /to_extended_list to_extended_list_k_app.
    rewrite Nat.add_0_r. len.
    eapply arity_spine_it_mkProd_or_LetIn_smash.
    - rewrite -(closed_ctx_lift #|ind_indices idecl| 0 (ind_params mdecl)@[u]).
      { rewrite closedn_subst_instance_context.
        eapply (declared_inductive_closed_params isdecl). }
      rewrite (smash_context_lift []).
      rewrite /idxctx app_context_assoc.
      rewrite to_extended_list_k_lift_context.
      replace #|ind_indices idecl| with (#|ind_indices idecl| + 0) by lia.
      rewrite PCUICLiftSubst.lift_to_extended_list_k Nat.add_0_r.
      rewrite -map_rev.
      relativize #|ind_indices idecl|.
      eapply subslet_lift; tea => //; len. 2:len.
      epose proof (spine_subst_to_extended_list_k (Γ := Γ) (Δ := smash_context [] (ind_params mdecl)@[u])); tea.
      forward X.
      { apply wf_local_smash_end, weaken_wf_local => //. eapply (on_minductive_wf_params isdecl); tea. }
      destruct X. len in inst_subslet.
      rewrite PCUICClosed.closed_ctx_lift in inst_subslet => //.
      apply closedn_smash_context.
      rewrite closedn_subst_instance_context.
      apply (declared_inductive_closed_params isdecl).
      rewrite all_rels_smash in inst_subslet.
      { apply smash_context_assumption_context. constructor. }
      apply inst_subslet.
    - have clpars : closed_ctx (ind_params mdecl).
      { apply (declared_inductive_closed_params isdecl). }
      have clinds : closedn_ctx #|(ind_params mdecl)| (ind_indices idecl)@[u].
      { epose proof (declared_inductive_closed_pars_indices isdecl).
        len. rewrite closedn_subst_instance_context.
        rewrite closedn_ctx_app in H0. now move/andP: H0. }
      rewrite subst_let_expand_it_mkProd_or_LetIn /=. simpl.
      eapply arity_spine_it_mkProd_or_LetIn_Sort => //. reflexivity.
      rewrite /subst_context_let_expand.
      relativize (subst_context _ _ _).
      rewrite /idxctx app_context_assoc.
      rewrite subst_instance_expand_lets_ctx.
      eapply spine_subst_to_extended_list_k => //; len.
      rewrite distr_lift_subst_context PCUICClosed.closed_ctx_lift //.
      rewrite PCUICClosed.closed_ctx_lift //; len. cbn. len.
      rewrite PCUICClosed.closed_ctx_lift //.
      rewrite subst_map_lift_lift_context; len => //.
      rewrite -extended_subst_to_extended_list_k -map_rev.
      replace #|ind_indices idecl| with (#|ind_indices idecl| + 0) by len.
      rewrite PCUICLiftSubst.lift_to_extended_list_k Nat.add_0_r.
      rewrite -map_rev map_map_compose.
      setoid_rewrite subst_lift_subst.
      rewrite -map_map_compose map_rev extended_subst_to_extended_list_k map_rev
         -PCUICLiftSubst.lift_to_extended_list_k Nat.add_0_r
         -subst_context_map_subst_expand_lets; len.
      rewrite subst_extended_lift //; len. now rewrite closedn_subst_instance_context.
      rewrite (lift_extended_subst _ #|ind_indices _|) subst_map_lift_lift_context; len. }
  constructor => //.
  2:{ eapply has_sort_isTypeRel.
    2: rewrite /idxctx app_context_assoc in tyass; tea.
    rewrite relevance_subst_eq.
    pose proof (on_declared_inductive isdecl) as [onmind oib]. apply oib.(ind_relevance_compat). }
  apply typing_wf_local in tyass.
  rewrite /idxctx app_context_assoc in tyass => //.
Qed.

(* We show that the derived predicate of a case is always well-typed, for *any*
  instance of the parameters (not just the ones from a well-formed predicate). *)
Lemma isType_case_predicate {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} u params ps :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_sort Σ ps ->
  spine_subst Σ Γ params (List.rev params) (smash_context [] (subst_instance u (ind_params mdecl))) ->
  isType Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps)).
Proof.
  move=> wfΓ isdecl cu wfps sp.
  pose proof (on_declared_inductive isdecl) as [onmind oib].
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  set (iass := {| decl_name := _ |}).
  cbn.
  rewrite [map (map_decl _) _]subst_instance_expand_lets_ctx.
  rewrite subst_context_snoc /=. len.
  unshelve epose proof (on_inductive_inst isdecl _ _ _ cu); tea.
  rewrite -/(subst_context_let_expand _ _ _).
  rewrite subst_instance_app_ctx in X.
  destruct X as (_ & s & Hs & _).
  eapply isType_it_mkProd_or_LetIn_app in Hs.
  2:eapply sp.
  rewrite subst_let_expand_it_mkProd_or_LetIn in Hs.
  eapply type_it_mkProd_or_LetIn_inv in Hs as (idxs & inds & [sortsidx sortind leq]).
  eapply has_sort_isType with (s := sort_of_products (subst_instance u (ind_sort idecl) :: idxs)
    (Sort.super ps)).
  set (idxctx := subst_context_let_expand _ _ _) in *.
  have tyass : Σ ;;; Γ ,,, idxctx |-
    subst (List.rev params) #|ind_indices idecl| (decl_type iass)@[u] : tSort (ind_sort idecl)@[u].
  { pose proof (on_inductive_sort_inst isdecl _ cu).
    rewrite /iass /=.
    have wfidxctx : wf_local Σ (Γ ,,, idxctx) by pcuic.
    rewrite subst_instance_mkApps /=; cbn.
    erewrite subst_instance_id_mdecl; tea.
    rewrite subst_mkApps. cbn.
    eapply pre_type_mkApps_arity. econstructor; tea.
    eapply isTypeRel_isType, declared_inductive_valid_type; tea.
    rewrite oib.(ind_arity_eq) !subst_instance_it_mkProd_or_LetIn
      subst_instance_to_extended_list subst_instance_app_ctx
      subst_instance_smash.
    (* rewrite -it_mkProd_or_LetIn_app. *)
    rewrite /to_extended_list to_extended_list_k_app.
    rewrite map_app Nat.add_0_r. len.
    eapply arity_spine_it_mkProd_or_LetIn_smash.
    erewrite subst_to_extended_list_k.
    2:{ eapply make_context_subst_spec_inv.
        rewrite List.rev_involutive. cbn.
        eapply sp. }
    len.
    rewrite -(closed_ctx_lift #|ind_indices idecl| 0 (ind_params mdecl)@[u]).
    { rewrite closedn_subst_instance_context.
      eapply (declared_inductive_closed_params isdecl). }
    rewrite (smash_context_lift []) -map_rev.
    relativize #|ind_indices idecl|.
    eapply subslet_lift; tea.
    apply sp. len.
    rewrite subst_let_expand_it_mkProd_or_LetIn /=.
    eapply arity_spine_it_mkProd_or_LetIn_Sort => //. reflexivity.
    rewrite -subst_instance_to_extended_list_k.
    rewrite /expand_lets_ctx /expand_lets_k_ctx.
    rewrite to_extended_list_k_subst to_extended_list_k_lift_context.
    rewrite map_subst_instance_to_extended_list_k.
    rewrite -to_extended_list_k_map_subst. lia.
    relativize (subst_context_let_expand (List.rev (map _ _)) _ _).
    relativize (to_extended_list_k _ _).
    eapply spine_subst_to_extended_list_k; tea.
    rewrite [reln [] _ _]to_extended_list_subst_context_let_expand.
    apply PCUICLiftSubst.map_subst_instance_to_extended_list_k.
    rewrite subst_context_let_expand_length subst_instance_length.
    rewrite /subst_context_let_expand.
    rewrite distr_lift_subst_context map_rev.
    rewrite PCUICClosed.closed_ctx_lift //.
    pose proof (PCUICContextSubst.context_subst_length2 sp).
    rewrite context_assumptions_smash_context /= in H0. len in H0. len.
    rewrite H0.
    relativize (context_assumptions _).
    eapply (PCUICClosed.closedn_ctx_expand_lets 0); len.
    rewrite closedn_subst_instance_context.
    apply (declared_inductive_closed_params isdecl).
    2:len.
    epose proof (declared_inductive_closed_pars_indices isdecl).
    rewrite closedn_ctx_app in H1.
    rewrite closedn_subst_instance_context.
    move/andP: H1 => [] //.
    f_equal. f_equal.
    erewrite subst_to_extended_list_k => //.
    eapply make_context_subst_spec_inv. rewrite List.rev_involutive. cbn. apply sp. }
  set (sdecl := subst_decl _ _ _).
  rewrite -(it_mkProd_or_LetIn_app [sdecl]).
  eapply type_it_mkProd_or_LetIn_sorts; tea.
  constructor => //. repeat (eexists; tea). apply relevance_subst, oib.(ind_relevance_compat).
  constructor => //. simpl.
  constructor => //.
  now eapply sorts_local_ctx_wf_local; tea.
  repeat (eexists; tea).
  apply relevance_subst, oib.(ind_relevance_compat).
Qed.

Lemma arity_spine_case_predicate {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {u params indices ps} {c} :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_sort Σ ps ->
  spine_subst Σ Γ params (List.rev params)
    (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_subst Σ Γ indices (List.rev indices)
    (subst_context_let_expand (List.rev params)
        (subst_instance u (ind_params mdecl))
        (smash_context [] (subst_instance u (ind_indices idecl)))) ->
  Σ ;;; Γ |- c : mkApps (tInd ci u) (params ++ indices) ->
  arity_spine Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps))
    (indices ++ [c]) (tSort ps).
Proof.
  move=> wfΓ isdecl cu wfps sppars spidx Hc.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context.
  rewrite subst_instance_cons subst_instance_expand_lets_ctx.
  rewrite subst_context_snoc /=. len.
  eapply arity_spine_it_mkProd_or_LetIn_smash; tea.
  rewrite (smash_context_subst []).
  rewrite /subst_context_let_expand (expand_lets_smash_context _ [])
    expand_lets_k_ctx_nil /= in spidx; cbn.
  apply spidx. rewrite subst_let_expand_tProd /=.
  constructor.
  2:econstructor.
  set (ictx := subst_instance u _).
  eapply meta_conv; tea.
  rewrite subst_instance_mkApps subst_mkApps /=.
  erewrite subst_instance_id_mdecl; tea.
  rewrite subst_let_expand_mkApps subst_let_expand_tInd.
  f_equal.
  rewrite !subst_instance_to_extended_list subst_instance_app_ctx.
  rewrite /to_extended_list to_extended_list_k_app !map_app. f_equal.
  len.
  erewrite subst_to_extended_list_k => //.
  2:{ eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
      rewrite subst_instance_smash.
      eapply sppars. }
  rewrite -{1}[params](map_id params).
  rewrite map_map_compose; eapply map_ext => x.
  setoid_rewrite subst_let_expand_lift_id; auto.
  now rewrite /ictx; len.
  rewrite /ictx /expand_lets_ctx /expand_lets_k_ctx; len.
  pose proof (PCUICContextSubst.context_subst_length2 spidx).
  rewrite /subst_context_let_expand in H. now len in H.
  (* Should be a lemma *)
  rewrite -subst_context_map_subst_expand_lets.
  rewrite /ictx; len.
  pose proof (PCUICContextSubst.context_subst_length2 sppars).
  now rewrite context_assumptions_smash_context /= in H; len in H.
  rewrite /subst_let_expand /expand_lets /expand_lets_k.
  rewrite -map_map_compose.
  rewrite -{1}(spine_subst_subst_to_extended_list_k spidx).
  f_equal. len.
  rewrite to_extended_list_k_subst /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !to_extended_list_k_subst to_extended_list_k_lift_context.
  rewrite -map_map_compose. simpl. len.
  set (ctx := subst_context _ _ _).
  rewrite -subst_instance_to_extended_list_k.
  rewrite to_extended_list_k_subst to_extended_list_k_lift_context.
  rewrite map_subst_instance_to_extended_list_k.
  rewrite -to_extended_list_k_map_subst. lia.
  relativize (context_assumptions (ind_indices idecl)).
  relativize #|ind_indices idecl|.
  relativize (to_extended_list_k (ind_indices idecl) _).
  erewrite map_subst_extended_subst_lift_to_extended_list_k => //.
  rewrite -(subst_instance_smash _ _ []).
  rewrite /ctx. rewrite (smash_context_subst []).
  rewrite /to_extended_list to_extended_list_k_subst //.
  rewrite subst_instance_smash //.
  rewrite /ctx /to_extended_list to_extended_list_k_subst.
  now rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k. len.
  len.
Qed.

Lemma inductive_ind_ind_bodies_length `{cf:checker_flags}
  Σ ind mib oib
  (wfΣ : wf Σ)
  (inddecl: declared_inductive Σ ind mib oib) :
  inductive_ind ind < #|ind_bodies mib|.
Proof.
  unshelve eapply declared_inductive_to_gen in inddecl; eauto.
  move: (declared_inductive_lookup_gen inddecl).
  rewrite /lookup_inductive /lookup_inductive_gen (PCUICLookup.declared_minductive_lookup_gen (PCUICGlobalEnv.declared_inductive_minductive inddecl)).
  remember (nth_error _ _) as o eqn:eo; symmetry in eo.
  move: o eo=> [io|] // /nth_error_Some_length //.
Qed.
