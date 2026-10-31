(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICEquality PCUICContextSubst PCUICUnivSubst PCUICCases
  PCUICReduction PCUICCumulativity PCUICTyping PCUICGuardCondition
  PCUICWeakeningEnv PCUICWeakeningEnvConv.
From Equations Require Import Equations.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | (extends ?t.1 _) => fresh "ext" t
  | (extends _ _) => fresh "ext"
  | _ => PCUICTyping.my_rename_hyp h th
  | _ => PCUICWeakeningEnv.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma extends_wf_local_gen `{cf : checker_flags} R Σ Γ (wfΓ : wf_local Σ Γ) :
  All_local_env_over (typing Σ)
      (fun Γ0 wfΓ (t T : term) ty =>
         forall Σ' : global_env,
           wf Σ' ->
           R Σ Σ' ->
           (Σ', Σ.2);;; Γ0 |- t : T
      ) Γ wfΓ ->
    forall Σ' : global_env, wf Σ' -> R Σ Σ' -> wf_local (Σ', Σ.2) Γ.
Proof.
  intros X0 Σ' H0.
  induction X0 in H0 |- *; try econstructor; simpl in *; intuition auto.
  - apply lift_sorting_it_impl with tu => //. intro; eauto.
  - apply lift_sorting_it_impl with tu => /=. all: intro; eauto.
Qed.

Definition extends_wf_local `{cf : checker_flags} := extends_wf_local_gen extends.
Definition extends_decls_wf_local `{cf : checker_flags} := extends_wf_local_gen extends_decls.
Definition extends_strictly_on_decls_wf_local `{cf : checker_flags} := extends_wf_local_gen extends_strictly_on_decls.
Definition strictly_extends_decls_wf_local `{cf : checker_flags} := extends_wf_local_gen strictly_extends_decls.
#[global]
Hint Resolve extends_wf_local extends_decls_wf_local extends_strictly_on_decls_wf_local strictly_extends_decls_wf_local : extends.

Lemma extends_check_recursivity_kind `{cf : checker_flags} Σ ind k Σ' : extends Σ Σ' -> wf Σ' ->
  check_recursivity_kind (lookup_env Σ) ind k -> check_recursivity_kind (lookup_env Σ') ind k.
Proof.
  intros ext wfΣ'.
  rw /check_recursivity_kind.
  destruct lookup_env eqn:Heq => //.
  eapply extends_lookup in Heq; eauto.
  now rw Heq.
Qed.

Lemma extends_wf_fixpoint `{cf : checker_flags} (Σ Σ' : global_env_ext) mfix : extends Σ Σ' -> wf Σ' ->
  wf_fixpoint Σ mfix -> wf_fixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_fixpoint, wf_fixpoint_gen.
  move/andb_and => [] -> /=.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.

Lemma extends_wf_cofixpoint `{cf : checker_flags} (Σ Σ' : global_env_ext) mfix : extends Σ Σ' -> wf Σ' ->
  wf_cofixpoint Σ mfix -> wf_cofixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.
#[global]
Hint Resolve extends_wf_fixpoint extends_wf_cofixpoint : extends.

Lemma extends_primitive_constant Σ Σ' p t :
  extends Σ Σ' ->
  primitive_constant Σ p = Some t ->
  primitive_constant Σ' p = Some t.
Proof.
  intros [_ _ ext].
  unfold primitive_constant.
  case: ext => o [] o' [] o'' o'''.
  destruct p => //.
  - intros hr. now rw hr in o; depelim o.
  - intros hr. now rw hr in o'; depelim o'.
  - intros hr. now rw hr in o''; depelim o''.
  - intros hr. now rw hr in o'''; depelim o'''.
Qed.
Local Hint Resolve extends_primitive_constant : extends.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ -> wf Σ' -> extends Σ.1 Σ' -> (Σ', Σ.2) ;;; Γ |- t : T)
           (fun Σ Γ j =>
              forall Σ', wf Σ -> wf Σ' -> extends Σ.1 Σ' -> lift_typing typing (Σ', Σ.2) Γ j)
           (fun Σ Γ =>
             forall Σ', wf Σ -> wf Σ' -> extends Σ.1 Σ' -> wf_local (Σ', Σ.2) Γ).
Proof.
  apply typing_ind_env; intros;
    rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - apply lift_typing_impl with (1 := X) => t T [] _ IH //.
    now apply IH.

  - apply All_local_env_impl with (1 := X0) => Γ' j Hj.
    now apply Hj.
  - econstructor; eauto 2 with extends.
    now apply extends_wf_sort.
  - econstructor; eauto 2 with extends. all: econstructor; eauto 2 with extends.
    * revert X5. clear -Σ' wf0 wfΣ' extΣ.
      induction 1; constructor; try destruct t0; eauto with extends.
    * close_Forall. intros; intuition eauto with extends.
  - econstructor; eauto with extends.
    + specialize (forall_Σ' _ wf0 wfΣ' extΣ).
      now apply All_local_env_app_inv in forall_Σ'.
    + eapply fix_guard_extends; eauto.
    + eapply (All_impl X1); intros d X. now apply X.
    + eapply (All_impl X3); intros d X. now apply X.
  - econstructor; eauto with extends.
    + specialize (forall_Σ' _ wf0 wfΣ' extΣ).
      now apply All_local_env_app_inv in forall_Σ'.
    + eapply cofix_guard_extends; eauto.
    + eapply (All_impl X1); intros d X. now apply X.
    + eapply (All_impl X3); intros d X. now apply X.
  - econstructor; eauto with extends.
    destruct X1; constructor; eauto with extends.
    * now eapply extends_wf_universe.
    * solve_all.
  - econstructor. 1: eauto.
    + eapply forall_Σ'1; eauto.
    + destruct Σ as [Σ φ]. eapply weakening_env_cumulSpec in cumulA; eauto.
Qed.

Lemma weakening_on_global_decl_gen `{checker_flags} R P Σ Σ' φ kn decl :
  CRelationClasses.subrelation R extends ->
  weaken_env_prop_gen cumulSpec0 (lift_typing typing) R P ->
  wf Σ -> wf Σ' -> R Σ Σ' ->
  on_global_decl cumulSpec0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpec0 P (Σ', φ) kn decl.
Proof.
  unfold weaken_env_prop_gen.
  intros HRext HPΣ wfΣ wfΣ' Hext.
  apply on_global_decl_impl_full; eauto.
  - reflexivity.
  - intros ?????. eapply weakening_env_cumulSpec0; eauto.
  - intro. eapply (extends_wf_sort (Σ:=(Σ,φ)) Σ'); auto.
  - unfold check_constructors_smaller. intros ???.
    eapply Forall_impl; tea; cbn. intros.
    eapply Forall_impl; tea; simpl; intros.
    eapply leq_sort_subset; tea.
    apply weakening_env_global_ext_constraints; tea; eauto.
  - rw /on_variance. intros u l. destruct u => //.
    destruct l => //.
    intros [univs' [i [i' []]]]. exists univs', i, i'. split => //.
    all:eapply weakening_env_consistent_instance; tea; eauto.
Qed.

Definition weakening_on_global_decl `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> wf Σ' -> extends Σ Σ' ->
  on_global_decl cumulSpec0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpec0 P (Σ', φ) kn decl.
Proof. intro; eapply weakening_on_global_decl_gen; [ | eassumption ]; tc. Qed.
Lemma weakening_on_global_decl_ext `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> wf Σ' -> extends_decls Σ Σ' ->
  on_global_decl cumulSpec0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpec0 P (Σ', φ) kn decl.
Proof. intro; eapply weakening_on_global_decl_gen; [ | eassumption ]; tc. Qed.
Lemma weakening_on_global_decl_strictly `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_strictly_on_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> wf Σ' -> extends_strictly_on_decls Σ Σ' ->
  on_global_decl cumulSpec0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpec0 P (Σ', φ) kn decl.
Proof. intro; eapply weakening_on_global_decl_gen; [ | eassumption ]; tc. Qed.
Lemma weakening_on_global_decl_strictly_ext `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> wf Σ' -> strictly_extends_decls Σ Σ' ->
  on_global_decl cumulSpec0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpec0 P (Σ', φ) kn decl.
Proof. intro; eapply weakening_on_global_decl_gen; [ | eassumption ]; tc. Qed.

Import CRelationClasses CMorphisms.
Lemma weakening_env_gen_lookup_on_global_env `{checker_flags} R P Σ Σ' c decl :
  subrelation R extends ->
  subrelation strictly_extends_decls R ->
  Transitive R ->
  weaken_env_prop_gen cumulSpec0 (lift_typing typing) R P ->
  wf Σ' -> wf Σ -> R Σ Σ' -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HRext1 HRext2 HTR HP wfΣ' wfΣ Hext HΣ.
  destruct HΣ as [onu onΣ].
  destruct Σ as [univs Σ retro]; cbn in *.
  induction onΣ; simpl. 1: congruence.
  assert (HH: R {| universes := univs; declarations := Σ; retroknowledge := retro |} Σ'). {
    etransitivity; [ eapply HRext2 | exact Hext ].
    split; cbv [snoc]; cbn; auto.
    eexists [_]; cbn; reflexivity.
  }
  case: eqb_specT; intro eq; subst.
  - intros [= ->]. subst. destruct o.
    clear Hext; eapply weakening_on_global_decl_gen; [ .. | eassumption ]; eauto; [].
    destruct wfΣ as [? wfΣ]; inversion wfΣ; subst; split; tea.
  - destruct o. apply IHonΣ; auto.
    destruct wfΣ. split => //. now depelim o0.
Qed.

Lemma weakening_env_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ' -> wf Σ -> extends Σ Σ' -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl.
Proof. eapply weakening_env_gen_lookup_on_global_env; tc. Qed.
Lemma weakening_env_decls_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ' -> wf Σ -> extends_decls Σ Σ' -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl.
Proof. eapply weakening_env_gen_lookup_on_global_env; tc. Qed.
Lemma weakening_env_strictly_decls_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ' -> wf Σ -> strictly_extends_decls Σ Σ' -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl.
Proof. eapply weakening_env_gen_lookup_on_global_env; tc. Qed.
Lemma weakening_env_strictly_on_decls_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_strictly_on_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ' -> wf Σ -> extends_strictly_on_decls Σ Σ' -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl.
Proof. eapply weakening_env_gen_lookup_on_global_env; tc. Qed.

(* we can fill weaken_env_strictly_decls_prop with any other weaken_env_*_prop, so we only include this version *)
Lemma weaken_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_strictly_decls_lookup_on_global_env; tea; tc; reflexivity.
Qed.

Lemma declared_constant_inv `{checker_flags} Σ P cst decl :
  weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  declared_constant Σ cst decl ->
  on_constant_decl P (Σ, cst_universes decl) decl.
Proof.
  intros.
  unshelve eapply declared_constant_to_gen in H0; tea.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_minductive_inv `{checker_flags} {Σ P ind mdecl} :
  weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive cumulSpec0 P (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  unshelve eapply declared_minductive_to_gen in H0; tea.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body cumulSpec0 P (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv in Hmdecl; cbn in X; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma weaken_decls_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_decls_lookup_on_global_env; eauto.
  split => //.
  - exists []; simpl; destruct Σ; eauto.
Qed.

Lemma declared_constructor_inv `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P)
  (wfΣ : wf Σ)
  (HΣ : on_global_env cumulSpec0 P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor cumulSpec0 P (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_minductive_inv_decls `{checker_flags} {Σ P ind mdecl} :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive cumulSpec0 P (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  unshelve eapply declared_minductive_to_gen in H0; tea.
  eapply weaken_decls_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv_decls `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body cumulSpec0 P (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv_decls in Hmdecl; cbn in X; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma declared_constructor_inv_decls `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_decls_prop cumulSpec0 (lift_typing typing) P)
  (wfΣ : wf Σ)
  (HΣ : on_global_env cumulSpec0 P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv_decls HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor cumulSpec0 P (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv_decls HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_projection_inv `{checker_flags} {Σ P mdecl idecl cdecl ref pdecl} :
  forall (HP : weaken_env_strictly_decls_prop cumulSpec0 (lift_typing typing) P)
  (wfΣ : wf Σ)
  (HΣ : on_global_env cumulSpec0 P Σ)
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl),
  match idecl.(ind_ctors) return Type with
  | [c] =>
    let oib := declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in
      let (x, _) := x in x) in
    (match oib.(ind_cunivs) with
     | [cs] => sorts_local_ctx P (Σ, ind_universes mdecl) (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args c) cs
     | _ => False
    end) *
    on_projections mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) idecl (idecl.(ind_indices)) c *
    (ref.(proj_arg) < context_assumptions c.(cstr_args)) *
    on_projection mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) c ref.(proj_arg) pdecl
  | _ => False
  end.
Proof.
  intros.
  destruct (declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in let (x, _) := x in x)) in *.
  destruct Hdecl as [Hidecl [Hcdecl Hnpar]]. simpl.
  move: onProjections. generalize (nth_error_Some_length Hcdecl).
  case: (ind_projs idecl) => //= .
  { lia. }
  destruct (ind_ctors idecl) as [|? []]; try contradiction.
  destruct ind_cunivs as [|? []]; try contradiction; depelim onConstructors.
  2:{ depelim onConstructors. }
  intuition auto.
  - destruct onProjections.
    destruct (ind_ctors idecl) as [|? []]; simpl in *; try discriminate.
    inv onConstructors. now eapply on_cargs in o.
  - destruct onProjections. eapply nth_error_Some_length in Hcdecl. lia.
  - destruct onProjections.
    eapply nth_error_alli in Hcdecl; eauto.
    eapply Hcdecl.
Qed.


Lemma weaken_env_prop_typing `{checker_flags} : weaken_env_prop cumulSpec0 (lift_typing typing) (lift_typing typing).
Proof.
  do 2 red. intros * wfΣ wfΣ' Hext Γ j Hj.
  apply lift_typing_impl with (1 := Hj); intros ?? HT.
  eapply (weakening_env (_, _)).
  2: eauto.
  all: auto.
Qed.

#[global]
 Hint Unfold weaken_env_prop weaken_env_prop_gen : pcuic.

Lemma on_declared_constant `{checker_flags} {Σ cst decl} :
  wf Σ -> declared_constant Σ cst decl ->
  on_constant_decl (lift_typing typing) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply declared_constant_inv; tea.
  exact weaken_env_prop_typing.
Qed.


Lemma weaken_wf_local `{checker_flags} (Σ : global_env_ext) Σ' Γ :
  wf Σ -> extends Σ Σ' -> wf Σ' -> wf_local Σ Γ -> wf_local (Σ', Σ.2) Γ.
Proof.
  intros * wfΣ Hext wfΣ' *.
  intros wfΓ.
  eapply (env_prop_wf_local weakening_env); eauto.
Qed.

#[global]
Hint Resolve weaken_wf_local | 100 : pcuic.

Lemma on_declared_minductive `{checker_flags} {Σ ref decl} :
  wf Σ ->
  declared_minductive Σ ref decl ->
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes decl) ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductive `{checker_flags} {Σ ref mdecl idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ref mdecl idecl ->
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl *
  on_ind_body cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros Hdecl.
  split.
  - destruct Hdecl as [Hmdecl _]. now apply on_declared_minductive in Hmdecl.
  - apply (declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_constructor `{checker_flags} {Σ ref mdecl idecl cdecl}
  {wfΣ : wf Σ}
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind (fst ref)) mdecl *
  on_ind_body cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl)
              (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  ∑ ind_ctor_sort,
    let onib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in x) in
     nth_error (ind_cunivs onib) ref.2 = Some ind_ctor_sort
    ×  on_constructor cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl)
                 mdecl (inductive_ind (fst ref))
                 idecl idecl.(ind_indices) cdecl ind_ctor_sort.
Proof.
  split.
  - destruct Hdecl; now apply on_declared_inductive.
  - apply (declared_constructor_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_projection `{checker_flags} {Σ ref mdecl idecl cdecl pdecl} {wfΣ : wf Σ}
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl) :
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref.(proj_ind)) mdecl *
  (idecl.(ind_ctors) = [cdecl]) *
  let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in let (x, _) := x in x) in
  (match oib.(ind_cunivs) with
  | [cs] => sorts_local_ctx (lift_typing typing) (Σ, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args cdecl) cs
    | _ => False
  end) *
  on_projections mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) idecl (idecl.(ind_indices)) cdecl *
  (ref.(proj_arg) < context_assumptions cdecl.(cstr_args)) *
  on_projection mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) cdecl ref.(proj_arg) pdecl.
Proof.
  have hctors : idecl.(ind_ctors) = [cdecl].
  { pose proof (declared_projection_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
    move: X. destruct Hdecl. destruct d. cbn in *.
    move: e. destruct (ind_ctors idecl) as [|? []] => //.
    intros [= ->] => //. }
  split.
  - split => //. destruct Hdecl as [[] ?]. now eapply on_declared_inductive.
  - pose proof (declared_projection_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
    destruct Hdecl. cbn in *. destruct d; cbn in *.
    now rw hctors in X.
Qed.
