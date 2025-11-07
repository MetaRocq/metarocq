(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph EnvMap.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv.
From Equations Require Import Equations.

Class abstract_guard_impl :=
  { guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool ;
    guard_correct : forall fix_cofix Σ Γ mfix, guard fix_cofix Σ Γ mfix <-> guard_impl fix_cofix Σ Γ mfix
  }.

Definition fake_guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool
  := fun fix_cofix Σ Γ mfix => true.

Record reference_impl_ext {cf:checker_flags} {guard : abstract_guard_impl} := {
      reference_impl_env_ext :> global_env_ext;
      reference_impl_ext_wf :> ∥ wf_ext reference_impl_env_ext ∥;
      reference_impl_ext_graph := projT1 (graph_of_wf_ext reference_impl_ext_wf);
      reference_impl_ext_graph_wf := projT2 (graph_of_wf_ext reference_impl_ext_wf)
  }.

Record reference_impl {cf:checker_flags} := {
      reference_impl_env :> global_env;
      reference_impl_wf :> ∥ wf reference_impl_env ∥;
      reference_impl_graph := projT1 (graph_of_wf reference_impl_wf);
      reference_impl_graph_wf := projT2 (graph_of_wf reference_impl_wf)
  }.

Program Definition reference_pop {cf:checker_flags} (Σ : reference_impl) : reference_impl :=
match Σ.(declarations) with
 [] => Σ
 | (d::decls) =>
   {| reference_impl_env := {| universes := Σ.(universes); declarations := decls; retroknowledge := Σ.(retroknowledge) |} |}
end.
Next Obligation.
destruct Σ.(reference_impl_wf). sq.
destruct X as [onu ond]; split => //. rewrite <- Heq_anonymous in ond.
depelim ond. apply ond.
Qed.

Program Definition make_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl}
(Σ : reference_impl) (univs : universes_decl)
(prf : forall Σ0 : global_env, Σ0 = Σ -> ∥ wf_ext (Σ0, univs) ∥) : reference_impl_ext :=
{| reference_impl_env_ext := (Σ, univs);|}.

Program Global Instance canonical_abstract_env_struct {cf:checker_flags} {guard : abstract_guard_impl} :
  abstract_env_struct reference_impl reference_impl_ext :=
  {|
  abstract_env_lookup := fun Σ => lookup_env (reference_impl_env_ext Σ) ;
  abstract_env_check := fun Σ => checkb (reference_impl_ext_graph Σ) ;
  abstract_env_level_mem := fun Σ l => LevelSet.mem l (global_ext_levels (reference_impl_env_ext Σ));
  abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (reference_impl_env_ext Σ);
  abstract_env_ext_rel := fun X Σ => Σ = reference_impl_env_ext X;
  abstract_env_init := fun cs retro H =>  {|
     reference_impl_env := {| universes := cs ;
                               declarations := [];
                               retroknowledge := retro |}; |} ;
  abstract_env_add_decl := fun X kn d H =>
    {| reference_impl_env := add_global_decl X.(reference_impl_env) (kn,d); |};
  abstract_env_is_consistent X uctx :=
   let G := reference_impl_graph X in
   (match push_uctx G uctx with
    | Some G' => true
      (* wGraph.IsFullSubgraph.is_full_extension G G' *)
    | None => false
    end) ;
  abstract_env_add_udecl X udecl Hglobal :=
    {| reference_impl_env_ext := (X.(reference_impl_env) , udecl); |} ;
  abstract_primitive_constant := fun X tag => primitive_constant X tag;
  abstract_env_rel := fun X Σ => Σ = reference_impl_env X ;
  abstract_pop_decls := reference_pop ;
 |}.
Next Obligation. sq; constructor; cbn; eauto. econstructor. Qed.
Next Obligation.
 pose proof (reference_impl_wf X). destruct (H _ eq_refl).
 sq. destruct H0.  econstructor; eauto. econstructor; eauto.
  Qed.
Next Obligation.
  pose proof (reference_impl_wf X). destruct (Hglobal _ eq_refl); sq.
  now econstructor.
Qed.

(* We pack up all the information required on the global environment and graph in a
single record. *)

Record wf_env {cf:checker_flags} := {
  wf_env_reference :> reference_impl;
  wf_env_map :> EnvMap.t global_decl;
  wf_env_map_repr :> EnvMap.repr (reference_impl_env wf_env_reference).(declarations) wf_env_map;
}.

Record wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} := {
  wf_env_ext_reference :> reference_impl_ext;
  wf_env_ext_map :> EnvMap.t global_decl;
  wf_env_ext_map_repr :> EnvMap.repr (reference_impl_env_ext wf_env_ext_reference).(declarations) wf_env_ext_map;
}.

Lemma wf_env_eta {cf : checker_flags} (Σ : wf_env) :
 {| universes := Σ.(universes); declarations := Σ.(declarations); retroknowledge := Σ.(retroknowledge) |} = Σ.
Proof.
  destruct Σ => /= //. destruct reference_impl_env => //.
Qed.

Lemma wf_fresh_globals {cf : checker_flags} Σ : wf Σ -> EnvMap.fresh_globals Σ.(declarations).
Proof. destruct Σ as [univs Σ]; cbn.
  move=> [] onu; cbn. induction 1; constructor; auto. now destruct o.
Qed.


Lemma wf_env_fresh {cf : checker_flags} (Σ : wf_env) : EnvMap.EnvMap.fresh_globals Σ.(declarations).
Proof.
  destruct Σ.(reference_impl_wf).
  now eapply wf_fresh_globals.
Qed.

Lemma of_global_env_cons {cf:checker_flags} d g : EnvMap.fresh_globals (add_global_decl g d).(declarations) ->
  EnvMap.of_global_env (add_global_decl g d).(declarations) = EnvMap.add d.1 d.2 (EnvMap.of_global_env g.(declarations)).
Proof.
  unfold EnvMap.of_global_env. simpl. unfold KernameMapFact.uncurry.
  reflexivity.
Qed.

Program Definition wf_env_init {cf:checker_flags} {guard : abstract_guard_impl} cs retro :
  on_global_univs cs -> wf_env := fun H =>
  {|
  wf_env_reference := abstract_env_init cs retro H;
  wf_env_map := EnvMap.empty;
  |}.

Lemma reference_pop_decls_correct {cf:checker_flags} (X:reference_impl) decls
  (prf : forall Σ : global_env, Σ = X ->
  exists d, Σ.(declarations) = d :: decls) :
  let X' := reference_pop X in
  forall Σ Σ', Σ = X -> Σ' = X' ->
          Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\
          Σ.(retroknowledge) = Σ'.(retroknowledge).
Proof.
  cbn; intros; subst. specialize (prf _ eq_refl).
  unfold reference_pop. cbn. set (reference_pop_obligation_1 cf X).
  clearbody s. destruct (X.(declarations)); cbn; inversion prf; now inversion H.
Qed.

Program Definition optim_pop {cf:checker_flags} (Σ : wf_env) : wf_env :=
  match Σ.(reference_impl_env).(declarations) with
    [] => Σ
    | ((kn , d) :: decls) =>
    {| wf_env_reference := reference_pop Σ ;
        wf_env_map := EnvMap.EnvMap.remove kn Σ.(wf_env_map);
    |}
  end.

Next Obligation.
  pose proof Σ.(wf_env_map_repr). red in H.
  rewrite <- Heq_anonymous in H.
  set (Σ0 := EnvMap.of_global_env decls).
  pose proof (EnvMap.remove_add_eq decls kn d Σ0).
  PCUICSR.forward_keep H0.
  { pose proof (Σf := wf_env_fresh Σ). rewrite <- Heq_anonymous in Σf. now depelim Σf. }
  PCUICSR.forward_keep H0.
  { pose proof (Σf := wf_env_fresh Σ). rewrite <- Heq_anonymous in Σf. now depelim Σf. }
  PCUICSR.forward_keep H0.
  { red. unfold EnvMap.equal. reflexivity. }
  unfold EnvMap.repr.
  rewrite H /=. unfold KernameMapFact.uncurry; cbn.
  unfold EnvMap.add in H0.
  unfold reference_pop. cbn. set (reference_pop_obligation_1 cf _).
  clearbody s.
  destruct (declarations Σ); cbn in *; inversion Heq_anonymous; clear Heq_anonymous s.
  subst. unfold KernameMapFact.uncurry in *; cbn in *.
  unfold Σ0 in * ; clear Σ0. unfold EnvMap.equal, KernameMap.Equal in H0.
  specialize (H0 y). cbn in H0. rewrite H0. reflexivity.
Qed.

Program Global Instance optimized_abstract_env_struct {cf:checker_flags} {guard : abstract_guard_impl} :
  abstract_env_struct wf_env wf_env_ext :=
 {|
 abstract_env_lookup := fun Σ k => EnvMap.lookup k (wf_env_ext_map Σ);
 abstract_env_check X := abstract_env_check X.(wf_env_ext_reference);
 abstract_env_level_mem X := abstract_env_level_mem X.(wf_env_ext_reference);
 abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (wf_env_ext_reference Σ);
 abstract_env_ext_rel X := abstract_env_ext_rel X.(wf_env_ext_reference);

 abstract_env_init := wf_env_init;
 abstract_env_add_decl X kn d H :=
  {| wf_env_reference := @abstract_env_add_decl _ _ reference_impl_ext _ X.(wf_env_reference) kn d H ;
     wf_env_map := EnvMap.add kn d X.(wf_env_map) |};
 abstract_env_is_consistent X uctx := abstract_env_is_consistent X.(wf_env_reference) uctx;
 abstract_env_add_udecl X udecl Hdecl :=
 {| wf_env_ext_reference := @abstract_env_add_udecl _ _ reference_impl_ext _ X.(wf_env_reference) udecl Hdecl ;
    wf_env_ext_map := X.(wf_env_map) |};
 abstract_primitive_constant X := abstract_primitive_constant X.(wf_env_ext_reference);
 abstract_env_rel X := abstract_env_rel X.(wf_env_reference) ;
 abstract_pop_decls := optim_pop ;
 |}.
Next Obligation.
  pose proof (X.(wf_env_reference).(reference_impl_wf)) as [?].
  sq. destruct (H _ eq_refl).
  apply EnvMap.repr_add; eauto; try eapply wf_fresh_globals; eauto.
  destruct X1; eauto.
  apply wf_env_map_repr.
Qed.
Next Obligation. apply wf_env_map_repr. Qed.

Section WfEnv.
  Context {cf : checker_flags} {guard : abstract_guard_impl}.

  Definition reference_impl_sq_wf (Σ : reference_impl_ext) : ∥ wf Σ ∥.
  Proof using Type.
    destruct (reference_impl_ext_wf Σ).
    sq. apply X.
  Qed.

  Definition lookup (Σ : wf_env_ext) (kn : kername) : option global_decl :=
    EnvMap.lookup kn Σ.(wf_env_ext_map).

  Lemma lookup_lookup_env Σ kn : lookup Σ kn = lookup_env Σ kn.
  Proof using Type.
    rewrite /lookup. destruct Σ as [Σ map repr]. pose (reference_impl_sq_wf Σ).
    sq. apply EnvMap.lookup_spec; auto. now eapply wf_fresh_globals.
  Qed.

End WfEnv.


Create HintDb wf_env discriminated.
Global Hint Constants Opaque : wf_env.
Global Hint Variables Opaque : wf_env.

Global Hint Resolve reference_impl_ext_wf : wf_env.
Global Hint Resolve reference_impl_wf : wf_env.

Definition Σudecl_ref {cf : checker_flags} {guard : abstract_guard_impl} (Σ : reference_impl_ext) :
  ∥ on_udecl Σ.(reference_impl_env_ext).1 Σ.(reference_impl_env_ext).2 ∥ :=
    map_squash (fun x => x.2) Σ.

Definition Σudecl {cf : checker_flags} {guard : abstract_guard_impl} (Σ : wf_env_ext) :
  ∥ on_udecl Σ.(reference_impl_env_ext).1 Σ.(reference_impl_env_ext).2 ∥ :=
  map_squash (fun x => x.2) Σ.

  Global Hint Resolve Σudecl : wf_env.

Ltac wf_env := auto with wf_env.


(** Build an optimized environment representation for lookups along with the graph associated to a well-formed
  global environment. The graph building is separated, so that [(build_wf_env_ext Σ wfΣ).(wf_env_ext_env)] is
  convertible to [Σ]. *)

Definition build_wf_env_ext {cf : checker_flags} {guard : abstract_guard_impl} (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) : wf_env_ext :=
  {| wf_env_ext_reference :=
      {| reference_impl_env_ext := Σ; reference_impl_ext_wf := wfΣ |} ;
     wf_env_ext_map := EnvMap.of_global_env Σ.(declarations);
     wf_env_ext_map_repr := EnvMap.repr_global_env Σ.(declarations);
|}.

Section GraphSpec.
  Context {cf:checker_flags} {guard : abstract_guard_impl} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
      (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
      (G : universe_model) (HG : model_of_uctx G (global_ext_uctx Σ)).

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Qed.

  Lemma is_graph_of_uctx_levels (l : Level.t) :
    LevelSet.mem l (UnivLoopChecking.UnivLoopChecking.levels G) <->
    LevelSet.mem l (global_ext_levels Σ).
  Proof using HG.
    destruct HG as [-> _].
    rewrite ![is_true _]LevelSet.mem_spec LevelSet.union_spec LevelSet.singleton_spec.
    split => //. intros [] => //. subst.
    apply global_ext_levels_InSet. intuition.
  Qed.

End GraphSpec.

Import UnivLoopChecking.UnivLoopChecking.

From Stdlib Require Import Morphisms.

Instance wf_uctx_ext_proper : Morphisms.Proper (LevelSet.Equal ==> eq ==> iff) wf_uctx_ext.
Proof.
  intros ? ? ls ? ? ->.
  rewrite /wf_uctx_ext. now setoid_rewrite ls.
Qed.

Program Global Instance canonical_abstract_env_prop {cf:checker_flags} {guard : abstract_guard_impl} :
  @abstract_env_prop _ _ _ canonical_abstract_env_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (reference_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Qed.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation.
  apply (reference_pop_decls_correct X decls prf X (reference_pop X) eq_refl eq_refl).
Qed.
Next Obligation.
  epose proof (HΣ := reference_impl_ext_wf X). sq.
  apply lookup_global_Some_iff_In_NoDup => //.
  destruct HΣ as [[] _]. now eapply NoDup_on_global_decls.
Qed.
Next Obligation.
  pose proof (reference_impl_ext_wf X); sq.
  assert (consistent (global_ext_uctx X).2) as HC.
      { sq; apply (global_ext_uctx_consistent _ H0). }
  rewrite (checkb_spec (reference_impl_ext_graph X) (clean_uctx (global_ext_uctx X))).
  + eapply wf_ext_global_uctx_invariants, H0.
  + eapply model_of_clean_uctx.
    apply (reference_impl_ext_graph_wf X).
  + rewrite /clean_uctx. destruct c as [[l d] r]; cbn; rewrite levelset_add_remove. exact H.
  + reflexivity.
Qed.
Next Obligation. pose (reference_impl_ext_wf X). sq. symmetry; apply LevelSet.Raw.mem_spec. typeclasses eauto. Defined.
Next Obligation.
  pose (reference_impl_wf X). sq.
  rename H0 into Hudecl.
  assert (H0 : global_uctx_invariants (clean_uctx (global_uctx X))).
  { eapply wf_global_uctx_invariants; eauto. }
  destruct (push_uctx _ udecl) eqn:hp.
  - split => // _.
    have h := is_model_of_uctx (reference_impl_graph X). cbn in h.
    pose proof (reference_impl_graph_wf X) as HG. simpl in HG.
    unfold reference_impl_graph in hp.
    eapply push_uctx_model in hp; tea.
    exists (to_valuation (LoopCheck.valuation u.(model))).
    destruct hp as [hl hc].
    have hv := model_satisfies u. rewrite hc in hv.
    apply satisfies_union in hv as [hv hv'].
    apply satisfies_union in hv as [ht hg].
    apply satisfies_union => //.
  - split=> // hcon.
    pose proof (reference_impl_graph_wf X) as HG. simpl in HG.
    have hs := push_uctx_spec (reference_impl_graph X) udecl.
    rewrite hp in hs. cbn in hs.
    apply push_uctx_model_unsat in hp.
    * exfalso; apply hp.
      destruct hcon as [v h]. exists v. apply satisfies_union in h as [].
      apply satisfies_union => //. split => //.
      unfold reference_impl_graph. unfold global_constraints in H.
      destruct HG as [hl hc]. rewrite hc.
      apply satisfies_union. split => //. apply satisfies_init.
    * clear H. move: Hudecl.
      destruct HG as [hl hc].
      move=> [hl' hc'].
      rewrite /reference_impl_graph hl. cbn.
      split.
      { move=> l hin hin'. specialize (hl' l hin).
        apply hl'. apply LevelSet.union_spec in hin' as [] => //.
        apply LevelSet.singleton_spec in H. subst l.
        apply global_levels_InSet. }
      { move=> cl /hc'.
        eapply declared_univ_cstr_levels_subset. lsets. reflexivity. }
Qed.

Next Obligation. apply guard_correct. Qed.

Program Global Instance optimized_abstract_env_prop {cf:checker_flags} {guard : abstract_guard_impl} :
  @abstract_env_prop _ _ _ optimized_abstract_env_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (reference_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Qed.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation. unfold optim_pop. set (optim_pop_obligation_1 cf X). clearbody r.
  pose proof (reference_pop_decls_correct X decls prf X (reference_pop X) eq_refl eq_refl).
  specialize (prf _ eq_refl).
  destruct (declarations X); cbn; inversion prf; inversion H0. subst.
  now destruct x.
Qed.
Next Obligation.
  epose proof (HΣ := reference_impl_ext_wf X). sq.
  etransitivity; try apply abstract_env_lookup_correct => //.
  assert (lookup_env X kn = EnvMap.lookup kn X).
  { erewrite EnvMap.lookup_spec; try reflexivity.
    1: apply wf_fresh_globals; eauto.
    1: apply wf_env_ext_map_repr. }
  now rewrite <- H.
Qed.
Next Obligation.
 (* erewrite wf_ext_gc_of_uctx_irr. *)
 have h := abstract_env_check_correct X.(wf_env_ext_reference).
 specialize (h cf _ _ _ X eq_refl). now apply h.
Qed.
Next Obligation.
  now erewrite (abstract_env_level_mem_correct X.(wf_env_ext_reference)).
Qed.
Next Obligation.
  rewrite (abstract_env_is_consistent_correct X.(wf_env_reference)) //.
Qed.
Next Obligation. eapply guard_correct. Qed.

Definition canonical_abstract_env_impl {cf:checker_flags} {guard : abstract_guard_impl} : abstract_env_impl :=
  (reference_impl ; reference_impl_ext ; canonical_abstract_env_struct ; canonical_abstract_env_prop).

Definition optimized_abstract_env_impl {cf:checker_flags} {guard : abstract_guard_impl} : abstract_env_impl :=
  (wf_env; wf_env_ext ; optimized_abstract_env_struct ; optimized_abstract_env_prop).

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env
  :=
  let Σm := EnvMap.of_global_env Σ.(declarations) in
  {| wf_env_reference := {| reference_impl_env := Σ; reference_impl_wf := wfΣ |} ;
     wf_env_map := Σm;
     wf_env_map_repr := EnvMap.repr_global_env Σ.(declarations);
 |}.
