(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require CMorphisms CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst UnivConstraintType Universes Environment Primitive.
From Equations Require Import Equations.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Definition declared_constant_gen (lookup : kername -> option global_decl) (id : kername) decl : Prop :=
    lookup id = Some (ConstantDecl decl).

  Definition declared_constant (Σ : global_env) id decl := In (id,ConstantDecl decl) (declarations Σ).

  Definition declared_minductive_gen (lookup : kername -> option global_decl) mind decl :=
    lookup mind = Some (InductiveDecl decl).

  Definition declared_minductive Σ mind decl := In (mind,InductiveDecl decl) (declarations Σ).

  Definition declared_inductive_gen lookup ind mdecl decl :=
    declared_minductive_gen lookup (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_inductive Σ ind mdecl decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor_gen lookup cstr mdecl idecl cdecl : Prop :=
    declared_inductive_gen lookup (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_constructor Σ cstr mdecl idecl cdecl :=
    declared_inductive Σ (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection_gen lookup (proj : projection) mdecl idecl cdecl pdecl
  : Prop :=
    declared_constructor_gen lookup (proj.(proj_ind), 0) mdecl idecl cdecl /\
    List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
    mdecl.(ind_npars) = proj.(proj_npars).

  Definition declared_projection Σ (proj : projection) mdecl idecl cdecl pdecl
  : Prop :=
    declared_constructor Σ (proj.(proj_ind), 0) mdecl idecl cdecl /\
    List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
    mdecl.(ind_npars) = proj.(proj_npars).

  Definition lookup_constant_gen (lookup : kername -> option global_decl) kn :=
    match lookup kn with
    | Some (ConstantDecl d) => Some d
    | _ => None
    end.

  Definition lookup_constant Σ := lookup_constant_gen (lookup_env Σ).

  Definition lookup_minductive_gen (lookup : kername -> option global_decl) mind :=
    match lookup mind with
    | Some (InductiveDecl decl) => Some decl
    | _ => None
    end.

  Definition lookup_minductive Σ := lookup_minductive_gen (lookup_env Σ).

  Definition lookup_inductive_gen lookup ind :=
    match lookup_minductive_gen lookup (inductive_mind ind) with
    | Some mdecl =>
      match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
      | Some idecl => Some (mdecl, idecl)
      | None => None
      end
    | None => None
    end.

  Definition lookup_inductive Σ := lookup_inductive_gen (lookup_env Σ).

  Definition lookup_constructor_gen lookup ind k :=
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match nth_error idecl.(ind_ctors) k with
      | Some cdecl => Some (mdecl, idecl, cdecl)
      | None => None
      end
    | _ => None
    end.

  Definition lookup_constructor Σ := lookup_constructor_gen (lookup_env Σ).

  Definition lookup_projection_gen lookup p :=
    match lookup_constructor_gen lookup p.(proj_ind) 0 with
    | Some (mdecl, idecl, cdecl) =>
      match nth_error idecl.(ind_projs) p.(proj_arg) with
      | Some pdecl => Some (mdecl, idecl, cdecl, pdecl)
      | None => None
      end
    | _ => None
    end.

  Definition lookup_projection Σ := lookup_projection_gen (lookup_env Σ).

  Lemma declared_constant_lookup_gen {lookup kn cdecl} :
    declared_constant_gen lookup kn cdecl ->
    lookup_constant_gen lookup kn = Some cdecl.
  Proof.
    unfold declared_constant_gen, lookup_constant_gen.
    now intros ->.
  Qed.

  Lemma lookup_constant_declared_gen {lookup kn cdecl} :
    lookup_constant_gen lookup kn = Some cdecl ->
    declared_constant_gen lookup kn cdecl.
  Proof.
    unfold declared_constant_gen, lookup_constant_gen.
    destruct lookup as [[]|] => //. congruence.
  Qed.

  Lemma declared_minductive_lookup_gen {lookup ind mdecl} :
    declared_minductive_gen lookup ind mdecl ->
    lookup_minductive_gen lookup ind = Some mdecl.
  Proof.
    rewrite /declared_minductive_gen /lookup_minductive_gen.
    now intros ->.
  Qed.

  Lemma lookup_minductive_declared_gen {lookup ind mdecl} :
    lookup_minductive_gen lookup ind = Some mdecl ->
    declared_minductive_gen lookup ind mdecl.
  Proof.
    rewrite /declared_minductive_gen /lookup_minductive_gen.
    destruct lookup as [[]|] => //. congruence.
  Qed.

  Lemma declared_inductive_lookup_gen {lookup ind mdecl idecl} :
    declared_inductive_gen lookup ind mdecl idecl ->
    lookup_inductive_gen lookup ind = Some (mdecl, idecl).
  Proof.
    rewrite /declared_inductive_gen /lookup_inductive_gen.
    intros []. now rewrite (declared_minductive_lookup_gen H) H0.
  Qed.

  Lemma lookup_inductive_declared_gen {lookup ind mdecl idecl} :
    lookup_inductive_gen lookup ind = Some (mdecl, idecl) ->
    declared_inductive_gen lookup ind mdecl idecl.
  Proof.
    rewrite /declared_inductive_gen /lookup_inductive_gen.
    destruct lookup_minductive_gen as [[]|] eqn:hl => //=.
    destruct nth_error eqn:hnth => //. intros [= <- <-].
    split => //.
    apply (lookup_minductive_declared_gen hl).
  Qed.

  Lemma declared_constructor_lookup_gen {lookup id mdecl idecl cdecl} :
    declared_constructor_gen lookup id mdecl idecl cdecl ->
    lookup_constructor_gen lookup id.1 id.2 = Some (mdecl, idecl, cdecl).
  Proof.
    intros []. unfold lookup_constructor_gen.
    rewrite (declared_inductive_lookup_gen (lookup := lookup) H) /= H0 //.
  Qed.

  Lemma lookup_constructor_declared_gen {lookup id mdecl idecl cdecl} :
    lookup_constructor_gen lookup id.1 id.2 = Some (mdecl, idecl, cdecl) ->
    declared_constructor_gen lookup id mdecl idecl cdecl.
  Proof.
    unfold lookup_constructor_gen.
    destruct lookup_inductive_gen as [[]|] eqn:hl => //=.
    destruct nth_error eqn:hnth => //. intros [= <- <-].
    split => //.
    apply (lookup_inductive_declared_gen hl). congruence.
  Qed.

  Lemma declared_projection_lookup_gen {lookup p mdecl idecl cdecl pdecl} :
    declared_projection_gen lookup p mdecl idecl cdecl pdecl ->
    lookup_projection_gen lookup p = Some (mdecl, idecl, cdecl, pdecl).
  Proof.
    intros [? []]. unfold lookup_projection_gen.
    rewrite (declared_constructor_lookup_gen (lookup := lookup) H) /= H0 //.
  Qed.

  Lemma lookup_projection_declared_gen {lookup p mdecl idecl cdecl pdecl} :
    ind_npars mdecl = p.(proj_npars) ->
    lookup_projection_gen lookup p = Some (mdecl, idecl, cdecl, pdecl) ->
    declared_projection_gen lookup p mdecl idecl cdecl pdecl.
  Proof.
    intros hp. unfold lookup_projection_gen.
    destruct lookup_constructor_gen as [[[] ?]|] eqn:hl => //=.
    destruct nth_error eqn:hnth => //. intros [= <- <-]. subst c p0.
    split => //.
    apply (lookup_constructor_declared_gen (id:=(proj_ind p, 0)) hl).
  Qed.

  Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl cb => F cb.(cst_universes)
  | InductiveDecl mb => F mb.(ind_universes)
  end.

  Definition universes_decl_of_decl := on_udecl_decl (fun x => x).

  (* Definition LevelSet_add_list l := LevelSet.union (LevelSetProp.of_list l). *)

  Definition global_levels (univs : ContextSet.t) : LevelSet.t :=
    LevelSet.union (ContextSet.levels univs) (LevelSet.singleton (Level.lzero)).

  Lemma global_levels_InSet Σ :
    LevelSet.In Level.lzero (global_levels Σ).
  Proof.
    apply LevelSet.union_spec; right.
    now apply LevelSet.singleton_spec.
  Qed.

  Lemma global_levels_memSet univs :
    LevelSet.mem Level.lzero (global_levels univs) = true.
  Proof.
    apply LevelSet.mem_spec, global_levels_InSet.
  Qed.

  (** One can compute the constraints associated to a global environment or its
      extension by folding over its constituent definitions.

      We make *only* the second of these computations an implicit coercion
      for more readability. Note that [fst_ctx] is also a coercion which goes
      from a [global_env_ext] to a [global_env]: coercion coherence would *not*
      be ensured if we added [global_constraints] as well as a coercion, as it
      would forget the extension's constraints. *)

  Definition global_constraints (Σ : global_env) : UnivConstraintSet.t :=
    snd Σ.(universes).

  Definition global_uctx (Σ : global_env) : ContextSet.t :=
    (global_levels Σ.(universes), global_constraints Σ).

  Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t :=
    LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1.(universes)).

  Definition global_ext_constraints (Σ : global_env_ext) : UnivConstraintSet.t :=
    UnivConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1).

  Coercion global_ext_constraints : global_env_ext >-> UnivConstraintSet.t.

  Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t :=
    (global_ext_levels Σ, global_ext_constraints Σ).


  Lemma global_ext_levels_InSet Σ :
    LevelSet.In Level.lzero (global_ext_levels Σ).
  Proof.
    apply LevelSet.union_spec; right.
    now apply global_levels_InSet.
  Qed.

  (** Check that [uctx] instantiated at [u] is consistent with
    the current universe graph. *)

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : UnivConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx => List.length u = 0
    | Polymorphic_ctx c =>
      (* levels of the instance already declared *)
      forallb (fun l : Universe.t => LevelSet.subset (Universe.levels l) lvs) u /\
      List.length u = List.length c.1 /\
      valid_constraints φ (subst_instance_cstrs u c.2)
    end.

  Definition consistent_instance_ext `{checker_flags} Σ :=
    consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).

  Lemma consistent_instance_length {cf : checker_flags} {Σ : global_env_ext} {univs u} :
    consistent_instance_ext Σ univs u ->
    #|u| = #|abstract_instance univs|.
  Proof.
    unfold consistent_instance_ext, consistent_instance.
    destruct univs; simpl; auto.
    intros [_ [H _]].
    destruct cst; simpl in *.
    now rewrite H; cbn; autorewrite with len.
  Qed.

  Definition wf_universe Σ (u : Universe.t) : Prop :=
    forall l, LevelExprSet.In l u -> LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ).

  Definition wf_sort Σ (s : sort) : Prop :=
    Sort.on_sort (wf_universe Σ) True s.

  Definition wf_universe_dec Σ u : {wf_universe Σ u} + {~wf_universe Σ u}.
  Proof.
    cbv [wf_universe LevelExprSet.In LevelExprSet.this Universe.t_set].
    destruct u as [[t _] _].
    induction t as [|t ts [IHt|IHt]]; [ left | | right ].
    { inversion 1. }
    { destruct (LevelSetProp.In_dec (LevelExpr.get_level t) (global_ext_levels Σ)) as [H|H]; [ left | right ].
      { inversion 1; subst; auto. }
      { intro H'; apply H, H'; now constructor. } }
    { intro H; apply IHt; intros; apply H; now constructor. }
  Defined.

  Definition wf_sort_dec Σ s : {@wf_sort Σ s} + {~@wf_sort Σ s}.
  Proof.
    destruct s; try (left; exact I).
    apply wf_universe_dec.
  Defined.

  Lemma declared_ind_declared_constructors `{cf : checker_flags} {Σ ind mib oib} :
    declared_inductive Σ ind mib oib ->
    Alli (fun i => declared_constructor Σ (ind, i) mib oib) 0 (ind_ctors oib).
  Proof using.
    move=> inddecl.
    apply: forall_nth_error_Alli=> /= i x eq => //.
  Qed.

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
  Include Lookup T E.
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).

  Import T E TU.

  (** Well-formedness of local environments embeds a sorting for each variable *)

  Notation on_local_decl P Γ d :=
    (P Γ (j_decl d)) (only parsing).

  Definition on_def_type (P : context -> judgment -> Type) Γ d :=
    P Γ (TypRel d.(dtype) d.(dname).(binder_relevance)).

  Definition on_def_body (P : context -> judgment -> Type) types Γ d :=
    P (Γ ,,, types) (TermTypRel d.(dbody) (lift0 #|types| d.(dtype)) d.(dname).(binder_relevance)).

  (* Various kinds of lifts *)

  Definition lift_wf_term wf_term (j : judgment) := option_default wf_term (j_term j) (unit : Type) × wf_term (j_typ j).
  Notation lift_wf_term1 wf_term := (fun (Γ : context) => lift_wf_term (wf_term Γ)).

  Definition lift_wfu_term wf_term wf_univ (j : judgment) := option_default wf_term (j_term j) (unit : Type) × wf_term (j_typ j) × option_default wf_univ (j_univ j) (unit : Type).

  Definition lift_wfb_term wfb_term (j : judgment) := option_default wfb_term (j_term j) true && wfb_term (j_typ j).
  Notation lift_wfb_term1 wfb_term := (fun (Γ : context) => lift_wfb_term (wfb_term Γ)).

  Definition lift_wfbu_term wfb_term wfb_univ (j : judgment) := option_default wfb_term (j_term j) true && wfb_term (j_typ j) && option_default wfb_univ (j_univ j) true.

  Definition lift_sorting checking sorting : judgment -> Type :=
    fun j => option_default (fun tm => checking tm (j_typ j)) (j_term j) (unit : Type) ×
                                ∑ s, sorting (j_typ j) s ×
                                  option_default (fun u => u = s) (j_univ j) True /\
                                  isSortRelOpt s (j_rel j).

  Notation lift_sorting1 checking sorting := (fun Γ => lift_sorting (checking Γ) (sorting Γ)).
  Notation lift_sorting2 checking sorting := (fun Σ Γ => lift_sorting (checking Σ Γ) (sorting Σ Γ)).

  Notation typing_sort typing := (fun T s => typing T (tSort s)).
  Notation typing_sort1 typing := (fun Γ T s => typing Γ T (tSort s)).
  Notation typing_sort2 typing := (fun Σ Γ T s => typing Σ Γ T (tSort s)).

  Definition lift_typing0 typing := lift_sorting typing (typing_sort typing).
  Notation lift_typing1 typing := (fun Γ => lift_typing0 (typing Γ)).
  Notation lift_typing typing := (fun Σ Γ => lift_typing0 (typing Σ Γ)).

  Notation Prop_local_conj P Q := (fun Γ t T => P Γ t T × Q Γ t T).
  Notation Prop_conj P Q := (fun Σ Γ t T => P Σ Γ t T × Q Σ Γ t T).

  Definition lift_typing_conj (P Q : context -> _) := lift_typing1 (Prop_local_conj P Q).

  Lemma lift_wf_term_it_impl {P Q} {tm tm' : option term} {t t' : term} {u u' r r'} :
    forall tu: lift_wf_term P (Judge tm t u r),
    match tm', tm with None, _ => unit | Some tm', Some tm => P tm -> Q tm' | _, _ => False end ->
    (P t -> Q t') ->
    lift_wf_term Q (Judge tm' t' u' r').
  Proof.
    intros (Htm & Hs) HPQc HPQs.
    split; auto.
    destruct tm, tm' => //=. now apply HPQc.
  Qed.

  Lemma lift_wf_term_f_impl P Q tm t u u' r r' :
    forall f,
    lift_wf_term P (Judge tm t u r) ->
    (forall t, P t -> Q (f t)) ->
    lift_wf_term Q (Judge (option_map f tm) (f t) u' r').
  Proof.
    unfold lift_wf_term; cbn.
    intros f (Hb & Ht) HPQ.
    split; auto.
    destruct tm; cbn in *; auto.
  Defined.

  Lemma lift_wf_term_impl P Q j :
    lift_wf_term P j ->
    (forall t, P t -> Q t) ->
    lift_wf_term Q j.
  Proof.
    unfold lift_wf_term; cbn.
    intros (Hb & Ht) HPQ.
    split; auto.
    destruct j_term; cbn in *; auto.
  Defined.

  Lemma lift_wfbu_term_f_impl (P Q : term -> bool) tm t u r :
    forall f fu,
    lift_wfbu_term P (P ∘ tSort) (Judge tm t u r) ->
    (forall u, f (tSort u) = tSort (fu u)) ->
    (forall t, P t -> Q (f t)) ->
    lift_wfbu_term Q (Q ∘ tSort) (Judge (option_map f tm) (f t) (option_map fu u) r).
  Proof.
    unfold lift_wfbu_term; cbn.
    intros. rtoProp.
    repeat split; auto.
    1: destruct tm; cbn in *; auto.
    destruct u; rewrite //= -H0 //. auto.
  Defined.

  Lemma lift_wf_wfb_term (p : _ -> bool) j :
    reflectT (lift_wf_term p j) (lift_wfb_term p j).
  Proof.
    rewrite /lift_wf_term /lift_wfb_term.
    set (HP := @reflectT_pred _ p).
    destruct (HP (j_typ j)) => //;
    destruct (reflect_option_default HP (j_term j)) => /= //; now constructor.
  Qed.

  Lemma lift_wfu_wfbu_term (p : _ -> bool) (pu : _ -> bool) j :
    reflectT (lift_wfu_term p pu j) (lift_wfbu_term p pu j).
  Proof.
    set (HP := @reflectT_pred _ p); set (HPu := @reflectT_pred _ pu).
    rewrite /lift_wfu_term /lift_wfbu_term.
    destruct (HP (j_typ j)) => //;
    destruct (reflect_option_default HP (j_term j)) => /= //;
    destruct (reflect_option_default HPu (j_univ j)) => /= //; now constructor.
  Qed.

  Lemma unlift_TermTyp {Pc Ps tm ty u r} :
    lift_sorting Pc Ps (Judge (Some tm) ty u r) ->
    Pc tm ty.
  Proof.
    apply fst.
  Defined.

  Definition unlift_TypUniv {Pc Ps tm ty u r} :
    lift_sorting Pc Ps (Judge tm ty (Some u) r) ->
    Ps ty u
    := fun H => eq_rect_r _ H.2.π2.1 H.2.π2.2.p1.

  Definition lift_sorting_extract {c s tm ty r} (w : lift_sorting c s (Judge tm ty None r)) :
    lift_sorting c s (Judge tm ty (Some w.2.π1) r)
    := (w.1, (w.2.π1; (w.2.π2.1, (conj eq_refl w.2.π2.2.p2)))).

  Lemma lift_sorting_forget_univ {Pc Ps tm ty u r} :
    lift_sorting Pc Ps (Judge tm ty u r) ->
    lift_sorting Pc Ps (Judge tm ty None r).
  Proof.
    intros (? & ? & ? & ? & ?).
    repeat (eexists; tea).
  Qed.

  Lemma lift_sorting_forget_body {Pc Ps tm ty u r} :
    lift_sorting Pc Ps (Judge tm ty u r) ->
    lift_sorting Pc Ps (Judge None ty u r).
  Proof.
    intros (? & ? & ? & ? & ?).
    repeat (eexists; tea).
  Qed.

  Lemma lift_sorting_forget_rel {Pc Ps tm ty u r} :
    lift_sorting Pc Ps (Judge tm ty u r) ->
    lift_sorting Pc Ps (Judge tm ty u None).
  Proof.
    intros (? & ? & ? & ? & ?).
    repeat (eexists; tea).
  Qed.

  Lemma lift_sorting_ex_it_impl_gen {Pc Qc Ps Qs} {tm tm' : option term} {t t' : term} {r r' : option relevance} :
    forall tu: lift_sorting Pc Ps (Judge tm t None r),
    let s := tu.2.π1 in
    match tm', tm with None, _ => unit | Some tm', Some tm => Pc tm t -> Qc tm' t' | _, _ => False end ->
    (Ps t s -> isSortRelOpt s r -> ∑ s', Qs t' s' × isSortRelOpt s' r') ->
    lift_sorting Qc Qs (Judge tm' t' None r').
  Proof.
    intros (? & ? & Hs & e & er) s HPQc HPQs.
    split.
    - destruct tm, tm' => //=. now apply HPQc.
    - specialize (HPQs Hs er) as (s' & H & He).
      eexists. repeat split; eassumption.
  Qed.

  Lemma lift_sorting_it_impl_gen {Pc Qc Ps Qs} {tm tm' : option term} {t t' : term} {u r} :
    forall tu: lift_sorting Pc Ps (Judge tm t u r),
    let s := tu.2.π1 in
    match tm', tm with None, _ => unit | Some tm', Some tm => Pc tm t -> Qc tm' t' | _, _ => False end ->
    (Ps t s -> Qs t' s) ->
    lift_sorting Qc Qs (Judge tm' t' u r).
  Proof.
    intros (? & ? & Hs & e) s HPQc HPQs.
    split.
    - destruct tm, tm' => //=. now apply HPQc.
    - eexists. split; [now apply HPQs|].
      destruct u => //.
  Qed.

  Lemma lift_sorting_fu_it_impl {Pc Qc Ps Qs} {tm : option term} {t : term} {u r} :
    forall f fu, forall tu: lift_sorting Pc Ps (Judge tm t u r),
    let s := tu.2.π1 in
    option_default (fun rel => isSortRel s rel -> isSortRel (fu s) rel) r True ->
    option_default (fun tm => Pc tm t -> Qc (f tm) (f t)) tm unit ->
    (Ps t s -> Qs (f t) (fu s)) ->
    lift_sorting Qc Qs (Judge (option_map f tm) (f t) (option_map fu u) r).
  Proof.
    intros ?? (? & ? & Hs & e & er) s Hr HPQc HPQs.
    split.
    - destruct tm => //=. now apply HPQc.
    - eexists. split; [now apply HPQs|].
      split.
      + destruct u => //.
        cbn. f_equal => //.
      + destruct r => //.
        now apply Hr.
  Qed.

  Lemma lift_sorting_f_it_impl {Pc Qc Ps Qs} {j : judgment} :
    forall f, forall tu: lift_sorting Pc Ps j,
    let s := tu.2.π1 in
    option_default (fun tm => Pc tm (j_typ j) -> Qc (f tm) (f (j_typ j))) (j_term j) unit ->
    (Ps (j_typ j) s -> Qs (f (j_typ j)) s) ->
    lift_sorting Qc Qs (judgment_map f j).
  Proof.
    intro f.
    replace (judgment_map f j) with (Judge (option_map f (j_term j)) (f (j_typ j)) (option_map id (j_univ j)) (j_rel j)).
    2: unfold judgment_map; destruct j_univ => //.
    intro tu.
    apply lift_sorting_fu_it_impl with (fu := id) (tu := tu).
    destruct tu as (? & s & ?); cbn; clear.
    destruct j_rel => //.
  Qed.

  Lemma lift_sorting_it_impl {Pc Qc Ps Qs} {j} :
    forall tu: lift_sorting Pc Ps j,
    let s := tu.2.π1 in
    option_default (fun tm => Pc tm (j_typ j) -> Qc tm (j_typ j)) (j_term j) unit ->
    (Ps (j_typ j) s -> Qs (j_typ j) s) ->
    lift_sorting Qc Qs j.
  Proof.
    relativize (lift_sorting Qc Qs j).
    1: apply lift_sorting_f_it_impl with (f := id).
    destruct j, j_term => //.
  Qed.

  Lemma lift_sorting_fu_impl {Pc Qc Ps Qs tm t u r} :
    forall f fu,
    lift_sorting Pc Ps (Judge tm t u r) ->
    (forall r s, isSortRelOpt s r -> isSortRelOpt (fu s) r) ->
    (forall t T, Pc t T -> Qc (f t) (f T)) ->
    (forall t u, Ps t u -> Qs (f t) (fu u)) ->
    lift_sorting Qc Qs (Judge (option_map f tm) (f t) (option_map fu u) r).
  Proof.
    intros ?? tu Hr ??.
    apply lift_sorting_fu_it_impl with (tu := tu); auto.
    1: destruct r => //=; apply Hr with (r := Some _).
    destruct tm => //=. auto.
  Qed.

  Lemma lift_typing_fu_impl {P Q tm t u r} :
    forall f fu,
    lift_typing0 P (Judge tm t u r) ->
    (forall t T, P t T -> Q (f t) (f T)) ->
    (forall u, f (tSort u) = tSort (fu u)) ->
    (forall r s, isSortRelOpt s r -> isSortRelOpt (fu s) r) ->
    lift_typing0 Q (Judge (option_map f tm) (f t) (option_map fu u) r).
  Proof.
    intros ?? HT HPQ Hf Hr.
    apply lift_sorting_fu_impl with (1 := HT); tas.
    intros; rewrite -Hf; now apply HPQ.
  Qed.

  Lemma lift_sorting_f_impl {Pc Qc Ps Qs j} :
    forall f,
    lift_sorting Pc Ps j ->
    (forall t T, Pc t T -> Qc (f t) (f T)) ->
    (forall t u, Ps t u -> Qs (f t) u) ->
    lift_sorting Qc Qs (judgment_map f j).
  Proof.
    intros ? tu ??.
    apply lift_sorting_f_it_impl with (tu := tu); auto.
    destruct j_term => //=. auto.
  Qed.

  Lemma lift_typing_f_impl {P Q j} :
    forall f,
    lift_typing0 P j ->
    (forall t T, P t T -> Q (f t) (f T)) ->
    (forall u, f (tSort u) = tSort u) ->
    lift_typing0 Q (judgment_map f j).
  Proof.
    intros ? HT HPQ Hf.
    apply lift_sorting_f_impl with (1 := HT); tas.
    intros; rewrite -Hf; now apply HPQ.
  Qed.

  Lemma lift_typing_map {P} f j :
    lift_typing0 (fun t T => P (f t) (f T)) j ->
    (forall u, f (tSort u) = tSort u) ->
    lift_typing0 P (judgment_map f j).
  Proof.
    intros HT Hf.
    apply lift_typing_f_impl with (1 := HT) => //.
  Qed.

  Lemma lift_typing_mapu {P} f fu {tm ty u r} :
    lift_typing0 (fun t T => P (f t) (f T)) (Judge tm ty u r) ->
    (forall u, f (tSort u) = tSort (fu u)) ->
    (forall r s, isSortRelOpt s r -> isSortRelOpt (fu s) r) ->
    lift_typing0 P (Judge (option_map f tm) (f ty) (option_map fu u) r).
  Proof.
    intros HT.
    eapply lift_typing_fu_impl with (1 := HT) => //.
  Qed.

  Lemma lift_sorting_impl {Pc Qc Ps Qs j} :
    lift_sorting Pc Ps j ->
    (forall t T, Pc t T -> Qc t T) ->
    (forall t u, Ps t u -> Qs t u) ->
    lift_sorting Qc Qs j.
  Proof.
    intros tu ??.
    apply lift_sorting_it_impl with (tu := tu); auto.
    destruct j_term => //=. auto.
  Qed.

  Lemma lift_typing_impl {P Q j} :
    lift_typing0 P j ->
    (forall t T, P t T -> Q t T) ->
    lift_typing0 Q j.
  Proof.
    intros HT HPQ.
    apply lift_sorting_impl with (1 := HT); tas.
    intros; now apply HPQ.
  Qed.

  Lemma lift_typing_subject {P Q j} :
    lift_typing0 P j ->
    (forall t T, P t T -> Q t) ->
    lift_wf_term Q j.
  Proof.
    intros (? & ? & ? & _) HPQ.
    split; eauto.
    destruct j_term => //=.
    eauto.
  Qed.

  Lemma lift_typing_subjtyp {P Q Q' j} :
    lift_typing0 P j ->
    (forall t T, P t T -> Q t × Q T) ->
    (forall u, Q (tSort u) -> Q' u) ->
    lift_wfu_term Q Q' j.
  Proof.
    intros (Htm & s & Hty & e & er) HPQ HQQ'.
    repeat split.
    - destruct j_term => //=. eapply fst, HPQ, Htm.
    - eapply fst, HPQ, Hty.
    - destruct j_univ => //=. rewrite e. eapply HQQ', snd, HPQ, Hty.
  Qed.

  Section TypeLocal.
    Context (typing : forall (Γ : context), judgment -> Type).

    Inductive All_local_env : context -> Type :=
    | localenv_nil :
        All_local_env []

    | localenv_cons_abs Γ na t :
        All_local_env Γ ->
        typing Γ (j_vass na t) ->
        All_local_env (Γ ,, vass na t)

    | localenv_cons_def Γ na b t :
        All_local_env Γ ->
        typing Γ (j_vdef na b t) ->
        All_local_env (Γ ,, vdef na b t).

  Derive Signature NoConfusion for All_local_env.
  End TypeLocal.

  Arguments localenv_nil {_}.
  Arguments localenv_cons_def {_ _ _ _ _} _ _.
  Arguments localenv_cons_abs {_ _ _ _} _ _.

  Definition localenv_cons {typing Γ na bo t} :
    All_local_env typing Γ -> typing Γ (TermoptTypRel bo t na.(binder_relevance)) -> All_local_env typing (Γ ,, mkdecl na bo t)
    := match bo with None => localenv_cons_abs | Some b => localenv_cons_def end.

  Definition All_local_env_snoc {P Γ decl} : All_local_env P Γ -> on_local_decl P Γ decl -> All_local_env P (Γ ,, decl) :=
    match decl with mkdecl na bo t => localenv_cons end.

  Lemma All_local_env_tip {typing Γ decl} : All_local_env typing (Γ ,, decl) -> All_local_env typing Γ × on_local_decl typing Γ decl.
  Proof.
    intros wfΓ; depelim wfΓ.
    all: split; assumption.
  Defined.

  Lemma All_local_env_ind1 typing P :
    P [] ->
    (forall Γ decl, P Γ -> on_local_decl typing Γ decl -> P (Γ ,, decl)) ->
    forall Γ, All_local_env typing Γ -> P Γ.
  Proof.
    induction Γ => //.
    move/All_local_env_tip => [] ??.
    now apply X0.
  Defined.

  Lemma All_local_env_All_fold P Γ :
    All_local_env P Γ <~>
    All_fold (fun Γ decl => P Γ (j_decl decl)) Γ.
  Proof using Type.
    split.
    - induction 1 using All_local_env_ind1; constructor; auto.
    - induction 1; [constructor|].
      destruct d as [na [b|] ty]; cbn in p; constructor; auto.
  Qed.

  Lemma All_local_env_map (P : context -> judgment -> Type) f Γ :
    All_local_env (fun Γ j => P (map (map_decl f) Γ) (judgment_map f j)) Γ ->
    All_local_env P (map (map_decl f) Γ).
  Proof using Type.
    induction 1; econstructor; eauto.
  Qed.

  Lemma All_local_env_fold P f Γ :
    All_local_env (fun Γ j => P (fold_context_k f Γ) (judgment_map (f #|Γ|) j)) Γ <~>
    All_local_env P (fold_context_k f Γ).
  Proof.
    split.
    - induction 1; simpl; try unfold snoc; rewrite ?fold_context_k_snoc0; try constructor; auto.
    - induction Γ; simpl; try unfold snoc; rewrite ?fold_context_k_snoc0; intros H.
      * constructor.
      * destruct a as [na [b|] ty]; depelim H; specialize (IHΓ H); constructor; simpl; auto.
  Qed.

  Lemma All_local_env_impl_gen (P Q : context -> judgment -> Type) l :
    All_local_env P l ->
    (forall Γ decl, P Γ (j_decl decl) -> Q Γ (j_decl decl)) ->
    All_local_env Q l.
  Proof.
    intros H X.
    induction H using All_local_env_ind1. 1: constructor.
    apply All_local_env_snoc; auto.
  Qed.

  Lemma All_local_env_impl (P Q : context -> judgment -> Type) l :
    All_local_env P l ->
    (forall Γ j, P Γ j -> Q Γ j) ->
    All_local_env Q l.
  Proof.
    induction 1; intros; simpl; econstructor; eauto.
  Qed.

  Lemma All_local_env_impl_ind {P Q : context -> judgment -> Type} {l} :
    All_local_env P l ->
    (forall Γ j, All_local_env Q Γ -> P Γ j -> Q Γ j) ->
    All_local_env Q l.
  Proof.
    induction 1; intros; simpl; econstructor; eauto.
  Qed.

  Lemma All_local_env_skipn {P Γ} n : All_local_env P Γ -> All_local_env P (skipn n Γ).
  Proof.
    intros hΓ.
    induction n in Γ, hΓ |- * => //.
    destruct Γ; cbn; eauto.
    apply All_local_env_tip in hΓ as [].
    eauto.
  Defined.
  #[global]
  Hint Resolve All_local_env_skipn : wf.

  Lemma All_local_env_app_skipn {P Γ Δ} n : All_local_env P (Γ ,,, Δ) ->
    All_local_env P (Γ ,,, skipn n Δ).
  Proof.
    intros hΓ.
    induction n in Δ, hΓ |- * => //.
    destruct Δ; cbn; eauto.
    apply All_local_env_tip in hΓ as [].
    eauto.
  Qed.

  Lemma All_local_env_nth_error {P Γ n decl} : All_local_env P Γ -> nth_error Γ n = Some decl -> on_local_decl P (skipn (S n) Γ) decl.
  Proof.
    induction Γ in n |- *; destruct n => //= /All_local_env_tip [] wfΓ ondecl Hnth //=.
    - injection Hnth as [= ->]. assumption.
    - now eapply IHΓ.
  Defined.

  Lemma All_local_env_cst {P Γ} : All_local_env (fun _ => P) Γ <~> All (fun d => P (j_decl d)) Γ.
  Proof.
    split.
    - induction 1 using All_local_env_ind1; constructor => //.
    - induction 1. 1: constructor.
      apply All_local_env_snoc => //.
  Defined.

  Section All_local_env_rel.

    Definition All_local_rel P Γ Γ'
      := (All_local_env (fun Δ j => P (Γ ,,, Δ) j) Γ').

    Definition All_local_rel_nil {P Γ} : All_local_rel P Γ []
      := localenv_nil.

    Definition All_local_rel_snoc {P Γ Γ' decl} :
      All_local_rel P Γ Γ' -> on_local_decl P (Γ ,,, Γ') decl ->
      All_local_rel P Γ (Γ' ,, decl)
      := All_local_env_snoc.

    Definition All_local_rel_abs {P Γ Γ' A na} :
      All_local_rel P Γ Γ' -> P (Γ ,,, Γ') (j_vass na A)
      -> All_local_rel P Γ (Γ',, vass na A)
      := localenv_cons.

    Definition All_local_rel_def {P Γ Γ' t A na} :
      All_local_rel P Γ Γ' ->
      P (Γ ,,, Γ') (j_vdef na t A) ->
      All_local_rel P Γ (Γ',, vdef na t A)
      := localenv_cons.

    Definition All_local_rel_tip {P Γ Γ' decl} :
      All_local_rel P Γ (Γ' ,, decl) -> All_local_rel P Γ Γ' × on_local_decl P (Γ ,,, Γ') decl
      := All_local_env_tip.

    Definition All_local_rel_ind1 typing Γ P :
      P [] ->
      (forall Δ decl, P Δ -> on_local_decl typing (Γ ,,, Δ) decl -> P (Δ ,, decl)) ->
      forall Δ, All_local_rel typing Γ Δ -> P Δ
      := All_local_env_ind1 _ P.

    Lemma All_local_rel_local :
      forall P Γ,
        All_local_env P Γ ->
        All_local_rel P [] Γ.
    Proof.
      intros P Γ h. eapply All_local_env_impl.
      - exact h.
      - intros.
        rewrite app_context_nil_l. assumption.
    Defined.

    Lemma All_local_local_rel P Γ :
      All_local_rel P [] Γ -> All_local_env P Γ.
    Proof.
      intro X. eapply All_local_env_impl. exact X.
      intros Γ0 j XX; cbn in XX; rewrite app_context_nil_l in XX; assumption.
    Defined.

    Lemma All_local_app_rel {P Γ Γ'} :
      All_local_env P (Γ ,,, Γ') -> All_local_env P Γ × All_local_rel P Γ Γ'.
    Proof.
      induction Γ'.
      - intros hΓ.
        split.
        1: exact hΓ.
        constructor.
      - move => /= /All_local_env_tip [] hΓ ona.
        edestruct IHΓ' ; auto.
        split ; auto.
        apply All_local_rel_snoc; auto.
    Defined.

    Definition All_local_env_app_inv {P Γ Γ'} := @All_local_app_rel P Γ Γ'.

    Lemma All_local_rel_app_inv {P Γ Γ' Γ''} :
      All_local_rel P Γ (Γ' ,,, Γ'') -> All_local_rel P Γ Γ' × All_local_rel P (Γ ,,, Γ') Γ''.
    Proof.
      intro H.
      eapply All_local_env_app_inv in H as [H H'].
      split; tas.
      apply All_local_env_impl with (1 := H').
      intros; now rewrite -app_context_assoc.
    Defined.

    Lemma All_local_env_app {P Γ Γ'} :
      All_local_env P Γ -> All_local_rel P Γ Γ' -> All_local_env P (Γ ,,, Γ').
    Proof.
      induction 2 using All_local_rel_ind1 => //=.
      apply All_local_env_snoc; tas.
    Defined.

    Lemma All_local_rel_app {P Γ Γ' Γ''} :
      All_local_rel P Γ Γ' -> All_local_rel P (Γ ,,, Γ') Γ'' -> All_local_rel P Γ (Γ' ,,, Γ'').
    Proof.
      induction 2 using All_local_rel_ind1 => //=.
      apply All_local_rel_snoc; tas. now rewrite app_context_assoc.
    Defined.

    Lemma All_local_env_prod_inv :
      forall P Q Γ,
        All_local_env (fun Δ j => P Δ j × Q Δ j) Γ ->
        All_local_env P Γ × All_local_env Q Γ.
    Proof using Type.
      intros P Q Γ h.
      split; apply All_local_env_impl with (1 := h).
      all: now intros ??[].
    Qed.

    Lemma All_local_env_lift_prod_inv :
      forall P Q Δ,
        All_local_env (lift_typing1 (Prop_local_conj P Q)) Δ ->
        All_local_env (lift_typing1 P) Δ × All_local_env (lift_typing1 Q) Δ.
    Proof using Type.
      intros P Q Δ h.
      split; apply All_local_env_impl with (1 := h); intros ?? H; apply lift_typing_impl with (1 := H).
      all: move => ??[] //.
    Qed.

  End All_local_env_rel.

  Section TypeLocalOver.
    Context (checking : context -> term -> term -> Type).
    Context (sorting : context -> term -> sort -> Type).
    Context (cproperty : forall (Γ : context),
                All_local_env (lift_sorting1 checking sorting) Γ ->
                forall (t T : term), checking Γ t T -> Type).
    Context (sproperty : forall (Γ : context),
                All_local_env (lift_sorting1 checking sorting) Γ ->
                forall (t : term) (u : sort), sorting Γ t u -> Type).

    Inductive All_local_env_over_sorting :
        forall (Γ : context), All_local_env (lift_sorting1 checking sorting) Γ -> Type :=
    | localenv_over_nil :
        All_local_env_over_sorting [] localenv_nil

    | localenv_over_cons_abs Γ na t
        (all : All_local_env (lift_sorting1 checking sorting) Γ) :
        All_local_env_over_sorting Γ all ->
        forall (tu : lift_sorting1 checking sorting Γ (j_vass na t))
          (Hs: sproperty Γ all _ _ tu.2.π2.1),
          All_local_env_over_sorting (Γ ,, vass na t)
                              (localenv_cons_abs all tu)

    | localenv_over_cons_def Γ na b t
        (all : All_local_env (lift_sorting1 checking sorting) Γ) :
        All_local_env_over_sorting Γ all ->
        forall (tu : lift_sorting1 checking sorting Γ (j_vdef na b t))
          (Hc: cproperty Γ all _ _ tu.1)
          (Hs: sproperty Γ all _ _ tu.2.π2.1),
          All_local_env_over_sorting (Γ ,, vdef na b t)
                              (localenv_cons_def all tu).

  End TypeLocalOver.
  Derive Signature for All_local_env_over_sorting.

  Definition All_local_env_over typing property :=
    (All_local_env_over_sorting typing (typing_sort1 typing) property (fun Γ H t u tu => property _ H _ _ tu)).

  Lemma All_local_env_over_sorting_2 c s Pc Ps Γ (H : All_local_env (lift_sorting1 c s) Γ) :
    All_local_env_over_sorting _ _ (fun Γ _ t T _ => Pc Γ t T) (fun Γ _ t s _ => Ps Γ t s) _ H ->
    All_local_env (lift_sorting1 (Prop_local_conj c Pc) (Prop_local_conj s Ps)) Γ.
  Proof.
    induction 1; constructor; eauto.
    - destruct tu as (Htm & u & Hty & e).
      repeat (eexists; tea).
    - destruct tu as (Htm & u & Hty & e).
      repeat (eexists; tea).
  Defined.

  Definition on_wf_local_decl {typing Γ}
    (P : forall Γ (wfΓ : All_local_env (lift_typing1 typing) Γ) t T, typing Γ t T -> Type)
    (wfΓ : All_local_env (lift_typing1 typing) Γ) {d}
    (H : on_local_decl (lift_typing1 typing) Γ d) :=
  match d return (on_local_decl (lift_typing1 typing) Γ d) -> Type with
  | {| decl_name := na; decl_body := Some b; decl_type := ty |}
  => fun H => P Γ wfΓ b ty H.1 × P Γ wfΓ ty _ H.2.π2.1
  | {| decl_name := na; decl_body := None; decl_type := ty |}
  => fun H => P Γ wfΓ ty _ H.2.π2.1
  end H.


  Lemma nth_error_All_local_env_over {typing} {P Γ n decl} (eq : nth_error Γ n = Some decl) {wfΓ : All_local_env (lift_typing1 typing) Γ} :
    All_local_env_over typing P Γ wfΓ ->
    let Γ' := skipn (S n) Γ in
    let wfΓ' := All_local_env_skipn _ wfΓ in
    let p := All_local_env_nth_error wfΓ eq in
    (All_local_env_over typing P Γ' wfΓ' * on_wf_local_decl P wfΓ' p)%type.
  Proof.
    induction 1 in n, decl, eq |- *.
    - exfalso. destruct n => //.
    - destruct n; simpl.
    + simpl in *. split; tas. clear -Hs.
      destruct f_equal; cbn.
      assumption.
    + apply IHX.
    - destruct n; simpl.
    + simpl in *. split; tas. clear -Hc Hs.
      destruct f_equal; cbn.
      split; assumption.
    + apply IHX.
  Defined.

  Lemma All_local_env_over_2 typing P Γ (H : All_local_env (lift_typing1 typing) Γ) :
    All_local_env_over _ (fun Γ _ t T _ => P Γ t T) _ H ->
    All_local_env (lift_typing_conj typing P) Γ.
  Proof.
    apply All_local_env_over_sorting_2 with (Ps := fun Γ t u => P Γ t (tSort u)).
  Defined.

  Section TypeCtxInst.
    Context (typing : forall (Γ : context), term -> term -> Type).

    (* Γ |- s : Δ, where Δ is a telescope (reverse context) *)
    Inductive ctx_inst (Γ : context) : list term -> context -> Type :=
    | ctx_inst_nil : ctx_inst Γ [] []
    | ctx_inst_ass na t i inst Δ :
        typing Γ i t ->
        ctx_inst Γ inst (subst_telescope [i] 0 Δ) ->
        ctx_inst Γ (i :: inst) (vass na t :: Δ)
    | ctx_inst_def na b t inst Δ :
        ctx_inst Γ inst (subst_telescope [b] 0 Δ) ->
        ctx_inst Γ inst (vdef na b t :: Δ).
    Derive Signature NoConfusion for ctx_inst.
  End TypeCtxInst.

  Lemma ctx_inst_impl_gen Γ inst Δ args P :
    { P' & ctx_inst P' Γ inst Δ } ->
    (forall t T,
        All (fun P' => P' Γ t T) args ->
        P Γ t T) ->
    All (fun P' => ctx_inst P' Γ inst Δ) args ->
    ctx_inst P Γ inst Δ.
  Proof.
    intros [? Hexists] HPQ H.
    induction Hexists; constructor; tea.
    all: first [ apply IHHexists; clear IHHexists
               | apply HPQ ].
    all: eapply All_impl; tea; cbn; intros *; inversion 1; subst; eauto.
  Qed.

  Lemma ctx_inst_impl P Q Γ inst Δ :
    ctx_inst P Γ inst Δ ->
    (forall t T, P Γ t T -> Q Γ t T) ->
    ctx_inst Q Γ inst Δ.
  Proof.
    intros H HPQ. induction H; econstructor; auto.
  Qed.

  Definition option_default_size {A f} (fsize : forall (a : A), f a -> size) o (w : option_default f o (unit : Type)) : size :=
    match o as tm return option_default _ tm (unit : Type) -> size with
    | Some tm => fun w => fsize _ w
    | None => fun w => 0
    end w.

  Section lift_sorting_size_gen.
    Context {checking : term -> term -> Type}.
    Context {sorting : term -> sort -> Type}.
    Context (csize : forall (t T : term), checking t T -> size).
    Context (ssize : forall (t : term) (u : sort), sorting t u -> size).

    Definition lift_sorting_size_gen base j (w : lift_sorting checking sorting j) : size :=
      base + option_default_size (fun tm => csize tm _) (j_term j) w.1 + ssize _ _ w.2.π2.1.


    Lemma lift_sorting_size_gen_impl {Qc Qs j} :
      forall tu: lift_sorting checking sorting j,
      (forall t T, forall Hty: checking t T, csize _ _ Hty <= lift_sorting_size_gen 0 _ tu -> Qc t T) ->
      (forall t u, forall Hty: sorting t u, ssize _ _ Hty <= lift_sorting_size_gen 0 _ tu -> Qs t u) ->
      lift_sorting Qc Qs j.
    Proof.
      intros (Htm & s & Hty & es) HPQc HPQs.
      unfold lift_sorting_size_gen in *; cbn in *.
      repeat (eexists; tea).
      - destruct (j_term j) => //=.
        eapply HPQc with (Hty := Htm); cbn.
        lia.
      - eapply HPQs with (Hty := Hty); cbn.
        lia.
    Qed.

  End lift_sorting_size_gen.

  Definition on_def_type_size_gen {c s} (ssize : forall Γ t u, s Γ t u -> size) base
                                      Γ d (w : on_def_type (lift_sorting1 c s) Γ d) : size :=
    base + ssize _ _ _ w.2.π2.1.
  Definition on_def_body_size_gen {c s} (csize : forall Γ t u, c Γ t u -> size) (ssize : forall Γ t u, s Γ t u -> size) base
                                      types Γ d (w : on_def_body (lift_sorting1 c s) types Γ d) : size :=
    base + csize _ _ _ w.1 + ssize _ _ _ w.2.π2.1.

  Notation lift_sorting_size csize ssize := (lift_sorting_size_gen csize ssize 1).
  Notation typing_sort_size typing_size := (fun t s (tu: typing_sort _ t s) => typing_size t (tSort s) tu).
  Notation lift_typing_size typing_size := (lift_sorting_size_gen typing_size%function (typing_sort_size typing_size%function) 0).
  Notation typing_sort_size1 typing_size := (fun Γ t s (tu: typing_sort1 _ Γ t s) => typing_size Γ t (tSort s) tu).
  Notation on_def_type_sorting_size ssize := (on_def_type_size_gen ssize 1).
  Notation on_def_type_size typing_size := (on_def_type_size_gen (typing_sort_size1 typing_size) 0).
  Notation on_def_body_sorting_size csize ssize := (on_def_body_size_gen csize ssize 1).
  Notation on_def_body_size typing_size := (on_def_body_size_gen typing_size%function (typing_sort_size1 typing_size%function) 0).
  (* Will probably not pass the guard checker if in a list, must be unrolled like in on_def_* *)

  Lemma lift_sorting_size_impl {checking sorting Qc Qs j} csize ssize :
    forall tu: lift_sorting checking sorting j,
    (forall t T, forall Hty: checking t T, csize _ _ Hty < lift_sorting_size csize ssize _ tu -> Qc t T) ->
    (forall t u, forall Hty: sorting t u,  ssize _ _ Hty < lift_sorting_size csize ssize _ tu -> Qs t u) ->
    lift_sorting Qc Qs j.
  Proof.
    intros tu Xc Xs.
    eapply lift_sorting_size_gen_impl with (tu := tu).
    all: intros.
    1: eapply Xc. 2: eapply Xs.
    all: apply le_n_S, H.
  Qed.

  Lemma lift_typing_size_impl {P Q j} Psize :
    forall tu: lift_typing0 P j,
    (forall t T, forall Hty: P t T, Psize _ _ Hty <= lift_typing_size Psize _ tu -> Q t T) ->
    lift_typing0 Q j.
  Proof.
    intros.
    eapply lift_sorting_size_gen_impl with (csize := Psize).
    all: intros t T; apply X.
  Qed.

  Section All_local_env_size.
    Context {checking : forall (Γ : context), term -> term -> Type}.
    Context {sorting : forall (Γ : context), term -> sort -> Type}.
    Context (csize : forall Γ t T, checking Γ t T -> size).
    Context (ssize : forall Γ t u, sorting Γ t u -> size).

    Fixpoint All_local_env_size_gen base Γ (w : All_local_env (lift_sorting1 checking sorting) Γ) : size :=
      match w with
      | localenv_nil => base
      | localenv_cons_abs Γ' na t w' p => ssize _ _ _ p.2.π2.1 + All_local_env_size_gen base _ w'
      | localenv_cons_def Γ' na b t w' p => csize _ _ _ p.1 + ssize _ _ _ p.2.π2.1 + All_local_env_size_gen base _ w'
      end.

    Lemma All_local_env_size_pos base Γ w : base <= All_local_env_size_gen base Γ w.
    Proof using Type.
      induction w.
      all: simpl ; lia.
    Qed.
  End All_local_env_size.

  Notation All_local_rel_size_gen c s csize ssize base := (fun Γ Δ (w : All_local_rel (lift_sorting1 c s) Γ Δ) =>
    All_local_env_size_gen (fun Δ => csize (Γ ,,, Δ)) (fun Δ => ssize (Γ ,,, Δ)) base Δ w).

  Lemma All_local_env_size_app c s csize ssize base Γ Γ' (wfΓ : All_local_env (lift_sorting1 c s) Γ) (wfΓ' : All_local_rel (lift_sorting1 c s) Γ Γ') :
    All_local_env_size_gen csize ssize base _ (All_local_env_app wfΓ wfΓ') + base = All_local_env_size_gen csize ssize base _ wfΓ + All_local_rel_size_gen c s csize ssize base _ _ wfΓ'.
  Proof.
    induction Γ'.
    - dependent inversion wfΓ'.
      reflexivity.
    - revert IHΓ'.
      dependent inversion wfΓ' ; subst ; intros.
      + cbn.
        etransitivity.
        2: rewrite Nat.add_comm -Nat.add_assoc [X in _ + X]Nat.add_comm -IHΓ' Nat.add_assoc ; reflexivity.
        reflexivity.
      + cbn.
        etransitivity.
        2: rewrite Nat.add_comm -Nat.add_assoc [X in _ + X]Nat.add_comm -IHΓ' Nat.add_assoc ; reflexivity.
        reflexivity.
  Qed.

  Implicit Types (Σ : global_env_ext) (Γ : context) (t : term).

  Section Regular.
    Context {typing : context -> term -> term -> Type}.
    Context (typing_size : forall Γ t T, typing Γ t T -> size).

    Definition All_local_env_size := All_local_env_size_gen typing_size (typing_sort1 typing_size) 0.
    Definition All_local_rel_size Γ Γ' (wfΓ : All_local_rel (lift_typing1 typing) Γ Γ') := All_local_rel_size_gen typing (typing_sort1 typing) typing_size (typing_sort_size1 typing_size) 0 Γ Γ' wfΓ.
  End Regular.

  Section Bidirectional.
    Context {checking : context -> term -> term -> Type} {sorting : context -> term -> sort -> Type}.
    Context (checking_size : forall Γ t T, checking Γ t T -> size).
    Context (sorting_size : forall Γ t s, sorting Γ t s -> size).

    Definition All_local_env_sorting_size := All_local_env_size_gen checking_size sorting_size 1.
    Definition All_local_rel_sorting_size := All_local_rel_size_gen _ _ checking_size sorting_size 1.
  End Bidirectional.

End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
  Include EnvTyping T E TU.
End EnvTypingSig.

Module Conversion (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
  Import T E TU ET.

  Section Conversion.
  Context (cumul_gen : global_env_ext -> context -> conv_pb -> term -> term -> Type).

  Inductive All_decls_alpha_pb {pb} {P : conv_pb -> term -> term -> Type} :
    context_decl -> context_decl -> Type :=
  | all_decls_alpha_vass {na na' : binder_annot name} {t t' : term}
    (eqna : eq_binder_annot na na')
    (eqt : P pb t t') :
    All_decls_alpha_pb (vass na t) (vass na' t')

  | all_decls_alpha_vdef {na na' : binder_annot name} {b t b' t' : term}
    (eqna : eq_binder_annot na na')
    (eqb : P Conv b b') (* Note that definitions must be convertible, otherwise this notion
    of cumulativity is useless *)
    (eqt : P pb t t') :
    All_decls_alpha_pb (vdef na b t) (vdef na' b' t').

  Derive Signature NoConfusion for All_decls_alpha_pb.

  Arguments All_decls_alpha_pb pb P : clear implicits.

  Definition cumul_pb_decls pb (Σ : global_env_ext) (Γ Γ' : context) : forall (x y : context_decl), Type :=
    All_decls_alpha_pb pb (cumul_gen Σ Γ).

  Definition cumul_pb_context pb (Σ : global_env_ext) :=
    All2_fold (cumul_pb_decls pb Σ).

  Definition cumul_ctx_rel Σ Γ Δ Δ' :=
    All2_fold (fun Δ Δ' => cumul_pb_decls Cumul Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ'.
  End Conversion.

  Arguments All_decls_alpha_pb pb P : clear implicits.
  Notation conv cumul_gen Σ Γ := (cumul_gen Σ Γ Conv).
  Notation cumul cumul_gen Σ Γ := (cumul_gen Σ Γ Cumul).

  Notation conv_decls cumul_gen := (cumul_pb_decls cumul_gen Conv).
  Notation cumul_decls cumul_gen := (cumul_pb_decls cumul_gen Cumul).
  Notation conv_context cumul_gen Σ := (cumul_pb_context cumul_gen Conv Σ).
  Notation cumul_context cumul_gen Σ := (cumul_pb_context cumul_gen Cumul Σ).

  Lemma All_decls_alpha_pb_impl {pb} {P Q : conv_pb -> term -> term -> Type} {t t'} :
    (forall pb t t', P pb t t' -> Q pb t t') ->
    All_decls_alpha_pb pb P t t' -> All_decls_alpha_pb pb Q t t'.
  Proof. induction 2; constructor; eauto. Qed.
End Conversion.

Module Type ConversionSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
  Include Conversion T E TU ET.
End ConversionSig.


Module GlobalMaps (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
  (** *** Typing of inductive declarations *)
  Import T E TU ET C L.

  Section GlobalMaps.

    Context {cf: checker_flags}.
    Context (Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type).
    Context (P : global_env_ext -> context -> judgment -> Type).
    Definition on_context Σ ctx :=
      All_local_env (P Σ) ctx.

    (** For well-formedness of inductive declarations we need a way to check that a assumptions
      of a given context is typable in a sort [u]. We also force well-typing of the let-ins
      in any universe to imply wf_local. *)
    Fixpoint type_local_ctx Σ (Γ Δ : context) (u : sort) : Type :=
      match Δ with
      | [] => wf_sort Σ u
      | {| decl_name := na; decl_body := None; decl_type := t |} :: Δ =>
          type_local_ctx Σ Γ Δ u × P Σ (Γ ,,, Δ) (TypUnivRel t u na.(binder_relevance))
      | {| decl_body := Some _; |} as d :: Δ =>
          type_local_ctx Σ Γ Δ u × P Σ (Γ ,,, Δ) (j_decl d)
      end.

    Fixpoint sorts_local_ctx Σ (Γ Δ : context) (us : list sort) : Type :=
      match Δ, us with
      | [], [] => unit
      | {| decl_name := na; decl_body := None;   decl_type := t |} :: Δ, u :: us =>
        sorts_local_ctx Σ Γ Δ us × P Σ (Γ ,,, Δ) (TypUnivRel t u na.(binder_relevance))
      | {| decl_body := Some _ |} as d :: Δ, us =>
        sorts_local_ctx Σ Γ Δ us × P Σ (Γ ,,, Δ) (j_decl d)
      | _, _ => False
      end.

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body).

    Definition on_type Σ Γ T := P Σ Γ (Typ T).
    Definition on_type_rel Σ Γ T r := P Σ Γ (TypRel T r).

    Open Scope type_scope.

    Definition univs_ext_constraints univs φ :=
      UnivConstraintSet.union (constraints_of_udecl φ) univs.

    Definition satisfiable_udecl (univs : ContextSet.t) φ
      := consistent (univs_ext_constraints (ContextSet.constraints univs) φ).

    (* Constraints from udecl between *global* universes
       are implied by the constraints in univs *)
    Definition valid_on_mono_udecl (univs : ContextSet.t) ϕ :=
      consistent_extension_on univs (constraints_of_udecl ϕ).

    (* Check that: *)
    (*   - declared levels are fresh *)
    (*   - all levels used in constraints are declared *)
    Definition on_udecl (univs : ContextSet.t) (udecl : universes_decl)
      := let levels := levels_of_udecl udecl in
        let global_levels := global_levels univs in
        let all_levels := LevelSet.union levels global_levels in
        LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels
        /\ UnivConstraintSet.For_all (declared_univ_cstr_levels all_levels) (constraints_of_udecl udecl)
        /\ satisfiable_udecl univs udecl
        /\ valid_on_mono_udecl univs udecl.

    (** Positivity checking of the inductive, ensuring that the inductive itself
      can only appear at the right of an arrow in each argument's types. *)
    (*
    Definition positive_cstr_arg ninds npars narg (arg : term) : bool :=
      (* We decompose the constructor's arguments' type and verify the inductive references
        only appear in the conclusion, if any. *)
      let (ctx, concl) := decompose_prod_assum [] arg in
      (* Again, we smash the context, as Rocq does *)
      let ctx := smash_context [] ctx in
      alli (fun i d => noccur_between (npars + narg + i) ninds d.(decl_type)) 0 (List.rev ctx) &&
      let (hd, args) := decompose_app concl in
      match hd with
      | tRel i =>
        if noccur_between (npars + narg + #|ctx|) ninds (tRel i) then
          (* Call to an unrelated variable *)
          true
        else (* Recursive call to the inductive *)
          (* Rocq disallows the inductive to be applied to another inductive in the block *)
          forallb (noccur_between (npars + narg + #|ctx|) ninds) args
      | tInd ind u =>
        if forallb (noccur_between (npars + narg + #|ctx|) ninds) args then
          (* Unrelated inductive *)
          true
        else (* Nested inductive *)
          true
      end.

    Definition positive_cstr_args ninds npars (args : context) : bool :=
      alli (fun i decl => positive_cstr_arg nind npars i decl.(decl_type))
      (* We smash the context, just as Rocq's kernel computes positivity on
        weak-head normalized types *)
      (List.rev (smash_context [] args))
    *)

    (** A constructor argument type [t] is positive w.r.t. an inductive block [mdecl]
        when it's zeta-normal form is of the shape Π Δ. concl and:
        - [t] does not refer to any inductive in the block.
          In that case [t] must be a closed type under the context of parameters and
          previous arguments.
        - None of the variable assumptions in Δ refer to any inductive in the block,
          but the conclusion [concl] is of the form [mkApps (tRel k) args] for k
          refering to an inductive in the block, and none of the arguments [args]
          refer to the inductive. #|args| must be the length of the full inductive application.

      Let-in assumptions in Δ are systematically unfolded, i.e. we really consider:
      the zeta-reduction of [t]. *)

    Definition ind_realargs (o : one_inductive_body) :=
      match destArity [] o.(ind_type) with
      | Some (ctx, _) => #|smash_context [] ctx|
      | _ => 0
      end.

    Definition mdecl_at_i mdecl i (Γ:context) k : Prop :=
      #|Γ| <= k /\ k < #|Γ| + #|mdecl.(ind_bodies)| /\
       nth_error (List.rev mdecl.(ind_bodies)) (k - #|Γ|) = Some i.

    Reserved Notation " mdecl ;;; Γ |arg+> t " (at level 50, Γ, t at next level).
    Notation subst0 t := (subst t 0).
    Notation "M { j := N }" := (subst [N] j M) (at level 10, right associativity).

    Inductive positive_cstr_arg mdecl Γ : term -> Type :=
    | pos_arg_closed ty :
      closedn #|Γ| ty ->
      mdecl ;;; Γ |arg+> ty

    | pos_arg_concl l k i :
      (** Mutual inductive references in the conclusion are ok *)
      #|l| = ind_realargs i -> All (closedn #|Γ|) l ->
      mdecl_at_i mdecl i Γ k ->
      mdecl ;;; Γ |arg+> mkApps (tRel k) l

    | pos_arg_let na b ty ty' :
      mdecl ;;; Γ |arg+> ty' {0 := b} ->
      mdecl ;;; Γ |arg+> tLetIn na b ty ty'

    | pos_arg_ass na ty ty' :
      closedn #|Γ| ty ->
      mdecl ;;; vass na ty :: Γ |arg+> ty' ->
      mdecl ;;; Γ |arg+> tProd na ty ty'

  where " mdecl ;;; Γ |arg+> t " := (positive_cstr_arg mdecl Γ t) : type_scope.

    (** A constructor type [t] is positive w.r.t. an inductive block [mdecl]
      and inductive [i] when it's zeta normal-form is of the shape Π Δ. concl and:
        - All of the arguments in Δ are positive.
        - The conclusion is of the shape [mkApps (tRel k) indices]
          where [k] refers to the current inductive [i] and [indices] does not mention
          any of the inductive types in the block. I.e. [indices] are closed terms
          in [params ,,, args]. *)

    Reserved Notation " mdecl @ i ;;; Γ |+> t " (at level 50, i, Γ, t at next level).


    Inductive positive_cstr mdecl i Γ : term -> Type :=
    | pos_concl l (headrel := (#|mdecl.(ind_bodies)| - S i + #|Γ|)%nat) :
      All (closedn #|Γ|) l ->
      mdecl @ i ;;; Γ |+> mkApps (tRel headrel) l

    | pos_let na b ty ty' :
      mdecl @ i ;;; Γ |+> ty' {0 := b} ->
      mdecl @ i ;;; Γ |+> tLetIn na b ty ty'

    | pos_ass na ty ty' :
      mdecl ;;; Γ |arg+> ty ->
      mdecl @ i ;;; vass na ty :: Γ |+> ty' ->
      mdecl @ i ;;; Γ |+> tProd na ty ty'

    where " mdecl @ i ;;; Γ |+> t " := (positive_cstr mdecl i Γ t) : type_scope.

    Definition lift_level n l :=
      match l with
      | Level.lzero | Level.level _ => l
      | Level.lvar k => Level.lvar (n + k)
      end.

    Definition on_fst {A B} (f : A -> A) (x : A * B) : A * B := (f x.1, x.2).

    Definition lift_universe n u :=
      Universe.map (on_fst (lift_level n)) u.

    Definition lift_instance n l :=
      map (lift_universe n) l.

    Definition lift_constraint n (c : Universe.t * ConstraintType.t * Universe.t) :=
      let '((l, r), l') := c in
      ((lift_universe n l, r), lift_universe n l').

    Definition lift_constraints n cstrs :=
      UnivConstraintSet.fold (fun elt acc => UnivConstraintSet.add (lift_constraint n elt) acc)
        cstrs UnivConstraintSet.empty.

    Definition level_var_instance n (inst : list name) : LevelInstance.t :=
      mapi_rec (fun i _ => Level.lvar i) inst n.

    Fixpoint variance_cstrs (v : list Variance.t) (u u' : Instance.t) :=
      match v, u, u' with
      | _, [], [] => UnivConstraintSet.empty
      | v :: vs, u :: us, u' :: us' =>
        match v with
        | Variance.Irrelevant => variance_cstrs vs us us'
        | Variance.Covariant => UnivConstraintSet.add (u, ConstraintType.Le, u') (variance_cstrs vs us us')
        | Variance.Invariant => UnivConstraintSet.add (u, ConstraintType.Eq, u') (variance_cstrs vs us us')
        end
      | _, _, _ => (* Impossible due to on_variance invariant *) UnivConstraintSet.empty
      end.

    (** This constructs a duplication of the polymorphic universe context of the inductive,
      where the two instances are additionally related according to the variance information.
    *)

    Definition variance_universes univs v :=
      match univs with
      | Monomorphic_ctx => None
      | Polymorphic_ctx auctx =>
        let (inst, cstrs) := auctx in
        let u' : Instance.t := level_var_instance 0 inst in
        let u := lift_instance #|inst| u' in
        let cstrs := UnivConstraintSet.union cstrs (lift_constraints #|inst| cstrs) in
        let cstrv := variance_cstrs v u u' in
        let auctx' := (inst ++ inst, UnivConstraintSet.union cstrs cstrv) in
        Some (Polymorphic_ctx auctx', u, u')
      end.

    (** A constructor type respects the given variance [v] if each constructor
        argument respects it and each index (in the conclusion) does as well.
        We formalize this by asking for a cumulativity relation between the contexts
        of arguments and conversion of the lists of indices instanciated with [u] and
        [u'] where [u `v` u']. *)

    Definition ind_arities mdecl := arities_context (ind_bodies mdecl).

    Definition ind_respects_variance Σ mdecl v indices :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel Pcmp (Σ, univs) (smash_context [] (ind_params mdecl))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] indices))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] indices))@[u']
      | None => False
      end.

    Definition cstr_respects_variance Σ mdecl v cs :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel Pcmp (Σ, univs) (ind_arities mdecl ,,, smash_context [] (ind_params mdecl))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))@[u'] *
        All2
          (Pcmp (Σ, univs) (ind_arities mdecl ,,, smash_context [] (ind_params mdecl ,,, cstr_args cs))@[u] Conv)
          (map (subst_instance u ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
          (map (subst_instance u' ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
      | None => False (* Monomorphic inductives have no variance attached *)
      end.

    (* Conclusion head: reference to the current inductive in the block *)
    Definition cstr_concl_head mdecl i cdecl :=
      tRel (#|mdecl.(ind_bodies)| - S i + #|mdecl.(ind_params)| + #|cstr_args cdecl|).

    (* Constructor conclusion shape: the inductives type applied to variables for
       the (non-let) parameters
       followed by the indices *)
    Definition cstr_concl mdecl i cdecl :=
      (mkApps (cstr_concl_head mdecl i cdecl)
        (to_extended_list_k mdecl.(ind_params) #|cstr_args cdecl|
          ++ cstr_indices cdecl)).

    Record on_constructor Σ mdecl i idecl ind_indices cdecl cunivs := {
      (* cdecl.1 fresh ?? *)
      cstr_args_length : context_assumptions (cstr_args cdecl) = cstr_arity cdecl;

      cstr_eq : cstr_type cdecl =
       it_mkProd_or_LetIn mdecl.(ind_params)
        (it_mkProd_or_LetIn (cstr_args cdecl)
          (cstr_concl mdecl i cdecl));
      (* The type of the constructor canonically has this shape: parameters, real
        arguments ending with a reference to the inductive applied to the
        (non-lets) parameters and arguments *)

      on_ctype : on_type_rel Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl) idecl.(ind_relevance);
      on_cargs :
        sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cdecl.(cstr_args) cunivs;
      on_cindices :
        ctx_inst (fun Γ t T => P Σ Γ (TermTyp t T)) (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cdecl.(cstr_args))
                      cdecl.(cstr_indices)
                      (List.rev (lift_context #|cdecl.(cstr_args)| 0 ind_indices));

      on_ctype_positive : (* The constructor type is positive *)
        positive_cstr mdecl i [] (cstr_type cdecl);

      on_ctype_variance : (* The constructor type respect the variance annotation
        on polymorphic universes, if any. *)
        forall v, ind_variance mdecl = Some v ->
        cstr_respects_variance Σ mdecl v cdecl;

      on_lets_in_type : if lets_in_constructor_types
                        then True else is_true (is_assumption_context (cstr_args cdecl))
    }.

    Arguments on_ctype {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cargs {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cindices {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_args_length {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_eq {Σ mdecl i idecl ind_indices cdecl cunivs}.

    Definition on_constructors Σ mdecl i idecl ind_indices :=
      All2 (on_constructor Σ mdecl i idecl ind_indices).

    (** Each projection type corresponds to a non-let argument of the
        corresponding constructor. It is parameterized over the
        parameters of the inductive type and all the preceding arguments
        of the constructor. When computing the type of a projection for argument
        [n] at a given instance of the parameters and a given term [t] in the inductive
        type, we instantiate the argument context by corresponsping projections
        [t.π1 ... t.πn-1]. This is essential for subject reduction to hold: each
        projections type can only refer to the record object through projections.

      Projection types have their parameter and argument contexts smashed to avoid
      costly computations during type-checking and reduction: we can just substitute
      the instances of parameters and the inductive value without considering the
      presence of let bindings. *)

    Record on_proj mdecl mind i k (p : projection_body) decl :=
      { on_proj_name : (* All projections are be named after a constructor argument. *)
          binder_name (decl_name decl) = nNamed p.(proj_name);
        on_proj_type :
          (** The stored projection type already has the references to the inductive
              type substituted along with the previous arguments replaced by projections. *)
          let u := abstract_instance mdecl.(ind_universes) in
          let ind := {| inductive_mind := mind; inductive_ind := i |} in
          p.(proj_type) = subst (inds mind (Instance.of_level_instance u) mdecl.(ind_bodies)) (S (ind_npars mdecl))
            (subst (projs ind mdecl.(ind_npars) k) 0
              (lift 1 k (decl_type decl)));
        on_proj_relevance : p.(proj_relevance) = decl.(decl_name).(binder_relevance) }.

    Definition on_projection mdecl mind i cdecl (k : nat) (p : projection_body) :=
      let Γ := smash_context [] (cdecl.(cstr_args) ++ mdecl.(ind_params)) in
      match nth_error Γ (context_assumptions cdecl.(cstr_args) - S k) with
      | None => False
      | Some decl => on_proj mdecl mind i k p decl
      end.

    Record on_projections mdecl mind i idecl (ind_indices : context) cdecl :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;
        (** The inductive must be a record *)

        on_projs_noidx : #|ind_indices| = 0;
        (** The inductive cannot have indices *)

        on_projs_elim : idecl.(ind_kelim) = IntoAny;
        (** This ensures that all projections are definable *)

        on_projs_all : #|idecl.(ind_projs)| = context_assumptions (cstr_args cdecl);
        (** There are as many projections as (non-let) constructor arguments *)

        on_projs : Alli (on_projection mdecl mind i cdecl) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ cunivss ind_sort :=
      Forall (fun cunivs =>
        Forall (fun argsort => leq_sort φ argsort ind_sort) cunivs) cunivss.

    (** This ensures that all sorts in kelim are lower
        or equal to the top elimination sort, if set.
        For inductives in Type we do not check [kelim] currently. *)

    Definition constructor_univs := list sort.
    (* The sorts of the arguments context (without lets) *)

    Definition elim_sort_prop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] => (* Empty inductive proposition: *) IntoAny
      | [ s ] =>
        if forallb Sort.is_propositional s then
          IntoAny (* Singleton elimination *)
        else
          IntoPropSProp (* Squashed: some arguments are higher than Prop, restrict to Prop *)
      | _ => (* Squashed: at least 2 constructors *) IntoPropSProp
      end.

    Definition elim_sort_sprop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] => (* Empty inductive strict proposition: *) IntoAny
      | _ => (* All other inductives in SProp are squashed *) IntoSProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices cdecls ind_sort : Type :=
      match Sort.to_family ind_sort with
      | Sort.fProp =>
        (** The inductive is declared in the impredicative sort Prop *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        (allowed_eliminations_subset kelim (elim_sort_prop_ind cdecls) : Type)
      | Sort.fSProp =>
        (** The inductive is declared in the impredicative sort SProp *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        (allowed_eliminations_subset kelim (elim_sort_sprop_ind cdecls) : Type)
      | _ =>
        (** The inductive is predicative: check that all constructors arguments are
            smaller than the declared universe. *)
        check_constructors_smaller Σ cdecls ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True
      end.

    Record on_ind_body Σ mind mdecl i idecl :=
      { (** The type of the inductive must be an arity, sharing the same params
            as the rest of the block, and maybe having a context of indices. *)
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn idecl.(ind_indices) (tSort idecl.(ind_sort)));

        (** It must be well-typed in the empty context. *)
        onArity : on_type_rel Σ [] idecl.(ind_type) rel_of_Type;

        (** The sorts of the arguments contexts of each constructor *)
        ind_cunivs : list constructor_univs;

        (** Constructors are well-typed *)
        onConstructors :
          on_constructors Σ mdecl i idecl idecl.(ind_indices) idecl.(ind_ctors) ind_cunivs;

        (** Projections, if any, are well-typed *)
        onProjections :
          match idecl.(ind_projs), idecl.(ind_ctors) return Type with
          | [], _ => True
          | _, [ o ] =>
              on_projections mdecl mind i idecl idecl.(ind_indices) o
          | _, _ => False
          end;

        (** The universes and elimination sorts must be correct w.r.t.
            the universe of the inductive and the universes in its constructors, which
            are declared in [on_constructors]. *)
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          idecl.(ind_indices) ind_cunivs idecl.(ind_sort);

        ind_relevance_compat : isSortRel idecl.(ind_sort) idecl.(ind_relevance);

        onIndices :
          (* The inductive type respect the variance annotation on polymorphic universes, if any. *)
          match ind_variance mdecl with
          | Some v => ind_respects_variance Σ mdecl v idecl.(ind_indices)
          | None => True
          end
      }.

    Definition on_variance Σ univs (variances : option (list Variance.t)) :=
      match univs return Type with
      | Monomorphic_ctx => variances = None
      | Polymorphic_ctx auctx =>
        match variances with
        | None => unit
        | Some v =>
          ∑ univs' i i',
            [/\ (variance_universes univs v = Some (univs', i, i')),
              consistent_instance_ext (Σ, univs') univs i,
              consistent_instance_ext (Σ, univs') univs i' &
              List.length v = #|UContext.instance (AUContext.repr auctx)|]
        end
      end.

    (** We allow empty blocks for simplicity
        (no well-typed reference to them can be made). *)

    Record on_inductive Σ mind mdecl :=
      { onInductives : Alli (on_ind_body Σ mind mdecl) 0 mdecl.(ind_bodies);
        (** We check that the context of parameters is well-formed and that
            the size annotation counts assumptions only (no let-ins). *)
        onParams : on_context Σ mdecl.(ind_params);
        onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
        (** We check that the variance annotations are well-formed: i.e. they
          form a valid universe context. *)
        onVariance : on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance);
      }.

    (** *** Typing of constant declarations *)

    Definition on_constant_decl Σ d :=
      P Σ [] (TermoptTypRel d.(cst_body) d.(cst_type) d.(cst_relevance)).

    Definition on_global_decl Σ kn decl :=
      match decl with
      | ConstantDecl d => on_constant_decl Σ d
      | InductiveDecl inds => on_inductive Σ kn inds
      end.

    (** *** Typing of global environment

        All declarations should be typeable and the global
        set of universe constraints should be consistent. *)

    (** Well-formed global environments have no name clash. *)

    Definition fresh_global (s : kername) (g : global_declarations) : Prop :=
      Forall (fun g => g.1 <> s) g.

    Record on_global_decls_data (univs : ContextSet.t) retro (Σ : global_declarations) (kn : kername) (d : global_decl) :=
        {
          kn_fresh :  fresh_global kn Σ ;
          udecl := universes_decl_of_decl d ;
          on_udecl_udecl : on_udecl univs udecl ;
          on_global_decl_d : on_global_decl (mk_global_env univs Σ retro, udecl) kn d
        }.

    Inductive on_global_decls (univs : ContextSet.t) (retro : Retroknowledge.t): global_declarations -> Type :=
    | globenv_nil : on_global_decls univs retro []
    | globenv_decl Σ kn d :
        on_global_decls univs retro Σ ->
        on_global_decls_data univs retro Σ kn d ->
        on_global_decls univs retro (Σ ,, (kn, d)).

    Derive Signature for on_global_decls.

    Lemma fresh_global_iff_not_In kn Σ
      : fresh_global kn Σ <-> ~ In kn (map fst Σ).
    Proof using Type.
      rewrite /fresh_global; split; [ induction 1 | induction Σ; constructor ]; cbn in *.
      all: tauto.
    Qed.

    Lemma fresh_global_iff_lookup_global_None kn Σ
      : fresh_global kn Σ <-> lookup_global Σ kn = None.
    Proof using Type. rewrite fresh_global_iff_not_In lookup_global_None //. Qed.

    Lemma fresh_global_iff_lookup_globals_nil kn Σ
      : fresh_global kn Σ <-> lookup_globals Σ kn = [].
    Proof using Type. rewrite fresh_global_iff_not_In lookup_globals_nil //. Qed.

    Lemma NoDup_on_global_decls univs retro decls
      : on_global_decls univs retro decls -> NoDup (List.map fst decls).
    Proof using Type.
      induction 1; cbn in *; constructor => //.
      let H := match goal with H : on_global_decls_data _ _ _ _ _ |- _ => H end in
      move: H.
      case.
      rewrite fresh_global_iff_not_In; auto.
    Qed.

    Definition on_global_univs (c : ContextSet.t) :=
      let levels := global_levels c in
      let cstrs := ContextSet.constraints c in
      UnivConstraintSet.For_all (declared_univ_cstr_levels levels) cstrs /\
      LS.For_all (negb ∘ Level.is_var) levels /\
      consistent cstrs.

    Definition on_global_env (g : global_env) : Type :=
      on_global_univs g.(universes) × on_global_decls g.(universes) g.(retroknowledge) g.(declarations).

    Definition on_global_env_ext (Σ : global_env_ext) :=
      on_global_env Σ.1 × on_udecl Σ.(universes) Σ.2.

    Lemma on_global_env_ext_empty_ext g :
      on_global_env g -> on_global_env_ext (empty_ext g).
    Proof.
      intro H; split => //.
      unfold empty_ext, snd. repeat split.
      - unfold levels_of_udecl. intros x e. lsets.
      - unfold constraints_of_udecl. intros x e. ucsets.
      - unfold satisfiable_udecl, univs_ext_constraints, constraints_of_udecl, fst_ctx, fst => //.
        destruct H as ((cstrs & _ & consistent) & decls).
        destruct consistent; eexists.
        intros v e. specialize (H v e); tea.
      - unfold valid_on_mono_udecl, constraints_of_udecl, consistent_extension_on.
        intros v sat; exists v; split.
        + intros x e. ucsets.
        + intros x e => //.
    Qed.

  End GlobalMaps.

  Arguments cstr_args_length {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments cstr_eq {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cargs {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cindices {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_positive {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_variance {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.

  Arguments ind_arity_eq {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments ind_cunivs {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onArity {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onConstructors {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onProjections {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments ind_sorts {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments ind_relevance_compat {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onIndices {_ Pcmp P Σ mind mdecl i idecl}.

  Arguments onInductives {_ Pcmp P Σ mind mdecl}.
  Arguments onParams {_ Pcmp P Σ mind mdecl}.
  Arguments onNpars {_ Pcmp P Σ mind mdecl}.
  Arguments onVariance {_ Pcmp P Σ mind mdecl}.


  Local Ltac destr_prod :=
    repeat match goal with H : _ × _ |- _ => destruct H end.
  Lemma type_local_ctx_impl_gen Σ Γ Δ u args P :
    { P' & type_local_ctx P' Σ Γ Δ u } ->
    (forall Γ j,
        All (fun P' => P' Σ Γ j) args ->
        P Σ Γ j) ->
    All (fun P' => type_local_ctx P' Σ Γ Δ u) args ->
    type_local_ctx P Σ Γ Δ u.
  Proof.
    intros Hexists HP HPQ. revert HP Hexists; induction Δ in Γ, HPQ |- *; simpl; auto.
    { intros ? [? ?]; auto. }
    { intros HP Hexists; cbn in *.
      specialize (fun H1 Γ P' H2 H => IHΔ Γ H H1 (P'; H2)).
      forward IHΔ => //=; [].
      destruct Hexists as [? Hexists].
      all: destruct a as [na [b|] ty].
      all: repeat match goal with H : _ × _ |- _ => destruct H end.
      all: repeat split; eauto.
      all: simpl in *.
      all: first [ eapply IHΔ; clear IHΔ | apply HP; clear HP ]; tea.
      all: eapply All_impl; tea => //=; intros.
      all: repeat match goal with H : _ × _ |- _ => destruct H end => //=. }
  Qed.

  Lemma type_local_ctx_impl (P Q : global_env_ext -> context -> judgment -> Type) Σ Σ' Γ Δ u :
    type_local_ctx P Σ Γ Δ u ->
    (forall u, wf_sort Σ u -> wf_sort Σ' u) ->
    (forall Γ j, P Σ Γ j -> Q Σ' Γ j) ->
    type_local_ctx Q Σ' Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ |- *; simpl; auto.
    destruct a as [na [b|] ty].
    all: intros (? & ?); now split.
  Qed.

  Lemma sorts_local_ctx_impl_gen Σ Γ Δ u args P :
    { P' & sorts_local_ctx P' Σ Γ Δ u } ->
    (forall Γ j,
        All (fun P' => P' Σ Γ j) args ->
        P Σ Γ j) ->
    All (fun P' => sorts_local_ctx P' Σ Γ Δ u) args ->
    sorts_local_ctx P Σ Γ Δ u.
  Proof.
    intros Hexists HP HPQ. revert HP Hexists; induction Δ in Γ, HPQ, u |- *; simpl; auto.
    { intros ? [? ?]; auto. }
    { intros HP Hexists; cbn in *.
      specialize (fun H1 Γ u P' H2 H => IHΔ Γ u H H1 (P'; H2)).
      forward IHΔ => //=; []; cbn in *.
      destruct Hexists as [? Hexists].
      destruct a as [na [b|] ty]; [ | destruct u ].
      all: repeat match goal with H : _ × _ |- _ => destruct H end.
      all: repeat split; eauto.
      all: simpl in *.
      all: first [ eapply IHΔ; clear IHΔ | apply HP; clear HP ]; tea.
      all: eapply All_impl; tea => //=; intros.
      all: repeat match goal with H : _ × _ |- _ => destruct H end => //=. }
  Qed.

  Lemma sorts_local_ctx_impl (P Q : global_env_ext -> context -> judgment -> Type) Σ Σ' Γ Δ u :
    sorts_local_ctx P Σ Γ Δ u ->
    (forall Γ j, P Σ Γ j -> Q Σ' Γ j) ->
    sorts_local_ctx Q Σ' Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ, u |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    2: destruct u => //.
    all: intros (? & ?); now split.
  Qed.

  Lemma cstr_respects_variance_impl_gen Σ mdecl v cs args Pcmp :
    { Pcmp' & @cstr_respects_variance Pcmp' Σ mdecl v cs } ->
    (match variance_universes (ind_universes mdecl) v with
     | Some (univs, u, u')
       => forall Γ t T pb,
         All (fun Pcmp' => Pcmp' (Σ, univs) Γ pb t T) args ->
         Pcmp (Σ, univs) Γ pb t T
     | None => True
     end) ->
    All (fun Pcmp' => @cstr_respects_variance Pcmp' Σ mdecl v cs) args ->
    @cstr_respects_variance Pcmp Σ mdecl v cs.
  Proof.
    rewrite /cstr_respects_variance/cumul_ctx_rel/cumul_pb_decls.
    destruct variance_universes; destr_prod; try now case.
    move => Hexists HPQ HP.
    apply All_prod_inv in HP.
    destruct HP as [HP1 HP2].
    apply All_All2_fold_swap_sum in HP1.
    apply All_All2_swap_sum in HP2.
    destruct args.
    { specialize (fun Γ t T pb => HPQ Γ t T pb ltac:(constructor)).
      destruct Hexists as [? [? ?]];
        split; first [ eapply All2_fold_impl | eapply All2_impl ]; tea; intros *; cbn; eauto.
      eapply All_decls_alpha_pb_impl; eauto. }
    { destruct HP1 as [HP1|HP1], HP2 as [HP2|HP2]; subst; try congruence.
      split; first [ eapply All2_fold_impl | eapply All2_impl ]; tea; intros *; cbn; eauto.
      inversion 1; subst.
      let H := match goal with X : All_decls_alpha_pb _ _ _ _ |- _ => X end in
      inversion H; clear H; subst; constructor => //.
      all: apply HPQ; constructor; tea.
      all: eapply All_impl; tea; intros *; cbn.
      all: inversion 1; subst => //=. }
  Qed.

  Lemma cstr_respects_variance_impl Σ Σ' mdecl v cs Pcmp Pcmp' :
    (match variance_universes (ind_universes mdecl) v with
     | Some (univs, u, u')
       => forall Γ t T pb,
         Pcmp (Σ, univs) Γ pb t T ->
         Pcmp' (Σ', univs) Γ pb t T
     | None => True
     end) ->
    @cstr_respects_variance Pcmp Σ mdecl v cs ->
    @cstr_respects_variance Pcmp' Σ' mdecl v cs.
  Proof.
    rewrite /cstr_respects_variance/cumul_ctx_rel/cumul_pb_decls.
    destruct variance_universes; destr_prod; try now case.
    move => HPQ [HP1 HP2].
    split; first [ eapply All2_fold_impl | eapply All2_impl ]; tea; intros *; cbn; eauto.
    eapply All_decls_alpha_pb_impl; eauto.
  Qed.

  Lemma on_constructor_impl_config_gen Σ mdecl i idecl ind_indices cdecl cunivs args cf Pcmp P :
    { '(cf', Pcmp', P') & config.impl cf' cf × @on_constructor cf' Pcmp' P' Σ mdecl i idecl ind_indices cdecl cunivs } ->
    (forall Γ j,
        All (fun '(cf', Pcmp', P') => P' Σ Γ j) args ->
        P Σ Γ j) ->
    (forall u Γ t T pb,
        All (fun '(cf', Pcmp', P') => Pcmp' (Σ.1, u) Γ pb t T) args ->
        Pcmp (Σ.1, u) Γ pb t T) ->
    All (fun '(cf', Pcmp', P') => @on_constructor cf' Pcmp' P' Σ mdecl i idecl ind_indices cdecl cunivs) args
    -> @on_constructor cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs.
  Proof.
    intros Hexists H1 H2 Hargs.
    destruct Hexists as [[[??]?] [? Hexists]].
    destruct Hexists; split; tea.
    all: unfold on_type, config.impl in *; eauto.
    { apply H1; clear H1.
      eapply All_impl; tea; intros *; destr_prod; destruct 1; tea. }
    { eapply sorts_local_ctx_impl_gen; tea.
      { eexists; tea. }
      { intros; eapply H1, All_eta3; cbn; apply All_map_inv with (P:=fun P => P _ _ _) (f:=snd); tea. }
      { eapply All_map, All_impl; tea; intros *; destr_prod; destruct 1; cbn; tea. } }
    { eapply ctx_inst_impl_gen; tea.
      { eexists; tea. }
      { intros; eapply H1, All_eta3; cbn. apply All_map_inv with (P:=fun P => P _ t T1) (f:=fun P Γ t T => snd P Σ Γ (TermTyp t T)); tea. }
      { eapply All_map, All_impl; tea; intros *; destr_prod; destruct 1; cbn; tea. } }
    { move => ? H'.
      match goal with H : _ |- _ => specialize (H _ H'); revert H end => H''.
      eapply cstr_respects_variance_impl_gen; revgoals.
      { eapply All_map, All_impl; tea; intros *; destr_prod; destruct 1; cbn.
        instantiate (1:=ltac:(intros [[??]?])); cbn.
        match goal with H : _ |- _ => refine (H _ H') end. }
      { repeat match goal with |- context[match ?x with _ => _ end] => destruct x eqn:?; subst end => //.
        intros; eapply H2, All_eta3; cbn; apply All_map_inv with (P:=fun P => P _ _ _ _ _) (f:=fun x => x.1.2).
        erewrite map_ext; tea; intros; destr_prod; cbn => //. }
      { eexists; tea. } }
    { unfold config.impl in *.
      do 2 destruct lets_in_constructor_types; cbn in *; rewrite -> ?andb_false_r in * => //. }
  Qed.

  Lemma on_constructors_impl_config_gen Σ mdecl i idecl ind_indices cdecl cunivs args cf Pcmp P :
    { '(cf', Pcmp', P') & config.impl cf' cf × @on_constructors cf' Pcmp' P' Σ mdecl i idecl ind_indices cdecl cunivs } ->
    All (fun '(cf', Pcmp', P') => config.impl cf' cf) args ->
    (forall Γ j,
        All (fun '(cf', Pcmp', P') => P' Σ Γ j) args ->
        P Σ Γ j) ->
    (forall u Γ t T pb,
        All (fun '(cf', Pcmp', P') => Pcmp' (Σ.1, u) Γ pb t T) args ->
        Pcmp (Σ.1, u) Γ pb t T) ->
    All (fun '(cf', Pcmp', P') => @on_constructors cf' Pcmp' P' Σ mdecl i idecl ind_indices cdecl cunivs) args
    -> @on_constructors cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs.
  Proof.
    intros Hexists Hargsconfig H1 H2 Hargs.
    destruct Hexists as [[[??]?] [? Hexists]].
    unfold on_constructors in *.
    destruct args.
    { eapply All2_impl; tea; intros.
      eapply on_constructor_impl_config_gen; tea; try eexists (_, _, _); eauto. }
    apply All_eta3, All_All2_swap in Hargs; [ | constructor; congruence ].
    eapply All2_impl; try exact Hargs; cbv beta => ?? Hargs'.
    eapply on_constructor_impl_config_gen; tea.
    all: repeat first [ progress destr_prod
                      | match goal with
                        | [ H : All _ (_ :: _) |- _ ] => inversion H; clear H; subst
                        end ].
    { eexists; instantiate (1:=ltac:(repeat eapply pair)); cbn in *.
      eauto. }
    constructor; eauto.
    now eapply All_impl; [ multimatch goal with H : _ |- _ => exact H end | ]; intros; destr_prod; eauto.
  Qed.

  Lemma ind_respects_variance_impl Σ Σ' mdecl v cs Pcmp Pcmp' :
    match variance_universes (ind_universes mdecl) v with
     | Some (univs, u, u')
       => forall Γ t T pb,
         Pcmp (Σ, univs) Γ pb t T ->
         Pcmp' (Σ', univs) Γ pb t T
     | None => True
     end ->
    @ind_respects_variance Pcmp Σ mdecl v cs ->
    @ind_respects_variance Pcmp' Σ' mdecl v cs.
  Proof.
    rewrite /ind_respects_variance/cumul_ctx_rel/cumul_pb_decls.
    destruct variance_universes; destr_prod; try now case.
    move => HPQ HP.
    eapply All2_fold_impl; tea; intros *; cbn; eauto.
    inversion 1; subst; subst; constructor => //; auto.
  Qed.

  Lemma on_variance_impl Σ univs variances cf' cf :
    config.impl cf' cf ->
    @on_variance cf' Σ univs variances ->
    @on_variance cf Σ univs variances.
  Proof.
    rewrite /on_variance; case: univs; case: variances => //; intros.
    repeat first [ match goal with
                   | [ H : sigT _ |- _ ] => destruct H
                   | [ H : and4 _ _ _ _ |- _ ] => destruct H
                   | [ H : ssrbool.and4 _ _ _ _ |- _ ] => destruct H
                   | [ H : prod _ _ |- _ ] => destruct H
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ |- and _ _ ] => split
                   | [ |- sigT _ ]
                     => repeat match goal with |- sigT _ => eexists end;
                        split; tea
                   end
                 | progress unfold config.impl, consistent_instance_ext, consistent_instance, valid_constraints in *
                 | progress cbn in * => //=
                 | match goal with
                   | [ |- context[match ?x with _ => _ end] ] => destruct x eqn:?; subst
                   | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?; subst
                   end ].
  Qed.

  Lemma check_constructors_smaller_impl Σ cdecls ind_sort cf' cf :
    config.impl cf' cf ->
    @check_constructors_smaller cf' Σ cdecls ind_sort ->
    @check_constructors_smaller cf Σ cdecls ind_sort.
  Proof.
    intro Xcf.
    unfold check_constructors_smaller.
    intro H; apply Forall_impl with (1 := H).
    intros l Hl; apply Forall_impl with (1 := Hl).
    intro u. now apply leq_sort_config_impl.
  Qed.

  Lemma on_global_decl_impl_full {cf1 cf2 : checker_flags} Pcmp1 Pcmp2 P1 P2 Σ Σ' kn d :
    config.impl cf1 cf2 ->
    (forall Γ j, P1 Σ Γ j -> P2 Σ' Γ j) ->
    (forall u Γ pb t t', Pcmp1 (Σ.1, u) Γ pb t t' -> Pcmp2 (Σ'.1, u) Γ pb t t') ->
    (forall u, wf_sort Σ u -> wf_sort Σ' u) ->
    (forall l s, @check_constructors_smaller cf1 (global_ext_constraints Σ) l s ->
      @check_constructors_smaller cf2 (global_ext_constraints Σ') l s) ->
    (forall u l, @on_variance cf1 Σ.1 u l -> @on_variance cf2 Σ'.1 u l) ->
    @on_global_decl cf1 Pcmp1 P1 Σ kn d -> @on_global_decl cf2 Pcmp2 P2 Σ' kn d.
  Proof.
    intros Xcf XP Xcmp Xu Xc Xv.
    destruct d; simpl.
    - apply XP => //.
    - intros [onI onP onNP onV].
      constructor; auto.
      2: { eapply All_local_env_impl with (1 := onP). intros; apply XP => //. }

      eapply Alli_impl; tea. intros.
      refine {| ind_arity_eq := X.(ind_arity_eq);
                ind_cunivs := X.(ind_cunivs) |}.
      + eapply XP => //. now apply onArity in X.
      + pose proof X.(onConstructors) as X1.
        apply All2_impl with (1 := X1).
        intros ? ? [? ? ? ?]; unshelve econstructor; eauto.
        * apply XP; eauto.
        * eapply sorts_local_ctx_impl with (1 := on_cargs0).
          intros; apply XP => //.
        * eapply ctx_inst_impl with (1 := on_cindices0).
          intros; apply XP => //.
        * intros v e.
          eapply cstr_respects_variance_impl.
          2: eauto.
          destruct variance_universes as [[[]]|] => //=.
          intros; now eapply Xcmp.
        * move: on_lets_in_type0.
          move: Xcf.
          rewrite /config.impl.
          do 3 destruct lets_in_constructor_types => //=.
          all: rewrite ?andb_false_r //=.
      + exact (onProjections X).
      + pose proof (ind_sorts X) as X1. unfold check_ind_sorts in *.
        destruct Sort.to_family; auto.
        destruct X1 as [constr_smaller type_local_ctx].
        split.
        * apply Xc, constr_smaller.
        * unfold config.impl in Xcf.
          revert type_local_ctx.
          do 2 destruct indices_matter => //=.
          2: now rewrite ?andb_false_r //= in Xcf.
          intro. eapply type_local_ctx_impl; eauto.
      + apply (ind_relevance_compat X).
      + generalize (X.(onIndices)). destruct ind_variance => //.
        apply ind_respects_variance_impl.
        destruct variance_universes as [[[]]|] => //=.
        intros; now eapply Xcmp.
  Qed.

  Lemma on_global_decl_impl_only_config {cf cf1 cf2 : checker_flags} Pcmp Pcmp' P Q Σ kn d :
    config.impl cf1 cf2 ->
    (forall Γ j,
      @on_global_env cf Pcmp P Σ.1 ->
      P Σ Γ j -> Q Σ Γ j) ->
    (forall u Γ pb t t',
      @on_global_env cf Pcmp P Σ.1 ->
      Pcmp (Σ.1, u) Γ pb t t' -> Pcmp' (Σ.1, u) Γ pb t t') ->
    @on_global_env cf Pcmp P Σ.1 ->
    @on_global_decl cf1 Pcmp P Σ kn d -> @on_global_decl cf2 Pcmp' Q Σ kn d.
  Proof.
    destruct Σ as [Σ u]. cbn.
    intros ??? H.
    apply on_global_decl_impl_full => //.
    - intros ??. now apply X.
    - intros ?????. now apply X0.
    - intros ??; now apply check_constructors_smaller_impl.
    - intros ??; now apply on_variance_impl.
  Qed.

  Lemma on_global_decl_impl_simple {cf : checker_flags} Pcmp P Q Σ kn d :
    (forall Γ j, on_global_env Pcmp P Σ.1 -> P Σ Γ j -> Q Σ Γ j) ->
    on_global_env Pcmp P Σ.1 ->
    on_global_decl Pcmp P Σ kn d -> on_global_decl Pcmp Q Σ kn d.
  Proof.
    intro X.
    apply on_global_decl_impl_only_config; tas.
    1: reflexivity.
    easy.
  Qed.


  Lemma on_global_env_impl_config {cf1 cf2 : checker_flags} Pcmp Pcmp' P Q :
    config.impl cf1 cf2 ->
    (forall Σ Γ j,
        @on_global_env cf1 Pcmp P Σ.1 ->
        @on_global_env cf2 Pcmp' Q Σ.1 ->
        P Σ Γ j -> Q Σ Γ j) ->
    (forall Σ Γ t T pb,
        @on_global_env cf1 Pcmp P Σ.1 ->
        @on_global_env cf2 Pcmp' Q Σ.1 ->
        Pcmp Σ Γ pb t T -> Pcmp' Σ Γ pb t T) ->
    forall Σ, @on_global_env cf1 Pcmp P Σ -> @on_global_env cf2 Pcmp' Q Σ.
  Proof.
    intros Xcf X Xcmp Σ [cu IH]. split; auto.
    revert cu IH; generalize (universes Σ) as univs, (retroknowledge Σ) as retro, (declarations Σ). clear Σ.
    induction g; intros; auto. constructor; auto.
    depelim IH. specialize (IHg cu IH). constructor; auto.
    destruct o. constructor; auto.
    eapply @on_global_decl_impl_only_config with (cf := cf1) (1 := Xcf) (5 := on_global_decl_d0).
    { intros. eapply X; [tea| split; tea |tea]. }
    { cbn. intros. eapply Xcmp. 1,3: eassumption. split; cbn. all: eassumption. }
    split; eauto.
  Qed.

  Lemma on_global_env_impl {cf : checker_flags} Pcmp P Q :
    (forall Σ Γ j,
        on_global_env Pcmp P Σ.1 ->
        on_global_env Pcmp Q Σ.1 ->
        P Σ Γ j -> Q Σ Γ j) ->
    forall Σ, on_global_env Pcmp P Σ -> on_global_env Pcmp Q Σ.
  Proof. intros; eapply on_global_env_impl_config; eauto; reflexivity. Qed.

  Lemma lookup_on_global_env `{checker_flags} {Pcmp P} {Σ : global_env} {c decl} :
    on_global_env Pcmp P Σ ->
    lookup_env Σ c = Some decl ->
    ∑ Σ' : global_env_ext, on_global_env Pcmp P Σ' × strictly_extends_decls Σ' Σ × on_global_decl Pcmp P Σ' c decl.
  Proof.
    unfold on_global_env.
    destruct Σ as [univs Σ retro]; cbn. intros [cu ond].
    induction ond; cbn in * => //.
    destruct o. rename udecl0 into udecl.
    case: eqb_specT => [-> [= <-]| ne].
    - exists ({| universes := univs; declarations := Σ; retroknowledge := retro |}, udecl); cbn.
      split; try constructor; tas.
      split => //=. now exists [(kn, d)].
    - intros hl.
      specialize (IHond hl) as [[Σ' udecl'] [ong [[equ ext extretro] ond']]].
      exists (Σ', udecl'). cbn in equ |- *. subst univs. split; cbn; auto; try apply ong.
      split; cbn; auto. split; cbn; auto.
      cbn in ext. destruct ext as [Σ'' ->]. cbn in *.
      now exists ((kn, d) :: Σ'').
  Qed.


End GlobalMaps.

Module Type GlobalMapsSig (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
  Include GlobalMaps T E TU ET C L.
End GlobalMapsSig.

Module Type ConversionParSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).

  Import T E TU ET.

  Parameter Inline cumul_gen : forall {cf : checker_flags}, global_env_ext -> context -> conv_pb -> term -> term -> Type.

End ConversionParSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
  (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET).

  Import T E TU ET CT CS.

  Parameter Inline typing : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type.

  Notation " Σ ;;; Γ |- t : T " :=
    (typing Σ Γ t T) (at level 50, Γ, t, T at next level) : type_scope.

  Notation wf_local Σ Γ := (All_local_env (lift_typing Σ) Γ).

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
  (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
  (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
  (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).

  Import T E L TU ET CT GM CS Ty.

  Definition isTypeRel `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (rel : relevance) :=
    on_type_rel (lift_typing typing) Σ Γ t rel.

  Definition isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
    on_type (lift_typing typing) Σ Γ t.

  Lemma isTypeRel_isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (r : relevance) : isTypeRel Σ Γ t r -> isType Σ Γ t.
  Proof. apply lift_sorting_forget_rel. Defined.
  #[export] Hint Resolve isTypeRel_isType : pcuic.

  Coercion isTypeRel_isType : isTypeRel >-> isType.

  (** This predicate enforces that there exists typing derivations for every typable term in env. *)

  Definition Forall_decls_typing `{checker_flags}
            (P : global_env_ext -> context -> term -> term -> Type)
    := on_global_env cumul_gen (lift_typing P).

  (** *** Typing of local environments *)

  Definition type_local_decl `{checker_flags} Σ Γ d :=
    match d.(decl_body) with
    | None => isType Σ Γ d.(decl_type)
    | Some body => Σ ;;; Γ |- body : d.(decl_type)
    end.

  (** ** Induction principle for typing up-to a global environment *)

  Lemma refine_type `{checker_flags} Σ Γ t T U : Σ ;;; Γ |- t : T -> T = U -> Σ ;;; Γ |- t : U.
  Proof. now intros Ht ->. Qed.

  Definition wf_local_rel `{checker_flags} Σ := All_local_rel (lift_typing1 (typing Σ)).

  (** Functoriality of global environment typing derivations + folding of the well-formed
    environment assumption. *)
  Lemma on_wf_global_env_impl_config {cf1 cf2 cf3 : checker_flags} {Σ : global_env} {wfΣ : @on_global_env cf1 (@cumul_gen cf1) (lift_typing (@typing cf1)) Σ} P Q :
    config.impl cf2 cf3 ->
    (forall Σ Γ pb t T, @cumul_gen cf2 Σ Γ pb t T -> @cumul_gen cf3 Σ Γ pb t T) ->
    (forall Σ Γ j, @on_global_env cf1 (@cumul_gen cf1) (lift_typing (@typing cf1)) Σ.1 ->
        @on_global_env cf2 (@cumul_gen cf2) P Σ.1 ->
        @on_global_env cf3 (@cumul_gen cf3) Q Σ.1 ->
        P Σ Γ j -> Q Σ Γ j) ->
    @on_global_env cf2 (@cumul_gen cf2) P Σ -> @on_global_env cf3 (@cumul_gen cf3) Q Σ.
  Proof.
    intros Xcf Xcmp X [cu IH]. destruct wfΣ as [_ wfΣ]. split; auto.
    revert cu IH wfΣ; generalize (universes Σ) as univs, (retroknowledge Σ) as retro, (declarations Σ). clear Σ.
    induction g; intros; auto. constructor; auto.
    depelim IH. depelim wfΣ.
    specialize (IHg cu IH wfΣ).
    constructor; auto.
    destruct o. constructor; auto.
    eapply @on_global_decl_impl_only_config with (cf := cf2) (5 := on_global_decl_d0) => //.
    { intros. eapply X; cycle -1; tea; split; tea. }
    { intros. now eapply Xcmp. }
  Qed.

  Lemma on_wf_global_env_impl `{checker_flags} {Σ : global_env} {wfΣ : on_global_env cumul_gen (lift_typing typing) Σ} P Q :
    (forall Σ Γ j, on_global_env cumul_gen (lift_typing typing) Σ.1 ->
        on_global_env cumul_gen P Σ.1 ->
        on_global_env cumul_gen Q Σ.1 ->
        P Σ Γ j -> Q Σ Γ j) ->
    on_global_env cumul_gen P Σ -> on_global_env cumul_gen Q Σ.
  Proof.
    unshelve eapply on_wf_global_env_impl_config; eauto; reflexivity.
  Qed.

  Section Properties.
    Context {cf : checker_flags}.
    Context {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}.
    Context {P: global_env_ext -> context -> judgment -> Type}.

  Let wf := on_global_env Pcmp P.

  Lemma declared_constant_from_gen {Σ kn cdecl} :
    declared_constant_gen (lookup_env Σ) kn cdecl ->
    declared_constant Σ kn cdecl.
  Proof using Type.
    intro H. eapply lookup_global_Some_if_In.
    red in H. unfold lookup_env in H.
    apply lookup_constant_declared_gen => //.
    unfold lookup_constant_gen. now rewrite H.
  Qed.

  Lemma declared_constant_to_gen {Σ kn cdecl}
  {wfΣ : wf Σ} :
  declared_constant Σ kn cdecl ->
  declared_constant_gen (lookup_env Σ) kn cdecl.
  Proof using P Pcmp cf.
    intro H; eapply lookup_global_Some_iff_In_NoDup in H.
    - apply lookup_constant_declared_gen => //.
      unfold lookup_constant_gen, lookup_env.
      destruct (lookup_global _ _) => //.
      destruct g => //. now inversion H.
    - destruct wfΣ; now eapply NoDup_on_global_decls.
  Qed.

  Lemma declared_minductive_to_gen {Σ ind mdecl}
   {wfΣ : wf Σ} :
    declared_minductive Σ ind mdecl ->
    declared_minductive_gen (lookup_env Σ) ind mdecl.
  Proof using P Pcmp cf.
    intro H; eapply lookup_global_Some_iff_In_NoDup in H.
    - apply lookup_minductive_declared_gen => //.
      unfold lookup_minductive_gen, lookup_env.
      destruct (lookup_global _ _) => //.
      destruct g => //. now inversion H.
    - destruct wfΣ; now eapply NoDup_on_global_decls.
  Qed.

  Lemma declared_minductive_from_gen {Σ ind mdecl} :
    declared_minductive_gen (lookup_env Σ) ind mdecl ->
    declared_minductive Σ ind mdecl.
  Proof using Type.
    intro H; eapply lookup_global_Some_if_In.
    apply lookup_minductive_declared_gen => //.
    apply declared_minductive_lookup_gen in H => //.
  Qed.

  Lemma declared_inductive_to_gen {Σ ind mdecl idecl}
  {wfΣ : wf Σ} :
    declared_inductive Σ ind mdecl idecl ->
    declared_inductive_gen (lookup_env Σ) ind mdecl idecl.
  Proof using P Pcmp cf.
    intros []; split => //.
    eapply declared_minductive_to_gen; eauto.
    Unshelve. all:eauto.
  Qed.

  Lemma declared_inductive_from_gen {Σ ind mdecl idecl}:
    declared_inductive_gen (lookup_env Σ) ind mdecl idecl ->
    declared_inductive Σ ind mdecl idecl.
  Proof using Type.
    intros []; split => //.
    eapply declared_minductive_from_gen; eauto.
  Qed.

  Lemma declared_constructor_to_gen {Σ id mdecl idecl cdecl}
    {wfΣ : wf Σ} :
    declared_constructor Σ id mdecl idecl cdecl ->
    declared_constructor_gen (lookup_env Σ) id mdecl idecl cdecl.
  Proof using P Pcmp cf.
    intros []; split => //.
    eapply declared_inductive_to_gen; eauto.
    Unshelve. all:eauto.
  Qed.

  Lemma declared_constructor_from_gen {Σ id mdecl idecl cdecl} :
    declared_constructor_gen (lookup_env Σ) id mdecl idecl cdecl ->
    declared_constructor Σ id mdecl idecl cdecl.
  Proof using Type.
    intros []; split => //.
    eapply declared_inductive_from_gen; eauto.
  Qed.

  Lemma declared_projection_to_gen {Σ p mdecl idecl cdecl pdecl}
    {wfΣ : wf Σ} :
    declared_projection Σ p mdecl idecl cdecl pdecl ->
    declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl.
  Proof using P Pcmp cf.
    intros [? []]. split => //.
    eapply declared_constructor_to_gen; eauto.
    Unshelve. all:eauto.
  Qed.

  Lemma declared_projection_from_gen {Σ p mdecl idecl cdecl pdecl} :
    declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl ->
    declared_projection Σ p mdecl idecl cdecl pdecl.
  Proof using Type.
    intros [? []]. split => //.
    eapply declared_constructor_from_gen; eauto.
  Qed.
  End Properties.
End DeclarationTyping.

Module Type DeclarationTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
       (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
       (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
       (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).
  Include DeclarationTyping T E TU ET CT CS Ty L GM.
End DeclarationTypingSig.
