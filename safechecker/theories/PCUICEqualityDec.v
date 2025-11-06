(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ProofIrrelevance ssreflect ssrbool btauto.Algebra.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICTactics
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICEquality PCUICWfUniverses
     PCUICInduction.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

(* TODO move*)

Lemma consistent_instance_wf_sort `{checker_flags} Σ uctx u :
  consistent_instance_ext Σ uctx u ->
  Forall (wf_universe Σ) u.
Proof.
  move => /consistent_instance_ext_wf /wf_instanceP.
  rewrite -wf_universeb_instance_forall.
  move => /forallb_Forall ?.
  eapply Forall_impl ; tea.
  move => ? /wf_universeP //.
Qed.

Lemma ctx_inst_on_universes Σ Γ ts Ts :
  ctx_inst (fun _ t _ => wf_universes Σ t) Γ ts Ts ->
  Forall (wf_universes Σ) ts.
Proof.
  induction 1.
  - constructor.
  - now constructor.
  - assumption.
Qed.

(** ** Boolean of equality **  *)

Definition compare_universe_variance (cmpu : conv_pb -> Universe.t -> Universe.t -> bool) pb v u u' :=
  match v with
  | Variance.Irrelevant => true
  | Variance.Covariant => cmpu pb u u'
  | Variance.Invariant => cmpu Conv u u'
  end.

Definition compare_universe_instance equ (u u' : Instance.t) :=
  forallb2 equ u u'.

Definition compare_universe_instance_variance cmpu pb v u u' :=
  forallb3 (compare_universe_variance cmpu pb) v u u'.

Definition compare_global_instance lookup cmpu pb gr napp u u' :=
  match global_variance_gen lookup gr napp with
  | AllEqual => compare_universe_instance (cmpu Conv) u u'
  | Variance v =>
    compare_universe_instance_variance cmpu pb v u u' || compare_universe_instance (cmpu Conv) u u'
  | AllIrrelevant => #|u| == #|u'|
  end.

Definition eqb_binder_annots (x y : list aname) : bool :=
  forallb2 eqb_binder_annot x y.

Definition eqb_decl_upto_names (d d' : context_decl) : bool :=
  match d, d' with
  | {| decl_name := na; decl_body := None; decl_type := T |},
    {| decl_name := na'; decl_body := None; decl_type := T' |} =>
    eqb_binder_annot na na' && eqb T T'
  | {| decl_name := na; decl_body := Some b; decl_type := T |},
    {| decl_name := na'; decl_body := Some b'; decl_type := T' |} =>
    eqb_binder_annot na na' && eqb b b' && eqb T T'
  | _, _ => false
  end.

Notation eqb_context_upto_names := (forallb2 eqb_decl_upto_names).

Fixpoint eqb_term_upto_univ_napp
  (cmpu : conv_pb -> Universe.t -> Universe.t -> bool)
  (cmps : conv_pb -> sort -> sort -> bool)
  (gen_compare_global_instance : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
  pb napp (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    cmps pb u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance pb (S napp) u u' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    compare_universe_instance (cmpu Conv) u u'

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    gen_compare_global_instance pb (IndRef i) napp u u'

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    gen_compare_global_instance pb (ConstructRef i k) napp u u'

  | tLambda na A t, tLambda na' A' t' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 A A' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 A A' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance pb 0 B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 B B' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 b b' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_predicate_gen
      (compare_universe_instance (cmpu Conv))
      eqb_decl_upto_names
      (eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0) p p' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 c c' &&
    forallb2 (fun x y =>
      forallb2
        eqb_decl_upto_names x.(bcontext) y.(bcontext) &&
      eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 (bbody x) (bbody y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0 x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix'

  | tPrim p, tPrim p' => eqb_prim_val (equ := fun l l' => compare_universe_instance (cmpu Conv) [l] [l'])
    (req := eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance Conv 0) p p'

  | _, _ => false
  end.

Notation eqb_term_upto_univ cmpu cmps gen_compare_global_instance pb :=
  (eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance pb 0).

Definition conv_pb_relb_gen {T} (eq leq : T -> T -> bool) pb :=
    match pb with
    | Conv => eq
    | Cumul => leq
    end.

Lemma equiv_reflect P p :
  ssrbool.reflect P p <~>
  (P <-> p).
Proof.
  split.
  - destruct 1; split; intro; eauto.
    now exfalso.
  - destruct p; intros []; constructor; auto.
Qed.

Lemma reflect_cmp_universe_instance (p : Universe.t -> bool) cmpu cmp_universe ui ui' :
  (forall u u', p u -> p u' -> reflect (cmp_universe u u') (cmpu u u')) ->
  forallb p ui ->
  forallb p ui' ->
  reflect (cmp_universe_instance cmp_universe ui ui') (compare_universe_instance cmpu ui ui').
Proof.
  intros he hui hui'.
  apply equiv_reflect; split.
  all: unfold cmp_universe_instance, compare_universe_instance in *.
  all: solve_all.
  - now apply/he.
  - now apply/he.
Qed.

Lemma reflect_cmp_universe_instance_variance (p : Universe.t -> bool) cmpu cmp_universe pb v ui ui' :
  (forall u u', p u -> p u' -> reflect (cmp_universe Conv u u') (cmpu Conv u u')) ->
  (forall u u', p u -> p u' -> reflect (cmp_universe pb u u') (cmpu pb u u')) ->
  forallb p ui ->
  forallb p ui' ->
  reflect (cmp_universe_instance_variance cmp_universe pb v ui ui') (compare_universe_instance_variance cmpu pb v ui ui').
Proof.
  intros he hle hui hui'.
  apply equiv_reflect; split.
  all: unfold cmp_universe_instance_variance, compare_universe_instance_variance in *.
  - induction 1 in hui, hui' |- *; cbnr.
    cbn in hui, hui'; rtoProp.
    split; auto.
    destruct x; cbnr.
    + now apply/hle.
    + now apply/he.
  - intro X. apply forallb3_Forall3 in X.
    induction X in hui, hui' |- *; cbnr; try solve [ constructor ].
    cbn in hui, hui'; rtoProp.
    constructor; auto.
    destruct x; cbnr.
    + now apply/hle.
    + now apply/he.
Qed.

Lemma reflect_cmp_global_instance' lookup (p : Universe.t -> bool) cmpu cmp_universe pb gr napp ui ui' :
  (forall u u', p u -> p u' -> reflect (cmp_universe Conv u u') (cmpu Conv u u')) ->
  (forall u u', p u -> p u' -> reflect (cmp_universe pb u u') (cmpu pb u u')) ->
  forallb p ui ->
  forallb p ui' ->
  reflect (cmp_global_instance_gen lookup cmp_universe pb gr napp ui ui')
    (compare_global_instance lookup cmpu pb gr napp ui ui').
Proof.
  intros he hle hui hui'.
  rewrite /compare_global_instance /cmp_global_instance_gen /cmp_opt_variance.
  destruct (global_variance_gen _ gr napp) as [| |v].
  - eapply reflect_cmp_universe_instance; tea.
  - apply eqb_specT.
  - apply equiv_reflect; split.
    + intros [X|X]; apply orb_true_iff; [right|left].
      * now apply/reflect_cmp_universe_instance.
      * now apply/reflect_cmp_universe_instance_variance.
    + intros [X|X]%orb_true_iff; [right|left].
      * now apply/reflect_cmp_universe_instance_variance.
      * now apply/reflect_cmp_universe_instance.
Qed.

Lemma reflect_cmp_global_instance Σ lookup (p : Universe.t -> bool) cmpu cmp_universe pb gr napp ui ui' :
  (forall u u', p u -> p u' -> reflect (cmp_universe Conv u u') (cmpu Conv u u')) ->
  (forall u u', p u -> p u' -> reflect (cmp_universe pb u u') (cmpu pb u u')) ->
  (forall kn, lookup_env Σ kn = lookup kn) ->
  forallb p ui ->
  forallb p ui' ->
  reflect (cmp_global_instance Σ cmp_universe pb gr napp ui ui')
    (compare_global_instance lookup cmpu pb gr napp ui ui').
Proof.
  intros he hleh hlookup hui hui'.
  pose proof (Hglobal := reflect_cmp_global_instance' lookup p
        cmpu cmp_universe pb gr napp ui ui' he hleh hui hui').
  rewrite /cmp_global_instance_gen /compare_global_instance /cmp_opt_variance.
  rewrite /global_variance_gen /lookup_constructor_gen /lookup_inductive_gen /lookup_minductive_gen.
  destruct gr; auto; now repeat rewrite hlookup.
Qed.

Lemma forallb_true {A : Type} (l : list A) : forallb xpredT l.
Proof.
  now induction l.
Qed.

Lemma compare_global_instance_impl Σ lookup cmpu cmp_universe pb gr napp :
  (forall u u', reflect (cmp_universe Conv u u') (cmpu Conv u u')) ->
  (forall u u', reflect (cmp_universe pb u u') (cmpu pb u u')) ->
  (forall kn, lookup_env Σ kn = lookup kn) ->
  subrelation (compare_global_instance lookup cmpu pb gr napp) (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros hre hrle hlookup x y.
  move/reflect_cmp_global_instance => H. eapply H.
  all: intros; eauto.
  all: apply forallb_true.
Qed.

Lemma Forall2_forallb2:
  forall (A : Type) (p : A -> A -> bool) (l l' : list A),
  Forall2 (fun x y : A => p x y) l l' -> forallb2 p l l'.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma eqb_annot_spec {A} na na' : eqb_binder_annot na na' <-> @eq_binder_annot A A na na'.
Proof.
  unfold eqb_binder_annot, eq_binder_annot.
  now destruct Classes.eq_dec.
Qed.

Lemma eqb_annot_reflect {A} na na' : reflect (@eq_binder_annot A A na na') (eqb_binder_annot na na').
Proof.
  unfold eqb_binder_annot, eq_binder_annot.
  destruct Classes.eq_dec; constructor; auto.
Qed.

Lemma eqb_annot_refl {A} n : @eqb_binder_annot A n n.
Proof.
  apply eqb_annot_spec. reflexivity.
Qed.

Lemma eqb_annots_spec nas nas' : eqb_binder_annots nas nas' <-> Forall2 (on_rel eq binder_relevance) nas nas'.
Proof.
  unfold eqb_binder_annots, eq_binder_annot.
  split; intros.
  - eapply forallb2_Forall2 in H.
    eapply (Forall2_impl H). unfold on_rel. apply eqb_annot_spec.
  - eapply Forall2_forallb2, (Forall2_impl H); apply eqb_annot_spec.
Qed.

Lemma eqb_annots_reflect nas nas' : reflectT (All2 (on_rel eq binder_relevance) nas nas') (eqb_binder_annots nas nas').
Proof.
  unfold eqb_binder_annots, eq_binder_annot.
  destruct forallb2 eqn:H; constructor.
  - eapply Forall2_All2. now apply eqb_annots_spec.
  - intros H'; apply All2_Forall2, eqb_annots_spec in H'.
    red in H'. unfold eqb_binder_annots in H'. congruence.
Qed.

Lemma reflect_eq_decl_upto_names d d' :
  reflectT (eq_decl_upto_names d d') (eqb_decl_upto_names d d').
Proof.
  destruct d as [na [b|] ty], d' as [na' [b'|] ty'] => //=.
  2,3: constructor; intro X; inv X.
  all: eapply equiv_reflectT; intro X; [inv X|]; rtoProp.
  - repeat split; tas. 1: now apply/eqb_annot_reflect. all: apply eqb_refl.
  - apply eqb_eq in H0 as <-, H1 as <-. apply eqb_annot_spec in H.
    now constructor.
  - repeat split; tas. 1: now apply/eqb_annot_reflect. all: apply eqb_refl.
  - apply eqb_eq in H0 as <-. apply eqb_annot_spec in H.
    now constructor.
Qed.

Lemma reflect_eq_context_upto_names Γ Δ :
  reflectT (eq_context_upto_names Γ Δ) (eqb_context_upto_names Γ Δ).
Proof.
  eapply All2P, reflect_eq_decl_upto_names.
Qed.

Definition eqb_univ_reflect : forall u u' : sort, reflectProp (u = u') (eqb u u').
Proof.
  intros u u'.
  destruct (eqb_spec u u'); constructor; auto.
Qed.

Lemma eq_dec_to_bool_refl {A} {ea : Classes.EqDec A} (x : A) :
  eq_dec_to_bool x x.
Proof.
  unfold eq_dec_to_bool.
  now destruct (Classes.eq_dec x x).
Qed.

Lemma on_universes_true (t : term) : on_universes xpredT (fun _ => xpredT) t.
Proof.
  induction t using term_forall_list_ind => //=.
  - now apply All_forallb.
  - now destruct s.
  - now rewrite IHt1 IHt2.
  - now rewrite IHt1 IHt2.
  - now rewrite IHt1 IHt2 IHt3.
  - now rewrite IHt1 IHt2.
  - now apply forallb_true.
  - now apply forallb_true.
  - now apply forallb_true.
  - rewrite forallb_true IHt /=.
    destruct X as [? [? ->]].
    rewrite All_forallb //=.
    apply/andP ; split.
    + clear.
      induction (pcontext p) as [|[? [] ?]] => //=.
      all: now intuition.
    + apply All_forallb.
      eapply All_impl ; tea.
      cbn.
      move => [] /= bcontext ? [? ?].
      apply /andP ; split => //=.
      clear.
      induction bcontext as [|[? [] ?]] => //=.
      all: now intuition.

  - apply All_forallb.
    eapply All_impl ; tea.
    move => ? [? ?].
    now apply /andP.
  - apply All_forallb.
    eapply All_impl ; tea.
    move => ? [? ?].
    now apply /andP.
  - destruct p as [? []]; cbn in *; rtoProp; intuition eauto.
    solve_all.
Qed.

Ltac eqspec :=
  lazymatch goal with
  | |- context [ eqb ?u ?v ] =>
    destruct (eqb_specT u v) ; nodec ; subst
  end.

Ltac eqspecs :=
  repeat eqspec.

Local Ltac equspec equ pb h :=
  repeat lazymatch goal with
  | |- context [ equ pb ?x ?y ] =>
    destruct (h x y); tas ; nodec ; subst
  end.

Local Ltac ih :=
  repeat lazymatch goal with
  | ih : forall pb napp hle hspb hglpb t' ht ht', reflectT (eq_term_upto_univ_napp _ _ _ pb napp ?t _) _
    |- context [ eqb_term_upto_univ_napp _ _ _ ?pb ?napp ?t ?t' ] =>
    destruct (ih pb napp ltac:(assumption) ltac:(assumption) ltac:(assumption) t'); eauto;
      nodec ; subst
  end.

Arguments eqb : simpl never.

Lemma reflectT_change_left2 P1 P2 R p1 p2 :
  CRelationClasses.iffT (P1 × P2) R -> reflectT P1 p1 -> reflectT P2 p2 -> reflectT R (p1 && p2).
Proof.
  intros [H H'] [] []; constructor.
  1: apply H; now split.
  all: intro HR; destruct (H' HR); now apply f.
Qed.

Lemma reflectT_change_left3 P1 P2 P3 R p1 p2 p3 :
  CRelationClasses.iffT [× P1, P2 & P3] R -> reflectT P1 p1 -> reflectT P2 p2 -> reflectT P3 p3 -> reflectT R (p1 && p2 && p3).
Proof.
  intros [H H'] [] [] []; constructor.
  1: apply H; now split.
  all: intro HR; destruct (H' HR); now apply f.
Qed.

Lemma reflectT_change_left4 P1 P2 P3 P4 R p1 p2 p3 p4 :
  CRelationClasses.iffT [× P1, P2, P3 & P4] R -> reflectT P1 p1 -> reflectT P2 p2 -> reflectT P3 p3 -> reflectT P4 p4 -> reflectT R (p1 && p2 && p3 && p4).
Proof.
  intros [H H'] [] [] [] []; constructor.
  1: apply H; now split.
  all: intro HR; destruct (H' HR); now apply f.
Qed.

Transparent eqb_prim_val eqb_prim_model.

Lemma reflect_eq_term_upto_univ Σ (p : Universe.t -> bool) (q : nat -> term -> bool) cmpu cmps cmp_universe cmp_sort
  (gen_compare_global_instance : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
  pb napp :
  (forall u u', p u -> p u' -> reflect (cmp_universe Conv u u') (cmpu Conv u u')) ->
  (forall u u', p u -> p u' -> reflect (cmp_universe pb u u') (cmpu pb u u')) ->
  (forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' -> reflect (cmp_sort Conv s s') (cmps Conv s s')) ->
  (forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' -> reflect (cmp_sort pb s s') (cmps pb s s')) ->
  (forall gr napp ui ui', forallb p ui -> forallb p ui' -> reflect (cmp_global_instance Σ cmp_universe Conv gr napp ui ui') (gen_compare_global_instance Conv gr napp ui ui')) ->
  (forall gr napp ui ui', forallb p ui -> forallb p ui' -> reflect (cmp_global_instance Σ cmp_universe pb gr napp ui ui') (gen_compare_global_instance pb gr napp ui ui')) ->
  forall t t',
    on_universes p q t ->
    on_universes p q t' ->
    reflectT (eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t')
             (eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance pb napp t t').
Proof.
  intros he hle hs hspb hgl hglpb t t' ht ht'.
  induction t in t', pb, napp, hle, hspb, hglpb, ht, ht' |- * using term_forall_list_ind.
  all: destruct t' ; nodec.
  all: move: ht => /= ; (repeat move => /andP [?]) ; move => ht.
  all: move: ht' => /= ; (repeat move => /andP [?]) ; move => ht'.
  all: cbn - [eqb]; eqspecs; try solve [ ih => //; constructor; constructor; assumption ].
  all: try solve [ match goal with |- context [eqb_binder_annot ?na ?na'] =>
        destruct (eqb_annot_reflect na na'); ih => //=; constructor; constructor; assumption end ].

  - eapply reflectT_change_left. { split; intros XE. 1: constructor; now apply XE. now depelim XE. }
    eapply All_reflect_reflect_All2. 2: now apply forallb_All.
    solve_all.
  - equspec cmps pb hspb.
    constructor. constructor. assumption.
  - eapply reflectT_change_left. { split; intros XE. 1: constructor; now apply XE. now depelim XE. }
    apply reflect_reflectT. eapply reflect_cmp_universe_instance; eauto.
  - eapply reflectT_change_left. { split; intros XE. 1: constructor; now apply XE. now depelim XE. }
    apply reflect_reflectT. now eapply hglpb.
  - eapply reflectT_change_left. { split; intros XE. 1: constructor; now apply XE. now depelim XE. }
    apply reflect_reflectT. now eapply hglpb.

  - eapply reflectT_change_left3. { split; intros XE. 1: destruct XE as [XE1 XE2 XE3]; constructor; [apply XE1|apply XE2|apply XE3]. now depelim XE. }
    + eapply reflectT_change_left4. { split; intros XE. 1: destruct XE as [XE1 XE2 XE3 XE4]; repeat split; [apply XE1|apply XE2|apply XE3|apply XE4]. now depelim XE. }
      * eapply All_reflect_reflect_All2. 2: now apply forallb_All.
        solve_all.
      * apply reflect_reflectT. eapply reflect_cmp_universe_instance; eauto.
      * apply reflect_eq_context_upto_names.
      * solve_all.
    + ih => //=; constructor; assumption.
    + eapply All_reflect_reflect_All2. 2: now apply forallb_All.
      solve_all.
      eapply reflectT_change_left2. { split; intros XE. 1: destruct XE as [XE1 XE2]; constructor; [apply XE1|apply XE2]. now depelim XE. }
      1: apply reflect_eq_context_upto_names.
      unfold test_branch in *. rtoProp.
      ih => //=. constructor; assumption.

  - eapply reflectT_change_left. { split; intros XE. 1: constructor; now apply XE. now depelim XE. }
    eapply All_reflect_reflect_All2. 2: now apply forallb_All.
    solve_all.
    eapply reflectT_change_left4. { split; intros XE. 1: destruct XE as [XE1 XE2 XE3 XE4]; repeat split; [apply XE1|apply XE2|apply XE3|apply XE4]. now depelim XE. }
    1,2: ih => //; constructor; assumption.
    + apply reflect_reflectT, eqb_specT.
    + apply reflect_reflectT, eqb_annot_reflect.

  - eapply reflectT_change_left. { split; intros XE. 1: constructor; now apply XE. now depelim XE. }
    eapply All_reflect_reflect_All2. 2: now apply forallb_All.
    solve_all.
    eapply reflectT_change_left4. { split; intros XE. 1: destruct XE as [XE1 XE2 XE3 XE4]; repeat split; [apply XE1|apply XE2|apply XE3|apply XE4]. now depelim XE. }
    1,2: ih => //; constructor; assumption.
    + apply reflect_reflectT, eqb_specT.
    + apply reflect_reflectT, eqb_annot_reflect.

  - destruct p0 as [? []], prim as [? []];
    cbn in X, ht, ht';
    rewrite /eqb_prim_val /eqb_prim_model; cbn -[eqb]; try eqspecs;
    try repeat constructor.
    1-15:intros e; depelim e; try depelim o; intuition eauto.
    rtoProp. destruct X as (hty & hdef & harr).
    eapply reflectT_change_left. { split; intros XE. 1: constructor; now apply XE. now depelim XE. }
    eapply reflectT_change_left4. { split; intros XE. 1: destruct XE as [XE1 XE2 XE3 XE4]; constructor; [apply XE1|apply XE3|apply XE4|apply XE2]. now depelim XE. }
    3,4:  ih => //; constructor; assumption.
    + rewrite andb_true_r. eapply reflect_reflectT. eauto.
    + eapply All_reflect_reflect_All2. 2: now apply forallb_All.
      solve_all.
Qed.

Lemma eqb_term_upto_univ_impl Σ (p : Universe.t -> bool) (q : nat -> term -> bool) cmpu cmps cmp_universe cmp_sort
  (gen_compare_global_instance : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
  pb napp :
  (forall u u', p u -> p u' -> reflect (cmp_universe Conv u u') (cmpu Conv u u')) ->
  (forall u u', p u -> p u' -> reflect (cmp_universe pb u u') (cmpu pb u u')) ->
  (forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' -> reflect (cmp_sort Conv s s') (cmps Conv s s')) ->
  (forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' -> reflect (cmp_sort pb s s') (cmps pb s s')) ->
  (forall gr napp ui ui', forallb p ui -> forallb p ui' -> reflect (cmp_global_instance Σ cmp_universe Conv gr napp ui ui') (gen_compare_global_instance Conv gr napp ui ui')) ->
  (forall gr napp ui ui', forallb p ui -> forallb p ui' -> reflect (cmp_global_instance Σ cmp_universe pb gr napp ui ui') (gen_compare_global_instance pb gr napp ui ui')) ->
  forall t t', on_universes p q t -> on_universes p q t' ->
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance pb napp t t' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t'.
Proof.
  intros he hle hs hspb hgl hglpb t t' ht ht'.
  eapply elimT, reflect_eq_term_upto_univ.
  all: eassumption.
Qed.

Definition compare_global_instance_proper lookup cmpu cmpu' :
  (forall pb u u', cmpu pb u u' = cmpu' pb u u') ->
  forall ref pb n l l',
      compare_global_instance lookup cmpu pb ref n l l' =
      compare_global_instance lookup cmpu' pb ref n l l'.
Proof.
  intros Hequ ref pb n l l'.
  apply eq_true_iff_eq. etransitivity.
  - symmetry. eapply reflect_iff.
    eapply reflect_cmp_global_instance' with (p := xpredT) (cmp_universe := cmpu); intros; eauto.
    1-2: apply idP.
    1-2: apply forallb_true.
  - eapply reflect_iff.
    eapply reflect_cmp_global_instance' with (p := xpredT); intros; eauto.
    3-4: apply forallb_true.
    1-2: rewrite Hequ; apply idP.
Defined.

Definition eqb_term_upto_univ_proper Σ cmpu cmpu' cmps cmps'
  (gen_compare_global_instance gen_compare_global_instance' : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
  pb napp (t u : term) :
  (forall pb u u', wf_universe Σ u -> wf_universe Σ u' -> cmpu pb u u' = cmpu' pb u u') ->
  (forall pb s s', wf_sort Σ s -> wf_sort Σ s' -> cmps pb s s' = cmps' pb s s') ->
  (forall ref pb n l l', compare_global_instance (lookup_env Σ) cmpu pb ref n l l' = gen_compare_global_instance pb ref n l l') ->
  (forall ref pb n l l', gen_compare_global_instance ref pb n l l' =
                          gen_compare_global_instance' ref pb n l l') ->
  wf_universes Σ t -> wf_universes Σ u ->
  eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance pb napp t u =
  eqb_term_upto_univ_napp cmpu' cmps' gen_compare_global_instance' pb napp t u.
Proof.
  intros Hequ Heqs Hcompare Hgen_compare Ht Hu. apply eq_true_iff_eq.
  eassert _ as X.
  2: split; [apply introT|apply elimT]; apply X.
  eapply reflectT_change_left.
  2: eapply reflect_eq_term_upto_univ with (cmp_universe := cmpu) (cmp_sort := cmps).
  1: eassert _ as X; [eapply reflect_eq_term_upto_univ with (cmp_universe := cmpu) (cmp_sort := cmps) | split; [apply introT|apply elimT]; eapply X].
  all: intros; eauto.
  1-4: apply idP.
  1-2: rewrite -Hcompare; eapply reflect_cmp_global_instance; intros; eauto using idP.
  1-2: rewrite Hequ; eauto using idP.
  1-4: now apply/wf_universeP.
  1-2: rewrite Heqs; eauto using idP.
  1-4: now apply/wf_sort_reflect.
  1-2: rewrite -Hgen_compare -Hcompare; eapply reflect_cmp_global_instance; intros; eauto using idP.
Defined.


Lemma compare_global_instance_refl :
  forall Σ (cmpu : conv_pb -> Universe.t -> Universe.t -> bool) gr pb napp u,
    (forall u, cmpu Conv u u) ->
    (forall u, cmpu pb u u) ->
    compare_global_instance Σ cmpu pb gr napp u u.
Proof.
  intros Σ cmpu gr pb napp u cmpu_refl cmpu_refl'.
  rewrite /compare_global_instance.
  destruct global_variance_gen as [| |v].
  - apply All2_forallb2, All2_refl; auto.
  - apply eqb_refl.
  - apply orb_true_iff. right.
    apply All2_forallb2, All2_refl; auto.
Qed.

Lemma All_All2_diag {A} {P : A -> A -> Prop} {l} :
  All (fun x => P x x) l -> All2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_Forall2_diag {A} {P : A -> A -> Prop} {l} :
  Forall (fun x => P x x) l -> Forall2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma cmp_universe_instance_refl_wf Σ (cmp_universe : Universe.t -> Universe.t -> Prop) l :
  (forall u, wf_universe Σ u -> cmp_universe u u) ->
  forallb (wf_universeb Σ) l  ->
  cmp_universe_instance cmp_universe l l.
Proof.
  intros rRE Hl.
  unfold cmp_universe_instance. solve_all.
  eapply All_All2; tea. intros. apply rRE.
  now apply/wf_universeP.
Qed.

Lemma cmp_global_instance_refl_wf Σ (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop) gr pb napp l :
  (forall u, wf_universe Σ u -> cmp_universe Conv u u) ->
  forallb (wf_universeb Σ) l  ->
  cmp_global_instance Σ cmp_universe pb gr napp l l.
Proof.
  intros rRE Hl.
  rewrite /cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //=. 2: left. all: now eapply cmp_universe_instance_refl_wf.
Qed.

Definition eq_term_upto_univ_refl_wf Σ (cmp_universe : forall _ _ _, Prop) (cmp_sort : forall _ _ _, Prop) pb napp :
  (forall u, wf_universe Σ u -> cmp_universe Conv u u) ->
  (forall s, wf_sort Σ s -> cmp_sort Conv s s) ->
  (forall s, wf_sort Σ s -> cmp_sort pb s s) ->
  forall t, wf_universes Σ t -> eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t.
Proof.
  intros hU hS hS' t wt.
  induction t in pb, napp, hS', wt |- * using term_forall_list_ind.
  all: repeat (cbn in wt; apply andb_and in wt as [? wt]).
  all: try constructor. all: eauto.
  - apply forallb_All in wt; eapply All_mix in wt; try exact X; eapply All_All2 ; try exact wt;
    intros ? [? ?]; eauto.
  - revert s wt; move => ? /wf_sort_reflect ?; eauto.
  - eapply cmp_universe_instance_refl_wf; eauto.
  - apply cmp_global_instance_refl_wf; auto.
  - apply cmp_global_instance_refl_wf; auto.
  - destruct X as [? [? ?]].
    unfold eq_predicate. repeat split; eauto.
    + solve_all. eapply All_All2; tea. solve_all.
    + eapply cmp_universe_instance_refl_wf; eauto.
    + reflexivity.
  - solve_all.
    eapply All_All2; tea. solve_all.
    unfold test_branch in *. rtoProp.
    split. 1: reflexivity.
    eapply b0; tea.
  - eapply forallb_All in wt; eapply All_mix in X; try apply wt; clear wt.
    eapply All_All2; eauto; simpl; intuition eauto;
    apply andb_and in a as [? ?]; eauto.
  - eapply forallb_All in wt; eapply All_mix in X; try apply wt; clear wt.
    eapply All_All2; eauto; simpl; intuition eauto;
    apply andb_and in a as [? ?]; eauto.
  - destruct p as [? []]; cbn -[Universe.of_level] in X, wt; rtoProp; intuition eauto; constructor; eauto.
    + eapply hU. now move/wf_universeP: H.
    + solve_all. eapply All_All2; eauto; simpl; intuition eauto.
Defined.

Lemma eqb_term_upto_univ_refl Σ (cmpu : forall _ _ _, bool) (cmps : forall _ _ _, bool) gen_compare_global_instance pb napp t :
    (forall u, wf_universe Σ u -> cmpu Conv u u) ->
    (forall s, wf_sort Σ s -> cmps Conv s s) ->
    (forall s, wf_sort Σ s -> cmps pb s s) ->
    (forall gr napp ui ui', forallb (wf_universeb Σ) ui -> forallb (wf_universeb Σ) ui' -> reflect (cmp_global_instance Σ cmpu Conv gr napp ui ui') (gen_compare_global_instance Conv gr napp ui ui')) ->
    (forall gr napp ui ui', forallb (wf_universeb Σ) ui -> forallb (wf_universeb Σ) ui' -> reflect (cmp_global_instance Σ cmpu pb gr napp ui ui') (gen_compare_global_instance pb gr napp ui ui')) ->
    wf_universes Σ t ->
    eqb_term_upto_univ_napp cmpu cmps gen_compare_global_instance pb napp t t.
Proof.
  intros eqb_refl leqb_refl eqRe Hglobal Hglobal' Ht.
  eapply introT.
  2: eapply eq_term_upto_univ_refl_wf; eauto.
  1: eapply reflect_eq_term_upto_univ with (p := wf_universeb Σ) (cmp_universe := cmpu) (cmp_sort := cmps); eauto.
  1-4: intros; apply idP.
  all: cbn; tas.
Qed.

(* generic equality for contexts *)

Definition eqb_decl_gen eqb_term pb (d d' : context_decl) : bool :=
  match d, d' with
  | {| decl_name := na; decl_body := None; decl_type := T |},
    {| decl_name := na'; decl_body := None; decl_type := T' |} =>
    eqb_binder_annot na na' && eqb_term pb T T'
  | {| decl_name := na; decl_body := Some b; decl_type := T |},
    {| decl_name := na'; decl_body := Some b'; decl_type := T' |} =>
    eqb_binder_annot na na' && eqb_term Conv b b' && eqb_term pb T T'
  | _, _ => false
  end.

Notation eqb_context_gen eqb_term pb := (forallb2 (eqb_decl_gen eqb_term pb)).

Definition eqb_ctx_upto cmpu cmps gen_compare_global_instance pb : context -> context -> bool :=
  eqb_context_gen (fun pb => eqb_term_upto_univ cmpu cmps gen_compare_global_instance pb) pb.

Lemma eqb_binder_annot_spec {A} na na' : eqb_binder_annot (A:=A) na na' -> eq_binder_annot (A:=A) na na'.
Proof. case: eqb_annot_reflect => //. Qed.

Section reflectContext.
  Context Σ (p : Universe.t -> bool) (q : nat -> term -> bool) cmpu cmps cmp_universe cmp_sort
  (gen_compare_global_instance : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
  pb
  (hu : forall u u', p u -> p u' -> reflect (cmp_universe Conv u u') (cmpu Conv u u'))
  (hu' : forall u u', p u -> p u' -> reflect (cmp_universe pb u u') (cmpu pb u u'))
  (hs : forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' -> reflect (cmp_sort Conv s s') (cmps Conv s s'))
  (hs' : forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' -> reflect (cmp_sort pb s s') (cmps pb s s'))
  (hglobal : forall gr napp ui ui', forallb p ui -> forallb p ui' -> reflect (cmp_global_instance Σ cmp_universe Conv gr napp ui ui') (gen_compare_global_instance Conv gr napp ui ui'))
  (hglobal' : forall gr napp ui ui', forallb p ui -> forallb p ui' -> reflect (cmp_global_instance Σ cmp_universe pb gr napp ui ui') (gen_compare_global_instance pb gr napp ui ui')).

  Lemma reflect_eqb_decl_gen :
    forall d d',
      on_decl_universes p q d ->
      on_decl_universes p q d' ->
      reflectT (compare_decls (fun pb => eq_term_upto_univ Σ cmp_universe cmp_sort pb) pb d d')
        (eqb_decl_gen (fun pb => eqb_term_upto_univ cmpu cmps gen_compare_global_instance pb) pb d d').
  Proof.
    unfold on_decl_universes, compare_decls.
    move => [na [b|] A] [na' [b'|] A'] /= ond ond'.
    2,3: constructor; intro X; depelim X.
    all: rtoProp.
    - eapply reflectT_change_left3. 1: { split; intros XE. 1: destruct XE as [XE1 XE2 XE3]; constructor; [apply XE1|apply XE2|apply XE3]. now depelim XE. }
      + apply reflect_reflectT, eqb_annot_reflect.
      + eapply reflect_eq_term_upto_univ; tea.
      + eapply reflect_eq_term_upto_univ; tea.
    - eapply reflectT_change_left2. 1: { split; intros XE. 1: destruct XE as [XE1 XE2]; constructor; [apply XE1|apply XE2]. now depelim XE. }
      + apply reflect_reflectT, eqb_annot_reflect.
      + eapply reflect_eq_term_upto_univ; tea.
  Qed.

  Lemma reflect_eqb_ctx_gen :
    forall Γ Δ,
      on_ctx_universes p q Γ ->
      on_ctx_universes p q Δ ->
      reflectT (eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ)
        (eqb_ctx_upto cmpu cmps gen_compare_global_instance pb Γ Δ).
  Proof.
    intros.
    eapply reflectT_change_left. 1: { split; apply All2_fold_All2. }
    eapply All_reflect_reflect_All2. 2: apply forallb_All in H0; apply H0.
    apply forallb_All in H. solve_all.
    now apply reflect_eqb_decl_gen.
  Qed.
End reflectContext.

Definition eqb_ctx_gen_proper Σ cmpu cmpu' cmps cmps'
  (gen_compare_global_instance gen_compare_global_instance' : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
  pb :
  (forall pb u u', wf_universe Σ u -> wf_universe Σ u' -> cmpu pb u u' = cmpu' pb u u') ->
  (forall pb s s', wf_sort Σ s -> wf_sort Σ s' -> cmps pb s s' = cmps' pb s s') ->
  (forall ref pb n l l', compare_global_instance (lookup_env Σ) cmpu pb ref n l l' = gen_compare_global_instance pb ref n l l') ->
  (forall ref pb n l l', gen_compare_global_instance ref pb n l l' =
                          gen_compare_global_instance' ref pb n l l') ->
  forall Γ Δ,
    wf_ctx_universes Σ Γ -> wf_ctx_universes Σ Δ ->
    eqb_ctx_upto cmpu cmps gen_compare_global_instance pb Γ Δ =
    eqb_ctx_upto cmpu' cmps' gen_compare_global_instance' pb Γ Δ.
Proof.
  intros hu hs hglob hglob'.
  induction Γ; destruct Δ; simpl; eauto.
  intros HΓ HΔ. rtoProp; f_equal; eauto.
  destruct a as [na [b|] ty], c as [na' [b'|] ty']; cbnr.
  all: unfold wf_decl_universes, on_decl_universes in *; rtoProp; cbn in *.
  all: repeat apply (f_equal2 andb); cbnr.
  all: eapply eqb_term_upto_univ_proper; tea.
Defined.

(** Checking equality *)
(*
Lemma wf_gc_of_uctx {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
: ∑ uctx', push_uctx (global_uctx Σ) = Some uctx'.
Proof.
assert (consistent (global_uctx Σ).2) as HC.
{ sq; apply (wf_consistent _ HΣ). }
unfold gc_of_uctx; simpl in *.
apply gc_consistent_iff in HC.
destruct (gc_of_constraints (global_constraints Σ)).
- eexists; reflexivity.
- contradiction HC.
Defined. *)

Import UnivLoopChecking.UnivLoopChecking.

Lemma init_constraints_of_clean_uctx uctx : init_constraints_of_levels (uctx.1) =_ucset init_constraints_of_levels (clean_uctx uctx).1.
Proof.
  destruct uctx; cbn -[init_constraints_of_levels].
  intros cl.
  split.
  - move/init_constraints_of_levels_spec_inv => [l [hin heq]].
    eapply init_constraints_of_levels_spec; tea.
    apply LevelSet.remove_spec. split => //.
    destruct l; noconf heq; intros eq; congruence.
  - move/init_constraints_of_levels_spec_inv => [l [hin heq]].
    eapply init_constraints_of_levels_spec; tea.
    now apply LevelSet.remove_spec in hin as [].
Qed.

Lemma model_of_clean_uctx m uctx : model_of_uctx m (clean_uctx uctx) <-> model_of_uctx m uctx.
Proof.
  unfold model_of_uctx. cbn -[init_constraints_of_levels].
  rewrite [LevelSet.union (LevelSet.remove _ _) _]LevelSetProp.union_sym.
    rewrite -LevelSetProp.add_union_singleton levelset_add_remove LevelSetProp.add_union_singleton
      LevelSetProp.union_sym.
    rewrite -init_constraints_of_clean_uctx. reflexivity.
Qed.

Lemma graph_of_wf {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
: ∑ G, model_of_uctx G (global_uctx Σ).
Proof.
  destruct (push_uctx init_model (clean_uctx (global_uctx Σ))) eqn:hp.
  - exists u. apply push_uctx_init_model_sat in hp.
    now apply model_of_clean_uctx.
  - apply push_uctx_init_model_unsat in hp; tea.
    * exfalso. destruct HΣ. apply hp.
      assert (consistent (global_uctx Σ).2) as HC.
      { sq; apply (wf_consistent _ X). }
      destruct HC as [v sat].
      exists v. apply satisfies_union. split => //.
      apply satisfies_init.
    * destruct HΣ. eapply wf_global_uctx_invariants. exact X.
Qed.

Lemma graph_of_wf_ext {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
: ∑ G, model_of_uctx G (global_ext_uctx Σ).
Proof.
  destruct (push_uctx init_model (clean_uctx (global_ext_uctx Σ))) eqn:hp.
  - exists u. apply push_uctx_init_model_sat in hp.
    now apply model_of_clean_uctx.
  - apply push_uctx_init_model_unsat in hp; tea.
    * exfalso. destruct HΣ. apply hp.
      assert (consistent (global_ext_uctx Σ).2) as HC.
      { sq. now apply (wf_ext_consistent _ X). }
      destruct HC as [v sat].
      exists v. apply satisfies_union. split => //.
      apply satisfies_init.
    * destruct HΣ. eapply wf_ext_global_uctx_invariants. exact X.
Qed.

(* Lemma uctx'_eq {cf:checker_flags} {Σ} (wfΣ : ∥ wf_ext Σ ∥) :
  let G := graph_of_wf_ext wfΣ in
  (wf_ext_gc_of_uctx wfΣ).π1 = uctx' G.π1 (global_ext_uctx Σ) G.π2.
Proof.
  sq. Opaque gc_of_constraints.
  unfold wf_ext_gc_of_uctx, uctx'. destruct Σ. cbn.
  match goal with | |- (_ ?X).π1 = _ ?Y => set (prf := X) ; set (prf' := Y) end.
  clearbody prf prf'. cbn in *. revert prf prf'.
  set (G := graph_of_wf_ext _). destruct G as [G HG].
  unfold is_graph_of_uctx in *. cbn in *.
  Transparent gc_of_constraints.
  set (gc_of_constraints ((g, u):global_env_ext)) in *.
  now destruct o.
Qed. *)

Lemma valid_cstr_eq {cf : config.checker_flags} cstrs u v : valid_cstr cstrs (u, UnivConstraintType.ConstraintType.Eq, v) <-> eq_universe cstrs u v.
Proof.
  unfold valid_cstr, eq_universe.
  cbn; split.
  - destruct check_univs => //=.
    move=> val hval /val he; now depelim he.
  - destruct check_univs => //=.
    move=> val hval /val he; now constructor.
Qed.

Lemma valid_cstr_le {cf : config.checker_flags} cstrs u v : valid_cstr cstrs (u, UnivConstraintType.ConstraintType.Le, v) <-> leq_universe cstrs u v.
Proof.
  unfold valid_cstr, leq_universe.
  cbn; split.
  - destruct check_univs => //=.
    move=> val hval /val he; now depelim he.
  - destruct check_univs => //=.
    move=> val hval /val he; now constructor.
Qed.

Lemma wf_universe_declared {cf : checker_flags} Σ u :
  wf_universe Σ u ->
  levels_declared (clean_uctx (global_ext_uctx Σ)) u.
Proof.
  move=> wf l /wf.
  rewrite /expr_declared //= levelset_add_remove.
  destruct l; cbn. lsets.
Qed.

Lemma wf_universe_subset {cf : checker_flags} Σ u :
  wf_universe Σ u ->
  LevelSet.Subset (Universe.levels u) (LevelSet.add Level.lzero (clean_uctx (global_ext_uctx Σ)).1).
Proof.
  move=> wf. now apply levels_declared_uctx, wf_universe_declared.
Qed.

Lemma wf_sort_declared {cf : checker_flags} Σ u :
  wf_sort Σ u ->
  levels_declared_sort (clean_uctx (global_ext_uctx Σ)) u.
Proof.
  destruct u; cbn => //.
  move/wf_universe_declared.
  move=> le hin le'. red.
  now apply le in le'.
Qed.

Lemma check_spec_clean uctx check : check_spec (clean_uctx uctx) check <-> check_spec uctx check.
Proof.
  split.
  - unfold check_spec.
    intros. apply H.
    rewrite /clean_uctx //=. red. destruct c as [[l d] r]. rewrite levelset_add_remove.
    apply H0.
  - unfold check_spec.
    intros. apply H.
    rewrite /clean_uctx //=. red. destruct c as [[l d] r]. cbn in H0. rewrite levelset_add_remove in H0.
    apply H0.
Qed.

Section EqualityDecGen.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf_ext Σ ∥).

  Let uctx := global_ext_uctx Σ.

  Let G := (graph_of_wf_ext hΣ).π1.

  Let HG := (graph_of_wf_ext hΣ).π2.

  Lemma eq_universeP_gen checkb
    (check_correct : check_spec uctx checkb)
    u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (eq_universe Σ u u') (check_eqb_universe_gen checkb u u').
  Proof using hΣ.
    intros. destruct Σ as [Σ' φ].
    apply (equivP idP).
    rewrite -valid_cstr_eq.
     pose proof hΣ as hΣ' ; sq.
    eapply check_eqb_universe_spec_gen
         with (uctx := clean_uctx (global_ext_uctx (Σ', φ))) ; eauto.
    + now eapply wf_ext_global_uctx_invariants.
    + eapply model_of_clean_uctx. apply HG.
    + now apply check_spec_clean.
    + split; eapply wf_universe_subset; tea.
  Qed.

  Lemma leq_universeP_gen checkb
    (check_correct : check_spec uctx checkb)
    u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (leq_universe Σ u u') (check_leqb_universe_gen checkb u u').
  Proof using hΣ.
    intros. destruct Σ as [Σ' φ].
    apply (equivP idP).
    rewrite -valid_cstr_le.
     pose proof hΣ as hΣ' ; sq.
    eapply check_leqb_universe_spec_gen
         with (uctx := clean_uctx (global_ext_uctx (Σ', φ))) ; eauto.
    + now eapply wf_ext_global_uctx_invariants.
    + eapply model_of_clean_uctx. apply HG.
    + now apply check_spec_clean.
    + split; eapply wf_universe_subset; tea.
  Qed.

  Definition check_cmpb_universe_gen checkb :=
    (conv_pb_relb_gen (check_eqb_universe_gen checkb) (check_leqb_universe_gen checkb)).

  Lemma compare_universeP_gen checkb
    (check_correct : check_spec uctx checkb) pb u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (compare_universe Σ pb u u') (check_cmpb_universe_gen checkb pb u u').
  Proof.
    destruct pb.
    - now apply eq_universeP_gen.
    - now apply leq_universeP_gen.
  Qed.

  Lemma eq_sortP_gen checkb
    (check_correct : check_spec uctx checkb)
    s s' :
    wf_sort Σ s ->
    wf_sort Σ s' ->
    reflect (eq_sort Σ s s') (check_eqb_sort_gen checkb s s').
  Proof using hΣ.
    apply check_spec_clean in check_correct.
    intros. destruct Σ as [Σ' φ].
    apply (equivP idP); split; sq.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_eqb_sort_spec_gen
        with (uctx := clean_uctx (global_ext_uctx (Σ', φ))) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + eapply model_of_clean_uctx. apply HG.
      + now apply wf_sort_declared in H.
      + now apply wf_sort_declared in H0.
    - intros e.
      eapply check_eqb_sort_spec_gen
        with (uctx := clean_uctx (global_ext_uctx (Σ', φ))); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + eapply model_of_clean_uctx. apply HG.
      + now apply wf_sort_declared in H.
      + now apply wf_sort_declared in H0.
  Qed.

  Lemma leq_sortP_gen checkb
    (check_correct : check_spec uctx checkb)
    s s' :
    wf_sort Σ s ->
    wf_sort Σ s' ->
    reflect (leq_sort Σ s s') (check_leqb_sort_gen checkb s s').
  Proof using hΣ.
    apply check_spec_clean in check_correct.
    intros. destruct Σ as [Σ' φ].
    apply (equivP idP); split; sq.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_leqb_sort_spec_gen
        with (uctx := clean_uctx (global_ext_uctx (Σ', φ))) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + eapply model_of_clean_uctx. apply HG.
      + now apply wf_sort_declared in H.
      + now apply wf_sort_declared in H0.
    - intros e.
      eapply check_leqb_sort_spec_gen
        with (uctx := clean_uctx (global_ext_uctx (Σ', φ))); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + eapply model_of_clean_uctx. apply HG.
      + now apply wf_sort_declared in H.
      + now apply wf_sort_declared in H0.
  Qed.

  Definition check_cmpb_sort_gen checkb :=
    (conv_pb_relb_gen (check_eqb_sort_gen checkb) (check_leqb_sort_gen checkb)).

  Lemma compare_sortP_gen checkb
    (check_correct : check_spec uctx checkb) pb s s' :
    wf_sort Σ s ->
    wf_sort Σ s' ->
    reflect (compare_sort Σ pb s s') (check_cmpb_sort_gen checkb pb s s').
  Proof.
    destruct pb.
    - now apply eq_sortP_gen.
    - now apply leq_sortP_gen.
  Qed.

  Definition eqb_ctx checkb :=
      eqb_ctx_upto (check_cmpb_universe_gen checkb) (check_cmpb_sort_gen checkb)
        (compare_global_instance (lookup_env Σ) (check_cmpb_universe_gen checkb)).

  Definition eqb_termp_napp checkb :=
    eqb_term_upto_univ_napp (check_cmpb_universe_gen checkb) (check_cmpb_sort_gen checkb)
    (compare_global_instance (lookup_env Σ) (check_cmpb_universe_gen checkb)).

  Lemma reflect_eqb_termp_napp pb checkb
    (check_correct : check_spec uctx checkb) napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (eq_termp_napp Σ pb napp t u) (eqb_termp_napp checkb pb napp t u).
  Proof using hΣ.
    apply reflect_eq_term_upto_univ.
    - move => ? ? /wf_universeP ? - /wf_universeP ?.
      now apply compare_universeP_gen.
    - move => ? ? /wf_universeP ? - /wf_universeP ?.
      now apply compare_universeP_gen.
    - move => ? ? /wf_sort_reflect ? - /wf_sort_reflect ?.
      now apply compare_sortP_gen.
    - move => ? ? /wf_sort_reflect ? - /wf_sort_reflect ?.
      now apply compare_sortP_gen.
    - intros.
      eapply reflect_cmp_global_instance; eauto.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
    - intros.
      eapply reflect_cmp_global_instance; eauto.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
  Qed.

  Lemma eqb_termp_napp_spec pb checkb
  (check_correct : check_spec uctx checkb) napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    eqb_termp_napp checkb pb napp t u ->
    eq_termp_napp Σ pb napp t u.
  Proof using hΣ.
    intros.
    eapply elimT. 1: apply reflect_eqb_termp_napp.
    all: eassumption.
  Qed.

  Definition eqb_termp pb leq := (eqb_termp_napp leq pb 0).
  Definition eqb_term := (eqb_termp Conv).
  Definition leqb_term := (eqb_termp Cumul).

  Lemma eqb_term_spec checkb
    (check_correct : check_spec uctx checkb) t u :
    wf_universes Σ t -> wf_universes Σ u ->
    eqb_term checkb t u ->
    eq_term Σ Σ t u.
  Proof using hΣ.
    intros.
    eapply (eqb_termp_napp_spec Conv) ; tea.
  Qed.

  Lemma leqb_term_spec checkb
    (check_correct : check_spec uctx checkb)
    t u :
    wf_universes Σ t -> wf_universes Σ u ->
    leqb_term checkb t u ->
    leq_term Σ Σ t u.
  Proof using hΣ.
    intros.
    eapply (eqb_termp_napp_spec Cumul) ; tea.
  Qed.

  Lemma reflect_leq_term checkb
    (check_correct : check_spec uctx checkb) t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (leq_term Σ Σ t u) (leqb_term checkb t u).
  Proof using hΣ.
    intros.
    now eapply (reflect_eqb_termp_napp Cumul).
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma reflect_eq_term checkb
  (check_correct : check_spec uctx checkb) t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (eq_term Σ t u) (eqb_term checkb t u).
  Proof using hΣ.
    intros.
    now eapply (reflect_eqb_termp_napp Conv).
  Qed.

  Lemma eqb_term_refl checkb
  (check_correct : check_spec uctx checkb) :
    forall t, wf_universes Σ t -> eqb_term checkb t t.
  Proof using hΣ.
    intro t. eapply eqb_term_upto_univ_refl.
    4,5: intros; eapply reflect_cmp_global_instance; tea; intros; cbnr; try apply idP.
    - intros. cbn. unfold check_eqb_universe_gen; toProp; left. toProp. right. apply eqb_refl.
    - intros. eapply check_eqb_sort_refl_gen; eauto.
    - intros. eapply check_eqb_sort_refl_gen; eauto.
  Qed.

  Lemma eqb_ctx_spec checkb
  (check_correct : check_spec uctx checkb) :
    forall pb Γ Δ,
      wf_ctx_universes Σ Γ ->
      wf_ctx_universes Σ Δ ->
      eqb_ctx checkb pb Γ Δ ->
      eq_context_upto Σ (compare_universe Σ) (compare_sort Σ) pb Γ Δ.
  Proof using hΣ.
    intros pb Γ Δ hΓ hΔ h. eapply elimT. 1: eapply reflect_eqb_ctx_gen; eauto. 7: tea.
    - move => ? ? /wf_universeP ? - /wf_universeP ?.
      now apply compare_universeP_gen.
    - move => ? ? /wf_universeP ? - /wf_universeP ?.
      now apply compare_universeP_gen.
    - move => ? ? /wf_sort_reflect ? - /wf_sort_reflect ?.
      now apply compare_sortP_gen.
    - move => ? ? /wf_sort_reflect ? - /wf_sort_reflect ?.
      now apply compare_sortP_gen.
    - intros.
      eapply reflect_cmp_global_instance; eauto.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
    - intros.
      eapply reflect_cmp_global_instance; eauto.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
      + move => ? ? /wf_universeP ? - /wf_universeP ?.
        now apply compare_universeP_gen.
  Qed.

  (*
  Definition eqb_opt_term leq (t u : option term) :=
    match t, u with
    | Some t, Some u => eqb_term leq t u
    | None, None => true
    | _, _ => false
    end.


  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> compare_opt_term Conv Σ (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn => //.
    apply eqb_term_spec; tea.
  Qed.

  Definition eqb_decl (d d' : context_decl) :=
    eqb_binder_annot d.(decl_name) d'.(decl_name) &&
    eqb_opt_term d.(decl_body) d'.(decl_body) && eqb_term d.(decl_type) d'.(decl_type).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl Σ (global_ext_constraints Σ) d d'.
  Proof.
    unfold eqb_decl, eq_decl.
    intro H. rtoProp. apply eqb_opt_term_spec in H1.
    eapply eqb_term_spec in H0; tea.
    eapply eqb_binder_annot_spec in H.
    destruct d as [na [b|] ty], d' as [na' [b'|] ty']; simpl in * => //;
    repeat constructor; eauto.
  Qed.

  Definition eqb_context (Γ Δ : context) := forallb2 eqb_decl Γ Δ.

  Lemma eqb_context_spec Γ Δ
    : eqb_context Γ Δ -> eq_context Σ (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_fold_All2.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed. *)



End EqualityDecGen.
